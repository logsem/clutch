From clutch Require Export clutch lib.flip. 
From clutch.examples Require Export keyed_hash hash rng.

Set Default Proof Using "Type*".

(* A "splittable" pseudo-random number generator derived from a keyed
   hashing function.

   The idea is to be able to generate a collection of separate independent RNGs from a single keyed hash
   by having each RNG use a different key.

   Compare with rng.v, which generates a single rng from a hash function.

*)


Section rng.

  Context (MAX_RNGS_POW : nat).
  Context (MAX_SAMPLES_POW : nat).

  Definition MAX_RNGS : nat := (Nat.pow 2 MAX_RNGS_POW) - 1.
  Definition MAX_SAMPLES : nat := (Nat.pow 2 MAX_SAMPLES_POW) - 1.

  Definition init_rng_gen : val :=
    λ: "_",
      let: "f" := (init_keyed_hash MAX_RNGS_POW MAX_SAMPLES_POW) #() in
      let: "key_cntr" := ref #0 in
      (* We return an rng "generator" that gets a fresh key from key_cntr (if available) and returns
         an rng function using that key *)
      λ: "_",
        let: "k" := !"key_cntr" in
        if: #MAX_RNGS < "k" then
          NONE
        else
          "key_cntr" <- "k" + #1;;
          let: "sample_cntr" := ref #0 in
          SOME (λ: "_",
               let: "v" := !"sample_cntr" in
               let: "b" :=
                 if: "v" ≤ #MAX_SAMPLES then
                   "f" "k" "v"
                 else
                   #false
               in
               "sample_cntr" <- "v" + #1;;
               "b").

  Definition hash_rng_gen_specialized (f : val) (key_cntr : loc) : val :=
      λ: "_",
        let: "k" := ! #key_cntr in
        if: #MAX_RNGS < "k" then
          NONE
        else
          #key_cntr <- "k" + #1;;
          let: "sample_cntr" := ref #0 in
          SOME (λ: "_",
               let: "v" := !"sample_cntr" in
               let: "b" :=
                 if: "v" ≤ #MAX_SAMPLES then
                   f "k" "v"
                 else
                   #false
               in
               "sample_cntr" <- "v" + #1;;
               "b").

  Definition hash_rng_specialized (f : val) (k : nat) (c : loc) : val :=
    (λ: "_",
      let: "v" := !#c in
      let: "b" :=
        if: "v" ≤ #MAX_SAMPLES then
          f #k "v"
        else
          #false
      in
      #c <- "v" + #1;;
      "b").

  Context `{!clutchRGS Σ}.

  (* TODO: it would be better to wrap this ghost_mapG with keyed_mapG *)
  Context {GHOST_MAP: ghost_mapG Σ (fin_hash_dom_space MAX_RNGS_POW MAX_SAMPLES_POW) (option bool)}.

  Definition khashN := nroot.@"khash".

  Definition is_keyed_hash γ f :=
    na_inv clutchRGS_nais khashN (keyed_hash_auth MAX_RNGS_POW MAX_SAMPLES_POW γ f).
  Definition is_skeyed_hash γ f :=
    na_inv clutchRGS_nais khashN (skeyed_hash_auth MAX_RNGS_POW MAX_SAMPLES_POW γ f).

  (* Putting is_keyed_hash seems like it makes the definition but then this is not timeless *)

  Definition hash_rng (n: nat) (g: val) : iProp Σ :=
    ∃ h k c m γ, ⌜ g = hash_rng_specialized h (fin_to_nat k) c ⌝ ∗
             ⌜ ∀ x, n <= x → x ∉ dom m ⌝ ∗
             khashfun_own MAX_RNGS_POW MAX_SAMPLES_POW γ k m ∗
             is_keyed_hash γ h ∗
             c ↦ #n.

  Definition shash_rng (n: nat) (g: val) : iProp Σ :=
    ∃ h k c m γ, ⌜ g = hash_rng_specialized h (fin_to_nat k) c ⌝ ∗
             ⌜ ∀ x, n <= x → x ∉ dom m ⌝ ∗
             khashfun_own MAX_RNGS_POW MAX_SAMPLES_POW γ k m ∗
             is_skeyed_hash γ h ∗
             c ↦ₛ #n.

  Definition hash_rng_gen (n: nat) (f: val) : iProp Σ :=
    ∃ h kcntr γ, ⌜ f = hash_rng_gen_specialized h kcntr ⌝ ∗
                  is_keyed_hash γ h ∗
                  kcntr ↦ #n ∗
                  [∗ set] k ∈ fin_to_set (fin_key_space MAX_RNGS_POW),
                     (⌜ n <= fin_to_nat k ⌝ → khashfun_own _ MAX_SAMPLES_POW γ k ∅).

  Definition shash_rng_gen (n: nat) (f: val) : iProp Σ :=
    ∃ h kcntr γ, ⌜ f = hash_rng_gen_specialized h kcntr ⌝ ∗
                  is_skeyed_hash γ h ∗
                  kcntr ↦ₛ #n ∗
                  [∗ set] k ∈ fin_to_set (fin_key_space MAX_RNGS_POW),
                     (⌜ n <= fin_to_nat k ⌝ → khashfun_own _ MAX_SAMPLES_POW γ k ∅).

  Lemma wp_init_rng_gen E :
    {{{ True }}}
      init_rng_gen #() @ E
    {{{ (f: val), RET f; hash_rng_gen 0 f }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /init_rng_gen.
    wp_pures.
    wp_apply (wp_init_keyed_hash with "[//]").
    iIntros (h) "H". iDestruct "H" as (γ) "(Hauth&Hks)".
    wp_pures.
    wp_alloc key_cntr as "Hkc".
    wp_pures.
    iAssert (|={E}=> is_keyed_hash γ h)%I with "[Hauth]" as ">#His_keyed".
    { iApply na_inv_alloc. iNext. eauto. }
    iModIntro. iApply "HΦ".
    iExists _, _, _. iFrame "# ∗".
    iSplit; first by eauto.
    iApply (big_sepS_mono with "Hks").
    iIntros (x Helem) "$"; auto.
  Qed.

  Lemma spec_init_rng_gen E K :
    ↑specN ⊆ E →
    refines_right K (init_rng_gen #()) ={E}=∗
    ∃ f, refines_right K (of_val f) ∗ shash_rng_gen 0 f.
  Proof.
    iIntros (?) "HK".
    rewrite /init_rng_gen.
    tp_pures.
    tp_bind (init_keyed_hash _ _ _).
    rewrite refines_right_bind.
    iMod (spec_init_keyed_hash with "[$]") as (h γ) "(HK&Hauth&Hks)"; first done.
    rewrite -refines_right_bind /=.
    tp_pures.
    tp_alloc as key_cntr "Hkc".
    tp_pures.
    iAssert (|={E}=> is_skeyed_hash γ h)%I with "[Hauth]" as ">#His_keyed".
    { iApply na_inv_alloc. iNext. eauto. }
    iModIntro. iExists _. iFrame "HK".
    iExists _, _, _. iFrame "# ∗".
    iSplit; first by eauto.
    iApply (big_sepS_mono with "Hks").
    iIntros (x Helem) "$"; auto.
  Qed.

  Lemma wp_run_rng_gen k f E :
    k <= MAX_RNGS →
    {{{ ▷ hash_rng_gen k f }}}
      f #() @ E
    {{{ (g: val), RET (SOMEV g); hash_rng_gen (S k) f ∗ hash_rng 0 g }}}.
  Proof.
    iIntros (Hle Φ) "Hgen HΦ".
    iDestruct "Hgen" as (h kcntr γ) "(>->&#His&Hknctr&Hks)".

    iEval (rewrite /hash_rng_gen_specialized). wp_pures.
    wp_load. wp_pures.
    case_bool_decide; first by lia.
    wp_pures.
    wp_store.
    wp_alloc sample_cntr as "Hsc".
    wp_pures.
    iModIntro.
    rewrite /init_rng_gen.
    iApply "HΦ".
    assert (Hlt: k < S MAX_RNGS) by lia.
    set (k' := (nat_to_fin Hlt : fin_key_space MAX_RNGS_POW)).
    iDestruct (big_sepS_delete _ _ k' with "Hks") as "(Hk&Hks)".
    { apply elem_of_fin_to_set. }
    iSplitL "Hks Hknctr".
    - iExists _, _, _. iSplit; first eauto. iFrame "#".
      assert (Z.of_nat k + 1 = Z.of_nat (S k))%Z as -> by lia.
      iFrame "Hknctr".
      iApply (big_sepS_delete _ _ k').
      { apply elem_of_fin_to_set. }
      iSplitR "Hks".
      * iIntros (Hle'). iExFalso. rewrite /k' fin_to_nat_to_fin in Hle'. lia.
      * iApply (big_sepS_mono with "Hks"). iIntros (??) "H %Hle'".
        iApply "H". iPureIntro; lia.
    - iExists _, k', _, ∅, _. iFrame "Hsc #". iSplit.
      { rewrite /hash_rng_specialized. rewrite /k' fin_to_nat_to_fin //. }
      iSplit.
      { iPureIntro. set_solver. }
      iApply "Hk". rewrite /k' fin_to_nat_to_fin; auto.
  Qed.

  Lemma spec_run_rng_gen k f K E  :
    ↑specN ⊆ E →
    k <= MAX_RNGS →
    shash_rng_gen k f -∗
    refines_right K (f #()) ={E}=∗
    ∃ g, refines_right K (of_val (SOMEV g)) ∗ shash_rng_gen (S k) f ∗ shash_rng 0 g.
  Proof.
    iIntros (HE Hle) "Hgen HK".
    iDestruct "Hgen" as (h kcntr γ) "(->&#His&Hknctr&Hks)".
    iEval (rewrite /hash_rng_gen_specialized) in "HK".
    tp_pures.
    tp_load.
    tp_pures.
    case_bool_decide; first by lia.
    tp_pures.
    tp_store.
    tp_pures.
    tp_alloc as sample_cntr "Hsc".
    tp_pures.
    iModIntro.
    iExists _. iFrame "HK".
    assert (Hlt: k < S MAX_RNGS) by lia.
    set (k' := (nat_to_fin Hlt : fin_key_space MAX_RNGS_POW)).
    iDestruct (big_sepS_delete _ _ k' with "Hks") as "(Hk&Hks)".
    { apply elem_of_fin_to_set. }
    iSplitL "Hks Hknctr".
    - iExists _, _, _. iSplit; first eauto. iFrame "#".
      assert (Z.of_nat k + 1 = Z.of_nat (S k))%Z as -> by lia.
      iFrame "Hknctr".
      iApply (big_sepS_delete _ _ k').
      { apply elem_of_fin_to_set. }
      iSplitR "Hks".
      * iIntros (Hle'). iExFalso. rewrite /k' fin_to_nat_to_fin in Hle'. lia.
      * iApply (big_sepS_mono with "Hks"). iIntros (??) "H %Hle'".
        iApply "H". iPureIntro; lia.
    - iExists _, k', _, ∅, _. iFrame "Hsc #". iSplit.
      { rewrite /hash_rng_specialized. rewrite /k' fin_to_nat_to_fin //. }
      iSplit.
      { iPureIntro. set_solver. }
      iApply "Hk". rewrite /k' fin_to_nat_to_fin; auto.
  Qed.

  Lemma wp_run_rng_gen_out_of_range k f E :
    MAX_RNGS < k →
    {{{ ▷ hash_rng_gen k f }}}
      f #() @ E
    {{{ RET NONEV; hash_rng_gen k f }}}.
  Proof.
    iIntros (Hlt Φ) "Hgen HΦ".
    iDestruct "Hgen" as (h kcntr γ) "(>->&#His&Hknctr&Hks)".

    iEval (rewrite /hash_rng_gen_specialized). wp_pures.
    wp_load. wp_pures.
    case_bool_decide; last by lia.
    wp_pures.
    iApply "HΦ".
    iModIntro. iExists _, _, _. iSplit; first eauto. iFrame "#∗".
  Qed.

  Lemma spec_run_rng_gen_out_of_range k f K E  :
    ↑specN ⊆ E →
    MAX_RNGS < k →
    shash_rng_gen k f -∗
    refines_right K (f #()) ={E}=∗
    refines_right K (of_val NONEV) ∗ shash_rng_gen k f.
  Proof.
    iIntros (HE Hlt) "Hgen HK".
    iDestruct "Hgen" as (h kcntr γ) "(->&#His&Hknctr&Hks)".

    iEval (rewrite /hash_rng_gen_specialized) in "HK". tp_pures.
    tp_load. tp_pures.
    case_bool_decide; last by lia.
    tp_pures.
    iModIntro. iFrame "HK".
    iExists _, _, _. iSplit; first eauto. iFrame "#∗".
  Qed.

  Instance fin_keys_inhabited :
    Inhabited (fin (S (MAX_KEYS MAX_RNGS_POW))).
  Proof. econstructor. econstructor. Qed.

  (* Notice this is almost identical to the version in rng.v, except we need the token
     to open the invariant for the keyed hash *)
  Lemma wp_hash_rng_flip n g K E :
    ↑specN ⊆ E →
    ↑khashN ⊆ E →
    n ≤ MAX_SAMPLES →
    {{{ ▷ hash_rng n g ∗ refines_right K flip%E ∗ na_own clutchRGS_nais (↑khashN) }}}
      g #() @ E
    {{{ (b : bool), RET #b; hash_rng (S n) g ∗ refines_right K #b ∗ na_own clutchRGS_nais (↑khashN) }}}.
  Proof.
    iIntros (HN1 HN2 Hle Φ) "(Hhash&HK&Htok) HΦ".
    rewrite /hash_rng.
    iDestruct "Hhash" as (h k c m γ) "(>->&>%Hdom&Hhash&#Hkeyed_hash&Hc)".
    rewrite /hash_rng_specialized. wp_pures.
    wp_load. wp_pures.
    case_bool_decide; last by lia.
    rewrite /is_keyed_hash.
    wp_pures.
    iMod (na_inv_acc with "[$] [$]") as "(>H&Htok&Hclo)"; auto.
    iDestruct (khashfun_own_couplable _ _ _ _ _ m n with "[$] [$]") as "Hcoup"; auto.
    { apply not_elem_of_dom. auto. }
    iApply (hash.impl_couplable_elim with "[-]"); [done | done |].
    iFrame "Hcoup HK". iIntros (b) ">(Hauth&Hhash) HK".
    wp_apply (wp_khashfun_prev with "[$]").
    { rewrite lookup_insert //. }
    iIntros "(Hauth&Hhash)". wp_pures.
    wp_store. iMod ("Hclo" with "[$]") as "Htok". iModIntro. iApply "HΦ".
    iFrame. iExists _, _, _, _, _. iFrame.
    iSplit; first done.
    iSplit.
    { iPureIntro. intros x. rewrite dom_insert_L.
      set_unfold. intros Hle' [?|?]; first lia.
      eapply Hdom; last by eassumption. lia.
    }
    assert (Z.of_nat n + 1 = Z.of_nat (S n))%Z as -> by lia.
    auto.
  Qed.

  Existing Instance timeless_skeyed_hash_auth.

  Lemma spec_hash_rng_flip_couplable n g K E :
    ↑specN ⊆ E →
    ↑khashN ⊆ E →
    n ≤ MAX_SAMPLES →
    shash_rng n g -∗
    na_own clutchRGS_nais (↑khashN) -∗
    refines_right K (g #()) ={E}=∗
    spec_couplable (λ b, |={E}=> refines_right K #b ∗ shash_rng (S n) g ∗ na_own clutchRGS_nais (↑khashN)).
  Proof.
    iIntros (HN1 HN2 Hle) "Hhash Htok HK".
    iDestruct "Hhash" as (h k c m γ) "(->&%Hdom&Hhash&#Hkeyed_hash&Hc)".
    rewrite /hash_rng_specialized. tp_pures.
    tp_load. tp_pures.
    case_bool_decide; last by lia.
    rewrite /is_skeyed_hash.
    tp_pures.
    iMod (na_inv_acc with "[$] [$]") as "(>H&Htok&Hclo)"; auto.
    iDestruct (khashfun_own_spec_couplable _ _ _ _ _ m n with "[$] [$]") as "Hcoup"; auto.
    { apply not_elem_of_dom. auto. }
    iModIntro.
    iApply (spec_couplable_wand with "Hcoup").
    iIntros (b) ">(Hauth&Hhash)".
    tp_bind (h #k #n).
    rewrite refines_right_bind.
    iMod (spec_khashfun_prev with "[$] [$] [$]") as "(HK&Hauth&Hhash)".
    { rewrite lookup_insert //. }
    { done. }
    rewrite -refines_right_bind/=.
    tp_pures.
    tp_store.
    tp_pures.
    iMod ("Hclo" with "[$]") as "Htok". iModIntro.
    iFrame. iExists _, _, _, _, _. iFrame.
    iSplit; first done.
    iSplit.
    { iPureIntro. intros x. rewrite dom_insert_L.
      set_unfold. intros Hle' [?|?]; first lia.
      eapply Hdom; last by eassumption. lia.
    }
    assert (Z.of_nat n + 1 = Z.of_nat (S n))%Z as -> by lia.
    auto.
  Qed.

  Lemma wp_hash_rng_flip_out_of_range n g E:
    MAX_SAMPLES < n →
    {{{ ▷ hash_rng n g }}}
      g #() @ E
    {{{ RET #false; hash_rng (S n) g }}}.
  Proof.
    iIntros (Hlt Φ) "Hhash HΦ".
    iDestruct "Hhash" as (h k c m γ) "(>->&>%Hdom&Hhash&#Hkeyed_hash&Hc)".
    rewrite /hash_rng_specialized. wp_pures.
    wp_load. wp_pures.
    case_bool_decide; first lia.
    wp_pures. wp_store. iApply "HΦ".
    iModIntro.
    assert (Z.of_nat n + 1 = Z.of_nat (S n))%Z as -> by lia.
    iExists _, _, _, _, _. iFrame "#∗". iSplit; first eauto.
    iPureIntro. intros. apply Hdom. lia.
  Qed.

  Lemma spec_hash_rng_flip_out_of_range n g K E :
    ↑specN ⊆ E →
    MAX_SAMPLES < n →
    shash_rng n g -∗
    refines_right K (g #()) ={E}=∗
    refines_right K #false ∗ shash_rng (S n) g.
  Proof.
    iIntros (HE Hlt) "Hhash HK".
    iDestruct "Hhash" as (h k c m γ) "(->&%Hdom&Hhash&#Hkeyed_hash&Hc)".
    rewrite /hash_rng_specialized. tp_pures.
    tp_load. tp_pures.
    case_bool_decide; first lia.
    tp_pures. tp_store. tp_pures.
    iModIntro. iFrame "HK".
    assert (Z.of_nat n + 1 = Z.of_nat (S n))%Z as -> by lia.
    iExists _, _, _, _, _. iFrame "#∗". iSplit; first eauto.
    iPureIntro. intros. apply Hdom. lia.
  Qed.

  (* The "ideal" version that calls a tape-less flip directly *)

  Definition init_bounded_rng_gen : val :=
    λ: "_",
      let: "rng_cntr" := ref #0 in
      λ: "_",
        let: "k" := !"rng_cntr" in
        if: #MAX_RNGS < "k" then
          NONE
        else
          "rng_cntr" <- "k" + #1;;
          let: "f" := (init_bounded_rng MAX_SAMPLES) #() in
          SOME "f".

  Definition bounded_rng_gen_specialized (c : loc) : val :=
      λ: "_",
        let: "k" := !#c in
        if: #MAX_RNGS < "k" then
          NONE
        else
          #c <- "k" + #1;;
          let: "f" := (init_bounded_rng MAX_SAMPLES) #() in
          SOME "f".

  Definition bounded_rng_gen (n: nat) (g: val) : iProp Σ :=
    ∃ c, ⌜ g = bounded_rng_gen_specialized c ⌝ ∗ c ↦ #n.

  Definition sbounded_rng_gen (n: nat) (g: val) : iProp Σ :=
    ∃ c, ⌜ g = bounded_rng_gen_specialized c ⌝ ∗ c ↦ₛ #n.

  Lemma wp_init_bounded_rng_gen E :
    {{{ True }}}
      init_bounded_rng_gen #() @ E
    {{{ g, RET g; bounded_rng_gen O g }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /init_bounded_rng_gen. wp_pures.
    wp_alloc c as "Hc".
    wp_pures. iModIntro.
    iApply "HΦ".
    iExists _. iFrame. eauto.
  Qed.

  Lemma spec_init_bounded_rng_gen E K :
    ↑specN ⊆ E →
    refines_right K (init_bounded_rng_gen #()) ={E}=∗ ∃ f, refines_right K (of_val f) ∗ sbounded_rng_gen O f.
  Proof.
    iIntros (?) "Hspec".
    rewrite /init_bounded_rng_gen.
    tp_pures.
    tp_alloc as c "Hc".
    tp_pures.
    iModIntro. iExists _. iFrame. iExists c. eauto.
  Qed.

  Lemma wp_run_bounded_rng_gen k f E :
    k <= MAX_RNGS →
    {{{ bounded_rng_gen k f }}}
      f #() @ E
    {{{ (g: val), RET (SOMEV g); bounded_rng_gen (S k) f ∗ bounded_rng MAX_SAMPLES 0 g }}}.
  Proof.
    iIntros (Hle Φ) "Hhash HΦ".
    iDestruct "Hhash" as (c ->) "Hc".
    rewrite /bounded_rng_gen_specialized.
    wp_pures. wp_load. wp_pures.
    case_bool_decide; try lia; [].
    wp_pures. wp_store.
    wp_apply (wp_init_bounded_rng with "[//]").
    iIntros (?) "H". wp_pures.
    iModIntro. iApply "HΦ".
    iFrame.
    iExists _. iSplit; first done.
    assert (Z.of_nat k + 1 = Z.of_nat (S k))%Z as -> by lia. auto.
  Qed.

  Lemma spec_run_bounded_rng_gen k f E K :
    ↑specN ⊆ E →
    k <= MAX_RNGS →
    sbounded_rng_gen k f -∗
    refines_right K (f #()) ={E}=∗
    ∃ g, refines_right K (of_val (SOMEV g)) ∗
         sbounded_rng_gen (S k) f ∗
         sbounded_rng MAX_SAMPLES O g.
  Proof.
    iIntros (? Hle) "Hgen Hspec".
    iDestruct "Hgen" as (c ->) "Hc".
    rewrite /bounded_rng_gen_specialized.
    tp_pures.
    tp_load.
    tp_pures.
    case_bool_decide; try lia; [].
    tp_pures.
    tp_store.
    tp_pures.
    tp_bind (init_bounded_rng _ _).
    rewrite refines_right_bind.
    iMod (spec_init_bounded_rng with "[$]") as (g) "(HK&Hrng)"; auto.
    rewrite -refines_right_bind /=.
    tp_pures.
    iModIntro. iExists _. iFrame. iExists c.
    assert (Z.of_nat k + 1 = Z.of_nat (S k))%Z as -> by lia. auto.
  Qed.

  Lemma wp_run_bounded_rng_gen_out_of_range k f E :
    MAX_RNGS < k →
    {{{ bounded_rng_gen k f }}}
      f #() @ E
    {{{ RET NONEV; bounded_rng_gen k f }}}.
  Proof.
    iIntros (Hle Φ) "Hhash HΦ".
    iDestruct "Hhash" as (c ->) "Hc".
    rewrite /bounded_rng_gen_specialized.
    wp_pures. wp_load. wp_pures.
    case_bool_decide; try lia; [].
    wp_pures.
    iModIntro. iApply "HΦ".
    iExists _. iFrame; eauto.
  Qed.

  Lemma spec_run_bounded_rng_gen_out_of_range k f E K :
    ↑specN ⊆ E →
    MAX_RNGS < k →
    sbounded_rng_gen k f -∗
    refines_right K (f #()) ={E}=∗
         refines_right K (of_val NONEV) ∗
         sbounded_rng_gen k f.
  Proof.
    iIntros (? Hle) "Hgen Hspec".
    iDestruct "Hgen" as (c ->) "Hc".
    rewrite /bounded_rng_gen_specialized.
    tp_pures.
    tp_load.
    tp_pures.
    case_bool_decide; try lia; [].
    tp_pures.
    iFrame.
    iModIntro. iExists _. iFrame. eauto.
  Qed.

  Lemma wp_hash_rng_flip_refine n g sg K E :
    ↑khashN ⊆ E →
    ↑specN ⊆ E →
    {{{ ▷ hash_rng n g ∗ sbounded_rng MAX_SAMPLES n sg ∗ refines_right K (sg #()) ∗
          na_own clutchRGS_nais (↑khashN) }}}
      g #() @ E
    {{{ (b : bool), RET #b; hash_rng (S n) g ∗ sbounded_rng MAX_SAMPLES (S n) sg ∗ refines_right K #b ∗
          na_own clutchRGS_nais (↑khashN) }}}.
  Proof.
    iIntros (HN1 HN2 Φ) "(Hhash&Hbrng&HK&Htok) HΦ".
    iDestruct "Hbrng" as (sc ->) "Hsc".
    rewrite /bounded_rng_specialized.
    tp_pures.
    tp_load.
    tp_pures.
    case_bool_decide.
    - tp_pures.
      tp_bind flip%E.
      rewrite refines_right_bind.
      iApply wp_fupd.
      wp_apply (wp_hash_rng_flip with "[$HK $Hhash $Htok]"); auto.
      { lia. }
      iIntros (b) "(Hhash&HK&Htok)".
      rewrite -refines_right_bind /=.
      tp_pures.
      tp_store.
      tp_pures.
      iApply "HΦ".
      iFrame. iModIntro.
      iExists _.
      assert (Z.of_nat n + 1 = Z.of_nat (S n))%Z as -> by lia.
      iFrame. eauto.
    - tp_pures.
      tp_store.
      tp_pures.
      wp_apply (wp_hash_rng_flip_out_of_range with "[$Hhash]"); auto.
      { lia. }
      iIntros "Hhash".
      iApply "HΦ".
      iFrame.
      iExists _.
      assert (Z.of_nat n + 1 = Z.of_nat (S n))%Z as -> by lia.
      iFrame. eauto.
  Qed.

  Lemma wp_bounded_rng_flip_refine n g sg K E :
    ↑specN ⊆ E →
    ↑khashN ⊆ E →
    {{{ bounded_rng MAX_SAMPLES n g ∗ ▷ shash_rng n sg ∗ refines_right K (sg #()) ∗
          na_own clutchRGS_nais (↑khashN)}}}
      g #() @ E
    {{{ (b : bool), RET #b; bounded_rng MAX_SAMPLES (S n) g ∗ shash_rng (S n) sg ∗ refines_right K #b ∗
          na_own clutchRGS_nais (↑khashN)}}}.
  Proof.
    iIntros (HN1 HN2 Φ) "(Hbrng&Hhash&HK&Htok) HΦ".
    iDestruct "Hbrng" as (sc ->) "Hsc".
    rewrite /bounded_rng_specialized.
    wp_pures. wp_load. wp_pures.
    case_bool_decide.
    - wp_pures.
      iAssert (spec_ctx) with "[-]" as "#Hspec_ctx".
      { iDestruct "HK" as "($&_)". }
      iMod (spec_hash_rng_flip_couplable with "Hhash Htok HK") as "Hspec"; auto.
      { lia. }
      wp_apply (spec_couplable_elim with "[$Hspec $Hspec_ctx Hsc HΦ]"); auto.
      iIntros (b) ">(HK&Hhash)".
      wp_pures. wp_store.
      iModIntro. iApply "HΦ".
      iFrame "HK Hhash". iExists _.
      assert (Z.of_nat n + 1 = Z.of_nat (S n))%Z as -> by lia.
      iFrame. eauto.
    - wp_pures.
      iMod (spec_hash_rng_flip_out_of_range with "Hhash HK") as "(HK&Hhash)"; auto.
      { lia. }
      wp_store.
      iModIntro. iApply "HΦ".
      iFrame "HK Hhash Htok". iExists _.
      assert (Z.of_nat n + 1 = Z.of_nat (S n))%Z as -> by lia.
      iFrame. eauto.
  Qed.

  Definition rngN := nroot.@"rng".

  Lemma hash_bounded_refinement :
    ⊢ REL init_rng_gen << init_bounded_rng_gen :
      lrel_unit → (lrel_unit → lrel_sum lrel_unit (lrel_unit → lrel_bool)).
  Proof.
    rel_arrow_val.
    iIntros (??) "(->&->)".
    rewrite refines_eq. iIntros (K) "HK Hown".
    iApply wp_fupd.
    wp_apply (wp_init_rng_gen with "[//]").
    iIntros (g) "Hhash_gen".
    iMod (spec_init_bounded_rng_gen with "[$]") as (f) "(HK&Hbounded_gen)"; first done.
    set (P := (∃ n, hash_rng_gen n g ∗ sbounded_rng_gen n f)%I).
    iMod (na_inv_alloc clutchRGS_nais _ rngN P with "[Hhash_gen Hbounded_gen]") as "#Hinv".
    { iNext. iExists O. iFrame. }
    iModIntro. iExists _. iFrame.
    iIntros (v1 v2) "!> (->&->)".
    clear K.
    rewrite /P.
    iApply (refines_na_inv with "[$Hinv]") ; auto ; iIntros "[HP Hclose]".
    rewrite refines_eq. iIntros (K) "HK Hown".
    iDestruct "HP" as (m) "(Hg&>Hsf)".
    iApply wp_fupd.
    destruct (decide (m <= MAX_RNGS)) as [Hl|]; last first.
    { wp_apply (wp_run_rng_gen_out_of_range with "[$]"); first lia.
      iIntros "Hg".
      iMod (spec_run_bounded_rng_gen_out_of_range with "[$] [$]") as "(HK&Hsf)"; auto; try lia.
      iMod ("Hclose" with "[Hg Hsf $Hown]").
      { iNext. iExists _; iFrame. }
      iModIntro. iExists _; iFrame.
      iExists _, _. iLeft.
      iSplit; first eauto.
      iSplit; first eauto.
      eauto. }

    wp_apply (wp_run_rng_gen with "[$]"); first done.
    iIntros (hrng) "(Hg&Hrng)".
    iMod (spec_run_bounded_rng_gen with "Hsf HK") as (srng) "(HK&Hsf&Hsrng)"; auto.
    iMod ("Hclose" with "[Hg Hsf Hown]") as "Hown".
    { iFrame. iNext. iExists _; iFrame. }


    (* finally we show a refinement between the generated rngs *)
    set (Prng := (∃ n, hash_rng n hrng ∗ sbounded_rng MAX_SAMPLES n srng)%I).
    iMod (na_inv_alloc clutchRGS_nais _ rngN Prng with "[Hrng Hsrng]") as "#Hinv_rng".
    { rewrite /Prng. iNext. iExists _. iFrame.  }
    iClear "Hinv".
    iModIntro. iExists _. iFrame.


    iExists _, _. iRight.
    iSplit; first eauto.
    iSplit; first eauto.

    iIntros (v1 v2) "!> (->&->)".
    clear Hl m K.
    iApply (refines_na_inv with "[$Hinv_rng]") ; auto ; iIntros "[HP Hclose]".
    rewrite refines_eq. iIntros (K) "HK Hown".
    iDestruct "HP" as (m) "(Hf&>Hsf)".
    iApply wp_fupd.
    iDestruct (na_own_acc (↑khashN) with "Hown") as "(Hown&Hclose')"; first solve_ndisj.
    wp_apply (wp_hash_rng_flip_refine with "[$Hf $Hsf $HK $Hown]"); [done | done |].
    iIntros (b) "(Hhash&Hbounded&HK&Hown)".
    iDestruct ("Hclose'" with "[$]") as "Hown".
    iMod ("Hclose" with "[-HK]").
    { iFrame. iExists _. iFrame. }
    iExists _. iFrame. eauto.
  Qed.

  Lemma bounded_hash_refinement :
    ⊢ REL init_bounded_rng_gen << init_rng_gen :
      lrel_unit → (lrel_unit → lrel_sum lrel_unit (lrel_unit → lrel_bool)).
  Proof.
    rel_arrow_val.
    iIntros (??) "(->&->)".
    rewrite refines_eq. iIntros (K) "HK Hown".
    iApply wp_fupd.
    wp_apply (wp_init_bounded_rng_gen with "[//]").
    iIntros (g) "Hbounded_gen".
    iMod (spec_init_rng_gen with "[$]") as (f) "(HK&Hhash_gen)"; first done.
    set (P := (∃ n, shash_rng_gen n f ∗ bounded_rng_gen n g)%I).
    iMod (na_inv_alloc clutchRGS_nais _ rngN P with "[Hhash_gen Hbounded_gen]") as "#Hinv".
    { iNext. iExists O. iFrame. }
    iModIntro. iExists _. iFrame.
    iIntros (v1 v2) "!> (->&->)".
    clear K.
    rewrite /P.
    iApply (refines_na_inv with "[$Hinv]") ; auto ; iIntros "[HP Hclose]".
    rewrite refines_eq. iIntros (K) "HK Hown".
    iDestruct "HP" as (m) "(Hsf&>Hg)".
    iApply wp_fupd.
    destruct (decide (m <= MAX_RNGS)) as [Hl|]; last first.
    { wp_apply (wp_run_bounded_rng_gen_out_of_range with "[$]"); first lia.
      iIntros "Hg".
      iMod (spec_run_rng_gen_out_of_range with "[$] [$]") as "(HK&Hsf)"; auto; try lia.
      iMod ("Hclose" with "[Hg Hsf $Hown]").
      { iNext. iExists _; iFrame. }
      iModIntro. iExists _; iFrame.
      iExists _, _. iLeft.
      iSplit; first eauto.
      iSplit; first eauto.
      eauto. }

    wp_apply (wp_run_bounded_rng_gen with "[$]"); first done.
    iIntros (rng) "(Hg&Hrng)".
    iMod (spec_run_rng_gen with "Hsf HK") as (srng) "(HK&Hsf&Hsrng)"; auto.
    iMod ("Hclose" with "[Hg Hsf Hown]") as "Hown".
    { iFrame. iNext. iExists _; iFrame. }


    (* finally we show a refinement between the generated rngs *)
    set (Prng := (∃ n, shash_rng n srng ∗ bounded_rng MAX_SAMPLES n rng)%I).
    iMod (na_inv_alloc clutchRGS_nais _ rngN Prng with "[Hrng Hsrng]") as "#Hinv_rng".
    { rewrite /Prng. iNext. iExists _. iFrame.  }
    iClear "Hinv".
    iModIntro. iExists _. iFrame.


    iExists _, _. iRight.
    iSplit; first eauto.
    iSplit; first eauto.

    iIntros (v1 v2) "!> (->&->)".
    clear Hl m K.
    iApply (refines_na_inv with "[$Hinv_rng]") ; auto ; iIntros "[HP Hclose]".
    rewrite refines_eq. iIntros (K) "HK Hown".
    iDestruct "HP" as (m) "(Hf&>Hsf)".
    iApply wp_fupd.
    iDestruct (na_own_acc (↑khashN) with "Hown") as "(Hown&Hclose')"; first solve_ndisj.
    wp_apply (wp_bounded_rng_flip_refine with "[$Hf $Hsf $HK $Hown]"); [done | done |].
    iIntros (b) "(Hhash&Hbounded&HK&Hown)".
    iDestruct ("Hclose'" with "[$]") as "Hown".
    iMod ("Hclose" with "[-HK]").
    { iFrame. iExists _. iFrame. }
    iExists _. iFrame. eauto.
  Qed.

End rng.
