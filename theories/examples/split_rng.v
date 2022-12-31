From stdpp Require Import namespaces.
From iris.base_logic Require Import invariants na_invariants.
From self.prob_lang Require Import notation proofmode primitive_laws spec_rules spec_tactics.
From self.logrel Require Import model rel_rules rel_tactics.
From iris.algebra Require Import auth gmap excl frac agree.
From self.prelude Require Import base.
From self.examples Require Import keyed_hash hash rng.

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
               if: #MAX_SAMPLES < "v" then
                 #false
               else
                 let: "b" := "f" "k" "v" in
                 "sample_cntr" <- "v" + #1;;
                 "b").

  Definition hash_rng_gen_specialized (f: val) (key_cntr: loc) : val :=
      λ: "_",
        let: "k" := ! #key_cntr in
        if: #MAX_RNGS < "k" then
          NONE
        else
          #key_cntr <- "k" + #1;;
          let: "sample_cntr" := ref #0 in
          SOME (λ: "_",
               let: "v" := !"sample_cntr" in
               if: #MAX_SAMPLES < "v" then
                 #false
               else
                 let: "b" := f "k" "v" in
                 "sample_cntr" <- "v" + #1;;
                 "b").

  Definition hash_rng_specialized (f : val) (k : nat) (c : loc) : val :=
    (λ: "_",
      let: "v" := !#c in
      if: #MAX_SAMPLES < "v" then
        #false
      else
        let: "b" := f #k "v" in
        #c <- "v" + #1;;
        "b").


  Context `{!prelogrelGS Σ}.

  (* TODO: it would be better to wrap this ghost_mapG with keyed_mapG *)
  Context {GHOST_MAP: ghost_mapG Σ (fin_hash_dom_space MAX_RNGS_POW MAX_SAMPLES_POW) (option bool)}.

  Definition khashN := nroot.@"khash".

  Definition is_keyed_hash γ f :=
    na_inv prelogrelGS_nais khashN (keyed_hash_auth MAX_RNGS_POW MAX_SAMPLES_POW γ f).

  (* Putting is_keyed_hash seems like it makes the definition but then this is not timeless *)

  Definition hash_rng (n: nat) (g: val) : iProp Σ :=
    ∃ h k c m γ, ⌜ g = hash_rng_specialized h (fin_to_nat k) c ⌝ ∗
             ⌜ ∀ x, n <= x → x ∉ dom m ⌝ ∗
             khashfun_own MAX_RNGS_POW MAX_SAMPLES_POW γ k m ∗
             is_keyed_hash γ h ∗
             c ↦ #n.

  Definition hash_rng_gen (n: nat) (f: val) : iProp Σ :=
    ∃ h kcntr γ, ⌜ f = hash_rng_gen_specialized h kcntr ⌝ ∗
                  is_keyed_hash γ h ∗
                  kcntr ↦ #n ∗
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

  Lemma wp_run_rng_gen k f E :
    k <= MAX_RNGS →
    {{{ hash_rng_gen k f }}}
      f #() @ E
    {{{ (g: val), RET (SOMEV g); hash_rng_gen (S k) f ∗ hash_rng 0 g }}}.
  Proof.
    iIntros (Hle Φ) "Hgen HΦ".
    iDestruct "Hgen" as (h kcntr γ ->) "(#His&Hknctr&Hks)".

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

  Lemma wp_run_rng_gen_out_of_range k f E :
    MAX_RNGS < k →
    {{{ hash_rng_gen k f }}}
      f #() @ E
    {{{ RET NONEV; hash_rng_gen k f }}}.
  Proof.
    iIntros (Hlt Φ) "Hgen HΦ".
    iDestruct "Hgen" as (h kcntr γ ->) "(#His&Hknctr&Hks)".

    iEval (rewrite /hash_rng_gen_specialized). wp_pures.
    wp_load. wp_pures.
    case_bool_decide; last by lia.
    wp_pures.
    iApply "HΦ".
    iModIntro. iExists _, _, _. iSplit; first eauto. iFrame "#∗".
  Qed.

  (* Notice this is almost identical to the version in rng.v, except we need the token
     to open the invariant for the keyed hash *)
  Lemma wp_hash_rng_flip n g K E :
    ↑specN ⊆ E →
    ↑khashN ⊆ E →
    n ≤ MAX_SAMPLES →
    {{{ hash_rng n g ∗ refines_right K (flip #()) ∗ na_own prelogrelGS_nais (↑khashN) }}}
      g #() @ E
    {{{ (b : bool), RET #b; hash_rng (S n) g ∗ refines_right K #b ∗ na_own prelogrelGS_nais (↑khashN) }}}.
  Proof.
    iIntros (HN1 HN2 Hle Φ) "(Hhash&HK&Htok) HΦ".
    iDestruct "Hhash" as (h k c m γ -> Hdom) "(Hhash&#Hkeyed_hash&Hc)".
    rewrite /hash_rng_specialized. wp_pures.
    wp_load. wp_pures.
    case_bool_decide; first by lia.
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

  Lemma wp_hash_rng_flip_out_of_range n g E:
    MAX_SAMPLES < n →
    {{{ hash_rng n g }}}
      g #() @ E
    {{{ RET #false; hash_rng n g }}}.
  Proof.
    iIntros (Hlt Φ) "Hhash HΦ".
    iDestruct "Hhash" as (h c ? m γ -> Hdom) "(Hhash&#His&Hc)".
    rewrite /hash_rng_specialized. wp_pures.
    wp_load. wp_pures.
    case_bool_decide; last lia.
    wp_pures. iApply "HΦ".
    iModIntro. iExists _, _, _, _, _. iFrame. eauto.
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

  Lemma wp_hash_rng_flip_refine n g sg K E :
    ↑khashN ⊆ E →
    ↑specN ⊆ E →
    {{{ hash_rng n g ∗ sbounded_rng MAX_SAMPLES n sg ∗ refines_right K (sg #()) ∗
          na_own prelogrelGS_nais (↑khashN) }}}
      g #() @ E
    {{{ (b : bool), RET #b; hash_rng (S n) g ∗ sbounded_rng MAX_SAMPLES (S n) sg ∗ refines_right K #b }}}.
  Proof.
    iIntros (HN1 HN2 Φ) "(Hhash&Hbrng&HK&Htok) HΦ".
    iDestruct "Hbrng" as (sc ->) "Hsc".
    rewrite /bounded_rng_specialized.
    tp_pures K.
    tp_load K.
    tp_pures K.
    case_bool_decide.
    - tp_pures K.
      tp_bind K (flip #())%E.
      rewrite refines_right_bind.
      iApply wp_fupd.
      wp_apply (wp_hash_rng_flip with "[$HK $Hhash $Htok]"); auto.
      { lia. }
      iIntros (b) "(Hhash&HK&Htok)".
      rewrite -refines_right_bind /=.
      tp_pures K.
      tp_store K.
      tp_pures K.
      iApply "HΦ".
      iFrame. iModIntro.
      iExists _.
      assert (Z.of_nat n + 1 = Z.of_nat (S n))%Z as -> by lia.
      iFrame. eauto.
    - tp_pures K.
      tp_store K.
      tp_pures K.
      wp_apply (wp_hash_rng_flip_out_of_range with "[$Hhash]"); auto.
      { lia. }
      iIntros "Hhash".
      iApply "HΦ".
      iFrame.
  Abort.
  (*
      iExists _.
      assert (Z.of_nat n + 1 = Z.of_nat (S n))%Z as -> by lia.
      iFrame. eauto.
  Qed.
   *)

End rng.
