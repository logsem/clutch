From clutch Require Export clutch lib.flip.
From clutch.examples Require Export hash.

Set Default Proof Using "Type*".

(* A simple "pseudo-random number generator" derived from a hashing function.

   The random number generator maintains an internal private
   counter. Each time a flip is requested, it hashes the value of the
   counter, increments the counter, and returns the hash bit.

   We prove that this is contextually equivalent to an "ideal"
   implentation that keeps a counter value but just calls flip
   directly so long as the counter is under a maximum value.

   In some sense this equvialence proof may seem trivial, since we use the lazy hash function,
   and under the hood our lazy hash actually does in fact amount to calling flip
   () when a hash is queried for the first time for a given key. So
   the proof boils down to showing that counter is incremented properly
   and we never re-use the counter value twice.

   Nevertheless, the proof is still an interesting exercise for two
   reasons:

   (1) This is somewhat similar to PRNG based on encrypting a counter
   with AES, which is used in realistic scenarios. (Though in that
   context, because a block cipher implements a pseudo-random
   permutation instead of a pseudo-random function, the argument is
   more involved since the PRNG is not indistinguishable from flip()).

   (2) If we had used the eager hash, the proof would be much harder
   and we would need the "ideal" non-hash version to use a tape so
   that we could pre-sample all of its values.  Fortunately we already
   proved the eager hash is equivalent to the lazy hash.

 *)


Section rng.

  Context (MAX : nat).

  Definition init_hash_rng : val :=
    λ: "_",
      let: "f" := init_hash #MAX in
      let: "c" := ref #0 in
      (λ: "_",
        let: "n" := !"c" in
        let: "b" := "f" "n" in
        "c" <- "n" + #1;;
        "b").

  Definition hash_rng_specialized (f : val) (c : loc) : val :=
      (λ: "_",
        let: "n" := !#c in
        let: "b" := f "n" in
        #c <- "n" + #1;;
        "b").


  Context `{!clutchRGS Σ}.

  Definition hash_rng (n: nat) (g: val) : iProp Σ :=
    ∃ h c m, ⌜ g = hash_rng_specialized h c ⌝ ∗
             ⌜ ∀ x, n <= x → x ∉ dom m ⌝ ∗
             hashfun MAX h m ∗
             c ↦ #n.

  Definition shash_rng (n: nat) (g: val) : iProp Σ :=
    ∃ h c m, ⌜ g = hash_rng_specialized h c ⌝ ∗
             ⌜ ∀ x, n <= x → x ∉ dom m ⌝ ∗
             shashfun MAX h m ∗
             c ↦ₛ #n.

  Existing Instances timeless_hashfun.
  Lemma timeless_hash_rng n g :
    Timeless (hash_rng n g).
  Proof. apply _. Qed.

  Existing Instances timeless_shashfun.
  Lemma timeless_shash_rng n g :
    Timeless (shash_rng n g).
  Proof. apply _. Qed.

  (* TODO(Joe): these instances interfere in a bad way that I don't understand. *)
  (*
  Existing Instances timeless_hash_rng timeless_shash_rng.
   *)

  Lemma wp_init_hash_rng E :
    {{{ True }}}
      init_hash_rng #() @ E
    {{{ g, RET g; hash_rng O g }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /init_hash_rng. wp_pures.
    wp_apply (wp_init_hash with "[//]").
    iIntros (f) "Hhash".
    wp_pures.

    wp_alloc c as "Hc".
    wp_pures. iModIntro.
    iApply "HΦ".

    iExists _, _, _. iFrame. iSplit; iPureIntro; auto.
    set_solver.
  Qed.

  Lemma spec_init_hash_rng K E :
    ↑specN ⊆ E →
    refines_right K (init_hash_rng #()) ={E}=∗ ∃ f, refines_right K (of_val f) ∗ shash_rng O f.
  Proof.
    iIntros (?) "HK".
    rewrite /init_hash_rng.
    tp_pures.
    tp_bind (init_hash _)%E.
    rewrite refines_right_bind.
    iMod (spec_init_hash with "[$HK]") as (f) "(HK&Hhash)"; first done.
    rewrite -refines_right_bind/=.
    tp_pures.
    tp_alloc as c "Hc".
    tp_pures.
    iModIntro.
    iExists _; iFrame "HK".
    iExists _, _, _. iFrame. iSplit; iPureIntro; auto.
    set_solver.
  Qed.

  Lemma wp_hash_rng_flip n g K E :
    ↑specN ⊆ E →
    n ≤ MAX →
    {{{ hash_rng n g ∗ refines_right K flip}}}
      g #() @ E
    {{{ (b : bool), RET #b; hash_rng (S n) g ∗ refines_right K #b }}}.
  Proof.
    iIntros (HN Hle Φ) "(Hhash&HK) HΦ".
    iDestruct "Hhash" as (h c m -> Hdom) "(Hhash&Hc)".
    rewrite /hash_rng_specialized. wp_pures.
    wp_load. wp_pures.
    iDestruct (hashfun_couplable n with "[$]") as "Hcoup"; auto.
    { apply not_elem_of_dom. auto. }
    iApply (impl_couplable_elim with "[$Hcoup $HK Hc HΦ]"); [done | done |].
    iIntros (b) "Hhash HK".
    wp_apply (wp_hashfun_prev with "[$]").
    { rewrite lookup_insert //. }
    iIntros "Hhash". wp_pures.
    wp_store. iModIntro. iApply "HΦ".
    iFrame. iExists _, _, _. iFrame.
    iSplit; first done.
    iSplit.
    { iPureIntro. intros x. rewrite dom_insert_L.
      set_unfold. intros Hle' [?|?]; first lia.
      eapply Hdom; last by eassumption. lia.
    }
    assert (Z.of_nat n + 1 = Z.of_nat (S n))%Z as -> by lia.
    auto.
  Qed.

 (* TODO: move *)
  Lemma spec_couplable_wand (P Q: bool → iProp Σ) :
    spec_couplable P -∗
    (∀ b, P b -∗ Q b) -∗
    spec_couplable Q.
  Proof.
    rewrite /spec_couplable.
    iDestruct 1 as (α bs) "(Hα&HP)".
    iIntros "HPQ".
    iExists α, bs. iFrame. iIntros (?) "H". iApply "HPQ".
    iApply "HP". auto.
  Qed.

  Lemma spec_hash_rng_flip_couplable n g K E :
    ↑specN ⊆ E →
    n ≤ MAX →
    shash_rng n g -∗
    refines_right K (g #()) ={E}=∗
    spec_couplable (λ b, |={E}=> refines_right K #b ∗ shash_rng (S n) g).
  Proof.
    iIntros (? Hle) "Hshash HK".
    iDestruct "Hshash" as (h c m -> Hdom) "(Hhash&Hc)".
    rewrite /hash_rng_specialized.
    tp_pures. tp_load. tp_pures.
    iModIntro.
    iDestruct (shashfun_couplable n with "Hhash") as "Hhash"; auto.
    { apply not_elem_of_dom, Hdom. auto. }
    iApply (spec_couplable_wand with "Hhash").
    iIntros (b) "Hhash".
    tp_bind (h _)%E.
    rewrite refines_right_bind.
    iMod (spec_hashfun_prev with "Hhash HK") as "(HK&Hhash)".
    { rewrite lookup_insert //. }
    { done. }
    rewrite -refines_right_bind /=.
    tp_pures.
    tp_store.
    tp_pures.
    iFrame "HK". iModIntro.
    iExists _, _, _.
    iFrame.
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
    MAX < n →
    {{{ hash_rng n g }}}
      g #() @ E
    {{{ RET #false; hash_rng (S n) g }}}.
  Proof.
    iIntros (Hlt Φ) "Hhash HΦ".
    iDestruct "Hhash" as (h c m -> Hdom) "(Hhash&Hc)".
    rewrite /hash_rng_specialized. wp_pures.
    wp_load. wp_pures.
    wp_apply (wp_hashfun_out_of_range with "[$]").
    { lia. }
    iIntros "Hhash". wp_pures.
    wp_store. iModIntro. iApply "HΦ".
    iFrame. iExists _, _, _. iFrame.
    iSplit; first done.
    iSplit.
    { iPureIntro. intros. apply Hdom. lia. }
    assert (Z.of_nat n + 1 = Z.of_nat (S n))%Z as -> by lia.
    auto.
  Qed.

  Lemma spec_hash_rng_flip_out_of_range n g K E :
    ↑specN ⊆ E →
    MAX < n →
    shash_rng n g -∗
    refines_right K (g #()) ={E}=∗
    refines_right K #false ∗ shash_rng (S n) g.
  Proof.
    iIntros (? Hlt) "Hshash HK".
    iDestruct "Hshash" as (h c m -> Hdom) "(Hhash&Hc)".
    rewrite /hash_rng_specialized.
    tp_pures. tp_load. tp_pures.
    tp_bind (h _)%E.
    rewrite refines_right_bind.
    iMod (spec_hashfun_out_of_range with "Hhash HK") as "(HK&Hhash)"; auto.
    { lia. }
    rewrite -refines_right_bind /=.
    tp_pures.
    tp_store.
    tp_pures.
    iFrame "HK". iModIntro.
    iExists _, _, _.
    iFrame.
    iSplit; first done.
    iSplit.
    { iPureIntro. intros. apply Hdom. lia. }
    assert (Z.of_nat n + 1 = Z.of_nat (S n))%Z as -> by lia.
    auto.
  Qed.

  (* The "ideal" version that calls a tape-less flip directly *)
  Definition init_bounded_rng : val :=
    λ: "_",
      let: "c" := ref #0 in
      (λ: "_",
        let: "n" := !"c" in
        let: "b" :=
          if: "n" ≤ #MAX then
            flip
          else #false in
        "c" <- "n" + #1;;
        "b").

  Definition bounded_rng_specialized (c : loc) : val :=
      (λ: "_",
        let: "n" := !#c in
        let: "b" :=
          if: "n" ≤ #MAX then
            flip
          else #false in
        #c <- "n" + #1;;
        "b").

  Definition bounded_rng (n: nat) (g: val) : iProp Σ :=
    ∃ c, ⌜ g = bounded_rng_specialized c ⌝ ∗ c ↦ #n.

  Definition sbounded_rng (n: nat) (g: val) : iProp Σ :=
    ∃ c, ⌜ g = bounded_rng_specialized c ⌝ ∗ c ↦ₛ #n.

  Lemma wp_init_bounded_rng E :
    {{{ True }}}
      init_bounded_rng #() @ E
    {{{ g, RET g; bounded_rng O g }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /init_bounded_rng. wp_pures.
    wp_alloc c as "Hc".
    wp_pures. iModIntro.
    iApply "HΦ".
    iExists _. iFrame. eauto.
  Qed.

  Lemma spec_init_bounded_rng E K :
    ↑specN ⊆ E →
    refines_right K (init_bounded_rng #()) ={E}=∗ ∃ f, refines_right K (of_val f) ∗ sbounded_rng O f.
  Proof.
    iIntros (?) "Hspec".
    rewrite /init_bounded_rng.
    tp_pures.
    tp_alloc as c "Hc".
    tp_pures.
    iModIntro. iExists _. iFrame. iExists c. eauto.
  Qed.

  Lemma wp_hash_rng_flip_refine n g sg K E :
    ↑specN ⊆ E →
    {{{ hash_rng n g ∗ sbounded_rng n sg ∗ refines_right K (sg #())}}}
      g #() @ E
    {{{ (b : bool), RET #b; hash_rng (S n) g ∗ sbounded_rng (S n) sg ∗ refines_right K #b }}}.
  Proof.
    iIntros (HN Φ) "(Hhash&Hbrng&HK) HΦ".
    iDestruct "Hbrng" as (sc ->) "Hsc".
    rewrite /bounded_rng_specialized.
    tp_pures.
    tp_load.
    tp_pures.
    case_bool_decide.
    - tp_pures.
      tp_bind flip.
      rewrite refines_right_bind.
      iApply wp_fupd.
      wp_apply (wp_hash_rng_flip with "[$HK $Hhash]"); [done|lia|].
      iIntros (b) "(Hhash&HK)".
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
    {{{ bounded_rng n g ∗ shash_rng n sg ∗ refines_right K (sg #())}}}
      g #() @ E
    {{{ (b : bool), RET #b; bounded_rng (S n) g ∗ shash_rng (S n) sg ∗ refines_right K #b }}}.
  Proof.
    iIntros (HN Φ) "(Hbrng&Hhash&HK) HΦ".
    iDestruct "Hbrng" as (sc ->) "Hsc".
    rewrite /bounded_rng_specialized.
    wp_pures. wp_load. wp_pures.
    case_bool_decide.
    - wp_pures.
      iAssert (spec_ctx) with "[-]" as "#Hspec_ctx".
      { iDestruct "HK" as "($&_)". }
      iMod (spec_hash_rng_flip_couplable with "Hhash HK") as "Hspec"; auto.
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
      iFrame "HK Hhash". iExists _.
      assert (Z.of_nat n + 1 = Z.of_nat (S n))%Z as -> by lia.
      iFrame. eauto.
  Qed.

  Definition rngN := nroot.@"rng".

  Lemma hash_bounded_refinement :
    ⊢ REL init_hash_rng << init_bounded_rng : lrel_unit → (lrel_unit → lrel_bool).
  Proof.
    rel_arrow_val.
    iIntros (??) "(->&->)".
    rewrite refines_eq. iIntros (K) "HK Hown".
    iApply wp_fupd.
    wp_apply (wp_init_hash_rng with "[//]").
    iIntros (g) "Hhash".
    iMod (spec_init_bounded_rng with "[$]") as (f) "(HK&Hbounded)"; first done.
    set (P := (∃ n, hash_rng n g ∗ sbounded_rng n f)%I).
    iMod (na_inv_alloc clutchRGS_nais _ rngN P with "[Hhash Hbounded]") as "#Hinv".
    { iNext. iExists O. iFrame. }
    iModIntro. iExists _. iFrame.
    iIntros (v1 v2) "!> (->&->)".
    clear K.
    rewrite /P.
    iApply (refines_na_inv with "[$Hinv]") ; auto ; iIntros "[HP Hclose]".
    rewrite refines_eq. iIntros (K) "HK Hown".
    iDestruct "HP" as (m) "(Hf&>Hsf)".
    rewrite timeless_hash_rng.
    iDestruct "Hf" as ">Hf".
    iApply wp_fupd.
    wp_apply (wp_hash_rng_flip_refine with "[$]"); first done.
    iIntros (b) "(Hhash&Hbounded&HK)".
    iMod ("Hclose" with "[-HK]").
    { iFrame. iExists _. iFrame. }
    iExists _. iFrame. eauto.
  Qed.

  Lemma bounded_hash_refinement :
    ⊢ REL init_bounded_rng << init_hash_rng : lrel_unit → (lrel_unit → lrel_bool).
  Proof.
    rel_arrow_val.
    iIntros (??) "(->&->)".
    rewrite refines_eq. iIntros (K) "HK Hown".
    iApply wp_fupd.
    wp_apply (wp_init_bounded_rng with "[//]").
    iIntros (g) "Hbounded".
    iMod (spec_init_hash_rng with "[$]") as (f) "(HK&Hhash)"; first done.
    set (P := (∃ n, bounded_rng n g ∗ shash_rng n f)%I).
    iMod (na_inv_alloc clutchRGS_nais _ rngN P with "[Hhash Hbounded]") as "#Hinv".
    { iNext. iExists O. iFrame. }
    iModIntro. iExists _. iFrame.
    iIntros (v1 v2) "!> (->&->)".
    clear K.
    rewrite /P.
    iApply (refines_na_inv with "[$Hinv]") ; auto ; iIntros "[HP Hclose]".
    rewrite refines_eq. iIntros (K) "HK Hown".
    iDestruct "HP" as (m) "(>Hf&Hsf)".
    rewrite timeless_shash_rng.
    iDestruct "Hsf" as ">Hsf".
    iApply wp_fupd.

    wp_apply (wp_bounded_rng_flip_refine with "[$]"); first done.
    iIntros (b) "(Hhash&Hbounded&HK)".
    iMod ("Hclose" with "[-HK]").
    { iFrame. iExists _. iFrame. }
    iExists _. iFrame. eauto.
  Qed.

End rng.
