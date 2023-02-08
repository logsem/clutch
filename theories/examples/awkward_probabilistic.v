(*
An example in Sec. 6 of https://cs.au.dk/~birke/papers/step-probability-conf.pdf

Maybe this is another example, relying on local state encapsulation
  tau = (1 - > 1) -> 1
  e1 = let x = ref (flip ()) in \f. f(); !x
  e2 = \f. f(); flip()
show e1 related to e2 at tau.

Or how about a variant of the above, but where e1 is let x = ref (flip ()) in \f. (x := negate (!x); f(); !x). ?

NB: e1 and e2 are equivalent only if executed only once. We prove the
equivalence by adding a guard that returns `NONE` after the first invocation.
*)

From stdpp Require Import namespaces.
From self.prob_lang Require Import lang notation spec_ra proofmode primitive_laws.
From self.logrel Require Import model rel_rules rel_tactics compatibility.
From self.prelude Require Import base.
Set Default Proof Using "Type*".

Section proofs.
  Context `{!prelogrelGS Σ}.

  Definition awkwardN := nroot.@"awkward".

  Definition shootN := nroot .@ "shootN".

  Lemma refinement_prob :
    ⊢ REL
      (let: "α" := AllocTape in
       let: "callable" := ref #true in
       (λ: "f", if: ! "callable" then "callable" <- #false ;; "f" #() ;; SOME (flip "α") else NONE))
    <<
      (let: "x" := ref (flip #()) in
       let: "callable" := ref #true in
       (λ: "f", if: ! "callable" then "callable" <- #false ;; "f" #() ;; SOME (!"x") else NONE))
    : (() → ()) → lrel_sum lrel_unit lrel_bool.
  Proof.
    rel_alloctape_l α as "α".
    rel_bind_r (flip _)%E.
    iApply (refines_couple_tape_flip with "[$α]"); [done|].
    iIntros (b) "Hα /=".
    rel_pures_l.
    rel_alloc_r x as "Hx". rel_pures_r.
    rel_alloc_l cl as "Hcl". rel_pures_l.
    rel_alloc_r cr as "Hcr". rel_pures_r.
    set (P := ((x ↦ₛ #b ∗ α ↪ [b] ∗ cl ↦ #true ∗ cr ↦ₛ #true ∨ cl ↦ #false ∗ cr ↦ₛ #false))%I).
    iApply (refines_na_alloc P shootN).
    iSplitL ; [ iFrame ; iLeft ; iFrame |].
    iIntros "#Hinv".
    iApply refines_arrow.
    iIntros "!#" (f1 f2) "#Hf".
    rel_pures_l. rel_pures_r.
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "(>[(Hx & Hα & Hcl & Hcr) | (Hx & Hcr)] & Hclose)".
    - rel_load_l. rel_pures_l. rel_store_l. rel_pures_l.
      rel_load_r. rel_pures_r. rel_store_r. rel_pures_r.
      iApply (refines_na_close with "[-$Hclose]"). iSplitR "Hα Hx".
      { iModIntro. iFrame. iRight. iFrame. }
      iApply (refines_seq with "[Hf]"); auto.
      + iApply (refines_app with "Hf").
        rel_values.
      + rel_load_r.
        rel_flip_l. rel_pures_l. rel_pures_r.
        rel_values. iModIntro.
        unfold lrel_sum, lrel_car.
        iExists (#b). iExists (#b). simpl. iRight.
        eauto.
    - rel_load_l. rel_pures_l.
      rel_load_r. rel_pures_r.
      iApply (refines_na_close with "[-$Hclose]"). iSplitL.
      { iModIntro. iFrame. iRight; by iFrame. }
      rel_values.
      rewrite /lrel_sum/lrel_car/=.
      iModIntro. iExists _. iExists _. iLeft. eauto.
  Qed.

  (* The following is an example of a contextual equivalence we expect to hold
     but cannot currently prove conveniently using our relational logic. The
     issue is that we cannot determine, ahead of time, which flip to couple
     with in the rhs.

     One is tempted to argue that it should be sufficient to find a coupling
     the for any given call to the lhs and rhs closures, and couple `α` and
     `β`.

     But even though `x` is local to `f`, we cannot argue the coupling of `α`
     and `β` will be propagated to `x`. The reason is that `f` may be
     instantiated with the a function calling the rhs, which would sample a new
     bit to `β` and modify `x`. Of course this shouldn't matter since the newly
     sampled bit would follow the same distribution, but we cannot exploit this
     observation in the formal argument. *)
  Lemma refinement_prob_resample :
    ⊢ REL
      (λ: "f", let: "α" := alloc in
               "f" #() ;; flip "α")
    <<
      (let: "x" := ref NONE in
       (λ: "f", let: "β" := alloc in
                let: "b" := flip "β" in
                "x" <- SOME "b" ;;
                "f" #() ;;
                !"x" ))
    : (() → ()) → lrel_int.
  Proof.
    rel_pures_r. rel_alloc_r x as "Hx". rel_pures_r.
    rel_pures_l.
    set (P := (x ↦ₛ NONEV ∨ ∃ (b : bool), (x ↦ₛ SOMEV #b (* ∗ β ↪ₛ [] ∗ α ↪ [] *)) (* ∨ (x ↦ₛ #b ∗ β ↪ₛ [] ∗ α ↪ [b]) *))%I).
    iApply (refines_na_alloc P shootN).
    iSplitL ; [ try iExists _ ; try iLeft ; iFrame |].
    iIntros "#Hinv".
    iApply refines_arrow_val.
    iIntros "!#" (f1 f2) "#Hf".
    rel_alloctape_r β as "β". rel_pures_r.
    rel_alloctape_l α as "α".
    rel_pures_l. rel_pures_r.
    iApply (refines_na_inv with "[-$Hinv]"); [done|].
    try iIntros "(>(%b & b ) & Hclose)" ; (* | (b & β & α) *)
    try iIntros "(> [b | (%b & b )] & Hclose)". (* | (b & β & α) *)
    - iApply refines_couple_tapes ; auto ; iFrame ;
        iIntros (b) "(β & α)" => /=.
      rel_flip_r ; rel_store_r ; rel_pures_r.
      (* `x` points to `b`, but calling `f2` may not preserve this. *)
      iApply (refines_na_close with "[-$Hclose]") ; iSplitL "b".
      { iModIntro. iRight. iExists _. iFrame. }
      iApply (refines_seq with "[Hf]"); auto. 1: iApply "Hf" => //.
      rel_flip_l.
Abort.

End proofs.
