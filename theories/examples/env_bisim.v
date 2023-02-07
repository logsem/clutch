(* Example taken from Sangiorgi and Vignudelli's "Environmental Bisimulations
   for Probabilistic Higher-order Languages".

NB: This example was mentioned as open problem in Aleš's thesis.
 *)

From stdpp Require Import namespaces.
From iris.base_logic Require Import invariants na_invariants.
From self.program_logic Require Import exec.
From self.prob_lang Require Import spec_ra notation proofmode primitive_laws spec_rules lang.
From self.logrel Require Import model rel_rules rel_tactics adequacy.
From self.typing Require Import types contextual_refinement soundness.
From self.prelude Require Import base.
Set Default Proof Using "Type*".

(* A diverging term. *)
Definition Ω : expr := (rec: "f" "x" := "f" "x") #().

Notation " e1 '⊕' e2 " := (if: flip #() then e1 else e2)%E (at level 80) : expr_scope.
Notation " e1 '⊕α' e2 " := (if: flip "α" then e1 else e2)%E (at level 80) : expr_scope.

Definition M : expr :=
  if: !"x" = #0 then "x" <- #1 ;; #true else Ω.

Definition N : expr :=
  if: !"x" = #0 then "x" <- #1 ;; #false else Ω.

Definition H : expr :=
  let: "x" := ref #0 in
  (λ:<>, M ⊕ N).

Definition H_with_tape : expr :=
  let: "x" := ref #0 in
  let: "α" := alloc in
  (λ:<>, M ⊕α N).

Definition K : expr :=
  let: "x" := ref #0 in
  (λ:<>, M) ⊕ (λ:<>, N).

Definition L : expr := (λ:<>, #true) ⊕ (λ:<>, #false).
Definition I : expr := (λ:<>, #true ⊕ #false).
Definition C := [CTX_AppR (λ: "f", "f" #() = "f" #())].
Definition c' : typed_ctx C ∅ (() → TBool) ∅ TBool.
  unshelve eapply (TPCTX_cons _ _ _ _ _ _ _ _ _ (TPCTX_nil _ _)).
  by repeat (eauto ; econstructor ; try simplify_map_eq).
Defined.

Theorem eager_lazy_equiv :
  (∅ ⊨ L =ctx= I : () → TBool) -> False.
Proof.
  intros [h1 _].
  set (σ := {| heap := ∅; tapes := ∅ |}).
  specialize (h1 C σ true c').
  revert h1.
  unfold I, L.
  simpl.
  rewrite lim_exec_val_prim_step.
  rewrite prim_step_or_val_no_val // /=.
Abort.


Section proofs.
  Context `{!prelogrelGS Σ}.

  Definition bisimN := nroot.@"bisim".

  Lemma H_with_tape_K_rel :
    ⊢ REL H_with_tape << K : lrel_unit → lrel_bool.
  Proof.
    rewrite /H_with_tape /K.
    rel_alloc_l x as "x". rel_alloc_r y as "y".
    rel_pures_l. rel_pures_r.
    rel_alloctape_l α as "α".
    rel_bind_r (flip _)%E.
    iApply (refines_couple_tape_flip with "[$α x y]"); [done|].
    iIntros (b) "α /=".
    rel_pures_l. rel_pures_r.
    set (P := ((α ↪ [b] ∗ x ↦ #0 ∗ y ↦ₛ #0) ∨ (α ↪ [] ∗ x ↦ #1 ∗ y ↦ₛ #1))%I).
    iApply (refines_na_alloc P bisimN).
    iSplitL. 1: iModIntro ; iLeft ; iFrame.
    iIntros "#Hinv".
    destruct b.
    (* Both cases are proven in *exactly* the same way. *)
    - rel_pures_r.
      rel_arrow_val.
      iIntros (??) "_".
      iApply (refines_na_inv with "[$Hinv]") ; [done|].
      iIntros "[[(α & x & y) | (α & x & y)] Hclose]".
      all: rel_pures_l ; rel_pures_r.
      + rel_flip_l. rel_pures_l. rel_load_r. rel_load_l. rel_pures_l. rel_pures_r.
        rel_store_l. rel_store_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]").
        iSplitL; [|rel_values].
        iRight. iModIntro. iFrame.
      + rel_load_r. rel_pures_r.
        rel_apply_l refines_flip_empty_l.
        iFrame. iIntros (b) "α".
        destruct b.
        (* Both cases are proven in *exactly* the same way. *)
        * rel_pures_l. rel_load_l. rel_pures_l.
          iApply (refines_na_close with "[- $Hclose]"). iSplitL.
          1: { iModIntro. iRight. iFrame. }
          rewrite refines_eq /refines_def.
          iIntros (?) "??".
          iLöb as "HH".
          wp_rec.
          now iApply ("HH" with "[$]").
        * rel_pures_l. rel_load_l. rel_pures_l.
          iApply (refines_na_close with "[- $Hclose]"). iSplitL.
          1: iModIntro ; iRight ; iFrame.
          rewrite refines_eq /refines_def.
          iIntros (?) "??".
          iLöb as "HH".
          wp_rec.
          now iApply ("HH" with "[$]").
    - rel_pures_r.
      rel_arrow_val.
      iIntros (??) "_".
      iApply (refines_na_inv with "[$Hinv]") ; [done|].
      iIntros "[[(α & x & y) | (α & x & y)] Hclose]".
      all: rel_pures_l ; rel_pures_r.
      + rel_flip_l. rel_pures_l. rel_load_r. rel_load_l. rel_pures_l. rel_pures_r.
        rel_store_l. rel_store_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]").
        iSplitL; [|rel_values].
        iRight. iModIntro. iFrame.
      + rel_load_r. rel_pures_r.
        rel_apply_l refines_flip_empty_l.
        iFrame. iIntros (b) "α".
        destruct b.
        (* Both cases are proven in *exactly* the same way. *)
        * rel_pures_l. rel_load_l. rel_pures_l.
          iApply (refines_na_close with "[- $Hclose]"). iSplitL.
          1: { iModIntro. iRight. iFrame. }
          rewrite refines_eq /refines_def.
          iIntros (?) "??".
          iLöb as "HH".
          wp_rec.
          now iApply ("HH" with "[$]").
        * rel_pures_l. rel_load_l. rel_pures_l.
          iApply (refines_na_close with "[- $Hclose]"). iSplitL.
          1: iModIntro ; iRight ; iFrame.
          rewrite refines_eq /refines_def.
          iIntros (?) "??".
          iLöb as "HH".
          wp_rec.
          now iApply ("HH" with "[$]").
  Qed.

  Lemma H_H_with_tape_rel :
    ⊢ REL H << H_with_tape : lrel_unit → lrel_bool.
  Proof.
    rewrite /H_with_tape /H.
    rel_alloc_l x as "x". rel_alloc_r y as "y".
    rel_pures_l. rel_pures_r.
    rel_alloctape_r α as "α".
    rel_pures_r.
    set (P := ((α ↪ₛ [] ∗ x ↦ #0 ∗ y ↦ₛ #0) ∨ (α ↪ₛ [] ∗ x ↦ #1 ∗ y ↦ₛ #1))%I).
    iApply (refines_na_alloc P bisimN).
    iSplitL. 1: iModIntro ; iLeft ; iFrame.
    iIntros "#Hinv".
    rel_arrow_val.
    iIntros (??) "_".
    iApply (refines_na_inv with "[$Hinv]") ; [done|].
    iIntros "[[(α & x & y) | (α & x & y)] Hclose]".
    all: rel_pures_l ; rel_pures_r.
    + rel_bind_l (Flip _). rel_bind_r (Flip _).
      rel_apply_l refines_couple_flips_r.
      iFrame ; iIntros (b) "α".
      destruct b.
      * rel_pures_l. rel_pures_r. rel_load_l. rel_load_r. rel_pures_l. rel_pures_r.
        rel_store_l. rel_store_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]").
        iSplitL; [|rel_values].
        iRight ; iModIntro ; iFrame.
      * rel_pures_l. rel_pures_r. rel_load_l. rel_load_r. rel_pures_l. rel_pures_r.
        rel_store_l. rel_store_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]").
        iSplitL; [|rel_values].
        iRight ; iModIntro ; iFrame.
    + rel_bind_l (Flip _). rel_bind_r (Flip _).
      rel_apply_l refines_couple_flips_r.
      iFrame ; iIntros (b) "α".
      destruct b.
      * rel_pures_l. rel_pures_r. rel_load_l. rel_load_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]"). iSplitL.
        1: iModIntro ; iRight ; iFrame.
        rewrite refines_eq /refines_def.
        iIntros (?) "??".
        iLöb as "HH".
        wp_rec.
        now iApply ("HH" with "[$]").
      * rel_pures_l. rel_pures_r. rel_load_l. rel_load_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]"). iSplitL.
        1: iModIntro ; iRight ; iFrame.
        rewrite refines_eq /refines_def.
        iIntros (?) "??".
        iLöb as "HH".
        wp_rec.
        now iApply ("HH" with "[$]").
  Qed.

  Lemma K_H_with_tape_rel :
    ⊢ REL K << H_with_tape : lrel_unit → lrel_bool.
  Proof.
    rewrite /H_with_tape /K.
    rel_alloc_l x as "x". rel_alloc_r y as "y".
    rel_pures_l. rel_pures_r.
    rel_alloctape_r α as "α".
    rel_bind_l (flip _)%E.
    iApply (refines_couple_flip_tape with "[$α x y]").
    iIntros (b) "α /=".
    rel_pures_l. rel_pures_r.
    set (P := ((α ↪ₛ [b] ∗ x ↦ #0 ∗ y ↦ₛ #0) ∨ (α ↪ₛ [] ∗ x ↦ #1 ∗ y ↦ₛ #1))%I).
    iApply (refines_na_alloc P bisimN).
    iSplitL. 1: iModIntro ; iLeft ; iFrame.
    iIntros "#Hinv".
    destruct b.
    (* Both cases are proven in *exactly* the same way. *)
    - rel_pures_l.
      rel_arrow_val.
      iIntros (??) "_".
      iApply (refines_na_inv with "[$Hinv]") ; [done|].
      iIntros "[[(α & x & y) | (α & x & y)] Hclose]".
      all: rel_pures_l ; rel_pures_r.
      + rel_flip_r. rel_pures_r. rel_load_r. rel_load_l. rel_pures_l. rel_pures_r.
        rel_store_l. rel_store_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]").
        iSplitL; [|rel_values].
        iRight. iModIntro. iFrame.
      + rel_load_l.
        rel_apply_r refines_flip_empty_r => // ;
        iFrame ; iIntros (b) "α". rel_pures_l.
        destruct b.
        (* Both cases are proven in *exactly* the same way. *)
        all: rel_pures_r ; rel_load_r ; rel_pures_r ;
          iApply (refines_na_close with "[- $Hclose]") ; iSplitL ;
          [iModIntro ; iRight ; iFrame|] ;
          rewrite refines_eq /refines_def ; iIntros (?) "??" ;
          iLöb as "HH" ; wp_rec ; now iApply ("HH" with "[$]").
    - rel_pures_l.
      rel_arrow_val.
      iIntros (??) "_".
      iApply (refines_na_inv with "[$Hinv]") ; [done|].
      iIntros "[[(α & x & y) | (α & x & y)] Hclose]".
      all: rel_pures_l ; rel_pures_r.
      + rel_flip_r. rel_pures_r. rel_load_r. rel_load_l. rel_pures_l. rel_pures_r.
        rel_store_l. rel_store_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]").
        iSplitL; [|rel_values].
        iRight. iModIntro. iFrame.
      + rel_load_l.
        rel_apply_r refines_flip_empty_r. 1: auto.
        iFrame. iIntros (b) "α". rel_pures_l.
        destruct b.
        (* Both cases are proven in *exactly* the same way. *)
        all: rel_pures_r ; rel_load_r ; rel_pures_r ;
          iApply (refines_na_close with "[- $Hclose]") ; iSplitL ;
          [iModIntro ; iRight ; iFrame|] ;
          rewrite refines_eq /refines_def ; iIntros (?) "??" ;
          iLöb as "HH" ; wp_rec ; now iApply ("HH" with "[$]").
  Qed.

  Lemma H_with_tape_H_rel :
    ⊢ REL H_with_tape << H : lrel_unit → lrel_bool.
  Proof.
    rewrite /H_with_tape /H.
    rel_alloc_l x as "x". rel_alloc_r y as "y".
    rel_pures_l. rel_pures_r.
    rel_alloctape_l α as "α".
    rel_pures_r.
    set (P := ((α ↪ [] ∗ x ↦ #0 ∗ y ↦ₛ #0) ∨ (α ↪ [] ∗ x ↦ #1 ∗ y ↦ₛ #1))%I).
    iApply (refines_na_alloc P bisimN).
    iSplitL. 1: iModIntro ; iLeft ; iFrame.
    iIntros "#Hinv".
    rel_arrow_val.
    iIntros (??) "_".
    iApply (refines_na_inv with "[$Hinv]") ; [done|].
    iIntros "[[(α & x & y) | (α & x & y)] Hclose]".
    all: rel_pures_l ; rel_pures_r.
    + rel_bind_l (Flip _). rel_bind_r (Flip _).
      rel_apply_l refines_couple_flips_l.
      iFrame ; iIntros (b) "α".
      destruct b ;
        rel_pures_l ; rel_pures_r ; rel_load_l ; rel_load_r ; rel_pures_l ; rel_pures_r ;
        rel_store_l ; rel_store_r ; rel_pures_l ; rel_pures_r ;
        iApply (refines_na_close with "[- $Hclose]").
      all: iSplitL; [|rel_values] ;
        iRight ; iModIntro ; iFrame.
    + rel_bind_l (Flip _). rel_bind_r (Flip _).
      rel_apply_l refines_couple_flips_l.
      iFrame ; iIntros (b) "α".
      destruct b ;
        rel_pures_l ; rel_pures_r ; rel_load_l ; rel_load_r ; rel_pures_l ; rel_pures_r ;
        iApply (refines_na_close with "[- $Hclose]").
        all: iSplitL ; [iModIntro ; iRight ; iFrame|] ;
          rewrite refines_eq /refines_def ; iIntros (?) "??" ;
          iLöb as "HH" ; wp_rec ; now iApply ("HH" with "[$]").
  Qed.

End proofs.

Theorem H_K_refinement :
  ∅ ⊨ H ≤ctx≤ K : () → TBool.
Proof.
  eapply ctx_refines_transitive.
  - eapply (refines_sound prelogrelΣ).
    intros. simpl. apply: H_H_with_tape_rel.
  - eapply (refines_sound prelogrelΣ).
    intros. apply: H_with_tape_K_rel.
Qed.

Theorem K_H_refinement :
  ∅ ⊨ K ≤ctx≤ H : () → TBool.
Proof.
  eapply ctx_refines_transitive.
  - eapply (refines_sound prelogrelΣ).
    intros. simpl. apply: K_H_with_tape_rel.
  - eapply (refines_sound prelogrelΣ).
    intros. apply: H_with_tape_H_rel.
Qed.

Theorem eager_lazy_equiv :
  ∅ ⊨ H =ctx= K : () → TBool.
Proof.
  split.
  - apply H_K_refinement.
  - apply K_H_refinement.
Qed.
