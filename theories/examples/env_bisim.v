(* Example taken from Sangiorgi and Vignudelli's "Environmental Bisimulations
   for Probabilistic Higher-order Languages".

   NB: This example was mentioned as open problem in Aleš Bizjak's thesis.
 *)

From clutch Require Export clutch lib.flip.
Set Default Proof Using "Type*".

(* A diverging term. *)
Definition Ω : expr := (rec: "f" "x" := "f" "x") #().

Notation " e1 '⊕' e2 " := (if: flip then e1 else e2)%E (at level 80) : expr_scope.
Notation " e1 '⊕α' e2 " := (if: flipL "α" then e1 else e2)%E (at level 80) : expr_scope.

Definition M : expr :=
  if: !"x" = #0 then "x" <- #1 ;; #true else Ω.

Definition N : expr :=
  if: !"x" = #0 then "x" <- #1 ;; #false else Ω.

Definition H : expr :=
  let: "x" := ref #0 in
  (λ:<>, M ⊕ N).

Definition H_with_tape : expr :=
  let: "x" := ref #0 in
  let: "α" := alloc #1%nat in
  (λ:<>, M ⊕α N).

Definition K : expr :=
  let: "x" := ref #0 in
  (λ:<>, M) ⊕ (λ:<>, N).

Definition L : expr := (λ:<>, #true) ⊕ (λ:<>, #false).
Definition I : expr := (λ:<>, #true ⊕ #false).

(* L and I are not, in general, contextually equivalent.
   The following (well-typed) context distinguishes them. *)
Definition C := [CTX_AppR (λ: "f", "f" #() = "f" #())].
Fact c' : typed_ctx C ∅ (() → TBool) ∅ TBool.
  unshelve eapply (TPCTX_cons _ _ _ _ _ _ _ _ _ (TPCTX_nil _ _)).
  by repeat (eauto ; econstructor ; try simplify_map_eq).
Qed.

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
  Context `{!clutchRGS Σ}.

  Definition bisimN := nroot.@"bisim".

  Lemma H_with_tape_K_rel :
    ⊢ REL H_with_tape << K : lrel_unit → lrel_bool.
  Proof.
    rewrite /H_with_tape /K.
    rel_alloc_l x as "x". rel_alloc_r y as "y".
    rel_pures_l. rel_pures_r.
    rel_allocBtape_l α as "α".
    rel_apply_r (refines_couple_tape_flip with "[$α x y]"); [done|].
    iIntros (b) "α /=".
    rel_pures_l. rel_pures_r.
    set (P := ((α ↪B [b] ∗ x ↦ #0 ∗ y ↦ₛ #0) ∨ (α ↪B [] ∗ x ↦ #1 ∗ y ↦ₛ #1))%I).
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
      + rel_flipL_l. rel_pures_l. rel_load_r. rel_load_l. rel_pures_l. rel_pures_r.
        rel_store_l. rel_store_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]").
        iSplitL; [|rel_values].
        iRight. iModIntro. iFrame.
      + rel_load_r. rel_pures_r.
        rel_apply_l refines_flipL_empty_l.
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
      + rel_flipL_l. rel_pures_l. rel_load_r. rel_load_l. rel_pures_l. rel_pures_r.
        rel_store_l. rel_store_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]").
        iSplitL; [|rel_values].
        iRight. iModIntro. iFrame.
      + rel_load_r. rel_pures_r.
        rel_apply_l refines_flipL_empty_l.
        iFrame. iIntros (b) "α".
        destruct b.
        (* Both cases are proven in *exactly* the same way. *)
        * rel_pures_l. rel_load_l. rel_pures_l.
          iApply (refines_na_close with "[- $Hclose]"). iSplitL.
          1: { iModIntro. iRight. iFrame. }
          assert (lrel_bool = (interp TBool [])%lrel) as -> by auto.
          iApply refines_typed.
          tychk.
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
    rel_allocBtape_r α as "α".
    rel_pures_r.
    set (P := ((α ↪ₛB [] ∗ x ↦ #0 ∗ y ↦ₛ #0) ∨ (α ↪ₛB [] ∗ x ↦ #1 ∗ y ↦ₛ #1))%I).
    iApply (refines_na_alloc P bisimN).
    iSplitL. 1: iModIntro ; iLeft ; iFrame.
    iIntros "#Hinv".
    rel_arrow_val.
    iIntros (??) "_".
    iApply (refines_na_inv with "[$Hinv]") ; [done|].
    iIntros "[[(α & x & y) | (α & x & y)] Hclose]".
    all: rel_pures_l ; rel_pures_r.
    + rel_bind_l flip. rel_bind_r (flipL _).
      rel_apply_l refines_couple_flip_flipL.
      iFrame ; iIntros "!>" (b) "α".
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
    + rel_bind_l flip. rel_bind_r (flipL _).
      rel_apply_l refines_couple_flip_flipL.
      iFrame ; iIntros "!>" (b) "α".
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
    rel_allocBtape_r α as "α".
    rel_apply_l (refines_couple_flip_tape with "[$α x y]").
    iIntros "!>" (b) "α /=".
    rel_pures_l. rel_pures_r.
    set (P := ((α ↪ₛB [b] ∗ x ↦ #0 ∗ y ↦ₛ #0) ∨ (α ↪ₛB [] ∗ x ↦ #1 ∗ y ↦ₛ #1))%I).
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
      + rel_flipL_r. rel_pures_r. rel_load_r. rel_load_l. rel_pures_l. rel_pures_r.
        rel_store_l. rel_store_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]").
        iSplitL; [|rel_values].
        iRight. iModIntro. iFrame.
      + rel_load_l.
        rel_apply_r refines_flipL_empty_r; [done|]. 
        iFrame. iIntros (b) "α". rel_pures_l.
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
      + rel_flipL_r. rel_pures_r. rel_load_r. rel_load_l. rel_pures_l. rel_pures_r.
        rel_store_l. rel_store_r. rel_pures_l. rel_pures_r.
        iApply (refines_na_close with "[- $Hclose]").
        iSplitL; [|rel_values].
        iRight. iModIntro. iFrame.
      + rel_load_l.
        rel_apply_r refines_flipL_empty_r; [done|].
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
    rel_allocBtape_l α as "α".
    rel_pures_r.
    set (P := ((α ↪B [] ∗ x ↦ #0 ∗ y ↦ₛ #0) ∨ (α ↪B [] ∗ x ↦ #1 ∗ y ↦ₛ #1))%I).
    iApply (refines_na_alloc P bisimN).
    iSplitL. 1: iModIntro ; iLeft ; iFrame.
    iIntros "#Hinv".
    rel_arrow_val.
    iIntros (??) "_".
    iApply (refines_na_inv with "[$Hinv]") ; [done|].
    iIntros "[[(α & x & y) | (α & x & y)] Hclose]".
    all: rel_pures_l ; rel_pures_r.
    + rel_bind_l (flipL _). rel_bind_r flip.
      rel_apply_l refines_couple_flipL_flip; [solve_ndisj|].
      iFrame ; iIntros "!>" (b) "α".
      destruct b ;
        rel_pures_l ; rel_pures_r ; rel_load_l ; rel_load_r ; rel_pures_l ; rel_pures_r ;
        rel_store_l ; rel_store_r ; rel_pures_l ; rel_pures_r ;
        iApply (refines_na_close with "[- $Hclose]").
      all: iSplitL; [|rel_values] ;
        iRight ; iModIntro ; iFrame.
    + rel_bind_l (flipL _). rel_bind_r flip.
      rel_apply_l refines_couple_flipL_flip; [solve_ndisj|].
      iFrame ; iIntros "!>" (b) "α".
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
  - eapply (refines_sound clutchRΣ).
    intros. simpl. apply: H_H_with_tape_rel.
  - eapply (refines_sound clutchRΣ).
    intros. apply: H_with_tape_K_rel.
Qed.

Theorem K_H_refinement :
  ∅ ⊨ K ≤ctx≤ H : () → TBool.
Proof.
  eapply ctx_refines_transitive.
  - eapply (refines_sound clutchRΣ).
    intros. simpl. apply: K_H_with_tape_rel.
  - eapply (refines_sound clutchRΣ).
    intros. apply: H_with_tape_H_rel.
Qed.

Theorem H_K_equiv :
  ∅ ⊨ H =ctx= K : () → TBool.
Proof.
  split.
  - apply H_K_refinement.
  - apply K_H_refinement.
Qed.
