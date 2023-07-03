From clutch Require Export clutch lib.flip. 
Set Default Proof Using "Type*".

(** The lazy/eager coins, without tapes *)
Definition lazy : expr :=
  let: "s" := ref NONEV in
  λ: <>,
    match: !"s" with
    | NONE => let: "b" := flip in
              "s" <- SOME "b" ;;
              "b"
    | SOME "b" => "b"
    end.

Definition eager : expr :=
  let: "b" := flip in
  λ: <>, "b".

(** An intermediate version of [lazy] that uses a tape to allow presampling
    bits during the proof *)
Definition lazy_with_tape : expr :=
  let: "α" := allocB in
  let: "s" := ref NONEV in
  λ: <>,
    match: !"s" with
    | NONE => let: "b" := flipL "α" in
              "s" <- SOME "b" ;;
              "b"
    | SOME "b" => "b"
    end.

Section logical_ref.
  Context `{!clutchRGS Σ}.

  Definition coinN := nroot.@"coins".

  (** lazy << lazy_with_tape << eager *)
  Lemma lazy_lazy_with_tape_rel :
    ⊢ REL lazy << lazy_with_tape : () → lrel_bool.
  Proof.
    rewrite /lazy /lazy_with_tape.
    rel_alloc_l l as "Hl".

    rel_pure_l.
    rel_pure_l.
    
    rel_pures_l.
    rel_allocBtape_r α as "Hα".
    rel_pures_r.
    rel_alloc_r l' as "Hl'".
    rel_pures_r.
    set (P := (α ↪ₛB [] ∗ (l ↦ NONEV ∗ l' ↦ₛ NONEV ∨
               ∃ b : bool, l ↦ SOMEV #b ∗ l' ↦ₛ SOMEV #b))%I).
    iApply (refines_na_alloc P coinN).
    iSplitL.
    { iFrame. iLeft. iFrame. }
    iIntros "#Hinv".
    rel_arrow_val.
    iIntros (?? [-> ->]).
    rel_pures_l.
    rel_pure_r.
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "[(Hα & [[Hl Hl'] | >[%b [Hl Hl']]]) Hclose]".
    - rel_load_l. rel_pures_l.
      rel_load_r. rel_pures_r.
      rel_apply (refines_couple_flip_flipL with "[-$Hα]").
      iIntros "!>" (b) "Hα /=".
      rel_pures_l. rel_store_l. rel_pures_l.
      rel_pures_r. rel_store_r. rel_pures_r.
      iApply (refines_na_close with "[- $Hclose $Hα]");
      iSplitL. 2: rel_values.
      iRight. iModIntro. iExists _. iFrame.
    - rel_load_l. rel_pures_l.
      rel_load_r. rel_pures_r.
      iApply (refines_na_close with "[- $Hclose $Hα]").
      iSplitL; [|rel_values].
      iRight. iModIntro. iExists _. iFrame.
  Qed.

  Lemma lazy_with_tape_eager_rel :
    ⊢ REL lazy_with_tape << eager : () → lrel_bool.
  Proof.
    rewrite /lazy_with_tape /eager.
    rel_allocBtape_l α as "Hα".
    rel_pures_l.
    rel_bind_r flip.
    iApply (refines_couple_tape_flip with "[$Hα]"); [solve_ndisj|done|].
    iIntros (b) "Hα /=".
    rel_pures_r.
    rel_alloc_l l as "Hl". rel_pures_l.
    set (P := ((α ↪B [b] ∗ l ↦ NONEV) ∨ (l ↦ SOMEV #b))%I).
    iApply (refines_na_alloc P coinN).
    iSplitL.
    { iModIntro. iLeft. iFrame. }
    iIntros "#Hinv".
    rel_arrow_val.
    iIntros (??) "_".
    rel_pures_l. rel_pures_r.
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "[[[Hα Hl] | Hl] Hclose]".
    - rel_load_l. rel_pures_l.
      rel_flipL_l. rel_pures_l.
      rel_store_l. rel_pures_l.
      iApply (refines_na_close with "[- $Hclose]").
      iSplitL; [|rel_values].
      iModIntro. iRight. iFrame.
    - rel_load_l. rel_pures_l.
      iApply (refines_na_close with "[- $Hclose]").
      iSplitL; [|rel_values].
      iModIntro. iRight. iFrame.
  Qed.

  (** eager << lazy_with_tape << lazy *)
  Lemma eager_lazy_with_tape_rel :
    ⊢ REL eager << lazy_with_tape : () → lrel_bool.
  Proof.
    rewrite /lazy_with_tape /eager.
    rel_allocBtape_r α as "Hα". rel_pures_r.
    rel_bind_l flip.
    rel_apply_l (refines_couple_flip_tape with "[$Hα]").
    iIntros "!>" (b) "Hα /=".
    rel_pures_r.
    rel_alloc_r l as "Hl". rel_pures_r.
    set (P := ((α ↪ₛB [b] ∗ l ↦ₛ NONEV) ∨ (l ↦ₛ SOMEV #b))%I).
    iApply (refines_na_alloc P coinN).
    iSplitL.
    { iModIntro. iLeft. iFrame. }
    iIntros "#Hinv".
    rel_arrow_val.
    iIntros (??) "_".
    rel_pures_l. rel_pures_r.
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "[[>[Hα Hl] | >Hl] Hclose]".
    - rel_load_r. rel_pures_r.
      rel_flipL_r. rel_pures_r.
      rel_store_r. rel_pures_r.
      iApply (refines_na_close with "[- $Hclose]").
      iSplitL; [|rel_values].
      iModIntro. iRight. iFrame.
    - rel_load_r. rel_pures_r.
      iApply (refines_na_close with "[- $Hclose]").
      iSplitL; [|rel_values].
      iModIntro. iRight. iFrame.
  Qed.

  Lemma lazy_with_tape_lazy_rel :
    ⊢ REL lazy_with_tape << lazy : () → lrel_bool.
  Proof.
    rewrite /lazy /lazy_with_tape.
    rel_alloc_r l' as "Hl'". rel_pures_l.
    rel_allocBtape_l α as "Hα". rel_pures_l.
    rel_alloc_l l as "Hl". rel_pures_l.
    set (P := (α ↪B [] ∗ (l ↦ NONEV ∗ l' ↦ₛ NONEV ∨
               ∃ (b : bool), l ↦ SOMEV #b ∗ l' ↦ₛ SOMEV #b))%I).
    iApply (refines_na_alloc P coinN).
    iSplitL.
    { iFrame. iLeft. iFrame. }
    iIntros "#Hinv".
    rel_arrow_val.
    iIntros (?? [-> ->]).
    rel_pures_l.
    rel_pure_r.
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "[(Hα & [[Hl Hl'] | >[%b [Hl Hl']]]) Hclose]".
    - rel_load_l. rel_pures_l.
      rel_load_r. rel_pures_r.
      rel_bind_l (flipL _)%E.
      rel_bind_r flip.
      iApply (refines_couple_flipL_flip with "[-$Hα]"); [solve_ndisj|].
      iIntros "!>" (b) "Hα /=".
      rel_pures_l. rel_store_l. rel_pures_l.
      rel_pures_r. rel_store_r. rel_pures_r.
      iApply (refines_na_close with "[- $Hclose $Hα]").
      iSplitL; [|rel_values].
      iRight. iModIntro. iExists _. iFrame.
    - rel_load_l. rel_pures_l.
      rel_load_r. rel_pures_r.
      iApply (refines_na_close with "[- $Hclose $Hα]").
      iSplitL; [|rel_values].
      iRight. iModIntro. iExists _. iFrame.
  Qed.

End logical_ref.

Theorem lazy_eager_refinement :
  ∅ ⊨ lazy ≤ctx≤ eager : () → TBool.
Proof.
  eapply ctx_refines_transitive.
  - eapply (refines_sound clutchRΣ).
    intros. apply: lazy_lazy_with_tape_rel.
  - eapply (refines_sound clutchRΣ).
    intros. apply: lazy_with_tape_eager_rel.
Qed.

Theorem eager_lazy_refinement :
  ∅ ⊨ eager ≤ctx≤ lazy : () → TBool.
Proof.
  eapply ctx_refines_transitive.
  - eapply (refines_sound clutchRΣ).
    intros. apply: eager_lazy_with_tape_rel.
  - eapply (refines_sound clutchRΣ).
    intros. apply: lazy_with_tape_lazy_rel.
Qed.

Theorem eager_lazy_equiv :
  ∅ ⊨ lazy =ctx= eager : () → TBool.
Proof.
  split.
  - apply lazy_eager_refinement.
  - apply eager_lazy_refinement.
Qed.
