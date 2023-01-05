From stdpp Require Import namespaces.
From iris.base_logic Require Import invariants na_invariants.
From self.prob_lang Require Import notation proofmode primitive_laws spec_rules.
From self.logrel Require Import model rel_rules rel_tactics.
From self.typing Require Import soundness.
From self.prelude Require Import base.
Set Default Proof Using "Type*".

(** The lazy/eager coins, without tapes *)
Definition lazy : expr :=
  let: "s" := ref NONEV in
  λ: <>,
    match: !"s" with
    | NONE => let: "b" := flip #() in
              "s" <- SOME "b" ;;
              "b"
    | SOME "b" => "b"
    end.

Definition eager : expr :=
  let: "b" := flip #() in
  λ: <>, "b".

(** An intetermedaite version of [lazy] that uses a tape to allow presampling
    bits during the proof *)
Definition lazy_with_tape : expr :=
  let: "α" := alloc in
  let: "s" := ref NONEV in
  λ: <>,
    match: !"s" with
    | NONE => let: "b" := flip "α" in
              "s" <- SOME "b" ;;
              "b"
    | SOME "b" => "b"
    end.

Section logical_ref.
  Context `{!prelogrelGS Σ}.

  Definition coinN := nroot.@"coins".

  (** lazy << lazy_with_tape << eager *)
  Lemma lazy_lazy_with_tape_rel :
    ⊢ REL lazy << lazy_with_tape : () → lrel_bool.
  Proof.
    rewrite /lazy /lazy_with_tape.
    rel_alloc_l l as "Hl".
    rel_pures_l.
    rel_alloctape_r α as "Hα".
    rel_pures_r.
    rel_alloc_r l' as "Hl'".
    rel_pures_r.
    set (P := (α ↪ₛ [] ∗ (l ↦ NONEV ∗ l' ↦ₛ NONEV ∨
                  ∃ (b: bool), l ↦ SOMEV #b ∗ l' ↦ₛ SOMEV #b))%I).
    iMod (na_inv_alloc prelogrelGS_nais _ coinN P with "[-]") as "#Hinv".
    { iFrame. iLeft. iFrame. }
    rel_arrow_val.
    iIntros (?? [-> ->]).
    rel_pures_l.
    rel_pure_r.
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "[(Hα & [[Hl Hl'] | >[%b [Hl Hl']]]) Hclose]".
    - rel_load_l. rel_pures_l.
      rel_load_r. rel_pures_r.
      rel_bind_l (flip _)%E.
      rel_bind_r (flip _)%E.
      iApply (refines_couple_flips_r with "[-$Hα]"); [solve_ndisj|].
      iIntros (b) "Hα /=".
      rel_pures_l. rel_store_l. rel_pures_l.
      rel_pures_r. rel_store_r. rel_pures_r.
      iApply (refines_na_close with "[- $Hclose $Hα]").
      iSplitR; [rel_values|].
      iRight. iModIntro. iExists _. iFrame.
    - rel_load_l. rel_pures_l.
      rel_load_r. rel_pures_r.
      iApply (refines_na_close with "[- $Hclose $Hα]").
      iSplitR; [rel_values|].
      iRight. iModIntro. iExists _. iFrame.
  Qed.

  Lemma lazy_with_tape_eager_rel :
    ⊢ REL lazy_with_tape << eager : () → lrel_bool.
  Proof.
    rewrite /lazy_with_tape /eager.
    rel_alloctape_l α as "Hα". rel_pures_l.
    rel_bind_r (flip _)%E.
    iApply (refines_couple_tape_flip with "[$Hα]"); [done|done|].
    iIntros (b) "Hα /=".
    rel_pures_r.
    rel_alloc_l l as "Hl". rel_pures_l.
    set (P := ((α ↪ [b] ∗ l ↦ NONEV) ∨ (α ↪ [] ∗ l ↦ SOMEV #b))%I).
    iMod (na_inv_alloc prelogrelGS_nais _ coinN P with "[-]") as "#Hinv".
    { iModIntro. iLeft. iFrame. }
    rel_arrow_val.
    iIntros (??) "_".
    rel_pures_l. rel_pures_r.
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "[[[Hα Hl] | [Hα Hl]] Hclose]".
    - rel_load_l. rel_pures_l.
      rel_flip_l. rel_pures_l.
      rel_store_l. rel_pures_l.
      iApply (refines_na_close with "[- $Hclose]").
      iSplitR.
      { iModIntro. rel_values. }
      iModIntro. iRight. iFrame.
    - rel_load_l. rel_pures_l.
      iApply (refines_na_close with "[- $Hclose]").
      iSplitR.
      { iModIntro. rel_values. }
      iModIntro. iRight. iFrame.
  Qed.

  (** eager << lazy_with_tape << lazy *)
  Lemma eager_lazy_with_tape_rel :
    ⊢ REL eager << lazy_with_tape : () → lrel_bool.
  Proof.
    rewrite /lazy_with_tape /eager.
    rel_alloctape_r α as "Hα". rel_pures_r.
    rel_bind_l (flip _)%E.
    iApply (refines_couple_flip_tape with "[$Hα]"); [done|].
    iIntros (b) "Hα /=".
    rel_pures_r.
    rel_alloc_r l as "Hl". rel_pures_r.
    set (P := ((α ↪ₛ [b] ∗ l ↦ₛ NONEV) ∨ (α ↪ₛ [] ∗ l ↦ₛ SOMEV #b))%I).
    iMod (na_inv_alloc prelogrelGS_nais _ coinN P with "[-]") as "#Hinv".
    { iModIntro. iLeft. iFrame. }
    rel_arrow_val.
    iIntros (??) "_".
    rel_pures_l. rel_pures_r.
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "[[>[Hα Hl] | >[Hα Hl]] Hclose]".
    - rel_load_r. rel_pures_r.
      rel_flip_r. rel_pures_r.
      rel_store_r. rel_pures_r.
      iApply (refines_na_close with "[- $Hclose]").
      iSplitR.
      { iModIntro. rel_values. }
      iModIntro. iRight. iFrame.
    - rel_load_r. rel_pures_r.
      iApply (refines_na_close with "[- $Hclose]").
      iSplitR.
      { iModIntro. rel_values. }
      iModIntro. iRight. iFrame.
  Qed.

  Lemma lazy_with_tape_lazy_rel :
    ⊢ REL lazy_with_tape << lazy : () → lrel_bool.
  Proof.
    rewrite /lazy /lazy_with_tape.
    rel_alloc_r l' as "Hl'". rel_pures_l.
    rel_alloctape_l α as "Hα". rel_pures_l.
    rel_alloc_l l as "Hl". rel_pures_l.
    set (P := (α ↪ [] ∗ (l ↦ NONEV ∗ l' ↦ₛ NONEV ∨
                  ∃ (b: bool), l ↦ SOMEV #b ∗ l' ↦ₛ SOMEV #b))%I).
    iMod (na_inv_alloc prelogrelGS_nais _ coinN P with "[-]") as "#Hinv".
    { iFrame. iLeft. iFrame. }
    rel_arrow_val.
    iIntros (?? [-> ->]).
    rel_pures_l.
    rel_pure_r.
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "[(Hα & [[Hl Hl'] | >[%b [Hl Hl']]]) Hclose]".
    - rel_load_l. rel_pures_l.
      rel_load_r. rel_pures_r.
      rel_bind_l (flip _)%E.
      rel_bind_r (flip _)%E.
      iApply (refines_couple_flips_l with "[-$Hα]"); [solve_ndisj|].
      iIntros (b) "Hα /=".
      rel_pures_l. rel_store_l. rel_pures_l.
      rel_pures_r. rel_store_r. rel_pures_r.
      iApply (refines_na_close with "[- $Hclose $Hα]").
      iSplitR; [rel_values|].
      iRight. iModIntro. iExists _. iFrame.
    - rel_load_l. rel_pures_l.
      rel_load_r. rel_pures_r.
      iApply (refines_na_close with "[- $Hclose $Hα]").
      iSplitR; [rel_values|].
      iRight. iModIntro. iExists _. iFrame.
  Qed.

End logical_ref.

Theorem lazy_eager_refinement :
  ∅ ⊨ lazy ≤ctx≤ eager : () → TBool.
Proof.
  eapply ctx_refines_transitive.
  - eapply (refines_sound prelogrelΣ).
    intros. apply: lazy_lazy_with_tape_rel.
  - eapply (refines_sound prelogrelΣ).
    intros. apply: lazy_with_tape_eager_rel.
Qed.

Theorem eager_lazy_refinement :
  ∅ ⊨ eager ≤ctx≤ lazy : () → TBool.
Proof.
  eapply ctx_refines_transitive.
  - eapply (refines_sound prelogrelΣ).
    intros. apply: eager_lazy_with_tape_rel.
  - eapply (refines_sound prelogrelΣ).
    intros. apply: lazy_with_tape_lazy_rel.
Qed.

Theorem eager_lazy_equiv :
  ∅ ⊨ lazy =ctx= eager : () → TBool.
Proof.
  split.
  - apply lazy_eager_refinement.
  - apply eager_lazy_refinement.
Qed.
