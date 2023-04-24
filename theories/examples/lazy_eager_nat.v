From stdpp Require Import namespaces.
From iris.base_logic Require Import invariants na_invariants.
From self.prob_lang Require Import notation proofmode primitive_laws spec_rules.
From self.logrel Require Import model rel_rules rel_tactics.
From self.typing Require Import soundness.
From self.prelude Require Import base.
Set Default Proof Using "Type*".

(** The lazy/eager coins, without tapes *)
Definition lazy : expr :=
  λ: "n",
  let: "s" := ref NONEV in
  λ: <>,
    match: !"s" with
    | NONE => let: "b" := rand "n" in
              "s" <- SOME "b" ;;
              "b"
    | SOME "b" => "b"
    end.

Definition eager : expr :=
  λ: "n",
  let: "b" := rand "n" in
  λ: <>, "b".

(** An intetermedaite version of [lazy] that uses a tape to allow presampling
    bits during the proof *)
Definition lazy_with_tape : expr :=
  λ: "n",
  let: "α" := alloc "n" in
  let: "s" := ref NONEV in
  λ: <>,
    match: !"s" with
    | NONE => let: "b" := rand "α" in
              "s" <- SOME "b" ;;
              "b"
    | SOME "b" => "b"
    end.

Section logical_ref.
  Context `{!prelogrelGS Σ}.

  Definition coinN := nroot.@"coins".

  (** lazy << lazy_with_tape << eager *)
  Lemma lazy_lazy_with_tape_rel :
    ⊢ REL lazy << lazy_with_tape : lrel_nat → (lrel_arr lrel_unit lrel_int).
  Proof.
    rewrite /lazy /lazy_with_tape.
    rel_arrow_val.
    iIntros (? ? (z & -> & ->)).
    rel_pures_l.
    rel_pures_r.
    rel_alloc_l l as "Hl".
    rel_pures_l.
    rel_alloctape_r α as "Hα".
    rel_pures_r.
    rel_alloc_r l' as "Hl'".
    rel_pures_r.
    rewrite Nat2Z.id.
    set (P := (α ↪ₛ (z, []) ∗ (l ↦ NONEV ∗ l' ↦ₛ NONEV ∨
                 ∃ (b: Z), l ↦ SOMEV #b ∗ l' ↦ₛ SOMEV #b))%I).
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
      rel_bind_l (rand _)%E.
      rel_bind_r (rand _)%E.
      iApply (refines_couple_rands_r with "[-$Hα]").
      iIntros (b) "[%Hleq Hα] /=".
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

  Lemma lazy_with_tape_eager_rel :
    ⊢ REL lazy_with_tape << eager : lrel_nat → (lrel_arr lrel_unit lrel_int).
  Proof.
    rewrite /lazy_with_tape /eager.
    rel_arrow_val.
    iIntros (? ? (z & -> & ->)).
    rel_pures_l. rel_pures_r.
    rel_alloctape_l α as "Hα". rel_pures_l.
    rewrite Nat2Z.id.
    rel_bind_r (rand _)%E.
    iApply (refines_couple_tape_rand with "[$Hα]"); [done|].
    iIntros (b) "[%Hleq Hα] /=".
    rel_pures_r.
    rel_alloc_l l as "Hl". rel_pures_l.
    set (P := ((α ↪ (z,[b]) ∗ l ↦ NONEV) ∨ (l ↦ SOMEV #b))%I).
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
      rel_rand_l. rel_pures_l.
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
    ⊢ REL eager << lazy_with_tape : lrel_nat → (lrel_arr lrel_unit lrel_int).
  Proof.
    rewrite /lazy_with_tape /eager.
    rel_arrow_val.
    iIntros (? ? (z & -> & ->)).
    rel_pures_l. rel_pures_r.
    rel_alloctape_r α as "Hα". rel_pures_r.
    rewrite Nat2Z.id.
    rel_bind_l (rand _)%E.
    iApply (refines_couple_rand_tape with "[$Hα]").
    iIntros (b) "[Hleq Hα] /=".
    rel_pures_r.
    rel_alloc_r l as "Hl". rel_pures_r.
    set (P := ((α ↪ₛ (z,[b]) ∗ l ↦ₛ NONEV) ∨ (l ↦ₛ SOMEV #b))%I).
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
      rel_rand_r. rel_pures_r.
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
    ⊢ REL lazy_with_tape << lazy : lrel_nat → (lrel_arr lrel_unit lrel_int).
  Proof.
    rewrite /lazy /lazy_with_tape.
    rel_arrow_val.
    iIntros (? ? (z & -> & ->)).
    rel_alloc_r l' as "Hl'". rel_pures_l.
    rel_alloctape_l α as "Hα". rel_pures_l.
    rewrite Nat2Z.id.
    rel_alloc_l l as "Hl". rel_pures_l.
    set (P := (α ↪ (z,[]) ∗ (l ↦ NONEV ∗ l' ↦ₛ NONEV ∨
                           ∃ (b: Z), l ↦ SOMEV #b ∗ l' ↦ₛ SOMEV #b))%I).
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
      rel_bind_l (rand _)%E.
      rel_bind_r (rand _)%E.
      iApply (refines_couple_rands_l with "[-$Hα]").
      iIntros (b) "[Hleq Hα] /=".
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
  ∅ ⊨ lazy ≤ctx≤ eager : (TArrow TNat (TArrow TUnit TInt)).
Proof.
  eapply ctx_refines_transitive.
  - eapply (refines_sound prelogrelΣ).
    intros. apply: lazy_lazy_with_tape_rel.
  - eapply (refines_sound prelogrelΣ).
    intros. apply: lazy_with_tape_eager_rel.
Qed.

Theorem eager_lazy_refinement :
  ∅ ⊨ eager ≤ctx≤ lazy : (TArrow TNat (TArrow TUnit TInt)).
Proof.
  eapply ctx_refines_transitive.
  - eapply (refines_sound prelogrelΣ).
    intros. apply: eager_lazy_with_tape_rel.
  - eapply (refines_sound prelogrelΣ).
    intros. apply: lazy_with_tape_lazy_rel.
Qed.

Theorem eager_lazy_equiv :
  ∅ ⊨ lazy =ctx= eager : (TArrow TNat (TArrow TUnit TInt)).
Proof.
  split.
  - apply lazy_eager_refinement.
  - apply eager_lazy_refinement.
Qed.
