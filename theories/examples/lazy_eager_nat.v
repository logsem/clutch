From clutch Require Export clutch.
Set Default Proof Using "Type*".

(** The lazy/eager coins, without tapes *)
Definition lazy : expr :=
  λ: "N",
    let: "s" := ref NONEV in
    λ: <>,
      match: !"s" with
      | NONE => let: "n" := rand "N" from #() in
                "s" <- SOME "n" ;;
                "n"
      | SOME "n" => "n"
      end.

Definition eager : expr :=
  λ: "N",
  let: "n" := rand "N" from #() in
  λ: <>, "n".

(** An intermediate version of [lazy] that uses a tape to allow presampling
    bits during the proof *)
Definition lazy_with_tape : expr :=
  λ: "N",
  let: "α" := alloc "N" in
  let: "s" := ref NONEV in
  λ: <>,
    match: !"s" with
    | NONE => let: "n" := rand "N" from "α" in
              "s" <- SOME "n" ;;
              "n"
    | SOME "n" => "n"
    end.

Section logical_ref.
  Context `{!clutchRGS Σ}.

  Definition coinN := nroot.@"coins".

  (** lazy << lazy_with_tape << eager *)
  Lemma lazy_lazy_with_tape_rel :
    ⊢ REL lazy << lazy_with_tape : lrel_nat → () → lrel_nat.
  Proof.
    rewrite /lazy /lazy_with_tape.
    rel_arrow_val.
    iIntros (? ? (N & -> & ->)).
    rel_pures_l.
    rel_pures_r.
    rel_alloc_l l as "Hl".
    rel_pures_l.
    rel_alloctape_r α as "Hα".
    rel_pures_r.
    rel_alloc_r l' as "Hl'".
    rel_pures_r.
    set (P := (α ↪ₛ (N; []) ∗ (l ↦ NONEV ∗ l' ↦ₛ NONEV ∨
              ∃ n : fin (S N), l ↦ SOMEV #n ∗ l' ↦ₛ SOMEV #n))%I).
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
      rel_bind_l (rand _ from _)%E.
      rel_bind_r (rand _ from _)%E.
      rel_apply_l (refines_couple_rands_r with "[-$Hα]").
      iIntros "!>" (n) "Hα /=".
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
    ⊢ REL lazy_with_tape << eager : lrel_nat → () → lrel_nat.
  Proof.
    rewrite /lazy_with_tape /eager.
    rel_arrow_val.
    iIntros (? ? (N & -> & ->)).
    rel_pures_l. rel_pures_r.
    rel_alloctape_l α as "Hα". rel_pures_l.
    rel_apply_r (refines_couple_tape_rand with "[$Hα]"); [done|].
    iIntros (n) "Hα /=".
    rel_pures_r.
    rel_alloc_l l as "Hl". rel_pures_l.
    set (P := ((α ↪ (N; [n]) ∗ l ↦ NONEV) ∨ (l ↦ SOMEV #n))%I).
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
    ⊢ REL eager << lazy_with_tape : lrel_nat → () → lrel_nat.
  Proof.
    rewrite /lazy_with_tape /eager.
    rel_arrow_val.
    iIntros (? ? (N & -> & ->)).
    rel_pures_l. rel_pures_r.
    rel_alloctape_r α as "Hα". rel_pures_r.
    rel_apply_l (refines_couple_rand_tape with "[$Hα]").
    iIntros "!>" (n) "Hα /=".
    rel_pures_r.
    rel_alloc_r l as "Hl". rel_pures_r.
    set (P := ((α ↪ₛ (N; [n]) ∗ l ↦ₛ NONEV) ∨ (l ↦ₛ SOMEV #n))%I).
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
    ⊢ REL lazy_with_tape << lazy : lrel_nat → () → lrel_nat.
  Proof.
    rewrite /lazy /lazy_with_tape.
    rel_arrow_val.
    iIntros (? ? (N & -> & ->)).
    rel_alloc_r l' as "Hl'". rel_pures_l.
    rel_alloctape_l α as "Hα". rel_pures_l.
    rel_alloc_l l as "Hl". rel_pures_l.
    set (P := (α ↪ (N; []) ∗ (l ↦ NONEV ∗ l' ↦ₛ NONEV ∨
             ∃ n : fin (S N), l ↦ SOMEV #n ∗ l' ↦ₛ SOMEV #n))%I).
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
      rel_bind_l (rand _ from _)%E.
      rel_bind_r (rand _ from _)%E.
      iApply (refines_couple_rands_l with "[-$Hα]").
      iIntros "!>" (n) "Hα /=".
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
  ∅ ⊨ lazy ≤ctx≤ eager : TNat → TUnit → TNat.
Proof.
  eapply ctx_refines_transitive.
  - eapply (refines_sound clutchRΣ).
    intros. apply: lazy_lazy_with_tape_rel.
  - eapply (refines_sound clutchRΣ).
    intros. apply: lazy_with_tape_eager_rel.
Qed.

Theorem eager_lazy_refinement :
  ∅ ⊨ eager ≤ctx≤ lazy : TNat → TUnit → TNat.
Proof.
  eapply ctx_refines_transitive.
  - eapply (refines_sound clutchRΣ).
    intros. apply: eager_lazy_with_tape_rel.
  - eapply (refines_sound clutchRΣ).
    intros. apply: lazy_with_tape_lazy_rel.
Qed.

Theorem eager_lazy_equiv :
  ∅ ⊨ lazy =ctx= eager : TNat → () → TNat.
Proof.
  split.
  - apply lazy_eager_refinement.
  - apply eager_lazy_refinement.
Qed.
