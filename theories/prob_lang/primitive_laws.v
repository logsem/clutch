(** This file proves the basic laws of the ProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export ghost_map.
From self.program_logic Require Import weakestpre.
From self.program_logic Require Import ectx_lifting.
From self.prob_lang Require Import locations class_instances.
From self.prob_lang Require Import spec_ra.
From self.prob_lang Require Import tactics lang notation.
From iris.prelude Require Import options.

Class prelocGS Σ := HeapG {
  prelocGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state *)
  prelocGS_heap : ghost_mapG Σ loc val;
  prelocGS_tapes : ghost_mapG Σ loc (list bool);
  (* ghost names for the state *)
  prelocGS_heap_name : gname;
  prelocGS_tapes_name : gname;
  (* CMRA and ghost name for the spec *)
  prelocGS_spec :> specGS Σ;
}.

Definition heap_auth `{prelocGS Σ} :=
  @ghost_map_auth _ _ _ _ _ prelocGS_heap prelocGS_heap_name.
Definition tapes_auth `{prelocGS Σ} :=
  @ghost_map_auth _ _ _ _ _ prelocGS_tapes prelocGS_tapes_name.

Global Instance prelocGS_irisGS `{!prelocGS Σ} : irisGS prob_lang Σ := {
  iris_invGS := prelocGS_invG;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes))%I;
  spec_interp ρ := spec_interp_auth ρ;
}.

(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ prelocGS_heap prelocGS_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Tapes *)
Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ _ _ _ prelocGS_tapes prelocGS_tapes_name l dq v)
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.

Section lifting.
Context `{!prelocGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

(** Recursive functions: we do not use this lemmas as it is easier to use Löb *)
(* induction directly, but this demonstrates that we can state the expected *)
(* reasoning principle for recursive functions, without any visible ▷. *)
Lemma wp_rec_löb E f x e Φ Ψ :
  □ ( □ (∀ v, Ψ v -∗ WP (rec: f x := e)%V v @ E {{ Φ }}) -∗
     ∀ v, Ψ v -∗ WP (subst' x v (subst' f (rec: f x := e) e)) @ E {{ Φ }}) -∗
  ∀ v, Ψ v -∗ WP (rec: f x := e)%V v @ E {{ Φ }}.
Proof.
  iIntros "#Hrec". iLöb as "IH". iIntros (v) "HΨ".
  iApply lifting.wp_pure_step_later; first done.
  iNext. iApply ("Hrec" with "[] HΨ"). iIntros "!>" (w) "HΨ".
  iApply ("IH" with "HΨ").
Qed.

(** Heap *)
Lemma wp_alloc E v :
  {{{ True }}} Alloc (Val v) @ E {{{ l, RET LitV (LitLoc l); l ↦ v }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iSplit; [by eauto with head_step|].
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iMod ((ghost_map_insert (fresh_loc σ1.(heap)) v) with "Hh") as "[$ Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iIntros "!>". iFrame. by iApply "HΦ".
Qed.

Lemma wp_load E l dq v :
  {{{ ▷ l ↦{dq} v }}} Load (Val $ LitV $ LitLoc l) @ E {{{ RET v; l ↦{dq} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  iSplit; [by eauto with head_step|].
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iFrame. iModIntro. by iApply "HΦ".
Qed.

Lemma wp_store E l v' v :
  {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  iSplit; [by eauto with head_step|].
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iMod (ghost_map_update with "Hh Hl") as "[$ Hl]".
  iFrame. iModIntro. by iApply "HΦ".
Qed.

(** Tapes  *)
Lemma wp_alloc_tape E :
  {{{ True }}} AllocTape @ E {{{ α, RET LitV (LitLbl α); α ↪ [] }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !# /=".
  iSplit; [by eauto with head_step|].
  iIntros "!>" (e2 σ2 Hs); inv_head_step.
  iMod (ghost_map_insert (fresh_loc σ1.(tapes)) with "Ht") as "[$ Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iFrame. iModIntro. by iApply "HΦ".
Qed.

Lemma wp_flip E α b bs :
  {{{ ▷ α ↪ (b :: bs) }}} Flip (Val $ LitV $ LitLbl α) @ E
  {{{ RET LitV (LitBool b); α ↪ bs }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  iSplit; [by eauto with head_step|].
  simpl.
  iIntros "!>" (e2 σ2 Hs); inv_head_step; last first.
  { destruct_or?; simplify_map_eq. }
  iMod (ghost_map_update with "Ht Hl") as "[$ Hl]".
  iFrame. iModIntro. by iApply "HΦ".
Qed.

Lemma wp_flipU E :
  {{{ True }}} Flip (Val $ LitV $ LitUnit) @ E
  {{{ b, RET LitV (LitBool b); True }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iSplit; [unshelve by eauto with head_step|].
  1: exact inhabitant.
  simpl.
  iIntros "!>" (e2 σ2 Hs); inv_head_step; last first.
  iFrame. iModIntro. by iApply "HΦ".
Qed.

Lemma wp_flip_empty E α :
  {{{ ▷ α ↪ [] }}} Flip (Val $ LitV $ LitLbl α) @ E
  {{{ b, RET LitV (LitBool b); α ↪ [] }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !# /=".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  iSplit; [by eauto with head_step|].
  Unshelve.
  Unshelve. 2: { exact inhabitant. }
  iIntros "!>" (e2 σ2 Hs); inv_head_step.
  iFrame. iModIntro. by iApply "HΦ".
Qed.

End lifting.
