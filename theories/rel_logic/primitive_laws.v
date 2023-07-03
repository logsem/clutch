(** This file proves the basic laws of the ProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export ghost_map.
From clutch.program_logic Require Export weakestpre.
From clutch.program_logic Require Import ectx_lifting.
From clutch.prob_lang Require Export class_instances.
From clutch.prob_lang Require Import tactics lang notation.
From clutch.rel_logic Require Import spec_ra.
From iris.prelude Require Import options.

Class clutchGS Σ := HeapG {
  clutchGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state *)
  clutchGS_heap : ghost_mapG Σ loc val;
  clutchGS_tapes : ghost_mapG Σ loc tape;
  (* ghost names for the state *)
  clutchGS_heap_name : gname;
  clutchGS_tapes_name : gname;
  (* CMRA and ghost name for the spec *)
  clutchGS_spec :> specGS Σ;
}.

Definition heap_auth `{clutchGS Σ} :=
  @ghost_map_auth _ _ _ _ _ clutchGS_heap clutchGS_heap_name.
Definition tapes_auth `{clutchGS Σ} :=
  @ghost_map_auth _ _ _ _ _ clutchGS_tapes clutchGS_tapes_name.


Global Instance clutchGS_irisGS `{!clutchGS Σ} : irisGS prob_lang Σ := {
  iris_invGS := clutchGS_invG;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes))%I;
  spec_interp ρ := (spec_interp_auth ρ)%I ;
}.

(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ clutchGS_heap clutchGS_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Tapes *)
Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ tape _ _ clutchGS_tapes clutchGS_tapes_name l dq v)
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.

Section lifting.
Context `{!clutchGS Σ}.
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

Lemma wp_rand (N : nat) (z : Z) E :
  TCEq N (Z.to_nat z) →
  {{{ True }}} rand #z from #() @ E {{{ (n : fin (S N)), RET #n; True }}}.
Proof.
  iIntros (-> Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "Hσ !#".
  iSplit; [eauto with head_step|].
  Unshelve. 2 : { apply 0%fin . }
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  by iApply ("HΦ" $! x) .
Qed.

(** Tapes  *)
Lemma wp_alloc_tape N z E :
  TCEq N (Z.to_nat z) →
  {{{ True }}} alloc #z @ E {{{ α, RET #lbl:α; α ↪ (N; []) }}}.
Proof.
  iIntros (-> Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !# /=".
  iSplit; [by eauto with head_step|].
  iIntros "!>" (e2 σ2 Hs); inv_head_step.
  iMod (ghost_map_insert (fresh_loc σ1.(tapes)) with "Ht") as "[$ Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iFrame. iModIntro.
  by iApply "HΦ".
Qed.

Lemma wp_rand_tape N α n ns z E :
  TCEq N (Z.to_nat z) →
  {{{ ▷ α ↪ (N; n :: ns) }}} rand #z from #lbl:α @ E {{{ RET #(LitInt n); α ↪ (N; ns) }}}.
Proof.
  iIntros (-> Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !#".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  iSplit; [eauto with head_step|].
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iMod (ghost_map_update with "Ht Hl") as "[$ Hl]".
  iFrame. iModIntro.
  by iApply "HΦ".
Qed.

Lemma wp_rand_tape_empty N z α E :
  TCEq N (Z.to_nat z) →
  {{{ ▷ α ↪ (N; []) }}} rand #z from #lbl:α @ E {{{ (n : fin (S N)), RET #(LitInt n); α ↪ (N; []) }}}.
Proof.
  iIntros (-> Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !#".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  iSplit; [by eauto with head_step|].
  Unshelve. 2 : { apply 0%fin. }
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iModIntro. iApply ("HΦ" with "[$Hl //]").
Qed.

Lemma wp_rand_tape_wrong_bound N M z α E ns :
  TCEq N (Z.to_nat z) →
  N ≠ M →
  {{{ ▷ α ↪ (M; ns) }}} rand #z from #lbl:α @ E {{{ (n : fin (S N)), RET #(LitInt n); α ↪ (M; ns) }}}.
Proof.
  iIntros (-> ? Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !#".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  iSplit; [by eauto with head_step|].
  Unshelve. 2 : { apply 0%fin. }
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iModIntro.
  iApply ("HΦ" with "[$Hl //]").
Qed.  

End lifting.

Global Hint Extern 0 (TCEq _ (Z.to_nat _ )) => rewrite Nat2Z.id : typeclass_instances. 
