(** This file proves the basic laws of the ProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Export ghost_map.
From tachis.tachis Require Export expected_time_credits ert_weakestpre ectx_lifting problang_wp.
From tachis.prob_lang Require Export class_instances.
From tachis.prob_lang Require Import tactics lang notation.
From iris.prelude Require Import options.


Section primitive_laws.
Context `{!tachisGS Σ F}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

#[global] Instance Req_decision (r1 r2 : R) : Decision (r1 = r2).
Proof. destruct (Rle_dec r1 r2); destruct (Rle_dec r2 r1);
 [left | right | right |]; lra. Defined. 

(** Heap *)
Lemma wp_alloc E x v s :
  TCEq x (cost (ref v)) →
  {{{ if bool_decide (cost (ref v) = 0%R) then True else ⧖ x }}}
    ref v @ s; E
  {{{ l, RET #l; l ↦ v }}}.
Proof.
  iIntros (-> Φ) "Hx HΦ".
  iMod etc_zero as "Hz".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  solve_red.
  iAssert ((⧖ (cost _))%I) with "[Hz Hx]" as "Hx".
  { case_bool_decide as Hz; [|done]. rewrite Hz //. }
  iFrame "Hx".
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iMod ((ghost_map_insert (fresh_loc σ1.(heap)) v) with "Hh") as "[? Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iFrame.
  rewrite map_union_empty -insert_union_singleton_l.
  iFrame.
  iIntros "!>".
  by iApply "HΦ".
Qed.

Lemma wp_allocN_seq x (N : nat) (z : Z) E v s:
  TCEq x (cost (AllocN #z v)) ->
  TCEq N (Z.to_nat z) →
  (0 < N)%Z →
  {{{ if bool_decide (cost (AllocN #z v) = 0%R) then True else ⧖ x }}}
    AllocN #z v @ s; E
  {{{ l, RET #l; [∗ list] i ∈ seq 0 N, (l +ₗ (i : nat)) ↦ v }}}.
Proof.
  iIntros (-> -> Hn Φ) "Hx HΦ".
  iMod etc_zero as "Hz".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iSplit.
  { iPureIntro.
    rewrite /head_reducible.
    eexists.
    apply head_step_support_equiv_rel.
    econstructor; eauto.
    lia. }
  iAssert (⧖ (cost _))%I with "[Hz Hx]" as "Hx".
  { case_bool_decide as Hz; [|done]. rewrite Hz //. }
  iFrame "Hx".
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iMod ((ghost_map_insert_big _ _ with "Hh")) as "[$ Hl]".
  iIntros "!>". iFrame.
  iApply "HΦ".
  iInduction H as [ | ?] "IH" forall (σ1).
  - simpl.
    iSplit; [|done].
    rewrite map_union_empty.
    rewrite loc_add_0.
    by rewrite big_sepM_singleton.
  - rewrite seq_S.
    rewrite heap_array_replicate_S_end.
    iPoseProof (big_sepM_union _ _ _ _ with "Hl") as "[H1 H2]".
    iApply big_sepL_app.
    iSplitL "H1".
    + iApply "IH"; [|done]. iPureIntro; lia.
    + simpl. iSplit; [|done].
      by rewrite big_sepM_singleton.
      Unshelve.
      { apply heap_array_map_disjoint.
        intros.
        apply not_elem_of_dom_1.
        by apply fresh_loc_offset_is_fresh. }
      { apply heap_array_map_disjoint.
      intros.
      apply not_elem_of_dom_1.
      rewrite dom_singleton.
      apply not_elem_of_singleton_2.
      intros H2.
      apply loc_add_inj in H2.
      rewrite replicate_length in H1.
      lia. }
Qed.

Lemma wp_load E x l dq v s :
  TCEq x (cost (! #l)) →
  {{{ (if bool_decide (cost (! #l) = 0%R) then True else ⧖ x) ∗ ▷ l ↦{dq} v }}}
    ! #l @ s; E
  {{{ RET v; l ↦{dq} v }}}.
Proof.
  iIntros (-> Φ) "[Hx >Hl] HΦ".
  iMod etc_zero as "Hz".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  solve_red.
  iAssert (⧖ (cost _)%I) with "[Hz Hx]" as "Hx".
  { case_bool_decide as Hz; [|done]. rewrite Hz //. }
  iFrame "Hx".
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iFrame. iModIntro.
  iApply "HΦ"; done.
Qed.

Lemma wp_store E x l v' v s :
  TCEq x (cost (#l <- v)) →
  {{{ (if bool_decide (cost (#l <- v) = 0%R) then True else ⧖ x) ∗ ▷ l ↦ v' }}}
    #l <- v @ s; E
  {{{ RET #(); l ↦ v }}}.
Proof.
  iIntros (-> Φ) "[Hx >Hl] HΦ".
  iMod etc_zero as "Hz".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  solve_red.
  iAssert (⧖ (cost _))%I with "[Hz Hx]" as "Hx".
  { case_bool_decide as Hz; [|done]. rewrite Hz //. }
  iFrame "Hx".
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iMod (ghost_map_update with "Hh Hl") as "[$ Hl]".
  iFrame. iModIntro. by iApply "HΦ".
Qed.

Lemma wp_rand x (N : nat) (z : Z) E s :
  TCEq x (cost (rand #z)%E) →
  TCEq N (Z.to_nat z) →
  {{{ if bool_decide (cost (rand #z) = 0%R) then True else ⧖ x }}}
    rand #z @ s; E
  {{{ (n : fin (S N)), RET #n; True }}}.
Proof.
  iIntros (-> -> Φ) "Hx HΦ".
  iMod etc_zero as "Hz".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "Hσ !#".
  solve_red.
  iAssert (⧖ (cost _))%I with "[Hz Hx]" as "Hx".
  { case_bool_decide as Hz; [|done]. rewrite Hz //. }
  iFrame "Hx".
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame. iModIntro. by iApply "HΦ".
Qed.

(** Recursive functions: we do not use this lemmas as it is easier to use Löb *)
(* induction directly, but this demonstrates that we can state the expected *)
(* reasoning principle for recursive functions, without any visible ▷. *)
Lemma wp_rec_löb E f x e Φ Ψ :
  □ ( □ (∀ v, Ψ v -∗ ⧖ (cost ((rec: f x := e)%V v))  -∗ WP (rec: f x := e)%V v @ E {{ Φ }}) -∗
     ∀ v, Ψ v -∗ WP (subst' x v (subst' f (rec: f x := e) e)) @ E {{ Φ }}) -∗
  ∀ v, Ψ v -∗ ⧖ (cost ((rec: f x := e)%V v)) -∗ WP (rec: f x := e)%V v @ E {{ Φ }}.
Proof.
  iIntros "#Hrec". iLöb as "IH". iIntros (v) "HΨ H⧖".
  iApply lifting.wp_pure_step_later; first done.
  iFrame.
  iNext. iApply ("Hrec" with "[] HΨ"). iIntros "!>" (w) "HΨ H⧖".
  iApply ("IH" with "HΨ"). iFrame.
Qed.

End primitive_laws.

Global Hint Extern 0 (TCEq _ (Z.to_nat _ )) => rewrite Nat2Z.id : typeclass_instances.
