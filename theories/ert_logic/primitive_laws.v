(** This file proves the basic laws of the ProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Export ghost_map.
From clutch.ert_logic Require Export expected_time_credits ert_weakestpre ectx_lifting problang_wp.
From clutch.prob_lang Require Export class_instances.
From clutch.prob_lang Require Import tactics lang notation.
From iris.prelude Require Import options.


Section primitive_laws.
Context (cost : Costfun prob_lang).
Context `{!ert_clutchGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

(** Recursive functions: we do not use this lemmas as it is easier to use Löb *)
(* induction directly, but this demonstrates that we can state the expected *)
(* reasoning principle for recursive functions, without any visible ▷. *)
(*
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
*)

(** Heap *)

Lemma wp_alloc E x v s :
  TCEq x (cost (Alloc (Val v))) →
  {{{ ⧖ x }}} Alloc (Val v) @ s; E {{{ l, RET LitV (LitLoc l); l ↦ v }}}.
Proof.
  iIntros (-> Φ) "Hx HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  solve_red.
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
  {{{ ⧖ x }}}
    AllocN #z v @ s; E
  {{{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 N, (l +ₗ (i : nat)) ↦ v }}}.
Proof.
  iIntros (-> -> Hn Φ) "Hx HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iSplit.
  { iPureIntro.
    rewrite /head_reducible.
    eexists.
    apply head_step_support_equiv_rel.
    econstructor; eauto.
    lia. }
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
      (* TODO: this is nasty... Find a better solution *)
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
  TCEq x (cost (Load (Val $ LitV $ LitLoc l))) →
  {{{ ⧖ x ∗ ▷ l ↦{dq} v }}}
    Load (Val $ LitV $ LitLoc l) @ s; E
  {{{ RET v; l ↦{dq} v }}}.
Proof.
  iIntros (-> Φ) "[Hx >Hl] HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  solve_red.
  iFrame "Hx".
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iFrame. iModIntro.
  iApply "HΦ"; done.
Qed.

Lemma wp_store E x l v' v s :
  TCEq x (cost (Store (Val $ LitV (LitLoc l)) (Val v))) →
  {{{ ⧖ x ∗ ▷ l ↦ v' }}}
    Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (-> Φ) "[Hx >Hl] HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  solve_red.
  iFrame "Hx".
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iMod (ghost_map_update with "Hh Hl") as "[$ Hl]".
  iFrame. iModIntro. by iApply "HΦ".
Qed.

Lemma wp_rand x (N : nat) (z : Z) E s :
  TCEq x (cost (rand #z)%E) →
  TCEq N (Z.to_nat z) →
  {{{ ⧖ x }}} rand #z @ s; E {{{ (n : fin (S N)), RET #n; True }}}.
Proof.
  iIntros (-> -> Φ) "Hx HΦ".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "Hσ !#".
  solve_red.
  iFrame "Hx".
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame. iModIntro. by iApply "HΦ".
Qed.

(** TODO tapes *)
(** Tapes  *)
(* Lemma wp_alloc_tape N z E s : *)
(*   TCEq N (Z.to_nat z) → *)
(*   {{{ True }}} alloc #z @ s; E {{{ α, RET #lbl:α; α ↪ (N; []) }}}. *)
(* Proof. *)
(*   iIntros (-> Φ) "_ HΦ". *)
  (*
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !# /=".
  solve_red.
  iIntros "!>" (e2 σ2 Hs); inv_head_step.
  iMod (ghost_map_insert (fresh_loc σ1.(tapes)) with "Ht") as "[$ Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iFrame. iModIntro.
  by iApply "HΦ".
Qed.
*)

(* Lemma wp_rand_tape N α n ns z E s : *)
(*   TCEq N (Z.to_nat z) → *)
(*   {{{ ▷ α ↪ (N; n :: ns) }}} rand(#lbl:α) #z @ s; E {{{ RET #(LitInt n); α ↪ (N; ns) }}}. *)
(* Proof. *)
(*   iIntros (-> Φ) ">Hl HΦ". *)
  (*
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !#".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  solve_red.
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iMod (ghost_map_update with "Ht Hl") as "[$ Hl]".
  iFrame. iModIntro.
  by iApply "HΦ".
Qed.
   *)

(* Lemma wp_rand_tape_empty N z α E s : *)
(*   TCEq N (Z.to_nat z) → *)
(*   {{{ ▷ α ↪ (N; []) }}} rand(#lbl:α) #z @ s; E {{{ (n : fin (S N)), RET #(LitInt n); α ↪ (N; []) }}}. *)
(* Proof. *)
(*   iIntros (-> Φ) ">Hl HΦ". *)
  (*
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !#".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  solve_red.
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iModIntro. iApply ("HΦ" with "[$Hl //]").
Qed.
*)

(* Lemma wp_rand_tape_wrong_bound N M z α E ns s : *)
(*   TCEq N (Z.to_nat z) → *)
(*   N ≠ M → *)
(*   {{{ ▷ α ↪ (M; ns) }}} rand(#lbl:α) #z @ s; E {{{ (n : fin (S N)), RET #(LitInt n); α ↪ (M; ns) }}}. *)
(* Proof. *)
(*   iIntros (-> ? Φ) ">Hl HΦ". *)
  (*
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !#".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  solve_red.
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iModIntro.
  iApply ("HΦ" with "[$Hl //]").
Qed.
*)

End primitive_laws.

Global Hint Extern 0 (TCEq _ (Z.to_nat _ )) => rewrite Nat2Z.id : typeclass_instances.
