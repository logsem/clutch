From iris.proofmode Require Import proofmode.
From clutch.ub_logic Require Export error_credits ub_total_weakestpre total_ectx_lifting primitive_laws.
From clutch.prob_lang Require Import tactics lang notation.
From clutch.prob_lang Require Export class_instances.

Section total_primitive_laws.
Context `{!ub_clutchGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.


(** Heap *)
Lemma twp_alloc E v :
 [[{ True }]] Alloc (Val v) @ E [[{ l, RET LitV (LitLoc l); l ↦ v }]].
Proof.
  iIntros (Φ) "_ HΦ".
  iApply twp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  solve_red.
  iIntros "/=" (e2 σ2 Hs); inv_head_step.
  iMod ((ghost_map_insert (fresh_loc σ1.(heap)) v) with "Hh") as "[$ Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iIntros "!>". iFrame. by iApply "HΦ".
Qed.

Lemma twp_load E l dq v :
  [[{ ▷ l ↦{dq} v }]] Load (Val $ LitV $ LitLoc l) @ E [[{ RET v; l ↦{dq} v }]].
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply twp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  solve_red.
  iIntros "/=" (e2 σ2 Hs); inv_head_step.
  iFrame. iModIntro. by iApply "HΦ".
Qed.

Lemma twp_store E l v' v :
  [[{ ▷ l ↦ v' }]] Store (Val $ LitV (LitLoc l)) (Val v) @ E
  [[{ RET LitV LitUnit; l ↦ v }]].
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply twp_lift_atomic_head_step; [done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  solve_red.
  iIntros "/=" (e2 σ2 Hs); inv_head_step.
  iMod (ghost_map_update with "Hh Hl") as "[$ Hl]".
  iFrame. iModIntro. by iApply "HΦ".
Qed.

Lemma twp_rand (N : nat) (z : Z) E :
  TCEq N (Z.to_nat z) →
  [[{ True }]] rand #z @ E [[{ (n : fin (S N)), RET #n; True }]].
Proof.
  iIntros (-> Φ) "_ HΦ".
  iApply twp_lift_atomic_head_step; [done|].
  iIntros (σ1) "Hσ !#".
  solve_red.
  iIntros (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  by iApply ("HΦ" $! x) .
Qed.


(** Tapes  *)
Lemma twp_alloc_tape N z E :
  TCEq N (Z.to_nat z) →
  [[{ True }]] alloc #z @ E [[{ α, RET #lbl:α; α ↪ (N; []) }]].
Proof.
  iIntros (-> Φ) "_ HΦ".
  iApply twp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !# /=".
  solve_red.
  iIntros (e2 σ2 Hs); inv_head_step.
  iMod (ghost_map_insert (fresh_loc σ1.(tapes)) with "Ht") as "[$ Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iFrame. iModIntro.
  by iApply "HΦ".
Qed.

Lemma twp_rand_tape N α n ns z E :
  TCEq N (Z.to_nat z) →
  [[{ ▷ α ↪ (N; n :: ns) }]] rand(#lbl:α) #z @ E [[{ RET #(LitInt n); α ↪ (N; ns) }]].
Proof.
  iIntros (-> Φ) ">Hl HΦ".
  iApply twp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !#".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  solve_red.
  iIntros (e2 σ2 Hs).
  inv_head_step.
  iMod (ghost_map_update with "Ht Hl") as "[$ Hl]".
  iFrame. iModIntro.
  by iApply "HΦ".
Qed.

Lemma twp_rand_tape_empty N z α E :
  TCEq N (Z.to_nat z) →
  [[{ ▷ α ↪ (N; []) }]] rand(#lbl:α) #z @ E [[{ (n : fin (S N)), RET #(LitInt n); α ↪ (N; []) }]].
Proof.
  iIntros (-> Φ) ">Hl HΦ".
  iApply twp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !#".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  solve_red.
  iIntros (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iModIntro. iApply ("HΦ" with "[$Hl //]").
Qed.

Lemma twp_rand_tape_wrong_bound N M z α E ns :
  TCEq N (Z.to_nat z) →
  N ≠ M →
  [[{ ▷ α ↪ (M; ns) }]] rand(#lbl:α) #z @ E [[{ (n : fin (S N)), RET #(LitInt n); α ↪ (M; ns) }]].
Proof.
  iIntros (-> ? Φ) ">Hl HΦ".
  iApply twp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht) !#".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  solve_red.
  iIntros (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iModIntro.
  iApply ("HΦ" with "[$Hl //]").
Qed.

End total_primitive_laws.
