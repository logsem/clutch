From iris.proofmode Require Import proofmode.
From clutch.eris Require Export total_weakestpre total_ectx_lifting primitive_laws.
From clutch.prob_lang Require Import tactics lang notation.
From clutch.prob_lang Require Export class_instances.

Section total_primitive_laws.
Context `{!erisGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.


(** Heap *)


Lemma twp_alloc E v s :
  [[{ True }]] Alloc (Val v) @ s; E [[{ l, RET LitV (LitLoc l); l ↦ v }]].
Proof.
  iIntros (Φ) "_ HΦ".
  iApply twp_lift_atomic_head_step; [done|].
  iIntros (? σ1) "[Hh Ht] !#".
  solve_red.
  iIntros "/=" (e2 σ2 Hs); inv_head_step.
  iMod ((ghost_map_insert (fresh_loc σ1.(heap)) v) with "Hh") as "[? Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iFrame.
  rewrite map_union_empty -insert_union_singleton_l.
  iFrame.
  iIntros "!>". by iApply "HΦ".
Qed.

Lemma twp_allocN_seq (N : nat) (z : Z) E v s:
  TCEq N (Z.to_nat z) →
  (0 < N)%Z →
  [[{ True }]]
    AllocN (Val $ LitV $ LitInt $ z) (Val v) @ s; E
  [[{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 N, (l +ₗ (i : nat)) ↦ v }]].
Proof.
  iIntros (-> Hn Φ) "_ HΦ".
  iApply twp_lift_atomic_head_step; [done|].
  iIntros (? σ1) "[Hh Ht] !#".
  iSplit.
  { iPureIntro.
    rewrite /head_reducible.
    eexists.
    apply head_step_support_equiv_rel.
    econstructor; eauto.
    lia.
  }
  iIntros "/=" (e2 σ2 Hs); inv_head_step.
  iMod ((ghost_map_insert_big _ _ with "Hh")) as "[$ Hl]".
  iIntros "!>". iFrame.
  iApply "HΦ".
  iInduction (H) as [ | ?] "IH" forall (σ1).
  - simpl.
    iSplit; auto.
    rewrite map_union_empty.
    rewrite loc_add_0.
    by rewrite big_sepM_singleton.
  - rewrite seq_S.
    rewrite heap_array_replicate_S_end.
    iPoseProof (big_sepM_union _ _ _ _ with "Hl") as "[H1 H2]".
    iApply big_sepL_app.
    iSplitL "H1".
    + iApply "IH".
      { iPureIntro. lia. }
      iApply "H1".
    + simpl. iSplit; auto.
      by rewrite big_sepM_singleton.
      Unshelve.
      {
        apply heap_array_map_disjoint.
        intros.
        apply not_elem_of_dom_1.
        by apply fresh_loc_offset_is_fresh.
      }
      apply heap_array_map_disjoint.
      intros.
      apply not_elem_of_dom_1.
      rewrite dom_singleton.
      apply not_elem_of_singleton_2.
      intros H2.
      apply loc_add_inj in H2.
      rewrite replicate_length in H1.
      lia.
Qed.

Lemma twp_load E l dq v s :
  [[{ l ↦{dq} v }]] Load (Val $ LitV $ LitLoc l) @ s; E [[{ RET v; l ↦{dq} v }]].
Proof.
  iIntros (Φ) "Hl HΦ".
  iApply twp_lift_atomic_head_step; [done|].
  iIntros (? σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  solve_red.
  iIntros "/=" (e2 σ2 Hs); inv_head_step.
  iFrame. iModIntro. by iApply "HΦ".
Qed.

Lemma twp_store E l v' v s :
  [[{ l ↦ v' }]] Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
  [[{ RET LitV LitUnit; l ↦ v }]].
Proof.
  iIntros (Φ) "Hl HΦ".
  iApply twp_lift_atomic_head_step; [done|].
  iIntros (? σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  solve_red.
  iIntros "/=" (e2 σ2 Hs); inv_head_step.
  iMod (ghost_map_update with "Hh Hl") as "[$ Hl]".
  iFrame. iModIntro. by iApply "HΦ".
Qed.

Lemma twp_rand (N : nat) (z : Z) E s :
  TCEq N (Z.to_nat z) →
  [[{ True }]] rand #z @ s; E [[{ (n : fin (S N)), RET #n; True }]].
Proof.
  iIntros (-> Φ) "_ HΦ".
  iApply twp_lift_atomic_head_step; [done|].
  iIntros (? σ1) "Hσ !#".
  solve_red.
  iIntros (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  by iApply ("HΦ" $! x) .
Qed.


(** Tapes  *)
Lemma twp_alloc_tape N z E s :
  TCEq N (Z.to_nat z) →
  [[{ True }]] alloc #z @ s; E [[{ α, RET #lbl:α; α ↪ (N; []) }]].
Proof.
  iIntros (-> Φ) "_ HΦ".
  iApply twp_lift_atomic_head_step; [done|].
  iIntros (? σ1) "(Hh & Ht) !# /=".
  solve_red.
  iIntros (e2 σ2 Hs); inv_head_step.
  iMod (ghost_map_insert (fresh_loc σ1.(tapes)) with "Ht") as "[$ Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iFrame. iModIntro.
  by iApply "HΦ".
Qed.

Lemma twp_rand_tape N α n ns z E s :
  TCEq N (Z.to_nat z) →
  [[{ α ↪ (N; n :: ns) }]] rand(#lbl:α) #z @ s; E [[{ RET #(LitInt n); α ↪ (N; ns) }]].
Proof.
  iIntros (-> Φ) "Hl HΦ".
  iApply twp_lift_atomic_head_step; [done|].
  iIntros (? σ1) "(Hh & Ht) !#".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  solve_red.
  iIntros (e2 σ2 Hs).
  inv_head_step.
  iMod (ghost_map_update with "Ht Hl") as "[$ Hl]".
  iFrame. iModIntro.
  by iApply "HΦ".
Qed.

Lemma twp_rand_tape_empty N z α E s :
  TCEq N (Z.to_nat z) →
  [[{ α ↪ (N; []) }]] rand(#lbl:α) #z @ s; E [[{ (n : fin (S N)), RET #(LitInt n); α ↪ (N; []) }]].
Proof.
  iIntros (-> Φ) "Hl HΦ".
  iApply twp_lift_atomic_head_step; [done|].
  iIntros (? σ1) "(Hh & Ht) !#".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  solve_red.
  iIntros (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iModIntro. iApply ("HΦ" with "[$Hl //]").
Qed.

Lemma twp_rand_tape_wrong_bound N M z α E ns s :
  TCEq N (Z.to_nat z) →
  N ≠ M →
  [[{ α ↪ (M; ns) }]] rand(#lbl:α) #z @ s; E [[{ (n : fin (S N)), RET #(LitInt n); α ↪ (M; ns) }]].
Proof.
  iIntros (-> ? Φ) "Hl HΦ".
  iApply twp_lift_atomic_head_step; [done|].
  iIntros (? σ1) "(Hh & Ht) !#".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  solve_red.
  iIntros (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iModIntro.
  iApply ("HΦ" with "[$Hl //]").
Qed.


(** A rule for error amplification for recursive functions *)
Lemma twp_rec_err E f x e ε k Φ Ψ :
  (0 < ε)%R ->
  (1 < k)%R ->
  □ (∀ ε', □ (∀ v, ↯ (k*ε') -∗ Ψ v -∗ WP (rec: f x := e)%V v @ E [{ Φ }]) -∗
      ∀ v, ↯ ε' -∗ Ψ v -∗ WP (subst' x v (subst' f (rec: f x := e) e)) @ E [{ Φ }]) -∗
  ∀ v, ↯ ε -∗ Ψ v -∗ WP (rec: f x := e)%V v @ E [{ Φ }].
Proof.
  iIntros (Hε Hk).
  iIntros "#Hrec".
  iIntros (v) "Herr Hv".
  iRevert (v) "Hv".
  iApply (ec_ind_amp _ k with "[] Herr"); auto.
  iModIntro.
  iIntros (ε') "%Hε' #IH Herr'".
  iIntros (v) "Hv".
  iApply total_lifting.twp_pure_step_fupd; first done.
  iApply ("Hrec" with "[] Herr' Hv").
  iModIntro.
  iIntros (w) "Hkerr Hw".
  iApply ("IH" with "Hkerr Hw").
Qed.


End total_primitive_laws.
