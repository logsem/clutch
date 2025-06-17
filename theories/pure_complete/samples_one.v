From stdpp Require Import prelude coPset namespaces.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list.
From clutch.common Require Import language ectx_language ectxi_language locations.
From clutch.prelude Require Import fin.
From clutch.prob_lang Require Import notation lang.
From clutch.prob_lang.spec Require Import spec_ra spec_rules spec_tactics.
From clutch.approxis Require Import ectx_lifting app_weakestpre model.
From clutch.approxis Require Export proofmode primitive_laws coupling_rules.
From clutch.base_logic Require Export spec_update.
From clutch.pure_complete Require Import pure tachis_ert prob_additional.
From Coq.Logic Require Import ClassicalEpsilon.
Local Open Scope R.

Inductive SamplesOneTape : loc -> expr -> Prop :=
  | SamplesOneTapeRand t :
    SamplesOneTape t (Rand #2 (Val (LitV (LitLbl t))))
  | SamplesOneTapeIf t e2 e3 e4 (H1 : SamplesOneTape t e2) (H2 : SamplesOneTape t e3) (H3 : SamplesOneTape t e4) :
    SamplesOneTape t (if: e2 then e3 else e4)%E
  | SamplesOneTapeVar t s : 
    SamplesOneTape t (Var s)
  | SamplesOneTapePair t e2 e3 (H : SamplesOneTape t e2) (H1 : SamplesOneTape t e3) :
    SamplesOneTape t (Pair e2 e3)
  | SamplesOneTapeFst t e2 (H : SamplesOneTape t e2) :
    SamplesOneTape t (Fst e2)
  | SamplesOneTapeSnd t e2 (H : SamplesOneTape t e2) :
    SamplesOneTape t (Snd e2)
  | SamplesOneTapeInjL t e2 (H : SamplesOneTape t e2) :
    SamplesOneTape t (InjL e2)
  | SamplesOneTapeInjR t e2 (H : SamplesOneTape t e2) :
    SamplesOneTape t (InjR e2)
  | SamplesOneTapeCase t e2 e3 e4 (H : SamplesOneTape t e2) (H1 : SamplesOneTape t e3) (H2 : SamplesOneTape t e4) :
    SamplesOneTape t (Case e2 e3 e4)
  | SamplesOneTapeRec f x t e2 (H : SamplesOneTape t e2) :
    SamplesOneTape t (Rec f x e2)
  | SamplesOneTapeApp t e2 e3 (H : SamplesOneTape t e2) (H1 : SamplesOneTape t e3) :
    SamplesOneTape t (App e2 e3)
  | SamplesOneTapeTick t e2 (H : SamplesOneTape t e2) :
    SamplesOneTape t (Tick e2)
  | SamplesOneTapeUnOp t e2 (H : SamplesOneTape t e2) (op : un_op) :
    SamplesOneTape t (UnOp op e2)
  | SamplesOneTapeBinOp t e2 e3 (H : SamplesOneTape t e2) (H1 : SamplesOneTape t e3) (op : bin_op) :
    SamplesOneTape t (BinOp op e2 e3)
  | SamplesOneTapeVal t v (H : SamplesOneTapeV t v) :
    SamplesOneTape t (Val v)
with SamplesOneTapeV : loc -> val -> Prop :=
  | SamplesOneTapeVRecV f x t e2 (H : SamplesOneTape t e2) :
    SamplesOneTapeV t (RecV f x e2)
  | SamplesOneTapeVPairV v1 v2 t (H : SamplesOneTapeV t v1) (H1 : SamplesOneTapeV t v2) :
    SamplesOneTapeV t (PairV v1 v2)
  | SamplesOneTapeVInjLV v t (H : SamplesOneTapeV t v) :
    SamplesOneTapeV t (InjLV v)
  | SamplesOneTapeVInjRV v t (H : SamplesOneTapeV t v) :
    SamplesOneTapeV t (InjRV v)
  | SamplesOneTapeVLitV v t :
    SamplesOneTapeV t (LitV v)
.

Inductive SamplesOneTapeItem (t : loc) : ectx_item -> Prop :=
  | SamplesOneTapeItemAppLCtx v : SamplesOneTapeV t v -> SamplesOneTapeItem t (AppLCtx  v)
  | SamplesOneTapeItemAppRCtx e : SamplesOneTape t e -> SamplesOneTapeItem t (AppRCtx  e)
  | SamplesOneTapeItemUnOpCtx op : SamplesOneTapeItem t (UnOpCtx  op)
  | SamplesOneTapeItemBinOpLCtx op v : SamplesOneTapeV t v -> SamplesOneTapeItem t (BinOpLCtx op v)
  | SamplesOneTapeItemBinOpRCtx op e : SamplesOneTape t e -> SamplesOneTapeItem t (BinOpRCtx op e)
  | SamplesOneTapeItemIfCtx e1 e2 : SamplesOneTape t e1 -> SamplesOneTape t e2 -> SamplesOneTapeItem t (IfCtx e1 e2)
  | SamplesOneTapeItemPairLCtx v : SamplesOneTapeV t v -> SamplesOneTapeItem t (PairLCtx v)
  | SamplesOneTapeItemPairRCtx e : SamplesOneTape t e -> SamplesOneTapeItem t (PairRCtx e)
  | SamplesOneTapeItemFstCtx : SamplesOneTapeItem t FstCtx
  | SamplesOneTapeItemSndCtx : SamplesOneTapeItem t SndCtx
  | SamplesOneTapeItemInjLCtx : SamplesOneTapeItem t InjLCtx
  | SamplesOneTapeItemInjRCtx : SamplesOneTapeItem t InjRCtx
  | SamplesOneTapeItemCaseCtx e1 e2 : SamplesOneTape t e1 -> SamplesOneTape t e2 -> SamplesOneTapeItem t (CaseCtx e1 e2)
  | SamplesOneTapeItemTickCtx : SamplesOneTapeItem t TickCtx.

Lemma SamplesOneTape_fill_item Ki e l :
  SamplesOneTape l e ->
  SamplesOneTapeItem l Ki ->
  SamplesOneTape l (fill_item Ki e).
Proof.
  intros.
  inversion H0; simpl; 
  try econstructor; eauto;
  try econstructor; eauto.
Qed.

Lemma SamplesOneTape_fill K e l :
  SamplesOneTape l e ->
  Forall (SamplesOneTapeItem l) K ->
  SamplesOneTape l (fill K e).
Proof.
  intros. 
  revert e H.
  induction K; auto. 
  intros. simpl.
  inversion H0; subst.
  apply IHK; auto.
  by apply SamplesOneTape_fill_item. 
Qed.

Lemma SamplesOneTape_head l e ei e' : 
  SamplesOneTape l e ->
  decomp_item e = Some (ei, e') ->
  SamplesOneTape l e'.
Proof.
  intros.
  inversion H; subst; simpl in *; inversion H0;
  try (destruct e2; inversion H3; done);
  try (destruct e3; destruct e2; inversion H4; done);
  (destruct e2; inversion H5; done). 
Qed.

Lemma SamplesOneTape_ectx e l :
  SamplesOneTape l e ->
  Forall (SamplesOneTapeItem l)(decomp e).1.
Proof.
  simpl.
  destruct (decomp e) eqn : Hde.
  remember (length l0).
  revert e e0 l0 Hde Heqn.
  induction n.
  {
    intros.
    destruct l0; inversion Heqn.
    apply decomp_inv_nil in Hde as [Hd Hde].
    by subst e.
  }
  intros.
  rewrite decomp_unfold in Hde.
  destruct (ectxi_language.decomp_item e) eqn : Hde'; intros.
  2: {inversion Hde. by subst e. }
  destruct p.
  destruct (decomp e2) eqn: Hde2.
  inversion Hde. subst.
  apply Forall_app_2. 
  {
    eapply IHn.
    - apply Hde2.
    - rewrite app_length Nat.add_1_r in Heqn. by inversion Heqn.
    - simpl in *.
      eapply SamplesOneTape_head; eauto.
  }
  apply Forall_singleton. 
  simpl in *.
  rewrite /decomp_item in Hde'.
  inversion H; subst; simpl in *;
  try by inversion Hde';
  try (destruct e3; inversion Hde'; econstructor; done);
  try (destruct e4; destruct e3; inversion Hde'; econstructor; auto; by inversion H1). 
Qed.
  
Lemma SamplesOneTape_decomp l e : 
  SamplesOneTape l e ->
  SamplesOneTape l (decomp e).2.
Proof.
  destruct (decomp e) eqn : Hde.
  simpl.
  remember (length l0).
  revert e l0 e0 Hde Heqn.
  induction n.
  {
    intros.
    destruct l0; simpl in *; try by inversion Heqn.
    apply decomp_inv_nil in Hde as [Hd Hde].
    by subst.
  }
  intros.
  rewrite decomp_unfold in Hde.
  destruct (ectxi_language.decomp_item e) eqn : Hde'; intros.
  2: {inversion Hde. by subst e. }
  destruct p.
  destruct (decomp e2) eqn: Hde2.
  inversion Hde. subst.
  assert (n = length l1).
  { 
    rewrite app_length in Heqn. 
    rewrite Nat.add_1_r in Heqn. auto.
  }
  apply (IHn _ _ _ Hde2 H0).
  by eapply SamplesOneTape_head. 
Qed.

Lemma SamplesOneTape_decomp' l e e' Ks : 
  SamplesOneTape l e ->
  decomp e = (Ks, e') ->
  SamplesOneTape l e'.
Proof.
  intros.
  replace e' with (decomp e).2.
  2 : by rewrite H0.
  by apply SamplesOneTape_decomp.
Qed.

Lemma SamplesOneTape_head_step_det l e σ v t e' σ':
  SamplesOneTape l e ->
  σ.(tapes) !! l = Some (2%nat ; v :: t) ->
  head_step e σ (e', σ') > 0 ->
  head_step e σ (e', σ') = 1.
Proof.
  intros.
  destruct e; inv_head_step;
  try by inversion H;
  try by apply dret_1. 
  - inversion H; subst. 
    rewrite H0 in H8. inversion H8.
  - inversion H; subst. rewrite H0 in H8. 
    inversion H8. rewrite -H3 in H1. lia. 
Qed.

Lemma SamplesOneTape_head_step_tape l e σ v t e' σ':
  SamplesOneTape l e ->
  σ.(tapes) !! l = Some (2%nat ; v :: t) ->
  head_step e σ (e', σ') > 0 ->
  σ'.(tapes) = σ.(tapes) ∨ σ'.(tapes) = <[l := (2%nat ; t)]>σ.(tapes).
Proof.
  intros.
  destruct e; inv_head_step; 
  auto; inversion H.
  subst. rewrite H8 in H0. inversion H0; subst.
  by right. 
Qed.


Lemma SamplesOneTape_head_step_heap l e σ v t e' σ':
  SamplesOneTape l e ->
  σ.(tapes) !! l = Some (2%nat; v :: t) ->
  head_step e σ (e', σ') > 0 ->
  σ'.(heap) = σ.(heap).
Proof.
  intros.
  destruct e; inv_head_step; 
  auto; inversion H. 
Qed.

Lemma SamplesOneTape_step_det l e σ v t e' σ':
  SamplesOneTape l e ->
  σ.(tapes) !! l = Some (2%nat; v :: t) ->
  step (e, σ) (e', σ') > 0 ->
  step (e, σ) (e', σ') = 1.
Proof.
  rewrite /step.
  simpl. rewrite /prim_step.
  intros. simpl in *. 
  destruct (decomp e) eqn : Hde.
  rewrite Hde.
  rewrite Hde in H1.
  apply dmap_pos in H1 as [(e1 & σ1) (?&?)].
  eapply dmap_one.
  - eapply SamplesOneTape_head_step_det; eauto.
    eapply SamplesOneTape_decomp'; eauto.
  - eauto.
Qed.

Lemma SamplesOneTape_step_det' l e σ v t e' σ':
  SamplesOneTape l e ->
  σ.(tapes) !! l = Some (2%nat; v :: t) ->
  step (e, σ) (e', σ') > 0 ->
  step (e, σ) = dret (e', σ').
Proof.
  intros.
  by eapply pmf_1_eq_dret, SamplesOneTape_step_det. 
Qed.

Lemma SamplesOneTape_step_tapes l e σ v t e' σ':
  SamplesOneTape l e ->
  σ.(tapes) !! l = Some (2%nat; v :: t) ->
  step (e, σ) (e', σ') > 0 ->
  σ'.(tapes) = σ.(tapes) ∨ σ'.(tapes) = <[l := (2%nat; t)]>σ.(tapes). 
Proof.
  rewrite /step.
  simpl. rewrite /prim_step.
  intros. simpl in *. 
  destruct (decomp e) eqn : Hde.
  rewrite Hde in H1.
  apply dmap_pos in H1 as [(e1 & σ1) (?&?)].
  inversion H1; subst.
  eapply SamplesOneTape_head_step_tape.
  - eapply SamplesOneTape_decomp'; eauto.
  - eauto.
  - eauto.
Qed. 

Lemma SamplesOneTape_step_heap l e σ v t e' σ':
  SamplesOneTape l e ->
  σ.(tapes) !! l = Some (2%nat; v :: t) ->
  step (e, σ) (e', σ') > 0 ->
  σ'.(heap) = σ.(heap) .
Proof.
  rewrite /step.
  simpl. rewrite /prim_step.
  intros. simpl in *. 
  destruct (decomp e) eqn : Hde.
  rewrite Hde in H1.
  apply dmap_pos in H1 as [(e1 & σ1) (?&?)].
  inversion H1; subst.
  eapply SamplesOneTape_head_step_heap. 
  - eapply SamplesOneTape_decomp'; eauto.
  - eauto.
  - eauto.
Qed.

Lemma SamplesOneTape_head_step_expr_var l e σ1 σ2 v t e'1 σ'1 e'2 σ'2:
  SamplesOneTape l e ->
  σ1.(tapes) !! l = Some (2%nat; v :: t) -> 
  σ2.(tapes) !! l = Some (2%nat; v :: t) ->
  head_step e σ1 (e'1, σ'1) > 0 ->
  head_step e σ2 (e'2, σ'2) > 0 ->
  e'1 = e'2.
Proof. 
  intros.
  destruct e; inv_head_step; 
  auto; inversion H; subst;
  try (rewrite H14 in H0; inversion H0); 
  try (rewrite H10 in H1; inversion H1);
  subst; try lia. 
  apply inj_pair2 in H3, H5. by subst.  
Qed.

Lemma SamplesOneTape_step_expr_var l e σ1 σ2 v t e'1 σ'1 e'2 σ'2:
  SamplesOneTape l e ->
  σ1.(tapes) !! l = Some (2%nat; v :: t) -> 
  σ2.(tapes) !! l = Some (2%nat; v :: t) ->
  step (e, σ1) (e'1, σ'1) > 0 ->
  step (e, σ2) (e'2, σ'2) > 0 ->
  e'1 = e'2.
Proof.
  rewrite /step.
  simpl. rewrite /prim_step.
  intros. simpl in *. 
  destruct (decomp e) eqn : Hde. 
  rewrite Hde in H2.
  apply dmap_pos in H2 as [(?&?) (?&?)].
  inversion H2; subst. 
  rewrite Hde in H3.
  apply dmap_pos in H3 as [(?&?) (?&?)]. 
  inversion H3; subst. 
  f_equal.
  eapply SamplesOneTape_head_step_expr_var. 
  - eapply SamplesOneTape_decomp'; eauto. 
  - apply H0.
  - apply H1.
  - eauto.
  - eauto. 
Qed.

Lemma SamplesOneTape_head_step_state_var l e σ1 σ2 v t e'1 σ'1 e'2 σ'2:
  SamplesOneTape l e ->
  σ1.(tapes) !! l = Some (2%nat; v :: t) -> 
  σ2.(tapes) !! l = Some (2%nat; v :: t) ->
  head_step e σ1 (e'1, σ'1) > 0 ->
  head_step e σ2 (e'2, σ'2) > 0 ->
  σ'1.(tapes) !! l = σ'2.(tapes) !! l .
Proof. 
  intros.
  destruct e; inv_head_step; 
  auto; inversion H; subst;
  try (rewrite H14 in H0; inversion H0); 
  try (rewrite H10 in H1; inversion H1);
  subst; try lia. 
  apply inj_pair2 in H4, H6. subst. 
  by rewrite !lookup_insert.   
Qed.

Lemma SamplesOneTape_step_state_var l e σ1 σ2 v t e'1 σ'1 e'2 σ'2:
  SamplesOneTape l e ->
  σ1.(tapes) !! l = Some (2%nat; v :: t) -> 
  σ2.(tapes) !! l = Some (2%nat; v :: t) ->
  step (e, σ1) (e'1, σ'1) > 0 ->
  step (e, σ2) (e'2, σ'2) > 0 ->
  σ'1.(tapes) !! l = σ'2.(tapes) !! l .
Proof. 
  rewrite /step.
  simpl. rewrite /prim_step.
  intros. simpl in *. 
  destruct (decomp e) eqn : Hde. 
  rewrite Hde in H2.
  apply dmap_pos in H2 as [(?&?) (?&?)].
  inversion H2; subst. 
  rewrite Hde in H3.
  apply dmap_pos in H3 as [(?&?) (?&?)]. 
  inversion H3; subst. 
  eapply SamplesOneTape_head_step_state_var. 
  - eapply SamplesOneTape_decomp'; eauto. 
  - apply H0.
  - apply H1.
  - eauto.
  - eauto. 
Qed.

Lemma SamplesOneTape_head_step_pos_var l e σ1 σ2  t e' σ'1:
  SamplesOneTape l e ->
  σ1.(tapes) !! l = Some (2%nat; t) -> 
  σ2.(tapes) !! l = Some (2%nat; t) ->
  head_step e σ1 (e', σ'1) > 0 ->
  ∃ σ'2, head_step e σ2 (e', σ'2) > 0.
Proof.
  intros. 
  inversion H;
  inv_head_step; 
  try (econstructor; erewrite dret_1_1; try lra; reflexivity);
  try (by inversion H). 
  econstructor. eapply dmap_pos. econstructor; eauto.  
Qed. 

Lemma SamplesOneTape_step_pos_var l e σ1 σ2 t e' σ'1:
  SamplesOneTape l e ->
  σ1.(tapes) !! l = Some (2%nat; t) -> 
  σ2.(tapes) !! l = Some (2%nat; t) ->
  step (e, σ1) (e', σ'1) > 0 ->
  ∃ σ'2, step (e, σ2) (e', σ'2) > 0.
Proof.
  rewrite /step.
  simpl. rewrite /prim_step.
  intros. simpl in *. 
  destruct (decomp e) eqn : Hde. 
  rewrite Hde in H2.
  apply dmap_pos in H2 as [(?&?) (?&?)].
  inversion H2; subst. 
  rewrite Hde. 
  eapply SamplesOneTape_head_step_pos_var in H3 as [σ'2 H3]; eauto. 
  2 : {eapply SamplesOneTape_decomp'; eauto. }
  exists σ'2. 
  apply dmap_pos. 
  exists (e1, σ'2). 
  split; auto.
Qed.
  
(* 
Lemma SamplesOneTape_head_step_state_rel l e σ1 σ2:
  SamplesOneTape l e ->
  σ1.(tapes) !! l = σ2.(tapes) !! l ->
  ∀ e' σ'1, ∃ σ'2, 
  σ'1.(tapes) !! l = σ'2.(tapes) !! l ∧
  head_step e σ1 (e', σ'1) = head_step e σ2 (e', σ'2).
Proof.
  intros.
  (* destruct (tapes σ1 !! l) eqn : Ht.  *)
  destruct (decide (head_step e σ1 (e', σ'1) > 0)). 2 : {

    admit.
  } 
  
  assert ( ∀ x1 : fin (S (Z.to_nat 2)), dmap (λ n : fin (S (Z.to_nat 2)), (#n : expr, σ1)) (dunifP (Z.to_nat 2)) (#x1 : expr, σ1) = dmap (λ n : fin (S (Z.to_nat 2)), (#n : expr, σ2)) (dunifP (Z.to_nat 2)) (#x1 : expr, σ2)) as H'. {
    intros. 
    erewrite !dmap_unif_nonzero; auto; 
    move => a b Ha; inversion Ha; 
    by apply Nat2Z.inj, fin_to_nat_inj in H2. 
  }

  inversion H; inv_head_step;
  try (econstructor; split; eauto; rewrite !dret_1_1; auto; done);
  try (rewrite H0 H5 in H1; inversion H1; done);
  try (rewrite H1 H4 in H0; inversion H0; done).  
  - rewrite H1 H5 in H0. inversion H0; subst. 
    apply inj_pair2 in H4; subst. 
    set σ'2 := (state_upd_tapes <[l:=(Z.to_nat 2; l3)]> σ2). 
    exists σ'2. unfold σ'2. simpl. rewrite lookup_insert. 
    split; auto. rewrite !dret_1_1; auto. 
    apply inj_pair2 in H3; by subst. 
  - rewrite H1 H4 in H0. inversion H0; subst. 
    apply inj_pair2 in H7; subst. econstructor; split; eauto.
Admitted.   *)

Lemma SamplesOneTape_head_step_state_rel' l t e σ1 σ2:
  SamplesOneTape l e ->
  σ1.(tapes) !! l = σ2.(tapes) !! l ->
  σ1.(tapes) !! l = Some (2%nat; t) ->
  ∃ μ t', 
    head_step e σ1 = dmap (fun e' => (e', state_upd_tapes <[l:=(2%nat; t')]> σ1)) μ ∧
    head_step e σ2 = dmap (fun e' => (e', state_upd_tapes <[l:=(2%nat; t')]> σ2)) μ. 
Proof. 
  intros.
  pose proof H1 as H1'. rewrite H0 in H1'.
  (* destruct (ExcludedMiddle (∃ e' σ', head_step e σ1 (e', σ') > 0)). 2 : {
    pose proof (not_exists_forall_not _ _ H2) as H2'. 
    assert (head_step e σ1 = dzero). {
      apply dzero_ext.
      intros. 
      apply Rle_antisym; try real_solver.
      
      (* apply Rle_antisym; try real_solver.
      
      simpl in *.
      real_solver. *)
    }
    admit. 
  }
  destruct H2 as [e' [σ' Hst]]. *) 
  destruct (ExcludedMiddle (∃ ρ, head_step e σ1 ρ > 0)). 
  2 : { 
    pose proof (not_exists_forall_not _ _ H2) as H2'. 
    destruct (ExcludedMiddle (∃ ρ, head_step e σ2 ρ > 0)).
    { 
      destruct H3 as [[e' σ'] Hst]. 
      eapply (SamplesOneTape_head_step_pos_var _ _ _ σ1) in Hst; eauto. 
      destruct Hst. exfalso. apply H2. by exists (e', x).    
    }
    pose proof (not_exists_forall_not _ _ H3) as H3'. 
    exists dzero, t. 
    simpl in *. rewrite !dmap_dzero.
    split; apply distr_ext; intros;
    rewrite dzero_0. 
    - specialize (H2' a). apply Rle_antisym; real_solver. 
    - specialize (H3' a). apply Rle_antisym; real_solver. 
  } 
  destruct H2 as [[e' σ'] Hst]. 
  inversion H; inv_head_step; simpl;
  try (destruct σ1, σ2; eexists (dret _), t; rewrite !dmap_dret; split;
    simpl; rewrite insert_id; auto). 
  - destruct σ1, σ2. 
    exists (dmap (λ n : fin 3, (#n : expr)) (dunifP 2)), [].  
    rewrite !dmap_comp. split; f_equal; apply functional_extensionality;
    intros; simpl in *; rewrite insert_id; auto.
  - destruct σ1, σ2; simpl in *. eexists (dret _), l0. rewrite !dmap_dret.
    split; auto. 
Qed.

Lemma SamplesOneTape_step_state_rel' l t e σ1 σ2:
  SamplesOneTape l e ->
  σ1.(tapes) !! l = σ2.(tapes) !! l ->
  σ1.(tapes) !! l = Some (2%nat; t) ->
  ∃ μ t', 
    step (e, σ1) = dmap (fun e' => (e', state_upd_tapes <[l:=(2%nat; t')]> σ1)) μ ∧
    step (e, σ2) = dmap (fun e' => (e', state_upd_tapes <[l:=(2%nat; t')]> σ2)) μ. 
Proof.
  rewrite /step.
  simpl. rewrite /prim_step.
  intros. simpl in *. 
  destruct (decomp e) eqn : Hde.
  rewrite !Hde. 
  pose proof Hde as Hde'.
  eapply SamplesOneTape_decomp' in Hde'; eauto. 
  edestruct SamplesOneTape_head_step_state_rel' as [μ0 [t' [Hd1 Hd2]]];
  eauto. 
  rewrite Hd1 Hd2. 
  rewrite !dmap_comp. 
  replace (fill_lift l0 ∘ λ e' : expr, (e', state_upd_tapes <[l:=(2%nat; t')]> σ1)) with ((λ e' : expr, (e', state_upd_tapes <[l:=(2%nat; t')]> σ1)) ∘ (fill l0)). 
  2 : by apply functional_extensionality. 
  replace (fill_lift l0 ∘ λ e' : expr, (e', state_upd_tapes <[l:=(2%nat; t')]> σ2)) with ((λ e' : expr, (e', state_upd_tapes <[l:=(2%nat; t')]> σ2)) ∘ (fill l0)). 
  2 : by apply functional_extensionality.
  rewrite -!dmap_comp. 
  econstructor; eauto.
Qed.

(* Lemma SamplesOneTape_step_state_rel l e σ1 σ2:
  SamplesOneTape l e ->
  σ1.(tapes) !! l = σ2.(tapes) !! l ->
  ∀ e' σ'1, ∃ σ'2, 
  σ'1.(tapes) !! l = σ'2.(tapes) !! l ∧
  step (e, σ1) (e', σ'1) = step (e, σ2) (e', σ'2).
Proof.
  intros.

Admitted. *)

(* Lemma SamplesOneTape_exec_state_rel l e σ1 σ2 n:
  SamplesOneTape l e ->
  σ1.(tapes) !! l = σ2.(tapes) !! l ->
  exec n (e, σ1) = exec n (e, σ2).
Proof.
  revert e σ1 σ2.
  induction n. {
    intros. 
    rewrite exec_unfold. simpl. 
    destruct (to_val e) eqn : Hve; auto.
  }
  intros.
  rewrite !exec_Sn. 
  apply distr_ext. 
  intros.
  rewrite !dbind_unfold_pmf.
  Search (Bij). 
Admitted. *)

Lemma SamplesOneTape_subst l x v e : 
  SamplesOneTape l e ->
  SamplesOneTapeV l v ->
  SamplesOneTape l (subst x v e).
Proof.
  intros.
  induction e; simpl; auto;
  try (inversion H; subst; case_decide; auto; econstructor; by eauto); 
  try (inversion H; subst; econstructor; by eauto).  
Qed.

Lemma SamplesOneTape_head_inv l e σ e' σ':
  SamplesOneTape l e ->
  head_step e σ (e', σ') > 0 ->
  SamplesOneTape l e'.
Proof.
  intros.
  inversion H; inv_head_step;
  auto;
  try (inversion H1; inversion H5; subst; econstructor; eauto; econstructor; done);
  try (do 2 econstructor; done); 
  try (econstructor; econstructor; inversion H1; inversion H2; subst; done);
  try (inversion H1; inversion H3; subst; econstructor; done). 
  - inversion H1. inversion H4. inversion H2. subst. 
    destruct x, f; simpl; auto; 
    apply SamplesOneTape_subst; auto;
    apply SamplesOneTape_subst; auto.
  - destruct op; destruct v; inversion H3;
    destruct l0; inversion H3; do 2 econstructor. 
  - destruct op, v; inversion H5; 
    try (destruct l0; inversion H5; destruct v0; inversion H5;
    destruct l0; inversion H5; econstructor; try econstructor;
    destruct l1; inversion H5; by econstructor);
    try (unfold bin_op_eval in *;
    case_decide; try contradiction; case_decide; inversion H5;
    subst; do 2 econstructor). 
Qed.

Lemma SamplesOneTape_inv l e σ e' σ':
  SamplesOneTape l e ->
  step (e, σ) (e', σ') > 0 ->
  SamplesOneTape l e'.
Proof.
  unfold step.
  simpl. unfold prim_step.
  intros. 
  destruct (decomp e) eqn : Hde.
  simpl in *.
  rewrite Hde dmap_pos in H0.
  destruct H0 as [[e1 σ1] [Hfl Hs]].
  inversion Hfl.
  apply SamplesOneTape_fill.
  - eapply SamplesOneTape_head_inv.
    + eapply (SamplesOneTape_decomp'); last first; eauto.  
    + eauto.
  - replace l0 with (decomp e).1; try by rewrite Hde. 
    by apply SamplesOneTape_ectx. 
Qed. 

Lemma SamplesOneTape_exec_state_rel' l t e σ1 σ2 n:
  SamplesOneTape l e ->
  σ1.(tapes) !! l = σ2.(tapes) !! l ->
  σ1.(tapes) !! l = Some (2%nat; t) -> 
  exec n (e, σ1) = exec n (e, σ2).
Proof.
  revert e t σ1 σ2.
  induction n. {
    intros. 
    rewrite exec_unfold. simpl. 
    destruct (to_val e) eqn : Hve; auto.
  }
  intros.
  rewrite !exec_Sn. 
  apply distr_ext. 
  intros.
  destruct (to_val e) eqn : Hve. {
    rewrite !step_or_final_is_final; unfold is_final, to_final; simpl; auto.   
    rewrite !dret_id_left'.  
    f_equal. eapply IHn; eauto.
  }
  rewrite !step_or_final_no_final; unfold is_final, to_final; simpl; try by rewrite Hve.
  edestruct (SamplesOneTape_step_state_rel') as [μ [t' [Hs1 Hs2]]]; eauto. 
  simpl in *.
  rewrite Hs1 Hs2.  
  rewrite -!dmap_fold -!dbind_assoc'. f_equal.
  apply dbind_ext_right_strong. 
  intros.
  rewrite !dret_id_left'.  
  eapply IHn; simpl; try by rewrite !lookup_insert. 
  eapply SamplesOneTape_inv; eauto.
  simpl. erewrite Hs1. 
  eapply dmap_pos. 
  econstructor; eauto.  
Qed.

Lemma SamplesOneTape_lim_exec_state_rel l t e σ1 σ2:
  SamplesOneTape l e ->
  σ1.(tapes) !! l = σ2.(tapes) !! l ->
  σ1.(tapes) !! l = Some (2%nat; t) -> 
  lim_exec (e, σ1) = lim_exec (e, σ2).
Proof.
  intros.
  unfold lim_exec. 
  apply distr_ext. 
  intros. rewrite !lim_distr_pmf. 
  do 2 f_equal.  
  apply functional_extensionality.
  intros. f_equal. 
  erewrite SamplesOneTape_exec_state_rel';
  eauto. 
Qed.