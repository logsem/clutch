From stdpp Require Import coPset namespaces.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list.
From clutch.common Require Import language ectx_language ectxi_language locations.
From clutch.prelude Require Import fin.
From clutch.prob_lang Require Import notation lang.
From clutch.prob_lang.spec Require Import spec_ra spec_rules spec_tactics.
From clutch.approxis Require Import ectx_lifting app_weakestpre model.
From clutch.approxis Require Export proofmode primitive_laws coupling_rules.
From clutch.base_logic Require Export spec_update.
From clutch.pure_complete Require Import pure tachis_ert.

Local Open Scope R.

Lemma exec_pos_step_pos {δ : markov} (x : mstate δ) n :
  to_final x = None ->
  SeriesC (exec n x) > 0 ->
  ∃ y, step x y > 0.
Proof.
  intros.
  destruct (ExcludedMiddle (∃ y, step x y > 0)); auto.
  pose proof (not_exists_forall_not _ _ H1).
  assert (SeriesC (exec n x) = 0).
  2 : { rewrite H3 in H0. lra. }
  simpl in *.
  apply SeriesC_0.
  intros.
  rewrite exec_unfold H.
  destruct n; auto.
  replace (step x) with (dzero : distr (mstate δ)).
  { by rewrite dbind_dzero_pmf. }
  erewrite dzero_ext; auto.
  intros.
  apply Rle_antisym; auto.
  specialize (H2 a).
  lra. 
Qed.

Lemma dmap_one `{Countable A, Countable B} (μ : distr A) (f : A -> B) a b :
  μ a = 1 ->
  b = f a ->
  dmap f μ b = 1.
Proof.
  intros.
  apply pmf_1_eq_dret in H1.
  subst. 
  rewrite dmap_dret.
  by apply dret_1_1.
Qed.

Lemma SeriesC_0_nonneg `{Countable A} (f : A -> R):
  ex_seriesC f ->
  (∀ x, 0 <= f x) ->
  SeriesC f = 0 ->
  ∀ x, f x = 0.
Proof.
  intros ???.
  destruct (ExcludedMiddle (∀ x, f x = 0)); auto.
  pose proof (Classical_Pred_Type.not_all_ex_not _ _ H3) as (a & ?).
  assert (f a > 0). {
    specialize (H1 a). lra.
  }
  assert (f a <= 0). {
    rewrite -H2.
    apply pos_series_le_one; auto.
  }
  lra.
Qed.

Lemma dbind_det_inv1 `{Countable A, Countable B} (μ : distr A) (f : A -> distr B):
  SeriesC (dbind f μ) = 1 ->
  SeriesC μ = 1.
Proof.
  intros.
  rewrite dbind_mass in H1.
  apply Rle_antisym; auto.
  rewrite -H1.
  apply SeriesC_le; auto.
  intros.
  split.
  - apply Rmult_le_pos; auto.
  - rewrite -(Rmult_1_r (μ n)) Rmult_assoc. 
    apply Rmult_le_compat_l; auto; real_solver.
Qed.

Lemma dbind_det_inv2 `{Countable A, Countable B} (μ : distr A) (f : A -> distr B):
  SeriesC (dbind f μ) = 1 ->
  ∀ a, μ a > 0 ->  
  SeriesC (f a) = 1.
Proof.
  intros.
  apply dbind_det_inv1 in H1 as H3.
  rewrite dbind_mass in H1.
  rewrite -H1 in H3.
  assert (SeriesC (fun x => μ x * (1 - SeriesC (f x))) = 0). {
    erewrite SeriesC_ext. 
    2 : intros; by rewrite Rmult_minus_distr_l Rmult_1_r.
    rewrite SeriesC_minus; auto.
    { rewrite H3. real_solver. }
    apply (ex_seriesC_le _ μ); auto.
    split; try real_solver.
  }
  epose proof (SeriesC_0_nonneg _ _ _ H4 a).
  simpl in H5. 
  apply Rmult_integral in H5 as [H5 | H5]; lra.
  Unshelve.
  - apply (ex_seriesC_le _ μ); auto.
    split; try real_solver. 
    apply Rmult_le_pos; try real_solver. by apply Rle_0_le_minus. 
  - intros.
    simpl.
    apply Rmult_le_pos; try real_solver. by apply Rle_0_le_minus. 
Qed.

Lemma erasable_execN_det e μ σ n: 
  erasable μ σ ->
  SeriesC (exec n (e, σ)) = 1 ->
  ∀ σ', μ σ' > 0 ->
    SeriesC (exec n (e, σ')) = 1.
Proof.
  rewrite /erasable.
  intros.
  pose proof (H e n). 
  rewrite -H2 in H0. 
  eapply dbind_det_inv2 in H0; eauto.
Qed.
    

Definition is_det `{Countable A} (μ : distr A) :=
  ∃ a, μ = dret a.

Lemma is_det_bind `{Countable A, Countable B} (μ : distr A) (f : A -> distr B) :
  is_det μ ->
  (∀ a, μ a > 0 -> is_det (f a)) ->
  is_det (dbind f μ).
Proof.
  intros [a Ha] Hd.
  epose proof (Hd a _) as [b Hdb].
  exists b.
  apply pmf_1_eq_dret.
  rewrite dbind_unfold_pmf.
  rewrite Ha.
  pose proof (Expval_dret (fun x => f x b) a).
  unfold Expval in*.
  rewrite H1 Hdb.
  by apply dret_1.
  Unshelve.
  rewrite Ha.
  rewrite dret_1_1; auto; lra. 
Qed.

Lemma ARcoupl_map_rev `{Countable A, Countable B, Countable A', Countable B'} 
  (μ1 : distr A) (μ2 : distr B) (f1 : A → A') (f2 : B → B') ψ ε :
  ARcoupl (dmap f1 μ1) (dmap f2 μ2) ψ ε -> ARcoupl μ1 μ2 (fun x y =>  ψ (f1 x) (f2 y)) ε.
Proof.
  rewrite /ARcoupl.
  intros.
Admitted.

Definition skip_one (e : expr) := (λ: <>, e)%V #().

Lemma skip_one_after e σ: step (skip_one e, σ) = dret (e, σ).
Proof.
  simpl.
  rewrite /skip_one /prim_step.
  simpl.
  rewrite decomp_unfold.
  simpl. by rewrite dmap_dret.
Qed.

Inductive SamplesOneTape : loc -> expr -> Prop :=
  | SamplesOneTapeRand t e2 (H1 : SamplesOneTape t e2) :
    SamplesOneTape t (Rand e2 (Val (LitV (LitLoc t))))
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
  | SamplesOneTapeItemRandLCtx : SamplesOneTapeItem t (RandLCtx #t)
  | SamplesOneTapeItemTickCtx : SamplesOneTapeItem t TickCtx.


Lemma SamplesOneTape_presamples_n_val (l : loc) e σ n N t v:
  to_val e = Some v ->
  SeriesC (exec n (e, σ)) = 1 ->
  SamplesOneTape l e ->
  σ.(tapes) !! l = Some (N; t) ->
  ∃ μ, erasable μ σ ∧
    (∀ σ', μ σ' > 0 -> 
    σ'.(heap) = σ.(heap) ∧
    (∃ t', σ'.(tapes) = <[l:=(N; t')]>(σ.(tapes))) ∧
    is_det (exec n (e, σ'))).
Proof.
  intros.
  exists (dret σ).
  split.
  { apply dret_erasable. }
  intros.
  apply dret_pos in H3.
  subst.
  split; auto.
  split.
  2 : { erewrite exec_is_final; try by simpl. by econstructor. }
  exists t.
  rewrite insert_id; auto.
Qed.

Lemma SamplesOneTape_fill_item Ki e l :
  SamplesOneTape l e ->
  SamplesOneTapeItem l Ki ->
  SamplesOneTape l (fill_item Ki e).
Proof.
  intros.
  inversion H0; simpl; 
  econstructor; auto;
  econstructor; auto.
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

Lemma SamplesOneTape_head_step_det l e σ N v t e' σ':
  SamplesOneTape l e ->
  σ.(tapes) !! l = Some (N; v :: t) ->
  head_step e σ (e', σ') > 0 ->
  head_step e σ (e', σ') = 1.
Proof.
  intros.
  destruct e; inv_head_step;
  try by inversion H;
  try by apply dret_1.
Qed.

Lemma SamplesOneTape_head_step_tape l e σ N v t e' σ':
  SamplesOneTape l e ->
  σ.(tapes) !! l = Some (N; v :: t) ->
  head_step e σ (e', σ') > 0 ->
  σ'.(tapes) = σ.(tapes) ∨ σ'.(tapes) = <[l := (N; t)]>σ.(tapes).
Proof.
  intros.
  destruct e; inv_head_step; 
  auto; inversion H. 
Qed.

Lemma SamplesOneTape_step_det l e σ N v t e' σ':
  SamplesOneTape l e ->
  σ.(tapes) !! l = Some (N; v :: t) ->
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

Lemma SamplesOneTape_step_state l e σ N v t e' σ':
  SamplesOneTape l e ->
  σ.(tapes) !! l = Some (N; v :: t) ->
  step (e, σ) (e', σ') > 0 ->
  σ'.(tapes) = σ.(tapes) ∨ σ'.(tapes) = <[l := (N; t)]>σ.(tapes).
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
  
Lemma presamples_execN_det l σ n N t e:
  σ.(tapes) !! l = Some (N; t) ->
  (n <= length t)%nat ->
  SeriesC (exec n (e, σ)) = 1 ->
  SamplesOneTape l e -> 
  is_det (exec n (e, σ)).
Proof.
  revert σ e t.
  induction n.
  {
    intros.
    destruct (to_val e) eqn : Hve.
    { 
      erewrite exec_is_final; try by simpl.
      by econstructor. 
    }
    rewrite exec_O_not_final in H1; auto.
    rewrite dzero_mass in H1.
    lra.
  }
  intros.
  destruct (to_val e) eqn : Hve.
  { 
    erewrite exec_is_final; try by simpl.
    by econstructor. 
  }
  rewrite exec_Sn_not_final; auto.
  destruct t; simpl in H0; try lia.
  apply is_det_bind.
  {
    epose proof (exec_pos_step_pos (e, σ) (S n) _ _) as [[e' σ'] Hr].
    Unshelve.
    2 : auto.
    2 : rewrite H1; lra.
    exists (e', σ').
    apply pmf_1_eq_dret.
    eapply SamplesOneTape_step_det; eauto.
  }
  intros.
  destruct a as [e' σ'].
  rewrite exec_Sn_not_final in H1; auto.
  epose proof (dbind_det_inv2 _ _ H1 _ H3).
  epose proof (SamplesOneTape_step_state _ _ _ _ _ _ _ _ H2 H H3) as [Ht | Ht].
  - eapply IHn.
    + by rewrite Ht. 
    + simpl. lia.
    + auto.
    + by eapply SamplesOneTape_inv. 
  - eapply IHn.
    + rewrite Ht. rewrite lookup_insert. done.
    + lia.
    + auto.
    + by eapply SamplesOneTape_inv. 
Qed. 

Definition state_stepN σ l n := iterM n (λ σ', state_step σ' l) σ.

Lemma state_stepN_tape σ l n σ' N t : 
  σ.(tapes) !! l = Some (N; t) ->
  (state_stepN σ l n) σ' > 0 ->
  ∃ t', 
    length t' = n ∧
    σ'.(tapes) = <[l := (N; t ++ t')]>σ.(tapes).
Proof.
  intros.
  eapply metatheory.iterM_state_step_unfold in H.
  rewrite /state_stepN H in H0.
  apply dmap_pos in H0 as [t' [Ht Htd]].
  apply dunifv_pos in Htd.
  exists t'.
  split; auto.
  destruct σ'.
  by inversion Ht.
  Unshelve.
  apply n.
Qed.

Lemma state_stepN_heap σ l n σ' N t : 
  σ.(tapes) !! l = Some (N; t) ->
  (state_stepN σ l n) σ' > 0 ->
  σ.(heap) = σ'.(heap).
Proof.
  revert σ σ' t.
  induction n.
  - intros. 
    rewrite /state_stepN iterM_O // in H0.
    apply dret_pos in H0.
    by subst.
  - intros.
    rewrite /state_stepN iterM_Sn // in H0.
    apply dbind_pos in H0 as (σ1 & H1 & H2).
    epose proof (state_stepN_tape _ _ 1 _ _ _ H _).
    Unshelve.
    3 : {
      rewrite /state_stepN iterM_Sn.
      replace (iterM 0 _) with (fun s : state => dret s). 
      2 : { apply functional_extensionality. intros. by rewrite iterM_O. }
      rewrite dret_id_right.
      apply H2.
    }
    destruct H0 as [t' [H00 H0]].
    replace (heap σ') with (heap σ1).
    2 : {
      eapply IHn.
      - by rewrite H0 lookup_insert.
      - by rewrite /state_stepN.
    }
    apply state_step_support_equiv_rel in H2.
    by inversion H2.
Qed.

 Lemma SamplesOneTape_state_stepN_det l σ σ' n N t e:
  σ.(tapes) !! l = Some (N; t) ->
  SeriesC (exec n (e, σ)) = 1 ->
  SamplesOneTape l e -> 
  (state_stepN σ l n) σ' > 0 ->
  is_det (exec n (e, σ')).
Proof.
  intros.
  destruct (to_val e) eqn : Hve.
  { 
    erewrite exec_is_final; try by simpl.
    by econstructor. 
  }
  apply (state_stepN_heap _ _ _ _ _ _ H) in H2 as Hh.
  pose proof (state_stepN_tape _ _ _ _ _ _ H H2) as [t' [Ht Hst]]. 
  eapply presamples_execN_det; eauto.
  - rewrite Hst. apply lookup_insert. 
  - rewrite app_length Ht. lia.
  - eapply erasable_execN_det.
    + eapply erasure.iterM_state_step_erasable; eauto.
    + auto.
    + by rewrite /state_stepN in H2.
Qed.

(* 

Lemma SamplesOneTape_presamples_n (l : loc) e σ n N t :
  SeriesC (exec n (e, σ)) = 1 ->
  SamplesOneTape l e ->
  σ.(tapes) !! l = Some (N; t) ->
  ∃ μ, erasable μ σ ∧
    (∀ σ', μ σ' > 0 -> 
    σ'.(heap) = σ.(heap) ∧
    (∃ t', σ'.(tapes) = <[l:=(N; t')]>(σ.(tapes))) ∧
    is_det (exec n (e, σ'))).
Proof.
  revert e σ t.
  induction n.
  {
    intros.
    destruct (to_val e) eqn: Hve.
    { by eapply SamplesOneTape_presamples_n_val. }
    intros.
    rewrite exec_O_not_final in H; auto.
    rewrite dzero_mass in H.
    lra.
  }
  intros.
  destruct (to_val e) eqn: Hve.
  { by eapply SamplesOneTape_presamples_n_val. }

  (* Search (state_step).
  exists (state_step σ l).
  split.
  { eapply erasure.state_step_erasable. apply H1. }
  intros. *)


  (* induction n.
  - destruct (to_val e) eqn: Hve.
    + rewrite /exec in H.
      simpl in H.
      rewrite Hve in H. *)
       *)



Lemma SamplesOneTape_presamples_lim (l : loc) e σ N t :
  SeriesC (lim_exec (e, σ)) = 1 ->
  SamplesOneTape l e ->
  σ.(tapes) !! l = Some (N; t) ->
  ∃ μ, erasable μ σ ∧
    (∀ σ', μ σ' > 0 -> 
    σ'.(heap) = σ.(heap) ∧
    (∃ t', σ'.(tapes) = <[l:=(N; t')]>(σ.(tapes))) ∧
    is_det (lim_exec (e, σ')) ).    
Admitted.

Context `{!approxisGS Σ}.

Notation σ₀ := {| heap := ∅; tapes := ∅ |}.

Lemma det_ARcoupl_rwp (e1 e2 : expr) (σ1 σ2 : state) l1 l2 ψ ε :
  SeriesC (lim_exec (e1, σ1)) = 1 -> SeriesC (lim_exec (e2, σ2)) = 1 ->
  SamplesOneTape l1 e1 -> SamplesOneTape l2 e2 ->
  is_det (lim_exec (e1, σ1)) -> is_det (lim_exec (e2, σ2)) ->
  ARcoupl (lim_exec (e1, σ1)) (lim_exec (e2, σ2)) ψ ε ->
  ↯ ε -∗ ⤇ e2 -∗ WP e1 {{ v, ∃ v', ⤇ (Val v') ∗ ⌜ψ v v'⌝ }}.
Proof.
  iIntros "%%%%%%% He Hspec".
  rewrite wp_unfold /wp_pre.
  simpl.
  iIntros "%%%% ((Hsa & Hta) & Hspeca & Hea)".
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "hclose".
  

  

Admitted.