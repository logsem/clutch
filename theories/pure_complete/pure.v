From Coq Require Import Reals Psatz.
From clutch.common Require Import ectx_language.
From clutch.prob_lang Require Import notation tactics metatheory.
From clutch.prob_lang Require Export lang.
From clutch.prelude Require Import base Coquelicot_ext Reals_ext stdpp_ext classical.
From clutch.pure_complete Require Import term.

Local Open Scope R.

Ltac bool_solve :=
  repeat match goal with
  | H : ?b1 && ?b2 = true |- _ =>
      apply andb_true_iff in H; destruct H as [? ?]
  end;
  repeat match goal with
  | H : false = true |- _ => inversion H
  | H : ?X = true |- context ic [?X] => try rewrite H
  end;
try reflexivity.

Fixpoint is_pure (e : expr) := 
  match e with
  | Rec _ _ e' => is_pure e'
  | App e1 e2 => is_pure e1 && is_pure e2
  | UnOp _ e2 => is_pure e2
  | BinOp _ e1 e2 => is_pure e1 && is_pure e2
  | If e1 e2 e3 => is_pure e1 && is_pure e2 && is_pure e3
  | Pair e1 e2 => is_pure e1 && is_pure e2
  | Fst e' => is_pure e'
  | Snd e' => is_pure e'
  | InjL e' => is_pure e'
  | InjR e' => is_pure e'
  | Case e1 e2 e3 => is_pure e1 && is_pure e2 && is_pure e3
  | Rand e' (LitV (LitUnit))=> is_pure e'
  | AllocN _ _ | Load _ | Store _ _ | AllocTape _ | Rand _ _ => false
  | Val v => is_pureV v
  | Var _ => true
  | Tick e => is_pure e
end
with is_pureV (v : val) :=
  match v with
  | RecV _ _ e' => is_pure e'
  | PairV v1 v2 => is_pureV v1 && is_pureV v2
  | InjLV v' | InjRV v' => is_pureV v'
  | LitV _ => true
end.

Inductive isPure : expr → Prop :=
  | isPure_Rec : ∀ x y e,
      isPure e →
      isPure (Rec x y e)
  | isPure_App : ∀ e1 e2,
      isPure e1 →
      isPure e2 →
      isPure (App e1 e2)
  | isPure_UnOp : ∀ op e,
      isPure e →
      isPure (UnOp op e)
  | isPure_BinOp : ∀ op e1 e2,
      isPure e1 →
      isPure e2 →
      isPure (BinOp op e1 e2)
  | isPure_If : ∀ e1 e2 e3,
      isPure e1 →
      isPure e2 →
      isPure e3 →
      isPure (If e1 e2 e3)
  | isPure_Pair : ∀ e1 e2,
      isPure e1 →
      isPure e2 →
      isPure (Pair e1 e2)
  | isPure_Fst : ∀ e,
      isPure e →
      isPure (Fst e)
  | isPure_Snd : ∀ e,
      isPure e →
      isPure (Snd e)
  | isPure_InjL : ∀ e,
      isPure e →
      isPure (InjL e)
  | isPure_InjR : ∀ e,
      isPure e →
      isPure (InjR e)
  | isPure_Case : ∀ e1 e2 e3,
      isPure e1 →
      isPure e2 →
      isPure e3 →
      isPure (Case e1 e2 e3)
  | isPure_Rand_Unit : ∀ op,
      isPure op ->
      isPure (Rand op (LitV LitUnit))
  | isPure_Val : ∀ v,
      isPureV v →
      isPure (Val v)
  | isPure_Var : ∀ x,
      isPure (Var x)
  | isPure_Tick : ∀ e,
      isPure e →
      isPure (Tick e)
with isPureV : val → Prop :=
  | isPureV_RecV : ∀ x y e,
      isPure e →
      isPureV (RecV x y e)
  | isPureV_PairV : ∀ v1 v2,
      isPureV v1 →
      isPureV v2 →
      isPureV (PairV v1 v2)
  | isPureV_InjLV : ∀ v,
      isPureV v →
      isPureV (InjLV v)
  | isPureV_InjRV : ∀ v,
      isPureV v →
      isPureV (InjRV v)
  | isPureV_LitV : ∀ l,
      isPureV (LitV l).

Fixpoint isPure_is_pure (e : expr) : isPure e -> is_pure e = true
  with isPureV_is_pureV (v : val) : isPureV v -> is_pureV v = true.
Proof.
  - intros. clear isPure_is_pure. induction e; 
    inversion H; simpl; auto; 
    try (rewrite IHe1); auto;
    try (rewrite IHe2); auto;
    try (rewrite IHe3); auto. 
  - intros. clear isPureV_is_pureV. 
    induction v; inversion H; simpl; auto.
    rewrite IHv1; auto.
Qed.

Fixpoint is_pure_isPure (e : expr) : is_pure e = true -> isPure e
  with is_pureV_isPureV (v : val) : is_pureV v = true -> isPureV v.
Proof.
  - intros. clear is_pure_isPure.
    induction e; try repeat (apply andb_prop in H as [H ?]);
    inversion H; try econstructor; eauto.
    destruct e2; inversion H1. destruct v; inversion H1.
    destruct l; inversion H1. econstructor. by apply IHe1.
  - intros. clear is_pureV_isPureV. 
    induction v; simpl in H; try repeat (apply andb_prop in H as [H ?]);
    econstructor; eauto.
Qed.

Lemma is_pure_iff (e : expr) : (isPure e) ↔ (is_pure e = true).
Proof.
  split.
  - apply isPure_is_pure.
  - apply is_pure_isPure.
Qed.

Lemma is_pure_subst v e x : 
  is_pure e = true -> is_pureV v = true -> is_pure (subst x v e) = true.
Proof.
  intros.
  induction e; simpl; auto; 
  try (case_decide; auto); simpl in H;
  try repeat (apply andb_prop in H as [H ?]);
  subst; try (rewrite IHe1; auto); try(rewrite IHe2; auto).
  {  
    destruct e2; try by inversion H; simpl. 
    destruct v0; inversion H. 
    destruct l; inversion H. simpl. auto. 
    }
  destruct e2; inversion H. rewrite H2. simpl. auto.
  destruct v0; inversion H. destruct l; inversion H. auto.
Qed.

Lemma pure_head_step_inv (e e' : expr) (σ : state):
  is_pure e = true -> 
  head_step e σ (e', σ) > 0 -> 
  is_pure e' = true.
Proof.
  intros. 
  destruct e; inv_head_step; auto; 
  try repeat (apply andb_prop in H as [H ?]); subst; auto.
  - destruct x, f; simpl; auto; apply is_pure_subst; auto.
    apply is_pure_subst; auto.
  - destruct v; destruct op; inversion H2;
    destruct l; inversion H2; auto.
  - revert H3. rewrite /bin_op_eval. 
    case_decide.
    + case_decide; intros H';by inversion H'.
    + destruct v; intros H'; inversion H'.
      destruct l; inversion H'; destruct v0; inversion H';
      destruct l; inversion H'; auto; destruct op; inversion H';
      auto; destruct l0; inversion H'; auto.
  - by rewrite H H1.
  - by rewrite H H0.
Qed.


Definition is_pure_ectx (Ki : ectx_item) : bool :=
  match Ki with
  | AppLCtx v => is_pureV v
  | AppRCtx e => is_pure e
  | UnOpCtx _ => true
  | BinOpLCtx _ v => is_pureV v
  | BinOpRCtx _ e => is_pure e
  | IfCtx e1 e2 => is_pure e1 && is_pure e2
  | PairLCtx v => is_pureV v
  | PairRCtx e => is_pure e
  | FstCtx => true
  | SndCtx => true
  | InjLCtx => true
  | InjRCtx => true
  | CaseCtx e1 e2 => is_pure e1 && is_pure e2
  | RandRCtx e => false
  | RandLCtx (LitV (LitUnit)) => true
  | AllocNLCtx _ | AllocNRCtx _ | LoadCtx | StoreLCtx _ | StoreRCtx _ 
  | AllocTapeCtx | RandLCtx _ => false
  | TickCtx => true
  end.

Lemma is_pure_fill_item e Ki : 
  is_pure e = true ->  
  is_pure_ectx Ki = true ->
  is_pure (fill_item Ki e) = true.
Proof.
  intros.
  destruct Ki; inversion H0; 
  destruct e; inversion H; simpl; 
  try (rewrite H2); auto; try (rewrite H3); auto.
Qed.

Lemma is_pure_fill e Ki:
  is_pure e = true ->
  Forall (fun k => is_pure_ectx k = true) Ki ->
  is_pure (fill Ki e) = true.
Proof.
  intros. revert e H.
  induction Ki; auto.
  simpl. intros. 
  inversion H0. subst.
  apply IHKi; auto. by apply is_pure_fill_item.
Qed.

Lemma is_pure_head ei (e e2: expr): 
  is_pure e = true -> decomp_item e = Some (ei, e2) ->
    is_pure e2 = true.
Proof.
  rewrite -!is_pure_iff.
  intros.
  inversion H; subst; simpl in H0; try by inversion H0;
  try by (inversion H1; subst; inversion H0; auto).
  - inversion H2; subst; inversion H0; auto. inversion H1; subst; inversion H0; auto.
  - inversion H2; subst; inversion H0; auto. inversion H1; subst; inversion H0; auto.
  - destruct e0; inversion H0; subst; auto.
    destruct e1; inversion H0; subst; auto.
Qed.


Lemma is_pure_heads (e : expr): 
  is_pure e = true -> is_pure (decomp e).2 = true.
Proof.
  destruct (decomp e) eqn : Hde.
  simpl.
  remember (length l).
  revert e e0 l Hde Heqn.
  induction n.
  {
    intros.
    destruct l; inversion Heqn.
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
  assert (n = length l0).
  { 
    rewrite app_length in Heqn. 
    rewrite Nat.add_1_r in Heqn. auto.
  }
  apply (IHn _ _ _ Hde2 H0).
  by eapply is_pure_head.
Qed.

Lemma is_pure_heads_ectx (e : expr):
  is_pure e = true -> Forall (fun k => is_pure_ectx k = true) (decomp e).1.
Proof.
  destruct (decomp e) eqn : Hde.
  simpl.
  remember (length l).
  revert e e0 l Hde Heqn.
  induction n.
  {
    intros.
    destruct l; inversion Heqn.
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
  2: {
    apply Forall_singleton.
    destruct e; inversion H; inversion Hde';
    try by (destruct e; inversion H2; subst; auto).
    { 
      destruct e4; try inversion H2; subst; simpl in *; bool_solve.
      destruct e3; inversion H2; subst; auto.
    }
    {
      destruct e4; try inversion H2; subst; simpl in *; bool_solve;
      destruct e3; inversion H2; subst; auto.
    }
    {
      destruct e3; try inversion H2; subst; simpl in *; auto; bool_solve.
    }
    {
      destruct e4; try inversion H2; subst; simpl in *; bool_solve.
      destruct e3; inversion H2; subst; auto.
    }
    {
      destruct e3; try inversion H2; subst; simpl in *; auto; bool_solve.
    }
    {
      destruct e4; try by inversion H1. destruct v; try by inversion H1.
      destruct l; try by inversion H1. destruct e3; try by inversion H2.
    }
  }
  eapply IHn.
  - apply Hde2.
  - rewrite app_length Nat.add_1_r in Heqn. by inversion Heqn.
  - by eapply is_pure_head.
Qed.
    
Lemma is_pure_reduce e e0 e1 l: 
    is_pure e = true -> is_pure e1 = true -> 
    decomp e = (l, e0) -> 
    is_pure (fill l e1) = true.
Proof.
  intros.
  apply is_pure_heads_ectx in H as H2.
  apply is_pure_heads in H as H3.
  rewrite H1 in H2, H3. simpl in *.
  by apply is_pure_fill.
Qed.


Lemma pure_state_head_step (e e' : expr) (σ σ': state) : 
  is_pure e = true -> head_step e σ' (e', σ) > 0 -> σ = σ'.
Proof.
  intros.
  destruct e; inv_head_step; auto.
Qed.

Lemma pure_step_inv (e e' : expr) (σ : state):
  is_pure e = true ->
  step (e, σ) (e', σ) > 0 ->
  is_pure e' = true.
Proof.
  rewrite /step. simpl. rewrite /prim_step. simpl.
  destruct (decomp e) eqn: Hde. rewrite Hde. simpl.
  rewrite dmap_pos. 
  intros. destruct H0 as [a [H0 H1]]. destruct a.
  simpl in H0. inversion H0. subst.
  apply pure_head_step_inv in H1.
  2: { 
    replace e0 with (decomp e).2.
    { by apply is_pure_heads. } 
    by rewrite Hde.
  }
  by apply (is_pure_reduce e e0).
Qed.

Lemma pure_state_step (e e' : expr) (σ σ': state) : 
  is_pure e = true -> step (e, σ) (e', σ') > 0 -> σ = σ'.
Proof.
  rewrite /step. simpl. rewrite /prim_step. simpl.
  destruct (decomp e) eqn: Hde. rewrite Hde. simpl.
  rewrite dmap_pos. 
  intros. destruct H0 as [a [H0 H1]]. destruct a.
  simpl in H0. inversion H0. 
  apply is_pure_heads in H. rewrite Hde in H. 
  apply pure_state_head_step in H1; subst; auto.
Qed.

Lemma dret_cfg_eq (e e': expr) (σ1 σ2: state) :
  dret (e, σ1) (e', σ1) = dret (e, σ2) (e', σ2).
Proof.
  destruct (decide (e = e')); try subst e'. 
  - rewrite !dret_1_1; auto.
  - rewrite !dret_0; auto;
    move => a; apply n; by inversion a.
Qed.

Lemma pure_step_state (e e': expr) (σ1 σ2: state) :
  is_pure e = true -> step (e, σ1) (e', σ1) = step (e, σ2) (e', σ2).
Proof.
  intros.
  rewrite /step. simpl. rewrite /prim_step. simpl.
  destruct (decomp e) eqn: Hde. rewrite Hde. simpl.
  apply is_pure_heads in H. rewrite Hde in H. simpl in H.
  destruct e0; inv_head_step; 
  try (rewrite dmap_dzero; by rewrite !dzero_0);
  try (rewrite !dmap_dret /fill_lift; apply (dret_cfg_eq _ e' σ1 σ2)). 
  erewrite !dmap_comp.
  rewrite /fill_lift. simpl.
  replace ((λ '(e0, σ), (fill l e0, σ)) ∘ λ n0 : fin (S (Z.to_nat n)), (_, σ1)) with (λ n0 : fin (S (Z.to_nat n)), (fill l #n0, σ1)).
  2: by apply functional_extensionality.
  replace ((λ '(e0, σ), (fill l e0, σ)) ∘ λ n0 : fin (S (Z.to_nat n)), (_, σ2)) with (λ n0 : fin (S (Z.to_nat n)), (fill l #n0, σ2)).
  2: by apply functional_extensionality.
  rewrite !dmap_unfold_pmf.
  apply SeriesC_ext.
  intros. case_bool_decide; case_bool_decide; auto.
  - inversion H. subst e'. contradiction.
  - inversion H0. subst e'. contradiction.
Qed.

Lemma pure_reducible e σ σ' : 
  is_pure e = true -> 
  reducible (e, σ) ->
  reducible (e, σ').
Proof.
  intros.
  destruct H0 as [[e' σ1] Hs].
  exists (e', σ').
  apply pure_state_step in Hs as He; auto.
  subst. 
  erewrite pure_step_state; auto.
  apply Hs.
Qed.

Lemma pure_exec_state n e σ σ':
  is_pure e = true -> 
  exec n (e, σ) = exec n (e, σ').
Proof.
  revert e.
  induction n; auto.
  intros. simpl.
  destruct (to_val e); auto.
  apply distr_ext => v //=.
  rewrite !dbind_unfold_pmf.
  rewrite fubini_pos_seriesC_prod_lr; try real_solver.
  2 : { apply pmf_ex_seriesC_mult_fn. by exists 1. }
  rewrite fubini_pos_seriesC_prod_lr. 
  2 : real_solver.
  2 : { apply pmf_ex_seriesC_mult_fn. by exists 1. }
  apply SeriesC_ext => e' //=.
  erewrite <- (SeriesC_ext (λ b, if bool_decide (b = σ) then (if bool_decide (0 < step (e, σ) (e', σ)) then step (e, σ) (e', σ) * exec n (e', σ) v else 0) else 0)). 2 : {
    intros. case_bool_decide; subst.
    - case_bool_decide; try real_solver. 
      symmetry. apply Rmult_eq_0_compat_r. simpl in *.
      apply Rle_antisym; real_solver.
    - symmetry. apply Rmult_eq_0_compat_r.
      apply Rle_antisym; try real_solver.
      destruct (decide (0 < step (e, σ) (e', n0))); try by simpl in *; real_solver.
      by apply pure_state_step in r. 
  }
  rewrite SeriesC_singleton. 
  erewrite <- (SeriesC_ext (λ b, if bool_decide (b = σ') then (if bool_decide (0 < step (e, σ') (e', σ')) then step (e, σ') (e', σ') * exec n (e', σ') v else 0) else 0)). 2 : {
    intros. case_bool_decide; subst.
    - case_bool_decide; try real_solver. 
      symmetry. apply Rmult_eq_0_compat_r. simpl in *.
      apply Rle_antisym; real_solver.
    - symmetry. apply Rmult_eq_0_compat_r.
      apply Rle_antisym; try real_solver.
      destruct (decide (0 < step (e, σ') (e', n0))); try by simpl in *; real_solver.
      by apply pure_state_step in r. 
  } 
  rewrite !SeriesC_singleton (pure_step_state e e' σ σ'); auto.
  do 2 case_bool_decide; try real_solver.
  rewrite IHn; auto.
  by eapply pure_step_inv.
Qed.

Lemma pure_pterm n (e : expr) (σ σ' : state) :
  is_pure e = true -> pterm n (e, σ) = pterm n (e, σ').
Proof.
  intros.
  revert e H.
  induction n.
  {
    intros.
    rewrite /pterm /exec /to_final. simpl.
    destruct (to_val e) eqn: He; auto.
  }
  intros.
  destruct (to_val e) eqn: He. 
  { rewrite /pterm /exec /to_final. simpl. by rewrite He. }
  rewrite !pterm_rec; try assumption.
  rewrite /Expval.
  rewrite fubini_pos_seriesC_prod_rl.
  2: { intros. apply (Rmult_le_pos _ _ (pmf_pos _ _) (pmf_SeriesC_ge_0 _)). }
  2: { 
    apply pmf_ex_seriesC_mult_fn. 
    exists 1. 
    intros. split.
    - apply pmf_SeriesC_ge_0.
    - apply pmf_SeriesC.
  }
  rewrite fubini_pos_seriesC_prod_rl.
  2: { intros. apply (Rmult_le_pos _ _ (pmf_pos _ _) (pmf_SeriesC_ge_0 _)). }
  2: { 
    apply pmf_ex_seriesC_mult_fn. 
    exists 1. 
    intros. split.
    - apply pmf_SeriesC_ge_0.
    - apply pmf_SeriesC.
  }
  rewrite (SeriesC_ext 
    (λ b : language.state prob_lang, _) 
    (λ b, if bool_decide (b = σ) then SeriesC (λ a : language.expr prob_lang, step (e, σ) (a, b) * pterm n (a, b)) else 0)).
  2: {
    intros.
    case_bool_decide; auto.
    apply SeriesC_0.
    intros. apply Rmult_eq_0_compat_r.
    destruct (Rle_decision (step (e, σ) (x, n0)) 0).
    { by apply Rle_antisym. }
    exfalso. apply H0. 
    symmetry.
    apply (pure_state_step e x); auto. 
    by apply Rnot_le_gt.
  }
  rewrite (SeriesC_ext 
    (λ b : language.state prob_lang, SeriesC _) 
    (λ b, if bool_decide (b = σ') then SeriesC (λ a : language.expr prob_lang, step (e, σ') (a, b) * pterm n (a, b)) else 0)).
  2: {
    intros.
    case_bool_decide; auto.
    apply SeriesC_0.
    intros. apply Rmult_eq_0_compat_r.
    destruct (Rle_decision (step (e, σ') (x, n0)) 0).
    { by apply Rle_antisym. }
    exfalso. apply H0. 
    symmetry.
    apply (pure_state_step e x); auto. 
    by apply Rnot_le_gt.
  }
  rewrite !(SeriesC_singleton_dependent).
  apply SeriesC_ext.
  intros.
  rewrite (pure_step_state _ n0 σ' σ H).
  destruct (Rle_decision (step (e, σ) (n0, σ)) 0).
  - epose proof (Rle_antisym _ _ r _). 
    rewrite H0. real_solver.
    Unshelve. auto.
  - rewrite IHn.
    { rewrite (pure_step_state _ n0 σ σ' H). auto. }
    eapply pure_step_inv.
    { apply H. }
    { apply Rnot_le_gt. apply n1. }
Qed.