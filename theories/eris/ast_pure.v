From clutch.eris Require Export eris error_rules. 

Local Open Scope R.

Section Term.

  Context `{Λ : language}.

  Implicit Types ρ : language.cfg Λ.

  Definition pterm (n : nat) ρ := SeriesC (exec n ρ).

  Definition pterm_nnr (n : nat) ρ := mknonnegreal (pterm n ρ) (pmf_SeriesC_ge_0 _).

  Lemma pterm_le1 (n : nat) ρ : (0 <= 1 - pterm n ρ)%R. 
  Proof.
  specialize (pmf_SeriesC (exec n ρ)) as he.
  rewrite /pterm. apply -> Rcomplements.Rminus_le_0. auto.
  Qed.

  Definition pterm_comp (n : nat) ρ := mknonnegreal (1 - pterm n ρ) (pterm_le1 _ _).

  Lemma pterm_rec (n : nat) ρ : 
    language.to_val ρ.1 = None ->
    pterm (S n) ρ = Expval (step ρ) (pterm n).
  Proof.
    intros.
    rewrite /pterm exec_Sn dbind_mass /Expval.
    apply SeriesC_ext. intros.
    rewrite /step_or_final.
    rewrite /to_final. simpl. rewrite H. 
    auto.
  Qed.

  Lemma AST_pt_lim m ε : 
    SeriesC (lim_exec m) = 1 ->
    ε < 1 -> ∃ n, ε < pterm n m.
  Proof.
    intros Hst?.
    rewrite lim_exec_Sup_seq in Hst. intros.
    assert (Lim_seq.is_sup_seq (λ n : nat, Rbar.Finite (SeriesC (exec n m))) (Rbar.Finite 1)). {
      rewrite <- Hst. rewrite rbar_finite_real_eq. 2: {
        apply is_finite_Sup_seq_SeriesC_exec.
      }
      apply Lim_seq.Sup_seq_correct.
    }
    unfold Lim_seq.is_sup_seq in H0.
    assert (0 < 1 - ε). { lra. }
    specialize H0 with (mkposreal (1 - ε) H1).
    simpl in H0. destruct H0 as [H0 [n H2]].
    exists n. rewrite /pterm. field_simplify in H2. apply H2.
  Qed.

  Lemma pterm_reducible (n : nat) ρ : 
    language.to_val ρ.1 = None ->
    0 < pterm n ρ ->
    reducible ρ.
  Proof.
    rewrite /pterm.
    intros. apply SeriesC_gtz_ex in H0.
    2: apply pmf_pos.
    induction n.
    - destruct H0. rewrite /exec /to_final in H0. simpl in H0.
      rewrite H in H0.
      rewrite dzero_0 in H0. lra.
    - apply mass_pos_reducible.
      destruct H0.
      simpl in H0.
      rewrite H in H0.
      apply dbind_pos in H0.
      destruct H0 as [ρ' [H0 H1]].
      simpl.
      apply (SeriesC_pos _ ρ').
      + apply pmf_pos.
      + apply pmf_ex_seriesC.
      + apply H1.
  Qed.

End Term.

Section Pure.

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
    Print fill_item.
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
    Search (Forall).
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

  Lemma pure_step (e e': expr) (σ1 σ2: state) :
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
    rewrite (pure_step _ n0 σ' σ H).
    destruct (Rle_decision (step (e, σ) (n0, σ)) 0).
    - epose proof (Rle_antisym _ _ r _). 
      rewrite H0. real_solver.
      Unshelve. auto.
    - rewrite IHn.
      { rewrite (pure_step _ n0 σ σ' H). auto. }
      eapply pure_step_inv.
      { apply H. }
      { apply Rnot_le_gt. apply n1. }
  Qed.

End Pure.

Section Complete.

  Context `{!erisGS Σ}.

  Notation σ₀ := {| heap := ∅; tapes := ∅ |}.
  Notation almost_surely_terminates ρ := (SeriesC (lim_exec ρ) = 1%R).

  Lemma AST_complete_pure_pre (n: nat) (e : expr) (σ : state) E : 
    is_pure e = true -> 
    ↯ (pterm_comp n (e, σ)) -∗ WP e @ E [{ v, True }].
  Proof. 
    intros.
    iInduction n as [|n] "IH" forall (e H σ).
    - destruct ( language.to_val e) eqn: He.
      { iIntros. apply of_to_val in He as <-. by wp_pures. }
      iIntros "Herr". 
      rewrite /pterm_comp /pterm. simpl. rewrite He dzero_mass. 
      rewrite Rminus_0_r. iPoseProof (ec_contradict with "Herr") as "H"; 
      auto; try lra.
    - destruct (language.to_val e) eqn: He.
      { iIntros. apply of_to_val in He as <-. by wp_pures. }
      iIntros "Herr".
      iApply twp_lift_step_fupd_glm; auto.
      iIntros "%% [Hs Herra]". 
      iDestruct (ec_supply_ec_inv with "Herra Herr") as %(ε1' & ε3 & Hε_now & Hε1').
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros "hclose".
      iApply glm_adv_comp. 
      iExists (fun s => step (e, σ1) s > 0), 0%NNR, (fun x => (ε3 + (pterm_comp n x))%NNR).
      destruct (Rlt_dec 0 (pterm (S n) (e, σ))).
      2 : {
        iExFalso.
        iApply (ec_contradict with "Herr").
        rewrite /pterm_comp. simpl. lra. 
      }
      iSplitR.
      { iPureIntro. apply (pterm_reducible (S n)); auto. rewrite (pure_pterm _ _ σ1 σ); auto. }
      iSplitR.
      { 
        iPureIntro. exists (ε3+1).
        intros. simpl.
        apply Rplus_le_compat_l, Rminus_le_0_compat, pmf_SeriesC_ge_0.
      
      }
      iSplitR.
      { 
        iPureIntro.
        simpl. rewrite Rplus_0_l. 
        rewrite (SeriesC_ext _ (λ r, (λ a, (prim_step e σ1 a) * (ε3 + 1)) r + (-1) * (λ a,  (prim_step e σ1 a) * (pterm n a)) r)).
        2: {
          intros.
          field_simplify. real_solver.
        }
        rewrite (SeriesC_plus).
        2 : {
          apply ex_seriesC_scal_r. apply pmf_ex_seriesC.
        }
        2 : {
          apply ex_seriesC_scal_l.
          apply pmf_ex_seriesC_mult_fn. 
          exists 1. intros. split.
          - apply pmf_SeriesC_ge_0.
          - apply pmf_SeriesC.
        }
        rewrite Hε_now. replace (nonneg (ε1' + ε3)%NNR) with (nonneg ε1' + ε3); auto.
        rewrite Hε1'.
        rewrite /pterm_comp. simpl. 
        rewrite SeriesC_scal_l SeriesC_scal_r.
        rewrite /step. simpl. field_simplify.
        rewrite <- Rplus_minus_swap. 
        rewrite !Rminus_def.
        apply Rplus_le_compat.
        {
          apply Rplus_le_compat.
          - simpl. rewrite <- Rmult_1_l.
            apply Rmult_le_compat_r; auto.
          - apply pmf_SeriesC.
        }
        apply Ropp_le_contravar, Req_le.
        rewrite (pure_pterm _ _ _ σ1); auto.
        by rewrite pterm_rec /Expval.
      }
      iSplitR.
      { 
        Search (pgl).
        iPureIntro.
        simpl.
        apply (pgl_mon_pred _ (fun x => (fun _ => True) x ∧ (prim_step e σ1) x > 0)).
        - by intros a [_ Hp]. 
        - apply pgl_pos_R, pgl_trivial. lra.
      }
      iIntros. 
      iMod (ec_supply_decrease with "Herra Herr") as (????) "Herra".
      iModIntro.
      destruct (Rlt_decision (nonneg ε3 + nonneg (pterm_comp n (e2, σ2)))%R 1%R) as [Hdec|Hdec]; last first.
      { 
        apply Rnot_lt_ge, Rge_le in Hdec.
        iApply exec_stutter_spend.
        iPureIntro.
        simpl.
        simpl in Hdec. lra.
      }
      iApply exec_stutter_free.
      replace (nonneg ε3 + nonneg (pterm_comp n (e2, σ2)))%R with (nonneg (ε3 + (pterm_comp n (e2, σ2)))%NNR); [|by simpl].
      iMod (ec_supply_increase ε3 (pterm_comp n (e2, σ2)) with "[Herra]") as "[Herra Herr]"; try lra.
      { iApply ec_supply_eq; [|done]. simplify_eq. lra. }
      simpl in H0. 
      apply (pure_state_step) in H0 as H'0; auto.
      subst σ2.
      iFrame.
      iMod "hclose".
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros.
      iApply "IH"; iFrame.
      { 
        iPureIntro. eapply pure_step_inv. 
        - apply H.
        - apply H0.
      }
  Qed.

  Theorem AST_complete_pure (e : expr) ε: 
    is_pure e = true ->
    almost_surely_terminates (e, σ₀) ->
    0 < ε -> 
    ↯ ε -∗ WP e [{ v, True }].
  Proof.
    iIntros "%%% Herr".
    assert (0 <= ε). { lra. }
    apply (AST_pt_lim _ (1-ε)) in H0 as [n H']; auto; try lra.
    iPoseProof ((ec_weaken ε (1 - pterm n (e, σ₀))) with "[Herr]") as "Herr"; try iFrame.
    - pose proof (pmf_SeriesC (exec n (e, σ₀))).
      split; try lra. apply pterm_le1.
    - by iApply AST_complete_pure_pre.
  Qed.

End Complete.