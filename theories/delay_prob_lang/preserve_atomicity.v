From Stdlib Require Import Reals Psatz.
From clutch.delay_prob_lang Require Import tactics notation urn_subst metatheory.
From clutch.delay_prob_lang Require Export lang.
From clutch.prob Require Import distribution.
Set Default Proof Using "Type*".

Lemma list_destruct_rev {A: Type} (l:list A) :
  l= [] \/ ∃ x xs, l = xs ++ [x].
Proof.
  induction l using rev_ind; destruct!/=; first naive_solver.
  - right. eexists _, []. naive_solver.
  - right. naive_solver.
Qed.

Local Ltac smash :=
  repeat (done||subst||simpl in *||rewrite app_nil_r||rewrite app_assoc||split||eexists _).

Lemma fill_is_val K (e:expr) v:
  fill K e = (Val v) -> K=[].
Proof.
  intros H.
  eapply fill_to_val; by erewrite H.
Qed. 

Local Ltac fill_inv :=
  repeat
    match goal with
    | H : fill _ _ = (Val _)  |- _ => apply fill_is_val in H as ?; subst; simpl in *; subst
    | H : (Val _) = fill _ _  |- _ => symmetry in H; apply fill_is_val in H as ?; subst; simpl in *; subst
    | H : is_Some (to_val (fill _ _))  |- _ =>  destruct H as [? H]; apply of_to_val in H;symmetry in H
    end.

Lemma fill_equal_break K K' e1' v' σ:
  head_step_pred e1' σ ->
  fill K' e1' = fill K (Val v') ->
  (∃ K1, K= K1++K') \/ (∃ Kall K1 K1' K2, K' = K1++[K1']++ Kall /\ K = K2:: Kall /\ fill (K1++[K1']) e1' = fill_item K2 (Val v') /\ K1' ≠ K2).
Proof.
  revert K' e1' v'.
  induction K as [|K1 K2 IHK]using rev_ind.
  - intros K' e1' v' H1 H2.
    simpl in *.
    epose proof fill_to_val K' _ as ->; last by erewrite H2.
    left. exists []. naive_solver.
  - intros K' e1' v' H1 H2.
    rewrite fill_app in H2.
    simpl in *.
    destruct (list_destruct_rev K') as [|[K1' [K2']]].
    { subst. simpl in *. subst.
      setoid_rewrite app_nil_r.
      naive_solver. }
    subst. rewrite fill_app in H2.
    simpl in *.
    destruct (decide (K1=K1')).
    { subst. simplify_eq.
      apply IHK in H2; last done.
      destruct!/=.
      - setoid_rewrite app_assoc; naive_solver.
      - right. eexists _, _, _, _.
        split; last done.
        rewrite -app_assoc. f_equal.
    }
    destruct K1, K1'; simplify_eq; fill_inv; simplify_eq; try (by inversion H1); right.
    all: repeat eexists _; split; last split; [|done|]; try (by rewrite app_nil_r); try (by rewrite fill_app); try (by f_equal); by rewrite fill_app.
Qed.

Lemma head_step_pred_fill K v σ:
  head_step_pred (fill K (Val v)) σ -> ∃ Ki, K = [Ki].
Proof.
  destruct (list_destruct_rev K) as [|[K1[K']]].
  { subst.
    simpl.
    intros H1.
    inversion H1.
  }
  destruct (list_destruct_rev K') as [|[K2[]]]; first naive_solver.
  subst.
  rewrite !fill_app.
  simpl.
  intros H1; inversion H1; destruct K1; simplify_eq; destruct K2; simplify_eq.
Qed.


Lemma head_step_pred_laplace bl0 bl1 bl2:
  base_lit_type_check bl0 = Some BLTInt ->
  base_lit_type_check bl1 = Some BLTInt ->
  base_lit_type_check bl2 = Some BLTInt->
  ∃ σ' : state, head_step_pred (Laplace #bl0 #bl1 #bl2) σ'.
Proof.
  intros H1 H2 H3.
  set (s:=base_lit_support_set bl0 ∪ base_lit_support_set bl1 ∪ base_lit_support_set bl2 ).
  set (f' := gset_to_gmap 0%Z s).
  exists ({| heap := inhabitant; urns :=urns_subst_f_to_urns f'|}).
  eapply (urn_subst_exists _ _ f') in H1 as K1; last first.
  { rewrite /f'. rewrite dom_gset_to_gmap. rewrite /s. set_solver. }
  eapply (urn_subst_exists _ _ f') in H2 as K2; last first.
  { rewrite /f'. rewrite dom_gset_to_gmap. rewrite /s. set_solver. }
  eapply (urn_subst_exists _ _ f') in H3 as K3; last first.
  { rewrite /f'. rewrite dom_gset_to_gmap. rewrite /s. set_solver. }
  destruct K1 as (num&K1&?).
  destruct K2 as (den&K2&?).
  destruct K3 as (loc&K3&?).
  apply urn_subst_is_simple in K1 as K1'.
  apply urn_subst_is_simple in K2 as K2'.
  apply urn_subst_is_simple in K3 as K3'.
  destruct num; simplify_eq.
  destruct den; simplify_eq.
  destruct loc; simplify_eq.
  destruct (decide (0<IZR n/IZR n0)%R).
  - eapply LaplaceHSP; last done; intros ??%urns_subst_f_to_urns_unique_valid; by subst.
  - eapply LaplaceHSP'; last done; intros ??%urns_subst_f_to_urns_unique_valid; by subst.
Qed.

Lemma head_step_pred_dlaplace bl0 bl1 bl2:
  base_lit_type_check bl0 = Some BLTInt ->
  base_lit_type_check bl1 = Some BLTInt ->
  base_lit_type_check bl2 = Some BLTInt->
  ∃ σ' : state, head_step_pred (DLaplace #bl0 #bl1 #bl2) σ'.
Proof.
  intros H1 H2 H3.
  set (s:=base_lit_support_set bl0 ∪ base_lit_support_set bl1 ∪ base_lit_support_set bl2 ).
  set (f' := gset_to_gmap 0%Z s).
  exists ({| heap := inhabitant; urns :=urns_subst_f_to_urns f'|}).
  eapply (urn_subst_exists _ _ f') in H1 as K1; last first.
  { rewrite /f'. rewrite dom_gset_to_gmap. rewrite /s. set_solver. }
  eapply (urn_subst_exists _ _ f') in H2 as K2; last first.
  { rewrite /f'. rewrite dom_gset_to_gmap. rewrite /s. set_solver. }
  eapply (urn_subst_exists _ _ f') in H3 as K3; last first.
  { rewrite /f'. rewrite dom_gset_to_gmap. rewrite /s. set_solver. }
  destruct K1 as (num&K1&?).
  destruct K2 as (den&K2&?).
  destruct K3 as (loc&K3&?).
  apply urn_subst_is_simple in K1 as K1'.
  apply urn_subst_is_simple in K2 as K2'.
  apply urn_subst_is_simple in K3 as K3'.
  destruct num; simplify_eq.
  destruct den; simplify_eq.
  destruct loc; simplify_eq.
  destruct (decide (0<IZR n/IZR n0)%R).
  - eapply DLaplaceHSP; last done; intros ??%urns_subst_f_to_urns_unique_valid; by subst.
  - eapply DLaplaceHSP'; last done; intros ??%urns_subst_f_to_urns_unique_valid; by subst.
Qed. 

Local Ltac urn_smash H':=
  intros ??%urns_subst_f_to_urns_unique_valid;
  subst;
  rename select (urn_subst_equal _ _ _) into H';
  eapply urn_subst_equal_unique in H'; last apply urn_subst_equal_obv; last by eapply urn_subst_is_simple.

(** Simplify this proof? *)
Lemma value_promote_preserves_atomicity_empty_context1 Ki v' v σ f:
  head_step_pred (fill_item Ki (Val v')) σ ->
  urn_subst_val f v = Some (v') ->
  ∃ σ',
  head_step_pred (fill_item Ki (Val v)) σ'.
Proof.
  intros H1 H2.
  inversion H1; destruct Ki; simplify_eq; simpl in *; simplify_eq.
  - exists inhabitant. apply PairHSP.
  - exists inhabitant. apply PairHSP.
  - exists inhabitant. apply InjLHSP.
  - exists inhabitant. apply InjRHSP.
  - exists inhabitant. destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=.
    apply BetaSP.
  - exists inhabitant. apply BetaSP.
  - exists inhabitant. admit.
  - exists inhabitant. admit.
  - exists inhabitant. admit.
  - exists ({| heap := σ.(heap); urns :=urns_subst_f_to_urns f|}). destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=. eapply IfTrueHSP.
    urn_smash H'. naive_solver.
  - exists ({| heap := σ.(heap); urns :=urns_subst_f_to_urns f|}). destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=. eapply IfFalseHSP.
    urn_smash H'. naive_solver.
  - exists inhabitant. destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=. eapply FstHSP.
  - exists inhabitant. destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=. eapply SndHSP.
  - exists inhabitant. destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=. eapply CaseLHSP.
  - exists inhabitant. destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=. eapply CaseRHSP.
  - exists ({| heap := σ.(heap); urns :=urns_subst_f_to_urns f|}).
    destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=. eapply AllocNHSP; try done.
    urn_smash H'. naive_solver.
  - exists σ. by eapply AllocNHSP.
  - exists ({| heap := σ.(heap); urns :=urns_subst_f_to_urns f|}).
    destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=. eapply LoadHSP; try done.
    urn_smash H'. naive_solver.
  - exists ({| heap := σ.(heap); urns :=urns_subst_f_to_urns f|}).
    destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=. eapply StoreHSP; try done.
    urn_smash H'. naive_solver.
  - exists σ. by eapply StoreHSP.
  - exists ({| heap := σ.(heap); urns :=urns_subst_f_to_urns f|}).
    destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=. eapply RandHSP; try done.
    urn_smash H'. naive_solver.
  - exists ({| heap := σ.(heap); urns :=urns_subst_f_to_urns f|}).
    destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=. eapply DRandHSP; try done.
    urn_smash H'. naive_solver.
    (** laplace *)
  - apply urn_subst_equal_well_typed in H3, H4.
    destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=.
    apply urn_subst_well_typed in H3 as ?. destruct!/=.
    eapply urn_subst_equal_unique in H0; last apply urn_subst_equal_obv; last by eapply urn_subst_is_simple. simplify_eq. simpl in *. simplify_eq.
    by eapply head_step_pred_laplace.
  - apply urn_subst_equal_well_typed in H0, H4.
    destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=.
    apply urn_subst_well_typed in H0 as ?. destruct!/=.
    eapply urn_subst_equal_unique in H3; last apply urn_subst_equal_obv; last by eapply urn_subst_is_simple. simplify_eq. simpl in *. simplify_eq.
    by eapply head_step_pred_laplace.
  - apply urn_subst_equal_well_typed in H0, H3.
    destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=.
    apply urn_subst_well_typed in H0 as ?. destruct!/=.
    eapply urn_subst_equal_unique in H4; last apply urn_subst_equal_obv; last by eapply urn_subst_is_simple. simplify_eq. simpl in *. simplify_eq.
    by eapply head_step_pred_laplace.
  - apply urn_subst_equal_well_typed in H3, H4.
    destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=.
    apply urn_subst_well_typed in H3 as ?. destruct!/=.
    eapply urn_subst_equal_unique in H0; last apply urn_subst_equal_obv; last by eapply urn_subst_is_simple. simplify_eq. simpl in *. simplify_eq.
    by eapply head_step_pred_laplace.
  - apply urn_subst_equal_well_typed in H0, H4.
    destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=.
    apply urn_subst_well_typed in H0 as ?. destruct!/=.
    eapply urn_subst_equal_unique in H3; last apply urn_subst_equal_obv; last by eapply urn_subst_is_simple. simplify_eq. simpl in *. simplify_eq.
    by eapply head_step_pred_laplace.
  - apply urn_subst_equal_well_typed in H0, H3.
    destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=.
    apply urn_subst_well_typed in H0 as ?. destruct!/=.
    eapply urn_subst_equal_unique in H4; last apply urn_subst_equal_obv; last by eapply urn_subst_is_simple. simplify_eq. simpl in *. simplify_eq.
    by eapply head_step_pred_laplace.
    (** Dlaplace*)
  - apply urn_subst_equal_well_typed in H3, H4.
    destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=.
    apply urn_subst_well_typed in H3 as ?. destruct!/=.
    eapply urn_subst_equal_unique in H0; last apply urn_subst_equal_obv; last by eapply urn_subst_is_simple. simplify_eq. simpl in *. simplify_eq.
    by eapply head_step_pred_dlaplace.
  - apply urn_subst_equal_well_typed in H0, H4.
    destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=.
    apply urn_subst_well_typed in H0 as ?. destruct!/=.
    eapply urn_subst_equal_unique in H3; last apply urn_subst_equal_obv; last by eapply urn_subst_is_simple. simplify_eq. simpl in *. simplify_eq.
    by eapply head_step_pred_dlaplace.
  - apply urn_subst_equal_well_typed in H0, H3.
    destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=.
    apply urn_subst_well_typed in H0 as ?. destruct!/=.
    eapply urn_subst_equal_unique in H4; last apply urn_subst_equal_obv; last by eapply urn_subst_is_simple. simplify_eq. simpl in *. simplify_eq.
    by eapply head_step_pred_dlaplace.
  - apply urn_subst_equal_well_typed in H3, H4.
    destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=.
    apply urn_subst_well_typed in H3 as ?. destruct!/=.
    eapply urn_subst_equal_unique in H0; last apply urn_subst_equal_obv; last by eapply urn_subst_is_simple. simplify_eq. simpl in *. simplify_eq.
    by eapply head_step_pred_dlaplace.
  - apply urn_subst_equal_well_typed in H0, H4.
    destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=.
    apply urn_subst_well_typed in H0 as ?. destruct!/=.
    eapply urn_subst_equal_unique in H3; last apply urn_subst_equal_obv; last by eapply urn_subst_is_simple. simplify_eq. simpl in *. simplify_eq.
    by eapply head_step_pred_dlaplace.
  - apply urn_subst_equal_well_typed in H0, H3.
    destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=.
    apply urn_subst_well_typed in H0 as ?. destruct!/=.
    eapply urn_subst_equal_unique in H4; last apply urn_subst_equal_obv; last by eapply urn_subst_is_simple. simplify_eq. simpl in *. simplify_eq.
    by eapply head_step_pred_dlaplace.
Admitted.
  
Lemma fill_item_not_match K1 K2 e v v': 
  K1 ≠ K2 -> fill_item K1 e = fill_item K2 (Val v) ->
  ∃ K1', fill_item K1' e = fill_item K2 (Val v').
Proof.
  intros H1 H2.
  destruct K1, K2; simplify_eq; simpl.
  - by eexists (AppLCtx _).
  - by eexists (AppRCtx _).
  - by eexists (BinOpLCtx _ _).
  - by eexists (BinOpRCtx _ _).
  - by eexists (PairLCtx _).
  - by eexists (PairRCtx _).
  - by eexists (AllocNLCtx _).
  - by eexists (AllocNRCtx _).
  - by eexists (StoreLCtx _).
  - by eexists (StoreRCtx _).
  - by eexists (LaplaceNumCtx _ _).
  - by eexists (LaplaceNumCtx _ _).
  - by eexists (LaplaceDenCtx _ _).
  - by eexists (LaplaceDenCtx _ _).
  - by eexists (LaplaceLocCtx _ _).
  - by eexists (LaplaceLocCtx _ _).
  - by eexists (DLaplaceNumCtx _ _).
  - by eexists (DLaplaceNumCtx _ _).
  - by eexists (DLaplaceDenCtx _ _).
  - by eexists (DLaplaceDenCtx _ _).
  - by eexists (DLaplaceLocCtx _ _).
  - by eexists (DLaplaceLocCtx _ _).
Qed.
  

Lemma value_promote_preserves_atomicity_empty_context f v v' e1' e2' σ σ' K K' :
  urn_subst_val f v = Some v' ->
  head_step_rel e1' σ e2' σ' ->
  fill K' e1' = fill K (Val v') ->
  ( ∀ (σ σ' : state) (K0 : list ectx_item) (e1' : ectxi_language.expr d_prob_ectxi_lang) (e2' : expr),
      fill K0 e1' = fill K v → head_step e1' σ (e2', σ') > 0 → is_Some (to_val (fill K0 e2'))) ->
  K' = [].
Proof.
  intros H1 H2 H3 H4.
  eapply fill_equal_break in H3 as H5; last first.
  { rewrite head_step_pred_ex_rel. naive_solver. }
  destruct H5 as [H|H].
  - destruct!/=.
    rewrite fill_app in H3.
    simplify_eq.
    assert (head_step_pred (fill K1 v') σ) as H3.
    { rewrite head_step_pred_ex_rel. naive_solver. }
    apply head_step_pred_fill in H3 as H5.
    destruct!/=.
    setoid_rewrite head_step_support_equiv_rel in H4.
    eapply value_promote_preserves_atomicity_empty_context1 in H3 as K; last done.
    destruct!/=.
    rewrite head_step_pred_ex_rel in K.
    destruct!/=.
    eapply H4 in K; last done.
    by eapply fill_to_val.
  - destruct H as (Hall & K1 & K1' & K2 & -> &-> &H&Hneq).
    rewrite !fill_app//= in H3, H.
    simplify_eq. simpl in *.
    eapply (fill_item_not_match _ _ _ _ v) in H; last done.
    destruct!/=.
    setoid_rewrite head_step_support_equiv_rel in H4.
    eapply (H4 _ _ ((_++[_])++Hall)) in H2; last first.
    + erewrite fill_app. f_equal.
      erewrite fill_app. by rewrite -H.
    + apply fill_to_val in H2.
      apply app_eq_nil in H2 as [H2 H'].
      apply app_eq_nil in H2. destruct!/=.
Qed. 
    (* destruct (list_destruct_rev K1) as [|[K1' [K2']]]. *)
    (* + subst. simpl in *. inversion H2. *)
    (* + subst. rewrite fill_app in H2. simpl in H2. *)
    (*   destruct (list_destruct_rev K2') as [|[K1'' [K2'']]]; last first. *)
    (*   { subst. rewrite fill_app in H2. *)
    (*     simpl in *. inversion H2; destruct K1'; simplify_eq; destruct K1''; simplify_eq. *)
    (*   } *)
    (*   subst. simpl in *. *)
    (*   inversion H2; destruct K1'; simplify_eq; simpl in *; simplify_eq. *)
    (*   * unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply PairS|..]. by fill_inv. *)
    (*   * unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply PairS|..]. by fill_inv. *)
    (*   * unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply InjLS|..]; last by fill_inv. *)
    (*   * unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply InjRS|..]; last by fill_inv. *)
    (*   * destruct v; simpl in *; repeat setoid_rewrite bind_Some in H1; destruct!/=. *)
    (*     unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply BetaS|..]; last by fill_inv. *)
    (*     2:{ done. } *)
    (*   * unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply BetaS|..]; last by fill_inv. *)
    (*     2:{ done. } *)
    (*   * unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply UnOpS|..]; last by fill_inv. *)
        
    (*     admit. *)
    (*   * admit. *)
    (*   * admit. *)
    (*   * destruct v; simpl in *; repeat setoid_rewrite bind_Some in H1; destruct!/=. *)
    (*     unshelve epose proof H4 ({|heap:=inhabitant; urns :=urns_subst_f_to_urns  f|}) _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply IfTrueS|..]; last by fill_inv. *)
    (*     admit.  *)
    (*   * destruct v; simpl in *; repeat setoid_rewrite bind_Some in H1; destruct!/=. *)
    (*     unshelve epose proof H4 ({|heap:=inhabitant; urns :=urns_subst_f_to_urns  f|}) _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply IfFalseS|..]; last by fill_inv. *)
    (*     admit.  *)
    (*   * destruct v; simpl in *; repeat setoid_rewrite bind_Some in H1; destruct!/=. *)
    (*     unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply FstS|..]; last by fill_inv. *)
    (*   * destruct v; simpl in *; repeat setoid_rewrite bind_Some in H1; destruct!/=. *)
    (*     unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply SndS|..]; last by fill_inv. *)
    (*   * destruct v; simpl in *; repeat setoid_rewrite bind_Some in H1; destruct!/=. *)
    (*     unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply CaseLS|..]; last by fill_inv. *)
    (*   * destruct v; simpl in *; repeat setoid_rewrite bind_Some in H1; destruct!/=. *)
    (*     unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply CaseRS|..]; last by fill_inv. *)
    (*   * destruct v; simpl in *; repeat setoid_rewrite bind_Some in H1; destruct!/=. *)
    (*     unshelve epose proof H4 ({|heap:=inhabitant; urns :=urns_subst_f_to_urns  f|}) _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply AllocNS|..]; last by fill_inv. *)
    (*     all: try done. *)
    (*     admit. *)
    (*   * unshelve epose proof H4 ({|heap:=inhabitant; urns :=urns_subst_f_to_urns  f|}) _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply AllocNS|..]; last by fill_inv. *)
    (*     all: try done. *)
    (*     admit. *)
    (*   * destruct v as [l0| | | |]; simpl in *; repeat setoid_rewrite bind_Some in H1; destruct!/=. *)
    (*     destruct l0; simpl in *; repeat setoid_rewrite bind_Some in H; destruct!/=; repeat case_match; simplify_eq. *)
    (*     -- admit. *)
    (*     -- admit.  *)
    (*   * admit. *)
    (*   * admit.  *)
    (*   * admit. *)
    (*   * admit.  *)
    (*   * admit. *)
    (*   * admit.  *)
    (*   * admit. *)
    (*   * admit.  *)
    (*   * admit. *)
    (*   * admit.  *)
    (*   * admit. *)
    (*   * admit.  *)
    (*   * admit. *)
    (*   * admit.  *)
    (*   * admit. *)
    (*   * admit.  *)


Lemma value_promote_preserves_atomicity K f v v':
  Atomic StronglyAtomic (fill K (Val v)) ->
  urn_subst_val f v = Some v' ->
  Atomic StronglyAtomic (fill K (Val v')).
Proof.
  rewrite /Atomic/=.
  intros H1 H2 σ e' σ' Hstep.
  rewrite prim_step_iff in Hstep.
  destruct Hstep as (K' & e1' & e2' & H3 & <- & H4).
  simpl in *.
  rewrite head_step_support_equiv_rel in H4.
  setoid_rewrite prim_step_iff in H1.
  simpl in *.
  assert (∀ (σ : state) (σ' : state) (K0 : list ectx_item) e1' e2',
      fill K0 e1' = fill K v  -> head_step e1' σ (e2', σ') > 0
      → is_Some (to_val (fill K0 e2'))) as H1' by naive_solver.
  clear H1.
  assert (K' = []) as ->; last first.
  { simpl.
    inversion H4; simpl; subst; simpl in *; try done.
    - simpl in *.
      destruct (list_destruct_rev K) as [|[K1 [K2]]]; simplify_eq.
      rewrite fill_app in H3.
      simpl in *.
      destruct K1; simplify_eq; simpl in *; simplify_eq.
      + destruct (list_destruct_rev K2) as [|[K1' [K2']]]; simplify_eq; last first. 
        * rewrite fill_app in H3. simpl in *. destruct K1'; simplify_eq.
        * simpl in *. simplify_eq.
          destruct v; simpl in *; repeat setoid_rewrite bind_Some in H2; destruct!/=.
          unshelve epose proof H1' σ' σ' [] _ _ _ _; [| |done|..].
          2:{ rewrite head_step_support_equiv_rel.
              by apply BetaS. }
          simpl in *.
          unfold is_Some in *. destruct!/=.
          rename select (to_val _ = _) into H'.
          apply of_to_val in H'. subst.
          destruct x, f0; simpl in *.
          -- simpl in *. subst. setoid_rewrite bind_Some in H. destruct!/=.
             naive_solver.
          -- induction e; simplify_eq; simpl in *; subst; simplify_eq.
             ++ setoid_rewrite bind_Some in H. destruct!/=.
                naive_solver.
             ++ case_match; subst; simplify_eq; simpl.
                case_match; last done.
                naive_solver.
          -- induction e; simpl in *; simplify_eq.
             ++ rewrite bind_Some in H. destruct!/=; naive_solver.
             ++ case_match; subst; simpl; case_match; try done.
                naive_solver.
          -- induction e; simpl in *; simplify_eq.
             ++ rewrite bind_Some in H. destruct!/=; naive_solver.
             ++ case_match; subst; simpl; case_match; try done; first naive_solver.
                simpl. case_match; subst; first naive_solver.
                simpl in *; by case_match. 
      + unshelve epose proof (fill_to_val K2 _ _) as ->; [|by erewrite <-H|].
        simpl in *. simplify_eq.
        unshelve epose proof H1' σ' σ' [] _ _ _ _; [| |done|..].
        2:{ rewrite head_step_support_equiv_rel.
            by apply BetaS.
        }
        simpl in *.
        by eapply subst_to_val_change'.
    - destruct (list_destruct_rev K) as [|[K1[K2]]]; simplify_eq.
      rewrite fill_app in H3.
      destruct K1; simplify_eq; simpl in *; simplify_eq.
      destruct (list_destruct_rev K2) as [|[K1' [K2']]]; simplify_eq; last first.
      * rewrite fill_app in H3; simpl in *; destruct K1'; simplify_eq.
      * simpl in *. simplify_eq.
        destruct v; simpl in *; repeat setoid_rewrite bind_Some in H2; destruct!/=.
        eapply urn_subst_equal_unique in H; last apply urn_subst_equal_obv; last first.
        { by eapply urn_subst_is_simple. }
        subst. 
        unshelve epose proof H1' ({|heap:=∅; urns:=urns_subst_f_to_urns f|}) ({|heap:=∅; urns:=urns_subst_f_to_urns f|}) [] _ _ _ _; [| |done|..].
        2:{ rewrite head_step_support_equiv_rel.
            eapply IfTrueS.
            intros ? H .
            simpl in *.
            apply urns_subst_f_to_urns_unique_valid in H.
            by subst. 
        }
        done. 
    - destruct (list_destruct_rev K) as [|[K1[K2]]]; simplify_eq.
      rewrite fill_app in H3.
      destruct K1; simplify_eq; simpl in *; simplify_eq.
      destruct (list_destruct_rev K2) as [|[K1' [K2']]]; simplify_eq; last first.
      * rewrite fill_app in H3; simpl in *; destruct K1'; simplify_eq.
      * simpl in *. simplify_eq.
        destruct v; simpl in *; repeat setoid_rewrite bind_Some in H2; destruct!/=.
        eapply urn_subst_equal_unique in H; last apply urn_subst_equal_obv; last first.
        { by eapply urn_subst_is_simple. }
        subst. 
        unshelve epose proof H1' ({|heap:=∅; urns:=urns_subst_f_to_urns f|}) ({|heap:=∅; urns:=urns_subst_f_to_urns f|}) [] _ _ _ _; [| |done|..].
        2:{ rewrite head_step_support_equiv_rel.
            eapply IfFalseS.
            intros ? H .
            simpl in *.
            apply urns_subst_f_to_urns_unique_valid in H.
            by subst. 
        }
        done. 
    - destruct (list_destruct_rev K) as [|[K1[K2]]]; simplify_eq.
      rewrite fill_app in H3.
      destruct K1; simplify_eq; simpl in *; simplify_eq.
      destruct (list_destruct_rev K2) as [|[K1' [K2']]]; simplify_eq; last first.
      { rewrite fill_app in H3. destruct K1'; simplify_eq. }
      simpl in *. simplify_eq.
      destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=. 
      unshelve epose proof H1' σ' σ' [] _ _ _ _ as IHv'; [| |done| |].
      2:{ rewrite head_step_support_equiv_rel. apply CaseLS. }
      done. 
    - destruct (list_destruct_rev K) as [|[K1[K2]]]; simplify_eq.
      rewrite fill_app in H3.
      destruct K1; simplify_eq; simpl in *; simplify_eq.
      destruct (list_destruct_rev K2) as [|[K1' [K2']]]; simplify_eq; last first.
      { rewrite fill_app in H3. destruct K1'; simplify_eq. }
      simpl in *. simplify_eq.
      induction v; repeat setoid_rewrite bind_Some in H2; destruct!/=. 
      unshelve epose proof H1' σ' σ' [] _ _ _ _; [| |done| |].
      2:{ rewrite head_step_support_equiv_rel. apply CaseRS. }
      done. 
  }
  by eapply value_promote_preserves_atomicity_empty_context.
Qed. 

                     
