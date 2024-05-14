From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Lim_seq.
From stdpp Require Import fin_maps fin_map_dom.
From clutch.prelude Require Import stdpp_ext.
From clutch.common Require Import language ectx_language erasable.
From clutch.prob_lang Require Import locations notation lang metatheory.
From clutch.prob Require Import couplings couplings_app markov.

Set Default Proof Using "Type*".
Local Open Scope R.

Section erasure_helpers.

  Variable (m : nat).
  Hypothesis IH :
    ∀ (e1 : expr) (σ1 : state) α N zs,
    tapes σ1 !! α = Some (N; zs) →
    Rcoupl
      (exec m (e1, σ1))
      (dunifP N ≫= (λ z, exec m (e1, state_upd_tapes <[α:= (N; zs ++ [z])]> σ1))) eq.

  Local Lemma ind_case_det e σ α N zs K :
    tapes σ !! α = Some (N; zs) →
    is_det_head_step e σ = true →
    Rcoupl
      (dmap (fill_lift K) (head_step e σ) ≫= exec m)
      (dunifP N ≫= (λ z, dmap
                           (fill_lift K)
                           (head_step e (state_upd_tapes <[α:= (N; zs ++ [z]) ]> σ)) ≫= exec m))
       (=).
  Proof using m IH.
    intros Hα (e2 & (σ2 & Hdet))%is_det_head_step_true%det_step_pred_ex_rel.
    erewrite 1!det_head_step_singleton; [|done..].
    setoid_rewrite (det_head_step_singleton ); eauto; last first.
    - eapply det_head_step_upd_tapes; eauto.
    - erewrite det_step_eq_tapes in Hα; [|done].
      rewrite !dmap_dret.
      setoid_rewrite (dmap_dret (fill_lift K)).
      rewrite !dret_id_left.
      setoid_rewrite (dret_id_left (exec m)).
      eapply IH; eauto.
  Qed.

  Local Lemma ind_case_dzero e σ α N zs K :
    tapes σ !! α = Some (N; zs) →
    head_step e σ = dzero →
    Rcoupl
      (dmap (fill_lift K) (head_step e σ) ≫= exec m)
      (dunifP N ≫= (λ z,
         dmap (fill_lift K) (head_step e (state_upd_tapes <[α:=(N; zs ++ [z])]> σ)) ≫= exec m)) eq.
  Proof using m IH.
    intros Hα Hz.
    rewrite Hz.
    setoid_rewrite head_step_dzero_upd_tapes; [|by eapply elem_of_dom_2|done].
    rewrite dmap_dzero dbind_dzero dzero_dbind.
    apply Rcoupl_dzero_dzero.
  Qed.

  Local Lemma ind_case_alloc σ α N ns (z : Z) K :
    tapes σ !! α = Some (N; ns) →
    Rcoupl
      (dmap (fill_lift K) (head_step (alloc #z) σ) ≫= exec m)
      (dunifP N ≫=
         (λ n, dmap (fill_lift K) (head_step (alloc #z) (state_upd_tapes <[α:= (N; ns ++ [n])]> σ)) ≫= exec m))
      eq.
  Proof using m IH.
    intros Hα.
    rewrite dmap_dret dret_id_left -/exec.
    setoid_rewrite (dmap_dret (fill_lift K)).
    setoid_rewrite (dret_id_left (exec m)).
    (* TODO: fix slightly ugly hack ... *)
    revert IH; intro IHm.
    apply lookup_total_correct in Hα as Hαtot.
    pose proof (elem_fresh_ne _ _ _ Hα) as Hne.
    erewrite dbind_ext_right; last first.
    { intros n.
      rewrite -(fresh_loc_upd_some _ _ (N; ns)); [|done].
      rewrite (fresh_loc_upd_swap σ α (N; ns) (_; [])) //. }
    apply IHm.
    by apply fresh_loc_lookup.
  Qed.

  Local Lemma ind_case_rand_some σ α α' K N M (z : Z) n ns ns' :
    N = Z.to_nat z →
    tapes σ !! α = Some (M; ns') →
    tapes σ !! α' = Some (N; n :: ns) →
    Rcoupl
      (dmap (fill_lift K) (head_step (rand(#lbl:α') #z) σ) ≫= exec m)
      (dunifP M ≫=
         (λ n, dmap (fill_lift K)
                 (head_step (rand(#lbl:α') #z) (state_upd_tapes <[α:= (M; ns' ++ [n])]> σ))
                 ≫= exec m))
      (=).
  Proof using m IH.
    intros Hz Hα Hα'.
    apply lookup_total_correct in Hα as Hαtot.
    apply lookup_total_correct in Hα' as Hα'tot.
    destruct (decide (α = α')) as [-> | Hαneql].
    - simplify_eq. rewrite /head_step Hα.
      setoid_rewrite lookup_insert.
      rewrite bool_decide_eq_true_2 //.
      rewrite dmap_dret dret_id_left -/exec.
      erewrite dbind_ext_right; last first.
      { intros.
        rewrite -app_comm_cons.
        rewrite upd_tape_twice dmap_dret dret_id_left -/exec //. }
      assert (Haux : ∀ n,
                 state_upd_tapes <[α':=(Z.to_nat z; ns ++ [n])]> σ =
                 state_upd_tapes <[α':=(Z.to_nat z; ns ++ [n])]> (state_upd_tapes <[α':=(Z.to_nat z; ns)]> σ)).
      { intros. rewrite /state_upd_tapes. f_equal. rewrite insert_insert //. }
      erewrite dbind_ext_right; [| intros; rewrite Haux; done].
      apply IH.
      apply lookup_insert.
    - rewrite /head_step Hα'.
      rewrite bool_decide_eq_true_2 //.
      setoid_rewrite lookup_insert_ne; [|done].
      rewrite Hα' bool_decide_eq_true_2 //.
      rewrite !dmap_dret !dret_id_left -/exec.
      erewrite dbind_ext_right; last first.
      { intros.
        rewrite upd_diff_tape_comm; [|done].
        rewrite dmap_dret dret_id_left -/exec //. }
      eapply IH.
      rewrite lookup_insert_ne //.
  Qed.

  Local Lemma ind_case_rand_empty σ α α' K (N M : nat) z ns :
    M = Z.to_nat z →
    tapes σ !! α = Some (N; ns) →
    tapes σ !! α' = Some (M; []) →
    Rcoupl
      (dmap (fill_lift K) (head_step (rand(#lbl:α') #z) σ) ≫= exec m)
      (dunifP N ≫=
         (λ n, dmap (fill_lift K)
                 (head_step (rand(#lbl:α') #z) (state_upd_tapes <[α := (N; ns ++ [n])]> σ))
                 ≫= exec m))
      eq.
  Proof using m IH.
    intros Hz Hα Hα'.
    destruct (decide (α = α')) as [-> | Hαneql].
    + simplify_eq.  rewrite /head_step Hα.
      rewrite bool_decide_eq_true_2 //.
      rewrite {1 2}/dmap.
      rewrite -!dbind_assoc -/exec.
      eapply (Rcoupl_dbind _ _ _ _ (=)); [ |apply Rcoupl_eq].
      intros ? b ->.
      do 2 rewrite dret_id_left.
      rewrite lookup_insert.
      rewrite bool_decide_eq_true_2 //.
      rewrite dmap_dret dret_id_left -/exec.
      rewrite upd_tape_twice.
      rewrite /state_upd_tapes insert_id //.
      destruct σ; simpl.
      apply Rcoupl_eq.
    + rewrite /head_step /=.
      setoid_rewrite lookup_insert_ne; [|done].
      rewrite Hα'.
      rewrite bool_decide_eq_true_2 //.
      rewrite {1 2}/dmap.
      erewrite (dbind_ext_right (dunifP N)); last first.
      { intro.
        rewrite {1 2}/dmap.
        do 2 rewrite -dbind_assoc -/exec.
        done. }
      rewrite -!dbind_assoc -/exec.
      rewrite dbind_comm.
      eapply Rcoupl_dbind; [|apply Rcoupl_eq].
      intros; simplify_eq.
      do 2 rewrite dret_id_left /=.
      erewrite dbind_ext_right; last first.
      { intro; do 2 rewrite dret_id_left. done. }
      by apply IH.
  Qed.

  Local Lemma ind_case_rand_some_neq σ α α' K N M ns ns' z :
    N ≠ Z.to_nat z →
    tapes σ !! α = Some (M; ns') →
    tapes σ !! α' = Some (N; ns) →
    Rcoupl
      (dmap (fill_lift K) (head_step (rand(#lbl:α') #z) σ) ≫= exec m)
      (dunifP M ≫=
         (λ n, dmap (fill_lift K)
                 (head_step (rand(#lbl:α') #z) (state_upd_tapes <[α:= (M; ns' ++ [n]) : tape]> σ))
                 ≫= exec m))
      (=).
  Proof using m IH.
    intros Hz Hα Hα'.
    rewrite /head_step Hα'.
    rewrite bool_decide_eq_false_2 //.
    destruct (decide (α = α')) as [-> | Heq].
    - simplify_eq.
      setoid_rewrite lookup_insert.
      rewrite bool_decide_eq_false_2 //.
      rewrite /dmap /=.
      rewrite -!dbind_assoc -/exec.
      erewrite (dbind_ext_right (dunifP M)); last first.
      { intros. rewrite -!dbind_assoc -/exec //. }
      rewrite dbind_comm.
      eapply Rcoupl_dbind; [|apply Rcoupl_eq].
      intros; simplify_eq.
      rewrite 2!dret_id_left.
      erewrite dbind_ext_right; last first.
      { intros. rewrite 2!dret_id_left //. }
      by apply IH.
    - setoid_rewrite lookup_insert_ne; [|done].
      rewrite Hα' bool_decide_eq_false_2 //.
      rewrite /dmap.
      rewrite -!dbind_assoc -/exec.
      erewrite (dbind_ext_right (dunifP M)); last first.
      { intros. rewrite -!dbind_assoc -/exec //. }
      rewrite dbind_comm.
      eapply Rcoupl_dbind; [|apply Rcoupl_eq].
      intros; simplify_eq.
      rewrite 2!dret_id_left.
      erewrite dbind_ext_right; last first.
      { intros. rewrite 2!dret_id_left //. }
      by apply IH.
  Qed.

  Local Lemma ind_case_rand σ α K (M N : nat) z ns :
    N = Z.to_nat z →
    tapes σ !! α = Some (M; ns) →
    Rcoupl
      (dmap (fill_lift K) (head_step (rand #z) σ) ≫= exec m)
      (dunifP M ≫=
         (λ n,
           dmap (fill_lift K)
             (head_step (rand #z) (state_upd_tapes <[α := (M; ns ++ [n]) : tape]> σ))
             ≫= exec m))
      eq.
  Proof using m IH.
    intros Hz Hα.
    rewrite /head_step.
    rewrite {1 2}/dmap.
    erewrite (dbind_ext_right (dunifP M)); last first.
    { intro.
      rewrite {1 2}/dmap.
      do 2 rewrite -dbind_assoc //. }
    rewrite -/exec /=.
    rewrite -!dbind_assoc -/exec.
    erewrite (dbind_ext_right (dunifP M)); last first.
    { intros n. rewrite -!dbind_assoc. done. }
    rewrite dbind_comm.
    eapply Rcoupl_dbind; [|apply Rcoupl_eq].
    intros; simplify_eq.
    do 2 rewrite dret_id_left.
    erewrite dbind_ext_right; last first.
    { intro; do 2 rewrite dret_id_left; auto. }
    apply IH; auto.
  Qed.

End erasure_helpers.


Lemma prim_coupl_upd_tapes_dom m e1 σ1 α N ns :
  σ1.(tapes) !! α = Some (N; ns) →
  Rcoupl
    (exec m (e1, σ1))
    (dunifP N ≫=
       (λ n, exec m (e1, state_upd_tapes <[α := (N; ns ++ [n])]> σ1)))
    (=).
Proof.
  revert e1 σ1 α N ns; induction m; intros e1 σ1 α N ns Hα.
  - rewrite /exec /=.
    destruct (to_val e1) as [v|] eqn:He1.
    + rewrite (dret_const (dunifP N) v); [apply Rcoupl_eq | apply dunif_mass; lia].
    + rewrite dzero_dbind. apply Rcoupl_dzero_dzero.
  - rewrite exec_Sn /step_or_final /=.
    destruct (to_val e1) eqn:He1.
    + rewrite dret_id_left -/exec.
      erewrite (exec_is_final); [|done].
      rewrite dret_const; [|solve_distr_mass].
      by apply Rcoupl_dret.
    + rewrite /prim_step /=.
      destruct (decomp e1) as [K ered] eqn:Hdecomp_e1.
      rewrite Hdecomp_e1.
      destruct (det_or_prob_or_dzero ered σ1) as [ HD | [HP | HZ]].
      * eapply ind_case_det; [done|done|]. by apply is_det_head_step_true.
      * inversion HP; simplify_eq.
        -- by eapply ind_case_alloc.
        -- by eapply ind_case_rand_some.
        -- by eapply ind_case_rand_empty.
        -- by eapply ind_case_rand_some_neq.
        -- by eapply ind_case_rand.
      * by eapply ind_case_dzero.
Qed.

Lemma prim_coupl_step_prim m e1 σ1 α bs :
  σ1.(tapes) !! α = Some bs →
  Rcoupl
    (exec m (e1, σ1))
    (state_step σ1 α ≫= (λ σ2, exec m (e1, σ2)))
    eq.
Proof.
  intros Hα.
  rewrite /state_step.
  rewrite bool_decide_eq_true_2; last first.
  { apply elem_of_dom; auto. }
  simpl.
  rewrite (lookup_total_correct (tapes σ1) α bs); auto.
  destruct bs; simpl.
  rewrite /dmap.
  rewrite -dbind_assoc.
  erewrite dbind_ext_right; last first.
  { intro. rewrite dret_id_left; auto. }
  by eapply prim_coupl_upd_tapes_dom.
Qed.

Lemma state_step_erasable σ1 α bs :
  σ1.(tapes) !! α = Some bs →
  erasable (state_step σ1 α) σ1.
Proof.
  intros. rewrite /erasable.
  intros.
  symmetry.
  apply Rcoupl_eq_elim.
  by eapply prim_coupl_step_prim.
Qed.
  

Lemma limprim_coupl_step_limprim_aux e1 σ1 α bs v:
  σ1.(tapes) !! α = Some bs →
  (lim_exec (e1, σ1)) v =
  (state_step σ1 α ≫= (λ σ2, lim_exec (e1, σ2))) v.
Proof.
  intro Hsome.
   rewrite lim_exec_unfold/=.
   rewrite {2}/pmf/=/dbind_pmf.
   setoid_rewrite lim_exec_unfold.
   simpl in *.
   assert
     (SeriesC (λ a: state, state_step σ1 α a * Sup_seq (λ n : nat, exec n (e1, a) v)) =
     SeriesC (λ a: state, Sup_seq (λ n : nat, state_step σ1 α a * exec n (e1, a) v))) as Haux.
   { apply SeriesC_ext; intro v'.
     apply eq_rbar_finite.
     rewrite rmult_finite.
     rewrite (rbar_finite_real_eq (Sup_seq (λ n : nat, exec n (e1, v') v))); auto.
     - rewrite <- (Sup_seq_scal_l (state_step σ1 α v') (λ n : nat, exec n (e1, v') v)); auto.
     - apply (Rbar_le_sandwich 0 1).
       + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
       + apply upper_bound_ge_sup; intro; simpl; auto.
   }
   rewrite Haux.
   rewrite (MCT_seriesC _ (λ n, exec n (e1,σ1) v) (lim_exec (e1,σ1) v)); auto.
   - real_solver.
   - intros. apply Rmult_le_compat; auto; [done|apply exec_mono].
   - intro. exists (state_step σ1 α a)=>?. real_solver.
   - intro n.
     rewrite (Rcoupl_eq_elim _ _ (prim_coupl_step_prim n e1 σ1 α bs Hsome)); auto.
     rewrite {3}/pmf/=/dbind_pmf.
     apply SeriesC_correct; auto.
     apply (ex_seriesC_le _ (state_step σ1 α)); auto.
     real_solver.
   - rewrite lim_exec_unfold.
     rewrite rbar_finite_real_eq; [apply Sup_seq_correct |].
     rewrite mon_sup_succ.
     + apply (Rbar_le_sandwich 0 1); auto.
       * apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
       * apply upper_bound_ge_sup; intro; simpl; auto.
     + intros. eapply exec_mono.
Qed.

Lemma limprim_coupl_step_limprim e1 σ1 α bs :
  σ1.(tapes) !! α = Some bs →
  Rcoupl
    (lim_exec (e1, σ1))
    (state_step σ1 α ≫= (λ σ2, lim_exec (e1, σ2)))
    eq.
Proof.
  intro Hsome.
  erewrite (distr_ext (lim_exec (e1, σ1))); last first.
  - intro a.
    apply (limprim_coupl_step_limprim_aux _ _ _ _ _ Hsome).
  - apply Rcoupl_eq.
Qed.

Lemma lim_exec_eq_erasure αs e σ :
  αs ⊆ get_active σ →
  lim_exec (e, σ) = foldlM state_step σ αs ≫= (λ σ', lim_exec (e, σ')).
Proof.
  induction αs as [|α αs IH] in σ |-*.
  { rewrite /= dret_id_left //. }
  intros Hα.
  eapply Rcoupl_eq_elim.
  assert (lim_exec (e, σ) = state_step σ α ≫= (λ σ2, lim_exec (e, σ2))) as ->.
  { apply distr_ext => v.
    assert (α ∈ get_active σ) as Hel; [apply Hα; left|].
    rewrite /get_active in Hel.
    apply elem_of_elements, elem_of_dom in Hel as [? ?].
    by eapply limprim_coupl_step_limprim_aux. }
  rewrite foldlM_cons -dbind_assoc.
  eapply Rcoupl_dbind; [|eapply Rcoupl_pos_R, Rcoupl_eq].
  intros ?? (-> & Hs%state_step_support_equiv_rel & _).
  inversion_clear Hs.
  rewrite IH; [eapply Rcoupl_eq|].
  intros α' ?. rewrite /get_active /=.
  apply elem_of_elements.
  apply elem_of_dom.
  destruct (decide (α = α')); subst.
  + eexists. rewrite lookup_insert //.
  + rewrite lookup_insert_ne //.
    apply elem_of_dom. eapply elem_of_elements, Hα. by right.
Qed.

Lemma refRcoupl_erasure e1 σ1 e1' σ1' α α' R Φ m bs bs':
  σ1.(tapes) !! α = Some bs →
  σ1'.(tapes) !! α' = Some bs' →
  Rcoupl (state_step σ1 α) (state_step σ1' α') R →
  (∀ σ2 σ2', R σ2 σ2' →
             refRcoupl (exec m (e1, σ2))
               (lim_exec (e1', σ2')) Φ ) →
  refRcoupl (exec m (e1, σ1))
    (lim_exec (e1', σ1')) Φ.
Proof.
  intros Hα Hα' HR Hcont.
  eapply refRcoupl_eq_refRcoupl_unfoldl ;
    [eapply prim_coupl_step_prim; eauto |].
  eapply refRcoupl_eq_refRcoupl_unfoldr;
    [| eapply Rcoupl_eq_sym, limprim_coupl_step_limprim; eauto].
  apply (refRcoupl_dbind _ _ _ _ R); auto.
  by eapply Rcoupl_refRcoupl.
Qed.

Lemma ARcoupl_erasure e1 σ1 e1' σ1' α α' R Φ ε ε' m bs bs':
  0 <= ε ->
  0 <= ε' ->
  σ1.(tapes) !! α = Some bs →
  σ1'.(tapes) !! α' = Some bs' →
  ARcoupl (state_step σ1 α) (state_step σ1' α') R ε →
  (∀ σ2 σ2', R σ2 σ2' →
             ARcoupl (exec m (e1, σ2))
               (lim_exec (e1', σ2')) Φ  ε' ) →
  ARcoupl (exec m (e1, σ1))
    (lim_exec (e1', σ1')) Φ (ε + ε').
Proof.
  intros Hε Hε' Hα Hα' HR Hcont.
  rewrite -(Rplus_0_l (ε + ε')).
  eapply ARcoupl_eq_trans_l; try lra.
  - eapply ARcoupl_from_eq_Rcoupl; try lra; eauto.
    eapply prim_coupl_step_prim; eauto.
  - rewrite -(Rplus_0_r (ε + ε')).
    eapply ARcoupl_eq_trans_r; auto; try lra; last first.
    + eapply ARcoupl_from_eq_Rcoupl; try lra; eauto.
      eapply Rcoupl_eq_sym, limprim_coupl_step_limprim; eauto.
    + apply (ARcoupl_dbind _ _ _ _ R); auto.
Qed.

Lemma refRcoupl_erasure_r (e1 : expr) σ1 e1' σ1' α' R Φ m bs':
  to_val e1 = None →
  σ1'.(tapes) !! α' = Some bs' →
  Rcoupl (prim_step e1 σ1) (state_step σ1' α') R →
  (∀ e2 σ2 σ2', R (e2, σ2) σ2' → refRcoupl (exec m (e2, σ2)) (lim_exec (e1', σ2')) Φ ) →
  refRcoupl (exec (S m) (e1, σ1)) (lim_exec (e1', σ1')) Φ.
Proof.
  intros He1 Hα' HR Hcont.
  rewrite exec_Sn_not_final; [|eauto].
  eapply (refRcoupl_eq_refRcoupl_unfoldr _ (state_step σ1' α' ≫= (λ σ2', lim_exec (e1', σ2')))).
  - eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl].
    intros [] ??. by apply Hcont.
  - apply Rcoupl_eq_sym. by eapply limprim_coupl_step_limprim.
Qed.


Lemma ARcoupl_erasure_r (e1 : expr) σ1 e1' σ1' α' R Φ ε ε' m bs':
  0 <= ε ->
  0 <= ε' ->
  to_val e1 = None →
  σ1'.(tapes) !! α' = Some bs' →
  ARcoupl (prim_step e1 σ1) (state_step σ1' α') R ε →
  (∀ e2 σ2 σ2', R (e2, σ2) σ2' → ARcoupl (exec m (e2, σ2)) (lim_exec (e1', σ2')) Φ ε' ) →
  ARcoupl (exec (S m) (e1, σ1)) (lim_exec (e1', σ1')) Φ (ε + ε').
Proof.
  intros Hε Hε' He1 Hα' HR Hcont.
  rewrite exec_Sn_not_final; [|eauto].
  rewrite -(Rplus_0_r (ε + ε')).
  eapply (ARcoupl_eq_trans_r _ (state_step σ1' α' ≫= (λ σ2', lim_exec (e1', σ2')))); try lra.
  - eapply ARcoupl_dbind; try lra; auto; [| apply HR].
    intros [] ??. by apply Hcont.
  - eapply ARcoupl_from_eq_Rcoupl; [lra | ].
    apply Rcoupl_eq_sym. by eapply limprim_coupl_step_limprim.
Qed.

Lemma refRcoupl_erasure_l (e1 e1' : expr) σ1 σ1' α R Φ m bs :
  σ1.(tapes) !! α = Some bs →
  Rcoupl (state_step σ1 α) (prim_step e1' σ1') R →
  (∀ σ2 e2' σ2', R σ2 (e2', σ2') → refRcoupl (exec m (e1, σ2)) (lim_exec (e2', σ2')) Φ ) →
  refRcoupl (exec m (e1, σ1)) (lim_exec (e1', σ1')) Φ.
Proof.
  intros Hα HR Hcont.
  assert (to_val e1' = None).
  { apply Rcoupl_pos_R, Rcoupl_inhabited_l in HR as (?&?&?&?&?); [eauto using val_stuck|].
    rewrite state_step_mass; [lra|]. apply elem_of_dom. eauto. }
  eapply (refRcoupl_eq_refRcoupl_unfoldl _ (state_step σ1 α ≫= (λ σ2, exec m (e1, σ2)))).
  - by eapply prim_coupl_step_prim.
  - rewrite lim_exec_step.
    rewrite step_or_final_no_final; [|eauto].
    eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl].
    intros ? [] ?. by apply Hcont.
Qed.

Lemma ARcoupl_erasure_l (e1 e1' : expr) σ1 σ1' α R Φ ε ε' m bs :
  0 <= ε ->
  0 <= ε' ->
  σ1.(tapes) !! α = Some bs →
  ARcoupl (state_step σ1 α) (prim_step e1' σ1') R ε →
  (∀ σ2 e2' σ2', R σ2 (e2', σ2') → ARcoupl (exec m (e1, σ2)) (lim_exec (e2', σ2')) Φ ε') →
  ARcoupl (exec m (e1, σ1)) (lim_exec (e1', σ1')) Φ (ε + ε').
Proof.
  intros Hε Hε' Hα HR Hcont.
  destruct (to_val e1') eqn:Hval.
  - assert (prim_step e1' σ1' = dzero) as Hz.
    { by eapply (is_final_dzero (e1', σ1')), to_final_Some_2. }
    rewrite Hz in HR.
    rewrite -(Rplus_0_l (ε + ε')).
    eapply (ARcoupl_eq_trans_l _ (state_step σ1 α ≫= (λ σ2, exec m (e1, σ2)))); [lra| lra | | ].
    + apply ARcoupl_from_eq_Rcoupl; [lra |].
      by eapply prim_coupl_step_prim.
    + rewrite lim_exec_step.
      rewrite step_or_final_is_final; [|eauto].
      eapply ARcoupl_dbind; [lra|lra| | ]; last first.
      * rewrite -(Rplus_0_r ε).
        eapply ARcoupl_eq_trans_r; [lra|lra| | apply ARcoupl_dzero; lra ].
        eauto.
      * intros ? [] ?. by apply Hcont.
  - rewrite -(Rplus_0_l (ε + ε')).
    eapply (ARcoupl_eq_trans_l _ (state_step σ1 α ≫= (λ σ2, exec m (e1, σ2)))); [lra| lra | | ].
    + apply ARcoupl_from_eq_Rcoupl; [lra |].
      by eapply prim_coupl_step_prim.
    + rewrite lim_exec_step.
      rewrite step_or_final_no_final; [|eauto].
      eapply ARcoupl_dbind; [lra|lra| | apply HR].
      intros ? [] ?. by apply Hcont.
Qed.


Lemma refRcoupl_erasure_erasable (e1 e1' : expr) σ1 σ1' μ1 μ2 R Φ n :
  Rcoupl (μ1) (μ2) R ->
  erasable μ1 σ1->
  erasable μ2 σ1'->
  (∀ σ2 σ2' : language.state prob_lang, R σ2 σ2' → refRcoupl (exec (S n) (e1, σ2)) (lim_exec (e1', σ2')) Φ) ->
  refRcoupl (exec (S n) (e1, σ1)) (lim_exec (e1', σ1')) Φ.
Proof.
  rewrite {1}/erasable.
  intros Hcoupl Hμ1 Hμ2 Hcont.
  rewrite -Hμ1.
  erewrite <-erasable_lim_exec; last exact Hμ2.
  eapply refRcoupl_dbind; try done.
  by apply Rcoupl_refRcoupl.
Qed.

Lemma ARcoupl_erasure_erasable (e1 e1' : expr) ε ε1 ε2 σ1 σ1' μ1 μ2 R Φ n :
  0 <= ε1 ->
  0 <= ε2 ->
  ε1 + ε2 <= ε ->
  ARcoupl (μ1) (μ2) R ε1->
  erasable μ1 σ1->
  erasable μ2 σ1'->
  (∀ σ2 σ2' : language.state prob_lang, R σ2 σ2' → ARcoupl (exec (S n) (e1, σ2)) (lim_exec (e1', σ2')) Φ ε2) ->
  ARcoupl (exec (S n) (e1, σ1)) (lim_exec (e1', σ1')) Φ ε.
Proof.
  rewrite {1}/erasable.
  intros H1 H2 Hineq Hcoupl Hμ1 Hμ2 Hcont.
  rewrite -Hμ1.
  erewrite <-erasable_lim_exec; last exact.
  eapply ARcoupl_mon_grading; first exact.
  eapply ARcoupl_dbind; try done.
Qed.


Lemma ARcoupl_erasure_erasable_adv_RHS (e1 e1' : expr) ε ε1 ε2 σ1 σ1' μ1 μ2 (E2 : _ -> R) R Φ n :
  0 <= ε1 ->
  0 <= ε2 ->
  ε1 + ε2 <= ε ->
  ARcoupl (μ1) (μ2) R ε1 ->
  SeriesC (λ b, μ2 b * E2 b) = ε2 -> 
  erasable μ1 σ1->
  erasable μ2 σ1'->
  (∀ σ2 σ2' : language.state prob_lang, R σ2 σ2' → ARcoupl (exec (S n) (e1, σ2)) (lim_exec (e1', σ2')) Φ (E2 σ2')) ->
  ARcoupl (exec (S n) (e1, σ1)) (lim_exec (e1', σ1')) Φ ε.
Proof.
  rewrite {1}/erasable.
  intros H1 H2 Hineq Hcoupl Hsum Hμ1 Hμ2 Hcont.
  rewrite -Hμ1.
  erewrite <-erasable_lim_exec; last exact.
  eapply ARcoupl_mon_grading; first exact.
  eapply (ARcoupl_dbind_adv_rhs _ _ _ _ _ _ _ _ E2); try done.
Admitted.
(*   rewrite {1}/erasable. *)
(*   intros Hcoupl Hμ1 Hμ2 Hcont. *)
(*   rewrite -Hμ1. *)
(*   erewrite <-erasable_lim_exec; last exact Hμ2. *)
(*   eapply refRcoupl_dbind; try done. *)
(*   by apply Rcoupl_refRcoupl. *)
(* Qed. *)
