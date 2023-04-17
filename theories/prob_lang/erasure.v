From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Import fin_maps fin_map_dom.
From self.prelude Require Import stdpp_ext.
From self.program_logic Require Export exec.
From self.prob_lang Require Import notation lang metatheory.
From self.prob Require Export couplings distribution.

Set Default Proof Using "Type*".
Local Open Scope R.

Section erasure_helpers.

  Variable (m : nat).
  Hypothesis IH :
    ∀ (e1 : expr) (σ1 : state) α (n : nat) zs,
    tapes σ1 !! α = Some (n, zs) →
    Rcoupl (exec_val m (e1, σ1))
      (dunif n ≫= (λ z, exec_val m (e1, state_upd_tapes <[α:= (n, zs ++ [z])]> σ1))) eq.

  Local Lemma ind_case_det e σ α n zs K :
    tapes σ !! α = Some (n, zs) →
    is_det_head_step e σ = true →
    Rcoupl
      (dmap (fill_lift K) (head_step e σ) ≫= exec_val m)
      (dunif n ≫= (λ z : nat, dmap (fill_lift K)
                                   (head_step e (state_upd_tapes <[α:= (n, zs ++ [z]) ]> σ)) ≫= exec_val m))
       eq.
  Proof using m IH.
    intros Hα (e2 & (σ2 & Hdet))%is_det_head_step_true%det_step_pred_ex_rel.
    erewrite 1!det_head_step_singleton; [|done..].
    setoid_rewrite (det_head_step_singleton ); eauto; last first.
    - eapply det_head_step_upd_tapes; eauto.
    - erewrite det_step_eq_tapes in Hα; [|done].
      rewrite !dmap_dret.
      setoid_rewrite (dmap_dret (fill_lift K)).
      rewrite !dret_id_left.
      setoid_rewrite (dret_id_left (exec_val m)).
      eapply IH; eauto.
  Qed.

  Local Lemma ind_case_dzero e σ α n zs K :
    tapes σ !! α = Some (n, zs) →
    is_det_head_step e σ = false →
    ¬ det_head_step_pred e σ →
    (∀ σ', σ.(heap) = σ'.(heap) → head_step e σ' = dzero) →
    Rcoupl
      (dmap (fill_lift K) (head_step e σ) ≫= exec_val m)
      (dunif n ≫= (λ z,
         dmap (fill_lift K) (head_step e (state_upd_tapes <[α:=(n, zs ++ [z])]> σ)) ≫= exec_val m)) eq.
  Proof using m IH.
    intros Hα Hdet Hndet HZ.
    rewrite !HZ //.
    rewrite dmap_dzero dbind_dzero.
    setoid_rewrite HZ; [|done].
    rewrite dmap_dzero dbind_dzero dzero_dbind.
    apply Rcoupl_dzero_dzero.
  Qed.


  Local Lemma ind_case_alloc σ α n zs n0 K :
    tapes σ !! α = Some (n, zs) →
    prob_head_step_pred (alloc n0) σ →
    ¬ det_head_step_pred (alloc n0) σ →
    is_det_head_step (alloc n0) σ = false →
    Rcoupl
      (dmap (fill_lift K) (head_step (alloc n0) σ) ≫= exec_val m)
      (dunif n ≫=
         (λ z : nat, dmap (fill_lift K) (head_step (alloc n0) (state_upd_tapes <[α:= (n, zs ++ [z])]> σ)) ≫= exec_val m))
      eq.
  Proof using m IH.
    intros Hα HP Hndet Hdet.
    inversion HP; simplify_eq.
    rewrite dmap_dret dret_id_left -/exec_val.
    setoid_rewrite (dmap_dret (fill_lift K)).
    setoid_rewrite (dret_id_left (exec_val m)).
    (* TODO: fix slightly ugly hack :P *)
    revert IH; intro IHm.
    apply lookup_total_correct in Hα as Hαtot.
    pose proof (elem_fresh_ne _ _ _ Hα) as Hne.
    assert (α ≠ fresh_loc (tapes σ)) as Hne' by auto ; clear Hne.
    (* TODO: slow *)
    setoid_rewrite <- fresh_loc_upd_some; eauto.
    erewrite dbind_ext_right; last first.
    { intros. rewrite (fresh_loc_upd_swap σ α (n, zs) (_, [])) //. }
    apply IHm.
    by apply fresh_loc_lookup.
  Qed.

  Local Lemma ind_case_flip_some σ α α' K z n zs n' zs' :
    tapes σ !! α = Some (n, zs) →
    tapes σ !! α' = Some (n', z :: zs') →
    Rcoupl
      (dmap (fill_lift K) (head_step (rand #lbl:α') σ) ≫= exec_val m)
      (dunif n ≫=
         (λ z, dmap (fill_lift K) (head_step (rand #lbl:α') (state_upd_tapes <[α:= (n, zs ++ [z])]> σ)) ≫= exec_val m))
      eq.
  Proof using m IH.
    intros Hα Hα'.
    apply lookup_total_correct in Hα as Hαtot.
    apply lookup_total_correct in Hα' as Hα'tot.
    destruct (decide (α = α')) as [-> | Hαneql].
    - simplify_eq. rewrite /head_step Hα.
      setoid_rewrite lookup_insert.
      rewrite dmap_dret dret_id_left -/exec_val.
      specialize (IH (fill K #z) (state_upd_tapes <[α':=(n, zs')]> σ) α' n zs').
      erewrite dbind_ext_right; last first.
      { intros.
        rewrite -app_comm_cons.
        rewrite upd_tape_twice dmap_dret dret_id_left -/exec_val //. }


      assert (∀ z0,
                 state_upd_tapes <[α':=(n, zs' ++ [z0])]> σ =
                   state_upd_tapes <[α':=(n, zs' ++ [z0])]> (state_upd_tapes <[α':=(n, zs')]> σ)) as Haux.
      { intro z0. rewrite /state_upd_tapes. f_equal. rewrite insert_insert //. }
      erewrite dbind_ext_right; [| intro; rewrite Haux; done].
      apply IH.
      apply lookup_insert.
    - rewrite /head_step.
      rewrite Hα'.
      rewrite !dmap_dret !dret_id_left -/exec_val.
      assert (tapes (state_upd_tapes <[α':=(n', zs')]> σ) !! α = Some (n, zs)) as Hα''.
      { rewrite lookup_insert_ne //. }
      pose proof (IH (fill K #z) (state_upd_tapes <[α':=(n', zs')]> σ) α n zs Hα'') as IHm2.
      erewrite dbind_ext_right; last first.
      { intro.
        rewrite {1}/state_upd_tapes.
        rewrite lookup_insert_ne ?Hα'; [|done].
        rewrite upd_diff_tape_comm; [|done].
        rewrite dmap_dret dret_id_left -/exec_val. done. }
      apply IHm2.
  Qed.

  Local Lemma ind_case_flip_empty σ α α' K n n' zs :
    tapes σ !! α = Some (n, zs) →
    (tapes σ !! α' = Some (n', [])) →
    Rcoupl
      (dmap (fill_lift K) (head_step (rand #lbl:α') σ) ≫= exec_val m)
      (dunif n ≫=
         (λ z, dmap (fill_lift K) (head_step (rand #lbl:α') (state_upd_tapes <[α := (n, zs ++ [z])]> σ)) ≫= exec_val m))
      eq.
  Proof using m IH.
    intros Hα Hα'.
    destruct (decide (α = α')) as [-> | Hαneql].
    + simplify_eq.
      rewrite /head_step Hα.
      rewrite {1 2}/dmap.
      rewrite -!dbind_assoc -/exec_val.
      eapply (Rcoupl_dbind _ _ _ _ (=)); [ | apply Rcoupl_eq].
      intros ? b ->.
      do 2 rewrite dret_id_left /=.
      rewrite lookup_insert.
      rewrite dmap_dret dret_id_left -/exec_val.
      rewrite insert_insert.
      rewrite insert_id; auto.
      destruct σ; simpl.
      apply Rcoupl_eq.
    + rewrite /head_step /=.
      setoid_rewrite lookup_insert_ne; [|done].
      rewrite Hα'.
      rewrite {1 2}/dmap.
      erewrite (dbind_ext_right (dunif n)); last first.
      { intro.
        rewrite {1 2}/dmap.
        do 2 rewrite -dbind_assoc -/exec_val.
        done. }
      rewrite -!dbind_assoc -/exec_val.
      rewrite dbind_comm.
      eapply Rcoupl_dbind; [|apply Rcoupl_eq].
      intros; simplify_eq.
      do 2 rewrite dret_id_left /=.
      erewrite dbind_ext_right; last first.
      { intro; do 2 rewrite dret_id_left. done. }
      by apply IH.
  Qed.

  Local Lemma ind_case_flip_none σ α α' K n zs :
    tapes σ !! α = Some (n, zs) →
    tapes σ !! α' = None →
    Rcoupl
      (dmap (fill_lift K) (head_step (rand #lbl:α') σ) ≫= exec_val m)
      (dunif n ≫=
         (λ z, dmap (fill_lift K) (head_step (rand #lbl:α') (state_upd_tapes <[α := (n, zs ++ [z])]> σ)) ≫= exec_val m))
      eq.
  Proof using m IH.
    intros Hα Hα'.
    destruct (decide (α = α')) as [-> | Hαneql]; [simplify_map_eq|].
    rewrite /head_step /=.
    setoid_rewrite lookup_insert_ne; [|done].
    rewrite Hα'.
    rewrite -!dbind_assoc.
    erewrite (dbind_ext_right (dunif n)); last first.
    { intro.
      rewrite /dmap.
      do 2 rewrite -dbind_assoc.
      auto. }
    rewrite dbind_comm.
    eapply Rcoupl_dbind; [|apply Rcoupl_eq].
    intros; simplify_eq.
    destruct b; simpl; rewrite dret_id_left.
    - simpl.
      rewrite dret_id_left.
      erewrite (dbind_ext_right (dunif n)); last first.
      { intros.
        do 2 rewrite dret_id_left.
        simpl; auto.
       }
       apply IH; auto.
    - simpl.
      rewrite dret_id_left.
      erewrite (dbind_ext_right (dunif n)); last first.
      { intros.
        do 2 rewrite dret_id_left.
        simpl; auto.
       }
       apply IH; auto.
  Qed.

  Local Lemma ind_case_flip_int σ α (z:Z) K n zs :
    tapes σ !! α = Some (n, zs) →
    Rcoupl
      (dmap (fill_lift K) (head_step (rand #z) σ) ≫= exec_val m)
      (dunif n ≫=
         (λ x : nat, dmap (fill_lift K) (head_step (rand #z) (state_upd_tapes <[α := (n, zs ++ [x])]> σ)) ≫= exec_val m))
      eq.
  Proof using m IH.
    intros Hα.
    rewrite /head_step.
    rewrite {1 2}/dmap.
    erewrite (dbind_ext_right (dunif n)); last first.
      { intro.
        rewrite {1 2}/dmap.
        do 2 rewrite -dbind_assoc.
        auto.
      }
      rewrite -!dbind_assoc.
      rewrite -/exec_val.
      rewrite dbind_comm.
      eapply Rcoupl_dbind; [|apply Rcoupl_eq].
      intros; simplify_eq.
      do 2 rewrite dret_id_left.
      erewrite dbind_ext_right; last first.
      { intro; do 2 rewrite dret_id_left; auto. }
      apply IH; auto.
  Qed.

End erasure_helpers.

Lemma prim_coupl_upd_tapes_dom m e1 σ1 α n zs :
  σ1.(tapes) !! α = Some (n, zs) →
  Rcoupl
    (exec_val m (e1, σ1))
    (dbind (λ z, (exec_val m (e1, (state_upd_tapes <[α := (n, zs ++ [z])]> σ1)))) (dunif n))
    eq.
Proof.
  revert e1 σ1 α n zs; induction m; intros e1 σ1 α n zs Hα.
  - rewrite /exec_val/=.
    destruct (to_val e1) eqn:He1.
    + rewrite (dret_const (dunif n) v); [apply Rcoupl_eq | apply dunif_mass].
    + exists dzero. repeat split_and!.
      * apply lmarg_dzero.
      * rewrite dzero_dbind. apply rmarg_dzero.
      * intros. inv_distr.
  - simpl. destruct (to_val e1) eqn:He1.
    + specialize (IHm e1 σ1 α n zs Hα).
      destruct m; simpl in *; by rewrite He1 in IHm.
    + rewrite /prim_step /=.
      destruct (decomp e1) as [K ered] eqn:decomp_e1.
      rewrite decomp_e1.
      destruct (is_det_head_step ered σ1) eqn:Hdet.
      * by eapply ind_case_det.
      * assert (¬ det_head_step_pred ered σ1) as Hndet.
        { intros ?%is_det_head_step_true. rewrite H // in Hdet. }
        destruct (det_or_prob_or_dzero ered σ1) as [ HD | [HP | HZ]].
        { by destruct Hndet. }
        { inversion HP; simplify_eq.
          - by eapply ind_case_alloc.
          - by eapply ind_case_flip_some.
          - destruct H; [by eapply ind_case_flip_empty | by eapply ind_case_flip_none].
          - by eapply ind_case_flip_int. }
        { by eapply ind_case_dzero. }
Qed.

Lemma prim_coupl_step_prim m e1 σ1 α bs :
  σ1.(tapes) !! α = Some bs →
  Rcoupl
    (exec_val m (e1, σ1))
    (state_step σ1 α ≫= (λ σ2, exec_val m (e1, σ2)))
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

Lemma limprim_coupl_step_limprim_aux e1 σ1 α bs v:
  σ1.(tapes) !! α = Some bs →
  (lim_exec_val (e1, σ1)) v =
  (state_step σ1 α ≫= (λ σ2, lim_exec_val (e1, σ2))) v.
Proof.
  intro Hsome.
   rewrite lim_exec_val_rw/=.
   rewrite {2}/pmf/=/dbind_pmf.
   setoid_rewrite lim_exec_val_rw.
   simpl in *.
   assert
     (SeriesC (λ a: state, state_step σ1 α a * Sup_seq (λ n : nat, exec_val n (e1, a) v)) =
     SeriesC (λ a: state, Sup_seq (λ n : nat, state_step σ1 α a * exec_val n (e1, a) v))) as Haux.
   { apply SeriesC_ext; intro v'.
     apply eq_rbar_finite.
     rewrite rmult_finite.
     rewrite (rbar_finite_real_eq (Sup_seq (λ n : nat, exec_val n (e1, v') v))); auto.
     - rewrite <- (Sup_seq_scal_l (state_step σ1 α v') (λ n : nat, exec_val n (e1, v') v)); auto.
     - apply (Rbar_le_sandwich 0 1).
       + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
       + apply upper_bound_ge_sup; intro; simpl; auto.
   }
   rewrite Haux.
   rewrite (MCT_seriesC _ (λ n, exec_val n (e1,σ1) v) (lim_exec_val (e1,σ1) v)); auto.
   - intros; apply Rmult_le_pos; auto.
   - intros.
     apply Rmult_le_compat; auto; [apply Rle_refl | apply exec_val_mon]; auto.
   - intro.
     exists (state_step σ1 α a); intro.
     rewrite <- Rmult_1_r.
     apply Rmult_le_compat_l; auto.
   - intro n.
     rewrite (Rcoupl_eq_elim _ _ (prim_coupl_step_prim n e1 σ1 α bs Hsome)); auto.
     rewrite {3}/pmf/=/dbind_pmf.
     apply SeriesC_correct; auto.
     apply (ex_seriesC_le _ (state_step σ1 α)); auto.
     intro; split; auto.
     + apply Rmult_le_pos; auto.
     + rewrite <- Rmult_1_r.
       apply Rmult_le_compat_l; auto.
   - rewrite lim_exec_val_rw.
     rewrite rbar_finite_real_eq; [ apply Sup_seq_correct | ].
     rewrite mon_sup_succ.
     + apply (Rbar_le_sandwich 0 1); auto.
       * apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
       * apply upper_bound_ge_sup; intro; simpl; auto.
     + intro; apply exec_val_mon.
Qed.

Lemma limprim_coupl_step_limprim e1 σ1 α bs :
  σ1.(tapes) !! α = Some bs →
  Rcoupl
    (lim_exec_val (e1, σ1))
    (state_step σ1 α ≫= (λ σ2, lim_exec_val (e1, σ2)))
    eq.
Proof.
  intro Hsome.
  erewrite (distr_ext (lim_exec_val (e1, σ1))); last first.
  - intro a.
    apply (limprim_coupl_step_limprim_aux _ _ _ _ _ Hsome).
  - apply Rcoupl_eq.
Qed.

Lemma refRcoupl_erasure e1 σ1 e1' σ1' α α' R Φ m bs bs':
  σ1.(tapes) !! α = Some bs →
  σ1'.(tapes) !! α' = Some bs' →
  Rcoupl (state_step σ1 α) (state_step σ1' α') R →
  (∀ σ2 σ2', R σ2 σ2' →
             refRcoupl (exec_val m (e1, σ2))
               (lim_exec_val (e1', σ2')) Φ ) →
  refRcoupl (exec_val m (e1, σ1))
    (lim_exec_val (e1', σ1')) Φ.
Proof.
  intros Hα Hα' HR Hcont.
  eapply refRcoupl_eq_refRcoupl_unfoldl ;
    [eapply prim_coupl_step_prim; eauto |].
  eapply refRcoupl_eq_refRcoupl_unfoldr;
    [| eapply Rcoupl_eq_sym, limprim_coupl_step_limprim; eauto].
  apply (refRcoupl_dbind _ _ _ _ R); auto.
  by eapply Rcoupl_refRcoupl.
Qed.

Lemma refRcoupl_erasure_r (e1 : expr) σ1 e1' σ1' α' R Φ m bs':
  to_val e1 = None →
  σ1'.(tapes) !! α' = Some bs' →
  Rcoupl (prim_step e1 σ1) (state_step σ1' α') R →
  (∀ e2 σ2 σ2', R (e2, σ2) σ2' → refRcoupl (exec_val m (e2, σ2)) (lim_exec_val (e1', σ2')) Φ ) →
  refRcoupl (exec_val (S m) (e1, σ1)) (lim_exec_val (e1', σ1')) Φ.
Proof.
  intros He1 Hα' HR Hcont.
  rewrite exec_val_Sn_not_val //.
  eapply (refRcoupl_eq_refRcoupl_unfoldr _ (state_step σ1' α' ≫= (λ σ2', lim_exec_val (e1', σ2')))).
  - eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl].
    intros [] ??. by apply Hcont.
  - apply Rcoupl_eq_sym. by eapply limprim_coupl_step_limprim.
Qed.

Lemma refRcoupl_erasure_l (e1 e1' : expr) σ1 σ1' α R Φ m bs :
  σ1.(tapes) !! α = Some bs →
  Rcoupl (state_step σ1 α) (prim_step e1' σ1') R →
  (∀ σ2 e2' σ2', R σ2 (e2', σ2') → refRcoupl (exec_val m (e1, σ2)) (lim_exec_val (e2', σ2')) Φ ) →
  refRcoupl (exec_val m (e1, σ1)) (lim_exec_val (e1', σ1')) Φ.
Proof.
  intros Hα HR Hcont.
  assert (to_val e1' = None).
  { apply Rcoupl_pos_R, Rcoupl_inhabited_l in HR as (?&?&?&?&?); [eauto using val_stuck|].
    rewrite state_step_mass; [lra|]. apply elem_of_dom. eauto. }
  eapply (refRcoupl_eq_refRcoupl_unfoldl _ (state_step σ1 α ≫= (λ σ2, exec_val m (e1, σ2)))).
  - by eapply prim_coupl_step_prim.
  - rewrite lim_exec_val_prim_step.
    rewrite prim_step_or_val_no_val //.
    eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl].
    intros ? [] ?. by apply Hcont.
Qed.
