From stdpp Require Import prelude coPset namespaces.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list.
From clutch.common Require Import language ectx_language ectxi_language locations.
From clutch.prelude Require Import fin.
From clutch.prob_lang Require Import notation lang.
From clutch.prob_lang.spec Require Import spec_ra spec_rules spec_tactics.
From clutch.approxis Require Import ectx_lifting app_weakestpre model.
From clutch.approxis Require Export proofmode primitive_laws coupling_rules app_rel_rules.
From clutch.base_logic Require Export spec_update.
From Coq.Logic Require Import ClassicalEpsilon.
From clutch.pure_complete Require Import pure term prob_additional samples_one.

Local Open Scope R.

Definition det_exec_result n (ρ : cfg) :=
  match decide (is_det (exec n ρ)) with
  | left P => proj1_sig (constructive_indefinite_description _ P)
  | right _ => #()
end.

Lemma det_exec_result_correct n ρ v : 
  (exec n ρ) = dret v ->
  det_exec_result n ρ = v.
Proof.
  intros.
  unfold det_exec_result.
  case_decide.
  2 : { exfalso. apply H0. by econstructor. }
  epose proof (proj2_sig (constructive_indefinite_description _ H0)).
  simpl in H1. 
  rewrite H1 in H.
  by apply dret_ext_inv.
Qed.

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

Lemma stepN_pos_step_pos {δ : markov} (x : mstate δ) n :
  SeriesC (stepN (S n) x) > 0 ->
  ∃ y, step x y > 0.
Proof.
  intros.
  destruct (ExcludedMiddle (∃ y, step x y > 0)); auto.
  pose proof (not_exists_forall_not _ _ H0).
  assert (SeriesC (stepN (S n) x) = 0). 
  2 : { rewrite H2 in H. lra. } 
  simpl in *. 
  apply SeriesC_0. 
  intros. rewrite stepN_Sn.
  replace (step x) with (dzero : distr (mstate δ)). 
  { by rewrite dbind_dzero_pmf.  }
  erewrite dzero_ext; auto. 
  intros. 
  apply Rle_antisym; auto.
  specialize (H1 a). 
  lra. 
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

Lemma lim_exec_mass_lim {δ : markov} (x : mstate δ) ɛ :
  0 < ɛ ->
  ∃ n, SeriesC (lim_exec x) - SeriesC (exec n x) < ɛ.
Proof.
  intros.
  rewrite lim_exec_Sup_seq. 
  pose proof (Lim_seq.Sup_seq_correct (λ n0 : nat, Rbar.Finite (SeriesC (exec n0 x)))). 
  unfold Lim_seq.is_sup_seq in *.
  pose proof (is_finite_Sup_seq_SeriesC_exec x). 
  rewrite -H1 in H0. 
  specialize H0 with (mkposreal ɛ H).
  destruct H0 as [? [n ?]].
  exists n.
  simpl in *. 
  lra. 
Qed.

Lemma lim_exec_approx_coupl {δ1 δ2 : markov} (x : mstate δ1) (y : mstate δ2) ɛ R :
  0 <= ɛ ->
  ARcoupl (lim_exec x) (lim_exec y) R ɛ ->
  ∀ ɛ', ɛ < ɛ' ->
    ∃ m, ∀ n, ARcoupl (exec n x) (exec m y) R ɛ'.
Proof.
  unfold ARcoupl.
  intros.
  destruct (lim_exec_mass_lim y (ɛ' - ɛ)) as [m Hm].
  { real_solver. }
  exists m.
  intros.
  apply H0 in H4; auto. 
  etrans. {
    eapply SeriesC_le.
    - intros. split. { real_solver. }
      eapply (Rmult_le_compat_r _ _ (lim_exec x n0)). { real_solver. }
      rewrite lim_exec_unfold.
      apply rbar_le_finite. { apply is_finite_Sup_seq_exec. } 
      eapply Lim_seq.Sup_seq_minor_le. reflexivity. 
    - by apply ex_expval_unit.
  }
  etrans. { apply H4. }
  trans (SeriesC (λ b : mstate_ret δ2, exec m y b * g b) + (SeriesC (lim_exec y) - SeriesC (exec m y)) + ɛ). 
  2 : { real_solver. }
  apply Rplus_le_compat_r. 
  rewrite Rplus_minus_assoc Rplus_minus_swap. 
  apply (Rplus_le_reg_r (-SeriesC (lim_exec y))), Ropp_le_cancel. 
  ring_simplify. 
  rewrite Rplus_comm -Rminus_def. 
  do 2 (rewrite -SeriesC_minus; auto; try by apply ex_expval_unit). 
  apply SeriesC_le.
  2 :{
    eapply ex_seriesC_ext.
    { intros. by rewrite Rminus_def. } 
    apply ex_seriesC_plus; auto. 
    apply (ex_seriesC_ext (λ x0 : mstate_ret δ2, (-1) * (lim_exec y x0 * g x0))).
    { intros. by real_solver. } 
    by apply ex_seriesC_scal_l, ex_expval_unit. 
  }
  intros.
  split. 
  - apply -> Rcomplements.Rminus_le_0. real_solver. 
  - rewrite -(Rmult_1_r (exec m y n0)) -(Rmult_1_r (lim_exec y n0)). 
    rewrite !Rmult_assoc -!Rmult_minus_distr_l Rmult_1_l. 
    apply Rmult_le_compat_r.
    { apply Rle_0_le_minus. real_solver. }
    rewrite lim_exec_unfold.
    apply rbar_le_finite. { apply is_finite_Sup_seq_exec. } 
    eapply Lim_seq.Sup_seq_minor_le. reflexivity. 
Qed.

Definition skip_one (e : expr) := (λ: <>, e)%V #().

Lemma skip_one_after e σ: step (skip_one e, σ) = dret (e, σ).
Proof.
  simpl.
  rewrite /skip_one /prim_step.
  simpl.
  rewrite decomp_unfold.
  simpl. by rewrite dmap_dret.
Qed.

Section Presample.

Lemma presamples_stepN_det_part l σ n t e:
  σ.(tapes) !! l = Some (2%nat; t) ->
  (n <= length t)%nat ->
  SamplesOneTape l e -> 
  stepN n (e, σ) = dzero ∨ is_det (stepN n (e, σ)).
Proof.
  revert σ e t.
  induction n.
  {
    intros.
    rewrite stepN_O. right.
    by econstructor. 
  }
  intros.
  destruct t; simpl in H0; try lia.
  rewrite stepN_Sn. 
  destruct (ExcludedMiddle (∃ ρ', step (e,σ) ρ' > 0)).
  2 : {
    pose proof (not_exists_forall_not _ _ H2) as H2'.
    assert (step (e, σ) = dzero). {
      apply dzero_ext.
      intros.
      apply Rle_antisym; try real_solver.
      specialize (H2' a).
      simpl in *.
      real_solver.
    }
    rewrite H3.
    left.
    apply dbind_dzero.
  }
  destruct H2 as [[e' σ'] Hst]. 
  pose proof H as H'.
  eapply SamplesOneTape_inv in Hst as He'; eauto.
  erewrite SamplesOneTape_step_det'; eauto.  
  rewrite dret_id_left'. 
  epose proof (SamplesOneTape_step_tapes _ _ _ _ _ _ _ H1 H Hst) as [Ht | Ht]. 
  - eapply IHn; eauto. 
    { by rewrite Ht. }
    simpl. lia.
  - eapply IHn; eauto. 
    { rewrite Ht. by apply lookup_insert. }
    lia.
Qed. 

Lemma presamples_pexec_det_part l σ n t e:
  σ.(tapes) !! l = Some (2%nat; t) ->
  (n <= length t)%nat ->
  SamplesOneTape l e -> 
  pexec n (e, σ) = dzero ∨ is_det (pexec n (e, σ)).
Proof.
  revert σ e t.
  induction n.
  {
    intros.
    rewrite pexec_O. right.
    by econstructor. 
  }
  intros.
  destruct t; simpl in H0; try lia.
  rewrite pexec_Sn.
  destruct (decide (is_final (e, σ))).
  {
    rewrite step_or_final_is_final; auto.
    rewrite dret_id_left'. 
    eapply IHn; eauto.
    simpl. lia.
  }
  rewrite step_or_final_no_final; auto.
  destruct (ExcludedMiddle (∃ ρ', step (e,σ) ρ' > 0)).
  2 : {
    pose proof (not_exists_forall_not _ _ H2) as H2'.
    assert (step (e, σ) = dzero). {
      apply dzero_ext.
      intros.
      apply Rle_antisym; try real_solver.
      specialize (H2' a).
      simpl in *.
      real_solver.
    }
    rewrite H3.
    left.
    apply dbind_dzero.
  }
  destruct H2 as [[e' σ'] Hst]. 
  pose proof H as H'.
  eapply SamplesOneTape_inv in Hst as He'; eauto.
  erewrite SamplesOneTape_step_det'; eauto.  
  rewrite dret_id_left'. 
  epose proof (SamplesOneTape_step_tapes _ _ _ _ _ _ _ H1 H Hst) as [Ht | Ht].  
  - eapply IHn; eauto. 
    { by rewrite Ht. }
    simpl. lia. 
  - eapply IHn; eauto. 
    { rewrite Ht. by apply lookup_insert. }
    lia.
Qed.

Lemma presamples_pexec_det_state l σ σ' n t e e':
  σ.(tapes) !! l = Some (2%nat; t) ->
  (n <= length t)%nat ->
  SamplesOneTape l e -> 
  pexec n (e, σ) = dret (e', σ') ->
  heap σ' = heap σ ∧ 
  ∃ t', tapes σ' = <[l := (2%nat; t')]>(tapes σ).
Proof.
  revert σ e e' σ' t.
  induction n; intros.
  {
    rewrite pexec_O in H2.
    apply dret_ext_inv in H2. 
    inversion H2; subst. 
    split; auto.
    exists t. by rewrite insert_id.
  } 
  destruct t as [|nv t]; simpl in H0; try lia. 
  rewrite pexec_Sn in H2. 
  destruct (decide (is_final (e, σ))).
  {
    rewrite step_or_final_is_final in H2; auto.
    rewrite dret_id_left' in H2. 
    eapply IHn; eauto. simpl. 
    lia.
  }
  rewrite step_or_final_no_final in H2; auto. 
  destruct (ExcludedMiddle (∃ ρ', step (e,σ) ρ' > 0)).
  2 : {
    pose proof (not_exists_forall_not _ _ H3) as H3'.
    assert (step (e, σ) = dzero). {
      apply dzero_ext.
      intros.
      apply Rle_antisym; try real_solver. 
      specialize (H3' a).
      simpl in *.
      real_solver.
    }  
    rewrite H4 dbind_dzero in H2. 
    by apply dzero_neq_dret in H2. 
  }
  destruct H3 as [[e1 σ1] Hst]. 
  eapply SamplesOneTape_inv in Hst as He'; eauto.
  erewrite SamplesOneTape_step_det' in H2; eauto. 
  rewrite dret_id_left' in H2. 
  eapply SamplesOneTape_step_heap in Hst as Hh; eauto.
  eapply SamplesOneTape_step_tapes in Hst as Ht; eauto.
  assert (∃ t', tapes σ1 = <[l:=(2%nat; t')]> (tapes σ) ∧ n ≤ length t' ) as [t' [Ht' Ht'l]]. {
    destruct Ht as [-> | ->].
    - exists (nv :: t). split.  
      2 : { simpl. lia. }
      symmetry. by eapply insert_id. 
    - exists t; split; auto; lia. 
  }
  eapply IHn in H2 as [H21 H22]; eauto.
  2 : { rewrite Ht'. apply lookup_insert. }
  split. 
  { by rewrite H21. }
  destruct H22.
  exists x.
  by rewrite Ht' insert_insert in H2. 
Qed. 

Lemma presamples_stepN_det l σ n t e:
  σ.(tapes) !! l = Some (2%nat; t) ->
  (n <= length t)%nat ->
  SeriesC (stepN n (e, σ)) > 0 ->
  SamplesOneTape l e -> 
  is_det (stepN n (e, σ)).
Proof.
  intros.
  epose proof (presamples_stepN_det_part _ _ _ _ _) as [? | ?]; eauto. 
  rewrite H3 dzero_mass in H1.
  lra. 
Qed.

Lemma presamples_exec_det_part l σ n t e:
  σ.(tapes) !! l = Some (2%nat; t) ->
  (n <= length t)%nat ->
  SamplesOneTape l e -> 
  (exec n (e, σ)) = dzero ∨ is_det (exec n (e, σ)).
Proof.
  intros.
  rewrite exec_pexec_relate.
  epose proof (presamples_pexec_det_part _ _  _ _ _) as [? | (? & ?)]; eauto;
  rewrite H2. 
  - left. by rewrite dbind_dzero.  
  - rewrite dret_id_left'. 
    destruct (to_final x).
    + right. by econstructor.
    + by left. 
Qed.

Lemma presamples_exec_det l σ n t e:
  σ.(tapes) !! l = Some (2%nat; t) ->
  (n <= length t)%nat ->
  SeriesC (exec n (e, σ)) > 0 ->
  SamplesOneTape l e -> 
  is_det (exec n (e, σ)).
Proof.
  intros.
  epose proof (presamples_exec_det_part _ _ _ _ _) as [? | ?]; eauto.
  rewrite H3 dzero_mass in H1.
  lra. 
Qed.

Lemma presamples_exec_det_pexec l σ n t e v:
  σ.(tapes) !! l = Some (2%nat; t) ->
  (n <= length t)%nat ->
  SamplesOneTape l e -> 
  exec n (e, σ) = dret v ->
  ∃ σ', pexec n (e, σ) = dret (Val v, σ').
Proof.
  intros ??? H3. 
  rewrite exec_pexec_relate in H3. 
  epose proof (presamples_pexec_det_part _ _ _ _ _) as [? | [[e' σ'] ?]]; eauto.
  - rewrite H2 dbind_dzero in H3. 
    by apply dzero_neq_dret in H3.
  - rewrite H2 dret_id_left' in H3. 
    simpl in *. destruct (to_val e') eqn : Hve'. 
    2 : { by apply dzero_neq_dret in H3. }
    apply dret_ext_inv in H3; subst.
    apply of_to_val in Hve'; subst. 
    by econstructor.  
Qed. 

Lemma presamples_pexec_var l e e' σ1 σ2 n t σ'1:
  σ1.(tapes) !! l = Some (2%nat; t) -> 
  σ2.(tapes) !! l = Some (2%nat; t) ->
  (n <= length t)%nat ->
  SamplesOneTape l e ->
  pexec n (e, σ1) = dret (e', σ'1) ->
  ∃ σ'2, pexec n (e, σ2) = dret (e', σ'2).
Proof.
  revert e e' σ1 σ2 t σ'1.
  induction n.
  {
    intros. 
    exists σ2. 
    rewrite pexec_O in H3. 
    rewrite pexec_O. 
    apply dret_ext_inv in H3.
    inversion H3; by subst. 
  }
  intros.
  destruct t as [|nv t]; simpl in H1; try lia. 
  rewrite pexec_Sn in H3. rewrite pexec_Sn. 
  destruct (decide (is_final (e, σ1))).
  {
    rewrite step_or_final_is_final in H3; auto.
    rewrite dret_id_left' in H3. 
    rewrite step_or_final_is_final; auto.
    rewrite dret_id_left'. eapply IHn. 
    5 : apply H3. 
    - eauto.
    - eauto.
    - simpl. lia. 
    - eauto.
  }
  rewrite step_or_final_no_final; auto.
  rewrite step_or_final_no_final in H3; auto. 
  destruct (ExcludedMiddle (∃ ρ', step (e, σ1) ρ' > 0)).
  2 : {
    pose proof (not_exists_forall_not _ _ H4) as H4'.
    assert (step (e, σ1) = dzero). {
      apply dzero_ext.
      intros.
      apply Rle_antisym; try real_solver. 
      specialize (H4' a).
      simpl in *.
      real_solver.
    }  
    rewrite H5 dbind_dzero in H3. 
    by apply dzero_neq_dret in H3. 
  }
  destruct H4 as [[e''1 σ''1] Hst].
  eapply SamplesOneTape_inv in Hst as He'; eauto.
  erewrite SamplesOneTape_step_det' in H3; eauto. 
  rewrite dret_id_left' in H3.
  pose proof Hst as Hst''.
  eapply SamplesOneTape_step_pos_var in Hst as [σ'2 Hst']; eauto.
  eapply SamplesOneTape_step_state_var in Hst'' as Ht; eauto. 
  eapply SamplesOneTape_step_det in Hst'; eauto.
  apply pmf_1_eq_dret in Hst'.
  rewrite Hst'.
  rewrite dret_id_left'. 
  eapply SamplesOneTape_step_tapes in Hst'' as Ht'; eauto.
  assert (∃ t', tapes σ''1 = <[l:=(2%nat; t')]> (tapes σ1) ∧ n ≤ length t' ) as [t' [Ht'' Ht''l]]. {
    destruct Ht' as [-> | ->].
    - exists (nv :: t). split.  
      2 : { simpl. lia. }
      symmetry. by eapply insert_id. 
    - exists t; split; auto; lia. 
  }
  eapply IHn.
  - erewrite Ht''. eapply lookup_insert. 
  - simpl. rewrite Ht Ht''. eapply lookup_insert.  
  - auto.
  - apply He'. 
  - apply H3.
Qed.

Definition state_stepN σ l n := iterM n (λ σ', state_step σ' l) σ.

Lemma state_stepN_tape σ l n σ' t : 
  σ.(tapes) !! l = Some (2%nat; t) ->
  (state_stepN σ l n) σ' > 0 ->
  ∃ t', 
    length t' = n ∧
    σ'.(tapes) = <[l := (2%nat; t ++ t')]>σ.(tapes).
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

Lemma state_stepN_heap σ l n σ' t : 
  σ.(tapes) !! l = Some (2%nat; t) ->
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
    epose proof (state_stepN_tape _ _ 1 _ _ H _). 
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

Lemma SamplesOneTape_state_stepN_exec_det_part l σ σ' n t e:
  σ.(tapes) !! l = Some (2%nat; t) ->
  SamplesOneTape l e -> 
  (state_stepN σ l n) σ' > 0 ->
  exec n (e, σ') = dzero ∨ is_det (exec n (e, σ')).
Proof.
  intros.
  apply (state_stepN_heap _ _ _ _ _ H) in H1 as Hh.
  pose proof (state_stepN_tape _ _ _ _ _ H H1) as [t' [Ht Hst]].
  eapply presamples_exec_det_part; eauto.
  - rewrite Hst. apply lookup_insert. 
  - rewrite app_length Ht. lia.
Qed.

Lemma SamplesOneTape_state_stepN_exec_det l σ σ' n t e:
  σ.(tapes) !! l = Some (2%nat; t) ->
  SamplesOneTape l e -> 
  (state_stepN σ l n) σ' > 0 ->
  SeriesC (exec n (e, σ')) > 0 ->
  is_det (exec n (e, σ')).
Proof.
  intros.
  epose proof (SamplesOneTape_state_stepN_exec_det_part _  _ _ _ _ _) as [? | ?]; eauto.
  rewrite H3 dzero_mass in H2. lra.
Qed.

Lemma SamplesOneTape_exec_decompose l σ n t e:
  σ.(tapes) !! l = Some (2%nat; t) ->
  SamplesOneTape l e -> 
  exec n (e, σ) = 
    dmap (fun σ' => det_exec_result n (e, σ')) 
    (ssdp (fun σ' => is_det (exec n (e, σ'))) (state_stepN σ l n)).
Proof.
  intros.
  apply distr_ext.
  intros v.
  rewrite -dmap_fold.
  rewrite dbind_unfold_pmf.
  rewrite (SeriesC_ext _ (fun a => (state_stepN σ l n) a * exec n (e, a) v)). {
    rewrite -dbind_unfold_pmf.
    f_equal. symmetry.
    by eapply erasure.iterM_state_step_erasable. 
  }
  intros σ'.
  destruct (decide (state_stepN σ l n σ' > 0)). 
  2 : {
    assert (state_stepN σ l n σ' = 0). 
    { apply Rle_antisym; real_solver. }
    rewrite H1.
    rewrite ssd_zero; auto.
    real_solver. 
  }
  unfold pmf at 1. simpl. unfold ssd_pmf.
  epose proof (SamplesOneTape_state_stepN_exec_det_part _ _ _ _ _ _) as [? | ?]; eauto. 
  - case_bool_decide. 
    2 : rewrite H1 dzero_0; real_solver.
    destruct H2. 
    rewrite H1 in H2.
    by apply dzero_neq_dret in H2.
  - case_bool_decide; try done. 
    destruct H1. 
    erewrite det_exec_result_correct; eauto.  
    by rewrite H1. 
Qed. 

Lemma SamplesOneTape_exec_state_determinize l1 l2 e1 σ1 e2 σ2 t1 t2 n m ɛ ɛ' ψ:
  σ1.(tapes) !! l1 = Some (2%nat; t1) ->
  σ2.(tapes) !! l2 = Some (2%nat; t2) ->
  SamplesOneTape l1 e1 ->
  SamplesOneTape l2 e2 ->
  0 <= ɛ ->
  ɛ' = 1 - SeriesC (exec n (e1, σ1)) ->
  ARcoupl (exec n (e1, σ1)) (exec m (e2, σ2)) ψ ɛ ->
  ARcoupl (state_stepN σ1 l1 n) (state_stepN σ2 l2 m) 
    (λ σ'1 σ'2, ∃ v1 v2, ψ v1 v2 ∧ exec n (e1, σ'1) = dret v1 ∧ exec m (e2, σ'2) = dret v2) 
    (ɛ + ɛ').
Proof.
  intros ???? He He' ?.
  eapply (ARcoupl_mono _ _ _ _ (λ σ'1 σ'2 : state, ψ (det_exec_result n (e1, σ'1)) (det_exec_result m (e2, σ'2)) ∧ is_det (exec n (e1, σ'1)) ∧ is_det (exec m (e2, σ'2))));
  intros; try reflexivity. 
  {
    destruct H4 as (Hres & [v1 Hv1] & [v2 Hv2]).
    erewrite !det_exec_result_correct in Hres; eauto.
  }
  assert (ɛ' = probp (state_stepN σ1 l1 n) (λ a, ¬ is_det (exec n (e1, a)))). {
    rewrite He'.
    rewrite /probp. 
    erewrite SamplesOneTape_exec_decompose; eauto.
    rewrite dmap_mass.
    unfold pmf at 1. simpl. unfold ssd_pmf. 
    simpl. symmetry. apply Rminus_diag_uniq_sym. 
    rewrite -Rminus_plus_distr.
    apply Rminus_diag_eq.
    rewrite -SeriesC_plus;
    try (apply (ex_seriesC_le _ (state_stepN σ1 l1 n)); auto; intros; simpl; case_bool_decide; real_solver).
    erewrite SeriesC_ext.
    2 : {
      intros.
      case_bool_decide; case_bool_decide; try contradiction.
      - ring_simplify. reflexivity.
      - ring_simplify. reflexivity.
    }
    rewrite /state_stepN.
    erewrite metatheory.iterM_state_step_unfold; eauto.
    by rewrite dmap_mass dunifv_mass. 
  }
  rewrite H4. 
  eapply ARcoupl_ssdp_inv.
  eapply ARcoupl_map_inv; auto.
  erewrite SamplesOneTape_exec_decompose in H3; eauto.
  rewrite (SamplesOneTape_exec_decompose l2 _ m t2) in H3; auto.
Qed.

Lemma SamplesOneTape_lim_exec_state_determinize l1 l2 e1 σ1 e2 σ2 t1 t2 ɛ ɛ' ψ:
  σ1.(tapes) !! l1 = Some (2%nat; t1) ->
  σ2.(tapes) !! l2 = Some (2%nat; t2) ->
  SamplesOneTape l1 e1 ->
  SamplesOneTape l2 e2 ->
  0 <= ɛ < ɛ' ->
  SeriesC (lim_exec (e1, σ1)) = 1 ->
  ARcoupl (lim_exec (e1, σ1)) (lim_exec (e2, σ2)) ψ ɛ ->
  ∃ n m, ARcoupl (state_stepN σ1 l1 n) (state_stepN σ2 l2 m) 
    (λ σ'1 σ'2, ∃ v1 v2, ψ v1 v2 ∧ exec n (e1, σ'1) = dret v1 ∧ exec m (e2, σ'2) = dret v2) 
    ɛ'.
Proof.
  intros.
  eapply lim_exec_approx_coupl in H5 as [m ?].
  Unshelve.
  4 : exact ((ɛ + ɛ')/2).
  2 : real_solver.
  2 : real_solver.
  set ɛ1 := (ɛ' - ɛ) / 2.
  assert (0 < ɛ1). {
    rewrite /ɛ1. real_solver. 
  }
  assert (1 - ɛ1 < 1). { real_solver. }
  pose proof (AST_pt_lim _ _ H4 H7) as [n Hn].
  exists n, m.
  replace ɛ' with ((ɛ + ɛ')/2 + ɛ1). 
  2 : { rewrite /ɛ1. real_solver. } 
  eapply ARcoupl_mono; try eauto.
  { intros. apply H8. }
  { 
    eapply Rplus_le_compat_l. 
    assert (1 - pterm n (e1, σ1) <= ɛ1).
    { real_solver. }
    { apply H8. } 
  }
  eapply SamplesOneTape_exec_state_determinize; eauto.
  real_solver. 
Qed.

End Presample.

Section Coupl.
Context `{!approxisGS Σ}.

Notation σ₀ := {| heap := ∅; tapes := ∅ |}.

Lemma det_result_rel_wp (e1 e2 : expr) (σ1 σ2 : state) l1 l2 n m t1 t2 v1 v2 :
  SamplesOneTape l1 e1 -> SamplesOneTape l2 e2 ->
  (n <= length t1)%nat -> (m <= length t2)%nat ->
  σ1.(tapes) !! l1 = Some (2%nat; t1) ->
  σ2.(tapes) !! l2 = Some (2%nat; t2) ->
  (exec n (e1, σ1)) = dret v1 -> (exec m (e2, σ2)) = dret v2 ->
  l1 ↪ (2%nat; t1) ∗ l2 ↪ₛ (2%nat; t2) ∗ ⤇ e2 -∗ 
    WP e1 {{ v,  ⤇ (Val v2) ∗ ⌜v = v1⌝ }}.
Proof.
  iLöb as "IH"  forall (e1 σ1 e2 σ2 n m t1 t2).
  iIntros "%%%%%%%% (Hl1 & Hl2 & Hsp)".
  iApply wp_lift_step_couple. simpl.
  iIntros "%%%% ((Hsa & Hta) & Hspa & Hea)". 
  iPoseProof (spec_auth_prog_agree with "Hspa Hsp") as "%He2".
  subst.
  iDestruct "Hspa" as "(Hspa & (Hsha & Hsta))".
  simpl. 
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "hclose".
  iPoseProof (ghost_map_lookup with "Hta Hl1") as "%Hl1". 
  iPoseProof (ghost_map_lookup with "Hsta Hl2") as "%Hl2". 
  destruct (to_val e1) eqn : Hev.
  {
    eapply presamples_exec_det_pexec in x6 as [σ' Hs']; eauto.
    eapply presamples_pexec_var in Hs' as [σ'2 Hs1']; eauto. 
    pose proof Hs1' as Hs1''.
    eapply presamples_pexec_det_state in Hs1'' as [Hs1'h [t'' Hs1't] ]; eauto.
    iApply spec_coupl_steps_det. 
    { 
      simpl.
      erewrite Hs1'. eapply dret_1_1.
      reflexivity.
    }
    iApply spec_coupl_ret.
    iMod (spec_update_prog (Val v2) with "[Hspa Hsha Hsta] Hsp") as "[Hspa Hsp]".
    { iFrame. }    
    iMod (spec_auth_update_tape (2%nat; t'') with "Hspa Hl2") as "[Hspa Hl2]".
    iMod "hclose".
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros.
    unfold spec_auth. simpl.
    iDestruct "Hspa" as "(H1 & H2 & H3)". 
    rewrite Hs1'h. rewrite Hs1't. 
    iFrame. 
    iPureIntro.
    rewrite exec_unfold in x5. 
    simpl in x5. rewrite Hev in x5. by apply dret_ext_inv in x5.
  }
  iApply spec_coupl_ret.
  destruct n. {
    rewrite exec_unfold in x5. simpl in x5.
    rewrite Hev in x5. by apply dzero_neq_dret in x5. 
  }
  pose proof Hl1 as Hl1'. 
  eapply SamplesOneTape_exec_state_rel' in Hl1'. 
  3 : simpl; by rewrite Hl1 -x3.
  2 : eauto. 
  erewrite x5 in Hl1'. 
  rewrite exec_Sn step_or_final_no_final in x5; auto.
   
  assert (∃ e' σ', step (e1, σ0) = dret (e', σ')) as [ e' [ σ' H] ].
  { 
    destruct (ExcludedMiddle (∃ ρ', step (e1, σ1) ρ' > 0)).
    2 : {
      pose proof (not_exists_forall_not _ _ H) as H'.
      assert (step (e1, σ1) = dzero). {
        apply dzero_ext.
        intros.
        apply Rle_antisym; try real_solver. 
        specialize (H' a).
        simpl in *.
        real_solver.
      }  
      rewrite H0 dbind_dzero in x5. 
      by apply dzero_neq_dret in x5.
    }
    destruct H as [ [e' _σ'] H].
    destruct t1; simpl in x1; try lia. 
    eapply SamplesOneTape_step_pos_var in H as [σ' H]; eauto. 
    eapply SamplesOneTape_step_det in H; eauto. 
    exists e', σ'.
    by apply pmf_1_eq_dret.
  }
  
  iApply (prog_coupl_step_l_dret ε1 0%NNR _ (λ r s, r = (e', σ') ∧ s = σ1')).
  { apply nnreal_ext =>/=. lra. }
  { exists (e', σ'). rewrite H dret_1_1; auto; lra. }
  { 
    simpl in *.
    rewrite H.
    apply ARcoupl_dret; auto; lra.
  }
  iIntros "%%%". 
  destruct H0 as [H00 _].
  inversion H00; subst. clear H00.
  assert  (step (e1, σ0) (e', σ') > 0). 
  { rewrite H dret_1_1; auto; lra. }
  destruct t1; simpl in x1; try lia.
  pose proof H0 as H0'.
  eapply SamplesOneTape_step_heap in H0 as <- ; eauto.
  assert (∃ t', tapes σ' = <[l1 :=(2%nat; t')]> (tapes σ0) ∧ n ≤ length t' ) as [t' [Ht' Ht'l] ]. {
    eapply SamplesOneTape_step_tapes in H0' as Ht' ; eauto.   
    destruct Ht' as [-> | ->].
    - exists (t :: t1). split.  
      2 : { simpl. lia. }
      symmetry. by eapply insert_id. 
    - exists t1; split; auto; lia. 
  }
  iMod (ghost_map_update with "Hta Hl1") as "[Hta Hl1]". 
  Unshelve. 2 : (exact (2%nat; t')).
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "hclose'".
  iApply spec_coupl_ret. 
  iNext.
  iMod "hclose". 
  iApply fupd_mask_intro.
  { set_solver. } 
  iIntros. rewrite Ht'. 
  iFrame. 
  pose proof H0' as H0.
  eapply SamplesOneTape_step_pos_var in H0' as [σ'2 H0']; eauto.
  iApply "IH"; last first; first iFrame;
  iPureIntro; eauto. 
  - Unshelve. 2 : exact σ'2.
    eapply SamplesOneTape_step_det in H0'; eauto.
    apply pmf_1_eq_dret in H0'. 
    rewrite exec_Sn step_or_final_no_final in Hl1'; auto. 
    by rewrite H0' dret_id_left' in Hl1'. 
  - eapply SamplesOneTape_step_state_var in H0; eauto. 
    rewrite H0 Ht'. apply lookup_insert.  
  - eapply SamplesOneTape_inv; eauto.
Qed.

Lemma det_result_rel_wp' (e1 e2 : expr) (σ1 σ2 : state) l1 l2 t1 t2 ψ ɛ ɛ':
  SamplesOneTape l1 e1 -> SamplesOneTape l2 e2 ->
  σ1.(tapes) !! l1 = Some (2%nat; t1) -> σ2.(tapes) !! l2 = Some (2%nat; t2) -> 
  SeriesC (lim_exec (e1, σ1)) = 1 ->
  0 <= ɛ -> ɛ < ɛ' ->
  ARcoupl (lim_exec (e1, σ1)) (lim_exec (e2, σ2)) ψ ɛ -> 
  ↯ ɛ' ∗ l1 ↪ (2%nat; t1) ∗ l2 ↪ₛ (2%nat; t2) ∗ ⤇ e2 -∗ 
    WP e1 {{ v, ∃ v', ⤇ (Val v') ∗ ⌜ψ v v'⌝ }}.
Proof.
Admitted.  
End Coupl.