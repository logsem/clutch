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

Lemma presamples_stepN_det_part l σ n N t e:
  σ.(tapes) !! l = Some (N; t) ->
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
  epose proof (SamplesOneTape_step_state _ _ _ _ _ _ _ _ H1 H Hst) as [Ht | Ht].
  - eapply IHn; eauto. 
    { by rewrite Ht. }
    simpl. lia.
  - eapply IHn; eauto. 
    { rewrite Ht. by apply lookup_insert. }
    lia.
Qed. 

Lemma presamples_pexec_det_part l σ n N t e:
  σ.(tapes) !! l = Some (N; t) ->
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
  epose proof (SamplesOneTape_step_state _ _ _ _ _ _ _ _ H1 H Hst) as [Ht | Ht].
  - eapply IHn; eauto. 
    { by rewrite Ht. }
    simpl. lia.
  - eapply IHn; eauto. 
    { rewrite Ht. by apply lookup_insert. }
    lia.
Qed.

Lemma presamples_stepN_det l σ n N t e:
  σ.(tapes) !! l = Some (N; t) ->
  (n <= length t)%nat ->
  SeriesC (stepN n (e, σ)) > 0 ->
  SamplesOneTape l e -> 
  is_det (stepN n (e, σ)).
Proof.
  intros.
  epose proof (presamples_stepN_det_part _ _ _ _ _ _) as [? | ?]; eauto.
  rewrite H3 dzero_mass in H1.
  lra.
Qed.

Lemma presamples_exec_det_part l σ n N t e:
  σ.(tapes) !! l = Some (N; t) ->
  (n <= length t)%nat ->
  SamplesOneTape l e -> 
  (exec n (e, σ)) = dzero ∨ is_det (exec n (e, σ)).
Proof.
  intros.
  rewrite exec_pexec_relate.
  epose proof (presamples_pexec_det_part _ _ _ _ _ _) as [? | (? & ?)]; eauto;
  rewrite H2. 
  - left. by rewrite dbind_dzero.  
  - rewrite dret_id_left'. 
    destruct (to_final x).
    + right. by econstructor.
    + by left. 
Qed.

Lemma presamples_exec_det l σ n N t e:
  σ.(tapes) !! l = Some (N; t) ->
  (n <= length t)%nat ->
  SeriesC (exec n (e, σ)) > 0 ->
  SamplesOneTape l e -> 
  is_det (exec n (e, σ)).
Proof.
  intros.
  epose proof (presamples_exec_det_part _ _ _ _ _ _) as [? | ?]; eauto.
  rewrite H3 dzero_mass in H1.
  lra.
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

Lemma SamplesOneTape_state_stepN_exec_det_part l σ σ' n N t e:
  σ.(tapes) !! l = Some (N; t) ->
  SamplesOneTape l e -> 
  (state_stepN σ l n) σ' > 0 ->
  exec n (e, σ') = dzero ∨ is_det (exec n (e, σ')).
Proof.
  intros.
  apply (state_stepN_heap _ _ _ _ _ _ H) in H1 as Hh.
  pose proof (state_stepN_tape _ _ _ _ _ _ H H1) as [t' [Ht Hst]].
  eapply presamples_exec_det_part; eauto.
  - rewrite Hst. apply lookup_insert. 
  - rewrite app_length Ht. lia.
Qed.

Lemma SamplesOneTape_state_stepN_exec_det l σ σ' n N t e:
  σ.(tapes) !! l = Some (N; t) ->
  SamplesOneTape l e -> 
  (state_stepN σ l n) σ' > 0 ->
  SeriesC (exec n (e, σ')) > 0 ->
  is_det (exec n (e, σ')).
Proof.
  intros.
  epose proof (SamplesOneTape_state_stepN_exec_det_part _ _ _ _ _ _ _) as [? | ?]; eauto.
  rewrite H3 dzero_mass in H2. lra.
Qed. 

Lemma SamplesOneTape_exec_decompose l σ n N t e:
  σ.(tapes) !! l = Some (N; t) ->
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
  epose proof (SamplesOneTape_state_stepN_exec_det_part _ _ _ _ _ _ _) as [? | ?]; eauto.
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

Lemma SamplesOneTape_exec_state_determinize l1 l2 e1 σ1 e2 σ2 N M t1 t2 n m ɛ ɛ' ψ:
  σ1.(tapes) !! l1 = Some (N; t1) ->
  σ2.(tapes) !! l2 = Some (M; t2) ->
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
  rewrite (SamplesOneTape_exec_decompose l2 _ m M t2) in H3; auto.
Qed.

Lemma SamplesOneTape_lim_exec_state_determinize l1 l2 e1 σ1 e2 σ2 N M t1 t2 ɛ ɛ' ψ:
  σ1.(tapes) !! l1 = Some (N; t1) ->
  σ2.(tapes) !! l2 = Some (M; t2) ->
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

Lemma det_result_wp (e1 e2 : expr) (σ1 σ2 : state) l1 l2 n m N M t1 t2 v1 v2 :
  SamplesOneTape l1 e1 -> SamplesOneTape l2 e2 ->
  (n <= length t1)%nat -> (m <= length t2)%nat ->
  (exec n (e1, σ1)) = dret v1 -> (exec m (e2, σ2)) = dret v2 ->
  l1 ↪ (N; t1) ∗ l2 ↪ₛ (M; t2) ∗ ⤇ e2 -∗ 
    WP e1 {{ v, ∃ v', ⤇ (Val v') ∗ ⌜v = v1 ∧ v' = v2⌝ }}.
Proof.
  (* iLöb as "IH"  forall (e1 σ1 e2 σ2 n m t1 t2).
  iIntros "%%%%% (Hl1 & Hl2 & Hsp)".
  iApply wp_lift_step_couple. simpl.
  iIntros "%%%% ((Hsa & Hta) & Hspeca & Hea)". 
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "hclose".
  destruct (to_val e1) eqn : Hev.
  { 
    iApply spec_coupl_steps_det.
    { 

    }
    (* erewrite exec_is_final in x2; eauto. 
    apply dret_ext_inv in x2; subst.
    iMod "hclose". 
    iMod ((spec_update_prog v2) with "Hspeca Hsp") as "[Hspeca Hsp]".
    
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "hclose'".
    iFrame. by iPureIntro. *)
  } *)


  (* 
  iInduction m as [|m] "IH" forall (e1 σ1 e2 σ2 n t1 t2 H1 H2 H3 H0 H).
  {
    unfold exec in H3. simpl in H3.
    destruct (to_val e2) eqn : Hev.
    2 : by apply dzero_neq_dret in H3. 
    apply dret_ext_inv in H3; subst.
    apply of_to_val in Hev; subst.
    iLöb as "IH". 
    iApply wp_lift_step_couple. simpl.
    iIntros "%%%% ((Hsa & Hta) & Hspeca & Hea)". 
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "hclose".
    iApply spec_coupl_ret.
    destruct (to_val e1) eqn : Hev.
    { 
      erewrite exec_is_final in H2; eauto. 
      apply dret_ext_inv in H2; subst.
      iMod "hclose". 
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros "hclose'".
      iFrame. by iPureIntro.
    }
    iApply prog_coupl_step_l.

  }
    *)
Admitted.

Theorem SamplesOneTape_ARcoupl_wp e1 e2 σ1 σ2 l1 l2 t1 t2 N M ψ ɛ ɛ' :
  SamplesOneTape l1 e1 ->
  SamplesOneTape l2 e2 ->
  SeriesC (lim_exec (e1, σ1)) = 1 ->
  0 <= ɛ -> ɛ < ɛ' ->
  ARcoupl (lim_exec (e1, σ1)) (lim_exec (e2, σ2)) ψ ɛ ->
End Coupl.