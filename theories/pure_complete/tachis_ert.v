From clutch.tachis Require Import adequacy.
From clutch.tachis Require Import ert_weakestpre problang_wp.
From clutch.common Require Import ectx_language.
From clutch.prob_lang Require Import notation tactics metatheory.
From clutch.prob_lang Require Export lang.
From clutch.tachis Require Export expected_time_credits ert_weakestpre problang_wp proofmode
  derived_laws cost_models ert_rules.
From iris.proofmode Require Export proofmode.
From Coquelicot Require Import Rcomplements Rbar Lim_seq.
From clutch.pure_complete Require Import pure term.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(* Some misc lemmas *)

Lemma pos_series_le_one `{Countable A} (f : A -> R) (x : A):
  (∀ y, 0 <= f y) ->
  ex_seriesC f ->
  f x <= SeriesC f.
Proof.
  intros.
  rewrite -(SeriesC_singleton_dependent).
  by apply SeriesC_filter_leq.
Qed.

Lemma is_finite_dec x:
  {is_finite x} + {¬ is_finite x}.
Proof.
  rewrite /is_finite.
  destruct x; simpl.
  - by left.
  - right. unfold not. intros. inversion H.
  - right. unfold not. intros. inversion H.
Qed.

Lemma reducible_dec {δ} (x : mstate δ):
  {reducible x} + {¬ reducible x}.
Proof.
  destruct (Rle_dec (SeriesC (step x)) 0).
  - right. 
    apply not_reducible. rewrite /irreducible.
    intros. replace (step x) with (dzero : distr (mstate δ)); auto.
    symmetry. apply SeriesC_zero_dzero.
    apply Rle_antisym; auto. 
  - left. 
    apply mass_pos_reducible. lra.
Qed.

Lemma finite_bounded n (f : fin n -> R):
  (∀ x, 0 <= f x) ->
  ∃ r, 0 <= r ∧ ∀ x, f x <= r.
Proof.
  induction n.
  { 
    intros. exists 0. 
    split; try lra.
    intros. 
    apply Fin.case0. apply x.
  }
  intros.
  epose proof (IHn (f ∘ Fin.FS) _) as [r [Hp Hr]].
  assert (n < S n)%nat; try lia.
  destruct (Rle_dec (f 0%fin) r).
  {
    exists r.
    split; auto.
    by apply (fin_S_inv (n := n)).
  }
  exists (f 0%fin).
  split; auto.
  apply (fin_S_inv (n := n)); try lra. 
  intros.
  etrans.
  { apply Hr. }
  lra.
  Unshelve.
  by simpl.
Qed.

Lemma prim_step_fin e σ:
  reducible (e, σ) ->
  (∃ ρ, prim_step e σ = dret ρ) 
  ∨ (∃ n (g : (fin n) -> cfg), 
    prim_step e σ = dmap g (dunif n) ∧ (Inj eq eq g)).
Proof.
  rewrite /reducible.
  simpl.
  rewrite /prim_step.
  intros.
  destruct H as [[e' σ'] ].
  simpl in *.
  assert (∀ n, Inj eq eq (λ n0 : fin (S (Z.to_nat n)), (#n0, σ))). {
    intros.
    unfold Inj.
    intros.
    inversion H0. 
    by apply Nat2Z.inj, fin_to_nat_inj in H2.
  }
  destruct (decomp e) eqn :Hde.  
  rewrite Hde.
  rewrite Hde in H.
  apply dmap_pos in H as [[e1 σ1] [Hf H]].
  destruct e0; inv_head_step; 
  try by (rewrite dmap_dret; do 3 econstructor).
  - rewrite dmap_comp. do 4 econstructor; try by econstructor. 
    apply (compose_inj eq eq eq).
    + unfold Inj.
      intros.
      inversion H.
      by apply Nat2Z.inj, fin_to_nat_inj in H2.
    + apply inj_fill.
  - rewrite dmap_comp. do 4 econstructor; try by econstructor.
    apply (compose_inj eq eq eq).
    + unfold Inj.
      intros.
      inversion H.
      by apply Nat2Z.inj, fin_to_nat_inj in H2.
    + apply inj_fill.
  - rewrite dmap_comp. do 4 econstructor; try by econstructor. 
    apply (compose_inj eq eq eq).
    + unfold Inj.
      intros.
      inversion H1.
      by apply Nat2Z.inj, fin_to_nat_inj in H3.
    + apply inj_fill.
Qed.

Lemma pos_step_exExpval e σ f: 
  (∀ ρ : mstate (lang_markov prob_lang), 0 <= f ρ) ->
  ex_seriesC (λ ρ , step (e, σ) ρ * f ρ).
Proof.
  simpl. intros.
  destruct (Rlt_dec 0 (SeriesC (step (e, σ)))).
  2: {
    eapply ex_seriesC_ext.
    2:  apply ex_seriesC_0.
    intros. 
    replace (prim_step _ _) with (dzero : distr (expr * state)); try real_solver.
    symmetry. apply SeriesC_zero_dzero.
    apply Rle_antisym.
    - by apply Rnot_lt_le.
    - apply pmf_SeriesC_ge_0.
  }
  epose proof (prim_step_fin e σ _) as [[ρ Hd] | [m [g [Hd _]]]];
  rewrite Hd.
  - apply ex_expval_dret.
  - rewrite /dmap. apply ex_expval_dbind.
    + apply H.
    + apply ex_seriesC_finite.
    + intros. apply ex_expval_dret.
  Unshelve.
  by apply mass_pos_reducible.
Qed.

Lemma bounded_finite_sup (h : nat -> R): 
  is_finite (Sup_seq h) ↔ ∃ r, ∀ x, h x <= r.
Proof.
  split.
  - rewrite is_finite_correct. intros [y Hs].
    specialize (sup_is_upper_bound h). rewrite Hs. intros.
    exists y. intros. apply H.
  - intros [r Hbound].
    destruct (Sup_seq h) eqn: Hss.
    + by rewrite /is_finite.
    + exfalso. 
      specialize (Sup_seq_correct (λ x : nat, h x)).
      rewrite Hss /is_sup_seq. intros.
      specialize (H r) as [m H].
      specialize (Hbound m). simpl in H. lra.
    + exfalso. 
      specialize (Sup_seq_correct (λ x : nat, h x)).
      rewrite Hss /is_sup_seq. intros.
      specialize (H (h 0%nat) 0%nat).
      simpl in H. lra.
Qed. 

Section ERT.
Context {costfun : Costfun prob_lang}.

Lemma ERT_val n e σ:
  is_Some (to_val e) ->
  ERT n (e, σ) = 0.
Proof.
  intros.
  inversion H.
  destruct n; auto.
  by rewrite /ERT H0.
Qed.

Lemma ERT_n_exExpval n e σ: 
  ex_seriesC (λ ρ , step (e, σ) ρ * ERT n ρ).
Proof.
  apply pos_step_exExpval, ERT_nonneg.
Qed.

Lemma ERT_mono e σ n: 
  ERT n (e, σ) <= ERT (S n) (e, σ).
Proof.
  revert e σ.
  induction n.
  { intros. apply ERT_nonneg. }
  
  intros. 
  destruct (to_val e) eqn: Hev.
  {
    simpl. by rewrite Hev.
  }
  rewrite !ERT_Sn; auto.
  apply Rplus_le_compat_l.
  apply SeriesC_le.
  2 : apply ERT_n_exExpval.
  intros.
  destruct n0.
  destruct (to_val e0) eqn: Hve.
  {
    rewrite !ERT_val; auto.
    by rewrite Rmult_0_r.
  }
  split.
  - apply Rmult_le_pos.
    + apply pmf_pos.
    + apply ERT_nonneg.
  - apply Rmult_le_compat_l.
    + apply pmf_pos.
    + by apply IHn.
Qed.

Lemma lim_ERT_ge e σ (x : nonnegreal) :
  Rbar_le (lim_ERT (e, σ)) x ->
  ∀ n, ERT n (e, σ) <= x.
Proof.
  rewrite /lim_ERT.
  intros.
  pose proof (sup_is_upper_bound (fun n => ERT n (e,σ)) n).
  apply (Rbar_le_fin (ERT n (pair e σ)) x).
  - apply cond_nonneg.
  - etrans.
    + simpl in *. apply H0.
    + apply H.
Qed.

Lemma lim_ERT_bge0 ρ:
  Rbar_le 0 (lim_ERT ρ).
Proof.
  intros.
  rewrite /lim_ERT.
  etrans.
  - apply rbar_le_rle. apply ERT_nonneg.
  - apply (sup_is_upper_bound (λ n : nat, ERT n _) 0).
Qed.

Lemma lim_ERT_ge0 ρ:
  0 <= (lim_ERT ρ).
Proof.
  intros.
  apply Rbar_0_le_to_Rle.
  apply lim_ERT_bge0.
Qed.

Lemma lim_ERT_fin_inv ρ:
  is_finite (lim_ERT ρ) ->
  ∀ ρ', (step ρ ρ' > 0 -> is_finite (lim_ERT ρ')).
Proof.
  (* 
  Proof by contradiction:
  assume that ERT_n(ρ') is not bounded for some
  step ρ ρ' > 0, then ERT_n(ρ) is not bounded.
  *)
  destruct (to_val ρ.1) eqn : Hv.
  {
    intros.
    destruct ρ.
    assert (step (e,s) ρ' = 0).
    {
      rewrite is_final_dzero; auto.
      rewrite /is_final /to_final. simpl. auto.
    } 
    lra.
  }
  rewrite bounded_finite_sup.
  intros.
  destruct (is_finite_dec (lim_ERT ρ')) as [HH | Hcontras]; auto.
  destruct H.
  rewrite bounded_finite_sup in Hcontras.
  exfalso.
  assert (∀ r: R, ∃ x : nat, r < ERT x ρ').
  {
    apply Classical_Pred_Type.not_ex_not_all.
    unfold not. intros. apply Hcontras. destruct H1.
    exists x0. apply Classical_Pred_Type.not_ex_not_all.
    unfold not. intros. apply H1. destruct H2.
    exists x1. by apply Rnot_le_lt in H2.
  }
  specialize H1 with (x / (step ρ ρ')) as [n H'].
  specialize H with (S n).
  eapply Rmult_lt_compat_r in H'.
  2: apply H0.
  rewrite Rdiv_def Rmult_assoc Rinv_l in H'.
  2: lra.
  rewrite Rmult_1_r in H'.
  destruct ρ, ρ'.
  rewrite ERT_Sn in H; auto.
  assert (ERT n (e0, s0) * step (e, s) (e0, s0) <= x).
  2: lra.
  trans (SeriesC (λ ρ : mstate (lang_markov prob_lang), step (e, s) ρ * ERT n ρ)).
  - rewrite Rmult_comm.
    apply (pos_series_le_one (λ ρ : mstate (lang_markov prob_lang), step (e, s) ρ * ERT n ρ)).
    + intros. apply Rmult_le_pos; auto. 
      apply ERT_nonneg.
    + apply ERT_n_exExpval.
  - etrans.
    2: apply H.
    rewrite Rplus_comm.
    apply Rplus_le_0_compat.
    apply cost_nonneg.
Qed.

Lemma lim_ERT_bounded_inv ρ:
  is_finite (lim_ERT ρ) ->
  ∃ r, 0 <= r ∧ ∀ ρ', step ρ ρ' > 0 -> (lim_ERT ρ') <= r.
Proof.
  (*
  step ρ has finite support, simply take 
  r := max{lim_ERT ρ' | step ρ ρ' > 0}
  *)
  intros.
  destruct (reducible_dec ρ) as [Hr | Hnr].
  2 : {
    exists 0. split; try lra.
    intros. exfalso. apply Hnr.
    econstructor. apply H0.
  }
  destruct ρ.
  destruct (prim_step_fin _ _ Hr) as [[ρ' Hd]| [n [g [Hd Hg]]]]. 
  {
    exists (lim_ERT ρ'). split.
    { apply lim_ERT_ge0. }
    simpl. rewrite Hd.
    intros. apply dret_pos in H0. by subst.
  }
  simpl. rewrite Hd. 
  destruct (finite_bounded n (lim_ERT ∘ g)) as [r [Hrp He]]. 
  { intros. simpl. apply lim_ERT_ge0. }
  exists r.
  split; auto.
  intros.
  apply dmap_pos in H0 as [m [H1 H2]]; subst.
  simpl in *. apply He.
Qed.


Definition lim_ERTNN ρ := mknonnegreal (lim_ERT ρ) (lim_ERT_ge0 ρ).

Lemma lim_ERT_exp_ge e σ (x : nonnegreal):
  to_val e = None ->
  Rbar_le (lim_ERT (e, σ)) x -> 
  ∀ n, SeriesC (λ ρ, step (e, σ) ρ * ERT n ρ) <= x.
Proof.
  intros. 
  apply (Rplus_le_reg_l (cost e)).
  rewrite -ERT_Sn; auto.
  etrans.
  - by apply lim_ERT_ge.
  - specialize (cost_nonneg e) as H'.
    lra.
Qed.

Lemma lim_ERT_fin_part e σ: 
  to_val e = None ->
  is_finite (lim_ERT (e, σ)) ->
  is_finite (Sup_seq (fun n => SeriesC (λ ρ, step (e, σ) ρ * ERT n ρ))).
Proof.
  intros. 
  rewrite bounded_finite_sup.
  destruct (lim_ERT (e, σ)) eqn : Hl;
  try by inversion H0.
  assert (0 <= r). {
    specialize (lim_ERT_bge0 (e, σ)). 
    by rewrite Hl.
  }
  set (rnn := mknonnegreal r H1).
  exists rnn.
  eapply (lim_ERT_exp_ge); auto.
  simpl. by rewrite Hl.
Qed.

(* 
  swap supremum and series using monotone convergence
*)
Lemma lim_ERT_rec e σ: 
  is_finite (lim_ERT (e, σ)) ->
  to_val e = None ->
  lim_ERT (e, σ) = cost e + SeriesC (λ ρ, step (e, σ) ρ * lim_ERT ρ)%R.
Proof.
  intros.
  rewrite /lim_ERT. 
  assert (Rbar_le (lim_ERT (e,σ)) (lim_ERTNN (e,σ))).
  {
    simpl. by rewrite H.
  }
  rewrite mon_sup_succ.
  2 : intros; by apply ERT_mono. 
  erewrite Sup_seq_ext.
  2 : { intros. by rewrite ERT_Sn. }
  erewrite Sup_seq_bounded_plus_l.
  2 : {
    intros. split.
    - apply SeriesC_ge_0'.
      intros. apply Rmult_le_pos.
      + apply pmf_pos.
      + apply ERT_nonneg.
    - by apply lim_ERT_exp_ge. 
  }
  rewrite (SeriesC_ext _ (fun ρ => step (e, σ) ρ *  Sup_seq (λ n : nat, (if bool_decide (0 < step (e, σ) ρ) then ERT n ρ else 0)))). 
  2: {
    intros.
    case_bool_decide; auto.
    replace (step _ _) with 0; try lra.
    apply Rle_antisym.
    - apply pmf_pos.
    - lra.
  }
  rewrite (SeriesC_ext _ (fun ρ => Sup_seq (λ n : nat, step (e, σ) ρ * (if bool_decide (0 < step (e, σ) ρ) then ERT n ρ else 0)))).
  2: {
    intros.
    rewrite Sup_seq_scal_l'.
    2: apply pmf_pos. 
    2: {
      case_bool_decide.
      - by eapply lim_ERT_fin_inv.
      - apply (is_finite_bounded 0 0).
        + apply (Sup_seq_minor_le _ _ 0). 
          reflexivity.
        + apply upper_bound_ge_sup. intro.
          reflexivity.
    }
    simpl. do 5 f_equal. 
    apply functional_extensionality.
    intros. case_bool_decide; auto.
  }
  erewrite SeriesC_ext.
  2 : {
    intros.
    erewrite Sup_seq_ext.
    { reflexivity. }
    intros. case_bool_decide.
    - reflexivity.
    - replace (step (e,σ) n) with 0.
      + simpl. by rewrite !Rmult_0_l.
      + apply Rle_antisym.
        { apply pmf_pos. }
        { lra. }
  }
  destruct (lim_ERT_bounded_inv (e,σ) H) as [r [Hr1 Hr2]].
  erewrite (SeriesC_Sup_seq_swap (lim_ERT (e,σ)) (fun n => SeriesC (λ ρ , step (e, σ) ρ * ERT n ρ))); auto.
  - intros.
    apply Rmult_le_pos; auto.
    apply ERT_nonneg.
  - intros. 
    apply Rmult_le_compat_l; auto.
    destruct a.
    apply ERT_mono.
  - intros. 
    exists r.
    intros.
    destruct (Rle_dec (step (e,σ) a) 0).
    + replace (step (e,σ) a) with 0; real_solver.
    + apply Rnot_le_lt in n0 as Hst. apply Hr2 in Hst.
      rewrite -(Rmult_1_l r).
      apply Rmult_le_compat; auto.
      { apply ERT_nonneg. }
      { 
        destruct a.
        specialize (lim_ERT_ge e0 s (mknonnegreal r Hr1)). simpl.
        intros. apply H2.
        apply Rnot_le_lt, lim_ERT_fin_inv in n0; auto.
        by rewrite -n0.
      }
  - intros. apply SeriesC_correct.
    apply ERT_n_exExpval.
  - intros. 
    rewrite /lim_ERT mon_sup_succ. 
    2 : apply ERT_mono.
    erewrite Sup_seq_ext.
    2 : { intros. rewrite ERT_Sn; auto. }
    erewrite Sup_seq_bounded_plus_l.
    2 : {
      intros. split.
      - apply SeriesC_ge_0'.
        intros. apply Rmult_le_pos.
        + apply pmf_pos.
        + apply ERT_nonneg.
      - by apply lim_ERT_exp_ge. 
    }
    trans (Sup_seq (λ x0 : nat, SeriesC (λ ρ : mstate (lang_markov prob_lang), step (e, σ) ρ * ERT x0 ρ))).
    + rewrite -rbar_le_rle. 
      pose proof (lim_ERT_fin_part e σ H0 H).
      rewrite /is_finite in H2. rewrite H2.
      eapply (is_sup_seq_major (λ x0 : nat, SeriesC (λ ρ : mstate (lang_markov prob_lang), step (e, σ) ρ * ERT x0 ρ))). 
      apply Sup_seq_correct.
    + rewrite Rplus_comm. 
      apply Rplus_le_0_compat. 
      apply cost_nonneg.
      
  Unshelve.
  { apply 0. }
Qed.

Lemma ERT_pure n e σ σ':
  is_pure e = true ->
  ERT n (e, σ) = ERT n (e, σ'). 
Proof.
  intros.
  revert n e σ σ' H.
  induction n; auto.
  intros. simpl.
  destruct (language.to_val e) eqn: He; rewrite He; auto.
  f_equal. 
  rewrite !fubini_pos_seriesC_prod_rl; 
  try apply ERT_n_exExpval.
  2 : {
    intros. 
    apply Rmult_le_pos.
    - apply pmf_pos.
    - apply ERT_nonneg.
  }
  2 : {
    intros. 
    apply Rmult_le_pos.
    - apply pmf_pos.
    - apply ERT_nonneg.
  }
  rewrite (SeriesC_ext 
    (λ b : language.state prob_lang, _) 
    (λ b, if bool_decide (b = σ) then SeriesC (λ a , step (e, σ) (a, b) * ERT n (a, b)) else 0)).
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
    (λ b : state, _) 
    (λ b, if bool_decide (b = σ') then SeriesC (λ a , step (e, σ') (a, b) * ERT n (a, b)) else 0)).
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
  rewrite (pure_step_state _ _ σ' σ); auto.
  destruct (Rle_decision (step (e, σ) (n0, σ)) 0).
  - epose proof (Rle_antisym _ _ r _). 
    rewrite H0. real_solver.
    Unshelve. auto.
  - erewrite IHn.
    { rewrite (pure_step_state _ n0 σ σ' H). auto. }
    eapply pure_step_inv.
    { apply H. }
    { apply Rnot_le_gt. apply n1. }
Qed.

Lemma lim_ERT_pure e σ σ':
  is_pure e = true ->
  lim_ERT (e, σ) = lim_ERT (e, σ').
Proof.
  intros.
  rewrite /lim_ERT. 
  apply Sup_seq_ext.
  intros. f_equal. by apply ERT_pure. 
Qed.

End ERT.

Section Complete.

Context (costfun : Costfun prob_lang).
Context `{!tachisGS Σ costfun}.

Notation σ₀ := {| heap := ∅; tapes := ∅ |}. 

(* the expression have to be well-typed*)
Inductive ReducibleInv : (expr * state) -> Prop:=
  | RINeverStuck e σ:
      reducible (e, σ) ->
      (∀ e' σ', step (e, σ) (e', σ') > 0 -> ReducibleInv (e', σ')) -> 
      ReducibleInv (e, σ).

Theorem wp_ERT_complete_pure (e : expr):
  ReducibleInv (e, σ₀) ->
  is_pure e = true ->
  is_finite (lim_ERT (e, σ₀)) ->
  ⧖ (lim_ERT (e, σ₀)) -∗ WP e {{ v, True }}.
Proof.
  iLöb as "IH" forall (e).
  iIntros "%H%Hp%Hlim Hc".
  destruct ( language.to_val e) eqn: He.
  { iIntros. apply of_to_val in He as <-. by wp_pures. }
  inversion H; subst.
  iApply wp_lift_step_fupd_ERM; auto.
  iIntros "%% [Hs Hca]". 
  iDestruct (etc_supply_bound' with "Hca Hc") as "%".
  do 3 destruct H0.
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hclose".
  iApply ERM_adv_comp. simpl.
  iExists (fun ρ => if bool_decide (step (e, σ1) ρ > 0) then (x0 + lim_ERTNN ρ)%NNR else 0%NNR).
  iSplitR.
  { 
    iPureIntro. 
    by eapply pure_reducible.
  }
  iSplitR.
  {
    iPureIntro.
    intros. simpl.
    case_bool_decide; simpl; try lra. 
    apply Rplus_le_le_0_compat; auto.
    - apply cond_nonneg.
    - apply lim_ERT_ge0.
  }
  iSplitR.
  {
    iPureIntro.
    erewrite lim_ERT_pure in Hlim; auto.
    destruct (lim_ERT_bounded_inv (e,σ1) Hlim) as [r [Hr1 Hr2]].
    exists (x0+r). intros.
    case_bool_decide.
    - simpl. specialize (Hr2 ρ H4).
      lra.
    - simpl. apply Rplus_le_le_0_compat; auto.
      apply cond_nonneg.
  }
  iSplitR.
  {
    iPureIntro.
    erewrite SeriesC_ext.
    2: {
      intros.
      case_bool_decide.
      - reflexivity.
      - simpl in *. 
        apply Rnot_gt_le in H4.
        pose proof (pmf_pos (prim_step e σ1) n).
        assert ((prim_step e σ1 n) = 0); try real_solver.
        rewrite H6. real_solver.
    }
    erewrite SeriesC_ext.
    2: intros; by rewrite Rmult_plus_distr_l.
    rewrite SeriesC_plus.
    2: apply ex_seriesC_scal_r, pmf_ex_seriesC.
    2: apply pos_step_exExpval, lim_ERT_ge0.
    rewrite SeriesC_scal_r. 
    rewrite H0. simpl.
    rewrite (Rplus_comm (SeriesC _ * _) _) -Rplus_assoc. 
    apply Rplus_le_compat.
    2: {
      rewrite <-(Rmult_1_l x0) at 2.
      apply Rmult_le_compat_r. 
      - apply cond_nonneg.
      - apply pmf_SeriesC.
    }
    rewrite H1.
    rewrite (lim_ERT_pure _ _ σ1); auto.
    rewrite lim_ERT_rec; auto.
    2: by rewrite (lim_ERT_pure _ _ σ1) in Hlim.
    by simpl.
  }
  iIntros.
  case_bool_decide; try (simpl in *; by lra).
  iMod (etc_supply_decrease with "Hca Hc") as (????) "Hca".
  replace (nonneg x0 + nonneg (lim_ERTNN (costfun := costfun) (e2, σ2)))%R with (nonneg (x0 + lim_ERTNN(e2, σ2)))%NNR; [|by simpl].
  replace x3 with x0 in *. 2: {
    apply nnreal_ext.
    eapply (Rplus_eq_reg_r (lim_ERT (e, σ₀))).
    rewrite <- H7 at 2. rewrite -H1.
    simpl in *.
    replace (nonneg x0 + nonneg x)%R with(nonneg (x0 + x)%NNR); [|by simpl].
    replace (nonneg x3 + nonneg x2)%R with(nonneg (x3 + x2)%NNR); [|by simpl].
    rewrite nnreal_plus_comm.
    rewrite -H0 -H6 //.
  }
  iMod (etc_supply_increase x0 (lim_ERTNN (e2, σ2)) with "[Hca]") as "(%x4&Hca&%&Hc)"; try lra; auto.
  { simpl. apply lim_ERT_ge0. }
  iModIntro.
  iNext.
  iMod "Hclose".
  iApply fupd_mask_intro.
  { set_solver. }
  apply (pure_state_step) in H5 as H'5; auto.
  subst σ2.
  iIntros.
  iFrame.
  iSplitL "Hca".
  {
    iApply (etc_supply_irrel with "Hca").
    simpl. real_solver.
  }
  iApply "IH".
  - iPureIntro. 
    eapply H3.
    erewrite pure_step_state; auto.
    apply H5.
  - iPureIntro. 
    eapply pure_step_inv.
    + apply Hp.
    + apply H5.
  - iPureIntro.
    eapply lim_ERT_fin_inv.
    + apply Hlim.
    + erewrite pure_step_state in H5; auto. 
      simpl in H5. apply H5.
  - erewrite lim_ERT_pure; auto.
    eapply pure_step_inv.
    + apply Hp.
    + apply H5.
  Unshelve.
  apply 0. (* Where did that come from ??? *)
Qed.

End Complete.