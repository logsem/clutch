(** * Simple Geometric Example *)
From tachis.prob_lang Require Import lang notation tactics metatheory.
From tachis.tachis Require Export expected_time_credits ert_weakestpre problang_wp proofmode
  derived_laws cost_models ert_rules.
From iris.proofmode Require Export proofmode.
From Coquelicot Require Export Hierarchy.

From Coq Require Export Reals Psatz.
Require Import Lra.


Set Default Proof Using "Type*".
(* Simple example: Flip until heads, expectation should be constant *)

Definition geo
  := (rec: "g" "_" :=
        if: ((rand #1) = #0)%E
          then #()
          else ("g" #()))%V.

Section proofs.
  Context `{!tachisGS Σ CostApp}.
  Lemma wp_geo E:
    {{{ ⧖ (2) }}}
      geo #()@E
      {{{RET #(); True}}}.
  Proof.
    iIntros (Φ) "Hx HΦ".
    iLöb as "IH" forall (Φ) "Hx HΦ".
    rewrite /geo.
    wp_pures.
    replace (2-1) with 1 by lra.
    wp_apply (wp_couple_rand_adv_comp' _ _ _ _ _
                (λ x, if (bool_decide (# (fin_to_nat x) = # 0))
                          then 0
                      else 2) with "[$]").
    - intros; case_bool_decide; lra.
    - simpl. rewrite SeriesC_finite_foldr.
      simpl. lra.
    - iIntros (n) "Hx".
      wp_pure.
      case_bool_decide; simpl; wp_pure.
      + iModIntro. iApply "HΦ". done.
      + iApply ("IH" with "[$]"). done.
  Qed.

End proofs.

From tachis.tachis Require Import adequacy.
From Coquelicot Require Import Rbar.
Open Scope NNR.
Open Scope R.

Lemma ert_geo σ :
  Rbar.real (lim_ERT (costfun := CostApp) (geo #(), σ)) <= 2%NNR.
Proof.
  eapply (wp_ERT_lim _ tachisΣ _ _ _ (λ _, True)) => HtachGS.
  iIntros "Hx".
  by iApply (wp_geo with "Hx").
Qed.

Section generalized.

  Local Hint Resolve pos_INR : core.
  Local Hint Resolve pos_INR_S: core.

  Context (n m:nat).
  Hypothesis (Hineq:(0<m<=S n)%nat).
  Definition geo'
    := (rec: "g" "_" :=
          if: ((rand #n) < #m)%E
          then #()
          else ("g" #()))%V.

  Definition tc := (S n)/(m).

  Local Lemma SeriesC_geo':
    SeriesC (λ n0 : fin (S n), if bool_decide (n0 < m) then 0 else 1) = (S n - m)%R.
  Proof.
    revert Hineq.
    induction m as [|m' IH].
    - intros. lia.
    - intros. replace (S n - S m')%R with (S n - m' - 1); last first.
      { rewrite (S_INR m'). lra. }
      apply Req_minus_r.
      destruct m'.
      + rewrite Rminus_0_r.
        assert (0<S n)%nat as H by lia.
        rewrite -{2}(SeriesC_singleton (nat_to_fin H) 1).
        rewrite -SeriesC_plus; try apply ex_seriesC_finite.
        erewrite SeriesC_ext.
        * erewrite SeriesC_finite_mass. rewrite fin_card.
          apply Rmult_1_r.
        * intros k. simpl. case_bool_decide as H1; case_bool_decide as H2; try lra.
          -- exfalso. apply H2. destruct (fin_to_nat k) eqn:K.
             ++ apply fin_to_nat_inj. done.
             ++ rewrite S_INR in H1. pose proof pos_INR n0. lra.
          -- exfalso. apply H1. rewrite H2. simpl. lra.
      + rewrite -IH; last lia.
        assert (S m' < S n)%nat as H by lia.
        rewrite -{2}(SeriesC_singleton (nat_to_fin H) 1).
        rewrite -SeriesC_plus; last first.
        * apply ex_seriesC_finite.
        * apply ex_seriesC_finite.
        * apply SeriesC_ext.
          intros. case_bool_decide as H1; case_bool_decide as H2; case_bool_decide as H3; simpl; try lra.
          -- rewrite H2 in H3. rewrite fin_to_nat_to_fin in H3. apply INR_lt in H3. lia.
          -- exfalso. apply H3. apply lt_INR. apply INR_lt in H1. assert (fin_to_nat n0 ≠ S m'); try lia.
             intro. apply H2. apply fin_to_nat_inj. rewrite H0. rewrite fin_to_nat_to_fin.
             done.
          -- rewrite H2 in H3. rewrite fin_to_nat_to_fin in H3. apply INR_lt in H3. lia.
          -- exfalso. rewrite H2 in H1. rewrite fin_to_nat_to_fin in H1. apply H1.
             apply lt_INR. lia.
          -- exfalso. apply H1. apply INR_lt in H3. apply lt_INR.
             assert (fin_to_nat n0 ≠ S m')%nat; lia.
  Qed.

  Local Lemma tc_split:
    SeriesC (λ n0 : fin (S n), 1 / (S n) * (if bool_decide (n0 < m) then 0 else tc)) = tc - 1.
  Proof.
    unfold tc.
    remember (S n) as n'.
    erewrite (SeriesC_ext _ (λ n0 : fin n', (if bool_decide (n0 < m) then 0 else 1)*/m)); last first.
    { intros. case_bool_decide; try lra. rewrite Rmult_div_assoc !Rdiv_def Rmult_1_l Rinv_l.
      - done.
      - intro. subst. pose proof pos_INR_S n. lra.
    }
    rewrite SeriesC_scal_r. rewrite <-(Rdiv_diag m) at 1; last first.
    { replace 0 with (INR 0); last (simpl; lra). apply not_INR. lia. }
    rewrite -Rdiv_minus_distr. rewrite -Rdiv_def. f_equal. subst.
    apply SeriesC_geo'.
  Qed.

  Context `{!tachisGS Σ CostApp}.

  Lemma wp_geo' E:
    {{{ ⧖ tc }}}
      geo' #()@E
      {{{RET #(); True}}}.
  Proof.
    assert (1<=tc).
    { unfold tc. apply Rcomplements.Rle_div_r.
      - apply Rlt_gt. replace 0 with (INR 0); last (simpl; lra). apply lt_INR.
        lia.
      - rewrite Rmult_1_l. apply le_INR. lia. }
    iIntros (Φ) "Hx HΦ".
    iLöb as "IH" forall (Φ) "Hx HΦ".
    rewrite /geo'.
    wp_pure.
    wp_apply (wp_couple_rand_adv_comp' _ _ _ _ _
                (λ x, if (bool_decide ((fin_to_nat x) < m))
                          then 0
                      else tc) with "[$]").
    - intros; case_bool_decide; lra.
    - simpl. rewrite Rplus_0_l. apply tc_split.
    - iIntros (v) "Hx". wp_pure.
      case_bool_decide as H1; case_bool_decide as H2; wp_pure.
      + iModIntro. iApply "HΦ". done.
      + exfalso. apply INR_lt in H1. lia.
      + exfalso. apply H1. apply lt_INR. lia.
      + iApply ("IH" with "[$]"). done.
  Qed.

End generalized.
