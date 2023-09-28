From Coq Require Import Reals Psatz.
From clutch.prob_lang Require Import lang notation metatheory.
From clutch.tpref_logic Require Import weakestpre spec primitive_laws proofmode.
From clutch.prob Require Import distribution markov.
From clutch.tpref_logic.examples Require Import flip.
#[local] Open Scope R.

Section brw.
  Context (N : nat).

  Definition brw_step (n : nat) : distr (nat) :=
    if bool_decide (N <= n) then dzero
    else match n with
      | 0 => dzero
      | S m => fair_conv_comb (dret (S n)) (dret (m))
    end.

  Definition brw_to_final (n : nat) : option nat :=
    if bool_decide (N <= n) then Some N
    else match n with
      | 0 => Some 0%nat
      | S m => None
    end.

  Local Lemma brw_to_final_is_Some (n : nat) :
    is_Some (brw_to_final n) → n = 0%nat \/ N <= n.
  Proof.
    rewrite /brw_to_final; case_bool_decide; auto.
    destruct n; auto.
    intros []; done.
  Qed.

  Local Lemma brw_to_final_None (n : nat) :
    brw_to_final n = None → 0 < n < N.
  Proof.
    rewrite /brw_to_final; case_bool_decide.
    - intro; done.
    - destruct n as [? | n0] eqn:Hn ; [ intro; done | ].
      intro; split.
      + rewrite S_INR.
        pose proof (pos_INR n0); lra.
      + lra.
  Qed.

  Definition brw_mixin : MarkovMixin brw_step brw_to_final.
  Proof.
    constructor.
    intros n Hf m.
    rewrite /brw_step.
    apply brw_to_final_is_Some in Hf as [-> | ?];
    case_bool_decide; auto; lra.
  Qed.

  Canonical Structure bounded_random_walk : markov := Markov _ _ brw_mixin.

  Definition rws_rsm_fun (n : nat) := if bool_decide (n <= N) then n*(N-n) else 0.

  Local Lemma rws_rsm_fun_nneg (n : nat) :
    0 <= rws_rsm_fun n.
  Proof.
    rewrite /rws_rsm_fun.
    case_bool_decide; [ | lra].
    pose proof (pos_INR n). nra.
  Qed.

  Lemma rws_rsm_dec (n : nat) :
      0 < n < N →
      0.5 * rws_rsm_fun (S n) + 0.5 * rws_rsm_fun (Nat.pred n) + 0.5 <= rws_rsm_fun n.
  Proof.
    intros [Hn1 Hn2].
    pose proof (S_INR n).
    assert (S n <= N).
    {
      apply le_INR.
      apply INR_lt in Hn2.
      lia.
    }
    assert (INR (Nat.pred n) = n - 1 ).
    { rewrite -Nat.sub_1_r.
      rewrite minus_INR; auto.
      assert ((IZR Z0) = INR 0) as Hrw; [simpl; auto | ].
      rewrite Hrw in Hn1.
      apply INR_lt in Hn1.
      lia.
    }
    rewrite /rws_rsm_fun.
    do 3 (rewrite bool_decide_eq_true_2; [ | lra]).
    nra.
  Qed.

  Program Instance rws_rsm : rsm rws_rsm_fun 0.5.
  Next Obligation. apply rws_rsm_fun_nneg. Qed.
  Next Obligation. lra. Qed.
  Next Obligation.
    intros a H; rewrite /step/=/brw_step.
    apply to_final_None_1 in H.
    apply brw_to_final_None in H.
    case_bool_decide; [lra | ].
    case_match; [simpl in H; lra | ].
    rewrite /fair_conv_comb fair_coin_dbind_mass.
    do 2 rewrite dret_mass; lra.
  Qed.
  Next Obligation.
   intros a H; rewrite /is_final/=/brw_to_final; auto.
   case_bool_decide as H1; auto.
   case_match; simplify_eq; auto.
   rewrite /rws_rsm_fun in H.
   pose proof (pos_INR N).
   pose proof (pos_INR_S m).
   case_bool_decide as H3; auto.
   - apply Rnot_le_gt in H1. nra.
   - lra.
  Qed.
  Next Obligation.
    intros.
    rewrite /ex_expval /rws_rsm_fun.
    apply (ex_seriesC_ext (λ a0 : mstate bounded_random_walk, if bool_decide (a0 <= N) then (step a a0) * a0 * (N - a0) else 0 )).
    { intro n. case_bool_decide; lra. }
    apply ex_seriesC_nat_bounded_Rle.
  Qed.
  Next Obligation.
   intros a H.
   apply to_final_None_1 in H.
   apply brw_to_final_None in H.
   destruct H.
   rewrite /step/=/brw_step.
   rewrite bool_decide_eq_false_2; auto; try lra.
   case_match; [ simpl in H; lra |].
   rewrite /fair_conv_comb.
   rewrite Expval_dbind.
   - rewrite Expval_fair_coin.
     do 2 rewrite Expval_dret.
     rewrite -{2}(Nat.pred_succ m).
     by apply rws_rsm_dec.
   - apply rws_rsm_fun_nneg.
   - rewrite /ex_expval.
     eapply (ex_seriesC_le _ rws_rsm_fun).
     + intro n. pose proof (rws_rsm_fun_nneg n). real_solver.
     + rewrite /rws_rsm_fun. apply ex_seriesC_nat_bounded_Rle.
  Qed.

  Lemma bounded_random_walk_terminates (p : mstate bounded_random_walk) :
    SeriesC (lim_exec p) = 1.
  Proof. by eapply (rsm_term_limexec). Qed.
  
End brw.
