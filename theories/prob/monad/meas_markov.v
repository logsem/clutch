Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz Logic.FunctionalExtensionality Program.Wf Reals.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp classical_sets.
From iris.prelude Require Import options.
From iris.algebra Require Import ofe.
From clutch.bi Require Import weakestpre.
From mathcomp.analysis Require Import reals measure ereal Rstruct.
From clutch.prob.monad Require Export laws.
Set Warnings "hiding-delimiting-key".
(*From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Lim_seq.
From clutch.prob Require Import distribution couplings couplings_app mdp.
*)
Set Default Proof Using "Type*".

Notation giryM := (giryM (R := R)).

(** * Markov Chains *)
Section meas_markov_mixin.
  Context {mstate_disp mstate_ret_disp : measure_display}.
  Context {mstate : measurableType mstate_disp}.
  Context {mstate_ret : measurableType mstate_ret_disp}.
  Context (step : mstate → giryM mstate).
  Context (to_final : mstate → option mstate_ret).

  Record MeasMarkovMixin := {
    mixin_step_meas : measurable_fun setT step;
    mixin_to_final_meas : measurable_fun setT to_final;
    mixin_to_final_is_final a :
      is_Some (to_final a) → is_zero (step a);
  }.
End meas_markov_mixin.

Structure meas_markov := MeasMarkov {
  mstate_disp : measure_display;
  mstate_ret_disp : measure_display;
  mstate : measurableType mstate_disp ;
  mstate_ret : measurableType mstate_ret_disp ;
  step     : mstate → giryM mstate;
  to_final : mstate → option mstate_ret;
  markov_mixin : MeasMarkovMixin step to_final;
}.

#[global] Arguments MeasMarkov {_ _ _ _} _ _ _.
#[global] Arguments step {_}.
#[global] Arguments to_final {_}.

(*
Definition markov_mdp_mixin (m : markov):
  MdpMixin (λ (x:()) s, m.(step) s) (m.(to_final)).
Proof.
  constructor.
  intros.
  by apply markov_mixin.
Qed.

Canonical Structure markov_mdp (m : markov) := Mdp _ _ (markov_mdp_mixin m).
*)


Section is_final.
  Context {δ : meas_markov}.
  Implicit Types a : mstate δ.
  Implicit Types b : mstate_ret δ.

  Lemma step_meas : measurable_fun setT (@step δ).
  Proof. apply markov_mixin. Qed.

  Lemma to_final_meas : measurable_fun setT (@to_final δ).
  Proof. apply markov_mixin. Qed.

  Lemma to_final_is_final a :
    is_Some (to_final a) → is_zero (step a).
  Proof. apply markov_mixin. Qed.

  Definition is_final a := is_Some (to_final a).

  Lemma to_final_None a : ¬ is_final a ↔ to_final a = None.
  Proof. rewrite eq_None_not_Some //. Qed.

  Lemma to_final_None_1 a : ¬ is_final a → to_final a = None.
  Proof. apply to_final_None. Qed.

  Lemma to_final_None_2 a : to_final a = None → ¬ is_final a.
  Proof. apply to_final_None. Qed.

  Lemma to_final_Some a : is_final a ↔ ∃ b, to_final a = Some b.
  Proof. done. Qed.

  Lemma to_final_Some_1 a : is_final a → ∃ b, to_final a = Some b.
  Proof. done. Qed.

  Lemma to_final_Some_2 a b : to_final a = Some b → is_final a.
  Proof. intros. by eexists. Qed.

  Lemma is_final_dzero a : is_final a → is_zero (step a).
  Proof.
    intros Hf.
    by rewrite to_final_is_final //.
  Qed.

  (*
  #[global] Instance is_final_dec a : Decision (is_final a).
  Proof. rewrite /is_final. apply _. Qed.
   *)
End is_final.

#[global] Hint Immediate to_final_Some_2 to_final_None_2 to_final_None_1: core.

Section reducible.
  Context {δ : meas_markov}.
  Implicit Types a : mstate δ.

  Definition reducible a := ¬ is_zero (step a).
  Definition irreducible a := is_zero (step a).
  Definition stuck a := ¬ is_final a ∧ irreducible a.
  Definition not_stuck a := is_final a ∨ reducible a.

  Lemma not_reducible a  : ¬ reducible a ↔ irreducible a.
  Proof.
    unfold reducible, irreducible. split.
    { by apply classical.NNP_P. }
    { by apply classical.P_NNP. }
  Qed.

  Lemma reducible_not_final a :
    reducible a → ¬ is_final a.
  Proof. move=> H ?. apply H. by apply is_final_dzero. Qed.

  Lemma is_final_irreducible a : is_final a → irreducible a.
  Proof. by intros ?; rewrite /irreducible is_final_dzero //. Qed.

  Lemma not_not_stuck a : ¬ not_stuck a ↔ stuck a.
  Proof.
    rewrite /stuck /not_stuck -not_reducible.
    destruct (decide (is_final a)); naive_solver.
  Qed.

  (* Delete me *)
  Lemma irreducible_dzero a :
    irreducible a → is_zero (step a).
  Proof. done. Qed.

  Lemma reducible_not_stuck a :
    reducible a → not_stuck a.
  Proof. intros. by right. Qed.

  (*
  Lemma mass_pos_reducible a :
    SeriesC (step a) > 0 → reducible a.
  Proof. by intros ?%SeriesC_gtz_ex. Qed.

  Lemma reducible_mass_pos a :
    reducible a → SeriesC (step a) > 0.
  Proof.
    intros [a' Ha].
    eapply Rlt_le_trans; [done|].
    apply pmf_le_SeriesC.
  Qed.
  *)

End reducible.

Section markov.
  Context {δ : meas_markov}.
  Implicit Types a : mstate δ.
  Implicit Types b : mstate_ret δ.


  (** * Strict partial evaluation *)
  (* FIXME: Some of the bind lemmas might be in the wrong order. This is easier to prove so
     change it if matters. *)
  Program Definition stepN (n : nat) a : giryM (mstate δ) :=
    giryM_iterN n step a.

  Lemma stepN_meas (n : nat) : measurable_fun setT (stepN n).
  Proof. apply giryM_iterN_meas, step_meas. Qed.

  Lemma stepN_O : stepN 0 = giryM_ret.
  Proof. done. Qed.

  Lemma stepN_Sn a n :
    stepN (S n) a = giryM_bind_external (step a) (stepN n).
  Proof. done. Qed.

  Lemma stepN_1 a :
    stepN 1 a = step a.
  Proof. rewrite stepN_Sn stepN_O. (* dret_id_right //. Qed. *)  Admitted.

  Lemma stepN_plus a (n m : nat) :
    stepN (n + m) a = giryM_bind_external (stepN n a) (stepN m).
  Proof. Admitted.

  (*
    Generalize these ones to eval on sets?

  Lemma stepN_Sn_inv n a0 a2 :
    stepN (S n) a0 a2 > 0 →
    ∃ a1, step a0 a1 > 0 ∧ stepN n a1 a2 > 0.
  Proof. intros (?&?&?)%dbind_pos. eauto. Qed.

  Lemma stepN_det_steps n m a1 a2 :
    stepN n a1 a2 = 1 →
    stepN n a1 ≫= stepN m = stepN m a2.
  Proof. intros ->%pmf_1_eq_dret. rewrite dret_id_left //. Qed.

  Lemma stepN_det_trans n m a1 a2 a3 :
    stepN n a1 a2 = 1 →
    stepN m a2 a3 = 1 →
    stepN (n + m) a1 a3 = 1.
  Proof.
    rewrite stepN_plus.
    intros ->%pmf_1_eq_dret.
    replace (dret a2 ≫= _)
      with (stepN m a2); [|by rewrite dret_id_left].
    intros ->%pmf_1_eq_dret.
    by apply dret_1.
  Qed.
   *)

  (** * Non-strict partial evaluation *)
  Definition step_or_final a : giryM (mstate δ) :=
    match to_final a with
    | Some _ => giryM_ret a
    | None => step a
    end.

  Lemma step_or_final_meas : measurable_fun setT step_or_final.
  Proof. Admitted.

  Lemma step_or_final_no_final a :
    ¬ is_final a → step_or_final a = step a.
  Proof. rewrite /step_or_final /is_final /= -eq_None_not_Some. by intros ->. Qed.

  Lemma step_or_final_is_final a :
    is_final a → step_or_final a = giryM_ret a.
  Proof. rewrite /step_or_final /=. by intros [? ->]. Qed.

  Definition pexec (n : nat) a : giryM (mstate δ) := giryM_iterN n step_or_final a.

  Lemma pexec_meas (n : nat) : measurable_fun setT (pexec n).
  Proof. Admitted.

  Lemma pexec_O a :
    pexec 0 a = giryM_ret a.
  Proof. done. Qed.


  Lemma pexec_Sn a n :
    pexec (S n) a = giryM_bind_external (step_or_final a) (pexec n).
  Proof. done. Qed.

  Lemma pexec_plus ρ n m :
    pexec (n + m) ρ = giryM_bind_external (pexec n ρ) (pexec m).
  Proof. Admitted.

  Lemma pexec_1 :
    pexec 1 = step_or_final.
  Proof.
    rewrite /pexec//=.
    apply functional_extensionality.
    move=> x //=.
  Admitted.

  Lemma pexec_Sn_r a n :
    pexec (S n) a = giryM_bind_external (pexec n a) step_or_final.
  Proof.
    assert (S n = n + 1)%nat as -> by lia.
    rewrite pexec_plus.
    rewrite pexec_1 //.
  Qed.

  Lemma pexec_is_final n a :
    is_final a → pexec n a = giryM_ret a.
  Proof.
    intros ?.
    induction n.
    { by rewrite pexec_O //. }
    { rewrite pexec_Sn.
      (*
      rewrite -step_or_final_is_final. //.
      rewrite dret_id_left -IHn //.
      *)
      admit.
    }
  Admitted.

  Lemma pexec_no_final a n :
    ¬ is_final a →
    pexec (S n) a = giryM_bind_external (step a) (pexec n).
  Proof. intros. rewrite pexec_Sn step_or_final_no_final //. Qed.

  (*
  Lemma pexec_det_step n a1 a2 a0 :
    step a1 a2 = 1 →
    pexec n a0 a1 = 1 →
    pexec (S n) a0 a2 = 1.
  Proof.
    rewrite pexec_Sn_r.
    intros Hs ->%pmf_1_eq_dret.
    rewrite dret_id_left /=.
    case_match; [|done].
    assert (step a1 a2 = 0) as Hns; [by eapply to_final_is_final|].
    lra.
  Qed.

  Lemma pexec_det_steps n m a1 a2 :
    pexec n a1 a2 = 1 →
    pexec n a1 ≫= pexec m = pexec m a2.
  Proof. intros ->%pmf_1_eq_dret. rewrite dret_id_left //. Qed.

  Lemma stepN_pexec_det n x y:
    stepN n x y = 1 → pexec n x y = 1.
  Proof.
    rewrite /stepN /pexec.
    intros H.
    apply Rle_antisym; [done|].
    rewrite -H.
    apply iterM_mono => a a'.
    destruct (decide (is_final a)).
    - rewrite to_final_is_final //.
    - rewrite step_or_final_no_final //.
  Qed.
*)

  (** * Stratified evaluation to a final state *)
  Fixpoint exec (n : nat) (a : mstate δ) {struct n} : giryM (mstate_ret δ) :=
    match to_final a, n with
      | Some b, _ => giryM_ret b
      | None, 0 => giryM_zero
      | None, S n => giryM_bind_external (step a) (exec n)
    end.

  Lemma exec_unfold (n : nat) :
    exec n = λ a,
      match to_final a, n with
      | Some b, _ => giryM_ret b
      | None, 0 => giryM_zero
      | None, S n => giryM_bind_external (step a) (exec n)
      end.
  Proof. by destruct n. Qed.

  Lemma exec_is_final a b n :
    to_final a = Some b → exec n a = giryM_ret b.
  Proof. destruct n; simpl; by intros ->. Qed.

  Lemma exec_Sn a n :
    exec (S n) a = giryM_bind_external (step a) (exec n).
  Proof.
    rewrite /step_or_final /=.
    case_match; [|done].
  Admitted.
  (*
    rewrite dret_id_left -/exec.
    by erewrite exec_is_final.
  Qed.
*)

  Lemma exec_plus a n1 n2 :
    exec (n1 + n2) a = giryM_bind_external (pexec n1 a) (exec n2).
  Proof.
    revert a. induction n1.
    { intro a. rewrite pexec_O. admit. (* dret_id_left //. *) }
    { admit.
      (*
      intro a. replace ((S n1 + n2)%nat) with ((S (n1 + n2))); auto.
      rewrite exec_Sn pexec_Sn.
      apply distr_ext.
      intro.
      rewrite -dbind_assoc.
      rewrite /pmf/=/dbind_pmf.
      by setoid_rewrite IHn1.
      *)
      }
  Admitted.

  (*
  Lemma exec_pexec_relate a n:
    exec n a = pexec n a ≫=
                 (λ e, match to_final e with
                             | Some b => dret b
                             | _ => dzero
                       end).
  Proof.
    revert a.
    induction n; intros a.
    - simpl. rewrite pexec_O.
      rewrite dret_id_left'.
      done.
    - simpl. rewrite pexec_Sn.
      rewrite -dbind_assoc'.
      case_match eqn:H.
      + rewrite step_or_final_is_final; last by eapply to_final_Some_2.
        rewrite dret_id_left'.
        rewrite pexec_is_final; last by eapply to_final_Some_2.
        rewrite dret_id_left'. rewrite H. done.
      + rewrite step_or_final_no_final; last by eapply to_final_None_2.
        apply dbind_ext_right. done.
  Qed.

  Lemma exec_mono a n v :
    exec n a v <= exec (S n) a v.
  Proof.
    apply refRcoupl_eq_elim.
    move : a.
    induction n.
    - intros.
      apply refRcoupl_from_leq.
      intros b. rewrite /distr_le /=.
      by case_match.
    - intros; do 2 rewrite exec_Sn.
      eapply refRcoupl_dbind; [|apply refRcoupl_eq_refl].
      by intros ? ? ->.
  Qed.

  Lemma exec_mono' ρ n m v :
    n ≤ m → exec n ρ v <= exec m ρ v.
  Proof.
    eapply (mon_succ_to_mon (λ x, exec x ρ v)).
    intro. apply exec_mono.
  Qed.

  Lemma exec_mono_term a b n m :
    SeriesC (exec n a) = 1 →
    n ≤ m →
    exec m a b = exec n a b.
  Proof.
    intros Hv Hleq.
    apply Rle_antisym; [ |by apply exec_mono'].
    destruct (decide (exec m a b <= exec n a b))
      as [|?%Rnot_le_lt]; [done|].
    exfalso.
    assert (1 < SeriesC (exec m a)); last first.
    - assert (SeriesC (exec m a) <= 1); [done|]. lra.
    - rewrite -Hv.
      apply SeriesC_lt; eauto.
      intros b'. by split; [|apply exec_mono'].
  Qed.

  Lemma exec_O_not_final a :
    ¬ is_final a →
    exec 0 a = dzero.
  Proof. intros ?%to_final_None_1 =>/=; by case_match. Qed.

  Lemma exec_Sn_not_final a n :
    ¬ is_final a →
    exec (S n) a = step a ≫= exec n.
  Proof. intros ?. rewrite exec_Sn step_or_final_no_final //. Qed.

  Lemma pexec_exec_le_final n a a' b :
    to_final a' = Some b →
    pexec n a a' <= exec n a b.
  Proof.
    intros Hb.
    revert a. induction n; intros a.
    - rewrite pexec_O.
      destruct (decide (a = a')) as [->|].
      + erewrite exec_is_final; [|done].
        rewrite !dret_1_1 //.
      + rewrite dret_0 //.
    - rewrite exec_Sn pexec_Sn.
      destruct (decide (is_final a)).
      + rewrite step_or_final_is_final //.
        rewrite 2!dret_id_left -/exec.
        apply IHn.
      + rewrite step_or_final_no_final //.
        rewrite /pmf /= /dbind_pmf.
        eapply SeriesC_le.
        * intros a''. split; [by apply Rmult_le_pos|].
          by apply Rmult_le_compat.
        * eapply pmf_ex_seriesC_mult_fn.
          exists 1. by intros ρ.
  Qed.

  Lemma pexec_exec_det n a a' b :
    to_final a' = Some b →
    pexec n a a' = 1 → exec n a b = 1.
  Proof.
    intros Hf.
    pose proof (pexec_exec_le_final n a a' b Hf).
    pose proof (pmf_le_1 (exec n a) b).
    lra.
  Qed.

  Lemma exec_pexec_val_neq_le n m a a' b b' :
    to_final a' = Some b' →
    b ≠ b' → exec m a b + pexec n a a' <= 1.
  Proof.
    intros Hf Hneq.
    etrans; [by apply Rplus_le_compat_l, pexec_exec_le_final|].
    etrans; [apply Rplus_le_compat_l, (exec_mono' _ n (n `max` m)), Nat.le_max_l|].
    etrans; [apply Rplus_le_compat_r, (exec_mono' _ m (n `max` m)), Nat.le_max_r|].
    etrans; [|apply (pmf_SeriesC (exec (n `max` m) a))].
    by apply pmf_plus_neq_SeriesC.
  Qed.

  Lemma pexec_exec_det_neg n m a a' b b' :
    to_final a' = Some b' →
    pexec n a a' = 1 →
    b ≠ b' →
    exec m a b = 0.
  Proof.
    intros Hf Hexec Hv.
    pose proof (exec_pexec_val_neq_le n m a a' b b' Hf Hv) as Hle.
    rewrite Hexec in Hle.
    pose proof (pmf_pos (exec m a) b).
    lra.
  Qed.

  Lemma is_finite_Sup_seq_exec a b :
    is_finite (Sup_seq (λ n, exec n a b)).
  Proof.
    apply (Rbar_le_sandwich 0 1).
    - by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
    - by apply upper_bound_ge_sup=>/=.
  Qed.

  Lemma is_finite_Sup_seq_SeriesC_exec a :
    is_finite (Sup_seq (λ n, SeriesC (exec n a))).
  Proof.
    apply (Rbar_le_sandwich 0 1).
    - by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
    - by apply upper_bound_ge_sup=>/=.
  Qed.

*)



  (** * Full evaluation (limit of stratification)
  Definition lim_exec (a : mstate δ) : distr (mstate_ret δ) := lim_distr (λ n, exec n a) (exec_mono a).
*)



  (*
  Lemma lim_exec_unfold a b :
    lim_exec a b = Sup_seq (λ n, (exec n a) b).
  Proof. apply lim_distr_pmf. Qed.

  Lemma lim_exec_Sup_seq a :
    SeriesC (lim_exec a) = Sup_seq (λ n, SeriesC (exec n a)).
  Proof.
    erewrite SeriesC_ext; last first.
    { intros ?. rewrite lim_exec_unfold //. }
    erewrite MCT_seriesC; eauto.
    - intros. apply exec_mono.
    - intros. by eapply SeriesC_correct.
    - rewrite (Rbar_le_sandwich 0 1).
      + apply Sup_seq_correct.
      + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
      + by apply upper_bound_ge_sup=>/=.
  Qed.

  Lemma lim_exec_step a :
    lim_exec a = step_or_final a ≫= lim_exec.
  Proof.
   apply distr_ext.
   intro b.
   rewrite {2}/pmf /= /dbind_pmf.
   rewrite lim_exec_unfold.
   setoid_rewrite lim_exec_unfold.
   assert
     (SeriesC (λ a', step_or_final a a' * Sup_seq (λ n, exec n a' b)) =
      SeriesC (λ a', Sup_seq (λ n, step_or_final a a' * exec n a' b))) as ->.
   { apply SeriesC_ext; intro b'.
     apply eq_rbar_finite.
     rewrite rmult_finite.
     rewrite (rbar_finite_real_eq).
     - rewrite -Sup_seq_scal_l //.
     - apply (Rbar_le_sandwich 0 1).
       + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
       + by apply upper_bound_ge_sup=>/=. }
   rewrite (MCT_seriesC _ (λ n, exec (S n) a b) (lim_exec a b)) //.
   - intros. by apply Rmult_le_pos.
   - intros.
     apply Rmult_le_compat; [done|done|done|].
     apply exec_mono.
   - intros a'.
     exists (step_or_final a a').
     intros n.
     rewrite <- Rmult_1_r. by apply Rmult_le_compat_l.
   - intro n.
     rewrite exec_Sn.
     rewrite {3}/pmf/=/dbind_pmf.
     apply SeriesC_correct.
     apply (ex_seriesC_le _ (step_or_final a)); [|done].
     intros a'. split.
     + by apply Rmult_le_pos.
     + rewrite <- Rmult_1_r. by apply Rmult_le_compat_l.
   - rewrite lim_exec_unfold.
     rewrite mon_sup_succ.
     + rewrite (Rbar_le_sandwich 0 1).
       * apply Sup_seq_correct.
       * by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
       * by apply upper_bound_ge_sup=>/=.
     + intro; apply exec_mono.
  Qed.

  Lemma lim_exec_pexec n a :
    lim_exec a = pexec n a ≫= lim_exec.
  Proof.
    move : a.
    induction n; intro a.
    - rewrite pexec_O dret_id_left //.
    - rewrite pexec_Sn -dbind_assoc/=.
      rewrite lim_exec_step.
      apply dbind_eq; [|done].
      intros ??. apply IHn.
  Qed.

  Lemma lim_exec_det_final n a a' b :
    to_final a' = Some b →
    pexec n a a' = 1 →
    lim_exec a = dret b.
  Proof.
    intros Hb Hpe.
    apply distr_ext.
    intro b'.
    rewrite lim_exec_unfold.
    rewrite {2}/pmf /= /dret_pmf.
    case_bool_decide; simplify_eq.
    - apply Rle_antisym.
      + apply finite_rbar_le; [eapply is_finite_Sup_seq_exec|].
        by apply upper_bound_ge_sup=>/=.
      + apply rbar_le_finite; [eapply is_finite_Sup_seq_exec|].
        apply (Sup_seq_minor_le _ _ n)=>/=.
        by erewrite pexec_exec_det.
    - rewrite -(sup_seq_const 0).
      f_equal. apply Sup_seq_ext=> m.
      f_equal. by eapply pexec_exec_det_neg.
  Qed.

  Lemma lim_exec_final a b :
    to_final a = Some b →
    lim_exec a = dret b.
  Proof.
    intros. erewrite (lim_exec_det_final 0%nat); [done|done|].
    rewrite pexec_O. by apply dret_1_1.
  Qed.

  Lemma lim_exec_not_final a :
    ¬ is_final a →
    lim_exec a = step a ≫= lim_exec.
  Proof.
    intros Hn. rewrite lim_exec_step step_or_final_no_final //.
  Qed.

  Lemma lim_exec_leq a b (r : R) :
    (∀ n, exec n a b <= r) →
    lim_exec a b <= r.
  Proof.
    intro Hexec.
    rewrite lim_exec_unfold.
    apply finite_rbar_le; [apply is_finite_Sup_seq_exec|].
    by apply upper_bound_ge_sup=>/=.
  Qed.

  Lemma lim_exec_leq_mass  a r :
    (∀ n, SeriesC (exec n a) <= r) →
    SeriesC (lim_exec a) <= r.
  Proof.
    intro Hm.
    erewrite SeriesC_ext; last first.
    { intros. rewrite lim_exec_unfold //. }
    erewrite (MCT_seriesC _ (λ n, SeriesC (exec n a)) (Sup_seq (λ n, SeriesC (exec n a)))); eauto.
    - apply finite_rbar_le; [apply is_finite_Sup_seq_SeriesC_exec|].
      by apply upper_bound_ge_sup.
    - apply exec_mono.
    - intros. by apply SeriesC_correct.
    - rewrite (Rbar_le_sandwich 0 1).
      + apply (Sup_seq_correct (λ n, SeriesC (exec n a))).
      + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
      + by apply upper_bound_ge_sup=>/=.
  Qed.

  Lemma lim_exec_term n a :
    SeriesC (exec n a) = 1 →
    lim_exec a = exec n a.
  Proof.
    intro Hv.
    apply distr_ext=> b.
    rewrite lim_exec_unfold.
    apply Rle_antisym.
    - apply finite_rbar_le; [apply is_finite_Sup_seq_exec|].
      rewrite -/pmf.
      apply upper_bound_ge_sup.
      intros n'.
      destruct (decide (n <= n')) as [|?%Rnot_le_lt].
      + right. apply exec_mono_term; [done|]. by apply INR_le.
      + apply exec_mono'. apply INR_le. by left.
    - apply rbar_le_finite; [apply is_finite_Sup_seq_exec|].
      apply (sup_is_upper_bound (λ m, exec m a b) n).
  Qed.

  Lemma lim_exec_pos a b :
    lim_exec a b > 0 → ∃ n, exec n a b > 0.
  Proof.
    intros.
    apply Classical_Pred_Type.not_all_not_ex.
    intros H'.
    assert (lim_exec a b <= 0); [|lra].
    apply lim_exec_leq => n.
    by apply Rnot_gt_le.
  Qed.

  Lemma lim_exec_continuous_prob a ϕ r :
    (∀ n, prob (exec n a) ϕ <= r) →
    prob (lim_exec a) ϕ <= r.
  Proof.
    intro Hm.
    rewrite /prob.
    erewrite SeriesC_ext; last first.
    { intro; rewrite lim_exec_unfold; auto. }
    assert
      (forall v, (if ϕ v then real (Sup_seq (λ n0 : nat, exec n0 a v)) else 0) =
                 (real (Sup_seq (λ n0 : nat, if ϕ v then exec n0 a v else 0)))) as Haux.
    { intro v.
      destruct (ϕ v); auto.
      rewrite sup_seq_const //.
    }
    assert
      (is_finite (Sup_seq (λ n0 : nat, SeriesC (λ v, if ϕ v then exec n0 a v else 0)))) as Hfin.
    {
      apply (Rbar_le_sandwich 0 1).
      + apply (Sup_seq_minor_le _ _ 0%nat); simpl.
        apply SeriesC_ge_0'.
        intro v; destruct (ϕ v); auto.
        lra.
      + apply upper_bound_ge_sup; intro; simpl; auto.
        apply (Rle_trans _ (SeriesC (exec n a))); auto.
        apply (SeriesC_le _ (exec n a)); auto.
        intro v; destruct (ϕ v); real_solver.
    }
    erewrite SeriesC_ext; last first.
    {
      intro; rewrite Haux //.
    }
    erewrite (MCT_seriesC _ (λ n, SeriesC (λ v, if ϕ v then exec n a v else 0))
                (Sup_seq (λ n0 : nat, SeriesC (λ v, if ϕ v then exec n0 a v else 0))));
      auto.
    - apply finite_rbar_le; auto.
      apply upper_bound_ge_sup; auto.
    - intros n v.
      destruct (ϕ v); auto.
      lra.
    - intros n v.
      destruct (ϕ v); [ apply exec_mono | lra].
    - intro v; destruct (ϕ v); exists 1; intro; auto; lra.
    - intros n.
      apply SeriesC_correct; auto.
      apply (ex_seriesC_le _ (exec n a)); auto.
      intro v; destruct (ϕ v); real_solver.
    - rewrite (Rbar_le_sandwich 0 1); auto.
      + apply (Sup_seq_correct (λ n0 : nat, SeriesC (λ v, if ϕ v then exec n0 a v else 0))).
      + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
        apply SeriesC_ge_0'.
        intro v; destruct (ϕ v); real_solver.
      + apply upper_bound_ge_sup; intro; simpl; auto.
        apply (Rle_trans _ (SeriesC (exec n a))); auto.
        apply (SeriesC_le _ (exec n a)); auto.
        intro v; destruct (ϕ v); real_solver.
  Qed.

**)
End markov.
#[global] Arguments pexec {_} _ _ : simpl never.
