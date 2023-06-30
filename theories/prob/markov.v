From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Lim_seq.
From clutch.prob Require Import distribution couplings.

Class markov (A B : Type) `{Countable A} := Markov {
  step     : A → distr A;
  to_final : A → option B;

  to_final_is_final a a' :
    is_Some (to_final a) → step a a' = 0;
}.

Section is_final.
  Context `{markov A B}.

  Definition is_final (a : A) := is_Some (to_final a).

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

  Lemma is_final_dzero a : is_final a → step a = dzero.
  Proof.
    intros Hf.
    apply distr_ext=> a'.
    rewrite to_final_is_final //.
  Qed.
  
End is_final.

Global Hint Extern 0 (is_final _) => eapply to_final_Some_2 : markov.
Global Hint Extern 0 (¬ is_final _) => apply to_final_None_2 : markov.
Global Hint Extern 0 (to_final _ = None) => apply to_final_None_1  : markov.
Global Hint Extern 0 (∃ _, to_final _ = Some _) => apply to_final_Some_2 : markov.

(** Strict partial evaluation  *)
Section stepN.
  Context {A B : Type} `{markov A B}.
  Implicit Types a : A.

  Definition stepN (n : nat) (a : A) : distr A := iterM n step a.
                                                        
  Lemma stepN_O a :
    stepN 0 a = dret a. 
  Proof. done. Qed.

  Lemma stepN_Sn a n :
    stepN (S n) a = step a ≫= stepN n.
  Proof. done. Qed.

  Lemma stepN_plus (a : A) (n m : nat) :
    stepN (n + m) a = stepN n a ≫= stepN m.
  Proof. apply iterM_plus. Qed.

  Lemma stepN_Sn_inv n a0 a2 :
    stepN (S n) a0 a2 > 0 →
    ∃ a1, step a0 a1 > 0 ∧ stepN n a1 a2 > 0.
  Proof. intros (?&?&?)%dbind_pos. eauto. Qed. 

  Lemma stepN_det_steps n m a1 a2 :
    stepN n a1 a2 = 1 →
    stepN n a1 ≫= stepN m = stepN m a2.
  Proof. intros ->%pmf_1_eq_dret. rewrite dret_id_left //. Qed.  
          
End stepN. 

(** Non-strict partial evaluation *)
Section pexec.
  Context {A B : Type} `{Countable A, !markov A B}.
  Implicit Types a : A.
  Implicit Types b : B.

  Definition step_or_final a : distr A :=
    match to_final a with
    | Some _ => dret a
    | None => step a
    end.

  Lemma step_or_final_no_final a :
    ¬ is_final a → step_or_final a = step a.
  Proof. rewrite /step_or_final /is_final /= -eq_None_not_Some. by intros ->. Qed.

  Lemma step_or_final_is_final a :
    is_final a → step_or_final a = dret a.
  Proof. rewrite /step_or_final /=. by intros [? ->]. Qed.

  Definition pexec (n : nat) a : distr A := iterM n step_or_final a.

  Lemma pexec_O a :
    pexec 0 a = dret a.
  Proof. done. Qed.

  Lemma pexec_Sn a n :
    pexec (S n) a = step_or_final a ≫= pexec n.
  Proof. done. Qed.

  Lemma pexec_plus ρ n m :
    pexec (n + m) ρ = pexec n ρ ≫= pexec m.
  Proof. rewrite /pexec iterM_plus //.  Qed.

  Lemma pexec_1 :
    pexec 1 = step_or_final.
  Proof.
    extensionality a.
    rewrite pexec_Sn /pexec /= dret_id_right //.
  Qed.

  Lemma pexec_Sn_r a n :
    pexec (S n) a = pexec n a ≫= step_or_final.
  Proof.
    assert (S n = n + 1)%nat as -> by lia.
    rewrite pexec_plus pexec_1 //.
  Qed.

  Lemma pexec_is_final n a :
    is_final a → pexec n a = dret a.
  Proof.
    intros ?.
    induction n.
    - rewrite pexec_O //.
    - rewrite pexec_Sn step_or_final_is_final //.
      rewrite dret_id_left -IHn //. 
  Qed.

  Lemma pexec_no_final a n :
    ¬ is_final a →
    pexec (S n) a = step a ≫= pexec n.
  Proof. intros. rewrite pexec_Sn step_or_final_no_final //. Qed. 

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
  

End pexec.

Global Arguments pexec {_ _ _ _ _} _ _ : simpl never.

(** Stratified evaluation to a final state *)
Section exec.
  Context {A B : Type} `{Countable A, Countable B, !markov A B}.
  Implicit Types a : A.
  Implicit Types b : B.

  Fixpoint exec (n : nat) (a : A) {struct n} : distr B :=
    match to_final a, n with
      | Some b, _ => dret b
      | None, 0 => dzero
      | None, S n => step a ≫= exec n
    end.

  Lemma exec_unfold (n : nat) :
    exec n = λ a,
      match to_final a, n with
      | Some b, _ => dret b
      | None, 0 => dzero
      | None, S n => step a ≫= exec n
      end.
  Proof. by destruct n. Qed.

  Lemma exec_is_final a b n :
    to_final a = Some b → exec n a = dret b.
  Proof. destruct n; simpl; by intros ->. Qed.

  Lemma exec_Sn a n :
    exec (S n) a = step_or_final a ≫= exec n.
  Proof.
    rewrite /step_or_final /=.
    case_match; [|done].
    rewrite dret_id_left -/exec.
    by erewrite exec_is_final.
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

End exec.

(** Full evaluation to a final state *)
Section lim_exec.
  Context {A B : Type} `{Countable A, Countable B, !markov A B}.
  Implicit Types a : A.
  Implicit Types b : B.

  Definition lim_exec (a : A) : distr B := lim_distr (λ n, exec n a) (exec_mono a).

  Lemma lim_exec_unfold a b :
    lim_exec a b = Sup_seq (λ n, (exec n a) b).
  Proof. apply lim_distr_pmf. Qed.

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

End lim_exec.
