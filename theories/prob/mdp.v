From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Lim_seq.
From coneris.prob Require Import distribution couplings.
Set Default Proof Using "Type*".

(** * Markov decision process *)
Section mdp_mixin.
  Context `{Countable mdpstate, Countable mdpstate_ret, Countable mdpaction}.
  Context (step : mdpaction -> mdpstate → distr mdpstate).
  Context (to_final : mdpstate → option mdpstate_ret).

  Record MdpMixin := {
      mixin_to_final_is_final a :
      is_Some (to_final a) → ∀ ac a', step ac a a' = 0;
    }.
End mdp_mixin.

Structure mdp := Mdp {
                     mdpstate : Type;
                     mdpstate_ret : Type;
                     mdpaction : Type;
                     
                     mdpstate_eqdec : EqDecision mdpstate;
                     mdpstate_count : Countable mdpstate;
                     mdpstate_ret_eqdec : EqDecision mdpstate_ret;
                     mdpstate_ret_count : Countable mdpstate_ret;
                     mdpaction_eqdec : EqDecision mdpaction;
                     mdpaction_count : Countable mdpaction;

                     step     : mdpaction -> mdpstate → distr mdpstate;
                     to_final : mdpstate → option mdpstate_ret;

                     mdp_mixin : MdpMixin step to_final;
                   }.
#[global] Arguments Mdp {_ _ _ _ _ _ _ _ _} _ _ _.
#[global] Arguments step {_}.
#[global] Arguments to_final {_}.

#[global] Existing Instance mdpstate_eqdec.
#[global] Existing Instance mdpstate_count.
#[global] Existing Instance mdpstate_ret_eqdec.
#[global] Existing Instance mdpstate_ret_count.
#[global] Existing Instance mdpaction_eqdec.
#[global] Existing Instance mdpaction_count.

Section scheduler.
  Context {δ : mdp}.
  Context `{Hsch_state: Countable sch_state}.
  Record scheduler:= {
      scheduler_f :> (sch_state * mdpstate δ) -> distr (sch_state * mdpaction δ)
    }.
  
  Definition sch_int_state_f (s:scheduler) ρ := lmarg (s ρ).
  Definition sch_action_f (s:scheduler) ρ := rmarg (s ρ).

  
  Section is_final.
    Implicit Types a : mdpstate δ.
    Implicit Types b : mdpstate_ret δ.

    Lemma to_final_is_final a :
      is_Some (to_final a) → ∀ ac a', step ac a a' = 0.
    Proof. apply mdp_mixin. Qed.

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

    Lemma is_final_dzero a ac : is_final a → step ac a = dzero.
    Proof.
      intros Hf.
      apply distr_ext=> a'.
      rewrite to_final_is_final //.
    Qed.

    #[global] Instance is_final_dec a : Decision (is_final a).
    Proof. rewrite /is_final. apply _. Qed.
    
  End is_final.


  (** Everything below is dependent on an instance of a scheduler (and an mdp) 0*)
  Context (sch:scheduler).

  
  Section reducible.
    Implicit Types ρ : sch_state * mdpstate δ.

    Definition reducible ρ := ∃ ac a', sch_action_f sch ρ ac > 0 /\ step ac ρ.2 a' > 0.
    Definition irreducible ρ := ∀ ac a', sch_action_f sch ρ ac = 0 \/ step ac ρ.2 a' = 0.
    Definition stuck a := ¬ is_final a.2 ∧ irreducible a.
    Definition not_stuck a := is_final a.2 ∨ reducible a.

    Lemma not_reducible a  : ¬ reducible a ↔ irreducible a.
    Proof.
      rewrite /reducible /irreducible. split.
      - intros H ac a'.
        apply (not_exists_forall_not _ _) with ac in H.
        apply (not_exists_forall_not _ _) with a' in H.
        apply not_and_or_not in H as [|].
        + left. pose proof pmf_pos (sch_action_f sch a) ac.
          lra.
        + right. pose proof pmf_pos (step ac a.2) a'.
          lra.
      - intros H [x[x'[]]]. 
        specialize (H x x') as [|]; lra.
    Qed.

    Lemma reducible_not_final a :
      reducible a → ¬ is_final a.2.
    Proof. move => [] a' /[swap] /is_final_dzero -> []?[]??. inv_distr. Qed.

    Lemma is_final_irreducible a : is_final a.2 → irreducible a.
    Proof. intros ??. rewrite is_final_dzero //. naive_solver. Qed.

    Lemma not_not_stuck a : ¬ not_stuck a ↔ stuck a.
    Proof.
      rewrite /stuck /not_stuck -not_reducible.
      destruct (decide (is_final a.2)); naive_solver.
    Qed.

    (* Lemma irreducible_dzero a ac: *)
    (*   irreducible a → step ac a = dzero. *)
    (* Proof. *)
    (*   intros Hirr%not_reducible. apply dzero_ext=> a'. *)
    (*   destruct (decide (step ac a a' = 0)); [done|]. *)
    (*   exfalso. eapply Hirr. *)
    (*   exists ac, a'. *)
    (*   pose proof (pmf_le_1 (step ac a) a'). *)
    (*   pose proof (pmf_pos (step ac a) a'). *)
    (*   lra. *)
    (* Qed. *)

    Lemma reducible_not_stuck a :
      reducible a → not_stuck a.
    Proof. intros. by right. Qed.

    (* Lemma mass_pos_reducible a ac : *)
    (*   SeriesC (step ac a) > 0 → reducible a. *)
    (* Proof. intros [??]%SeriesC_gtz_ex; try done. *)
    (*        rewrite /reducible. naive_solver. *)
    (* Qed. *)

    (* Lemma reducible_mass_pos a ac : *)
    (*   reducible a → SeriesC (step ac a.2) > 0. *)
    (* Proof. *)
    (*   intros [a' [Ha []]]. *)
    (*   eapply Rlt_le_trans; [done|]. *)
    (*   apply pmf_le_SeriesC. *)
    (* Qed. *)
  End reducible.

  Section step.
    (* sch_step takes a strict step and returns the whole configuration, including the sch state *)
    Definition sch_step (ρ:sch_state*mdpstate δ) : distr(sch_state*mdpstate δ) :=
      sch ρ ≫= (λ '(sch_σ', mdp_a), dmap (λ mdp_σ', (sch_σ', mdp_σ')) (step mdp_a ρ.2)).

    Definition sch_stepN (n:nat) p := iterM n sch_step p.

    Lemma sch_stepN_O :
      sch_stepN 0 = dret.
    Proof. done. Qed.

    Lemma sch_stepN_Sn a n :
      sch_stepN (S n) a = sch_step a ≫= sch_stepN n.
    Proof. done. Qed.

    Lemma sch_stepN_1 a :
      sch_stepN 1 a = sch_step a.
    Proof. rewrite sch_stepN_Sn sch_stepN_O dret_id_right //. Qed.

    Lemma sch_stepN_plus a (n m : nat) :
      sch_stepN (n + m) a = sch_stepN n a ≫= sch_stepN m.
    Proof. apply iterM_plus. Qed.

    Lemma sch_stepN_Sn_inv n a0 a2 :
      sch_stepN (S n) a0 a2 > 0 →
      ∃ a1, sch_step a0 a1 > 0 ∧ sch_stepN n a1 a2 > 0.
    Proof. intros (?&?&?)%dbind_pos. eauto. Qed.

    Lemma sch_stepN_det_steps n m a1 a2 :
      sch_stepN n a1 a2 = 1 →
      sch_stepN n a1 ≫= sch_stepN m = sch_stepN m a2.
    Proof. intros ->%pmf_1_eq_dret. rewrite dret_id_left //. Qed.

    Lemma sch_stepN_det_trans n m a1 a2 a3 :
      sch_stepN n a1 a2 = 1 →
      sch_stepN m a2 a3 = 1 →
      sch_stepN (n + m) a1 a3 = 1.
    Proof.
      rewrite sch_stepN_plus.
      intros ->%pmf_1_eq_dret.
      replace (dret a2 ≫= _)
        with (sch_stepN m a2); [|by rewrite dret_id_left].
      intros ->%pmf_1_eq_dret.
      by apply dret_1.
    Qed.

    (* sch_step_or_final does a non-strict step, and returns whole configuration *)
    Definition sch_step_or_final a :=
      match to_final a.2 with
      | Some _ => dret a
      | None => sch_step a
      end.

    Lemma sch_step_or_final_is_final ρ:
      is_final ρ.2 -> sch_step_or_final ρ = dret ρ.
    Proof.
      rewrite /sch_step_or_final.
      by intros [? ->].
    Qed.

    Lemma sch_step_or_final_not_final ρ:
      ¬ is_final ρ.2 -> sch_step_or_final ρ = sch_step ρ.
    Proof.
      rewrite /sch_step_or_final.
      intros H. case_match; last done.
      exfalso. rewrite /is_final in H. naive_solver.
    Qed.

    Definition sch_pexec (n:nat) p := iterM n sch_step_or_final p.

    Lemma sch_pexec_fold n p:
      iterM n sch_step_or_final p = sch_pexec n p.
    Proof.
      done.
    Qed.

    Lemma sch_pexec_O a :
      sch_pexec 0 a = dret a.
    Proof. done. Qed.

    Lemma sch_pexec_Sn a n :
      sch_pexec (S n) a = sch_step_or_final a ≫= sch_pexec n.
    Proof. done. Qed.

    Lemma sch_pexec_plus ρ n m :
      sch_pexec (n + m) ρ = sch_pexec n ρ ≫= sch_pexec m.
    Proof. rewrite /sch_pexec iterM_plus //.  Qed.

    Lemma sch_pexec_1 :
      sch_pexec 1 = sch_step_or_final.
    Proof.
      extensionality a.
      rewrite sch_pexec_Sn /sch_pexec /= dret_id_right //.
    Qed.

    Lemma sch_pexec_Sn_r a n :
      sch_pexec (S n) a = sch_pexec n a ≫= sch_step_or_final.
    Proof.
      assert (S n = n + 1)%nat as -> by lia.
      rewrite sch_pexec_plus sch_pexec_1 //.
    Qed.

    Lemma sch_pexec_is_final n a :
      is_final a.2 → sch_pexec n a = dret a.
    Proof.
      intros H.
      induction n.
      - rewrite sch_pexec_O //.
      - erewrite sch_pexec_Sn, sch_step_or_final_is_final; last done.
        rewrite dret_id_left -IHn //.
    Qed.

    (* Lemma pexec_no_final a n : *)
    (*   ¬ is_final a → *)
    (*   pexec (S n) a = step a ≫= pexec n. *)
    (* Proof. intros. rewrite pexec_Sn step_or_final_no_final //. Qed. *)

    (* Lemma sch_pexec_det_step n a1 a2 a0 : *)
    (*   sch_step a1 a2 = 1 → *)
    (*   sch_pexec n a0 a1 = 1 → *)
    (*   sch_pexec (S n) a0 a2 = 1. *)
    (* Proof. *)
    (*   rewrite sch_pexec_Sn_r. *)
    (*   intros Hs ->%pmf_1_eq_dret. *)
    (*   rewrite dret_id_left /=. *)
    (*   case_match; [|done]. *)
    (*   assert (sch_step a1 a2 = 0) as Hns; [by eapply to_final_is_final|]. *)
    (*   lra. *)
    (* Qed. *)

    Lemma sch_pexec_det_steps n m a1 a2 :
      sch_pexec n a1 a2 = 1 →
      sch_pexec n a1 ≫= sch_pexec m = sch_pexec m a2.
    Proof. intros ->%pmf_1_eq_dret. rewrite dret_id_left //. Qed.

    (* Lemma sch_stepN_pexec_det n x y: *)
    (*   sch_stepN n x y = 1 → sch_pexec n x y = 1. *)
    (* Proof. *)
    (*   rewrite /sch_stepN /sch_pexec. *)
    (*   intros H'. *)
    (*   apply Rle_antisym; [done|]. *)
    (*   rewrite -H'. *)
    (*   apply iterM_mono => a a'. *)
    (*   destruct (decide (is_final a)). *)
    (*   - rewrite to_final_is_final //. *)
    (*   - rewrite step_or_final_no_final //. *)
    (* Qed. *)

    (* exec takes non-strict steps and returns the final mstate_ret,
     in a language setting, that's the value
     *)

    Fixpoint sch_exec (n:nat) (ρ : sch_state * mdpstate δ) {struct n} : distr (mdpstate_ret δ) :=
      let '(sch_σ, mdp_σ) := ρ in
      match to_final mdp_σ, n with
      | Some b, _ => dret b
      | None, 0 => dzero
      | None, S n => sch_step ρ ≫= sch_exec n
      end.

    Lemma sch_exec_is_final ρ b n :
      to_final ρ.2 = Some b → sch_exec n ρ = dret b.
    Proof. destruct ρ, n; simpl; by intros ->. Qed.

    Lemma sch_exec_Sn a n :
      sch_exec (S n) a = sch_step_or_final a ≫= sch_exec n.
    Proof.
      rewrite /sch_step_or_final /=.
      destruct a. simpl.
      case_match; [|done].
      rewrite dret_id_left -/sch_exec.
      by erewrite sch_exec_is_final.
    Qed.
    
    Lemma sch_exec_plus a n1 n2 :
      sch_exec (n1 + n2) a = sch_pexec n1 a ≫= sch_exec n2.
    Proof.
      revert a. induction n1.
      - intro a. rewrite sch_pexec_O dret_id_left //.
      - intro a. replace ((S n1 + n2)%nat) with ((S (n1 + n2))); auto.
        rewrite sch_exec_Sn sch_pexec_Sn.
        apply distr_ext.
        intro.
        rewrite -dbind_assoc.
        rewrite /pmf/=/dbind_pmf.
        by setoid_rewrite IHn1.
    Qed.

    Lemma sch_exec_pexec_relate a n:
      sch_exec n a = sch_pexec n a ≫=
                       (λ e, match to_final e.2 with
                             | Some b => dret b
                             | _ => dzero
                             end).
    Proof.
      revert a.
      induction n; intros [].
      - simpl. rewrite sch_pexec_O.
        rewrite dret_id_left'.
        done.
      - simpl. rewrite sch_pexec_Sn.
        rewrite -dbind_assoc'.
        case_match eqn:H.
        + erewrite sch_step_or_final_is_final; last by eapply to_final_Some_2. 
          rewrite dret_id_left'.
          rewrite sch_pexec_is_final; last by eapply to_final_Some_2.
          rewrite dret_id_left'. rewrite H. done.
        + rewrite sch_step_or_final_not_final; last by eapply to_final_None_2.
          apply dbind_ext_right. done.
    Qed.

    
    Lemma sch_exec_mono a n v :
      sch_exec n a v <= sch_exec (S n) a v.
    Proof.
      apply refRcoupl_eq_elim.
      move : a.
      induction n.
      - intros [].
        apply refRcoupl_from_leq.
        intros b. rewrite /distr_le /=.
        by case_match.
      - intros []; do 2 rewrite sch_exec_Sn.
        eapply refRcoupl_dbind; [|apply refRcoupl_eq_refl].
        by intros ? ? ->.
    Qed.

    Lemma sch_exec_mono' ρ n m v :
      n ≤ m → sch_exec n ρ v <= sch_exec m ρ v.
    Proof.
      eapply (mon_succ_to_mon (λ x, sch_exec x ρ v)).
      intro. apply sch_exec_mono.
    Qed.

    Lemma sch_exec_mono_term a b n m :
      SeriesC (sch_exec n a) = 1 →
      n ≤ m →
      sch_exec m a b = sch_exec n a b.
    Proof.
      intros Hv Hleq.
      apply Rle_antisym; [ |by apply sch_exec_mono'].
      destruct (decide (sch_exec m a b <= sch_exec n a b))
        as [|?%Rnot_le_lt]; [done|].
      exfalso.
      assert (1 < SeriesC (sch_exec m a)); last first.
      - assert (SeriesC (sch_exec m a) <= 1); [done|]. lra.
      - rewrite -Hv.
        apply SeriesC_lt; eauto.
        intros b'. by split; [|apply sch_exec_mono'].
    Qed.

    Lemma sch_exec_O_not_final a :
      ¬ is_final a.2 →
      sch_exec 0 a = dzero.
    Proof. destruct a. intros ?%to_final_None_1 =>/=. simpl in *. by case_match. Qed.

    Lemma sch_exec_Sn_not_final a n :
      ¬ is_final a.2 →
      sch_exec (S n) a = sch_step a ≫= sch_exec n.
    Proof. intros ?. rewrite sch_exec_Sn sch_step_or_final_not_final //. 
    Qed.

    Lemma sch_pexec_exec_le_final n a a' b :
      to_final a'.2 =Some b->
      sch_pexec n a a' <= sch_exec n a b.
    Proof.
      intros.
      revert a. induction n; intros a.
      - rewrite sch_pexec_O.
        destruct (decide (a = a')) as [->|].
        + erewrite sch_exec_is_final; last done.
          rewrite !dret_1_1 //.
        + rewrite dret_0 //.
      - rewrite sch_exec_Sn sch_pexec_Sn.
        destruct (decide (is_final a.2)) as [|].
        + erewrite sch_step_or_final_is_final; last done.
          rewrite 2!dret_id_left -/sch_exec.
          apply IHn.
        + rewrite sch_step_or_final_not_final //.
          rewrite /pmf /= /dbind_pmf.
          eapply SeriesC_le.
          * intros a''. split; [by apply Rmult_le_pos|].
            by apply Rmult_le_compat.
          * eapply pmf_ex_seriesC_mult_fn.
            exists 1. by intros ρ.
    Qed.

    Lemma sch_pexec_exec_det n a a' b :
      to_final a'.2 = Some b →
      sch_pexec n a a' = 1 → sch_exec n a b = 1.
    Proof.
      intros Hf.
      pose proof (sch_pexec_exec_le_final n a a' b Hf).
      pose proof (pmf_le_1 (sch_exec n a) b).
      lra.
    Qed.

    Lemma sch_exec_pexec_val_neq_le n m a a' b b' :
      to_final a'.2 = Some b' →
      b ≠ b' → sch_exec m a b + sch_pexec n a a' <= 1.
    Proof.
      intros Hf Hneq.
      etrans; [by apply Rplus_le_compat_l, sch_pexec_exec_le_final|].
      etrans; [apply Rplus_le_compat_l, (sch_exec_mono' _ n (n `max` m)), Nat.le_max_l|].
      etrans; [apply Rplus_le_compat_r, (sch_exec_mono' _ m (n `max` m)), Nat.le_max_r|].
      etrans; [|apply (pmf_SeriesC (sch_exec (n `max` m) a))].
      by apply pmf_plus_neq_SeriesC.
    Qed.

    Lemma sch_pexec_exec_det_neg n m a a' b b' :
      to_final a'.2 = Some b' →
      sch_pexec n a a' = 1 →
      b ≠ b' →
      sch_exec m a b = 0.
    Proof.
      intros Hf Hexec Hv.
      pose proof (sch_exec_pexec_val_neq_le n m a a' b b' Hf Hv) as Hle.
      rewrite Hexec in Hle.
      pose proof (pmf_pos (sch_exec m a) b).
      lra.
    Qed.

    Lemma is_finite_Sup_seq_sch_exec a b :
      is_finite (Sup_seq (λ n, sch_exec n a b)).
    Proof.
      apply (Rbar_le_sandwich 0 1).
      - by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
      - by apply upper_bound_ge_sup=>/=.
    Qed.

    Lemma is_finite_Sup_seq_SeriesC_sch_exec a :
      is_finite (Sup_seq (λ n, SeriesC (sch_exec n a))).
    Proof.
      apply (Rbar_le_sandwich 0 1).
      - by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
      - by apply upper_bound_ge_sup=>/=.
    Qed.

    (** * Full evaluation (limit of stratification) *)
    Definition sch_lim_exec (ρ : sch_state * mdpstate δ) : distr (mdpstate_ret δ) :=
      lim_distr (λ n, sch_exec n ρ) (sch_exec_mono ρ).

    
    Lemma sch_lim_exec_unfold a b :
      sch_lim_exec a b = Sup_seq (λ n, (sch_exec n a) b).
    Proof. apply lim_distr_pmf. Qed.

    Lemma sch_lim_exec_Sup_seq a :
      SeriesC (sch_lim_exec a) = Sup_seq (λ n, SeriesC (sch_exec n a)).
    Proof.
      erewrite SeriesC_ext; last first.
      { intros ?. rewrite sch_lim_exec_unfold //. }
      erewrite MCT_seriesC; eauto.
      - intros. apply sch_exec_mono.
      - intros. by eapply SeriesC_correct.
      - rewrite (Rbar_le_sandwich 0 1).
        + apply Sup_seq_correct.
        + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
        + by apply upper_bound_ge_sup=>/=.
    Qed.

    Lemma sch_lim_exec_step a :
      sch_lim_exec a = sch_step_or_final a ≫= sch_lim_exec.
    Proof.
      apply distr_ext.
      intro b.
      rewrite {2}/pmf /= /dbind_pmf.
      rewrite sch_lim_exec_unfold.
      setoid_rewrite sch_lim_exec_unfold.
      assert
        (SeriesC (λ a', sch_step_or_final a a' * Sup_seq (λ n, sch_exec n a' b)) =
         SeriesC (λ a', Sup_seq (λ n, sch_step_or_final a a' * sch_exec n a' b))) as ->.
      { apply SeriesC_ext; intro b'.
        apply eq_rbar_finite.
        rewrite rmult_finite.
        rewrite (rbar_finite_real_eq).
        - rewrite -Sup_seq_scal_l //.
        - apply (Rbar_le_sandwich 0 1).
          + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
          + by apply upper_bound_ge_sup=>/=. }
      rewrite (MCT_seriesC _ (λ n, sch_exec (S n) a b) (sch_lim_exec a b)) //.
      - intros. by apply Rmult_le_pos.
      - intros.
        apply Rmult_le_compat; [done|done|done|].
        apply sch_exec_mono.
      - intros a'.
        exists (sch_step_or_final a a').
        intros n.
        rewrite <- Rmult_1_r. by apply Rmult_le_compat_l.
      - intro n.
        rewrite sch_exec_Sn.
        rewrite {3}/pmf/=/dbind_pmf.
        apply SeriesC_correct.
        apply (ex_seriesC_le _ (sch_step_or_final a)); [|done].
        intros a'. split.
        + by apply Rmult_le_pos.
        + rewrite <- Rmult_1_r. by apply Rmult_le_compat_l.
      - rewrite sch_lim_exec_unfold.
        rewrite mon_sup_succ.
        + rewrite (Rbar_le_sandwich 0 1).
          * apply Sup_seq_correct.
          * by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
          * by apply upper_bound_ge_sup=>/=.
        + intro; apply sch_exec_mono.
    Qed.

    Lemma sch_lim_exec_pexec n a :
      sch_lim_exec a = sch_pexec n a ≫= sch_lim_exec.
    Proof.
      move : a.
      induction n; intro a.
      - rewrite sch_pexec_O dret_id_left //.
      - rewrite sch_pexec_Sn -dbind_assoc/=.
        rewrite sch_lim_exec_step.
        apply dbind_eq; [|done].
        intros ??. apply IHn.
    Qed.

    Lemma sch_lim_exec_det_final n a a' b :
      to_final a'.2 = Some b →
      sch_pexec n a a' = 1 →
      sch_lim_exec a = dret b.
    Proof.
      intros Hb Hpe.
      apply distr_ext.
      intro b'.
      rewrite sch_lim_exec_unfold.
      rewrite {2}/pmf /= /dret_pmf.
      case_bool_decide; simplify_eq.
      - apply Rle_antisym.
        + apply finite_rbar_le; [eapply is_finite_Sup_seq_sch_exec|].
          by apply upper_bound_ge_sup=>/=.
        + apply rbar_le_finite; [eapply is_finite_Sup_seq_sch_exec|].
          apply (Sup_seq_minor_le _ _ n)=>/=.
          by erewrite sch_pexec_exec_det.
      - rewrite -(sup_seq_const 0).
        f_equal. apply Sup_seq_ext=> m.
        f_equal. by eapply sch_pexec_exec_det_neg.
    Qed.

    Lemma sch_lim_exec_final a b :
      to_final a.2 = Some b →
      sch_lim_exec a = dret b.
    Proof.
      intros. erewrite (sch_lim_exec_det_final 0%nat); [done|done|].
      rewrite sch_pexec_O. by apply dret_1_1.
    Qed.

    Lemma sch_lim_exec_not_final a :
      ¬ is_final a.2 →
      sch_lim_exec a = sch_step a ≫= sch_lim_exec.
    Proof.
      intros Hn. rewrite sch_lim_exec_step sch_step_or_final_not_final //.
    Qed.

    Lemma sch_lim_exec_leq a b (r : R) :
      (∀ n, sch_exec n a b <= r) →
      sch_lim_exec a b <= r.
    Proof.
      intro Hexec.
      rewrite sch_lim_exec_unfold.
      apply finite_rbar_le; [apply is_finite_Sup_seq_sch_exec|].
      by apply upper_bound_ge_sup=>/=.
    Qed.

    Lemma sch_lim_exec_leq_mass  a r :
      (∀ n, SeriesC (sch_exec n a) <= r) →
      SeriesC (sch_lim_exec a) <= r.
    Proof.
      intro Hm.
      erewrite SeriesC_ext; last first.
      { intros. rewrite sch_lim_exec_unfold //. }
      erewrite (MCT_seriesC _ (λ n, SeriesC (sch_exec n a)) (Sup_seq (λ n, SeriesC (sch_exec n a)))); eauto.
      - apply finite_rbar_le; [apply is_finite_Sup_seq_SeriesC_sch_exec|].
        by apply upper_bound_ge_sup.
      - apply sch_exec_mono.
      - intros. by apply SeriesC_correct.
      - rewrite (Rbar_le_sandwich 0 1).
        + apply (Sup_seq_correct (λ n, SeriesC (sch_exec n a))).
        + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
        + by apply upper_bound_ge_sup=>/=.
    Qed.

    Lemma sch_lim_exec_term n a :
      SeriesC (sch_exec n a) = 1 →
      sch_lim_exec a = sch_exec n a.
    Proof.
      intro Hv.
      apply distr_ext=> b.
      rewrite sch_lim_exec_unfold.
      apply Rle_antisym.
      - apply finite_rbar_le; [apply is_finite_Sup_seq_sch_exec|].
        rewrite -/pmf.
        apply upper_bound_ge_sup.
        intros n'.
        destruct (decide (n <= n')) as [|?%Rnot_le_lt].
        + right. apply sch_exec_mono_term; [done|]. by apply INR_le.
        + apply sch_exec_mono'. apply INR_le. by left.
      - apply rbar_le_finite; [apply is_finite_Sup_seq_sch_exec|].
        apply (sup_is_upper_bound (λ m, sch_exec m a b) n).
    Qed.

    Lemma sch_lim_exec_pos a b :
      sch_lim_exec a b > 0 → ∃ n, sch_exec n a b > 0.
    Proof.
      intros.
      apply Classical_Pred_Type.not_all_not_ex.
      intros H'.
      assert (sch_lim_exec a b <= 0); [|lra].
      apply sch_lim_exec_leq => n.
      by apply Rnot_gt_le.
    Qed.

    Lemma sch_lim_exec_continuous_prob a ϕ r :
      (∀ n, prob (sch_exec n a) ϕ <= r) →
      prob (sch_lim_exec a) ϕ <= r.
    Proof.
      intro Hm.
      rewrite /prob.
      erewrite SeriesC_ext; last first.
      { intro; rewrite sch_lim_exec_unfold; auto. }
      assert
        (forall v, (if ϕ v then real (Sup_seq (λ n0 : nat, sch_exec n0 a v)) else 0) =
              (real (Sup_seq (λ n0 : nat, if ϕ v then sch_exec n0 a v else 0)))) as Haux.
      { intro v.
        destruct (ϕ v); auto.
        rewrite sup_seq_const //.
      }
      assert
        (is_finite (Sup_seq (λ n0 : nat, SeriesC (λ v, if ϕ v then sch_exec n0 a v else 0)))) as Hfin.
      {
        apply (Rbar_le_sandwich 0 1).
        + apply (Sup_seq_minor_le _ _ 0%nat); simpl.
          apply SeriesC_ge_0'.
          intro v; destruct (ϕ v); auto.
          lra.
        + apply upper_bound_ge_sup; intro; simpl; auto.
          apply (Rle_trans _ (SeriesC (sch_exec n a))); auto.
          apply (SeriesC_le _ (sch_exec n a)); auto.
          intro v; destruct (ϕ v); real_solver.
      }
      erewrite SeriesC_ext; last first.
      {
        intro; rewrite Haux //.
      }
      erewrite (MCT_seriesC _ (λ n, SeriesC (λ v, if ϕ v then sch_exec n a v else 0))
                  (Sup_seq (λ n0 : nat, SeriesC (λ v, if ϕ v then sch_exec n0 a v else 0))));
        auto.
      - apply finite_rbar_le; auto.
        apply upper_bound_ge_sup; auto.
      - intros n v.
        destruct (ϕ v); auto.
        lra.
      - intros n v.
        destruct (ϕ v); [ apply sch_exec_mono | lra].
      - intro v; destruct (ϕ v); exists 1; intro; auto; lra.
      - intros n.
        apply SeriesC_correct; auto.
        apply (ex_seriesC_le _ (sch_exec n a)); auto.
        intro v; destruct (ϕ v); real_solver.
      - rewrite (Rbar_le_sandwich 0 1); auto.
        + apply (Sup_seq_correct (λ n0 : nat, SeriesC (λ v, if ϕ v then sch_exec n0 a v else 0))).
        + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
          apply SeriesC_ge_0'.
          intro v; destruct (ϕ v); real_solver.
        + apply upper_bound_ge_sup; intro; simpl; auto.
          apply (Rle_trans _ (SeriesC (sch_exec n a))); auto.
          apply (SeriesC_le _ (sch_exec n a)); auto.
          intro v; destruct (ϕ v); real_solver.
    Qed.
    
  End step.

End scheduler.

#[global] Arguments scheduler (_ _) {_ _}.
