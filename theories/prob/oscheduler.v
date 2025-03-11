From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Lim_seq.
From clutch.prob Require Import distribution couplings couplings_app mdp.
Set Default Proof Using "Type*".

Section oscheduler.
  Context {δ : mdp}.
  Context `{Hosch_state: Countable osch_state}.
  Record oscheduler:= {
      oscheduler_f :> (osch_state * mdpstate δ) -> option (distr (osch_state * mdpaction δ))
    }.
  
  (** Everything below is dependent on an instance of a scheduler (and an mdp) 0*)
  Context (osch:oscheduler).

  Section step.
    Definition osch_step (ρ:osch_state*mdpstate δ) : distr(osch_state*mdpstate δ) :=
      match osch ρ with
        | Some μ => μ ≫= (λ '(sch_σ', mdp_a), dmap (λ mdp_σ', (sch_σ', mdp_σ')) (step mdp_a ρ.2))
        | None => dzero
      end.
        
    Definition osch_step_or_final_or_none a :=
      match to_final a.2 with
      | Some _ => dret a
      | None =>
          match osch a with
          | Some μ => osch_step a
          | None => dret a
          end
      end.

    Lemma osch_step_or_final_or_none_is_final ρ:
      is_final ρ.2 -> osch_step_or_final_or_none ρ = dret ρ.
    Proof.
      rewrite /osch_step_or_final_or_none.
      by intros [? ->].
    Qed.

    Lemma osch_step_or_final_or_none_is_none ρ:
      osch ρ = None -> osch_step_or_final_or_none ρ = dret ρ.
    Proof.
      rewrite /osch_step_or_final_or_none.
      intros ->.
      by case_match.
    Qed.
    
    Definition osch_pexec (n:nat) p := iterM n osch_step_or_final_or_none p.
    
    Lemma sch_opexec_fold n p:
      iterM n osch_step_or_final_or_none p = osch_pexec n p.
    Proof.
      done.
    Qed.

    Lemma osch_pexec_O a :
      osch_pexec 0 a = dret a.
    Proof. done. Qed.

    Lemma osch_pexec_Sn a n :
      osch_pexec (S n) a = osch_step_or_final_or_none a ≫= osch_pexec n.
    Proof. done. Qed.

    Lemma osch_pexec_plus ρ n m :
      osch_pexec (n + m) ρ = osch_pexec n ρ ≫= osch_pexec m.
    Proof. rewrite /osch_pexec iterM_plus //.  Qed.

    Lemma osch_pexec_1 :
      osch_pexec 1 = osch_step_or_final_or_none.
    Proof.
      extensionality a.
      rewrite osch_pexec_Sn /osch_pexec /= dret_id_right //.
    Qed.

    Lemma osch_pexec_Sn_r a n :
      osch_pexec (S n) a = osch_pexec n a ≫= osch_step_or_final_or_none.
    Proof.
      assert (S n = n + 1)%nat as -> by lia.
      rewrite osch_pexec_plus osch_pexec_1 //.
    Qed.

    Lemma osch_pexec_is_final n a :
      is_final a.2 → osch_pexec n a = dret a.
    Proof.
      intros H.
      induction n.
      - rewrite osch_pexec_O //.
      - erewrite osch_pexec_Sn, osch_step_or_final_or_none_is_final; last done.
        rewrite dret_id_left -IHn //.
    Qed.

    Lemma osch_pexec_det_steps n m a1 a2 :
      osch_pexec n a1 a2 = 1 →
      osch_pexec n a1 ≫= osch_pexec m = osch_pexec m a2.
    Proof. intros ->%pmf_1_eq_dret. rewrite dret_id_left //. Qed.

    
    Fixpoint osch_exec (n:nat) (ρ : osch_state * mdpstate δ) {struct n} : distr (osch_state * mdpstate δ) :=
      let '(osch_σ, mdp_σ) := ρ in
      match to_final mdp_σ, osch ρ, n with
      | Some b, _, _ => dret ρ
      | None, None, _ => dret ρ
      | None, Some μ, 0 => dzero
      | None, Some μ, S n => μ ≫= (λ '(osch_σ', mdp_a),
                                    (step mdp_a mdp_σ) ≫=
                                      (λ mdp_σ', osch_exec n (osch_σ', mdp_σ')))
                                      
      end.

    Lemma osch_exec_is_final ρ b n :
      to_final ρ.2 = Some b → osch_exec n ρ = dret ρ.
    Proof. destruct ρ, n; simpl; by intros ->. Qed.

    Lemma osch_exec_is_none ρ n :
      osch ρ = None → osch_exec n ρ = dret ρ.
    Proof. intros. rewrite /osch_exec.
           destruct ρ, n; by repeat case_match.
    Qed.

    Lemma osch_exec_Sn a n :
      osch_exec (S n) a = osch_step_or_final_or_none a ≫= osch_exec n.
    Proof.
      rewrite /osch_step_or_final_or_none /=.
      destruct a. simpl. rewrite /osch_step.
      repeat case_match; try done.
      - rewrite dret_id_left -/osch_exec.
        by erewrite osch_exec_is_final.
      - simpl.
        rewrite -dbind_assoc.
        apply dbind_ext_right.
        intros [??]. rewrite /dmap.
        rewrite -dbind_assoc.
        apply dbind_ext_right.
        intros. by rewrite dret_id_left.
      - rewrite dret_id_left -/osch_exec.
        rewrite /osch_exec. 
        by erewrite osch_exec_is_none.
    Qed.
    
    Lemma osch_exec_plus a n1 n2 :
      osch_exec (n1 + n2) a = osch_pexec n1 a ≫= osch_exec n2.
    Proof.
      revert a. induction n1.
      - intro a. rewrite osch_pexec_O dret_id_left //.
      - intro a. replace ((S n1 + n2)%nat) with ((S (n1 + n2))); auto.
        rewrite osch_exec_Sn osch_pexec_Sn.
        apply distr_ext.
        intro.
        rewrite -dbind_assoc.
        rewrite /pmf/=/dbind_pmf.
        by setoid_rewrite IHn1.
    Qed.

    Lemma osch_exec_pexec_relate a n:
      osch_exec n a = osch_pexec n a ≫=
                       (λ e, match to_final e.2, osch e with
                             | Some b, _ => dret e
                             | None, None => dret e
                             | _, _ => dzero
                             end).
    Proof.
      revert a.
      induction n; intros [].
      - simpl. rewrite osch_pexec_O.
        rewrite dret_id_left'.
        done.
      - simpl. rewrite osch_pexec_Sn.
        rewrite -dbind_assoc'.
        case_match eqn:H.
        + erewrite osch_step_or_final_or_none_is_final; last by eapply to_final_Some_2. 
          rewrite dret_id_left'.
          rewrite osch_pexec_is_final; last by eapply to_final_Some_2.
          rewrite dret_id_left'. rewrite H. done.
        + case_match.
          * rewrite /osch_step_or_final_or_none/osch_step/=.
            repeat case_match; try done.
            simplify_eq.
            rewrite -dbind_assoc. apply dbind_ext_right.
            intros [??].
            rewrite -dbind_assoc.
            apply dbind_ext_right.
            intros ?.
            by rewrite dret_id_left.
          * rewrite osch_step_or_final_or_none_is_none; last done.
            rewrite dret_id_left. rewrite -IHn.
            by rewrite osch_exec_is_none.
    Qed.

    
    Lemma osch_exec_mono a n v :
      osch_exec n a v <= osch_exec (S n) a v.
    Proof.
      apply refRcoupl_eq_elim.
      move : a.
      induction n.
      - intros [].
        apply refRcoupl_from_leq.
        intros b. rewrite /distr_le /=.
        by repeat case_match.
      - intros []; do 2 rewrite osch_exec_Sn.
        eapply refRcoupl_dbind; [|apply refRcoupl_eq_refl].
        by intros ? ? ->.
    Qed.

    Lemma osch_exec_mono' ρ n m v :
      n ≤ m → osch_exec n ρ v <= osch_exec m ρ v.
    Proof.
      eapply (mon_succ_to_mon (λ x, osch_exec x ρ v)).
      intro. apply osch_exec_mono.
    Qed.

    Lemma osch_exec_mono_term a b n m :
      SeriesC (osch_exec n a) = 1 →
      n ≤ m →
      osch_exec m a b = osch_exec n a b.
    Proof.
      intros Hv Hleq.
      apply Rle_antisym; [ |by apply osch_exec_mono'].
      destruct (decide (osch_exec m a b <= osch_exec n a b))
        as [|?%Rnot_le_lt]; [done|].
      exfalso.
      assert (1 < SeriesC (osch_exec m a)); last first.
      - assert (SeriesC (osch_exec m a) <= 1); [done|]. lra.
      - rewrite -Hv.
        apply SeriesC_lt; eauto.
        intros b'. by split; [|apply osch_exec_mono'].
    Qed.

    Lemma osch_pexec_exec_le_final n a a' b :
      to_final a'.2 =Some b->
      osch_pexec n a a' <= osch_exec n a a'.
    Proof.
      intros.
      revert a. induction n; intros a.
      - rewrite osch_pexec_O.
        destruct (decide (a = a')) as [->|].
        + erewrite osch_exec_is_final; last done.
          rewrite !dret_1_1 //.
        + rewrite dret_0 //.
      - rewrite osch_exec_Sn osch_pexec_Sn.
        destruct (decide (is_final a.2)) as [|].
        + erewrite osch_step_or_final_or_none_is_final; last done.
          rewrite 2!dret_id_left -/osch_exec.
          apply IHn.
        + rewrite /osch_step_or_final_or_none.
          repeat case_match; try done.
          * rewrite !dret_id_left'. naive_solver.
          * rewrite /dbind/dbind_pmf{1 4}/pmf/=.
            apply SeriesC_le.
            -- intros. split; real_solver.
            -- apply pmf_ex_seriesC_mult_fn.
               naive_solver.
          * by rewrite !dret_id_left'.
    Qed.

    Lemma osch_pexec_exec_det n a a' b :
      to_final a'.2 = Some b →
      osch_pexec n a a' = 1 → osch_exec n a a' = 1.
    Proof.
      intros Hf.
      pose proof (osch_pexec_exec_le_final n a a' b Hf).
      pose proof (pmf_le_1 (osch_exec n a) a').
      lra.
    Qed.

    Lemma osch_exec_pexec_val_neq_le n m a a1 a2 b b' :
      to_final a1.2 = Some b →
      to_final a2.2 = Some b' ->
      b ≠ b' → osch_exec m a a1 + osch_pexec n a a2 <= 1.
    Proof.
      intros Hf Hneq.
      etrans; [by eapply Rplus_le_compat_l, osch_pexec_exec_le_final|].
      etrans; [apply Rplus_le_compat_l, (osch_exec_mono' _ n (n `max` m)), Nat.le_max_l|].
      etrans; [apply Rplus_le_compat_r, (osch_exec_mono' _ m (n `max` m)), Nat.le_max_r|].
      etrans; [|apply (pmf_SeriesC (osch_exec (n `max` m) a))].
      apply pmf_plus_neq_SeriesC.
      intro. simplify_eq.
    Qed.

    Lemma osch_pexec_exec_det_neg n m a a1 a2 b b' :
      to_final a1.2 = Some b →
      to_final a2.2 = Some b' ->
      osch_pexec n a a1 = 1 →
      b ≠ b' →
      osch_exec m a a2 = 0.
    Proof.
      intros Hf Hf' Hexec Hv.
      epose proof (osch_exec_pexec_val_neq_le n m a _ _ _ _  Hf' Hf _) as Hle.
      Unshelve.
      2: { done. } 
      rewrite Hexec in Hle.
      pose proof (pmf_pos (osch_exec m a) a2).
      lra.
    Qed.

    Lemma is_finite_Sup_seq_osch_exec a b :
      is_finite (Sup_seq (λ n, osch_exec n a b)).
    Proof.
      apply (Rbar_le_sandwich 0 1).
      - by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
      - by apply upper_bound_ge_sup=>/=.
    Qed.

    Lemma is_finite_Sup_seq_SeriesC_osch_exec a :
      is_finite (Sup_seq (λ n, SeriesC (osch_exec n a))).
    Proof.
      apply (Rbar_le_sandwich 0 1).
      - by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
      - by apply upper_bound_ge_sup=>/=.
    Qed.

    (** * Full evaluation (limit of stratification) *)
    Definition osch_lim_exec (ρ : osch_state * mdpstate δ) : distr (osch_state * mdpstate δ) :=
      lim_distr (λ n, osch_exec n ρ) (osch_exec_mono ρ).

    
    Lemma osch_lim_exec_unfold a b :
      osch_lim_exec a b = Sup_seq (λ n, (osch_exec n a) b).
    Proof. apply lim_distr_pmf. Qed.

    Lemma osch_lim_exec_Sup_seq a :
      SeriesC (osch_lim_exec a) = Sup_seq (λ n, SeriesC (osch_exec n a)).
    Proof.
      erewrite SeriesC_ext; last first.
      { intros ?. rewrite osch_lim_exec_unfold //. }
      erewrite MCT_seriesC; eauto.
      - intros. apply osch_exec_mono.
      - intros. by eapply SeriesC_correct.
      - rewrite (Rbar_le_sandwich 0 1).
        + apply Sup_seq_correct.
        + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
        + by apply upper_bound_ge_sup=>/=.
    Qed.

    Lemma osch_lim_exec_step a :
      osch_lim_exec a = osch_step_or_final_or_none a ≫= osch_lim_exec.
    Proof.
      apply distr_ext.
      intro b.
      rewrite {2}/pmf /= /dbind_pmf.
      rewrite osch_lim_exec_unfold.
      setoid_rewrite osch_lim_exec_unfold.
      assert
        (SeriesC (λ a', osch_step_or_final_or_none a a' * Sup_seq (λ n, osch_exec n a' b)) =
         SeriesC (λ a', Sup_seq (λ n, osch_step_or_final_or_none a a' * osch_exec n a' b))) as ->.
      { apply SeriesC_ext; intro b'.
        apply eq_rbar_finite.
        rewrite rmult_finite.
        rewrite (rbar_finite_real_eq).
        - rewrite -Sup_seq_scal_l //.
        - apply (Rbar_le_sandwich 0 1).
          + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
          + by apply upper_bound_ge_sup=>/=. }
      rewrite (MCT_seriesC _ (λ n, osch_exec (S n) a b) (osch_lim_exec a b)) //.
      - intros. by apply Rmult_le_pos.
      - intros.
        apply Rmult_le_compat; [done|done|done|].
        apply osch_exec_mono.
      - intros a'.
        exists (osch_step_or_final_or_none a a').
        intros n.
        rewrite <- Rmult_1_r. by apply Rmult_le_compat_l.
      - intro n.
        rewrite osch_exec_Sn.
        rewrite {3}/pmf/=/dbind_pmf.
        apply SeriesC_correct.
        apply (ex_seriesC_le _ (osch_step_or_final_or_none a)); [|done].
        intros a'. split.
        + by apply Rmult_le_pos.
        + rewrite <- Rmult_1_r. by apply Rmult_le_compat_l.
      - rewrite osch_lim_exec_unfold.
        rewrite mon_sup_succ.
        + rewrite (Rbar_le_sandwich 0 1).
          * apply Sup_seq_correct.
          * by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
          * by apply upper_bound_ge_sup=>/=.
        + intro; apply osch_exec_mono.
    Qed.

    Lemma osch_lim_exec_pexec n a :
      osch_lim_exec a = osch_pexec n a ≫= osch_lim_exec.
    Proof.
      move : a.
      induction n; intro a.
      - rewrite osch_pexec_O dret_id_left //.
      - rewrite osch_pexec_Sn -dbind_assoc/=.
        rewrite osch_lim_exec_step.
        apply dbind_eq; [|done].
        intros ??. apply IHn.
    Qed.

    Lemma osch_lim_exec_det_final n a a' b :
      to_final a'.2 = Some b →
      osch_pexec n a a' = 1 →
      osch_lim_exec a = dret a'.
    Proof.
      intros Hb Hpe.
      apply distr_ext.
      intro b'.
      rewrite osch_lim_exec_unfold.
      rewrite {2}/pmf /= /dret_pmf.
      case_bool_decide; simplify_eq.
      - apply Rle_antisym.
        + apply finite_rbar_le; [eapply is_finite_Sup_seq_osch_exec|].
          by apply upper_bound_ge_sup=>/=.
        + apply rbar_le_finite; [eapply is_finite_Sup_seq_osch_exec|].
          apply (Sup_seq_minor_le _ _ n)=>/=.
          by erewrite osch_pexec_exec_det.
      - rewrite -(sup_seq_const 0).
        f_equal. apply Sup_seq_ext=> m.
        destruct (pmf_pos (osch_exec m a) b') as [|<-]; last done.
        assert (osch_exec n a a' = 1)%R as K1.
        { apply Rle_antisym; first done.
          rewrite -Hpe.
          by eapply osch_pexec_exec_le_final.
        }
        destruct (Nat.le_ge_cases n m).
        + erewrite <-osch_exec_mono_term in K1; last exact.
          * assert (SeriesC (λ x, if bool_decide (x ∈ [a'; b']) then osch_exec m a x else 0) <=1)%R as K2.
            { trans (SeriesC (osch_exec m a)); last done.
              apply SeriesC_le; last done.
              intros. by case_match.
            }
            rewrite SeriesC_list in K2.
            -- simpl in K2.
               rewrite K1 in K2.
               lra.
            -- apply NoDup_cons; split; last apply NoDup_singleton.
               set_solver.
          * by erewrite <-pmf_1_eq_SeriesC.
        + assert (osch_exec n a b' = 0)%R as K2; last first.
          { destruct (pmf_pos (osch_exec m a) b') as [|]; last lra.
            exfalso.
            assert (osch_exec m a b'<=osch_exec n a b')%R.
            - by eapply osch_exec_mono'.
            - lra.
          }
          erewrite osch_exec_mono_term in K1; last reflexivity.
          * assert (SeriesC (λ x, if bool_decide (x ∈ [a'; b']) then osch_exec n a x else 0) <=1)%R as K2.
            { trans (SeriesC (osch_exec n a)); last done.
              apply SeriesC_le; last done.
              intros. by case_match.
            }
            rewrite SeriesC_list in K2.
            -- simpl in K2.
               assert (osch_exec n a a' =1)%R as K3.
               { apply Rle_antisym; first done.
                 rewrite -K1.
                 by apply osch_exec_mono'.
               }
               rewrite K3 in K2.
               destruct (pmf_pos (osch_exec n a) b'); lra.
            -- apply NoDup_cons; split; last apply NoDup_singleton.
               set_solver.
          * by erewrite <-pmf_1_eq_SeriesC.
    Qed.

    Lemma osch_lim_exec_final a b :
      to_final a.2 = Some b →
      osch_lim_exec a = dret a.
    Proof.
      intros. erewrite (osch_lim_exec_det_final 0%nat); [done|done|].
      rewrite osch_pexec_O. by apply dret_1_1.
    Qed.

    Lemma osch_lim_exec_leq a b (r : R) :
      (∀ n, osch_exec n a b <= r) →
      osch_lim_exec a b <= r.
    Proof.
      intro Hexec.
      rewrite osch_lim_exec_unfold.
      apply finite_rbar_le; [apply is_finite_Sup_seq_osch_exec|].
      by apply upper_bound_ge_sup=>/=.
    Qed.

    Lemma osch_lim_exec_leq_mass  a r :
      (∀ n, SeriesC (osch_exec n a) <= r) →
      SeriesC (osch_lim_exec a) <= r.
    Proof.
      intro Hm.
      erewrite SeriesC_ext; last first.
      { intros. rewrite osch_lim_exec_unfold //. }
      erewrite (MCT_seriesC _ (λ n, SeriesC (osch_exec n a)) (Sup_seq (λ n, SeriesC (osch_exec n a)))); eauto.
      - apply finite_rbar_le; [apply is_finite_Sup_seq_SeriesC_osch_exec|].
        by apply upper_bound_ge_sup.
      - apply osch_exec_mono.
      - intros. by apply SeriesC_correct.
      - rewrite (Rbar_le_sandwich 0 1).
        + apply (Sup_seq_correct (λ n, SeriesC (osch_exec n a))).
        + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
        + by apply upper_bound_ge_sup=>/=.
    Qed.

    Lemma osch_lim_exec_term n a :
      SeriesC (osch_exec n a) = 1 →
      osch_lim_exec a = osch_exec n a.
    Proof.
      intro Hv.
      apply distr_ext=> b.
      rewrite osch_lim_exec_unfold.
      apply Rle_antisym.
      - apply finite_rbar_le; [apply is_finite_Sup_seq_osch_exec|].
        rewrite -/pmf.
        apply upper_bound_ge_sup.
        intros n'.
        destruct (decide (n <= n')) as [|?%Rnot_le_lt].
        + right. apply osch_exec_mono_term; [done|]. by apply INR_le.
        + apply osch_exec_mono'. apply INR_le. by left.
      - apply rbar_le_finite; [apply is_finite_Sup_seq_osch_exec|].
        apply (sup_is_upper_bound (λ m, osch_exec m a b) n).
    Qed.

    Lemma osch_lim_exec_pos a b :
      osch_lim_exec a b > 0 → ∃ n, osch_exec n a b > 0.
    Proof.
      intros.
      apply Classical_Pred_Type.not_all_not_ex.
      intros H'.
      assert (osch_lim_exec a b <= 0); [|lra].
      apply osch_lim_exec_leq => n.
      by apply Rnot_gt_le.
    Qed.

    Lemma osch_lim_exec_continuous_prob a ϕ r :
      (∀ n, prob (osch_exec n a) ϕ <= r) →
      prob (osch_lim_exec a) ϕ <= r.
    Proof.
      intro Hm.
      rewrite /prob.
      erewrite SeriesC_ext; last first.
      { intro; rewrite osch_lim_exec_unfold; auto. }
      assert
        (forall v, (if ϕ v then real (Sup_seq (λ n0 : nat, osch_exec n0 a v)) else 0) =
              (real (Sup_seq (λ n0 : nat, if ϕ v then osch_exec n0 a v else 0)))) as Haux.
      { intro v.
        destruct (ϕ v); auto.
        rewrite sup_seq_const //.
      }
      assert
        (is_finite (Sup_seq (λ n0 : nat, SeriesC (λ v, if ϕ v then osch_exec n0 a v else 0)))) as Hfin.
      {
        apply (Rbar_le_sandwich 0 1).
        + apply (Sup_seq_minor_le _ _ 0%nat); simpl.
          apply SeriesC_ge_0'.
          intro v; destruct (ϕ v); auto.
          lra.
        + apply upper_bound_ge_sup; intro; simpl; auto.
          apply (Rle_trans _ (SeriesC (osch_exec n a))); auto.
          apply (SeriesC_le _ (osch_exec n a)); auto.
          intro v; destruct (ϕ v); real_solver.
      }
      erewrite SeriesC_ext; last first.
      {
        intro; rewrite Haux //.
      }
      erewrite (MCT_seriesC _ (λ n, SeriesC (λ v, if ϕ v then osch_exec n a v else 0))
                  (Sup_seq (λ n0 : nat, SeriesC (λ v, if ϕ v then osch_exec n0 a v else 0))));
        auto.
      - apply finite_rbar_le; auto.
        apply upper_bound_ge_sup; auto.
      - intros n v.
        destruct (ϕ v); auto.
        lra.
      - intros n v.
        destruct (ϕ v); [ apply osch_exec_mono | lra].
      - intro v; destruct (ϕ v); exists 1; intro; auto; lra.
      - intros n.
        apply SeriesC_correct; auto.
        apply (ex_seriesC_le _ (osch_exec n a)); auto.
        intro v; destruct (ϕ v); real_solver.
      - rewrite (Rbar_le_sandwich 0 1); auto.
        + apply (Sup_seq_correct (λ n0 : nat, SeriesC (λ v, if ϕ v then osch_exec n0 a v else 0))).
        + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
          apply SeriesC_ge_0'.
          intro v; destruct (ϕ v); real_solver.
        + apply upper_bound_ge_sup; intro; simpl; auto.
          apply (Rle_trans _ (SeriesC (osch_exec n a))); auto.
          apply (SeriesC_le _ (osch_exec n a)); auto.
          intro v; destruct (ϕ v); real_solver.
    Qed.
    
  End step.

End oscheduler.

#[global] Arguments oscheduler (_ _) {_ _}.
