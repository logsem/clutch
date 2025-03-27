From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Lim_seq.
From stdpp Require Import option.
From clutch.common Require Import con_language.
From clutch.con_prob_lang Require Import lang.
From clutch.prob Require Import distribution couplings couplings_app mdp.
Set Default Proof Using "Type*".

(* Unlike a scheduler, we can take steps of other threads even if first thread is a value *)

Definition step' (n: nat) (ρ : mdpstate (con_lang_mdp con_prob_lang)) : distr (mdpstate (con_lang_mdp con_prob_lang)) :=
  let '(expr_lis, σ) := ρ in
  match expr_lis!!n with
  | None => (* thread id exceed num of thread, so we stutter *)
      dret (expr_lis, σ)
  | Some expr =>
      match to_val expr with 
      | Some _ => (* expr is a val, so we stutter *) dret (expr_lis, σ)
      | None => dmap (λ '(expr', σ', efs), ((<[n:=expr']> expr_lis) ++ efs, σ')) (prim_step expr σ)
      end
  end.

Section oscheduler.
  Context `{Hosch_state: Countable osch_state}.
  
  Record oscheduler:= {
      oscheduler_f :> (osch_state * mdpstate (con_lang_mdp con_prob_lang)) -> option (distr (osch_state * mdpaction (con_lang_mdp con_prob_lang)))
    }.
  
  (* Instance oscheduler_inhabited : Inhabited (oscheduler) := populate ( {| oscheduler_f := inhabitant |} ). *)

  (** Everything below is dependent on an instance of an oscheduler *)
  Context (osch:oscheduler).

  Section step.
    Definition osch_step (ρ:osch_state*cfg) : distr(osch_state*cfg) :=
      match osch ρ with
        | Some μ => μ ≫= (λ '(sch_σ', mdp_a), dmap (λ mdp_σ' :cfg, (sch_σ', mdp_σ')) (step' mdp_a ρ.2))
        | None => dzero
      end.
        
    Definition osch_step_or_none a :=
      match osch a with
      | Some μ => osch_step a
      | None => dret a
      end.

    Lemma osch_step_or_none_is_none ρ:
      osch ρ = None -> osch_step_or_none ρ = dret ρ.
    Proof.
      rewrite /osch_step_or_none.
      by intros ->.
    Qed.
    
    Definition osch_pexec (n:nat) p := iterM n osch_step_or_none p.
    
    Lemma sch_opexec_fold n p:
      iterM n osch_step_or_none p = osch_pexec n p.
    Proof.
      done.
    Qed.

    Lemma osch_pexec_O a :
      osch_pexec 0 a = dret a.
    Proof. done. Qed.

    Lemma osch_pexec_Sn a n :
      osch_pexec (S n) a = osch_step_or_none a ≫= osch_pexec n.
    Proof. done. Qed.

    Lemma osch_pexec_plus ρ n m :
      osch_pexec (n + m) ρ = osch_pexec n ρ ≫= osch_pexec m.
    Proof. rewrite /osch_pexec iterM_plus //.  Qed.

    Lemma osch_pexec_1 :
      osch_pexec 1 = osch_step_or_none.
    Proof.
      extensionality a.
      rewrite osch_pexec_Sn /osch_pexec /= dret_id_right //.
    Qed.

    Lemma osch_pexec_Sn_r a n :
      osch_pexec (S n) a = osch_pexec n a ≫= osch_step_or_none.
    Proof.
      assert (S n = n + 1)%nat as -> by lia.
      rewrite osch_pexec_plus osch_pexec_1 //.
    Qed.

    Lemma osch_pexec_det_steps n m a1 a2 :
      osch_pexec n a1 a2 = 1 →
      osch_pexec n a1 ≫= osch_pexec m = osch_pexec m a2.
    Proof. intros ->%pmf_1_eq_dret. rewrite dret_id_left //. Qed.

    (* osch_exec returns whole configuration if nothing else to step*)
    
    Fixpoint osch_exec (n:nat) (ρ : osch_state * mdpstate (con_lang_mdp con_prob_lang)) {struct n} : distr (osch_state * mdpstate (con_lang_mdp con_prob_lang)) :=
      let '(osch_σ, mdp_σ) := ρ in
      match osch ρ, n with
      | None, _ => dret ρ
      | Some μ, 0 => dzero
      | Some μ, S n => μ ≫= (λ '(osch_σ', mdp_a),
                              (step' mdp_a mdp_σ) ≫=
                                (λ mdp_σ', osch_exec n (osch_σ', mdp_σ')))
                        
      end.

    Lemma osch_exec_is_none ρ n :
      osch ρ = None → osch_exec n ρ = dret ρ.
    Proof. intros. rewrite /osch_exec.
           destruct ρ, n; by repeat case_match.
    Qed.

    Lemma osch_exec_0 ρ:
      is_Some (osch ρ) -> osch_exec 0 ρ = dzero.
    Proof.
      rewrite /osch_exec. destruct ρ.
      by intros [? ->].
    Qed.

    Lemma osch_exec_Sn a n :
      osch_exec (S n) a = osch_step_or_none a ≫= osch_exec n.
    Proof.
      rewrite /osch_step_or_none /=.
      destruct a. simpl. rewrite /osch_step.
      repeat case_match; try done.
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
                       (λ e, match osch e with
                             | None => dret e
                             | _ => dzero
                             end).
    Proof.
      revert a.
      induction n; intros [].
      - simpl. rewrite osch_pexec_O.
        rewrite dret_id_left'.
        done.
      - simpl. rewrite osch_pexec_Sn.
        rewrite -dbind_assoc'.
        rewrite /osch_step_or_none /osch_step.  
        case_match eqn:H.
        + rewrite /osch_step_or_none/osch_step/=.
          repeat case_match; try done.
          simplify_eq.
          rewrite -dbind_assoc. apply dbind_ext_right.
          intros [??].
          rewrite -dbind_assoc.
          apply dbind_ext_right.
          intros ?.
          by rewrite dret_id_left.
        + rewrite dret_id_left. rewrite -IHn.
          by rewrite osch_exec_is_none.
    Qed.

    Lemma osch_exec_pos n a b:
      (osch_exec n a b > 0)%R ->
      osch b = None.
    Proof.
      rewrite osch_exec_pexec_relate.
      rewrite dbind_pos. elim.
      intros [??].
      repeat case_match.
      - elim. rewrite dzero_0. lra.
      - elim. intros H'. apply dret_pos in H'. simplify_eq. naive_solver.
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

    (* Lemma osch_pexec_exec_le_final n a a' b : *)
    (*   to_final a'.2 =Some b-> *)
    (*   osch_pexec n a a' <= osch_exec n a a'. *)
    (* Proof. *)
    (*   intros. *)
    (*   revert a. induction n; intros a. *)
    (*   - rewrite osch_pexec_O. *)
    (*     destruct (decide (a = a')) as [->|]. *)
    (*     + erewrite osch_exec_is_final; last done. *)
    (*       rewrite !dret_1_1 //. *)
    (*     + rewrite dret_0 //. *)
    (*   - rewrite osch_exec_Sn osch_pexec_Sn. *)
    (*     destruct (decide (is_final a.2)) as [|]. *)
    (*     + erewrite osch_step_or_none_is_final; last done. *)
    (*       rewrite 2!dret_id_left -/osch_exec. *)
    (*       apply IHn. *)
    (*     + rewrite /osch_step_or_none. *)
    (*       repeat case_match; try done. *)
    (*       * rewrite !dret_id_left'. naive_solver. *)
    (*       * rewrite /dbind/dbind_pmf{1 4}/pmf/=. *)
    (*         apply SeriesC_le. *)
    (*         -- intros. split; real_solver. *)
    (*         -- apply pmf_ex_seriesC_mult_fn. *)
    (*            naive_solver. *)
    (*       * by rewrite !dret_id_left'. *)
    (* Qed. *)

    (* Lemma osch_pexec_exec_det n a a' b : *)
    (*   to_final a'.2 = Some b → *)
    (*   osch_pexec n a a' = 1 → osch_exec n a a' = 1. *)
    (* Proof. *)
    (*   intros Hf. *)
    (*   pose proof (osch_pexec_exec_le_final n a a' b Hf). *)
    (*   pose proof (pmf_le_1 (osch_exec n a) a'). *)
    (*   lra. *)
    (* Qed. *)

    (* Lemma osch_exec_pexec_val_neq_le n m a a1 a2 b b' : *)
    (*   to_final a1.2 = Some b → *)
    (*   to_final a2.2 = Some b' -> *)
    (*   b ≠ b' → osch_exec m a a1 + osch_pexec n a a2 <= 1. *)
    (* Proof. *)
    (*   intros Hf Hneq. *)
    (*   etrans; [by eapply Rplus_le_compat_l, osch_pexec_exec_le_final|]. *)
    (*   etrans; [apply Rplus_le_compat_l, (osch_exec_mono' _ n (n `max` m)), Nat.le_max_l|]. *)
    (*   etrans; [apply Rplus_le_compat_r, (osch_exec_mono' _ m (n `max` m)), Nat.le_max_r|]. *)
    (*   etrans; [|apply (pmf_SeriesC (osch_exec (n `max` m) a))]. *)
    (*   apply pmf_plus_neq_SeriesC. *)
    (*   intro. simplify_eq. *)
    (* Qed. *)

    (* Lemma osch_pexec_exec_det_neg n m a a1 a2 b b' : *)
    (*   to_final a1.2 = Some b → *)
    (*   to_final a2.2 = Some b' -> *)
    (*   osch_pexec n a a1 = 1 → *)
    (*   b ≠ b' → *)
    (*   osch_exec m a a2 = 0. *)
    (* Proof. *)
    (*   intros Hf Hf' Hexec Hv. *)
    (*   epose proof (osch_exec_pexec_val_neq_le n m a _ _ _ _  Hf' Hf _) as Hle. *)
    (*   Unshelve. *)
    (*   2: { done. }  *)
    (*   rewrite Hexec in Hle. *)
    (*   pose proof (pmf_pos (osch_exec m a) a2). *)
    (*   lra. *)
    (* Qed. *)

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
    Definition osch_lim_exec (ρ : osch_state * mdpstate (con_lang_mdp con_prob_lang)) : distr (osch_state * mdpstate (con_lang_mdp con_prob_lang)) :=
      lim_distr (λ n, osch_exec n ρ) (osch_exec_mono ρ).

    
    Lemma osch_lim_exec_unfold a b :
      osch_lim_exec a b = Sup_seq (λ n, (osch_exec n a) b).
    Proof. apply lim_distr_pmf. Qed.

    Lemma osch_lim_exec_is_sup n a b:
      osch_exec n a b <= osch_lim_exec a b.
    Proof. rewrite osch_lim_exec_unfold.
           apply rbar_le_finite.
           - apply is_finite_Sup_seq_osch_exec.
           - etrans; last apply sup_is_upper_bound; done.
    Qed.

    Lemma osch_lim_exec_dmap_le `{Countable B} f a (b:B) r:
      (∀ n, dmap f (osch_exec n a) b <= r) ->
      dmap f (osch_lim_exec a) b <= r.
    Proof. 
      intros H1.
      rewrite /dmap/dbind/dbind_pmf{1}/pmf.
      setoid_rewrite osch_lim_exec_unfold.
      erewrite SeriesC_ext; last first.
      { intros. rewrite rbar_scal_r; last apply is_finite_Sup_seq_osch_exec.
        by rewrite -Sup_seq_scal_r.
      }
      setoid_rewrite SeriesC_Sup_seq_swap.
      - apply Rbar_le_fin.
        { etrans; last eapply H1. done. }
        apply upper_bound_ge_sup.
        intros n.
        pose proof H1 n as H0.
        apply rbar_le_rle in H0.
        naive_solver.
      - intros. real_solver.
      - intros. apply Rmult_le_compat; try done.
        apply osch_exec_mono.
      - intros. exists (1*1).
        intros.
        by apply Rmult_le_compat.
      - intros. apply SeriesC_correct.
        apply pmf_ex_seriesC_mult_fn. naive_solver.
      - simpl. done.
        Unshelve.
        exact 0%nat.
    Qed.
      
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
      osch_lim_exec a = osch_step_or_none a ≫= osch_lim_exec.
    Proof.
      apply distr_ext.
      intro b.
      rewrite {2}/pmf /= /dbind_pmf.
      rewrite osch_lim_exec_unfold.
      setoid_rewrite osch_lim_exec_unfold.
      assert
        (SeriesC (λ a', osch_step_or_none a a' * Sup_seq (λ n, osch_exec n a' b)) =
         SeriesC (λ a', Sup_seq (λ n, osch_step_or_none a a' * osch_exec n a' b))) as Hrewrite.
      { apply SeriesC_ext; intro b'.
        apply eq_rbar_finite.
        rewrite rmult_finite.
        rewrite (rbar_finite_real_eq).
        - rewrite -Sup_seq_scal_l //.
        - apply (Rbar_le_sandwich 0 1).
          + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
          + by apply upper_bound_ge_sup=>/=. }
      rewrite Hrewrite.
      rewrite (MCT_seriesC _ (λ n, osch_exec (S n) a b) (osch_lim_exec a b)) //.
      - intros. by apply Rmult_le_pos.
      - intros.
        apply Rmult_le_compat; [done|done|done|].
        apply osch_exec_mono.
      - intros a'.
        exists (osch_step_or_none a a').
        intros n.
        rewrite <- Rmult_1_r. by apply Rmult_le_compat_l.
      - intro n.
        rewrite osch_exec_Sn.
        rewrite {3}/pmf/=/dbind_pmf.
        apply SeriesC_correct.
        apply (ex_seriesC_le _ (osch_step_or_none a)); [|done].
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

    (* Lemma osch_lim_exec_det_final n a a' b : *)
    (*   to_final a'.2 = Some b → *)
    (*   osch_pexec n a a' = 1 → *)
    (*   osch_lim_exec a = dret a'. *)
    (* Proof. *)
    (*   intros Hb Hpe. *)
    (*   apply distr_ext. *)
    (*   intro b'. *)
    (*   rewrite osch_lim_exec_unfold. *)
    (*   rewrite {2}/pmf /= /dret_pmf. *)
    (*   case_bool_decide; simplify_eq. *)
    (*   - apply Rle_antisym. *)
    (*     + apply finite_rbar_le; [eapply is_finite_Sup_seq_osch_exec|]. *)
    (*       by apply upper_bound_ge_sup=>/=. *)
    (*     + apply rbar_le_finite; [eapply is_finite_Sup_seq_osch_exec|]. *)
    (*       apply (Sup_seq_minor_le _ _ n)=>/=. *)
    (*       by erewrite osch_pexec_exec_det. *)
    (*   - rewrite -(sup_seq_const 0). *)
    (*     f_equal. apply Sup_seq_ext=> m. *)
    (*     destruct (pmf_pos (osch_exec m a) b') as [|<-]; last done. *)
    (*     assert (osch_exec n a a' = 1)%R as K1. *)
    (*     { apply Rle_antisym; first done. *)
    (*       rewrite -Hpe. *)
    (*       by eapply osch_pexec_exec_le_final. *)
    (*     } *)
    (*     destruct (Nat.le_ge_cases n m). *)
    (*     + erewrite <-osch_exec_mono_term in K1; last exact. *)
    (*       * assert (SeriesC (λ x, if bool_decide (x ∈ [a'; b']) then osch_exec m a x else 0) <=1)%R as K2. *)
    (*         { trans (SeriesC (osch_exec m a)); last done. *)
    (*           apply SeriesC_le; last done. *)
    (*           intros. by case_match. *)
    (*         } *)
    (*         rewrite SeriesC_list in K2. *)
    (*         -- simpl in K2. *)
    (*            rewrite K1 in K2. *)
    (*            lra. *)
    (*         -- apply NoDup_cons; split; last apply NoDup_singleton. *)
    (*            set_solver. *)
    (*       * by erewrite <-pmf_1_eq_SeriesC. *)
    (*     + assert (osch_exec n a b' = 0)%R as K2; last first. *)
    (*       { destruct (pmf_pos (osch_exec m a) b') as [|]; last lra. *)
    (*         exfalso. *)
    (*         assert (osch_exec m a b'<=osch_exec n a b')%R. *)
    (*         - by eapply osch_exec_mono'. *)
    (*         - lra. *)
    (*       } *)
    (*       erewrite osch_exec_mono_term in K1; last reflexivity. *)
    (*       * assert (SeriesC (λ x, if bool_decide (x ∈ [a'; b']) then osch_exec n a x else 0) <=1)%R as K2. *)
    (*         { trans (SeriesC (osch_exec n a)); last done. *)
    (*           apply SeriesC_le; last done. *)
    (*           intros. by case_match. *)
    (*         } *)
    (*         rewrite SeriesC_list in K2. *)
    (*         -- simpl in K2. *)
    (*            assert (osch_exec n a a' =1)%R as K3. *)
    (*            { apply Rle_antisym; first done. *)
    (*              rewrite -K1. *)
    (*              by apply osch_exec_mono'. *)
    (*            } *)
    (*            rewrite K3 in K2. *)
    (*            destruct (pmf_pos (osch_exec n a) b'); lra. *)
    (*         -- apply NoDup_cons; split; last apply NoDup_singleton. *)
    (*            set_solver. *)
    (*       * by erewrite <-pmf_1_eq_SeriesC. *)
    (* Qed. *)

    (* Lemma osch_lim_exec_final a b : *)
    (*   to_final a.2 = Some b → *)
    (*   osch_lim_exec a = dret a. *)
    (* Proof. *)
    (*   intros. erewrite (osch_lim_exec_det_final 0%nat); [done|done|]. *)
    (*   rewrite osch_pexec_O. by apply dret_1_1. *)
    (* Qed. *)

    Lemma osch_lim_exec_None a :
      osch a = None ->
      osch_lim_exec a = dret a.
    Proof.
      intros.
      apply distr_ext; intros [??].
      rewrite osch_lim_exec_unfold.
      symmetry.
      apply eq_rbar_finite.
      apply Rbar_le_antisym.
      - apply Sup_seq_minor_le with 0%nat.
        by rewrite osch_exec_is_none.
      - apply upper_bound_ge_sup.
        intros.
        by rewrite osch_exec_is_none.
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
    
    Lemma osch_lim_exec_pos_res x y:
      (osch_lim_exec x y > 0)%R ->
      osch y = None.
    Proof.
      intros H. apply osch_lim_exec_pos in H as [? H].
      by apply osch_exec_pos in H.
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

    (* osch_exec_val returns the val if final *)
    
    Definition osch_exec_val (n:nat) (ρ : osch_state * mdpstate (con_lang_mdp con_prob_lang)) : distr (val) :=
       (osch_exec n ρ) ≫= (λ ρ, match to_final ρ.2 with
                                | Some v => dret v
                                | None => dzero
                                end
        ).

    Lemma osch_exec_val_not_final_None ρ n :
      to_final ρ.2 = None -> osch ρ = None → osch_exec_val n ρ = dzero.
    Proof. destruct ρ as [?[??]]; destruct n; simpl; repeat case_match; rewrite /osch_exec_val /osch_exec; intros ? ->; rewrite dret_id_left; simpl; repeat case_match; simpl; by simplify_eq.
    Qed.
    
    Lemma osch_exec_val_Sn a n :
      osch_exec_val (S n) a = osch_step_or_none a ≫= osch_exec_val n.
    Proof.
      rewrite /osch_step_or_none /=.
      destruct a. simpl. rewrite /osch_step.
      repeat case_match; try done.
      - simpl.
        rewrite /osch_exec_val/osch_exec.
        case_match; last done.
        simplify_eq.
        rewrite -!dbind_assoc.
        apply dbind_ext_right.
        intros [??]. rewrite /dmap.
        rewrite -!dbind_assoc.
        apply dbind_ext_right.
        intros. by rewrite dret_id_left.
      - rewrite dret_id_left. rewrite /osch_exec_val.
        by rewrite !osch_exec_is_none.
    Qed.
    
    Lemma osch_exec_val_plus a n1 n2 :
      osch_exec_val (n1 + n2) a = osch_pexec n1 a ≫= osch_exec_val n2.
    Proof.
      revert a. induction n1.
      - intro a. rewrite osch_pexec_O dret_id_left //.
      - intro a. replace ((S n1 + n2)%nat) with ((S (n1 + n2))); auto.
        rewrite osch_exec_val_Sn osch_pexec_Sn.
        apply distr_ext.
        intro.
        rewrite -dbind_assoc.
        rewrite /pmf/=/dbind_pmf.
        erewrite SeriesC_ext; last first.
        { intros. by rewrite IHn1. }
        done.
    Qed.

    (* Not true *)
    (* Lemma osch_exec_val_pexec_relate a n: *)
    (*   osch_exec_val n a = osch_pexec n a ≫= *)
    (*                    (λ e, match to_final e.2 with *)
    (*                          | Some b => dret b *)
    (*                          | _ => dzero *)
    (*                          end). *)
    (* Proof. *)
    (*   revert a. *)
    (*   induction n; intros []. *)
    (*   - simpl. rewrite osch_pexec_O. *)
    (*     rewrite dret_id_left'. *)
    (*     rewrite /osch_exec_val/osch_exec. *)
    (*     repeat case_match; naive_solver. *)
    (*   - simpl. rewrite osch_pexec_Sn. *)
    (*     rewrite -dbind_assoc'. *)
    (*     case_match eqn:H. *)
    (*     + erewrite osch_step_or_none_is_final; last by eapply to_final_Some_2.  *)
    (*       rewrite dret_id_left'. *)
    (*       rewrite osch_pexec_is_final; last by eapply to_final_Some_2. *)
    (*       rewrite dret_id_left'. rewrite H. done. *)
    (*     + case_match. *)
    (*       * rewrite /osch_step_or_none/osch_step/=. *)
    (*         repeat case_match; try done. *)
    (*         simplify_eq. *)
    (*         rewrite -dbind_assoc. apply dbind_ext_right. *)
    (*         intros [??]. *)
    (*         rewrite -dbind_assoc. *)
    (*         apply dbind_ext_right. *)
    (*         intros ?. *)
    (*         by rewrite dret_id_left. *)
    (*       * rewrite osch_step_or_none_is_none; last done. *)
    (*         rewrite dret_id_left. rewrite -IHn. *)
    (*         by rewrite osch_exec_val_not_final_None. *)
    (* Qed. *)

    
    Lemma osch_exec_val_mono a n v :
      osch_exec_val n a v <= osch_exec_val (S n) a v.
    Proof.
      apply refRcoupl_eq_elim.
      move : a.
      induction n.
      - intros [].
        apply refRcoupl_from_leq.
        intros b. rewrite /distr_le /=.
        rewrite /osch_exec_val/osch_exec.
        repeat case_match; try done.
        by rewrite dbind_dzero dzero_0.
      - intros []; do 2 rewrite osch_exec_val_Sn.
        eapply refRcoupl_dbind; [|apply refRcoupl_eq_refl].
        by intros ? ? ->.
    Qed.

    Lemma osch_exec_val_mono' ρ n m v :
      n ≤ m → osch_exec_val n ρ v <= osch_exec_val m ρ v.
    Proof.
      eapply (mon_succ_to_mon (λ x, osch_exec_val x ρ v)).
      intro. apply osch_exec_val_mono.
    Qed.

    Lemma osch_exec_val_mono_term a b n m :
      SeriesC (osch_exec_val n a) = 1 →
      n ≤ m →
      osch_exec_val m a b = osch_exec_val n a b.
    Proof.
      intros Hv Hleq.
      apply Rle_antisym; [ |by apply osch_exec_val_mono'].
      destruct (decide (osch_exec_val m a b <= osch_exec_val n a b))
        as [|?%Rnot_le_lt]; [done|].
      exfalso.
      assert (1 < SeriesC (osch_exec_val m a)); last first.
      - assert (SeriesC (osch_exec_val m a) <= 1); [done|]. lra.
      - rewrite -Hv.
        apply SeriesC_lt; eauto.
        intros b'. by split; [|apply osch_exec_val_mono'].
    Qed.

    Lemma osch_exec_val_is_final_None a b m:
      to_final a.2 = Some b->
      osch a = None->
      osch_exec_val m a b = 1.
    Proof.
      rewrite /osch_exec_val.
      intros H ?.
      rewrite osch_exec_is_none; last done.
      rewrite dret_id_left.
      rewrite H.
      by apply dret_1_1.
    Qed.

    Lemma osch_exec_val_is_final a b m:
      to_final a.2 = Some b ->
      ∀ x, osch_exec_val m a x <= dret b x.
    Proof.
      revert a b.
      induction m; intros [?[l s]]? H.
      - intros x. rewrite /osch_exec_val/osch_exec.
        case_match.
        + rewrite dbind_dzero. done.
        + rewrite dret_id_left. by rewrite H.
      - intros x. rewrite osch_exec_val_Sn.
        rewrite /osch_step_or_none.
        case_match eqn : Heqn; last first.
        { rewrite dret_id_left. naive_solver. }
        rewrite /osch_step.
        rewrite Heqn. rewrite -dbind_assoc_pmf.
        rewrite {1}/dbind{1}/dbind_pmf{1}/pmf.
        trans (SeriesC (λ a, d a * dret b x)); last first.
        { rewrite SeriesC_scal_r. etrans; first apply Rmult_le_compat; [done|done| |done|].
          - apply pmf_SeriesC.
          - lra.
        }
        apply SeriesC_le; last first.
        { apply pmf_ex_seriesC_mult_fn; naive_solver. }
        intros [??].
        split; first (by apply Rmult_le_pos).
        apply Rmult_le_compat; try done.
        rewrite -/osch_exec_val.
        rewrite /dmap.
        rewrite -dbind_assoc_pmf.
        rewrite {1}/dbind{1}/dbind_pmf{1}/pmf.
        trans (SeriesC (λ a, step' n (l, s) a * dret b x)); last first.
        { rewrite SeriesC_scal_r. etrans; first apply Rmult_le_compat; [done|done| |done|].
          - apply pmf_SeriesC.
          - lra. }
        apply SeriesC_le; last first.
        { apply pmf_ex_seriesC_mult_fn; naive_solver. }
        intros [l0 s0]. split; first by apply Rmult_le_pos.
        destruct (pmf_pos (step' n (l,s)) (l0, s0)) as [Hpos|Hrewrite].
        + apply Rlt_gt in Hpos.
          apply Rmult_le_compat; try done.
          rewrite dret_id_left.
          apply IHm.
          simpl. simpl in *.
          destruct (l!!0%nat) eqn :Heqn1; last done.
          case_match; last first.
          { apply dret_pos in Hpos. simplify_eq. by rewrite Heqn1. }
          case_match.
          { apply dret_pos in Hpos. simplify_eq. by rewrite Heqn1. }
          apply dmap_pos in Hpos. destruct Hpos as [[[??]?][? Hstep]].
          simplify_eq.
          assert (0<length l)%nat.
          { destruct l; last (simpl; lia).
            by simpl in *. }
          destruct n.
          * rewrite lookup_app_l; last first. 
            { rewrite insert_length. lia.
            }
            rewrite list_lookup_insert; try done.
            rewrite Heqn1 in H0.
            simplify_eq.
          * rewrite lookup_app_l; last (rewrite insert_length; lia).
            rewrite list_lookup_insert_ne; last lia.
            by rewrite Heqn1.
        + rewrite -Hrewrite.
          lra.
    Qed.

    (* Lemma osch_pexec_exec_val_le_final n a a' b : *)
    (*   to_final a'.2 =Some b-> *)
    (*   osch_pexec n a a' <= osch_exec_val n a b. *)
    (* Proof. *)
    (*   intros. *)
    (*   revert a. induction n; intros a. *)
    (*   - rewrite osch_pexec_O. *)
    (*     destruct (decide (a = a')) as [->|]. *)
    (*     + erewrite osch_exec_val_is_final; last done. *)
    (*       rewrite !dret_1_1 //. *)
    (*     + rewrite dret_0 //. *)
    (*   - rewrite osch_exec_val_Sn osch_pexec_Sn. *)
    (*     destruct (decide (is_final a.2)) as [|]. *)
    (*     + erewrite osch_step_or_none_is_final; last done. *)
    (*       rewrite 2!dret_id_left -/osch_exec. *)
    (*       apply IHn. *)
    (*     + rewrite /osch_step_or_none. *)
    (*       repeat case_match; try done. *)
    (*       * rewrite !dret_id_left'. naive_solver. *)
    (*       * rewrite /dbind/dbind_pmf{1 4}/pmf/=. *)
    (*         apply SeriesC_le. *)
    (*         -- intros. split; real_solver. *)
    (*         -- apply pmf_ex_seriesC_mult_fn. *)
    (*            naive_solver. *)
    (*       * by rewrite !dret_id_left'. *)
    (* Qed. *)

    (* Lemma osch_pexec_exec_val_det n a a' b : *)
    (*   to_final a'.2 = Some b → *)
    (*   osch_pexec n a a' = 1 → osch_exec_val n a b = 1. *)
    (* Proof. *)
    (*   intros Hf. *)
    (*   pose proof (osch_pexec_exec_val_le_final n a a' b Hf). *)
    (*   pose proof (pmf_le_1 (osch_exec_val n a) b). *)
    (*   lra. *)
    (* Qed. *)

    (* Lemma osch_exec_val_pexec_val_neq_le n m a a' b b' : *)
    (*   to_final a'.2 = Some b' -> *)
    (*   b ≠ b' → osch_exec_val m a b + osch_pexec n a a' <= 1. *)
    (* Proof. *)
    (*   intros Hf Hneq. *)
    (*   etrans; [by eapply Rplus_le_compat_l, osch_pexec_exec_val_le_final|]. *)
    (*   etrans; [apply Rplus_le_compat_l, (osch_exec_val_mono' _ n (n `max` m)), Nat.le_max_l|]. *)
    (*   etrans; [apply Rplus_le_compat_r, (osch_exec_val_mono' _ m (n `max` m)), Nat.le_max_r|]. *)
    (*   etrans; [|apply (pmf_SeriesC (osch_exec_val (n `max` m) a))]. *)
    (*   apply pmf_plus_neq_SeriesC. *)
    (*   intro. simplify_eq. *)
    (* Qed. *)

    (* Lemma osch_pexec_exec_val_det_neg n m a a1 b b' : *)
    (*   to_final a1.2 = Some b → *)
    (*   osch_pexec n a a1 = 1 → *)
    (*   b' ≠ b → *)
    (*   osch_exec_val m a b' = 0. *)
    (* Proof. *)
    (*   intros Hf  Hexec Hv. *)
    (*   epose proof (osch_exec_val_pexec_val_neq_le n m a _ _ _ Hf _) as Hle. *)
    (*   Unshelve. *)
    (*   2: { done. } *)
    (*   2:{ done. } *)
    (*   rewrite Hexec in Hle. *)
    (*   pose proof (pmf_pos (osch_exec_val m a) b'). *)
    (*   simpl in *. *)
    (*   lra. *)
    (* Qed. *)

    Lemma is_finite_Sup_seq_osch_exec_val a b :
      is_finite (Sup_seq (λ n, osch_exec_val n a b)).
    Proof.
      apply (Rbar_le_sandwich 0 1).
      - by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
      - by apply upper_bound_ge_sup=>/=.
    Qed.

    Lemma is_finite_Sup_seq_SeriesC_osch_exec_val a :
      is_finite (Sup_seq (λ n, SeriesC (osch_exec_val n a))).
    Proof.
      apply (Rbar_le_sandwich 0 1).
      - by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
      - by apply upper_bound_ge_sup=>/=.
    Qed.

    (** * Full evaluation (limit of stratification) *)
    Definition osch_lim_exec_val (ρ : osch_state * mdpstate (con_lang_mdp con_prob_lang)) :=
      lim_distr (λ n, osch_exec_val n ρ) (osch_exec_val_mono ρ).

    
    Lemma osch_lim_exec_val_unfold a b :
      osch_lim_exec_val a b = Sup_seq (λ n, (osch_exec_val n a) b).
    Proof. apply lim_distr_pmf. Qed.

    Lemma osch_lim_exec_val_Sup_seq a :
      SeriesC (osch_lim_exec_val a) = Sup_seq (λ n, SeriesC (osch_exec_val n a)).
    Proof.
      erewrite SeriesC_ext; last first.
      { intros ?. rewrite osch_lim_exec_val_unfold //. }
      erewrite MCT_seriesC; eauto.
      - intros. apply osch_exec_val_mono.
      - intros. by eapply SeriesC_correct.
      - rewrite (Rbar_le_sandwich 0 1).
        + apply Sup_seq_correct.
        + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
        + by apply upper_bound_ge_sup=>/=.
    Qed.

    Lemma osch_lim_exec_val_step a :
      osch_lim_exec_val a = osch_step_or_none a ≫= osch_lim_exec_val.
    Proof.
      apply distr_ext.
      intro b.
      rewrite {2}/pmf /= /dbind_pmf.
      rewrite osch_lim_exec_val_unfold.
      setoid_rewrite osch_lim_exec_val_unfold.
      assert
        (SeriesC (λ a', osch_step_or_none a a' * Sup_seq (λ n, osch_exec_val n a' b)) =
         SeriesC (λ a', Sup_seq (λ n, osch_step_or_none a a' * osch_exec_val n a' b))) as Hrewrite.
      { apply SeriesC_ext; intro b'.
        apply eq_rbar_finite.
        rewrite rmult_finite.
        rewrite (rbar_finite_real_eq).
        - rewrite -Sup_seq_scal_l //.
        - apply (Rbar_le_sandwich 0 1).
          + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
          + by apply upper_bound_ge_sup=>/=. }
      rewrite Hrewrite.
      rewrite (MCT_seriesC _ (λ n, osch_exec_val (S n) a b) (osch_lim_exec_val a b)) //.
      - intros. by apply Rmult_le_pos.
      - intros.
        apply Rmult_le_compat; [done|done|done|].
        apply osch_exec_val_mono.
      - intros a'.
        exists (osch_step_or_none a a').
        intros n.
        rewrite <- Rmult_1_r. by apply Rmult_le_compat_l.
      - intro n.
        rewrite osch_exec_val_Sn.
        rewrite {3}/pmf/=/dbind_pmf.
        apply SeriesC_correct.
        apply (ex_seriesC_le _ (osch_step_or_none a)); [|done].
        intros a'. split.
        + by apply Rmult_le_pos.
        + rewrite <- Rmult_1_r. by apply Rmult_le_compat_l.
      - rewrite osch_lim_exec_val_unfold.
        rewrite mon_sup_succ.
        + rewrite (Rbar_le_sandwich 0 1).
          * apply Sup_seq_correct.
          * by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
          * by apply upper_bound_ge_sup=>/=.
        + intro; apply osch_exec_val_mono.
    Qed.

    Lemma osch_lim_exec_val_pexec n a :
      osch_lim_exec_val a = osch_pexec n a ≫= osch_lim_exec_val.
    Proof.
      move : a.
      induction n; intro a.
      - rewrite osch_pexec_O dret_id_left //.
      - rewrite osch_pexec_Sn -dbind_assoc/=.
        rewrite osch_lim_exec_val_step.
        apply dbind_eq; [|done].
        intros ??. apply IHn.
    Qed.

    (* Lemma osch_lim_exec_val_det_final n a a' b : *)
    (*   to_final a'.2 = Some b → *)
    (*   osch_pexec n a a' = 1 → *)
    (*   osch_lim_exec_val a = dret b. *)
    (* Proof. *)
    (*   intros Hb Hpe. *)
    (*   apply distr_ext. *)
    (*   intro b'. *)
    (*   rewrite osch_lim_exec_val_unfold. *)
    (*   rewrite {2}/pmf /= /dret_pmf. *)
    (*   case_bool_decide; simplify_eq. *)
    (*   - apply Rle_antisym. *)
    (*     + apply finite_rbar_le; [eapply is_finite_Sup_seq_osch_exec_val|]. *)
    (*       by apply upper_bound_ge_sup=>/=. *)
    (*     + apply rbar_le_finite; [eapply is_finite_Sup_seq_osch_exec_val|]. *)
    (*       apply (Sup_seq_minor_le _ _ n)=>/=. *)
    (*       by erewrite osch_pexec_exec_val_det. *)
    (*   - rewrite -(sup_seq_const 0). *)
    (*     f_equal. apply Sup_seq_ext=> m. *)
    (*     destruct (pmf_pos (osch_exec_val m a) b') as [|<-]; last done. *)
    (*     assert (osch_exec_val n a b = 1)%R as K1. *)
    (*     { apply Rle_antisym; first done. *)
    (*       rewrite -Hpe. *)
    (*       by eapply osch_pexec_exec_val_le_final. *)
    (*     } *)
    (*     destruct (Nat.le_ge_cases n m). *)
    (*     + erewrite <-osch_exec_val_mono_term in K1; last exact. *)
    (*       * assert (SeriesC (λ x, if bool_decide (x ∈ [b; b']) then osch_exec_val m a x else 0) <=1)%R as K2. *)
    (*         { trans (SeriesC (osch_exec_val m a)); last done. *)
    (*           apply SeriesC_le; last done. *)
    (*           intros. by case_match. *)
    (*         } *)
    (*         rewrite SeriesC_list in K2. *)
    (*         -- simpl in K2. *)
    (*            rewrite K1 in K2. *)
    (*            lra. *)
    (*         -- apply NoDup_cons; split; last apply NoDup_singleton. *)
    (*            set_solver. *)
    (*       * by erewrite <-pmf_1_eq_SeriesC. *)
    (*     + assert (osch_exec_val n a b' = 0)%R as K2; last first. *)
    (*       { destruct (pmf_pos (osch_exec_val m a) b') as [|]; last lra. *)
    (*         exfalso. *)
    (*         assert (osch_exec_val m a b'<=osch_exec_val n a b')%R. *)
    (*         - by eapply osch_exec_val_mono'. *)
    (*         - lra. *)
    (*       } *)
    (*       erewrite osch_exec_val_mono_term in K1; last reflexivity. *)
    (*       * assert (SeriesC (λ x, if bool_decide (x ∈ [b; b']) then osch_exec_val n a x else 0) <=1)%R as K2. *)
    (*         { trans (SeriesC (osch_exec_val n a)); last done. *)
    (*           apply SeriesC_le; last done. *)
    (*           intros. by case_match. *)
    (*         } *)
    (*         rewrite SeriesC_list in K2. *)
    (*         -- simpl in K2. *)
    (*            assert (osch_exec_val n a b =1)%R as K3. *)
    (*            { apply Rle_antisym; first done. *)
    (*              rewrite -K1. *)
    (*              by apply osch_exec_val_mono'. *)
    (*            } *)
    (*            rewrite K3 in K2. *)
    (*            destruct (pmf_pos (osch_exec_val n a) b'); lra. *)
    (*         -- apply NoDup_cons; split; last apply NoDup_singleton. *)
    (*            set_solver. *)
    (*       * by erewrite <-pmf_1_eq_SeriesC. *)
    (* Qed. *)

    Lemma osch_lim_exec_val_final a b :
      to_final a.2 = Some b →
      osch a = None->
      osch_lim_exec_val a b = 1.
    Proof.
      intros.
      apply Rle_antisym; first done.
      erewrite <-osch_exec_val_is_final_None; [|done..].
      rewrite osch_lim_exec_val_unfold.
      apply rbar_le_finite; last eapply Sup_seq_minor_le.
      - apply is_finite_Sup_seq_osch_exec_val.
      - done.
        Unshelve. exact 0%nat.
    Qed.

    Lemma osch_lim_exec_val_leq a b (r : R) :
      (∀ n, osch_exec_val n a b <= r) →
      osch_lim_exec_val a b <= r.
    Proof.
      intro Hexec.
      rewrite osch_lim_exec_val_unfold.
      apply finite_rbar_le; [apply is_finite_Sup_seq_osch_exec_val|].
      by apply upper_bound_ge_sup=>/=.
    Qed.

    Lemma osch_lim_exec_val_leq_mass  a r :
      (∀ n, SeriesC (osch_exec_val n a) <= r) →
      SeriesC (osch_lim_exec_val a) <= r.
    Proof.
      intro Hm.
      erewrite SeriesC_ext; last first.
      { intros. rewrite osch_lim_exec_val_unfold //. }
      erewrite (MCT_seriesC _ (λ n, SeriesC (osch_exec_val n a)) (Sup_seq (λ n, SeriesC (osch_exec_val n a)))); eauto.
      - apply finite_rbar_le; [apply is_finite_Sup_seq_SeriesC_osch_exec_val|].
        by apply upper_bound_ge_sup.
      - apply osch_exec_val_mono.
      - intros. by apply SeriesC_correct.
      - rewrite (Rbar_le_sandwich 0 1).
        + apply (Sup_seq_correct (λ n, SeriesC (osch_exec_val n a))).
        + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
        + by apply upper_bound_ge_sup=>/=.
    Qed.

    Lemma osch_lim_exec_val_term n a :
      SeriesC (osch_exec_val n a) = 1 →
      osch_lim_exec_val a = osch_exec_val n a.
    Proof.
      intro Hv.
      apply distr_ext=> b.
      rewrite osch_lim_exec_val_unfold.
      apply Rle_antisym.
      - apply finite_rbar_le; [apply is_finite_Sup_seq_osch_exec_val|].
        rewrite -/pmf.
        apply upper_bound_ge_sup.
        intros n'.
        destruct (decide (n <= n')) as [|?%Rnot_le_lt].
        + right. apply osch_exec_val_mono_term; [done|]. by apply INR_le.
        + apply osch_exec_val_mono'. apply INR_le. by left.
      - apply rbar_le_finite; [apply is_finite_Sup_seq_osch_exec_val|].
        apply (sup_is_upper_bound (λ m, osch_exec_val m a b) n).
    Qed.

    Lemma osch_lim_exec_val_pos a b :
      osch_lim_exec_val a b > 0 → ∃ n, osch_exec_val n a b > 0.
    Proof.
      intros.
      apply Classical_Pred_Type.not_all_not_ex.
      intros H'.
      assert (osch_lim_exec_val a b <= 0); [|lra].
      apply osch_lim_exec_val_leq => n.
      by apply Rnot_gt_le.
    Qed.

    Lemma osch_lim_exec_val_continuous_prob a ϕ r :
      (∀ n, prob (osch_exec_val n a) ϕ <= r) →
      prob (osch_lim_exec_val a) ϕ <= r.
    Proof.
      intro Hm.
      rewrite /prob.
      erewrite SeriesC_ext; last first.
      { intro; rewrite osch_lim_exec_val_unfold; auto. }
      assert
        (forall v, (if ϕ v then real (Sup_seq (λ n0 : nat, osch_exec_val n0 a v)) else 0) =
              (real (Sup_seq (λ n0 : nat, if ϕ v then osch_exec_val n0 a v else 0)))) as Haux.
      { intro v.
        destruct (ϕ v); auto.
        rewrite sup_seq_const //.
      }
      assert
        (is_finite (Sup_seq (λ n0 : nat, SeriesC (λ v, if ϕ v then osch_exec_val n0 a v else 0)))) as Hfin.
      {
        apply (Rbar_le_sandwich 0 1).
        + apply (Sup_seq_minor_le _ _ 0%nat); simpl.
          apply SeriesC_ge_0'.
          intro v; destruct (ϕ v); auto.
          lra.
        + apply upper_bound_ge_sup; intro; simpl; auto.
          apply (Rle_trans _ (SeriesC (osch_exec_val n a))); auto.
          apply (SeriesC_le _ (osch_exec_val n a)); auto.
          intro v; destruct (ϕ v); real_solver.
      }
      erewrite SeriesC_ext; last first.
      {
        intro; rewrite Haux //.
      }
      erewrite (MCT_seriesC _ (λ n, SeriesC (λ v, if ϕ v then osch_exec_val n a v else 0))
                  (Sup_seq (λ n0 : nat, SeriesC (λ v, if ϕ v then osch_exec_val n0 a v else 0))));
        auto.
      - apply finite_rbar_le; auto.
        apply upper_bound_ge_sup; auto.
      - intros n v.
        destruct (ϕ v); auto.
        lra.
      - intros n v.
        destruct (ϕ v); [ apply osch_exec_val_mono | lra].
      - intro v; destruct (ϕ v); exists 1; intro; auto; lra.
      - intros n.
        apply SeriesC_correct; auto.
        apply (ex_seriesC_le _ (osch_exec_val n a)); auto.
        intro v; destruct (ϕ v); real_solver.
      - rewrite (Rbar_le_sandwich 0 1); auto.
        + apply (Sup_seq_correct (λ n0 : nat, SeriesC (λ v, if ϕ v then osch_exec_val n0 a v else 0))).
        + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
          apply SeriesC_ge_0'.
          intro v; destruct (ϕ v); real_solver.
        + apply upper_bound_ge_sup; intro; simpl; auto.
          apply (Rle_trans _ (SeriesC (osch_exec_val n a))); auto.
          apply (SeriesC_le _ (osch_exec_val n a)); auto.
          intro v; destruct (ϕ v); real_solver.
    Qed.

    
    Lemma osch_lim_exec_val_is_final a b :
      to_final a.2 = Some b ->
      ∀ x, osch_lim_exec_val a x <= dret b x.
    Proof.
      intros H.
      intros x; rewrite osch_lim_exec_val_unfold.
      apply Rbar_le_fin; first done. 
      apply upper_bound_ge_sup.
      intros n.
      by apply osch_exec_val_is_final.
    Qed.
      
    
    Lemma osch_exec_exec_val a n:
      osch_exec_val n a = osch_exec n a ≫= (λ '(_, a'), match to_final a' with
                                                        | Some b => dret b
                                                        | None => dzero
                                                        end
                            ).
    Proof.
      rewrite /osch_exec_val; f_equal.
      extensionality e. by destruct e.
    Qed.

    Lemma osch_lim_exec_exec_val a:
      osch_lim_exec_val a = osch_lim_exec a ≫= (λ '(_, a'), match to_final a' with
                                                        | Some b => dret b
                                                        | None => dzero
                                                        end
                            ).
    Proof.
      apply distr_ext.
      intros b.
      apply Rle_antisym.
      - apply osch_lim_exec_val_leq; intros n. rewrite osch_exec_exec_val.
        rewrite /dbind/dbind_pmf{1 4}/pmf.
        apply SeriesC_le.
        + intros [??]. split.
          * case_match; real_solver.
          * apply Rmult_le_compat_r; first by case_match.
            (* rewrite osch_lim_exec_unfold. *)
            apply rbar_le_finite; last eapply Sup_seq_minor_le.
            -- apply is_finite_Sup_seq_osch_exec.
            -- done.
        + apply pmf_ex_seriesC_mult_fn. naive_solver.
      - trans (prob (osch_lim_exec a) (λ '(_, x), bool_decide (to_final x = Some b))).
        + rewrite /prob. rewrite /dbind/dbind_pmf{1}/pmf.
          right.
          apply SeriesC_ext.
          intros [??].
          case_match; case_bool_decide; simplify_eq.
          * rewrite dret_1_1; [lra|done].
          * rewrite dret_0; first lra.
            naive_solver.
          * rewrite dzero_0; lra.
        + apply osch_lim_exec_continuous_prob.
          intros n.
          revert a b.
          induction n; intros a b.
          * destruct a. simpl.
            repeat case_match.
            -- rewrite /prob.
               rewrite SeriesC_0; first done.
               intros []. case_bool_decide; last done.
               apply dzero_0. 
            -- destruct (decide (con_lang_mdp_to_final con_prob_lang m = Some b)) eqn:Heqn.
               ** rewrite prob_dret_true.
                  --- by rewrite osch_lim_exec_val_final.
                  --- by case_bool_decide.
               ** rewrite prob_dret_false; first done.
                  by case_bool_decide.
          * rewrite osch_exec_Sn.
            rewrite prob_dbind.
            trans (SeriesC
                     (λ a0, 
                        osch_step_or_none a a0 * osch_lim_exec_val a0 b )).
            -- apply SeriesC_le; last apply pmf_ex_seriesC_mult_fn; last naive_solver.
               intros [??]; split.
               ++ intros. apply Rmult_le_pos; first done.
                  apply prob_ge_0.
               ++ by apply Rmult_le_compat_l.
            -- by rewrite osch_lim_exec_val_step.
    Qed.        
  End step.

End oscheduler.

#[global] Arguments oscheduler (_) {_ _}.


Section osch_typeclasses.
  Class oTapeOblivious `{Countable osch_int_σ} (osch : oscheduler osch_int_σ) : Prop :=
    otape_oblivious :
     ∀ ζ ρ ρ', ρ.1 = ρ'.1 -> heap ρ.2 = heap ρ'.2 -> osch (ζ, ρ) = osch (ζ, ρ')
  .
  Global Arguments oTapeOblivious (_) {_ _} (_).

  Lemma osch_tape_oblivious `{oTapeOblivious si osch} ζ ρ ρ' :
    ρ.1 = ρ'.1 -> heap ρ.2 = heap ρ'.2 -> osch (ζ, ρ) = osch (ζ, ρ').
  Proof.
    apply otape_oblivious.
  Qed.

  Lemma osch_tape_oblivious_state_upd_tapes `{oTapeOblivious si osch} ζ α t σ es:
    osch (ζ, (es, state_upd_tapes <[α:=t]> σ)) = osch (ζ, (es, σ)).
  Proof.
    apply osch_tape_oblivious; by simpl.
  Qed.
  
End osch_typeclasses.

Lemma osch_to_sch `{Countable osch_int_σ} (osch : oscheduler osch_int_σ) `{Htape: !oTapeOblivious osch_int_σ osch} : ∃ (sch:scheduler (con_lang_mdp con_prob_lang) osch_int_σ), TapeOblivious osch_int_σ sch /\ ∀ x y, osch_lim_exec_val osch x y <= sch_lim_exec sch x y.
Proof.
  exists ({| scheduler_f := λ x, match osch x with Some d => d | _ => dzero end |}).
  split.
  - intros ?????. simpl. erewrite Htape; [|exact..]; done.
  - intros [o m]; simpl.
    intros v. 
    + apply osch_lim_exec_val_leq.
      intros n.
      revert o m.
      induction n; intros o m.
      * simpl.
        repeat case_match; [|by rewrite dzero_0..].
        rewrite /osch_exec_val/osch_exec.
        repeat case_match.
        -- rewrite dbind_dzero dzero_0. done.
        -- rewrite dret_id_left. case_match; last (by rewrite dzero_0).
           rewrite /dret/dret_pmf{1}/pmf.
           case_bool_decide; last done.
           simplify_eq.
           erewrite sch_lim_exec_final; last done.
           by rewrite dret_1_1.
      * destruct (to_final m)  as [v' |] eqn:Heqn.
        -- (* LHS  is smaller than dret *)
          erewrite sch_lim_exec_final; last done.
          by apply osch_exec_val_is_final.
        -- rewrite osch_exec_val_Sn.
           erewrite sch_lim_exec_step.
           rewrite /dbind/dbind_pmf{1 4}/pmf.
           apply SeriesC_le.
           ++ intros [o' m']; split; first real_solver.
              rewrite /osch_step_or_none/osch_step/sch_step_or_final/sch_step/=.
              destruct (con_lang_mdp_to_final con_prob_lang m) eqn :Heqn'.
              { rewrite /to_final in Heqn. simpl in *. naive_solver. }
              case_match; last first.
              { rewrite /dret/dret_pmf{1}/pmf.
                case_bool_decide.
                - simplify_eq.
                  rewrite Rmult_1_l.
                  rewrite osch_exec_val_not_final_None; try done.
                  rewrite dzero_0. by apply Rmult_le_pos.
                - rewrite Rmult_0_l. by apply Rmult_le_pos. 
              }
              apply Rmult_le_compat; try done.
              rewrite {1 2}/dbind{1 2}/dbind_pmf{1 4}/pmf.
              apply SeriesC_le; last first.
              { apply pmf_ex_seriesC_mult_fn; naive_solver. }
              intros [??]. split; first real_solver.
              apply Rmult_le_compat; try done.
              rewrite /dmap.
              rewrite {1 2}/dbind{1 2}/dbind_pmf{1 4}/pmf.
              apply SeriesC_le; last first.
              { apply pmf_ex_seriesC_mult_fn; naive_solver. }
              intros [??]. split; first real_solver.
              apply Rmult_le_compat; try done.
              rewrite /step'/con_lang_mdp_step.
              destruct m.
              destruct (mbind con_language.to_val _) eqn:Heqn1; last done.
              rewrite /con_lang_mdp_to_final in Heqn'. rewrite bind_Some in Heqn1.
              destruct Heqn1 as [?[H1 ?]].
              rewrite H1 in Heqn'. naive_solver.
           ++  apply pmf_ex_seriesC_mult_fn. naive_solver.
Qed.

(* Program Instance oTapeOblivious_inhabitant `{Countable sch_int_σ}: oTapeOblivious sch_int_σ (@inhabitant _ oscheduler_inhabited). *)
(* Next Obligation. *)
(*   naive_solver. *)
(* Qed. *)


