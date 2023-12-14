(* TODO: this is leftover from merging developments: most of this theory now
   exists for arbitrary markov chains, see [prob/markov.v]. Some theory, however,
   like [exec_cfg] and [lim_exec_cfg] does not exist so should be ported. *)
From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Lim_seq.
From stdpp Require Import relations.
From clutch.common Require Import language.
From clutch.prob Require Import distribution couplings.

(** Distribution for [n]-step partial evaluation *)
Section exec.
  Context {Λ : language}.
  Implicit Types ρ : cfg Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.

  Definition prim_step_or_val (ρ : cfg Λ) : distr (cfg Λ) :=
    match to_val ρ.1 with
    | Some v => dret ρ
    | None => prim_step ρ.1 ρ.2
    end.

  Lemma prim_step_or_val_no_val e σ :
    to_val e = None → prim_step_or_val (e, σ) = prim_step e σ.
  Proof. rewrite /prim_step_or_val /=. by intros ->. Qed.

  Lemma prim_step_or_val_is_val e σ :
    is_Some (to_val e) → prim_step_or_val (e, σ) = dret (e, σ).
  Proof. rewrite /prim_step_or_val /=. by intros [? ->]. Qed.

  Definition exec (n : nat) ρ : distr (cfg Λ) := iterM n prim_step_or_val ρ.

  Lemma exec_O ρ :
    exec 0 ρ = dret ρ.
  Proof. done. Qed.

  Lemma exec_Sn ρ n :
    exec (S n) ρ = prim_step_or_val ρ ≫= exec n.
  Proof. done. Qed.

  Lemma exec_plus ρ n m :
    exec (n + m) ρ = exec n ρ ≫= exec m.
  Proof. rewrite /exec iterM_plus //.  Qed.

  Lemma exec_1 :
    exec 1 = prim_step_or_val.
  Proof.
    extensionality ρ; destruct ρ as [e σ].
    rewrite exec_Sn /exec /= dret_id_right //.
  Qed.

  Lemma exec_Sn_r e σ n :
    exec (S n) (e, σ) = exec n (e, σ) ≫= prim_step_or_val.
  Proof.
    assert (S n = n + 1)%nat as -> by lia.
    rewrite exec_plus exec_1 //.
  Qed.
    
  Lemma exec_det_step n ρ e1 e2 σ1 σ2 :
    prim_step e1 σ1 (e2, σ2) = 1 →
    exec n ρ (e1, σ1) = 1 →
    exec (S n) ρ (e2, σ2) = 1.
  Proof.
    destruct ρ as [e0 σ0].
    rewrite exec_Sn_r.
    intros H ->%pmf_1_eq_dret.
    rewrite dret_id_left /=.
    case_match; [|done].
    assert (to_val e1 = None); [|simplify_eq].
    eapply val_stuck. erewrite H. lra.
  Qed.

  Lemma exec_det_step_ctx K `{!LanguageCtx K} n ρ e1 e2 σ1 σ2 :
    prim_step e1 σ1 (e2, σ2) = 1 →
    exec n ρ (K e1, σ1) = 1 →
    exec (S n) ρ (K e2, σ2) = 1.
  Proof.
    intros. eapply exec_det_step; [|done].
    rewrite -fill_step_prob //.
    eapply (val_stuck _ σ1 (e2, σ2)). lra.
  Qed.

  Lemma exec_PureExec_ctx K `{!LanguageCtx K} (P : Prop) m n ρ e e' σ :
    P →
    PureExec P n e e' →
    exec m ρ (K e, σ) = 1 →
    exec (m + n) ρ (K e', σ) = 1.
  Proof.
    move=> HP /(_ HP).
    destruct ρ as [e0 σ0].
    revert e e' m. induction n=> e e' m.
    { rewrite -plus_n_O. by inversion 1. }
    intros (e'' & Hsteps & Hpstep)%nsteps_inv_r Hdet.
    specialize (IHn _ _ m Hsteps Hdet).
    rewrite -plus_n_Sm.
    eapply exec_det_step_ctx; [done| |done].
    apply Hpstep.
  Qed.

End exec.

Global Arguments exec {_} _ _ : simpl never.

(** Distribution for evaluation ending in a value in less than [n]-step *)
Section exec_val.
  Context {Λ : language}.
  Implicit Types ρ : cfg Λ.
  Implicit Types e : expr Λ.
  Implicit Types v : val Λ.
  Implicit Types σ : state Λ.

  Fixpoint exec_val (n : nat) (ρ : cfg Λ) {struct n} : distr (val Λ) :=
    match to_val ρ.1, n with
      | Some v, _ => dret v
      | None, 0 => dzero
      | None, S n => prim_step ρ.1 ρ.2 ≫= exec_val n
    end.

  Fixpoint exec_cfg (n : nat) (ρ : cfg Λ) {struct n} : distr (cfg Λ) :=
    match to_val ρ.1, n with
      | Some _, _ => dret ρ
      | None, 0 => dzero
      | None, S n => prim_step ρ.1 ρ.2 ≫= exec_cfg n
    end.

  Lemma exec_val_unfold (n : nat) :
    exec_val n = λ ρ,
      match to_val ρ.1, n with
      | Some v, _ => dret v
      | None, 0 => dzero
      | None, S n => prim_step ρ.1 ρ.2 ≫= exec_val n
      end.
  Proof. by destruct n. Qed.

  Lemma exec_val_is_val v e σ n :
    to_val e = Some v → exec_val n (e, σ) = dret v.
  Proof. destruct n; simpl; by intros ->. Qed.

  Lemma exec_val_Sn (ρ : cfg Λ) (n: nat) :
    exec_val (S n) ρ = prim_step_or_val ρ ≫= exec_val n.
  Proof.
    destruct ρ as [e σ].
    rewrite /prim_step_or_val /=.
    destruct (to_val e) eqn:Hv=>/=; [|done].
    rewrite dret_id_left -/exec_val.
    fold exec_val.
    erewrite exec_val_is_val; eauto.
  Qed.

  Lemma exec_val_mon ρ n v :
    exec_val n ρ v <= exec_val (S n) ρ v.
  Proof.
    apply refRcoupl_eq_elim.
    move : ρ.
    induction n.
    - intros.
      apply refRcoupl_from_leq.
      intros w. rewrite /distr_le /=.
      by case_match.
    - intros; do 2 rewrite exec_val_Sn.
      eapply refRcoupl_dbind; [|apply refRcoupl_eq_refl].
      by intros ? ? ->.
  Qed.

  Lemma exec_cfg_is_val v e σ n :
    to_val e = Some v →  exec_cfg n (e, σ) = dret (of_val v, σ).
  Proof.
    intros.
    apply of_to_val in H; subst.
    destruct n; simpl; intros; by rewrite to_of_val.
  Qed.
  
  Lemma exec_cfg_Sn (ρ : cfg Λ) (n: nat) :
    exec_cfg (S n) ρ = prim_step_or_val ρ ≫= exec_cfg n.
  Proof.
    destruct ρ as [e σ].
    rewrite /prim_step_or_val /=.
    destruct (to_val e) eqn:Hv=>/=; [|done].
    rewrite dret_id_left -/exec_cfg.
    fold exec_cfg.
    epose proof (exec_cfg_is_val _ _ _ _ Hv) as Hv'.
    erewrite Hv'.
    apply of_to_val in Hv. by subst.
  Qed.
  
  Lemma exec_cfg_mon ρ n ρ':
    exec_cfg n ρ ρ' <= exec_cfg (S n) ρ ρ'.
  Proof.
    apply refRcoupl_eq_elim.
    move : ρ.
    induction n.
    - intros.
      apply refRcoupl_from_leq.
      intros w. rewrite /distr_le /=.
      by case_match.
    - intros; do 2 rewrite exec_cfg_Sn.
      eapply refRcoupl_dbind; [|apply refRcoupl_eq_refl].
      by intros ? ? ->.
  Qed.

  Lemma exec_val_mon' ρ n m v :
    n ≤ m → exec_val n ρ v <= exec_val m ρ v.
  Proof.
    eapply (mon_succ_to_mon (λ x, exec_val x ρ v)); intro; apply exec_val_mon.
  Qed.

  Lemma exec_val_Sn_not_val e σ n :
    to_val e = None →
    exec_val (S n) (e, σ) = prim_step e σ ≫= exec_val n.
  Proof. intros ?. rewrite exec_val_Sn prim_step_or_val_no_val //. Qed.

  Lemma exec_exec_val_le n ρ v σ :
    exec n ρ (of_val v, σ) <= exec_val n ρ v.
  Proof.
    revert ρ. induction n; intros [e σ'].
    - rewrite exec_O.
      destruct (decide ((e, σ') = (of_val v, σ))) as [[= -> ->]|].
      + rewrite (exec_val_is_val v); [|auto using to_of_val].
        rewrite !dret_1_1 //.
      + rewrite dret_0 //.
    - rewrite exec_Sn exec_val_Sn.
      destruct (to_val e) as [w|] eqn:Heq.
      + rewrite prim_step_or_val_is_val //.
        rewrite 2!dret_id_left -/exec_val.
        apply IHn.
      + rewrite prim_step_or_val_no_val //.
        rewrite /pmf /= /dbind_pmf.
        eapply SeriesC_le.
        * intros ρ. split.
          { by apply Rmult_le_pos. }
          apply Rmult_le_compat; by auto.
        * eapply pmf_ex_seriesC_mult_fn.
          exists 1. by intros ρ.
  Qed.

  Lemma exec_exec_val_det n ρ v σ :
    exec n ρ (of_val v, σ) = 1 → exec_val n ρ v = 1.
  Proof.
    intros ?.
    pose proof (exec_exec_val_le n ρ v σ).
    pose proof (pmf_le_1 (exec_val n ρ) v).
    lra.
  Qed.

  Lemma exec_exec_val_neq_le n m ρ v v' σ :
    v ≠ v' → exec_val m ρ v' + exec n ρ (of_val v, σ) <= 1.
  Proof.
    intros Hneq.
    eapply Rle_trans; [apply Rplus_le_compat_l, exec_exec_val_le | ].
    eapply Rle_trans; [apply Rplus_le_compat_l,
        (exec_val_mon' _ n (n `max` m)), Nat.le_max_l | ].
    eapply Rle_trans; [apply Rplus_le_compat_r,
        (exec_val_mon' _ m (n `max` m)), Nat.le_max_r | ].
    eapply Rle_trans; [ | apply (pmf_SeriesC (exec_val (n `max` m) ρ)) ].
    apply pmf_plus_neq_SeriesC; auto.
  Qed.

  Lemma exec_exec_val_det_neg n m ρ v v' σ :
    exec n ρ (of_val v, σ) = 1 →
    v ≠ v' →
    exec_val m ρ v' = 0.
  Proof.
    intros Hexec Hv.
    pose proof (exec_exec_val_neq_le n m ρ v v' σ Hv) as H.
    rewrite Hexec in H.
    pose proof (pmf_pos (exec_val m ρ) v').
    lra.
  Qed.

End exec_val.

(** Limit of [prim_exec]  *)
Section prim_exec_lim.
  Context {Λ : language}.
  Implicit Types ρ : cfg Λ.
  Implicit Types e : expr Λ.
  Implicit Types v : val Λ.
  Implicit Types σ : state Λ.

  Definition lim_exec_val (ρ : cfg Λ) : distr (val Λ):=
    lim_distr (λ n, exec_val n ρ) (exec_val_mon ρ).

  Definition lim_exec_cfg (ρ : cfg Λ) : distr (cfg Λ) :=
    lim_distr (λ n, exec_cfg n ρ) (exec_cfg_mon ρ).
  
  Lemma lim_exec_val_rw (ρ : cfg Λ) v :
    lim_exec_val ρ v = Sup_seq (λ n, (exec_val n ρ) v).
  Proof.
    rewrite lim_distr_pmf; auto.
  Qed.

  Lemma lim_exec_val_prim_step (ρ : cfg Λ) :
    lim_exec_val ρ = prim_step_or_val ρ ≫= lim_exec_val.
  Proof.
   apply distr_ext.
   intro v.
   rewrite lim_exec_val_rw/=.
   rewrite {2}/pmf/=/dbind_pmf.
   setoid_rewrite lim_exec_val_rw.
   assert
     (SeriesC (λ a : cfg Λ, prim_step_or_val ρ a * Sup_seq (λ n : nat, exec_val n a v)) =
     SeriesC (λ a : cfg Λ, Sup_seq (λ n : nat, prim_step_or_val ρ a * exec_val n a v))) as H.
   { apply SeriesC_ext; intro v'.
     apply eq_rbar_finite.
     rewrite rmult_finite.
     rewrite (rbar_finite_real_eq (Sup_seq (λ n : nat, exec_val n v' v))); auto.
     - rewrite <- (Sup_seq_scal_l (prim_step_or_val ρ v') (λ n : nat, exec_val n v' v)); auto.
     - apply (Rbar_le_sandwich 0 1).
       + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
       + apply upper_bound_ge_sup; intro; simpl; auto.
   }
   rewrite H.
   rewrite (MCT_seriesC _ (λ n, exec_val (S n) ρ v) (lim_exec_val ρ v)); auto.
   - intros; apply Rmult_le_pos; auto.
   - intros.
     apply Rmult_le_compat; auto; [apply Rle_refl | apply exec_val_mon]; auto.
   - intro.
     exists (prim_step_or_val ρ a); intro.
     rewrite <- Rmult_1_r.
     apply Rmult_le_compat_l; auto.
   - intro n.
     rewrite exec_val_Sn.
     rewrite {3}/pmf/=/dbind_pmf.
     apply SeriesC_correct; auto.
     apply (ex_seriesC_le _ (prim_step_or_val ρ)); auto.
     intro; split; auto.
     + apply Rmult_le_pos; auto.
     + rewrite <- Rmult_1_r.
       apply Rmult_le_compat_l; auto.
   - rewrite lim_exec_val_rw.
     rewrite mon_sup_succ.
     + rewrite (Rbar_le_sandwich 0 1); auto.
       * apply (Sup_seq_correct (λ n : nat, exec_val (S n) ρ v)).
       * apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
       * apply upper_bound_ge_sup; intro; simpl; auto.
     + intro; apply exec_val_mon.
  Qed.

  Lemma lim_exec_val_exec n (ρ : cfg Λ) :
    lim_exec_val ρ = exec n ρ ≫= lim_exec_val.
  Proof.
    move : ρ.
    induction n; intro ρ.
    - rewrite exec_O.
      rewrite dret_id_left; auto.
    - rewrite exec_Sn -dbind_assoc/=.
      rewrite lim_exec_val_prim_step.
      apply dbind_eq; [|done].
      intros ??. apply IHn.
  Qed.


  (** * strengthen this lemma? *)
  
  Lemma lim_exec_bind_continuity_1 e σ ν v:
    (lim_exec_cfg (e, σ) ≫= (λ s, ν s)) v =
    Sup_seq (λ n, (exec_cfg n (e, σ) ≫= (λ s, ν s)) v).
  Proof.
    rewrite /pmf /= /dbind_pmf.
    rewrite /lim_exec_cfg.
    assert (SeriesC (λ a : cfg Λ, lim_distr (λ n : nat, exec_cfg n (e, σ)) (exec_cfg_mon (e, σ)) a * ν a v) = SeriesC (λ a : cfg Λ, Sup_seq (λ n : nat, exec_cfg n (e, σ) a) * ν a v)) as H by f_equal.
    rewrite H. clear H.
    pose (h := λ n a, exec_cfg n (e, σ) a * ν a v).
    assert (SeriesC (λ a : cfg Λ, Sup_seq (λ n : nat, exec_cfg n (e, σ) a) * ν a v) =
            SeriesC (λ a : cfg Λ, Sup_seq (λ n : nat, h n a))).
    { f_equal. apply functional_extensionality_dep => s. rewrite /h.
      rewrite Rmult_comm. apply eq_rbar_finite. rewrite rmult_finite rbar_finite_real_eq; last first.
      { apply (is_finite_bounded 0 1).
        - apply (Sup_seq_minor_le _ _ 0). apply pmf_pos.
        - apply upper_bound_ge_sup => n. apply pmf_le_1.
      }
      rewrite -Sup_seq_scal_l; [|done].
      f_equal. apply functional_extensionality_dep => n. rewrite Rmult_comm. done.
    }
    rewrite H. clear H.
    rewrite /h. clear h.
    eapply MCT_seriesC; intros.
    - by apply Rmult_le_pos.
    - apply Rmult_le_compat_r; [done|apply exec_cfg_mon].
    - exists 1. intros. replace 1 with (1*1); [by apply Rmult_le_compat|lra].
    - apply SeriesC_correct.
      eapply (ex_seriesC_le _ (λ a, exec_cfg n (e, σ) a)).
      + intros; split; [by apply Rmult_le_pos|].
        rewrite <-Rmult_1_r.
        by apply Rmult_le_compat_l.
      + apply pmf_ex_seriesC.
    - rewrite (Rbar_le_sandwich 0 1).
      + eapply is_sup_seq_ext; last first.
        { eapply Sup_seq_correct. }
        intros => /=. done.
      + eapply (Sup_seq_minor_le _ _ 0%nat). apply SeriesC_ge_0' => ?.
        by apply Rmult_le_pos.
      + apply upper_bound_ge_sup => n.
        trans ((exec_cfg n (e, σ) ≫= λ a, ν a) v ).
        -- by rewrite {3}/pmf.
        -- apply pmf_le_1.
  Qed.

    
  (** * strengthen this lemma? *)
  
  Lemma lim_exec_bind_continuity_2 (μ : distr (cfg Λ)) v `{!LanguageCtx K}:
    (μ ≫= (λ '(e, σ), lim_exec_val ((K e), σ) )) v =
    Sup_seq (λ n, (μ ≫= (λ '(e, σ), exec_val n ((K e), σ))) v).
  Proof.
    rewrite {1}/pmf /= /dbind_pmf.
    rewrite {3}/pmf /= /dbind_pmf.
    rewrite /lim_exec_val.
    assert (SeriesC
    (λ a : expr Λ * state Λ,
       μ a *
         (let '(e, σ) := a in lim_distr (λ n : nat, exec_val n (K e, σ)) (exec_val_mon (K e, σ))) v) =
            SeriesC
    (λ a : expr Λ * state Λ,
       μ a *
         (let '(e, σ) := a in Sup_seq (λ n : nat, exec_val n (K e, σ) v) )
           )) as H.
    { f_equal. apply functional_extensionality_dep => e. destruct e. f_equal. }
    rewrite H. clear H.
    assert (SeriesC
              (λ a : expr Λ * state Λ, μ a * (let '(e, σ) := a in Sup_seq (λ n : nat, exec_val n (K e, σ) v)))=
           SeriesC
             (λ a : expr Λ * state Λ, Sup_seq (λ n : nat, μ a * (let '(e, σ) := a in exec_val n (K e, σ) v)))) as H.
    { f_equal. apply functional_extensionality_dep => e. destruct e.
      apply eq_rbar_finite. rewrite rmult_finite rbar_finite_real_eq; last first.
      { apply (is_finite_bounded 0 1).
        - apply (Sup_seq_minor_le _ _ 0). apply pmf_pos.
        - apply upper_bound_ge_sup => n. apply pmf_le_1.
      }
      rewrite -Sup_seq_scal_l; [|done].
      f_equal.
    }
    rewrite H. clear H.
    eapply MCT_seriesC; intros.
    - destruct a. by apply Rmult_le_pos.
    - apply Rmult_le_compat_l; [done|]. destruct a. apply exec_val_mon.
    - exists 1. intros. destruct a. replace 1 with (1*1); [by apply Rmult_le_compat|lra].
    - apply SeriesC_correct.
      pose (ν := λ a, let '(e, σ) := a in exec_val n (K e, σ) v).
      assert (ex_seriesC (λ a : expr Λ * state Λ, μ a * (let '(e, σ) := a in exec_val n (K e, σ) v))
              = ex_seriesC (λ a : expr Λ * state Λ, μ a * ν a)) as H by f_equal.
      rewrite H.
      eapply pmf_ex_seriesC_mult_fn. exists 1. intros [e σ]. rewrite /ν. split; done.
    - rewrite (Rbar_le_sandwich 0 1).
      + eapply is_sup_seq_ext; last first.
        { eapply Sup_seq_correct. }
        intros. simpl. repeat f_equal. apply functional_extensionality_dep. by intros [e σ].
      + eapply (Sup_seq_minor_le _ _ 0%nat). apply SeriesC_ge_0' => ?.
        apply Rmult_le_pos; done.
      + apply upper_bound_ge_sup => n.
        trans ((μ ≫= λ '(e, σ), exec_val n (K e, σ)) v).
        -- by rewrite {3}/pmf /= /dbind_pmf.
        -- apply pmf_le_1.
  Qed.

  
  Lemma lim_exec_val_context_bind `{!LanguageCtx K} e σ:
    lim_exec_val (K e, σ) =
    lim_exec_cfg (e, σ) ≫= λ '(e', σ'), lim_exec_val (K e', σ').
  Proof.
    apply distr_le_antisym; rewrite /distr_le; intros v;
      [unfold lim_exec_val|]; rewrite lim_distr_pmf; rewrite lim_exec_bind_continuity_1.
    - apply Rbar_le_fin.
      { apply Rbar_0_le_to_Rle. apply (Sup_seq_minor_le _ _ 0). apply pmf_pos. }
      rewrite rbar_finite_real_eq; last first.
      { eapply is_finite_bounded.
        ++ apply (Sup_seq_minor_le _ _ 0). rewrite /lim_exec_val. apply pmf_pos.
        ++ apply upper_bound_ge_sup => ?. apply pmf_le_1.
      }
      apply Sup_seq_le.
      intros n; revert e σ v; induction n => e σ v/=.
      ++ destruct (to_val e) eqn:H1; destruct (to_val (K e)) eqn:H2.
         --- rewrite dret_id_left. rewrite /lim_exec_val lim_distr_pmf.
             apply rbar_le_finite.
             { apply (is_finite_bounded 0 1).
               +++ apply (Sup_seq_minor_le _ _ 0). apply pmf_pos.
               +++ apply upper_bound_ge_sup => n. apply pmf_le_1.
             }
             eapply (Sup_seq_minor_le _ _ 0). simpl; rewrite H2. lra.
         --- replace (dzero v) with 0.
             2:{ done. }
             apply pmf_pos.
         --- apply fill_not_val in H1. rewrite H1 in H2. inversion H2.
         --- replace (dzero v) with 0.
             2:{ done. }
             apply pmf_pos.
      ++ destruct (to_val e) eqn:H1; destruct (to_val (K e)) eqn:H2.
         --- rewrite dret_id_left. rewrite /lim_exec_val lim_distr_pmf.
             apply rbar_le_finite.
             { apply (is_finite_bounded 0 1).
               +++ apply (Sup_seq_minor_le _ _ 0). apply pmf_pos.
               +++ apply upper_bound_ge_sup => ?. apply pmf_le_1.
             }
             eapply (Sup_seq_minor_le _ _ 0). simpl; rewrite H2. lra.
         --- rewrite dret_id_left. rewrite -exec_val_Sn_not_val; last done.
             unfold lim_exec_val. rewrite lim_distr_pmf.
             eapply rbar_le_finite.
             { apply (is_finite_bounded 0 1).
               +++ apply (Sup_seq_minor_le _ _ 0). apply pmf_pos.
               +++ apply upper_bound_ge_sup => ?. apply pmf_le_1.
             }
             eapply (Sup_seq_minor_le _ _ (S n)). done.
         --- apply fill_not_val in H1. rewrite H1 in H2. inversion H2.
         --- rewrite fill_dmap; last done. rewrite /dmap.
             rewrite -!dbind_assoc -/exec_cfg -/exec_val.
             revert v. apply distr_le_dbind. { apply distr_le_refl. }
             intros [e' σ']. unfold distr_le. intros v.
             rewrite dret_id_left. simpl.
             apply IHn.
    - apply Rbar_le_fin.
      { apply Rbar_0_le_to_Rle. apply (Sup_seq_minor_le _ _ 0). apply pmf_pos. }
      rewrite rbar_finite_real_eq; last first.
      { eapply is_finite_bounded.
        ++ by eapply (Sup_seq_minor_le _ _ 0).
        ++ apply upper_bound_ge_sup => n. apply pmf_le_1.
      }
      pose (μ := λ n (s : cfg Λ), exec_cfg n s).
      assert (Sup_seq (λ n : nat, (exec_cfg n (e, σ) ≫= (λ '(e', σ'), lim_exec_val (K e', σ'))) v) =
               Sup_seq (λ n : nat, Sup_seq (λ m, ((μ n) (e, σ) ≫= (λ '(e', σ'), exec_val m (K e', σ'))) v))) as H.
      { rewrite /μ. apply Sup_seq_ext => ?.
        rewrite lim_exec_bind_continuity_2 rbar_finite_real_eq;[f_equal|].
        apply (is_finite_bounded 0 1).
        ++ apply (Sup_seq_minor_le _ _ 0). apply pmf_pos.
        ++ apply upper_bound_ge_sup => n. apply pmf_le_1.
      }
      rewrite H.
      rewrite /μ. clear H μ.
      pose (μ := λ '(n, m), ((exec_cfg n (e, σ) ≫= (λ '(e', σ'), exec_val m (K e', σ'))) v)).
      assert (Sup_seq
                (λ n : nat, Sup_seq (λ m : nat, (exec_cfg n (e, σ) ≫= (λ '(e', σ'), exec_val m (K e', σ'))) v)) =
             Sup_seq
               (λ n : nat, Sup_seq (λ m : nat, μ (n, m)) )) as -> by f_equal.
      rewrite sup_seq_swap.
      apply upper_bound_ge_sup => m.
      replace (Sup_seq (λ n : nat, exec_val n (K e, σ) v)) with (Sup_seq (λ n : nat, exec_val (n+m) (K e, σ) v)); last first.
      { apply sup_seq_eq_antisym => n; try by eexists _.
        eexists n. apply exec_val_mon'. lia.
      }
      rewrite /μ. clear μ.
      apply Sup_seq_le => n. revert e σ m v.
      induction n => e σ m v.
      ++ destruct (to_val e) eqn:H1; destruct (to_val (K e)) eqn:H2.
         all: simpl; rewrite H1; try rewrite dret_id_left; try rewrite dbind_dzero; try rewrite H2.
         all: done.
      ++ destruct (to_val e) eqn:H1; destruct (to_val (K e)) eqn:H2.
         all: simpl; rewrite H1; try rewrite dret_id_left; try rewrite H2.
         --- erewrite exec_val_is_val; done.
         --- rewrite -prim_step_or_val_no_val; [|done]. rewrite -exec_val_Sn.
             apply exec_val_mon'. lia.
         --- apply fill_not_val in H1. rewrite H1 in H2. inversion H2.
         --- rewrite fill_dmap; last done. rewrite /dmap.
             rewrite -!dbind_assoc -/exec_cfg -/exec_val.
             revert v. apply distr_le_dbind. { apply distr_le_refl. }
             intros [e' σ']. unfold distr_le. intros v.
             rewrite dret_id_left. simpl.
             apply IHn.
  Qed.

  Lemma lim_exec_cfg_lim_exec_val_relate e σ v: SeriesC (λ σ', lim_exec_cfg (e, σ) (of_val v, σ')) = lim_exec_val (e, σ) v.
    Proof.
assert ( (λ σ', lim_exec_cfg (e, σ) (of_val v, σ')) = (λ σ', Sup_seq (λ n, exec_cfg n (e, σ) (of_val v, σ')))).
    { apply functional_extensionality_dep. by intros. }
    rewrite H.
    assert (SeriesC (λ σ', Sup_seq (λ n : nat, exec_cfg n (e, σ) (of_val v, σ'))) = Sup_seq (λ n, SeriesC (λ σ', exec_cfg n (e, σ) (of_val v, σ')))).
    { eapply MCT_seriesC.
      - by intros.
      - intros. apply exec_cfg_mon.
      - intros.
        by exists 1.
      - intros. apply SeriesC_correct. apply ex_distr_lmarg.
      - rewrite (Rbar_le_sandwich 0 1).
        + eapply is_sup_seq_ext; last first.
          { eapply Sup_seq_correct. }
          intros; done.
        + eapply (Sup_seq_minor_le _ _ 0%nat). apply SeriesC_ge_0' => ?. done.
        + apply upper_bound_ge_sup => n.
          assert ((SeriesC (λ σ', exec_cfg n (e, σ) (of_val v, σ'))) = lmarg (exec_cfg n (e, σ)) (of_val v)).
          { rewrite lmarg_pmf. done. }
          rewrite H0.
          apply pmf_le_1.
    }
    rewrite H0. clear H0 H. rewrite lim_exec_val_rw.
    repeat f_equal. apply functional_extensionality_dep.
    intros n. revert e σ.
    induction n; intros.
    - simpl. destruct (to_val e) eqn:H.
      + apply of_to_val in H.
        rewrite /dret/pmf/dret_pmf.
        case_bool_decide.
        -- assert ((λ σ', dret (e, σ) (of_val v, σ')) = (dret σ)).
           { apply functional_extensionality_dep. intros.
             unfold dret, pmf, dret_pmf.
             repeat case_bool_decide; try done.
             + inversion H1. done.
             + subst. done.
           }
           rewrite H1. f_equal. apply dret_mass.
        -- assert ( (λ σ', if bool_decide ((of_val v, σ') = (e, σ)) then 1 else 0) = dzero).
           { apply functional_extensionality_dep. intros. case_bool_decide.
             - inversion H1. subst. apply of_to_val_flip in H3. rewrite to_of_val in H3.
               inversion H3. done.
             - done.
           }
         rewrite H1. f_equal. apply dzero_mass.
      + replace (dzero _) with 0; [|done].
        f_equal. eapply SeriesC_0. intros. done.
    - destruct (to_val e) eqn:H.
      + erewrite SeriesC_ext; last first.
        { intros. simpl. rewrite H. done. }
        simpl. rewrite H.
        rewrite /dret/pmf/dret_pmf.
        case_bool_decide.
        -- subst.
           assert ((λ n0 : state Λ, if bool_decide ((of_val v0, n0) = (e, σ)) then 1 else 0) = dret σ).
           { apply functional_extensionality_dep. intros.
             unfold dret, pmf, dret_pmf.
             repeat case_bool_decide; try done.
             + inversion H0. done.
             + subst. apply of_to_val in H. by subst.
           }
           rewrite H0. f_equal. apply dret_mass.
        -- assert ((λ n0 : state Λ, if bool_decide ((of_val v, n0) = (e, σ)) then 1 else 0) = dzero).
           { apply functional_extensionality_dep. intros. case_bool_decide.
             - inversion H1. subst. rewrite to_of_val in H.
               inversion H. done.
             - done.
           }
         rewrite H1. f_equal. apply dzero_mass.
      + simpl. rewrite H.
        rewrite /dbind/pmf/=/dbind_pmf.
        assert (SeriesC (λ σ', SeriesC (λ a : cfg Λ, prim_step e σ a * exec_cfg n a (of_val v, σ'))) =
               SeriesC (λ a: cfg Λ, SeriesC (λ σ', prim_step e σ a * exec_cfg n a (of_val v, σ')))).
        { rewrite distr_double_swap_lmarg. f_equal. }
        rewrite H0. clear H0.
        assert (SeriesC (λ a : cfg Λ, SeriesC (λ σ', prim_step e σ a * exec_cfg n a (of_val v, σ'))) =
                SeriesC (λ a : cfg Λ, prim_step e σ a * SeriesC (λ σ', exec_cfg n a (of_val v, σ')))).
        { f_equal. apply functional_extensionality_dep. intros. rewrite SeriesC_scal_l. done. }
        rewrite H0. clear H0.
        repeat f_equal. apply functional_extensionality_dep.
        intros []. f_equal. apply Rbar_finite_eq. apply IHn.
  Qed.
  
  (** * strengthen lemma? *)
  Lemma ssd_fix_value_lim_exec_val_lim_exec_cfg e σ (v : val Λ):
    SeriesC (ssd (λ '(e', σ'), bool_decide (to_val e' = Some v)) (lim_exec_cfg (e, σ))) =
    SeriesC (ssd (λ e' : val Λ, bool_decide (e' = v)) (lim_exec_val (e, σ))).
  Proof.
    rewrite {2}/ssd {2}/pmf/ssd_pmf.
    pose (id := λ a: val Λ, a).
    assert ( SeriesC (λ a : val Λ, if bool_decide (a = v) then lim_exec_val (e, σ) a else 0) =
      (SeriesC (λ a : val Λ, if bool_decide (id a = v) then lim_exec_val (e, σ) v else 0))).
    { f_equal. apply functional_extensionality_dep.
      intros. rewrite /id. case_bool_decide; by subst. }
    rewrite H.
    rewrite SeriesC_singleton_inj; [|eauto]. clear H id.
    
    replace (SeriesC _) with
            (SeriesC (λ σ', lim_exec_cfg (e, σ) (of_val v, σ'))); last first.
    { erewrite <-(dmap_mass _ (λ s, s.2)). f_equal.
      apply functional_extensionality_dep.
      intros.
      rewrite /dmap.
      rewrite {2}/pmf/=/dbind_pmf.
      replace (SeriesC _) with (SeriesC (λ s, if bool_decide (s = (of_val v, x)) then lim_exec_cfg (e, σ) (of_val v, x) else 0)).
      2: { f_equal. apply functional_extensionality_dep. intros [].
           case_bool_decide; rewrite /ssd {2}/pmf/=/ssd_pmf; first case_bool_decide.
           - inversion H. rewrite dret_1_1; [|done]. by rewrite Rmult_1_r.
           - inversion H. subst. rewrite to_of_val in H0. done.
           - rewrite /pmf. case_bool_decide.
             + apply of_to_val in H0. rewrite H0 in H.
               replace (dret_pmf _ _) with 0; [lra|].
               assert (s ≠ x); [intro; by subst|].
               rewrite /dret_pmf. case_bool_decide; [done|lra].
             + lra.
      }
      rewrite SeriesC_singleton_inj; eauto.
    }
    apply lim_exec_cfg_lim_exec_val_relate.
Qed.
    
    
    
  
  Lemma lim_exec_val_exec_det n ρ (v : val Λ) σ :
    exec n ρ (of_val v, σ) = 1 →
    lim_exec_val ρ = dret v.
  Proof.
    intro Hv.
    apply distr_ext.
    intro v'.
    rewrite lim_exec_val_rw.
    rewrite {2}/pmf/=/dret_pmf.
    assert (is_finite (Sup_seq (λ n, exec_val n ρ v'))) as Haux.
    {
      apply (Rbar_le_sandwich 0 1).
      + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
      + apply upper_bound_ge_sup; intro; simpl; auto.
    }
    case_bool_decide; simplify_eq.
    - apply Rle_antisym.
      + apply finite_rbar_le; auto.
        apply upper_bound_ge_sup.
        intro; simpl; auto.
      + apply rbar_le_finite; auto.
        apply (Sup_seq_minor_le _ _ n); simpl; auto.
        destruct ρ as (e2 & σ2).
        eapply exec_exec_val_det in Hv.
        rewrite Hv //.
    - rewrite -(sup_seq_const 0).
      f_equal. apply Sup_seq_ext=> m.
      f_equal. by eapply exec_exec_val_det_neg.
  Qed.

  Lemma lim_exec_val_val e σ v :
    to_val e = Some v →
    lim_exec_val (e, σ) = dret v.
  Proof.
    intros. erewrite (lim_exec_val_exec_det 0%nat); [done|].
    rewrite exec_O. erewrite of_to_val; [|done]. by apply dret_1_1.
  Qed.
    
  Lemma lim_exec_val_continous ρ1 v r :
    (∀ n, exec_val n ρ1 v <= r) → lim_exec_val ρ1 v <= r.
  Proof.
    intro Hexec.
    rewrite lim_exec_val_rw.
    assert (is_finite (Sup_seq (λ n : nat, exec_val n ρ1 v))) as Haux.
    {
      apply (Rbar_le_sandwich 0 1); auto.
      + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
      + apply upper_bound_ge_sup; intro; simpl; auto.
    }
    apply finite_rbar_le; auto.
    apply upper_bound_ge_sup.
    intro; simpl; auto.
  Qed.

Lemma lim_exec_positive_ast n ρ :
  SeriesC (exec_val n ρ) = 1 →
  lim_exec_val ρ = exec_val n ρ.
Proof.
    intro Hv.
    apply distr_ext.
    intro v.
    rewrite lim_exec_val_rw.
    assert (is_finite (Sup_seq (λ n, exec_val n ρ v))) as Haux.
    {
      apply (Rbar_le_sandwich 0 1).
      + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
      + apply upper_bound_ge_sup; intro; simpl; auto.
    }
    assert (forall m, (n <= m)%nat -> exec_val m ρ v = exec_val n ρ v ) as Haux2.
    {
      intros m Hleq.
      apply Rle_antisym; [ | apply exec_val_mon'; auto ].
      destruct (decide (exec_val m ρ v <= exec_val n ρ v)) as [Hdec | Hdec]; auto.
      apply Rnot_le_lt in Hdec.
      exfalso.
      assert (1 < SeriesC (exec_val m ρ)); last first.
      - assert (SeriesC (exec_val m ρ) <= 1); auto; lra.
      - rewrite <- Hv.
        apply SeriesC_lt; eauto.
        intro v'; split; [ | apply exec_val_mon']; auto.
    }
    apply Rle_antisym.
    - apply finite_rbar_le; auto.
      (* Why does pmf unfold here? *)
      rewrite -/pmf.
      apply upper_bound_ge_sup; intro n'.
      destruct (decide (n <= n')) as [Hdec | Hdec].
      + right. apply Haux2.
        apply INR_le; auto.
      + apply exec_val_mon'.
        apply Rnot_le_lt in Hdec.
        apply INR_le.
        auto with arith.
        left; auto.
    - apply rbar_le_finite; auto.
      (* It seems Coq cannot infer the first argument because of the order in which the n0 is used *)
      apply (sup_is_upper_bound (λ n0 : nat, exec_val n0 ρ v) n).
Qed.

Lemma lim_exec_continous_mass a r :
    (∀ n, SeriesC (exec_val n a) <= r) →
    SeriesC (lim_exec_val a) <= r.
Proof.
  intro Hm.
  erewrite SeriesC_ext; last first.
  { intro; rewrite lim_exec_val_rw; auto. }
  assert (is_finite (Sup_seq (λ n : nat, SeriesC (exec_val n a)))) as Haux.
  {
    apply (Rbar_le_sandwich 0 1).
    + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
    + apply upper_bound_ge_sup; intro; simpl; auto.
  }
  erewrite (MCT_seriesC _ (λ n, SeriesC (exec_val n a)) (Sup_seq (λ n : nat, SeriesC (exec_val n a)))); auto.
  - apply finite_rbar_le; auto.
    apply upper_bound_ge_sup; auto.
  - apply exec_val_mon.
  - intro; exists 1; intro; auto.
  - intros.
    apply SeriesC_correct; auto.
  - rewrite (Rbar_le_sandwich 0 1); auto.
    + apply (Sup_seq_correct (λ n : nat, SeriesC (exec_val n a))).
    + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
    + apply upper_bound_ge_sup; intro; simpl; auto.
Qed.

End prim_exec_lim.
