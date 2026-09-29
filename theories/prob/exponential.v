(** One-sided discrete exponential noise distribution — the new noise the
    [gen_prob_lang] generalization targets for report-noisy-max (the exponential
    mechanism).  Built by RESTRICTING the (already-defined) Laplace one-sided
    weights [laplace_f] to the non-negative support [z ≥ 0]; the normalization is
    then a single geometric series (vs Laplace's two-sided sum).  Provides
    [exp_dist ε loc] (centered at [loc], support [≥ loc]) and the rational-ε
    wrapper [exp_rat num den loc] with mass 1 — the [exp_family] analogue of
    [laplace_rat]. *)
From Stdlib Require Import Reals Psatz.
From clutch.prelude Require Import base.
From clutch.prob Require Export distribution.
From clutch.prob Require Import couplings_exp couplings_dp.

Local Open Scope R.

Section exponential.

  (** the one-sided weight: the Laplace weight on [z ≥ 0], else 0 *)
  Definition exp_f (ε : posreal) (z : Z) : R :=
    if bool_decide (0 <= z)%Z then laplace_f ε z else 0.

  Lemma exp_f_pos ε z : 0 <= exp_f ε z.
  Proof. rewrite /exp_f. case_bool_decide; [|lra]. rewrite /laplace_f. apply laplace_f_nat_pos. Qed.

  Lemma exp_f_le ε z : exp_f ε z <= laplace_f ε z.
  Proof.
    rewrite /exp_f. case_bool_decide; [lra|]. rewrite /laplace_f. apply laplace_f_nat_pos.
  Qed.

  Lemma ex_seriesC_exp_f ε : ex_seriesC (λ z, exp_f ε z).
  Proof.
    eapply (ex_seriesC_le _ (λ z, laplace_f ε z)); last apply ex_seriesC_laplace_f.
    intros z. split; [apply exp_f_pos | apply exp_f_le].
  Qed.

  Lemma exp_f_0 ε : exp_f ε 0 = 1.
  Proof.
    rewrite /exp_f bool_decide_eq_true_2; [|lia].
    rewrite /laplace_f /laplace_f_nat Z.abs_0 /=.
    replace (- 0 * ε)%R with 0%R by lra. apply exp_0.
  Qed.

  Lemma SeriesC_exp_f_pos ε : 0 < SeriesC (λ z, exp_f ε z).
  Proof.
    eapply Rlt_le_trans; last eapply (SeriesC_ge_elem _ 0%Z).
    - cbn beta. rewrite exp_f_0. lra.
    - intros; apply exp_f_pos.
    - apply ex_seriesC_exp_f.
  Qed.

  (** the centered one-sided exponential (support [z ≥ 0]) *)
  Program Definition exp' ε : distr Z :=
    MkDistr (λ z, exp_f ε z / SeriesC (λ z, exp_f ε z)) _ _ _.
  Next Obligation.
    intros. unfold Rdiv. apply Rmult_le_pos; [apply exp_f_pos|].
    left. apply Rinv_0_lt_compat, SeriesC_exp_f_pos.
  Qed.
  Next Obligation.
    intros. setoid_rewrite Rdiv_def. apply ex_seriesC_scal_r, ex_seriesC_exp_f.
  Qed.
  Next Obligation.
    intros. setoid_rewrite Rdiv_def. rewrite SeriesC_scal_r.
    apply Req_le, Rdiv_diag. pose proof (SeriesC_exp_f_pos ε). lra.
  Qed.

  Lemma exp'_mass ε : SeriesC (exp' ε) = 1.
  Proof.
    rewrite /exp' {1}/pmf. setoid_rewrite Rdiv_def. rewrite SeriesC_scal_r.
    apply Rdiv_diag. pose proof (SeriesC_exp_f_pos ε). lra.
  Qed.

  (** shifted to be centered at [loc] (support [z ≥ loc]) *)
  Program Definition exp_dist ε (loc : Z) : distr Z :=
    MkDistr (λ z, exp' ε (z - loc)%Z) _ _ _.
  Next Obligation. intros. apply pmf_pos. Qed.
  Next Obligation.
    intros.
    pose (h := (λ '(z1, z2), if bool_decide (z2 - z1 = loc)%Z then exp' ε z1 else 0)).
    apply (ex_seriesC_ext (λ z2, SeriesC (λ z1, h (z1, z2)))).
    { rewrite /h. intros z2. erewrite SeriesC_ext; first apply SeriesC_singleton_dependent.
      simpl. intros; repeat case_bool_decide; try done; lia. }
    apply fubini_pos_seriesC_ex_double; rewrite /h.
    - intros. case_bool_decide; [apply pmf_pos|done].
    - intros. eapply ex_seriesC_ext; last apply (ex_seriesC_singleton (loc + a)%Z).
      intros. simpl. repeat case_bool_decide; try lia; done.
    - eapply ex_seriesC_ext; last apply (pmf_ex_seriesC (exp' ε)).
      intros n. erewrite SeriesC_ext; first by erewrite (SeriesC_singleton (n + loc)%Z).
      intros. simpl. repeat case_bool_decide; try lia; done.
  Qed.
  Next Obligation.
    intros.
    pose (h := (λ '(z1, z2), if bool_decide (z2 - z1 = loc)%Z then exp' ε z1 else 0)).
    rewrite (SeriesC_ext _ (λ z, SeriesC (λ n, h (n, z)))).
    - rewrite fubini_pos_seriesC.
      + rewrite /h. erewrite (SeriesC_ext _ (exp' ε)).
        * apply pmf_SeriesC.
        * intros n. erewrite (SeriesC_ext _ (λ b, if bool_decide (b = n + loc)%Z then exp' ε n else 0));
            first by rewrite SeriesC_singleton.
          intros. repeat case_bool_decide; try lia; done.
      + rewrite /h. intros. case_bool_decide; [apply pmf_pos|done].
      + rewrite /h. intros n.
        apply (ex_seriesC_ext (λ b, if bool_decide (b = n + loc)%Z then exp' ε n else 0));
          last apply ex_seriesC_singleton.
        intros. repeat case_bool_decide; try lia; done.
      + rewrite /h. apply (ex_seriesC_ext (exp' ε)); last apply pmf_ex_seriesC.
        intros n. erewrite (SeriesC_ext _ (λ b, if bool_decide (b = n + loc)%Z then exp' ε n else 0));
          first by rewrite SeriesC_singleton.
        intros. repeat case_bool_decide; try lia; done.
    - intros n. rewrite /h.
      erewrite (SeriesC_ext _ (λ b, if bool_decide (b = n - loc)%Z then exp' ε b else 0));
        first by rewrite SeriesC_singleton_dependent.
      intros. repeat case_bool_decide; try lia; done.
  Qed.

  Lemma exp_dist_mass ε loc : SeriesC (exp_dist ε loc) = 1.
  Proof.
    rewrite -(exp'_mass ε).
    apply SeriesC_translate; [intros; apply pmf_pos | apply pmf_ex_seriesC].
  Qed.

  (** the rational-ε wrapper, mirroring [laplace_rat] *)
  Definition exp_rat (num den loc : Z) : distr Z :=
    match decide (0 < IZR num / IZR den)%R with
    | left εpos => exp_dist (mkposreal (IZR num / IZR den) εpos) loc
    | right _ => dret loc
    end.

  Lemma exp_rat_mass num den loc : SeriesC (exp_rat num den loc) = 1.
  Proof.
    rewrite /exp_rat. case_decide; [apply exp_dist_mass | apply dret_mass].
  Qed.

  (** The exact center-shift (isometry) coupling, at ZERO cost: shifting the
      location by [loc - loc'] maps [exp_dist ε loc] onto [exp_dist ε loc']
      exactly (both are pure translates of [exp']).  This is the one-sided
      exponential analogue of [Mcoupl_laplace_isometry], and the building block
      for the non-argmax coordinates of report-noisy-max with exponential noise. *)
  Lemma Mcoupl_exp_isometry (ε : posreal) (loc loc' : Z) :
    Mcoupl (exp_dist ε loc) (exp_dist ε loc') (λ z z', z - z' = loc - loc')%Z 0.
  Proof.
    intros ?? Hf Hg Hfg.
    rewrite exp_0. ring_simplify.
    rewrite -(SeriesC_translate _ (loc - loc')).
    2:{ intros. apply Rmult_le_pos. 1: auto. apply Hf. }
    2:{ eapply ex_seriesC_le. 2: apply (pmf_ex_seriesC (exp_dist ε loc)).
        intros z. simpl. split.
        - apply Rmult_le_pos => //. apply Hf.
        - destruct (Hf z). etrans. 2: right ; apply Rmult_1_r.
          apply Rmult_le_compat => //. }
    apply SeriesC_le.
    2:{ eapply ex_seriesC_le. 2: apply (pmf_ex_seriesC (exp_dist ε loc')).
        intros z. simpl. split.
        - apply Rmult_le_pos => //. apply Hg.
        - destruct (Hg z). etrans. 2: right ; apply Rmult_1_r.
          apply Rmult_le_compat => //. }
    intros z. split.
    { apply Rmult_le_pos => //. apply Hf. }
    opose proof (Hfg ((z + (loc - loc'))) z _)%Z. 1: lia.
    apply Rmult_le_compat => //. 1: apply Hf.
    (* [exp_dist ε loc (z + (loc-loc')) = exp_dist ε loc' z]: both are [exp']
       at the same offset, since [(z+(loc-loc')) - loc = z - loc']. *)
    right.
    assert (Hd : ∀ l w, exp_dist ε l w = exp' ε (w - l)%Z) by reflexivity.
    rewrite !Hd. f_equal. lia.
  Qed.

  (** The shift coupling WITH cost — the per-coordinate DP coupling for
      report-noisy-max with one-sided exponential noise.  Coupling the impl draw
      [z] (from [exp_dist ε loc]) to the spec draw [z' = z + k] (from
      [exp_dist ε loc']) costs [k' · ε], provided the shift is *upward* enough to
      stay in the (one-sided) target support — [0 ≤ k + loc - loc'] — and the
      offset is bounded — [k + loc - loc' ≤ k'].  (Contrast Laplace, two-sided:
      it needs only [|k+loc-loc'| ≤ k'] and no directionality.)  The one-sided
      directionality is exactly what makes this the exponential mechanism. *)
  Lemma Mcoupl_exp ε (loc loc' k k' : Z)
    (Hdir : (0 <= k + loc - loc')%Z) (Hdist : (k + loc - loc' <= k')%Z) :
    Mcoupl (exp_dist ε loc) (exp_dist ε loc') (λ z z', z + k = z')%Z (IZR k' * ε).
  Proof.
    intros ?? Hf Hg Hfg.
    rewrite -SeriesC_scal_l.
    assert (∀ z : Z, 0 <= exp_dist ε loc z * f z).
    { intros. apply Rmult_le_pos => //. apply Hf. }
    rewrite -(SeriesC_translate _ (-k)) => //.
    2:{ eapply ex_seriesC_le. 2: apply (pmf_ex_seriesC (exp_dist ε loc)).
        intros z. simpl. split => //.
        destruct (Hf z). etrans. 2: right ; apply Rmult_1_r. apply Rmult_le_compat => //. }
    apply SeriesC_le.
    2:{ apply ex_seriesC_scal_l.
        eapply ex_seriesC_le. 2: apply (pmf_ex_seriesC (exp_dist ε loc')).
        intros z. simpl. split.
        - apply Rmult_le_pos => //. apply Hg.
        - destruct (Hg z). etrans. 2: right ; apply Rmult_1_r. apply Rmult_le_compat => //. }
    intros z. split. { apply Rmult_le_pos => //. apply Hf. }
    rewrite -Rmult_assoc.
    opose proof (Hfg ((z - k))%Z z _). 1: lia.
    apply Rmult_le_compat => //. 1: apply Hf.
    (* [exp_dist ε loc (z-k) ≤ exp(k'·ε) * exp_dist ε loc' z]; cancel the shared
       normaliser, then case on the one-sided supports. *)
    assert (Hd : ∀ l w, exp_dist ε l w = exp' ε (w - l)%Z) by reflexivity.
    rewrite !Hd.
    assert (He : ∀ A, exp' ε A = exp_f ε A / SeriesC (λ z, exp_f ε z)) by reflexivity.
    rewrite !He !Rdiv_def -Rmult_assoc.
    apply Rmult_le_compat_r.
    { left. apply Rinv_0_lt_compat, SeriesC_exp_f_pos. }
    rewrite /exp_f.
    case_bool_decide as HA1; last first.
    { apply Rmult_le_pos; [left; apply exp_pos|].
      case_bool_decide; [rewrite /laplace_f; apply laplace_f_nat_pos | lra]. }
    case_bool_decide as HA2; last first.
    { exfalso. lia. }
    (* both offsets non-negative: pure exp ratio *)
    rewrite /laplace_f /laplace_f_nat.
    rewrite -exp_plus. apply exp_mono.
    rewrite !Z.abs_eq; try lia.
    rewrite !INR_IZR_INZ !Z2Nat.id; try lia.
    pose proof (cond_pos ε).
    (* The goal's offset is normalised to [z + - k - loc]; match it in [Hb] so
       [nra]'s atoms line up (a [z - k - loc] form would be a distinct atom). *)
    assert (Hb : (IZR (z - loc') - IZR (z + - k - loc) <= IZR k')%R).
    { rewrite -minus_IZR. apply IZR_le. lia. }
    nra.
  Qed.

End exponential.
