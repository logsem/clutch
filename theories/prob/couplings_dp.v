From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Lim_seq Rbar.
From stdpp Require Export countable.
From clutch.prelude Require Export base Coquelicot_ext Reals_ext stdpp_ext.
From clutch.prob Require Export countable_sum distribution couplings graded_predicate_lifting couplings_app couplings_exp.

Open Scope R.


Section couplings.
  Context `{Countable A, Countable B, Countable A', Countable B'}.
  Context (μ1 : distr A) (μ2 : distr B) (S : A -> B -> Prop).

  Definition DPcoupl (ε : R) (δ : R):=
    ∀ (f : A → R) (g : B -> R)
      (Hf : ∀ a, 0 <= f a <= 1)
      (Hg : ∀ b, 0 <= g b <= 1)
      (Hfg : ∀ a b, S a b -> f a <= g b),
      SeriesC (λ a, μ1 a * f a) <= exp(ε) * SeriesC (λ b, μ2 b * g b) + δ.

End couplings.

Section couplings_theory.
  Context `{Countable A, Countable B, Countable A', Countable B'}.


  Lemma exp_mono (r s : R) : r <= s -> exp r <= exp s.
  Proof.
    intros [| ->].
    + left.
      by apply exp_increasing.
    + lra.
  Qed.


  Lemma exp_pos_ge_1 (r : R) : 0 <= r -> 1 <= exp r.
  Proof.
    intros.
    trans (exp 0); last by apply exp_mono.
    by rewrite exp_0.
  Qed.


  Lemma DPcoupl_mono (μ1 μ1': distr A') (μ2 μ2': distr B') R R' ε ε' δ δ':
    (∀ a, μ1 a = μ1' a) ->
    (∀ b, μ2 b = μ2' b) ->
    (∀ x y, R x y -> R' x y) ->
    (ε <= ε') ->
    (δ <= δ') ->
    DPcoupl μ1 μ2 R ε δ ->
    DPcoupl μ1' μ2' R' ε' δ'.
  Proof.
    intros Hμ1 Hμ2 HR Hε Hδ Hcoupl f g Hf Hg Hfg.
    specialize (Hcoupl f g Hf Hg).
    replace (μ1') with μ1; last by apply distr_ext.
    replace (μ2') with μ2; last by apply distr_ext.
    trans (exp(ε) * SeriesC (λ b, μ2 b * g b) + δ).
    - apply Hcoupl.
      naive_solver.
    - apply Rplus_le_compat; auto.
      apply Rmult_le_compat_r; first by series.
      by apply exp_mono.
  Qed.


  Lemma DPcoupl_1 (μ1 : distr A') (μ2 : distr B') R ε δ:
    (1 <= δ) -> DPcoupl μ1 μ2 R ε δ.
  Proof.
    rewrite /DPcoupl.
    intros Hδ f g Hf Hg Hfg.
    trans 1.
    - trans (SeriesC μ1); last auto.
      apply SeriesC_le; last auto.
      real_solver.
    - replace 1 with (0+1); last lra.
      apply Rplus_le_compat; last lra.
      apply Rmult_le_pos; [left; apply exp_pos |].
      apply SeriesC_ge_0'; real_solver.
  Qed.


  Lemma DPcoupl_mon_grading (μ1 : distr A') (μ2 : distr B') (R : A' → B' → Prop) ε1 ε2 δ1 δ2:
    (ε1 <= ε2) ->
    (δ1 <= δ2) ->
    DPcoupl μ1 μ2 R ε1 δ1 ->
    DPcoupl μ1 μ2 R ε2 δ2.
  Proof.
    intros Hleq.
    by apply DPcoupl_mono.
  Qed.


  Lemma DPcoupl_dret (a : A) (b : B) (R : A → B → Prop) ε δ :
    0 <= ε →
    0 <= δ →
    R a b → DPcoupl (dret a) (dret b) R ε δ.
  Proof.
    intros Hε Hδ HR f g Hf Hg Hfg.
    assert (SeriesC (λ a0 : A, dret a a0 * f a0) = f a) as ->.
    { rewrite <-(SeriesC_singleton a (f a)).
      rewrite /pmf/=/dret_pmf ; series.
    }
    assert (SeriesC (λ b0 : B, dret b b0 * g b0) = g b) as ->.
    { rewrite <-(SeriesC_singleton b (g b)).
      rewrite /pmf/=/dret_pmf ; series.
    }
    specialize (Hfg _ _ HR).
    rewrite <- (Rmult_1_l (f a)).
    rewrite <- (Rplus_0_r (1 * f a)).
    apply Rplus_le_compat; auto.
    apply Rmult_le_compat; [real_solver | real_solver | | auto].
    by apply exp_pos_ge_1.
  Qed.


  (* The hypothesis (0 ≤ δ1) is not really needed, I just kept it for symmetry *)
  Lemma DPcoupl_dbind (f : A → distr A') (g : B → distr B')
    (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A' → B' → Prop) ε1 ε2 δ1 δ2:
    (0 <= δ1) ->
    (0 <= δ2) ->
    (∀ a b, R a b → DPcoupl (f a) (g b) S ε2 δ2) → DPcoupl μ1 μ2 R ε1 δ1 → DPcoupl (dbind f μ1) (dbind g μ2) S (ε1 + ε2) (δ1 + δ2).
  Proof.
    intros Hδ1 Hδ2 Hcoup_fg Hcoup_R h1 h2 Hh1pos Hh2pos Hh1h2S.
    rewrite /pmf/=/dbind_pmf.
    (* To use the hypothesis that we have an R-ACoupling up to ε1 for μ1, μ2,
       we have to rewrite the sums in such a way as to isolate (the expectation
       of) a random variable X on the LHS and Y on the RHS, and ε1 on the
       RHS. *)
    (* First step: rewrite the LHS into a RV X on μ1. *)
    setoid_rewrite <- SeriesC_scal_r.
    rewrite <-(fubini_pos_seriesC (λ '(a,x), μ1 x * f x a * h1 a)).

    (* Boring Fubini sideconditions. *)
    2: { real_solver. }
    2: { intro a'.
         (* specialize (Hh1pos a'). *)
         apply (ex_seriesC_le _ μ1); auto.
         intro a; split.
         + apply Rmult_le_pos.
           * real_solver.
           * real_solver.
         + rewrite <- Rmult_1_r.
           rewrite Rmult_assoc.
           apply Rmult_le_compat_l; auto.
           rewrite <- Rmult_1_r.
           apply Rmult_le_compat; real_solver. }
    2: { setoid_rewrite SeriesC_scal_r.
         apply (ex_seriesC_le _ (λ a : A', SeriesC (λ x : A, μ1 x * f x a))); auto.
         + series.
         + apply (pmf_ex_seriesC (dbind f μ1)). }

    (* LHS: Pull the (μ1 b) factor out of the inner sum. *)
    assert (SeriesC (λ b : A, SeriesC (λ a : A', μ1 b * f b a * h1 a)) =
              SeriesC (λ b : A, μ1 b * SeriesC (λ a : A', f b a * h1 a))) as ->.
    { setoid_rewrite <- SeriesC_scal_l. series. }

    (* Second step: rewrite the RHS into a RV Y on μ2. *)
    (* RHS: Fubini. *)
    rewrite <-(fubini_pos_seriesC (λ '(b,x), μ2 x * g x b * h2 b)).
    2: by series.
    2:{ intro b'.
        specialize (Hh2pos b').
        apply (ex_seriesC_le _ μ2) ; auto.
        intro b; split.
        - series.
        - do 2 rewrite <- Rmult_1_r. series. }
    2:{ setoid_rewrite SeriesC_scal_r.
        apply (ex_seriesC_le _ (λ a : B', SeriesC (λ b : B, μ2 b * g b a))); auto.
        - intros b'; specialize (Hh2pos b'); split.
          + apply Rmult_le_pos; [ | lra].
            apply (pmf_pos ((dbind g μ2)) b').
          + rewrite <- Rmult_1_r.
            apply Rmult_le_compat_l; auto.
            * apply SeriesC_ge_0'. real_solver.
            * real_solver.
        - apply (pmf_ex_seriesC (dbind g μ2)). }

    (* RHS: Factor out (μ2 b) *)
    assert (SeriesC (λ b : B, SeriesC (λ a : B', μ2 b * g b a * h2 a))
            = SeriesC (λ b : B, μ2 b * SeriesC (λ a : B', g b a * h2 a))) as ->.
    { apply SeriesC_ext; intro.
      rewrite <- SeriesC_scal_l.
      apply SeriesC_ext; real_solver. }

    rewrite -Rplus_assoc.
    apply Rle_minus_l.


    (* To construct X, we want to push ε2 into the inner sum. We don't do this
       directly, because X might be larger than 1, but
       our assumption on the ε1 R-ACoupling requires it to be valued in [0,1].
       Instead, we take min(1, exp(ε2) * (Σ(a:A')(f b a * h1 a))).
       ALT: could use a more fine-grained min inside the sum?
     *)

    assert (exp (ε1) * SeriesC (λ b : B, μ2 b * (Rmin 1 (exp (ε2) * SeriesC (λ a : B', g b a * h2 a)))) + δ1
            <= exp (ε1 + ε2) * SeriesC (λ b : B, μ2 b * SeriesC (λ a : B', g b a * h2 a)) + δ1) as <-.
    {
       apply Rplus_le_compat_r.
       rewrite exp_plus.
       rewrite Rmult_assoc.
       rewrite -(SeriesC_scal_l _ (exp ε2)).
       apply Rmult_le_compat_l; [left; apply exp_pos |].
       apply SeriesC_le.
       - intros b; split.
         + apply Rmult_le_pos; auto.
           apply Rmin_glb; [lra |].
           apply Rmult_le_pos; [left; apply exp_pos |].
           apply SeriesC_ge_0'.
           real_solver.
         + rewrite Rmult_min_distr_l; auto.
           etrans; [apply Rmin_r | lra].
       - apply ex_seriesC_scal_l.
         apply (ex_seriesC_le _ μ2); auto.
         intro b; split.
         + apply Rmult_le_pos; auto.
           apply SeriesC_ge_0'.
           intro; apply Rmult_le_pos; auto.
           apply Hh2pos.
         + rewrite <- Rmult_1_r.
           apply Rmult_le_compat_l; auto.
           apply (Rle_trans _ (SeriesC (g b))); auto.
           apply SeriesC_le; auto.
           real_solver.
    }

    assert (
        SeriesC (λ b : A, μ1 b * SeriesC (λ a : A', f b a * h1 a)) - δ2
        <= SeriesC (λ b : A, μ1 b * Rmax 0 (SeriesC (λ a : A', f b a * h1 a) - δ2))
      ) as ->.
    {
      apply (Rle_trans _ (SeriesC (λ b : A, μ1 b * SeriesC (λ a : A', f b a * h1 a) - μ1 b * δ2))).
      - rewrite SeriesC_minus.
        + apply Rplus_le_compat_l.
          apply Ropp_le_contravar.
          rewrite SeriesC_scal_r.
          real_solver.
        + apply (ex_seriesC_le _ μ1); auto.
         intro a; split.
         * apply Rmult_le_pos; auto.
           apply SeriesC_ge_0'.
           intro; apply Rmult_le_pos; auto.
           apply Hh1pos.
         * rewrite <- Rmult_1_r.
           apply Rmult_le_compat_l; auto.
           apply (Rle_trans _ (SeriesC (f a))); auto.
           apply SeriesC_le; auto.
           real_solver.
        + apply ex_seriesC_scal_r; auto.
      - apply SeriesC_le'.
        + intros a.
          rewrite -Rmult_minus_distr_l.
          apply Rmult_le_compat_l; auto.
          apply Rmax_r.
        + apply ex_seriesC_plus.
          * apply (ex_seriesC_le _ μ1); auto.
            intro a; split.
            ** apply Rmult_le_pos; auto.
               apply SeriesC_ge_0'.
               intro; apply Rmult_le_pos; auto.
               apply Hh1pos.
            ** rewrite <- Rmult_1_r.
               apply Rmult_le_compat_l; auto.
               apply (Rle_trans _ (SeriesC (f a))); auto.
               apply SeriesC_le; auto.
               real_solver.
          * setoid_rewrite Ropp_mult_distr_r.
            apply ex_seriesC_scal_r; auto.
        + apply (ex_seriesC_le _ μ1); auto.
          intros a; split.
          * apply Rmult_le_pos; auto.
            apply Rmax_l.
          * rewrite -{2}(Rmult_1_r (μ1 a)).
            apply Rmult_le_compat_l; auto.
            apply Rmax_lub; first by lra.
            apply Rle_minus_l.
            apply (Rle_trans _ 1); last by lra.
            apply (Rle_trans _ (SeriesC (f a))); auto.
            apply SeriesC_le; auto.
            real_solver.
    }

    (*
        Now we instantiate the lifting definitions and use them to prove the
        inequalities
    *)
    rewrite /DPcoupl in Hcoup_R.
    apply Hcoup_R.
    + intro; split; first apply Rmax_l.
      apply Rmax_lub; first by lra.
      apply  (Rle_trans _ (SeriesC (λ a0 : A', f a a0 * h1 a0))); first by lra.
      apply (Rle_trans _ (SeriesC (f a))); auto.
      apply SeriesC_le; auto.
      intro a'.
      specialize (Hh1pos a'); real_solver.
    + intro; split.
      * apply Rmin_glb; [lra |].
        apply Rmult_le_pos.
        ** left. apply exp_pos.
        ** apply SeriesC_ge_0'; intro b'.
           specialize (Hh2pos b'); real_solver.
      * apply Rmin_l.

    + intros a b Rab.
      apply Rmin_glb; apply Rmax_lub; first by lra.
      * apply (Rle_trans _ (SeriesC (λ a0 : A', f a a0 * h1 a0))); first by lra.
        apply (Rle_trans _ (SeriesC (f a))); auto.
        apply SeriesC_le; auto.
        intro a'.
        real_solver.
      * series.
        left.
        by apply exp_pos.
      * apply Rle_minus_l.
        by apply Hcoup_fg.
   Qed.

  Lemma DPcoupl_dbind' (ε1 ε2 ε : R) (δ1 δ2 δ : R)
    (f : A → distr A') (g : B → distr B')
    (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A' → B' → Prop) :
    ε = ε1 + ε2 →
    0 <= δ1 ->
    0 <= δ2 ->
    δ = δ1 + δ2 →
    (∀ a b, R a b → DPcoupl (f a) (g b) S ε2 δ2) →
    DPcoupl μ1 μ2 R ε1 δ1 →
    DPcoupl (dbind f μ1) (dbind g μ2) S ε δ.
  Proof. intros -> ? ? ->. by eapply DPcoupl_dbind. Qed.

  Lemma DPcoupl_mass_leq (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) ε δ :
    DPcoupl μ1 μ2 R ε δ → SeriesC μ1 <= exp ε * SeriesC μ2 + δ.
  Proof.
    intros Hcoupl.
    rewrite /DPcoupl in Hcoupl.
    rewrite -(Rmult_1_r (SeriesC μ1)).
    rewrite -(Rmult_1_r (SeriesC μ2)).
    do 2 rewrite -SeriesC_scal_r.
    apply Hcoupl; intros; lra.
  Qed.

  Lemma DPcoupl_eq_elim (μ1 μ2 : distr A) ε δ :
    DPcoupl μ1 μ2 (=) ε δ → forall a, μ1 a <= exp ε * μ2 a + δ.
  Proof.
    intros Hcoupl a.
    rewrite /DPcoupl in Hcoupl.
    rewrite -(SeriesC_singleton a (μ1 a)).
    rewrite -(SeriesC_singleton a (μ2 a)).
    assert (SeriesC (λ n : A, if bool_decide (n = a) then μ1 a else 0)
            = SeriesC (λ n : A, μ1 n * (if bool_decide (n = a) then 1 else 0))) as ->.
    {
      apply SeriesC_ext; real_solver.
    }
    assert (SeriesC (λ n : A, if bool_decide (n = a) then μ2 a else 0)
            = SeriesC (λ n : A, μ2 n * (if bool_decide (n = a) then 1 else 0))) as ->.
    {
      apply SeriesC_ext; real_solver.
    }
    apply Hcoupl; real_solver.
  Qed.


  Lemma DPcoupl_eq_elim_dp (μ1 μ2 : distr A) ε δ:
    DPcoupl μ1 μ2 (=) ε δ →
    forall (P : A -> Prop),
    SeriesC (λ a : A, if bool_decide (P a) then μ1 a else 0) <=
    exp ε * SeriesC (λ a : A, if bool_decide (P a) then μ2 a else 0) + δ.
  Proof.
    intros Hcoupl P.
    rewrite /DPcoupl in Hcoupl.
    assert (SeriesC (λ a : A, if bool_decide (P a) then μ1 a else 0)
            = SeriesC (λ a : A, μ1 a * (if bool_decide (P a) then 1 else 0))) as ->.
    { apply SeriesC_ext; real_solver. }
    assert (SeriesC (λ a : A, if bool_decide (P a) then μ2 a else 0)
            = SeriesC (λ a : A, μ2 a * (if bool_decide (P a) then 1 else 0))) as ->.
    { apply SeriesC_ext; real_solver. }
    apply Hcoupl; real_solver.
  Qed.

  Lemma DPcoupl_to_Mcoupl (μ1 μ2 : distr A) Q ε :
    DPcoupl μ1 μ2 Q ε 0 -> Mcoupl μ1 μ2 Q ε.
  Proof.
    intros Hcoupl f g Hf Hg HQ.
    rewrite <- Rplus_0_r.
    by apply Hcoupl.
  Qed.

  Lemma Mcoupl_to_DPcoupl (μ1 μ2 : distr A) Q ε :
    Mcoupl μ1 μ2 Q ε -> DPcoupl μ1 μ2 Q ε 0.
  Proof.
    intros Hcoupl f g Hf Hg HQ.
    etransitivity; first by apply Hcoupl.
    real_solver.
  Qed.

  Lemma DPcoupl_to_ARcoupl (μ1 μ2 : distr A) Q δ :
    DPcoupl μ1 μ2 Q 0 δ -> ARcoupl μ1 μ2 Q δ.
  Proof.
    intros Hcoupl f g Hf Hg HQ.
    etransitivity; first by apply Hcoupl.
    rewrite exp_0.
    real_solver.
  Qed.

  Lemma ARcoupl_to_DPcoupl (μ1 μ2 : distr A) Q δ :
    ARcoupl μ1 μ2 Q δ -> DPcoupl μ1 μ2 Q 0 δ.
  Proof.
    intros Hcoupl f g Hf Hg HQ.
    etransitivity; first by apply Hcoupl.
    rewrite exp_0.
    real_solver.
  Qed.

End couplings_theory.

Section DPcoupl.
  Context `{Countable A, Countable B}.
  Variable (μ1 : distr A) (μ2 : distr B).

  Lemma DPcoupl_dzero (μ : distr B) φ ε δ :
    (0 <= δ) ->
    DPcoupl (dzero (A:=A)) μ φ ε δ.
  Proof.
    intros Hleq ?????. rewrite SeriesC_scal_l. field_simplify.
    apply Rle_plus_l; auto.
    apply Rmult_le_pos. 1: left ; apply exp_pos.
    apply SeriesC_ge_0'. intros ; apply Rmult_le_pos => //. apply Hg.
  Qed.

  Lemma DPcoupl_trivial :
    SeriesC μ1 = 1 ->
    SeriesC μ2 = 1 ->
    DPcoupl μ1 μ2 (λ _ _, True) 0 0.
  Proof.
    intros Hμ1 Hμ2 f g Hf Hg Hfg.
    destruct (LubC_correct f) as [H1 H2].
    destruct (GlbC_correct g) as [H3 H4].
    rewrite Rplus_0_r.
    apply (Rle_trans _ (SeriesC (λ a : A, μ1 a * (real (LubC f))))).
    {
      apply SeriesC_le'; auto.
      - intro a.
        apply Rmult_le_compat_l; auto.
        apply rbar_le_finite; auto.
        apply (Rbar_le_sandwich (f a) 1); auto.
        apply H2; auto.
        intro; apply Hf.
      - apply (ex_seriesC_le _ μ1); auto.
        intro a; specialize (Hf a); real_solver.
      - apply ex_seriesC_scal_r; auto.
    }
    rewrite SeriesC_scal_r Hμ1 -Hμ2 -SeriesC_scal_r.
    apply (Rle_trans _ (SeriesC (λ b : B, μ2 b * (real (GlbC g))))).
    {
      (* We step form LubC f to Glb here because it is easier if
         we have an inhabitant of B *)
      apply SeriesC_le'; auto.
      - intro b.
        apply Rmult_le_compat_l; auto.
        apply rbar_le_finite; auto.
        + apply (Rbar_le_sandwich 0 (g b)); auto.
          apply H4; auto.
          apply Hg.
        + apply H4.
          intro b'.
          destruct (LubC f) eqn:Hlub.
          * rewrite <- Hlub; simpl.
            apply finite_rbar_le; auto.
            { apply is_finite_correct; eauto. }
            rewrite Hlub.
            apply H2; intro.
            apply Hfg; auto.
          * apply Hg.
          * apply Hg.
      - apply ex_seriesC_scal_r; auto.
      - apply ex_seriesC_scal_r; auto.
    }
    rewrite exp_0.
    rewrite Rmult_1_l.
    apply SeriesC_le'; auto.
    - intro b.
      apply Rmult_le_compat_l; auto.
      apply finite_rbar_le.
      + apply (Rbar_le_sandwich 0 (g b)); auto.
        apply H4.
        apply Hg.
      + apply H3.
    - apply ex_seriesC_scal_r; auto.
    - apply (ex_seriesC_le _ μ2); auto.
      intro b; specialize (Hg b); real_solver.
  Qed.

  Lemma DPcoupl_pos_R R ε δ :
    DPcoupl μ1 μ2 R ε δ → DPcoupl μ1 μ2 (λ a b, R a b ∧ μ1 a > 0 ∧ μ2 b > 0) ε δ.
  Proof.
    intros Hμ1μ2 f g Hf Hg Hfg.
    assert (SeriesC (λ a : A, μ1 a * f a) =
              SeriesC (λ a : A, μ1 a * (if bool_decide (μ1 a > 0) then f a else 0))) as ->.
    { apply SeriesC_ext; intro a.
      case_bool_decide; auto.
      assert (0 <= μ1 a); auto.
      assert (μ1 a = 0); nra.
    }
    assert (SeriesC (λ b : B, μ2 b * g b) =
              SeriesC (λ b : B, μ2 b * (if bool_decide (μ2 b > 0) then g b else 1))) as ->.
    { apply SeriesC_ext; intro b.
      case_bool_decide; auto.
      assert (0 <= μ2 b); auto.
      assert (μ2 b = 0); nra.
    }
    apply Hμ1μ2; auto.
    - intro a; specialize (Hf a); real_solver.
    - intro b; specialize (Hg b); real_solver.
    - intros a b Rab.
      specialize (Hf a).
      specialize (Hg b).
      specialize (Hfg a b).
      real_solver.
  Qed.

End DPcoupl.

Lemma DPcoupl_eq_trans_l `{Countable A, Countable B} μ1 μ2 μ3 (R: A → B → Prop) ε1 ε2:
  (0 <= ε1) ->
  (0 <= ε2) ->
  DPcoupl μ1 μ2 (=) ε1 0 ->
  DPcoupl μ2 μ3 R ε2 0 ->
  DPcoupl μ1 μ3 R (ε1 + ε2) 0.
Proof.
  intros Hleq1 Hleq2 Heq HR f g Hf Hg Hfg.
  specialize (HR f g Hf Hg Hfg).
  eapply Rle_trans; [apply Heq | ]; auto.
  - intros ? ? ->; lra.
  - do 2 rewrite Rplus_0_r.
    rewrite exp_plus Rmult_assoc.
    apply Rmult_le_compat => //.
    1: etrans. 2: by apply exp_pos_ge_1.
    2: apply SeriesC_ge_0'.
    + real_solver.
    + real_solver.
    + rewrite <- Rplus_0_r.
      apply HR.
Qed.

Lemma DPcoupl_eq_trans_r `{Countable A, Countable B} μ1 μ2 μ3 (R: A → B → Prop) ε1 ε2 :
  (0 <= ε1) ->
  (0 <= ε2) ->
  DPcoupl μ1 μ2 R ε1 0 ->
  DPcoupl μ2 μ3 (=) ε2 0 ->
  DPcoupl μ1 μ3 R (ε1 + ε2) 0.
Proof.
  intros Hleq1 Hleq2 HR Heq f g Hf Hg Hfg.
  specialize (HR f g Hf Hg Hfg).
  eapply Rle_trans ; eauto.
  do 2 rewrite Rplus_0_r.
  rewrite exp_plus Rmult_assoc.
  apply Rmult_le_compat_l.
  1: etrans ; [| apply exp_pos_ge_1]. 1: lra. 1: lra.
  rewrite <- Rplus_0_r.
  apply Heq; eauto.
  intros; simplify_eq; lra.
Qed.

Lemma DPcoupl_pweq `{Countable A} (μ μ' : distr A) ε δ (εpos : 0 <= ε) (δpos : forall a, 0 <= δ a)
                  (δconv : ex_seriesC δ)
                  (pw : ∀ x, DPcoupl μ μ' (λ a a', a = x → a' = x) ε (δ x)) :
  DPcoupl μ μ' eq ε (SeriesC δ).
Proof.
  intros ?????.
  rewrite -SeriesC_scal_l.
  rewrite -SeriesC_plus; auto.
  2:{
    apply ex_seriesC_scal_l.
    apply (ex_seriesC_le _ μ'); auto.
    real_solver.
  }
  eapply SeriesC_le.
  2:{
    apply ex_seriesC_plus; auto.
    apply ex_seriesC_scal_l.
    apply (ex_seriesC_le _ μ') => //.
    intros b ; specialize (Hg b) ; real_solver. }
  intros x.
  split. 1: apply Rmult_le_pos => // ; apply Hf.
  cut (SeriesC (λ a, if bool_decide (a = x) then μ a * f x else 0) <=
         SeriesC (λ a, if bool_decide (a = x) then exp ε * μ' a * g x + δ x else 0)).
  { intros h. rewrite !SeriesC_singleton_dependent in h. rewrite -Rmult_assoc ; done. }
  specialize (pw x).
  replace (SeriesC (λ a : A, if bool_decide (a = x) then exp ε * μ' a * g x + δ x else 0))
    with (exp ε * SeriesC (λ a : A, if bool_decide (a = x) then μ' a * g x else 0) + δ x).
  2: do 2 rewrite SeriesC_singleton_dependent; lra.
  set (f' := λ a, if bool_decide (a = x) then f x else 0).
  set (g' := λ a, if bool_decide (a = x) then g x else 0).
  opose proof (pw f' g' _ _ _) as pw'.
  1,2: intros ; subst f' g' => /= ; case_bool_decide ; (apply Hf || apply Hg || lra).
  {
    intros. subst f' g' => /=. repeat case_bool_decide. 4: done.
    - subst. by apply Hfg.
    - subst. exfalso. eauto.
    - apply Hg.
  }
  etrans.
  1: etrans.
  2: exact pw'. 1,2: right ; subst f' g'.
  2: apply Rplus_eq_compat_r; apply Rmult_eq_compat_l.
  all: apply SeriesC_ext ; intros ; case_bool_decide ; field.
Qed.
