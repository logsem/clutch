From Stdlib Require Import Reals Psatz.
From Stdlib.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Lim_seq Rbar.
From stdpp Require Export countable.
From clutch.prelude Require Export base Coquelicot_ext Reals_ext stdpp_ext.
From clutch.prob Require Export countable_sum distribution couplings graded_predicate_lifting couplings_app couplings_exp.

Open Scope R.


Section Kcouplings.
  Context `{Countable A, Countable B, Countable A', Countable B'}.
  Context (μ1 : distr A) (μ2 : distr B) (S : A -> B -> R).

  Definition Kcoupl (ε : R) (δ : R) :=
    ∀ (f : A → R) (g : B -> R)
      (Hf : ∀ a, 0 <= f a <= 1)
      (Hg : ∀ b, 0 <= g b <= 1)
      (Hfg : ∀ a b, f a <= g b + S a b),
      SeriesC (λ a, μ1 a * f a) <= exp(ε) * SeriesC (λ b, μ2 b * g b) + δ.

End Kcouplings.

Section Kcouplings_theory.
  Context `{Countable A, Countable B, Countable A', Countable B'}.


  Lemma Kcoupl_mono (μ1 μ1': distr A') (μ2 μ2': distr B') R R' ε ε' δ δ':
    (∀ a, μ1 a = μ1' a) ->
    (∀ b, μ2 b = μ2' b) ->
    (∀ x y, R' x y <= R x y) ->
    (ε <= ε') ->
    (δ <= δ') ->
    Kcoupl μ1 μ2 R ε δ ->
    Kcoupl μ1' μ2' R' ε' δ'.
  Proof.
    intros Hμ1 Hμ2 HR Hε Hδ Hcoupl f g Hf Hg Hfg.
    specialize (Hcoupl f g Hf Hg).
    replace (μ1') with μ1; last by apply distr_ext.
    replace (μ2') with μ2; last by apply distr_ext.
    trans (exp(ε) * SeriesC (λ b, μ2 b * g b) + δ).
    - apply Hcoupl.
      intros a b.
      specialize (Hfg a b).
      specialize (HR a b).
      lra.
    - apply Rplus_le_compat; auto.
      apply Rmult_le_compat_r; first by series.
      by apply exp_mono.
  Qed.


  Lemma DPcoupl_1 (μ1 : distr A') (μ2 : distr B') R ε δ:
    (1 <= δ) -> Kcoupl μ1 μ2 R ε δ.
  Proof.
    rewrite /Kcoupl.
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


  Lemma DPcoupl_mon_grading (μ1 : distr A') (μ2 : distr B') (R : A' → B' → R) ε1 ε2 δ1 δ2:
    (ε1 <= ε2) ->
    (δ1 <= δ2) ->
    Kcoupl μ1 μ2 R ε1 δ1 ->
    Kcoupl μ1 μ2 R ε2 δ2.
  Proof.
    intros Hleq.
    by apply Kcoupl_mono.
  Qed.


  Lemma DPcoupl_dret (a : A) (b : B) (R : A → B → R) ε δ :
    0 <= ε ->
    0 <= δ →
    R a b <= δ → Kcoupl (dret a) (dret b) R ε δ.
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
    specialize (Hfg a b).
    etrans; [apply Hfg|].
    apply Rplus_le_compat; auto.
    rewrite -{1}(Rmult_1_l (g b)).
    apply Rmult_le_compat; [real_solver | real_solver | | lra].
    apply exp_pos_ge_1.
    lra.
  Qed.




  Lemma DPcoupl_dbind_adv_lhs (f : A → distr A') (g : B → distr B')
    (μ1 : distr A) (μ2 : distr B) (S : A → B → R) (S' : A' → B' → R)
    ε1 ε2 δ1 δ2 (Δ2 : A → R) :
    (forall a b, 0 <= S a b) -> (0 <= δ1) → (∀ a, 0 <= (Δ2 a) <= 1) →
    (* (SeriesC (λ a, μ1 a * (E2 a)) <= ε2) → *)
    (SeriesC (λ a, μ1 a * (Δ2 a)) = δ2) →
    (∀ a b, Kcoupl (f a) (g b) S' ε2 (Δ2 a + S a b)) →
    Kcoupl μ1 μ2 S ε1 δ1 →
    Kcoupl (dbind f μ1) (dbind g μ2) S' (ε1 + ε2) (δ1 + δ2).
  Proof.
    intros HSpos Hδ1 HΔ2 <- Hcoup_fg Hcoup_S h1 h2 Hh1pos Hh2pos Hh1h2S.
    rewrite {-3}/pmf/=/dbind_pmf.
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
        SeriesC (λ b : A, μ1 b * SeriesC (λ a : A', f b a * h1 a)) -
          SeriesC (λ a, μ1 a * Δ2 a)
        <= SeriesC (λ b : A, μ1 b * Rmax 0 (SeriesC (λ a : A', f b a * h1 a) - Δ2 b))
      ) as ->.
    {
      apply (Rle_trans _ (SeriesC (λ b : A, μ1 b * SeriesC (λ a : A', f b a * h1 a) - μ1 b * Δ2 b))).
      - rewrite SeriesC_minus.
        + apply Rplus_le_compat_l.
          apply Ropp_le_contravar.
          done.
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
        + apply (ex_seriesC_le _ μ1); auto.
          intros; real_solver.
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
          * apply (ex_seriesC_ext (λ x, -1 * (μ1 x * Δ2 x))).
            1: intros; real_solver.
            apply ex_seriesC_scal_l.
            apply (ex_seriesC_le _ μ1); auto.
            intros; real_solver.
        + apply (ex_seriesC_le _ μ1); auto.
          intros a; split.
          * apply Rmult_le_pos; auto.
            apply Rmax_l.
          * rewrite -{2}(Rmult_1_r (μ1 a)).
            apply Rmult_le_compat_l; auto.
            apply Rmax_lub; first by lra.
            apply Rle_minus_l.
            apply (Rle_trans _ 1); last by real_solver.
            apply (Rle_trans _ (SeriesC (f a))); auto.
            apply SeriesC_le; auto.
            real_solver.
    }



    (*
        Now we instantiate the lifting definitions and use them to prove the
        inequalities
    *)
    rewrite /Kcoupl in Hcoup_S.
    apply Hcoup_S.
    + intro; split; first apply Rmax_l.
      apply Rmax_lub; first by lra.
      apply Rle_minus_l.
      apply (Rle_trans _ 1); last by real_solver.
      apply (Rle_trans _ (SeriesC (f a))); auto.
      apply SeriesC_le; auto; real_solver.
    + intro; split.
      * apply Rmin_glb; [lra |].
        apply Rmult_le_pos.
        ** left. apply exp_pos.
        ** apply SeriesC_ge_0'; intro b'.
           specialize (Hh2pos b'); real_solver.
      * apply Rmin_l.

    + intros a b.
      specialize (HSpos a b).
      specialize (HΔ2 a).
      rewrite Rplus_min_distr_r.
      apply Rmin_glb; apply Rmax_lub; first by lra.
      * apply Rle_minus_l.
        apply (Rle_trans _ 1); last by lra.
        apply (Rle_trans _ (SeriesC (f a))); auto.
        apply SeriesC_le; auto; real_solver.
      * apply Rplus_le_le_0_compat; auto.
        series.
        left.
        by apply exp_pos.
      * apply Rle_minus_l.
        rewrite Rplus_assoc (Rplus_comm (S a b)).
        apply Hcoup_fg; auto.
  Qed.


  Lemma Kcoupl_eq_elim (μ1 μ2 : distr A) ε δ :
    Kcoupl μ1 μ2 (λ a a', if bool_decide (a = a') then 0 else 1) ε δ → forall a, μ1 a <= exp(ε) * μ2 a + δ.
  Proof.
    intros Hcoupl a.
    rewrite /Kcoupl in Hcoupl.
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


  Lemma Kcoupl_eq_elim_dp (μ1 μ2 : distr A) ε δ:
    Kcoupl μ1 μ2 (λ a a', if bool_decide (a = a') then 0 else 1) ε δ →
    forall (P : A -> Prop),
    SeriesC (λ a : A, if bool_decide (P a) then μ1 a else 0) <=
    exp(ε) * SeriesC (λ a : A, if bool_decide (P a) then μ2 a else 0) + δ.
  Proof.
    intros Hcoupl P.
    rewrite /Kcoupl in Hcoupl.
    assert (SeriesC (λ a : A, if bool_decide (P a) then μ1 a else 0)
            = SeriesC (λ a : A, μ1 a * (if bool_decide (P a) then 1 else 0))) as ->.
    { apply SeriesC_ext; real_solver. }
    assert (SeriesC (λ a : A, if bool_decide (P a) then μ2 a else 0)
            = SeriesC (λ a : A, μ2 a * (if bool_decide (P a) then 1 else 0))) as ->.
    { apply SeriesC_ext; real_solver. }
    apply Hcoupl; real_solver.
  Qed.

 End Kcouplings_theory.
