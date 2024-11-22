From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Lim_seq Rbar.
From stdpp Require Export countable.
From clutch.prelude Require Export base Coquelicot_ext Reals_ext stdpp_ext.
From clutch.prob Require Export countable_sum distribution couplings graded_predicate_lifting.

Open Scope R.


Section couplings.
  Context `{Countable A, Countable B, Countable A', Countable B'}.
  Context (μ1 : distr A) (μ2 : distr B) (S : A -> B -> Prop).

  (* The M stands for multiplicative *)
  Definition Mcoupl (ε : R) :=
    forall (f: A → R) (g: B -> R),
      (forall a, 0 <= f a <= 1) ->
      (forall b, 0 <= g b <= 1) ->
      (forall a b, S a b -> f a <= g b) ->
      SeriesC (λ a, μ1 a * f a) <= exp(ε) * SeriesC (λ b, μ2 b * g b).

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


  Lemma Mcoupl_mono (μ1 μ1': distr A') (μ2 μ2': distr B') R R' ε ε':
    (∀ a, μ1 a = μ1' a) ->
    (∀ b, μ2 b = μ2' b) ->
    (∀ x y, R x y -> R' x y) ->
    (ε <= ε') ->
    Mcoupl μ1 μ2 R ε ->
    Mcoupl μ1' μ2' R' ε'.
  Proof.
    intros Hμ1 Hμ2 HR Hε Hcoupl f g Hf Hg Hfg.
    specialize (Hcoupl f g Hf Hg).
    replace (μ1') with μ1; last by apply distr_ext.
    replace (μ2') with μ2; last by apply distr_ext.
    trans (exp(ε) * SeriesC (λ b, μ2 b * g b)).
    - apply Hcoupl.
      naive_solver.
    - apply Rmult_le_compat_r; first by series.
      by apply exp_mono.
  Qed.


  Lemma Mcoupl_mon_grading (μ1 : distr A') (μ2 : distr B') (R : A' → B' → Prop) ε1 ε2 :
    (ε1 <= ε2) ->
    Mcoupl μ1 μ2 R ε1 ->
    Mcoupl μ1 μ2 R ε2.
  Proof.
    intros Hleq.
    by apply Mcoupl_mono.
  Qed.


  Lemma Mcoupl_dret (a : A) (b : B) (R : A → B → Prop) r :
    0 <= r →
    R a b → Mcoupl (dret a) (dret b) R r.
  Proof.
    intros Hr HR f g Hf Hg Hfg.
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
    apply Rmult_le_compat; [real_solver | real_solver | | auto].
    by apply exp_pos_ge_1.
  Qed.


  (* The hypothesis (0 ≤ ε1) is not really needed, I just kept it for symmetry *)
  Lemma Mcoupl_dbind (f : A → distr A') (g : B → distr B')
    (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A' → B' → Prop) ε1 ε2 :
    (Rle 0 ε1) -> (Rle 0 ε2) ->
    (∀ a b, R a b → Mcoupl (f a) (g b) S ε2) → Mcoupl μ1 μ2 R ε1 → Mcoupl (dbind f μ1) (dbind g μ2) S (ε1 + ε2).
  Proof.
    intros Hε1 Hε2 Hcoup_fg Hcoup_R h1 h2 Hh1pos Hh2pos Hh1h2S.
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


    (* To construct X, we want to push ε2 into the inner sum. We don't do this
       directly, because X might be larger than 1, but
       our assumption on the ε1 R-ACoupling requires it to be valued in [0,1].
       Instead, we take min(1, exp(ε2) * (Σ(a:A')(f b a * h1 a))).
       ALT: could use a more fine-grained min inside the sum?
     *)

    assert (exp (ε1) * SeriesC (λ b : B, μ2 b * (Rmin 1 (exp (ε2) * SeriesC (λ a : B', g b a * h2 a))))
            <= exp (ε1 + ε2) * SeriesC (λ b : B, μ2 b * SeriesC (λ a : B', g b a * h2 a))) as <-.
    {
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

    (*
        Now we instantiate the lifting definitions and use them to prove the
        inequalities
    *)
    rewrite /Mcoupl in Hcoup_R.
    apply Hcoup_R.
    + intro; split; series.
      apply (Rle_trans _ (SeriesC (f a))); auto.
      apply SeriesC_le; auto.
      intro a'.
      specialize (Hh1pos_l a'); real_solver.
    + intro; split.
      * apply Rmin_glb; [lra |].
        apply Rmult_le_pos.
        ** left. apply exp_pos.
        ** apply SeriesC_ge_0'; intro b'.
           specialize (Hh2pos b'); real_solver.
      * apply Rmin_l.

    + intros a b Rab.
      apply Rmin_glb.
      * apply (Rle_trans _ (SeriesC (f a))); auto.
        apply SeriesC_le; auto.
        intro a'.
        real_solver.
      * by apply Hcoup_fg.
   Qed.


  Lemma Mcoupl_dbind' (ε1 ε2 ε : R) (f : A → distr A') (g : B → distr B')
    (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A' → B' → Prop) :
    (0 <= ε1) → (0 <= ε2) →
    ε = ε1 + ε2 →
    (∀ a b, R a b → Mcoupl (f a) (g b) S ε2) →
    Mcoupl μ1 μ2 R ε1 →
    Mcoupl (dbind f μ1) (dbind g μ2) S ε.
  Proof. intros ? ? ->. by eapply Mcoupl_dbind. Qed.

End couplings_theory.

