From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Lim_seq Rbar.
From stdpp Require Export countable.
From clutch.prelude Require Export base Coquelicot_ext Reals_ext stdpp_ext.
From clutch.prob Require Export countable_sum distribution couplings graded_predicate_lifting.

Open Scope R.

(* TODO: cleanup this file *)

Section couplings.
  Context `{Countable A, Countable B, Countable A', Countable B'}.
  Context (μ1 : distr A) (μ2 : distr B) (S : A -> B -> Prop).

  Definition ARcoupl (ε : R) :=
    forall (f: A → R) (g: B -> R),
      (forall a, 0 <= f a <= 1) ->
      (forall b, 0 <= g b <= 1) ->
      (forall a b, S a b -> f a <= g b) ->
      SeriesC (λ a, μ1 a * f a) <= SeriesC (λ b, μ2 b * g b) + ε.

End couplings.

Section couplings_theory.
  Context `{Countable A, Countable B, Countable A', Countable B'}.

  Lemma ARcoupl_mono (μ1 μ1': distr A') (μ2 μ2': distr B') R R' ε ε':
    (∀ a, μ1 a = μ1' a) ->
    (∀ b, μ2 b = μ2' b) ->
    (∀ x y, R x y -> R' x y) ->
    (ε <= ε') ->
    ARcoupl μ1 μ2 R ε ->
    ARcoupl μ1' μ2' R' ε'.
  Proof.
    intros Hμ1 Hμ2 HR Hε Hcoupl f g Hf Hg Hfg.
    specialize (Hcoupl f g Hf Hg).
    replace (μ1') with μ1; last by apply distr_ext.
    replace (μ2') with μ2; last by apply distr_ext.
    trans (SeriesC (λ b, μ2 b * g b) + ε); last lra.
    apply Hcoupl.
    naive_solver.
  Qed.

  Lemma ARcoupl_1 (μ1 : distr A') (μ2 : distr B') R ε:
    (1 <= ε) -> ARcoupl μ1 μ2 R ε.
  Proof.
    rewrite /ARcoupl.
    intros Hε f g Hf Hg Hfg.
    trans 1.
    - trans (SeriesC μ1); last auto.
      apply SeriesC_le; last auto.
      real_solver.
    - replace 1 with (0+1); last lra.
      apply Rplus_le_compat; last lra.
      apply SeriesC_ge_0'; real_solver.
  Qed.

  Lemma ARcoupl_mon_grading (μ1 : distr A') (μ2 : distr B') (R : A' → B' → Prop) ε1 ε2 :
    (ε1 <= ε2) ->
    ARcoupl μ1 μ2 R ε1 ->
    ARcoupl μ1 μ2 R ε2.
  Proof.
    intros Hleq HR f g Hf Hg Hfg.
    specialize (HR f g Hf Hg Hfg).
    lra.
  Qed.

  Lemma ARcoupl_dret (a : A) (b : B) (R : A → B → Prop) r :
    0 <= r →
    R a b → ARcoupl (dret a) (dret b) R r.
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
    specialize (Hfg _ _ HR). lra. 
  Qed.


  (* The hypothesis (0 ≤ ε1) is not really needed, I just kept it for symmetry *)
  Lemma ARcoupl_dbind (f : A → distr A') (g : B → distr B')
    (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A' → B' → Prop) ε1 ε2 :
    (Rle 0 ε1) -> (Rle 0 ε2) ->
    (∀ a b, R a b → ARcoupl (f a) (g b) S ε2) → ARcoupl μ1 μ2 R ε1 → ARcoupl (dbind f μ1) (dbind g μ2) S (ε1 + ε2).
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
    rewrite -Rplus_assoc.

    (* Third step: isolate ε1 on the RHS.
       ALT: could move ε2 into Y instead of into X. *)
    apply Rle_minus_l.

    (* To construct X, we want to push ε2 into the inner sum. We don't do this
       directly, because if `ε2 > (f b a * h1 a)` then X might be negative, but
       our assumption on the ε1 R-ACoupling requires it to be valued in [0,1].
       Instead, we take max(0, (Σ(a:A')(f b a * h1 a)) - ε2).
       ALT: could use a more fine-grained max inside the sum?
     *)
    assert (SeriesC (λ b : A, μ1 b * SeriesC (λ a : A', f b a * h1 a)) - ε2
            <= SeriesC (λ b : A, μ1 b * (Rmax (SeriesC (λ a : A', f b a * h1 a) - ε2) 0))) as Hleq.
    {
      (* This could be an external lemma *)
      trans (SeriesC (λ b : A, μ1 b * SeriesC (λ a : A', f b a * h1 a)) - SeriesC (λ b, μ1 b * ε2)).
      - apply Rplus_le_compat; [lra | ].
        apply Ropp_le_contravar.
        rewrite SeriesC_scal_r.
        rewrite <- Rmult_1_l.
        apply Rmult_le_compat; auto; try lra.
      - rewrite -SeriesC_minus.
        * apply SeriesC_le'.
          ++ intro a.
             rewrite -Rmult_minus_distr_l.
             apply Rmult_le_compat_l; auto.
             apply Rmax_l.
          ++ apply ex_seriesC_plus.
             ** apply (ex_seriesC_le _ (λ x : A, μ1 x * SeriesC (λ a : A', f x a * h1 a))).
                --- intros a; split; [ | lra].
                    apply Rmult_le_pos; auto.
                    apply SeriesC_ge_0'.
                    intro; apply Rmult_le_pos; auto.
                    apply Hh1pos.
                --- apply (ex_seriesC_le _ μ1); auto.
                    intro a; split.
                    +++ apply Rmult_le_pos; auto.
                        apply SeriesC_ge_0'.
                        intro; apply Rmult_le_pos; auto.
                        apply Hh1pos.
                    +++ rewrite <- Rmult_1_r.
                        apply Rmult_le_compat_l; auto.
                        apply (Rle_trans _ (SeriesC (f a))); auto.
                        apply SeriesC_le; auto.
                        intro a'; specialize (Hh1pos a').
                        split; real_solver.
             ** apply (ex_seriesC_ext (λ x : A, (-1) * (μ1 x * ε2))); [intro; nra | ].
                apply ex_seriesC_scal_l.
                apply ex_seriesC_scal_r; auto.
          ++ eapply (ex_seriesC_le _ (λ b : A, μ1 b * (SeriesC (λ a : A', f b a * h1 a)))).
             --- intro a; split.
                 +++ apply Rmult_le_pos; auto.
                     apply Rmax_r.
                 +++ apply Rmult_le_compat_l; auto.
                     apply Rmax_lub.
                     *** apply Rle_minus_l.
                         rewrite <- Rplus_0_r at 1.
                         apply Rplus_le_compat_l; auto.
                     *** apply SeriesC_ge_0'.
                         intro a'.
                         apply Rmult_le_pos; auto.
                         apply Hh1pos.
             --- apply (ex_seriesC_le _ μ1); auto.
                 intro; split.
                 +++ apply Rmult_le_pos; auto.
                     apply SeriesC_ge_0'; intro.
                     apply Rmult_le_pos; auto.
                     apply Hh1pos.
                 +++ rewrite <- Rmult_1_r.
                     apply Rmult_le_compat_l; auto.
                     apply (Rle_trans _ (SeriesC (f n))); auto.
                     apply SeriesC_le; auto.
                     intro a'; specialize (Hh1pos a'); real_solver.
        * apply (ex_seriesC_le _ μ1); auto.
          intro; split.
          ++ apply Rmult_le_pos; auto.
             apply SeriesC_ge_0'; intro.
             apply Rmult_le_pos; auto.
             apply Hh1pos.
          ++ rewrite <- Rmult_1_r.
             apply Rmult_le_compat_l; auto.
             apply (Rle_trans _ (SeriesC (f n))); auto.
             apply SeriesC_le; auto.
             intro a'; specialize (Hh1pos a'); real_solver.
        * apply ex_seriesC_scal_r; auto.
    }
    eapply Rle_trans; [apply Hleq | ].

    rewrite /ARcoupl in Hcoup_R.
    apply Hcoup_R.
    + intro; split.
      * apply Rmax_r; auto.
      * apply Rmax_lub; [ | lra].
        apply Rle_minus_l.
        rewrite <- Rplus_0_r at 1.
        apply Rplus_le_compat; auto.
        apply (Rle_trans _ (SeriesC (f a))); auto.
        apply SeriesC_le; auto.
        intro a'.
        specialize (Hh1pos a'); real_solver.
    + intro; split.
      * apply SeriesC_ge_0'; intro b'.
        specialize (Hh2pos b'); real_solver.
      * apply (Rle_trans _ (SeriesC (g b))); auto.
        apply SeriesC_le; auto.
        intro b'.
        specialize (Hh2pos b'); real_solver.

    + intros a b Rab.
      apply Rmax_lub.
      2:{ apply SeriesC_ge_0'; intro b'.
          specialize (Hh2pos b'); real_solver. }
      rewrite /ARcoupl in Hcoup_fg.
      apply Rle_minus_l, Hcoup_fg; auto.
  Qed.
  
  Lemma ARcoupl_dbind' (ε1 ε2 ε : R) (f : A → distr A') (g : B → distr B')
    (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A' → B' → Prop) :
    (0 <= ε1) → (0 <= ε2) →
    ε = ε1 + ε2 →
    (∀ a b, R a b → ARcoupl (f a) (g b) S ε2) →
    ARcoupl μ1 μ2 R ε1 →
    ARcoupl (dbind f μ1) (dbind g μ2) S ε.
  Proof. intros ? ? ->. by eapply ARcoupl_dbind. Qed. 

  Local Notation ℝ := R.
  (* Depend on LHS *)
  Lemma ARcoupl_dbind_adv_lhs (f : A → distr A') (g : B → distr B')
    (μ1 : distr A) (μ2 : distr B) (S : A → B → Prop) (S' : A' → B' → Prop)
    ε1 ε2 (E2 : A → ℝ) :
    (Rle 0 ε1) → (∀ a, 0 <= (E2 a) <= 1) →
    (* (SeriesC (λ a, μ1 a * (E2 a)) <= ε2) → *)
    (SeriesC (λ a, μ1 a * (E2 a)) = ε2) →
    (∀ a b, S a b → ARcoupl (f a) (g b) S' (E2 a)) → ARcoupl μ1 μ2 S ε1 → ARcoupl (dbind f μ1) (dbind g μ2) S' (ε1 + ε2).
  Proof.
    intros Hε1 HE2 Hε2 Hcoup_fg Hcoup_R h1 h2 Hh1pos Hh2pos Hh1h2S.

    rewrite /pmf/=/dbind_pmf.

    (* To use the hypothesis that we have an R-ACoupling up to ε1 for μ1, μ2,
       we have to rewrite the sums in such a way as to isolate (the expectation
       of) a random variable X on the LHS and Y on the RHS, and ε1 on the
       RHS. *)
    (* First step: rewrite the LHS into a RV X on μ1. *)
    setoid_rewrite <- SeriesC_scal_r.
    rewrite -(fubini_pos_seriesC (λ '(a,x), μ1 x * f x a * h1 a)).

    (* Boring Fubini side-conditions. *)
    2: real_solver.
    2: { intro a'.
         apply (ex_seriesC_le _ μ1) => //.
         intro a; split.
         - real_solver.
         - do 2 rewrite <- Rmult_1_r. real_solver. }
    2: { setoid_rewrite SeriesC_scal_r.
         apply (ex_seriesC_le _ (λ a : A', SeriesC (λ x : A, μ1 x * f x a))).
         - series.
         - apply (pmf_ex_seriesC (dbind f μ1)). }

    (* LHS: Pull the (μ1 b) factor out of the inner sum. *)
    assert (SeriesC (λ a : A, SeriesC (λ a' : A', μ1 a * f a a' * h1 a')) =
              SeriesC (λ a : A, μ1 a * SeriesC (λ a' : A', f a a' * h1 a')))
      as -> by (setoid_rewrite <- SeriesC_scal_l ; series).

    (* Second step: rewrite the RHS into a RV Y on μ2. *)
    rewrite <-(fubini_pos_seriesC (λ '(b,x), μ2 x * g x b * h2 b)).
    2: real_solver.
    2:{ intro b'.
        apply (ex_seriesC_le _ μ2) => //.
        intro b; split.
        - real_solver.
        - do 2 rewrite <- Rmult_1_r. real_solver. }
    2: { setoid_rewrite SeriesC_scal_r.
         apply (ex_seriesC_le _ (λ a : B', SeriesC (λ b : B, μ2 b * g b a))).
         - series.
         - apply (pmf_ex_seriesC (dbind g μ2)). }

    (* RHS: Factor out (μ2 b) *)
    assert (SeriesC (λ b, SeriesC (λ b' : B', μ2 b * g b b' * h2 b'))
            = SeriesC (λ b, μ2 b * SeriesC (λ b' : B', g b b' * h2 b')))
      as -> by (setoid_rewrite <- SeriesC_scal_l ; series).

    rewrite -Rplus_assoc.

    set (Y b := SeriesC (λ b', g b b' * h2 b')).
    replace (λ b, μ2 b * _) with (λ b, μ2 b * Y b) by auto.

    (* Third step: isolate ε1 on the RHS by moving ε2 into X. *)
    apply Rle_minus_l.

    (* To construct X, we want to push ε2 into the inner sum. We don't do this
       directly, because if `ε2 > (f b a * h1 a)` then X might be negative, but
       our assumption on the ε1 R-ACoupling requires it to be valued in [0,1].
       Instead, we take max(0, (Σ(a:A')(f b a * h1 a)) - ε2).
       ALT: could use a more fine-grained max inside the sum?
     *)
    rewrite -Hε2.
    set (fh1 a := SeriesC (λ a' : A', f a a' * h1 a')).
    replace (λ b, μ1 b * _) with (λ a, μ1 a * fh1 a) by auto.
    rewrite -SeriesC_minus.
    2:{
      apply pmf_ex_seriesC_mult_fn. eexists _.
      intros a. split.
      - rewrite /fh1 ; series.
      - trans (SeriesC (f a)) => //.
        apply SeriesC_le => //. real_solver.
    }
    2:{ apply pmf_ex_seriesC_mult_fn. eexists _ ; real_solver. }

    setoid_rewrite <-Rmult_minus_distr_l.

    trans (SeriesC (λ a, μ1 a * Rmax (fh1 a - E2 a) 0)) ; last first.
    {
      set (X a := Rmax (fh1 a - E2 a) 0).
      replace (λ a, μ1 a * _) with (λ a, μ1 a * X a) by auto.

      rewrite /ARcoupl in Hcoup_R.
      apply Hcoup_R.
      + intro a ; split.
        * apply Rmax_r.
        * rewrite /X. apply Rmax_lub; [ | lra].
          apply Rle_minus_l.
          trans (SeriesC (f a)).
          1: apply SeriesC_le ; real_solver.
          trans 1 => //.
          real_solver.
      + intro b ; split.
        * rewrite /Y ; series.
        * trans (SeriesC (g b)) => //.
          apply SeriesC_le ; real_solver.
      + intros a b Sab.

        rewrite /X.
        apply Rmax_lub.
        2: rewrite /Y ; series.
        rewrite /ARcoupl in Hcoup_fg.
        apply Rle_minus_l.
        by apply Hcoup_fg.
    }

    apply SeriesC_le'.
    3:{
      apply pmf_ex_seriesC_mult_fn.
      eexists 1. intros a. split.
      - apply Rmax_r.
      - apply Rmax_lub ; [| lra ].
        trans (SeriesC (f a) - E2 a).
        + rewrite -Rle_minus_l Rplus_minus_r. apply SeriesC_le => //. real_solver.
        + trans (SeriesC (f a)) => //. real_solver.
    }

    2:{
      apply ex_seriesC_Rabs.
      setoid_rewrite Rabs_mult.
      setoid_rewrite Rabs_right at 1.
      2: real_solver.
      apply pmf_ex_seriesC_mult_fn.
      eexists 1. intros a.
      destruct (HE2 a).
      split. 1: apply Rabs_pos.
      apply Rabs_le_between'.
      rewrite /fh1. split.
      - trans 0 ; series.
      - trans 1. 2: lra.
        trans (SeriesC (λ a' : A', f a a')) => //.
        apply SeriesC_le => //. real_solver.
    }

    intros. repeat real_solver_partial.
    by apply Rmax_l.
  Qed.

  Lemma ARcoupl_dbind_adv_lhs' (E2 : A → ℝ) (f : A → distr A') (g : B → distr B')
    (μ1 : distr A) (μ2 : distr B) (S : A → B → Prop) (S' : A' → B' → Prop)
    ε1 ε2 :
    (Rle 0 ε1) → (∃ n, ∀ a, 0 <= (E2 a) <= n) →
    (SeriesC (λ a, μ1 a * (E2 a)) <= ε2) →
    (∀ a b, S a b → ARcoupl (f a) (g b) S' (E2 a)) → ARcoupl μ1 μ2 S ε1 → ARcoupl (dbind f μ1) (dbind g μ2) S' (ε1 + ε2).
  Proof.
    intros Hε1 HE2 Hsum Hfg Hcoupl.
    pose (E2' x:= Rmin 1 (E2 x)).
    eapply (ARcoupl_mon_grading _ _ _ (ε1 + SeriesC (λ a, μ1 a * (E2' a)))).
    { apply Rplus_le_compat_l; etrans; last exact. apply SeriesC_le; last apply pmf_ex_seriesC_mult_fn.
      - intros. rewrite /E2'. split.
        + apply Rmult_le_pos; try done. apply Rmin_glb; [lra|naive_solver].
        + apply Rmult_le_compat_l; first done. apply Rmin_r.
      - naive_solver.
    }
    eapply (ARcoupl_dbind_adv_lhs _ _ _ _ _ _ _ _ E2'); try done. 
    - intros a; split.
      + apply Rmin_glb; [lra|naive_solver].
      + apply Rmin_l.
    - intros a b Hs. specialize (Hfg a b Hs).
      rewrite /E2'. 
      rewrite /Rmin.
      case_match.
      + apply ARcoupl_1; done.
      + eapply ARcoupl_mon_grading; done.
  Qed.
  

  (* Depend on RHS *)

  Lemma ARcoupl_dbind_adv_rhs (f : A → distr A') (g : B → distr B')
    (μ1 : distr A) (μ2 : distr B) (S : A → B → Prop) (S' : A' → B' → Prop)
    ε1 ε2 (E2 : B → ℝ) :
    (Rle 0 ε1) → (∀ b, 0 <= (E2 b) <= 1) →
    (SeriesC (λ b, μ2 b * (E2 b)) = ε2) →
    (∀ a b, S a b → ARcoupl (f a) (g b) S' (E2 b)) → ARcoupl μ1 μ2 S ε1 → ARcoupl (dbind f μ1) (dbind g μ2) S' (ε1 + ε2).
  Proof.
    intros Hε1 HE2 Hε2 Hcoup_fg Hcoup_R h1 h2 Hh1pos Hh2pos Hh1h2S.
    rewrite /pmf/=/dbind_pmf.

    (* Used later. *)
    assert (0 <= ε2).
    { rewrite -Hε2. apply SeriesC_ge_0'. intros.
      repeat apply Rmult_le_pos ; try apply pmf_pos ; apply HE2. }

    (* To use the hypothesis that we have an R-ACoupling up to ε1 for μ1, μ2,
       we have to rewrite the sums in such a way as to isolate (the expectation
       of) a random variable X on the LHS and Y on the RHS, and ε1 on the
       RHS. *)
    (* First step: rewrite the LHS into a RV X on μ1. *)
    setoid_rewrite <- SeriesC_scal_r.
    rewrite <-(fubini_pos_seriesC (λ '(a,x), μ1 x * f x a * h1 a)).

    (* Boring Fubini sideconditions. *)
    2: { intros a' a. specialize (Hh1pos a') ; real_solver. }
    2: { intro a'.
         specialize (Hh1pos a').
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
         + intros a'; specialize (Hh1pos a'); split.
           * apply Rmult_le_pos; [ | lra].
             apply (pmf_pos ((dbind f μ1)) a').
           * rewrite <- Rmult_1_r.
             apply Rmult_le_compat_l; auto.
             -- apply SeriesC_ge_0'. real_solver.
             -- real_solver.
         + apply (pmf_ex_seriesC (dbind f μ1)). }

    (* LHS: Pull the (μ1 b) factor out of the inner sum. *)
    assert (SeriesC (λ b : A, SeriesC (λ a : A', μ1 b * f b a * h1 a)) =
              SeriesC (λ b : A, μ1 b * SeriesC (λ a : A', f b a * h1 a))) as ->.
    { apply SeriesC_ext; intro.
      rewrite <- SeriesC_scal_l.
      apply SeriesC_ext; real_solver. }

    (* Second step: rewrite the RHS into a RV Y on μ2. *)
    rewrite <-(fubini_pos_seriesC (λ '(b,x), μ2 x * g x b * h2 b)).
    2:{ intros b' b.
        specialize (Hh2pos b').
        real_solver. }
    2:{ intro b'.
        specialize (Hh2pos b').
        apply (ex_seriesC_le _ μ2); auto.
        intro b; split.
        - apply Rmult_le_pos.
          + real_solver.
          + real_solver.
        - rewrite <- Rmult_1_r.
          rewrite Rmult_assoc.
          apply Rmult_le_compat_l; auto.
          rewrite <- Rmult_1_r.
          apply Rmult_le_compat; real_solver. }
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
    rewrite (Rplus_comm ε1) -Rplus_assoc.

    set (X a := SeriesC (λ a' : A', f a a' * h1 a')).
    replace (λ b, μ1 b * _) with (λ a, μ1 a * X a) by auto.

    rewrite -Hε2.

    set (gh2 b := SeriesC (λ b' : B', g b b' * h2 b')).
    replace (λ b, μ2 b * _) with (λ b, μ2 b * gh2 b) by auto.

    rewrite -SeriesC_plus.

    2:{
      apply pmf_ex_seriesC_mult_fn.
      eexists 1.
      intros b.
      split.
      - apply SeriesC_ge_0'.
        intros. apply Rmult_le_pos ; auto. naive_solver.
      - trans (SeriesC (g b)) => //.
        apply SeriesC_le => //. intros b'.
        destruct (Hh2pos b'). real_solver.
    }
    2:{
      apply pmf_ex_seriesC_mult_fn.
      eexists 1.
      intros b.
      destruct (HE2 b) ; lra.
    }

    set (Y b := Rmin (gh2 b + E2 b) 1).
    setoid_rewrite <-Rmult_plus_distr_l.

    assert (forall b, 0 <= gh2 b + E2 b).
    { intros b. apply Rplus_le_le_0_compat. 2: apply HE2.
      apply SeriesC_ge_0'. intros b'.
      apply Rmult_le_pos => //.
      apply Hh2pos.
    }

    trans (SeriesC (λ b, μ2 b * Y b) + ε1).
    {
      (* This is the core of the argument. *)
      rewrite /ARcoupl in Hcoup_R.
      apply Hcoup_R.

      + intro; split.
        * apply SeriesC_ge_0'; intro a'.
          specialize (Hh1pos a'); real_solver.
        * apply (Rle_trans _ (SeriesC (f a))); auto.
          apply SeriesC_le; auto.
          intro a'.
          specialize (Hh1pos a'); real_solver.

      + intro; split.
        * rewrite /Y /gh2.
          apply Rmin_glb ; [|lra].
          apply Rle_plus_r. 1: apply HE2.
          apply SeriesC_ge_0'. intros b'.
          apply Rmult_le_pos => //.
          apply Hh2pos.
        * rewrite /Y/gh2. apply Rmin_r.

      + intros a b Sab.


        rewrite /Y.
        apply Rmin_glb.
        2:{ rewrite /X.
            trans (SeriesC (λ a' : A', f a a' * 1)).
            - apply SeriesC_le.
              + intros a'. destruct (Hh1pos a'). real_solver.
              + apply pmf_ex_seriesC_mult_fn. exists 1. intros ; lra.
            - setoid_rewrite Rmult_1_r. auto.
        }
        rewrite /ARcoupl in Hcoup_fg.
        by apply Hcoup_fg.
    }
    apply Rle_plus_proper => //.
    apply SeriesC_le'.
    1: { intros b. apply Rmult_le_compat_l => //. rewrite /Y.
         apply Rmin_l. }
    - rewrite /Y.
      apply pmf_ex_seriesC_mult_fn.
      eexists 1.
      intros b.
      split.
      + apply Rmin_glb. 2: lra. auto.
      + apply Rmin_r.
    - apply pmf_ex_seriesC_mult_fn.
      exists (1 + 1). intros b. split => //.
      apply Rle_plus_proper => //.
      + rewrite /gh2. trans (SeriesC (λ b' : B', g b b')) => //.
        apply SeriesC_le => //.
        intros b' => //. destruct (Hh2pos b'). real_solver.
      + apply HE2.
  Qed.

  Lemma ARcoupl_dbind_adv_rhs' (E2 : B → ℝ) (f : A → distr A') (g : B → distr B')
    (μ1 : distr A) (μ2 : distr B) (S : A → B → Prop) (S' : A' → B' → Prop)
    ε1 ε2 :
    (Rle 0 ε1) → (∃ n, ∀ b, 0 <= (E2 b) <= n) →
    (SeriesC (λ b, μ2 b * (E2 b)) <= ε2) →
    (∀ a b, S a b → ARcoupl (f a) (g b) S' (E2 b)) → ARcoupl μ1 μ2 S ε1 → ARcoupl (dbind f μ1) (dbind g μ2) S' (ε1 + ε2).
  Proof.
    intros Hε1 HE2 Hsum Hfg Hcoupl.
    pose (E2' x:= Rmin 1 (E2 x)).
    eapply (ARcoupl_mon_grading _ _ _ (ε1 + SeriesC (λ a, μ2 a * (E2' a)))).
    { apply Rplus_le_compat_l; etrans; last exact. apply SeriesC_le; last apply pmf_ex_seriesC_mult_fn.
      - intros. rewrite /E2'. split.
        + apply Rmult_le_pos; try done. apply Rmin_glb; [lra|naive_solver].
        + apply Rmult_le_compat_l; first done. apply Rmin_r.
      - naive_solver.
    }
    eapply (ARcoupl_dbind_adv_rhs _ _ _ _ _ _ _ _ E2'); try done. 
    - intros a; split.
      + apply Rmin_glb; [lra|naive_solver].
      + apply Rmin_l.
    - intros a b Hs. specialize (Hfg a b Hs).
      rewrite /E2'. 
      rewrite /Rmin.
      case_match.
      + apply ARcoupl_1; done.
      + eapply ARcoupl_mon_grading; done.
  Qed.

  (* Depend on both *)
  (** This statement atm is not sound.
      Counter example: 
      Suppose μ1 and μ2 are rand 1s, and S is (=), ε1 is 1/2
      With this statement, we can assign E2 to be λ a b, if a = b then 1 else 0
      Meaning, that for the branches where the two rands return the same value,
      we somehow bumped up the errors from 1/2 to 1, which should not be possible 
      in the normal case
   *)
  Lemma ARcoupl_dbind_adv (f : A → distr A') (g : B → distr B')
    (μ1 : distr A) (μ2 : distr B) (S : A → B → Prop) (S' : A' → B' → Prop)
    ε1 ε2 (E2 : A → B → ℝ) :
    (Rle 0 ε1) → (∀ a b, Rle 0 (E2 a b)) →
    (SeriesC (λ '(a, b), μ1 a * μ2 b * (E2 a b)) <= ε2) →
    (∀ a b, S a b → ARcoupl (f a) (g b) S' (E2 a b)) → ARcoupl μ1 μ2 S ε1 → ARcoupl (dbind f μ1) (dbind g μ2) S' (ε1 + ε2).
  Proof.
  Abort.


  Lemma ARcoupl_mass_leq (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) ε :
    ARcoupl μ1 μ2 R ε → SeriesC μ1 <= SeriesC μ2 + ε.
  Proof.
    intros Hcoupl.
    rewrite /ARcoupl in Hcoupl.
    rewrite -(Rmult_1_r (SeriesC μ1)).
    rewrite -(Rmult_1_r (SeriesC μ2)).
    do 2 rewrite -SeriesC_scal_r.
    apply Hcoupl; intros; lra.
  Qed.


  Lemma ARcoupl_eq (μ1 : distr A) :
    ARcoupl μ1 μ1 (=) 0.
  Proof.
    intros f g Hf Hg Hfg.
    rewrite Rplus_0_r.
    apply SeriesC_le.
    - intro a; specialize (Hf a); specialize (Hg a); real_solver.
    - apply (ex_seriesC_le _ μ1); auto.
      intro a; specialize (Hg a); real_solver.
  Qed.


  Lemma ARcoupl_eq_elim (μ1 μ2 : distr A) ε :
    ARcoupl μ1 μ2 (=) ε → forall a, μ1 a <= μ2 a + ε.
  Proof.
    intros Hcoupl a.
    rewrite /ARcoupl in Hcoupl.
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

  Lemma ARcoupl_eq_elim_tv (μ1 μ2 : distr A) ε :
    ARcoupl μ1 μ2 (=) ε →
    forall (P : A -> Prop),
    SeriesC (λ a : A, if bool_decide (P a) then μ1 a else 0)  <=
    SeriesC (λ a : A, if bool_decide (P a) then μ2 a else 0) + ε.
  Proof.
    intros Hcoupl P.
    rewrite /ARcoupl in Hcoupl.
    assert (SeriesC (λ a : A, if bool_decide (P a) then μ1 a else 0)
            = SeriesC (λ a : A, μ1 a * (if bool_decide (P a) then 1 else 0))) as ->.
    { apply SeriesC_ext; real_solver. }
    assert (SeriesC (λ a : A, if bool_decide (P a) then μ2 a else 0)
            = SeriesC (λ a : A, μ2 a * (if bool_decide (P a) then 1 else 0))) as ->.
    { apply SeriesC_ext; real_solver. }
    apply Hcoupl; real_solver.
  Qed.
  
End couplings_theory.

(* TODO: cleanup *)
Section ARcoupl.
  Context `{Countable A, Countable B}.
  Variable (μ1 : distr A) (μ2 : distr B).

  Lemma ARcoupl_trivial :
    SeriesC μ1 = 1 ->
    SeriesC μ2 = 1 ->
    ARcoupl μ1 μ2 (λ _ _, True) 0.
  Proof.
    intros Hμ1 Hμ2 f g Hf Hg Hfg.
    destruct (LubC_correct f) as [H1 H2].
    destruct (GlbC_correct g) as [H3 H4].
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
    rewrite Rplus_0_r.
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


  Lemma ARcoupl_pos_R R ε :
    ARcoupl μ1 μ2 R ε → ARcoupl μ1 μ2 (λ a b, R a b ∧ μ1 a > 0 ∧ μ2 b > 0) ε.
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

End ARcoupl.

Lemma ARcoupl_dzero_dzero `{Countable A, Countable B} (R : A → B → Prop) :
  ARcoupl dzero dzero R 0.
Proof.
  intros f g Hf Hg HR.
  rewrite /pmf/=.
  do 2 rewrite SeriesC_scal_l; lra.
Qed.

Lemma ARcoupl_dzero_r_inv `{Countable A, Countable B} μ1 (R : A → B → Prop) :
  ARcoupl μ1 dzero R 0 → μ1 = dzero.
Proof.
  intros Hz%ARcoupl_mass_leq.
  apply SeriesC_zero_dzero.
  rewrite dzero_mass in Hz.
  assert (0 <= SeriesC μ1); auto.
  lra.
Qed.

Lemma ARcoupl_dzero `{Countable A, Countable B} (μ : distr B) (R: A → B → Prop) ε :
  (0 <= ε) ->
  ARcoupl dzero μ R ε.
Proof.
  intros Hleq f g Hf Hg HR.
  rewrite {1}/pmf SeriesC_scal_l Rmult_0_l.
  rewrite <- Rplus_0_l at 1.
  apply Rplus_le_compat; auto.
  apply SeriesC_ge_0'.
  intro; apply Rmult_le_pos; auto.
  apply Hg.
Qed.

(*
Lemma Rcoupl_dzero_l_inv `{Countable A, Countable B} μ2 (R : A → B → Prop) :
  Rcoupl dzero μ2 R → μ2 = dzero.
Proof.
  intros Hz%Rcoupl_mass_eq.
  apply SeriesC_zero_dzero.
  rewrite -Hz SeriesC_0 //.
Qed.
 *)

Lemma ARcoupl_map `{Countable A, Countable B, Countable A', Countable B'}
  (f : A → A') (g : B → B') (μ1 : distr A) (μ2 : distr B) (R : A' → B' → Prop) ε :
  (0 <= ε) ->
  ARcoupl μ1 μ2 (λ a a', R (f a) (g a')) ε → ARcoupl (dmap f μ1) (dmap g μ2) R ε.
Proof.
  intros Hleq Hcoupl. rewrite /dmap.
  rewrite -(Rplus_0_r ε).
  eapply (ARcoupl_dbind _ _ _ _ (λ (a : A) (a' : B), R (f a) (g a')) _ ε 0); auto; [lra |].
  intros a b Hab.
  by eapply ARcoupl_dret. 
Qed.

Lemma ARcoupl_eq_trans_l `{Countable A, Countable B} μ1 μ2 μ3 (R: A → B → Prop) ε1 ε2 :
  (0 <= ε1) ->
  (0 <= ε2) ->
  ARcoupl μ1 μ2 (=) ε1 ->
  ARcoupl μ2 μ3 R ε2 ->
  ARcoupl μ1 μ3 R (ε1 + ε2).
Proof.
  intros Hleq1 Hleq2 Heq HR f g Hf Hg Hfg.
  specialize (HR f g Hf Hg Hfg).
  eapply Rle_trans; [apply Heq | ]; auto.
  - intros ? ? ->; lra.
  - rewrite (Rplus_comm ε1) -Rplus_assoc.
    apply Rplus_le_compat_r; auto.
Qed.

Lemma ARcoupl_eq_trans_r `{Countable A, Countable B} μ1 μ2 μ3 (R: A → B → Prop) ε1 ε2 :
  (0 <= ε1) ->
  (0 <= ε2) ->
  ARcoupl μ1 μ2 R ε1 ->
  ARcoupl μ2 μ3 (=) ε2 ->
  ARcoupl μ1 μ3 R (ε1 + ε2).
Proof.
  intros Hleq1 Hleq2 HR Heq f g Hf Hg Hfg.
  specialize (HR f g Hf Hg Hfg).
  eapply Rle_trans; eauto.
  rewrite (Rplus_comm ε1) -Rplus_assoc.
  apply Rplus_le_compat_r.
  apply Heq; eauto.
  intros; simplify_eq; lra.
Qed.

(* Maybe this can be generalized, but for now I only need this version *)
Lemma ARcoupl_from_eq_Rcoupl `{Countable A} (μ1 μ2 : distr A) ε :
  (0 <= ε) ->
  Rcoupl μ1 μ2 (=) ->
  ARcoupl μ1 μ2 (=) ε.
Proof.
  intros Hε Hcpl.
  rewrite (Rcoupl_eq_elim μ1 μ2); auto.
  apply (ARcoupl_mon_grading _ _ _ 0); auto.
  apply ARcoupl_eq.
Qed.

Lemma ARcoupl_dunif (N : nat) f `{Bij (fin N) (fin N) f} :
  ARcoupl (dunif N) (dunif N) (λ n m, m = f n) 0.
Proof.
  intros g h Hg Hh Hgh.
  rewrite !SeriesC_finite_foldr.
  rewrite Rplus_0_r.
  assert (exists l : list (fin N),
             foldr (Rplus ∘ (λ a : fin N, dunif N a * g a)) 0 (enum (fin N))
             <= foldr (Rplus ∘ (λ b : fin N, if bool_decide (b ∈ l) then dunif N b * h b else 0)) 0 (enum (fin N))) as [l H1]; last first.
  - etrans; first exact. remember (enum (fin N)) as n eqn:Heqn. clear Heqn H1.
    induction n.
    + done.
    + simpl. case_bool_decide; try lra.
      assert (0<=dunif N a * h a); last lra.
      apply Rmult_le_pos; [done|apply Hh].
  - remember (enum (fin N)) as n eqn:Heqn. rewrite {2}Heqn.
    assert (NoDup n) as Hnd.
    { subst. apply NoDup_enum. }
    clear Heqn.
    cut (
        foldr (Rplus ∘ (λ a : fin N, dunif N a * g a)) 0 n <=
          foldr (Rplus ∘ (λ b : fin N, if bool_decide (b ∈ f<$>n) then dunif N b * h b else 0)) 0
            (enum (fin N))).
    { intros. eexists _. done. }
    revert Hnd.
    induction n.
    + intros. clear. simpl. induction (fin_enum N); first done. simpl. lra.
    + intros Hnd. rewrite NoDup_cons in Hnd. destruct Hnd as [Hnd1 Hnd2].
      specialize (IHn Hnd2).
      simpl.
      trans (foldr (Rplus ∘ (λ b : fin N, if bool_decide (b = f a) then dunif N b * h b else 0)) 0
               (fin_enum N) + foldr (Rplus ∘ (λ b : fin N, if bool_decide (b ∈ f<$>n) then dunif N b * h b else 0)) 0 (fin_enum N)).
      * apply Rplus_le_compat; last done.
        trans (dunif N (f a) * h (f a)).
        { apply Rmult_le_compat; naive_solver. }
        clear IHn Hnd1 Hnd2.
        assert (f a ∈ fin_enum N).
        { replace (fin_enum _) with (enum (fin N)); last done.
          apply elem_of_enum.
        }
        apply elem_of_list_split in H0.
        destruct H0 as [?[? ->]].
        induction x.
        -- simpl. case_bool_decide; last done.
           apply Rle_plus_l; first lra.
           induction x0; simpl; first lra.
           case_bool_decide; try lra.
           apply Rplus_le_le_0_compat; last lra.
           apply Rmult_le_pos; naive_solver.
        -- simpl. assert (0<=if (bool_decide (a0 = f a)) then dunif N a0 * h a0 else 0); last lra.
           case_bool_decide; last lra.
           apply Rmult_le_pos; naive_solver.
      * induction (fin_enum N); first (simpl; lra).
        simpl.
        repeat case_bool_decide; subst.
        -- apply elem_of_list_fmap_2_inj in H1; first done. by destruct H.
        -- set_solver.
        -- lra.
        -- set_solver.
        -- lra.
        -- set_solver.
        -- set_solver.
        -- lra.
Qed.

Lemma ARcoupl_Bij (N : nat) f `{Bij (fin N) (fin N) f} (ε:nonnegreal):
  ARcoupl (dunif N) (dunif N) (λ n m, m = f n) ε <->
    ARcoupl (dmap f (dunif N)) (dmap id (dunif N)) (=) ε.
Proof.
  split; intros H1.
  - apply ARcoupl_map; first apply cond_nonneg.
    eapply ARcoupl_mono; last done; naive_solver.
  - rewrite dmap_id in H1.
    replace (nonneg ε) with (0+nonneg ε); last lra.
    eapply ARcoupl_eq_trans_r; [done|apply cond_nonneg| |done].
    erewrite <-(dmap_id (dunif N)) at 1.
    apply ARcoupl_map; first done.
    eapply ARcoupl_mono; last apply (ARcoupl_dunif _ id); naive_solver.
Qed.

Lemma ARcoupl_dunif_leq_inj (N M : nat) h `{Inj (fin N) (fin M) (=) (=) h}:
  (0 < N <= M) -> ARcoupl (dunif N) (dunif M) (λ n m, m = h n) ((M-N)/M).
Proof.
  intros Hleq f g Hg Hf Hfg.
  etrans; last first.
  { apply Rplus_le_compat_r.
    eapply (SeriesC_filter_leq _ (λ b, ∃ a, b = h a)).
    - intros. rewrite dunif_pmf. apply Rmult_le_pos.
      + rewrite -Rdiv_1_l. apply Rdiv_le_0_compat; lra.
      + naive_solver.
    - apply ex_seriesC_finite.
  }
  simpl.
  etrans; last first.
  { apply Rplus_le_compat_r.
    pose (hsome := λ x, Some (h x)).
    eapply (SeriesC_le_inj _ hsome).
    - intros. case_bool_decide; last lra.
      intros. rewrite dunif_pmf. apply Rmult_le_pos.
      + rewrite -Rdiv_1_l. apply Rdiv_le_0_compat; lra.
      + naive_solver.
    - rewrite /hsome. naive_solver.
    - apply ex_seriesC_finite.
  } simpl.
  etrans; last first.
  { apply Rplus_le_compat_l.
    instantiate (1:= SeriesC (λ x: fin N, (M-N)/(M*N))).
    rewrite SeriesC_finite_mass fin_card Rmult_div_assoc.
    rewrite (Rmult_comm N (M-N)). rewrite !Rdiv_def Rmult_assoc.
    apply Rmult_le_compat_l; first lra.
    rewrite -(Rdiv_1_l M). rewrite -Rdiv_def- Rle_div_r; last lra.
    apply Req_le_sym. rewrite Rdiv_mult_distr !Rdiv_def.
    rewrite (Rmult_assoc N) (Rmult_comm (/ M)) -Rmult_assoc.
    rewrite Rmult_inv_r; last lra.
    rewrite Rmult_1_l. rewrite Rmult_comm Rmult_inv_r; lra.
  }
  rewrite -SeriesC_plus; [|apply ex_seriesC_finite|apply ex_seriesC_finite].
  apply SeriesC_le; last apply ex_seriesC_finite.
  intros. case_bool_decide; last first.
  { exfalso. naive_solver. }
  split.
  - intros. rewrite dunif_pmf. apply Rmult_le_pos.
    + rewrite -Rdiv_1_l. apply Rdiv_le_0_compat; lra.
    + naive_solver.
  - intros. rewrite !dunif_pmf.
    etrans.
    { apply Rmult_le_compat_l.
      - rewrite -Rdiv_1_l. apply Rdiv_le_0_compat; lra.
      - apply Hfg. reflexivity.
    }
    cut ((/ N - / M)* g (h n) <=  (M - N) / (M * N)); first lra.
    trans ((/ N - / M)*1).
    + apply Rmult_le_compat_l; last naive_solver.
      rewrite -Rminus_le_0. apply Rinv_le_contravar; lra.
    + rewrite Rmult_1_r.
      cut (/ N - / M <= M / (M * N) - N/ (M*N)); first lra.
      cut (/N = M/(M*N)/\ /M=N/(M*N)); first lra.
      split.
      * rewrite -Rdiv_1_l. erewrite <-Rdiv_mult_l_l.
        -- f_equal. lra.
        -- lra.
      * rewrite -Rdiv_1_l. erewrite <-Rdiv_mult_l_r.
        -- f_equal. lra.
        -- lra.
Qed.

Lemma ARcoupl_dunif_leq (N M : nat):
  (0 < N <= M) -> ARcoupl (dunif N) (dunif M) (λ n m, fin_to_nat n = m) ((M-N)/M).
Proof.
  intros Hleq f g Hf Hg Hfg.
  assert (∀ x:fin N, (fin_to_nat x < M)%nat) as Hineq.
  { intros x. pose proof fin_to_nat_lt x. destruct Hleq as [? H1].
    apply INR_le in H1. lia. }
  eapply (ARcoupl_dunif_leq_inj _ _ (λ x:fin N, nat_to_fin (Hineq x))); try done.
  intros. apply Hfg.
  subst. by rewrite fin_to_nat_to_fin.
  Unshelve.
  intros ?? H. apply (f_equal fin_to_nat) in H.
  rewrite !fin_to_nat_to_fin in H.
  by apply fin_to_nat_inj.
Qed.

(* Note the asymmetry on the error wrt to the previous lemma *)
Lemma ARcoupl_dunif_leq_rev_inj (N M : nat) h `{Inj (fin M) (fin N) (=) (=) h}:
  (0 < M <= N) -> ARcoupl (dunif N) (dunif M) (λ n m, n = h m) ((N-M)/N).
Proof.
  intros Hleq f g Hf Hg Hfg.
  rewrite /pmf/=.
  do 2 rewrite SeriesC_scal_l.
  rewrite Rmult_comm.
  apply Rle_div_r.
  - apply Rlt_gt.
    apply Rinv_0_lt_compat; lra.
  - rewrite /Rdiv Rinv_inv Rmult_plus_distr_r.
    rewrite (Rmult_assoc (N-M)) Rinv_l; [ | lra].
    rewrite Rmult_1_r Rplus_comm.
    assert (SeriesC f <= SeriesC g + (N - M)) as Haux.
    { erewrite (SeriesC_split_pred _ (λ x, (bool_decide (∃ y, x= h y)))); [|naive_solver|apply ex_seriesC_finite].
      apply Rplus_le_compat.
      - apply SeriesC_filter_finite_1'; try done.
        destruct Hleq. split; [apply INR_lt|by apply INR_le].
        by simpl.
      - trans (SeriesC (λ a : fin (N-M), 1)); last first.
        + rewrite SeriesC_finite_mass fin_card Rmult_1_r minus_INR; try lra. apply INR_le. naive_solver.
        + etrans; first apply SeriesC_filter_finite_2; try done.
          * destruct Hleq. split; [apply INR_lt|by apply INR_le].
            by simpl.
          * rewrite SeriesC_finite_mass. rewrite fin_card. lra.
    }
    apply (Rle_trans _ (SeriesC g + (N - M))); auto.
    rewrite Rplus_comm.
    apply Rplus_le_compat_l.
    assert (0<=SeriesC g) as Hpos.
    { apply SeriesC_ge_0'. naive_solver. }
    rewrite Rmult_comm (Rmult_comm (/M)).
    rewrite -Rdiv_def Rmult_div_assoc.
    rewrite -Rle_div_r; last lra.
    rewrite Rmult_comm.
    apply Rmult_le_compat_r; lra.
Qed.

Lemma ARcoupl_dunif_leq_rev (N M : nat) :
  (0 < M <= N) -> ARcoupl (dunif N) (dunif M) (λ n m, fin_to_nat n = m) ((N-M)/N).
Proof.
  intros Hleq f g Hf Hg Hfg.
  assert (∀ x:fin M, (fin_to_nat x < N)%nat) as Hineq.
  { intros x. pose proof fin_to_nat_lt x. destruct Hleq as [? H1].
    apply INR_le in H1. lia. }
  eapply (ARcoupl_dunif_leq_rev_inj _ _ (λ x:fin M, nat_to_fin (Hineq x))); try done.
  intros. apply Hfg.
  subst. by rewrite fin_to_nat_to_fin.
  Unshelve.
  intros ?? H. apply (f_equal fin_to_nat) in H.
  rewrite !fin_to_nat_to_fin in H.
  by apply fin_to_nat_inj.
Qed.


Lemma ARcoupl_dunif_no_coll_l `{Countable A} (v : A) (N : nat) (x : fin N) :
  (0 < N ) -> ARcoupl (dunif N) (dret v) (λ m n, m ≠ x ∧ n = v) (1/N).
Proof with try (by apply ex_seriesC_finite) ; auto ; try done.
  intros Hleq f g Hf Hg Hfg.
  rewrite /pmf/=/dret_pmf.
  assert (∀ b, 0 <= g b) by apply Hg.
  assert (∀ b, g b <= 1) by apply Hg.
  assert (∀ a, 0 <= f a) by apply Hf.
  assert (∀ a, f a <= 1) by apply Hf.
  assert (0 <= / N) by (left ; apply Rinv_0_lt_compat ; lra).
  assert (forall n, 0 <= / N * f n).
  { intros ; apply Rmult_le_pos... }
  setoid_rewrite (SeriesC_ext _ (λ b, (if bool_decide (b = v) then g v else 0))) at 1; last first.
  { intro ; case_bool_decide ; simplify_eq ; real_solver. }
  transitivity (SeriesC (λ a : fin N, if bool_decide (a = x) then 1 / N else / N * f a )).
  { apply SeriesC_le...
    intros ; case_bool_decide ; split...
    rewrite -(Rmult_1_r (1/N)).
    apply Rmult_le_compat... nra. }
  rewrite (SeriesC_split_elem _ x)...
  - rewrite Rplus_comm.
    apply Rplus_le_compat.
    + etrans.
      * apply (SeriesC_finite_bound _ (/ N * g v)).
        intros; split.
        -- case_bool_decide; [|lra].
           rewrite bool_decide_eq_false_2...
        -- case_bool_decide.
           2: apply Rmult_le_pos...
           rewrite bool_decide_eq_false_2...
           apply Rmult_le_compat_l...
      * rewrite SeriesC_singleton fin_card.
        rewrite -Rmult_assoc Rinv_r ; lra.
    + etrans ; [ | right; apply (SeriesC_singleton x (1/N))].
      right ; apply SeriesC_ext => n.
      by case_bool_decide.
  - intro ; case_bool_decide... lra.
Qed.

Corollary ARcoupl_dunif_no_coll_l' (N : nat) (x : fin N) :
  (0 < N ) -> ARcoupl (dunif N) (dret x) (λ m n, m ≠ x ∧ n = x) (1/N).
Proof.
  apply ARcoupl_dunif_no_coll_l.
Qed.

Lemma ARcoupl_dunif_no_coll_r `{Countable A} (v : A) (N : nat) (x : fin N) :
  (0 < N ) -> ARcoupl (dret v) (dunif N) (λ m n, m = v ∧ n ≠ x) (1/N).
Proof with try (by apply ex_seriesC_finite) ; auto ; try done.
  intros Hleq f g Hf Hg Hfg.
  rewrite /pmf/=/dret_pmf.
  assert (∀ b, 0 <= g b) by apply Hg.
  assert (∀ b, g b <= 1) by apply Hg.
  assert (∀ a, 0 <= f a) by apply Hf.
  assert (∀ a, f a <= 1) by apply Hf.
  assert (0 <= / N) by (left ; apply Rinv_0_lt_compat ; lra).
  assert (forall n, 0 <= / N * f n).
  { intros ; apply Rmult_le_pos... }
  assert (forall a, 0 <= / N * g a).
  { intros ; apply Rmult_le_pos... }
  setoid_rewrite (SeriesC_ext _ (λ a, (if bool_decide (a = v) then f v else 0))) ; last first.
  { intro ; case_bool_decide ; simplify_eq ; real_solver. }
  transitivity (SeriesC (λ n : fin N, if bool_decide (n = x) then 0 else / N * g n) + 1/N) ; last first.
  { apply Rplus_le_compat...
    apply SeriesC_le...
    intros n.
    case_bool_decide... }
  rewrite -(SeriesC_singleton x (1 / N)).
  rewrite -SeriesC_plus...
  transitivity (SeriesC (λ _ : fin N, / N * f v)).
  + rewrite SeriesC_finite_mass SeriesC_singleton fin_card.
    rewrite -Rmult_assoc Rinv_r ; lra.
  + apply SeriesC_le...
    intros ; split...
    case_bool_decide.
    * rewrite Rplus_0_l -(Rmult_1_r (1/N)).
      apply Rmult_le_compat... nra.
    * rewrite Rplus_0_r. apply Rmult_le_compat_l...
Qed.

Corollary ARcoupl_dunif_no_coll_r' (N : nat) (x : fin N) :
  (0 < N) -> ARcoupl (dret x) (dunif N) (λ m n, m = x ∧ n ≠ x) (1/N).
Proof.
  eapply ARcoupl_dunif_no_coll_r.
Qed.

Lemma UB_to_ARcoupl `{Countable A, Countable B} (μ1 : distr A) (P : A -> Prop) (ε : R) :
  pgl μ1 P ε ->
  ARcoupl μ1 (dret tt) (λ a _, P a) ε.
Proof.
  rewrite /pgl /prob.
  intros Hub f g Hf Hg Hfg.
  rewrite SeriesC_finite_foldr; simpl.
  rewrite dret_1_1; last done.
  rewrite Rmult_1_l Rplus_0_r.
  remember ((λ a:A, negb (bool_decide (P a)))) as q. 
  rewrite (SeriesC_split_pred _ q).
  - rewrite Rplus_comm.
    apply Rplus_le_compat.
    + trans (SeriesC (λ a : A, if q a then 0 else μ1 a * g ())).
      * apply SeriesC_le; first subst.
        -- intros. case_bool_decide; simpl; try lra.
           split.
           ++ apply Rmult_le_pos; naive_solver.
           ++ apply Rmult_le_compat_l; auto.
        -- eapply (ex_seriesC_ext (λ a : A, if bool_decide (P a) then μ1 a * g () else 0)); last eapply ex_seriesC_filter_pos.
           ++ intros. subst. repeat case_bool_decide; done.
           ++ intros; apply Rmult_le_pos; naive_solver.
           ++ apply ex_seriesC_scal_r. done.
      * trans (SeriesC (λ a, μ1 a * g ())).
        -- apply SeriesC_le; last by apply ex_seriesC_scal_r.
           intros. subst. case_bool_decide; simpl; split; try lra.
           all: apply Rmult_le_pos; naive_solver.
        -- rewrite SeriesC_scal_r. etrans; first apply Rmult_le_compat_r; auto.
           ++ naive_solver.
           ++ lra.
    + etrans; last exact.
      apply SeriesC_le.
      * subst. intros. case_bool_decide; simpl; try lra.
        split.
        -- apply Rmult_le_pos; naive_solver.
        -- rewrite <- Rmult_1_r. apply Rmult_le_compat; naive_solver.
      * apply ex_seriesC_filter_bool_pos; auto.
  - intros. apply Rmult_le_pos; naive_solver.
  - apply pmf_ex_seriesC_mult_fn. naive_solver.
Qed.


Lemma ARcoupl_to_UB `{Countable A, Countable B} (μ1 : distr A) (μ2 : distr B) (P : A -> Prop) (ε : R) :
  ARcoupl μ1 μ2 (λ a _, P a) ε -> pgl μ1 P ε.
Proof.
  rewrite /ARcoupl/pgl/prob.
  intros Har.
  eset (λ a:A, if bool_decide (P a) then 0 else 1) as f.
  eset (λ b:B, 0) as g.
  specialize (Har f g).
  replace (ε) with (SeriesC (λ b, μ2 b * g b) + ε).
  { etrans; last apply Har.
    - apply SeriesC_le; last apply pmf_ex_seriesC_mult_fn.
      + intros. rewrite /f. repeat case_bool_decide; try done; simpl; split; try lra.
        done.
      + exists 1. rewrite /f. intros; case_match; lra.
    - intros. rewrite /f. case_match; lra.
    - rewrite /g. intros; lra.
    - intros. rewrite /f/g. case_match; first done.
      apply bool_decide_eq_false in H2. done. }
  rewrite /g.
  rewrite SeriesC_scal_r. lra.
Qed.

Lemma up_to_bad_lhs `{Countable A, Countable B} (μ1 : distr A) (μ2 : distr B) (P : A -> Prop) (Q : A → B → Prop) (ε ε' : R) :
  ARcoupl μ1 μ2 (λ a b, P a -> Q a b) ε ->
  pgl μ1 P ε' ->
  ARcoupl μ1 μ2 Q (ε + ε').
Proof.
  intros Hcpl Hub f g Hf Hg Hfg.
  set (P' := λ a, bool_decide (P a)).
  set (f' := λ a, if bool_decide (P a) then f a else 0).
  (* epose proof (Hub P' _) as Haux. *)
  (* Unshelve. *)
  (* 2:{ *)
  (*   intros a Ha; rewrite /P'. *)
  (*   case_bool_decide; auto. *)
  (* } *)
  (* rewrite /prob in Haux. *)
  rewrite -Rplus_assoc.
  eapply Rle_trans; [ | by apply Rplus_le_compat_l].
  eapply Rle_trans; last first.
  - eapply Rplus_le_compat_r.
    eapply (Hcpl f' g); auto.
    + intro a; specialize (Hf a).
      rewrite /f'; real_solver.
    + intros a b HPQ; rewrite /f'.
      case_bool_decide; [apply Hfg; auto | apply Hg ].
  - rewrite /f' /P' -SeriesC_plus.
    + apply SeriesC_le.
      * intro a; specialize (Hf a); split; [real_solver |].
        case_bool_decide; simpl; [lra | ].
        rewrite Rmult_0_r Rplus_0_l.
        real_solver.
      * apply (ex_seriesC_le _ (λ x, (μ1 x)*2)); [ | apply ex_seriesC_scal_r; auto].
        intro a; specialize (Hf a); split.
        -- case_bool_decide; simpl.
           ++ rewrite Rplus_0_r. real_solver.
           ++ rewrite Rmult_0_r Rplus_0_l //.
        -- case_bool_decide; simpl.
           ++ rewrite Rplus_0_r. real_solver.
           ++ rewrite Rmult_0_r Rplus_0_l //.
              rewrite <- Rmult_1_r at 1.
              real_solver.
    + apply (ex_seriesC_le _ μ1); auto.
      intro a; specialize (Hf a); real_solver.
    + apply (ex_seriesC_le _ μ1); auto.
      intro a; specialize (Hf a); real_solver.
Qed.


Lemma up_to_bad_rhs `{Countable A, Countable B} (μ1 : distr A) (μ2 : distr B) (P : B -> Prop) (Q : A → B → Prop) (ε ε' : R) :
  ARcoupl μ1 μ2 (λ a b, P b -> Q a b) ε ->
  pgl μ2 P ε' ->
  ARcoupl μ1 μ2 Q (ε + ε').
Proof.
  intros Hcpl Hub f g Hf Hg Hfg.
  set (P' := λ a, bool_decide (P a)).
  set (g' := λ a, if bool_decide (P a) then g a else 0).
  rewrite -Rplus_assoc.
  eapply Rle_trans; [ | by apply Rplus_le_compat_l].
  clear Hub.

  rewrite Rplus_assoc (Rplus_comm ε) -Rplus_assoc.
  rewrite -SeriesC_plus.
  2,3: apply (ex_seriesC_le _ (λ b : B, μ2 b)) => // ; real_solver.
  unfold ARcoupl in Hcpl.
  trans (SeriesC (λ b : B, μ2 b * g b + μ2 b * (if negb (bool_decide (P b)) then 1 else 0)) + ε) ; [|(right ; f_equal ; series)].
  setoid_rewrite <-Rmult_plus_distr_l.
  trans (SeriesC
           (λ b : B, μ2 b * Rmin 1 (g b + (if negb (bool_decide (P b)) then 1 else 0))) + ε).
  2:{ apply Rplus_le_compat_r. apply SeriesC_le.
      2:{
        eapply (ex_seriesC_le _ (λ b : B, μ2 b * (1 + 1))).
        2: apply ex_seriesC_scal_r => //.
        intros b. assert (0 <= g b) by real_solver.
        repeat real_solver_partial.
        all: apply Rplus_le_compat ; real_solver.
      }
      intros b.
      assert (0 <= g b /\ (g b <= 1)) by real_solver.
      repeat real_solver_partial.
      - rewrite Rmin_right ; real_solver.
      - rewrite Rmin_right ; real_solver.
      - rewrite Rmin_left ; real_solver.
      - rewrite Rmin_left ; real_solver.
  }
  apply Hcpl.
  1: real_solver.
  - intros b ; assert (0 <= g b /\ (g b <= 1)) by real_solver.
    repeat real_solver_partial.
    + rewrite Rmin_right ; real_solver.
    + rewrite Rmin_right ; real_solver.
    + rewrite Rmin_left ; real_solver.
    + rewrite Rmin_left ; real_solver.
  - repeat real_solver_partial.
    + rewrite Rplus_0_r. trans (g b). 1: eauto. rewrite Rmin_right. 1: lra. real_solver.
    + rewrite Rmin_left. 2: assert (0 <= g b) by real_solver ; real_solver.
      real_solver.
Qed.


Lemma ARcoupl_refRcoupl `{Countable A, Countable B}
  μ1 μ2 (ψ : A → B → Prop) : refRcoupl μ1 μ2 ψ -> ARcoupl μ1 μ2 ψ 0.
Proof.
  intros (μ&(<-&Hrm)&Hs).
  setoid_rewrite rmarg_pmf in Hrm.
  intros f g Hf Hg Hfg.
  rewrite Rplus_0_r.
  setoid_rewrite lmarg_pmf.
  etrans; last first.
  {
    apply SeriesC_le.
    - split; last first.
      + apply Rmult_le_compat_r; [apply Hg | apply Hrm].
      + simpl. apply Rmult_le_pos; [ | apply Hg].
        by apply SeriesC_ge_0'.
    - eapply ex_seriesC_le ; [ | eapply (pmf_ex_seriesC μ2)].
      intros; split.
      * apply Rmult_le_pos; auto. apply Hg.
      * rewrite <- Rmult_1_r.
        apply Rmult_le_compat_l; auto. apply Hg.
  }
  setoid_rewrite <- SeriesC_scal_r.
  rewrite (fubini_pos_seriesC (λ '(a,n), Rmult (μ (a, n)) (g n))).
  - apply SeriesC_le.
    + intro a; split.
      * apply SeriesC_ge_0'.
        intro.
        apply Rmult_le_pos; auto. apply Hf.
      * apply SeriesC_le.
        ** intro b; split.
           *** apply Rmult_le_pos; auto.
               apply Hf.
           *** destruct (decide ((μ(a,b) > 0)%R)) as [H3 | H4].
               **** apply Hs, Hfg in H3.
                    by apply Rmult_le_compat_l.
               **** apply Rnot_gt_le in H4.
                    replace (μ(a,b)) with 0%R; [ lra | by apply Rle_antisym].
        ** eapply ex_seriesC_le; [ | eapply (ex_seriesC_lmarg μ); eauto ].
           intros; split.
           *** apply Rmult_le_pos; auto.
               apply Hg.
           *** rewrite <- Rmult_1_r.
               apply Rmult_le_compat_l; auto.
               apply Hg.
    + eapply ex_seriesC_le; [ | eapply (fubini_pos_ex_seriesC_prod_ex_lr μ)]; eauto.
      * intro; simpl.
        split.
        ** apply SeriesC_ge_0'.
           intro; apply Rmult_le_pos; auto.
           apply Hg.
        ** apply SeriesC_le.
           *** intro; split.
               **** apply Rmult_le_pos; auto. apply Hg.
               **** rewrite <- Rmult_1_r.
                    apply Rmult_le_compat_l; eauto; eapply Hg.
           *** apply ex_seriesC_lmarg; auto.
  - intros; apply Rmult_le_pos; auto. apply Hg.
  - intros a.
    eapply ex_seriesC_le; [ | unshelve eapply (ex_seriesC_lmarg μ _ a) ]; eauto.
    intros. split.
    + apply Rmult_le_pos; auto. apply Hg.
    + rewrite <- Rmult_1_r. apply Rmult_le_compat_l; auto; apply Hg.
  - eapply ex_seriesC_le; [ | eapply (fubini_pos_ex_seriesC_prod_ex_lr μ)]; eauto.
    + intro; simpl.
      split.
      * apply SeriesC_ge_0'.
        intro; apply Rmult_le_pos; auto.
        apply Hg.
      * apply SeriesC_le.
        ** intro; split.
           *** apply Rmult_le_pos; auto. apply Hg.
           *** rewrite <- Rmult_1_r.
               apply Rmult_le_compat_l; eauto; eapply Hg.
        ** apply ex_seriesC_lmarg; auto.
Qed.

Lemma ARcoupl_exact `{Countable A, Countable B}
  μ1 μ2 (ψ : A → B → Prop) : Rcoupl μ1 μ2 ψ → ARcoupl μ1 μ2 ψ 0.
Proof.
  intros ; by eapply ARcoupl_refRcoupl, Rcoupl_refRcoupl.
Qed.

Lemma ARcoupl_limit `{Countable A, Countable B} μ1 μ2 ε (ψ : A -> B -> Prop):
  (forall ε', ε' > ε -> ARcoupl μ1 μ2 ψ ε') -> ARcoupl μ1 μ2 ψ ε.
Proof.
  rewrite /ARcoupl.
  intros Hlimit. intros.
  apply real_le_limit.
  intros. rewrite Rle_minus_l.
  rewrite Rplus_assoc.
  apply Hlimit; try done.
  lra.
Qed.

Lemma ARcoupl_antisym `{Countable A} (μ1 μ2: distr A):
  ARcoupl μ1 μ2 eq 0 -> ARcoupl μ2 μ1 eq 0 ->
  μ1 = μ2.
Proof.
  intros H1 H2.
  apply distr_ext.
  intros a.
  pose proof (ARcoupl_eq_elim _ _ _ H1 a).
  pose proof (ARcoupl_eq_elim _ _ _ H2 a). lra.
Qed. 
  
Lemma ARcoupl_tight `{Countable A} (μ1 μ2 : distr A) ε:
  ARcoupl μ1 μ2 eq ε <-> SeriesC (λ x, if bool_decide (μ2 x <= μ1 x) then μ1 x - μ2 x else 0) <= ε.
Proof.
  split.
  - rewrite /ARcoupl.
    set (f:=λ x, if bool_decide (μ2 x <= μ1 x) then 1 else 0).
    intros Hcoupl.
    assert (∀ x, 0<=f x <=1).
    { intros. rewrite /f. case_bool_decide; lra. }
    eassert (SeriesC _ <= SeriesC _ + _) as H'.
    { apply (Hcoupl f f); naive_solver. }
    rewrite Rplus_comm -Rle_minus_l in H'.
    etrans; last exact.
    rewrite Rle_minus_r.
    apply Req_le.
    rewrite -SeriesC_plus; last first.
    + apply pmf_ex_seriesC_mult_fn. naive_solver.
    + apply ex_seriesC_le with μ1; last done.
      intros. case_bool_decide; try done.
      split; first lra.
      by apply Rminus_le_0_compat.
    + apply SeriesC_ext.
      intros. rewrite /f.
      case_bool_decide; lra.
  - intros HseriesC f g Hf Hg Hfg.
    rewrite Rplus_comm -Rle_minus_l.
    etrans; last exact.
    rewrite Rle_minus_l. 
    rewrite -SeriesC_plus; last first.
    + apply pmf_ex_seriesC_mult_fn. naive_solver.
    + apply ex_seriesC_le with μ1; last done.
      intros. case_bool_decide; try done.
      split; first lra.
      by apply Rminus_le_0_compat.
    + apply SeriesC_le.
      * intros n. split.
        { apply Rmult_le_pos; naive_solver. }
        case_bool_decide.
        -- assert (f n <= g n) by naive_solver.
           rewrite -Rle_minus_l.
           trans (μ1 n * f n - μ2 n * f n).
           ++ apply Ropp_le_cancel. rewrite !Ropp_minus_distr.
              apply Rplus_le_compat_r.
              apply Rmult_le_compat_l; [done|lra].
           ++ rewrite -Rmult_minus_distr_r.
              rewrite -{2}(Rmult_1_r (_-_)).
              apply Rmult_le_compat_l; last naive_solver.
              lra.
        -- trans (μ1 n * g n).
           ++ apply Rmult_le_compat_l; [done|naive_solver].
           ++ rewrite Rplus_0_l. apply Rmult_le_compat_r; [naive_solver|lra].
      * apply ex_seriesC_le with (λ x, μ1 x + μ2 x); last first.
        { by apply ex_seriesC_plus. }
        intros; split; case_bool_decide.
        -- trans (μ1 n - μ2 n); first lra.
           apply Rplus_le_0_compat.
           apply Rmult_le_pos; naive_solver.
        -- rewrite Rplus_0_l. apply Rmult_le_pos; naive_solver.
        -- trans (μ1 n).
           ++ cut (μ1 n + μ2 n * g n <= μ1 n + μ2 n*1); first lra.
              apply Rplus_le_compat_l.
              apply Rmult_le_compat_l; [done|naive_solver].
           ++ by apply Rplus_le_0_compat.
        -- trans (μ2 n * 1).
           ++ rewrite Rplus_0_l.
              apply Rmult_le_compat_l; [done|naive_solver].
           ++ rewrite Rmult_1_r.
              rewrite Rplus_comm.
              by apply Rplus_le_0_compat.
Qed.
                 
Lemma ARcoupl_swap `{Countable A} (μ1 μ2 : distr A) ε:
  SeriesC μ2 <= SeriesC μ1 -> (ARcoupl μ1 μ2 eq ε -> ARcoupl μ2 μ1 eq ε).
Proof.
  intros Heq.
  rewrite !ARcoupl_tight.
  intros; etrans; last exact.
  cut (SeriesC (λ x : A, if bool_decide (μ1 x <= μ2 x) then μ2 x - μ1 x else 0) + SeriesC μ1<=
         SeriesC (λ x : A, if bool_decide (μ2 x <= μ1 x) then μ1 x - μ2 x else 0) + SeriesC μ2).
  { intros. lra. }
  rewrite -!SeriesC_plus; last first; try done.
  - apply ex_seriesC_le with (μ2); last done.
    intros; case_bool_decide; split; try (lra||done).
    apply Rminus_le_0_compat. done.
  - apply ex_seriesC_le with (μ1); last done.
    intros; case_bool_decide; split; try (lra||done).
    apply Rminus_le_0_compat. done.
  - apply SeriesC_le; last first.
    + apply ex_seriesC_le with (λ x, μ1 x+ μ2 x); last first.
      * by apply ex_seriesC_plus.
      * intros n.
        pose proof pmf_pos μ1 n.
        pose proof pmf_pos μ2 n.
        intros; case_bool_decide; lra.
    + intros.
      pose proof pmf_pos μ1 n.
      pose proof pmf_pos μ2 n.
      intros; repeat case_bool_decide; lra.
Qed.

Lemma ARcoupl_symmetric `{Countable A} (μ1 μ2 : distr A) ε:
  SeriesC μ1 = SeriesC μ2 -> (ARcoupl μ1 μ2 eq ε <-> ARcoupl μ2 μ1 eq ε).
Proof.
  intros; split; intros; apply ARcoupl_swap; (lra||naive_solver).
Qed.
  
Lemma ARcoupl_dunif_avoid N (l:list (fin N)):
  NoDup l->
  ARcoupl (dunif N) (dunif N) (λ x y, x∉l /\ x=y) (length l/N).
Proof.
  intros Hl.
  cut (∀ ε, ARcoupl (dunif N) (ssd (λ x, bool_decide(x∉l)) (dunif N)) (=) ε ->
            ARcoupl (dunif N) (dunif N) (λ x y, x∉l /\ x=y) ε).
  {
    intros H.
    apply H.
    apply ARcoupl_tight.
    rewrite (SeriesC_ext _ (λ x, if bool_decide(x∈l) then 1/(N) else 0)).
    - rewrite SeriesC_list_2; [lra|done].
    - intros.
      rewrite bool_decide_eq_true_2; last first.
      { rewrite /ssd/ssd_pmf/pmf/=. case_bool_decide; try lra.
        rewrite -Rdiv_1_l.
        apply Rdiv_INR_ge_0.
      }
      rewrite /ssd/ssd_pmf{2}/pmf.
      case_bool_decide.
      + rewrite bool_decide_eq_false_2; last done.
        lra.
      + rewrite bool_decide_eq_true_2; last done.
        rewrite dunif_pmf. lra.
  }
  intros ε Hcoupl f g Hf Hg Hfg.
  pose (g':=λ x, if bool_decide (x∈l) then 1 else g x).
  assert (∀ b, 0<=g' b <=1).
  { rewrite /g'. intros. case_bool_decide; try lra. naive_solver. }
  epose proof Hcoupl f g' _ _ _.
  etrans; first exact.
  apply Rplus_le_compat_r.
  apply SeriesC_le; last apply pmf_ex_seriesC_mult_fn; last naive_solver.
  intros n; split.
  - apply Rmult_le_pos; naive_solver.
  - rewrite /g'.
    rewrite /ssd/ssd_pmf{1}/pmf.
    case_bool_decide.
    + by rewrite bool_decide_eq_false_2.
    + rewrite Rmult_0_l.
      apply Rmult_le_pos; naive_solver.
    Unshelve.
    all: try done.
    intros ?? ->.
    rewrite /g'.
    case_bool_decide; naive_solver.
Qed.
    
      
    
