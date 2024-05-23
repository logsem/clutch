From Coq Require Import Reals Psatz.
From clutch.prob_lang Require Import rejection_sampler_distribution.
From clutch.common Require Import language.
From clutch.prob Require Export couplings distribution markov.

Section erasable.
  Context {Λ : language}.

  Definition erasable (μ : distr (state Λ)) σ:=
    ∀ e m, μ ≫= (λ σ', exec m (e, σ')) = exec m (e, σ).

  Definition erasable_dbind (μ1 : distr(state Λ)) (μ2 : state Λ → distr (state Λ)) σ:
    erasable μ1 σ → (∀ σ', μ1 σ' > 0 → erasable (μ2 σ') σ') → erasable (μ1 ≫= μ2) σ.
  Proof.
    intros H1 H2.
    rewrite /erasable.
    intros. rewrite -dbind_assoc'.
    rewrite -H1. apply dbind_eq; last naive_solver.
    intros. by apply H2.
  Qed.

  Lemma erasable_lim_exec (μ : distr (state Λ)) σ e :
    erasable μ σ →
    μ ≫= (λ σ', lim_exec (e, σ')) = lim_exec (e, σ).
  Proof.
    rewrite /erasable.
    intros He. apply distr_ext. intros c.
    rewrite /dbind{1}/pmf/dbind_pmf. simpl.
    rewrite /lim_exec. rewrite lim_distr_pmf.
    assert ((Rbar.real (Lim_seq.Sup_seq (λ n : nat, Rbar.Finite (exec n (e, σ) c)))) =
      (Rbar.real (Lim_seq.Sup_seq (λ n : nat, Rbar.Finite ((μ ≫= (λ σ', exec n (e, σ'))) c))))) as Heq.
    { f_equal. apply Lim_seq.Sup_seq_ext. intros n. rewrite He. done. }
    rewrite Heq.
    setoid_rewrite lim_distr_pmf; last first.
    { intros. rewrite /dbind/pmf/dbind_pmf.
      apply SeriesC_le.
      - intros. split; first real_solver.
        epose proof exec_mono. real_solver.
      - apply pmf_ex_seriesC_mult_fn.
        exists 1. intros. auto.
    }
    rewrite /dbind{3}/pmf/dbind_pmf/=.
    assert
     (SeriesC (λ a : state Λ, μ a * Rbar.real (Lim_seq.Sup_seq (λ n : nat, Rbar.Finite (exec n (e, a) c)))) =
     SeriesC (λ a, Rbar.real (Lim_seq.Sup_seq (λ n : nat, Rbar.Finite (μ a * exec n (e, a) c))))) as Haux.
   { apply SeriesC_ext; intro v'.
     apply eq_rbar_finite.
     rewrite rmult_finite.
     rewrite (rbar_finite_real_eq (Lim_seq.Sup_seq (λ n : nat, Rbar.Finite (exec n (e, v') c)))); auto.
     - rewrite <- (Lim_seq.Sup_seq_scal_l ); auto.
     - apply (Rbar_le_sandwich 0 1).
       + apply (Lim_seq.Sup_seq_minor_le _ _ 0%nat); simpl; auto.
       + apply upper_bound_ge_sup; intro; simpl; auto.
   }
   rewrite Haux.
   eapply MCT_seriesC.
    - intros. real_solver.
    - intros. epose proof exec_mono. real_solver.
    - intros. exists 1. intros. real_solver.
    - intros. apply SeriesC_correct.
      apply pmf_ex_seriesC_mult_fn.
      exists 1. intros. auto.
    - rewrite rbar_finite_real_eq.
      + apply Lim_seq.Sup_seq_correct.
      + apply (Rbar_le_sandwich 0 1); auto.
        * apply (Lim_seq.Sup_seq_minor_le _ _ 0%nat); simpl.
          apply SeriesC_ge_0'. intros. case_match; real_solver.
        * apply upper_bound_ge_sup; intro; simpl; auto.
          trans (SeriesC (μ)); last auto.
          apply SeriesC_le; last auto.
          intros. real_solver.
  Qed.

  Lemma erasable_dret_val (μ : distr (state Λ)) σ (v : val Λ) :
    erasable μ σ → dret v = μ ≫= λ _, dret v.
  Proof.
    intros Her.
    assert (to_final (of_val v, σ) = Some v).
    { rewrite /= to_of_val //. }
    rewrite -(exec_is_final (of_val v, σ) v 1) //.
    rewrite -{1}Her //.
    by setoid_rewrite exec_is_final.
  Qed.

  Lemma erasable_pexec_lim_exec (μ : distr (state Λ)) n σ e :
    erasable μ σ →
    (σ' ← μ; pexec n (e, σ')) ≫= lim_exec = lim_exec (e, σ).
  Proof.     
    intros Hμ.
    rewrite -(erasable_lim_exec μ) //.
    setoid_rewrite (lim_exec_pexec n).
    rewrite -dbind_assoc //.
  Qed.   

  Lemma erasable_dbind_predicate `{Countable A} (μ : distr _) μ1 μ2 (σ : state Λ) (f: A → bool):
    SeriesC μ = 1 →
    erasable μ1 σ →
    erasable μ2 σ →
    erasable (dbind (λ x, if f x then μ1 else μ2) μ) σ.
  Proof.
    rewrite /erasable.
    intros Hsum H1 H2.
    intros e m. rewrite -dbind_assoc'.
    rewrite {1}/dbind/dbind_pmf/=.
    apply distr_ext. intros v. rewrite {1}/pmf/=.
    erewrite (SeriesC_ext _ (λ a : A, μ a * exec m (e, σ) v)).
    { rewrite SeriesC_scal_r. rewrite Hsum. apply Rmult_1_l. }
    intros. case_match.
    - by rewrite H1.
    - by rewrite H2.
  Qed.

End erasable.

Section erasable_functions.

  Lemma dret_erasable {Λ} (σ : state Λ) :
    erasable (dret σ) σ.
  Proof.
    intros.
    rewrite /erasable.
    intros. rewrite dret_id_left'. done.
  Qed.

  Lemma rej_samp_state_erasable N σ α s (ns:list(fin(S N))) (Hfound: σ.(tapes)!!α = Some (N;ns)):
    erasable (rej_samp_state_distr N σ α s ns Hfound) σ.
  Proof.
    rewrite /erasable.
    intros e m.
    apply distr_ext_pmf.
  Admitted.
End erasable_functions.
