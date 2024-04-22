From Coq Require Import Reals Psatz.
From clutch.prob_lang Require Import rejection_sampler_distribution.
From clutch.common Require Import language.
From clutch.prob Require Export couplings distribution markov.

Section erasable.
  Definition erasable {Λ: language} (μ: distr (state Λ)) σ:=
    (∀ e m, μ ≫= (λ σ', exec m (e, σ'))= exec m (e, σ)).

  Lemma erasable_lim_exec {Λ: language} (μ: distr (state Λ)) σ :
    erasable μ σ->
    (∀ e, μ ≫= (λ σ', lim_exec (e, σ'))= lim_exec (e, σ)).
  Proof.
    rewrite /erasable.
    intros He e. apply distr_ext. intros c.
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
End erasable.

Section erasable_functions.
  Lemma rej_samp_state_erasable N σ α s (ns:list(fin(S N))) (Hfound: σ.(tapes)!!α = Some (N;ns)):
    erasable (rej_samp_state_distr N σ α s ns Hfound) σ.
  Proof.
    rewrite /erasable.
    intros e m.
    apply distr_ext_pmf.
  Admitted.
End erasable_functions.
