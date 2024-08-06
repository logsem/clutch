From Coq Require Import Reals Psatz.
From clutch.common Require Import con_language.
From clutch.prob Require Export couplings distribution mdp.

Section sch_erasable.
  Context {Λ : conLanguage}.
  Context (P : ∀ {t} {Heq: EqDecision t} {Hcount: Countable t}, scheduler (con_lang_mdp Λ) t -> Prop).
  Global Arguments P {_ _ _} (_).
  
  Definition sch_erasable (μ : distr (state Λ)) σ:=
    ∀ (sch_state:Type) `(H:Countable sch_state) (sch : scheduler (con_lang_mdp Λ) sch_state) es ζ m,
    P sch ->
    μ ≫= (λ σ', sch_exec sch m (ζ, (es, σ'))) = sch_exec sch m (ζ, (es, σ)).

  Definition sch_erasable_dbind (μ1 : distr(state Λ)) (μ2 : state Λ → distr (state Λ)) σ:
    sch_erasable μ1 σ → (∀ σ', μ1 σ' > 0 → sch_erasable (μ2 σ') σ') → sch_erasable (μ1 ≫= μ2) σ.
  Proof.
    intros H1 H2.
    rewrite /sch_erasable.
    intros. rewrite -dbind_assoc'.
    rewrite -H1; last done. apply dbind_eq; last naive_solver.
    intros. by apply H2.
  Qed.

  Lemma sch_erasable_sch_lim_exec
    (μ : distr (state Λ)) `{Countable sch_state} (sch : scheduler (con_lang_mdp Λ) sch_state) σ es ζ :
    sch_erasable μ σ →
    P sch ->
    μ ≫= (λ σ', sch_lim_exec sch (ζ, (es, σ'))) = sch_lim_exec sch (ζ, (es, σ)).
  Proof.
    rewrite /sch_erasable.
    intros He HP. apply distr_ext. intros c.
    rewrite /dbind{1}/pmf/dbind_pmf. simpl.
    rewrite /sch_lim_exec. rewrite lim_distr_pmf.
    assert ((Rbar.real (Lim_seq.Sup_seq (λ n : nat, Rbar.Finite (sch_exec sch n (ζ, (es, σ)) c)))) =
      (Rbar.real (Lim_seq.Sup_seq (λ n : nat, Rbar.Finite ((μ ≫= (λ σ', sch_exec sch n (ζ, (es, σ')))) c))))) as Heq.
    { f_equal. apply Lim_seq.Sup_seq_ext. intros n. rewrite He; done. }
    rewrite Heq.
    setoid_rewrite lim_distr_pmf; last first.
    { intros. rewrite /dbind/pmf/dbind_pmf.
      apply SeriesC_le.
      - intros. split; first real_solver.
        epose proof sch_exec_mono. real_solver.
      - apply pmf_ex_seriesC_mult_fn.
        exists 1. intros. auto.
    }
    rewrite /dbind{3}/pmf/dbind_pmf/=.
    assert
     (SeriesC (λ a : state Λ, μ a * Rbar.real (Lim_seq.Sup_seq (λ n : nat, Rbar.Finite (sch_exec sch n (ζ, (es, a)) c)))) =
     SeriesC (λ a, Rbar.real (Lim_seq.Sup_seq (λ n : nat, Rbar.Finite (μ a * sch_exec sch n (ζ, (es, a)) c))))) as Haux.
   { apply SeriesC_ext; intro v'.
     apply eq_rbar_finite.
     rewrite rmult_finite.
     rewrite (rbar_finite_real_eq (Lim_seq.Sup_seq (λ n : nat, Rbar.Finite (sch_exec sch n (ζ, (es, v')) c)))); auto.
     - rewrite <- (Lim_seq.Sup_seq_scal_l ); auto.
     - apply (Rbar_le_sandwich 0 1).
       + apply (Lim_seq.Sup_seq_minor_le _ _ 0%nat); simpl; auto.
       + apply upper_bound_ge_sup; intro; simpl; auto.
   }
   rewrite Haux.
   eapply MCT_seriesC.
    - intros. real_solver.
    - intros. epose proof sch_exec_mono. real_solver.
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

  (* Lemma sch_erasable_dret_val (μ : distr (state Λ)) σ (v : val Λ) : *)
  (*   sch_erasable μ σ → dret v = μ ≫= λ _, dret v. *)
  (* Proof. *)
  (*   intros Her. *)
  (*   assert (to_final (of_val v, σ) = Some v). *)
  (*   { rewrite /= to_of_val //. } *)
  (*   rewrite -(exec_is_final (of_val v, σ) v 1) //. *)
  (*   rewrite -{1}Her //. *)
  (*   by setoid_rewrite exec_is_final. *)
  (* Qed. *)

  Lemma sch_erasable_pexec_sch_lim_exec
    `{Countable sch_state} (sch : scheduler (con_lang_mdp Λ) sch_state) (μ : distr (state Λ)) n σ e ζ :
    sch_erasable μ σ →
    P sch ->
    (σ' ← μ; sch_pexec sch n (ζ, (e, σ'))) ≫= sch_lim_exec sch = sch_lim_exec sch  (ζ, (e, σ)).
  Proof.     
    intros Hμ HP.
    rewrite -(sch_erasable_sch_lim_exec μ) //.
    setoid_rewrite (sch_lim_exec_pexec sch n).
    rewrite -dbind_assoc //.
  Qed.   

  Lemma sch_erasable_dbind_predicate `{Countable A} (μ : distr _)  μ1 μ2 (σ : state Λ) (f: A → bool):
    SeriesC μ = 1 →
    sch_erasable μ1 σ →
    sch_erasable μ2 σ →
    sch_erasable (dbind (λ x, if f x then μ1 else μ2) μ) σ.
  Proof.
    rewrite /sch_erasable.
    intros Hsum H1 H2.
    intros ζ ? ? sch e m ac HP. rewrite -dbind_assoc'.
    rewrite {1}/dbind/dbind_pmf/=.
    apply distr_ext. intros v. rewrite {1}/pmf/=.
    erewrite (SeriesC_ext _ (λ a : A, μ a * sch_exec sch ac (m, (e, σ)) v)).
    { rewrite SeriesC_scal_r. rewrite Hsum. apply Rmult_1_l. }
    intros. case_match.
    - by rewrite H1.
    - by rewrite H2.
  Qed.

End sch_erasable.

Section sch_erasable_functions.

  Lemma dret_sch_erasable {Λ} 
    (σ : state Λ) :
    sch_erasable (λ _, True) (dret σ) σ.
  Proof.
    intros.
    rewrite /sch_erasable.
    intros. rewrite dret_id_left'. done.
  Qed.
  
End sch_erasable_functions.
