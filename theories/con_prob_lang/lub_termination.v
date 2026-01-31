From Coquelicot Require Import Lub Rbar Lim_seq.
From clutch.con_prob_lang Require Import erasure notation.
From Stdlib Require Import Reals.

Set Default Proof Using "Type*".

Definition termination_prob cfg sch_int_σ ζ `{Countable sch_int_σ} sch `{!TapeOblivious sch_int_σ sch} :=
  SeriesC (sch_lim_exec sch (ζ, cfg)).

Definition termination_prob_type:Type :=
  (sigT (λ sch_int_σ:Type,
                    sch_int_σ * 
                    sigT (λ Heqdecision:EqDecision sch_int_σ,
                            sigT (λ Hcountable : @Countable sch_int_σ Heqdecision,
                                    sigT (λ sch : @scheduler (con_lang_mdp con_prob_lang) sch_int_σ Heqdecision Hcountable,
                                            
                                                    @TapeOblivious sch_int_σ Heqdecision Hcountable sch
                                            
                                      )
                              )
  )))%type.

Definition termination_n_prob n cfg sch_int_σ ζ `{Countable sch_int_σ} sch `{!TapeOblivious sch_int_σ sch} :=
  SeriesC (sch_exec sch n (ζ, cfg)).

Definition termination_prob' e σ (r:R):=
  ∃ (p:termination_prob_type), 
    @termination_prob
      ([e], σ)
      (projT1 p)
      ((projT2 p).1)
      (projT1 $ (projT2 p).2)
      (projT1 $ projT2 $ (projT2 p).2)
      (projT1 $ projT2 $ projT2 $ (projT2 p).2)
      (projT2 $ projT2 $ projT2 $ (projT2 p).2) = r.

Definition termination_n_prob' n e σ (r:R) :=
  ∃ (p:termination_prob_type), 
    @termination_n_prob
      n
      ([e], σ)
      (projT1 p)
      ((projT2 p).1)
      (projT1 $ (projT2 p).2)
      (projT1 $ projT2 $ (projT2 p).2)
      (projT1 $ projT2 $ projT2 $ (projT2 p).2)
      (projT2 $ projT2 $ projT2 $ (projT2 p).2) = r.

Definition lub_termination_prob e σ:= (Lub_Rbar (termination_prob' e σ)).
Definition lub_termination_n_prob n e σ:= (Lub_Rbar (termination_n_prob' n e σ)).

Lemma lub_termination_sup_seq_termination_n e σ:
  lub_termination_prob e σ = Sup_seq (λ n, lub_termination_n_prob n e σ).
Proof.
  apply Rbar_le_antisym; rewrite /lub_termination_prob.
  - pose proof Lub_Rbar_correct (termination_prob' e σ) as H.
    apply H.
    rewrite /termination_prob'.
    rewrite /is_ub_Rbar.
    rewrite /termination_prob.
    intros r [? <-].
    rewrite sch_lim_exec_Sup_seq.
    rewrite rbar_finite_real_eq; last first.
    { eapply (is_finite_bounded 0 1).
      - eapply Sup_seq_minor_le. apply pmf_SeriesC_ge_0.
      - apply upper_bound_ge_sup. intros. apply pmf_SeriesC.
    }
    apply Sup_seq_le.
    rewrite /lub_termination_n_prob.
    intros n.
    pose proof Lub_Rbar_correct (termination_n_prob' n e σ) as H'.
    apply H'.
    rewrite /termination_n_prob'.
    eexists _.
    by instantiate (1:= (_;(_,(_;(_;(_;_)))))).
  - apply upper_bound_ge_sup.
    intros n.
    rewrite /lub_termination_n_prob.
    pose proof Lub_Rbar_correct (termination_n_prob' n e σ) as H. apply H.
    rewrite /is_ub_Rbar.
    intros r [x <-].
    etrans.
    + instantiate (1:= termination_prob ([e], σ) _ _ _).
      rewrite /termination_n_prob/termination_prob.
      apply SeriesC_le; last done.
      intros; split; first done.
      erewrite sch_lim_exec_unfold.
      apply Coquelicot_ext.rbar_le_finite.
      { eapply (is_finite_bounded 0 1).
      - eapply Sup_seq_minor_le. apply pmf_pos.
      - apply upper_bound_ge_sup. intros. apply pmf_le_1. }
      etrans; last apply sup_is_upper_bound. done.
    + 
    pose proof Lub_Rbar_correct (termination_prob' e σ) as H'.
    rewrite /is_lub_Rbar in H'.
    rewrite /is_ub_Rbar in H'.
    destruct H' as [H' _].
    apply H'.
    rewrite /termination_prob'.
    by exists x.
         Unshelve.
         { exact 0%nat. }
         { simpl.
           by destruct x as (?&?&?&?&?&?). 
         }
         exact 0%nat.
Qed.

Lemma lub_termination_prob_eq e σ: Rbar.Finite $ real $ lub_termination_prob e σ = lub_termination_prob e σ.
Proof.
  apply rbar_finite_real_eq. rewrite lub_termination_sup_seq_termination_n. 
  apply (is_finite_bounded 0 1).
  - eapply Sup_seq_minor_le with 0%nat.
    rewrite /lub_termination_n_prob.
    pose proof Lub_Rbar_correct (termination_n_prob' 0 e σ) as [H ?].
    etrans; last apply H; last first.
    + rewrite /termination_n_prob'. by eexists. 
    + simpl. rewrite /termination_n_prob. apply pmf_SeriesC_ge_0.
  - apply upper_bound_ge_sup.
    intros.
    rewrite /lub_termination_n_prob.
    pose proof Lub_Rbar_correct (termination_n_prob' n e σ) as [? H'].
    apply H'.
    rewrite /termination_n_prob'.
    intros ? H1. destruct H1 as [[?[?[?[?[]]]]] <-].
    simpl. rewrite /termination_n_prob.
    apply pmf_SeriesC.
    Unshelve.
    rewrite /termination_prob_type. 
    eexists unit. constructor; [constructor|].
    do 2 econstructor.
    eexists  {| scheduler_f := inhabitant |}.
    done. 
Qed. 
