From Coquelicot Require Import Lub Rbar Lim_seq.
From iris.proofmode Require Import base proofmode.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.base_logic Require Import error_credits.
From clutch.foxtrot Require Import weakestpre primitive_laws oscheduler full_info.
From clutch.prob Require Import distribution couplings_app.
Import uPred.

Section adequacy.
  Context `{!foxtrotGS Σ}.

  Lemma wp_adequacy_step_fupdN sch_int_σ `{Countable sch_int_σ} sch ζ `{!TapeOblivious sch_int_σ sch} σ σ' (ε:nonnegreal) e es es' ϕ n:
    state_interp σ ∗ err_interp ε ∗ spec_interp (es', σ') ∗
    WP e {{ v, ∃ v' : val, 0 ⤇ Val v' ∗ ⌜ϕ v v'⌝ }} ∗ ([∗ list] e' ∈ es, WP e' {{ _, True }})
    ⊢ |={⊤,∅}=> |={∅}▷=>^n
                 ⌜∀ ε', ε'>0 -> ∃ (osch:full_info_oscheduler),
                   ARcoupl (sch_exec sch n (ζ, (e::es, σ))) (osch_lim_exec osch ([], (es', σ')))
                     (λ v '(l, ρ), ∃ v', ρ.1!!0%nat = Some (Val v') /\ ϕ v v') (ε + ε') ⌝.
  Proof.
  Admitted.
                              
End adequacy.


Lemma foxtrot_adequacy_full_info_intermediate_multi Σ `{foxtrotGpreS Σ} (ε:R) ϕ n e es es' :
  (0 <= ε)%R -> 
  (∀ `{foxtrotGS Σ}, ⊢ ↯ ε -∗
                     ([∗ map] n↦e ∈ (to_tpool es'), n ⤇ e) -∗
                     WP e {{ v, ∃ v', 0%nat ⤇ Val v' ∗ ⌜ ϕ v v' ⌝ }} ∗
                     [∗ list] e'∈ es, WP e' {{ _, True%I }}
  ) ->
  ∀ sch_int_σ `(Countable sch_int_σ) sch ζ `{!TapeOblivious sch_int_σ sch} σ σ' ε',
  ε'>0 ->
  ∃ (osch:full_info_oscheduler),
    ARcoupl (sch_exec sch n (ζ, (e::es, σ))) (osch_lim_exec osch ([], (es', σ')))
      (λ v '(l, ρ), ∃ v', ρ.1!!0%nat = Some (Val v') /\ ϕ v v') (ε + ε').
Proof.
  intros Heps Hwp.
  intros ????????. 
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod (spec_ra_init es' σ') as (HspecGS) "(Hs & Hj & ?)".
  destruct (decide (ε < 1)) as [? | K%Rnot_lt_le].
  - set ε_nonneg := mknonnegreal _ Heps.
    iMod (ec_alloc ε_nonneg) as (?) "[HE He]"; [done|].
    set (HfoxtrotGS := HeapG Σ _ _ _ γH γT HspecGS _).
    iApply (wp_adequacy_step_fupdN _ _ _ _ _ ε_nonneg).
    iFrame.
    simpl.
    iApply (Hwp with "[He][-]").
    + iApply ec_eq; last done.
      done.
    + iFrame.
  - iApply fupd_mask_intro; [done|]; iIntros "_".
    iApply step_fupdN_intro; [done|]; iModIntro.
    iPureIntro. eexists full_info_inhabitant.
    apply ARcoupl_1.
    simpl in *. lra.
Qed.


Lemma foxtrot_adequacy_full_info_intermediate Σ `{foxtrotGpreS Σ} (ε:R) ϕ n e e' :
  (0 <= ε)%R -> 
  (∀ `{foxtrotGS Σ}, ⊢ ↯ ε -∗ 0%nat ⤇ e' -∗ WP e {{ v, ∃ v', 0%nat ⤇ Val v' ∗ ⌜ ϕ v v' ⌝ }}) ->
  ∀ sch_int_σ `(Countable sch_int_σ) sch ζ `{!TapeOblivious sch_int_σ sch} σ σ' ε',
  ε'>0 ->
  ∃ (osch:full_info_oscheduler),
    ARcoupl (sch_exec sch n (ζ, ([e], σ))) (osch_lim_exec osch ([], ([e'], σ')))
      (λ v '(l, ρ), ∃ v', ρ.1!!0%nat = Some (Val v') /\ ϕ v v') (ε + ε').
Proof.
  intros ? Hwp ??????????.
  by epose proof foxtrot_adequacy_full_info_intermediate_multi _ _ _ _ e [] [e'] _ _ _ _ _ _ _ _ _ _.
  Unshelve.
  all: try done.
  iIntros (?) "? H". simpl. rewrite /to_tpool.
  iSplit; last done.
  iApply (Hwp with "[$]").
  iApply big_sepM_lookup; last iFrame.
  simpl. apply lookup_insert.
Qed.

Lemma foxtrot_adequacy_intermediate Σ `{foxtrotGpreS Σ} (ε:R) ϕ n e e' :
  (0 <= ε)%R -> 
  (∀ `{foxtrotGS Σ}, ⊢ ↯ ε -∗ 0%nat ⤇ e' -∗ WP e {{ v, ∃ v', 0%nat ⤇ Val v' ∗ ⌜ ϕ v v' ⌝ }}) ->
  ∀ sch_int_σ `(Countable sch_int_σ) sch ζ `{!TapeOblivious sch_int_σ sch} σ σ' ε',
  ε'>0 ->
  ∃ `(Countable sch_int_σ') sch' ζ' `(!TapeOblivious sch_int_σ' sch'),
     ARcoupl (sch_exec sch n (ζ, ([e], σ))) (sch_lim_exec sch' (ζ', ([e'], σ'))) ϕ (ε + ε').
Proof.
  intros Heps Hwp.
  intros ??? sch ζ ? ? ? ε' ?.
  epose proof foxtrot_adequacy_full_info_intermediate _ _ _ _ _ _ Heps Hwp _ _ sch ζ _ _ _ _ as [osch Hcoupl].
  epose proof osch_to_sch osch as [sch'[Htape ?]].
  eexists _, _, _, sch', [], Htape.
  replace (_+_)%R with ((ε+ε')+0)%R; last lra.
  eapply (ARcoupl_eq_trans_r _ ((osch_lim_exec_val osch ([], ([e'], _))))) ; [lra|done| |by apply ARcoupl_eq_0].
  rewrite osch_lim_exec_exec_val.
  replace (_+_)%R with ((ε+ε')+0)%R; last lra.
  rewrite -(dret_id_right (sch_exec _ _ _)).
  eapply ARcoupl_dbind; try done.
  { real_solver. }
  simpl. intros ? [?[??]][? [Hsome ?]].
  simpl. simpl in *. rewrite Hsome.
  simpl. by apply ARcoupl_dret.
  Unshelve. done.
Qed.

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
      rewrite sch_lim_exec_unfold.
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

Lemma Rbar_le_lub R S : (∀ r, R r -> ∀ ε, (ε > 0)%R -> ∃ r', r-ε<= r' /\ S r') ->
                        Rbar_le (Lub_Rbar R) (Lub_Rbar S).
Proof.
  intros H.
  apply Lub_Rbar_correct.
  rewrite /is_ub_Rbar.
  intros r Hr.
  apply Rbar_le_plus_epsilon.
  intros eps Heps.
  replace eps with (- - eps) by lra.
  apply Rbar_le_opp.
  pose proof (H _ Hr eps Heps) as (r' & Hr' & Hs).
  trans r'.
  { simpl. lra. }
  by apply Lub_Rbar_correct.
Qed.

Lemma foxtrot_adequacy Σ `{foxtrotGpreS Σ} ϕ e e' σ σ' : 
  (∀ `{foxtrotGS Σ}, ⊢ 0%nat ⤇ e' -∗ WP e {{ v, ∃ v', 0%nat ⤇ Val v' ∗ ⌜ ϕ v v' ⌝ }}) ->
  Rbar_le (lub_termination_prob e σ) (lub_termination_prob e' σ').
Proof.
  intros Hwp.
  rewrite lub_termination_sup_seq_termination_n.
  apply upper_bound_ge_sup.
  intros n.
  apply Rbar_le_lub.
  rewrite /termination_prob'.
  intros r [(sch_int_σ&ζ&Heqdecision&Hcountable&sch&Htape) <-].
  simpl.
  intros ε Hε.
  epose proof foxtrot_adequacy_intermediate Σ 0 ϕ n e e' _ _ as Hwp'. Unshelve.
  2: { done. }
  2: { iIntros. by iApply Hwp. }
  epose proof Hwp' sch_int_σ Heqdecision Hcountable sch ζ Htape σ σ' ε Hε as
    (sch_int_σ'&Heqdeicision'&Hcountable'&sch'&ζ'&Htape'&Hcoupl).
  apply ARcoupl_mass_leq in Hcoupl.
  replace (0+_) with ε in Hcoupl by lra.
  exists (SeriesC (sch_lim_exec sch' (ζ', ([e'], σ')))). split.
  - rewrite /termination_n_prob. rewrite Rcomplements.Rle_minus_l.
    apply Hcoupl.
  - rewrite /termination_prob_type.
    eexists (sch_int_σ'; _); simpl.
    instantiate (1:=(ζ', (_;(_;(_;Htape'))))).
    by rewrite /termination_prob.
Qed.
