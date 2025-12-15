From Stdlib Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export fixpoint big_op.
From iris.prelude Require Import options.

From clutch.bi Require Export weakestpre.
From clutch.prelude Require Import stdpp_ext iris_ext NNRbar.
From clutch.con_prob_lang Require Import lang erasure.
From clutch.coneris Require Import weakestpre.
From clutch.foxtrot Require Import weakestpre oscheduler full_info.

Import uPred.

Set Default Proof Using "Type*".

Section relate.
  Context `{H:!foxtrotWpGS con_prob_lang Σ}.
  Global Instance foxtrotGS_conerisGS : conerisWpGS con_prob_lang Σ := {
      conerisWpGS_invGS := foxtrotWpGS_invGS;
      coneris.weakestpre.state_interp := state_interp ;
      coneris.weakestpre.fork_post :=  fork_post;
      coneris.weakestpre.err_interp := err_interp;
    }.

  Definition foxtrot_wp := wp (Wp :=wp').
  Definition coneris_wp := wp (Wp:=pgl_wp').

  
  Lemma state_step_coupl_implies_spec_coupl σ ρ ε Φ1 Φ2:
    □(∀ σ' ε', spec_interp ρ -∗ Φ1 σ' ε' -∗ Φ2 σ' ρ ε') -∗
     state_step_coupl σ ε Φ1 -∗ spec_interp ρ -∗ spec_coupl σ ρ ε Φ2.
  Proof.
    iIntros "#H H'".
    rewrite /state_step_coupl/state_step_coupl'.
    iApply (least_fixpoint_ind _ (λ '(σ, ε), spec_interp ρ -∗ spec_coupl σ ρ ε Φ2)%I with "[][$H']").
    iModIntro.
    iIntros ([σ1 ε1]).
    iIntros "[%H'| [H'|[H'|H']]] Hspec".
    - by iApply spec_coupl_ret_err_ge_1.
    - iApply spec_coupl_ret. by iApply ("H" with "[$]").
    - iApply spec_coupl_amplify. iIntros. iDestruct ("H'" with "[//]") as "[H' _]".
      by iApply "H'".
    - iDestruct "H'" as "(%μ & %ε2 & % & [%r %] & %Hineq  &H')".
      iApply (spec_coupl_step_l_dret_adv (λ _, True) μ 0%NNR (λ σ, if bool_decide (μ σ > 0)%R then ε2 σ else 1)%NNR); try done.
      + exists (Rmax r 1).
        intros; case_bool_decide.
        * etrans; last apply Rmax_l. done.
        * simpl. apply Rmax_r.
      + simpl. rewrite Rplus_0_l. etrans; last exact.
        rewrite /Expval. apply Req_le.
        apply SeriesC_ext.
        intros n. case_bool_decide; first done.
        destruct (pmf_pos μ n) as [K|K].
        * exfalso. apply Rlt_gt in K. naive_solver.
        * simpl. rewrite -K. lra.
      +  by apply pgl_trivial.
      + iIntros. case_bool_decide.
        * iDestruct ("H'" $!_ ) as "[H' _]". by iApply "H'".
        * by iApply spec_coupl_ret_err_ge_1.
          Unshelve.
          -- apply state_step_coupl_pre_mono.
          -- intros ?[][][].
             by do 2 f_equiv.
  Qed. 
  
  Lemma coneris_prog_coupl_implies_prog_coupl e σ ρ ε Φ1 Φ2:
    □ (∀ e2  σ2 efs,
      Φ1 e2 σ2 efs 1%NNR) -∗
    (∀ e' σ' efs ε', spec_interp ρ -∗ Φ1 e' σ' efs ε' -∗ Φ2 e' σ' efs ρ ε') -∗
    coneris.weakestpre.prog_coupl e σ ε Φ1-∗
    spec_interp ρ -∗ 
    prog_coupl e σ ρ ε Φ2 .
  Proof.
    iIntros "#? H Hprog Hspec".
    iDestruct (prog_coupl_equiv1 with "[$][$]") as "H'".
    iDestruct "H'" as "(%R2&%ε1&%ε2&%&% & %Hineq & %Hpgl & H')".
    iApply prog_coupl_step_l_dret_adv; try done.
    iIntros.
    iApply ("H" with "[$]").
    by iApply "H'".
  Qed.
  
  Lemma coneris_implies_foxtrot s E e Φ:
    coneris_wp s E e Φ -∗ foxtrot_wp s E e Φ.
  Proof.
    rewrite /coneris_wp/foxtrot_wp.
    iLöb as "IH" forall (e E Φ).
    rewrite pgl_wp_unfold wp_unfold.
    rewrite /pgl_wp_pre/wp_pre.
    iIntros "H" (???) "(H1&H2&H3)".
    unshelve iMod ("H" with "[$]") as "H". 
    iModIntro.
    iApply (state_step_coupl_implies_spec_coupl with "[][$][$]").
    iModIntro.
    iIntros (??) "Hspec".
    case_match.
    { iIntros ">(?&?&?)". by iFrame. }
    iIntros.
    iApply (coneris_prog_coupl_implies_prog_coupl with "[][][$][$]").
    { iModIntro. iIntros. iNext.
      by iApply state_step_coupl_ret_err_ge_1.
    }
    iIntros (????) "Hspec H !>".
    iApply (state_step_coupl_implies_spec_coupl with "[][$][$]").
    iModIntro. 
    iIntros (??) " Hspec >(?&?&H&Hefs)".
    iFrame.
    iModIntro. iSplitL "H".
    { by iApply "IH". }
    iInduction efs as [|ef efs'] "IH'"; first done.
    iDestruct "Hefs" as "[Hef Hefs]".
    iSplitL "Hef".
    { by iApply "IH". }
    by iApply "IH'".
  Qed. 

  

End relate.
