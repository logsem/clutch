(** * Examples related to rejection samplers with a bounded number of attempts *)
From clutch.ub_logic Require Export ub_clutch ub_rules.
From clutch Require Export examples.approximate_samplers.approx_sampler_lib.
From Coquelicot Require Import Series.
Require Import Lra.

Set Default Proof Using "Type*".

Section basic.
  (** * Correctness of bounded and unbounded rejection samplers using error credits instead of Löb induction *)
  (** The samplers in this section simulate (rand #n') using (rand #m') samplers *)

  Local Open Scope R.
  Context `{!ub_clutchGS Σ}.

  (** Bounded sampler (fails after `depth` attempts) *)
  Definition bdd_rejection_sampler (n' m' : nat) : val :=
    λ: "depth",
      let: "do_sample" :=
        (rec: "f" "tries_left" :=
           if: ("tries_left" - #1) < #0
            then NONE
            else let: "next_sample" := (rand #m') in
                if: ("next_sample" ≤ #n')
                then SOME "next_sample"
                else "f" ("tries_left" - #1))
      in "do_sample" "depth".


  (** Unbounded sampler (may not terminate) *)
  Definition ubdd_rejection_sampler (n' m' : nat) : val :=
    λ: "_",
      let: "do_sample" :=
        (rec: "f" "_" :=
           let: "next_sample" := (rand #m') in
           if: ("next_sample" ≤ #n')
            then SOME "next_sample"
            else "f" #())
      in "do_sample" #().




  (** general case for the bounded sampler *)
  Definition bdd_approx_safe (n' m' depth : nat) (Hnm : (S n' < S m')%nat) E :
    {{{ € (bdd_cf_error (S n') (S m') (S depth) Hnm) }}} bdd_rejection_sampler n' m' #(S depth)@ E {{{ v, RET v ; ⌜exists v' : nat, v = SOMEV #v' /\ (v' < S n')%nat⌝ }}}.
  Proof.
 iIntros (Φ) "Hcr HΦ"; rewrite /bdd_rejection_sampler.
    assert (Hnm' : (n' < m')%nat) by lia.
    do 4 wp_pure.
    (* Induction will reach the base cse when S depth = 1 <=> depth = 0 *)
    iInduction depth as [|depth' Hdepth'] "IH".
    - wp_pures.
      wp_apply (wp_rand_err_list_nat _ m' (seq (S n') ((S m') - (S n')))).
      iSplitL "Hcr".
      + iApply (ec_spend_irrel with "[$]").
        Opaque INR.
        rewrite /= Rmult_1_r.
        rewrite seq_length; apply Rmult_eq_compat_l.
        do 2 f_equal; lia.
      + iIntros (sample'') "%Hsample''".
        wp_pures.
        case_bool_decide; wp_pures.
        * iApply "HΦ"; iModIntro; iPureIntro; eexists _; split; [auto|lia].
        * exfalso.
          rewrite List.Forall_forall in Hsample''.
          rewrite /not in Hsample''.
          eapply Hsample''; last reflexivity.
          rewrite in_seq.
          split; first lia.
          replace (S n' + (S m' - S n'))%nat with (S m') by lia.
          apply fin_to_nat_lt.
    - wp_pures.
      replace (bool_decide _) with false; last (symmetry; apply bool_decide_eq_false; lia).
      wp_pures.
      wp_apply (wp_couple_rand_adv_comp _ _ _ _ (bdd_cf_sampling_error (S n') _ _) with "Hcr").
      { exists 1. intros s. apply sample_err_wf; try lia. }
      { by apply sample_err_mean. }
      iIntros (sample') "Hcr".
      wp_pures.
      case_bool_decide.
      + wp_pures; iApply "HΦ"; iModIntro; iPureIntro; exists (fin_to_nat sample'); split; [auto|lia].
      + wp_pure.
        rewrite (simplify_amp_err (S n') (S m') _); last (apply Nat.ltb_nlt; by lia); try lia.
        wp_bind (#_ - #_)%E; wp_pure.
        replace (S (S depth') - 1)%Z with (Z.of_nat (S depth')) by lia.
        wp_apply ("IH" with "Hcr HΦ").
  Qed.



  (** (approximate) safety of the unbounded rejection sampler *)
  Definition ubdd_approx_safe (n' m' depth : nat) Hnm E :
    {{{ € (bdd_cf_error (S n') (S m') (S depth) Hnm) }}}
      ubdd_rejection_sampler n' m' #() @ E
    {{{ v, RET v ; ⌜exists v' : nat, v = SOMEV #v' /\ (v' < S n')%nat⌝  }}}.
  Proof.
    iIntros (Φ) "Hcr HΦ"; rewrite /ubdd_rejection_sampler.
    assert (Hnm' : (n' < m')%nat) by lia.
    do 4 wp_pure.

    iInduction depth as [|depth' Hdepth'] "IH".
    - wp_pures.
      wp_apply (wp_rand_err_list_nat _ _ (seq (S n') (S m' - S n'))).
      iSplitL "Hcr".
      + iApply (ec_spend_irrel with "[$]").
        rewrite /= Rmult_1_r.
        rewrite seq_length; apply Rmult_eq_compat_l.
        do 2 f_equal; lia.
      + iIntros (sample'') "%Hsample''".
        wp_pures.
        case_bool_decide; wp_pures.
        * iApply "HΦ"; iModIntro; iPureIntro; eexists _. split; [auto|lia].
        * exfalso.
          rewrite List.Forall_forall in Hsample''.
          specialize Hsample'' with (fin_to_nat sample'').
          apply Hsample''; last reflexivity.
          rewrite in_seq.
          split; first lia.
          replace (S n' + (S m'-S n'))%nat with (S m') by lia.
          specialize (fin_to_nat_lt sample''); by lia.
    - wp_pures.
      wp_apply (wp_couple_rand_adv_comp _ _ _ _ (bdd_cf_sampling_error (S n') _ _) with "Hcr").
      { eexists _. intros s. apply sample_err_wf; try lia. }
      { pose P := (sample_err_mean n' m' Hnm' (bdd_cf_error (S n') (S m') _ Hnm)). by eapply P. }
      iIntros (sample') "Hcr".
      wp_pures.
      case_bool_decide.
      + wp_pures. iApply "HΦ"; iModIntro; iPureIntro; exists (fin_to_nat sample'); split; [auto|lia].
      + wp_pure.
        rewrite simplify_amp_err; last (apply Nat.ltb_nlt; by lia); try lia.
        wp_apply ("IH" with "Hcr HΦ").
  Qed.


  (* FIXME: maybe use errror_limit' from below with ε/2 *)
  Lemma error_limit (r : nonnegreal) : (r < 1) -> forall ε : posreal, exists n : nat, r ^ (S n) < ε.
  Proof.
    intros Hr ε.
    assert (H1 : Lim_seq.is_lim_seq (fun n => (r ^ n)%R) (Rbar.Finite 0)).
    { eapply Lim_seq.is_lim_seq_geom.
      rewrite Rabs_pos_eq; auto.
      apply cond_nonneg.
    }
    rewrite /Lim_seq.is_lim_seq
            /Hierarchy.filterlim
            /Hierarchy.filter_le
            /Hierarchy.eventually
            /Hierarchy.filtermap
            in H1.
    destruct (H1 (fun e' : R => (e' <= ε)%R)); simpl.
    - rewrite /Hierarchy.locally.
      eexists _. intros.
      rewrite /Hierarchy.ball /Hierarchy.UniformSpace.ball /Hierarchy.R_UniformSpace /=
              /Hierarchy.AbsRing_ball Hierarchy.minus_zero_r /Hierarchy.abs /=
            in H.
      eapply Rle_trans; [eapply RRle_abs|].
      by apply Rlt_le.
    - exists x.
      apply (Rcomplements.Rle_mult_Rlt r); [apply cond_pos|lra|].
      rewrite Rmult_comm.
      apply Rmult_le_compat_r; [apply cond_nonneg|].
      auto.
  Qed.


  (** Improve the safety of the unbounded sampler to use any positive amount of error credit *)
  Theorem ubdd_cf_safety (n' m' : nat) ε E :
    (n' < m')%nat ->
    ⊢ {{{ €ε ∗ ⌜0 < ε ⌝ }}}
        ubdd_rejection_sampler n' m' #() @ E
      {{{ v, RET v ; ⌜exists v' : nat, v = SOMEV #v' /\ (v' < S n')%nat⌝ }}}.
  Proof.
    iIntros (? Φ) "!> (Hcr&%Hcrpos) HΦ".
    assert (Hef: (err_factor (S n') (S m')) < 1) by (apply err_factor_lt1; lia).
    destruct (error_limit (err_factor (S n') (S m')) Hef (mkposreal ε Hcrpos)) as [d].
    iApply ((ubdd_approx_safe _ _ d _) with "[Hcr] [HΦ]"); auto.
    iApply ec_weaken; last iAssumption.
    rewrite /bdd_cf_error /=; simpl in H.
    apply Rlt_le. done.
    Unshelve. by lia.
  Qed.

End basic.
