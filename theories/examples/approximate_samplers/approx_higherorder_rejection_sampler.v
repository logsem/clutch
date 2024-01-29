(** * Examples related to rejection samplers with a bounded number of attempts *)
From clutch.ub_logic Require Export ub_clutch ub_rules.
From clutch Require Export examples.approximate_samplers.approx_sampler_lib.
From Coquelicot Require Import Series.
Require Import Lra.


Section spec.
  Local Open Scope R.
  Context `{!ub_clutchGS Σ}.

  Definition sampling_scheme_spec (sampler checker : val) 𝜀factor 𝜀final E : iProp Σ
    := ((∀ 𝜀,
          {{{ € 𝜀 }}}
            ((Val sampler) #())%E @ E
          {{{ (v : val), RET v;
               ((WP ((Val checker) v) @ E {{ λ v', ⌜v' = #true ⌝ }}) ∨
               (∃ 𝜀', € 𝜀' ∗ ⌜𝜀 <= 𝜀' * 𝜀factor ⌝ ∗ (WP ((Val checker) v) @ E {{ λ v', ⌜v' = #true \/ v' = #false⌝ }})))}}}) ∗
        (∀ v : val,
          {{{ € 𝜀final }}}
            ((Val sampler) v) @ E
          {{{ (v' : val), RET v'; (WP ((Val checker) v') @ E {{ λ v', ⌜v' = #true ⌝ }})}}}))%I.

End spec.


Section accounting.
  (** Specification for general (stateful) bounded rejection samplers which makes use of
      Iris' higher order Hoare triples *)
  Local Open Scope R.
  Context `{!ub_clutchGS Σ}.


  Program Definition generic_geometric_error (r 𝜀final : nonnegreal) (depth : nat) : nonnegreal
    := (𝜀final * (mknonnegreal (r ^ depth) _))%NNR.
  Next Obligation. intros. apply pow_le. by destruct r. Qed.

  Lemma final_generic_geometric_error (r 𝜀final : nonnegreal) : (generic_geometric_error r 𝜀final 0%nat) = 𝜀final.
  Proof. apply nnreal_ext; by rewrite /generic_geometric_error /= Rmult_1_r. Qed.

  Lemma simpl_generic_geometric_error (r 𝜀final : nonnegreal) (depth : nat) :
    (not (eq (nonneg r) 0)) ->
    (nnreal_div (generic_geometric_error r 𝜀final (S depth)) r)%NNR = (generic_geometric_error r 𝜀final  depth).
  Proof.
    intros.
    rewrite /generic_geometric_error /nnreal_div /nnreal_mult.
    apply  nnreal_ext; simpl.
    rewrite Rmult_assoc;  apply Rmult_eq_compat_l.
    rewrite -Rmult_comm -Rmult_assoc Rinv_l; [lra|auto].
  Qed.

End accounting.


Section safety.
  Local Open Scope R.
  Context `{!ub_clutchGS Σ}.

  (* safety for higher-order bounded rejection samplers *)
  Lemma ho_bounded_approx_safe (sampler checker : val) (r εfinal : nonnegreal) (depth : nat) E :
    (0 < r < 1) ->
    (0 < εfinal < 1) ->
    sampling_scheme_spec sampler checker r εfinal E -∗
    € (generic_geometric_error r εfinal depth) -∗
    (WP (gen_bounded_rejection_sampler #(S depth) sampler checker) @ E {{ fun v => ∃ v', ⌜ v = SOMEV v' ⌝}})%I.
  Proof.
    (* initial setup *)
    rewrite /sampling_scheme_spec.
    iIntros ([Hr_pos Hr] [Hεfinal_pos Hεfinal]) "(#Hamplify&#Haccept) Hcr".
    rewrite /gen_bounded_rejection_sampler.
    do 9 wp_pure.
    iInduction depth as [|depth' Hdepth'] "IH".
    - wp_pures; wp_bind (sampler #())%E.
      wp_apply ("Haccept" with "[Hcr]").
      { iApply (ec_weaken with "Hcr"); rewrite /generic_geometric_error /=; lra. }
      iIntros (next_sample) "Hcheck_accept".
      wp_pures; wp_bind (checker next_sample)%E.
      iApply (ub_wp_wand with "Hcheck_accept").
      iIntros (?) "#->"; wp_pures.
      iModIntro; iExists next_sample; iFrame; auto.
    - wp_pures.
      replace (bool_decide _) with false; last (symmetry; apply bool_decide_eq_false; lia).
      wp_pures; wp_bind (sampler #())%E.
      iApply ("Hamplify" $! (generic_geometric_error r εfinal (S depth')) with "Hcr").
      iIntros (next_sample) "!> [Hcheck_accept|[%ε'(Hcr&%Hε'&Hcheck_reject)]]"; wp_pures.
      + wp_bind (checker next_sample)%V.
        iApply (ub_wp_wand with "Hcheck_accept").
        iIntros (?) "#->"; wp_pures.
        iModIntro; iExists next_sample; iFrame; auto.
      + wp_bind (checker next_sample)%V.
        iApply (ub_wp_wand with "Hcheck_reject").
        iIntros (?) "%Hresult".
        iSpecialize ("IH" with "[Hcr]").
        * iApply (ec_spend_le_irrel with "Hcr").
          rewrite /generic_geometric_error /=.
          apply (Rmult_le_reg_r r); auto.
          by rewrite /generic_geometric_error /=
                     (Rmult_comm r _) -Rmult_assoc in Hε'.
        * destruct Hresult as [-> | ->].
          { wp_pures; eauto. }
          { do 2 wp_pure.
            iClear "#".
            replace #((S (S depth')) - 1) with #(S depth'); [| do 2 f_equal; lia].
            iApply "IH". }
  Qed.


  (* safety for higher-order unbounded rejection samplers (almost the same proof) *)
  Lemma ho_ubdd_approx_safe (sampler checker : val) (r εfinal : nonnegreal) (depth : nat) E :
    (0 < r < 1) ->
    (0 < εfinal < 1) ->
    sampling_scheme_spec sampler checker r εfinal E -∗
    ▷ € (generic_geometric_error r εfinal depth) -∗
    (WP (gen_rejection_sampler sampler checker) @ E {{ fun v => ∃ v', ⌜ v = SOMEV v' ⌝}})%I.
  Proof.
    rewrite /sampling_scheme_spec.
    iIntros ([Hr_pos Hr] [Hεfinal_pos Hεfinal]) "(#Hamplify&#Haccept) Hcr".
    rewrite /gen_rejection_sampler.
    do 7 wp_pure.
    iInduction depth as [|depth' Hdepth'] "IH".
    - wp_pures; wp_bind (sampler #())%E.
      wp_apply ("Haccept" with "[Hcr]").
      { iApply (ec_weaken with "Hcr"); rewrite /generic_geometric_error /=; lra. }
      iIntros (next_sample) "Hcheck_accept".
      wp_pures; wp_bind (checker next_sample)%E.
      iApply (ub_wp_wand with "Hcheck_accept").
      iIntros (?) "#->"; wp_pures.
      iModIntro; iExists next_sample; iFrame; auto.
    - wp_pures.
      wp_pures; wp_bind (sampler #())%E.
      iApply ("Hamplify" $! (generic_geometric_error r εfinal (S depth')) with "Hcr").
      iIntros (next_sample) "!> [Hcheck_accept|[%ε'(Hcr&%Hε'&Hcheck_reject)]]"; wp_pures.
      + wp_bind (checker next_sample)%V.
        iApply (ub_wp_wand with "Hcheck_accept").
        iIntros (?) "#->"; wp_pures.
        iModIntro; iExists next_sample; iFrame; auto.
      + wp_bind (checker next_sample)%V.
        iApply (ub_wp_wand with "Hcheck_reject").
        iIntros (?) "%Hresult".
        iSpecialize ("IH" with "[Hcr]").
        * iApply (ec_spend_le_irrel with "Hcr").
          rewrite /generic_geometric_error /=.
          apply (Rmult_le_reg_r r); auto.
          by rewrite /generic_geometric_error /=
                     (Rmult_comm r _) -Rmult_assoc in Hε'.
        * destruct Hresult as [-> | ->].
          { wp_pures; eauto. }
          { wp_pure.
            iClear "#".
            replace #((S (S depth')) - 1) with #(S depth'); [| do 2 f_equal; lia].
            iApply "IH". }
  Qed.


  (** Limiting argument: any amount of credit suffices to show the unbounded sampler is safe *)
  Lemma ho_ubdd_safe (sampler checker : val) (r εfinal ε : nonnegreal) E :
    (0 < r < 1) ->
    (0 < εfinal < 1) ->
    0 < ε ->
    ⊢ sampling_scheme_spec sampler checker r εfinal E -∗
      €ε -∗
      WP gen_rejection_sampler sampler checker @ E {{ v, ∃ v', ⌜ v = SOMEV v' ⌝ }}.
  Proof.
    iIntros (? ? ?) "#Hspec Hcr".
    remember (/ NNRbar_to_real (NNRbar.Finite εfinal) * nonneg ε) as p.
    assert (Hp : (0 < p)).
    { rewrite Heqp.
      apply Rmult_lt_0_compat; try done.
      apply Rinv_0_lt_compat.
      by destruct H0. }
    assert (H' : r < 1); first by destruct H.
    destruct (error_limit' r H' (mkposreal p Hp)) as [depth Hlim].
    iApply (ho_ubdd_approx_safe _ _ _ _ depth);[|done|done|];[done|]. (* weird unification order *)
    iApply (ec_spend_le_irrel with "Hcr").
    rewrite /generic_geometric_error /=.
    apply (Rmult_le_reg_l (/ εfinal)).
    { apply Rinv_0_lt_compat; by destruct H0. }
    rewrite /= Heqp in Hlim.
    rewrite -Rmult_assoc Rinv_l; last lra.
    rewrite Rmult_1_l.
    by apply Rlt_le.
  Qed.
End safety.


Section higherorder_rand.
  (** Instantiation of the higher-order spec for a basic rejection sampler *)
  Local Open Scope R.
  Context `{!ub_clutchGS Σ}.

  Definition rand_ε2 (n' m' : nat) (ε1 : nonnegreal) : (fin (S m')) -> nonnegreal
    := fun z => if (bool_decide (z < S n')%nat)
                  then nnreal_zero
                  else (nnreal_div ε1 (err_factor (S n') (S m'))).


  Lemma sample_err_mean_higherorder n' m' (Hnm : (n' < m')%nat) 𝜀₁ :
    SeriesC (λ n : fin (S m'), (1 / S m') * rand_ε2 n' m' 𝜀₁ n) = 𝜀₁.
  Proof.
    rewrite /bdd_cf_sampling_error SeriesC_scal_l.
    apply (Rmult_eq_reg_l (S m')); last (apply not_0_INR; lia).
    rewrite Rmult_assoc -Rmult_assoc Rmult_1_r.
    rewrite -Rmult_assoc -Rinv_r_sym; last (apply not_0_INR; lia).
    rewrite Rmult_1_l.
    rewrite /rand_ε2.
    rewrite reindex_fin_series; try lia.
    rewrite /err_factor.
    Opaque INR.
    rewrite /= Rinv_mult Rinv_inv.
    rewrite -Rmult_assoc -Rmult_assoc Rmult_comm.
    apply Rmult_eq_compat_l.
    rewrite Rmult_comm -Rmult_assoc.
    rewrite -minus_INR; [|lia].
    rewrite Nat.sub_succ Rinv_l.
    - by rewrite Rmult_1_l.
    - apply not_0_INR; lia.
  Qed.

  Lemma rand_sampling_scheme_spec (n' m' : nat) (Hnm : (n' < m')%nat) E :
    ⊢ sampling_scheme_spec
          (λ: "_", rand #m')%V
          (λ: "sample", "sample" ≤ #n')%V
          (err_factor (S n') (S m'))
          (err_factor (S n') (S m'))
          E.
  Proof.
    Opaque INR.
    rewrite /sampling_scheme_spec.
    iStartProof; iSplit.
    - (* sampling rule *)
      iIntros (ε Φ) "!> Hcr HΦ"; wp_pures.
      iApply (wp_couple_rand_adv_comp  m' _ _ _ ε (rand_ε2 n' m' ε) _ with "Hcr").
      { (* uniform bound *)
        eexists (nnreal_div ε (err_factor (S n') (S m'))); intros s.
        rewrite /rand_ε2.
        case_bool_decide; simpl; [|lra].
        apply Rmult_le_pos.
        - by apply cond_nonneg.
        - apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat.
          + apply lt_0_INR. lia.
          + apply Rinv_0_lt_compat. apply lt_0_INR. lia.
      }

      { (* series convergence *)
        by apply sample_err_mean_higherorder. }

      iNext; iIntros (s) "Hcr".
      iApply "HΦ".
      destruct (le_gt_dec s n') as [|] eqn:Hdec; [iLeft | iRight].
      + (* the sample is inbounds, the checker should accept *)
        wp_pures; iModIntro; iPureIntro.
        do 2 f_equal; apply bool_decide_true; lia.
      + (* the sample is out of bounds *)
        iExists _; iSplitL; first iFrame.
        iSplit.
        * (* credit is amplified *)
          iPureIntro.
          rewrite /rand_ε2 bool_decide_eq_false_2; last first.
          { rewrite /not; intros; lia. }
          rewrite /nnreal_div Rmult_assoc /nnreal_inv; simpl.
          rewrite Rinv_l; [lra|].
          apply Rmult_integral_contrapositive; split.
          -- apply Rgt_not_eq, Rlt_gt, lt_0_INR; lia.
          -- apply Rinv_neq_0_compat.
             apply Rgt_not_eq, Rlt_gt, lt_0_INR; lia.
        * (* sampler rejects *)
          wp_pures; iModIntro; iPureIntro. right.
          do 2 f_equal; apply bool_decide_false; lia.

    - (* checking rule *)
      iIntros (s Φ) "!> Hcr HΦ"; wp_pures.
      wp_apply (wp_rand_err_list_nat _ m' (seq (S n') ((S m') - (S n')))).
      iSplitL "Hcr".
      + (* credit accounting *)
        iApply (ec_spend_irrel with "Hcr").
        rewrite /err_factor seq_length /=.
        apply Rmult_eq_compat_l.
        do 2 f_equal; lia.
      + iIntros (s') "%Hs'".
        iApply "HΦ"; wp_pures.
        iModIntro; iPureIntro.
        do 2 f_equal; apply bool_decide_true.
        rewrite List.Forall_forall in Hs'.
        specialize Hs' with s'.
        apply Znot_gt_le.
        intros Hcont; apply Hs'; last reflexivity.
        rewrite in_seq.
        split; first lia.
        replace (S n' + (S m' - S n'))%nat with (S m') by lia.
        specialize (fin_to_nat_lt s'); by lia.

    Unshelve.
    { apply Φ. }
    { rewrite Nat2Z.id; apply TCEq_refl. }
  Qed.

End higherorder_rand.




Section higherorder_flip2.
  (** Instantiation of the higher-order spec for a pair of coin flips *)
  Local Open Scope R.
  Context `{!ub_clutchGS Σ}.

  Definition ε2_flip2 (ε1 : nonnegreal) (v : fin (S 1%nat)) : nonnegreal :=
    if (fin_to_bool v)
      then nnreal_zero
      else (nnreal_nat(2%nat) * ε1)%NNR.

  Definition flip_is_1  (v : val): bool :=
    match v with
    | LitV (LitInt 1%Z) => true
    | _ => false
    end.

  Definition ε2_flip1 (ε1 εh εt : nonnegreal) (v : fin (S 1%nat)) : nonnegreal :=
    if (fin_to_bool v) then εh else εt.

  Definition scale_flip (ε1 εh εt : nonnegreal) : val -> nonnegreal
    := (fun z => if (flip_is_1 z) then εh else εt).

  Lemma flip_amplification (ε1 εh εt : nonnegreal) (Hmean : (εh + εt) = 2 * ε1 ) E :
    {{{ € ε1 }}}
      rand #1 @ E
    {{{ v, RET #v; ⌜(v = 0%nat) \/ (v = 1%nat) ⌝ ∗ € (scale_flip ε1 εh εt #v) }}}.
  Proof.
    iIntros (Φ) "Hcr HΦ".
    iApply (wp_couple_rand_adv_comp 1%nat  _ _ _ ε1 (ε2_flip1 ε1 εh εt) _ with "Hcr").
    - (* uniform bound *)
      exists (εh + εt)%NNR; intros n.
      rewrite /ε2_flip1.
      destruct (fin_to_bool n); destruct εt, εh; rewrite /bound /=; lra.
    - (* series mean *)
      rewrite SeriesC_finite_foldr /enum /fin_finite /fin_enum /ε2_flip1 /=.
      rewrite Rplus_0_r -Rmult_plus_distr_l Rplus_comm Hmean /=.
      lra.
    - (* continutation *)
      iNext. iIntros (n) "Hcr".
      iApply ("HΦ" $! (fin_to_nat n)); iSplitR.
      + iPureIntro; apply fin2_enum.
      + iApply (ec_spend_irrel with "Hcr"). rewrite /ε2_flip2.
        destruct (fin2_enum n) as [H|H].
        * rewrite /ε2_flip1 H /=.
          rewrite -fin2_nat_bool.
          replace (n =? 1)%nat with false; [done|].
          symmetry; apply Nat.eqb_neq; lia.
        * rewrite /ε2_flip1 H /=.
          rewrite -fin2_nat_bool.
          replace (n =? 1)%nat with true; [done|].
          symmetry; apply Nat.eqb_eq; lia.
      Unshelve.
      { apply Φ. }
      { apply TCEq_refl. }
  Qed.


  Lemma flip2_sampling_scheme_spec E :
    ⊢ sampling_scheme_spec
          (λ: "_", Pair (rand #1) (rand #1))
          (λ: "sample", (((Fst "sample") = #1) && ((Snd "sample") = #1)))
          (nnreal_div (nnreal_nat 3%nat) (nnreal_nat 4%nat))
          (nnreal_div (nnreal_nat 3%nat) (nnreal_nat 4%nat))
          E.
  Proof.
    rewrite /sampling_scheme_spec.
    iStartProof; iSplit.
    - (* amplification rule *)
      iIntros (𝜀 Φ) "!> Hcr HΦ"; wp_pures.
      wp_apply (flip_amplification 𝜀
                  (nnreal_mult 𝜀 (nnreal_div (nnreal_nat 2) (nnreal_nat 3)))
                  (nnreal_mult 𝜀 (nnreal_div (nnreal_nat 4) (nnreal_nat 3)))
                   with "Hcr"); [simpl; lra| ].
      iIntros (v) "(%Hv&Hcr)".
      destruct Hv as [-> | ->].
      + (* first flip was zero, check is going to false and the second flip doesn't matter. *)
        wp_bind (rand _)%E; iApply wp_rand; auto.
        iNext; iIntros (v') "_"; wp_pures; iModIntro; iApply "HΦ".
        iRight; iExists _.
        iSplitL "Hcr"; [iFrame|].
        iSplit.
        * (* credit accounting *)
          iPureIntro; simpl; lra.
        * (* step the checker *)
          wp_pures; case_bool_decide; wp_pures; auto.
      + (* first flip was 1, we only have 2/3 error so we need to amplify up to 4/3
            in the case that the second flip is not 1 *)
        replace (scale_flip 𝜀 _ _ _) with (𝜀 * nnreal_div (nnreal_nat 2) (nnreal_nat 3))%NNR; last first.
        { rewrite /scale_flip /flip_is_1 /=. by apply nnreal_ext. }
        remember (𝜀 * nnreal_div (nnreal_nat 2) (nnreal_nat 3))%NNR as 𝜀'.
        wp_bind (rand #1 )%E.
        wp_apply (flip_amplification 𝜀' nnreal_zero (nnreal_mult 𝜀' (nnreal_nat 2)) with "Hcr").
        { simpl. lra. }
        iIntros (v) "(%Hv&Hcr)".
        destruct Hv as [-> | ->].
        * (* second flip was zero *)
          wp_pures; iModIntro; iApply "HΦ".
          iRight; iExists _.
          iSplitL "Hcr"; [iFrame|].
          iSplit.
          -- (* credit accounting *)
            iPureIntro; rewrite Heq𝜀' /=; lra.
          -- (* step the checker *)
            wp_pures; auto.
        * (* both flips are 1, checker should accept *)
          wp_pures; iModIntro; iApply "HΦ".
          iLeft; wp_pures; auto.

    - (* credit spending rule *)
      iIntros (s Φ) "!> Hcr HΦ"; wp_pures.
      wp_bind (rand #1)%E.

      (* give € 1 to the 0 flip, and € 1/2 to the 1 flip *)
      wp_apply (flip_amplification
                  (nnreal_div (nnreal_nat 3) (nnreal_nat 4))
                  (nnreal_div (nnreal_nat 1) (nnreal_nat 2))
                  nnreal_one with "Hcr"); [simpl; lra|].
      iIntros (v') "(%Hv'&Hcr)".
      destruct Hv' as [-> | ->].
      + (* first flip is zero: but we can spend € 1 to conclude *)
        iApply (wp_ec_spend with "Hcr").
        * rewrite /scale_flip /flip_is_1 /=; lra.
        * rewrite /to_val; done.
      +  (* we have € 1/2 so we can make the second flip be 1 too *)
        wp_bind (rand #1)%E.
        iApply (wp_rand_err _ _ 0%fin with "[Hcr HΦ]").
        iSplitL "Hcr". { iApply (ec_spend_irrel with "Hcr"). rewrite /=; lra. }
        iIntros (v') "%Hv'".
        wp_pures; iModIntro; iApply "HΦ".
        wp_pures; case_bool_decide; wp_pures; auto.
        (* we have a contradiction in Hv' and H *)
        exfalso. apply fin2_not_0  in Hv'. apply H. rewrite Hv' /=. f_equal.
  Qed.
End higherorder_flip2.
