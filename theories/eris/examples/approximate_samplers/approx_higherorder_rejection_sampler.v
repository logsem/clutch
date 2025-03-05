(** * Examples related to rejection samplers with a bounded number of attempts *)
From clutch.eris Require Export eris error_rules.
From clutch.eris Require Export examples.approximate_samplers.approx_sampler_lib.
From Coquelicot Require Import Series.
Require Import Lra.


Section spec.
  Local Open Scope R.
  Context `{!erisGS Σ}.

  (* Spec for samplers which need to amplify some number of times, and then spend.
     In particular, this is a spec for bounded samplers. *)
  Definition bounded_sampling_scheme_spec (sampler checker : val) 𝜀factor 𝜀final E Θ : iProp Σ
    := ((∀ (𝜀 : nonnegreal),
          [[{ ↯ 𝜀 }]]
            ((Val sampler) #())%E @ E
          [[{ (v : val), RET v;
               ((WP ((Val checker) v) @ E [{ λ v', ⌜v' = #true ⌝ ∗ Θ v }]) ∨
               (∃ 𝜀', ↯ 𝜀' ∗ ⌜𝜀 <= 𝜀' * 𝜀factor ⌝ ∗ (WP ((Val checker) v) @ E [{ λ v', ⌜v' = #false⌝ ∨ (⌜v' = #true ⌝ ∗ Θ v)}])))}]]) ∗
        (∀ v : val,
          [[{ ↯ 𝜀final }]]
            ((Val sampler) v) @ E
          [[{ (v' : val), RET v'; (WP ((Val checker) v') @ E [{ λ v'', ⌜v'' = #true ⌝ ∗ Θ v' }])}]]))%I.

  (* Easier to explain spec.
     It is allowed to wait arbitrarily long before spending,
     and thus can wait to spend credit ↯1. *)
  Definition sampling_scheme_spec (sampler checker : val) (εfactor : nonnegreal) E Θ : iProp Σ
    := (∀ (ε : nonnegreal),           
       [[{ ↯ ε }]]
            ((Val sampler) #())%E @ E
       [[{ (v : val), RET v;
               ((WP ((Val checker) v) @ E [{ λ v', ⌜v' = #true ⌝ ∗ Θ v }]) ∨
               (∃ ε', ↯ ε' ∗ ⌜ε <= ε' * εfactor ⌝ ∗ (WP ((Val checker) v) @ E [{ λ v', ⌜v' = #false⌝ ∨ (⌜v' = #true ⌝ ∗ Θ v)}])))}]])%I.

  Definition unbounded_scheme_implies_bounded sampler checker (εfactor : nonnegreal) E Θ :
    ⊢ sampling_scheme_spec sampler checker εfactor E Θ -∗
      bounded_sampling_scheme_spec sampler checker εfactor nnreal_one E Θ.
  Proof.
    iIntros "?".
    iSplitL; iFrame.
    iIntros (? ?) "!> ?".
    iExFalso; iApply (ec_contradict with "[$]").
    simpl; lra.
  Qed.
End spec.


Section safety.
  Local Open Scope R.
  Context `{!erisGS Σ}.

  (* safety for higher-order bounded rejection samplers *)
  Lemma ho_bounded_approx_safe (sampler checker : val) (r εfinal : nonnegreal) (depth : nat) E Θ :
    (0 < r < 1) ->
    (0 < εfinal < 1) ->
    bounded_sampling_scheme_spec sampler checker r εfinal E Θ -∗
    ↯ (generic_geometric_error r εfinal depth) -∗
    (WP (gen_bounded_rejection_sampler #(S depth) sampler checker) @ E [{ fun v => Θ v }])%I.
  Proof.
    (* initial setup *)
    rewrite /sampling_scheme_spec.
    iIntros ([Hr_pos Hr] [Hεfinal_pos Hεfinal]) "(#Hamplify&#Haccept) Hcr".
    rewrite /gen_bounded_rejection_sampler.
    do 9 wp_pure.
    iInduction depth as [|depth' Hdepth'] "IH".
    - wp_pures; wp_bind (sampler #())%E.
      wp_apply ("Haccept" with "[Hcr]").
      { iApply (ec_weaken with "Hcr"). split; [lra|]. rewrite /generic_geometric_error /=; lra. }
      iIntros (next_sample) "Hcheck_accept".
      wp_pures; wp_bind (checker next_sample)%E.
      iApply (tgl_wp_wand with "Hcheck_accept").
      iIntros (?) "(#-> & ?)"; wp_pures.
      iModIntro; iFrame.
    - wp_pures.
      replace (bool_decide _) with false; last (symmetry; apply bool_decide_eq_false; lia).
      wp_pures; wp_bind (sampler #())%E.
      iApply ("Hamplify" $! (generic_geometric_error r εfinal (S depth')) with "Hcr").
      iIntros (next_sample) "[Hcheck_accept|[%ε'(Hcr&%Hε'&Hcheck_reject)]]"; wp_pures.
      + wp_bind (checker next_sample)%V.
        iApply (tgl_wp_wand with "Hcheck_accept").
        iIntros (?) "(#-> & ?)"; wp_pures.
        iModIntro; iFrame.
      + wp_bind (checker next_sample)%V.
        iApply (tgl_wp_wand with "Hcheck_reject").
        iIntros (?) "Hresult".
        iSpecialize ("IH" with "[Hcr]").
        * iApply (ec_weaken with "Hcr").
          rewrite /generic_geometric_error /=.
          split.
          { real_solver. }
          
          apply (Rmult_le_reg_r r); auto.
          by rewrite /generic_geometric_error /=
                     (Rmult_comm r _) -Rmult_assoc in Hε'.
        * iDestruct "Hresult" as "[-> | (-> & ?)]".
          { do 2 wp_pure.
            iClear "#".
            replace #((S (S depth')) - 1) with #(S depth'); [| do 2 f_equal; lia].
            iApply "IH". }
          { wp_pures; eauto. }
  Qed.


  (* safety for higher-order unbounded rejection samplers *)
  Lemma ho_ubdd_approx_safe (sampler checker : val) (r : nonnegreal) (depth : nat) E Θ :
    (0 < r < 1) ->
    sampling_scheme_spec sampler checker r E Θ -∗
    ↯ (generic_geometric_error r nnreal_one depth) -∗
    (WP (gen_rejection_sampler sampler checker) @ E [{ fun v => Θ v }])%I.
  Proof.
    rewrite /sampling_scheme_spec.
    iIntros ([Hr_pos Hr]) "#Hamplify Hcr".
    rewrite /gen_rejection_sampler.
    do 7 wp_pure.
    iInduction depth as [|depth' Hdepth'] "IH".
    - wp_pures; wp_bind (sampler #())%E.
      iExFalso; iApply (ec_contradict with "[$]").
      rewrite /generic_geometric_error /=; lra.
    - wp_pures.
      wp_pures; wp_bind (sampler #())%E.
      iApply ("Hamplify" $! (generic_geometric_error r nnreal_one (S depth')) with "Hcr").
      iIntros (next_sample) "[Hcheck_accept|[%ε'(Hcr&%Hε'&Hcheck_reject)]]"; wp_pures.
      + wp_bind (checker next_sample)%V.
        iApply (tgl_wp_wand with "Hcheck_accept").
        iIntros (?) "(#-> & ?)"; wp_pures.
        iModIntro; iFrame.
      + wp_bind (checker next_sample)%V.
        iApply (tgl_wp_wand with "Hcheck_reject").
        iIntros (?) "Hresult".
        iSpecialize ("IH" with "[Hcr]").
        * iApply (ec_weaken with "Hcr").
          rewrite /generic_geometric_error /=.
          split; [real_solver|]. 
          apply (Rmult_le_reg_r r); auto.
          by rewrite /generic_geometric_error /=
                     (Rmult_comm r _) -Rmult_assoc in Hε'.
        * iDestruct "Hresult" as "[-> | (-> & ?)]".
          { wp_pure.
            iClear "#".
            replace #((S (S depth')) - 1) with #(S depth'); [| do 2 f_equal; lia].
            iApply "IH". }
          { wp_pures; eauto. }
  Qed.


  (** Limiting argument: any amount of credit suffices to show the unbounded sampler is safe *)
  Lemma ho_ubdd_safe (sampler checker : val) (r ε : nonnegreal) E Θ :
    (0 < r < 1) ->
    0 < ε ->
    ⊢ sampling_scheme_spec sampler checker r E Θ -∗
      ↯ε -∗
      WP gen_rejection_sampler sampler checker @ E [{ v, Θ v }].
  Proof.
    iIntros ([? Hr] Hε) "#Hspec Hcr".
    rewrite /generic_geometric_error /=.
    destruct (error_limit' r Hr (mkposreal (nonneg ε) Hε)) as [d Hlim].
    iApply (ho_ubdd_approx_safe with "[]"); [eauto| iApply "Hspec" |].
    iApply (ec_weaken with "Hcr").
    rewrite /generic_geometric_error /= Rmult_1_l.
    split; last first. 
    - apply Rlt_le. simpl in Hlim; eauto.
    - real_solver. 
  Qed.
End safety.


Section higherorder_rand.
  (** Instantiation of the higher-order spec for a basic rejection sampler *)
  Local Open Scope R.
  Context `{!erisGS Σ}.

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

  Definition rand_sampling_scheme_goal (n' : nat) (v : val) : iProp Σ := ∃ (n : nat), ⌜v = #n /\ (n <= n')%nat⌝.

  Lemma rand_sampling_scheme_spec (n' m' : nat) (Hnm : (n' < m')%nat) E :
    ⊢ sampling_scheme_spec
          (λ: "_", rand #m')%V
          (λ: "sample", "sample" ≤ #n')%V
          (err_factor (S n') (S m'))
          E
          (rand_sampling_scheme_goal n').
  Proof.
    Opaque INR.
    rewrite /sampling_scheme_spec.
    iStartProof.
    iIntros (ε Φ) "!> Hcr HΦ"; wp_pures.
    iApply (twp_couple_rand_adv_comp1 m' _ _ ε (rand_ε2 n' m' ε) _ with "Hcr").
    { intros; apply cond_nonneg. }
    { by apply sample_err_mean_higherorder. }
    iIntros (s) "Hcr".
    iApply "HΦ".
    destruct (le_gt_dec s n') as [|] eqn:Hdec; [iLeft | iRight].
    + (* the sample is inbounds, the checker should accept *)
      wp_pures; iModIntro; iPureIntro.
      split.
      { do 2 f_equal; apply bool_decide_true; lia. }
      { eexists _. split; [by f_equal|done]. }
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
        wp_pures; iModIntro; iPureIntro. left.
        { do 2 f_equal; apply bool_decide_false; lia. }
    Unshelve.
    { rewrite Nat2Z.id; apply TCEq_refl. }
  Qed.

End higherorder_rand.


Section higherorder_flip2.
  (** Instantiation of the higher-order spec for a pair of coin flips *)
  Local Open Scope R.
  Context `{!erisGS Σ}.

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
    [[{ ↯ ε1 }]]
      rand #1 @ E
    [[{ v, RET #v; ⌜(v = 0%nat) \/ (v = 1%nat) ⌝ ∗ ↯ (scale_flip ε1 εh εt #v) }]].
  Proof.
    iIntros (Φ) "Hcr HΦ".
    iApply (twp_couple_rand_adv_comp1 1%nat  _ _ ε1 (ε2_flip1 ε1 εh εt) _ with "Hcr").
    - intros; apply cond_nonneg.
    - (* series mean *)
      rewrite SeriesC_finite_foldr /enum /fin_finite /fin_enum /ε2_flip1 /=.
      rewrite Rplus_0_r -Rmult_plus_distr_l Rplus_comm Hmean /=.
      lra.
    - (* continutation *)
      iIntros (n) "Hcr".
      iApply ("HΦ" $! _); iSplitR.
      + iPureIntro.
        inv_fin n; first (left; done).
        intros i; inv_fin i; first (right; done).
        intros k. by apply Fin.case0.
      + iApply (ec_eq with "Hcr"). rewrite /ε2_flip1 /scale_flip.
        inv_fin n; first by rewrite /ε2_flip1 /=.
        intros n; inv_fin n; first by rewrite /ε2_flip1 /=.
        intros n; by apply Fin.case0.
      Unshelve.
      { apply TCEq_refl. }
  Qed.

  Definition flip2_goal (v : val) : iProp Σ := ⌜v = (#1%nat, #1%nat)%V⌝.

  Lemma flip2_sampling_scheme_spec E :
    ⊢ sampling_scheme_spec
          (λ: "_", Pair (rand #1) (rand #1))
          (λ: "sample", (((Fst "sample") = #1) && ((Snd "sample") = #1)))
          (nnreal_div (nnreal_nat 3%nat) (nnreal_nat 4%nat))
          E
          flip2_goal.
  Proof.
    rewrite /sampling_scheme_spec.
    iStartProof.
    iIntros (𝜀 Φ) "!> Hcr HΦ"; wp_pures.
    wp_apply (flip_amplification 𝜀
                (nnreal_mult 𝜀 (nnreal_div (nnreal_nat 2) (nnreal_nat 3)))
                (nnreal_mult 𝜀 (nnreal_div (nnreal_nat 4) (nnreal_nat 3)))
                 with "Hcr"); [simpl; lra| ].
    iIntros (v) "(%Hv&Hcr)".
    destruct Hv as [-> | ->].
    + (* first flip was zero, check is going to false and the second flip doesn't matter. *)
      wp_bind (rand _)%E; iApply twp_rand; auto.
      iIntros (v') "_"; wp_pures; iModIntro; iApply "HΦ".
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
  Qed.
End higherorder_flip2.
