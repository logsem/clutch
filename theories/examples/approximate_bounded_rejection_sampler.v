From clutch.app_rel_logic Require Export app_weakestpre primitive_laws.
From clutch.ub_logic Require Export ub_clutch.
From Coquelicot Require Import Series.
Require Import Lra.

Set Default Proof Using "Type*".

Section basic.
  Local Open Scope R.
  Context `{!clutchGS Σ}.

  (* In general:
      S n' = n
      S m' = m
     This notation simplifies the proofs. *)


  (** PROGRAMS *)

  (** rejection sampler which takes a preset number of attempts *)
  Definition bdd_rejection_sampler (n' m' : nat) : val :=
    λ: "depth",
      let: "do_sample" :=
        (rec: "f" "tries_left" :=
           if: ("tries_left" - #1) < #0
            then NONE
            else let: "next_sample" := (rand #m' from #()) in
                if: ("next_sample" ≤ #n')
                then SOME "next_sample"
                else "f" ("tries_left" - #1))
      in "do_sample" "depth".


  (** rejection sampler that may take an unbounded number of attempts *)
  Definition ubdd_rejection_sampler (n' m' : nat) : val :=
    λ: "_",
      let: "do_sample" :=
        (rec: "f" "_" :=
           let: "next_sample" := (rand #m' from #()) in
           if: ("next_sample" ≤ #n')
            then SOME "next_sample"
            else "f" #())
      in "do_sample" #().





  (** PROBLEM 0: show that the unbounded sampler only returns inbounds values *)
  Definition ubdd_sampler_safe (n' m' : nat) E :
    {{{ True }}} ubdd_rejection_sampler  n' m' #() @ E {{{ v, RET v ; ⌜exists v' : nat, v = SOMEV #v' /\ (v' < S n')%nat⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /ubdd_rejection_sampler.
    do 4 wp_pure.
    iLöb as "IH"; wp_pures.
    (* this is a regular lob induction proof, it does not use error credits *)
    wp_apply wp_rand; [done|]; iIntros (n0) "_".
    wp_pures.
    case_bool_decide; last first.
    - wp_pure; by wp_apply ("IH" with "HΦ").
    - wp_pures; iApply "HΦ"; iModIntro; iPureIntro.
      exists (fin_to_nat n0); split; [auto|lia].
  Qed.




  (** PROBLEM 1: show the bounded sampler terminates inbounds with some error *)

  (** defining error values for each step *)

  Definition err_factor n m := (nnreal_div (nnreal_nat (m - n)%nat) (nnreal_nat m%nat)).

  Lemma err_factor_lt1 n m (Hn : (0 < n)%nat) (Hnm : (n < m)%nat) : err_factor n m < 1.
  Proof.
    rewrite /err_factor.
    simpl. apply Rcomplements.Rlt_div_l.
    - apply Rlt_gt; apply lt_0_INR; by lia.
    - rewrite Rmult_1_l; apply lt_INR; by lia.
  Qed.


  Lemma err_factor_nz_R n m (Hnm : (n < m)%nat) : (m - n)%nat * / m ≠ 0.
  Proof.
    intros.
    rewrite /not; intros HR; apply Rmult_integral in HR; destruct HR as [HRL|HRR].
    * rewrite minus_INR in HRL; last lia.
      apply Rminus_diag_uniq_sym in HRL.
      apply INR_eq in HRL.
      lia.
    * assert (K : not (eq (INR m) 0)).
      { apply not_0_INR; apply PeanoNat.Nat.neq_0_lt_0; lia. }
      by apply (Rinv_neq_0_compat (INR m) K).
  Qed.

  Lemma err_factor_nz n m (Hnm : (n < m)%nat) : err_factor n m ≠ nnreal_zero.
  Proof.
    rewrite /err_factor.
    rewrite /not; intros H; inversion H.
    by apply (err_factor_nz_R n m Hnm).
  Qed.


  (* error for the bounded sampler with a given number of tries remaining *)
  Program Definition bdd_cf_error n m depth (Hnm : (n < m)%nat) := mknonnegreal ((err_factor n m) ^ depth) _.
  Next Obligation.
    intros.
    apply pow_le; rewrite /err_factor /=.
    apply Rle_mult_inv_pos.
    - apply pos_INR.
    - apply lt_0_INR; lia.
  Qed.

  (* this lemma is for proofs which iterate to the very end
     ie, doing 0 samples requires error tolerance of 1 *)
  Lemma bdd_cd_error_final n m (Hnm : (n < m)%nat) : bdd_cf_error n m 0 Hnm = nnreal_one.
  Proof. by apply nnreal_ext; simpl. Qed.

  (* this lemma is for proofs which iterate up until the last sample
     ie, a rejection sampler to exclude the final recursive step *)
  (* proof irrelevant *)
  Lemma bdd_cd_error_penultimate n m (Hnm : (n < m)%nat) : bdd_cf_error n m 1 Hnm = err_factor n m.
  Proof. apply nnreal_ext; simpl; apply Rmult_1_r. Qed.


  (* distribution of error mass 𝜀₁ for a given sample:
      - zero error given to cases which are inbounds
      - uniform error to the recursive case *)
  Definition bdd_cf_sampling_error n m 𝜀₁ : (fin m) -> nonnegreal
    := fun sample =>
         if bool_decide (sample < n)%nat
            then nnreal_zero
            else (nnreal_div 𝜀₁ (err_factor n m)).

  (* lemma for simplifying accumulated error in the recursive case *)
  Lemma simplify_accum_err (n m d': nat) (Hnm : (n < m)%nat) (s : fin m)  :
    (s <? n)%nat = false -> bdd_cf_sampling_error n m (bdd_cf_error n m (S d') Hnm) s = (bdd_cf_error n m d' Hnm).
  Proof.
    intros Hcase.
    apply nnreal_ext.
    rewrite /bdd_cf_sampling_error.
    rewrite bool_decide_false; last by apply Nat.ltb_nlt.
    rewrite /bdd_cf_error /=.
    apply Rinv_r_simpl_m.
    by apply err_factor_nz_R.
  Qed.


  Lemma factor_lt_1 n m (Hnm : (n < m)%nat) (Hn : (0 < n)%nat): ((m - n)%nat  * / m) < 1.
  Proof.
    apply (Rmult_lt_reg_l m); first (apply lt_0_INR; lia).
    rewrite Rmult_1_r.
    replace (m * (INR ((m-n)%nat) * / m)) with (INR (m-n)%nat); last first.
    - rewrite Rmult_comm.
      rewrite Rmult_assoc.
      replace (/m * m) with 1; last by (symmetry; apply Rinv_l; apply not_0_INR; lia).
      symmetry; apply Rmult_1_r.
    - apply lt_INR. lia.
  Qed.


  (* error distribution is well-formed for each possible sample *)
  Lemma sample_err_wf n m d (s : fin m) (Hn : (0 < n)%nat) (Hnm : (n < m)%nat) : bdd_cf_sampling_error n m (bdd_cf_error n m (S d) Hnm) s <= 1.
  Proof.
    (* it is either 1, or epsilon times something at most 1 *)
    rewrite /bdd_cf_sampling_error.
    remember (s <? n)%nat as H.
    destruct H; simpl.
    - rewrite bool_decide_true; last by apply Nat.ltb_lt.
      by apply Rle_0_1.
    - rewrite bool_decide_false; last by apply Nat.ltb_nlt.
      rewrite /nnreal_div /=.
      rewrite -> Rinv_r_simpl_m.
      + destruct d as [|d'].
        * simpl; apply Rge_refl.
        * apply Rlt_le.
          apply pow_lt_1_compat; try lia; split.
          -- apply Rle_mult_inv_pos; [ apply pos_INR | apply lt_0_INR; lia ].
          -- apply factor_lt_1; auto.
      + apply err_factor_nz_R; auto.
  Qed.

  (* generalization of Coq.Logic.FinFun *)
  Definition f_lift_fin_nat {A} (N : nat) (a : A) (f : fin N -> A) : (nat -> A) :=
    fun n =>
      match le_lt_dec N n with
      | left _ => a
      | right h => f (Fin.of_nat_lt h)
      end.


  (* uses proof irrelevance *)
  Lemma f_lift_fin_nat_ltN {A} (n N: nat) (a : A) (Hn : (n < N)%nat) f :
    (f_lift_fin_nat N a f) n = f (nat_to_fin Hn).
  Proof.
    rewrite /f_lift_fin_nat.
    destruct (le_lt_dec N n) as [Hl|Hr].
    - lia.
    - f_equal; f_equal.
      apply proof_irrelevance.
  Qed.


  Lemma f_lift_fin_nat_geN {A} (N n: nat) (a : A) (Hn : not (n < N)%nat) f :
    (f_lift_fin_nat N a f) n = a.
  Proof.
    rewrite /f_lift_fin_nat.
    destruct (le_lt_dec N n); [done | lia].
  Qed.


  Lemma encode_inv_nat_nat_total (n : nat) : (@encode_inv_nat nat _ _ n)  = Some n.
  Proof.
    rewrite -encode_inv_encode_nat.
    f_equal.
    rewrite /encode_nat.
    rewrite /encode /nat_countable.
    destruct n; try done.
    rewrite /= /encode /N_countable /= -SuccNat2Pos.inj_succ.
    symmetry; apply SuccNat2Pos.pred_id.
  Qed.


  Lemma series_incr_N_zero f N :
    (forall m : nat, (m < N)%nat -> f m = 0) -> SeriesC (fun n : nat => f n) = SeriesC (fun n : nat => f (N + n)%nat).
  Proof.
    intros Hinit.
    rewrite /SeriesC /Series.
    rewrite -(Lim_seq.Lim_seq_incr_n (λ n : nat, @Hierarchy.sum_n Hierarchy.R_AbelianGroup _ _) N).
    f_equal; apply Lim_seq.Lim_seq_ext; intros n.
    rewrite /Hierarchy.sum_n.
    replace (@Hierarchy.sum_n_m Hierarchy.R_AbelianGroup (countable_sum (λ n0 : nat, f n0)) 0 (n + N))
      with (@Hierarchy.sum_n_m Hierarchy.R_AbelianGroup (countable_sum (λ n0 : nat, f n0)) N (n + N));
      last first.
    { destruct N as [|N']; first by simpl.
      rewrite (Hierarchy.sum_n_m_Chasles _ 0%nat N' (n + S N')%nat); try lia.
      replace  (@Hierarchy.sum_n_m Hierarchy.R_AbelianGroup (countable_sum (λ n0 : nat, f n0)) 0 N')
          with (@Hierarchy.zero Hierarchy.R_AbelianGroup).
      - by rewrite Hierarchy.plus_zero_l.
      - replace (@Hierarchy.sum_n_m  Hierarchy.R_AbelianGroup (countable_sum (λ n0 : nat, f n0)) 0 N')
          with  (@Hierarchy.sum_n_m  Hierarchy.R_AbelianGroup (λ n0 : nat, 0) 0 N').
          { rewrite (Hierarchy.sum_n_m_const _ _ 0); rewrite Rmult_0_r; auto. }
            apply Hierarchy.sum_n_m_ext_loc.
            intros K Hk.
            rewrite /countable_sum.
            (* I can simplify this with some of my lemmas now? *)
            rewrite encode_inv_nat_nat_total /=.
            symmetry; apply Hinit.
            lia. }

    induction n as [| n' IH].
    - simpl.
      do 2 (rewrite Hierarchy.sum_n_n).
      (* now we do the song and dance to evaluate the countable_sum at a value again *)
      rewrite /countable_sum encode_inv_nat_nat_total /=.
      replace (N + 0)%nat with N%nat by lia.
      reflexivity.
    - simpl.
      do 2 (rewrite Hierarchy.sum_n_Sm; last by lia).
      f_equal; first by apply IH.
      do 2 (rewrite /countable_sum encode_inv_nat_nat_total /=).
      f_equal; lia.
  Qed.

  Lemma encode_inv_nat_fin_undef (n N: nat) (H : not (n < N)%nat) : (@encode_inv_nat (fin N) _ _ n) = None.
  Proof.
    apply encode_inv_decode_ge.
    rewrite fin_card.
    lia.
  Qed.

  Lemma encode_inv_nat_fin_total (n N: nat) (H : (n < N)%nat) : (@encode_inv_nat (fin N) _ _ n) = Some (nat_to_fin H).
  Proof.
    assert (G : (n < card $ fin N)%nat).
    { rewrite fin_card. lia. }
    destruct (encode_inv_decode n G) as [y [Hy1 Hy2]]; simpl.

    rewrite Hy1; f_equal.
    symmetry.

    Set Printing Coercions.

    Check  (encode_inv_nat_some_inj _ y _ Hy1).
    (* there has to be a better way to prove this than unfolding the definitions one by one,
       unfortunately I think it is necessary.
     *)
  Admitted.

  Lemma reindex_fin_series M z K (Hnm : ((S z) < M)%nat):
    SeriesC (fun x : fin M => nonneg (if bool_decide (x < (S z))%nat then nnreal_zero else K)) = SeriesC (fun x : fin (M-(S z)) => nonneg K).
  Proof.
    remember (S z) as N.
    (* try to do the same induction dance as the reindexing part of the above lemma *)
    rewrite /SeriesC /Series.
    f_equal.
    (* after we increment the top sum by N, they are pointwise equal *)
    rewrite -(Lim_seq.Lim_seq_incr_n (λ n : nat, @Hierarchy.sum_n Hierarchy.R_AbelianGroup _ _) N).
    apply Lim_seq.Lim_seq_ext; intros n.

    (* rewrite to a two-ended sum, and compute the first N terms to be zero like above *)

    induction n as [| n' IH].
    - (* split the sum into the zero part, and the singular term of value K *)
      rewrite /= HeqN Hierarchy.sum_Sn -HeqN.

      (* now we can evaluate the first handful of terms to be zero *)

      rewrite Hierarchy.sum_O.
      remember (fun x : fin M => nonneg $ if bool_decide (x < N)%nat then nnreal_zero else K) as body.
      remember (fun _ : fin M => nnreal_zero) as body1.
      replace
        (@Hierarchy.sum_n Hierarchy.R_AbelianGroup (countable_sum body) z)
      with
        (@Hierarchy.sum_n Hierarchy.R_AbelianGroup (countable_sum body1) z);
      last first.
      { apply Hierarchy.sum_n_ext_loc.
        intros n Hn.
        rewrite /countable_sum.
        rewrite encode_inv_nat_fin_total; first lia.
        intros Hn1.
        rewrite /= Heqbody1 Heqbody HeqN fin_to_nat_to_fin /=.
        rewrite bool_decide_true; first done.
        lia. }

      (* now we can replace the countable sum with a constant zero function (TODO: make me a lemma)*)
      rewrite Heqbody1.
      replace
        (@countable_sum (Fin.t M) (@fin_dec M) (@finite_countable (Fin.t M) (@fin_dec M) (fin_finite M))
          (fun _ : Fin.t M => nonneg nnreal_zero))
      with (fun _ : nat => 0); last first.
      { apply functional_extensionality.
        intros x; rewrite /countable_sum.
        destruct (encode_inv_nat x) as [t|]; by simpl. }

      (* now the two series are both constant zero, we cam simplify *)
      rewrite Hierarchy.sum_n_const Rmult_0_r.
      rewrite /countable_sum.

      do 2 (rewrite encode_inv_nat_fin_total; try lia).
      intros H''.
      rewrite /= Heqbody fin_to_nat_to_fin /=.
      rewrite bool_decide_false; try lia.
      rewrite Hierarchy.plus_zero_l.
      done.
    - simpl.
      rewrite Hierarchy.sum_Sn.
      rewrite Hierarchy.sum_Sn.
      f_equal; first by apply IH.
      remember (bool_decide (S n' < (M - N))%nat) as HCond1.
      case_bool_decide.
      + rewrite {2}/countable_sum.
        rewrite encode_inv_nat_fin_total.
        simpl.
        rewrite /countable_sum.
        rewrite encode_inv_nat_fin_total; try lia.
        intros H''.
        remember (nat_to_fin H'') as D.
        simpl.
        rewrite bool_decide_false; first done.
        rewrite HeqD.
        rewrite fin_to_nat_to_fin.
        lia.
      + rewrite /countable_sum.
        rewrite encode_inv_nat_fin_undef; last lia.
        rewrite encode_inv_nat_fin_undef; last auto.
        done.
  Qed.

  (* mean of error distribution is preserved *)
  Lemma sample_err_mean n' m' (Hnm : (n' < m')%nat) 𝜀₁ :
    SeriesC (λ s : fin (S m'), (1 / S m') * bdd_cf_sampling_error (S n') (S m') 𝜀₁ s) = 𝜀₁.
  Proof.
    (* annoying: pull out the constant factor to leave a bare SeriesC on the left. I guess it's not necessary. *)
    rewrite /bdd_cf_sampling_error SeriesC_scal_l.
    apply (Rmult_eq_reg_l (S m')); last (apply not_0_INR; lia).
    rewrite Rmult_assoc -Rmult_assoc Rmult_1_r.
    assert (X : forall A B C, (Rmult A (Rmult B C)) = (Rmult (Rmult A B) C)).
    { intros. by rewrite Rmult_assoc. }
    rewrite X -Rinv_r_sym; last (apply not_0_INR; lia).
    rewrite Rmult_1_l.
    rewrite reindex_fin_series SeriesC_finite_mass fin_card.
    rewrite /err_factor.
    remember (S m' - S n')%nat as D.
    remember (S m') as M.
    rewrite /= Rinv_mult Rinv_inv.
    rewrite -Rmult_assoc -Rmult_assoc Rmult_comm.
    apply Rmult_eq_compat_l.
    rewrite Rmult_comm -Rmult_assoc Rinv_l.
    - by rewrite Rmult_1_l.
    - rewrite HeqD HeqM.
      apply not_0_INR.
      lia.
  Qed.



  (** warmup: a finite example *)
  Definition bdd_approx_safe_finite_example (n' m' depth : nat) (Hnm : (S n' < S m')%nat) E :
    (depth = 3%nat) ->
    {{{ € (bdd_cf_error (S n') (S m') depth Hnm) }}} bdd_rejection_sampler n' m' #(S depth) @ E {{{ v, RET v ; ⌜exists v' : nat, v = SOMEV #v' /\ (v' < S n')%nat⌝ }}}.
  Proof.
    iIntros (-> Φ) "Hcr HΦ"; rewrite /bdd_rejection_sampler.
    assert (Hnm' : (n' < m')%nat) by lia.
    wp_pures.

    (* S depth=3 sample *)
    wp_apply (wp_couple_rand_adv_comp _ _ _ Φ _ (bdd_cf_sampling_error (S n') _ _) with "Hcr").
    { intros s. apply sample_err_wf; try lia. }
    { pose P := (sample_err_mean n' m' Hnm' (bdd_cf_error (S n') (S m') 3 Hnm)); apply P. }
    iIntros (sample) "Hcr".
    wp_pures.
    case_bool_decide; wp_pures.
    { iApply "HΦ"; iModIntro; iPureIntro; exists (fin_to_nat sample); split; [auto|lia]. }
    rewrite (simplify_accum_err (S n') (S m') _); last (apply Nat.ltb_nlt; by lia); try lia.

    (* S depth=2 sample *)
    wp_apply (wp_couple_rand_adv_comp _ _ _ Φ _ (bdd_cf_sampling_error (S n') _ _) with "Hcr").
    { intros s. apply sample_err_wf; try lia. }
    { pose P := (sample_err_mean n' m' Hnm' (bdd_cf_error (S n') (S m') 2 Hnm)); apply P. }
    iIntros (sample') "Hcr".
    wp_pures.
    case_bool_decide; wp_pures.
    { iApply "HΦ"; iModIntro; iPureIntro; exists (fin_to_nat sample'); split; [auto|lia]. }
    rewrite (simplify_accum_err (S n') (S m') _); last (apply Nat.ltb_nlt; by lia); try lia.

    (* S depth=1 sample *)
    rewrite bdd_cd_error_penultimate.
    remember (S n') as n.
    remember (S m') as m.
    wp_apply (wp_rand_err_list_nat _ m' (seq n (m - n))).
    iSplitL "Hcr".
    - (* yeesh *)
      rewrite /err_factor.
      replace (length (seq _ _)) with (m - n)%nat by (symmetry; apply seq_length).
      replace (m) with (m' + 1)%nat by lia.
      done.
    - iIntros (sample'') "%Hsample''".
      wp_pures.
      case_bool_decide; wp_pures.
      + iApply "HΦ"; iModIntro; iPureIntro; exists (fin_to_nat sample''); split; [auto|lia].
      + exfalso.
        rewrite List.Forall_forall in Hsample''.
        specialize Hsample'' with sample''.
        apply Hsample''; last reflexivity.
        rewrite in_seq.
        split; first lia.
        replace (n + (m-n))%nat with m by lia.
        specialize (fin_to_nat_lt sample''); by lia.
  Qed.


  (** general case for the bounded sampler *)
  Definition bdd_approx_safe (n' m' depth : nat) (Hnm : (S n' < S m')%nat) E :
    {{{ € (bdd_cf_error (S n') (S m') (S depth) Hnm) }}} bdd_rejection_sampler n' m' #(S depth)@ E {{{ v, RET v ; ⌜exists v' : nat, v = SOMEV #v' /\ (v' < S n')%nat⌝ }}}.
  Proof.
    iIntros (Φ) "Hcr HΦ"; rewrite /bdd_rejection_sampler.
    assert (Hnm' : (n' < m')%nat) by lia.
    do 4 wp_pure.

    (* induction should reach the base cse when S depth = 1 <=> depth = 0 *)
    iInduction depth as [|depth' Hdepth'] "IH".
    - wp_pures.
      rewrite bdd_cd_error_penultimate.
      remember (S n') as n.
      remember (S m') as m.
      wp_apply (wp_rand_err_list_nat _ m' (seq n (m - n))).
      iSplitL "Hcr".
      + rewrite /err_factor.
        replace (length (seq _ _)) with (m - n)%nat by (symmetry; apply seq_length).
        replace (m) with (m' + 1)%nat by lia.
        done.
      + iIntros (sample'') "%Hsample''".
        wp_pures.
        case_bool_decide; wp_pures.
        * iApply "HΦ"; iModIntro; iPureIntro; exists (fin_to_nat sample''); split; [auto|lia].
        * exfalso.
          rewrite List.Forall_forall in Hsample''.
          specialize Hsample'' with sample''.
          apply Hsample''; last reflexivity.
          rewrite in_seq.
          split; first lia.
          replace (n + (m-n))%nat with m by lia.
          specialize (fin_to_nat_lt sample''); by lia.
    - wp_pures.
      replace (bool_decide _) with false; last (symmetry; apply bool_decide_eq_false; lia).
      wp_pures.
      wp_apply (wp_couple_rand_adv_comp _ _ _ Φ _ (bdd_cf_sampling_error (S n') _ _) with "Hcr").
      { intros s. apply sample_err_wf; try lia. }
      { pose P := (sample_err_mean n' m' Hnm' (bdd_cf_error (S n') (S m') _ Hnm)); by eapply P. }
      iIntros (sample') "Hcr".
      wp_pures.
      case_bool_decide.
      + wp_pures; iApply "HΦ"; iModIntro; iPureIntro; exists (fin_to_nat sample'); split; [auto|lia].
      + wp_pure.
        rewrite (simplify_accum_err (S n') (S m') _); last (apply Nat.ltb_nlt; by lia); try lia.
        wp_bind (#_ - #_)%E. wp_pure.
        replace (S (S depth') - 1)%Z with (Z.of_nat (S depth')) by lia.
        wp_apply ("IH" with "Hcr HΦ").
  Qed.



  (** PROBLEM 3: show that the unbounded approximate sampler is safe if we have enough error to eliminate past a depth *)
  Definition ubdd_approx_safe (n' m' depth : nat) (Hnm : (S n' < S m')%nat) E :
    {{{ € (bdd_cf_error (S n') (S m') (S depth) Hnm) }}} ubdd_rejection_sampler n' m' #() @ E {{{ v, RET v ; ⌜exists v' : nat, v = SOMEV #v' /\ (v' < S n')%nat⌝  }}}.
  Proof.
    iIntros (Φ) "Hcr HΦ"; rewrite /ubdd_rejection_sampler.
    assert (Hnm' : (n' < m')%nat) by lia.
    do 4 wp_pure.

    iInduction depth as [|depth' Hdepth'] "IH".
    - wp_pures.
      rewrite bdd_cd_error_penultimate.
      remember (S n') as n.
      remember (S m') as m.
      wp_apply (wp_rand_err_list_nat _ m' (seq n (m - n))).
      iSplitL "Hcr".
      + rewrite /err_factor.
        replace (length (seq _ _)) with (m - n)%nat by (symmetry; apply seq_length).
        replace (m) with (m' + 1)%nat by lia.
        done.
      + iIntros (sample'') "%Hsample''".
        wp_pures.
        case_bool_decide; wp_pures.
        * iApply "HΦ"; iModIntro; iPureIntro; exists (fin_to_nat sample''); split; [auto|lia].
        * exfalso.
          rewrite List.Forall_forall in Hsample''.
          specialize Hsample'' with sample''.
          apply Hsample''; last reflexivity.
          rewrite in_seq.
          split; first lia.
          replace (n + (m-n))%nat with m by lia.
          specialize (fin_to_nat_lt sample''); by lia.
    - wp_pures.
      wp_apply (wp_couple_rand_adv_comp _ _ _ Φ _ (bdd_cf_sampling_error (S n') _ _) with "Hcr").
      { intros s. apply sample_err_wf; try lia. }
      { pose P := (sample_err_mean n' m' Hnm' (bdd_cf_error (S n') (S m') _ Hnm));  by eapply P. }
      iIntros (sample') "Hcr".
      wp_pures.
      case_bool_decide.
      + wp_pures. iApply "HΦ"; iModIntro; iPureIntro; exists (fin_to_nat sample'); split; [auto|lia].
      + wp_pure.
        rewrite (simplify_accum_err (S n') (S m') _); last (apply Nat.ltb_nlt; by lia); try lia.
        wp_apply ("IH" with "Hcr HΦ").
  Qed.

  Lemma error_limit (r : nonnegreal) : (r < 1) -> forall 𝜀 : posreal, exists n : nat, r ^ (S n) < 𝜀.
  Proof.
    intros Hr 𝜀.
    assert (Har : Rabs r < 1).
    { destruct r as [rv Hrv]. simpl. rewrite Rabs_pos_eq; auto. }
    pose Lm := Lim_seq.is_lim_seq_geom r Har.
    apply Lim_seq.is_lim_seq_spec in Lm.
    simpl in Lm.
    specialize Lm with 𝜀.
    rewrite /Hierarchy.eventually in Lm.
    destruct Lm as [n Hn]; exists n; specialize Hn with (S n).
    replace (Rabs (r ^ S n - 0)) with (r ^ S n) in Hn; last first.
    { rewrite Rabs_right; rewrite Rminus_0_r; [done | apply Rle_ge, pow_le; by destruct r ]. }
    apply Hn; lia.
  Qed.


  (** PROBLEM 4: show that any positive error 𝜀 suffices to make the unbounded sampler terminate inbounds *)
  Theorem ubdd_cf_safety (n' m' : nat) (Hnm : (S n' < S m')%nat) E : forall 𝜀 : nonnegreal,
    ⊢ {{{ €𝜀 ∗ ⌜0 < 𝜀 ⌝  }}} ubdd_rejection_sampler n' m' #()@ E {{{ v, RET v ; ⌜exists v' : nat, v = SOMEV #v' /\ (v' < S n')%nat⌝ }}}.
  Proof.
    iIntros (𝜀 Φ) "!> (Hcr&%Hcrpos) HΦ".
    assert (Hef: (err_factor (S n') (S m')) < 1) by (apply err_factor_lt1; lia).
    destruct (error_limit (err_factor (S n') (S m')) Hef (mkposreal 𝜀 Hcrpos)) as [d].
    iApply ((ubdd_approx_safe _ _ d Hnm) with "[Hcr] [HΦ]"); auto.
    iApply ec_weaken; last iAssumption.
    rewrite /bdd_cf_error.
    simpl. simpl in H. apply Rlt_le. done.
  Qed.

End basic.



Section higherorder.
  Local Open Scope R.
  Context `{!clutchGS Σ}.


  Definition scale_unless (𝜀 𝜀1 : nonnegreal) (Θ : val -> bool) : val -> nonnegreal
    := (fun z => if (Θ z) then nnreal_zero else (𝜀 * 𝜀1)%NNR).

  Definition sampling_scheme_spec (e : expr) 𝜀 E (Ψ : val -> bool) (Θ : val -> bool) : Prop
    := {{{ True }}}
         e @ E
       {{{sampler checker, RET (PairV sampler checker);
            (* sampler needs to be able to amplify the mass during sampling *)
            (∀ 𝜀1, {{{€  𝜀1}}} ((Val sampler) #())%E @ E {{{ v, RET v; ⌜Ψ v = true ⌝ ∗ € (scale_unless 𝜀 𝜀1 Θ v) }}}) ∗
            (* Θ reflects checker whenever the value is one we could have sampled *)
            (∀ v : val, {{{ ⌜Ψ v = true⌝ }}} ((Val checker) v) @ E {{{ b, RET #b; ⌜b = Θ v⌝ }}}) ∗
            (* 𝜀 credit suffices to force checker to pass, on any possible sampled values *)
            (∀ v, {{{ €𝜀 }}} ((Val sampler) v) @ E {{{ v', RET v'; ⌜Ψ v' = true ⌝ ∗ ⌜Θ v' = true ⌝ }}}) ∗
            (* get weird typeclass errors when including this...
                {{{ True }}} ((Val checker) v) @ E {{{ v', RET v'; ⌜v' = true ⌝ }}} *)
            (* we can always just get _some_ value out of the sampler if we want *)
            ({{{ True }}} (Val sampler) #() @ E {{{ v, RET v; ⌜Ψ v = true ⌝ }}})
       }}}.

  (* next, we should show that this can actually be instantiated by some sane samplers *)
  Definition rand_sampling_scheme (n' m' : nat) (Hnm : (n' < m')%nat) : expr
     := (λ: "_", (Pair
                    (λ: "_", rand #m' from #())
                    (λ: "sample", "sample" ≤ #n')))%E.


  Definition flip_sampling_scheme : expr
     := (λ: "_",  (Pair
                     (λ: "_", Pair (rand #1 from #()) (rand #1 from #()))
                     (λ: "sample", (((Fst "sample") = #1) && ((Snd "sample") = #1)))))%E.

  (* TODO could try an unbounded one? *)

  Definition rand_support (m' : nat) (v : val) : bool :=
    match v with
    | LitV (LitInt n) => (Z.leb 0 n)%Z && (Z.leb n (Z.of_nat m'))%Z
    | _ => false
    end.

  Definition rand_check_accepts (n' : nat) (v : val): bool :=
    match v with
    | LitV (LitInt n) => (Z.leb n (Z.of_nat n'))%Z
    | _ => false
    end.

  (* TODO lift logical types into unofrm distributions? *)

  Lemma rand_sampling_scheme_spec (n' m' : nat) (Hnm : (n' < m')%nat) E :
    sampling_scheme_spec
      (rand_sampling_scheme n' m' Hnm #())
      (nnreal_div (nnreal_nat (S m' - S n')%nat) (nnreal_nat (S m')%nat))
      E
      (rand_support m')
      (rand_check_accepts n').
  Proof.
    rewrite /sampling_scheme_spec. iIntros (Φ) "_ HΦ".
    rewrite /rand_sampling_scheme. wp_pures.
    iModIntro; iApply "HΦ".
    iSplit.
    { (* the generic composition rule *)
      iIntros (𝜀1 Post) "!> Hcr HPost".
      wp_pures.
      pose 𝜀2 := (fun (z : fin (S m')) =>
          (scale_unless (nnreal_div (nnreal_nat (S m' - S n')) (nnreal_nat (S m'))) 𝜀1 (rand_check_accepts n')) #z).
      iApply (wp_couple_rand_adv_comp  m' _ _ _ 𝜀1 𝜀2 _ with "Hcr") .
      - (* uniform bound on 𝜀2*) admit.
      - (* series converges to expectation *) admit.
      - iNext; iIntros (n) "Hcr".
        iApply "HPost".
        iSplitR.
        + iPureIntro. rewrite /rand_support.
          (* true fact for fin types *)
          admit.
        + rewrite /𝜀2.
          iApply "Hcr".}
    iSplit.
    { iIntros (v).
      (* in the support, sample ... *)
      admit. }
    iSplit.
    { admit. }
    { admit. }
  Admitted.


  (* higher order rejection sampler *)
  Definition ho_bdd_rejection_sampler :=
    (λ: "depth",
      λ: "ho_sampler",
        let: "sampler" := (Fst "ho_sampler") in
        let: "checker" := (Snd "ho_sampler") in
        let: "do_sample" :=
          (rec: "f" "tries_left" :=
              if: ("tries_left" - #1) < #0
                then NONE
                else let: "next_sample" := ("sampler" #()) in
                     if: ("checker" "next_sample")
                        then SOME "next_sample"
                        else "f" ("tries_left" - #1))
        in "do_sample" "depth")%E.


  Program Definition generic_geometric_error (r : nonnegreal) (depth : nat) : nonnegreal := nnreal_inv (mknonnegreal (r ^ depth) _).
  Next Obligation. intros. apply pow_le. by destruct r. Qed.

  Lemma simpl_generic_geometric_error (r : nonnegreal) (depth : nat) : (r * generic_geometric_error r (S depth))%NNR = (generic_geometric_error r depth).
  Proof.
    rewrite /generic_geometric_error.
    simpl.
    (* easy proof, come back to this. *)
  Admitted.



  (* prove the bounded rejection sampler always ends in SOME using only the higher order spec *)
  Definition ho_bdd_approx_safe (make_sampler : val) (r : nonnegreal) (depth : nat) Ψ Θ E :
    r < 1 ->
    sampling_scheme_spec make_sampler r E Ψ Θ ->
    {{{ € (generic_geometric_error r (S depth)) }}}
      ho_bdd_rejection_sampler #(S depth) make_sampler  @ E
    {{{ v, RET v; ∃ v', ⌜ v = SOMEV v' ⌝}}}.
  Proof.
    (* initial setup *)
    iIntros (Hr Hmake_sampler Φ) "Hcr HΦ".
    rewrite /ho_bdd_rejection_sampler.
    wp_pures.
    wp_bind (_ make_sampler)%E.
    rewrite /sampling_scheme_spec in Hmake_sampler.
    wp_apply Hmake_sampler; try done.
    iIntros (sampler _c) "(#Hcomp&_&#HsampleErr&#Hsampler)".
    wp_pures.
    wp_bind (_ make_sampler)%E.
    wp_apply Hmake_sampler; try done.
    iIntros (_s checker) "(_&#Hcheck&_&_)".
    do 6 wp_pure.
    clear _s _c Hmake_sampler.

    iInduction depth as [|depth' Hdepth'] "IH".
    - (* base case: we should be able to spend the geometric error to eliminate the bad sample
         and end up in the right branch *)
      wp_pures.

      (* step the sampler*)
      wp_bind (sampler #())%E.
      wp_apply ("HsampleErr" with "[Hcr]"); try done.
      { (* proof irrelevance thing *)
          iClear "#".
          iApply (ec_weaken with "Hcr").
          rewrite /generic_geometric_error /=.
          rewrite Rmult_1_r.
          (* this is true... but I want to double check that this generic_geometric_error spec is right first *)
          admit. }

      iIntros (next_sample) "(%HsampleV & %HcheckV )"; wp_pures.
      (* spend the credits in the checker*)
      wp_bind (checker next_sample)%E.
      wp_apply "Hcheck"; first by iPureIntro.
      iIntros (b) "->"; wp_pures.
      rewrite HcheckV; wp_pures.
      iModIntro; iApply "HΦ".
      iExists next_sample; auto.
    - wp_pures.
      replace (bool_decide _) with false; last (symmetry; apply bool_decide_eq_false; lia).
      (* apply the amplification lemma step the sampler *)
      wp_pures.
      wp_bind (sampler #())%E.
      (* why did this stop working? *)
      wp_apply ("Hcomp" $! (generic_geometric_error r (S (S depth'))) with "Hcr").
      iIntros (sample) "(%HΨ&Hcr)".
      wp_pures.
      (* depending on which case we're in (as in, depending on (Θ sample)), either conclude or apply the IH. *)
      wp_bind (checker sample)%E.
      wp_apply "Hcheck"; first (iPureIntro; by assumption).
      iIntros (b) "%Hb".
      destruct b.
      + wp_pures.
        iApply "HΦ"; iModIntro; iPureIntro. exists sample; auto.
      +  iSpecialize ("IH" with "[Hcr]").
        { iClear "#". rewrite /scale_unless. replace (Θ sample) with false.
          rewrite simpl_generic_geometric_error. iFrame. }
        iSpecialize ("IH" with "HΦ").
        iClear "#".
        wp_pure.
        wp_bind (#(S (S depth'))- #1%nat)%E; wp_pure.

        replace #((S (S depth')) - 1) with #(S depth'); last first.
        { do 2 f_equal. rewrite Nat2Z.inj_succ. lia. }
        iApply "IH".
  Admitted.

End higherorder.
