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

  (* FinFun.Fin2Restrict.extend: *)

  (* extends a function from fin to a function on nat using a default value *)
  Program Definition f_lift_fin_nat {A} (N : nat) (a : A) (f : fin N -> A) : nat -> A
    := fun n => match (n <? N)%nat with
              | true => f (nat_to_fin (_ : (n < N)%nat))
              | false => a
              end.
  Next Obligation. intros; by apply (reflect_iff _ _ (Nat.ltb_spec0 _ _)). Qed.

  Lemma f_lift_fin_nat_ltN {A} (N n: nat) (a : A) (Hn : (n < N)%nat) f :
    (f_lift_fin_nat N a f) n = f (nat_to_fin Hn).
  Proof. Admitted.

  Lemma f_lift_fin_nat_geN {A} (N n: nat) (a : A) (Hn : not (n < N)%nat) f :
    (f_lift_fin_nat N a f) n = a.
  Proof. Admitted.


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

  Lemma encode_inv_nat_fin_total (n N: nat) (H : (n < N)%nat) : (@encode_inv_nat (fin N) _ _ n) = Some (nat_to_fin H).
  Proof.
    (* assert (H' : (n < card (fin N))%nat) by (rewrite fin_card; lia).
    destruct (encode_inv_decode n H') as [x [-> Hx]]; f_equal.
    rewrite /encode_nat in Hx.   *)

    rewrite -encode_inv_encode_nat.
    f_equal.
    rewrite /encode_nat.
    rewrite /encode /nat_countable /finite_countable.
    rewrite -Pos.of_nat_succ SuccNat2Pos.pred_id.
    replace (list_find (eq (nat_to_fin H)) (enum (fin N))) with (Some (n, nat_to_fin H)); first by simpl.


    (* the fact that I'm using nat_to_fin H has being... extremely annoying. But I'm not sure
        if there's a better option.



     *)
    (* Check fin_to_nat_to_fin.
    Check nat_to_fin_to_nat. *)

    rewrite /enum; simpl.
    symmetry; apply list_find_Some; split; last split.
    - induction n as [|n' IH].
      + intros. simpl. destruct N; [lia | done].
      + (* lost, is this the right induction? *)

        (* can use to turn (nat_to_fin (_ < (S N'))) into (nat_to_fin (_ < N'))
           Check Fin.of_nat_ext.
        *)
        admit.
    - done.
    - admit.
  Admitted.


  Lemma encode_inv_nat_fin_undef (n N: nat) (H : not (n < N)%nat) : (@encode_inv_nat (fin N) _ _ n) = None.
  Proof.
    apply encode_inv_decode_ge.
    rewrite fin_card.
    lia.
  Qed.

  Lemma SeriesC_fin_to_nat (N : nat) (f : fin N -> R) :
    SeriesC (fun s : fin N => f s) = SeriesC (fun n : nat => (f_lift_fin_nat N 0 f) n).
  Proof.
    (* can't use SeriesC_ext since the two series have different types
       can we use series_ext on the underlying countable sum? *)
    rewrite /SeriesC.
    apply Series_ext; intros n.
    rewrite /countable_sum.
    rewrite encode_inv_nat_nat_total.
    remember (n <? N)%nat as K; destruct K.
    - symmetry in HeqK; apply Nat.ltb_lt in HeqK.
      rewrite encode_inv_nat_fin_total.
      simpl. by rewrite f_lift_fin_nat_ltN.
    - rewrite encode_inv_nat_fin_undef; last (apply Nat.ltb_nlt; by symmetry).
      simpl.
      rewrite f_lift_fin_nat_geN; last (apply Nat.ltb_nlt; by symmetry).
      done.
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
          (* their extensionality is too weak... it claims equality at all points rather than
                just those on the sum indices *)
            (* apply Hierarchy.sum_n_m_ext.
            intros.
            apply countable_sum_ext; intros.
            symmetry; apply Hinit. *)
            admit. }

    (* now it's the reindexing problem *)
    admit.

  Admitted.




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

    (* turn it into a sum over the naturals so we can use all the familiar SeriesC lemmas *)
    rewrite SeriesC_fin_to_nat.

    (* somehow we want to _reindex_ this series *)


    (* finite sum to sum_n_m? *)
    (* finite sum to nat sum? *)

    Check Hierarchy.sum_n_m _ 0 5.


    (* rewrite to be a difference? *)
    replace (S m') with (S n' + (S m' - S n'))%nat; last lia.
    remember (S m' - S n')%nat as 𝛥.
    induction 𝛥 as [| 𝛥' IH].
    - (* extensionally equal to 0 *)
      rewrite <- (SeriesC_ext (fun x : fin (S n' + 0) => nnreal_zero)).

    -



    Check SeriesC_leq.
    rewrite /SeriesC.


  Admitted.



Lemma SeriesC_leq (N : nat) (v : R) :
  Series (λ (n : nat), if bool_decide (n < N)%nat then v else 0) = INR N * v.
Proof.
  induction N as [|N IHN].
  - rewrite Series_0 //=; lra.
  - assert (INR (S N) = (INR N + 1)) as ->; [apply S_INR | ].
    rewrite Rmult_plus_distr_r Rmult_1_l.
    rewrite -IHN.
    rewrite -(Series_singleton (N)%nat v).
    erewrite <- Series_plus; [ | apply ex_series_leq | apply ex_series_singleton].
    apply Series_ext; intro n.
    repeat case_bool_decide; simplify_eq; try (lra || lia).
    rewrite Rplus_0_l.
    apply Series_singleton.
Qed.







    (* we want something pretty close to SeriesC_leq *)




    (* replace (s <? S n') with (bool_decide (s < S n')%nat).
    (* for some reason it doesn't unify unless I explicitly give it the body? awkward *)
    Set Printing Coercions.
    rewrite /SeriesC /countable_sum. rewrite /Series.Series.



    remember
      (fun s : fin (S m') => 1 / INR (S m') * nonneg (if (fin_to_nat s <? S n')%nat then nnreal_zero else nnreal_div 𝜀₁ (err_factor (S n') (S m'))))
      as Body.
    rewrite (SeriesC_split_pred Body (fun s => (s <? S n')%nat)).
    - Check SeriesC_finite_bound.
       unfold SeriesC.
       unfold Series.Series.


      (* simplify the first series
      replace (SeriesC (λ a : fin (S m'), if (a <? S n')%nat then Body a else 0))
        with (SeriesC (λ a : fin (S m'), 0)); last first.
      { apply SeriesC_ext.
        intros s.
        remember (s <? S n')%nat as HCond.
        destruct HCond; try done.
        rewrite HeqBody; rewrite <- HeqHCond.
        replace (nonneg nnreal_zero) with 0 by auto.
        by rewrite Rmult_0_r. }
      (* simplify the second series *)
      pose K := (1 / S m' * nnreal_div 𝜀₁ (err_factor (S n') (S m'))).
      replace (SeriesC (λ a : fin (S m'), if (a <? S n')%nat then 0 else Body a)) with (nonneg 𝜀₁); last first.
      {  apply SeriesC_ext.
         intros s.
         remember (s <? S n')%nat as HCond.
         destruct HCond.

      }

      (* lol wait, this is the same problem *)

    -
    -




    /err_factor.
    (* split the sum into the elements less than n and those greater *)
    (* sum of constant zero is zero *)
    (* after simplification, the other sum has m-n elements at constant (𝜀₁/m-n) *)

    *)*)
  Admitted.




  (** warmup: a finite example *)
  Definition bdd_approx_safe_finite_example (n' m' depth : nat) (Hnm : (S n' < S m')%nat) E :
    (depth = 3%nat) ->
    {{{ € (bdd_cf_error (S n') (S m') depth Hnm) }}} bdd_rejection_sampler n' m' #(S depth) @ E {{{ v, RET v ; ⌜exists v' : nat, v = SOMEV #v' /\ (v' < S n')%nat⌝ }}}.
  Proof.
    iIntros (-> Φ) "Hcr HΦ"; rewrite /bdd_rejection_sampler.
    wp_pures.

    (* S depth=3 sample *)
    wp_apply (wp_couple_rand_adv_comp _ _ _ Φ _ (bdd_cf_sampling_error (S n') _ _) with "Hcr").
    { intros s. apply sample_err_wf; try lia. }
    { pose P := (sample_err_mean n' m' (bdd_cf_error (S n') (S m') 3 Hnm)); apply P. }
    iIntros (sample) "Hcr".
    wp_pures.
    case_bool_decide; wp_pures.
    { iApply "HΦ"; iModIntro; iPureIntro; exists (fin_to_nat sample); split; [auto|lia]. }
    rewrite (simplify_accum_err (S n') (S m') _); last (apply Nat.ltb_nlt; by lia); try lia.

    (* S depth=2 sample *)
    wp_apply (wp_couple_rand_adv_comp _ _ _ Φ _ (bdd_cf_sampling_error (S n') _ _) with "Hcr").
    { intros s. apply sample_err_wf; try lia. }
    { pose P := (sample_err_mean n' m' (bdd_cf_error (S n') (S m') 2 Hnm)); apply P. }
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
      { pose P := (sample_err_mean n' m' (bdd_cf_error (S n') (S m') _ Hnm)); by eapply P. }
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
      { pose P := (sample_err_mean n' m' (bdd_cf_error (S n') (S m') _ Hnm));  by eapply P. }
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
  Theorem ubdd_cf_safety (n' m' : nat) (Hnm : (S n' < S m')%nat) E : forall 𝜀,
    ⊢ {{{ €𝜀 ∗ ⌜𝜀 > 0 ⌝  }}} ubdd_rejection_sampler n' m' #()@ E {{{ v, RET v ; ⌜exists v' : nat, v = SOMEV #v' /\ (v' < S n')%nat⌝ }}}.
  Proof.
    iIntros (𝜀 Φ) "!> (Hcr&%Hcrpos) HΦ".
    assert (Hef: (err_factor (S n') (S m')) < 1).
    { rewrite /err_factor.  apply factor_lt_1; try lia. }
    destruct (error_limit (err_factor (S n') (S m')) Hef 𝜀) as [d].
    iApply ((ubdd_approx_safe _ _ d Hnm) with "[Hcr] [HΦ]"); auto.
    iApply ec_weaken; last iAssumption.
    rewrite /bdd_cf_error.
    simpl. simpl in H. apply Rlt_le. done.
  Qed.

End basic.
