From clutch.app_rel_logic Require Export app_weakestpre primitive_laws.
From clutch.ub_logic Require Export ub_clutch.

Set Default Proof Using "Type*".

Section proofs.
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

  (** nnreal exponents *)
  Fixpoint nnreal_nat_exp (r : nonnegreal) (n : nat) : nonnegreal :=
    match n with
    | O    => nnreal_one
    | S n' => nnreal_mult r (nnreal_nat_exp r n')
    end.

  Lemma nnreal_nat_exp_limit : forall (r 𝜀 : nonnegreal), (r < 1) -> exists n, forall n0, (n0 > n)%nat -> (nnreal_nat_exp r n0) < 𝜀.
  Proof. (* this is true, how to prove it in the nnreal framework? *) Admitted.


  (** defining error values for each step *)

  Definition err_factor n m := (nnreal_div (nnreal_nat (m - n)%nat) (nnreal_nat m%nat)).

  Lemma err_factor_lt1 n m (Hn : (0 < n)%nat) (Hnm : (n < m)%nat) : err_factor n m < 1.
  Proof.
    rewrite /err_factor.
    assert (Hdenom : (0 < m)%nat) by lia.
    assert (Hnum : (m - n < m)%nat) by lia.
    (* numerator is less than the denominator and they are both positive *)
  Admitted.

  (* error for the bounded sampler with a given number of tries remaining *)
  Definition bdd_cf_error n m depth := nnreal_nat_exp (err_factor n m) depth.

  (* this lemma is for proofs which iterate to the very end
     ie, doing 0 samples requires error tolerance of 1 *)
  Lemma bdd_cd_error_final n m : bdd_cf_error n m 0 = nnreal_one.
  Proof. by rewrite /bdd_cf_error /nnreal_nat_exp. Qed.

  (* this lemma is for proofs which iterate up until the last sample
     ie, a rejection sampler to exclude the final recursive step *)
  Lemma bdd_cd_error_penultimate n m : bdd_cf_error n m 1 = err_factor n m.
  Proof. rewrite /bdd_cf_error /nnreal_nat_exp. (* nnreal: _ * 1 = _ *) Admitted.

  (* distribution of error mass 𝜀₁ for a given sample:
      - zero error given to cases which are inbounds
      - uniform error to the recursive case *)
  Definition bdd_cf_sampling_error n m 𝜀₁ : (fin m) -> nonnegreal
    := fun sample =>
         if (sample <? n)%nat
            then nnreal_zero
            else (nnreal_div 𝜀₁ (err_factor n m)).

  (* lemma for simplifying accumulated error in the recursive case *)
  Lemma simplify_accum_err (n m d': nat) (s : fin m)  :
    (s <? n)%nat = false -> bdd_cf_sampling_error n m (bdd_cf_error n m (S d')) s = (bdd_cf_error n m d' ).
  Proof.
    intros Hcase.
    rewrite /bdd_cf_sampling_error Hcase /bdd_cf_error {1}/nnreal_nat_exp -/nnreal_nat_exp.
    remember (err_factor n m) as X.
    remember (nnreal_nat_exp X d') as Y.
    (* nnreal: X * Y  / X = Y *)
  Admitted.


  (* error distribution is well-formed for each possible sample *)
  Lemma sample_err_wf n m d (s : fin m) : bdd_cf_sampling_error n m (bdd_cf_error n m (S d)) s <= 1.
  Proof.
    (* it is either 1, or epsilon times something at most 1 *)
    rewrite /bdd_cf_sampling_error.
    remember (s <? n)%nat as H.
    destruct H.
    - admit. (* nnreal: 0 < 1 *)
    - rewrite /bdd_cf_error.
      (* nnreal: this is true because we can pull out a factor from the exponent, and the remainder is
         a natural power of a number less than 1. *)
      admit.
  Admitted.

  (* mean of error distribution is preserved *)
  Lemma sample_err_mean n' m' 𝜀₁ :
    SeriesC (λ s : fin (S m'), (1 / S m') * bdd_cf_sampling_error (S n') (S m') 𝜀₁ s) = 𝜀₁.
  Proof.
    remember (S n') as n.
    remember (S m') as m.
    rewrite /bdd_cf_sampling_error /err_factor.
    (* split the sum into the elements less than n and those greater *)
    (* sum of constant zero is zero *)
    (* after simplification, the other sum has m-n elements at constant (𝜀₁/m-n) *)
  Admitted.




  (** warmup: a finite example *)
  Definition bdd_approx_safe_finite_example (n' m' depth : nat) (Hnm : (S n' < S m')%nat) E :
    (depth = 3%nat) ->
    {{{ € (bdd_cf_error (S n') (S m') depth) }}} bdd_rejection_sampler n' m' #(S depth) @ E {{{ v, RET v ; ⌜exists v' : nat, v = SOMEV #v' /\ (v' < S n')%nat⌝ }}}.
  Proof.
    (* make these off by one errors easier to unpack *)
    remember (S n') as n.
    remember (S m') as m.
    assert (Hn : (0 < n)%nat) by lia.
    assert (Hm : (0 < m)%nat) by lia.

    iIntros (-> Φ) "Hcr HΦ"; rewrite /bdd_rejection_sampler.
    wp_pures. rewrite Heqm Heqn.

    (* S depth=3 sample *)
    wp_apply (wp_couple_rand_adv_comp _ _ _ Φ _ (bdd_cf_sampling_error (S n') _ _) with "Hcr").
    { apply sample_err_wf. }
    { pose P := (sample_err_mean n' m' (bdd_cf_error (S n') (S m') 3)); apply P. }
    iIntros (sample) "Hcr".
    wp_pures.
    case_bool_decide; wp_pures.
    { iApply "HΦ"; iModIntro; iPureIntro; exists (fin_to_nat sample); split; [auto|lia]. }
    rewrite (simplify_accum_err (S n') (S m') _); last (apply Nat.ltb_nlt; by lia).

    (* S depth=2 sample *)
    wp_apply (wp_couple_rand_adv_comp _ _ _ Φ _ (bdd_cf_sampling_error (S n') _ _) with "Hcr").
    { apply sample_err_wf. }
    { pose P := (sample_err_mean n' m' (bdd_cf_error (S n') (S m') 2)); apply P. }
    iIntros (sample') "Hcr".
    wp_pures.
    case_bool_decide; wp_pures.
    { iApply "HΦ"; iModIntro; iPureIntro; exists (fin_to_nat sample'); split; [auto|lia]. }
    rewrite (simplify_accum_err (S n') (S m') _); last (apply Nat.ltb_nlt; by lia).

    (* S depth=1 sample *)
    rewrite bdd_cd_error_penultimate.
    rewrite -Heqm -Heqn.
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
    {{{ € (bdd_cf_error (S n') (S m') (S depth)) }}} bdd_rejection_sampler n' m' #(S depth)@ E {{{ v, RET v ; ⌜exists v' : nat, v = SOMEV #v' /\ (v' < S n')%nat⌝ }}}.
  Proof.
    remember (S n') as n.
    remember (S m') as m.
    assert (Hn : (0 < n)%nat) by lia.
    assert (Hm : (0 < m)%nat) by lia.

    iIntros (Φ) "Hcr HΦ"; rewrite /bdd_rejection_sampler.
    do 4 wp_pure.

    (* induction should reach the base cse when S depth = 1 <=> depth = 0 *)
    iInduction depth as [|depth' Hdepth'] "IH".
    - wp_pures.
      rewrite bdd_cd_error_penultimate.
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
      { apply sample_err_wf. }
      { pose P := (sample_err_mean n' m' (bdd_cf_error (S n') (S m') _)); rewrite Heqn Heqm; by eapply P. }
      iIntros (sample') "Hcr".
      wp_pures.
      case_bool_decide.
      + wp_pures; iApply "HΦ"; iModIntro; iPureIntro; exists (fin_to_nat sample'); split; [auto|lia].
      + wp_pure.
        rewrite (simplify_accum_err (S n') (S m') _); last (apply Nat.ltb_nlt; by lia).
        wp_bind (#_ - #_)%E. wp_pure.
        replace (S (S depth') - 1)%Z with (Z.of_nat (S depth')) by lia.
        rewrite Heqn Heqm.
        wp_apply ("IH" with "Hcr HΦ").
  Qed.



  (** PROBLEM 3: show that the unbounded approximate sampler is safe if we have enough error to eliminate past a depth *)
  Definition ubdd_approx_safe (n' m' depth : nat) (Hnm : (S n' < S m')%nat) E :
    {{{ € (bdd_cf_error (S n') (S m') (S depth)) }}} ubdd_rejection_sampler n' m' #() @ E {{{ v, RET v ; ⌜exists v' : nat, v = SOMEV #v' /\ (v' < S n')%nat⌝  }}}.
  Proof.
    remember (S n') as n.
    remember (S m') as m.
    assert (Hn : (0 < n)%nat) by lia.
    assert (Hm : (0 < m)%nat) by lia.

    iIntros (Φ) "Hcr HΦ"; rewrite /ubdd_rejection_sampler.
    do 4 wp_pure.

    iInduction depth as [|depth' Hdepth'] "IH".
    - wp_pures.
      rewrite bdd_cd_error_penultimate.
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
      { apply sample_err_wf. }
      { pose P := (sample_err_mean n' m' (bdd_cf_error (S n') (S m') _)); rewrite Heqn Heqm; by eapply P. }
      iIntros (sample') "Hcr".
      wp_pures.
      case_bool_decide.
      + wp_pures. iApply "HΦ"; iModIntro; iPureIntro; exists (fin_to_nat sample'); split; [auto|lia].
      + wp_pure.
        rewrite (simplify_accum_err (S n') (S m') _); last (apply Nat.ltb_nlt; by lia).
        rewrite Heqn Heqm.
        wp_apply ("IH" with "Hcr HΦ").
  Qed.


  (** PROBLEM 4: show that any positive error 𝜀 suffices to make the unbounded sampler terminate inbounds *)
  Theorem ubdd_cf_safety (n' m' : nat) (Hnm : (S n' < S m')%nat) E : forall 𝜀,
    ⊢ {{{ €𝜀 ∗ ⌜𝜀 > 0 ⌝  }}} ubdd_rejection_sampler n' m' #()@ E {{{ v, RET v ; ⌜exists v' : nat, v = SOMEV #v' /\ (v' < S n')%nat⌝ }}}.
  Proof.
    iIntros (𝜀 Φ) " !> (Hcr&%Hcrpos) HΦ".
    destruct (nnreal_nat_exp_limit (err_factor (S n') (S m')) 𝜀) as [d].
    - apply err_factor_lt1; lia.
    - iApply (ubdd_approx_safe with "[Hcr] [HΦ]"); auto.
      iApply ec_weaken; last iAssumption.
      rewrite /bdd_cf_error.
      apply Rlt_le.
      specialize H with (S d); apply H; lia.
  Qed.


  (* PROBLEM ??: If error credits can rule out nontermination we could show that the unbounded
     rejection sampler doesn't terminate with probability zero (in the UB logic)  *)

  (* PROBLEM ??: We should be able to prove:
        - the unbounded sampler is equivalent to the bounded sampler with a given error
        - the bounded sampler is equivalent to a single sample with a given error
      in the approximate relational logic. *)

End proofs.
