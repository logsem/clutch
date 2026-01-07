From clutch.eris.tutorial Require Export eris_tutorial.


Section geometric.
  Context `{!erisGS Σ}.

  (** * Geometric distribution *)

  (** In this example we will prove some properties about the geometric
      distribution. The program below simulates a geometric process with
      parameter (1/2). On every step it generates a random bit, and it returns
      the number of failed attempts before generating a 0 *)

  Definition geometric : val :=
    rec: "geo" "n" :=
      if: rand #1%nat <= #0 then #0 else "geo" "n" + #1.


  (** First, we want to show that the result is always non-negative. Note that
      below we are proving a partial correctness specification, divergence is a
      valid behavior, so the specification just says that the probability that
      the program terminates in a value that is negative is zero *)

  Lemma geo_nonneg :
    {{{ True }}} geometric #() {{{ m, RET #m; ⌜0 <= m⌝%Z }}}.
  Proof.
    iLöb as "IH".
    iIntros (Φ) "_ HΦ".
    wp_lam.
    wp_bind (rand _)%E.
    iApply wp_rand_nat; auto.
    iIntros (n) "%Hn".
    destruct n.
    - wp_pures.
      iModIntro.
      by iApply ("HΦ").
    - do 2 wp_pure.
      wp_bind (geometric #()).
      iApply "IH"; auto.
      iModIntro.
      iIntros (m) "%Hm".
      wp_pures.
      iApply "HΦ".
      iPureIntro.
      lia.
  Qed.

  (** We can use the specification above to reason about the probability that
      the program returns a strictly positive result. Again, in a partial
      correctness logic, the only thing we can actually prove is that the
      probability that the program returns 0 or less is (1/2). *)

  Lemma geo_gt0 :
    {{{ ↯(1/2) }}} geometric #() {{{ m, RET #m; ⌜0 < m⌝%Z }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    wp_lam.
    wp_bind (rand _)%E.
    (** Since we only want to avoid one single outcome, we can use
        wp_rand_err_nat and spend ↯ to ensure we do not get 0 *)
    iApply (wp_rand_err_nat 1 0 with "Herr").
    (* Exercise *)
  Admitted.

    (* Sample solution:
    iIntros (n) "(%Hn1 & %Hn2)".
    destruct n; [done|].
    do 2 wp_pure.
    wp_bind (geometric #()).
    iApply geo_nonneg; auto.
    iModIntro.
    iIntros (m) "%Hm".
    wp_pures.
    iApply "HΦ".
    iPureIntro.
    lia.
  Qed. *)


  (** Similarly, we can prove that the probability that the program does not
      return 0 or less is (1/2). *)

  Lemma geo_le0 :
    {{{ ↯(1/2) }}} geometric #() {{{ m, RET #m; ⌜m <= 0⌝%Z }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    wp_lam.
    wp_bind (rand _)%E.
    (* Exercise *)
  Admitted.


 (* Sample solution:
    iApply (wp_rand_err_nat _ _ 1).
    iFrame.
    iIntros (n) "(%Hn1 & %Hn2)".
    inversion Hn1 as [Hn3|? Hn3].
    - exfalso.
      apply Hn2, Hn3.
    - inversion Hn3.
      do 2 wp_pure.
      iApply "HΦ".
      auto.
  Qed.
  *)

  (** Note that the two specifications together still do not say anything about
      termination behavior of the geometric process. A program that diverges
      with probability 1 will satisfy all of the specifications as well. Eris
      supports as well total correctness specifications that allow us to reason
      about termination. However, let's keep this aside for now, and just reason
      about partial correctness.

      We can try to prove some properties about ranges of outputs, e.g. the
      probability that the geometric does not return a result equal to or less
      than 1 is (1/4) *)

  Lemma geo_le1 :
    {{{ ↯(1/4) }}} geometric #() {{{ m, RET #m; ⌜m <= 1⌝%Z }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    wp_lam.
    wp_bind (rand _)%E.

    (** At this point, we do not have enough error credits to outright reject
        one outcome. Instead, we have to distribute error credits across the
        outcomes of [rand #1]. Note that in the case v=0, we can immediately
        prove the postcondition, since 0 <= 1. That branch then needs 0 error
        credits. Therefore, we can give all other credits to the branch v=1. By
        a simple calculation, we get that we can give ↯(1/2) to the branch. To
        simplify the proof script, however, we will give it ↯(/(1+1)). *)

    set (F (n:nat) := if bool_decide (n=0) then 0%R else (1/2)%R).
    iApply (wp_rand_exp_nat 1 _ F with "Herr").
    - intro n.
      unfold F.
      real_solver.
    - (** The goal gives us a fold for a finite list, so we can actually
          compute with it *)
      unfold F.
      simpl.
      lra.
    - iIntros (n) "(%Hn & Herr)".
      unfold F.
      (** We now have two disjuncts: either n=1 or n<= 0. We can obtain them
          by inverting n<=1
       *)
      inversion Hn as [|m Hm].
      + (** Let's first look at the case n=1. We can execute the program until
            before of the recursive call *)
        do 2 wp_pure.
        simpl.
        (** We now have ↯(1/2) and we have to compute [geometric #() + #1].
            In order for the result to be <=1, geometric must return 0 (or less).
            We will then spend our error credits to use the spec given by geo_le0
         *)
        wp_bind (geometric #()).
        iApply (geo_le0 with "Herr").
        iModIntro.
        iIntros (m) "%Hm".
        wp_pures.
        iApply "HΦ".
        iPureIntro.
        lia.
      + (** The case n<=0 is simpler. We can first invert the hypothesis once
            again to get an equality n=0. Then we can simply execute the program
            symbolically and get to a result *)
        inversion Hm.
        simpl.
        wp_pures.
        iApply "HΦ".
        iPureIntro.
        lia.
  Qed.

  (** Let us now try to generalize these results. It is well-known that the mass
      of the tails of such a geometric, i.e. the probability of sampling larger
      than n is (1/2^(n+1)). Below we write a definition for this probability.
  *)

  Definition geo_tail_mass (n : nat) := (1/ 2^(n+1))%R.


  (** We write and prove some lemmas to work with this construct. *)

  Lemma geo_tail_mass_0  :
    geo_tail_mass 0 = (1/2)%R.
  Proof.
    unfold geo_tail_mass.
    simpl.
    lra.
  Qed.

  Lemma geo_tail_mass_bounded (m: nat) :
    (0 <= geo_tail_mass m <= 1)%R.
  Proof.
    unfold geo_tail_mass.
    split.
    - left.
      apply Rdiv_lt_0_compat; real_solver.
    - rewrite <- Rcomplements.Rdiv_le_1.
      + apply pow_R1_Rle.
        real_solver.
      + apply pow_lt.
        real_solver.
  Qed.

  Lemma geo_tail_mass_S (m : nat) :
    (geo_tail_mass (S m) = (1 / 2) * geo_tail_mass m)%R.
  Proof.
    unfold geo_tail_mass.
    simpl.
    rewrite Rdiv_mult_distr.
    lra.
  Qed.


  (** Let us now prove a specification about the mass of the tails of the
      geometric process. Namely, we will show that the probability that the
      output is not n or less is (geo_tail_mass n) for every (n : nat).
      The proof goes by induction on n, and uses the specifications and
      lemmas we introduced above
   *)

  Lemma geo_le_n (n: nat) :
    {{{ ↯(geo_tail_mass n)}}} geometric #() {{{ m, RET #m; ⌜m <= n⌝%Z }}}.
  Proof.
    iInduction (n) as [|m] "IH".
    - iIntros (Φ) "Herr HΦ".
      rewrite geo_tail_mass_0.
      iApply (geo_le0 with "[Herr]"); auto.
    - iIntros (Φ) "Herr HΦ".
      wp_lam.

      (** We now get to the main part of the proof. Here we need to split error
          credits depending on whether the result of the sampling is 0 or 1.
          Luckily, we have defined an abstraction over the credit arithmetic to
          simplify this task. *)

      (* Exercise *)

   Admitted.

      (* Sample solution:
      set (F (n:nat) := if bool_decide (n=0)
                      then 0%R
                      else geo_tail_mass m %R).
      wp_bind (rand _)%E.
      iApply (wp_rand_exp_nat 1 _ F with "Herr").
      + intro n.
        unfold F.
        case_bool_decide; [real_solver|].
        apply geo_tail_mass_bounded.
      + unfold F.
        simpl.
        rewrite geo_tail_mass_S.
        lra.
      + iIntros (n) "(%Hn & Herr)".
        unfold F.
        inversion Hn as [|k Hk].
        * do 2 wp_pure.
          simpl.
          wp_bind (geometric #()).
          wp_apply ("IH" with "Herr"); auto.
          iIntros (l) "%Hl".
          wp_pures.
          iApply "HΦ".
          iPureIntro.
          lia.
        * inversion Hk.
          simpl.
          wp_pures.
          iApply "HΦ".
          iPureIntro.
          lia.
  Qed.
  *)

  Lemma geo_gt1 :
    {{{ ↯(3/4) }}} geometric #() {{{ m, RET #m; ⌜1 < m⌝%Z }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    wp_lam.
    wp_bind (rand _)%E.
    set (F (n:nat) := if bool_decide (n=0) then 1%R else (1/2)%R).
    iApply (wp_rand_exp_nat 1 _ F with "Herr").
    - intro n.
      unfold F.
      real_solver.
    - unfold F.
      simpl.
      lra.
    - iIntros (n) "(%Hn & Herr)".
      unfold F.
      inversion Hn as [|m Hm].
      + do 2 wp_pure.
        simpl.
        wp_bind (geometric #()).
        iApply (geo_gt0 with "[$Herr]").
        iModIntro.
        iIntros (m) "%Hm".
        wp_pures.
        iApply "HΦ".
        iPureIntro.
        lia.
      + inversion Hm.
        simpl.
        iExFalso.
        by iApply (ec_contradict with "Herr").
  Qed.


End geometric.
