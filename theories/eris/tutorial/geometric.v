From clutch.eris Require Export eris.


Section geometric.
  Context `{!erisGS Σ}.

  (** * Geometric distribution

  *)

  (**
      In this example we will prove some properties about
      the geometric distribution. The program below simulates
      a geometric process with parameter (1/2). On every step
      it generates a random bit, and it returns the number
      of failed attempts before generating a 0
   *)

  Definition geometric : val :=
    rec: "geo" "n" :=
      if: rand #1 <= #0 then #0 else "geo" "n" + #1.


  (**
    First, we want to show that the result is always non-negative. Note that
    below we are proving a partial correctness specification, divergence is a
    valid behavior, so the specification just says that the probability that the
    program terminates in a value that is negative is zero
   *)

  Lemma geo_nonneg :
    {{{ True }}} geometric #() {{{ m, RET #m; ⌜0 <= m⌝%Z }}}.
  Proof.
    iLöb as "IH".
    iIntros (Φ) "_ HΦ".
    wp_lam.
    wp_bind (rand _)%E.
    iApply wp_rand_nat; auto.
    iModIntro.
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

  (**
     We can use the specification above to reason about the probability that
     the program returns a strictly positive result. Again, in a partial correctness
     logic, the only thing we can actually prove is that the probability that
     the program returns 0 or less is (1/2)
   *)

  Lemma geo_gt0 :
    {{{ ↯(/(1+1)) }}} geometric #() {{{ m, RET #m; ⌜0 < m⌝%Z }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    wp_lam.
    wp_bind (rand _)%E.
    iApply (wp_rand_err_nat _ _ 0).
    iFrame.
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
  Qed.


  (**
     Similarly, we can prove that the probability that the program does not
     return 0 or less is (1/2).
  *)

  Lemma geo_le0 :
    {{{ ↯(/(1+1)) }}} geometric #() {{{ m, RET #m; ⌜m <= 0⌝%Z }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    wp_lam.
    wp_bind (rand _)%E.
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

  (**
      Note that the two specifications together still do not say anything about
      termination behavior of the geometric process. A program that diverges
      with probability 1 will satisfy all of the specifications as well. Eris
      supports as well total correctness specifications that allow us to reason
      about termination. However, let's keep this aside for now, and just reason
      about partial correctness.

      We can try to prove some properties about ranges of outputs, e.g. the
      probability that the geometric does not return a result equal to or less
      than 1 is (1/4)
  *)

  Lemma geo_le1 :
    {{{ ↯(1/4) }}} geometric #() {{{ m, RET #m; ⌜m <= 1⌝%Z }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    wp_lam.
    wp_bind (rand _)%E.
    set (F (n:nat) := if bool_decide (n=0) then 0%R else (/(1+1)%R)).
    iApply (wp_rand_exp_nat 1 _ _ F with "Herr").
    - intro n.
      rewrite /F.
      real_solver.
    - rewrite SeriesC_nat_bounded_to_foldr /F /=.
      lra.
    - iIntros (n) "(%Hn & Herr)".
      rewrite /F.
      inversion Hn as [|m].
      + do 2 wp_pure.
        simpl.
        wp_bind (geometric #()).
        iApply (geo_le0 with "[Herr]"); auto.
        iModIntro.
        iIntros (m) "%Hm".
        wp_pures.
        iApply "HΦ".
        iPureIntro.
        lia.
      + assert (n=0) as -> by lia.
        simpl.
        wp_pures.
        iApply "HΦ".
        iPureIntro.
        lia.
  Qed.

  (**
     Let us now try to generalize these results. It is well-known that the
     mass of the tails of such a geometric, i.e. the probability of sampling
     larger than n is (1/2^(n+1)). Below we write a definition for this
     probability.
   *)

  Definition geo_tail_mass (n : nat) := (1/ 2^(n+1))%R.


  (**
     We write some lemmas to work with this construct.
   *)

  Lemma geo_tail_mass_0  :
    geo_tail_mass 0 = (/(1+1))%R.
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
    (1 / 2 * geo_tail_mass m = geo_tail_mass (S m))%R.
  Proof.
    unfold geo_tail_mass.
    simpl.
    rewrite Rdiv_mult_distr.
    lra.
  Qed.


  (**

   Let us now prove a specification about the mass of the tails of the
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
      simpl.
      rewrite geo_tail_mass_0.
      iApply (geo_le0 with "[Herr]"); auto.
    - iIntros (Φ) "Herr HΦ".
      simpl.
      wp_lam.
      (**
         We now get to the main part of the proof. Here we need to split
         error credits depending on whether the result of the sampling is
         0 or 1
       *)
      set (F (n:nat) := if bool_decide (n=0)
                      then 0%R
                      else geo_tail_mass m %R).
      wp_bind (rand _)%E.
      iApply (wp_rand_exp_nat 1 _ _ F with "Herr").
      + intro n.
        rewrite /F.
        case_bool_decide; [real_solver|].
        apply geo_tail_mass_bounded.
      + rewrite SeriesC_nat_bounded_to_foldr.
        unfold F.
        simpl.
        rewrite geo_tail_mass_S.
        lra.
      + iIntros (n) "(%Hn & Herr)".
        rewrite /F.
        inversion Hn as [|k].
        * do 2 wp_pure.
          simpl.
          wp_bind (geometric #()).
          wp_apply ("IH" with "Herr"); auto.
          iIntros (l) "%Hl".
          wp_pures.
          iApply "HΦ".
          iPureIntro.
          lia.
        * assert (n=0) as -> by lia.
          simpl.
          wp_pures.
          iApply "HΦ".
          iPureIntro.
          lia.
  Qed.

  Lemma geo_gt1 :
    {{{ ↯(3/4) }}} geometric #() {{{ m, RET #m; ⌜1 < m⌝%Z }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    wp_lam.
    wp_bind (rand _)%E.
    set (F (n:nat) := if bool_decide (n=0) then 1%R else (/(1+1)%R)).
    iApply (wp_rand_exp_nat 1 _ _ F with "Herr").
    - intro n.
      rewrite /F.
      real_solver.
    - rewrite SeriesC_nat_bounded_to_foldr /F /=.
      lra.
    - iIntros (n) "(%Hn & Herr)".
      rewrite /F.
      inversion Hn as [|m].
      + do 2 wp_pure.
        simpl.
        wp_bind (geometric #()).
        iApply (geo_gt0 with "[Herr]"); auto.
        iModIntro.
        iIntros (m) "%Hm".
        wp_pures.
        iApply "HΦ".
        iPureIntro.
        lia.
      + assert (n=0) as -> by lia.
        simpl.
        iExFalso.
        by iApply (ec_contradict with "Herr").
  Qed.


End geometric.
