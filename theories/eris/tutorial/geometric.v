From clutch.eris Require Import eris tutorial.eris_rules.
From clutch.eris.tutorial Require Import eris_rules.

(* ###################################################################### *)
(** * Geometric distribution *)

Section geometric.
  Context `{!erisGS Σ}.

  (** In this example we will prove some properties about the geometric
      distribution. The program below simulates a geometric process with
      parameter [1/3]. On every step it generates a random bit, and it returns
      the number of failed attempts before returning [0] *)

  Definition geometric : val :=
    rec: "geo" "n" :=
      if: rand #2 = #0 then #0 else "geo" "n" + #1.

  (** First, we want to show that the result is always non-negative. Note that
      below we are proving a partial correctness specification, divergence is a
      valid behavior, so the specification just says that the probability that
      the program terminates in a value that is negative is zero *)

  Lemma geo_nonneg :
    {{{ True }}} geometric #() {{{ m, RET #m; ⌜0 ≤ m⌝%Z }}}.
  Proof.
    iLöb as "IH".
    iIntros (Φ) "_ HΦ".
    wp_lam.
    wp_apply wp_rand.
    iIntros (n) "%Hn".
    destruct n.
    - wp_pures.
      iModIntro.
      by iApply ("HΦ").
    - do 2 wp_pure.
      wp_apply "IH".
      { done. }
      iIntros (m) "%Hm".
      wp_pures.
      iApply "HΦ".
      iPureIntro.
      nat_solver.
  Qed.

  (** We can use the specification above to reason about the probability that
      the program returns a strictly positive result. Again, in a partial
      correctness logic, the only thing we can actually prove is that the
      probability that the program returns 0 or less is (2/3). *)
  Lemma geo_gt0 :
    {{{ ↯ (1/3) }}} geometric #() {{{ m, RET #m; ⌜0 < m⌝%Z }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    wp_lam.
    wp_bind (rand _)%E.
    (** Since we only want to avoid one single outcome, we can use [wp_rand_err]
        and spend the error credit to ensure we do not get 0 *)
    wp_apply (wp_rand_err 0 2 with "[Herr]").
    { iApply (ec_eq with "Herr").
      real_solver. }
    (* exercise *)
    (* Admitted. *)

    (* Sample solution: *)
    iIntros (n) "(%Hn1 & %Hn2)".
    destruct n; [done|].
    do 2 wp_pure.
    wp_apply geo_nonneg.
    { done. }
    iIntros (m) "%Hm".
    wp_pures.
    iApply "HΦ".
    iPureIntro.
    nat_solver.
  Qed.


  (** Similarly, we can prove that the probability that the program does not
      return 0 or less is (1/3). However this case needs us to reject all
      cases where we sample 1 or more.
   *)
  Lemma geo_le0 :
    {{{ ↯ (2/3) }}} geometric #() {{{ m, RET #m; ⌜m <= 0⌝%Z }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    wp_lam.
    wp_bind (rand _)%E.
    (* exercise *)
    (* Admitted. *)

    (* Sample solution: *)
    set (F n := if bool_decide (n = 0) then 0 else 1).
    wp_apply (wp_rand_exp F with "Herr").
    { unfold F. real_solver. }
    { unfold F. simpl. real_solver. }
    iIntros (n) "(%Hn1 & Herr)".
    destruct n.
    - simpl.
      wp_pures.
      iApply "HΦ".
      done.
    - simpl.
      iExFalso.
      iApply (ec_contradict with "Herr").
      real_solver.
  Qed.

  (** Note that the two specifications together still do not say anything about
      termination behavior of the geometric process. A program that diverges
      with probability 1 will satisfy all of the specifications as well. Eris
      supports as well total correctness specifications that allow us to reason
      about termination. However, let's keep this aside for now, and just reason
      about partial correctness.

      We can try to prove some properties about ranges of outputs, e.g. the
      probability that the geometric does not return a result equal to or less
      than 1 is (2/3)*(2/3) = (4/9) *)

  Lemma geo_le1 :
    {{{ ↯ (4/9) }}} geometric #() {{{ m, RET #m; ⌜m <= 1⌝%Z }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    wp_lam.
    wp_bind (rand _)%E.

    (** At this point, we do not have enough error credits to outright reject
        one outcome. Instead, we have to distribute error credits across the
        outcomes of [rand #1]. Note that in the case v=0, we can immediately
        prove the postcondition, since 0 <= 1. That branch then needs 0 error
        credits. Therefore, we can give all other credits to the other branch
        By a simple calculation, we get that we can give ↯(2/3) to each branch. *)

    set (F (n:nat) := if bool_decide (n=0) then 0%R else (2/3)%R).
    wp_apply (wp_rand_exp F 2 with "Herr").
    { intro n.
      unfold F.
      real_solver. }
    { unfold F.
      simpl.
      real_solver. }
    iIntros (n) "(%Hn & Herr)".
    unfold F.
    (** We do a case distinction on whether n = 0 *)
    destruct n.
    - simpl.
      wp_pures.
      iApply "HΦ".
      iPureIntro.
      nat_solver.
    - simpl.
      wp_pures.
      (** In the case [n >= 1], we execute the program until the recursive call *)
      (** We now have [↯ (2/3)] and we have to compute [geometric #() + #1].
            In order for the result to be less than [1], geometric must return
            [0] (or less). We will spend our error credits to use [geo_le0]. *)
      wp_bind (geometric #()).
      wp_apply (geo_le0 with "Herr").
      iIntros (m) "%Hm".
      wp_pures.
      iApply "HΦ".
      iPureIntro.
      nat_solver.
  Qed.

  (** Let us now try to generalize these results. It is well-known that the mass
      of the tails of such a geometric, i.e. the probability of sampling larger
      than [n] is [2^(n+1) / 3^(n + 1)]. *)
  Definition geo_tail_mass (n : nat) := (2^(n+1) / 3^(n + 1))%R.

  (** We will need some mathematical facts about this function. *)
  Lemma geo_tail_mass_0 :
    geo_tail_mass 0 = (2/3)%R.
  Proof.
    unfold geo_tail_mass.
    simpl.
    real_solver.
  Qed.

  Lemma geo_tail_mass_bounded (m : nat) :
    (0 <= geo_tail_mass m <= 1)%R.
  Proof.
    unfold geo_tail_mass.
    split.
    - left.
      apply Rdiv_lt_0_compat; real_solver.
    - rewrite <- Rcomplements.Rdiv_le_1.
      + apply pow_incr.
        real_solver.
      + apply pow_lt.
        real_solver.
  Qed.

  Lemma geo_tail_mass_S (m : nat) :
    (geo_tail_mass (S m) = (2/3) * geo_tail_mass m)%R.
  Proof.
    unfold geo_tail_mass.
    simpl.
    rewrite Rdiv_mult_distr.
    real_solver.
  Qed.

  (** Let us now prove a specification about the mass of the tails of the
      geometric process. Namely, we will show that the probability that the
      output is not larger than [n] is less than [geo_tail_mass n] for every
      [n]. The proof goes by induction on [n], and uses the specifications and
      lemmas we introduced above. *)
  Lemma geo_le_n (n : nat) :
    {{{ ↯ (geo_tail_mass n) }}} geometric #() {{{ m, RET #m; ⌜m <= n⌝%Z }}}.
  Proof.
    iInduction (n) as [|m] "IH".
    - iIntros (Φ) "Herr HΦ".
      rewrite geo_tail_mass_0.
      wp_apply (geo_le0 with "Herr").
      done.
    - iIntros (Φ) "Herr HΦ".
      wp_lam.

      (** We now get to the main part of the proof. Here we need to split error
          credits depending on whether the result of the sampling is 0 or >= 1.
          Luckily, we already defined an abstraction over the credit arithmetic
          to simplify this task. *)

      (* exercise *)
      (* Admitted. *)

      (* Sample solution: *)
      set (F (n : nat) := if bool_decide (n = 0) then 0%R else geo_tail_mass m).
      wp_bind (rand _)%E.
      wp_apply (wp_rand_exp F 2 with "Herr").
      { intro n.
        unfold F.
        case_bool_decide.
        { real_solver. }
        apply geo_tail_mass_bounded. }
      { unfold F.
        simpl.
        rewrite geo_tail_mass_S.
        real_solver. }
      iIntros (n) "(%Hn & Herr)".
      unfold F.
      destruct n.
      + wp_pures.
        simpl.
        iApply "HΦ".
        iPureIntro.
        nat_solver.
      + wp_pures.
        wp_apply ("IH" with "Herr").
        iIntros (l) "%Hl".
        wp_pures.
        iApply "HΦ".
        iPureIntro.
        nat_solver.
  Qed.


End geometric.
