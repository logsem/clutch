From clutch.eris Require Import eris tutorial.eris_rules.
From clutch.eris.tutorial Require Import eris_rules basic.

(* ###################################################################### *)
(** * Eris *)

(** Now we have enough basic separation logic under our belt to do what we're
    actually here for: verify probabilistic programs! *)

Section eris_introduction.
  (** As before, we assume some [Σ] .. *)
  Context {Σ : gFunctors}.

  (** ... but we also assume [Σ] contains whatever Eris needs. The details will
      not be important. *)
  Context {Heris : erisGS Σ}.

  (** Eris is a separation logic that can be used to specify and reason about
      stateful probabilistic programs.

      The Eris separation logic has two core concepts:

      1. Error credits [↯ ε], and
      2. Hoares triple [{{{ P }}} e {{{ v, Q v }}}].

      that we will use to reason about said programs. *)

  (** An error credit is separation logic resource, written [↯ ε], where [ε] is
      (non-negative) real number. Error credits can be split additively. *)
  Lemma error_credit_split :
    ↯ (1/4 + 1/4) ⊢ ↯ (1/4) ∗ ↯ (1/4).
  Proof.
    iIntros "H".
    (** The [ec_split] lemma tells us that [↯ (n + m)] can be split into [↯ n]
        and [↯ m] as long as [0 <= n] and [0 <= m]. We apply it directly. *)
    iApply ec_split.
    { real_solver. }
    { real_solver. }
    iApply "H".
  Qed.

  (** Similarly, error credits can be combined. *)
  Lemma error_credit_combine :
    ↯ (1/4) ∗ ↯ (1/4) ⊢ ↯ (1/2).
  Proof.
    iIntros "[H1 H2]".
    iDestruct (ec_combine with "[H1 H2]") as "H".
    { iFrame. }
    assert (1/4 + 1/4 = 1/2)%R as -> by real_solver.
    iApply "H".
  Qed.

  (** Interestingly, if we own [↯ ε] and [1 <= ε] then we can prove [False]! *)
  Lemma error_credit_False ε :
    (1 <= ε)%R →
    ↯ ε ⊢ False.
  Proof.
    intros Hr.
    iApply ec_contradict.
    apply Hr.
  Qed.

  (** If we can combine enough error credits to get above 1, any conclusion follows. *)
  Lemma error_credit_accumulate P Q :
    ↯ (2/3) ∗ (P -∗ ↯ (1/2)) -∗ P -∗ Q.
  Proof.
    (* exercise *)
    (* 1. Introduce the error credits and the assumption that [P] gives us half a credit, and [P]. *)
    (* 2. Use forward-reasoning to get the error credits out of the implication. *)
    (* 3. Combine the credits. *)
    (* 4. Derive a contradiction *)
    (* Admitted. *)


    (* Sample solution: *)
    iIntros "(err1 & Perr) HP".
    iDestruct ("Perr" with "HP") as "err2".
    iDestruct (ec_combine with "[err1 err2]") as "err".
    - iFrame.
    - iApply falso_seq.
      iSplitL.
      + iApply "err".
      + iApply error_credit_False.
        real_solver.
  Qed.

  (** We use Hoares triples to specify programs. Intuitively, a Hoare triple

        {{{ P }}} e {{{ v, Q v }}}

      usually means that, if [P] holds, and [e] terminates in a value [v],
      then the postconidtion [Q v] holds. Here both the precondition [P] and the
      postcondition [Q v] are arbitrary separation logic propositions.

      However, in Eris, we also have error credits that can be spent to prove
      "wrong" things. Intuitively, an Eris Hoare triple

        {{{ ↯ ε }}} e {{{ v, Q v }}}

      means that probability of [e] terminating in a value [v] that *does not*
      satisfy [Q], is at most [ε]. This may seem somewhat counterintutive but
      will be clearer in just a moment. *)

  (** The programming language [ProbLang] we consider in this tutorial has a
      single probabilistic connective [rand #N]. The expression [rand #N]
      evalautes uniformly at random to a value in the set [{0, 1, ..., N}]. For
      example, the expression [rand #1] corresponds to a coin flip, reducing
      with probability [1/2] to either [0] or [1]. *)

  Lemma wp_coin_flip :
    {{{ True }}} rand #1 {{{ (n : nat), RET #n; ⌜n = 0 ∨ n = 1⌝ }}}.
  Proof.
    (** Under the hood, Hoare triples in Eris are defined in terms of weakest
        precondition connectives.

        The triple [ {{{ P }}} e {{{ RET v, Q }}} ] is syntactic sugar for:

            ∀ Φ, P -∗ (Q -∗ Φ v) -∗ WP e {{ v, Φ v }}

        which is logically equivalent to [ P -∗ WP e {{ x, x = v ∗ Q }} ]

        Hoare triples are not more difficult to prove, but usually easier to use
        in other proofs, because the post-condition does not have to
        syntactically match [Q]. Using this way of stating specifications, the
        consequence and framing rule is implicitly applied in the
        post-condition. *)
    iIntros "%Φ HP HΦ".
    wp_apply wp_rand.
    iIntros (n) "%Hn".
    iApply "HΦ".
    iPureIntro.
    nat_solver.
  Qed.

  (** Let's try another example: The expression [rand #2] samples uniformly from
      the set [{0, 1, 2}]. The program therefore returns [false] with probability
      [1/3], and [true] with probability [2/3]. *)
  Definition unif_3_eq : expr :=
    if: rand #2 = #0 then #false else #true.

  (** Let's write a spec using error credits that captures this idea. *)
  Lemma wp_unif_3 :
    {{{ ↯ (1 / 3) }}} unif_3_eq {{{ (b : bool), RET #b; ⌜b = true⌝ }}}.
  Proof.
    iIntros (Φ) "Hε HΦ".
    unfold unif_3_eq.
    (** Here we apply [wp_rand_err] that allows us "spend" [1 / (N + 1)] error
        credits to avoid a concrete outcome in the range [0..N]. We choose [0]
        to be the outcome we want to avoid. *)
    wp_apply (wp_rand_err 0 with "[Hε]").
    { iApply (ec_eq with "Hε"). simpl. real_solver. }
    iIntros (x) "[% %]".
    (** the [wp_pures] tactic progresses the proof by stepping through pure
        evaluations steps such as equality tests *)
    wp_pures.
    rewrite bool_decide_eq_false_2; last first.
    { inversion 1. nat_solver. }
    wp_pures.
    (** The update modality allows us to update ghost resources—we won't need
        this here and will just introduce it using the [iModIntro] tactic. *)
    iModIntro.
    iApply "HΦ".
    done.
  Qed.

  (** For proving tight bounds, [wp_rand_err] is not always enough.  *)
  Definition twoflip : expr :=
    if: rand #1 = #1 then #true
    else
      if: rand #1 = #1 then #true
      else #false.

  (** Notice how in the [twoflip] program, the program returns [false] with
      probability [1/4]. However, to "avoid" this erroneous outcome, we need
      [1/2] error credits. As such, we need to "scale" the initial error budget
      using expectation-preserving composition via [wp_rand_exp] *)
  Lemma wp_twoflip :
    {{{ ↯ (1 / 4) }}} twoflip {{{ (b : bool), RET #b; ⌜b = true⌝ }}}.
  Proof.
    iIntros (Φ) "Hε HΦ".
    unfold twoflip.
    set (F (n : nat) := if bool_decide (n = 1) then 0%R else (1/2)%R).
    wp_apply (wp_rand_exp F with "Hε").
    { intros n. unfold F. real_solver. }
    { unfold F. simpl. real_solver. }
    iIntros (n) "[%Hn Hε]".
    wp_pures.
    case_bool_decide; simplify_eq.
    - wp_pures.
      iApply "HΦ".
      done.
    - unfold F.
      rewrite bool_decide_eq_false_2; last first.
      { intros ->. done. }
      (** Now we have [1 / 2] error credits and we progress like in the previous
          example using [wp_rand_err]. *)
      wp_pures.
      wp_apply (wp_rand_err 0 with "[Hε]").
      { iApply (ec_eq with "Hε"). simpl. real_solver. }
      iIntros (m) "[%Hm %Hm']".
      wp_pures.
      assert (m = 1) as -> by nat_solver.
      rewrite bool_decide_eq_true_2; [|done].
      wp_pures.
      iModIntro.
      iApply "HΦ".
      done.
  Qed.

End eris_introduction.
