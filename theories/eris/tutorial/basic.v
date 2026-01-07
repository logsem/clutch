From clutch.eris Require Import eris tutorial.eris_rules.
From clutch.eris.tutorial Require Import eris_rules.

(* ###################################################################### *)
(** * Separation logic in Rocq*)

(** In this chapter, we introduce the basic separation logic facilities of Eris.
    By virtue of building on Iris, Eris inherits a lot of technical machinery
    and many concepts are directly transferrable

    The core Iris separation logic framework is parameterized by the type of
    ghost state that is needed to carry out a proof. This manifest in the
    Rocq-level type of propositions in Iris, [iProp Σ], that is indexed by a [Σ]
    of type [gFunctors]. To make our proofs generic, we typically abstract over
    any such [Σ] and use type classes to ensure that the necessary constructions
    are present in [Σ]. For this tutorial, however, we will not be concerned
    with these matters–we will just assume some [Σ] is in scope. *)
Section separation_logic_introduction.
Context {Σ : gFunctors}.

(** The theorems we can prove in Iris have the form [P ⊢ Q] (type \vdash),
    saying that the separation logic assertion [P] implies the assertion [Q].

    Iris is built on top of Rocq and has a custom interface called the Iris
    Proof Mode (IPM). IPM has its own versions of many Rocq tactics, which
    maintain a new context, called the spatial context, in addition to the usual
    Rocq-level context. goal.

    The regular Rocq tactics can still be used when we work within the
    non-spatial context, but, in general, we shall use the new tactics that work
    natively with the spatial context. These new tactics start with 'i', and
    since many of them simply 'lift' the regular tactics to also work with the
    spatial context, they borrow the regular names but with the 'i' prefixed.
    For instance, the tactic [intros H] becomes [iIntros "H"], and instead of
    [apply H] we use [iApply "H"]. For technical reasons, identifiers for
    hypotheses in the spatial context are strings

    Let us start by provin prove the statement [P ⊢ P], for all [P]. *)
Lemma asm (P : iProp Σ) : P ⊢ P.
Proof.
  (** We start by introducing [P]. *)
  iIntros "H".
  (** This adds [P] to the spatial context with the identifier ["H"] and we are
      left with the goal [P]. In a typical Rocq proof, we would continue by
      either [exact] or [apply]. In Iris, we use either [iExact] or [iApply]. *)
  iApply "H".
Qed.

(** Iris propositions include many of the usual logical connectives such as
    conjunction [P ∧ Q] (type \and). As such, Iris uses a notation scope to
    overload the usual logical notation in Rocq. This scope is delimited by [I]
    and bound to [iProp Σ]. *)
Fail Definition and_fail (P Q : iProp Σ) := P ∧ Q.
Definition and_success (P Q : iProp Σ) := (P ∧ Q)%I.
Definition and_success' (P Q : iProp Σ) : iProp Σ := P ∧ Q.

(* ================================================================= *)
(** ** Separation Logic Connectives *)

(** The core connective in separation logic is the `separating conjunction',
    written [P ∗ Q] (type \sep or \star), for propositions [P] and [Q].
    Separating conjunction differs from regular conjunction, particularly in its
    introduction rule:

      P1 ⊢ Q1        P2 ⊢ Q2
      ----------------------
        P1 ∗ P2 ⊢ Q1 ∗ Q2

    That is, if we want to prove [Q1 ∗ Q2], we must decide which of our owned
    resources we use to prove [Q1] and which we use to prove [Q2]. To see this
    in action, let us prove that separating conjunction is commutative. *)
Lemma sep_comm (P Q : iProp Σ) : P ∗ Q ⊢ Q ∗ P.
Proof.
  iIntros "H".
  (** To eliminate a separating conjunction we use the tactic [iDestruct] with
      the usual destruction pattern. *)
  iDestruct "H" as "[HP HQ]".
  (** Alternatively, we can introduce and destruct resources simultaneously. *)
  (* Restart. iIntros "[HP HQ]" *)

  (** Unlike [∧], the separating conjunction [∗] is not idempotent. That is,
      there are Iris propositions for which [P ⊢ P ∗ P] is not the case. Because
      of this, it is generally not possible to use [iSplit] to introduce [∗].
      The [iSplit] tactic would duplicate the spatial context and is therefore
      not available when the context is non-empty. *)
  Fail iSplit.
  (** Instead, Iris introduces the tactics [iSplitL] and [iSplitR] that allow
      you to specify how you want to separate your resources to prove each
      subgoal. The hypotheses mentioned by [iSplitL] are given to the left
      subgoal, and the remaining to the right. Conversely for [iSplitR]. *)
  iSplitL "HQ".
  - iApply "HQ".
  - iApply "HP".
Qed.

(** Separating conjunction has an analogue to implication which, instead of
    introducing the antecedent to the assumptions with conjunction, introduces
    it with separating conjunction. This connective is written as [P -∗ Q] and
    pronounced `magic wand' or simply `wand'. *)
Lemma modus_ponens (P Q : iProp Σ) : ⊢ P -∗ (P -∗ Q) -∗ Q.
Proof.
  (* exercise *)
Admitted.

(** Just as with Rocq tactics, Iris supports complex nested introduction and
    destruction patterns. For example, you can use a pattern like [(H1 & .. & H2
    & H3)] as a shorthand for [[H1 .. [H2 H3] ..]].

    Exercise: use an introduction pattern of with parentheses to prove
    associativity of [∗]. Note that [∗] is right-associative, so [P ∗ Q ∗ R] is
    parsed as [P ∗ (Q ∗ R)]. *)
(* *)
Lemma sep_assoc_1 (P Q R : iProp Σ) : P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R.
Proof.
  (* exercise *)
Admitted.

(** Manually splitting separating conjunctions quickly becomes tedious. To
    alleviate this, the [iFrame] tactic automatically pairs up hypotheses with
    conjuncts in the goal separation sequence. *)
Lemma sep_comm_v2 (P Q : iProp Σ) : P ∗ Q ⊢ Q ∗ P.
Proof.
  iIntros "H".
  iDestruct "H" as "[HP HQ]".
  iFrame.
Qed.

(** For assertions with multiple assumptions, i.e. nested magic wands, it is
    often necessary specify which part of the context should go where. This is
    done using [iApply ("H" with "[H1 H2 H3] [H4 H5]")]. Each set of square
    brackets specifies the part of the context going to that argument.

    Let's try it out. *)
Lemma wand_adj_1 (P Q R : iProp Σ) : (P -∗ Q -∗ R) ∗ P ∗ Q ⊢ R.
Proof.
  iIntros "H".
  iDestruct "H" as "(H & HP & HQ)".
  (** When applying ["H"], we get the subgoals [P] and [Q]. To specify that
      we want to use ["HP"] to prove the first subgoal, and ["HQ"] the second,
      we add ["HP"] in the first square bracket, and ["HQ"] in the second. *)
  iApply ("H" with "[HP] [HQ]").
  - iApply "HP".
  - iApply "HQ".
Qed.

(** Hypotheses that fit arguments exactly can be supplied directly without a
    square bracket to avoid trivial subgoals, as in the above. Try this in the
    following exercise. *)
Lemma wand_adj (P Q R : iProp Σ) : (P -∗ Q -∗ R) ⊢ (P ∗ Q -∗ R).
Proof.
  (* exercise *)
Admitted.

(** Disjunctions [∨] are treated just like disjunctions in Rocq. The
    introduction pattern [[ _ | _ ]] allows us to eliminate a disjunction, while
    the tactics [iLeft] and [iRight] let us introduce them.

    Prove that disjunction commutes. *)
Lemma or_comm (P Q : iProp Σ) : Q ∨ P ⊢ P ∨ Q.
Proof.
  (* exercise *)
Admitted.

(** We can even prove the usual elimination rule for or-elimination written with
    separation. This version is, however, not very useful, as it does not allow
    the two cases to share resources. *)
Lemma or_elim (P Q R : iProp Σ) : ⊢ (P -∗ R) -∗ (Q -∗ R) -∗ P ∨ Q -∗ R.
Proof.
  (* exercise *)
Admitted.

(** Separating conjunction distributes over disjunction (for the same reason as
    ordinary conjunction). *)
Lemma sep_or_distr_1 (P Q R : iProp Σ) : P ∗ (Q ∨ R) ⊢ P ∗ Q ∨ P ∗ R.
Proof.
  (* exercise *)
Admitted.

Lemma sep_or_distr_2 (P Q R : iProp Σ) : P ∗ Q ∨ P ∗ R ⊢ P ∗ (Q ∨ R) .
Proof.
  (* exercise *)
Admitted.

(** Iris propositions can be existentialy and universally quantified over any
    Rocq type. Existential quantifiers are proved using the [iExists] tactic,
    using the same syntax as for [exists]. Elimination of existentials is done
    through the pattern ["[%x Hx]"] or as part of a ["(_ & .. & _)"] with a [%]
    in front of the existential variable. (type \exists). *)
Lemma sep_ex_distr {A} (P : iProp Σ) (Φ : A → iProp Σ) :
  (P ∗ ∃ x, Φ x) ⊣⊢ ∃ x, P ∗ Φ x.
Proof.
  iSplit.
  - iIntros "H".
    iDestruct "H" as "(HP & HΦ)".
    iDestruct "HΦ" as "(%x & HΦ)".
    iExists x.
    iFrame.
  - (* exercise *)
Admitted.

(** Likewise, universal quantification works almost as in Rocq. To introduce a
    universal qunatifier, you can either use [iIntros (x y z)] or [iIntros "%x
    %y %z"]. These patterns are interchangeable. To specify the parameters of
    hypotheses, we write [iApply ("H" $! x y z)]. (type \forall) *)
Lemma sep_all_distr {A} (P Q : A → iProp Σ) :
  ⊢ (∀ x, P x) ∗ (∀ x, Q x) -∗ (∀ x, P x ∗ Q x).
Proof.
  (* exercise *)
Admitted.

(** More useful introduction and elmination patterns can be found in the Iris
    documentation at

    <<https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md?ref_type=heads#introduction-patterns-ipat>>
*)

End separation_logic_introduction.


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
    { lra. }
    { lra. }
    iExact "H".
  Qed.

  (** Similarly, error credits can be combined. *)
  Lemma error_credit_combine :
    ↯ (1/4) ∗ ↯ (1/4) ⊢ ↯ (1/2).
  Proof.
    iIntros "[H1 H2]".
    iDestruct (ec_combine with "[H1 H2]") as "H".
    { iFrame. }
    assert (1/4 + 1/4 = 1/2)%R as -> by lra.
    iExact "H".
  Qed.

  (** Interestingly, if we own [↯ ε] and [1 <= ε] then we can prove [False]! *)
  Lemma error_credit_False ε :
    (1 <= ε)%R →
    ↯ ε ⊢ False.
  Proof.
    intros Hr.
    iApply ec_contradict.
    exact Hr.
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
      with to either [0] or [1]. *)

  Lemma coin_flip :
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
    wp_apply wp_rand_nat.
    iIntros (n) "%Hn".
    iApply "HΦ".
    iPureIntro.
    lia.
  Qed.

  (** Let's try another example: The expression [rand #2] samples uniformly from
      the set [{0, 1, 2}]. The program therefore returns [false] with probability
      [1/3], and [true] with probability [2/3]. *)
  Definition unif_3_eq : expr :=
    if: rand #2 = #0 then #false else #true.

  (** Let's write a spec using error credits that captures this idea. *)
  Lemma unif_3_spec :
    {{{ ↯ (1 / 3) }}} unif_3_eq {{{ RET #true; True }}}.
  Proof.
    iIntros (Φ) "Hε HΦ".
    unfold unif_3_eq.
    wp_apply (wp_rand_err_nat 0%nat with "[Hε]").
    { iApply (ec_eq with "Hε"). simpl. lra. }
    iIntros (x) "[% %]".
    wp_binop.
    rewrite bool_decide_eq_false_2; last first.
    { inversion 1. lia. }
    wp_if.
    iModIntro.
    iApply "HΦ".
    trivial.
  Qed.

  (* TODO(SG): give som more intuition for what we just proved *)
  (* TODO(SG): advanced composition *)
  (* TODO(SG): Somethings with functional lists, induction? *)

End eris_introduction.
