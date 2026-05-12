From clutch.eris Require Import eris tutorial.eris_rules.
From clutch.eris.tutorial Require Import eris_rules.

(* ###################################################################### *)
(** * Separation logic in Rocq*)

Section separation_logic_introduction.
Context {Σ : gFunctors}.

(** The theorems we can prove in Iris have the form [P ⊢ Q] (type \vdash),
    saying that the separation logic assertion [P] implies the assertion [Q].

    Iris is built on top of Rocq and has a custom interface called the Iris
    Proof Mode (IPM). IPM has its own versions of many Rocq tactics, which
    maintain a new context, called the spatial context. *)
Lemma asm (P : iProp Σ) : ⊢ P -∗ P.
Proof.
  (** We start by introducing the assumption [P]. *)
  iIntros "H".
  (** This adds [P] to the spatial context with the identifier ["H"] *)
  iApply "H".
Qed.

(* ================================================================= *)
(** ** Separation Logic Connectives *)

(** The core connective in separation logic is the `separating conjunction',
    written [P ∗ Q] (type \sep or \star), for propositions [P] and [Q].
    Separating conjunction differs from regular conjunction, particularly in its
    introduction rule:

      P1 ⊢ Q1        P2 ⊢ Q2
      ----------------------
        P1 ∗ P2 ⊢ Q1 ∗ Q2 *)
Lemma sep_comm (P Q : iProp Σ) : P ∗ Q ⊢ Q ∗ P.
Proof.
  iIntros "H".
  (** To eliminate a separating conjunction we use the tactic [iDestruct] with
      the usual destruction pattern. *)
  iDestruct "H" as "(HP & HQ)".
Abort.

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

(** The [iFrame] tactic automatically pairs up hypotheses with
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
    brackets specifies the part of the context going to that argument. *)
Lemma wand_adj_1 (P Q R : iProp Σ) : (P -∗ Q -∗ R) ∗ P ∗ Q ⊢ R.
Proof.
  iIntros "H".
  iDestruct "H" as "(H & HP & HQ)".
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

(** As usual, from a contradiction, any assertion [P] follows. *)
Lemma ex_falso (P : iProp Σ) : (⌜False⌝) ⊢ P.
Proof.
  iIntros "%contradiction". contradiction.
Qed.

(** In particular, if [P] is contradictory, then [Q] follows from [P]. *)
Lemma falso_seq (P Q : iProp Σ) : (P ∗ (P -∗ ⌜False⌝)) ⊢ Q.
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
  iIntros "[HP HQ] %x".
  iSplitL "HP".
  - iApply ("HP" $! x).
  - (* exercise *)
Admitted.

(** More useful introduction and elmination patterns can be found in the Iris
    documentation at

    <<https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md?ref_type=heads#introduction-patterns-ipat>>
*)

End separation_logic_introduction.
