From clutch Require Export clutch lib.flip.
Set Default Proof Using "Type*".

(** If we assume that we can freely pick presampling tapes to read from when
    resolving probabilistic choices, we can show refinements/equivalences that
    do not hold. *)
Section counterexample.
  Context `{!clutchRGS Σ}.

  (** An (unsound) rule that allows us to pick an arbitrary presampling tape
      when resolving the [flip] on the left. *)
  Definition refines_tape_unsound :=
    ∀ K E (A : lrel Σ) α b bs e',
    α ↪B (b :: bs) ∗
    (α ↪B bs -∗  REL fill K (of_val #b) << e' @ E : A)
    ⊢ REL fill K flip << e' @ E : A.

  (** [flip_ors] return [true] with probability 3/4, false with 1/4 *)
  Definition flip_ors : expr :=
    let: "x" := flip in
    let: "y" := flip in
    "x" || "y".

  (** If we assume [refines_tape_unsound], we can show that [flip] refines
      [flip_ors] which obviously cannot true. *)
  Lemma counterexample α1 α2 :
    refines_tape_unsound →
    α1 ↪B [] ∗ α2 ↪B []
    ⊢ REL flip << flip_ors  : lrel_bool.
  Proof.
    iIntros (refines_tape_unsound) "[Hα1 Hα2]". rewrite /flip_ors.
    rel_apply (refines_couple_tape_flip _ _ α1); [done|iFrame].
    iIntros (b1) "Hα1 /=".
    rel_pures_r.
    rel_apply (refines_couple_tape_flip _ _ α2); [done|iFrame].
    iIntros (b2) "Hα2 /=".
    rel_pures_r.
    destruct b1; rel_pures_r.
    - rel_apply (refines_tape_unsound _ _ _ α1).
      iFrame. iIntros "Hα1". rel_values.
    - rel_apply (refines_tape_unsound _ _ _ α2).
      iFrame. iIntros "Hα2". rel_values.
  Qed.

End counterexample.
