From clutch Require Export clutch lib.flip.
Set Default Proof Using "Type*".

(** If we assume that we can freely pick presampling tapes to read from when
    resolving probabilistic choices, we can show refinements/equivalences that
    do not hold. *)
Section counterexample_annotation.
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
  Lemma counterexample_annotation α1 α2 :
    refines_tape_unsound →
    α1 ↪B [] ∗ α2 ↪B []
    ⊢ REL flip << flip_ors  : lrel_bool.
  Proof.
    iIntros (refines_tape_unsound) "[Hα1 Hα2]". rewrite /flip_ors.
    rel_apply (refines_couple_tape_flip _ _ α1); iFrame.
    iIntros (b1) "Hα1 /=".
    rel_pures_r.
    rel_apply (refines_couple_tape_flip _ _ α2); iFrame.
    iIntros (b2) "Hα2 /=".
    rel_pures_r.
    destruct b1; rel_pures_r.
    - rel_apply (refines_tape_unsound _ _ _ α1).
      iFrame. iIntros "Hα1". rel_values.
    - rel_apply (refines_tape_unsound _ _ _ α2).
      iFrame. iIntros "Hα2". rel_values.
  Qed.

End counterexample_annotation.

(** This counterexample shows that prophecy variables (as developed in HeapLang
    and Iris) is unsound for the coupling logic, for the same reason that
    presampling is unsound without syntatic tape labels: If you can predict the
    outcomes of random samples ahead of time, it gives you too much power to
    choose which sampling you couple with. *)
Section counterexample_prophecies.
  Context `{!clutchRGS Σ}.

  (** We assume prophecy variables exist in our language with [WP] specs as
      found in [HeapLang] (see https://dl.acm.org/doi/10.1145/3371113) *)
  Class prophecies := {
      NewProph : val;
      ResolveProph : val;
      proph_id : Set;
      proph : proph_id → list (val * val) → iProp Σ;
      LitProphecy : proph_id → base_lit;

      wp_new_proph s E :
        {{{ True }}}
          NewProph #() @ s; E
        {{{ pvs p, RET (LitV (LitProphecy p)); proph p pvs }}};

     wp_resolve_proph s E (p : proph_id) (pvs : list (val * val)) v :
       {{{ proph p pvs }}}
         ResolveProph (Val $ LitV $ LitProphecy p) (Val v) @ s; E
       {{{ pvs', RET (LitV LitUnit); ⌜pvs = (LitV LitUnit, v)::pvs'⌝ ∗ proph p pvs' }}};
    }.

  (** [flip_ands] returns [true] with probability 1/4, [false] with 3/4 *)
  Definition flip_ands `{prophecies} : expr :=
    let: "p" := NewProph #() in
    let: "x" := flip in
    let: "y" := flip in
    ResolveProph "p" "y";;
    "x" && "y".

  (** We show that [flip_ands] refines [flip] which is not true. *)
  Lemma counterexample_prophecies `{prophecies} :
    ⊢ REL flip_ands << flip : lrel_bool.
  Proof.
    (** As we're assuming regular [WP] specs for the prophecy variables, we'll
        unfold the relational logic and work directly in the unary logic. *)
    rewrite refines_eq /refines_def /=.
    iIntros (K) "Hr Hna". rewrite /flip_ands.
    wp_apply wp_new_proph; [done|].
    iIntros (pvs p) "Hp".
    wp_pures.
    destruct pvs as [|(?&v) ?].
    { (** Contradictory case -- we will resolve the prophecy in the program so
          the list of prophecies is non-empty *)
      wp_apply wp_flip; [done|]; iIntros (b1) "_". wp_pures.
      wp_apply wp_flip; [done|]; iIntros (b2) "_". wp_pures.
      wp_apply (wp_resolve_proph with "Hp").
      iIntros (?) "(% & ?)". simplify_eq. }
    (** Prophecies resolve a priori to any value in the language, but we will
        only resolve it to a Bool in the program *)
    assert ((∃ b : bool, v = #b) ∨ ∀ b : bool, v ≠ #b) as Hcases.
    { destruct v; firstorder. destruct l; firstorder. eauto. }
    destruct Hcases as [Hbool|]; last first.
    { (** Contradictory case -- we *do* resolve the prophecy to a Bool *)
      wp_apply wp_flip; [done|]; iIntros (b1) "_". wp_pures.
      wp_apply wp_flip; [done|]; iIntros (b2) "_". wp_pures.
      wp_apply (wp_resolve_proph with "Hp").
      iIntros (?) "(% & ?)". congruence. }

    (** Now we're in the interesting situation. We case on the Boolean content
        of the prophecy. *)
    destruct Hbool as [[] ->].
    - (** The prophecy was [true], and we do an identity coupling with the
          [flip] of [x]. This guarantees that the result of [x && true] on the
          left agrees with the result of the [flip] on the right. *)
      wp_apply wp_couple_flip_flip.
      iFrame "Hr". iIntros "/= !>" (b) "Hr".
      wp_pures.
      wp_apply wp_flip; [done|]; iIntros (b2) "_". wp_pures.
      wp_apply (wp_resolve_proph with "Hp").
      iIntros (?) "[% Hp]". simplify_eq.
      destruct b; wp_pures;
        iModIntro; iExists _; eauto with iFrame.
    - (** The prophecy is [false], and we do an identity coupling with the
          [flip] of [y]. The result of the left is predetermined to be [x &&
          false = false]. By coupling [y] (that we know will be [false]) with
          the [flip] on the right, we ensure that the right is also [false]. *)
      wp_apply wp_flip; [done|]; iIntros (b1) "_". wp_pures.
      wp_apply wp_couple_flip_flip. iFrame.
      iIntros "/= !>" (b2) "Hr". wp_pures.
      wp_apply (wp_resolve_proph with "Hp").
      iIntros (?) "[% Hp]". simplify_eq. wp_pures.
      destruct b1; wp_pures;
        iModIntro; iExists _; eauto with iFrame.
  Qed.

End counterexample_prophecies.
