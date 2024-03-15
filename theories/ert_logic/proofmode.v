From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.

From clutch.prob_lang Require Import lang notation class_instances tactics.
From clutch.prob_lang Require Export wp_tactics.

From clutch.ert_logic Require Import ert_weakestpre lifting ectx_lifting primitive_laws.
From iris.prelude Require Import options.

#[global] Program Instance rel_logic_wptactics_base `{!ertwpG prob_lang Σ} : @GwpTacticsBase Σ unit _ _ wp.
Next Obligation. intros. by apply ert_wp_value. Qed.
Next Obligation. intros. by apply ert_wp_fupd. Qed.
Next Obligation. intros. by apply ert_wp_bind. Qed.

Section proofmode.
  Context `{!ertwpG prob_lang Σ}.

  Lemma tac_wp_pure_later Δ1 Δ2 Δ3 E i K e1 e2 φ n Φ a (x1 x2 : nonnegreal) :
    PureExec φ n e1 e2 →
    φ →
    envs_lookup i Δ1 = Some (false, ⧖ x1) →
    (* We need [n] credits, but they cannot be under [n] laters. The credit resource is of course
       timeless, but that does not mean that [▷^n ⧖ x1 ⊢ ◇ ⧖ x1] in general since of course [▷^n P]
       for isn't timeless for all [n]! So we find the credit resource in Δ1 first, *before* removing
       laters *)
    x1 = (nnreal_nat n + x2)%NNR →
    envs_delete false i false Δ1 = Δ2 →
    MaybeIntoLaterNEnvs n Δ2 Δ3 →
    match envs_app false (Esnoc Enil i (⧖ x2)) Δ3 with
    | Some Δ4 => envs_entails Δ4 (WP (fill K e2) @ a; E {{ Φ }})
    | None => False
    end →
    envs_entails Δ1 (WP (fill K e1) @ a; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ?? Hn Hx1 <- HΔ2.
    simplify_eq.
    destruct (envs_app _ _ _) as [Δ4 |] eqn: HΔ4; [|contradiction].
    intros Hcnt.
    rewrite (envs_lookup_sound Δ1) //.
    rewrite into_laterN_env_sound.
    rewrite envs_app_singleton_sound //.
    iIntros "/= [[Hn Hx2] HΔ4]".
    pose proof @pure_exec_fill.
    iApply wp_pure_step_later; [done|].
    iFrame. iModIntro.
    iApply Hcnt.
    by iApply "HΔ4".
  Qed.

End proofmode.

Tactic Notation "wp_pure" open_constr(efoc) :=
  let solve_credit _ :=
    iAssumptionCore || fail "wp_pure: cannot find credit '⧖ ?'" in
  let decompose_credit :=
    (* Tactics trying to solve the goal that says we have enough credits.  The current tactic works
       when the credit has the shape [⧖ (nnreal_nat (S n))]. Other patterns could probably be useful. *)
    (rewrite {1}[nnreal_nat _]/= {1}nnreal_nat_Sn) in
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      let e := eval simpl in e in
      reshape_expr e ltac:(fun K e' =>
        unify e' efoc;
        eapply (tac_wp_pure_later _ _ _ _ _ K e' _ _ _ _ _);
        [(* [PureExec φ] *)
          tc_solve
        | (* φ *)
          try solve_vals_compare_safe
        | (* credit resource *)
          solve_credit ()
        | (* try decomposing the credit, leave goal if not able to  *)
          try (by decompose_credit)
        | (* new environment *)
          done
        | (* IntoLaters *)
          tc_solve
        | (* new goal *)
          pm_reduce; wp_finish])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  end.

Tactic Notation "wp_pure" :=
  wp_pure _.

Tactic Notation "wp_pure" :=
  wp_pure _.

Ltac wp_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (wp_pure _; [])
        | wp_finish (* In case wp_pure never ran, make sure we do the usual cleanup. *)
    ].


(** Unlike [wp_pures], the tactics [wp_rec] and [wp_lam] should also reduce
    lambdas/recs that are hidden behind a definition, i.e. they should use
    [AsRecV_recv] as a proper instance instead of a [Hint Extern].

    We achieve this by putting [AsRecV_recv] in the current environment so that it
    can be used as an instance by the typeclass resolution system. We then perform
    the reduction, and finally we clear this new hypothesis. *)
Tactic Notation "wp_rec" :=
  let H := fresh in
  assert (H := AsRecV_recv);
  wp_pure (App _ _);
  clear H.

Tactic Notation "wp_if" := wp_pure (If _ _ _).
Tactic Notation "wp_if_true" := wp_pure (If (LitV (LitBool true)) _ _).
Tactic Notation "wp_if_false" := wp_pure (If (LitV (LitBool false)) _ _).
Tactic Notation "wp_unop" := wp_pure (UnOp _ _).
Tactic Notation "wp_binop" := wp_pure (BinOp _ _ _).
Tactic Notation "wp_op" := wp_unop || wp_binop.
Tactic Notation "wp_lam" := wp_rec.
Tactic Notation "wp_let" := wp_pure (Rec BAnon (BNamed _) _); wp_lam.
Tactic Notation "wp_seq" := wp_pure (Rec BAnon BAnon _); wp_lam.
Tactic Notation "wp_proj" := wp_pure (Fst _) || wp_pure (Snd _).
Tactic Notation "wp_case" := wp_pure (Case _ _ _).
Tactic Notation "wp_match" := wp_case; wp_pure (Rec _ _ _); wp_lam.
Tactic Notation "wp_inj" := wp_pure (InjL _) || wp_pure (InjR _).
Tactic Notation "wp_pair" := wp_pure (Pair _ _).
Tactic Notation "wp_closure" := wp_pure (Rec _ _ _).

Section tests.
  Context `{!ertwpG prob_lang Σ}.

  #[local] Lemma test_wp_pure n :
    {{{ ⧖ (nnreal_nat (S n)) }}} #2 + #2 {{{ RET #4; ⧖ (nnreal_nat n) }}}.
  Proof.
    iIntros (?) "Hx Hp".
    wp_pure.
    by iApply "Hp".
  Qed.

  #[local] Lemma test_wp_pure' :
    {{{ ⧖ (nnreal_nat 1) }}} #2 + #2 {{{ RET #4; True }}}.
  Proof.
    iIntros (?) "Hx Hp".
    wp_pure.
    by iApply "Hp".
  Qed.

  #[local] Lemma test_wp_pures n :
    {{{ ⧖ (nnreal_nat (2 + n)) }}} #2 + #2 + #2 {{{ RET #6; ⧖ (nnreal_nat n) }}}.
  Proof.
    iIntros (?) "Hx Hp".
    wp_pures.
    by iApply "Hp".
  Qed.

  #[local] Lemma test_wp_pures' :
    {{{ ⧖ (nnreal_nat 2) }}} #2 + #2 + #2 {{{ RET #6; ⧖ (nnreal_nat 0) }}}.
  Proof.
    iIntros (?) "Hx Hp".
    wp_pures.
    by iApply "Hp".
  Qed.

End tests.
