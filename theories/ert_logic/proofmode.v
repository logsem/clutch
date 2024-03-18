From iris.proofmode Require Import coq_tactics reduction spec_patterns intro_patterns.
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

  Lemma tac_wp_pure_later Δ1 Δ2 Δ3 E i K e1 e2 φ Φ a (x1 x2 : nonnegreal) :
    PureExec φ 1 e1 e2 →
    φ →
    envs_lookup i Δ1 = Some (false, ⧖ x1) →
    (* We need [n] credits, but they cannot be under [n] laters. The credit resource is of course
       timeless, but that does not mean that [▷^n ⧖ x1 ⊢ ◇ ⧖ x1] in general since of course [▷^n P]
       for isn't timeless for all [n]! So we find the credit resource in Δ1 first, *before* removing
       laters *)
    x1 = ((cost e1) + x2)%NNR →
    envs_delete false i false Δ1 = Δ2 →
    MaybeIntoLaterNEnvs 1 Δ2 Δ3 →
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
    rewrite cost_fill. iFrame. iModIntro.
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

Lemma tac_chip `{!ertwpG prob_lang Σ} i j Δ1 Δ2 Δ3 n P :
  envs_lookup i Δ1 = Some (false, ⧖ (nnreal_nat (S n))) →
  envs_simple_replace i false (Esnoc Enil i (⧖ (nnreal_nat n))) Δ1 = Some Δ2 →
  envs_app false (Esnoc Enil j ((⧖ (nnreal_nat 1)))) Δ2 = Some Δ3 →
  envs_entails Δ3 P →
  envs_entails Δ1 P.
Proof.
  rewrite envs_entails_unseal =>/= ??? Hcnt.
  rewrite envs_simple_replace_singleton_sound //.
  rewrite etc_nat_Sn /=.
  rewrite envs_app_singleton_sound //.
  rewrite Hcnt.
  iIntros "[[H1 Hc] HP]".
  replace (nnreal_one) with (nnreal_nat 1); last by apply nnreal_ext.
  iApply ("HP" with "Hc H1").
Qed.

(** Takes [H1 : ⧖ (nnreal_nat (S n))] to [H2 : ⧖ nnreal_one] and [H1 : ⧖ (nnreal_nat n)] *)
Tactic Notation "iChip" constr(H1) "as" constr(H2) :=
  eapply (tac_chip H1 H2);
  [iAssumptionCore || fail "iChip: cannot find credit '⧖ ?'"
  |done|done|].

Tactic Notation "iChip" constr(H1) :=
  let Htmp := iFresh in
  eapply (tac_chip H1 Htmp);
  [iAssumptionCore || fail "iChip: cannot find credit '⧖ ?'"
  |done|done|].

Tactic Notation "iChip" :=
  let Htmp := iFresh in
  eapply (tac_chip _ Htmp);
  [iAssumptionCore || fail "iChip: cannot find credit '⧖ ?'"
  |done|done|].

(** Some very primitive heap tactics  *)
Tactic Notation "wp_alloc" := iChip; wp_apply (wp_alloc with "[$]").
Tactic Notation "wp_load" := iChip; wp_apply (wp_load with "[$]").
Tactic Notation "wp_store" := iChip; wp_apply (wp_store with "[$]").

Section tests.
  #[local] Definition cost1 {Λ} (e : language.expr Λ) := (nnreal_nat 1).
  #[local] Instance Cost1 {Λ} : Costfun Λ.
  Proof.
    unshelve econstructor.
    - exact cost1.
    - eexists nnreal_one ; by intuition auto.
    - auto.
  Defined.

  Context `{!ert_clutchGS Σ Cost1}.


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

  Hint Extern 0 (TCEq nnreal_one _) => rewrite nnreal_nat_1 : typeclass_instances.

  #[local] Lemma test_wp_apply :
    {{{ ⧖ (nnreal_nat 7) }}} let: "x" := ref #42 in "x" <- #43;; !"x" {{{ RET #43; True }}}.
  Proof.
    iIntros (?) "Hc H".
    (* first variant *)
    iChip "Hc" as "H1".
    wp_apply (wp_alloc with "[H1]") => //.
    iIntros (?) "Hl".
    wp_pures.
    (* second variant *)
    iChip "Hc".
    wp_apply (wp_store with "[$]").
    iIntros "Hl".
    wp_pures.
    (* third variant *)
    iChip.
    wp_apply (wp_load with "[$]").
    iIntros "_".
    by iApply "H".
  Qed.

  #[local] Lemma test_wp_heap :
    {{{ ⧖ (nnreal_nat 7) }}} let: "x" := ref #42 in "x" <- #43;; !"x" {{{ RET #43; True }}}.
  Proof.
    iIntros (?) "Hc H".
    wp_alloc ; iIntros (?) "Hl".
    wp_pures.
    wp_store ; iIntros "Hl".
    wp_pures.
    wp_load ; iIntros "Hl".
    by iApply "H".
  Qed.

End tests.


Section tests.

  Fixpoint at_redex {A} (f : expr → A) (e : expr) : option A :=
    let noval (e' : expr) :=
      match e' with Val _ => Some $ f e | _ => at_redex f e' end in
    match e with
    | App e1 e2      =>
        match e2 with
        | (Val v)    => noval e1
        | _          => at_redex f e2
        end
    | UnOp op e      => noval e
    | BinOp op e1 e2 =>
        match e2 with
        | Val v      => noval e1
        | _          => at_redex f e2
        end
    | If e0 e1 e2    => noval e0
    | Pair e1 e2     =>
        match e2 with
        | Val v      => noval e1
        | _          => at_redex f e2
        end
    | Fst e          => noval e
    | Snd e          => noval e
    | InjL e         => noval e
    | InjR e         => noval e
    | Case e0 e1 e2  => noval e0
    | AllocN e1 e2        =>
        match e2 with
        | Val v      => noval e1
        | _          => at_redex f e2
        end

    | Load e         => noval e
    | Store e1 e2    =>
        match e2 with
        | Val v      => noval e1
        | _          => at_redex f e2
        end
    | AllocTape e    => noval e
    | Rand e1 e2     =>
        match e2 with
        | Val v      => noval e1
        | _          => at_redex f e2
        end
    | _              => None
    end.

  Definition cost_app (e : expr) :=
    match e with
    | App _ _ => nnreal_one
    | _ => nnreal_zero
    end.

  Let costapp e := match at_redex cost_app e with None => nnreal_zero | Some r => r end.


  (* Let K e := (let: "x" := e in "x")%E.
     Let e := App (Val $ (λ:"x", "x")%V) (Val #42).
     Set Printing All.
     Eval cbv in f e.
     Eval cbv in f (K e). *)

  #[local] Instance Costapp : Costfun prob_lang.
  Proof.
    unshelve econstructor.
    - apply costapp.
    - eexists nnreal_one. intros [] ; simpl ; try lra.
      all: admit.
    - intros. admit.
  Admitted.

  Context `{!ert_clutchGS Σ Costapp}.


  (* #[local] Lemma test_wp_pure n :
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

     Hint Extern 0 (TCEq nnreal_one _) => rewrite nnreal_nat_1 : typeclass_instances.

     #[local] Lemma test_wp_apply :
       {{{ ⧖ (nnreal_nat 7) }}} let: "x" := ref #42 in "x" <- #43;; !"x" {{{ RET #43; True }}}.
     Proof.
       iIntros (?) "Hc H".
       (* first variant *)
       iChip "Hc" as "H1".
       wp_apply (wp_alloc with "[H1]") => //.
       iIntros (?) "Hl".
       wp_pures.
       (* second variant *)
       iChip "Hc".
       wp_apply (wp_store with "[$]").
       iIntros "Hl".
       wp_pures.
       (* third variant *)
       iChip.
       wp_apply (wp_load with "[$]").
       iIntros "_".
       by iApply "H".
     Qed.

     #[local] Lemma test_wp_heap :
       {{{ ⧖ (nnreal_nat 7) }}} let: "x" := ref #42 in "x" <- #43;; !"x" {{{ RET #43; True }}}.
     Proof.
       iIntros (?) "Hc H".
       wp_alloc ; iIntros (?) "Hl".
       wp_pures.
       wp_store ; iIntros "Hl".
       wp_pures.
       wp_load ; iIntros "Hl".
       by iApply "H".
     Qed. *)

End tests.
