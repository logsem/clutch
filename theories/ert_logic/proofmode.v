From iris.proofmode Require Import coq_tactics reduction spec_patterns intro_patterns.
From iris.proofmode Require Export tactics.

From clutch.prob_lang Require Import lang notation class_instances tactics.
From clutch.prob_lang Require Export wp_tactics.

From clutch.ert_logic Require Import ert_weakestpre lifting ectx_lifting primitive_laws cost_models.
From iris.prelude Require Import options.
Set Default Proof Using "Type*".

#[global] Program Instance rel_logic_wptactics_base `{!ertwpG prob_lang Σ} : GwpTacticsBase Σ unit wp.
Next Obligation. intros. by apply ert_wp_value. Qed.
Next Obligation. intros. by apply ert_wp_fupd. Qed.

(** Like in [wp_tactics], but using a [CostLanguageCtx] *)
Class EwpTacticsBind (Σ : gFunctors) (A : Type) (c : Costfun prob_lang) `{!invGS_gen hlc Σ} (gwp : A → coPset → expr → (val → iProp Σ) → iProp Σ)  := {
    wptac_wp_bind K `{!CostLanguageCtx c K} E e Φ a :
      gwp a E e (λ v, gwp a E (K (of_val v)) Φ ) ⊢ gwp a E (K e) Φ ;
}.

Section wp_bind_tactics.
  Context `{EwpTacticsBind Σ A hlc gwp}.

  Local Notation "'WP' e @ s ; E {{ Φ } }" := (gwp s E e%E Φ)
    (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  Local Notation "'WP' e @ s ; E {{ v , Q } }" := (gwp s E e%E (λ v, Q))
    (at level 20, e, Q at level 200,
     format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

  Lemma tac_wp_bind K `{!CostLanguageCtx (Λ := prob_lang) c (fill K)} Δ E Φ e f a :
    f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
    envs_entails Δ (WP e @ a; E {{ v, WP f (Val v) @ a; E {{ Φ }} }})%I →
    envs_entails Δ (WP fill K e @ a; E {{ Φ }}).
  Proof. rewrite envs_entails_unseal=> -> ->. by apply: wptac_wp_bind. Qed.
End wp_bind_tactics.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
          | fail 1 "wp_bind: cannot find" efoc "in" e ]
  end.

Ltac wp_apply_core lem tac_suc tac_fail := first
  [iPoseProofCore lem as false (fun H =>
     lazymatch goal with
     | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
         reshape_expr e ltac:(fun K e' => wp_bind_core K; tac_suc H)
     end)
  |tac_fail ltac:(fun _ => wp_apply_core lem tac_suc tac_fail)
  |let P := type of lem in
   fail "wp_apply: cannot apply" lem ":" P ].

Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
                    ltac:(fun cont => fail).
Tactic Notation "wp_smart_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
                    ltac:(fun cont => wp_pure _; []; cont ()).

#[global] Program Instance ert_wptactics_bind `{!ertwpG prob_lang Σ} :
  EwpTacticsBind Σ () costfun wp.
Next Obligation. intros. by apply ert_wp_bind. Qed.

Section proofmode.
  Context `{!ertwpG prob_lang Σ}.

  Lemma tac_wp_pure_cost Δ1 Δ2 Δ3 E i K `{!CostLanguageCtx costfun (fill K)} e1 e2 φ Φ a r1 :
    PureExec φ 1 e1 e2 →
    φ →
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    envs_lookup i Δ2 = Some (false, ⧖ r1)%I →
    (cost e1 <= r1)%R →
    envs_simple_replace i false (Esnoc Enil i (⧖ (r1 - cost e1))) Δ2 = Some Δ3 →
    envs_entails Δ3 (WP (fill K e2) @ a; E {{ Φ }}) →
    envs_entails Δ1 (WP (fill K e1) @ a; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> HP Hφ ? ??? Hcnt.
    rewrite into_laterN_env_sound.
    rewrite envs_simple_replace_sound //=.
    rewrite (etc_split_le (cost e1)) /=; last first.
    { pose proof (cost_nonneg e1). lra. }
    iIntros "[>[? ?] HΔ3]".
    pose proof @pure_exec_fill.
    iApply wp_pure_step_later; [done|].
    assert (to_val e1 = None).
    { eapply PureExec_not_val; [apply Hφ|done]. }
    erewrite cost_fill; [|done].
    iFrame. iModIntro.
    iApply Hcnt.
    iApply ("HΔ3" with "[$]").
  Qed.

  Lemma tac_wp_pure_no_cost Δ1 Δ2 E K `{!CostLanguageCtx costfun (fill K)} e1 e2 φ Φ a :
    PureExec φ 1 e1 e2 →
    φ →
    cost e1 = 0%R →
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    envs_entails Δ2 (WP (fill K e2) @ a; E {{ Φ }}) →
    envs_entails Δ1 (WP (fill K e1) @ a; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ? Hφ Hcost ? HΔ'. rewrite into_laterN_env_sound /=.
    pose proof @pure_exec_fill.
    rewrite HΔ'.
    iIntros "He2".
    iMod etc_zero as "Hz".
    iApply wp_pure_step_later; [done|].
    assert (to_val e1 = None).
    { eapply PureExec_not_val; [apply Hφ|done]. }
    rewrite cost_fill // Hcost.
    iFrame.
  Qed.

End proofmode.

(** Pure reduction w/o cost  *)
Tactic Notation "wp_pure_no_cost" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      let e := eval simpl in e in
      reshape_expr e ltac:(fun K e' =>
        unify e' efoc;
        eapply (tac_wp_pure_no_cost _ _ _ K e');
        [tc_solve                       (* PureExec *)
        |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *)
        |(reflexivity || fail "wp_pure_no_cost: could not prove that cost of " e " is 0")
        |tc_solve                       (* IntoLaters *)
        |pm_reduce; wp_finish           (* new goal *)
      ])
    || fail "wp_pure_no_cost: cannot find" efoc "in" e "or" efoc "is not a redex"
  end.

Tactic Notation "wp_pure_no_cost" :=
  wp_pure_no_cost _.

(** Pure reduction w/potential cost  *)
Tactic Notation "wp_pure_cost" open_constr(efoc) :=
  let solve_credit _ :=
    iAssumptionCore || fail "wp_pure_cost: cannot find credit '⧖ ?'" in
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      let e := eval simpl in e in
      reshape_expr e ltac:(fun K e' =>
        unify e' efoc;
        eapply (tac_wp_pure_cost _ _ _ _ _ K e');
        [(* [PureExec φ] *)
          tc_solve
        | (* φ *)
          try solve_vals_compare_safe
        | (* MaybeIntoLaterNEnvs *)
          tc_solve
        | (* credit resource *)
          solve_credit ()
        | (* enough credits *)
          simpl; try lra
        | (* new environment *)
          rewrite [⧖ _]/=; done
        | (* new goal *)
          pm_reduce; wp_finish; rewrite [⧖ _]/=
        ])
    || fail "wp_pure_cost: cannot find" efoc "in" e "or" efoc "is not a redex"
  end.

Tactic Notation "wp_pure_cost" :=
  wp_pure_cost _.

(** Pure reduction w/cost and specific credit assumption  *)
Tactic Notation "wp_pure_cost" open_constr(efoc) "with" open_constr(credit) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      let e := eval simpl in e in
      reshape_expr e ltac:(fun K e' =>
        unify e' efoc;
        eapply (tac_wp_pure_cost _ _ _ _ credit K e');
        [(* [PureExec φ] *)
          tc_solve
        | (* φ *)
          try solve_vals_compare_safe
        | (* MaybeIntoLaterNEnvs *)
          tc_solve
        | (* credit resource *)
          (done || fail "wp_pure_cost: cannot find rcedit " credit)
        | (* enough credits -- postpone *)
          simpl; try lra
        | (* new environment *)
          rewrite [⧖ _]/=; done
        | (* new goal *)
          pm_reduce; wp_finish; rewrite [⧖ _]/=
        ])
    || fail "wp_pure_cost: cannot find" efoc "in" e "or" efoc "is not a redex"
  end.

Tactic Notation "wp_pure_cost" "with" open_constr(credit) :=
  wp_pure_cost _ with credit.

(** Applies [tac1] if the head redex has *no* cost and [tac2] if it *does*   *)
Tactic Notation "wp_has_cost" open_constr(efoc) "with" tactic3(tac1) "," tactic3(tac2) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      let e := eval simpl in e in
        reshape_expr e ltac:(fun K e' =>
                               unify e' efoc;
                               lazymatch eval hnf in (cost e') with
                               | R0 => tac1
                               | _ => tac2
                               end)
        || fail "wp_has_cost: cannot find" efoc "in" e "or" efoc "is not a redex"
  end.

Tactic Notation "wp_pure" open_constr(efoc) :=
  wp_has_cost efoc with wp_pure_no_cost, wp_pure_cost.

Tactic Notation "wp_pure" :=
  wp_pure _.

Tactic Notation "wp_pure" open_constr(efoc) "with" open_constr(credit) :=
  wp_pure_cost efoc with credit.
Tactic Notation "wp_pure" "with" open_constr(credit) :=
  wp_pure_cost with credit.

Ltac wp_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (wp_pure _; [])
        | wp_finish (* In case wp_pure never ran, make sure we do the usual cleanup. *)
    ].

Tactic Notation "wp_pures" "with" open_constr(credit) :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (wp_pure _ with credit; [])
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

Lemma tac_chip `{!ertwpG prob_lang Σ} i j Δ1 Δ2 Δ3 r P :
  envs_lookup i Δ1 = Some (false, ⧖ r) →
  (1 <= r)%R →
  envs_simple_replace i false (Esnoc Enil i (⧖ (r  - 1))) Δ1 = Some Δ2 →
  envs_app false (Esnoc Enil j (⧖ 1)) Δ2 = Some Δ3 →
  envs_entails Δ3 P →
  envs_entails Δ1 P.
Proof.
  rewrite envs_entails_unseal =>/= ???? Hcnt.
  rewrite envs_simple_replace_singleton_sound //.
  rewrite (etc_split_le 1); [|lra].
  rewrite envs_app_singleton_sound //.
  rewrite Hcnt.
  iIntros "/= [[H1 Hc] HP]".
  iApply ("HP" with "Hc H1").
Qed.

(** Takes [H1 : ⧖ r] to [H2 : ⧖ 1] and [H1 : ⧖ (r - 1)] if [1 <= r] *)
Tactic Notation "iChip" constr(H1) "as" constr(H2) :=
  eapply (tac_chip H1 H2);
  [iAssumptionCore || fail "iChip: cannot find credit '⧖ ?'"
  | (* [1 <= r] *)
    simpl; try lra
  |done|done|].

Tactic Notation "iChip" constr(H1) :=
  let Htmp := iFresh in
  iChip H1 as Htmp.

Tactic Notation "iChip" :=
  let Htmp := iFresh in
  eapply (tac_chip _ Htmp);
  [iAssumptionCore || fail "iChip: cannot find credit '⧖ ?'"
  | (* [1 <= r] *)
    simpl; try lra
  |done|done|].

(** Some very primitive heap tactics  *)
Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  let Htmp := iFresh in
  iPoseProof wp_alloc as Htmp;
  simpl;
  (rewrite bool_decide_eq_true_2 //; []
   || rewrite bool_decide_eq_false_2 //; []);
  lazymatch eval hnf in (cost (ref #42)) with
  | R0 => idtac
  | _ => iChip
  end;
  wp_apply (Htmp with "[$]");
  iClear Htmp;
  iIntros (l) H.
Tactic Notation "wp_alloc" ident(l) :=
  wp_alloc l as "?".
Tactic Notation "wp_alloc" :=
  let l := fresh in wp_alloc l as "?".

Tactic Notation "wp_store" :=
  let Htmp := iFresh in
  iPoseProof wp_store as Htmp;
  simpl;
  (rewrite bool_decide_eq_true_2 //; []
   || rewrite bool_decide_eq_false_2 //; []);
  lazymatch eval hnf in (cost (#1 <- #42)%E) with
  | R0 => idtac
  | _ => iChip
  end;
  wp_apply (Htmp with "[$]");
  iClear Htmp.

Tactic Notation "wp_load" :=
  let Htmp := iFresh in
  iPoseProof wp_load as Htmp;
  simpl;
  (rewrite bool_decide_eq_true_2 //; []
   || rewrite bool_decide_eq_false_2 //; []);
  lazymatch eval hnf in (cost (! #1)%E) with
  | R0 => idtac
  | _ => iChip
  end;
  wp_apply (Htmp with "[$]");
  iClear Htmp.

Section tests.
  Context `{!ert_clutchGS Σ Cost1}.

  #[local] Lemma test_wp_pure (r : R) :
    (0 <= r)%R →
    {{{ ⧖ (1 + r) }}} #2 + #2 {{{ RET #4; ⧖ r }}}.
  Proof.
    iIntros (??) "Hx Hp".
    wp_pure.
    assert (1 + r - 1 = r)%R as -> by lra.
    by iApply "Hp".
  Qed.

  #[local] Lemma test_wp_pure' :
    {{{ ⧖ 1 }}} #2 + #2 {{{ RET #4; True }}}.
  Proof.
    iIntros (?) "Hx Hp".
    wp_pure.
    by iApply "Hp".
  Qed.

  #[local] Lemma test_multiple r :
    {{{ ⧖ 2 ∗ ⧖ r }}} #2 + #2 + #2 {{{ RET #6; ⧖ r }}}.
  Proof.
    iIntros (?) "[Hc Hr] H".
    wp_pure_cost with "Hc".
    wp_pure_cost with "Hc".
    by iApply "H".
  Qed.

  #[local] Lemma test_wp_pures r:
    (0 <= r)%R →
    {{{ ⧖ (2 + r) }}} #2 + #2 + #2 {{{ RET #6; ⧖ r }}}.
  Proof.
    iIntros (??) "Hx Hp".
    wp_pures.
    assert (2 + r - 1 - 1 = r)%R as -> by lra.
    by iApply "Hp".
  Qed.

  #[local] Lemma test_wp_pures' :
    {{{ ⧖ 2 }}} #2 + #2 + #2 {{{ RET #6; ⧖ 0 }}}.
  Proof.
    iIntros (?) "Hx Hp".
    wp_pures.
    assert (2 - 1 - 1 = 0)%R as -> by lra.
    by iApply "Hp".
  Qed.

  #[local] Lemma test_wp_heap :
    {{{ ⧖ 7 }}} let: "x" := ref #42 in "x" <- #43;; !"x" {{{ RET #43; True }}}.
  Proof.
    iIntros (?) "Hc H".
    wp_alloc l.
    wp_pures.
    wp_store; iIntros "Hl".
    wp_pures.
    wp_load; iIntros "Hl".
    by iApply "H".
  Qed.

End tests.

Section testsapp.
  Context `{!ert_clutchGS Σ CostApp}.

  #[local] Lemma test_app_wp_pure (r : R) :
    {{{ ⧖ r }}} #2 + #2 {{{ RET #4; ⧖ r }}}.
  Proof.
    iIntros (?) "Hx Hp".
    wp_pure.
    by iApply "Hp".
  Qed.

  #[local] Lemma test_app_wp_pure_app (r : R) :
    {{{ ⧖ 1 }}} #2 + (λ: "x", "x") #2 {{{ RET #4; ⧖ 0 }}}.
  Proof.
    iIntros (?) "Hx Hp".
    wp_pures.
    assert (1 - 1 = 0)%R as -> by lra.
    by iApply "Hp".
  Qed.

  #[local] Lemma test_app_wp_heap (r : R) :
    {{{ ⧖ 3 }}} let: "x" := ref #42 in "x" <- #43;; !"x" + (λ: "x", "x") #2 {{{ RET #45; ⧖ 0 }}}.
  Proof.
    iIntros (?) "Hx Hp".
    wp_alloc l as "Hl".
    wp_pures.
    wp_store; iIntros "Hl".
    wp_pures.
    wp_load; iIntros "Hl".
    wp_pures.
    assert (3 - 1 - 1 - 1 = 0)%R as -> by lra.
    by iApply "Hp".
  Qed.

End testsapp.

Section testtick.
  Context `{!ert_clutchGS Σ CostTick}.

  #[local] Lemma test_tick_wp_pure :
    {{{ ⧖ 5 }}} tick #1;; #2 + #2;; tick #4 {{{ RET #(); ⧖ 0 }}}.
  Proof.
    iIntros (?) "Hx Hp".
    wp_pures.
    iApply "Hp".
    iApply (etc_irrel with "Hx"); lra.
  Qed.

End testtick.
