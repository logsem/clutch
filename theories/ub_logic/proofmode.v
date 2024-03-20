From clutch.prob_lang Require Import lang notation class_instances tactics.
From clutch.prob_lang Require Export wp_tactics.
From clutch.ub_logic Require Import ub_weakestpre primitive_laws derived_laws.
From clutch.ub_logic Require Import ub_total_weakestpre total_primitive_laws total_derived_laws.
From iris.prelude Require Import options.


(*
#[local] Definition ub_wp' `{!irisGS prob_lang Σ} := (ub_wp').
*)
(*
#[local] Program Instance ub_wp' `{!irisGS prob_lang Σ} : Gwp (iProp Σ) (expr) (val) () .
Next Obligation.
  intros Σ lang.
  pose proof ub_wp' as [wp ?].
  apply wp.
Defined.
Next Obligation.
  intros Σ lang.
  pose proof ub_wp' as [wp u].
  exact u.
Defined.
*)



#[global] Program Instance rel_logic_wptactics_base `{!ub_clutchGS Σ} : @GwpTacticsBase Σ unit _ _ wp.
Next Obligation. intros. by apply ub_wp_value. Qed.
Next Obligation. intros. by apply ub_wp_fupd. Qed.
Next Obligation. intros. by apply ub_wp_bind, _. Qed.

#[global] Program Instance rel_logic_wptactics_pure `{!ub_clutchGS Σ} : @GwpTacticsPure Σ unit true wp.
Next Obligation. intros. by eapply lifting.wp_pure_step_later. Qed.

#[global] Program Instance rel_logic_wptactics_heap `{!ub_clutchGS Σ} : @GwpTacticsHeap Σ unit true wp :=
  Build_GwpTacticsHeap _ _ _ _ (λ l q v, (l ↦{q} v)%I) (λ l q vs, (l ↦∗{q} vs)%I) _ _ _ _.
Next Obligation. intros. by apply wp_alloc. Qed.
Next Obligation. intros. by apply wp_allocN. Qed.
Next Obligation. intros. by apply wp_load. Qed.
Next Obligation. intros. by apply wp_store. Qed.


(*
#[global] Program Instance ub_twp' `{!irisGS prob_lang Σ} : Gwp (iProp Σ) (expr) (val) () .
Next Obligation.
  intros Σ lang.
  pose proof ub_twp' as [wp ?].
  apply wp.
Defined.
Next Obligation.
  intros Σ lang.
  pose proof ub_twp' as [wp u].
  exact u.
Defined.
*)

#[global] Program Instance rel_logic_twptactics_base `{!ub_clutchGS Σ} : @GwpTacticsBase Σ unit _ _ twp.
Next Obligation. intros. by apply ub_twp_value. Qed.
Next Obligation. intros. by apply ub_twp_fupd. Qed.
Next Obligation. intros. by apply ub_twp_bind, _. Qed.

#[global] Program Instance rel_logic_twptactics_pure `{!ub_clutchGS Σ} : @GwpTacticsPure Σ unit false twp.
Next Obligation. intros. by eapply total_lifting.twp_pure_step_fupd. Qed.

#[global] Program Instance rel_logic_twptactics_heap `{!ub_clutchGS Σ} : @GwpTacticsHeap Σ unit false twp :=
  Build_GwpTacticsHeap _ _ _ _ (λ l q v, (l ↦{q} v)%I) (λ l q vs, (l ↦∗{q} vs)%I) _ _ _ _.
Next Obligation. intros. by apply twp_alloc. Qed.
Next Obligation. intros. by apply twp_allocN. Qed.
Next Obligation. intros. iIntros ">H H2". iApply (twp_load with "[H //] [H2 //]"). Qed.
Next Obligation. intros. iIntros ">H H2". iApply (twp_store with "[H //] [H2 //]"). Qed.

(*
From iris.bi Require Export bi updates.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic.

From clutch.common Require Import language ectx_language.
From clutch.prob_lang Require Import lang notation class_instances tactics.
From clutch.ub_logic Require Import ub_weakestpre primitive_laws.
From clutch.ub_logic Require Import total_lifting total_ectx_lifting.
From clutch.ub_logic Require Import ub_total_weakestpre total_primitive_laws.
From iris.prelude Require Import options.
Import uPred.

Lemma tac_wp_expr_eval `{!irisGS hlc Σ} Δ s E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ s; E {{ Φ }}) → envs_entails Δ (WP e @ s; E {{ Φ }}).
Proof. by intros ->. Qed.
Lemma tac_twp_expr_eval `{!irisGS hlc Σ} Δ s E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ s; E [{ Φ }]) → envs_entails Δ (WP e @ s; E [{ Φ }]).
Proof. by intros ->. Qed.


Tactic Notation "wp_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    notypeclasses refine (tac_wp_expr_eval _ _ _ _ e _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    notypeclasses refine (tac_twp_expr_eval _ _ _ _ e _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]

  | _ => fail "wp_expr_eval: not a 'wp'"
  end.
Ltac wp_expr_simpl := wp_expr_eval simpl.

Lemma tac_wp_pure `{!ub_clutchGS Σ} Δ Δ' E K e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (WP (fill K e2) @ E {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_fill.
  rewrite HΔ' -lifting.wp_pure_step_later //.
  (* iIntros "Hwp !> _" => //. *)
Qed.
Lemma tac_twp_pure `{!ub_clutchGS Σ} Δ E K e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  envs_entails Δ (WP (fill K e2) @ E [{ Φ }]) →
  envs_entails Δ (WP (fill K e1) @ E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> ?? ->.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_fill.
  rewrite -total_lifting.twp_pure_step_fupd //.
Qed.



Lemma tac_wp_value_nofupd `{!ub_clutchGS Σ} Δ E Φ v :
  envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. by apply ub_wp_value. Qed.
Lemma tac_twp_value_nofupd `{!ub_clutchGS Σ} Δ s E Φ v :
  envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ s; E [{ Φ }]).
Proof. rewrite envs_entails_unseal=> ->. by apply ub_twp_value. Qed.


Lemma tac_wp_value `{!ub_clutchGS Σ} Δ E (Φ : val → iPropI Σ) v :
  envs_entails Δ (|={E}=> Φ v) → envs_entails Δ (WP (Val v) @ E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. by rewrite ub_wp_value_fupd. Qed.
Lemma tac_twp_value `{!ub_clutchGS Σ} Δ s E (Φ : val → iPropI Σ) v :
  envs_entails Δ (|={E}=> Φ v) → envs_entails Δ (WP (Val v) @ s; E [{ Φ }]).
Proof. rewrite envs_entails_unseal=> ->. by rewrite ub_twp_value_fupd. Qed.


(** Simplify the goal if it is [WP] of a value.
  If the postcondition already allows a fupd, do not add a second one.
  But otherwise, *do* add a fupd. This ensures that all the lemmas applied
  here are bidirectional, so we never will make a goal unprovable. *)
Ltac wp_value_head :=
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E (Val _) (λ _, fupd ?E _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp ?s ?E (Val _) (λ _, wp _ ?E _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp ?s ?E (Val _) _) =>
      eapply tac_wp_value             
  | |- envs_entails _ (twp ?s ?E (Val _) (λ _, fupd ?E _ _)) =>
      eapply tac_twp_value_nofupd
  | |- envs_entails _ (twp ?s ?E (Val _) (λ _, twp _ ?E _ _)) =>
      eapply tac_twp_value_nofupd
  | |- envs_entails _ (twp ?s ?E (Val _) _) =>
      eapply tac_twp_value
  end.

Ltac wp_finish :=
  wp_expr_simpl;      (* simplify occurences of subst/fill *)
  try wp_value_head;  (* in case we have reached a value, get rid of the WP *)
  pm_prettify.        (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and
                         λs caused by wp_value *)

Ltac solve_vals_compare_safe :=
  (* The first branch is for when we have [vals_compare_safe] in the context.
     The other two branches are for when either one of the branches reduces to
     [True] or we have it in the context. *)
  fast_done || (left; fast_done) || (right; fast_done).

(** The argument [efoc] can be used to specify the construct that should be
reduced. For example, you can write [wp_pure (EIf _ _ _)], which will search
for an [EIf _ _ _] in the expression, and reduce it.

The use of [open_constr] in this tactic is essential. It will convert all holes
(i.e. [_]s) into evars, that later get unified when an occurences is found
(see [unify e' efoc] in the code below). *)
Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_wp_pure _ _ _ K e');
      [tc_solve                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec --
         handles trivial goals, including [vals_compare_safe] *)
      |tc_solve                       (* IntoLaters *)
      |wp_finish                      (* new goal *)
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
       eapply (tac_twp_pure _ _ K e'); 
      [tc_solve                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec *)
      |wp_finish                      (* new goal *)
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wp_pure: not a 'wp'"
  end.
Tactic Notation "wp_pure" :=
  wp_pure _.

Tactic Notation "wp_pure" open_constr(efoc) "credit:" constr(H) :=
  iStartProof;
  let Htmp := iFresh in
  let finish _ :=
    pm_reduce;
    (iDestructHyp Htmp as H || fail 2 "wp_pure:" H "is not fresh");
    wp_finish
    in
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      (* eapply (tac_wp_pure_credit _ _ _ _ Htmp K e'); *)
      [tc_solve                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec --
         handles trivial goals, including [vals_compare_safe] *)
      |tc_solve                       (* IntoLaters *)
      |finish ()                      (* new goal *)
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    fail "wp_pure: credit generation is not supported for a TWP"
  | _ => fail "wp_pure: not a 'wp'"
  end.
Tactic Notation "wp_pure" "credit:" constr(H) :=
  wp_pure _ credit: H.

(* TODO: do this in one go, without [repeat]. *)
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

Lemma tac_wp_bind `{!ub_clutchGS Σ} K Δ E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ E {{ v, WP f (Val v) @ E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> -> ->. by apply: ub_wp_bind. Qed.
Lemma tac_twp_bind `{!ub_clutchGS Σ} K Δ s E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ s; E [{ v, WP f (Val v) @ s; E [{ Φ }] }])%I →
  envs_entails Δ (WP fill K e @ s; E [{ Φ }]).
Proof. rewrite envs_entails_unseal=> -> ->. by apply: ub_twp_bind. Qed.


Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.
Ltac twp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_twp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.


Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
          | fail 1 "wp_bind: cannot find" efoc "in" e ]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; twp_bind_core K)
          | fail 1 "wp_bind: cannot find" efoc "in" e ]

  | _ => fail "wp_bind: not a 'wp'"
  end.

(** Heap tactics *)
Section heap.
Context `{!ub_clutchGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types z : Z.

Lemma tac_wp_alloc Δ Δ' E j K v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀ l,
    match envs_app false (Esnoc Enil j (l ↦ v)) Δ' with
    | Some Δ'' =>
       envs_entails Δ'' (WP fill K (Val $ LitV l) @ E {{ Φ }})
    | None => False
    end) →
  envs_entails Δ (WP fill K (Alloc (Val v)) @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? HΔ.
  rewrite -ub_wp_bind. eapply wand_apply; first exact: wp_alloc.
  rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
  specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [ | contradiction ].
  rewrite envs_app_sound //; simpl.
  apply wand_intro_l.
  (* rewrite (sep_elim_l (l ↦ v)%I). *)
  rewrite right_id.
  rewrite wand_elim_r.
  done.
Qed.
Lemma tac_twp_alloc Δ E j K v Φ :
  (∀ l,
    match envs_app false (Esnoc Enil j (l ↦ v)) Δ with
    | Some Δ' =>
       envs_entails Δ' (WP fill K (Val $ LitV $ l) @ E [{ Φ }])
    | None => False
    end) →
  envs_entails Δ (WP fill K (Alloc (Val v)) @ E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> HΔ.
  rewrite -ub_twp_bind. eapply wand_apply; first apply wand_entails.
  { iIntros "P Q". iApply (twp_alloc with "[P][Q]"); done. }
  rewrite left_id. apply forall_intro=> l.
  specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction ].
  rewrite envs_app_sound //; simpl.
  apply wand_intro_l.
  iIntros "[?T]". iApply HΔ. iApply "T". iFrame. 
Qed.


Lemma tac_wp_load Δ Δ' E i K b l q v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (b, l ↦{q} v)%I →
  envs_entails Δ' (WP fill K (Val v) @ E {{ Φ }}) →
  envs_entails Δ (WP fill K (Load (LitV l)) @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?? Hi.
  rewrite -ub_wp_bind. eapply wand_apply; first exact: wp_load.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  apply later_mono.
  destruct b; simpl.
  * iIntros "[#$ He]". iIntros "_". iApply Hi. iApply "He". iFrame "#".
  * by apply sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_load Δ E i K b l q v Φ :
  envs_lookup i Δ = Some (b, l ↦{q} v)%I →
  envs_entails Δ (WP fill K (Val v) @ E [{ Φ }]) →
  envs_entails Δ (WP fill K (Load (LitV l)) @ E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> ? Hi.
  rewrite -ub_twp_bind. eapply wand_apply; first exact: twp_load.
  rewrite envs_lookup_split //; simpl.
  destruct b; simpl.
  - iIntros "[#$ He]". iIntros "_". iApply Hi. iApply "He". iFrame "#".
  - iIntros "[$ He]". iIntros "Hl". iApply Hi. iApply "He". iFrame "Hl".
Qed.


Lemma tac_wp_store Δ Δ' E i K l v v' Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ' with
  | Some Δ'' => envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ E {{ Φ }})
  | None => False
  end →
  envs_entails Δ (WP fill K (Store (LitV l) (Val v')) @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ???.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -ub_wp_bind. eapply wand_apply; first by eapply wp_store.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_store Δ E i K l v v' Φ :
  envs_lookup i Δ = Some (false, l ↦ v)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ with
  | Some Δ' => envs_entails Δ' (WP fill K (Val $ LitV LitUnit) @ E [{ Φ }])
  | None => False
  end →
  envs_entails Δ (WP fill K (Store (LitV l) v') @ E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal. intros.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -ub_twp_bind. eapply wand_apply; first by eapply twp_store.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. 
  iIntros "[H?]". iSplitL "H"; first done.
  by iApply wand_mono.
Qed.

End heap.

(** The tactic [wp_apply_core lem tac_suc tac_fail] evaluates [lem] to a
hypothesis [H] that can be applied, and then runs [wp_bind_core K; tac_suc H]
for every possible evaluation context [K].

- The tactic [tac_suc] should do [iApplyHyp H] to actually apply the hypothesis,
  but can perform other operations in addition (see [wp_apply] and [awp_apply]
  below).
- The tactic [tac_fail cont] is called when [tac_suc H] fails for all evaluation
  contexts [K], and can perform further operations before invoking [cont] to
  try again.

TC resolution of [lem] premises happens *after* [tac_suc H] got executed. *)
Ltac wp_apply_core lem tac_suc tac_fail := first
  [iPoseProofCore lem as false (fun H =>
     lazymatch goal with
     | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
       reshape_expr e ltac:(fun K e' =>
         wp_bind_core K; tac_suc H)
     | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
       reshape_expr e ltac:(fun K e' =>
         twp_bind_core K; tac_suc H)

     | _ => fail 1 "wp_apply: not a 'wp'"
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

(** Tactic tailored for atomic triples: the first, simple one just runs
[iAuIntro] on the goal, as atomic triples always have an atomic update as their
premise. The second one additionaly does some framing: it gets rid of [Hs] from
the context, reducing clutter. You get them all back in the continuation of the
atomic operation. *)
Tactic Notation "awp_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H) ltac:(fun cont => fail);
  last iAuIntro.
Tactic Notation "awp_apply" open_constr(lem) "without" constr(Hs) :=
  (* Convert "list of hypothesis" into specialization pattern. *)
  let Hs := words Hs in
  let Hs := eval vm_compute in (INamed <$> Hs) in
  wp_apply_core lem
    ltac:(fun H =>
      iApply (wp_frame_wand with
        [SGoal $ SpecGoal GSpatial false [] Hs false]); [iAccu|iApplyHyp H])
    ltac:(fun cont => fail);
  last iAuIntro.

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  let Htmp := iFresh in
  let finish _ :=
    first [intros l | fail 1 "wp_alloc:" l "not fresh"];
    pm_reduce;
    lazymatch goal with
    | |- False => fail 1 "wp_alloc:" H "not fresh"
    | _ => iDestructHyp Htmp as H; wp_finish
    end in
  wp_pures;
  (** The code first tries to use allocation lemma for a single reference,
     ie, [tac_wp_alloc] (respectively, [tac_twp_alloc]).
     If that fails, it tries to use the lemma [tac_wp_allocN]
     (respectively, [tac_twp_allocN]) for allocating an array.
     Notice that we could have used the array allocation lemma also for single
     references. However, that would produce the resource l ↦∗ [v] instead of
     l ↦ v for single references. These are logically equivalent assertions
     but are not equal. *)
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloc _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [tc_solve
        |finish ()]
    in (process_single ())
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_twp_alloc _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        finish ()
    in process_single ()
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  wp_alloc l as "?".

Tactic Notation "wp_load" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load _ _ _ _ K))
      |fail 1 "wp_load: cannot find 'Load' in" e];
    [tc_solve
    |solve_mapsto ()
    |wp_finish]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_load _ _ _ K))
      |fail 1 "wp_load: cannot find 'Load' in" e];
    [solve_mapsto ()
    |wp_finish]
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [tc_solve
    |solve_mapsto ()
    |pm_reduce; first [wp_seq|wp_finish]]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_store _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [solve_mapsto ()
    |pm_reduce; first [wp_seq|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.
*)
