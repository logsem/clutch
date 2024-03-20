From iris.bi Require Export bi updates.
From iris.base_logic.lib Require Import fancy_updates.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.

(*From clutch.bi Require Import weakestpre.*)
From clutch.prob_lang Require Import lang tactics notation class_instances.
Set Default Proof Using "Type*".

(** A basic set of requirements for a weakest precondition *)
Class GwpTacticsBase (Σ : gFunctors) (A : Type) `{!invGS_gen hlc Σ} (gwp : A → coPset → expr → (val → iProp Σ) → iProp Σ)  := {
    wptac_wp_value E Φ v a : Φ v ⊢ gwp a E (of_val v) Φ;
    wptac_wp_fupd E Φ e a : gwp a E e (λ v, |={E}=> Φ v) ⊢ gwp a E e Φ;
    wptac_wp_bind K E e Φ a :
      gwp a E e (λ v, gwp a E (fill K (of_val v)) Φ ) ⊢ gwp a E (fill K e) Φ ;
}.

Class GwpTacticsPure Σ A (laters : bool) (gwp : A → coPset → expr → (val → iProp Σ) → iProp Σ) := {
  wptac_wp_pure_step E e1 e2 φ n Φ a :
    PureExec φ n e1 e2 →
    φ →
    ▷^(if laters then n else 0) (gwp a E e2 Φ) ⊢ (gwp a E e1 Φ);
}.

(** Heap *)
Class GwpTacticsHeap Σ A (laters : bool) (gwp : A → coPset → expr → (val → iProp Σ) → iProp Σ):= {
  wptac_mapsto : loc → dfrac → val → iProp Σ;
  wptac_mapsto_array : loc → dfrac → (list val) → iProp Σ;

  wptac_wp_alloc E v a Φ :
    True -∗
    (▷?laters (∀ l, (wptac_mapsto l (DfracOwn 1) v) -∗ Φ (LitV (LitLoc l))%V)) -∗
    gwp a E (Alloc (Val v)) Φ;

  wptac_wp_allocN E v n a Φ :
    (0 < n)%Z →
    True -∗
    (▷?laters (∀ l, (wptac_mapsto_array l (DfracOwn 1) (replicate (Z.to_nat n) v)) -∗
                     Φ (LitV (LitLoc l))%V)) -∗
    gwp a E (AllocN (Val $ LitV $ LitInt $ n) (Val v)) Φ;

  wptac_wp_load E v l dq a Φ :
    (▷ wptac_mapsto l dq v) -∗
    (▷?laters ((wptac_mapsto l dq v) -∗ Φ v%V)) -∗
    gwp a E (Load (Val $ LitV $ LitLoc l)) Φ;

  wptac_wp_store E v v' l a Φ :
    (▷ wptac_mapsto l (DfracOwn 1) v') -∗
    (▷?laters ((wptac_mapsto l (DfracOwn 1) v) -∗ Φ (LitV (LitUnit))%V)) -∗
    gwp a E (Store (Val $ LitV $ LitLoc l) (Val v)) Φ;
}.

Section wp_tactics.
  Context `{GwpTacticsBase Σ A hlc gwp}.

  Local Notation "'WP' e @ s ; E {{ Φ } }" := (gwp s E e%E Φ)
    (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  Local Notation "'WP' e @ s ; E {{ v , Q } }" := (gwp s E e%E (λ v, Q))
    (at level 20, e, Q at level 200,
     format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

  Lemma tac_wp_expr_eval Δ a E Φ e e' :
    (∀ (e'':=e'), e = e'') →
    envs_entails Δ (WP e' @ a; E {{ Φ }}) → envs_entails Δ (WP e @ a; E {{ Φ }}).
  Proof. by intros ->. Qed.

  Lemma tac_wp_pure_later laters `{!GwpTacticsPure Σ A laters gwp} Δ Δ' E K e1 e2 φ n Φ a :
    PureExec φ n e1 e2 →
    φ →
    MaybeIntoLaterNEnvs (if laters then n else 0) Δ Δ' →
    envs_entails Δ' (WP (fill K e2) @ a; E {{ Φ }}) →
    envs_entails Δ (WP (fill K e1) @ a; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ??? HΔ'. rewrite into_laterN_env_sound /=.
    (* We want [pure_exec_fill] to be available to TC search locally. *)
    pose proof @pure_exec_fill.
    rewrite HΔ' -wptac_wp_pure_step //.
  Qed.

  Lemma tac_wp_value_nofupd Δ E Φ v a :
    envs_entails Δ (Φ v) → envs_entails Δ (WP (of_val v) @ a; E {{ Φ }}).
  Proof. rewrite envs_entails_unseal=> ->. apply wptac_wp_value. Qed.

  Lemma tac_wp_value' Δ E Φ v a :
    envs_entails Δ (|={E}=> Φ v) → envs_entails Δ (WP (of_val v) @ a; E {{ Φ }}).
  Proof. rewrite envs_entails_unseal=> ->. by rewrite -wptac_wp_fupd -wptac_wp_value. Qed.

  Lemma tac_wp_bind K Δ E Φ e f a :
    f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
    envs_entails Δ (WP e @ a; E {{ v, WP f (Val v) @ a; E {{ Φ }} }})%I →
    envs_entails Δ (WP fill K e @ a; E {{ Φ }}).
  Proof. rewrite envs_entails_unseal=> -> ->. by apply: wptac_wp_bind. Qed.

End wp_tactics.

(* TODO: find a better way so that we do not need to have a case for both [wp] and [twp]... *)
Tactic Notation "wp_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      notypeclasses refine (tac_wp_expr_eval _ _ _ _ e _ _ _ );
      [apply _|let x := fresh in intros x; simpl; unfold x; notypeclasses refine eq_refl|]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
      notypeclasses refine (tac_wp_expr_eval _ _ _ _ e _ _ _ );
      [apply _|let x := fresh in intros x; simpl; unfold x; notypeclasses refine eq_refl|]
  | _ => fail "wp_expr_eval: not a 'wp'"
  end.
Ltac wp_expr_simpl := wp_expr_eval simpl.

(** Simplify the goal if it is [wp] of a value.
  If the postcondition already allows a fupd, do not add a second one.
  But otherwise, *do* add a fupd. This ensures that all the lemmas applied
  here are bidirectional, so we never will make a goal unprovable. *)
Ltac wp_value_head :=
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E (of_val _) (λ _, fupd ?E _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp ?s ?E (of_val _) (λ _, wp _ ?E _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp ?s ?E (of_val _) _) =>
      eapply tac_wp_value'
  | |- envs_entails _ (twp ?s ?E (of_val _) (λ _, fupd ?E _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (twp ?s ?E (of_val _) (λ _, twp _ ?E _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (twp ?s ?E (of_val _) _) =>
      eapply tac_wp_value'
  end.

Ltac wp_finish :=
  (* simplify occurences of [wptac_mapsto] projections  *)
  rewrite ?[wptac_mapsto _ _ _]/=;
  (* simplify occurences of subst/fill *)
  wp_expr_simpl;
  (* in case we have reached a value, get rid of the wp *)
  try wp_value_head;
  (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and λs caused by wp_value *)
  pm_prettify.

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
        eapply (tac_wp_pure_later _ _ _ _ K e');
        [tc_solve                       (* PureExec *)
        |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *)
        |tc_solve                       (* IntoLaters *)
        |wp_finish                      (* new goal *)
        ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_wp_pure_later _ _ _ _ K e');
      [tc_solve                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *)
      |tc_solve                       (* IntoLaters *)
      |wp_finish                      (* new goal *)
      ])
    || fail "Hello! wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wp_pure: not a 'wp'"
  end.

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
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
          | fail 1 "wp_bind: cannot find" efoc "in" e ]
  | _ => fail "wp_bind: not a 'wp'"
  end.

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
         reshape_expr e ltac:(fun K e' => wp_bind_core K; tac_suc H)
     | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
         reshape_expr e ltac:(fun K e' => wp_bind_core K; tac_suc H)
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

Section heap_tactics.

  Context `{GwpTacticsBase Σ A hlc gwp, !GwpTacticsHeap Σ A laters gwp}.


  Local Notation "'WP' e @ s ; E {{ Φ } }" := (gwp s E e%E Φ)
    (at level 20, e, Φ at level 200, only parsing) : bi_scope.

  (** Notations with binder. *)
  Local Notation "'WP' e @ s ; E {{ v , Q } }" := (gwp s E e%E (λ v, Q))
    (at level 20, e, Q at level 200,
     format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

  Lemma tac_wp_alloc Δ Δ' E j K v Φ a :
    MaybeIntoLaterNEnvs (if laters then 1 else 0) Δ Δ' →
    (∀ (l : loc),
        match envs_app false (Esnoc Enil j (wptac_mapsto l (DfracOwn 1) v)) Δ' with
        | Some Δ'' =>
            envs_entails Δ'' (WP fill K (Val $ LitV $ LitLoc l) @ a ; E {{ Φ }})
        | None => False
        end) →
    envs_entails Δ (WP fill K (Alloc (Val v)) @ a; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ? HΔ.
    rewrite -wptac_wp_bind.
    eapply bi.wand_apply.
    { apply bi.wand_entails, wptac_wp_alloc. }
    rewrite left_id into_laterN_env_sound.
    apply bi.laterN_mono, bi.forall_intro=> l.
    specialize (HΔ l).
    destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [| contradiction].
    rewrite envs_app_sound //; simpl.
    apply bi.wand_intro_l.
    rewrite right_id.
    rewrite bi.wand_elim_r //.
  Qed.

  Lemma tac_wp_allocN Δ Δ' E j K v n Φ a :
    (0 < n)%Z →
    MaybeIntoLaterNEnvs (if laters then 1 else 0) Δ Δ' →
    (∀ l,
        match envs_app false (Esnoc Enil j (wptac_mapsto_array l (DfracOwn 1) (replicate (Z.to_nat n) v))) Δ' with
        | Some Δ'' =>
            envs_entails Δ'' (WP fill K (Val $ LitV $ LitLoc l) @ a; E {{ Φ }})
        | None => False
        end) →
    envs_entails Δ (WP fill K (AllocN (Val $ LitV $ LitInt n) (Val v)) @ a; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ? ? HΔ.
    rewrite -wptac_wp_bind.
    eapply bi.wand_apply.
    { by apply bi.wand_entails, wptac_wp_allocN. }
    rewrite left_id into_laterN_env_sound.
    apply bi.laterN_mono, bi.forall_intro=> l.
    specialize (HΔ l).
    destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [ | contradiction ].
    rewrite envs_app_sound //; simpl.
    apply bi.wand_intro_l.
    rewrite right_id.
    rewrite bi.wand_elim_r //.
  Qed.

  Lemma tac_wp_load Δ Δ' E i K b l dq v Φ a :
    MaybeIntoLaterNEnvs (if laters then 1 else 0) Δ Δ' →
    envs_lookup i Δ' = Some (b, wptac_mapsto l dq v) →
    envs_entails Δ' (WP fill K (Val v) @ a; E {{ Φ }}) →
    envs_entails Δ (WP fill K (Load (Val $ LitV $ LitLoc l)) @ a; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ?? Hi.
    rewrite -wptac_wp_bind.
    eapply bi.wand_apply.
    { apply bi.wand_entails, wptac_wp_load. }
    rewrite into_laterN_env_sound.
    destruct laters.
    - rewrite -bi.later_sep.
      rewrite envs_lookup_split //; simpl.
      apply bi.later_mono.
      destruct b; simpl.
      * iIntros "[#$ He]". iIntros "_". iApply Hi. iApply "He". iFrame "#".
      * by apply bi.sep_mono_r, bi.wand_mono.
    - rewrite envs_lookup_split //; simpl.
      destruct b; simpl.
      * iIntros "[#$ He]". iIntros "_". iApply Hi. iApply "He". iFrame "#".
      * iIntros "[$ He] H". iApply Hi. by iApply "He".
  Qed.

  Lemma tac_wp_store Δ Δ' E i K l v v' Φ a :
    MaybeIntoLaterNEnvs (if laters then 1 else 0) Δ Δ' →
    envs_lookup i Δ' = Some (false, wptac_mapsto l (DfracOwn 1) v)%I →
    match envs_simple_replace i false (Esnoc Enil i (wptac_mapsto l (DfracOwn 1) v')) Δ' with
    | Some Δ'' => envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ a; E {{ Φ }})
    | None => False
    end →
    envs_entails Δ (WP fill K (Store (Val $ LitV $ LitLoc l) (Val v')) @ a; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ?? Hcnt.
    destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
    rewrite -wptac_wp_bind. eapply bi.wand_apply.
    { eapply bi.wand_entails, wptac_wp_store. }
    rewrite into_laterN_env_sound.
    destruct laters.
    - rewrite -bi.later_sep envs_simple_replace_sound //; simpl.
      rewrite right_id. by apply bi.later_mono, bi.sep_mono_r, bi.wand_mono.
    - rewrite envs_simple_replace_sound //; simpl.
      rewrite right_id.
      iIntros "[$ He] H". iApply Hcnt. by iApply "He".
  Qed.

End heap_tactics.

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
    in
    let process_array _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_allocN _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [idtac| tc_solve
         |finish ()]
    in (process_single ()) || (process_array ())
| |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloc _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [tc_solve
        |finish ()]
    in
    let process_array _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_allocN _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [idtac| tc_solve
         |finish ()]
    in (process_single ()) || (process_array ())
  | _ => fail "wp_alloc: not a 'wp'"
  end.


Tactic Notation "wp_alloc" ident(l) :=
  wp_alloc l as "?".

Tactic Notation "wp_load" :=
  let solve_wptac_mapsto _ :=
    let l := match goal with |- _ = Some (_, (wptac_mapsto ?l _ _)%I) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load _ _ _ _ K))
      |fail 1 "wp_load: cannot find 'Load' in" e];
    [tc_solve
    |solve_wptac_mapsto ()
    |wp_finish]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load _ _ _ _ K))
      |fail 1 "wp_load: cannot find 'Load' in" e];
    [tc_solve
    |solve_wptac_mapsto ()
    |wp_finish]
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  let solve_wptac_mapsto _ :=
    let l := match goal with |- _ = Some (_, (wptac_mapsto ?l _ _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [tc_solve
    |solve_wptac_mapsto ()
    |pm_reduce; first [wp_seq|wp_finish]]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [tc_solve
    |solve_wptac_mapsto ()
    |pm_reduce; first [wp_seq|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.
