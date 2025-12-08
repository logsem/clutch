From iris.bi Require Export bi updates.
From iris.base_logic.lib Require Import fancy_updates.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From clutch.approxis Require Import app_weakestpre.
From clutch.common Require Import locations.

(*From clutch.bi Require Import weakestpre.*)
From clutch.prob_eff_lang.hazel_prob Require Import  tactics notation spec_ra spec_rules primitive_laws
                                         class_instances weakestpre lifting lang.
Set Default Proof Using "Type*".

Section ewp_tactics.
  Context `{probeffGS Σ}.

  Lemma pure_step_ctx K e1 e2 :
    pure_step e1 e2 → pure_step (fill K e1) (fill K e2).
  Proof.
    intros [Hred Hstep]. split.
    - unfold reducible in *. intros σ1.
      destruct (Hred σ1) as [[]].
      eexists. by eapply fill_step.
    - intros σ.
      rewrite -fill_step_prob //.
      { eapply (to_final_None_1 (_, σ)).
        by eapply reducible_not_final. }
      { apply (reducible_not_eff _ inhabitant). apply Hred.  }
  Qed.

  Lemma pure_step_nsteps_ctx K n e1 e2 :
    nsteps pure_step n e1 e2 →
    nsteps pure_step n (fill K e1) (fill K e2).
  Proof. eauto using nsteps_congruence, pure_step_ctx. Qed.
    
  Lemma pure_exec_fill K φ n e1 e2 :
    PureExec φ n e1 e2 → PureExec φ n (fill K e1) (fill K e2).
  Proof.
    rewrite /PureExec. eauto using pure_step_nsteps_ctx.
  Qed.
    
  Lemma tac_ewp_expr_eval (Δ : envs (iProp Σ)) E Φ Ψ e e' :
    (∀ (e'':=e'), e = e'') →
    envs_entails Δ (EWP e' @ E <| Ψ |> {{ Φ }}) →
    envs_entails Δ (EWP e @ E <| Ψ |> {{ Φ }}).
  Proof. by intros ->. Qed.

  Lemma tac_ewp_pure_later laters Δ Δ' E K e1 e2 φ n Φ Ψ :
    PureExec φ n e1 e2 →
    φ →
    MaybeIntoLaterNEnvs (if laters then n else 0%nat) Δ Δ' →
    envs_entails Δ' (EWP (fill K e2) @ E <| Ψ |> {{ Φ }}) →
    envs_entails Δ (EWP (fill K e1) @ E <| Ψ |> {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ??? HΔ'. rewrite into_laterN_env_sound /=.
    (* We want [pure_exec_fill] to be available to TC search locally. *)
    (* the lemma is adapted to the specific language *)
    pose proof @pure_exec_fill.
    rewrite HΔ' -ewp_pure_step_later //. destruct laters; try done. simpl.
    iIntros. iNext. done.
  Qed.

  Lemma tac_ewp_value_nofupd Δ E Φ Ψ v :
    envs_entails Δ (Φ v) → envs_entails Δ (EWP (of_val v) @ E <| Ψ |> {{ Φ }}).
  Proof. rewrite envs_entails_unseal=> ->. by apply ewp_value. Qed.

  Lemma tac_ewp_value' Δ E Φ Ψ v :
    envs_entails Δ (|={E}=> Φ v) → envs_entails Δ (EWP (of_val v) @ E <| Ψ |> {{ Φ }}).
  Proof. rewrite envs_entails_unseal=> ->. by rewrite -ewp_fupd -ewp_value. Qed.

End ewp_tactics.

Section ewp_bind_tactics.
  Context `{probeffGS Σ}.
  
  Lemma tac_ewp_bind K Δ E Φ Ψ e f :
    NeutralEctx K → 
    f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
    envs_entails Δ (EWP e @ E <| Ψ |> {{ v, EWP f (Val v) @ E <| Ψ |> {{ Φ }} }})%I →
    envs_entails Δ (EWP fill K e @ E <| Ψ |> {{ Φ }}).
  Proof. intros HK. rewrite envs_entails_unseal=> -> ->. by apply: ewp_bind. Qed.
End ewp_bind_tactics.

(* TODO: find a better way so that we do not need to have a case for both [wp] and [twp]... *)
Tactic Notation "ewp_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (ewp_def ?E ?e ?P ?Q) =>
      notypeclasses refine (tac_ewp_expr_eval _ _ _ _ e _ _ _);
      [apply _|let x := fresh in intros x; simpl; unfold x; notypeclasses refine eq_refl|]
  | _ => fail "ewp_expr_eval: not a 'ewp'"
  end.
Ltac ewp_expr_simpl := ewp_expr_eval simpl.

(** Simplify the goal if it is [wp] of a value.
  If the postcondition already allows a fupd, do not add a second one.
  But otherwise, *do* add a fupd. This ensures that all the lemmas applied
  here are bidirectional, so we never will make a goal unprovable. *)
Ltac ewp_value_head :=
  lazymatch goal with
  | |- envs_entails _ (ewp_def ?E (of_val _) _ (λ _, fupd ?E _ _)) =>
      eapply tac_ewp_value_nofupd
  | |- envs_entails _ (ewp_def ?E (of_val _) _ (λ _, ewp_def ?E _ _ _)) =>
      eapply tac_ewp_value_nofupd
  | |- envs_entails _ (ewp_def ?E (of_val _) _ _) =>
      eapply tac_ewp_value'
  end.

Ltac ewp_finish :=
  (* simplify occurences of [wptac_mapsto] projections  *)
  rewrite ?[(λ l q v, (l ↦{q} v)%I) _ _ _]/=;
  (* simplify occurences of subst/fill *)
  try ewp_expr_simpl;
  (* in case we have reached a value, get rid of the wp *)
  try ewp_value_head;
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
Tactic Notation "ewp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (ewp_def ?E ?e ?P ?Q) =>
      let e := eval simpl in e in
      reshape_expr e ltac:(fun K e' =>
        unify e' efoc;
        try (eapply (tac_ewp_pure_later _ _ _ _ K e');
        [tc_solve                       (* PureExec *)
        |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *)
        |tc_solve                       (* IntoLaters *)
        |ewp_finish                      (* new goal *)
        ]))
    || fail "ewp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "ewp_pure: not a 'ewp'"
  end.

Tactic Notation "ewp_pure" :=
  ewp_pure _.

Ltac ewp_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          (* progress *) repeat (ewp_pure _; [])
        | ewp_finish (* In case wp_pure never ran, make sure we do the usual cleanup. *)
    ].

(** Unlike [wp_pures], the tactics [wp_rec] and [wp_lam] should also reduce
    lambdas/recs that are hidden behind a definition, i.e. they should use
    [AsRecV_recv] as a proper instance instead of a [Hint Extern].

    We achieve this by putting [AsRecV_recv] in the current environment so that it
    can be used as an instance by the typeclass resolution system. We then perform
    the reduction, and finally we clear this new hypothesis. *)
Tactic Notation "ewp_rec" :=
  let H := fresh in
  assert (H := AsRecV_recv);
  ewp_pure (App _ _);
  clear H.

Tactic Notation "ewp_if" := ewp_pure (If _ _ _).
Tactic Notation "ewp_if_true" := ewp_pure (If (LitV (LitBool true)) _ _).
Tactic Notation "ewp_if_false" := ewp_pure (If (LitV (LitBool false)) _ _).
Tactic Notation "ewp_unop" := ewp_pure (UnOp _ _).
Tactic Notation "ewp_binop" := ewp_pure (BinOp _ _ _).
Tactic Notation "ewp_op" := ewp_unop || ewp_binop.
Tactic Notation "ewp_lam" := ewp_rec.
Tactic Notation "ewp_let" := ewp_pure (Rec BAnon (BNamed _) _); ewp_lam.
Tactic Notation "ewp_seq" := ewp_pure (Rec BAnon BAnon _); ewp_lam.
Tactic Notation "ewp_proj" := ewp_pure (Fst _) || ewp_pure (Snd _).
Tactic Notation "ewp_case" := ewp_pure (Case _ _ _).
Tactic Notation "ewp_match" := ewp_case; ewp_pure (Rec _ _ _); ewp_lam.
Tactic Notation "ewp_inj" := ewp_pure (InjL _) || ewp_pure (InjR _).
Tactic Notation "ewp_pair" := ewp_pure (Pair _ _).
Tactic Notation "ewp_closure" := ewp_pure (Rec _ _ _).

Ltac ewp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_ewp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "ewp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (ewp_def ?E ?e ?P ?Q) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; ewp_bind_core K)
          | fail 1 "ewp_bind: cannot find" efoc "in" e ]
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

Ltac ewp_apply_core lem tac_suc tac_fail := first
  [iPoseProofCore lem as false (fun H =>
     lazymatch goal with
     | |- envs_entails _ (ewp_def ?E ?e ?P ?Q) =>
         reshape_expr e ltac:(fun K e' => ewp_bind_core K; tac_suc H)
     | _ => fail 1 "wp_apply: not a 'wp'"
     end)
  |tac_fail ltac:(fun _ => ewp_apply_core lem tac_suc tac_fail)
  |let P := type of lem in
   fail "ewp_apply: cannot apply" lem ":" P ].

Tactic Notation "ewp_apply" open_constr(lem) :=
  ewp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try ewp_expr_simpl)
                    ltac:(fun cont => fail).
Tactic Notation "ewp_smart_apply" open_constr(lem) :=
  ewp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try ewp_expr_simpl)
                            ltac:(fun cont => ewp_pure _; []; cont ()).

(** Better tactics :) *)
Tactic Notation "ewp_apply" open_constr(lem) "as" constr(pat) :=
  ewp_apply lem; last iIntros pat.
Tactic Notation "ewp_apply" open_constr(lem) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  ewp_apply lem; last iIntros ( x1 ) pat.
Tactic Notation "ewp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  ewp_apply lem; last iIntros ( x1 x2 ) pat.
Tactic Notation "ewp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  ewp_apply lem; last iIntros ( x1 x2 x3 ) pat.
Tactic Notation "ewp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  ewp_apply lem; last iIntros ( x1 x2 x3 x4 ) pat.
Tactic Notation "ewp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  ewp_apply lem; last iIntros ( x1 x2 x3 x4 x5 ) pat.
Tactic Notation "ewp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  ewp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 ) pat.
Tactic Notation "ewp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  ewp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 ) pat.
Tactic Notation "ewp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  ewp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat.
Tactic Notation "ewp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) :=
  ewp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat.
Tactic Notation "ewp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")"
    constr(pat) :=
  ewp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat.


Tactic Notation "ewp_smart_apply" open_constr(lem) "as" constr(pat) :=
  ewp_smart_apply lem; last iIntros pat.
Tactic Notation "ewp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  ewp_smart_apply lem; last iIntros ( x1 ) pat.
Tactic Notation "ewp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  ewp_smart_apply lem; last iIntros ( x1 x2 ) pat.
Tactic Notation "ewp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  ewp_smart_apply lem; last iIntros ( x1 x2 x3 ) pat.
Tactic Notation "ewp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  ewp_smart_apply lem; last iIntros ( x1 x2 x3 x4 ) pat.
Tactic Notation "ewp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  ewp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 ) pat.
Tactic Notation "ewp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  ewp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 ) pat.
Tactic Notation "ewp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  ewp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 ) pat.
Tactic Notation "ewp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  ewp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat.
Tactic Notation "ewp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) :=
  ewp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat.
Tactic Notation "ewp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")"
    constr(pat) :=
  ewp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat.

Section heap_tactics.
  Context `{probeffGS Σ}.

  Lemma tac_ewp_alloc Δ Δ' E j K v Φ Ψ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    (∀ (l : loc),
        match envs_app false (Esnoc Enil j (l ↦{DfracOwn 1} v)) Δ' with
        | Some Δ'' =>
            envs_entails Δ'' (EWP fill K (Val $ LitV $ LitLoc l) @ E <| Ψ |> {{ Φ }})
        | None => False
        end) →
    envs_entails Δ (EWP fill K (Alloc (Val v)) @ E <| Ψ |> {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ? HΔ.
    rewrite -ewp_pure_bind.
    2: { done. }
    eapply bi.wand_apply.
    { apply ewp_alloc. } 
    rewrite left_id into_laterN_env_sound. simpl.
    apply (bi.laterN_mono 1 (of_envs Δ')), bi.forall_intro=> l.
    specialize (HΔ l).
    destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [| contradiction].
    rewrite envs_app_sound //; simpl.
    apply bi.wand_intro_l.
    rewrite right_id.
    rewrite bi.wand_elim_r //.
  Qed.

  (* Lemma tac_ewp_allocN Δ Δ' E j K v n Φ a :
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
     Qed. *)

  Lemma tac_ewp_load Δ Δ' E i K b l dq v Φ Ψ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (b, (l ↦{dq} v)%I) →
    envs_entails Δ' (EWP fill K (Val v) @ E <| Ψ |> {{ Φ }}) →
    envs_entails Δ (EWP fill K (Load (Val $ LitV $ LitLoc l)) @ E <| Ψ |> {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ?? Hi.
    rewrite -ewp_pure_bind; [|done].
    eapply bi.wand_apply.
    { apply bi.wand_entails, ewp_load. }
    rewrite into_laterN_env_sound.
    rewrite -bi.later_sep.
    rewrite envs_lookup_split //; simpl.
    apply bi.later_mono.
    destruct b; simpl.
    * iIntros "[#$ He]". iIntros "_". iApply Hi. iApply "He". iFrame "#".
    * by apply bi.sep_mono_r, bi.wand_mono.
  Qed.

  Lemma tac_ewp_store Δ Δ' E i K l v v' Φ Ψ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (false, (l ↦ v)%I) →
    match envs_simple_replace i false (Esnoc Enil i (l ↦ v')%I) Δ' with
    | Some Δ'' => envs_entails Δ'' (EWP fill K (Val $ LitV LitUnit) @ E <| Ψ |> {{ Φ }})
    | None => False
    end →
    envs_entails Δ (EWP fill K (Store (Val $ LitV $ LitLoc l) (Val v')) @ E <| Ψ |> {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ?? Hcnt.
    destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
    rewrite -ewp_pure_bind; [|done].
    eapply bi.wand_apply.
    { eapply bi.wand_entails, ewp_store. }
    rewrite into_laterN_env_sound.
    rewrite -bi.later_sep envs_simple_replace_sound //; simpl.
    rewrite right_id. by apply bi.later_mono, bi.sep_mono_r, bi.wand_mono.
  Qed.

End heap_tactics.

Tactic Notation "ewp_alloc" ident(l) "as" constr(H) :=
  let Htmp := iFresh in
  let finish _ :=
    first [intros l | fail 1 "wp_alloc:" l "not fresh"];
    pm_reduce;
    lazymatch goal with
    | |- False => fail 1 "ewp_alloc:" H "not fresh"
    | _ => iDestructHyp Htmp as H; ewp_finish
    end in
  ewp_pures;
  (** The code first tries to use allocation lemma for a single reference,
     ie, [tac_wp_alloc] (respectively, [tac_twp_alloc]).
     If that fails, it tries to use the lemma [tac_wp_allocN]
     (respectively, [tac_twp_allocN]) for allocating an array.
     Notice that we could have used the array allocation lemma also for single
     references. However, that would produce the resource l ↦∗ [v] instead of
     l ↦ v for single references. These are logically equivalent assertions
     but are not equal. *)
lazymatch goal with
  | |- envs_entails _ (ewp_def ?E ?e ?P ?Q) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_ewp_alloc _ _ _ Htmp K))
          |fail 1 "ewp_alloc: cannot find 'Alloc' in" e];
        [tc_solve
        |finish ()]
    in
    (* let process_array _ :=
           first
             [reshape_expr e ltac:(fun K e' => eapply (tac_wp_allocN _ _ _ Htmp K))
             |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
           [idtac| tc_solve
            |finish ()]
       in (process_array ()) || *) (process_single ())
  | _ => fail "ewp_alloc: not a 'ewp'"
  end.


Tactic Notation "ewp_alloc" ident(l) :=
  ewp_alloc l as "?".

Tactic Notation "ewp_load" :=
  let solve_ewptac_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "ewp_load: cannot find" l "↦ ?" in
  ewp_pures;
  lazymatch goal with
  | |- envs_entails _ (ewp_def ?E ?e ?P ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_ewp_load _ _ _ _ K))
      |fail 1 "ewp_load: cannot find 'Load' in" e];
    [tc_solve
    |solve_ewptac_mapsto ()
    |ewp_finish]
  (* | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
       first
         [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load _ _ _ _ K))
         |fail 1 "wp_load: cannot find 'Load' in" e];
       [tc_solve
       |solve_wptac_mapsto ()
       |wp_finish] *)
  | _ => fail "ewp_load: not a 'ewp'"
  end.

Tactic Notation "ewp_store" :=
  let solve_ewptac_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "ewp_store: cannot find" l "↦ ?" in
  ewp_pures;
  lazymatch goal with
  | |- envs_entails _ (ewp_def ?E ?e ?P ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_ewp_store _ _ _ _ K))
      |fail 1 "ewp_store: cannot find 'Store' in" e];
    [tc_solve
    |solve_ewptac_mapsto ()
    |pm_reduce; first [ewp_seq|ewp_finish]]
  (* | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
       first
         [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store _ _ _ _ K))
         |fail 1 "wp_store: cannot find 'Store' in" e];
       [tc_solve
       |solve_wptac_mapsto ()
       |pm_reduce; first [wp_seq|wp_finish]] *)
  | _ => fail "ewp_store: not a 'ewp'"
  end.

Section tape_tactics.
  Context `{probeffGS Σ}.

  Lemma tac_ewp_alloctape Δ Δ' E j K N z Φ Ψ :
    TCEq N (Z.to_nat z) ->
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    (∀ l,
        match envs_app false (Esnoc Enil j (l ↪N (N ; [] ))) Δ' with
        | Some Δ'' =>
            envs_entails Δ'' (EWP fill K (Val $ LitV $ LitLbl l) @ E <| Ψ |> {{ Φ }})
        | None => False
        end) →
    envs_entails Δ (EWP fill K (AllocTape (Val $ LitV $ LitInt z)) @ E <| Ψ |> {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ? ? HΔ.
    rewrite -ewp_pure_bind; [|done].
    eapply bi.wand_apply.
    { by apply ewp_alloc_tape. }
    rewrite left_id into_laterN_env_sound.
    apply (bi.laterN_mono 1 (of_envs Δ')), bi.forall_intro=> l.
    specialize (HΔ l).
    destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [| contradiction].
    rewrite envs_app_sound //; simpl.
    apply bi.wand_intro_l.
    rewrite right_id.
    rewrite bi.wand_elim_r //.
  Qed.


  Lemma tac_ewp_rand_tape Δ1 Δ2 E i j K l N z n ns Φ Ψ :
    TCEq N (Z.to_nat z) ->
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    envs_lookup i Δ2 = Some (false, (l ↪N (N; (n::ns)))%I) ->
    (match envs_simple_replace i false (Esnoc Enil i (l ↪N (N; ns))) Δ2 with
    | Some Δ3 =>
        (match envs_app false (Esnoc Enil j (⌜n ≤ N⌝%I)) Δ3 with
        | Some Δ4 => envs_entails Δ4 (EWP fill K (Val $ LitV $ LitInt n) @ E <| Ψ |> {{ Φ }})
        | None    => False
        end)
    | None    => False
    end) →
    envs_entails Δ1 (EWP (fill K (Rand (LitV (LitInt z)) (LitV (LitLbl l)))) @ E <| Ψ |> {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ?? Hi HΔ.
    destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
    rewrite -ewp_pure_bind; [|done].
    eapply bi.wand_apply.
    { by apply bi.wand_entails, ewp_rand_tape. }
    rewrite into_laterN_env_sound.
    rewrite -bi.later_sep.
    apply bi.later_mono.
    rewrite (envs_simple_replace_sound Δ2 Δ3 i) /= //; simpl.
    iIntros "[$ He]".
    iIntros "(Htp & %Hleq)".
    destruct (envs_app _ _ _) as [Δ4 |] eqn: HΔ4; [|contradiction].
    rewrite envs_app_sound //; simpl.
    iApply HΔ.
    iApply ("He" with "[$Htp]").
    iSplit; last done.
    by iPureIntro. 
  Qed.

End tape_tactics.

Tactic Notation "ewp_alloctape" ident(l) "as" constr(H) :=
  let Htmp := iFresh in
  let finish _ :=
    first [intros l | fail 1 "ewp_alloctape:" l "not fresh"];
    pm_reduce;
    lazymatch goal with
    | |- False => fail 1 "ewp_alloc:" H "not fresh"
    | _ => iDestructHyp Htmp as H; ewp_finish
    end in
  ewp_pures;
lazymatch goal with
  | |- envs_entails _ (ewp_def ?E ?e ?P ?Q) =>
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_ewp_alloctape _ _ _ Htmp K))
          |fail 1 "ewp_alloc: cannot find 'AllocTape' in" e];
        [tc_solve | tc_solve
        |finish ()]
(* | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
           first
             [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloctape _ _ _ Htmp K))
             |fail 1 "wp_alloc: cannot find 'AllocTape' in" e];
           [tc_solve | tc_solve
           |finish ()] *)
  | _ => fail "ewp_alloc: not a 'wp'"
  end.


Tactic Notation "ewp_alloctape" ident(l) :=
  ewp_alloctape l as "?".

Tactic Notation "ewp_randtape" "as" constr(H) :=
  let Htmp := iFresh in
  let solve_ewptac_mapsto_tape _ :=
    let l := match goal with |- _ = Some (_, (?l ↪{_}_ (_ ; (_ :: _)))%I) => l end in
    iAssumptionCore || fail "ewp_load: cannot find" l "↪N ?" in
  let finish _ :=
    pm_reduce;
    lazymatch goal with
    | |- False => fail 1 "ewp_alloc:" H "not fresh"
    | _ => iDestructHyp Htmp as H; ewp_finish
    end in
  ewp_pures;
  lazymatch goal with
  | |- envs_entails _ (ewp_def ?E ?e ?P ?Q) =>
      first
        [reshape_expr e ltac:(fun K e' => eapply (tac_ewp_rand_tape _ _ _ _ Htmp K))
        |fail 1 "ewp_load: cannot find 'Rand' in" e];
      [ (* Delay resolution of TCEq *)
      | tc_solve
      | solve_ewptac_mapsto_tape ()
      |];
      [try tc_solve | finish ()]
  (* | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
         first
           [reshape_expr e ltac:(fun K e' => eapply (tac_wp_rand_tape _ _ _ _ Htmp K))
           |fail 1 "wp_load: cannot find 'Rand' in" e];
         [try tc_solve
         |tc_solve
         |try (solve_wptac_mapsto_tape ())
         |finish ()] *)
  | _ => fail "ewp_load: not a 'ewp'"
  end.

Tactic Notation "ewp_randtape" :=
  ewp_randtape as "%".
