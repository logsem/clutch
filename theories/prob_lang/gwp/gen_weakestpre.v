From iris.bi Require Export bi updates.
From iris.base_logic.lib Require Import fancy_updates.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
(* From clutch.common Require Import ectx_language language. *)
From clutch.prob_lang Require Import lang tactics notation class_instances.
Set Default Proof Using "Type*".

Section GenWp_mixin.
  Context {Σ : gFunctors} `{!invGS_gen hlc Σ}.
  Context (laters : bool).
  Context (gwp : coPset → expr  → (val → iProp Σ) → iProp Σ).
  Context (gwp_pointsto : loc → dfrac → val → iProp Σ).

  Record GenWpMixin := {
    mixin_gwp_pointsto_timeless l dq v : Timeless (gwp_pointsto l dq v);

    mixin_gwp_value E Φ v : Φ v ⊢ gwp E (of_val v) Φ;
      mixin_gwp_fupd E Φ e : gwp E e (λ v, |={E}=> Φ v) ⊢ gwp E e Φ;
    mixin_gwp_bind K E e Φ :
      gwp E e (λ v, gwp E (fill K (of_val v)) Φ ) ⊢ gwp E (fill K e) Φ;
    mixin_gwp_pure_step E e1 e2 φ n Φ :
      PureExec φ n e1 e2 →
      φ →
      ▷^(if laters then n else 0) gwp E e2 Φ ⊢ gwp E e1 Φ;

    mixin_gwp_alloc E (v : val) Φ :
     ▷?laters (∀ l, gwp_pointsto l (DfracOwn 1) v -∗ Φ #l) ⊢ gwp E (ref v) Φ;
    mixin_gwp_load E v l dq Φ :
      ▷?laters gwp_pointsto l dq v -∗
      ▷?laters (gwp_pointsto l dq v -∗ Φ v) -∗
      gwp E (! #l) Φ;
    mixin_gwp_store E (v v' : val) l Φ :
      ▷?laters gwp_pointsto l (DfracOwn 1) v' -∗
      ▷?laters (gwp_pointsto l (DfracOwn 1) v -∗ Φ (LitV (LitUnit))%V) -∗
      gwp E (#l <- v) Φ;
  }.
End GenWp_mixin.

Structure GenWp Σ `{invGS_gen hlc Σ} := {
  gwp_laters : bool;

  gwp : coPset → expr  → (val → iProp Σ) → iProp Σ;
  gwp_pointsto : loc → dfrac → val → iProp Σ;

  gwp_mixin : GenWpMixin gwp_laters gwp gwp_pointsto;
}.

Arguments Build_GenWp {_ _ _ _ _ _}.
Arguments gwp {_ _ _}.
Arguments gwp_pointsto {_ _ _}.
Arguments gwp_laters {_ _ _}.

Notation "'GWP' e @ g ; E {{ Φ } }" := (gwp g E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'GWP' e @ g ; E {{ v , Q } }" := (gwp g E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'GWP'  e  '/' @  '[' g ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(* Texan triples *)
Notation "'G{{{' P } } } e @ g ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷?(gwp_laters g) (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ GWP e @ g; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' G{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' g ;  '/' E  ']' '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.

Notation "'G{{{' P } } } e @ g ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷?(gwp_laters g) (Q -∗ Φ pat%V) -∗ GWP e @ g; E {{ Φ }})%I
    (at level 20,
     format "'[hv' G{{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' g ;  '/' E  ']' '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'G{{{' P  } } } e @ g ; E {{{ x .. y , 'RET' pat ; Q  } } }" :=
  (∀ Φ, P -∗ ▷?(gwp_laters g) (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ GWP e @ g; E {{ Φ }}) : stdpp_scope.
Notation "'G{{{' P  } } } e @ g ; E {{{ 'RET' pat ; Q  } } }" :=
  (∀ Φ, P -∗ ▷?(gwp_laters g) (Q -∗ Φ pat%V) -∗ GWP e @ g; E {{ Φ }}) : stdpp_scope.

Notation "l G↦[ g ] dq v" := (gwp_pointsto g l dq v)
    (at level 20, dq custom dfrac at level 1, format "l  G↦[ g ] dq  v") : bi_scope.

Section genWp.
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.

  #[global] Instance gwp_pointsto_timeless l dq v : Timeless (gwp_pointsto g l dq v).
  Proof. apply gwp_mixin. Qed.

  Lemma gwp_value E Φ v : Φ v ⊢ GWP (of_val v) @ g ; E {{ Φ }}.
  Proof. apply gwp_mixin. Qed.
  Lemma gwp_fupd E Φ e : GWP e @ g ; E {{ v, |={E}=> Φ v }} ⊢ GWP e @ g ; E {{ Φ }}.
  Proof. apply gwp_mixin. Qed.
  Lemma gwp_bind K E e Φ :
    GWP e @ g ; E {{ v, GWP fill K (of_val v) @ g ; E {{ Φ  }} }} ⊢ GWP fill K e @ g ; E {{ Φ }}.
  Proof. apply gwp_mixin. Qed.
  Lemma gwp_pure_step E e1 e2 φ n Φ :
    PureExec φ n e1 e2 →
    φ →
    ▷^(if gwp_laters g then n else 0) GWP e2 @ g ; E {{ Φ }} ⊢ GWP e1 @ g ; E {{ Φ }}.
  Proof. apply gwp_mixin. Qed.

  Lemma gwp_alloc E (v : val) Φ :
    ▷?(gwp_laters g) (∀ l, l G↦[g] v -∗ Φ #l) ⊢ GWP ref v @ g ; E {{ Φ }}.
  Proof. apply gwp_mixin. Qed.
  Lemma gwp_load E l v (dq : dfrac) Φ :
    ▷?(gwp_laters g) l G↦[g]{dq} v -∗ ▷?(gwp_laters g) (l G↦[g]{dq} v -∗ Φ v) -∗ GWP (! #l) @ g ; E {{ Φ }}.
  Proof. apply gwp_mixin. Qed.
  Lemma gwp_store E l (v v' : val) Φ:
    ▷?(gwp_laters g) l G↦[g] v' -∗ ▷?(gwp_laters g) (l G↦[g] v -∗ Φ #()) -∗ GWP #l <- v @ g ; E {{ Φ }}.
  Proof. apply gwp_mixin. Qed.

  Lemma tac_gwp_expr_eval Δ E Φ e e' :
    (∀ (e'':=e'), e = e'') →
    envs_entails Δ (GWP e' @ g ; E {{ Φ }}) → envs_entails Δ (GWP e @ g ; E {{ Φ }}).
  Proof. by intros ->. Qed.

  Lemma tac_gwp_pure_later Δ Δ' E K e1 e2 φ n Φ :
    PureExec φ n e1 e2 →
    φ →
    MaybeIntoLaterNEnvs (if gwp_laters g then n else 0) Δ Δ' →
    envs_entails Δ' (GWP (fill K e2) @ g ; E {{ Φ }}) →
    envs_entails Δ (GWP (fill K e1) @ g ; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ??? HΔ'. rewrite into_laterN_env_sound /=.
    (* We want [pure_exec_fill] to be available to TC search locally. *)
    pose proof @pure_exec_fill.
    rewrite HΔ' -gwp_pure_step //.
  Qed.

  Lemma tac_gwp_value_nofupd Δ E Φ v :
    envs_entails Δ (Φ v) → envs_entails Δ (GWP (of_val v) @ g ; E {{ Φ }}).
  Proof. rewrite envs_entails_unseal=> ->. apply gwp_value. Qed.

  Lemma tac_gwp_value' Δ E Φ v :
    envs_entails Δ (|={E}=> Φ v) → envs_entails Δ (GWP (of_val v) @ g ; E {{ Φ }}).
  Proof. rewrite envs_entails_unseal=> ->. by rewrite -gwp_fupd -gwp_value. Qed.

  Lemma tac_gwp_bind K Δ E Φ e f :
    f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
    envs_entails Δ (GWP e @ g ; E {{ v, GWP f (Val v) @ g ; E {{ Φ }} }})%I →
    envs_entails Δ (GWP fill K e @ g ; E {{ Φ }}).
  Proof. rewrite envs_entails_unseal=> -> ->. by apply: gwp_bind. Qed.

End genWp.

Tactic Notation "gwp_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (gwp ?g ?E ?e ?Q) =>
    notypeclasses refine (tac_gwp_expr_eval _ _ _ e _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
  | _ => fail "gwp_expr_eval: not a 'wp'"
  end.

Ltac gwp_expr_simpl := gwp_expr_eval simpl.

(** Simplify the goal if it is [wp] of a value.
  If the postcondition already allows a fupd, do not add a second one.
  But otherwise, *do* add a fupd. This ensures that all the lemmas applied
  here are bidirectional, so we never will make a goal unprovable. *)
Ltac gwp_value_head :=
  lazymatch goal with
  | |- envs_entails _ (gwp ?g ?E (of_val _) (λ _, fupd ?E _ _)) =>
      eapply tac_gwp_value_nofupd
  | |- envs_entails _ (gwp ?g ?E (of_val _) (λ _, wp _ ?E _ _)) =>
      eapply tac_gwp_value_nofupd
  | |- envs_entails _ (gwp ?g ?E (of_val _) _) =>
      eapply tac_gwp_value'
  end.

Ltac gwp_finish :=
  (* simplify occurences of [gwp_pointsto] projections  *)
  (* rewrite ?[gwp_pointsto _ _ _]/=; *)
    (* simplify occurences of subst/fill *)
    gwp_expr_simpl;
  (* in case we have reached a value, get rid of the wp *)
  try gwp_value_head;
  (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and λs caused by gwp_value *)
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
Tactic Notation "gwp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (gwp ?g ?E ?e ?Q) =>
      let e := eval simpl in e in
        reshape_expr e ltac:(fun K e' =>
           unify e' efoc;
           eapply (tac_gwp_pure_later _ _ _ K e');
           [tc_solve                       (* PureExec *)
           |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *)
           |tc_solve                       (* IntoLaters *)
           |gwp_finish                      (* new goal *)
        ])
        || fail "gwp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "gwp_pure: not a 'wp'"
  end.

Tactic Notation "gwp_pure" :=
  gwp_pure _.

Ltac gwp_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
      progress repeat (gwp_pure _; [])
    | gwp_finish (* In case gwp_pure never ran, make sure we do the usual cleanup. *)
    ].

(** Unlike [wp_pures], the tactics [wp_rec] and [wp_lam] should also reduce
    lambdas/recs that are hidden behind a definition, i.e. they should use
    [AsRecV_recv] as a proper instance instead of a [Hint Extern].

    We achieve this by putting [AsRecV_recv] in the current environment so that it
    can be used as an instance by the typeclass resolution system. We then perform
    the reduction, and finally we clear this new hypothesis. *)
Tactic Notation "gwp_rec" :=
  let H := fresh in
  assert (H := AsRecV_recv);
  gwp_pure (App _ _);
  clear H.

Tactic Notation "gwp_if" := gwp_pure (If _ _ _).
Tactic Notation "gwp_if_true" := gwp_pure (If (LitV (LitBool true)) _ _).
Tactic Notation "gwp_if_false" := gwp_pure (If (LitV (LitBool false)) _ _).
Tactic Notation "gwp_unop" := gwp_pure (UnOp _ _).
Tactic Notation "gwp_binop" := gwp_pure (BinOp _ _ _).
Tactic Notation "gwp_op" := gwp_unop || gwp_binop.
Tactic Notation "gwp_lam" := gwp_rec.
Tactic Notation "gwp_let" := gwp_pure (Rec BAnon (BNamed _) _); gwp_lam.
Tactic Notation "gwp_seq" := gwp_pure (Rec BAnon BAnon _); gwp_lam.
Tactic Notation "gwp_proj" := gwp_pure (Fst _) || gwp_pure (Snd _).
Tactic Notation "gwp_case" := gwp_pure (Case _ _ _).
Tactic Notation "gwp_match" := gwp_case; gwp_pure (Rec _ _ _); gwp_lam.
Tactic Notation "gwp_inj" := gwp_pure (InjL _) || gwp_pure (InjR _).
Tactic Notation "gwp_pair" := gwp_pure (Pair _ _).
Tactic Notation "gwp_closure" := gwp_pure (Rec _ _ _).

Ltac gwp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_gwp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "gwp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (gwp ?g ?E ?e ?Q) =>
      first [ reshape_expr e ltac:(fun K e' => unify e' efoc; gwp_bind_core K)
            | fail 1 "gwp_bind: cannot find" efoc "in" e ]
  | _ => fail "gwp_bind: not a 'gwp'"
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

Ltac gwp_apply_core lem tac_suc tac_fail :=
  first
   [iPoseProofCore lem as false (fun H =>
         lazymatch goal with
         | |- envs_entails _ (gwp ?g ?E ?e ?Q) =>
             reshape_expr e ltac:(fun K e' => gwp_bind_core K; tac_suc H)
         | _ => fail 1 "gwp_apply: not a 'gwp'"
         end)
   |tac_fail ltac:(fun _ => gwp_apply_core lem tac_suc tac_fail)
   |let P := type of lem in
    fail "gwp_apply: cannot apply" lem ":" P ].

Tactic Notation "gwp_apply" open_constr(lem) :=
  gwp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try gwp_expr_simpl)
                            ltac:(fun cont => fail).
Tactic Notation "gwp_smart_apply" open_constr(lem) :=
  gwp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try gwp_expr_simpl)
                            ltac:(fun cont => gwp_pure _; []; cont ()).

(** Better tactics :) *)
Tactic Notation "gwp_apply" open_constr(lem) "as" constr(pat) :=
  gwp_apply lem; last iIntros pat.
Tactic Notation "gwp_apply" open_constr(lem) "as" "(" simple_intropattern(x1) ")"
  constr(pat) :=
  gwp_apply lem; last iIntros ( x1 ) pat.
Tactic Notation "gwp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
  simple_intropattern(x2) ")" constr(pat) :=
  gwp_apply lem; last iIntros ( x1 x2 ) pat.
Tactic Notation "gwp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
  simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  gwp_apply lem; last iIntros ( x1 x2 x3 ) pat.
Tactic Notation "gwp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
  simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
  constr(pat) :=
  gwp_apply lem; last iIntros ( x1 x2 x3 x4 ) pat.
Tactic Notation "gwp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
  simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
  simple_intropattern(x5) ")" constr(pat) :=
  gwp_apply lem; last iIntros ( x1 x2 x3 x4 x5 ) pat.
Tactic Notation "gwp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
  simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
  simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  gwp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 ) pat.
Tactic Notation "gwp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
  simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
  simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
  constr(pat) :=
  gwp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 ) pat.
Tactic Notation "gwp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
  simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
  simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
  simple_intropattern(x8) ")" constr(pat) :=
  gwp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat.
Tactic Notation "gwp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
  simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
  simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
  simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) :=
  gwp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat.
Tactic Notation "gwp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
  simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
  simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
  simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")"
  constr(pat) :=
  gwp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat.


Tactic Notation "gwp_smart_apply" open_constr(lem) "as" constr(pat) :=
  gwp_smart_apply lem; last iIntros pat.
Tactic Notation "gwp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1) ")"
  constr(pat) :=
  gwp_smart_apply lem; last iIntros ( x1 ) pat.
Tactic Notation "gwp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
  simple_intropattern(x2) ")" constr(pat) :=
  gwp_smart_apply lem; last iIntros ( x1 x2 ) pat.
Tactic Notation "gwp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
  simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  gwp_smart_apply lem; last iIntros ( x1 x2 x3 ) pat.
Tactic Notation "gwp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
  simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
  constr(pat) :=
  gwp_smart_apply lem; last iIntros ( x1 x2 x3 x4 ) pat.
Tactic Notation "gwp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
  simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
  simple_intropattern(x5) ")" constr(pat) :=
  gwp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 ) pat.
Tactic Notation "gwp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
  simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
  simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  gwp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 ) pat.
Tactic Notation "gwp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
  simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
  simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
  constr(pat) :=
  gwp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 ) pat.
Tactic Notation "gwp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
  simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
  simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
  simple_intropattern(x8) ")" constr(pat) :=
  gwp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat.
Tactic Notation "gwp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
  simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
  simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
  simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) :=
  gwp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat.
Tactic Notation "gwp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
  simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
  simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
  simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")"
  constr(pat) :=
  gwp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat.

Section gwp_heap.
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.

  Lemma tac_gwp_alloc Δ Δ' E j K v Φ :
    MaybeIntoLaterNEnvs (if gwp_laters g then 1 else 0) Δ Δ' →
    (∀ (l : loc),
        match envs_app false (Esnoc Enil j (l G↦[g] v)) Δ' with
        | Some Δ'' =>
            envs_entails Δ'' (GWP fill K (Val #l) @ g ; E {{ Φ }})
        | None => False
        end) →
    envs_entails Δ (GWP fill K (ref v) @ g ; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ? HΔ.
    iIntros "HΔ".
    gwp_apply gwp_bind.
    rewrite into_laterN_env_sound.
    gwp_apply gwp_alloc.
    iIntros (l) "Hl".
    specialize (HΔ l).
    destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [| contradiction].
    rewrite envs_app_sound //; simpl.
    iSpecialize ("HΔ" with "[$Hl]").
    by iApply HΔ.
  Qed.

  Lemma tac_gwp_load Δ Δ' E i K b l dq v Φ :
    MaybeIntoLaterNEnvs (if gwp_laters g then 1 else 0) Δ Δ' →
    envs_lookup i Δ' = Some (b, (l G↦[g] {dq} v)%I) →
    envs_entails Δ' (GWP fill K (Val v) @ g ; E {{ Φ }}) →
    envs_entails Δ (GWP fill K (! #l) @ g ; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ?? Hi.
    rewrite -gwp_bind.
    eapply bi.wand_apply.
    { apply bi.wand_entails, gwp_load. }
    rewrite into_laterN_env_sound.
    destruct (gwp_laters g).
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

  Lemma tac_gwp_store Δ Δ' E i K l v v' Φ :
    MaybeIntoLaterNEnvs (if gwp_laters g then 1 else 0) Δ Δ' →
    envs_lookup i Δ' = Some (false, l G↦[g] v)%I →
    match envs_simple_replace i false (Esnoc Enil i (l G↦[g] v')) Δ' with
    | Some Δ'' => envs_entails Δ'' (GWP fill K (Val #()) @ g ; E {{ Φ }})
    | None => False
    end →
    envs_entails Δ (GWP fill K (#l <- v') @ g ; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ?? Hcnt.
    destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
    rewrite -gwp_bind. eapply bi.wand_apply.
    { eapply bi.wand_entails, gwp_store. }
    rewrite into_laterN_env_sound.
    destruct (gwp_laters g).
    - rewrite -bi.later_sep envs_simple_replace_sound //; simpl.
      rewrite right_id. by apply bi.later_mono, bi.sep_mono_r, bi.wand_mono.
    - rewrite envs_simple_replace_sound //; simpl.
      rewrite right_id.
      iIntros "[$ He] H". iApply Hcnt. by iApply "He".
  Qed.

End gwp_heap.

Tactic Notation "gwp_alloc" ident(l) "as" constr(H) :=
  let Htmp := iFresh in
  let finish _ :=
    first [intros l | fail 1 "gwp_alloc:" l "not fresh"];
    pm_reduce;
    lazymatch goal with
    | |- False => fail 1 "gwp_alloc:" H "not fresh"
    | _ => iDestructHyp Htmp as H; gwp_finish
    end in
  gwp_pures;
  lazymatch goal with
  | |- envs_entails _ (gwp ?g ?E ?e ?Q) =>
      let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_gwp_alloc _ _ _ Htmp K))
          |fail 1 "gwp_alloc: cannot find 'Alloc' in" e];
        [tc_solve
        |finish ()]
      in (process_single ())
  | _ => fail "gwp_alloc: not a 'gwp'"
  end.


Tactic Notation "gwp_alloc" ident(l) :=
  gwp_alloc l as "?".

Tactic Notation "gwp_load" :=
  let solve_gwp_pointsto _ :=
    let l := match goal with |- _ = Some (_, (gwp_pointsto _ ?l _ _)%I) => l end in
    iAssumptionCore || fail "gwp_load: cannot find" l "G↦[g] ?" in
  gwp_pures;
  lazymatch goal with
  | |- envs_entails _ (gwp ?g ?E ?e ?Q) =>
      first
        [reshape_expr e ltac:(fun K e' => eapply (tac_gwp_load _ _ _ _ K))
        |fail 1 "gwp_load: cannot find 'Load' in" e];
      [tc_solve
      |solve_gwp_pointsto ()
      |gwp_finish]
  | _ => fail "gwp_load: not a 'gwp'"
  end.

Tactic Notation "gwp_store" :=
  let solve_gwp_pointsto _ :=
    let l := match goal with |- _ = Some (_, (gwp_pointsto _ ?l _ _)%I) => l end in
    iAssumptionCore || fail "gwp_store: cannot find" l "G↦[g] ?" in
  gwp_pures;
  lazymatch goal with
  | |- envs_entails _ (gwp ?g ?E ?e ?Q) =>
      first
        [reshape_expr e ltac:(fun K e' => eapply (tac_gwp_store _ _ _ _ K))
        |fail 1 "gwp_store: cannot find 'Store' in" e];
      [tc_solve
      |solve_gwp_pointsto ()
      |pm_reduce; first [gwp_seq|gwp_finish]]
    | _ => fail "gwp_store: not a 'gwp'"
    end.
