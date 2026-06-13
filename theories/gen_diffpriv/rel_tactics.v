(** Relational symbolic-execution tactics (generic DP, [gen_prob_lang]).

    Ported from [diffpriv/rel_tactics].  The [tac_rel_*] driver lemmas live in a
    section that pins the [gen_lang Sg] canonical-structure chain; [Sg] is an
    explicit leading argument (it is phantom in the [envs_entails Δ Q]
    conclusion, mirroring [spec_tactics]) which the tactic notations supply via
    the [rel_get_sig] hook reading [Sg] off the in-context [diffprivRGS Sg _].

    The rand/alloctape relational tactics ([rel_rand_*], [rel_alloctape_*]) are
    omitted: their driver lemmas build on the [prob_lang]-only [refines_rand_*]
    / [refines_alloctape_*] rules, which have no [gen_prob_lang] counterpart
    (sampling there goes through the abstract distribution signature, and the
    generalized type system has no sampling rule). *)
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import
     coq_tactics ltac_tactics
     reduction.
From clutch.prelude Require Import stdpp_ext.
From clutch.common Require Import language ectx_language ectxi_language locations.
From clutch.gen_diffpriv Require Import primitive_laws model app_rel_rules proofmode.
From clutch.gen_prob_lang Require Import class_instances notation tactics lang.
From clutch.gen_prob_lang.spec Require Export spec_tactics.

(** Read the distribution signature [Sg] off the in-context [diffprivRGS] (or
    [diffprivGS]) hypothesis and pass it to the continuation [k].  The
    [tac_rel_*] lemmas take [Sg] as an explicit leading argument that does not
    appear in their [envs_entails] conclusion, so the tactics must supply it. *)
Ltac rel_get_sig k :=
  lazymatch goal with
  | _ : diffprivRGS ?S _ |- _ => k S
  | _ : diffprivGS ?S _ |- _ => k S
  | _ => k open_constr:(_)
  end.

Section tactics.
  Context (Sg : Sig).
  Canonical Structure gen_ectxi_lang_rt := gen_ectxi_lang Sg.
  Canonical Structure gen_ectx_lang_rt := gen_ectx_lang Sg.
  Canonical Structure gen_lang_rt := gen_lang Sg.
  Canonical Structure gen_markov_rt := lang_markov (gen_lang Sg).
  Context `{!diffprivRGS Sg Σ}.

  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

(** * General-purpose tactics *)
Lemma tac_rel_bind_l e' K ℶ E e t A :
  e = fill K e' →
  envs_entails ℶ (REL fill K e' << t @ E : A) →
  envs_entails ℶ (REL e << t @ E : A).
Proof. intros. subst. assumption. Qed.

Lemma tac_rel_bind_r (t' : expr) K ℶ E e t A :
  t = fill K t' →
  envs_entails ℶ (REL e << fill K t' @ E : A) →
  envs_entails ℶ (REL e << t @ E : A).
Proof. intros. subst. assumption. Qed.

(** * Symbolic execution *)

(** Pure reductions *)

Lemma tac_rel_pure_l K e1 ℶ ℶ' E e e2 eres ϕ n m t A :
  e = fill K e1 →
  PureExec (Λ := gen_lang Sg) ϕ n e1 e2 →
  ϕ →
  m = n ∨ m = 0 →
  MaybeIntoLaterNEnvs m ℶ ℶ' →
  eres = fill K e2 →
  envs_entails ℶ' (REL eres << t @ E : A) →
  envs_entails ℶ (REL e << t @ E : A).
Proof.
  rewrite envs_entails_unseal.
  intros Hfill Hpure Hϕ Hm ?? Hp. subst.
  destruct Hm as [-> | ->]; rewrite into_laterN_env_sound /= Hp.
  - rewrite -refines_pure_l //.
  - rewrite -refines_pure_l //. apply bi.laterN_intro.
Qed.

Lemma tac_rel_pure_r K e1 ℶ E (e e2 eres : expr) ϕ n t A :
  e = fill K e1 →
  PureExec (Λ := gen_lang Sg) ϕ n e1 e2 →
  ϕ →
  eres = fill K e2 →
  envs_entails ℶ (REL t << eres @ E : A) →
  envs_entails ℶ (REL t << e @ E : A).
Proof.
  intros Hfill Hpure Hϕ ? Hp. subst.
  rewrite -refines_pure_r //.
Qed.

(** Load *)

Lemma tac_rel_load_l_simp K ℶ1 ℶ2 i1 p (l : loc) q v e t eres A E :
  e = fill K (Deref (# l)) →
  MaybeIntoLaterNEnvs 1 ℶ1 ℶ2 →
  envs_lookup i1 ℶ2 = Some (p, l ↦{q} v)%I →
  eres = fill K (of_val v) →
  envs_entails ℶ2 (refines E eres t A) →
  envs_entails ℶ1 (refines E e t A).
Proof.
  rewrite envs_entails_unseal. iIntros (-> ?? -> Hℶ2) "Henvs".
  iDestruct (into_laterN_env_sound with "Henvs") as "Henvs".
  iDestruct (envs_lookup_split with "Henvs") as "[Hl Henvs]"; first done.
  rewrite Hℶ2. iApply (refines_load_l Sg K E l q).
  iExists v.
  destruct p; simpl; [|by iFrame].
  iDestruct "Hl" as "#Hl". iSplitR; [by auto|].
  iIntros "!> _". by iApply "Henvs".
Qed.

Lemma tac_rel_load_r K ℶ1 E i1 p (l : loc) q e t tres A v :
  t = fill K (Deref (# l)) →
  envs_lookup i1 ℶ1 = Some (p, l ↦ₛ{q} v)%I →
  tres = fill K (of_val v) →
  envs_entails ℶ1 (refines E e tres A) →
  envs_entails ℶ1 (refines E e t A).
Proof.
  rewrite envs_entails_unseal. iIntros (-> ? -> Hg) "Henvs".
  iDestruct (envs_lookup_split with "Henvs") as "[Hl Henvs]"; first done.
  rewrite Hg. destruct p; simpl.
  - iDestruct "Hl" as "#Hl". iApply (refines_load_r with "Hl").
    iIntros "_". by iApply "Henvs".
  - by iApply (refines_load_r with "Hl").
Qed.

(** Store *)
Lemma tac_rel_store_l_simpl K ℶ1 ℶ2 ℶ3 i1 (l : loc) v e' v' e t eres A E :
  e = fill K (Store (# l) e') →
  @IntoVal (gen_lang Sg) e' v' →
  MaybeIntoLaterNEnvs 1 ℶ1 ℶ2 →
  envs_lookup i1 ℶ2 = Some (false, l ↦ v)%I →
  envs_simple_replace i1 false (Esnoc Enil i1 (l ↦ v')) ℶ2 = Some ℶ3 →
  eres = fill K #() →
  envs_entails ℶ3 (refines E eres t A) →
  envs_entails ℶ1 (refines E e t A).
Proof.
  rewrite envs_entails_unseal. intros ?????? Hg.
  subst e eres.
  rewrite into_laterN_env_sound envs_simple_replace_sound //; simpl.
  rewrite bi.later_sep.
  rewrite right_id.
  rewrite -(refines_store_l Sg K ⊤ l).
  rewrite -(bi.exist_intro v).
  by rewrite Hg.
Qed.

Lemma tac_rel_store_r K ℶ1 ℶ2 i1 E (l : loc) v e' v' e t eres A :
  e = fill K (Store (# l) e') →
  @IntoVal (gen_lang Sg) e' v' →
  envs_lookup i1 ℶ1 = Some (false, l ↦ₛ v)%I →
  envs_simple_replace i1 false (Esnoc Enil i1 (l ↦ₛ v')) ℶ1 = Some ℶ2 →
  eres = fill K #() →
  envs_entails ℶ2 (refines E t eres A) →
  envs_entails ℶ1 (refines E t e A).
Proof.
  rewrite envs_entails_unseal. intros ????? Hg.
  subst e eres.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id.
  rewrite (refines_store_r Sg E K) //.
  rewrite Hg.
  apply bi.wand_elim_l.
Qed.

(** Alloc *)

Lemma tac_rel_alloc_l_simpl K ℶ1 ℶ2 e t e' v' A E :
  e = fill K (Alloc e') →
  @IntoVal (gen_lang Sg) e' v' →
  MaybeIntoLaterNEnvs 1 ℶ1 ℶ2 →
  (envs_entails ℶ2 (∀ (l : loc),
     (l ↦ v' -∗ refines E (fill K (of_val #l)) t A))) →
  envs_entails ℶ1 (refines E e t A).
Proof.
  rewrite envs_entails_unseal. intros ???; subst.
  rewrite into_laterN_env_sound /=.
  rewrite -(refines_alloc_l Sg K ⊤); eauto.
  apply bi.later_mono.
Qed.

Lemma tac_rel_alloc_r K' ℶ E t' v' e t A :
  t = fill K' (Alloc t') →
  @IntoVal (gen_lang Sg) t' v' →
  envs_entails ℶ (∀ l, l ↦ₛ v' -∗ refines E e (fill K' #l) A) →
  envs_entails ℶ (refines E e t A).
Proof.
  intros ???. subst t.
  rewrite -refines_alloc_r //.
Qed.

End tactics.

Tactic Notation "rel_bind_l" open_constr(efoc) :=
  iStartProof;
  rel_get_sig ltac:(fun Sg =>
    eapply (tac_rel_bind_l Sg efoc));
  [ tp_bind_helper
  | (* new goal *)
  ].

Tactic Notation "rel_bind_r" open_constr(efoc) :=
  iStartProof;
  rel_get_sig ltac:(fun Sg =>
    eapply (tac_rel_bind_r Sg efoc));
  [ tp_bind_helper
  | (* new goal *)
  ].

Ltac rel_bind_ctx_l K :=
  rel_get_sig ltac:(fun Sg =>
    eapply (tac_rel_bind_l Sg _ K));
  [pm_reflexivity || tp_bind_helper
  |].

Ltac rel_bind_ctx_r K :=
  rel_get_sig ltac:(fun Sg =>
    eapply (tac_rel_bind_r Sg _ K));
  [pm_reflexivity || tp_bind_helper
  |].

(** Reshape the expression on the LHS/RHS untill you can apply `tac` to it *)
Ltac rel_reshape_cont_l tac :=
  lazymatch goal with
  | |- envs_entails _ (refines _ (@ectx_language.fill _ ?K ?e) _ _) =>
    reshape_expr e ltac:(fun K' e' =>
      tac (K' ++ K) e')
  | |- envs_entails _ (refines _ ?e _ _) =>
    reshape_expr e ltac:(fun K' e' => tac K' e')
  end.

Ltac rel_reshape_cont_r tac :=
  lazymatch goal with
  | |- envs_entails _ (refines _ _ (@ectx_language.fill _ ?K ?e) _) =>
    reshape_expr e ltac:(fun K' e' =>
      tac (K' ++ K) e')
  | |- envs_entails _ (refines _ _ ?e _) =>
    reshape_expr e ltac:(fun K' e' => tac K' e')
  end.

(** 1. prettify ▷s caused by [MaybeIntoLaterNEnvs]
    2. simplify the goal *)
Ltac rel_finish := pm_prettify; iSimpl.

Ltac rel_values :=
  iStartProof;
  iApply refines_ret;
  eauto with iFrame;
  rel_finish.

Ltac rel_values_na :=
  iStartProof;
  iApply refines_ret_na;
  rel_finish.

Tactic Notation "rel_apply_l" open_constr(lem) :=
  (iPoseProofCore lem as false (fun H =>
    rel_reshape_cont_l ltac:(fun K e =>
      rel_bind_ctx_l K;
      iApplyHyp H)
    || lazymatch iTypeOf H with
      | Some (_,?P) => fail "rel_apply_l: Cannot apply" P
      end));
  try rel_finish.

Tactic Notation "rel_apply_r" open_constr(lem) :=
  (iPoseProofCore lem as false (fun H =>
    rel_reshape_cont_r ltac:(fun K e =>
      rel_bind_ctx_r K;
      iApplyHyp H)
    || lazymatch iTypeOf H with
      | Some (_,?P) => fail "rel_apply_r: Cannot apply" P
      end));
  try lazymatch goal with
  | |- _ ⊆ _ => try solve_ndisj
  end;
  try rel_finish.

Tactic Notation "rel_apply" open_constr(lem) :=
  (iPoseProofCore lem as false (fun H =>
    rel_reshape_cont_l ltac:(fun K_l e_l =>
      rel_bind_ctx_l K_l;
      rel_reshape_cont_r ltac:(fun K_r e_r =>
        rel_bind_ctx_r K_r;
        iApplyHyp H))
    || lazymatch iTypeOf H with
      | Some (_,?P) => fail "rel_apply: Cannot apply" P
      end));
  try lazymatch goal with
  | |- _ ⊆ _ => try solve_ndisj
  end;
  try rel_finish.

(** Pure *)

Tactic Notation "rel_pure_l" open_constr(ef) "in" open_constr(Kf) :=
  iStartProof;
  rel_get_sig ltac:(fun Sg =>
  rel_reshape_cont_l ltac:(fun K e' =>
      unify K Kf;
      unify e' ef;
      eapply (tac_rel_pure_l Sg K e');
      [reflexivity                  (** e = fill K e1 *)
      |tc_solve                     (** PureExec ϕ n e1 e2 *)
      | .. ]);
      [try solve_vals_compare_safe                (** φ *)
      |first [left; reflexivity
             | right; reflexivity]                  (** (m = n) ∨ (m = 0) *)
      |tc_solve                                     (** IntoLaters *)
      |simpl; reflexivity           (** eres = fill K e2 *)
      |rel_finish                   (** new goal *)])
  || fail "rel_pure_l: cannot find the reduct".

Tactic Notation "rel_pure_l" open_constr(ef) := rel_pure_l ef in _.
Tactic Notation "rel_pure_l" := rel_pure_l _ in _.

Tactic Notation "rel_pure_r" open_constr(ef) "in" open_constr(Kf) :=
  iStartProof;
  rel_get_sig ltac:(fun Sg =>
  rel_reshape_cont_r ltac:(fun K e' =>
      unify K Kf;
      unify e' ef;
      eapply (tac_rel_pure_r Sg K e');
      [reflexivity                  (** e = fill K e1 *)
      |tc_solve                     (** PureExec ϕ n e1 e2 *)
      |..]);
      [try solve_vals_compare_safe                (** φ *)
      |simpl; reflexivity           (** eres = fill K e2 *)
      |rel_finish                   (** new goal *)])
  || fail "rel_pure_r: cannot find the reduct".

Tactic Notation "rel_pure_r" open_constr(ef) := rel_pure_r ef in _.
Tactic Notation "rel_pure_r" := rel_pure_r _ in _.

(* TODO: do this in one go, without [repeat]. *)
Ltac rel_pures_l :=
  iStartProof;
  repeat (rel_pure_l _ in _; []). (* The `;[]` makes sure that no side-condition
                             magically spawns. *)
Ltac rel_pures_r :=
  iStartProof;
  repeat (rel_pure_r _ in _; []).

(** Load *)

Tactic Notation "rel_load_l" open_constr(ef) "in" open_constr(Kf) :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "rel_load_l: cannot find" l "↦ ?" in
  rel_get_sig ltac:(fun Sg =>
  first
    [rel_reshape_cont_l ltac:(fun K e' =>
       unify K Kf ;
       unify e' ef ;
       eapply (tac_rel_load_l_simp Sg K); first reflexivity)
    |fail 1 "rel_load_l: cannot find 'Load'"]);
  (* the remaining goals are from tac_rel_load_l (except for the first one, which has already been solved by this point) *)
  [tc_solve             (** IntoLaters *)
  |solve_mapsto ()
  |reflexivity       (** eres = fill K v *)
  |rel_finish  (** new goal *)].
Tactic Notation "rel_load_l" := rel_pures_l ; rel_load_l _ in _.

Tactic Notation "rel_load_r" open_constr(ef) "in" open_constr(Kf) :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦ₛ{_} _)%I) => l end in
    iAssumptionCore || fail "rel_load_r: cannot find" l "↦ₛ ?" in
  rel_get_sig ltac:(fun Sg =>
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       unify K Kf ;
       unify e' ef ;
       eapply (tac_rel_load_r Sg K); first reflexivity)
    |fail 1 "rel_load_r: cannot find 'Load'"]);
  (* the remaining goals are from tac_rel_load_r (except for the first one, which has already been solved by this point) *)
  [solve_mapsto ()
  |reflexivity
  |rel_finish  (** new goal *)].
Tactic Notation "rel_load_r" := rel_pures_r ; rel_load_r _ in _.

(** Store *)

Tactic Notation "rel_store_l" open_constr(ef) "in" open_constr(Kf) :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦ _)%I) => l end in
    iAssumptionCore || fail "rel_store_l: cannot find" l "↦ ?" in
  rel_get_sig ltac:(fun Sg =>
  first
    [rel_reshape_cont_l ltac:(fun K e' =>
       unify K Kf ;
       unify e' ef ;
       eapply (tac_rel_store_l_simpl Sg K);
       [reflexivity (** e = fill K (#l <- e') *)
       |tc_solve    (** e' is a value *)
       |idtac..])
    |fail 1 "rel_store_l: cannot find 'Store'"]);
  (* the remaining goals are from tac_rel_store_l (except for the first one, which has already been solved by this point) *)
  [tc_solve        (** IntoLaters *)
  |solve_mapsto ()
  |reduction.pm_reflexivity || fail "rel_store_l: this should not happen O-:"
  |reflexivity
  |rel_finish  (** new goal *)].
Tactic Notation "rel_store_l" := rel_pures_l ; rel_store_l _ in _.

Tactic Notation "rel_store_r" open_constr(ef) "in" open_constr(Kf) :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦ₛ _)%I) => l end in
    iAssumptionCore || fail "rel_store_r: cannot find" l "↦ₛ ?" in
  rel_get_sig ltac:(fun Sg =>
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       unify K Kf ;
       unify e' ef ;
       eapply (tac_rel_store_r Sg K);
       [reflexivity|tc_solve|idtac..])
    |fail 1 "rel_store_r: cannot find 'Store'"]);
  (* the remaining goals are from tac_rel_store_r (except for the first one, which has already been solved by this point) *)
  [solve_mapsto ()
  |reduction.pm_reflexivity || fail "rel_store_r: this should not happen O-:"
  |reflexivity
  |rel_finish  (** new goal *)].
Tactic Notation "rel_store_r" := rel_pures_r ; rel_store_r _ in _.

(** Alloc *)

Tactic Notation "rel_alloc_l" simple_intropattern(l) "as" constr(H) "at" open_constr(ef) "in" open_constr(Kf) :=
  rel_get_sig ltac:(fun Sg =>
  first
    [rel_reshape_cont_l ltac:(fun K e' =>
       unify K Kf ;
       unify e' ef ;
       eapply (tac_rel_alloc_l_simpl Sg K);
       [reflexivity (** e = fill K (Alloc e') *)
       |tc_solve    (** e' is a value *)
       |idtac..])
    |fail 1 "rel_alloc_l: cannot find 'Alloc'"]);
  [tc_solve        (** IntoLaters *)
  |iIntros (l) H; rel_finish  (** new goal *)].
Tactic Notation "rel_alloc_l" simple_intropattern(l) "as" constr(H) :=
  rel_pures_l ; rel_alloc_l l as H at _ in _.

Tactic Notation "rel_alloc_r" simple_intropattern(l) "as" constr(H) "at" open_constr(ef) "in" open_constr(Kf) :=
  rel_get_sig ltac:(fun Sg =>
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       unify K Kf ;
       unify e' ef ;
       eapply (tac_rel_alloc_r Sg K);
       [reflexivity  (** t = K'[alloc t'] *)
       |tc_solve     (** t' is a value *)
       |idtac..])
    |fail 1 "rel_alloc_r: cannot find 'Alloc'"]);
  (iIntros (l) H; rel_finish  (** new goal *)).
Tactic Notation "rel_alloc_r" simple_intropattern(l) "as" constr(H) :=
  rel_pures_r ; rel_alloc_r l as H at _ in _.


(* The handling of beta-reductions is special because it also unlocks
 the locked `RecV` values. The the comments for the `wp_rec` tactic in
 the heap_lang proofmode. *)
Tactic Notation "rel_rec_l" :=
  let H := fresh in
  assert (H := AsRecV_recv);
  rel_pure_l (App _ _);
  clear H.
Tactic Notation "rel_rec_r" :=
  let H := fresh in
  assert (H := AsRecV_recv);
  rel_pure_r (App _ _);
  clear H.

(** For backwards compatibility *)
Tactic Notation "rel_seq_l" := rel_pure_l (App _ _).
Tactic Notation "rel_let_l" := rel_pure_l (App _ _).
Tactic Notation "rel_fst_l" := rel_pure_l (Fst _).
Tactic Notation "rel_snd_l" := rel_pure_l (Snd _).
Tactic Notation "rel_proj_l" := rel_pure_l (_ (Val (PairV _ _))).
Tactic Notation "rel_case_inl_l" := rel_pure_l (Case _ _ _).
Tactic Notation "rel_case_inr_l" := rel_pure_l (Case _ _ _).
Tactic Notation "rel_case_l" := rel_pure_l (Case _ _ _).
Tactic Notation "rel_binop_l" := rel_pure_l (BinOp _ _ _).
Tactic Notation "rel_op_l" := rel_binop_l.
Tactic Notation "rel_if_true_l" := rel_pure_l (If #true _ _).
Tactic Notation "rel_if_false_l" := rel_pure_l (If #false _ _).
Tactic Notation "rel_if_l" := rel_pure_l (If _ _ _).

Tactic Notation "rel_seq_r" := rel_pure_r (App _ _).
Tactic Notation "rel_let_r" := rel_pure_r (App _ _).
Tactic Notation "rel_fst_r" := rel_pure_r (Fst _).
Tactic Notation "rel_snd_r" := rel_pure_r (Snd _).
Tactic Notation "rel_proj_r" := rel_pure_r (_ (Val (PairV _ _))).
Tactic Notation "rel_case_inl_r" := rel_pure_r (Case _ _ _).
Tactic Notation "rel_case_inr_r" := rel_pure_r (Case _ _ _).
Tactic Notation "rel_case_r" := rel_pure_r (Case _ _ _).
Tactic Notation "rel_binop_r" := rel_pure_r (BinOp _ _ _).
Tactic Notation "rel_op_r" := rel_binop_r.
Tactic Notation "rel_if_true_r" := rel_pure_r (If #true _ _).
Tactic Notation "rel_if_false_r" := rel_pure_r (If #false _ _).
Tactic Notation "rel_if_r" := rel_pure_r (If _ _ _).

Ltac rel_arrow_val :=
  rel_pures_l; rel_pures_r;
  (iApply refines_arrow_val
  || fail "rel_arrow_val: cannot apply the closure rule");
  iModIntro.

Ltac rel_arrow :=
  rel_pures_l; rel_pures_r;
  (iApply refines_arrow
  || fail "rel_arrow: cannot apply the closure rule");
  iModIntro.
