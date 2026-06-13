(** Tactics for updating the specification program ([gen_prob_lang]).

    Ported from [prob_lang/spec/spec_tactics.v].  The generic, non-sampling
    [tp_*] tactics (pure steps, bind, heap alloc/load/store) are unchanged
    modulo the [gen_prob_lang] imports.  The per-distribution sampling tactics
    ([tp_rand], [tp_randnat], [tp_alloctape], [tp_alloctape_laplace],
    [tp_laplace]) are replaced by the two generic analogues
    [tp_alloc_sample_tape] and [tp_sample_tape], built on the generic spec rules
    [step_alloc_sample_tape] and [step_sample_tape].

    The generic language [gen_lang S] is parametric in a distribution signature
    [S : Sig]; it is *not* a globally-canonical [language].  As in
    [spec_rules.v] and [wp_tactics.v], the [tac_tp_*] lemmas are declared inside
    a [Section] over [S : Sig] with the
    [gen_ectxi_lang/gen_ectx_lang/gen_lang] canonical-structure chain in scope
    and the language-bearing positions ([fill], [spec_update], [PureExec],
    [IntoVal], [ElimModal (spec_update ...)]) pinned to [gen_lang S].  The
    [Tactic Notation]s remain at top level — they are purely syntactic — and
    feed the extra leading [S] argument of the [tac_tp_*] lemmas a placeholder
    [_], unified from the goal. *)
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import coq_tactics ltac_tactics reduction.
From clutch.common Require Import language ectx_language ectxi_language.
From clutch.base_logic Require Export spec_update.
From clutch.gen_prob_lang Require Import notation tactics metatheory class_instances wp_tactics.
From clutch.gen_prob_lang.spec Require Export spec_rules.
(* Import [gen_prob_lang.lang] LAST so that the concrete [expr]/[val] shadow the
   [language] record projections. *)
From clutch.gen_prob_lang Require Import lang.
Set Default Proof Using "Type".

Section tactics.
  Context (S : Sig).
  Canonical Structure gen_ectxi_lang_S_tp := gen_ectxi_lang S.
  Canonical Structure gen_ectx_lang_S_tp := gen_ectx_lang S.
  Canonical Structure gen_lang_S_tp := gen_lang S.
  Context `{!specG_prob_lang Σ, invGS_gen hasLc Σ}.

  (* Pin [fill] to the [gen_prob_lang] evaluation contexts (there is no canonical
     [ectxLanguage] structure to infer it from). *)
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang S)).
  (* Pin the spec-update modality to the markov chain of [gen_lang S]; the
     signature [S] is otherwise phantom in the proposition argument. *)
  Local Notation spec_update :=
    (@spec_update (lang_markov (gen_lang S)) Σ _ _ _).

  Implicit Types P Q : iProp Σ.

  (** ** bind *)
  Lemma tac_tp_bind_gen Δ Δ' i p e e' Q :
    envs_lookup i Δ = Some (p, ⤇ e)%I →
    e = e' →
    envs_simple_replace i p (Esnoc Enil i (⤇ e')) Δ = Some Δ' →
    (envs_entails Δ' Q) →
    (envs_entails Δ Q).
  Proof.
    rewrite envs_entails_unseal. intros; subst. simpl.
    rewrite envs_simple_replace_sound // /=.
    destruct p; rewrite /= ?right_id; by rewrite bi.wand_elim_r.
  Qed.

  Lemma tac_tp_bind e' Δ Δ' i p K' e Q :
    envs_lookup i Δ = Some (p, ⤇ e)%I →
    e = fill K' e' →
    envs_simple_replace i p (Esnoc Enil i (⤇ fill K' e')) Δ = Some Δ' →
    (envs_entails Δ' Q) →
    (envs_entails Δ Q).
  Proof. intros. by eapply tac_tp_bind_gen. Qed.

  (** ** pure *)
  Lemma tac_tp_pure e K e1 e2 Δ1 i1 e' ϕ ψ E1 Q n :
    e = fill K e1 →
    @PureExec (gen_lang S) ϕ n e1 e2 →
    (∀ P, ElimModal ψ false false (spec_update E1 P) P Q Q) →
    envs_lookup i1 Δ1 = Some (false, ⤇ e)%I →
    ψ →
    ϕ →
    e' = fill K e2 →
    match envs_simple_replace i1 false (Esnoc Enil i1 (⤇ e')) Δ1 with
    | Some Δ2 => envs_entails Δ2 Q
    | None => False
    end →
    envs_entails Δ1 Q.
  Proof.
    rewrite envs_entails_unseal. intros -> Hpure ? HΔ1 Hψ Hϕ -> ?.
    destruct (envs_simple_replace _ _ _ _) as [Δ2|] eqn:HΔ2; try done.
    rewrite (envs_simple_replace_sound Δ1 Δ2 i1) //; simpl.
    rewrite right_id.
    rewrite (step_pure S E1) //.
    rewrite -[Q]elim_modal // /=.
    apply bi.sep_mono_r.
    apply bi.wand_intro_l.
    by rewrite bi.wand_elim_r.
  Qed.

  (** ** store *)
  Lemma tac_tp_store Δ1 Δ2 E1 i1 i2 K e (l : loc) e' e2 v' v Q :
    (∀ P, ElimModal True false false (spec_update E1 P) P Q Q) →
    envs_lookup_delete false i1 Δ1 = Some (false, ⤇ e, Δ2)%I →
    e = fill K (Store (# l) e') →
    @IntoVal (gen_lang S) e' v →
    (* re-compose the expression and the evaluation context *)
    e2 = fill K #() →
    envs_lookup i2 Δ2 = Some (false, l ↦ₛ v')%I →
    match envs_simple_replace i2 false
       (Esnoc (Esnoc Enil i1 (⤇ e2)) i2 (l ↦ₛ v)) Δ2 with
    | None => False
    | Some Δ3 => envs_entails Δ3 Q
    end →
    envs_entails Δ1 Q.
  Proof.
    rewrite /IntoVal.
    rewrite envs_entails_unseal. intros ?? -> <- -> ? HQ.
    rewrite envs_lookup_delete_sound //; simpl.
    destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
    rewrite envs_simple_replace_sound //; simpl.
    rewrite right_id.
    rewrite !assoc.
    rewrite (step_store S) //=.
    rewrite -[Q]elim_modal //.
    apply bi.sep_mono_r.
    apply bi.wand_intro_l.
    rewrite (comm _ _ (l ↦ₛ v)%I). simpl.
    by rewrite bi.wand_elim_r.
  Qed.

  (** ** load *)
  Lemma tac_tp_load Δ1 Δ2 E1 i1 i2 K e e2 (l : loc) v Q q :
    (∀ P, ElimModal True false false (spec_update E1 P) P Q Q) →
    envs_lookup_delete false i1 Δ1 = Some (false, ⤇ e, Δ2)%I →
    e = fill K (Deref #l) →
    envs_lookup i2 Δ2 = Some (false, l ↦ₛ{q} v)%I →
    e2 = fill K (of_val v) →
    match envs_simple_replace i2 false
      (Esnoc (Esnoc Enil i1 (⤇ e2)) i2 (l ↦ₛ{q} v)%I) Δ2 with
    | Some Δ3 => envs_entails Δ3 Q
    | None    => False
    end →
    envs_entails Δ1 Q.
  Proof.
    rewrite envs_entails_unseal. intros ?? -> ? -> HQ.
    rewrite envs_lookup_delete_sound //; simpl.
    destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
    rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
    rewrite right_id.
    rewrite assoc.
    rewrite (step_load S) //=.
    rewrite -[Q]elim_modal //.
    apply bi.sep_mono_r.
    apply bi.wand_intro_l.
    rewrite (comm _ _ (l ↦ₛ{q} v)%I).
    rewrite HQ. apply bi.wand_elim_r.
  Qed.

  (** ** alloc *)
  Lemma tac_tp_alloc Δ1 E1 i1 K e e' v Q :
    (∀ P, ElimModal True false false (spec_update E1 P) P Q Q) →
    envs_lookup i1 Δ1 = Some (false, ⤇ e)%I →
    e = fill K (ref e') →
    @IntoVal (gen_lang S) e' v →
    (∀ l : loc, ∃ Δ2,
      envs_simple_replace i1 false
         (Esnoc Enil i1 (⤇ fill K #l)) Δ1 = Some Δ2 ∧
      (envs_entails Δ2 ((l ↦ₛ v) -∗ Q)%I)) →
    envs_entails Δ1 Q.
  Proof.
    rewrite envs_entails_unseal. intros ?? Hfill <- HQ.
    rewrite (envs_lookup_sound' Δ1 false i1); last by eassumption.
    rewrite Hfill /=.
    rewrite (step_alloc S) //.
    rewrite -[Q]elim_modal //.
    apply bi.sep_mono_r, bi.wand_intro_l.
    rewrite bi.sep_exist_r.
    apply bi.exist_elim=> l.
    destruct (HQ l) as (Δ2 & HΔ2 & HQ').
    rewrite (envs_simple_replace_sound' _ _ i1 _ _ HΔ2) /=.
    rewrite HQ' right_id.
    iIntros "[[H Hl] Hcnt]".
    iApply ("Hcnt" with "H Hl").
  Qed.

  (** ** allocate a generic sample tape *)
  Lemma tac_tp_alloc_sample_tape Δ1 E1 i1 K e (idx : nat) (pv : val) Q :
    (∀ P, ElimModal True false false (spec_update E1 P) P Q Q) →
    envs_lookup i1 Δ1 = Some (false, ⤇ e)%I →
    e = fill K (AllocSampleTape idx (Val pv)) →
    (∀ α : loc, ∃ Δ2,
      envs_simple_replace i1 false
         (Esnoc Enil i1 (⤇ fill K #lbl:α)) Δ1 = Some Δ2 ∧
      (envs_entails Δ2 ((α ↪ₛ (idx, pv, [])) -∗ Q)%I)) →
    envs_entails Δ1 Q.
  Proof.
    rewrite envs_entails_unseal. intros ?? Hfill HQ.
    rewrite (envs_lookup_sound' Δ1 false i1); last by eassumption.
    rewrite Hfill /=.
    rewrite (step_alloc_sample_tape S) //.
    rewrite -[Q]elim_modal //.
    apply bi.sep_mono_r, bi.wand_intro_l.
    rewrite bi.sep_exist_r.
    apply bi.exist_elim=> l.
    destruct (HQ l) as (Δ2 & HΔ2 & HQ').
    rewrite (envs_simple_replace_sound' _ _ i1 _ _ HΔ2) /=.
    rewrite HQ' right_id.
    iIntros "[[H Hl] Hcnt]".
    iApply ("Hcnt" with "H Hl").
  Qed.

  (** ** consume a head from a generic sample tape *)
  Lemma tac_tp_sample_tape Δ1 Δ2 E1 i1 i2 K e e2 (l : loc) (idx : nat) (pv x : val) xs Q :
    (∀ P, ElimModal True false false (spec_update E1 P) P Q Q) →
    envs_lookup_delete false i1 Δ1 = Some (false, ⤇ e, Δ2)%I →
    e = fill K (Sample idx (Val pv) (Val #lbl:l)) →
    envs_lookup i2 Δ2 = Some (false, l ↪ₛ (idx, pv, x :: xs))%I →
    e2 = fill K (of_val x) →
    match envs_simple_replace i2 false
      (Esnoc (Esnoc Enil i1 (⤇ e2)) i2 (l ↪ₛ (idx, pv, xs))%I) Δ2 with
    | Some Δ3 => envs_entails Δ3 Q
    | None    => False
    end →
    envs_entails Δ1 Q.
  Proof.
    rewrite envs_entails_unseal. intros ?? -> ? -> HQ.
    rewrite envs_lookup_delete_sound //; simpl.
    destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
    rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
    rewrite right_id.
    rewrite assoc.
    rewrite (step_sample_tape S) //=.
    rewrite -[Q]elim_modal //.
    apply bi.sep_mono_r.
    apply bi.wand_intro_l.
    rewrite HQ.
    rewrite (comm _ _ (l ↪ₛ (idx, pv, xs))%I).
    by apply bi.wand_elim_r.
  Qed.

End tactics.

(** ** Tactic notations.  These are purely syntactic and live at top level; the
    leading [S] argument of every [tac_tp_*] lemma is fed a placeholder [_],
    unified from the goal. *)

Ltac tp_bind_helper :=
  (* NB: unlike [prob_lang], we do *not* [simpl] first: in [gen_prob_lang]
     the [fill] of [gen_ectx_lang S] is a canonical-structure projection, and
     [simpl] reduces it to a stuck [let ... in fill] form which then fails to
     match the [@ectx_language.fill] patterns below. *)
  lazymatch goal with
  | |- @ectx_language.fill ?Λ ?K ?e = @ectx_language.fill _ _ ?efoc =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       let K'' := eval cbn[app] in (K' ++ K) in
       replace (@ectx_language.fill Λ K e) with (@ectx_language.fill Λ K'' e') by reflexivity)
  (* After a prior [tp_*] step the spec evaluation context is rebuilt with the
     [ectxi_language.fill] head (the [EctxLanguageOfEctxi] derivation), so peel
     that too; the result is convertible to the [ectx_language.fill] RHS. *)
  | |- @ectxi_language.fill ?Λ ?K ?e = @ectx_language.fill ?Λ2 _ ?efoc =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       let K'' := eval cbn[app] in (K' ++ K) in
       replace (@ectxi_language.fill Λ K e) with (@ectxi_language.fill Λ K'' e') by reflexivity)
  | |- @ectxi_language.fill ?Λ ?K ?e = @ectxi_language.fill _ _ ?efoc =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       let K'' := eval cbn[app] in (K' ++ K) in
       replace (@ectxi_language.fill Λ K e) with (@ectxi_language.fill Λ K'' e') by reflexivity)
  | |- ?e = @ectx_language.fill ?Λ _ ?efoc =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       replace e with (@ectx_language.fill Λ K' e') by reflexivity)
  | |- ?e = @ectxi_language.fill ?Λ _ ?efoc =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       replace e with (@ectxi_language.fill Λ K' e') by reflexivity)
  end; reflexivity.

(** [tp_get_sig k] reads the distribution signature [S] off the current spec
    goal (whose conclusion is [envs_entails _ (spec_update (lang_markov
    (gen_lang S)) ...)]) and passes it to the continuation [k].  This is needed
    because the [tac_tp_*] lemmas take [S] as a leading explicit argument that
    does *not* appear in their conclusion [envs_entails Δ Q]: [eapply] alone
    leaves [S] an evar, which blocks the [S]-parametric [PureExec]/[IntoVal]
    instance resolution.  Supplying [S] up front fixes the language so those
    instances resolve. *)
Ltac tp_get_sig k :=
  lazymatch goal with
  | |- environments.envs_entails _
         (@spec_update.spec_update (lang_markov (gen_lang ?S)) _ _ _ _ _ _) =>
      k S
  end.

Tactic Notation "tp_normalise" :=
  iStartProof;
  eapply tac_tp_bind_gen;
    [iAssumptionCore (* prove the lookup *)
    | lazymatch goal with
      | |- @ectx_language.fill _ ?K ?e = _ =>
          by rewrite /= ?fill_app /=
      | |- ?e = _ => try fast_done
      end
    |reflexivity
    |(* new goal *)].

(* NB (gen): rather than [tac_tp_bind] (whose [fill K']'s context [K'] is a fresh
   evar that the spec — folded [ectx(i)_language.fill K e] — cannot determine,
   because the unifier sees the [foldl] form), we use [tac_tp_bind_gen] and build
   the target spec [fill (K'++K) efoc] EXPLICITLY from [reshape_expr]; the
   [e = e'] obligation then holds by convertibility ([fill_app]). *)
Tactic Notation "tp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- context[environments.Esnoc _ ?i (⤇ (@ectxi_language.fill _ ?K ?e))] =>
      reshape_expr e ltac:(fun K' e' =>
        unify e' efoc;
        let Kc := eval cbn[app] in (K' ++ K) in
        eapply (tac_tp_bind_gen _ _ i _ _ (@ectxi_language.fill _ Kc e'));
        [ iAssumptionCore | by reflexivity | reflexivity | ])
  | |- context[environments.Esnoc _ ?i (⤇ (@ectx_language.fill _ ?K ?e))] =>
      reshape_expr e ltac:(fun K' e' =>
        unify e' efoc;
        let Kc := eval cbn[app] in (K' ++ K) in
        eapply (tac_tp_bind_gen _ _ i _ _ (@ectx_language.fill _ Kc e'));
        [ iAssumptionCore | by reflexivity | reflexivity | ])
  | |- context[environments.Esnoc _ ?i (⤇ ?e)] =>
      reshape_expr e ltac:(fun K' e' =>
        unify e' efoc;
        eapply (tac_tp_bind_gen _ _ i _ _ (@ectxi_language.fill _ K' e'));
        [ iAssumptionCore | by reflexivity | reflexivity | ])
  end.

(* NB (gen_prob_lang specific): [tac_tp_pure] takes [S] as a leading explicit
   argument.  We supply it via [tp_get_sig] (read off the goal) so the
   [S]-parametric [PureExec] instances can resolve; the rest mirrors [prob_lang]. *)
Tactic Notation "tp_pure_at" open_constr(ef) :=
  iStartProof;
  tp_get_sig ltac:(fun S =>
  lazymatch goal with
  | |- context[environments.Esnoc _ ?H (⤇ (@ectx_language.fill _ ?K' ?e))] =>
    reshape_expr e ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_tp_pure S (@ectx_language.fill _ K' e) (K++K') e');
      [by rewrite ?fill_app | tc_solve | ..])
  (* After the first [tp_pure] step the spec context is rebuilt with the
     [ectxi_language.fill] head (the [EctxLanguageOfEctxi] derivation displays
     [ectx_language.fill] as [ectxi_language.fill]); match it too so multi-step
     reductions (e.g. nested [Pair]s inside a [Sample] argument) complete. *)
  | |- context[environments.Esnoc _ ?H (⤇ (@ectxi_language.fill _ ?K' ?e))] =>
    reshape_expr e ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_tp_pure S (@ectxi_language.fill _ K' e) (K++K') e');
      [by rewrite ?fill_app | tc_solve | ..])
  | |- context[environments.Esnoc _ ?H (⤇ ?e)] =>
    reshape_expr e ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_tp_pure S e K e');
      [by rewrite ?fill_app | tc_solve | ..])
  end);
  [tc_solve || fail "tp_pure: cannot eliminate modality in the goal"
  |iAssumptionCore || fail "tp_pure: cannot find the RHS" (* TODO fix error message *)
  |try (exact I || reflexivity) (* ψ *)
  |try (exact I || reflexivity || solve_vals_compare_safe) (* ϕ *)
  |simpl; reflexivity ||  fail "tp_pure: this should not happen" (* e' = fill K' e2 *)
  |pm_reduce (* new goal *)].

Tactic Notation "tp_pure" := tp_pure_at _.
Tactic Notation "tp_pures" := repeat tp_pure.
Tactic Notation "tp_rec" :=
  let H := fresh in
  assert (H := AsRecV_recv);
  tp_pure_at (App _ _);
  clear H.
Tactic Notation "tp_seq" := tp_rec.
Tactic Notation "tp_let" := tp_rec.
Tactic Notation "tp_lam" := tp_rec.
Tactic Notation "tp_fst" := tp_pure_at (Fst (PairV _ _)).
Tactic Notation "tp_snd" := tp_pure_at (Snd (PairV _ _)).
Tactic Notation "tp_proj" := tp_pure_at (_ (PairV _ _)).
Tactic Notation "tp_case_inl" := tp_pure_at (Case (InjLV _) _ _).
Tactic Notation "tp_case_inr" := tp_pure_at (Case (InjRV _) _ _).
Tactic Notation "tp_case" := tp_pure_at (Case _ _ _).
Tactic Notation "tp_inj" := tp_pure_at (InjL _) || tp_pure_at (InjR _).
Tactic Notation "tp_binop" := tp_pure_at (BinOp _ _ _).
Tactic Notation "tp_unop" := tp_pure_at (UnOp _ _).
Tactic Notation "tp_op" := tp_binop.
Tactic Notation "tp_if_true" := tp_pure_at (If #true _ _).
Tactic Notation "tp_if_false" := tp_pure_at (If #false _ _).
Tactic Notation "tp_if" := tp_pure_at (If _ _ _).
Tactic Notation "tp_pair" := tp_pure_at (Pair _ _).
Tactic Notation "tp_closure" := tp_pure_at (Rec _ _ _).

Tactic Notation "tp_store" :=
  iStartProof;
  eapply tac_tp_store;
  [tc_solve || fail "tp_store: cannot eliminate modality in the goal"
  |iAssumptionCore || fail "tp_store: cannot find the RHS"
  |tp_bind_helper
  |tc_solve || fail "tp_store: cannot convert the argument to a value"
  |simpl; reflexivity || fail "tp_store: this should not happen"
  |iAssumptionCore || fail "tp_store: cannot find '? ↦ₛ ?'"
  |pm_reduce (* new goal *)].

Tactic Notation "tp_load" :=
  iStartProof;
  eapply tac_tp_load;
  [tc_solve || fail "tp_load: cannot eliminate modality in the goal"
  |iAssumptionCore || fail "tp_load: cannot find the RHS"
  |tp_bind_helper
  |iAssumptionCore || fail "tp_load: cannot find '? ↦ₛ ?'"
  |simpl; reflexivity || fail "tp_load: this should not happen"
  |pm_reduce (* new goal *)].

Tactic Notation "tp_alloc" "as" ident(l) constr(H) :=
  let finish _ :=
      first [ intros l | fail 1 "tp_alloc:" l "not fresh"];
        eexists; split;
        [ reduction.pm_reflexivity
        | (iIntros H; tp_normalise) || fail 1 "tp_alloc:" H "not correct intro pattern" ] in
  iStartProof;
  eapply tac_tp_alloc;
  [tc_solve || fail "tp_alloc: cannot eliminate modality in the goal"
  |iAssumptionCore || fail "tp_alloc: cannot find the RHS"
  |tp_bind_helper
  |tc_solve || fail "tp_alloc: expressions is not a value"
  |finish ()
(* new goal *)].

Tactic Notation "tp_alloc" "as" ident(j') :=
  let H := iFresh in tp_alloc as j' H.

Tactic Notation "tp_alloc_sample_tape" "as" ident(l) constr(H) :=
  let finish _ :=
      first [ intros l | fail 1 "tp_alloc_sample_tape:" l "not fresh"];
        eexists; split;
        [ reduction.pm_reflexivity
        | (iIntros H; tp_normalise) || fail 1 "tp_alloc_sample_tape:" H "not correct intro pattern" ] in
  iStartProof;
  eapply (tac_tp_alloc_sample_tape);
  [tc_solve || fail "tp_alloc_sample_tape: cannot eliminate modality in the goal"
  |iAssumptionCore || fail "tp_alloc_sample_tape: cannot find the RHS"
  |tp_bind_helper
  |finish ()
(* new goal *)].

Tactic Notation "tp_alloc_sample_tape" "as" ident(j') :=
  let H := iFresh in tp_alloc_sample_tape as j' H.

Tactic Notation "tp_sample_tape" :=
  iStartProof;
  eapply tac_tp_sample_tape;
  [tc_solve || fail "tp_sample_tape: cannot eliminate modality in the goal"
  |iAssumptionCore || fail "tp_sample_tape: cannot find the RHS"
  |tp_bind_helper
  |iAssumptionCore || fail "tp_sample_tape: cannot find '? ↪ₛ ?'"
  |simpl; reflexivity || fail "tp_sample_tape: this should not happen"
  |pm_reduce (* new goal *)].

(** Some simple tests *)
Section tests.
  Context (S : Sig).
  Canonical Structure gen_ectxi_lang_S_test := gen_ectxi_lang S.
  Canonical Structure gen_ectx_lang_S_test := gen_ectx_lang S.
  Canonical Structure gen_lang_S_test := gen_lang S.
  Context `{!specG_prob_lang Σ, invGS_gen hasLc Σ}.

  Local Notation spec_update :=
    (@spec_update (lang_markov (gen_lang S)) Σ _ _ _).

  Local Lemma test_tp_pures E :
    ⤇ (#2 + #2 + #2) ⊢ spec_update E (⤇ #6).
  Proof.
    iIntros "Hs".
    tp_pures.
    iModIntro.
    done.
  Qed.

  Local Lemma test_heap E :
    ⤇ (let: "x" := ref #41 in "x" <- !"x" + #1;; !"x") ⊢ spec_update E (⤇ #42).
  Proof.
    iIntros "Hs".
    tp_alloc as l "Hl".
    tp_pures.
    tp_load.
    tp_pures.
    tp_store.
    tp_pures.
    tp_load.
    iModIntro.
    done.
  Qed.

  Local Lemma test_sample_tape E α (idx : nat) (pv x : val) :
    α ↪ₛ (idx, pv, [x]) ∗ ⤇ (Sample idx (Val pv) (Val #lbl:α))
    ⊢ spec_update E (⤇ (Val x)).
  Proof.
    iIntros "[Hα Hs]".
    tp_sample_tape.
    iModIntro.
    done.
  Qed.

  Local Lemma test_alloc_sample_tape E (idx : nat) (pv : val) :
    ⤇ (AllocSampleTape idx (Val pv)) ⊢ spec_update E (∃ α, ⤇ #lbl:α ∗ α ↪ₛ (idx, pv, [])).
  Proof.
    iIntros "Hs".
    tp_alloc_sample_tape as α "Hα".
    iModIntro.
    iExists _. iFrame.
  Qed.

End tests.
