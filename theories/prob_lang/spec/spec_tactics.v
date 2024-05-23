(** Tactics for updating the specification program. *)
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import coq_tactics ltac_tactics reduction.
From clutch.common Require Import language ectx_language ectxi_language.
From clutch.base_logic Require Export spec_update.
From clutch.prob_lang Require Import locations notation tactics metatheory lang class_instances.
From clutch.prob_lang.spec Require Export spec_rules.
Set Default Proof Using "Type".

(** ** bind *)
Lemma tac_tp_bind_gen `{!specGS Σ} Δ Δ' i p e e' Q :
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

Lemma tac_tp_bind `{specGS Σ} e' Δ Δ' i p K' e Q :
  envs_lookup i Δ = Some (p, ⤇ e)%I →
  e = fill K' e' →
  envs_simple_replace i p (Esnoc Enil i (⤇ fill K' e')) Δ = Some Δ' →
  (envs_entails Δ' Q) →
  (envs_entails Δ Q).
Proof. intros. by eapply tac_tp_bind_gen. Qed.

Ltac tp_bind_helper :=
  simpl;
  lazymatch goal with
  | |- fill ?K ?e = fill _ ?efoc =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       let K'' := eval cbn[app] in (K' ++ K) in
       replace (fill K e) with (fill K'' e') by (by rewrite ?fill_app))
  | |- ?e = fill _ ?efoc =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       replace e with (fill K' e') by (by rewrite ?fill_app))
  end; reflexivity.

Tactic Notation "tp_normalise" :=
  iStartProof;
  eapply tac_tp_bind_gen;
    [iAssumptionCore (* prove the lookup *)
    | lazymatch goal with
      | |- fill ?K ?e = _ =>
          by rewrite /= ?fill_app /=
      | |- ?e = _ => try fast_done
      end
    |reflexivity
    |(* new goal *)].

Tactic Notation "tp_bind" open_constr(efoc) :=
  iStartProof;
  eapply (tac_tp_bind efoc);
    [iAssumptionCore (* prove the lookup *)
    |tp_bind_helper (* do actual work *)
    |reflexivity
    |(* new goal *)].

Lemma tac_tp_pure `{specGS Σ, invGS_gen hasLc Σ} e K e1 e2 Δ1 i1 e' ϕ ψ E1 Q n :
  e = fill K e1 →
  PureExec ϕ n e1 e2 →
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
  rewrite (step_pure E1) //.
  rewrite -[Q]elim_modal // /=.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "tp_pure_at" open_constr(ef) :=
  iStartProof;
  lazymatch goal with
  | |- context[environments.Esnoc _ ?H (⤇ (fill ?K' ?e))] =>
    reshape_expr e ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_tp_pure (fill K' e) (K++K') e');
      [by rewrite ?fill_app | tc_solve | ..])
  | |- context[environments.Esnoc _ ?H (⤇ ?e)] =>
    reshape_expr e ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_tp_pure e K e');
      [by rewrite ?fill_app | tc_solve | ..])
  end;
  [tc_solve || fail "tp_pure: cannot eliminate modality in the goal"
  |iAssumptionCore || fail "tp_pure: cannot find the RHS" (* TODO fix error message *)
  |try (exact I || reflexivity) (* ψ *)
  |try (exact I || reflexivity) (* ϕ *)
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
Tactic Notation "tp_binop" := tp_pure_at (BinOp _ _ _).
Tactic Notation "tp_op" := tp_binop.
Tactic Notation "tp_if_true" := tp_pure_at (If #true _ _).
Tactic Notation "tp_if_false" := tp_pure_at (If #false _ _).
Tactic Notation "tp_if" := tp_pure_at (If _ _ _).
Tactic Notation "tp_pair" := tp_pure_at (Pair _ _).
Tactic Notation "tp_closure" := tp_pure_at (Rec _ _ _).

Lemma tac_tp_store `{specGS Σ, invGS_gen hasLc Σ} Δ1 Δ2 E1 i1 i2 K e (l : loc) e' e2 v' v Q :
  (* TODO: here instead of True we can consider another Coq premise, like in tp_pure.
     Same goes for the rest of those tactics *)
  (∀ P, ElimModal True false false (spec_update E1 P) P Q Q) →
  envs_lookup_delete false i1 Δ1 = Some (false, ⤇ e, Δ2)%I →
  e = fill K (Store (# l) e') →
  IntoVal e' v →
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
  rewrite step_store //=.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ₛ v)%I). simpl.
  by rewrite bi.wand_elim_r.
Qed.

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

Lemma tac_tp_load `{specGS Σ, invGS_gen hasLc Σ} Δ1 Δ2 E1 i1 i2 K e e2 (l : loc) v Q q :
  (∀ P, ElimModal True false false (spec_update E1 P) P Q Q) →
  envs_lookup_delete false i1 Δ1 = Some (false, ⤇ e, Δ2)%I →
  e = fill K (Load #l) →
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
  rewrite step_load //=.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ₛ{q} v)%I).
  rewrite HQ. apply bi.wand_elim_r.
Qed.

Tactic Notation "tp_load" :=
  iStartProof;
  eapply tac_tp_load;
  [tc_solve || fail "tp_load: cannot eliminate modality in the goal"
  |iAssumptionCore || fail "tp_load: cannot find the RHS"
  |tp_bind_helper
  |iAssumptionCore || fail "tp_load: cannot find '? ↦ₛ ?'"
  |simpl; reflexivity || fail "tp_load: this should not happen"
  |pm_reduce (* new goal *)].

Lemma tac_tp_alloc `{specGS Σ, invGS_gen hasLc Σ} Δ1 E1 i1 K e e' v Q :
  (∀ P, ElimModal True false false (spec_update E1 P) P Q Q) →
  envs_lookup i1 Δ1 = Some (false, ⤇ e)%I →
  e = fill K (ref e') →
  IntoVal e' v →
  (∀ l : loc, ∃ Δ2,
    envs_simple_replace i1 false
       (Esnoc Enil i1 (⤇ fill K #l)) Δ1 = Some Δ2 ∧
    (envs_entails Δ2 ((l ↦ₛ v) -∗ Q)%I)) →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ?? Hfill <- HQ.
  rewrite (envs_lookup_sound' Δ1 false i1); last by eassumption.
  rewrite Hfill /=.
  rewrite step_alloc //.
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

Lemma tac_tp_alloctape `{specGS Σ, invGS_gen hasLc Σ} Δ1 E1 i1 K e N z Q :
  (∀ P, ElimModal True false false (spec_update E1 P) P Q Q) →
  TCEq N (Z.to_nat z) →
  envs_lookup i1 Δ1 = Some (false, ⤇ e)%I →
  e = fill K (alloc #z) →
  (∀ α : loc, ∃ Δ2,
    envs_simple_replace i1 false
       (Esnoc Enil i1 (⤇ fill K #lbl:α)) Δ1 = Some Δ2 ∧
    (envs_entails Δ2 ((α ↪ₛ (N; [])) -∗ Q)%I)) →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? Hfill HQ.
  rewrite (envs_lookup_sound' Δ1 false i1); last by eassumption.
  rewrite Hfill /=.
  rewrite step_alloctape //.
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

Tactic Notation "tp_alloctape" "as" ident(l) constr(H) :=
  let finish _ :=
      first [ intros l | fail 1 "tp_alloctape:" l "not fresh"];
        eexists; split;
        [ reduction.pm_reflexivity
        | (iIntros H; tp_normalise) || fail 1 "tp_alloctape:" H "not correct intro pattern" ] in
  iStartProof;
  eapply (tac_tp_alloctape);
  [tc_solve || fail "tp_alloctape: cannot eliminate modality in the goal"
  |tc_solve || fail "tp_alloctape: cannnot convert bound to a natural number"
  |iAssumptionCore || fail "tp_alloctape: cannot find the RHS"
  |tp_bind_helper
  |finish ()
(* new goal *)].

Tactic Notation "tp_alloctape" "as" ident(j') :=
  let H := iFresh in tp_alloctape as j' H.

Lemma tac_tp_rand `{specGS Σ, invGS_gen hasLc Σ} Δ1 Δ2 E1 i1 i2 K e e2 (l : loc) N z n ns Q :
  (∀ P, ElimModal True false false (spec_update E1 P) P Q Q) →
  TCEq N (Z.to_nat z) →
  envs_lookup_delete false i1 Δ1 = Some (false, ⤇ e, Δ2)%I →
  e = fill K (rand(#lbl:l) #z) →
  envs_lookup i2 Δ2 = Some (false, l ↪ₛ (N; n::ns))%I →
  e2 = fill K (of_val #n) →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (⤇ e2)) i2 (l ↪ₛ (N; ns))%I) Δ2 with
  | Some Δ3 => envs_entails Δ3 Q
  | None    => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? -> ? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
  rewrite right_id.
  rewrite assoc.
  rewrite step_rand //=.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite HQ.
  rewrite (comm _ _ (l ↪ₛ (N; ns))%I).
  by apply bi.wand_elim_r.
Qed.

Tactic Notation "tp_rand" :=
  iStartProof;
  eapply tac_tp_rand;
  [tc_solve || fail "tp_rand: cannot eliminate modality in the goal"
  | (* postpone solving [TCEq ...] until after the tape has been unified *)
  |iAssumptionCore || fail "tp_rand: cannot find the RHS"
  |tp_bind_helper
  |iAssumptionCore || fail "tp_rand: cannot find '? ↪ₛ ?'"
  |simpl; reflexivity || fail "tp_rand: this should not happen"
  |pm_reduce (* new goal *)];
  [tc_solve || fail "tp_rand: cannot convert bound to a natural number"
  |].

(** Some simple tests *)
Section tests.
  Context `{specGS Σ, invGS_gen hasLc Σ}.

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

  Local Lemma test_rand E α :
    α ↪ₛ ((1; [0%fin]) : tape) ∗ ⤇ (rand(#lbl:α) #1) ⊢ spec_update E (⤇ #0).
  Proof.
    iIntros "[Hα Hs]".
    tp_rand.
    iModIntro.
    done.
  Qed.

End tests.

(* From clutch.ctx_logic Require Import primitive_laws proofmode. *)

(* Section clutch_test. *)
(*   Context `{!clutchGS Σ}. *)

(*   Local Lemma test_wp_tp_pures E : *)
(*     {{{ ⤇ (#2 + #2 + #2)%E }}} #3 + #3 @ E {{{ RET #6; ⤇ #6 }}}. *)
(*   Proof. *)
(*     iIntros (Ψ) "Hs HΨ". *)
(*     tp_pures. *)
(*     wp_pures.  *)
(*     by iApply "HΨ". *)
(*   Qed. *)
(* End clutch_test.  *)
