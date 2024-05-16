(** Tactics for updating the specification program. *)
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import
     coq_tactics ltac_tactics
     reduction.
From clutch.common Require Import language ectx_language ectxi_language.
From clutch.prob_lang Require Import locations notation tactics metatheory lang
  class_instances.
From clutch.ctx_logic Require Import weakestpre lifting spec_ra spec_rules.
Set Default Proof Using "Type".

(** ** bind *)
Lemma tac_tp_bind_gen `{clutchGS Σ} k Δ Δ' i p e e' Q :
  envs_lookup i Δ = Some (p, refines_right k e)%I →
  e = e' →
  envs_simple_replace i p (Esnoc Enil i (refines_right k e')) Δ = Some Δ' →
  (envs_entails Δ' Q) →
  (envs_entails Δ Q).
Proof.
  rewrite envs_entails_unseal. intros; subst. simpl.
  rewrite envs_simple_replace_sound // /=.
  destruct p; rewrite /= ?right_id; by rewrite bi.wand_elim_r.
Qed.

Lemma tac_tp_bind `{clutchGS Σ} k e' Δ Δ' i p K' e Q :
  envs_lookup i Δ = Some (p, refines_right k e)%I →
  e = fill K' e' →
  envs_simple_replace i p (Esnoc Enil i (refines_right k (fill K' e'))) Δ = Some Δ' →
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
  eapply (tac_tp_bind _ efoc);
    [iAssumptionCore (* prove the lookup *)
    |tp_bind_helper (* do actual work *)
    |reflexivity
    |(* new goal *)].

Lemma tac_tp_pure `{clutchGS Σ} e K' e1 k e2 Δ1 E1 i1 e' ϕ ψ Q n :
  (* we have those premises first, because we will be trying to solve them
     with backtracking using reashape_expr; see the accompanying Ltac.
     the first premise decomposes the expression, the second one checks
     that we can make a pure step *)
  e = fill K' e1 →
  PureExec ϕ n e1 e2 →
  (∀ P, ElimModal ψ false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  envs_lookup i1 Δ1 = Some (false, refines_right k e)%I →
  ψ →
  ϕ →
  (* we will call simpl on this goal thus re-composing the expression again *)
  e' = fill K' e2 →
  match envs_simple_replace i1 false (Esnoc Enil i1 (refines_right k e')) Δ1 with
  | Some Δ2 => envs_entails Δ2 Q
  | None => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros -> Hpure ?? HΔ1 Hψ Hϕ -> ?.
  destruct (envs_simple_replace _ _ _ _) as [Δ2|] eqn:HΔ2; try done.
  rewrite (envs_simple_replace_sound Δ1 Δ2 i1) //; simpl.
  rewrite right_id.
  rewrite /refines_right.
  rewrite -!fill_app.
  rewrite step_pure //.
  rewrite -[Q]elim_modal // /=.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "tp_pure_at" open_constr(ef) :=
  iStartProof;
  lazymatch goal with
  | |- context[environments.Esnoc _ ?H (refines_right ?j (fill ?K' ?e))] =>
    reshape_expr e ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_tp_pure (fill K' e) (K++K') e' j);
      [by rewrite ?fill_app | tc_solve | ..])
  | |- context[environments.Esnoc _ ?H (refines_right ?j ?e)] =>
    reshape_expr e ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_tp_pure e K e' j);
      [by rewrite ?fill_app | tc_solve | ..])
  end;
  [tc_solve || fail "tp_pure: cannot eliminate modality in the goal"
  |solve_ndisj || fail "tp_pure: cannot prove 'nclose specN ⊆ ?'"
  (* |iAssumptionCore || fail "tp_pure: cannot find spec_ctx" (* spec_ctx *) *)
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

Lemma tac_tp_store `{clutchGS Σ} k Δ1 Δ2 E1 i1 i2 K' e (l : loc) e' e2 v' v Q :
  (* TODO: here instead of True we can consider another Coq premise, like in tp_pure.
     Same goes for the rest of those tactics *)
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  envs_lookup_delete false i1 Δ1 = Some (false, refines_right k e, Δ2)%I →
  e = fill K' (Store (# l) e') →
  IntoVal e' v →
  (* re-compose the expression and the evaluation context *)
  e2 = fill K' #() →
  envs_lookup i2 Δ2 = Some (false, l ↦ₛ v')%I →
  match envs_simple_replace i2 false
     (Esnoc (Esnoc Enil i1 (refines_right k e2)) i2 (l ↦ₛ v)) Δ2 with
  | None => False
  | Some Δ3 => envs_entails Δ3 Q
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite /IntoVal.
  rewrite envs_entails_unseal. intros ??? -> <- -> ? HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id.
  rewrite !assoc -(assoc _ spec_ctx).
  rewrite -fill_app step_store // /= fill_app.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ₛ v)%I). simpl.
  rewrite assoc. rewrite (comm _ spec_ctx (l ↦ₛ _)%I).
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "tp_store" :=
  iStartProof;
  eapply tac_tp_store;
  [tc_solve || fail "tp_store: cannot eliminate modality in the goal"
  |solve_ndisj || fail "tp_store: cannot prove 'nclose specN ⊆ ?'"
  |iAssumptionCore || fail "tp_store: cannot find the RHS"
  |tp_bind_helper
  |tc_solve || fail "tp_store: cannot convert the argument to a value"
  |simpl; reflexivity || fail "tp_store: this should not happen"
  |iAssumptionCore || fail "tp_store: cannot find '? ↦ₛ ?'"
  |pm_reduce (* new goal *)].

Lemma tac_tp_load `{clutchGS Σ} k Δ1 Δ2 E1 i1 i2 K' e e2 (l : loc) v Q q :
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  envs_lookup_delete false i1 Δ1 = Some (false, refines_right k e, Δ2)%I →
  e = fill K' (Load #l) →
  envs_lookup i2 Δ2 = Some (false, l ↦ₛ{q} v)%I →
  e2 = fill K' (of_val v) →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (refines_right k e2)) i2 (l ↦ₛ{q} v)%I) Δ2 with
  | Some Δ3 => envs_entails Δ3 Q
  | None    => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? -> ? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
  rewrite /refines_right.
  rewrite right_id.
  rewrite assoc. rewrite -(assoc _ spec_ctx).
  rewrite -fill_app step_load /= // fill_app.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ₛ{q} v)%I).
  rewrite assoc.
  rewrite (comm _ _ (l ↦ₛ{q} v)%I).
  rewrite -assoc.
  rewrite HQ. by apply bi.wand_elim_r.
Qed.

Tactic Notation "tp_load" :=
  iStartProof;
  eapply tac_tp_load;
  [tc_solve || fail "tp_load: cannot eliminate modality in the goal"
  |solve_ndisj || fail "tp_load: cannot prove 'nclose specN ⊆ ?'"
  |iAssumptionCore || fail "tp_load: cannot find the RHS"
  |tp_bind_helper
  |iAssumptionCore || fail "tp_load: cannot find '? ↦ₛ ?'"
  |simpl; reflexivity || fail "tp_load: this should not happen"
  |pm_reduce (* new goal *)].

Lemma tac_tp_alloc `{clutchGS Σ} k Δ1 E1 i1 K' e e' v Q :
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  envs_lookup i1 Δ1 = Some (false, refines_right k e)%I →
  e = fill K' (ref e') →
  IntoVal e' v →
  (* TODO use match here as well *)
  (∀ l : loc, ∃ Δ2,
    envs_simple_replace i1 false
       (Esnoc Enil i1 (refines_right k (fill K' #l))) Δ1 = Some Δ2 ∧
    (envs_entails Δ2 ((l ↦ₛ v) -∗ Q)%I)) →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? Hfill <- HQ.
  rewrite (envs_lookup_sound' Δ1 false i1); last by eassumption.
  rewrite /refines_right.
  rewrite Hfill -fill_app /=.
  rewrite step_alloc //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r, bi.wand_intro_l.
  rewrite bi.sep_exist_r.
  apply bi.exist_elim=> l.
  destruct (HQ l) as (Δ2 & HΔ2 & HQ').
  rewrite (envs_simple_replace_sound' _ _ i1 _ _ HΔ2) /=.
  rewrite HQ' right_id.
  rewrite /refines_right fill_app.
  rewrite (comm _ _ (l ↦ₛ _)%I).
  rewrite assoc.
  rewrite (comm _ _ (l ↦ₛ _)%I).
  rewrite -(assoc _ (l ↦ₛ _)%I spec_ctx _). rewrite -assoc.
  rewrite bi.wand_elim_r.
  by rewrite bi.wand_elim_r.
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
  |solve_ndisj || fail "tp_alloc: cannot prove 'nclose specN ⊆ ?'"
  |iAssumptionCore || fail "tp_alloc: cannot find the RHS"
  |tp_bind_helper
  |tc_solve || fail "tp_alloc: expressions is not a value"
  |finish ()
(* new goal *)].

Tactic Notation "tp_alloc" "as" ident(j') :=
  let H := iFresh in tp_alloc as j' H.

(* Will this ever be used when the argument of alloc is not a value? *)
Lemma tac_tp_alloctape `{clutchGS Σ} k Δ1 E1 i1 K' e N z Q :
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  TCEq N (Z.to_nat z) →
  nclose specN ⊆ E1 →
  envs_lookup i1 Δ1 = Some (false, refines_right k e)%I →
  e = fill K' (alloc #z) →
  (* TODO use match here as well *)
  (∀ α : loc, ∃ Δ2,
    envs_simple_replace i1 false
       (Esnoc Enil i1 (refines_right k (fill K' #lbl:α))) Δ1 = Some Δ2 ∧
    (envs_entails Δ2 ((α ↪ₛ (N; [])) -∗ Q)%I)) →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ???? Hfill HQ.
  rewrite (envs_lookup_sound' Δ1 false i1); last by eassumption.
  rewrite /refines_right.
  rewrite Hfill -fill_app /=.
  rewrite step_alloctape //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r, bi.wand_intro_l.
  rewrite bi.sep_exist_r.
  apply bi.exist_elim=> l.
  destruct (HQ l) as (Δ2 & HΔ2 & HQ').
  rewrite (envs_simple_replace_sound' _ _ i1 _ _ HΔ2) /=.
  rewrite HQ' right_id.
  rewrite /refines_right fill_app.
  rewrite (comm _ _ (l ↪ₛ _)%I).
  rewrite assoc.
  rewrite (comm _ _ (l ↪ₛ _)%I).
  rewrite -(assoc _ (l ↪ₛ _)%I spec_ctx _). rewrite -assoc.
  rewrite bi.wand_elim_r.
  by rewrite bi.wand_elim_r.
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
  |solve_ndisj || fail "tp_alloctape: cannot prove 'nclose specN ⊆ ?'"
  |iAssumptionCore || fail "tp_alloctape: cannot find the RHS"
  |tp_bind_helper
  |finish ()
(* new goal *)].

Tactic Notation "tp_alloctape" "as" ident(j') :=
  let H := iFresh in tp_alloctape as j' H.

Lemma tac_tp_rand `{clutchGS Σ} k Δ1 Δ2 E1 i1 i2 K' e e2 (l : loc) N z n ns Q :
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  TCEq N (Z.to_nat z) →
  nclose specN ⊆ E1 →
  envs_lookup_delete false i1 Δ1 = Some (false, refines_right k e, Δ2)%I →
  e = fill K' (rand(#lbl:l) #z) →
  envs_lookup i2 Δ2 = Some (false, l ↪ₛ (N; n::ns))%I →
  e2 = fill K' (of_val #n) →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (refines_right k e2)) i2 (l ↪ₛ (N; ns))%I) Δ2 with
  | Some Δ3 => envs_entails Δ3 Q
  | None    => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ???? -> ? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
  rewrite /refines_right.
  rewrite right_id.
  rewrite assoc. rewrite -(assoc _ spec_ctx).
  rewrite -fill_app step_rand /= // fill_app.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↪ₛ (N; ns))%I).
  rewrite assoc.
  rewrite (comm _ _ (l ↪ₛ (N; ns))%I).
  rewrite -assoc.
  rewrite HQ. by apply bi.wand_elim_r.
Qed.

Tactic Notation "tp_rand" :=
  iStartProof;
  eapply tac_tp_rand;
  [tc_solve || fail "tp_rand: cannot eliminate modality in the goal"
  |tc_solve || fail "tp_rand: cannot convert bound to a natural number"
  |solve_ndisj || fail "tp_rand: cannot prove 'nclose specN ⊆ ?'"
  |iAssumptionCore || fail "tp_rand: cannot find the RHS"
  |tp_bind_helper
  |iAssumptionCore || fail "tp_rand: cannot find '? ↪ₛ ?'"
  |simpl; reflexivity || fail "tp_rand: this should not happen"
  |pm_reduce (* new goal *)].

(* (* helper lemma to apply wp_flipU_r, similar to tac_tp_rand  *) *)
(* Lemma tac_tp_flipU `{clutchGS Σ} k Δ1 E i1 K' e t Φ : *)
(*   (* shouldn't be required because it holds for Q = WP ... *) *)
(*   (* (∀ P, ElimModal True false false (|={E}=> P) P Q Q) → *) *)
(*   to_val t = None → *)
(*   nclose specN ⊆ E → *)
(*   envs_lookup i1 Δ1 = Some (false, refines_right k e)%I → *)
(*   e = fill K' (rand #z) → *)
(*   (forall (b : bool), exists e2, *)
(*       e2 = fill K' (of_val #b) /\ *)
(*       match envs_simple_replace i1 false *)
(*               (Esnoc Enil i1 (refines_right k e2))%I Δ1 with *)
(*       | Some Δ3 => envs_entails Δ3 (WP t @ E {{ Φ }}) *)
(*       | None    => False *)
(*       end) → *)
(*   envs_entails Δ1 (WP t @ E {{ Φ }}). *)
(* Proof. *)
(*   rewrite envs_entails_unseal. intros ??? -> HQ. *)
(*   rewrite envs_lookup_sound //; simpl. *)
(*   epose proof (λ x y, eq_refl (refines_right x y)) as rr_def. *)
(*   rewrite {1}/refines_right in rr_def. *)
(*   rewrite /refines_right -fill_app. *)
(*   rewrite rr_def. *)
(*   eapply (bi.wand_apply emp) ; *)
(*     [ iIntros "??" ; iApply (wp_flipU_r' _ _ (K' ++ k)) => // | ]. *)
(*   rewrite (assoc _ spec_ctx). *)
(*   rewrite rr_def. *)
(*   rewrite assoc. *)
(*   rewrite (comm _ bi_emp). rewrite -assoc. *)
(*   set (Δ2 := of_envs _). *)
(*   rewrite left_id. *)
(*   set (rr := refines_right _ _). *)
(*   set (P := (∀ _ , _)%I). *)
(*   apply bi.sep_mono_r. *)
(*   iIntros "Δ2" (b) "rr". *)
(*   rewrite rr_def. *)
(*   specialize (HQ b). *)
(*   destruct HQ as [e2 [He2 HQ]]. *)
(*   rewrite He2 in HQ. *)
(*   destruct envs_simple_replace as [Δ3|] eqn:H13 ; [|contradiction]. *)
(*   iApply HQ. *)
(*   apply envs_simple_replace_singleton_sound' in H13. *)
(*   subst. subst Δ2. *)
(*   iApply (H13 with "Δ2"). *)
(*   rewrite /refines_right -fill_app. iFrame. *)
(* Qed. *)


(* Tactic Notation "tp_flipU" ident(b) := *)
(*   iStartProof; *)
(*   eapply tac_tp_flipU; *)
(*   [done || fail "tp_flipU: cannot prove 'to_val ? = None'" *)
(*   |solve_ndisj || fail "tp_flipU: cannot prove 'nclose specN ⊆ ?'" *)
(*   |iAssumptionCore || fail "tp_flipU: cannot find the RHS" *)
(*   |tp_bind_helper *)
(*   |(intros b *)
(*     ; eexists *)
(*     ; split *)
(*     ; [reflexivity *)
(*       | pm_reduce]) (* new goal *)]. *)

(* *)
(* (**************************) *)
(* (* tp_apply *) *)

(* Fixpoint print_sel (ss : list sel_pat) (s : string) := *)
(*   match ss with *)
(*   | nil => s *)
(*   | SelPure :: ss' => (String "%" (String " " (print_sel ss' s))) *)
(*   | SelPersistent :: ss' =>  (String "#" (print_sel ss' s)) *)
(*   | SelSpatial :: ss' => (* no clue :( *) (print_sel ss' s) *)
(*   | SelIdent (INamed n) :: ss' => append n (String " " (print_sel ss' s)) *)
(*   | SelIdent (IAnon _) :: ss' => String "?" (String " " (print_sel ss' s)) *)
(*   (* wat to do with the index? *) *)
(*   end. *)

(* Ltac print_sel ss := *)
(*   lazymatch type of ss with *)
(*   | list sel_pat => eval vm_compute in (print_sel ss "") *)
(*   | string => ss *)
(*   end. *)

(* Definition appP (ss : option (list sel_pat)) (Hj Hs : string) := *)
(*   match ss with *)
(*   | Some ss' => cons (SelIdent Hs) (app ss' [SelIdent Hj]) *)
(*   | None => cons (SelIdent Hs) [SelIdent Hj] *)
(*   end. *)

(* Definition add_elim_pat (pat : string) (Hj : string) := *)
(*   match pat with *)
(*   | EmptyString => Hj *)
(*   | _ => append (String "[" (append Hj (String " " pat))) "]" *)
(*   end. *)

(* Tactic Notation "tp_apply" constr(j) open_constr(lem) "with" constr(Hs) "as" constr(Hr) := *)
(*   iStartProof; *)
(*   let rec find Γ j := *)
(*     match Γ with *)
(*     | Esnoc ?Γ (IAnon _) ?P => *)
(*       find Γ j *)
(*     | Esnoc ?Γ (INamed ?Hj) ?P => *)
(*       lazymatch P with *)
(*       | (j ⤇ _)%I => Hj *)
(*       | _ => find Γ j *)
(*       end *)
(*     | Enil => fail 2 "tp_apply: cannot find " j " ⤇ _ " *)
(*     | _ => fail 2 "tp_apply: unknown error in find" *)
(*     end in *)
(*   let rec findSpec Γp Γs := *)
(*     match Γp with *)
(*     | Esnoc ?Γ (IAnon _) _ => findSpec Γ Γs *)
(*     | Esnoc ?Γ (INamed ?Hspec) ?P => *)
(*       lazymatch P with *)
(*       | (spec_ctx _)%I => Hspec *)
(*       | _ => findSpec Γ Γs *)
(*       end *)
(*     | Enil => *)
(*       match Γs with *)
(*       | Enil => fail 2 "tp_apply: cannot find spec_ctx _" *)
(*       | _ => findSpec Γs Enil *)
(*       end *)
(*     | _ => fail 2 "tp_apply: unknown error in findSpec" *)
(*     end in *)
(*   match goal with *)
(*   | |- envs_entails (Envs ?Γp ?Γs) ?Q => *)
(*     let Hj := (find Γs j) in *)
(*     let Hspec := findSpec Γp Γs in *)
(*     let pat := eval vm_compute in (appP (sel_pat.parse Hs) Hj Hspec) in *)
(*     let pats := print_sel pat in *)
(*     let elim_pats := eval vm_compute in (add_elim_pat Hr Hj) in *)
(*     iMod (lem with pats) as elim_pats; first try by solve_ndisj *)
(*   | _ => fail "tp_apply: cannot parse the context" *)
(*   end. *)

(* Tactic Notation "tp_apply" constr(j) open_constr(lem) "with" constr(Hs) := tp_apply j lem with Hs as "". *)

(* Tactic Notation "tp_apply" constr(j) open_constr(lem) "as" constr(Hr) := tp_apply j lem with "" as Hr. *)

(* Tactic Notation "tp_apply" constr(j) open_constr(lem) := tp_apply j lem with "" as "". *)
(* *)
