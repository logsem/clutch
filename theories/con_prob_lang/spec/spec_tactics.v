From iris.bi Require Export bi updates atomic.
From iris.base_logic.lib Require Import fancy_updates.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.

(*From clutch.bi Require Import weakestpre.*)
From clutch.con_prob_lang Require Import lang tactics notation class_instances spec_ra wp_tactics.
Set Default Proof Using "Type*".

(** ** bind *)
Lemma tac_tp_bind_gen `{!specG_con_prob_lang Σ} j Δ Δ' i p e e' Q :
  envs_lookup i Δ = Some (p, j ⤇ e)%I →
  e = e' →
  envs_simple_replace i p (Esnoc Enil i (j ⤇ e')) Δ = Some Δ' →
  (envs_entails Δ' Q) →
  (envs_entails Δ Q).
Proof.
  rewrite envs_entails_unseal. intros; subst. simpl.
  rewrite envs_simple_replace_sound // /=.
  destruct p; rewrite /= ?right_id; by rewrite bi.wand_elim_r.
Qed.

Lemma tac_tp_bind `{specG_con_prob_lang Σ} j e' Δ Δ' i p K' e Q :
  envs_lookup i Δ = Some (p, j ⤇ e)%I →
  e = fill K' e' →
  envs_simple_replace i p (Esnoc Enil i (j ⤇ fill K' e')) Δ = Some Δ' →
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

Tactic Notation "tp_normalise" constr(j) :=
  iStartProof;
  eapply (tac_tp_bind_gen j);
    [iAssumptionCore (* prove the lookup *)
    | lazymatch goal with
      | |- fill ?K ?e = _ =>
          by rewrite /= ?fill_app /=
      | |- ?e = _ => try fast_done
      end
    |reflexivity
    |(* new goal *)].

Tactic Notation "tp_bind" constr(j) open_constr(efoc) :=
  iStartProof;
  eapply (tac_tp_bind j efoc);
    [iAssumptionCore (* prove the lookup *)
    |tp_bind_helper (* do actual work *)
    |reflexivity
    |(* new goal *)].


(** A basic set of requirements for a weakest precondition *)
Class UpdPure `{specG_con_prob_lang Σ} (upd : coPset -> coPset -> iProp Σ -> iProp Σ):= {
  tptac_upd_pure_step j E e1 e2 φ n :
    PureExec φ n e1 e2 →
    φ →
    j ⤇ e1 ⊢ upd E E (j ⤇ e2) }.

Lemma tac_tp_pure `{!specG_con_prob_lang Σ, Hupd: !UpdPure upd} j e K e1 e2 Δ1 i1 e' ϕ ψ E1 Q n :
  e = fill K e1 →
  PureExec ϕ n e1 e2 →
  (∀ P, ElimModal ψ false false (upd E1 E1 P) P Q Q) →
  envs_lookup i1 Δ1 = Some (false, j ⤇ e)%I →
  ψ →
  ϕ →
  e' = fill K e2 →
  match envs_simple_replace i1 false (Esnoc Enil i1 (j ⤇ e')) Δ1 with
  | Some Δ2 => envs_entails Δ2 Q
  | None => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros -> Hpure ? HΔ1 Hψ Hϕ -> ?.
  destruct (envs_simple_replace _ _ _ _) as [Δ2|] eqn:HΔ2; try done.
  rewrite (envs_simple_replace_sound Δ1 Δ2 i1) //; simpl.
  rewrite right_id.
  (* rewrite (step_pure E1) //. *)
  rewrite -[Q]elim_modal // /=.
  apply bi.sep_mono.
  - eapply tptac_upd_pure_step; [by eapply pure_exec_fill|done].
  - simpl. 
    apply bi.wand_intro_l.
    by rewrite bi.wand_elim_r.
Qed.


Tactic Notation "tp_pure_at" constr(j) open_constr(ef) :=
  iStartProof;
  lazymatch goal with
  | |- context[environments.Esnoc _ ?H (j ⤇ (fill ?K' ?e))] =>
    reshape_expr e ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_tp_pure j (fill K' e) (K++K') e');
      [by rewrite ?fill_app | tc_solve | ..])
  | |- context[environments.Esnoc _ ?H (j ⤇ ?e)] =>
    reshape_expr e ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_tp_pure j e K e');
      [by rewrite ?fill_app | tc_solve | ..])
  end;
  [tc_solve || fail "tp_pure: cannot eliminate modality in the goal"
  |iAssumptionCore || fail "tp_pure: cannot find the RHS" (* TODO fix error message *)
  |try (exact I || reflexivity) (* ψ *)
  |try (exact I || reflexivity) (* ϕ *)
  |simpl; reflexivity ||  fail "tp_pure: this should not happen" (* e' = fill K' e2 *)
  |pm_reduce (* new goal *)].

Tactic Notation "tp_pure" constr(j) := tp_pure_at j _.
Tactic Notation "tp_pures" constr(j) := repeat (tp_pure j).
Tactic Notation "tp_rec" constr(j) :=
  let H := fresh in
  assert (H := AsRecV_recv);
  tp_pure_at j (App _ _);
  clear H.
Tactic Notation "tp_seq" constr(j):= tp_rec j.
Tactic Notation "tp_let" constr(j):= tp_rec j.
Tactic Notation "tp_lam" constr(j):= tp_rec j.
Tactic Notation "tp_fst" constr(j):= tp_pure_at j (Fst (PairV _ _)).
Tactic Notation "tp_snd" constr(j):= tp_pure_at j (Snd (PairV _ _)).
Tactic Notation "tp_proj" constr(j):= tp_pure_at j (_ (PairV _ _)).
Tactic Notation "tp_case_inl" constr(j):= tp_pure_at j (Case (InjLV _) _ _).
Tactic Notation "tp_case_inr" constr(j):= tp_pure_at j (Case (InjRV _) _ _).
Tactic Notation "tp_case" constr(j):= tp_pure_at j (Case _ _ _).
Tactic Notation "tp_binop" constr(j):= tp_pure_at j (BinOp _ _ _).
Tactic Notation "tp_op" constr(j):= tp_binop j.
Tactic Notation "tp_if_true" constr(j):= tp_pure_at j (If #true _ _).
Tactic Notation "tp_if_false" constr(j):= tp_pure_at j (If #false _ _).
Tactic Notation "tp_if" constr(j):= tp_pure_at j (If _ _ _).
Tactic Notation "tp_pair" constr(j):= tp_pure_at j (Pair _ _).
Tactic Notation "tp_closure" constr(j):= tp_pure_at j (Rec _ _ _).

(** Heap *)
Class UpdHeap `{specG_con_prob_lang Σ} (upd : coPset -> coPset -> iProp Σ -> iProp Σ):= {
    tptac_upd_alloc j K E v :
    j ⤇ (fill K (Alloc (Val v))) ⊢ upd E E (∃ l, l ↦ₛ v ∗ j ⤇ (fill K (LitV (LitLoc l))));

    (** TODO upd allocN on the spec side*)
  (* tptac_upd_allocN j K E v n : *)
  (*   (0 < n)%Z → *)
  (*   True -> *)
  (*   j ⤇ (fill K ((AllocN (Val $ LitV $ LitInt $ n) (Val v)))) ⊢ *)
    (*   upd E E (∃ l, l ↦ₛ (replicate (Z.to_nat n) v) ∗ j ⤇ (fill K (LitV (LitLoc l)))) *)

    tptac_upd_load j K E v l dq :
    ( l ↦ₛ{dq} v) -∗
    j ⤇ (fill K (Load (Val $ LitV $ LitLoc l))) -∗
    upd E E (l ↦ₛ{dq} v ∗ j ⤇ (fill K v));
    
    tptac_upd_store j K E v v' l :
    ( l ↦ₛ v') -∗
    j ⤇ (fill K (Store (Val $ LitV $ LitLoc l) (Val v))) -∗
    upd E E (l ↦ₛ v ∗ j ⤇ (fill K (LitV LitUnit%V))); }.


Lemma tac_tp_store `{!specG_con_prob_lang Σ, !UpdHeap upd} j Δ1 Δ2 E1 i1 i2 K e (l : loc) e' e2 v' v Q :
  (* TODO: here instead of True we can consider another Coq premise, like in tp_pure.
     Same goes for the rest of those tactics *)
  (∀ P, ElimModal True false false (upd E1 E1 P) P Q Q) →
  envs_lookup_delete false i1 Δ1 = Some (false, j ⤇ e, Δ2)%I →
  e = fill K (Store (# l) e') →
  IntoVal e' v →
  (* re-compose the expression and the evaluation context *)
  e2 = fill K #() →
  envs_lookup i2 Δ2 = Some (false, l ↦ₛ v')%I →
  match envs_simple_replace i2 false
     (Esnoc (Esnoc Enil i1 (j ⤇ e2)) i2 (l ↦ₛ v)) Δ2 with
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
  (* rewrite step_store //=. *)
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono; simpl.
  - iIntros "[??]". iApply (tptac_upd_store with "[$][$]").
  - apply bi.wand_intro_l.
    by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "tp_store" constr(j) :=
  iStartProof;
  eapply (tac_tp_store j);
  [tc_solve || fail "tp_store: cannot eliminate modality in the goal"
  |iAssumptionCore || fail "tp_store: cannot find the RHS"
  |tp_bind_helper
  |tc_solve || fail "tp_store: cannot convert the argument to a value"
  |simpl; reflexivity || fail "tp_store: this should not happen"
  |iAssumptionCore || fail "tp_store: cannot find '? ↦ₛ ?'"
  |pm_reduce (* new goal *)].


Lemma tac_tp_load `{!specG_con_prob_lang Σ, !UpdHeap upd} j Δ1 Δ2 E1 i1 i2 K e e2 (l : loc) v Q q :
  (∀ P, ElimModal True false false (upd E1 E1 P) P Q Q) →
  envs_lookup_delete false i1 Δ1 = Some (false, j ⤇ e, Δ2)%I →
  e = fill K (Load #l) →
  envs_lookup i2 Δ2 = Some (false, l ↦ₛ{q} v)%I →
  e2 = fill K (of_val v) →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (j ⤇ e2)) i2 (l ↦ₛ{q} v)%I) Δ2 with
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
  (* rewrite step_load //=. *)
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono.
  - iIntros "[??]". iApply (tptac_upd_load with "[$][$]").
  - apply bi.wand_intro_l.
    by rewrite bi.wand_elim_r.
Qed. 

Tactic Notation "tp_load" constr(j):=
  iStartProof;
  eapply (tac_tp_load j);
  [tc_solve || fail "tp_load: cannot eliminate modality in the goal"
  |iAssumptionCore || fail "tp_load: cannot find the RHS"
  |tp_bind_helper
  |iAssumptionCore || fail "tp_load: cannot find '? ↦ₛ ?'"
  |simpl; reflexivity || fail "tp_load: this should not happen"
  |pm_reduce (* new goal *)].


Lemma tac_tp_alloc `{!specG_con_prob_lang Σ, !UpdHeap upd} j Δ1 E1 i1 K e e' v Q :
  (∀ P, ElimModal True false false (upd E1 E1 P) P Q Q) →
  envs_lookup i1 Δ1 = Some (false, j ⤇ e)%I →
  e = fill K (ref e') →
  IntoVal e' v →
  (∀ l : loc, ∃ Δ2,
    envs_simple_replace i1 false
       (Esnoc Enil i1 (j ⤇ fill K #l)) Δ1 = Some Δ2 ∧
    (envs_entails Δ2 ((l ↦ₛ v) -∗ Q)%I)) →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ?? Hfill <- HQ.
  rewrite (envs_lookup_sound' Δ1 false i1); last by eassumption.
  rewrite Hfill /=.
  (* rewrite step_alloc //. *)
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono; first apply tptac_upd_alloc.
  - simpl. apply bi.wand_intro_l.
    rewrite bi.sep_exist_r.
    apply bi.exist_elim=> l.
    destruct (HQ l) as (Δ2 & HΔ2 & HQ').
    rewrite (envs_simple_replace_sound' _ _ i1 _ _ HΔ2) /=.
    rewrite HQ' right_id.
    iIntros "[[H Hl] Hcnt]".
    iApply ("Hcnt" with "Hl H").
Qed.

Tactic Notation "tp_alloc" constr(j) "as" ident(l) constr(H) :=
  let finish _ :=
      first [ intros l | fail 1 "tp_alloc:" l "not fresh"];
        eexists; split;
        [ reduction.pm_reflexivity
        | (iIntros H; tp_normalise j) || fail 1 "tp_alloc:" H "not correct intro pattern" ] in
  iStartProof;
  eapply (tac_tp_alloc j);
  [tc_solve || fail "tp_alloc: cannot eliminate modality in the goal"
  |iAssumptionCore || fail "tp_alloc: cannot find the RHS"
  |tp_bind_helper
  |tc_solve || fail "tp_alloc: expressions is not a value"
  |finish ()
(* new goal *)].

Tactic Notation "tp_alloc" constr(j) "as" ident(j') :=
  let H := iFresh in tp_alloc j as j' H.


(** Atomic Concurrency *)
Class UpdAtomicConcurrency `{specG_con_prob_lang Σ} (upd : coPset -> coPset -> iProp Σ -> iProp Σ):= {
    
    tptac_upd_cmpxchg_fail j K E l dq v v1 v2:
    v≠v1->
    vals_compare_safe v v1 ->
    (l ↦ₛ{dq} v) -∗
    j ⤇ fill K (CmpXchg (Val $ LitV $ LitLoc $ l) (Val v1) (Val v2)) -∗
    upd E E (l ↦ₛ{dq} v ∗ j⤇ fill K((PairV v (LitV $ LitBool false)))%V);
    
    tptac_upd_cmpxchg_suc j K E l v v1 v2:
    v=v1->
    vals_compare_safe v v1 ->
    (l ↦ₛ v) -∗
    j ⤇ fill K (CmpXchg (Val $ LitV $ LitLoc $ l) (Val v1) (Val v2)) -∗
    upd E E (l ↦ₛ v2 ∗ j⤇ fill K((PairV v (LitV $ LitBool true)))%V); 
    
    tptac_upd_xchg j K E l v1 v2:
    (l ↦ₛ v1) -∗
    j ⤇ fill K (Xchg (Val $ LitV $ LitLoc $ l) (Val v2)) -∗
    upd E E (l ↦ₛ v2 ∗ j⤇ fill K v1); 
    
    tptac_upd_faa j K E l i1 i2:
    (l ↦ₛ (LitV $ LitInt $ i1)) -∗
    j ⤇ fill K (FAA (Val $ LitV $ LitLoc $ l) (Val $ LitV $ LitInt i2) ) -∗
    upd E E (l ↦ₛ (LitV $ LitInt $ (i1+i2)%Z) ∗ j⤇ fill K (LitV $ LitInt i1));

    tptac_upd_fork j K E e:
    j ⤇ fill K (Fork e) -∗
    upd E E (∃ k, k ⤇ e ∗ j⤇ fill K (LitV LitUnit));
  }.

Lemma tac_tp_cmpxchg_fail `{!specG_con_prob_lang Σ, !UpdAtomicConcurrency upd} j K Δ1 Δ2 E1 i1 i2 e enew (l : loc) e1 e2 v' v1 v2 Q q :
  (∀ P, ElimModal True false false (upd E1 E1 P) P Q Q) →
  envs_lookup_delete false i1 Δ1 = Some (false, j ⤇ e, Δ2)%I →
  e = fill K (CmpXchg #l e1 e2) →
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  envs_lookup i2 Δ2 = Some (false, l ↦ₛ{q} v')%I →
  v' ≠ v1 →
  vals_compare_safe v' v1 →
  enew = fill K (v', #false)%V →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (j ⤇ enew)) i2 (l ↦ₛ{q} v')%I) Δ2 with
  | Some Δ3 => envs_entails Δ3 Q
  | None    =>  False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ?? -> Hv1 Hv2 ??? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
  rewrite right_id.
  rewrite assoc.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono.
  - iIntros "[??]". simpl.
    rewrite -Hv1-Hv2.
    by iApply (tptac_upd_cmpxchg_fail with "[$][$]").
  - simpl.
    apply bi.wand_intro_l.
    rewrite HQ.
    apply bi.wand_elim_r.
Qed. 

Tactic Notation "tp_cmpxchg_fail" constr(j) :=
  iStartProof;
  eapply (tac_tp_cmpxchg_fail j);
    [tc_solve || fail "tp_cmpxchg_fail: cannot eliminate modality in the goal"
    |iAssumptionCore || fail "tp_cmpxchg_fail: cannot find the RHS '" j "'"
    |tp_bind_helper (* e = K'[CmpXchg _ _ _] *)
    |tc_solve || fail "tp_cmpxchg_fail: argument is not a value"
    |tc_solve || fail "tp_cmpxchg_fail: argument is not a value"
    |iAssumptionCore || fail "tp_cmpxchg_fail: cannot find '? ↦ ?'"
    |try (simpl; congruence) (* v' ≠ v1 *)
    |try solve_vals_compare_safe
    |simpl; reflexivity || fail "tp_cmpxchg_fail: this should not happen"
    |pm_reduce (* new goal *)].

Lemma tac_tp_cmpxchg_suc `{!specG_con_prob_lang Σ, !UpdAtomicConcurrency upd} j K Δ1 Δ2 E1 i1 i2 e enew (l : loc) e1 e2 v' v1 v2 Q :
  (∀ P, ElimModal True false false (upd E1 E1 P) P Q Q) →
  envs_lookup_delete false i1 Δ1 = Some (false, j ⤇ e, Δ2)%I →
  e = fill K (CmpXchg #l e1 e2) →
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  envs_lookup i2 Δ2 = Some (false, l ↦ₛ v')%I →
  v' = v1 →
  vals_compare_safe v' v1 →
  enew = fill K (v', #true)%V →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (j ⤇ enew)) i2 (l ↦ₛ v2)%I) Δ2 with
  | Some Δ3 => envs_entails Δ3 Q
  | None => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ?? -> Hv1 Hv2 ??? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
  rewrite right_id.
  rewrite assoc. 
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono.
  - iIntros "[??]". simpl.
    rewrite -Hv1-Hv2.
    by iApply (tptac_upd_cmpxchg_suc with "[$][$]").
  - apply bi.wand_intro_l.
    rewrite HQ. by apply bi.wand_elim_r.
Qed.

Tactic Notation "tp_cmpxchg_suc" constr(j) :=
  iStartProof;
  eapply (tac_tp_cmpxchg_suc j);
  [tc_solve || fail "tp_cmpxchg_suc: cannot eliminate modality in the goal"
  |iAssumptionCore || fail "tp_cmpxchg_suc: cannot the RHS '" j "'"
  |tp_bind_helper (* e = K'[CmpXchg _ _ _] *)
  |tc_solve || fail "tp_cmpxchg_suc: argument is not a value"
  |tc_solve || fail "tp_cmpxchg_suc: argument is not a value"
  |iAssumptionCore || fail "tp_cmpxchg_suc: cannot find '? ↦ ?'"
  |try (simpl; congruence)     (* v' = v1 *)
  |try solve_vals_compare_safe
  |simpl; reflexivity || fail "tp_cmpxchg_suc: this should not happen"
  |pm_reduce (* new goal *)].


Lemma tac_tp_xchg `{!specG_con_prob_lang Σ, !UpdAtomicConcurrency upd} j K Δ1 Δ2 E1 i1 i2 e (l : loc) e' e2 v' v Q :
  (∀ P, ElimModal True false false (upd E1 E1 P) P Q Q) →
  envs_lookup_delete false i1 Δ1 = Some (false, j ⤇ e, Δ2)%I →
  e = fill K (Xchg (# l) e') →
  IntoVal e' v →
  (* re-compose the expression and the evaluation context *)
  envs_lookup i2 Δ2 = Some (false, l ↦ₛ v')%I →
  e2 = fill K (of_val v') →
  match envs_simple_replace i2 false
     (Esnoc (Esnoc Enil i1 (j ⤇ e2)) i2 (l ↦ₛ v)) Δ2 with
  | None => False
  | Some Δ3 => envs_entails Δ3 Q
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite /IntoVal.
  rewrite envs_entails_unseal. intros ?? -> <- ? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id.
  rewrite assoc.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono.
  - iIntros "[??]". simpl.
    by iApply (tptac_upd_xchg with "[$][$]").
  - apply bi.wand_intro_l.
    by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "tp_xchg" constr(j) :=
  iStartProof;
  eapply (tac_tp_xchg j);
  [tc_solve || fail "tp_xchg: cannot eliminate modality in the goal"
  |iAssumptionCore || fail "tp_xchg: cannot find '" j " ' RHS"
  |tp_bind_helper
  |tc_solve || fail "tp_xchg: cannot convert the argument to a value"
  |iAssumptionCore || fail "tp_xchg: cannot find '? ↦ₛ ?'"
  |simpl; reflexivity || fail "tp_xchg: this should not happen"
  |pm_reduce (* new goal *)].

Lemma tac_tp_faa `{!specG_con_prob_lang Σ, !UpdAtomicConcurrency upd} j K Δ1 Δ2 E1 i1 i2 e enew (l : loc)  e2 (z1 z2 : Z) Q :
  (∀ P, ElimModal True false false (upd E1 E1 P) P Q Q) →
  envs_lookup_delete false i1 Δ1 = Some (false, j ⤇ e, Δ2)%I →
  e = fill K (FAA #l e2) →
  IntoVal e2 #z2 →
  envs_lookup i2 Δ2 = Some (false, l ↦ₛ #z1)%I →
  enew = fill K #z1 →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (j ⤇ enew)) i2 (l ↦ₛ #(z1+z2))%I) Δ2 with
    | Some Δ3 =>   envs_entails Δ3 Q
    | None => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ?? -> <- ? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
  rewrite right_id.
  rewrite assoc.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono.
  - iIntros "[??]". simpl.
    iApply (tptac_upd_faa with "[$][$]").
  - apply bi.wand_intro_l.
    rewrite HQ. by apply bi.wand_elim_r.
Qed.

Tactic Notation "tp_faa" constr(j) :=
  iStartProof;
  eapply (tac_tp_faa j);
  [tc_solve || fail "tp_faa: cannot eliminate modality in the goal"
  |iAssumptionCore || fail "tp_faa: cannot find the RHS '" j "'"
  |tp_bind_helper (* e = K'[FAA _ _ _] *)
  |tc_solve (* IntoVal *)
  |iAssumptionCore || fail "tp_faa: cannot find '? ↦ ?'"
  |simpl;reflexivity || fail "tp_faa: this should not happen"
  |pm_reduce (* new goal *)].


Lemma tac_tp_fork `{!specG_con_prob_lang Σ, !UpdAtomicConcurrency upd} j K Δ1 E1 i1 e enew e' Q :
  (∀ P, ElimModal True false false (upd E1 E1 P) P Q Q) →
  envs_lookup i1 Δ1 = Some (false, j ⤇ e)%I →
  e = fill K (Fork e') →
  enew = fill K #() →
  match envs_simple_replace i1 false
      (Esnoc Enil i1 (j ⤇ enew )) Δ1 with
  | Some Δ2 => envs_entails Δ2 (∀ j', j' ⤇ e' -∗ Q)%I
  | None => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??->-> HQ.
  destruct (envs_simple_replace _ _ _ _) as [Δ2|] eqn:HΔ2; last done.
  rewrite (envs_simple_replace_sound Δ1 Δ2 i1) //; simpl.
  rewrite right_id.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono.
  - iIntros "?".
    by iApply (tptac_upd_fork with "[$]").
  - apply bi.wand_intro_l.
    rewrite bi.sep_exist_r.
    apply bi.exist_elim. intros j'.
    rewrite -assoc.
    rewrite bi.wand_elim_r.
    rewrite HQ. 
    rewrite (bi.forall_elim j') /=.
    by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "tp_fork" constr(j) :=
  iStartProof;
  eapply (tac_tp_fork j);
  [tc_solve || fail "tp_fork: cannot eliminate modality in the goal"
  |iAssumptionCore || fail "tp_fork: cannot find the RHS '" j "'"
  |tp_bind_helper
  |simpl; reflexivity || fail "tp_fork: this should not happen"
  |pm_reduce (* new goal *)].

Tactic Notation "tp_fork" constr(j) "as" ident(j') constr(H) :=
  iStartProof;
  eapply (tac_tp_fork j);
  [tc_solve || fail "tp_fork: cannot eliminate modality in the goal"
  |iAssumptionCore || fail "tp_fork: cannot find the RHS '" j "'"
  |tp_bind_helper
  |simpl; reflexivity || fail "tp_fork: this should not happen"
  |pm_reduce;
   (iIntros (j') || fail 1 "tp_fork: " j' " not fresh ");
   (iIntros H || fail 1 "tp_fork: " H " not fresh")
(* new goal *)].

Tactic Notation "tp_fork" constr(j) "as" ident(j') :=
  let H := iFresh in tp_fork j as j' H.


(* (** Tapes *) *)
(* Class GwpTacticsTapes Σ A (laters : bool) (gwp : A → coPset → expr → (val → iProp Σ) → iProp Σ):= { *)
(*   wptac_mapsto_tape : loc → dfrac → nat -> (list nat) → iProp Σ; *)

(*   wptac_wp_alloctape E (N : nat) (z : Z) a Φ : *)
(*     TCEq N (Z.to_nat z) -> *)
(*     True -∗ *)
(*     (▷?laters (∀ l, (wptac_mapsto_tape l (DfracOwn 1) N nil) -∗ Φ (LitV (LitLbl l))%V)) -∗ *)
(*     gwp a E (AllocTape (Val $ LitV $ LitInt $ z)) Φ; *)

(*     wptac_wp_rand_tape E N (n : nat) (z : Z) ns l dq a Φ : *)
(*     TCEq N (Z.to_nat z) -> *)
(*     (▷ wptac_mapsto_tape l dq N (n::ns)) -∗ *)
(*     (▷?laters ((wptac_mapsto_tape l dq N ns) -∗ ⌜ n ≤ N ⌝ -∗ Φ (LitV $ LitInt $ n)%V)) -∗ *)
(*     gwp a E (Rand (LitV (LitInt z)) (LitV (LitLbl l))) Φ; *)
(*   }. *)


(* Section wp_tactics. *)
(*   Context `{GwpTacticsBase Σ A hlc gwp}. *)

(*   Local Notation "'WP' e @ s ; E {{ Φ } }" := (gwp s E e%E Φ) *)
(*     (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)
(*   Local Notation "'WP' e @ s ; E {{ v , Q } }" := (gwp s E e%E (λ v, Q)) *)
(*     (at level 20, e, Q at level 200, *)
(*      format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope. *)

(*   Lemma tac_wp_expr_eval Δ a E Φ e e' : *)
(*     (∀ (e'':=e'), e = e'') → *)
(*     envs_entails Δ (WP e' @ a; E {{ Φ }}) → envs_entails Δ (WP e @ a; E {{ Φ }}). *)
(*   Proof. by intros ->. Qed. *)

(*   Lemma tac_wp_pure_later laters `{!GwpTacticsPure Σ A laters gwp} Δ Δ' E K e1 e2 φ n Φ a : *)
(*     PureExec φ n e1 e2 → *)
(*     φ → *)
(*     MaybeIntoLaterNEnvs (if laters then n else 0) Δ Δ' → *)
(*     envs_entails Δ' (WP (fill K e2) @ a; E {{ Φ }}) → *)
(*     envs_entails Δ (WP (fill K e1) @ a; E {{ Φ }}). *)
(*   Proof. *)
(*     rewrite envs_entails_unseal=> ??? HΔ'. rewrite into_laterN_env_sound /=. *)
(*     (* We want [pure_exec_fill] to be available to TC search locally. *) *)
(*     pose proof @pure_exec_fill. *)
(*     rewrite HΔ' -wptac_wp_pure_step //. *)
(*   Qed. *)

(*   Lemma tac_wp_value_nofupd Δ E Φ v a : *)
(*     envs_entails Δ (Φ v) → envs_entails Δ (WP (of_val v) @ a; E {{ Φ }}). *)
(*   Proof. rewrite envs_entails_unseal=> ->. apply wptac_wp_value. Qed. *)

(*   Lemma tac_wp_value' Δ E Φ v a : *)
(*     envs_entails Δ (|={E}=> Φ v) → envs_entails Δ (WP (of_val v) @ a; E {{ Φ }}). *)
(*   Proof. rewrite envs_entails_unseal=> ->. by rewrite -wptac_wp_fupd -wptac_wp_value. Qed. *)

(* End wp_tactics. *)

(* Section wp_bind_tactics. *)
(*   Context `{GwpTacticsBind Σ A hlc gwp}. *)

(*   Local Notation "'WP' e @ s ; E {{ Φ } }" := (gwp s E e%E Φ) *)
(*     (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)
(*   Local Notation "'WP' e @ s ; E {{ v , Q } }" := (gwp s E e%E (λ v, Q)) *)
(*     (at level 20, e, Q at level 200, *)
(*      format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.   *)
  
(*   Lemma tac_wp_bind K Δ E Φ e f a : *)
(*     f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *) *)
(*     envs_entails Δ (WP e @ a; E {{ v, WP f (Val v) @ a; E {{ Φ }} }})%I → *)
(*     envs_entails Δ (WP fill K e @ a; E {{ Φ }}). *)
(*   Proof. rewrite envs_entails_unseal=> -> ->. by apply: wptac_wp_bind. Qed. *)
(* End wp_bind_tactics.    *)

(* (* TODO: find a better way so that we do not need to have a case for both [wp] and [twp]... *) *)
(* Tactic Notation "wp_expr_eval" tactic3(t) := *)
(*   iStartProof; *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*       notypeclasses refine (tac_wp_expr_eval _ _ _ _ e _ _ _ ); *)
(*       [apply _|let x := fresh in intros x; simpl; unfold x; notypeclasses refine eq_refl|] *)
(*   | |- envs_entails _ (twp ?s ?E ?e ?Q) => *)
(*       notypeclasses refine (tac_wp_expr_eval _ _ _ _ e _ _ _ ); *)
(*       [apply _|let x := fresh in intros x; simpl; unfold x; notypeclasses refine eq_refl|] *)
(*   | _ => fail "wp_expr_eval: not a 'wp'" *)
(*   end. *)
(* Ltac wp_expr_simpl := wp_expr_eval simpl. *)

(* (** Simplify the goal if it is [wp] of a value. *)
(*   If the postcondition already allows a fupd, do not add a second one. *)
(*   But otherwise, *do* add a fupd. This ensures that all the lemmas applied *)
(*   here are bidirectional, so we never will make a goal unprovable. *) *)
(* Ltac wp_value_head := *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E (of_val _) (λ _, fupd ?E _ _)) => *)
(*       eapply tac_wp_value_nofupd *)
(*   | |- envs_entails _ (wp ?s ?E (of_val _) (λ _, wp _ ?E _ _)) => *)
(*       eapply tac_wp_value_nofupd *)
(*   | |- envs_entails _ (wp ?s ?E (of_val _) _) => *)
(*       eapply tac_wp_value' *)
(*   | |- envs_entails _ (twp ?s ?E (of_val _) (λ _, fupd ?E _ _)) => *)
(*       eapply tac_wp_value_nofupd *)
(*   | |- envs_entails _ (twp ?s ?E (of_val _) (λ _, twp _ ?E _ _)) => *)
(*       eapply tac_wp_value_nofupd *)
(*   | |- envs_entails _ (twp ?s ?E (of_val _) _) => *)
(*       eapply tac_wp_value' *)
(*   end. *)

(* Ltac wp_finish := *)
(*   (* simplify occurences of [wptac_mapsto] projections  *) *)
(*   rewrite ?[wptac_mapsto _ _ _]/=; *)
(*   (* simplify occurences of [wptac_mapsto_tape] projections  *) *)
(*   rewrite ?[wptac_mapsto_tape _ _ _]/=; *)
(*   (* simplify occurences of subst/fill *) *)
(*   wp_expr_simpl; *)
(*   (* in case we have reached a value, get rid of the wp *) *)
(*   try wp_value_head; *)
(*   (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and λs caused by wp_value *) *)
(*   pm_prettify. *)

(* Ltac solve_vals_compare_safe := *)
(*   (* The first branch is for when we have [vals_compare_safe] in the context. *)
(*      The other two branches are for when either one of the branches reduces to *)
(*      [True] or we have it in the context. *) *)
(*   fast_done || (left; fast_done) || (right; fast_done). *)

(* (** The argument [efoc] can be used to specify the construct that should be *)
(* reduced. For example, you can write [wp_pure (EIf _ _ _)], which will search *)
(* for an [EIf _ _ _] in the expression, and reduce it. *)

(* The use of [open_constr] in this tactic is essential. It will convert all holes *)
(* (i.e. [_]s) into evars, that later get unified when an occurences is found *)
(* (see [unify e' efoc] in the code below). *) *)
(* Tactic Notation "wp_pure" open_constr(efoc) := *)
(*   iStartProof; *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*       let e := eval simpl in e in *)
(*       reshape_expr e ltac:(fun K e' => *)
(*         unify e' efoc; *)
(*         eapply (tac_wp_pure_later _ _ _ _ K e'); *)
(*         [tc_solve                       (* PureExec *) *)
(*         |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *) *)
(*         |tc_solve                       (* IntoLaters *) *)
(*         |wp_finish                      (* new goal *) *)
(*         ]) *)
(*     || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex" *)
(*   | |- envs_entails _ (twp ?s ?E ?e ?Q) => *)
(*     let e := eval simpl in e in *)
(*     reshape_expr e ltac:(fun K e' => *)
(*       unify e' efoc; *)
(*       eapply (tac_wp_pure_later _ _ _ _ K e'); *)
(*       [tc_solve                       (* PureExec *) *)
(*       |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *) *)
(*       |tc_solve                       (* IntoLaters *) *)
(*       |wp_finish                      (* new goal *) *)
(*       ]) *)
(*     || fail "Hello! wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex" *)
(*   | _ => fail "wp_pure: not a 'wp'" *)
(*   end. *)

(* Tactic Notation "wp_pure" := *)
(*   wp_pure _. *)

(* Ltac wp_pures := *)
(*   iStartProof; *)
(*   first [ (* The `;[]` makes sure that no side-condition magically spawns. *) *)
(*           progress repeat (wp_pure _; []) *)
(*         | wp_finish (* In case wp_pure never ran, make sure we do the usual cleanup. *) *)
(*     ]. *)


(* (** Unlike [wp_pures], the tactics [wp_rec] and [wp_lam] should also reduce *)
(*     lambdas/recs that are hidden behind a definition, i.e. they should use *)
(*     [AsRecV_recv] as a proper instance instead of a [Hint Extern]. *)

(*     We achieve this by putting [AsRecV_recv] in the current environment so that it *)
(*     can be used as an instance by the typeclass resolution system. We then perform *)
(*     the reduction, and finally we clear this new hypothesis. *) *)
(* Tactic Notation "wp_rec" := *)
(*   let H := fresh in *)
(*   assert (H := AsRecV_recv); *)
(*   wp_pure (App _ _); *)
(*   clear H. *)

(* Tactic Notation "wp_if" := wp_pure (If _ _ _). *)
(* Tactic Notation "wp_if_true" := wp_pure (If (LitV (LitBool true)) _ _). *)
(* Tactic Notation "wp_if_false" := wp_pure (If (LitV (LitBool false)) _ _). *)
(* Tactic Notation "wp_unop" := wp_pure (UnOp _ _). *)
(* Tactic Notation "wp_binop" := wp_pure (BinOp _ _ _). *)
(* Tactic Notation "wp_op" := wp_unop || wp_binop. *)
(* Tactic Notation "wp_lam" := wp_rec. *)
(* Tactic Notation "wp_let" := wp_pure (Rec BAnon (BNamed _) _); wp_lam. *)
(* Tactic Notation "wp_seq" := wp_pure (Rec BAnon BAnon _); wp_lam. *)
(* Tactic Notation "wp_proj" := wp_pure (Fst _) || wp_pure (Snd _). *)
(* Tactic Notation "wp_case" := wp_pure (Case _ _ _). *)
(* Tactic Notation "wp_match" := wp_case; wp_pure (Rec _ _ _); wp_lam. *)
(* Tactic Notation "wp_inj" := wp_pure (InjL _) || wp_pure (InjR _). *)
(* Tactic Notation "wp_pair" := wp_pure (Pair _ _). *)
(* Tactic Notation "wp_closure" := wp_pure (Rec _ _ _). *)

(* Ltac wp_bind_core K := *)
(*   lazymatch eval hnf in K with *)
(*   | [] => idtac *)
(*   | _ => eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify] *)
(*   end. *)

(* Tactic Notation "wp_bind" open_constr(efoc) := *)
(*   iStartProof; *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*     first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K) *)
(*           | fail 1 "wp_bind: cannot find" efoc "in" e ] *)
(*   | |- envs_entails _ (twp ?s ?E ?e ?Q) => *)
(*     first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K) *)
(*           | fail 1 "wp_bind: cannot find" efoc "in" e ] *)
(*   | _ => fail "wp_bind: not a 'wp'" *)
(*   end. *)

(* (** The tactic [wp_apply_core lem tac_suc tac_fail] evaluates [lem] to a *)
(*     hypothesis [H] that can be applied, and then runs [wp_bind_core K; tac_suc H] *)
(*     for every possible evaluation context [K]. *)

(*     - The tactic [tac_suc] should do [iApplyHyp H] to actually apply the hypothesis, *)
(*       but can perform other operations in addition (see [wp_apply] and [awp_apply] *)
(*       below). *)
(*     - The tactic [tac_fail cont] is called when [tac_suc H] fails for all evaluation *)
(*       contexts [K], and can perform further operations before invoking [cont] to *)
(*       try again. *)

(*     TC resolution of [lem] premises happens *after* [tac_suc H] got executed. *) *)

(* Ltac wp_apply_core lem tac_suc tac_fail := first *)
(*   [iPoseProofCore lem as false (fun H => *)
(*      lazymatch goal with *)
(*      | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*          reshape_expr e ltac:(fun K e' => wp_bind_core K; tac_suc H) *)
(*      | |- envs_entails _ (twp ?s ?E ?e ?Q) => *)
(*          reshape_expr e ltac:(fun K e' => wp_bind_core K; tac_suc H) *)
(*      | _ => fail 1 "wp_apply: not a 'wp'" *)
(*      end) *)
(*   |tac_fail ltac:(fun _ => wp_apply_core lem tac_suc tac_fail) *)
(*   |let P := type of lem in *)
(*    fail "wp_apply: cannot apply" lem ":" P ]. *)

(* Tactic Notation "wp_apply" open_constr(lem) := *)
(*   wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl) *)
(*                     ltac:(fun cont => fail). *)
(* Tactic Notation "wp_smart_apply" open_constr(lem) := *)
(*   wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl) *)
(*                            ltac:(fun cont => wp_pure _; []; cont ()). *)

(* (** Better notations :) *) *)
(* Tactic Notation "wp_apply" open_constr(lem) "as" constr(pat) := *)
(*   wp_apply lem; last iIntros pat. *)
(* Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1) ")" *)
(*     constr(pat) := *)
(*   wp_apply lem; last iIntros ( x1 ) pat. *)
(* Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1) *)
(*     simple_intropattern(x2) ")" constr(pat) := *)
(*   wp_apply lem; last iIntros ( x1 x2 ) pat. *)
(* Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1) *)
(*     simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) := *)
(*   wp_apply lem; last iIntros ( x1 x2 x3 ) pat. *)
(* Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1) *)
(*     simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")" *)
(*     constr(pat) := *)
(*   wp_apply lem; last iIntros ( x1 x2 x3 x4 ) pat. *)
(* Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1) *)
(*     simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) *)
(*     simple_intropattern(x5) ")" constr(pat) := *)
(*   wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 ) pat. *)
(* Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1) *)
(*     simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) *)
(*     simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) := *)
(*   wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 ) pat. *)
(* Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1) *)
(*     simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) *)
(*     simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")" *)
(*     constr(pat) := *)
(*   wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 ) pat. *)
(* Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1) *)
(*     simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) *)
(*     simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) *)
(*     simple_intropattern(x8) ")" constr(pat) := *)
(*   wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat. *)
(* Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1) *)
(*     simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) *)
(*     simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) *)
(*     simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) := *)
(*   wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat. *)
(* Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1) *)
(*     simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) *)
(*     simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) *)
(*     simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")" *)
(*     constr(pat) := *)
(*   wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat. *)


(* Tactic Notation "wp_smart_apply" open_constr(lem) "as" constr(pat) := *)
(*   wp_smart_apply lem; last iIntros pat. *)
(* Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1) ")" *)
(*     constr(pat) := *)
(*   wp_smart_apply lem; last iIntros ( x1 ) pat. *)
(* Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1) *)
(*     simple_intropattern(x2) ")" constr(pat) := *)
(*   wp_smart_apply lem; last iIntros ( x1 x2 ) pat. *)
(* Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1) *)
(*     simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) := *)
(*   wp_smart_apply lem; last iIntros ( x1 x2 x3 ) pat. *)
(* Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1) *)
(*     simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")" *)
(*     constr(pat) := *)
(*   wp_smart_apply lem; last iIntros ( x1 x2 x3 x4 ) pat. *)
(* Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1) *)
(*     simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) *)
(*     simple_intropattern(x5) ")" constr(pat) := *)
(*   wp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 ) pat. *)
(* Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1) *)
(*     simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) *)
(*     simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) := *)
(*   wp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 ) pat. *)
(* Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1) *)
(*     simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) *)
(*     simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")" *)
(*     constr(pat) := *)
(*   wp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 ) pat. *)
(* Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1) *)
(*     simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) *)
(*     simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) *)
(*     simple_intropattern(x8) ")" constr(pat) := *)
(*   wp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat. *)
(* Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1) *)
(*     simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) *)
(*     simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) *)
(*     simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) := *)
(*   wp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat. *)
(* Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1) *)
(*     simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) *)
(*     simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) *)
(*     simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")" *)
(*     constr(pat) := *)
(*   wp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat. *)


(* Tactic Notation "awp_apply" open_constr(lem) := *)
(*   (* [pm_prettify] is needed to clean up telescopes. *) *)
(*   wp_apply_core lem ltac:(fun H => iApplyHyp H; pm_prettify) ltac:(fun cont => fail); *)
(*   last iAuIntro. *)
(* Tactic Notation "awp_apply" open_constr(lem) "without" constr(Hs) := *)
(*   (* Convert "list of hypothesis" into specialization pattern. *) *)
(*   let Hs := words Hs in *)
(*   let Hs := eval vm_compute in (INamed <$> Hs) in *)
(*     wp_apply_core lem *)
(*       ltac:(fun H => *)
(*               iApply (wptac_wp_frame_wand with *)
(*                   [SGoal $ SpecGoal GSpatial false [] Hs false]); *)
(*               [iAccu|iApplyHyp H; pm_prettify]) *)
(*              ltac:(fun cont => fail); *)
(*                                last iAuIntro. *)
  

(* Section heap_tactics. *)
(*   Context `{GwpTacticsBase Σ A hlc gwp, GwpTacticsBind Σ A hlc gwp, !GwpTacticsHeap Σ A laters gwp}. *)

(*   Local Notation "'WP' e @ s ; E {{ Φ } }" := (gwp s E e%E Φ) *)
(*     (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)

(*   (** Notations with binder. *) *)
(*   Local Notation "'WP' e @ s ; E {{ v , Q } }" := (gwp s E e%E (λ v, Q)) *)
(*     (at level 20, e, Q at level 200, *)
(*      format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope. *)

(*   Lemma tac_wp_alloc Δ Δ' E j K v Φ a : *)
(*     MaybeIntoLaterNEnvs (if laters then 1 else 0) Δ Δ' → *)
(*     (∀ (l : loc), *)
(*         match envs_app false (Esnoc Enil j (wptac_mapsto l (DfracOwn 1) v)) Δ' with *)
(*         | Some Δ'' => *)
(*             envs_entails Δ'' (WP fill K (Val $ LitV $ LitLoc l) @ a ; E {{ Φ }}) *)
(*         | None => False *)
(*         end) → *)
(*     envs_entails Δ (WP fill K (Alloc (Val v)) @ a; E {{ Φ }}). *)
(*   Proof. *)
(*     rewrite envs_entails_unseal=> ? HΔ. *)
(*     rewrite -wptac_wp_bind. *)
(*     eapply bi.wand_apply. *)
(*     { apply bi.wand_entails, wptac_wp_alloc. } *)
(*     rewrite left_id into_laterN_env_sound. *)
(*     apply bi.laterN_mono, bi.forall_intro=> l. *)
(*     specialize (HΔ l). *)
(*     destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [| contradiction]. *)
(*     rewrite envs_app_sound //; simpl. *)
(*     apply bi.wand_intro_l. *)
(*     rewrite right_id. *)
(*     rewrite bi.wand_elim_r //. *)
(*   Qed. *)

(*   Lemma tac_wp_allocN Δ Δ' E j K v n Φ a : *)
(*     (0 < n)%Z → *)
(*     MaybeIntoLaterNEnvs (if laters then 1 else 0) Δ Δ' → *)
(*     (∀ l, *)
(*         match envs_app false (Esnoc Enil j (wptac_mapsto_array l (DfracOwn 1) (replicate (Z.to_nat n) v))) Δ' with *)
(*         | Some Δ'' => *)
(*             envs_entails Δ'' (WP fill K (Val $ LitV $ LitLoc l) @ a; E {{ Φ }}) *)
(*         | None => False *)
(*         end) → *)
(*     envs_entails Δ (WP fill K (AllocN (Val $ LitV $ LitInt n) (Val v)) @ a; E {{ Φ }}). *)
(*   Proof. *)
(*     rewrite envs_entails_unseal=> ? ? HΔ. *)
(*     rewrite -wptac_wp_bind. *)
(*     eapply bi.wand_apply. *)
(*     { by apply bi.wand_entails, wptac_wp_allocN. } *)
(*     rewrite left_id into_laterN_env_sound. *)
(*     apply bi.laterN_mono, bi.forall_intro=> l. *)
(*     specialize (HΔ l). *)
(*     destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [ | contradiction ]. *)
(*     rewrite envs_app_sound //; simpl. *)
(*     apply bi.wand_intro_l. *)
(*     rewrite right_id. *)
(*     rewrite bi.wand_elim_r //. *)
(*   Qed. *)

(*   Lemma tac_wp_load Δ Δ' E i K b l dq v Φ a : *)
(*     MaybeIntoLaterNEnvs (if laters then 1 else 0) Δ Δ' → *)
(*     envs_lookup i Δ' = Some (b, wptac_mapsto l dq v) → *)
(*     envs_entails Δ' (WP fill K (Val v) @ a; E {{ Φ }}) → *)
(*     envs_entails Δ (WP fill K (Load (Val $ LitV $ LitLoc l)) @ a; E {{ Φ }}). *)
(*   Proof. *)
(*     rewrite envs_entails_unseal=> ?? Hi. *)
(*     rewrite -wptac_wp_bind. *)
(*     eapply bi.wand_apply. *)
(*     { apply bi.wand_entails, wptac_wp_load. } *)
(*     rewrite into_laterN_env_sound. *)
(*     destruct laters. *)
(*     - rewrite -bi.later_sep. *)
(*       rewrite envs_lookup_split //; simpl. *)
(*       apply bi.later_mono. *)
(*       destruct b; simpl. *)
(*       * iIntros "[#$ He]". iIntros "_". iApply Hi. iApply "He". iFrame "#". *)
(*       * by apply bi.sep_mono_r, bi.wand_mono. *)
(*     - rewrite envs_lookup_split //; simpl. *)
(*       destruct b; simpl. *)
(*       * iIntros "[#$ He]". iIntros "_". iApply Hi. iApply "He". iFrame "#". *)
(*       * iIntros "[$ He] H". iApply Hi. by iApply "He". *)
(*   Qed. *)

(*   Lemma tac_wp_store Δ Δ' E i K l v v' Φ a : *)
(*     MaybeIntoLaterNEnvs (if laters then 1 else 0) Δ Δ' → *)
(*     envs_lookup i Δ' = Some (false, wptac_mapsto l (DfracOwn 1) v)%I → *)
(*     match envs_simple_replace i false (Esnoc Enil i (wptac_mapsto l (DfracOwn 1) v')) Δ' with *)
(*     | Some Δ'' => envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ a; E {{ Φ }}) *)
(*     | None => False *)
(*     end → *)
(*     envs_entails Δ (WP fill K (Store (Val $ LitV $ LitLoc l) (Val v')) @ a; E {{ Φ }}). *)
(*   Proof. *)
(*     rewrite envs_entails_unseal=> ?? Hcnt. *)
(*     destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ]. *)
(*     rewrite -wptac_wp_bind. eapply bi.wand_apply. *)
(*     { eapply bi.wand_entails, wptac_wp_store. } *)
(*     rewrite into_laterN_env_sound. *)
(*     destruct laters. *)
(*     - rewrite -bi.later_sep envs_simple_replace_sound //; simpl. *)
(*       rewrite right_id. by apply bi.later_mono, bi.sep_mono_r, bi.wand_mono. *)
(*     - rewrite envs_simple_replace_sound //; simpl. *)
(*       rewrite right_id. *)
(*       iIntros "[$ He] H". iApply Hcnt. by iApply "He". *)
(*   Qed. *)

(* End heap_tactics. *)

(* Tactic Notation "wp_alloc" ident(l) "as" constr(H) := *)
(*   let Htmp := iFresh in *)
(*   let finish _ := *)
(*     first [intros l | fail 1 "wp_alloc:" l "not fresh"]; *)
(*     pm_reduce; *)
(*     lazymatch goal with *)
(*     | |- False => fail 1 "wp_alloc:" H "not fresh" *)
(*     | _ => iDestructHyp Htmp as H; wp_finish *)
(*     end in *)
(*   wp_pures; *)
(*   (** The code first tries to use allocation lemma for a single reference, *)
(*      ie, [tac_wp_alloc] (respectively, [tac_twp_alloc]). *)
(*      If that fails, it tries to use the lemma [tac_wp_allocN] *)
(*      (respectively, [tac_twp_allocN]) for allocating an array. *)
(*      Notice that we could have used the array allocation lemma also for single *)
(*      references. However, that would produce the resource l ↦∗ [v] instead of *)
(*      l ↦ v for single references. These are logically equivalent assertions *)
(*      but are not equal. *) *)
(* lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*     let process_single _ := *)
(*         first *)
(*           [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloc _ _ _ Htmp K)) *)
(*           |fail 1 "wp_alloc: cannot find 'Alloc' in" e]; *)
(*         [tc_solve *)
(*         |finish ()] *)
(*     in *)
(*     let process_array _ := *)
(*         first *)
(*           [reshape_expr e ltac:(fun K e' => eapply (tac_wp_allocN _ _ _ Htmp K)) *)
(*           |fail 1 "wp_alloc: cannot find 'Alloc' in" e]; *)
(*         [idtac| tc_solve *)
(*          |finish ()] *)
(*     in (process_single ()) || (process_array ()) *)
(* | |- envs_entails _ (twp ?s ?E ?e ?Q) => *)
(*     let process_single _ := *)
(*         first *)
(*           [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloc _ _ _ Htmp K)) *)
(*           |fail 1 "wp_alloc: cannot find 'Alloc' in" e]; *)
(*         [tc_solve *)
(*         |finish ()] *)
(*     in *)
(*     let process_array _ := *)
(*         first *)
(*           [reshape_expr e ltac:(fun K e' => eapply (tac_wp_allocN _ _ _ Htmp K)) *)
(*           |fail 1 "wp_alloc: cannot find 'Alloc' in" e]; *)
(*         [idtac| tc_solve *)
(*          |finish ()] *)
(*     in (process_single ()) || (process_array ()) *)
(*   | _ => fail "wp_alloc: not a 'wp'" *)
(*   end. *)


(* Tactic Notation "wp_alloc" ident(l) := *)
(*   wp_alloc l as "?". *)

(* Tactic Notation "wp_load" := *)
(*   let solve_wptac_mapsto _ := *)
(*     let l := match goal with |- _ = Some (_, (wptac_mapsto ?l _ _)%I) => l end in *)
(*     iAssumptionCore || fail "wp_load: cannot find" l "↦ ?" in *)
(*   wp_pures; *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*     first *)
(*       [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load _ _ _ _ K)) *)
(*       |fail 1 "wp_load: cannot find 'Load' in" e]; *)
(*     [tc_solve *)
(*     |solve_wptac_mapsto () *)
(*     |wp_finish] *)
(*   | |- envs_entails _ (twp ?s ?E ?e ?Q) => *)
(*     first *)
(*       [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load _ _ _ _ K)) *)
(*       |fail 1 "wp_load: cannot find 'Load' in" e]; *)
(*     [tc_solve *)
(*     |solve_wptac_mapsto () *)
(*     |wp_finish] *)
(*   | _ => fail "wp_load: not a 'wp'" *)
(*   end. *)

(* Tactic Notation "wp_store" := *)
(*   let solve_wptac_mapsto _ := *)
(*     let l := match goal with |- _ = Some (_, (wptac_mapsto ?l _ _)%I) => l end in *)
(*     iAssumptionCore || fail "wp_store: cannot find" l "↦ ?" in *)
(*   wp_pures; *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*     first *)
(*       [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store _ _ _ _ K)) *)
(*       |fail 1 "wp_store: cannot find 'Store' in" e]; *)
(*     [tc_solve *)
(*     |solve_wptac_mapsto () *)
(*     |pm_reduce; first [wp_seq|wp_finish]] *)
(*   | |- envs_entails _ (twp ?s ?E ?e ?Q) => *)
(*     first *)
(*       [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store _ _ _ _ K)) *)
(*       |fail 1 "wp_store: cannot find 'Store' in" e]; *)
(*     [tc_solve *)
(*     |solve_wptac_mapsto () *)
(*     |pm_reduce; first [wp_seq|wp_finish]] *)
(*   | _ => fail "wp_store: not a 'wp'" *)
(*   end. *)


(* Section tape_tactics. *)
(*   Context `{GwpTacticsBase Σ A hlc gwp, GwpTacticsBind Σ A hlc gwp, !GwpTacticsTapes Σ A laters gwp}. *)

(*   Local Notation "'WP' e @ s ; E {{ Φ } }" := (gwp s E e%E Φ) *)
(*     (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)

(*   (** Notations with binder. *) *)
(*   Local Notation "'WP' e @ s ; E {{ v , Q } }" := (gwp s E e%E (λ v, Q)) *)
(*     (at level 20, e, Q at level 200, *)
(*      format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope. *)

(*   Lemma tac_wp_alloctape Δ Δ' E j K N z Φ a : *)
(*     TCEq N (Z.to_nat z) -> *)
(*     MaybeIntoLaterNEnvs (if laters then 1 else 0) Δ Δ' → *)
(*     (∀ l, *)
(*         match envs_app false (Esnoc Enil j (wptac_mapsto_tape l (DfracOwn 1) N nil)) Δ' with *)
(*         | Some Δ'' => *)
(*             envs_entails Δ'' (WP fill K (Val $ LitV $ LitLbl l) @ a ; E {{ Φ }}) *)
(*         | None => False *)
(*         end) → *)
(*     envs_entails Δ (WP fill K (AllocTape (Val $ LitV $ LitInt z)) @ a; E {{ Φ }}). *)
(*   Proof. *)
(*     rewrite envs_entails_unseal=> ? ? HΔ. *)
(*     rewrite -wptac_wp_bind. *)
(*     eapply bi.wand_apply. *)
(*     { by apply bi.wand_entails, wptac_wp_alloctape. } *)
(*     rewrite left_id into_laterN_env_sound. *)
(*     apply bi.laterN_mono, bi.forall_intro=> l. *)
(*     specialize (HΔ l). *)
(*     destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [| contradiction]. *)
(*     rewrite envs_app_sound //; simpl. *)
(*     apply bi.wand_intro_l. *)
(*     rewrite right_id. *)
(*     rewrite bi.wand_elim_r //. *)
(*   Qed. *)


(*   Lemma tac_wp_rand_tape Δ1 Δ2 E i j K l N z n ns Φ a : *)
(*     TCEq N (Z.to_nat z) -> *)
(*     MaybeIntoLaterNEnvs (if laters then 1 else 0) Δ1 Δ2 → *)
(*     envs_lookup i Δ2 = Some (false, wptac_mapsto_tape l (DfracOwn 1) N (n::ns)) -> *)
(*     (match envs_simple_replace i false (Esnoc Enil i (wptac_mapsto_tape l (DfracOwn 1) N ns)) Δ2 with *)
(*     | Some Δ3 => *)
(*         (match envs_app false (Esnoc Enil j (⌜n ≤ N⌝%I)) Δ3 with *)
(*         | Some Δ4 => envs_entails Δ4 (WP fill K (Val $ LitV $ LitInt n) @ a; E {{ Φ }}) *)
(*         | None    => False *)
(*         end) *)
(*     | None    => False *)
(*     end) → *)
(*     envs_entails Δ1 (gwp a E (fill K (Rand (LitV (LitInt z)) (LitV (LitLbl l)))) Φ ). *)
(*   Proof. *)
(*     rewrite envs_entails_unseal=> ?? Hi HΔ. *)
(*     destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done. *)
(*     rewrite -wptac_wp_bind. *)
(*     eapply bi.wand_apply. *)
(*     { by apply bi.wand_entails, wptac_wp_rand_tape. } *)
(*     rewrite into_laterN_env_sound. *)
(*     destruct laters. *)
(*     - rewrite -bi.later_sep. *)
(*       apply bi.later_mono. *)
(*       rewrite (envs_simple_replace_sound Δ2 Δ3 i) /= //; simpl. *)
(*       iIntros "[$ He]". *)
(*       iIntros "Htp ?". *)
(*       destruct (envs_app _ _ _) as [Δ4 |] eqn: HΔ4; [|contradiction]. *)
(*       rewrite envs_app_sound //; simpl. *)
(*       iApply HΔ. *)
(*       iApply ("He" with "[$Htp]"). *)
(*       iFrame. *)
(*     - simpl. *)
(*       rewrite (envs_simple_replace_sound Δ2 Δ3 i) /= //; simpl. *)
(*       iIntros "[$ He]". *)
(*       iIntros "Htp ?". *)
(*       destruct (envs_app _ _ _) as [Δ4 |] eqn: HΔ4; [|contradiction]. *)
(*       rewrite envs_app_sound //; simpl. *)
(*       iApply HΔ. *)
(*       iApply ("He" with "[$Htp]"). *)
(*       iFrame. *)
(*   Qed. *)

(* End tape_tactics. *)


(* Tactic Notation "wp_alloctape" ident(l) "as" constr(H) := *)
(*   let Htmp := iFresh in *)
(*   let finish _ := *)
(*     first [intros l | fail 1 "wp_alloctape:" l "not fresh"]; *)
(*     pm_reduce; *)
(*     lazymatch goal with *)
(*     | |- False => fail 1 "wp_alloc:" H "not fresh" *)
(*     | _ => iDestructHyp Htmp as H; wp_finish *)
(*     end in *)
(*   wp_pures; *)
(* lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*         first *)
(*           [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloctape _ _ _ Htmp K)) *)
(*           |fail 1 "wp_alloc: cannot find 'AllocTape' in" e]; *)
(*         [tc_solve | tc_solve *)
(*         |finish ()] *)
(* | |- envs_entails _ (twp ?s ?E ?e ?Q) => *)
(*         first *)
(*           [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloctape _ _ _ Htmp K)) *)
(*           |fail 1 "wp_alloc: cannot find 'AllocTape' in" e]; *)
(*         [tc_solve | tc_solve *)
(*         |finish ()] *)
(*   | _ => fail "wp_alloc: not a 'wp'" *)
(*   end. *)


(* Tactic Notation "wp_alloctape" ident(l) := *)
(*   wp_alloctape l as "?". *)

(* Tactic Notation "wp_randtape" "as" constr(H) := *)
(*   let Htmp := iFresh in *)
(*   let solve_wptac_mapsto_tape _ := *)
(*     let l := match goal with |- _ = Some (_, (wptac_mapsto_tape ?l _ _ (_ :: _))%I) => l end in *)
(*     iAssumptionCore || fail "wp_load: cannot find" l "↪N ?" in *)
(*   let finish _ := *)
(*     pm_reduce; *)
(*     lazymatch goal with *)
(*     | |- False => fail 1 "wp_alloc:" H "not fresh" *)
(*     | _ => iDestructHyp Htmp as H; wp_finish *)
(*     end in *)
(*   wp_pures; *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*       first *)
(*         [reshape_expr e ltac:(fun K e' => eapply (tac_wp_rand_tape _ _ _ _ Htmp K)) *)
(*         |fail 1 "wp_load: cannot find 'Rand' in" e]; *)
(*       [ (* Delay resolution of TCEq *) *)
(*       | tc_solve *)
(*       | solve_wptac_mapsto_tape () *)
(*       |]; *)
(*       [try tc_solve | finish ()] *)
(*   | |- envs_entails _ (twp ?s ?E ?e ?Q) => *)
(*       first *)
(*         [reshape_expr e ltac:(fun K e' => eapply (tac_wp_rand_tape _ _ _ _ Htmp K)) *)
(*         |fail 1 "wp_load: cannot find 'Rand' in" e]; *)
(*       [try tc_solve *)
(*       |tc_solve *)
(*       |try (solve_wptac_mapsto_tape ()) *)
(*       |finish ()] *)
(*   | _ => fail "wp_load: not a 'wp'" *)
(*   end. *)

(* Tactic Notation "wp_randtape" := *)
(*   wp_randtape as "%". *)


(* Section concurrency_tactics. *)
(*   Context `{GwpTacticsBase Σ A hlc gwp, GwpTacticsBind Σ A hlc gwp, *)
(*               !GwpTacticsAtomicConcurrency Σ A laters gwp}. *)

(*   Local Notation "'WP' e @ s ; E {{ Φ } }" := (gwp s E e%E Φ) *)
(*     (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)

(*   (** Notations with binder. *) *)
(*   Local Notation "'WP' e @ s ; E {{ v , Q } }" := (gwp s E e%E (λ v, Q)) *)
(*     (at level 20, e, Q at level 200, *)
(*        format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope. *)

(*   Lemma tac_wp_cmpxchg Δ Δ' s E i K l v v1 v2 Φ : *)
(*     MaybeIntoLaterNEnvs (if laters then 1 else 0) Δ Δ' → *)
(*     envs_lookup i Δ' = Some (false, wptac_mapsto_conc l (DfracOwn 1) v)%I → *)
(*     vals_compare_safe v v1 → *)
(*     match envs_simple_replace i false (Esnoc Enil i (wptac_mapsto_conc l (DfracOwn 1) v2)) Δ' with *)
(*     | Some Δ'' => *)
(*         v = v1 → *)
(*         envs_entails Δ'' (WP fill K (Val $ PairV v (LitV $ LitBool true)) @ s; E {{ Φ }}) *)
(*     | None => False *)
(*     end → *)
(*     (v ≠ v1 → *)
(*      envs_entails Δ' (WP fill K (Val $ PairV v (LitV $ LitBool false)) @ s; E {{ Φ }})) → *)
(*     envs_entails Δ (WP fill K (CmpXchg (LitV l) (Val v1) (Val v2)) @ s; E {{ Φ }}). *)
(*   Proof. *)
(*     rewrite envs_entails_unseal=> ??? Hsuc Hfail. *)
(*     destruct (envs_simple_replace _ _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ]. *)
(*     destruct (decide (v = v1)) as [Heq|Hne]. *)
(*     - rewrite -wptac_wp_bind. eapply bi.wand_apply. *)
(*       { eapply bi.wand_entails, wptac_wp_cmpxchg_suc; eauto. } *)
(*       rewrite into_laterN_env_sound /= {1}envs_simple_replace_sound //; simpl. *)
(*       destruct laters. *)
(*       + rewrite -bi.later_sep. *)
(*         apply bi.later_mono, bi.sep_mono_r. rewrite right_id. apply bi.wand_mono; auto. *)
(*       + simpl. apply bi.sep_mono; eauto. *)
(*         apply bi.wand_mono; eauto.  *)
(*     - rewrite -wptac_wp_bind. eapply bi.wand_apply. *)
(*       { eapply bi.wand_entails, wptac_wp_cmpxchg_fail; eauto. } *)
(*       rewrite into_laterN_env_sound /= envs_lookup_split//; simpl. *)
(*       destruct laters. *)
(*       + rewrite -bi.later_sep. *)
(*         apply bi.later_mono, bi.sep_mono_r. apply bi.wand_mono; auto. *)
(*       + simpl. apply bi.sep_mono; eauto. *)
(*         apply bi.wand_mono; eauto. *)
(*   Qed. *)

(*   Lemma tac_wp_cmpxchg_fail Δ Δ' s E i K b l v v1 (v2:val) Φ : *)
(*     MaybeIntoLaterNEnvs (if laters then 1 else 0) Δ Δ' → *)
(*     envs_lookup i Δ' = Some (b, wptac_mapsto_conc l (DfracOwn 1) v)%I → *)
(*     v ≠ v1 → vals_compare_safe v v1 → *)
(*     envs_entails Δ' (WP fill K (Val $ PairV v (LitV $ LitBool false)) @ s; E {{ Φ }}) → *)
(*     envs_entails Δ (WP fill K (CmpXchg (LitV l) v1 v2) @ s; E {{ Φ }}). *)
(*   Proof. *)
(*     rewrite envs_entails_unseal=> ???? Hi. *)
(*     rewrite -wptac_wp_bind. eapply bi.wand_apply; first eapply bi.wand_entails, wptac_wp_cmpxchg_fail; eauto. *)
(*     erewrite into_laterN_env_sound, envs_lookup_split; simpl; eauto. *)
(*     destruct laters. *)
(*     - rewrite -bi.later_sep. simpl. iApply bi.later_mono. simpl. *)
(*       destruct b; simpl. *)
(*       + iIntros "[#$ He]". iIntros "_". iApply Hi. iApply "He". iFrame "#". *)
(*       + iIntros "[$ He]". iIntros "Hl". iApply Hi. iApply "He". iFrame "Hl". *)
(*     - simpl. destruct b; simpl. *)
(*       + iIntros "[#$ He]". iIntros "_". iApply Hi. iApply "He". iFrame "#". *)
(*       + iIntros "[$ He]". iIntros "Hl". iApply Hi. iApply "He". iFrame "Hl". *)
(*   Qed. *)

(*   Lemma tac_wp_cmpxchg_suc Δ Δ' s E i K l v v1 v2 Φ : *)
(*     MaybeIntoLaterNEnvs (if laters then 1 else 0) Δ Δ' → *)
(*     envs_lookup i Δ' = Some (false, wptac_mapsto_conc l (DfracOwn 1) v)%I → *)
(*     v = v1 → vals_compare_safe v v1 → *)
(*     match envs_simple_replace i false (Esnoc Enil i (wptac_mapsto_conc l (DfracOwn 1) v2)) Δ' with *)
(*     | Some Δ'' => *)
(*         envs_entails Δ'' (WP fill K (Val $ PairV v (LitV $ LitBool true)) @ s; E {{ Φ }}) *)
(*     | None => False *)
(*     end → *)
(*     envs_entails Δ (WP fill K (CmpXchg (LitV l) v1 v2) @ s; E {{ Φ }}). *)
(*   Proof. *)
(*     intros. eapply tac_wp_cmpxchg; eauto; last naive_solver. *)
(*     case_match; naive_solver. *)
(*   Qed. *)


(*   Lemma tac_wp_xchg Δ Δ' s E i K l v v' Φ : *)
(*     MaybeIntoLaterNEnvs (if laters then 1 else 0) Δ Δ' → *)
(*     envs_lookup i Δ' = Some (false, wptac_mapsto_conc l (DfracOwn 1) v)%I → *)
(*     match envs_simple_replace i false (Esnoc Enil i (wptac_mapsto_conc l (DfracOwn 1) v')) Δ' with *)
(*     | Some Δ'' => envs_entails Δ'' (WP fill K (Val $ v) @ s; E {{ Φ }}) *)
(*     | None => False *)
(*     end → *)
(*     envs_entails Δ (WP fill K (Xchg (LitV l) (Val v')) @ s; E {{ Φ }}). *)
(*   Proof. *)
(*     rewrite envs_entails_unseal=> ???. *)
(*     destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ]. *)
(*     rewrite -wptac_wp_bind. eapply bi.wand_apply; first by eapply bi.wand_entails, wptac_wp_xchg. *)
(*     destruct laters. *)
(*     - rewrite into_laterN_env_sound -bi.later_sep envs_simple_replace_sound //; simpl. *)
(*       rewrite right_id. *)
(*       by apply bi.later_mono, bi.sep_mono_r, bi.wand_mono. *)
(*     - rewrite into_laterN_env_sound envs_simple_replace_sound //; simpl. *)
(*       rewrite right_id. *)
(*       apply bi.sep_mono, bi.wand_mono; eauto. *)
(*   Qed. *)

(*   Lemma tac_wp_faa Δ Δ' s E i K l z1 z2 Φ : *)
(*     MaybeIntoLaterNEnvs (if laters then 1 else 0) Δ Δ' → *)
(*     envs_lookup i Δ' = Some (false, wptac_mapsto_conc l (DfracOwn 1) (LitV (LitInt z1)))%I → *)
(*     match envs_simple_replace i false (Esnoc Enil i (wptac_mapsto_conc l (DfracOwn 1) (LitV (LitInt (z1+z2))))) Δ' with *)
(*     | Some Δ'' => envs_entails Δ'' (WP fill K (Val $ LitV z1) @ s; E {{ Φ }}) *)
(*     | None => False *)
(*     end → *)
(*     envs_entails Δ (WP fill K (FAA (LitV l) (LitV z2)) @ s; E {{ Φ }}). *)
(*   Proof. *)
(*     rewrite envs_entails_unseal=> ???. *)
(*     destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ]. *)
(*     rewrite -wptac_wp_bind. eapply bi.wand_apply; first by eapply bi.wand_entails, (wptac_wp_faa _ _ _ z1 z2). *)
(*     destruct laters. *)
(*     - rewrite into_laterN_env_sound -bi.later_sep envs_simple_replace_sound //; simpl. *)
(*       rewrite right_id. by apply bi.later_mono, bi.sep_mono_r, bi.wand_mono. *)
(*     - rewrite into_laterN_env_sound envs_simple_replace_sound //; simpl. *)
(*       rewrite right_id. eapply bi.sep_mono, bi.wand_mono; eauto. *)
(*   Qed. *)


(* End concurrency_tactics. *)

(* Tactic Notation "wp_cmpxchg" "as" simple_intropattern(H1) "|" simple_intropattern(H2) := *)
(*   let solve_pointsto _ := *)
(*     let l := match goal with |- _ = Some (_, (wptac_mapsto_conc ?l _ _)%I) => l end in *)
(*     iAssumptionCore || fail "wp_cmpxchg: cannot find" l "↦ ?" in *)
(*   wp_pures; *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*     first *)
(*       [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cmpxchg _ _ _ _ _ K)) *)
(*       |fail 1 "wp_cmpxchg: cannot find 'CmpXchg' in" e]; *)
(*     [tc_solve *)
(*     |solve_pointsto () *)
(*     |try solve_vals_compare_safe *)
(*     |pm_reduce; intros H1; wp_finish *)
(*     |intros H2; wp_finish] *)
(*   | _ => fail "wp_cmpxchg: not a 'wp'" *)
(*   end. *)

(* Tactic Notation "wp_cmpxchg_fail" := *)
(*   let solve_pointsto _ := *)
(*     let l := match goal with |- _ = Some (_, (wptac_mapsto_conc ?l _ _)%I) => l end in *)
(*     iAssumptionCore || fail "wp_cmpxchg_fail: cannot find" l "↦ ?" in *)
(*   wp_pures; *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*     first *)
(*       [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cmpxchg_fail _ _ _ _ _ K)) *)
(*       |fail 1 "wp_cmpxchg_fail: cannot find 'CmpXchg' in" e]; *)
(*     [tc_solve *)
(*     |solve_pointsto () *)
(*     |try (simpl; congruence) (* value inequality *) *)
(*     |try solve_vals_compare_safe *)
(*     |wp_finish] *)
(*   | _ => fail "wp_cmpxchg_fail: not a 'wp'" *)
(*   end. *)

(* Tactic Notation "wp_cmpxchg_suc" := *)
(*   let solve_pointsto _ := *)
(*     let l := match goal with |- _ = Some (_, (wptac_mapsto_conc ?l _ _)%I) => l end in *)
(*     iAssumptionCore || fail "wp_cmpxchg_suc: cannot find" l "↦ ?" in *)
(*   wp_pures; *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*     first *)
(*       [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cmpxchg_suc _ _ _ _ _ K)) *)
(*       |fail 1 "wp_cmpxchg_suc: cannot find 'CmpXchg' in" e]; *)
(*     [tc_solve *)
(*     |solve_pointsto () *)
(*     |try (simpl; congruence) (* value equality *) *)
(*     |try solve_vals_compare_safe *)
(*     |pm_reduce; wp_finish] *)
(*   | _ => fail "wp_cmpxchg_suc: not a 'wp'" *)
(*   end. *)


(* Tactic Notation "wp_xchg" := *)
(*   let solve_pointsto _ := *)
(*     let l := match goal with |- _ = Some (_, (wptac_mapsto_conc ?l _ _)%I) => l end in *)
(*     iAssumptionCore || fail "wp_xchg: cannot find" l "↦ ?" in *)
(*   wp_pures; *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*     first *)
(*       [reshape_expr e ltac:(fun K e' => eapply (tac_wp_xchg _ _ _ _ _ K)) *)
(*       |fail 1 "wp_xchg: cannot find 'Xchg' in" e]; *)
(*     [tc_solve *)
(*     |solve_pointsto () *)
(*     |pm_reduce; first [wp_seq|wp_finish]] *)
(*   | _ => fail "wp_xchg: not a 'wp'" *)
(*   end. *)


(* Tactic Notation "wp_faa" := *)
(*   let solve_pointsto _ := *)
(*     let l := match goal with |- _ = Some (_, (wptac_mapsto_conc ?l _ _)%I) => l end in *)
(*     iAssumptionCore || fail "wp_faa: cannot find" l "↦ ?" in *)
(*   wp_pures; *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*     first *)
(*       [reshape_expr e ltac:(fun K e' => eapply (tac_wp_faa _ _ _ _ _ K)) *)
(*       |fail 1 "wp_faa: cannot find 'FAA' in" e]; *)
(*     [tc_solve *)
(*     |solve_pointsto () *)
(*     |pm_reduce; wp_finish] *)
(*   | _ => fail "wp_faa: not a 'wp'" *)
(*   end. *)
