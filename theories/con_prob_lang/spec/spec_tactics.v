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


(** Tapes *)
Class UpdTapes `{specG_con_prob_lang Σ} (upd : coPset -> coPset -> iProp Σ -> iProp Σ):= {

  tptac_upd_alloctape j K E (N : nat) (z : Z) :
    TCEq N (Z.to_nat z) ->
    True -∗
    j ⤇ fill K (AllocTape (Val $ LitV $ LitInt $ z)) -∗
    upd E E (∃ l, l ↪ₛN (N; []) ∗ j ⤇ fill K (LitV (LitLbl l))) ;

    tptac_upd_rand_tape j K E N (n : nat) (z : Z) ns l :
    TCEq N (Z.to_nat z) ->
    (l ↪ₛN (N; (n::ns))) -∗
    j ⤇ fill K (Rand (LitV (LitInt z)) (LitV (LitLbl l))) -∗
    upd E E ((l ↪ₛN (N; (ns))) ∗ ⌜ n ≤ N ⌝ ∗ j ⤇ fill K (LitV $ LitInt $ n)%V)
  }.

Lemma tac_tp_allocnattape `{!specG_con_prob_lang Σ, !UpdTapes upd} j K Δ1 E1 i1 e N z Q :
  (∀ P, ElimModal True false false (upd E1 E1 P) P Q Q) →
  TCEq N (Z.to_nat z) →
  envs_lookup i1 Δ1 = Some (false, j ⤇ e)%I →
  e = fill K (alloc #z) →
  (∀ α : loc, ∃ Δ2,
    envs_simple_replace i1 false
       (Esnoc Enil i1 (j ⤇ fill K #lbl:α)) Δ1 = Some Δ2 ∧
    (envs_entails Δ2 ((α ↪ₛN (N; [])) -∗ Q)%I)) →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? Hfill HQ.
  rewrite (envs_lookup_sound' Δ1 false i1); last by eassumption.
  rewrite Hfill /=.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono, bi.wand_intro_l; simpl; first by iApply tptac_upd_alloctape.
  rewrite bi.sep_exist_r.
  apply bi.exist_elim=> l.
  destruct (HQ l) as (Δ2 & HΔ2 & HQ').
  rewrite (envs_simple_replace_sound' _ _ i1 _ _ HΔ2) /=.
  rewrite HQ' right_id.
  iIntros "[[H Hl] Hcnt]".
  iApply ("Hcnt" with "Hl H").
Qed.

Tactic Notation "tp_allocnattape" constr(j) ident(l) "as"  constr(H) :=
  let finish _ :=
    first [intros l | fail 1 "tp_allocnattape:" l "not fresh"];
    eexists; split;
    [ reduction.pm_reflexivity
    | (iIntros H; tp_normalise j) || fail 1 "tp_alloctape:" H "not correct intro pattern" ] in
  iStartProof;
  eapply (tac_tp_allocnattape j);
  [tc_solve || fail "tp_allocnattape: cannot eliminate modality in the goal"
  | (* postpone solving [TCEq ...] *)
  |iAssumptionCore || fail "tp_allocnattape: cannot find the RHS"
  |tp_bind_helper
  | ];
  [tc_solve || fail "tp_rand: cannot convert bound to a natural number"
  | finish () ].

Tactic Notation "tp_allocnattape" constr(j) ident(j') :=
  let H := iFresh in tp_allocnattape j j' as H.


Lemma tac_tp_randnat `{specG_con_prob_lang Σ, !UpdTapes upd} j K Δ1 Δ2 E1 i1 i2 e e2 (l : loc) N z n ns Q :
  (∀ P, ElimModal True false false (upd E1 E1 P) P Q Q) →
  TCEq N (Z.to_nat z) →
  envs_lookup_delete false i1 Δ1 = Some (false, j ⤇ e, Δ2)%I →
  e = fill K (rand(#lbl:l) #z) →
  envs_lookup i2 Δ2 = Some (false, l ↪ₛN (N; n::ns))%I →
  e2 = fill K (of_val #n) →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (j ⤇ e2)) i2 (l ↪ₛN (N; ns))%I) Δ2 with
  | Some Δ3 => envs_entails Δ3 ((⌜n ≤ N⌝ -∗ Q)%I)
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
  (* rewrite step_randnat //=. *)
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono.
  - iIntros "[??]"; simpl.
    iApply (tptac_upd_rand_tape with "[$][$]").
  - apply bi.wand_intro_l. simpl.
    rewrite HQ//.
    iIntros "[(?&?&?) H]".
    iApply ("H" with "[$][$]").
Qed.

Tactic Notation "tp_randnat" constr(j) "as" constr(H) :=
  let finish _ :=
        ((iIntros H; tp_normalise j) || fail 1 "tp_alloctape:" H "not correct intro pattern") in
  iStartProof;
  eapply (tac_tp_randnat j);
  [tc_solve || fail "tp_rand: cannot eliminate modality in the goal"
  | (* postpone solving [TCEq ...] until after the tape has been unified *)
  |iAssumptionCore || fail "tp_rand: cannot find the RHS"
  |tp_bind_helper
  |iAssumptionCore || fail "tp_rand: cannot find '? ↪ₛ ?'"
  |simpl; reflexivity || fail "tp_rand: this should not happen"
  |pm_reduce (* new goal *)];
  [ try tc_solve (*|| fail "tp_rand: cannot convert bound to a natural number"*)
  | finish () ].

Tactic Notation "tp_randnat" constr(j) :=
  tp_randnat j as "%".
