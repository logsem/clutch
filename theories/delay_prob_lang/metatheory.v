From Coq Require Import Reals Psatz.
From stdpp Require Import functions gmap stringmap fin_sets.
From clutch.prelude Require Import stdpp_ext NNRbar fin uniform_list.
From clutch.prob Require Import distribution couplings couplings_app.
From clutch.common Require Import ectx_language.
From clutch.delay_prob_lang Require Import tactics notation urn_subst.
From clutch.delay_prob_lang Require Export lang.
From clutch.prob Require Import distribution couplings.
From iris.prelude Require Import options.
Set Default Proof Using "Type*".
(* This file contains some metatheory about the [delay_prob_lang] language *)

(* Adding a binder to a set of identifiers. *)
Local Definition set_binder_insert (x : binder) (X : stringset) : stringset :=
  match x with
  | BAnon => X
  | BNamed f => {[f]} ∪ X
  end.

(* Check if expression [e] is closed w.r.t. the set [X] of variable names,
   and that all the values in [e] are closed *)
Fixpoint is_closed_expr (X : stringset) (e : expr) : bool :=
  match e with
  | Val v => is_closed_val v
  | Var x => bool_decide (x ∈ X)
  | Rec f x e => is_closed_expr (set_binder_insert f (set_binder_insert x X)) e
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Load e |Rand e |DRand e=>
     is_closed_expr X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | AllocN e1 e2 | Store e1 e2 =>
     is_closed_expr X e1 && is_closed_expr X e2
  | If e0 e1 e2 | Case e0 e1 e2 =>
     is_closed_expr X e0 && is_closed_expr X e1 && is_closed_expr X e2
  end
with is_closed_val (v : val) : bool :=
  match v with
  | LitV _ => true
  | RecV f x e => is_closed_expr (set_binder_insert f (set_binder_insert x ∅)) e
  | PairV v1 v2 => is_closed_val v1 && is_closed_val v2
  | InjLV v | InjRV v => is_closed_val v
  end.

(** Parallel substitution *)
Fixpoint subst_map (vs : gmap string val) (e : expr)  : expr :=
  match e with
  | Val _ => e
  | Var y => if vs !! y is Some v then Val v else Var y
  | Rec f y e => Rec f y (subst_map (binder_delete y (binder_delete f vs)) e)
  | App e1 e2 => App (subst_map vs e1) (subst_map vs e2)
  | UnOp op e => UnOp op (subst_map vs e)
  | BinOp op e1 e2 => BinOp op (subst_map vs e1) (subst_map vs e2)
  | If e0 e1 e2 => If (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | Pair e1 e2 => Pair (subst_map vs e1) (subst_map vs e2)
  | Fst e => Fst (subst_map vs e)
  | Snd e => Snd (subst_map vs e)
  | InjL e => InjL (subst_map vs e)
  | InjR e => InjR (subst_map vs e)
  | Case e0 e1 e2 => Case (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | AllocN e1 e2 => AllocN (subst_map vs e1) (subst_map vs e2)
  | Load e => Load (subst_map vs e)
  | Store e1 e2 => Store (subst_map vs e1) (subst_map vs e2)
  | Rand e => Rand (subst_map vs e) 
  | DRand e => DRand (subst_map vs e) 
  end.

(* Properties *)
Local Instance set_unfold_elem_of_insert_binder x y X Q :
  SetUnfoldElemOf y X Q →
  SetUnfoldElemOf y (set_binder_insert x X) (Q ∨ BNamed y = x).
Proof. destruct 1; constructor; destruct x; set_solver. Qed.

Lemma is_closed_weaken X Y e : is_closed_expr X e → X ⊆ Y → is_closed_expr Y e.
Proof. revert X Y; induction e; naive_solver (eauto; set_solver). Qed.

Lemma is_closed_weaken_empty X e : is_closed_expr ∅ e → is_closed_expr X e.
Proof. intros. by apply is_closed_weaken with ∅, empty_subseteq. Qed.

Lemma is_closed_subst X e y v :
  is_closed_val v →
  is_closed_expr ({[y]} ∪ X) e →
  is_closed_expr X (subst y v e).
Proof.
  intros Hv. revert X.
  induction e=> X /= ?; destruct_and?; split_and?; simplify_option_eq;
    try match goal with
    | H : ¬(_ ∧ _) |- _ => apply not_and_l in H as [?%dec_stable|?%dec_stable]
    end; eauto using is_closed_weaken with set_solver.
Qed.
Lemma is_closed_subst' X e x v :
  is_closed_val v →
  is_closed_expr (set_binder_insert x X) e →
  is_closed_expr X (subst' x v e).
Proof. destruct x; eauto using is_closed_subst. Qed.

Lemma subst_is_closed X e x es : is_closed_expr X e → x ∉ X → subst x es e = e.
Proof.
  revert X. induction e=> X /=;
   rewrite ?bool_decide_spec ?andb_True=> ??;
   repeat case_decide; simplify_eq/=; f_equal; intuition eauto with set_solver.
Qed.

Lemma subst_is_closed_empty e x v : is_closed_expr ∅ e → subst x v e = e.
Proof. intros. apply subst_is_closed with (∅:stringset); set_solver. Qed.

Lemma subst_subst e x v v' :
  subst x v (subst x v' e) = subst x v' e.
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using subst_is_closed_empty with f_equal.
Qed.
Lemma subst_subst' e x v v' :
  subst' x v (subst' x v' e) = subst' x v' e.
Proof. destruct x; simpl; auto using subst_subst. Qed.

Lemma subst_subst_ne e x y v v' :
  x ≠ y → subst x v (subst y v' e) = subst y v' (subst x v e).
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using eq_sym, subst_is_closed_empty with f_equal.
Qed.
Lemma subst_subst_ne' e x y v v' :
  x ≠ y → subst' x v (subst' y v' e) = subst' y v' (subst' x v e).
Proof. destruct x, y; simpl; auto using subst_subst_ne with congruence. Qed.

Lemma subst_rec' f y e x v :
  x = f ∨ x = y ∨ x = BAnon →
  subst' x v (Rec f y e) = Rec f y e.
Proof. intros. destruct x; simplify_option_eq; naive_solver. Qed.
Lemma subst_rec_ne' f y e x v :
  (x ≠ f ∨ f = BAnon) → (x ≠ y ∨ y = BAnon) →
  subst' x v (Rec f y e) = Rec f y (subst' x v e).
Proof. intros. destruct x; simplify_option_eq; naive_solver. Qed.

Lemma bin_op_eval_closed op v1 v2 v' :
  is_closed_val v1 → is_closed_val v2 → bin_op_eval op v1 v2 = Some v' →
  is_closed_val v'.
Proof.
  rewrite /bin_op_eval. destruct op; simpl; repeat case_match; naive_solver.
Qed.

Lemma heap_closed_alloc σ l n w :
  (0 < n)%Z →
  is_closed_val w →
  map_Forall (λ _ v, is_closed_val v) (heap σ) →
  (∀ i : Z, (0 ≤ i)%Z → (i < n)%Z → heap σ !! (l +ₗ i) = None) →
  map_Forall (λ _ v, is_closed_val v)
             (heap_array l (replicate (Z.to_nat n) w) ∪ heap σ).
Proof.
  intros Hn Hw Hσ Hl.
  eapply (map_Forall_ind
            (λ k v, ((heap_array l (replicate (Z.to_nat n) w) ∪ heap σ)
                       !! k = Some v))).
  - apply map_Forall_empty.
  - intros m i x Hi Hix Hkwm Hm.
    apply map_Forall_insert_2; auto.
    apply lookup_union_Some in Hix; last first.
    { eapply heap_array_map_disjoint;
        rewrite replicate_length Z2Nat.id; auto with lia. }
    destruct Hix as [(?&?&?&[-> Hlt%inj_lt]%lookup_replicate_1)%heap_array_lookup|
                      [j Hj]%elem_of_map_to_list%elem_of_list_lookup_1].
    + simplify_eq/=. rewrite !Z2Nat.id in Hlt; eauto with lia.
    + apply map_Forall_to_list in Hσ.
      by eapply Forall_lookup in Hσ; eauto; simpl in *.
  - apply map_Forall_to_list, Forall_forall.
    intros [? ?]; apply elem_of_map_to_list.
Qed.

Lemma subst_map_empty e : subst_map ∅ e = e.
Proof.
  assert (∀ x, binder_delete x (∅:gmap _ val) = ∅) as Hdel.
  { intros [|x]; by rewrite /= ?delete_empty. }
  induction e; simplify_map_eq; rewrite ?Hdel; auto with f_equal.
Qed.
Lemma subst_map_insert x v vs e :
  subst_map (<[x:=v]>vs) e = subst x v (subst_map (delete x vs) e).
Proof.
  revert vs. induction e=> vs; simplify_map_eq; auto with f_equal.
  - match goal with
    | |- context [ <[?x:=_]> _ !! ?y ] =>
       destruct (decide (x = y)); simplify_map_eq=> //
    end. by case (vs !! _); simplify_option_eq.
  - destruct (decide _) as [[??]|[<-%dec_stable|[<-%dec_stable ?]]%not_and_l_alt].
    + rewrite !binder_delete_insert // !binder_delete_delete; eauto with f_equal.
    + by rewrite /= delete_insert_delete delete_idemp.
    + by rewrite /= binder_delete_insert // delete_insert_delete
        !binder_delete_delete delete_idemp.
Qed.
Lemma subst_map_singleton x v e :
  subst_map {[x:=v]} e = subst x v e.
Proof. by rewrite subst_map_insert delete_empty subst_map_empty. Qed.

Lemma subst_map_binder_insert b v vs e :
  subst_map (binder_insert b v vs) e =
  subst' b v (subst_map (binder_delete b vs) e).
Proof. destruct b; rewrite ?subst_map_insert //. Qed.
Lemma subst_map_binder_insert_empty b v e :
  subst_map (binder_insert b v ∅) e = subst' b v e.
Proof. by rewrite subst_map_binder_insert binder_delete_empty subst_map_empty. Qed.

Lemma subst_map_binder_insert_2 b1 v1 b2 v2 vs e :
  subst_map (binder_insert b1 v1 (binder_insert b2 v2 vs)) e =
  subst' b2 v2 (subst' b1 v1 (subst_map (binder_delete b2 (binder_delete b1 vs)) e)).
Proof.
  destruct b1 as [|s1], b2 as [|s2]=> /=; auto using subst_map_insert.
  rewrite subst_map_insert. destruct (decide (s1 = s2)) as [->|].
  - by rewrite delete_idemp subst_subst delete_insert_delete.
  - by rewrite delete_insert_ne // subst_map_insert subst_subst_ne.
Qed.
Lemma subst_map_binder_insert_2_empty b1 v1 b2 v2 e :
  subst_map (binder_insert b1 v1 (binder_insert b2 v2 ∅)) e =
  subst' b2 v2 (subst' b1 v1 e).
Proof.
  by rewrite subst_map_binder_insert_2 !binder_delete_empty subst_map_empty.
Qed.

Lemma subst_map_is_closed X e vs :
  is_closed_expr X e →
  (∀ x, x ∈ X → vs !! x = None) →
  subst_map vs e = e.
Proof.
  revert X vs. assert (∀ x x1 x2 X (vs : gmap string val),
    (∀ x, x ∈ X → vs !! x = None) →
    x ∈ set_binder_insert x2 (set_binder_insert x1 X) →
    binder_delete x1 (binder_delete x2 vs) !! x = None).
  { intros x x1 x2 X vs ??. rewrite !lookup_binder_delete_None. set_solver. }
  induction e=> X vs /= ? HX; repeat case_match; naive_solver eauto with f_equal.
Qed.

Lemma subst_map_is_closed_empty e vs : is_closed_expr ∅ e → subst_map vs e = e.
Proof. intros. apply subst_map_is_closed with (∅ : stringset); set_solver. Qed.

Local Open Scope R.

(** Removed lemmas on couplings*)

(** Some useful lemmas to reason about language properties  *)

Inductive det_head_step_rel : expr → state → expr → state → Prop :=
| RecDS f x e σ :
  det_head_step_rel (Rec f x e) σ (Val $ RecV f x e) σ
| PairDS v1 v2 σ :
  det_head_step_rel (Pair (Val v1) (Val v2)) σ (Val $ PairV v1 v2) σ
| InjLDS v σ :
  det_head_step_rel (InjL $ Val v) σ (Val $ InjLV v) σ
| InjRDS v σ :
  det_head_step_rel (InjR $ Val v) σ (Val $ InjRV v) σ
| BetaDS f x e1 v2 e' σ :
  e' = subst' x v2 (subst' f (RecV f x e1) e1) →
  det_head_step_rel (App (Val $ RecV f x e1) (Val v2)) σ e' σ
| UnOpDS op v v' σ :
  un_op_eval op v = Some v' →
  det_head_step_rel (UnOp op (Val v)) σ (Val v') σ
| BinOpDS op v1 v2 v' σ :
  bin_op_eval op v1 v2 = Some v' →
  det_head_step_rel (BinOp op (Val v1) (Val v2)) σ (Val v') σ
| IfTrueDS bl e1 e2 σ :
  urn_subst_equal σ bl true ->
  det_head_step_rel (If (Val $ LitV $ bl) e1 e2) σ e1 σ
| IfFalseDS bl e1 e2 σ :
  urn_subst_equal σ bl false ->
  det_head_step_rel (If (Val $ LitV $ bl) e1 e2) σ e2 σ
| FstDS v1 v2 σ :
  det_head_step_rel (Fst (Val $ PairV v1 v2)) σ (Val v1) σ
| SndDS v1 v2 σ :
  det_head_step_rel (Snd (Val $ PairV v1 v2)) σ (Val v2) σ
| CaseLDS v e1 e2 σ :
  det_head_step_rel (Case (Val $ InjLV v) e1 e2) σ (App e1 (Val v)) σ
| CaseRDS v e1 e2 σ :
  det_head_step_rel (Case (Val $ InjRV v) e1 e2) σ (App e2 (Val v)) σ
| AllocNDS z N v σ l :
  l = fresh_loc σ.(heap) →
  N = Z.to_nat z →
  (0 < N)%nat ->
  det_head_step_rel (AllocN (Val (LitV (LitInt z))) (Val v)) σ
    (Val $ LitV $ LitLoc l) (state_upd_heap_N l N v σ)
| LoadDS l v σ :
  σ.(heap) !! l = Some v →
  det_head_step_rel (Load (Val $ LitV $ LitLoc l)) σ (of_val v) σ
| StoreDS l v w σ :
  σ.(heap) !! l = Some v →
  det_head_step_rel (Store (Val $ LitV $ LitLoc l) (Val w)) σ
    (Val $ LitV LitUnit) (state_upd_heap <[l:=w]> σ).

Inductive det_head_step_pred : expr → state → Prop :=
| RecDSP f x e σ :
  det_head_step_pred (Rec f x e) σ
| PairDSP v1 v2 σ :
  det_head_step_pred (Pair (Val v1) (Val v2)) σ
| InjLDSP v σ :
  det_head_step_pred (InjL $ Val v) σ
| InjRDSP v σ :
  det_head_step_pred (InjR $ Val v) σ
| BetaDSP f x e1 v2 σ :
  det_head_step_pred (App (Val $ RecV f x e1) (Val v2)) σ
| UnOpDSP op v σ v' :
  un_op_eval op v = Some v' →
  det_head_step_pred (UnOp op (Val v)) σ
| BinOpDSP op v1 v2 σ v' :
  bin_op_eval op v1 v2 = Some v' →
  det_head_step_pred (BinOp op (Val v1) (Val v2)) σ
| IfTrueDSP bl e1 e2 σ :
  urn_subst_equal σ bl true ->
  det_head_step_pred (If (Val $ LitV $ bl) e1 e2) σ
| IfFalseDSP bl e1 e2 σ :
  urn_subst_equal σ bl false ->
  det_head_step_pred (If (Val $ LitV $ bl) e1 e2) σ
| FstDSP v1 v2 σ :
  det_head_step_pred (Fst (Val $ PairV v1 v2)) σ
| SndDSP v1 v2 σ :
  det_head_step_pred (Snd (Val $ PairV v1 v2)) σ
| CaseLDSP v e1 e2 σ :
  det_head_step_pred (Case (Val $ InjLV v) e1 e2) σ
| CaseRDSP v e1 e2 σ :
  det_head_step_pred (Case (Val $ InjRV v) e1 e2) σ
| AllocNDSP z N v σ l :
  l = fresh_loc σ.(heap) →
  N = Z.to_nat z →
  (0 < N)%nat ->
  det_head_step_pred (AllocN (Val (LitV (LitInt z))) (Val v)) σ
| LoadDSP l v σ :
  σ.(heap) !! l = Some v →
  det_head_step_pred (Load (Val $ LitV $ LitLoc l)) σ
| StoreDSP l v w σ :
  σ.(heap) !! l = Some v →
  det_head_step_pred (Store (Val $ LitV $ LitLoc l) (Val w)) σ.

Definition is_det_head_step (e1 : expr) (σ1 : state)  : bool :=
  match e1 with
  | Rec f x e => true
  | Pair (Val v1) (Val v2) => true
  | InjL (Val v) => true
  | InjR (Val v) => true
  | App (Val (RecV f x e1)) (Val v2) => true
  | UnOp op (Val v)  => bool_decide(is_Some(un_op_eval op v))
  | BinOp op (Val v1) (Val v2) => bool_decide (is_Some(bin_op_eval op v1 v2))
  | If (Val (LitV bl)) e1 e2 => bool_decide (urn_subst_equal σ1 bl true \/ urn_subst_equal σ1 bl false)
  | Fst (Val (PairV v1 v2)) => true
  | Snd (Val (PairV v1 v2)) => true
  | Case (Val (InjLV v)) e1 e2 => true
  | Case (Val (InjRV v)) e1 e2 => true
  | AllocN (Val (LitV (LitInt z))) (Val v) => bool_decide (0 < Z.to_nat z)%nat
  | Load (Val (LitV (LitLoc l)))  =>
      bool_decide (is_Some (σ1.(heap) !! l))
  | Store (Val (LitV (LitLoc l))) (Val w) =>
      bool_decide (is_Some (σ1.(heap) !! l))
  (* | Tick (Val (LitV (LitInt z))) => true *)
  | _ => false
  end.

Lemma det_step_eq_tapes e1 σ1 e2 σ2 :
  det_head_step_rel e1 σ1 e2 σ2 → σ1.(urns) = σ2.(urns).
Proof. inversion 1; auto. Qed.

Inductive prob_head_step_pred : expr -> state -> Prop :=
| IfPSP bl e1 e2 σ:
  ¬ urn_subst_equal σ bl (LitBool true) -> 
  ¬ urn_subst_equal σ bl (LitBool false) ->
  base_lit_type_check bl = Some BLTBool ->
  base_lit_support_set bl ⊆ urns_support_set (σ.(urns)) ->
  prob_head_step_pred (If (Val $ LitV $ bl) e1 e2) σ
| RandPSP (N : nat) σ (z:Z) bl :
  urn_subst_equal σ bl z ->
  N = Z.to_nat z →
  prob_head_step_pred (rand #bl) σ
| DRandPSP (N : nat) σ (z:Z) bl :
  urn_subst_equal σ bl z ->
  N = Z.to_nat z →
  prob_head_step_pred (drand #bl) σ.

Definition head_step_pred e1 σ1 :=
  det_head_step_pred e1 σ1 ∨ prob_head_step_pred e1 σ1.

Lemma det_step_is_unique e1 σ1 e2 σ2 e3 σ3 :
  det_head_step_rel e1 σ1 e2 σ2 →
  det_head_step_rel e1 σ1 e3 σ3 →
  e2 = e3 ∧ σ2 = σ3.
Proof.
  intros H1 H2.
  inversion H1; inversion H2; simplify_eq; auto.
  - exfalso. by eapply (urn_subst_equal_not_unique _ _ true false).
  - exfalso. by eapply (urn_subst_equal_not_unique _ _ true false).
Qed. 

Lemma det_step_pred_ex_rel e1 σ1 :
  det_head_step_pred e1 σ1 ↔ ∃ e2 σ2, det_head_step_rel e1 σ1 e2 σ2.
Proof.
  split.
  - intro H; inversion H; simplify_eq; eexists; eexists.
    9:{ by apply IfFalseDS. }
    all: econstructor; eauto.
  - intros (e2 & (σ2 & H)); inversion H.
    9:{ by apply IfFalseDSP. }
    all: econstructor; eauto.
Qed.

Local Ltac solve_step_det :=
  rewrite /pmf /=;
    repeat (rewrite bool_decide_eq_true_2 // || case_match);
  try (lra || lia || done || naive_solver).

Local Ltac inv_det_head_step :=
  repeat
    match goal with
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : is_det_head_step _ _ = true |- _ =>
        rewrite /is_det_head_step in H;
        repeat (case_match in H; simplify_eq)
    | H : is_Some _ |- _ => destruct H
    | H : bool_decide  _ = true |- _ => rewrite bool_decide_eq_true in H; destruct_and?; destruct_or?
    | _ => progress simplify_map_eq/=
    end.

Lemma is_det_head_step_true e1 σ1 :
  is_det_head_step e1 σ1 = true ↔ det_head_step_pred e1 σ1.
Proof.
  split; intro H.
  - destruct e1; inv_det_head_step.
    6:{ by apply IfFalseDSP. }
    all: by econstructor.
  - inversion H; solve_step_det.
Qed.

Lemma det_head_step_singleton e1 σ1 e2 σ2 :
  det_head_step_rel e1 σ1 e2 σ2 → head_step e1 σ1 = dret (e2, σ2).
Proof.
  intros Hdet.
  apply pmf_1_eq_dret.
  inversion Hdet; simplify_eq/=; try case_match;
    simplify_option_eq; rewrite ?dret_1_1 //.
  - by case_bool_decide.
  - case_bool_decide; last done.
    exfalso. by eapply (urn_subst_equal_not_unique _ _ true false).
  - rewrite bool_decide_eq_true_2; last done. rewrite dret_1_1//.
Qed.

Lemma val_not_head_step e1 σ1 :
  is_Some (to_val e1) → ¬ head_step_pred e1 σ1.
Proof.
  intros [] [Hs | Hs]; inversion Hs; simplify_eq.
Qed.

Lemma head_step_pred_ex_rel e1 σ1 :
  head_step_pred e1 σ1 ↔ ∃ e2 σ2, head_step_rel e1 σ1 e2 σ2.
Proof.
  split.
  - intros [Hdet | Hdet];
      inversion Hdet; simplify_eq; try by (do 2 eexists; try (by econstructor)).
    pose proof set_urns_f_nonempty (urns σ1) as Hnonempty.
    apply size_pos_elem_of in Hnonempty as [f Hnonempty].
    rewrite elem_of_set_urns_f_valid in Hnonempty.
    rename select (base_lit_type_check _ = _) into H'.
    eapply urn_subst_exists in H'; last by erewrite <-urns_f_valid_support.
    destruct H' as [[][H1 ]]; apply urn_subst_is_simple in H1 as H4; simplify_eq.
    rename select (bool) into b.
    destruct b.
    + eexists _, _.
      eapply IfTrueS'; try done.
      by intros ? ->%urns_subst_f_to_urns_unique_valid. 
    + eexists _, _.
      eapply IfFalseS'; try done.
      by intros ? ->%urns_subst_f_to_urns_unique_valid.
      Unshelve. all : apply 0%fin.
  - intros (?&?& H). inversion H; simplify_eq;
      (try by (left; econstructor));
      (try by (right; econstructor)).
    + rename select (urn_subst_equal _ _ _) into H'.
      right; econstructor; try done.
      * apply urn_subst_equal_well_typed in H'.
        by destruct!/=.
      * apply urn_subst_equal_support in H'.
        rewrite urns_subst_f_to_urns_support in H'.
        by erewrite urns_f_valid_support.
    + rename select (urn_subst_equal _ _ _) into H'.
      right; econstructor; try done.
      * apply urn_subst_equal_well_typed in H'.
        by destruct!/=.
      * apply urn_subst_equal_support in H'.
        rewrite urns_subst_f_to_urns_support in H'.
        by erewrite urns_f_valid_support.    
Qed.

Lemma not_head_step_pred_dzero e1 σ1:
  ¬ head_step_pred e1 σ1 ↔ head_step e1 σ1 = dzero.
Proof.
  split.
  - intro Hnstep.
    apply dzero_ext.
    intros (e2 & σ2).
    destruct (Rlt_le_dec 0 (head_step e1 σ1 (e2, σ2))) as [H1%Rgt_lt | H2]; last first.
    { pose proof (pmf_pos (head_step e1 σ1) (e2, σ2)). destruct H2; lra. }
    apply head_step_support_equiv_rel in H1.
    assert (∃ e2 σ2, head_step_rel e1 σ1 e2 σ2) as Hex; eauto.
    by apply head_step_pred_ex_rel in Hex.
  - intros Hhead (e2 & σ2 & Hstep)%head_step_pred_ex_rel.
    apply head_step_support_equiv_rel in Hstep.
    assert (head_step e1 σ1 (e2, σ2) = 0); [|lra].
    rewrite Hhead //.
Qed.

Lemma det_or_prob_or_dzero e1 σ1 :
  det_head_step_pred e1 σ1
  ∨ prob_head_step_pred e1 σ1
  ∨ head_step e1 σ1 = dzero.
Proof.
  destruct (Rlt_le_dec 0 (SeriesC (head_step e1 σ1))) as [H1%Rlt_gt | [HZ | HZ]].
  - pose proof (SeriesC_gtz_ex (head_step e1 σ1) (pmf_pos (head_step e1 σ1)) H1) as [[e2 σ2] Hρ].
    pose proof (head_step_support_equiv_rel e1 e2 σ1 σ2) as [H3 H4].
    specialize (H3 Hρ).
    assert (head_step_pred e1 σ1) as []; [|auto|auto].
    apply head_step_pred_ex_rel; eauto.
  - by pose proof (pmf_SeriesC_ge_0 (head_step e1 σ1))
      as ?%Rle_not_lt.
  - apply SeriesC_zero_dzero in HZ. eauto.
Qed.

(* Lemma head_step_dzero_upd_tapes α e σ N zs z  : *)
(*   α ∈ dom σ.(tapes) → *)
(*   head_step e σ = dzero → *)
(*   head_step e (state_upd_tapes <[α:=(N; zs ++ [z]) : tape]> σ) = dzero. *)
(* Proof. *)
(*   intros Hdom Hz. *)
(*   destruct e; simpl in *; *)
(*     repeat case_match; done || inv_dzero; simplify_map_eq. *)
(*   (* TODO: [simplify_map_eq] should solve this? *) *)
(*   - destruct (decide (α = l1)). *)
(*     + simplify_eq. *)
(*       by apply not_elem_of_dom_2 in H5. *)
(*     + rewrite lookup_insert_ne // in H6. *)
(*       rewrite H5 in H6. done. *)
(*   - destruct (decide (α = l1)). *)
(*     + simplify_eq. *)
(*       by apply not_elem_of_dom_2 in H5. *)
(*     + rewrite lookup_insert_ne // in H6. *)
(*       rewrite H5 in H6. done. *)
(*   - destruct (decide (α = l1)). *)
(*     + simplify_eq. *)
(*       by apply not_elem_of_dom_2 in H5. *)
(*     + rewrite lookup_insert_ne // in H6. *)
(*       rewrite H5 in H6. done. *)
(* Qed. *)

(* Lemma det_head_step_upd_tapes N e1 σ1 e2 σ2 α z zs : *)
(*   det_head_step_rel e1 σ1 e2 σ2 → *)
(*   tapes σ1 !! α = Some (N; zs) → *)
(*   det_head_step_rel *)
(*     e1 (state_upd_tapes <[α := (N; zs ++ [z])]> σ1) *)
(*     e2 (state_upd_tapes <[α := (N; zs ++ [z])]> σ2). *)
(* Proof. *)
(*   inversion 1; try econstructor; eauto. *)
(*   (* Unsolved case *) *)
(*   intros. rewrite state_upd_tapes_heap. econstructor; eauto. *)
(* Qed. *)

(** * Lemmas about updating urns *)
Lemma upd_urn_some σ α ns :
  urns (state_upd_urns <[α:= ns]> σ) !! α = Some ns.
Proof.
  rewrite /state_upd_urns /=. rewrite lookup_insert //.
Qed.

Lemma upd_urn_some_trivial σ α bs:
  urns σ !! α = Some bs →
  state_upd_urns <[α:=urns σ !!! α]> σ = σ.
Proof.
  destruct σ. simpl.
  intros H.
  rewrite (lookup_total_correct _ _ _ H).
  f_equal.
  by apply insert_id.
Qed.

Lemma upd_diff_urn_comm σ α β bs bs':
  α ≠ β →
  state_upd_urns <[β:= bs]> (state_upd_urns <[α := bs']> σ) =
    state_upd_urns <[α:= bs']> (state_upd_urns <[β := bs]> σ).
Proof.
  intros. rewrite /state_upd_urns /=. rewrite insert_commute //.
Qed.

Lemma upd_diff_urn_tot σ α β bs:
  α ≠ β →
  urns σ !!! α = urns (state_upd_urns <[β:=bs]> σ) !!! α.
Proof. symmetry ; by rewrite lookup_total_insert_ne. Qed.

Lemma upd_urn_twice σ β bs bs' :
  state_upd_urns <[β:= bs]> (state_upd_urns <[β:= bs']> σ) = state_upd_urns <[β:= bs]> σ.
Proof. rewrite /state_upd_urns insert_insert //. Qed.

Lemma fresh_loc_upd_some σ α bs bs' :
  (urns σ) !! α = Some bs →
  fresh_loc (urns σ) = (fresh_loc (<[α:= bs']> (urns σ))).
Proof.
  intros Hα.
  apply fresh_loc_eq_dom.
  by rewrite dom_insert_lookup_L.
Qed.

Lemma elem_fresh_ne {V} (ls : gmap loc V) k v :
  ls !! k = Some v → fresh_loc ls ≠ k.
Proof.
  intros; assert (is_Some (ls !! k)) as Hk by auto.
  pose proof (fresh_loc_is_fresh ls).
  rewrite -elem_of_dom in Hk.
  set_solver.
Qed.

Lemma fresh_loc_upd_swap σ α bs bs' bs'' :
  (urns σ) !! α = Some bs →
  state_upd_urns <[fresh_loc (urns σ):=bs']> (state_upd_urns <[α:=bs'']> σ)
  = state_upd_urns <[α:=bs'']> (state_upd_urns <[fresh_loc (urns σ):=bs']> σ).
Proof.
  intros H.
  apply elem_fresh_ne in H.
  unfold state_upd_urns.
  by rewrite insert_commute.
Qed.

Lemma fresh_loc_lookup σ α bs bs' :
  (urns σ) !! α = Some bs →
  (urns (state_upd_urns <[fresh_loc (urns σ):=bs']> σ)) !! α = Some bs.
Proof.
  intros H.
  pose proof (elem_fresh_ne _ _ _ H).
  by rewrite lookup_insert_ne.
Qed.

(* Lemma prim_step_empty_tape σ α (z:Z) K N : *)
(*   (urns σ) !! α = Some (N; []) -> prim_step (fill K (rand(#lbl:α) #z)) σ = prim_step (fill K (rand #z)) σ. *)
(* Proof. *)
(*   intros H. *)
(*   rewrite !fill_dmap; [|done|done]. *)
(*   rewrite /dmap. *)
(*   f_equal. *)
(*   simpl. apply distr_ext; intros [e s]. *)
(*   erewrite !head_prim_step_eq; simpl; last first. *)
(*   (** type classes dont work? *) *)
(*   { destruct (decide (Z.to_nat z=N)) as [<-|?] eqn:Heqn. *)
(*     all: eexists (_, σ); eapply head_step_support_equiv_rel; *)
(*       eapply head_step_support_eq; simpl; last first. *)
(*     - rewrite H. rewrite bool_decide_eq_true_2; last lia. *)
(*       eapply dmap_unif_nonzero; last done. *)
(*       intros ???. simplify_eq. done. *)
(*     - apply Rinv_pos. pose proof pos_INR_S (Z.to_nat z). lra. *)
(*     - rewrite H. case_bool_decide as H0; first lia. *)
(*       eapply dmap_unif_nonzero; last done. *)
(*       intros ???. by simplify_eq. *)
(*     - apply Rinv_pos. pose proof pos_INR_S (Z.to_nat z). lra. *)
(*   } *)
(*   { eexists (_, σ); eapply head_step_support_equiv_rel; *)
(*       eapply head_step_support_eq; simpl; last first. *)
(*     - eapply dmap_unif_nonzero; last done. *)
(*       intros ???. simplify_eq. done. *)
(*     - apply Rinv_pos. pose proof pos_INR_S (Z.to_nat z). lra. *)
(*   } rewrite H. *)
(*   case_bool_decide; last done. *)
(*   subst. done. *)
(*   Unshelve. *)
(*   all: exact (0%fin). *)
(* Qed. *)
  

(** * remove drand *)
Fixpoint remove_drand_expr e:=
  match e with
  | Val v => Val $ remove_drand_val v
  | Var x => Var x
  | Rec f x e => Rec f x (remove_drand_expr e)
  | App e1 e2 => App (remove_drand_expr e1) (remove_drand_expr e2)
  | UnOp op e => UnOp op (remove_drand_expr e)
  | BinOp op e1 e2 => BinOp op (remove_drand_expr e1) (remove_drand_expr e2)
  | If e0 e1 e2 => If (remove_drand_expr e0) (remove_drand_expr e1) (remove_drand_expr e2)
  | Pair e1 e2 => Pair (remove_drand_expr e1) (remove_drand_expr e2)
  | Fst e => Fst (remove_drand_expr e)
  | Snd e => Snd (remove_drand_expr e)
  | InjL e => InjL (remove_drand_expr e)
  | InjR e => InjR (remove_drand_expr e)
  | Case e0 e1 e2 => Case (remove_drand_expr e0) (remove_drand_expr e1) (remove_drand_expr e2)
  | AllocN e1 e2 => AllocN (remove_drand_expr e1) (remove_drand_expr e2)
  | Load e => Load (remove_drand_expr e)
  | Store e1 e2 => Store (remove_drand_expr e1) (remove_drand_expr e2)
  | Rand e => Rand (remove_drand_expr e)
  | DRand e => DRand (remove_drand_expr e)
  end
with remove_drand_val v : val:= 
  match v with
  | LitV l => LitV l
  | RecV f x e => RecV f x (remove_drand_expr e)
  | PairV v1 v2 => PairV (remove_drand_val v1) (remove_drand_val v2)
  | InjLV v => InjLV (remove_drand_val v)
  | InjRV v => InjRV (remove_drand_val v)
  end.
