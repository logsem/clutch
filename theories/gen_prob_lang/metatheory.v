(** Metatheory for [gen_prob_lang]: the deterministic-fragment classification
    and tape-update helper lemmas needed by [erasure.v].  Ported from
    [prob_lang/metatheory.v], collapsing the per-distribution tape machinery
    ([tapes]/[tapes_laplace]/…) into the single generic [stape] and the generic
    [Sample]/[AllocSampleTape] primitives.  Only the subset consumed by erasure
    is ported (the [Rcoupl_rand_*] family-coupling lemmas live with the uniform
    family rules, not here). *)
From Stdlib Require Import Reals Psatz.
From stdpp Require Import functions gmap stringmap fin_sets fin_maps fin_map_dom.
From clutch.prelude Require Import stdpp_ext.
From clutch.common Require Import language ectx_language.
From clutch.prob Require Import distribution.
From clutch.gen_prob_lang Require Import lang.
From iris.prelude Require Import options.

(** * Substitution and closedness (signature-independent syntax; needed by the
      relational layer).  Ported from [prob_lang/metatheory.v], with the generic
      [Sample]/[AllocSampleTape] cases replacing rand/alloc-tape/laplace. *)

(* Adding a binder to a set of identifiers. *)
Local Definition set_binder_insert (x : binder) (X : stringset) : stringset :=
  match x with
  | BAnon => X
  | BNamed f => {[f]} ∪ X
  end.

Fixpoint is_closed_expr (X : stringset) (e : expr) : bool :=
  match e with
  | Val v => is_closed_val v
  | Var x => bool_decide (x ∈ X)
  | Rec f x e => is_closed_expr (set_binder_insert f (set_binder_insert x X)) e
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Deref e =>
     is_closed_expr X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | AllocN e1 e2 | Store e1 e2 =>
     is_closed_expr X e1 && is_closed_expr X e2
  | If e0 e1 e2 | Case e0 e1 e2 =>
     is_closed_expr X e0 && is_closed_expr X e1 && is_closed_expr X e2
  | Sample _ e1 e2 => is_closed_expr X e1 && is_closed_expr X e2
  | AllocSampleTape _ e => is_closed_expr X e
  | Tick e => is_closed_expr X e
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
  | Deref e => Deref (subst_map vs e)
  | Store e1 e2 => Store (subst_map vs e1) (subst_map vs e2)
  | Sample i e1 e2 => Sample i (subst_map vs e1) (subst_map vs e2)
  | AllocSampleTape i e => AllocSampleTape i (subst_map vs e)
  | Tick e => Tick (subst_map vs e)
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
  rewrite /bin_op_eval /bin_op_eval_bool /bin_op_eval_int /bin_op_eval_loc;
    repeat case_match; by naive_solver.
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
        rewrite length_replicate Z2Nat.id; auto with lia. }
    destruct Hix as [(?&?&?&[-> Hlt%inj_lt]%lookup_replicate_1)%heap_array_lookup|
                      [j Hj]%elem_of_map_to_list%list_elem_of_lookup_1].
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
    + by rewrite /= delete_insert_eq delete_delete_eq.
    + by rewrite /= binder_delete_insert // delete_insert_eq
        !binder_delete_delete delete_delete_eq.
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
  - by rewrite delete_delete_eq subst_subst delete_insert_eq.
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

(** * Deterministic head steps (signature-independent: a deterministic step
      never consults the sampling signature). *)
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
| IfTrueDS e1 e2 σ :
  det_head_step_rel (If (Val $ LitV $ LitBool true) e1 e2) σ e1 σ
| IfFalseDS e1 e2 σ :
  det_head_step_rel (If (Val $ LitV $ LitBool false) e1 e2) σ e2 σ
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
| DerefDS l v σ :
  σ.(heap) !! l = Some v →
  det_head_step_rel (Deref (Val $ LitV $ LitLoc l)) σ (of_val v) σ
| StoreDS l v w σ :
  σ.(heap) !! l = Some v →
  det_head_step_rel (Store (Val $ LitV $ LitLoc l) (Val w)) σ
    (Val $ LitV LitUnit) (state_upd_heap <[l:=w]> σ)
| TickDS z σ :
  det_head_step_rel (Tick (Val $ LitV $ LitInt z)) σ (Val $ LitV $ LitUnit) σ.

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
| IfTrueDSP e1 e2 σ :
  det_head_step_pred (If (Val $ LitV $ LitBool true) e1 e2) σ
| IfFalseDSP e1 e2 σ :
  det_head_step_pred (If (Val $ LitV $ LitBool false) e1 e2) σ
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
| DerefDSP l v σ :
  σ.(heap) !! l = Some v →
  det_head_step_pred (Deref (Val $ LitV $ LitLoc l)) σ
| StoreDSP l v w σ :
  σ.(heap) !! l = Some v →
  det_head_step_pred (Store (Val $ LitV $ LitLoc l) (Val w)) σ
| TickDSP z σ :
  det_head_step_pred (Tick (Val $ LitV $ LitInt z)) σ.

Definition is_det_head_step (e1 : expr) (σ1 : state) : bool :=
  match e1 with
  | Rec f x e => true
  | Pair (Val v1) (Val v2) => true
  | InjL (Val v) => true
  | InjR (Val v) => true
  | App (Val (RecV f x e1)) (Val v2) => true
  | UnOp op (Val v)  => bool_decide (is_Some (un_op_eval op v))
  | BinOp op (Val v1) (Val v2) => bool_decide (is_Some (bin_op_eval op v1 v2))
  | If (Val (LitV (LitBool true))) e1 e2 => true
  | If (Val (LitV (LitBool false))) e1 e2 => true
  | Fst (Val (PairV v1 v2)) => true
  | Snd (Val (PairV v1 v2)) => true
  | Case (Val (InjLV v)) e1 e2 => true
  | Case (Val (InjRV v)) e1 e2 => true
  | AllocN (Val (LitV (LitInt z))) (Val v) => bool_decide (0 < Z.to_nat z)%nat
  | Deref (Val (LitV (LitLoc l)))  =>
      bool_decide (is_Some (σ1.(heap) !! l))
  | Store (Val (LitV (LitLoc l))) (Val w) =>
      bool_decide (is_Some (σ1.(heap) !! l))
  | Tick (Val (LitV (LitInt z))) => true
  | _ => false
  end.

Lemma det_step_eq_tapes e1 σ1 e2 σ2 :
  det_head_step_rel e1 σ1 e2 σ2 → σ1.(stapes) = σ2.(stapes).
Proof. inversion 1; auto. Qed.

Lemma det_step_is_unique e1 σ1 e2 σ2 e3 σ3 :
  det_head_step_rel e1 σ1 e2 σ2 →
  det_head_step_rel e1 σ1 e3 σ3 →
  e2 = e3 ∧ σ2 = σ3.
Proof.
  intros H1 H2.
  inversion H1; inversion H2; simplify_eq; auto.
Qed.

Lemma det_step_pred_ex_rel e1 σ1 :
  det_head_step_pred e1 σ1 ↔ ∃ e2 σ2, det_head_step_rel e1 σ1 e2 σ2.
Proof.
  split.
  - intro H; inversion H; simplify_eq; eexists; eexists; econstructor; eauto.
  - intros (e2 & (σ2 & H)); inversion H ; econstructor; eauto.
Qed.

Local Ltac inv_det_head_step :=
  repeat
    match goal with
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : is_det_head_step _ _ = true |- _ =>
        rewrite /is_det_head_step in H;
        repeat (case_match in H; simplify_eq)
    | H : is_Some _ |- _ => destruct H
    | H : bool_decide  _ = true |- _ => rewrite bool_decide_eq_true in H; destruct_and?
    | _ => progress simplify_map_eq/=
    end.

Lemma is_det_head_step_true e1 σ1 :
  is_det_head_step e1 σ1 = true ↔ det_head_step_pred e1 σ1.
Proof.
  split; intro H.
  - destruct e1; inv_det_head_step; by econstructor.
  - inversion H; rewrite /is_det_head_step /=;
      repeat (rewrite bool_decide_eq_true_2 // || case_match); try (lia || done).
Qed.

(** * Tape-update helper lemmas (signature-independent: pure [gmap] surgery on
      the generic [stapes] map). *)
Lemma det_head_step_upd_tapes e1 σ1 e2 σ2 α t :
  det_head_step_rel e1 σ1 e2 σ2 →
  stapes σ1 !! α = Some t →
  det_head_step_rel
    e1 (state_upd_stapes <[α := t]> σ1)
    e2 (state_upd_stapes <[α := t]> σ2).
Proof.
  inversion 1; try econstructor; eauto.
  (* the AllocN case rewrites the heap, which [state_upd_stapes] leaves intact *)
  intros. rewrite state_upd_stapes_heap. econstructor; eauto.
Qed.

Lemma upd_diff_tape_comm σ α β bs bs':
  α ≠ β →
  state_upd_stapes <[β:= bs]> (state_upd_stapes <[α := bs']> σ) =
    state_upd_stapes <[α:= bs']> (state_upd_stapes <[β := bs]> σ).
Proof.
  intros. rewrite /state_upd_stapes /=. rewrite insert_insert_ne //.
Qed.

Lemma upd_tape_twice σ β bs bs' :
  state_upd_stapes <[β:= bs]> (state_upd_stapes <[β:= bs']> σ) = state_upd_stapes <[β:= bs]> σ.
Proof. rewrite /state_upd_stapes insert_insert_eq //. Qed.

Lemma fresh_loc_upd_some σ α bs bs' :
  (stapes σ) !! α = Some bs →
  fresh_loc (stapes σ) = (fresh_loc (<[α:= bs']> (stapes σ))).
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
  (stapes σ) !! α = Some bs →
  state_upd_stapes <[fresh_loc (stapes σ):=bs']> (state_upd_stapes <[α:=bs'']> σ)
  = state_upd_stapes <[α:=bs'']> (state_upd_stapes <[fresh_loc (stapes σ):=bs']> σ).
Proof.
  intros H.
  apply elem_fresh_ne in H.
  unfold state_upd_stapes.
  by rewrite insert_insert_ne.
Qed.

Lemma fresh_loc_lookup σ α bs bs' :
  (stapes σ) !! α = Some bs →
  (stapes (state_upd_stapes <[fresh_loc (stapes σ):=bs']> σ)) !! α = Some bs.
Proof.
  intros H.
  pose proof (elem_fresh_ne _ _ _ H).
  by rewrite lookup_insert_ne.
Qed.

Section metatheory.
  Context (S : Sig).

  Lemma det_head_step_singleton e1 σ1 e2 σ2 :
    det_head_step_rel e1 σ1 e2 σ2 → head_step S e1 σ1 = dret (e2, σ2).
  Proof.
    intros Hdet.
    apply pmf_1_eq_dret.
    inversion Hdet; simplify_eq/=; try case_match;
      simplify_option_eq; rewrite ?dret_1_1 //.
  Qed.

  (** Probabilistic head steps.  The four generic sampling shapes; each carries
      [sig_sample S i pv = Some μ] where a fresh draw is taken, so that the shape
      genuinely has a reduct (mass-1 ⟹ nonempty support). *)
  Inductive prob_head_step_pred : expr → state → Prop :=
  | SampleNoTapePSP i pv μ σ :
    sig_sample S i pv = Some μ →
    prob_head_step_pred (Sample i (Val pv) (Val $ LitV LitUnit)) σ
  | AllocSampleTapePSP i pv σ :
    prob_head_step_pred (AllocSampleTape i (Val pv)) σ
  | SampleTapeConsPSP i pv l x xs σ :
    σ.(stapes) !! l = Some (i, pv, x :: xs) →
    prob_head_step_pred (Sample i (Val pv) (Val $ LitV $ LitLbl l)) σ
  | SampleTapeEmptyPSP i pv l μ σ :
    σ.(stapes) !! l = Some (i, pv, []) →
    sig_sample S i pv = Some μ →
    prob_head_step_pred (Sample i (Val pv) (Val $ LitV $ LitLbl l)) σ
  | SampleTapeOtherPSP i pv l i' pv' xs μ σ :
    σ.(stapes) !! l = Some (i', pv', xs) →
    ¬ (i = i' ∧ pv = pv') →
    sig_sample S i pv = Some μ →
    prob_head_step_pred (Sample i (Val pv) (Val $ LitV $ LitLbl l)) σ.

  Definition head_step_pred e1 σ1 :=
    det_head_step_pred e1 σ1 ∨ prob_head_step_pred e1 σ1.

  Lemma val_not_head_step e1 σ1 :
    is_Some (to_val e1) → ¬ head_step_pred e1 σ1.
  Proof.
    intros [] [Hs | Hs]; inversion Hs; simplify_eq.
  Qed.

  Lemma head_step_pred_ex_rel e1 σ1 :
    head_step_pred e1 σ1 ↔ ∃ e2 σ2, head_step_rel S e1 σ1 e2 σ2.
  Proof.
    split.
    - intros [Hdet | Hp].
      + inversion Hdet; simplify_eq; do 2 eexists; by econstructor.
      + inversion Hp; simplify_eq.
        * (* SampleNoTape: get a support witness from mass-1 *)
          destruct (SeriesC_gtz_ex μ (pmf_pos μ)) as [v Hv].
          { erewrite sig_sample_mass; [lra|eauto]. }
          do 2 eexists; by eapply SampleNoTapeS.
        * do 2 eexists; by eapply AllocSampleTapeS.
        * do 2 eexists; by eapply SampleTapeConsS.
        * destruct (SeriesC_gtz_ex μ (pmf_pos μ)) as [v Hv].
          { erewrite sig_sample_mass; [lra|eauto]. }
          do 2 eexists; by eapply SampleTapeEmptyS.
        * destruct (SeriesC_gtz_ex μ (pmf_pos μ)) as [v Hv].
          { erewrite sig_sample_mass; [lra|eauto]. }
          do 2 eexists; by eapply SampleTapeOtherS.
    - intros (?&?& H). inversion H; simplify_eq;
        (try by (left; econstructor));
        (try by (right; econstructor; eauto)).
  Qed.

  Lemma not_head_step_pred_dzero e1 σ1:
    ¬ head_step_pred e1 σ1 ↔ head_step S e1 σ1 = dzero.
  Proof.
    split.
    - intro Hnstep.
      apply dzero_ext.
      intros (e2 & σ2).
      destruct (Rlt_le_dec 0 (head_step S e1 σ1 (e2, σ2))) as [H1%Rgt_lt | H2]; last first.
      { pose proof (pmf_pos (head_step S e1 σ1) (e2, σ2)). destruct H2; lra. }
      apply head_step_support_equiv_rel in H1.
      assert (∃ e2 σ2, head_step_rel S e1 σ1 e2 σ2) as Hex; eauto.
      by apply head_step_pred_ex_rel in Hex.
    - intros Hhead (e2 & σ2 & Hstep)%head_step_pred_ex_rel.
      apply head_step_support_equiv_rel in Hstep.
      assert (head_step S e1 σ1 (e2, σ2) = 0); [|lra].
      rewrite Hhead //.
  Qed.

  Lemma det_or_prob_or_dzero e1 σ1 :
    det_head_step_pred e1 σ1
    ∨ prob_head_step_pred e1 σ1
    ∨ head_step S e1 σ1 = dzero.
  Proof.
    destruct (Rlt_le_dec 0 (SeriesC (head_step S e1 σ1))) as [H1%Rlt_gt | [HZ | HZ]].
    - pose proof (SeriesC_gtz_ex (head_step S e1 σ1) (pmf_pos (head_step S e1 σ1)) H1) as [[e2 σ2] Hρ].
      pose proof (head_step_support_equiv_rel S e1 e2 σ1 σ2) as [H3 H4].
      specialize (H3 Hρ).
      assert (head_step_pred e1 σ1) as []; [|auto|auto].
      apply head_step_pred_ex_rel; eauto.
    - by pose proof (pmf_SeriesC_ge_0 (head_step S e1 σ1)) as ?%Rle_not_lt.
    - apply SeriesC_zero_dzero in HZ. eauto.
  Qed.

  (* If [e] is stuck in [σ], it stays stuck after extending tape [α] by a draw.
     The descriptor-preserving extension carries [sig_sample S i pv = Some μ],
     which rules out the only branch where extending a tape could *unstick* a
     [Sample] (a descriptor-matching read whose family is unsupported — which
     never happens here, since [state_step] only appends to supported tapes). *)
  Lemma head_step_dzero_upd_tapes α e σ i pv xs μ v :
    σ.(stapes) !! α = Some (i, pv, xs) →
    sig_sample S i pv = Some μ →
    head_step S e σ = dzero →
    head_step S e (state_upd_stapes <[α:=(i, pv, xs ++ [v])]> σ) = dzero.
  Proof.
    intros Hα Hμ Hz.
    destruct e; simpl in *; repeat case_match; simplify_eq; try done.
    all: try (exfalso; by eapply dret_not_dzero).
    all: try (exfalso;
           match goal with
           | Hz : dmap _ ?d = dzero, Hs : sig_sample S _ _ = Some ?d |- _ =>
               apply dmap_dzero_inv in Hz;
               pose proof (sig_sample_mass _ _ _ _ Hs) as Hmm;
               rewrite Hz dzero_mass in Hmm; lra
           end).
    all: destruct (decide (l0 = α)) as [->|Hne]; simplify_map_eq; try done.
    all: try congruence.
    all: first [ (apply bool_decide_eq_true_1 in H6 as [-> ->]; congruence)
               | (rewrite H3 in H4; discriminate) ].
  Qed.

End metatheory.
