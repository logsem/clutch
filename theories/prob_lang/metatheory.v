From Coq Require Import Reals Psatz.
From stdpp Require Import functions gmap stringmap.
From clutch.prelude Require Import stdpp_ext.
From clutch.prob Require Import distribution couplings.
From clutch.program_logic Require Import ectx_language.
From clutch.prob_lang Require Import locations tactics notation.
From clutch.prob_lang Require Export lang.
From iris.prelude Require Import options.
Set Default Proof Using "Type*".
(* This file contains some metatheory about the [prob_lang] language *)

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
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Alloc e | Load e =>
     is_closed_expr X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Store e1 e2 | Rand e1 e2 =>
     is_closed_expr X e1 && is_closed_expr X e2
  | If e0 e1 e2 | Case e0 e1 e2 =>
     is_closed_expr X e0 && is_closed_expr X e1 && is_closed_expr X e2
  | AllocTape e => is_closed_expr X e
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
  | Alloc e => Alloc (subst_map vs e)
  | Load e => Load (subst_map vs e)
  | Store e1 e2 => Store (subst_map vs e1) (subst_map vs e2)
  | AllocTape e => AllocTape (subst_map vs e)
  | Rand e1 e2 => Rand (subst_map vs e1) (subst_map vs e2)
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
  rewrite /bin_op_eval /bin_op_eval_bool /bin_op_eval_int;
    repeat case_match; by naive_solver.
Qed.

(* The stepping relation preserves closedness *)
Lemma head_step_is_closed e1 σ1 e2 σ2 :
  is_closed_expr ∅ e1 →
  map_Forall (λ _ v, is_closed_val v) σ1.(heap) →
  head_step_rel e1 σ1 e2 σ2 →
  is_closed_expr ∅ e2 ∧
  map_Forall (λ _ v, is_closed_val v) σ2.(heap).
Proof.
  intros Cl1 Clσ1 STEP.
  induction STEP; simpl in *; split_and!;
    try apply map_Forall_insert_2; try by naive_solver.
  - subst. repeat apply is_closed_subst'; naive_solver.
  - unfold un_op_eval in *. repeat case_match; naive_solver.
  - eapply bin_op_eval_closed; eauto; naive_solver.
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

(** * rand(N) ~ rand(N) coupling *)
Lemma Rcoupl_rand_rand N f `{Bij (fin (S N)) (fin (S N)) f} z σ1 σ1' :
  N = Z.to_nat z →
  Rcoupl
    (prim_step (rand #z from #()) σ1)
    (prim_step (rand #z from #()) σ1')
    (λ ρ2 ρ2', ∃ (n : fin (S N)),
        ρ2 = (Val #n, σ1) ∧ ρ2' = (Val #(f n), σ1')).
Proof.
  intros Hz.
  rewrite head_prim_step_eq /=; last first.
  { eexists (Val #0%fin, σ1). eapply head_step_support_equiv_rel.
    by eapply (RandNoTapeS _ _ 0%fin). }
  rewrite head_prim_step_eq /=; last first.
  { eexists (Val #0, σ1'). eapply head_step_support_equiv_rel.
    by eapply (RandNoTapeS _ _ 0%fin). }
  rewrite /dmap -Hz.
  eapply Rcoupl_dbind; [|by eapply Rcoupl_dunif].
  intros n ? ->.
  apply Rcoupl_dret.
  eauto.
Qed.

(** * rand(N, α1) ~ rand(N, α2) coupling, "wrong" N *)
Lemma Rcoupl_rand_lbl_rand_lbl_wrong N M f `{Bij (fin (S N)) (fin (S N)) f} α1 α2 z σ1 σ2 xs ys :
  σ1.(tapes) !! α1 = Some (M; xs) →
  σ2.(tapes) !! α2 = Some (M; ys) →
  N ≠ M →
  N = Z.to_nat z →
  Rcoupl
    (prim_step (rand #z from #lbl:α1) σ1)
    (prim_step (rand #z from #lbl:α2) σ2)
    (λ ρ2 ρ2', ∃ (n : fin (S N)),
        ρ2 = (Val #n, σ1) ∧ ρ2' = (Val #(f n), σ2)).
Proof.
  intros Hσ1 Hσ2 Hneq Hz.
  rewrite head_prim_step_eq /=; last first.
  { eexists (Val #0%fin, σ1). eapply head_step_support_equiv_rel.
    by eapply RandTapeOtherS. }
  rewrite head_prim_step_eq /=; last first.
  { eexists (Val #0%fin, σ2). eapply head_step_support_equiv_rel.
    by eapply RandTapeOtherS. }
  rewrite /dmap -Hz Hσ1 Hσ2.
  rewrite bool_decide_eq_false_2 //.
  eapply Rcoupl_dbind; [|by eapply Rcoupl_dunif].
  intros n ? ->.
  apply Rcoupl_dret.
  eauto.
Qed.

(** * rand(N,α) ~ rand(N) coupling, "wrong" N *)
Lemma Rcoupl_rand_lbl_rand_wrong N M f `{Bij (fin (S N)) (fin (S N)) f} α1 z σ1 σ2 xs :
  σ1.(tapes) !! α1 = Some (M; xs) →
  N ≠ M →
  N = Z.to_nat z →
  Rcoupl
    (prim_step (rand #z from #lbl:α1) σ1)
    (prim_step (rand #z from #()) σ2)
    (λ ρ2 ρ2', ∃ (n : fin (S N)),
        ρ2 = (Val #n, σ1) ∧ ρ2' = (Val #(f n), σ2)).
Proof.
  intros Hσ1 Hneq Hz.
  rewrite head_prim_step_eq /=; last first.
  { eexists (Val #0%fin, σ1). eapply head_step_support_equiv_rel.
    by eapply RandTapeOtherS. }
  rewrite head_prim_step_eq /=; last first.
  { eexists (Val #0%fin, σ2). eapply head_step_support_equiv_rel.
    by eapply RandNoTapeS. }
  rewrite /dmap -Hz Hσ1.
  rewrite bool_decide_eq_false_2 //.
  eapply Rcoupl_dbind; [|by eapply Rcoupl_dunif].
  intros n ? ->.
  apply Rcoupl_dret.
  eauto.
Qed.

(** * rand(N) ~ rand(N, α) coupling, "wrong" N *)
Lemma Rcoupl_rand_rand_lbl_wrong N M f `{Bij (fin (S N)) (fin (S N)) f} α2 z σ1 σ2 ys :
  σ2.(tapes) !! α2 = Some (M; ys) →
  N ≠ M →
  N = Z.to_nat z →
  Rcoupl
    (prim_step (rand #z from #()) σ1)
    (prim_step (rand #z from #lbl:α2) σ2)
    (λ ρ2 ρ2', ∃ (n : fin (S N)),
        ρ2 = (Val #n, σ1) ∧ ρ2' = (Val #(f n), σ2)).
Proof.
  intros Hσ2 Hneq Hz.
  rewrite head_prim_step_eq /=; last first.
  { eexists (Val #0%fin, σ1). eapply head_step_support_equiv_rel.
    by eapply RandNoTapeS. }
  rewrite head_prim_step_eq /=; last first.
  { eexists (Val #0%fin, σ2). eapply head_step_support_equiv_rel.
    by eapply RandTapeOtherS. }
  rewrite /dmap -Hz Hσ2.
  rewrite bool_decide_eq_false_2 //.
  eapply Rcoupl_dbind; [|by eapply Rcoupl_dunif].
  intros n ? ->.
  apply Rcoupl_dret.
  eauto.
Qed.

(** * state_step(α, N) ~ state_step(α', N) coupling *)
Lemma Rcoupl_state_state N f `{Bij (fin (S N)) (fin (S N)) f} σ1 σ2 α1 α2 xs ys :
  σ1.(tapes) !! α1 = Some (N; xs) →
  σ2.(tapes) !! α2 = Some (N; ys) →
  Rcoupl
    (state_step σ1 α1)
    (state_step σ2 α2)
    (λ σ1' σ2', ∃ (n : fin (S N)),
        σ1' = state_upd_tapes <[α1 := (N; xs ++ [n])]> σ1 ∧
        σ2' = state_upd_tapes <[α2 := (N; ys ++ [f n])]> σ2).
Proof.
  intros Hα1 Hα2.
  rewrite /state_step.
  do 2 (rewrite bool_decide_eq_true_2; [|by eapply elem_of_dom_2]).
  rewrite (lookup_total_correct _ _ _ Hα1).
  rewrite (lookup_total_correct _ _ _ Hα2).
  eapply Rcoupl_dbind; [|by apply Rcoupl_dunif].
  intros n ? ->.
  apply Rcoupl_dret. eauto.
Qed.

(** * Generalized state_step(α) ~ state_step(α') coupling *)
Lemma Rcoupl_state_step_gen (m1 m2 : nat) (R : fin (S m1) -> fin (S m2) -> Prop) σ1 σ2 α1 α2 xs ys :
  σ1.(tapes) !! α1 = Some (m1; xs) →
  σ2.(tapes) !! α2 = Some (m2; ys) →
  Rcoupl (dunif (S m1)) (dunif (S m2)) R →
  Rcoupl
    (state_step σ1 α1)
    (state_step σ2 α2)
    (λ σ1' σ2', ∃ (n1 : fin (S m1)) (n2 : fin (S m2)),
        R n1 n2 ∧
        σ1' = state_upd_tapes <[α1 := (m1; xs ++ [n1])]> σ1 ∧
        σ2' = state_upd_tapes <[α2 := (m2; ys ++ [n2])]> σ2).
Proof.
  intros Hα1 Hα2 Hcoupl.
  apply Rcoupl_pos_R in Hcoupl.
  rewrite /state_step.
  pose proof (elem_of_dom_2 _ _ _ Hα1) as Hdom1.
  pose proof (elem_of_dom_2 _ _ _ Hα2) as Hdom2.
  rewrite bool_decide_eq_true_2; auto.
  rewrite bool_decide_eq_true_2; auto.
  rewrite (lookup_total_correct _ _ _ Hα1).
  rewrite (lookup_total_correct _ _ _ Hα2).
  rewrite /dmap.
  eapply Rcoupl_dbind; [ | apply Hcoupl ]; simpl.
  intros a b (Hab & HposA & HposB).
  rewrite /pmf/dunif/= in HposA.
  rewrite /pmf/dunif/= in HposB.
  apply Rcoupl_dret.
  exists a. exists b. split; try split; auto.
Qed.

(** * rand(unit, N) ~ state_step(α', N) coupling *)
Lemma Rcoupl_rand_state N f `{Bij (fin (S N)) (fin (S N)) f} z σ1 σ1' α' xs:
  N = Z.to_nat z →
  σ1'.(tapes) !! α' = Some (N; xs) →
  Rcoupl
    (prim_step (rand #z from #()) σ1)
    (state_step σ1' α')
    (λ ρ2 σ2', ∃ (n : fin (S N)),
        ρ2 = (Val #n, σ1) ∧ σ2' = state_upd_tapes <[α' := (N; xs ++ [f n])]> σ1').
Proof.
  intros Hz Hα'.
  rewrite head_prim_step_eq /=; last first.
  { eexists (Val #0, σ1). eapply head_step_support_equiv_rel.
    by eapply (RandNoTapeS _ _ 0%fin). }
  rewrite /state_step.
  rewrite bool_decide_eq_true_2; [|by eapply elem_of_dom_2] .
  rewrite -Hz.
  rewrite (lookup_total_correct _ _ _ Hα').
  eapply Rcoupl_dbind; [|by eapply Rcoupl_dunif].
  intros n ? ->.
  apply Rcoupl_dret. eauto.
Qed.

(** * state_step(α, N) ~ rand(unit, N) coupling *)
Lemma Rcoupl_state_rand N f `{Bij (fin (S N)) (fin (S N)) f} z σ1 σ1' α xs :
  N = Z.to_nat z →
  σ1.(tapes) !! α = Some (N; xs) →
  Rcoupl
    (state_step σ1 α)
    (prim_step (rand #z from #()) σ1')
    (λ σ2 ρ2' , ∃ (n : fin (S N)),
        σ2 = state_upd_tapes <[α := (N; xs ++ [n])]> σ1 ∧ ρ2' = (Val #(f n), σ1') ).
Proof.
  intros Hz Hα.
  rewrite head_prim_step_eq /=; last first.
  { eexists (Val #0, σ1'). eapply head_step_support_equiv_rel.
    by eapply (RandNoTapeS _ _ 0%fin). }
  rewrite /state_step.
  rewrite bool_decide_eq_true_2; [ |by eapply elem_of_dom_2] .
  rewrite -Hz.
  rewrite (lookup_total_correct _ _ _ Hα).
  eapply Rcoupl_dbind; [ |by eapply Rcoupl_dunif].
  intros n ? ->.
  apply Rcoupl_dret. eauto.
Qed.

Lemma Rcoupl_rand_r N z (ρ1 : cfg) σ1' :
  N = Z.to_nat z →
  Rcoupl
    (dret ρ1)
    (prim_step (rand #z from #()) σ1')
    (λ ρ2 ρ2', ∃ (n : fin (S N)), ρ2 = ρ1 ∧ ρ2' = (Val #n, σ1')).
Proof.
  intros ?.
  assert (head_reducible (rand #z from #()) σ1') as hr.
  { eexists (_, _).
    apply head_step_support_equiv_rel.
    by apply (RandNoTapeS _ N 0%fin). }
  rewrite head_prim_step_eq //.
  eapply Rcoupl_mono.
  - apply Rcoupl_pos_R, Rcoupl_trivial.
    all : auto using dret_mass, head_step_mass.
  - intros ? [] (_ & hh%dret_pos & ?).
    inv_head_step; eauto.
Qed.

(** * e1 ~ rand(α', N) coupling for α' ↪ₛ (N, []) *)
Lemma Rcoupl_rand_empty_r N z (ρ1 : cfg) σ1' α' :
  N = Z.to_nat z →
  tapes σ1' !! α' = Some (N; []) →
  Rcoupl
    (dret ρ1)
    (prim_step (rand #z from #lbl:α') σ1')
    (λ ρ2 ρ2', ∃ (n : fin (S N)), ρ2 = ρ1 ∧ ρ2' = (Val #n, σ1')).
Proof.
  intros ??.
  assert (head_reducible (rand #z from #lbl:α') σ1') as hr.
  { eexists (_, _).
    apply head_step_support_equiv_rel.
    by apply (RandTapeEmptyS _ _ N 0%fin). }
  rewrite head_prim_step_eq //.
  eapply Rcoupl_mono.
  - apply Rcoupl_pos_R, Rcoupl_trivial.
    all : auto using dret_mass, head_step_mass.
  - intros ? [] (_ & hh%dret_pos & ?).
    inv_head_step; eauto.
Qed.

Lemma Rcoupl_rand_wrong_r N M z ns (ρ1 : cfg) σ1' α' :
  N = Z.to_nat z →
  N ≠ M →
  tapes σ1' !! α' = Some (M; ns) →
  Rcoupl
    (dret ρ1)
    (prim_step (rand #z from #lbl:α') σ1')
    (λ ρ2 ρ2', ∃ (n : fin (S N)), ρ2 = ρ1 ∧ ρ2' = (Val #n, σ1')).
Proof.
  intros ???.
  assert (head_reducible (rand #z from #lbl:α') σ1') as hr.
  { eexists (_, _).
    apply head_step_support_equiv_rel.
    by apply (RandTapeOtherS _ _ M N ns 0%fin). }
  rewrite head_prim_step_eq //.
  eapply Rcoupl_mono.
  - apply Rcoupl_pos_R, Rcoupl_trivial.
    all : auto using dret_mass, head_step_mass.
  - intros ? [] (_ & hh%dret_pos & ?).
    inv_head_step; eauto.
Qed.


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
| AllocDS v σ l :
  l = fresh_loc σ.(heap) →
  det_head_step_rel (Alloc (Val v)) σ
    (Val $ LitV $ LitLoc l) (state_upd_heap <[l:=v]> σ)
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
| AllocDSP v σ l :
  l = fresh_loc σ.(heap) →
  det_head_step_pred (Alloc (Val v)) σ
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
  | If (Val (LitV (LitBool true))) e1 e2 => true
  | If (Val (LitV (LitBool false))) e1 e2 => true
  | Fst (Val (PairV v1 v2)) => true
  | Snd (Val (PairV v1 v2)) => true
  | Case (Val (InjLV v)) e1 e2 => true
  | Case (Val (InjRV v)) e1 e2 => true
  | Alloc (Val v) => true
  | Load (Val (LitV (LitLoc l)))  =>
      bool_decide (is_Some (σ1.(heap) !! l))
  | Store (Val (LitV (LitLoc l))) (Val w) =>
      bool_decide (is_Some (σ1.(heap) !! l))
  | _ => false
  end.

Lemma det_step_eq_tapes e1 σ1 e2 σ2 :
  det_head_step_rel e1 σ1 e2 σ2 → σ1.(tapes) = σ2.(tapes).
Proof. inversion 1; auto. Qed.

Inductive prob_head_step_pred : expr -> state -> Prop :=
| AllocTapePSP σ N z :
  N = Z.to_nat z →
  prob_head_step_pred (alloc #z) σ
| RandTapePSP α σ N n ns z :
  N = Z.to_nat z →
  σ.(tapes) !! α = Some ((N; n :: ns) : tape) →
  prob_head_step_pred (rand #z from #lbl:α) σ
| RandEmptyPSP N α σ z :
  N = Z.to_nat z →
  σ.(tapes) !! α = Some ((N; []) : tape) →
  prob_head_step_pred (rand #z from #lbl:α) σ
| RandTapeOtherPSP N M α σ ns z :
  N ≠ M →
  M = Z.to_nat z →
  σ.(tapes) !! α = Some ((N; ns) : tape) →
  prob_head_step_pred (rand #z from #lbl:α) σ
| RandNoTapePSP (N : nat) σ z :
  N = Z.to_nat z →
  prob_head_step_pred (rand #z from #()) σ.

Definition head_step_pred e1 σ1 :=
  det_head_step_pred e1 σ1 ∨ prob_head_step_pred e1 σ1.

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

Local Ltac solve_step_det :=
  rewrite /pmf /=;
    repeat (rewrite bool_decide_eq_true_2 // || case_match);
  try (lra || done).

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
  - inversion H; solve_step_det.
Qed.

Lemma det_head_step_singleton e1 σ1 e2 σ2 :
  det_head_step_rel e1 σ1 e2 σ2 → head_step e1 σ1 = dret (e2, σ2).
Proof.
  intros Hdet.
  apply pmf_1_eq_dret.
  inversion Hdet; simplify_eq/=; try case_match;
    simplify_option_eq; rewrite ?dret_1_1 //.
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
      inversion Hdet; simplify_eq; do 2 eexists; try (by econstructor).
    Unshelve. all : apply 0%fin.
  - intros (?&?& H). inversion H; simplify_eq;
      (try by (left; econstructor));
      (try by (right; econstructor)).
    right. by eapply RandTapeOtherPSP; [|done|done].
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
  - pose proof (pmf_SeriesC_ge_0 (head_step e1 σ1)); lra.
  - apply SeriesC_zero_dzero in HZ. eauto.
Qed.

Lemma head_step_dzero_upd_tapes α e σ N zs z  :
  α ∈ dom σ.(tapes) →
  head_step e σ = dzero →
  head_step e (state_upd_tapes <[α:=(N; zs ++ [z]) : tape]> σ) = dzero.
Proof.
  intros Hdom Hz.
  destruct e; simpl in *;
    repeat case_match; done || inv_dzero; simplify_map_eq.
  (* TODO: [simplify_map_eq] should solve this? *)
  - destruct (decide (α = l1)).
    + simplify_eq.
      by apply not_elem_of_dom_2 in H5.
    + rewrite lookup_insert_ne // in H6.
      rewrite H5 in H6. done.
  - destruct (decide (α = l1)).
    + simplify_eq.
      by apply not_elem_of_dom_2 in H5.
    + rewrite lookup_insert_ne // in H6.
      rewrite H5 in H6. done.
  - destruct (decide (α = l1)).
    + simplify_eq.
      by apply not_elem_of_dom_2 in H5.
    + rewrite lookup_insert_ne // in H6.
      rewrite H5 in H6. done.
Qed.

Lemma det_head_step_upd_tapes N e1 σ1 e2 σ2 α z zs :
  det_head_step_rel e1 σ1 e2 σ2 →
  tapes σ1 !! α = Some (N; zs) →
  det_head_step_rel
    e1 (state_upd_tapes <[α := (N; zs ++ [z])]> σ1)
    e2 (state_upd_tapes <[α := (N; zs ++ [z])]> σ2).
Proof. inversion 1; econstructor; eauto. Qed.

Lemma upd_tape_some σ α N n ns :
  tapes σ !! α = Some (N; ns) →
  tapes (state_upd_tapes <[α:= (N; ns ++ [n])]> σ) !! α = Some (N; ns ++ [n]).
Proof.
  intros H. rewrite /state_upd_tapes /=. rewrite lookup_insert //.
Qed.

Lemma upd_tape_some_trivial σ α bs:
  tapes σ !! α = Some bs →
  state_upd_tapes <[α:=tapes σ !!! α]> σ = σ.
Proof.
  destruct σ. simpl.
  intros H.
  rewrite (lookup_total_correct _ _ _ H).
  f_equal.
  by apply insert_id.
Qed.

Lemma upd_diff_tape_comm σ α β bs bs':
  α ≠ β →
  state_upd_tapes <[β:= bs]> (state_upd_tapes <[α := bs']> σ) =
    state_upd_tapes <[α:= bs']> (state_upd_tapes <[β := bs]> σ).
Proof.
  intros. rewrite /state_upd_tapes /=. rewrite insert_commute //.
Qed.

Lemma upd_diff_tape_tot σ α β bs:
  α ≠ β →
  tapes σ !!! α = tapes (state_upd_tapes <[β:=bs]> σ) !!! α.
Proof. symmetry ; by rewrite lookup_total_insert_ne. Qed.

Lemma upd_tape_twice σ β bs bs' :
  state_upd_tapes <[β:= bs]> (state_upd_tapes <[β:= bs']> σ) = state_upd_tapes <[β:= bs]> σ.
Proof. rewrite /state_upd_tapes insert_insert //. Qed.

Lemma fresh_loc_upd_some σ α bs bs' :
  (tapes σ) !! α = Some bs →
  fresh_loc (tapes σ) = (fresh_loc (<[α:= bs']> (tapes σ))).
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
  (tapes σ) !! α = Some bs →
  state_upd_tapes <[fresh_loc (tapes σ):=bs']> (state_upd_tapes <[α:=bs'']> σ)
  = state_upd_tapes <[α:=bs'']> (state_upd_tapes <[fresh_loc (tapes σ):=bs']> σ).
Proof.
  intros H.
  apply elem_fresh_ne in H.
  unfold state_upd_tapes.
  by rewrite insert_commute.
Qed.

Lemma fresh_loc_lookup σ α bs bs' :
  (tapes σ) !! α = Some bs →
  (tapes (state_upd_tapes <[fresh_loc (tapes σ):=bs']> σ)) !! α = Some bs.
Proof.
  intros H.
  pose proof (elem_fresh_ne _ _ _ H).
  by rewrite lookup_insert_ne.
Qed.
