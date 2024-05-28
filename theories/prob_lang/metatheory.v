From Coq Require Import Reals Psatz.
From stdpp Require Import functions gmap stringmap fin_sets.
From clutch.prelude Require Import stdpp_ext NNRbar fin.
From clutch.prob Require Import distribution couplings couplings_app.
From clutch.common Require Import ectx_language.
From clutch.prob_lang Require Import locations tactics notation.
From clutch.prob_lang Require Export lang.
From clutch.prob Require Import distribution couplings.
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
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Load e =>
     is_closed_expr X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | AllocN e1 e2 | Store e1 e2 | Rand e1 e2 =>
     is_closed_expr X e1 && is_closed_expr X e2
  | If e0 e1 e2 | Case e0 e1 e2 =>
     is_closed_expr X e0 && is_closed_expr X e1 && is_closed_expr X e2
  | AllocTape e => is_closed_expr X e
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
  | Load e => Load (subst_map vs e)
  | Store e1 e2 => Store (subst_map vs e1) (subst_map vs e2)
  | AllocTape e => AllocTape (subst_map vs e)
  | Rand e1 e2 => Rand (subst_map vs e1) (subst_map vs e2)
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


(** * rand(N) ~ rand(N) coupling *)
Lemma Rcoupl_rand_rand N f `{Bij (fin (S N)) (fin (S N)) f} z σ1 σ1' :
  N = Z.to_nat z →
  Rcoupl
    (prim_step (rand #z) σ1)
    (prim_step (rand #z) σ1')
    (λ ρ2 ρ2', ∃ (n : fin (S N)),
        ρ2 = (Val #n, σ1) ∧ ρ2' = (Val #(f n), σ1')).
Proof.
  intros Hz.
  rewrite head_prim_step_eq /=.
  rewrite head_prim_step_eq /=.
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
    (prim_step (rand(#lbl:α1) #z) σ1)
    (prim_step (rand(#lbl:α2) #z) σ2)
    (λ ρ2 ρ2', ∃ (n : fin (S N)),
        ρ2 = (Val #n, σ1) ∧ ρ2' = (Val #(f n), σ2)).
Proof.
  intros Hσ1 Hσ2 Hneq Hz.
  rewrite ?head_prim_step_eq /=.
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
    (prim_step (rand(#lbl:α1) #z) σ1)
    (prim_step (rand #z) σ2)
    (λ ρ2 ρ2', ∃ (n : fin (S N)),
        ρ2 = (Val #n, σ1) ∧ ρ2' = (Val #(f n), σ2)).
Proof.
  intros Hσ1 Hneq Hz.
  rewrite ?head_prim_step_eq /=.
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
    (prim_step (rand #z) σ1)
    (prim_step (rand(#lbl:α2) #z) σ2)
    (λ ρ2 ρ2', ∃ (n : fin (S N)),
        ρ2 = (Val #n, σ1) ∧ ρ2' = (Val #(f n), σ2)).
Proof.
  intros Hσ2 Hneq Hz.
  rewrite ?head_prim_step_eq /=.
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
    (prim_step (rand #z) σ1)
    (state_step σ1' α')
    (λ ρ2 σ2', ∃ (n : fin (S N)),
        ρ2 = (Val #n, σ1) ∧ σ2' = state_upd_tapes <[α' := (N; xs ++ [f n])]> σ1').
Proof.
  intros Hz Hα'.
  rewrite head_prim_step_eq /=.
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
    (prim_step (rand #z) σ1')
    (λ σ2 ρ2' , ∃ (n : fin (S N)),
        σ2 = state_upd_tapes <[α := (N; xs ++ [n])]> σ1 ∧ ρ2' = (Val #(f n), σ1') ).
Proof.
  intros Hz Hα.
  rewrite head_prim_step_eq /=.
  rewrite /state_step.
  rewrite bool_decide_eq_true_2; [ |by eapply elem_of_dom_2] .
  rewrite -Hz.
  rewrite (lookup_total_correct _ _ _ Hα).
  eapply Rcoupl_dbind; [ |by eapply Rcoupl_dunif].
  intros n ? ->.
  apply Rcoupl_dret. eauto.
Qed.

Lemma Rcoupl_rand_r `{Countable A} N z (a : A) σ1' :
  N = Z.to_nat z →
  Rcoupl
    (dret a)
    (prim_step (rand #z) σ1')
    (λ a' ρ2', ∃ (n : fin (S N)), a' = a ∧ ρ2' = (Val #n, σ1')).
Proof.
  intros ?.
  assert (head_reducible (rand #z) σ1') as hr by solve_red.
  rewrite head_prim_step_eq //.
  eapply Rcoupl_mono.
  - apply Rcoupl_pos_R, Rcoupl_trivial.
    all : auto using dret_mass, head_step_mass.
  - intros ? [] (_ & hh%dret_pos & ?).
    inv_head_step; eauto.
Qed.

(** * e1 ~ rand(α', N) coupling for α' ↪ₛ (N, []) *)
Lemma Rcoupl_rand_empty_r `{Countable A} N z (a : A) σ1' α' :
  N = Z.to_nat z →
  tapes σ1' !! α' = Some (N; []) →
  Rcoupl
    (dret a)
    (prim_step (rand(#lbl:α') #z) σ1')
    (λ a' ρ2', ∃ (n : fin (S N)), a' = a ∧ ρ2' = (Val #n, σ1')).
Proof.
  intros ??.
  assert (head_reducible (rand(#lbl:α') #z) σ1') as hr by solve_red.
  rewrite head_prim_step_eq //.
  eapply Rcoupl_mono.
  - apply Rcoupl_pos_R, Rcoupl_trivial.
    all : auto using dret_mass, head_step_mass.
  - intros ? [] (_ & hh%dret_pos & ?).
    inv_head_step; eauto.
Qed.

Lemma Rcoupl_rand_wrong_r `{Countable A} N M z (a : A) ns σ1' α' :
  N = Z.to_nat z →
  N ≠ M →
  tapes σ1' !! α' = Some (M; ns) →
  Rcoupl
    (dret a)
    (prim_step (rand(#lbl:α') #z) σ1')
    (λ a' ρ2', ∃ (n : fin (S N)), a' = a ∧ ρ2' = (Val #n, σ1')).
Proof.
  intros ???.
  assert (head_reducible (rand(#lbl:α') #z) σ1') as hr by solve_red.
  rewrite head_prim_step_eq //.
  eapply Rcoupl_mono.
  - apply Rcoupl_pos_R, Rcoupl_trivial.
    all : auto using dret_mass, head_step_mass.
  - intros ? [] (_ & hh%dret_pos & ?).
    inv_head_step; eauto.
Qed.

Lemma S_INR_le_compat (N M : nat) :
  (N <= M)%R ->
  (0 < S N <= S M)%R.
Proof.
  split; [| do 2 rewrite S_INR; lra ].
  rewrite S_INR.
  apply Rplus_le_lt_0_compat; [ apply pos_INR | lra].
Qed.

(** * Approximate rand(N) ~ rand(M) coupling, N <= M *)
Lemma ARcoupl_rand_rand (N M : nat) z w σ1 σ1' (ε : nonnegreal) :
  (N <= M)%R ->
  (((S M - S N) / S M) = ε)%R →
  N = Z.to_nat z →
  M = Z.to_nat w →
  ARcoupl
    (prim_step (rand #z) σ1)
    (prim_step (rand #w) σ1')
    (λ ρ2 ρ2', ∃ (n : fin (S N)) (m : fin (S M)),
        (fin_to_nat n = m) ∧
        ρ2 = (Val #n, σ1) ∧ ρ2' = (Val #m, σ1'))
   ε.
Proof.
  intros NMpos NMε Hz Hw.
  rewrite ?head_prim_step_eq /=.
  rewrite /dmap -Hz -Hw.
  replace ε with (nnreal_plus ε nnreal_zero); last first.
  { apply nnreal_ext; simpl; lra. }
  eapply ARcoupl_dbind.
  1,2: apply cond_nonneg.
  2 : {
    rewrite -NMε.
    by eapply ARcoupl_dunif_leq, S_INR_le_compat.
  }
  intros n m Hnm.
  apply ARcoupl_dret.
  exists n . exists m.
  by rewrite Hnm //.
Qed.

(** * Approximate rand(N) ~ rand(M) coupling, N <= M, along an injection *)
Lemma ARcoupl_rand_rand_inj (N M : nat) f `{Inj (fin (S N)) (fin (S M)) (=) (=) f} z w σ1 σ1' (ε : nonnegreal) :
  (N <= M)%R ->
  (((S M - S N) / S M) = ε)%R →
  N = Z.to_nat z →
  M = Z.to_nat w →
  ARcoupl
    (prim_step (rand #z) σ1)
    (prim_step (rand #w) σ1')
    (λ ρ2 ρ2', ∃ (n : fin (S N)),
        ρ2 = (Val #n, σ1) ∧ ρ2' = (Val #(f n), σ1'))
   ε.
Proof.
  intros NMpos NMε Hz Hw.
  rewrite ?head_prim_step_eq /=.
  rewrite /dmap -Hz -Hw.
  replace ε with (nnreal_plus ε nnreal_zero); last first.
  { apply nnreal_ext; simpl; lra. }
  eapply ARcoupl_dbind.
  1,2: apply cond_nonneg.
  2 : {
    rewrite -NMε.
    eapply ARcoupl_dunif_leq_inj; eauto.
    by apply S_INR_le_compat.
  }
  intros n m Hnm.
  apply ARcoupl_dret.
  exists n .
  by rewrite Hnm //.
Qed.

(** * Approximate rand(N) ~ rand(M) coupling, M <= N *)
Lemma ARcoupl_rand_rand_rev (N M : nat) z w σ1 σ1' (ε : nonnegreal) :
  (M <= N)%R ->
  (((S N - S M) / S N) = ε)%R →
  N = Z.to_nat z →
  M = Z.to_nat w →
  ARcoupl
    (prim_step (rand #z) σ1)
    (prim_step (rand #w) σ1')
    (λ ρ2 ρ2', ∃ (n : fin (S N)) (m : fin (S M)),
        (fin_to_nat n = m) ∧
        ρ2 = (Val #n, σ1) ∧ ρ2' = (Val #m, σ1'))
   ε.
Proof.
  intros NMpos NMε Hz Hw.
  rewrite ?head_prim_step_eq /=.
  rewrite /dmap -Hz -Hw.
  replace ε with (nnreal_plus ε nnreal_zero); last first.
  { apply nnreal_ext; simpl; lra. }
  eapply ARcoupl_dbind.
  1,2: apply cond_nonneg.
  2 : {
    rewrite -NMε.
    by eapply ARcoupl_dunif_leq_rev, S_INR_le_compat.
  }
  intros n m Hnm.
  apply ARcoupl_dret.
  exists n . exists m.
  by rewrite Hnm //.
Qed.


(** * Approximate rand(N) ~ rand(M) coupling, M <= N, along an injection *)
Lemma ARcoupl_rand_rand_rev_inj (N M : nat) f `{Inj (fin (S M)) (fin (S N)) (=) (=) f} z w σ1 σ1' (ε : nonnegreal) :
  (M <= N)%R ->
  (((S N - S M) / S N) = ε)%R →
  N = Z.to_nat z →
  M = Z.to_nat w →
  ARcoupl
    (prim_step (rand #z) σ1)
    (prim_step (rand #w) σ1')
    (λ ρ2 ρ2', ∃ (m : fin (S M)),
        ρ2 = (Val #(f m), σ1) ∧ ρ2' = (Val #m, σ1'))
   ε.
Proof.
  intros NMpos NMε Hz Hw.
  rewrite ?head_prim_step_eq /=.
  rewrite /dmap -Hz -Hw.
  replace ε with (nnreal_plus ε nnreal_zero); last first.
  { apply nnreal_ext; simpl; lra. }
  eapply ARcoupl_dbind.
  1,2: apply cond_nonneg.
  2 : {
    rewrite -NMε.
    by eapply ARcoupl_dunif_leq_rev_inj, S_INR_le_compat.
  }
  intros n m Hnm.
  apply ARcoupl_dret.
  exists m.
  by rewrite Hnm //.
Qed.


(** * Approximate state_step(α, N) ~ state_step(α', N) coupling *)
Lemma ARcoupl_state_state (N M : nat) σ1 σ2 α1 α2 xs ys (ε : nonnegreal) :
  (N <= M)%R ->
  (((S M - S N) / S M) = ε)%R →
  σ1.(tapes) !! α1 = Some (N; xs) →
  σ2.(tapes) !! α2 = Some (M; ys) →
  ARcoupl
    (state_step σ1 α1)
    (state_step σ2 α2)
    (λ σ1' σ2', ∃ (n : fin (S N)) (m : fin (S M)),
        (fin_to_nat n = m) ∧
        σ1' = state_upd_tapes <[α1 := (N; xs ++ [n])]> σ1 ∧
        σ2' = state_upd_tapes <[α2 := (M; ys ++ [m])]> σ2)
    ε.
Proof.
  intros NMpos NMε Hα1 Hα2.
  rewrite /state_step.
  do 2 (rewrite bool_decide_eq_true_2; [|by eapply elem_of_dom_2]).
  rewrite (lookup_total_correct _ _ _ Hα1).
  rewrite (lookup_total_correct _ _ _ Hα2).
  replace ε with (nnreal_plus ε nnreal_zero); last first.
  { apply nnreal_ext; simpl; lra. }
  unshelve eapply ARcoupl_dbind.
  { exact (λ (n : fin (S N)) (m : fin (S M)), fin_to_nat n = m). }
  { destruct ε ; done. } { simpl ; lra. }
  2: { rewrite -NMε. by apply ARcoupl_dunif_leq, S_INR_le_compat. }
  intros n m nm.
  apply ARcoupl_dret.
  simpl in nm. eauto.
Qed.

Lemma ARcoupl_state_state_rev (N M : nat) σ1 σ2 α1 α2 xs ys (ε : nonnegreal) :
  (M <= N)%R ->
  (((S N - S M) / S N) = ε)%R →
  σ1.(tapes) !! α1 = Some (N; xs) →
  σ2.(tapes) !! α2 = Some (M; ys) →
  ARcoupl
    (state_step σ1 α1)
    (state_step σ2 α2)
    (λ σ1' σ2', ∃ (n : fin (S N)) (m : fin (S M)),
        (fin_to_nat n = m) ∧
        σ1' = state_upd_tapes <[α1 := (N; xs ++ [n])]> σ1 ∧
        σ2' = state_upd_tapes <[α2 := (M; ys ++ [m])]> σ2)
    ε.
Proof.
  intros NMpos NMε Hα1 Hα2.
  rewrite /state_step.
  do 2 (rewrite bool_decide_eq_true_2; [|by eapply elem_of_dom_2]).
  rewrite (lookup_total_correct _ _ _ Hα1).
  rewrite (lookup_total_correct _ _ _ Hα2).
  replace ε with (nnreal_plus ε nnreal_zero); last first.
  { apply nnreal_ext; simpl; lra. }
  unshelve eapply ARcoupl_dbind.
  { exact (λ (n : fin (S N)) (m : fin (S M)), fin_to_nat n = m). }
  { destruct ε ; done. } { simpl ; lra. }
  2: { rewrite -NMε. by apply ARcoupl_dunif_leq_rev, S_INR_le_compat. }
  intros n m nm.
  apply ARcoupl_dret.
  simpl in nm. eauto.
Qed.

Lemma ARcoupl_rand_r `{Countable A} (a : A) N z σ1' :
  N = Z.to_nat z →
  ARcoupl
    (dret a)
    (prim_step (rand #z) σ1')
    (λ a' ρ2', ∃ (n : fin (S N)), a' = a ∧ ρ2' = (Val #n, σ1')) (nnreal_zero).
Proof.
  intros ?.
  apply ARcoupl_exact.
  by apply Rcoupl_rand_r.
Qed.

Lemma ARcoupl_rand_empty_r `{Countable A} N z (a : A) σ1' α' :
  N = Z.to_nat z →
  tapes σ1' !! α' = Some (N; []) →
  ARcoupl
    (dret a)
    (prim_step (rand(#lbl:α') #z) σ1')
    (λ a' ρ2', ∃ (n : fin (S N)), a' = a ∧ ρ2' = (Val #n, σ1')) (nnreal_zero).
Proof.
  intros ??.
  apply ARcoupl_exact.
  by apply Rcoupl_rand_empty_r.
Qed.

Lemma ARcoupl_rand_wrong_r `{Countable A} N M z ns (a : A) σ1' α' :
  N = Z.to_nat z →
  N ≠ M →
  tapes σ1' !! α' = Some (M; ns) →
  ARcoupl
    (dret a)
    (prim_step (rand(#lbl:α') #z) σ1')
    (λ a' ρ2', ∃ (n : fin (S N)), a' = a ∧ ρ2' = (Val #n, σ1')) (nnreal_zero).
Proof.
  intros ???.
  apply ARcoupl_exact.
  eapply Rcoupl_rand_wrong_r; eauto.
Qed.

Lemma wp_couple_rand_no_coll_l N z (σ : state) (ρₛ1 : cfg) (x : Fin.t (S N)) (ε : nonnegreal) :
  (0 < S N)%R →
  ((1 / S N) = ε)%R →
  N = Z.to_nat z →
  ARcoupl
    (prim_step (rand #z) σ)
    (dret ρₛ1)
    (λ ρ ρₛ2, ∃ n : fin (S N),
        ρ = (Val #n, σ) ∧ (n ≠ x) ∧ ρₛ2 = ρₛ1)
    ε.
Proof.
  intros Npos Nε Nz.
  rewrite head_prim_step_eq /=.
  rewrite -Nz.
  rewrite -(dmap_dret (λ x, x) _) /dmap.
  replace ε with (ε + nnreal_zero)%NNR by (apply nnreal_ext ; simpl ; lra).
  eapply ARcoupl_dbind ; [destruct ε ; done | simpl ; lra |..].
  2: rewrite -Nε ; apply (ARcoupl_dunif_no_coll_l _ _ x Npos).
  move => n ? [xn ->]. apply ARcoupl_dret.
  exists n. auto.
Qed.

Lemma wp_couple_rand_no_coll_r N z (σₛ : state) (ρ1 : cfg) (x : Fin.t (S N)) (ε : nonnegreal) :
  (0 < S N)%R →
  ((1 / S N) = ε)%R →
  N = Z.to_nat z →
  ARcoupl
    (dret ρ1)
    (prim_step (rand #z) σₛ)
    (λ ρ2 ρₛ, ∃ n : fin (S N),
        ρ2 = ρ1 ∧ ρₛ = (Val #n, σₛ) ∧ (n ≠ x))
    ε.
Proof.
  intros Npos Nε Nz.
  rewrite head_prim_step_eq /=.
  rewrite -Nz.
  rewrite -(dmap_dret (λ x, x) _).
  rewrite /dmap.
  replace ε with (nnreal_plus ε nnreal_zero) by (apply nnreal_ext ; simpl ; lra).
  eapply ARcoupl_dbind ; [destruct ε ; done | simpl ; lra |..].
  2: rewrite -Nε ; apply (ARcoupl_dunif_no_coll_r _ _ x Npos).
  move => ? n [-> xn]. apply ARcoupl_dret.
  exists n. auto.
Qed.
(** * state_step ~ fair_coin  *)
Lemma state_step_fair_coin_coupl σ α bs :
  σ.(tapes) !! α = Some ((1%nat; bs) : tape) →
  Rcoupl
    (state_step σ α)
    fair_coin
    (λ σ' b, σ' = state_upd_tapes (<[α := (1%nat; bs ++ [bool_to_fin b])]>) σ).
Proof.
  intros Hα.
  exists (dmap (λ b, (state_upd_tapes (<[α := (1%nat; bs ++ [bool_to_fin b]) : tape]>) σ, b)) fair_coin).
  repeat split.
  - rewrite /lmarg dmap_comp /state_step.
    rewrite bool_decide_eq_true_2; [|by eapply elem_of_dom_2].
    rewrite lookup_total_alt Hα /=.
    eapply distr_ext=> σ'.
    rewrite /dmap /= /pmf /= /dbind_pmf.
    rewrite SeriesC_bool SeriesC_fin2 /=.
    rewrite {1 3 5 7}/pmf /=.
    destruct (decide (state_upd_tapes <[α:=(1%nat; bs ++ [1%fin])]> σ = σ')); subst.
    + rewrite {1 2}dret_1_1 // dret_0; [lra|].
      intros [= H%(insert_inv (tapes σ))]. simplify_eq.
    + destruct (decide (state_upd_tapes <[α:=(1%nat; bs ++ [0%fin])]> σ = σ')); subst.
      * rewrite {1 2}dret_0 // dret_1_1 //. lra.
      * rewrite !dret_0 //. lra.
  - rewrite /rmarg dmap_comp.
    assert ((snd ∘ (λ b : bool, _)) = Datatypes.id) as -> by f_equal.
    rewrite dmap_id //.
  - by intros [σ' b] (b' & [=-> ->] & ?)%dmap_pos=>/=.
Qed.

(** * state_step ≫= state_step ~ dprod fair_coin fair_coin  *)
Lemma state_steps_fair_coins_coupl (σ : state) (α1 α2 : loc) (bs1 bs2 : list (fin 2)):
  α1 ≠ α2 →
  σ.(tapes) !! α1 = Some ((1%nat; bs1) : tape) →
  σ.(tapes) !! α2 = Some ((1%nat; bs2) : tape) →
  Rcoupl
    (state_step σ α1 ≫= (λ σ', state_step σ' α2))
    (dprod fair_coin fair_coin)
    (λ σ' '(b1, b2),
      σ' = (state_upd_tapes (<[α1 := (1%nat; bs1 ++ [bool_to_fin b1])]>)
              (state_upd_tapes (<[α2 := (1%nat; bs2 ++ [bool_to_fin b2])]>) σ))).
Proof.
  intros Hneq Hα1 Hα2.
  rewrite /dprod.
  rewrite -(dret_id_right (state_step _ _ ≫= _)) -dbind_assoc.
  eapply Rcoupl_dbind; [|by eapply state_step_fair_coin_coupl].
  intros σ' b1 ->.
  eapply Rcoupl_dbind; [|eapply state_step_fair_coin_coupl]; last first.
  { rewrite lookup_insert_ne //. }
  intros σ' b2 ->.
  eapply Rcoupl_dret.
  rewrite /state_upd_tapes insert_commute //.
Qed.

Lemma Rcoupl_state_1_3 σ σₛ α1 α2 αₛ (xs ys:list(fin (2))) (zs:list(fin (4))):
  α1 ≠ α2 -> 
  σ.(tapes) !! α1 = Some (1%nat; xs) ->
  σ.(tapes) !! α2 = Some (1%nat; ys) ->
  σₛ.(tapes) !! αₛ = Some (3%nat; zs) ->
  Rcoupl
      (state_step σ α1 ≫= (λ σ1', state_step σ1' α2))
      (state_step σₛ αₛ)
      (λ σ1' σ2', ∃ (x y:fin 2) (z:fin 4),
          σ1' = state_upd_tapes <[α2 := (1%nat; ys ++ [y])]> (state_upd_tapes <[α1 := (1%nat; xs ++ [x])]> σ) ∧
          σ2' = state_upd_tapes <[αₛ := (3%nat; zs ++ [z])]> σₛ /\
          (2*fin_to_nat x + fin_to_nat y = fin_to_nat z)%nat
      ).
Proof.
  intros Hneq H1 H2 H3.
  rewrite /state_step.
  do 2 (rewrite bool_decide_eq_true_2; [|by eapply elem_of_dom_2]).
  rewrite (lookup_total_correct _ _ _ H1).
  rewrite (lookup_total_correct _ _ _ H3).
  erewrite (dbind_eq _ (λ σ, dmap
    (λ n : fin 2,
       state_upd_tapes <[α2:=(1%nat; ys ++ [n])]> σ)
    (dunifP 1))); last first.
  - done.
  - intros [??] H.
    rewrite dmap_pos in H. destruct H as (?&->&H).
    rewrite bool_decide_eq_true_2; last first.
    { eapply elem_of_dom_2. by rewrite /state_upd_tapes/=lookup_insert_ne. }
    rewrite lookup_total_insert_ne; last done.
    rewrite (lookup_total_correct _ _ _ H2).
    done.
  - pose (witness:=dmap (λ n: fin 4, ( match fin_to_nat n with
                           | 0%nat =>state_upd_tapes <[α2:=(1%nat; ys ++ [0%fin])]>
                                      (state_upd_tapes <[α1:=(1%nat; xs ++ [0%fin])]> σ)
                           | 1%nat =>state_upd_tapes <[α2:=(1%nat; ys ++ [1%fin])]>
                                      (state_upd_tapes <[α1:=(1%nat; xs ++ [0%fin])]> σ)
                           | 2%nat =>state_upd_tapes <[α2:=(1%nat; ys ++ [0%fin])]>
                                      (state_upd_tapes <[α1:=(1%nat; xs ++ [1%fin])]> σ)
                           | 3%nat => state_upd_tapes <[α2:=(1%nat; ys ++ [1%fin])]>
                                   (state_upd_tapes <[α1:=(1%nat; xs ++ [1%fin])]> σ)
                           | _ => σ
                           end 
                           ,state_upd_tapes <[αₛ:=(3%nat; zs ++ [n])]> σₛ)
                      )(dunifP 3)).
    exists witness.
    split; last first.
    + intros [??].
      rewrite /witness dmap_pos.
      intros [?[??]].
      repeat (inv_fin x => x); simpl in *; simplify_eq => _; naive_solver.
    + rewrite /witness. split.
      -- rewrite /lmarg dmap_comp.
         erewrite dmap_eq; last first.
         ** done.
         ** intros ??. simpl. done.
         ** apply distr_ext. intros s.
            (** prove left marginal of witness is correct *)
            rewrite {1}/dmap{1}/dbind/dbind_pmf{1}/pmf.
            etrans; last first.
            { (** simplify the RHS *)
              rewrite /dmap/dbind/dbind_pmf/pmf/=.
              erewrite (SeriesC_ext _ (λ a,
                                         if (bool_decide (a ∈ [state_upd_tapes <[α1:=(1%nat; xs ++ [0%fin])]> σ; state_upd_tapes <[α1:=(1%nat; xs ++ [1%fin])]> σ]))
                                              then 
                                         SeriesC (λ a0 : fin 2, / (1 + 1) * dret_pmf (state_upd_tapes <[α1:=(1%nat; xs ++ [a0])]> σ) a) *
                                           SeriesC (λ a0 : fin 2, / (1 + 1) * dret_pmf (state_upd_tapes <[α2:=(1%nat; ys ++ [a0])]> a) s)
                                         else 0)); first rewrite SeriesC_list/=.
              - by rewrite !SeriesC_finite_foldr/dret_pmf/=. 
              - repeat constructor; last (set_unfold; naive_solver).
                rewrite elem_of_list_singleton. move /state_upd_tapes_same'. done.
              - intros [??].
                case_bool_decide; first done.
                apply Rmult_eq_0_compat_r.
                set_unfold.
                rewrite SeriesC_finite_foldr/dret_pmf/=.
                repeat case_bool_decide; try lra; naive_solver. 
            }
            pose proof state_upd_tapes_same' as K1.
            pose proof state_upd_tapes_neq' as K2.
            case_bool_decide; last done.
            rewrite (bool_decide_eq_false_2 (state_upd_tapes <[α1:=(1%nat; xs ++ [0%fin])]> σ =
                                             state_upd_tapes <[α1:=(1%nat; xs ++ [1%fin])]> σ)); last first.
            { apply K2. done. }
            rewrite (bool_decide_eq_false_2 (state_upd_tapes <[α1:=(1%nat; xs ++ [1%fin])]> σ =
                                             state_upd_tapes <[α1:=(1%nat; xs ++ [0%fin])]> σ)); last first.
            { apply K2. done. }
            rewrite (bool_decide_eq_true_2 (state_upd_tapes <[α1:=(1%nat; xs ++ [1%fin])]> σ =
                                            state_upd_tapes <[α1:=(1%nat; xs ++ [1%fin])]> σ)); last done.
            rewrite !Rmult_0_r.
            rewrite SeriesC_finite_foldr/dunifP /dunif/pmf /=/dret_pmf.
            case_bool_decide.
            { repeat rewrite bool_decide_eq_false_2.
              - lra.
              - subst. intro K. simplify_eq. rewrite map_eq_iff in K.
                specialize (K α2). rewrite !lookup_insert in K. simplify_eq.
              - subst. intro K. simplify_eq. rewrite map_eq_iff in K.
                specialize (K α1). rewrite lookup_insert_ne in K; last done.
                rewrite (lookup_insert_ne (<[_:=_]> _ )) in K; last done.
                rewrite !lookup_insert in K. simplify_eq.
              - subst. intro K. simplify_eq. rewrite map_eq_iff in K.
                specialize (K α2). rewrite !lookup_insert in K. simplify_eq.
            }
            case_bool_decide.
            { repeat rewrite bool_decide_eq_false_2.
              - lra.
              - subst. intro K. simplify_eq. rewrite map_eq_iff in K.
                specialize (K α1). rewrite lookup_insert_ne in K; last done.
                rewrite (lookup_insert_ne (<[_:=_]> _ )) in K; last done.
                rewrite !lookup_insert in K. simplify_eq.
              - subst. intro K. simplify_eq. rewrite map_eq_iff in K.
                specialize (K α2). rewrite !lookup_insert in K. simplify_eq.
            }
            case_bool_decide.
            { repeat rewrite bool_decide_eq_false_2.
              - lra.
              - subst. intro K. simplify_eq. rewrite map_eq_iff in K.
                specialize (K α2). rewrite !lookup_insert in K. simplify_eq.
            }
            lra.
      -- rewrite /rmarg dmap_comp.
         f_equal.
Qed.

Lemma Rcoupl_fragmented_rand_rand_inj (N M: nat) (f: fin (S M) -> fin (S N)) (Hinj: Inj (=) (=) f) σ σₛ ms ns α αₛ:
  (M<=N)%R ->
  σ.(tapes) !! α = Some (N%nat; ns) ->
  σₛ.(tapes) !! αₛ = Some (M%nat; ms) ->
  Rcoupl
    (state_step σ α)
    (dunifP N≫= λ x, if bool_decide (∃ m, f m = x) then state_step σₛ αₛ else dret σₛ)
    (λ σ1' σ2', ∃ (n : fin (S N)),
        if bool_decide (∃ m, f m = n)
        then ∃ (m : fin (S M)),
            σ1' = state_upd_tapes <[α := (N; ns ++ [n])]> σ ∧
            σ2' = state_upd_tapes <[αₛ := (M; ms ++ [m])]> σₛ /\
            f m = n
        else
          σ1' = state_upd_tapes <[α := (N; ns ++ [n])]> σ ∧
          σ2' =  σₛ
    ).
Proof.
  intros Hineq Hσ Hσₛ. (* rewrite <-(dret_id_right (state_step _ _)). *)
  replace (0)%NNR with (0+0)%NNR; last first.
  { apply nnreal_ext. simpl. lra. }
  erewrite (distr_ext (dunifP _ ≫= _)
              (MkDistr (dunifP N ≫= (λ x : fin (S N),
                                       match ClassicalEpsilon.excluded_middle_informative
                                               (∃ m, f m = x)
                                       with
                                       | left Hproof =>
                                           dret (state_upd_tapes <[αₛ:=(M; ms ++ [epsilon Hproof])]> σₛ)
                                       | _ =>
                                           dret σₛ
                                       end)) _ _ _) ); last first.
  { intros σ'. simpl. rewrite /pmf/=.
    rewrite /dbind_pmf. rewrite /dunifP. setoid_rewrite dunif_pmf.
    rewrite !SeriesC_scal_l. apply Rmult_eq_compat_l.
    erewrite (SeriesC_ext _
                (λ x : fin (S N), (if bool_decide (∃ m : fin (S M), f m = x) then state_step σₛ αₛ σ' else 0) +
                                    (if bool_decide (∃ m : fin (S M), f m = x) then 0 else dret σₛ σ')
             )); last first.
    { intros. case_bool_decide; lra. }
    trans (SeriesC
             (λ x : fin (S N),
                match ClassicalEpsilon.excluded_middle_informative
                                               (∃ m, f m = x) with
                | left Hproof => dret (state_upd_tapes <[αₛ:=(M; ms ++ [epsilon Hproof])]> σₛ) σ'
                | right _ => 0
                end +
                  match ClassicalEpsilon.excluded_middle_informative
                                               (∃ m, f m = x) with
                  | left Hproof => 0
                  | right _ => dret σₛ σ'
                  end
             )
          ); last first.
    { apply SeriesC_ext. intros. case_match; lra. }
    rewrite !SeriesC_plus; last first.
    all: try apply ex_seriesC_finite.
    etrans; first eapply Rplus_eq_compat_l; last apply Rplus_eq_compat_r.
    { apply SeriesC_ext. intros. case_bool_decide as H; case_match; done. }
    destruct (ExcludedMiddle (∃ x, σ' = (state_upd_tapes <[αₛ:=(M; ms ++ [x])]> σₛ))) as [H|H].
    + destruct H as [n ->].
      trans 1.
      * rewrite /state_step.
        rewrite bool_decide_eq_true_2; last first.
        { rewrite elem_of_dom. rewrite Hσₛ. done. }
        setoid_rewrite (lookup_total_correct (tapes σₛ) αₛ (M; ms)); last done.
        rewrite /dmap/dbind/dbind_pmf{1}/pmf/=.
        rewrite /dunifP. setoid_rewrite dunif_pmf.
        setoid_rewrite SeriesC_scal_l.
        rewrite (SeriesC_ext _ (λ x : fin (S N),
                                  if bool_decide (∃ m : fin (S M), f m = x)
                                  then
                                    / S M
                                  else 0)).
        -- erewrite (SeriesC_ext _ (λ x : fin (S N), / S M * if bool_decide (x∈f<$> enum (fin (S M))) then 1 else 0)).
           { rewrite SeriesC_scal_l. rewrite SeriesC_list_1.
             - rewrite fmap_length. rewrite length_enum_fin. rewrite Rinv_l; first lra.
               replace 0 with (INR 0) by done.
               move => /INR_eq. lia.
             - apply NoDup_fmap_2; try done.
               apply NoDup_enum.
           }
           intros n'.
           case_bool_decide as H.
           ++ rewrite bool_decide_eq_true_2; first lra.
              destruct H as [?<-].
              apply elem_of_list_fmap_1.
              apply elem_of_enum.
           ++ rewrite bool_decide_eq_false_2; first lra.
              intros H0. apply H.
              apply elem_of_list_fmap_2 in H0 as [?[->?]].
              naive_solver.
        -- intros.
           erewrite (SeriesC_ext _ (λ x, if (bool_decide (x=n)) then 1 else 0)).
           ++ rewrite SeriesC_singleton. case_bool_decide as H1; lra.
           ++ intros m. case_bool_decide; subst.
              ** by apply dret_1.
              ** apply dret_0. intro H1. apply H. apply state_upd_tapes_same in H1.
                 simplify_eq.
      * symmetry.
        rewrite (SeriesC_ext _ (λ x, if bool_decide (x = f n) then 1 else 0)).
        { apply SeriesC_singleton. }
        intros n'.
        case_match eqn:Heqn.
        { destruct e as [m <-] eqn:He.
          case_bool_decide as Heqn'.
          - apply Hinj in Heqn' as ->.
            apply dret_1.
            repeat f_equal.
            pose proof epsilon_correct (λ m : fin (S M), f m = f n) as H. simpl in H.
            apply Hinj. rewrite H. done.
          - apply dret_0.
            move => /state_upd_tapes_same. intros eq. simplify_eq.
            apply Heqn'. pose proof epsilon_correct (λ m0 : fin (S M), f m0 = f m) as H.
            by rewrite H.
        }
        rewrite bool_decide_eq_false_2; first done.
        intros ->.  naive_solver.
    + trans 0.
      * apply SeriesC_0.
        intros. case_bool_decide; last done.
        rewrite /state_step.
        rewrite bool_decide_eq_true_2; last first.
        { rewrite elem_of_dom. rewrite Hσₛ. done. }
        setoid_rewrite (lookup_total_correct (tapes σₛ) αₛ (M; ms)); last done.
        rewrite /dmap/dbind/dbind_pmf{1}/pmf/=.
        rewrite /dunifP. setoid_rewrite dunif_pmf.
        apply SeriesC_0.
        intros m. apply Rmult_eq_0_compat_l.
        apply dret_0.
        intros ->. apply H.
        exists m. done.
      * symmetry.
        apply SeriesC_0.
        intros. case_match; last done.
        apply dret_0.
        intros ->. apply H.
        naive_solver.
  }
  erewrite state_step_unfold; last done.
  rewrite /dmap. 
  eapply Rcoupl_dbind; last apply Rcoupl_eq.
  intros ??->.
  case_match eqn:Heqn.
  - destruct e as [m He].
    replace (epsilon _) with m; last first.
    { pose proof epsilon_correct (λ m0 : fin (S M), f m0 = b) as H.
      simpl in H. apply Hinj. rewrite H. done.
    }
    apply Rcoupl_dret.
    exists b.
    rewrite bool_decide_eq_true_2; last naive_solver.
    naive_solver.
  - apply Rcoupl_dret.
    exists b. rewrite bool_decide_eq_false_2; naive_solver.
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
| LoadDSP l v σ :
  σ.(heap) !! l = Some v →
  det_head_step_pred (Load (Val $ LitV $ LitLoc l)) σ
| StoreDSP l v w σ :
  σ.(heap) !! l = Some v →
  det_head_step_pred (Store (Val $ LitV $ LitLoc l) (Val w)) σ
| TickDSP z σ :
  det_head_step_pred (Tick (Val $ LitV $ LitInt z)) σ.

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
  | AllocN (Val (LitV (LitInt z))) (Val v) => bool_decide (0 < Z.to_nat z)%nat
  | Load (Val (LitV (LitLoc l)))  =>
      bool_decide (is_Some (σ1.(heap) !! l))
  | Store (Val (LitV (LitLoc l))) (Val w) =>
      bool_decide (is_Some (σ1.(heap) !! l))
  | Tick (Val (LitV (LitInt z))) => true
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
  prob_head_step_pred (rand(#lbl:α) #z) σ
| RandEmptyPSP N α σ z :
  N = Z.to_nat z →
  σ.(tapes) !! α = Some ((N; []) : tape) →
  prob_head_step_pred (rand(#lbl:α) #z) σ
| RandTapeOtherPSP N M α σ ns z :
  N ≠ M →
  M = Z.to_nat z →
  σ.(tapes) !! α = Some ((N; ns) : tape) →
  prob_head_step_pred (rand(#lbl:α) #z) σ
| RandNoTapePSP (N : nat) σ z :
  N = Z.to_nat z →
  prob_head_step_pred (rand #z) σ.

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
  try (lra || lia || done).

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
  - by pose proof (pmf_SeriesC_ge_0 (head_step e1 σ1))
      as ?%Rle_not_lt.
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
Proof.
  inversion 1; try econstructor; eauto.
  (* Unsolved case *)
  intros. rewrite state_upd_tapes_heap. econstructor; eauto.
Qed.

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

Lemma prim_step_empty_tape σ α (z:Z) K N :
  (tapes σ) !! α = Some (N; []) -> prim_step (fill K (rand(#lbl:α) #z)) σ = prim_step (fill K (rand #z)) σ.
Proof.
  intros H.
  rewrite !fill_dmap; [|done|done].
  rewrite /dmap.
  f_equal.
  simpl. apply distr_ext; intros [e s].
  erewrite !head_prim_step_eq; simpl; last first.
  (** type classes dont work? *)
  { destruct (decide (Z.to_nat z=N)) as [<-|?] eqn:Heqn.
    all: eexists (_, σ); eapply head_step_support_equiv_rel;
      eapply head_step_support_eq; simpl; last first.
    - rewrite H. rewrite bool_decide_eq_true_2; last lia.
      eapply dmap_unif_nonzero; last done.
      intros ???. simplify_eq. done.
    - apply Rinv_pos. pose proof pos_INR_S (Z.to_nat z). lra.
    - rewrite H. case_bool_decide as H0; first lia.
      eapply dmap_unif_nonzero; last done.
      intros ???. by simplify_eq.
    - apply Rinv_pos. pose proof pos_INR_S (Z.to_nat z). lra.
  }
  { eexists (_, σ); eapply head_step_support_equiv_rel;
      eapply head_step_support_eq; simpl; last first.
    - eapply dmap_unif_nonzero; last done.
      intros ???. simplify_eq. done.
    - apply Rinv_pos. pose proof pos_INR_S (Z.to_nat z). lra.
  } rewrite H.
  case_bool_decide; last done.
  subst. done.
  Unshelve.
  all: exact (0%fin).
Qed.
  
