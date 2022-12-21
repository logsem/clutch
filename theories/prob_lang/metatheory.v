From Coq Require Import Reals Psatz.
From stdpp Require Import functions fin_maps gmap stringmap.
From self.prelude Require Import stdpp_ext.
From self.prob Require Import distribution couplings.
From self.prob_lang Require Export lang tactics notation.
From iris.prelude Require Import options.

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
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Alloc e | Load e | Flip e =>
     is_closed_expr X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Store e1 e2 =>
     is_closed_expr X e1 && is_closed_expr X e2
  | If e0 e1 e2 | Case e0 e1 e2 =>
     is_closed_expr X e0 && is_closed_expr X e1 && is_closed_expr X e2
  | AllocTape => true
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
  | AllocTape => AllocTape
  | Flip e => Flip (subst_map vs e)
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

Goal Lookup loc val (gmap loc val).
  apply _.
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

(** * [state_step] coupling  *)
Local Definition add_bool_tapes '(σ, σ') α α' b : state * state :=
  (state_upd_tapes <[α  := σ.(tapes)  !!! α  ++ [b]]> σ,
   state_upd_tapes <[α' := σ'.(tapes) !!! α' ++ [b]]> σ').

Definition valid_double_state_step σs (α α' : loc) σs2 : Prop :=
  α ∈ dom σs.1.(tapes) ∧ α' ∈ dom σs.2.(tapes) ∧
  ∃ b, σs2 = add_bool_tapes σs α α' b.

Global Instance valid_double_state_step_dec σs α α' σs' :
  Decision (valid_double_state_step σs α α' σs').
Proof. apply _. Qed.

Definition double_state_step_pmf (σs1 : state * state) (α α' : loc) (σs2 : state * state) : R :=
  if bool_decide (valid_double_state_step σs1 α α' σs2) then 0.5 else 0.

Local Lemma ex_seriesC_double_state_step_pmf σ1 σ1' α α' :
  ex_seriesC (double_state_step_pmf (σ1, σ1') α α').
Proof.
  rewrite /double_state_step_pmf.
  apply (ex_seriesC_split_elem _ (add_bool_tapes (σ1, σ1') α α' true)).
  apply (ex_seriesC_split_elem _ (add_bool_tapes (σ1, σ1') α α' false)).
  eapply ex_seriesC_ext; [|apply ex_seriesC_0].
  intros [σ2 σ2'].
  do 2 (case_bool_decide; [|lra]).
  rewrite bool_decide_eq_false_2 //.
  intros (? & ? & [b [=]]); simplify_eq.
  assert (b ≠ false) by (intros ->; eauto).
  assert (b ≠ true) by (intros ->; eauto).
  by destruct b.
Qed.

Program Definition double_state_step (σs1 : state * state) (α α' : loc) : distr (state * state) :=
  MkDistr (double_state_step_pmf σs1 α α') _ _ _.
Next Obligation.
  rewrite /double_state_step_pmf.
  intros [] ?? []. case_bool_decide; lra.
Qed.
Next Obligation. intros [? ?]. apply ex_seriesC_double_state_step_pmf. Qed.
Next Obligation.
  rewrite /double_state_step_pmf. intros [σ1 σ1'] ??.
  destruct (decide (α ∈ dom σ1.(tapes))); last first.
  { rewrite SeriesC_0; [lra|]. intros [].
    rewrite bool_decide_eq_false_2 //. by intros (?&?&?). }
  destruct (decide (α' ∈ dom σ1'.(tapes))); last first.
  { rewrite SeriesC_0; [lra|]. intros [].
    rewrite bool_decide_eq_false_2 //. by intros (?&?&?). }
  rewrite (SeriesC_split_elem _ (add_bool_tapes (σ1, σ1') α α' true)); last first.
  { eapply ex_seriesC_double_state_step_pmf. }
  { intros [? ?]. case_bool_decide; lra. }
  rewrite (SeriesC_ext _
             (λ a, if bool_decide (a = add_bool_tapes (σ1, σ1') α α' true) then 0.5 else 0)); last first.
  { intros [? ?]. case_bool_decide as Heq; [|done]. case_bool_decide as Hnv; [done|].
    exfalso; eapply Hnv. do 2 (split; [done|]). by exists true. }
  rewrite SeriesC_singleton.
  rewrite (SeriesC_split_elem _ (add_bool_tapes (σ1, σ1') α α' false)); last first.
  { apply ex_seriesC_filter_pos; [intros; case_bool_decide; lra|].
    apply ex_seriesC_double_state_step_pmf. }
  { intros [? ?]. repeat case_bool_decide; lra. }
  rewrite (SeriesC_ext _ (λ a, if bool_decide (a = add_bool_tapes (σ1, σ1') α α' false)
                               then 0.5 else 0)); last first.
  { intros [? ?]. case_bool_decide as Heq; simplify_eq; [|done].
    rewrite bool_decide_eq_true_2; last first.
    - intros [=]. simplify_eq. inversion Heq as [Hst].
      apply insert_inv in Hst. simplify_map_eq.
    - case_bool_decide as H; [done|]. exfalso; apply H.
      do 2 (split; [done|]). by exists false. }
  rewrite SeriesC_singleton.
  erewrite SeriesC_0; [lra|].
  intros [σ2 σ2']. do 2 (case_bool_decide; [|done]).
  rewrite bool_decide_eq_false_2 //.
  intros (? & ? & (b & [=])). simplify_eq.
  assert (b ≠ false) by (intros ->; eauto).
  assert (b ≠ true) by (intros ->; eauto).
  by destruct b.
Qed.

Lemma Rcoupl_state_step σ1 σ2 α1 α2 :
  α1 ∈ dom σ1.(tapes) →
  α2 ∈ dom σ2.(tapes) →
  Rcoupl
    (state_step σ1 α1)
    (state_step σ2 α2)
    (λ σ1' σ2', valid_double_state_step (σ1, σ2) α1 α2 (σ1', σ2')).
Proof.
  intros Hd1 Hd2.
  exists (double_state_step (σ1, σ2) α1 α2). split.
  - split.
    + eapply distr_ext. intros σ.
      rewrite lmarg_pmf /pmf /= /double_state_step_pmf /state_step_pmf.
      case_bool_decide as Heq.
      * destruct Heq as (? & b & ?).
        erewrite SeriesC_ext;
          [eapply (SeriesC_singleton (state_upd_tapes <[α2 := σ2.(tapes) !!! α2 ++ [b]]> σ2))|].
        intros σ'; simpl.
        symmetry; case_bool_decide as Heq; simplify_eq.
        { rewrite bool_decide_eq_true_2 //. split_and!; eauto. }
        rewrite bool_decide_eq_false_2 //.
        intros (? & ? & [b' [= Htapes%insert_inv]]). simplify_map_eq.
      * apply SeriesC_0. intros σ'.
        rewrite bool_decide_eq_false_2 //.
        intros (?&?&(b & [=])); simplify_eq. apply Heq.
        split_and!; eauto.
    + eapply distr_ext. intros σ.
      rewrite rmarg_pmf /pmf /= /double_state_step_pmf /state_step_pmf.
      case_bool_decide as Heq.
      * destruct Heq as (? & (b & ?)).
        erewrite SeriesC_ext;
          [eapply (SeriesC_singleton (state_upd_tapes <[α1 := σ1.(tapes) !!! α1 ++ [b]]> σ1))|].
        intros σ'; simpl.
        symmetry; case_bool_decide as Heq; simplify_eq.
        { rewrite bool_decide_eq_true_2 //. split_and!; eauto. }
        rewrite bool_decide_eq_false_2 //.
        intros (?&?&(b' & [= ? Htapes%insert_inv])). simplify_map_eq.
      * apply SeriesC_0. intros σ'.
        rewrite bool_decide_eq_false_2 //.
        intros (?&?&(b & [=])); simplify_eq. apply Heq. split_and!; eauto.
  - intros [ρ1 ρ2]. rewrite /pmf /= /double_state_step_pmf.
    case_bool_decide; eauto. lra.
Qed.

(** * flip-flip coupling w/empty tape on left *)
(* the structure of the setup and the proofs are mostly similar to the result
   for [double_state_step] *)
Local Definition flips_bool σ1 σ1' b : cfg * cfg :=
  ((Val $ LitV $ LitBool b, σ1), (Val $ LitV $ LitBool b, σ1')).

Definition valid_flip_flip_l (ρs1 : cfg * cfg) (α : loc) (ρs2 : cfg * cfg) : Prop :=
  ρs1.1.1 = Flip (Val $ LitV $ LitLbl α) ∧ ρs1.2.1 = Flip (Val $ LitV LitUnit) ∧
  ∃ (b : bool), ρs2 = flips_bool ρs1.1.2 ρs1.2.2 b.

Global Instance valid_flip_flip_l_dec ρs1 α ρs2 :
  Decision (valid_flip_flip_l ρs1 α ρs2).
Proof. apply _. Qed.

Definition flip_flip_l_pmf (ρs1 : cfg * cfg) (α : loc) (ρs2 : cfg * cfg) : R :=
  if bool_decide (valid_flip_flip_l ρs1 α ρs2) then 0.5 else 0.

Local Lemma ex_seriesC_flip_flip_l_pmf e1 e1' σ1 σ1' α :
  ex_seriesC (flip_flip_l_pmf ((e1, σ1), (e1', σ1')) α).
Proof.
  apply (ex_seriesC_split_elem _ (flips_bool σ1 σ1' true)).
  apply (ex_seriesC_split_elem _ (flips_bool σ1 σ1' false)).
  eapply ex_seriesC_ext; [|apply ex_seriesC_0].
  intros [[e2 σ2] [e2' σ2']].
  do 2 (case_bool_decide; [|lra]).
  rewrite /flip_flip_l_pmf bool_decide_eq_false_2 //.
  rewrite /valid_flip_flip_l /=.
  intros (? & ? & [b ?]); simplify_eq.
  assert (b ≠ false) by (intros ->; eauto).
  assert (b ≠ true) by (intros ->; eauto).
  by destruct b.
Qed.

Program Definition flip_flip_l (ρs1 : cfg * cfg) (α : loc) : distr (cfg * cfg) :=
  MkDistr (flip_flip_l_pmf ρs1 α) _ _ _.
Next Obligation.
  rewrite /flip_flip_l_pmf.
  intros [[] []] ? [[] []].
  case_bool_decide; lra.
Qed.
Next Obligation. intros [[] []] ?. apply ex_seriesC_flip_flip_l_pmf. Qed.
Next Obligation.
  rewrite /flip_flip_l_pmf. intros [[e1 σ1] [e1' σ1']] ?.
  destruct (decide (e1 = Flip (Val $ LitV $ LitLbl α))) as [He1|]; last first.
  { rewrite SeriesC_0; [lra|]. intros [[] []].
    rewrite bool_decide_eq_false_2 //. by intros (?&?&?&?). }
  destruct (decide (e1' = Flip (Val $ LitV $ LitUnit))) as [He1'|]; last first.
  { rewrite SeriesC_0; [lra|]. intros [[] []].
    rewrite bool_decide_eq_false_2 //. by intros (?&?&?&?). }
  rewrite (SeriesC_split_elem _ (flips_bool σ1 σ1' true)); last first.
  { eapply ex_seriesC_flip_flip_l_pmf. }
  { intros [? ?]. case_bool_decide; lra. }
  rewrite (SeriesC_ext _
             (λ a, if bool_decide (a = flips_bool σ1 σ1' true) then 0.5 else 0)); last first.
  { intros [[] []]. case_bool_decide as Heq; [|done]. case_bool_decide as Hnv; [done|].
    exfalso; eapply Hnv. inversion Heq; simplify_eq.
    do 2 (split; [done|]). by exists true. }
  rewrite SeriesC_singleton.
  rewrite (SeriesC_split_elem _ (flips_bool σ1 σ1' false)); last first.
  { apply ex_seriesC_filter_pos; [intros; case_bool_decide; lra|].
    apply ex_seriesC_flip_flip_l_pmf. }
  { intros [? ?]. repeat case_bool_decide; lra. }
  rewrite (SeriesC_ext _ (λ a, if bool_decide (a = flips_bool σ1 σ1' false)
                               then 0.5 else 0)); last first.
  { intros [? ?]. case_bool_decide as Heq; simplify_eq; [|done].
    rewrite bool_decide_eq_true_2; last first.
    - intros [=]. simplify_eq.
    - case_bool_decide as H; [done|]. exfalso; apply H.
      do 2 (split; [done|]). by exists false. }
  rewrite SeriesC_singleton.
  erewrite SeriesC_0; [lra|].
  intros [σ2 σ2']. do 2 (case_bool_decide; [|done]).
  rewrite bool_decide_eq_false_2 //.
  intros (? & ? & (b & [=])). simplify_eq.
  assert (b ≠ false) by (intros ->; eauto).
  assert (b ≠ true) by (intros ->; eauto).
  by destruct b.
Qed.

Lemma Rcoupl_flip_flip_l σ1 σ1' α :
  σ1.(tapes) !! α = Some [] →
  Rcoupl
    (prim_step (Flip (Val $ LitV $ LitLbl α)) σ1)
    (prim_step (Flip (Val $ LitV $ LitUnit)) σ1')
    (λ ρ2 ρ2', ∃ (b : bool), (ρ2, ρ2') = flips_bool σ1 σ1' b).
Proof.
  intros Htape.
  exists (flip_flip_l ((Flip (Val $ LitV $ LitLbl α), σ1),
              (Flip (Val $ LitV $ LitUnit), σ1')) α). split.
  - split.
    + eapply distr_ext. intros [e2 σ2].
      rewrite lmarg_pmf {1}/pmf /= /flip_flip_l_pmf.
      rewrite head_prim_step_pmf_eq /=; last first.
      { eexists (Val $ LitV $ LitBool true, _); simpl;
          eapply head_step_support_equiv_rel.
        eapply FlipTapeEmptyS; eauto. }
      rewrite /valid_flip_flip_l /flips_bool /=.
      rewrite /pmf /= Htape.
      destruct (decide (e2 = Val $ LitV $ LitBool true)) as [He2|].
      * rewrite He2 /=.
        erewrite SeriesC_ext;
          [eapply (SeriesC_singleton (Val $ LitV $ LitBool true, σ1'))|].
        intros [e' σ'].
        case_bool_decide as Heq.
        { destruct Heq as (?&?&?&?); simplify_eq.
          rewrite ?bool_decide_eq_true_2 //. }
        destruct (decide (σ1 = σ2)) as [->|Hneq]; last first.
        { case_match; [|done]. rewrite bool_decide_eq_false_2 //. }
        rewrite bool_decide_eq_false_2 //.
        intros [=]; simplify_eq. apply Heq.
        split_and!; eauto.
      * destruct (decide (e2 = Val $ LitV $ LitBool false)) as [He2'|]; last first.
        { rewrite SeriesC_0.
          - repeat case_match; try done. by destruct b.
          - intros [e σ]. rewrite bool_decide_eq_false_2 //.
            intros (?&?&?&?); simplify_eq. destruct x; eauto. }
        rewrite He2' /=.
        erewrite SeriesC_ext;
          [eapply (SeriesC_singleton (Val $ LitV $ LitBool false, σ1'))|].
        intros [e' σ'].
        case_bool_decide as Heq.
        { destruct Heq as (?&?&?&?); simplify_eq.
          rewrite ?bool_decide_eq_true_2 //. }
        destruct (decide (σ1 = σ2)) as [->|Hneq]; last first.
        { case_match; [|done]. rewrite bool_decide_eq_false_2 //. }
        rewrite bool_decide_eq_false_2 //.
        intros [=]; simplify_eq. apply Heq.
        split_and!; eauto.
    + (* same approach as for [lmarg] - TODO: better lemmas *)
      eapply distr_ext. intros [e2' σ2'].
      rewrite rmarg_pmf {1}/pmf /= /flip_flip_l_pmf.
      rewrite head_prim_step_pmf_eq /=; last first.
      { eexists (Val $ LitV $ LitBool true, _); simpl.
        eapply head_step_support_equiv_rel. eapply FlipNoTapeS; eauto. }
      rewrite /valid_flip_flip_l /flips_bool /=.
      rewrite /pmf /=.
      destruct (decide (e2' = Val $ LitV $ LitBool true)) as [He2|].
      * rewrite He2 /=.
        erewrite SeriesC_ext;
          [eapply (SeriesC_singleton (Val $ LitV $ LitBool true, σ1))|].
        intros [e' σ'].
        case_bool_decide as Heq.
        { destruct Heq as (?&?&?&?); simplify_eq.
          rewrite ?bool_decide_eq_true_2 //. }
        destruct (decide (σ1' = σ2')) as [->|Hneq]; last first.
        { case_match; [|done]. rewrite bool_decide_eq_false_2 //. }
        rewrite bool_decide_eq_false_2 //.
        intros [=]; simplify_eq. apply Heq.
        split_and!; eauto.
      * destruct (decide (e2' = Val $ LitV $ LitBool false)) as [He2'|]; last first.
        { rewrite SeriesC_0.
          - repeat case_match; try done. by destruct b.
          - intros [e σ]. rewrite bool_decide_eq_false_2 //.
            intros (?&?&?&?); simplify_eq. destruct x; eauto. }
        rewrite He2' /=.
        erewrite SeriesC_ext;
          [eapply (SeriesC_singleton (Val $ LitV $ LitBool false, σ1))|].
        intros [e' σ'].
        case_bool_decide as Heq.
        { destruct Heq as (?&?&?&?); simplify_eq.
          rewrite ?bool_decide_eq_true_2 //. }
        destruct (decide (σ1' = σ2')) as [->|Hneq]; last first.
        { case_match; [|done]. rewrite bool_decide_eq_false_2 //. }
        rewrite bool_decide_eq_false_2 //.
        intros [=]; simplify_eq. apply Heq.
        split_and!; eauto.
  - intros [[] []].
    rewrite /pmf /= /flip_flip_l_pmf.
    case_bool_decide as Heq; [|lra].
    destruct Heq as (?&?&?&?). eauto.
Qed.

(** * flip-flip coupling w/empty tape on right *)
(* a lot of this is more or less identical (but not exactly) to the case for the
   LHS *)
(* TODO: generalize? *)
Definition valid_flip_flip_r (ρs1 : cfg * cfg) (α : loc) (ρs2 : cfg * cfg) : Prop :=
  ρs1.1.1 = Flip (Val $ LitV LitUnit)  ∧ ρs1.2.1 = Flip (Val $ LitV $ LitLbl α) ∧
  ∃ (b : bool), ρs2 = flips_bool ρs1.1.2 ρs1.2.2 b.

Global Instance valid_flip_flip_r_dec ρs1 α ρs2 :
  Decision (valid_flip_flip_r ρs1 α ρs2).
Proof. apply _. Qed.

Definition flip_flip_r_pmf (ρs1 : cfg * cfg) (α : loc) (ρs2 : cfg * cfg) : R :=
  if bool_decide (valid_flip_flip_r ρs1 α ρs2) then 0.5 else 0.

Local Lemma ex_seriesC_flip_flip_r_pmf e1 e1' σ1 σ1' α :
  ex_seriesC (flip_flip_r_pmf ((e1, σ1), (e1', σ1')) α).
Proof.
  apply (ex_seriesC_split_elem _ (flips_bool σ1 σ1' true)).
  apply (ex_seriesC_split_elem _ (flips_bool σ1 σ1' false)).
  eapply ex_seriesC_ext; [|apply ex_seriesC_0].
  intros [[e2 σ2] [e2' σ2']].
  do 2 (case_bool_decide; [|lra]).
  rewrite /flip_flip_r_pmf bool_decide_eq_false_2 //.
  rewrite /valid_flip_flip_r /=.
  intros (? & ? & [b ?]); simplify_eq.
  assert (b ≠ false) by (intros ->; eauto).
  assert (b ≠ true) by (intros ->; eauto).
  by destruct b.
Qed.

Program Definition flip_flip_r (ρs1 : cfg * cfg) (α : loc) : distr (cfg * cfg) :=
  MkDistr (flip_flip_r_pmf ρs1 α) _ _ _.
Next Obligation.
  rewrite /flip_flip_r_pmf.
  intros [[] []] ? [[] []].
  case_bool_decide; lra.
Qed.
Next Obligation. intros [[] []] ?. apply ex_seriesC_flip_flip_r_pmf. Qed.
Next Obligation.
  rewrite /flip_flip_r_pmf. intros [[e1 σ1] [e1' σ1']] ?.
  destruct (decide (e1 = Flip (Val $ LitV $ LitUnit))) as [He1|]; last first.
  { rewrite SeriesC_0; [lra|]. intros [[] []].
    rewrite bool_decide_eq_false_2 //. by intros (?&?&?&?). }
  destruct (decide (e1' = Flip (Val $ LitV $ LitLbl α))) as [He1'|]; last first.
  { rewrite SeriesC_0; [lra|]. intros [[] []].
    rewrite bool_decide_eq_false_2 //. by intros (?&?&?&?). }
  rewrite (SeriesC_split_elem _ (flips_bool σ1 σ1' true)); last first.
  { eapply ex_seriesC_flip_flip_r_pmf. }
  { intros [? ?]. case_bool_decide; lra. }
  rewrite (SeriesC_ext _
             (λ a, if bool_decide (a = flips_bool σ1 σ1' true) then 0.5 else 0)); last first.
  { intros [[] []]. case_bool_decide as Heq; [|done]. case_bool_decide as Hnv; [done|].
    exfalso; eapply Hnv. inversion Heq; simplify_eq.
    do 2 (split; [done|]). by exists true. }
  rewrite SeriesC_singleton.
  rewrite (SeriesC_split_elem _ (flips_bool σ1 σ1' false)); last first.
  { apply ex_seriesC_filter_pos; [intros; case_bool_decide; lra|].
    apply ex_seriesC_flip_flip_r_pmf. }
  { intros [? ?]. repeat case_bool_decide; lra. }
  rewrite (SeriesC_ext _ (λ a, if bool_decide (a = flips_bool σ1 σ1' false)
                               then 0.5 else 0)); last first.
  { intros [? ?]. case_bool_decide as Heq; simplify_eq; [|done].
    rewrite bool_decide_eq_true_2; last first.
    - intros [=]. simplify_eq.
    - case_bool_decide as H; [done|]. exfalso; apply H.
      do 2 (split; [done|]). by exists false. }
  rewrite SeriesC_singleton.
  erewrite SeriesC_0; [lra|].
  intros [σ2 σ2']. do 2 (case_bool_decide; [|done]).
  rewrite bool_decide_eq_false_2 //.
  intros (? & ? & (b & [=])). simplify_eq.
  assert (b ≠ false) by (intros ->; eauto).
  assert (b ≠ true) by (intros ->; eauto).
  by destruct b.
Qed.

Lemma Rcoupl_flip_flip_r σ1 σ1' α :
  σ1'.(tapes) !! α = Some [] →
  Rcoupl
    (prim_step (Flip (Val $ LitV $ LitUnit)) σ1)
    (prim_step (Flip (Val $ LitV $ LitLbl α)) σ1')
    (λ ρ2 ρ2', ∃ (b : bool), (ρ2, ρ2') = flips_bool σ1 σ1' b).
Proof.
  intros Htape.
  exists (flip_flip_r ((Flip (Val $ LitV $ LitUnit), σ1),
              (Flip (Val $ LitV $ LitLbl α), σ1')) α). split.
  - split.
    + eapply distr_ext. intros [e2 σ2].
      rewrite lmarg_pmf {1}/pmf /= /flip_flip_r_pmf.
      rewrite head_prim_step_pmf_eq /=; last first.
      { eexists (Val $ LitV $ LitBool true, _); simpl;
          eapply head_step_support_equiv_rel. eapply FlipNoTapeS. }
      rewrite /valid_flip_flip_r /flips_bool /=.
      rewrite /pmf /=.
      destruct (decide (e2 = Val $ LitV $ LitBool true)) as [He2|].
      * rewrite He2 /=.
        erewrite SeriesC_ext;
          [eapply (SeriesC_singleton (Val $ LitV $ LitBool true, σ1'))|].
        intros [e' σ'].
        case_bool_decide as Heq.
        { destruct Heq as (?&?&?&?); simplify_eq.
          rewrite ?bool_decide_eq_true_2 //. }
        destruct (decide (σ1 = σ2)) as [->|Hneq]; last first.
        { case_match; [|done]. rewrite bool_decide_eq_false_2 //. }
        rewrite bool_decide_eq_false_2 //.
        intros [=]; simplify_eq. apply Heq.
        split_and!; eauto.
      * destruct (decide (e2 = Val $ LitV $ LitBool false)) as [He2'|]; last first.
        { rewrite SeriesC_0.
          - repeat case_match; try done. by destruct b.
          - intros [e σ]. rewrite bool_decide_eq_false_2 //.
            intros (?&?&?&?); simplify_eq. destruct x; eauto. }
        rewrite He2' /=.
        erewrite SeriesC_ext;
          [eapply (SeriesC_singleton (Val $ LitV $ LitBool false, σ1'))|].
        intros [e' σ'].
        case_bool_decide as Heq.
        { destruct Heq as (?&?&?&?); simplify_eq.
          rewrite ?bool_decide_eq_true_2 //. }
        destruct (decide (σ1 = σ2)) as [->|Hneq]; last first.
        { case_match; [|done]. rewrite bool_decide_eq_false_2 //. }
        rewrite bool_decide_eq_false_2 //.
        intros [=]; simplify_eq. apply Heq.
        split_and!; eauto.
    + (* same approach as for [lmarg] - TODO: better lemmas *)
      eapply distr_ext. intros [e2' σ2'].
      rewrite rmarg_pmf {1}/pmf /= /flip_flip_r_pmf.
      rewrite head_prim_step_pmf_eq /=; last first.
      { eexists (Val $ LitV $ LitBool true, _); simpl.
        eapply head_step_support_equiv_rel. eapply FlipTapeEmptyS; eauto. }
      rewrite /valid_flip_flip_r /flips_bool /=.
      rewrite /pmf /= Htape.
      destruct (decide (e2' = Val $ LitV $ LitBool true)) as [He2|].
      * rewrite He2 /=.
        erewrite SeriesC_ext;
          [eapply (SeriesC_singleton (Val $ LitV $ LitBool true, σ1))|].
        intros [e' σ'].
        case_bool_decide as Heq.
        { destruct Heq as (?&?&?&?); simplify_eq.
          rewrite ?bool_decide_eq_true_2 //. }
        destruct (decide (σ1' = σ2')) as [->|Hneq]; last first.
        { case_match; [|done]. rewrite bool_decide_eq_false_2 //. }
        rewrite bool_decide_eq_false_2 //.
        intros [=]; simplify_eq. apply Heq.
        split_and!; eauto.
      * destruct (decide (e2' = Val $ LitV $ LitBool false)) as [He2'|]; last first.
        { rewrite SeriesC_0.
          - repeat case_match; try done. by destruct b.
          - intros [e σ]. rewrite bool_decide_eq_false_2 //.
            intros (?&?&?&?); simplify_eq. destruct x; eauto. }
        rewrite He2' /=.
        erewrite SeriesC_ext;
          [eapply (SeriesC_singleton (Val $ LitV $ LitBool false, σ1))|].
        intros [e' σ'].
        case_bool_decide as Heq.
        { destruct Heq as (?&?&?&?); simplify_eq.
          rewrite ?bool_decide_eq_true_2 //. }
        destruct (decide (σ1' = σ2')) as [->|Hneq]; last first.
        { case_match; [|done]. rewrite bool_decide_eq_false_2 //. }
        rewrite bool_decide_eq_false_2 //.
        intros [=]; simplify_eq. apply Heq.
        split_and!; eauto.
  - intros [[] []].
    rewrite /pmf /= /flip_flip_r_pmf.
    case_bool_decide as Heq; [|lra].
    destruct Heq as (?&?&?&?). eauto.
Qed.

(** * flip-flip coupling w/empty tape on both sides *)
(* the repetition is starting to get silly *)
(* TODO: generalize? *)
Definition valid_flip_flip_lr (ρs1 : cfg * cfg) (ρs2 : cfg * cfg) : Prop :=
  ρs1.1.1 = Flip (Val $ LitV LitUnit) ∧ ρs1.2.1 = Flip (Val $ LitV $ LitUnit) ∧
  ∃ (b : bool), ρs2 = flips_bool ρs1.1.2 ρs1.2.2 b.

Global Instance valid_flip_flip_lr_dec ρs1 ρs2 :
  Decision (valid_flip_flip_lr ρs1 ρs2).
Proof. apply _. Qed.

Definition flip_flip_lr_pmf (ρs1 : cfg * cfg) (ρs2 : cfg * cfg) : R :=
  if bool_decide (valid_flip_flip_lr ρs1 ρs2) then 0.5 else 0.

Local Lemma ex_seriesC_flip_flip_lr_pmf e1 e1' σ1 σ1' :
  ex_seriesC (flip_flip_lr_pmf ((e1, σ1), (e1', σ1'))).
Proof.
  apply (ex_seriesC_split_elem _ (flips_bool σ1 σ1' true)).
  apply (ex_seriesC_split_elem _ (flips_bool σ1 σ1' false)).
  eapply ex_seriesC_ext; [|apply ex_seriesC_0].
  intros [[e2 σ2] [e2' σ2']].
  do 2 (case_bool_decide; [|lra]).
  rewrite /flip_flip_lr_pmf bool_decide_eq_false_2 //.
  rewrite /valid_flip_flip_lr /=.
  intros (? & ? & [b ?]); simplify_eq.
  assert (b ≠ false) by (intros ->; eauto).
  assert (b ≠ true) by (intros ->; eauto).
  by destruct b.
Qed.

Program Definition flip_flip_lr (ρs1 : cfg * cfg) : distr (cfg * cfg) :=
  MkDistr (flip_flip_lr_pmf ρs1) _ _ _.
Next Obligation.
  rewrite /flip_flip_lr_pmf.
  intros [[] []] [[] []].
  case_bool_decide; lra.
Qed.
Next Obligation. intros [[] []]. apply ex_seriesC_flip_flip_lr_pmf. Qed.
Next Obligation.
  rewrite /flip_flip_lr_pmf. intros [[e1 σ1] [e1' σ1']].
  destruct (decide (e1 = Flip (Val $ LitV $ LitUnit))) as [He1|]; last first.
  { rewrite SeriesC_0; [lra|]. intros [[] []].
    rewrite bool_decide_eq_false_2 //. by intros (?&?&?&?). }
  destruct (decide (e1' = Flip (Val $ LitV $ LitUnit))) as [He1'|]; last first.
  { rewrite SeriesC_0; [lra|]. intros [[] []].
    rewrite bool_decide_eq_false_2 //. by intros (?&?&?&?). }
  rewrite (SeriesC_split_elem _ (flips_bool σ1 σ1' true)); last first.
  { eapply ex_seriesC_flip_flip_lr_pmf. }
  { intros [? ?]. case_bool_decide; lra. }
  rewrite (SeriesC_ext _
             (λ a, if bool_decide (a = flips_bool σ1 σ1' true) then 0.5 else 0)); last first.
  { intros [[] []]. case_bool_decide as Heq; [|done]. case_bool_decide as Hnv; [done|].
    exfalso; eapply Hnv. inversion Heq; simplify_eq.
    do 2 (split; [done|]). by exists true. }
  rewrite SeriesC_singleton.
  rewrite (SeriesC_split_elem _ (flips_bool σ1 σ1' false)); last first.
  { apply ex_seriesC_filter_pos; [intros; case_bool_decide; lra|].
    apply ex_seriesC_flip_flip_lr_pmf. }
  { intros [? ?]. repeat case_bool_decide; lra. }
  rewrite (SeriesC_ext _ (λ a, if bool_decide (a = flips_bool σ1 σ1' false)
                               then 0.5 else 0)); last first.
  { intros [? ?]. case_bool_decide as Heq; simplify_eq; [|done].
    rewrite bool_decide_eq_true_2; last first.
    - intros [=]. simplify_eq.
    - case_bool_decide as H; [done|]. exfalso; apply H.
      do 2 (split; [done|]). by exists false. }
  rewrite SeriesC_singleton.
  erewrite SeriesC_0; [lra|].
  intros [σ2 σ2']. do 2 (case_bool_decide; [|done]).
  rewrite bool_decide_eq_false_2 //.
  intros (? & ? & (b & [=])). simplify_eq.
  assert (b ≠ false) by (intros ->; eauto).
  assert (b ≠ true) by (intros ->; eauto).
  by destruct b.
Qed.

Lemma Rcoupl_flip_flip_lr σ1 σ1' :
  Rcoupl
    (prim_step (Flip (Val $ LitV $ LitUnit)) σ1)
    (prim_step (Flip (Val $ LitV $ LitUnit)) σ1')
    (λ ρ2 ρ2', ∃ (b : bool), (ρ2, ρ2') = flips_bool σ1 σ1' b).
Proof.
  exists (flip_flip_lr ((Flip (Val $ LitV $ LitUnit), σ1),
              (Flip (Val $ LitV $ LitUnit), σ1'))). split.
  - split.
    + eapply distr_ext. intros [e2 σ2].
      rewrite lmarg_pmf {1}/pmf /= /flip_flip_lr_pmf.
      rewrite head_prim_step_pmf_eq /=; last first.
      { eexists (Val $ LitV $ LitBool true, _); simpl;
          eapply head_step_support_equiv_rel. eapply FlipNoTapeS. }
      rewrite /valid_flip_flip_lr /flips_bool /=.
      rewrite /pmf /=.
      destruct (decide (e2 = Val $ LitV $ LitBool true)) as [He2|].
      * rewrite He2 /=.
        erewrite SeriesC_ext;
          [eapply (SeriesC_singleton (Val $ LitV $ LitBool true, σ1'))|].
        intros [e' σ'].
        case_bool_decide as Heq.
        { destruct Heq as (?&?&?&?); simplify_eq.
          rewrite ?bool_decide_eq_true_2 //. }
        destruct (decide (σ1 = σ2)) as [->|Hneq]; last first.
        { case_match; [|done]. rewrite bool_decide_eq_false_2 //. }
        rewrite bool_decide_eq_false_2 //.
        intros [=]; simplify_eq. apply Heq.
        split_and!; eauto.
      * destruct (decide (e2 = Val $ LitV $ LitBool false)) as [He2'|]; last first.
        { rewrite SeriesC_0.
          - repeat case_match; try done. by destruct b.
          - intros [e σ]. rewrite bool_decide_eq_false_2 //.
            intros (?&?&?&?); simplify_eq. destruct x; eauto. }
        rewrite He2' /=.
        erewrite SeriesC_ext;
          [eapply (SeriesC_singleton (Val $ LitV $ LitBool false, σ1'))|].
        intros [e' σ'].
        case_bool_decide as Heq.
        { destruct Heq as (?&?&?&?); simplify_eq.
          rewrite ?bool_decide_eq_true_2 //. }
        destruct (decide (σ1 = σ2)) as [->|Hneq]; last first.
        { case_match; [|done]. rewrite bool_decide_eq_false_2 //. }
        rewrite bool_decide_eq_false_2 //.
        intros [=]; simplify_eq. apply Heq.
        split_and!; eauto.
    + (* same approach as for [lmarg] - TODO: better lemmas *)
      eapply distr_ext. intros [e2' σ2'].
      rewrite rmarg_pmf {1}/pmf /= /flip_flip_lr_pmf.
      rewrite head_prim_step_pmf_eq /=; last first.
      { eexists (Val $ LitV $ LitBool true, _); simpl.
        eapply head_step_support_equiv_rel. eapply FlipNoTapeS; eauto. }
      rewrite /valid_flip_flip_lr /flips_bool /=.
      rewrite /pmf /=.
      destruct (decide (e2' = Val $ LitV $ LitBool true)) as [He2|].
      * rewrite He2 /=.
        erewrite SeriesC_ext;
          [eapply (SeriesC_singleton (Val $ LitV $ LitBool true, σ1))|].
        intros [e' σ'].
        case_bool_decide as Heq.
        { destruct Heq as (?&?&?&?); simplify_eq.
          rewrite ?bool_decide_eq_true_2 //. }
        destruct (decide (σ1' = σ2')) as [->|Hneq]; last first.
        { case_match; [|done]. rewrite bool_decide_eq_false_2 //. }
        rewrite bool_decide_eq_false_2 //.
        intros [=]; simplify_eq. apply Heq.
        split_and!; eauto.
      * destruct (decide (e2' = Val $ LitV $ LitBool false)) as [He2'|]; last first.
        { rewrite SeriesC_0.
          - repeat case_match; try done. by destruct b.
          - intros [e σ]. rewrite bool_decide_eq_false_2 //.
            intros (?&?&?&?); simplify_eq. destruct x; eauto. }
        rewrite He2' /=.
        erewrite SeriesC_ext;
          [eapply (SeriesC_singleton (Val $ LitV $ LitBool false, σ1))|].
        intros [e' σ'].
        case_bool_decide as Heq.
        { destruct Heq as (?&?&?&?); simplify_eq.
          rewrite ?bool_decide_eq_true_2 //. }
        destruct (decide (σ1' = σ2')) as [->|Hneq]; last first.
        { case_match; [|done]. rewrite bool_decide_eq_false_2 //. }
        rewrite bool_decide_eq_false_2 //.
        intros [=]; simplify_eq. apply Heq.
        split_and!; eauto.
  - intros [[] []].
    rewrite /pmf /= /flip_flip_lr_pmf.
    case_bool_decide as Heq; [|lra].
    destruct Heq as (?&?&?&?). eauto.
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
| AllocTapePSP σ :
  prob_head_step_pred AllocTape σ
| FlipPSP l σ b bs :
  σ.(tapes) !! l = Some (b :: bs) →
  prob_head_step_pred (Flip (Val (LitV (LitLbl l)))) σ
| FlipEmptyPSP l σ :
  (σ.(tapes) !! l = Some [] ∨ σ.(tapes) !! l = None) →
  prob_head_step_pred (Flip (Val (LitV (LitLbl l)))) σ
| FlipNoTapePSP σ :
  prob_head_step_pred (Flip (Val (LitV LitUnit))) σ.

Definition head_step_pred e1 σ1 :=
  det_head_step_pred e1 σ1 ∨ prob_head_step_pred e1 σ1.

Lemma det_step_is_unique e1 σ1 e2 σ2 e3 σ3 :
  det_head_step_rel e1 σ1 e2 σ2 ->
  det_head_step_rel e1 σ1 e3 σ3 ->
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
    | H : det_head_step_dec _ _ _ = true |- _ =>
        rewrite /det_head_step_dec in H;
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

Lemma det_head_step_true e1 σ1 e2 σ2:
  det_head_step_dec e1 σ1 (e2, σ2) = true ↔ det_head_step_rel e1 σ1 e2 σ2.
Proof.
  split; intros H.
  - destruct e1; inv_det_head_step; by econstructor.
  - inversion H; simplify_eq; solve_step_det.
Qed.

Lemma det_head_step_singleton e1 σ1 e2 σ2 :
  det_head_step_rel e1 σ1 e2 σ2 → head_step e1 σ1 = dret (e2, σ2).
Proof.
  intros Hdet%det_head_step_true.
  apply pmf_1_eq_dret.
  rewrite /pmf /head_step /head_step_pmf Hdet //.
Qed.

Lemma val_not_head_step e1 σ1 :
  is_Some (to_val e1) → ¬ head_step_pred e1 σ1.
Proof.
  intros [] [Hs | Hs]; inversion Hs; simplify_eq.
Qed.

Lemma state_step_fair_conv_comb σ α :
  α ∈ dom σ.(tapes) →
  state_step σ α =
    fair_conv_comb
      (dret (state_upd_tapes <[α:=tapes σ !!! α ++ [true]]> σ))
      (dret (state_upd_tapes <[α:=tapes σ !!! α ++ [false]]> σ)).
Proof.
  intros Hdom.
  apply distr_ext=>σ2.
  rewrite {1}/pmf/=/state_step_pmf/valid_state_step.
  case_bool_decide as H.
  - destruct H as [_ [b ->]].
    rewrite fair_conv_comb_pmf /pmf/=/dret_pmf/=.
    case_bool_decide as H2; case_bool_decide as H3; simplify_eq; try lra.
    + rewrite H2 in H3.
       apply (f_equal (λ m, m !!! α)) in H3.
       do 2 rewrite lookup_total_insert in H3.
       simplify_map_eq.
    + destruct b; simplify_eq.
  - rewrite fair_conv_comb_pmf.
    assert (dret (state_upd_tapes <[α:=tapes σ !!! α ++ [true]]> σ) σ2 = 0 ∧
            dret (state_upd_tapes <[α:=tapes σ !!! α ++ [false]]> σ) σ2 = 0)
      as [-> ->]; [|lra].
    rewrite /pmf/=/dret_pmf.
    split; case_bool_decide; auto; destruct H; eauto.
Qed.

Lemma head_step_pred_ex_rel e1 σ1 :
  head_step_pred e1 σ1 ↔ ∃ e2 σ2, head_step_rel e1 σ1 e2 σ2.
Proof.
  split.
  - intros [Hdet | Hdet];
      inversion Hdet; simplify_eq; do 2 eexists; by econstructor.
  - intros (?&?& H). inversion H; simplify_eq; try by (left; econstructor).
    + right. econstructor.
    + right. by econstructor.
    + right. by econstructor.
    + right. by econstructor.
  Unshelve. all: apply true.
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
  det_head_step_pred e1 σ1 ∨ prob_head_step_pred e1 σ1 ∨ (∀ σ1', σ1.(heap) = σ1'.(heap) -> head_step e1 σ1' = dzero).
Proof.
  destruct (Rlt_le_dec 0 (SeriesC (head_step e1 σ1))) as [H1%Rlt_gt | H2].
  - pose proof (SeriesC_gtz_ex (head_step e1 σ1) (pmf_pos (head_step e1 σ1)) H1) as [[e2 σ2] Hρ].
    pose proof (head_step_support_equiv_rel e1 e2 σ1 σ2) as [H3 H4].
    specialize (H3 Hρ).
    assert (head_step_pred e1 σ1) as []; [|auto|auto].
    apply head_step_pred_ex_rel; eauto.
  - destruct H2; right; right; intros σ1' Heq.
    + pose proof (pmf_SeriesC_ge_0 (head_step e1 σ1)); lra.
    + pose proof (SeriesC_zero_dzero (head_step e1 σ1) H) as H2.
      apply not_head_step_pred_dzero in H2.
      apply not_head_step_pred_dzero.
      inversion 1 as [H4 | H5].
      * apply H2; left.
        inversion H4; try by (econstructor; eauto).
        { econstructor. rewrite Heq //. }
        { econstructor. rewrite Heq //. }
      * apply H2; right.
        inversion H5.
        { econstructor. }
        { destruct (decide (is_Some (tapes σ1 !! l))) as [[x HSome] | HNone%eq_None_not_Some].
          - destruct x; [apply FlipEmptyPSP | eapply FlipPSP]; eauto.
          - apply FlipEmptyPSP; eauto. }
        { destruct (decide (is_Some (tapes σ1 !! l))) as [[x HSome] | HNone%eq_None_not_Some].
          - destruct x; [apply FlipEmptyPSP | eapply FlipPSP]; eauto.
          - apply FlipEmptyPSP; eauto. }
        { econstructor. }
Qed.


  Lemma det_head_step_upd_tapes e1 σ1 e2 σ2 α b:
    det_head_step_rel e1 σ1 e2 σ2 →
    det_head_step_rel
      e1 (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [b]]> σ1)
      e2 (state_upd_tapes <[α := σ2.(tapes) !!! α ++ [b]]> σ2).
  Proof. inversion 1; econstructor; eauto. Qed.

  Lemma head_step_alloc_unfold σ:
    head_step alloc σ = dret (let l := fresh_loc (tapes σ) in (Val #lbl:l, state_upd_tapes <[fresh_loc (tapes σ):=[]]> σ) ) .
  Proof.
    apply distr_ext.
    intros (e2 & σ2).
    rewrite /pmf/head_step/head_step_pmf/=/dret_pmf.
    case_bool_decide as H; simplify_eq; auto.
    + case_bool_decide; simplify_eq; auto.
      destruct H; auto.
    + do 3 (case_match; auto).
      case_bool_decide; simplify_eq; auto.
      destruct H.
      destruct_and?.
      f_equal; auto.
      rewrite H; auto.
  Qed.

  Lemma head_step_flip_nonempty_unfold σ l b bs :
    σ.(tapes) !! l = Some (b :: bs) →
    head_step (flip #lbl:l) σ = dret (Val (LitV (LitBool b)), state_upd_tapes <[l:=bs]> σ).
  Proof.
    intro Hσ.
    apply distr_ext.
    intro ρ.
    rewrite /pmf/head_step/head_step_pmf/=/dret_pmf.
    do 4 (case_match; auto); simplify_eq.
    rewrite Hσ/=.
    case_bool_decide as H.
    + case_bool_decide as H2; auto.
      destruct H2; destruct_and?; simplify_eq.
      f_equal; auto.
    + case_bool_decide; auto.
      destruct H;
      simplify_eq; auto.
  Qed.


  Lemma head_step_flip_empty_unfold σ l  :
    σ.(tapes) !! l = Some ([]) →
    head_step (flip #lbl:l) σ = fair_conv_comb (dret (Val(#true), σ)) (dret (Val(#false), σ)).
  Proof.
    intro Hσ.
    apply distr_ext.
    intro ρ.
    rewrite /pmf/head_step/head_step_pmf/=/dbind_pmf/dret_pmf/=.
  Admitted.

  Lemma head_step_flip_unalloc_unfold σ l  :
    σ.(tapes) !! l = None →
    head_step (flip #lbl:l) σ = fair_conv_comb (dret (Val(#true), σ)) (dret (Val(#false), σ)).
  Proof.
  Admitted.

  Lemma upd_tape_some σ α b bs:
    tapes σ !! α = Some bs →
      tapes (state_upd_tapes <[α:=tapes σ !!! α ++ [b]]> σ) !! α =  Some (bs++[b]).
  Proof.
    Admitted.


  Lemma upd_tape_some_trivial σ α bs:
    tapes σ !! α = Some bs →
      state_upd_tapes <[α:=tapes σ !!! α]> σ = σ.
  Proof.
    Admitted.


  Lemma upd_tape_none σ α b :
    tapes σ !! α = None →
      tapes (state_upd_tapes <[α:=tapes σ !!! α ++ [b]]> σ) !! α =  Some ([b]).
  Proof.
    Admitted.

  Lemma upd_diff_tape σ α β b:
    α ≠ β →
    tapes σ !! α = tapes (state_upd_tapes <[β:=tapes σ !!! β ++ b]> σ) !! α.
  Proof.
    Admitted.

  Lemma upd_diff_tape_comm σ α β bs bs':
    α ≠ β →
    state_upd_tapes <[β:= bs]> (state_upd_tapes <[α := bs']> σ) =
    state_upd_tapes <[α:= bs']> (state_upd_tapes <[β := bs]> σ).
  Proof.
    Admitted.

  Lemma upd_diff_tape_tot σ α β bs:
    α ≠ β →
    tapes σ !!! α = tapes (state_upd_tapes <[β:=bs]> σ) !!! α.
  Proof. symmetry ; by rewrite lookup_total_insert_ne. Qed.

  Lemma upd_tape_twice σ β bs bs' :
    state_upd_tapes <[β:= bs]> (state_upd_tapes <[β:= bs']> σ) =
      state_upd_tapes <[β:= bs]> σ.
  Proof.
    Admitted.

  Lemma upd_tape_app σ α bs bs':
    state_upd_tapes <[α:=bs ++ bs']> σ =
    state_upd_tapes <[α:=tapes (state_upd_tapes <[α:=bs]> σ) !!! α ++ bs']>
                    (state_upd_tapes <[α:=bs]> σ).
  Proof.
    Admitted.


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
