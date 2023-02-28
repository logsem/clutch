From Coq Require Import Reals Psatz.
From stdpp Require Import functions fin_maps gmap stringmap.
From self.prelude Require Import stdpp_ext.
From self.prob Require Import distribution couplings.
From self.prob_lang Require Export lang tactics notation.
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
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Alloc e | Load e | Flip e =>
     is_closed_expr X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Store e1 e2 =>
     is_closed_expr X e1 && is_closed_expr X e2
  | If e0 e1 e2 | Case e0 e1 e2 =>
     is_closed_expr X e0 && is_closed_expr X e1 && is_closed_expr X e2
  | AllocTape _ => true
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
  | AllocTape n => AllocTape n
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

Lemma head_step_flip_nonempty_unfold σ l n z zs :
  σ.(tapes) !! l = Some (n, z :: zs) →
  head_step (flip #lbl:l) σ = dret (Val (LitV (LitInt z)), state_upd_tapes <[l:=(n,zs)]> σ).
Proof.
  intro Hσ.
  apply distr_ext.
  intros [].
  rewrite head_step_pmf_eq /pmf/=/dret_pmf.
  do 3 (case_match; auto); simplify_eq.
  rewrite Hσ/=.
  case_bool_decide as H.
  + case_bool_decide as H2; auto.
    destruct H2; destruct_and?; simplify_eq.
    f_equal; auto.
  + case_bool_decide; auto.
    destruct H;
      simplify_eq; auto.
Qed.

Lemma head_step_flip_no_tape_unfold σ  :
  head_step (flip #()) σ = fair_conv_comb (dret (Val #true, σ)) (dret (Val #false, σ)).
Proof.
  apply distr_ext. intros [e σ'].
  rewrite fair_conv_comb_pmf.
  rewrite head_step_pmf_eq.
  rewrite /pmf /= /dret_pmf.
  case_bool_decide; last first.
  { rewrite ?bool_decide_eq_false_2;
      [repeat case_match; lra| |]; intros [=]; simplify_eq. }
  simplify_eq.
  do 3
    (case_match;
    try by (rewrite ?bool_decide_eq_false_2;
            [repeat case_match;lra | |]; intros [=]; simplify_eq)).
  destruct b.
  - rewrite bool_decide_eq_true_2 // bool_decide_eq_false_2 //. lra.
  - rewrite bool_decide_eq_false_2 // bool_decide_eq_true_2 //. lra.
Qed.

Lemma head_step_flip_empty_unfold σ l n :
  σ.(tapes) !! l = Some (n, []) →
  head_step (flip #lbl:l) σ = dmap (λ m, (Val (LitV (LitInt (Z.of_nat m))), σ)) (unif_distr n).
Proof.
  intro Hσ. apply distr_ext. intros [e σ'].
  symmetry.
  rewrite head_step_pmf_eq.
  rewrite /dmap.
  rewrite /head_step_pmf /=.
  do 3 (case_match;
    (* Get of trivial cases *)
    try (apply dbind_dret_unif_zero; intros; auto)).
  rewrite Hσ.
  case_bool_decide as H2.
  - destruct_and?.
    apply dbind_dret_unif_nonzero; [intros ? ? H4; inversion H4; lia | ].
    exists (Z.to_nat n0); split; try lia.
    f_equal; auto; try lia.
    do 3 f_equal.
    apply Z2Nat.id; auto.
  - apply dbind_dret_unif_zero.
    intros.
    intro H4; inversion H4; simplify_eq.
    eapply H2; split; auto.
    lia.
Qed.

Lemma head_step_flip_unalloc_unfold σ l  :
  σ.(tapes) !! l = None →
  head_step (flip #lbl:l) σ = fair_conv_comb (dret (Val #1, σ)) (dret (Val #0, σ)).
Proof.
  intro Hσ. apply distr_ext. intros [e σ'].
  rewrite head_step_pmf_eq.
  rewrite fair_conv_comb_pmf.
  rewrite /pmf /= /dret_pmf Hσ.
  case_bool_decide; case_bool_decide; simplify_eq.
  - rewrite bool_decide_eq_true_2; repeat (try split); auto; try lra; try lia.
  - rewrite bool_decide_eq_true_2; repeat (try split); auto; try lra; try lia.
  - do 3 (case_match; try lra).
    case_bool_decide; try lra.
    destruct_and?; simplify_eq.
    assert (n = 0%Z \/ n = 1%Z) as [Hn0 | Hn1] ; try lia; simplify_eq.
Qed.


(*
Updating this to uniform state steps may not be needed,
since the definition is already binding the uniform distribution

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

*)

Local Lemma Rcoupl_flip_dret_bij f `{Inj bool bool (=) (=) f, Surj bool bool (=) f} b (σ1 σ1' : state) :
  Rcoupl
    (if f b then dret (Val #true, σ1) else dret (Val #false, σ1))
    (if b then dret (Val #true, σ1') else dret (Val #false, σ1'))
    (λ ρ2 ρ2', ∃ b : bool, (ρ2, ρ2') = (Val #b, σ1, (Val #(f b), σ1'))).
Proof.
  destruct b.
  - destruct (f true) eqn:Hf1; apply Rcoupl_dret.
    + exists true. rewrite Hf1 //.
    + exists false. by erewrite bool_fn_inj_1.
  - destruct (f false) eqn:Hf1; apply Rcoupl_dret.
    + exists true. by erewrite bool_fn_inj_1.
    + exists false. rewrite Hf1 //.
Qed.

(** * flip(α) ~ flip(α') coupling *)
Lemma Rcoupl_flip_flip_empty f `{Inj bool bool (=) (=) f, Surj bool bool (=) f} σ1 σ1' α α' :
  σ1.(tapes) !! α = Some [] →
  σ1'.(tapes) !! α' = Some [] →
  Rcoupl
    (prim_step (Flip (Val $ LitV $ LitLbl α)) σ1)
    (prim_step (Flip (Val $ LitV $ LitLbl α')) σ1')
    (λ ρ2 ρ2', ∃ (b : bool), (ρ2, ρ2') = ((Val #b, σ1), (Val #(f b), σ1'))).
Proof.
  intros Hα Hα'.
  rewrite 2?head_prim_step_eq /=; last first.
  { eexists (_, _); simpl. eapply head_step_support_equiv_rel.
    eapply (FlipTapeEmptyS _ true). eauto. }
  { eexists (_, _); simpl. eapply head_step_support_equiv_rel.
    eapply (FlipTapeEmptyS _ true). eauto. }
  rewrite 2?head_step_flip_empty_unfold //.
  eapply (Rcoupl_fair_conv_comb f).
  intros. apply (Rcoupl_flip_dret_bij f).
Qed.

(** * flip(α) ~ flip(unit) coupling *)
Lemma Rcoupl_flip_flip_l f `{Inj bool bool (=) (=) f, Surj bool bool (=) f} σ1 σ1' α :
  σ1.(tapes) !! α = Some [] →
  Rcoupl
    (prim_step (Flip (Val $ LitV $ LitLbl α)) σ1)
    (prim_step (Flip (Val $ LitV $ LitUnit)) σ1')
    (λ ρ2 ρ2', ∃ (b : bool), (ρ2, ρ2') = ((Val #b, σ1), (Val #(f b), σ1'))).
Proof.
  intros Hα.
  rewrite head_prim_step_eq /=; last first.
  { eexists (_, _); simpl. eapply head_step_support_equiv_rel.
    eapply (FlipTapeEmptyS _ true). eauto. }
  rewrite head_prim_step_eq /=; last first.
  { eexists (_, _); simpl. eapply head_step_support_equiv_rel.
    eapply (FlipNoTapeS true). }
  rewrite head_step_flip_empty_unfold //.
  rewrite head_step_flip_no_tape_unfold //.
  eapply (Rcoupl_fair_conv_comb f).
  intros. apply (Rcoupl_flip_dret_bij f).
Qed.

(** * flip(unit) ~ flip(α) coupling *)
Lemma Rcoupl_flip_flip_r f `{Inj bool bool (=) (=) f, Surj bool bool (=) f} σ1 σ1' α' :
  σ1'.(tapes) !! α' = Some [] →
  Rcoupl
    (prim_step (Flip (Val $ LitV $ LitUnit)) σ1)
    (prim_step (Flip (Val $ LitV $ LitLbl α')) σ1')
    (λ ρ2 ρ2', ∃ (b : bool), (ρ2, ρ2') = ((Val #b, σ1), (Val #(f b), σ1'))).
Proof.
  intros Hα.
  rewrite head_prim_step_eq /=; last first.
  { eexists (_, _); simpl. eapply head_step_support_equiv_rel.
    eapply (FlipNoTapeS true). }
  rewrite head_prim_step_eq /=; last first.
  { eexists (_, _); simpl. eapply head_step_support_equiv_rel.
    eapply (FlipTapeEmptyS _ true). eauto. }
  rewrite head_step_flip_empty_unfold //.
  rewrite head_step_flip_no_tape_unfold //.
  eapply (Rcoupl_fair_conv_comb f).
  intros. apply (Rcoupl_flip_dret_bij f ).
Qed.

(** * flip(unit) ~ flip(unit) coupling *)
Lemma Rcoupl_flip_flip_lr f `{Inj bool bool (=) (=) f, Surj bool bool (=) f} σ1 σ1' :
  Rcoupl
    (prim_step (Flip (Val $ LitV $ LitUnit)) σ1)
    (prim_step (Flip (Val $ LitV $ LitUnit)) σ1')
    (λ ρ2 ρ2', ∃ (b : bool), (ρ2, ρ2') = ((Val #b, σ1), (Val #(f b), σ1'))).
Proof.
  rewrite 2?head_prim_step_eq /=; last first.
  { eexists (_, _); simpl. eapply head_step_support_equiv_rel.
    eapply (FlipNoTapeS true). }
  { eexists (_, _); simpl. eapply head_step_support_equiv_rel.
    eapply (FlipNoTapeS true). }
  rewrite 2!head_step_flip_no_tape_unfold //.
  eapply (Rcoupl_fair_conv_comb f).
  intros. apply (Rcoupl_flip_dret_bij f ).
Qed.

(** * state_step(α) ~ state_step(α') coupling *)
Lemma Rcoupl_state_step f `{Inj bool bool (=) (=) f, Surj bool bool (=) f} σ1 σ2 α1 α2 :
  α1 ∈ dom σ1.(tapes) →
  α2 ∈ dom σ2.(tapes) →
  Rcoupl
    (state_step σ1 α1)
    (state_step σ2 α2)
    (λ σ1' σ2', ∃ b,
        σ1' = state_upd_tapes <[α1 := σ1.(tapes) !!! α1 ++ [b]]> σ1 ∧
        σ2' = state_upd_tapes <[α2 := σ2.(tapes) !!! α2 ++ [f b]]> σ2).
Proof.
  intros Hα1 Hα2.
  rewrite 2?state_step_fair_conv_comb //.
  eapply (Rcoupl_fair_conv_comb f).
  (* TODO: extract a lemma for this *)
  intros [].
  - destruct (f true) eqn:Hf; apply Rcoupl_dret.
    + exists true. rewrite Hf //.
    + exists false. by erewrite bool_fn_inj_1.
  - destruct (f false) eqn:Hf; apply Rcoupl_dret.
    + exists true. by erewrite bool_fn_inj_1.
    + exists false. rewrite Hf //.
Qed.

(** * flip(unit) ~ state_step(α') coupling *)
Lemma Rcoupl_flip_state f `{Inj bool bool (=) (=) f, Surj bool bool (=) f} σ1 σ1' α' :
  α' ∈ dom σ1'.(tapes) →
  Rcoupl
    (prim_step (Flip (Val $ LitV $ LitUnit)) σ1)
    (state_step σ1' α')
    (λ ρ2 σ2', ∃ (b : bool),
        ρ2 = (Val #b, σ1) ∧ σ2' = state_upd_tapes <[α' := σ1'.(tapes) !!! α' ++ [f b]]> σ1').
Proof.
  intros Hα'.
  rewrite head_prim_step_eq /=; last first.
  { eexists (_, _); simpl. eapply head_step_support_equiv_rel.
    eapply (FlipNoTapeS true). }
  rewrite head_step_flip_no_tape_unfold //.
  rewrite state_step_fair_conv_comb //.
  eapply (Rcoupl_fair_conv_comb f).
  intros [].
  - destruct (f true) eqn:Hf; apply Rcoupl_dret.
    + exists true. rewrite Hf //.
    + exists false. by erewrite bool_fn_inj_1.
  - destruct (f false) eqn:Hf; apply Rcoupl_dret.
    + exists true. by erewrite bool_fn_inj_1.
    + exists false. rewrite Hf //.
Qed.

(** * state_step(α) ~ flip(unit) coupling *)
Lemma Rcoupl_state_flip f `{Inj bool bool (=) (=) f, Surj bool bool (=) f} σ1 σ1' α :
  α ∈ dom σ1.(tapes) →
  Rcoupl
    (state_step σ1 α)
    (prim_step (Flip (Val $ LitV $ LitUnit)) σ1')
    (λ σ2 ρ2', ∃ (b : bool),
        σ2 = state_upd_tapes <[α := σ1.(tapes) !!! α ++ [b]]> σ1 ∧ ρ2' = (Val #(f b), σ1')).
Proof.
  intros Hα'.
  rewrite head_prim_step_eq /=; last first.
  { eexists (_, _); simpl. eapply head_step_support_equiv_rel.
    eapply (FlipNoTapeS true). }
  rewrite head_step_flip_no_tape_unfold //.
  rewrite state_step_fair_conv_comb //.
  eapply (Rcoupl_fair_conv_comb f).
  intros [].
  - destruct (f true) eqn:Hf; apply Rcoupl_dret.
    + exists true. rewrite Hf //.
    + exists false. by erewrite bool_fn_inj_1.
  - destruct (f false) eqn:Hf; apply Rcoupl_dret.
    + exists true. by erewrite bool_fn_inj_1.
    + exists false. rewrite Hf //.
Qed.

(** * e1 ~ flip(α') coupling for α' ↪ₛ [] *)
Lemma Rcoupl_flip_empty_r (ρ1 : cfg) σ1' α' (_ : tapes σ1' !! α' = Some []) :
  Rcoupl
    (dret ρ1)
    (prim_step (Flip (Val $ LitV $ LitLbl α')) σ1')
    (λ ρ2 ρ2', ∃ (b : bool), ρ2 = ρ1 ∧ ρ2' = (Val #b, σ1')).
Proof.
  assert (head_reducible (flip #lbl:α') σ1') as hr.
  { econstructor.
    apply head_step_support_equiv_rel.
    apply (FlipTapeEmptyS _ inhabitant). auto. }
  rewrite head_prim_step_eq //.
  eapply Rcoupl_weaken.
  - apply Rcoupl_pos_R. apply Rcoupl_trivial.
    all: auto using dret_mass, head_step_mass.
  - intros ? [] (_ & hh%dret_pos & ?).
    inv_head_step.
    destruct_or?.
    + inv_head_step. eauto.
    + simplify_map_eq.
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

Lemma upd_tape_some σ α b bs:
  tapes σ !! α = Some bs →
  tapes (state_upd_tapes <[α:=tapes σ !!! α ++ [b]]> σ) !! α =  Some (bs++[b]).
Proof.
  intros ?. rewrite /state_upd_tapes /=.
  rewrite lookup_insert.
  by erewrite lookup_total_correct.
Qed.

Lemma upd_tape_some_trivial σ α bs:
  tapes σ !! α = Some bs →
  state_upd_tapes <[α:=tapes σ !!! α]> σ = σ.
Proof.
  destruct σ. simpl.
  intros ?. rewrite /state_upd_tapes /=.
  erewrite lookup_total_correct; [|done].
  f_equal.
  by apply insert_id.
Qed.

Lemma upd_tape_none σ α b :
  tapes σ !! α = None →
  tapes (state_upd_tapes <[α:=tapes σ !!! α ++ [b]]> σ) !! α =  Some ([b]).
Proof.
  intros ?. rewrite /state_upd_tapes /=.
  rewrite lookup_total_correct_2 //=.
  rewrite lookup_insert //.
Qed.

Lemma upd_diff_tape σ α β b:
  α ≠ β →
  tapes σ !! α = tapes (state_upd_tapes <[β:=tapes σ !!! β ++ b]> σ) !! α.
Proof.
  intros ?. rewrite /state_upd_tapes /=.
  rewrite lookup_insert_ne //.
Qed.

Lemma upd_diff_tape_comm σ α β bs bs':
  α ≠ β →
  state_upd_tapes <[β:= bs]> (state_upd_tapes <[α := bs']> σ) =
    state_upd_tapes <[α:= bs']> (state_upd_tapes <[β := bs]> σ).
Proof.
  intros. rewrite /state_upd_tapes /=.
  rewrite insert_commute //.
Qed.

Lemma upd_diff_tape_tot σ α β bs:
  α ≠ β →
  tapes σ !!! α = tapes (state_upd_tapes <[β:=bs]> σ) !!! α.
Proof. symmetry ; by rewrite lookup_total_insert_ne. Qed.

Lemma upd_tape_twice σ β bs bs' :
  state_upd_tapes <[β:= bs]> (state_upd_tapes <[β:= bs']> σ) = state_upd_tapes <[β:= bs]> σ.
Proof. rewrite /state_upd_tapes insert_insert //. Qed.

Lemma upd_tape_app σ α bs bs':
  state_upd_tapes <[α:=bs ++ bs']> σ =
    state_upd_tapes <[α:=tapes (state_upd_tapes <[α:=bs]> σ) !!! α ++ bs']>
      (state_upd_tapes <[α:=bs]> σ).
Proof.
  destruct σ. rewrite /state_upd_tapes /=. f_equal.
  rewrite lookup_total_insert.
  rewrite insert_insert //.
Qed.

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
