From stdpp Require Import countable numbers gmap.
From iris.prelude Require Export prelude.
From iris.prelude Require Import options.

Record loc := Loc { loc_car : Z }.

Add Printing Constructor loc.


Local Open Scope Z_scope.

Lemma loc_eq_spec l1 l2 : l1 = l2 ↔ loc_car l1 = loc_car l2.
  Proof. destruct l1, l2; naive_solver. Qed.

Global Instance loc_eq_decision : EqDecision loc.
Proof. solve_decision. Defined.

Global Instance loc_inhabited : Inhabited loc := populate {|loc_car := 0 |}.

Global Instance loc_countable : Countable loc.
Proof. by apply (inj_countable' loc_car Loc); intros []. Defined.

Global Program Instance loc_infinite : Infinite loc :=
  inj_infinite (λ p, {| loc_car := p |}) (λ l, Some (loc_car l)) _.
Next Obligation. done. Qed.

(* Global Instance loc_fresh : Fresh loc loc. *)
(* intros [z]. apply Loc. apply (fresh z).  *)

Definition loc_add (l : loc) (off : Z) : loc :=
  {| loc_car := loc_car l + off|}.

Definition loc_le (l1 l2 : loc) : Prop := loc_car l1 ≤ loc_car l2.

Definition loc_lt (l1 l2 : loc) : Prop := loc_car l1 < loc_car l2.


Notation "l +ₗ off" :=
  (loc_add l off) (at level 50, left associativity) : stdpp_scope.

Notation "l1 ≤ₗ l2" := (loc_le l1 l2) (at level 70) : stdpp_scope.
Notation "l1 <ₗ l2" := (loc_lt l1 l2) (at level 70) : stdpp_scope.

Lemma loc_add_assoc l i j : l +ₗ i +ₗ j = l +ₗ (i + j).
Proof. destruct l; rewrite /loc_add /=; f_equal; lia. Qed.

Lemma loc_add_0 l : l +ₗ 0 = l.
Proof. destruct l; rewrite /loc_add /=; f_equal; lia. Qed.

Global Instance loc_add_inj l : Inj eq eq (loc_add l).
Proof. destruct l; rewrite /Inj /loc_add /=; intros; simplify_eq; lia. Qed.

Definition fresh_locs (ls : gset loc) : loc :=
  {| loc_car := set_fold (λ k r, (1 + loc_car k) `max` r)%Z 1%Z ls |}.

Lemma fresh_locs_fresh ls i :
  (0 ≤ i)%Z → fresh_locs ls +ₗ i ∉ ls.
Proof.
  intros Hi. cut (∀ l, l ∈ ls → loc_car l < loc_car (fresh_locs ls) + i)%Z.
  { intros help Hf%help. simpl in *. lia. }
  apply (set_fold_ind_L (λ r ls, ∀ l, l ∈ ls → (loc_car l < r + i)%Z));
    set_solver by eauto with lia.
Qed.

Definition fresh_loc {V} (σ : gmap loc V) : loc := fresh (dom σ).

Lemma fresh_loc_is_fresh {V} (σ : gmap loc V) :
  fresh_loc σ ∉ dom σ.
Proof. apply is_fresh. Qed.

Lemma fresh_loc_offset_is_fresh {V} (σ : gmap loc V) i :
  (0 ≤ i)%Z → fresh_loc σ +ₗ i ∉ dom σ.
Proof.
  intros Hi. cut (∀ l, l ∈ (dom σ) → loc_car l < loc_car (fresh_loc σ) + i)%Z.
  { intros help Hf%help. simpl in *. lia. }
  rewrite /fresh_loc /fresh /set_fresh /=.
  rewrite /fresh /infinite_fresh /=.
  intros l Hl.
  apply elem_of_elements in Hl.
  induction (elements (dom σ)); auto.
  - inversion Hl.
  - simpl.
    rewrite -Z.add_max_distr_r.
    apply Z.max_lt_iff.
    inversion Hl.
    + simplify_eq.
      left. lia.
    + simplify_eq.
      right.
      auto.
Qed.

Lemma fresh_loc_eq_dom {V} (ls ls' : gmap loc V) :
  dom ls = dom ls' → fresh_loc ls = fresh_loc ls'.
Proof. rewrite /fresh_loc. by intros ->. Qed.

Global Instance loc_le_dec l1 l2 : Decision (l1 ≤ₗ l2).
Proof. rewrite /loc_le. apply _. Qed.

Global Instance loc_lt_dec l1 l2 : Decision (l1 <ₗ l2).
Proof. rewrite /loc_lt. apply _. Qed.

Global Instance loc_le_po : PartialOrder loc_le.
Proof.
  rewrite /loc_le. split; [split|].
  - by intros ?.
  - intros [x] [y] [z]; lia.
  - intros [x] [y] ??; f_equal/=; lia.
Qed.

Global Instance loc_le_total : Total loc_le.
Proof. rewrite /Total /loc_le. lia. Qed.

Lemma loc_le_ngt l1 l2 : l1 ≤ₗ l2 ↔ ¬l2 <ₗ l1.
Proof. apply Z.le_ngt. Qed.

Lemma loc_le_lteq l1 l2 : l1 ≤ₗ l2 ↔ l1 <ₗ l2 ∨ l1 = l2.
Proof. rewrite loc_eq_spec. apply Z.le_lteq. Qed.

Lemma loc_add_le_mono l1 l2 i1 i2 :
  l1 ≤ₗ l2 → i1 ≤ i2 → l1 +ₗ i1 ≤ₗ l2 +ₗ i2.
Proof. apply Z.add_le_mono. Qed.


Global Opaque fresh_locs fresh_loc.
