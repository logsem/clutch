From clutch.eris.examples.math Require Import prelude.
From clutch.eris Require Import infinite_tape.
Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(** Basic definitions for some sets *)

Definition Ioo (a b : R) : R → Prop :=
  fun x => Rmin a b < x < Rmax a b.

Definition Icc (a b : R) : R -> Prop :=
  fun t => Rmin a b <= t <= Rmax a b.

Definition Ici (a : R) : R -> Prop :=
  fun t => a <= t.

Definition Iic (b : R) : R -> Prop :=
  fun t => t <= b.

Definition Ioi (a : R) : R -> Prop :=
  fun t => a < t.

Definition Iio (b : R) : R -> Prop :=
  fun t => t < b.

Definition Iii : R -> Prop :=
  fun t => True.

Definition RII (X Y : R -> Prop) : R * R -> Prop :=
  fun '(tx, ty) => X tx /\ Y ty.

Definition On {T} (S U : T -> Prop) : Prop :=
  ∀ t, S t -> U t.

Definition Int {T} (S U : T -> Prop) : T -> Prop :=
  fun t => S t /\ U t.

Definition Bounded (f : R * R -> R) (M : R) : R * R -> Prop :=
  fun t => Rabs (f t) <= M.

Lemma Ioo_Icc {xa xb x} : Ioo xa xb x → Icc xa xb x.
Proof. rewrite /Ioo/Icc//=. lra. Qed.
