From clutch.eris.examples.math Require Import prelude continuity2.
From clutch.eris Require Import infinite_tape.
Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.


(** Composition of a continuous function with an integrable function is integrable.

There are elementary proofs of this fact, but broadly speaking, they depend on more complex machinery
that is not yet mechanized in Coquelicot.  For example, that comtinuous functions on closed intervals
are uniformly continuous.
*)
Axiom ex_RInt_comp_cts : ∀ (f g : R → R) {a b : R} (Hg : ∀ x, Continuity.continuous g x) (Hf : ex_RInt f a b),
  ex_RInt (fun x => (g (f x))) a b.


(** The weak variant of Fubini's theorem:
  Fubini's theorem holds when a function is 2D continuous on a rectangle.
  This is the variant of Fubini's theorem used by the Gaussian development.
 *)
Definition FubiniCondition (f : R → R → R_CompleteNormedModule) (xa xb ya yb : R) : Prop := forall x y,
  Rmin xa xb <= x <= Rmax xa xb →
  Rmin ya yb <= y <= Rmax ya yb →
  Continuity2 (uncurry f) x y.

Axiom Fubini_ex_x : ∀ {f xa xb ya yb}, FubiniCondition f xa xb ya yb →
  ex_RInt (fun x => RInt (fun y => f x y) ya yb) xa xb.

Axiom Fubini_eq : ∀ {f xa xb ya yb}, FubiniCondition f xa xb ya yb →
  RInt (fun x => RInt (fun y => f x y) ya yb) xa xb =  RInt (fun y => RInt (fun x => f x y) xa xb) ya yb.

(** A stronger variant of Fubini's theorem: the integrand is permitted to be
  discontinuous along a line in 2D. This variant is neccessary for the
  maximum of two uniforms example.

  This is true because the set of discontinuities, namely a line, has measure zero.
  It does not reduce to our prior axiomatiziation in general.
 *)

(*
Section max_lazy_real_ax.
  Import Hierarchy.
  (** Axiomatize Fubini's theorem for functions of the form
        F (max (x, y))
      Given that F is 2D-continuous on a rectange.

   *)

  Definition MaxFubiniCondition (f : R → R_CompleteNormedModule) (a b : R) : Prop :=
    forall x, Rmin a b <= x <= Rmax a b → Continuity.continuous f x.

  Axiom Max_Fubini_ex_x : ∀ {f a b}, MaxFubiniCondition f a b →
    ex_RInt (fun x => RInt (fun y => f (Rmax x y)) a b) a b.

  Axiom Max_Fubini_ex_y : ∀ {f a b}, MaxFubiniCondition f a b →
    ex_RInt (fun y => RInt (fun x => f (Rmax x y)) a b) a b.

  Axiom Max_Fubini_eq : ∀ {f a b}, MaxFubiniCondition f a b →
     RInt (fun x => RInt (fun y => f (Rmax x y)) a b) a b =  RInt (fun y => RInt (fun x => f (Rmax x y)) a b ) a b.

End max_lazy_real_ax.
*)
