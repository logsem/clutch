From clutch.eris.examples.math Require Import prelude continuity2.
From clutch.eris Require Import infinite_tape.
Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.


(** AXIOM: Composition of a continuous function with an integrable function is integrable.

There are elementary proofs of this fact, but broadly speaking, they depend on more complex machinery
that is not yet mechanized in Coquelicot.  For example, that continuous functions on closed intervals
are uniformly continuous. *)
Axiom ex_RInt_comp_cts : ∀ (f g : R → R) {a b : R} (Hg : ∀ x, Continuity.continuous g x) (Hf : ex_RInt f a b),
  ex_RInt (fun x => (g (f x))) a b.


(** Precondition for the ∫∫ Fubini's theorem

Our Fubini's theorem axiom holds when a function is 2D continuous on a rectangle.
This variant of Fubini's theorem used by the Gaussian development. *)
Definition FubiniCondition (f : R → R → R_CompleteNormedModule) (xa xb ya yb : R) : Prop := forall x y,
  Rmin xa xb <= x <= Rmax xa xb →
  Rmin ya yb <= y <= Rmax ya yb →
  Continuity2 (uncurry f) x y.

(** AXIOM: Existence of ∫∫ integrals for 2D continuous functions *)
Axiom Fubini_ex_x : ∀ {f xa xb ya yb}, FubiniCondition f xa xb ya yb →
  ex_RInt (fun x => RInt (fun y => f x y) ya yb) xa xb.

(** AXIOM: Exchange of ∫∫ integrals for 2D continuous functions *)
Axiom Fubini_eq : ∀ {f xa xb ya yb}, FubiniCondition f xa xb ya yb →
  RInt (fun x => RInt (fun y => f x y) ya yb) xa xb =  RInt (fun y => RInt (fun x => f x y) xa xb) ya yb.
