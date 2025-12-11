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

