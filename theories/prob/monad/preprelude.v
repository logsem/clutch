From HB Require Import structures.
From mathcomp Require Import all_ssreflect classical_sets boolp functions.
From clutch.prelude Require Import classical.
From mathcomp.analysis Require Import ereal measure lebesgue_measure lebesgue_integral sequences function_spaces.
From stdpp Require Import base decidable.

(* I have abosolutely no idea why it does this but when I put this code at the top of prelude
   it starts reflecting toPackedType into a Bool. There is no reason to do that so
   I am quaranitining this code. *)

(* A typeclass which contains the data of a measure space *)
Class SigmaAlgebra (d : measure_display) (T : Type) := {
    axioms : Measurable.axioms_ d T
}.

(* Take a type which has a SigmaAlgebra instance, and pack it into the type + SA struct *)
Definition toPackedType (d : measure_display) (T : Type) `{ SigmaAlgebra d T } : Measurable.type d :=
  @Measurable.Pack d T axioms.

(* Not sure if this is necessary yet (or what parts of Rocq can figure this out by reduction)
   but this takes a value and lifts it to a vlaue *)
Definition toPacked {d : measure_display} {T : Type} `{ SigmaAlgebra d T } (v : T) :
  @Measurable.sort d (toPackedType d T) := v.
