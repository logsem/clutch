Global Set Default Proof Using "Type".
#[export] Set Suggest Proof Using. (* also warns about forgotten [Proof.] *)

(* Enforces that every tactic is executed with a single focused goal, meaning
that bullets and curly braces must be used to structure the proof. *)
#[export] Set Default Goal Selector "!".
Global Set Bullet Behavior "Strict Subproofs".

From Coq.Unicode Require Export Utf8.
From Coq.Classes Require Export Morphisms RelationClasses.
From Coq.ssr Require Export ssreflect.
From stdpp Require Export base tactics countable.

(* TODO: find a better solution *)
(* see [https://gitlab.mpi-sws.org/iris/stdpp/-/issues/182] *)
#[global] Remove Hints bool_countable fin_countable : typeclass_instances.
