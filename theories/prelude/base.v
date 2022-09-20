Global Set Default Proof Using "Type".
Export Set Suggest Proof Using. (* also warns about forgotten [Proof.] *)

(* Enforces that every tactic is executed with a single focused goal, meaning
that bullets and curly braces must be used to structure the proof. *)
Export Set Default Goal Selector "!".
Global Set Bullet Behavior "Strict Subproofs".

From Coq.Unicode Require Export Utf8.
From Coq.Classes Require Export Morphisms RelationClasses.
From Coq.ssr Require Export ssreflect.
From stdpp Require Export base tactics.
