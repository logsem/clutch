Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From stdpp Require Import binders.
From mathcomp Require Import eqtype choice boolp classical_sets.
From mathcomp.analysis Require Export Rstruct.
From clutch.common Require Export locations.
From clutch.prob.monad Require Export giry.
From Coq Require Export Reals.
Set Warnings "hiding-delimiting-key".

(* Instances for Z *)
HB.instance Definition _ := gen_eqMixin Z.
HB.instance Definition _ := gen_choiceMixin Z.
HB.instance Definition _ := isPointed.Build Z inhabitant.
HB.saturate Z.

(* Instances for binder *)
HB.instance Definition _ := gen_eqMixin binder.
HB.instance Definition _ := gen_choiceMixin binder.
HB.instance Definition _ := isPointed.Build binder inhabitant.
HB.saturate binder.

(* Instances for loc *)
HB.instance Definition _ := gen_eqMixin loc.
HB.instance Definition _ := gen_choiceMixin loc.
HB.instance Definition _ := isPointed.Build loc inhabitant.
HB.saturate loc.

Hint Resolve gRet_meas_fun : measlang.


Local Open Scope classical_set_scope.

Definition loc_enum : nat -> <<discr loc>>. Admitted.
Lemma loc_enum_surj : forall l, exists n, loc_enum n = l.
Proof. Admitted.

Create HintDb ml_fun.
Create HintDb ml_set.
