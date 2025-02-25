Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From stdpp Require Import binders.
From mathcomp Require Import eqtype choice boolp classical_sets.
From mathcomp.analysis Require Export Rstruct.
From clutch.common Require Export locations.
From clutch.prob.monad Require Export giry.
From Coq Require Export Reals.
Set Warnings "hiding-delimiting-key".

(* Fix giryM to be the giry type with stdlib-valued real numbers *)
Notation giryM := (giryM (R := R)).

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
