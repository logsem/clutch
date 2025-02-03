Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp Require Import functions.
From mathcomp.analysis Require Import reals measure itv lebesgue_measure probability.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp fintype.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.common Require Export locations.
From clutch.meas_lang Require Import ectxi_language ectx_language.

From Coq Require Export Reals.
From clutch.prob.monad Require Export laws extras.
From mathcomp.analysis Require Export Rstruct.

From mathcomp Require Import classical_sets.

Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.

Set Warnings "hiding-delimiting-key".

Create HintDb measlang.

(* Fix giryM to be the giry type with stdlib-valued real numbers *)
Notation giryM := (giryM (R := R)).

Global Instance classical_eq_dec {T : Type} : EqDecision T.
Proof. intros ??; apply ClassicalEpsilon.excluded_middle_informative. Defined.

(* Instances for Z *)
HB.instance Definition _ := gen_eqMixin Z.
HB.instance Definition _ := gen_choiceMixin Z.
HB.instance Definition _ := isPointed.Build Z inhabitant.

(* Instances for binder *)
HB.instance Definition _ := gen_eqMixin binder.
HB.instance Definition _ := gen_choiceMixin binder.
HB.instance Definition _ := isPointed.Build binder inhabitant.

(* Instances for loc *)
HB.instance Definition _ := gen_eqMixin loc.
HB.instance Definition _ := gen_choiceMixin loc.
HB.instance Definition _ := isPointed.Build loc inhabitant.

Hint Resolve giry_ret_measurable : measlang.
