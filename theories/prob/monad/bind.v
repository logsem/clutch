(** Bind *)

From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed (* topology *) normedtype esum numfun measure lebesgue_measure lebesgue_integral.
From HB Require Import structures.


From clutch.prob.monad Require Export types join map.

Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type".

(*
Section bind.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d1} {T1 : measurableType d1}.
  Context {d2} {T2 : measurableType d2}.

  Definition giryM_bind (f : T1 -> (giryM T2)) (Hf : measurable_fun setT f): giryM T1 -> giryM T2
    := ssrfun.comp giryM_join (giryM_map f Hf).

  (** This is probably the one you want to use *)
  Definition giryM_bind_external (m : giryM T1) (f : T1 -> (giryM T2)) : giryM T2 :=
    giryM_join (giryM_map_external f m).

  Lemma giryM_bind_external_eq (m : giryM T1) (f : T1 -> (giryM T2)) (H : measurable_fun setT f) :
    giryM_bind_external m f = giryM_bind H m.
  Proof.
    rewrite /giryM_bind_external/giryM_bind/giryM_map_external.
    rewrite /ssrfun.comp//=.
    f_equal.
    by rewrite extern_if_eq.
  Qed.

  Definition giryM_bind_meas (f : T1 -> (giryM T2)) (Hf : measurable_fun setT f):
    measurable_fun setT (@giryM_bind f Hf).
  Proof. Admitted.

  (** Use this form when you want bind to be measurable *)
  Lemma giryM_bind_external'_meas (f : T1 -> (giryM T2)) (Hf : measurable_fun setT f) :
    measurable_fun setT (giryM_bind_external ^~ f).
  Proof.
    suffices -> : (giryM_bind_external^~ f) = (@giryM_bind f Hf) by apply giryM_bind_meas.
    apply functional_extensionality.
    intro m.
    by apply giryM_bind_external_eq.
  Qed.

End bind.

*)
