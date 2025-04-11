From Coq Require Export Reals Psatz ssrfun.
(*
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export fixpoint big_op.
From iris.prelude Require Import options.
From iris.algebra Require Import ofe. *)

From mathcomp.analysis Require Import measure.
(* From mathcomp.classical Require Import classical_sets. *)

(*
From clutch.prelude Require Import stdpp_ext iris_ext NNRbar.
From clutch.meas_lang Require Export language erasable.
From clutch.meas_lang Require Export meas_spec_update. *)
(* From clutch.bi Require Export weakestpre. *)
(*  From clutch.prob Require Export couplings_app distribution. *)

From mathcomp.analysis Require Import reals measure lebesgue_measure lebesgue_integral sequences function_spaces Rstruct.
From clutch.prob.monad Require Import prelude.
(* From stdpp Require Import base. *)
From Coq Require Import Reals.
From Coq.Bool Require Import Bool.
Require Import Coq.ssr.ssrbool.

From mathcomp.analysis Require Import constructive_ereal.

Local Open Scope R.

Ltac unfold_mathcomp :=
  unfold order.Order.le,
         ssralg.GRing.mul,
         order.Order.le,
         order.Order.lt,
         ssralg.GRing.mul,
         ssralg.GRing.natmul,
         ssralg.GRing.one,
         ssralg.GRing.zero,
         ssralg.GRing.add in *;
  simpl.

Ltac destroy_mathcomp :=
  unfold_mathcomp;
  match goal with
  | |- Is_true _ => apply Is_true_eq_left
                        
  | |- ((Rleb _ _) = true) => apply (Coq.ssr.ssrbool.introT (RlebP _ _))
  | |- is_true (Rleb _ _) => apply (Coq.ssr.ssrbool.introT (RlebP _ _))
  | H : ((Rleb _ _) = true) |- _ => apply (Coq.ssr.ssrbool.elimT (RlebP _ _)) in H
                                        
  | |- ((Rltb _ _) = true) => apply (Coq.ssr.ssrbool.introT (RltbP _ _))
  | |- is_true (Rltb _ _) => apply (Coq.ssr.ssrbool.introT (RltbP _ _))
  | H : ((Rltb _ _) = true) |- _ => apply (Coq.ssr.ssrbool.elimT (RltbP _ _)) in H
  | _ => idtac
  end.
