(* TODO cleanup imports *)
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
From clutch.prob.monad Require Export giry.
From mathcomp.analysis Require Export Rstruct.
From mathcomp Require Import classical_sets.
Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude types constructors shapes cover projections tapes state cfg.
Set Warnings "hiding-delimiting-key".

Local Open Scope classical_set_scope.

Definition load_eval_cov_ok : set (<<discr loc>> * state)%type. Admitted.
(*
Definition auxcov_load_ok : set (<<discr loc>> * state)%type :=
  preimage (ssrfun.comp hp_evalC $ mProd fst (ssrfun.comp heap snd)) option_cov_Some.
*)

Lemma load_eval_cov_ok_meas_set : measurable load_eval_cov_ok. Admitted.
(*
By the measurablity of that function
 *)

Hint Resolve load_eval_cov_ok_meas_set : mf_set.

Definition load_eval_ok : (<<discr loc>> * state)%type -> giryM cfg :=
  gRet \o (ValU \o of_option (hp_evalC \o (fst △ heap \o snd)) △ snd).

Lemma load_eval_ok_meas_fun : measurable_fun load_eval_cov_ok load_eval_ok. Admitted.

Definition load_eval : (<<discr loc>> * state)%type -> giryM cfg :=
  if_in load_eval_cov_ok load_eval_ok (cst gZero).

Lemma load_eval_meas_fun : measurable_fun setT load_eval. Admitted.

Hint Resolve load_eval_meas_fun : mf_fun.





(*
    | AllocN (Val (LitV (LitInt N))) (Val v) =>
        if bool_decide (0 < Z.to_nat N)%nat
          then
            let ℓ := fresh_loc σ1.(heap) in
            giryM_ret R ((Val $ LitV $ LitLoc ℓ, state_upd_heap_N ℓ (Z.to_nat N) v σ1) : cfg)
          else giryM_zero
*)

(* Case split on whether a finite or infinite *)
Definition alloc_eval_cov_ok : set (val * state)%type. Admitted.

Lemma alloc_eval_cov_ok_meas_set : measurable alloc_eval_cov_ok. Admitted.

Hint Resolve alloc_eval_cov_ok_meas_set : mf_set.


Definition alloc_eval_ok : (val * state)%type -> giryM cfg :=
  gRet \o (ValU \o LitVU \o LitLocU \o fresh \o heap \o snd △
          (state_of_prod \o
            ( hp_updateC \o (fresh \o heap \o snd △ (Some \o fst △ heap \o snd))
            △ tapes \o snd
            △ utapes \o snd))).

Lemma alloc_eval_ok_meas_fun : measurable_fun alloc_eval_cov_ok alloc_eval_ok. Admitted.

Hint Resolve alloc_eval_ok_meas_fun : mf_fun.

Definition alloc_eval : (val * state)%type -> giryM cfg :=
  if_in alloc_eval_cov_ok alloc_eval_ok (cst gZero).

Lemma alloc_eval_meas_fun : measurable_fun setT alloc_eval. Admitted.

Hint Resolve alloc_eval_ok_meas_fun : mf_fun.






(*






(* AllocN: the state part of the result *)

Definition state_allocNCS : (val * state)%type -> state :=
  ssrfun.comp state_of_prod $
  mProd
    (mProd
      (ssrfun.comp hp_updateC $
       mProd
         (ssrfun.comp fresh $ ssrfun.comp heap snd)
         (mProd
            (ssrfun.comp Some fst)
            (ssrfun.comp heap snd)))
      (ssrfun.comp tapes snd))
    (ssrfun.comp utapes snd).


(*
  state_upd_heap_N (fresh_loc x.2.(heap)) (Z.to_nat x.1.1) x.1.2 x.2.
*)
(* AllocN: the state part of the result *)
Definition state_allocNCE : (val * state)%type -> <<discr loc>> :=
  ssrfun.comp fresh $ ssrfun.comp heap snd.

(** FIXME: Rename to remove N*)
Definition auxcov_allocN_ok : set (val * state)%type :=
  setX setT $ preimage heap (hp_finite _).

Definition auxcov_allocN_stuck: set (val * state)%type :=
  ~` auxcov_allocN_ok.

Lemma auxcov_allocN_ok_meas : measurable auxcov_allocN_ok.
Proof.
Admitted.
Hint Resolve auxcov_allocN_ok_meas : measlang.

Lemma auxcov_allocN_stuck_meas : measurable auxcov_allocN_stuck.
Proof. Admitted.
Hint Resolve auxcov_allocN_stuck_meas : measlang.

Lemma state_allocNCE_meas : measurable_fun auxcov_allocN_ok state_allocNCE.
Proof.
Admitted.
Hint Resolve state_allocNCE_meas : measlang.

Lemma state_allocNCS_meas : measurable_fun auxcov_allocN_ok state_allocNCS.
Proof.
Admitted.
Hint Resolve state_allocNCS_meas : measlang.


(*
    | Store (Val (LitV (LitLoc l))) (Val w) =>
        match σ1.(heap) !! l with
          | Some v => giryM_ret R ((Val $ LitV LitUnit, state_upd_heap <[l:=w]> σ1) : cfg)
          | None => giryM_zero
        end
 *)


(* store: the state part of the result *)
Definition state_storeS : <<discr loc>> * val * state -> state :=
  ssrfun.comp state_of_prod $
  mProd
    (mProd
      (ssrfun.comp hp_updateC $
       mProd
         (ssrfun.comp fst fst)
         (mProd
            (ssrfun.comp Some $ ssrfun.comp snd fst)
            (ssrfun.comp heap snd)))
      (ssrfun.comp tapes snd))
  (ssrfun.comp utapes snd).

(* store: the expression part of the result *)
Definition state_storeE : (<<discr loc>> * val * state) -> expr :=
  cst $ ValU $ LitV $ LitUnit.

Definition auxcov_store_ok : set (<<discr loc>> * val * state)%type :=
  preimage
    (ssrfun.comp hp_evalC $ mProd (ssrfun.comp fst fst) (ssrfun.comp heap snd))
    (@option_cov_Some _ val).

Definition auxcov_store_stuck : set (<<discr loc>> * val * state)%type :=
  ~` auxcov_store_ok.

Lemma auxcov_store_ok_meas : measurable auxcov_store_ok.
Proof. Admitted.
Hint Resolve auxcov_store_ok_meas : measlang.

Lemma auxcov_store_stuck_meas : measurable auxcov_store_stuck.
Proof. Admitted.
Hint Resolve auxcov_store_stuck_meas : measlang.

Lemma state_storeS_meas : measurable_fun auxcov_store_ok state_storeS.
Proof.
Admitted.
Hint Resolve state_storeS_meas : measlang.

Lemma state_storeE_meas : measurable_fun auxcov_store_ok state_storeE.
Proof.
Admitted.
Hint Resolve state_storeE_meas : measlang.
*)
