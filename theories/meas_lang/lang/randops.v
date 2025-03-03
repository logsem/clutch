(* TODO cleanup imports *)
Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp Require Import functions.
From mathcomp.analysis Require Import reals measure itv lebesgue_measure probability.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
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
Require Import ssrfun.
Set Warnings "hiding-delimiting-key".

Local Open Scope classical_set_scope.

Local Notation RR := ((R : realType) : measurableType _)%type.

(* FIXME: Move *)
Section unif.
  Local Open Scope ereal_scope.

  Axiom unif_base : giryM RR.
    (* broken, how do
        := @uniform_prob _ _ _ _.
        (@Num.Internals.ltr01 TR). *)

  Axiom unifN_base : <<discr Z>> -> giryM <<discr Z>>.

  Lemma unifN_base_meas_fun : measurable_fun setT unifN_base.
  Proof. (* Function from discrete *) Admitted.
  Hint Resolve unifN_base_meas_fun : mf_fun.

End unif.

(* The set of states with a finite number of tapes *)
Definition AllocTape_eval_cov_ok : set (<<discr Z>> * state)%type :=
  setT `*` (setT `&` tapes @^-1` hp_finite).

(* The set of states with a finite number of utapes *)
Definition AllocUTape_eval_cov_ok : set state :=
  setT `&` utapes @^-1` hp_finite.

Definition RandT_eval_cov_noTape' (_ : <<discr Z>>) (ℓ  : <<discr loc>>) : set state :=
  (hp_eval ℓ \o tapes) @^-1` option_cov_None.

(* Location ℓ has no tape *)
Definition RandT_eval_cov_noTape : set (<<discr Z>> * <<discr loc>> * state)%type :=
  \bigcup_z \bigcup_l [set (z, l, σ) | σ in RandT_eval_cov_noTape' z l].

(* Location ℓ has a tape with the bound not equal to z *)
Definition RandT_eval_cov_boundMismatch' (z : <<discr Z>>) (ℓ  : <<discr loc>>) : set state :=
      ((hp_eval ℓ \o tapes) @^-1` option_cov_Some)
  `&` ((fst \o of_option (hp_eval ℓ \o tapes)) @^-1` [set t : <<discr nat>> | t ≠ Z.to_nat z]).

Definition RandT_eval_cov_boundMismatch : set (<<discr Z>> * <<discr loc>> * state)%type :=
  \bigcup_z \bigcup_l [set (z, l, σ) | σ in RandT_eval_cov_boundMismatch' z l].

(* Location ℓ has a tape with the right bound but the next space empty *)
Definition RandT_eval_cov_nextEmpty' (z : <<discr Z>>) (ℓ  : <<discr loc>>) : set state :=
      ((hp_eval ℓ \o tapes) @^-1` option_cov_Some)
  `&` ((fst \o of_option (hp_eval ℓ \o tapes)) @^-1` [set t : <<discr nat>> | t ≠ Z.to_nat z])
  `&` ((sequence_evalC \o snd \o (of_option (hp_eval ℓ \o tapes))) @^-1` option_cov_None).

Definition RandT_eval_cov_nextEmpty : set (<<discr Z>> * <<discr loc>> * state)%type :=
  \bigcup_z \bigcup_l [set (z, l, σ) | σ in RandT_eval_cov_nextEmpty' z l].

Definition RandT_eval_cov_ok' (z : <<discr Z>>) (ℓ  : <<discr loc>>) : set state :=
      ((hp_eval ℓ \o tapes) @^-1` option_cov_Some)
  `&` ((fst \o of_option (hp_eval ℓ \o tapes)) @^-1` [set t : <<discr nat>> | t ≠ Z.to_nat z])
  `&` ((sequence_evalC \o snd \o (of_option (hp_eval ℓ \o tapes))) @^-1` option_cov_Some).

Definition RandT_eval_cov_ok : set (<<discr Z>> * <<discr loc>> * state)%type :=
  \bigcup_z \bigcup_l [set (z, l, σ) | σ in RandT_eval_cov_ok' z l].

Definition URandT_eval_cov_noTape' (ℓ : <<discr loc>>) : set state:=
  (hp_eval ℓ \o utapes) @^-1` option_cov_None.

Definition URandT_eval_cov_noTape : set (<<discr loc>> * state)%type :=
  \bigcup_l [set (l, σ) | σ in URandT_eval_cov_noTape' l].

Definition URandT_eval_cov_nextEmpty' (ℓ : <<discr loc>>) : set state :=
      (hp_eval ℓ \o utapes) @^-1` option_cov_Some
  `&` ((sequence_evalC \o (of_option (hp_eval ℓ \o utapes))) @^-1` option_cov_None).

Definition URandT_eval_cov_nextEmpty : set (<<discr loc>> * state)%type :=
  \bigcup_l [set (l, σ) | σ in URandT_eval_cov_nextEmpty' l].

Definition URandT_eval_cov_ok' (ℓ : <<discr loc>>) : set state :=
      (hp_eval ℓ \o utapes) @^-1` option_cov_Some
  `&` ((sequence_evalC \o (of_option (hp_eval ℓ \o utapes))) @^-1` option_cov_Some).

Definition URandT_eval_cov_ok : set (<<discr loc>> * state)%type :=
  \bigcup_l [set (l, σ) | σ in URandT_eval_cov_ok' l].

Lemma RandT_eval_cov_ok'_meas_set (z : <<discr Z>>) (ℓ : <<discr loc>>) :
    measurable (RandT_eval_cov_ok' z ℓ).
Admitted.

Lemma RandT_eval_cov_noTape'_meas_set (z : <<discr Z>>) (ℓ : <<discr loc>>) :
    measurable (RandT_eval_cov_noTape' z ℓ).
Admitted.

Lemma RandT_eval_cov_nextEmpty'_meas_set (z : <<discr Z>>) (ℓ : <<discr loc>>) :
    measurable (RandT_eval_cov_nextEmpty' z ℓ).
Admitted.

Lemma RandT_eval_cov_boundMismatch'_meas_set (z : <<discr Z>>) (ℓ : <<discr loc>>) :
    measurable (RandT_eval_cov_boundMismatch' z ℓ).
Admitted.

Lemma URandT_eval_cov_ok'_meas_set (ℓ  : <<discr loc>>) :
    measurable (URandT_eval_cov_ok' ℓ).
Admitted.

Lemma URandT_eval_cov_noTape'_meas_set (ℓ : <<discr loc>>) :
    measurable (URandT_eval_cov_noTape' ℓ).
Admitted.

Lemma URandT_eval_cov_nextEmpty'_meas_set (ℓ : <<discr loc>>) :
    measurable (URandT_eval_cov_nextEmpty' ℓ).
Admitted.

Hint Resolve RandT_eval_cov_ok'_meas_set            : mf_set.
Hint Resolve RandT_eval_cov_noTape'_meas_set        : mf_set.
Hint Resolve RandT_eval_cov_nextEmpty'_meas_set     : mf_set.
Hint Resolve RandT_eval_cov_boundMismatch'_meas_set : mf_set.
Hint Resolve RandT_eval_cov_boundMismatch'_meas_set : mf_set.
Hint Resolve URandT_eval_cov_ok'_meas_set           : mf_set.
Hint Resolve URandT_eval_cov_noTape'_meas_set       : mf_set.
Hint Resolve URandT_eval_cov_nextEmpty'_meas_set    : mf_set.

Local Lemma int_loc_curry_meas_set (f : <<discr Z>> -> <<discr loc>> -> set state) :
  (∀ z ℓ, measurable (f z ℓ)) -> measurable (\bigcup_z \bigcup_l [set (z, l, σ) | σ in f z l]).
Proof. Admitted.

Local Lemma loc_curry_meas_set (f : <<discr loc>> -> set state) :
  (∀ ℓ, measurable (f ℓ)) -> measurable (\bigcup_l [set (l, σ) | σ in f l]).
Proof. Admitted.


Lemma AllocTape_eval_cov_ok_meas_set : measurable AllocTape_eval_cov_ok. Admitted.
Lemma AllocUTape_eval_cov_ok_meas_set : measurable AllocUTape_eval_cov_ok. Admitted.

Lemma RandT_eval_cov_ok_meas_set : measurable RandT_eval_cov_ok.
Proof. by ms_unfold; apply int_loc_curry_meas_set; ms_done. Qed.

Lemma RandT_eval_cov_noTape_meas_set : measurable RandT_eval_cov_noTape.
Proof. by ms_unfold; apply int_loc_curry_meas_set; ms_done. Qed.

Lemma RandT_eval_cov_nextEmpty_meas_set : measurable RandT_eval_cov_nextEmpty.
Proof. by ms_unfold; apply int_loc_curry_meas_set; ms_done. Qed.

Lemma RandT_eval_cov_boundMismatch_meas_set : measurable RandT_eval_cov_boundMismatch.
Proof. by ms_unfold; apply int_loc_curry_meas_set; ms_done. Qed.

Lemma URandT_eval_cov_ok_meas_set : measurable URandT_eval_cov_ok.
Proof. by ms_unfold; apply loc_curry_meas_set; ms_done. Qed.

Lemma URandT_eval_cov_noTape_meas_set : measurable URandT_eval_cov_noTape.
Proof. by ms_unfold; apply loc_curry_meas_set; ms_done. Qed.

Lemma URandT_eval_cov_nextEmpty_meas_set : measurable URandT_eval_cov_nextEmpty.
Proof. by ms_unfold; apply loc_curry_meas_set; ms_done. Qed.

Hint Resolve AllocTape_eval_cov_ok_meas_set         : mf_set.
Hint Resolve AllocUTape_eval_cov_ok_meas_set        : mf_set.
Hint Resolve RandT_eval_cov_ok_meas_set             : mf_set.
Hint Resolve RandT_eval_cov_noTape_meas_set         : mf_set.
Hint Resolve RandT_eval_cov_nextEmpty_meas_set      : mf_set.
Hint Resolve RandT_eval_cov_boundMismatch_meas_set  : mf_set.
Hint Resolve URandT_eval_cov_ok_meas_set            : mf_set.
Hint Resolve URandT_eval_cov_noTape_meas_set        : mf_set.
Hint Resolve URandT_eval_cov_nextEmpty_meas_set     : mf_set.

(* FIXME: Move *)
Definition Z_to_nat' : <<discr Z>> -> <<discr nat>> := Z.to_nat.

Definition AllocTape_eval_ok : (<<discr Z>> * state)%type -> giryM cfg :=
  gRet \o (ValU \o LitVU \o LitLblU \o fresh \o tapes \o snd
          △ state_of_prod \o
            ( heap \o snd
            △ hp_updateC \o (fresh \o tapes \o snd △ (Some \o (Z_to_nat' \o fst △ cst emptyTape) △ tapes \o snd))
            △ utapes \o snd)).

Definition AllocUTape_eval_ok : state -> giryM cfg :=
  gRet \o (ValU \o LitVU \o LitLblU \o fresh \o utapes
          △ state_of_prod \o
             ( heap
             △ tapes
             △ hp_updateC \o (fresh \o utapes △ (cst (Some emptyTape) △ utapes)))).

Local Notation S' := (S : <<discr nat>> -> <<discr nat>>).

Definition RandT_eval_ok : (<<discr Z>> * <<discr loc>> * state)%type -> giryM cfg :=
  gRet \o (ValU \o LitVU \o LitIntU \o of_option sequence_evalC \o snd \o of_option hp_evalC \o (snd \o fst △ tapes \o snd)
          △ state_of_prod \o
             ( heap \o snd
             △ (hp_updateC \o
                  (    snd \o fst
                  △ ( Some \o (S' \o fst △ snd) \o of_option hp_evalC \o (snd \o fst △ tapes \o snd)
                  △   tapes \o snd)))
             △ utapes \o snd)).

Definition RandT_eval_nextEmpty : (<<discr Z>> * <<discr loc>> * state)%type -> giryM cfg :=
  gMap' (  ValU \o LitVU \o LitIntU \o fst
        △ state_of_prod \o
           (  heap \o snd \o snd
           △ hp_updateC \o
               (    snd \o fst \o snd
               △ ( Some \o (    fst \o of_option hp_evalC \o (snd \o fst \o snd △ tapes \o snd \o snd)
                            △ ( S' \o fst \o snd \o of_option hp_evalC \o (snd \o fst \o snd △ tapes \o snd \o snd)
                            △   sequence_updateC \o
                                  (     fst \o snd \o of_option hp_evalC \o (snd \o fst \o snd △ tapes \o snd \o snd)
                                  △ (  Some \o fst
                                  △    snd \o snd \o of_option hp_evalC \o (snd \o fst \o snd △ tapes \o snd \o snd)))))
               △   tapes \o snd \o snd))
           △ utapes \o snd \o snd )) \o
  gProd \o (unifN_base \o fst \o fst △ gRet).

Definition RandT_eval_boundMismatch : (<<discr Z>> * <<discr loc>> * state)%type -> giryM cfg :=
  gMap' (ValU \o LitVU \o LitIntU \o fst △ snd \o snd) \o
  gProd \o (unifN_base \o fst \o fst △ gRet).

Definition URandT_eval_ok : (<<discr loc>> * state)%type -> giryM cfg :=
  gRet \o (ValU \o LitVU \o LitRealU \o of_option sequence_evalC \o of_option hp_evalC \o (fst △ utapes \o snd)
          △ state_of_prod \o
            (  heap \o snd
            △ tapes \o snd
            △ hp_updateC \o
                (    fst
                △ ( Some \o (S' \o fst △ snd) \o of_option hp_evalC \o (fst △ utapes \o snd)
                △   utapes \o snd)))).

 Definition URandT_eval_nextEmpty : (<<discr loc>> * state)%type -> giryM cfg :=
  gMap' ( ValU \o LitVU \o LitRealU \o fst
        △ state_of_prod \o
           (  heap \o snd \o snd
           △ tapes \o snd \o snd
           △ hp_updateC \o
              (    fst \o snd
              △ ( Some \o ( S' \o fst \o of_option hp_evalC \o (fst \o snd △ utapes \o snd \o snd)
                          △ sequence_updateC \o
                            (    fst \o of_option hp_evalC \o (fst \o snd △ utapes \o snd \o snd)
                            △ ( Some \o fst
                            △   snd \o of_option hp_evalC \o (fst \o snd △ utapes \o snd \o snd))))
              △   utapes \o snd \o snd)))) \o
    gProd \o (cst unif_base △ gRet).

Lemma AllocTape_eval_ok_meas_fun         : measurable_fun AllocTape_eval_cov_ok AllocTape_eval_ok. Admitted.
Lemma AllocUTape_eval_ok_meas_fun        : measurable_fun AllocUTape_eval_cov_ok AllocUTape_eval_ok. Admitted.
Lemma RandT_eval_ok_meas_fun             : measurable_fun RandT_eval_cov_ok RandT_eval_ok. Admitted.
Lemma RandT_eval_nextEmpty_meas_fun      : measurable_fun RandT_eval_cov_nextEmpty RandT_eval_nextEmpty. Admitted.
Lemma RandT_eval_boundMismatch_meas_fun  : measurable_fun RandT_eval_cov_boundMismatch RandT_eval_boundMismatch. Admitted.
Lemma URandT_eval_ok_meas_fun            : measurable_fun URandT_eval_cov_ok URandT_eval_ok. Admitted.
Lemma URandT_eval_nextEmpty_meas_fun     : measurable_fun URandT_eval_cov_nextEmpty URandT_eval_nextEmpty. Admitted.

Hint Resolve AllocTape_eval_ok_meas_fun         : mf_fun.
Hint Resolve AllocUTape_eval_ok_meas_fun        : mf_fun.
Hint Resolve RandT_eval_ok_meas_fun             : mf_fun.
Hint Resolve RandT_eval_nextEmpty_meas_fun      : mf_fun.
Hint Resolve RandT_eval_boundMismatch_meas_fun  : mf_fun.
Hint Resolve URandT_eval_ok_meas_fun            : mf_fun.
Hint Resolve URandT_eval_nextEmpty_meas_fun     : mf_fun.

Definition AllocTape_eval  : (<<discr Z>> * state)%type -> giryM cfg :=
  if_in AllocTape_eval_cov_ok AllocTape_eval_ok (cst gZero).

Definition AllocUTape_eval : state -> giryM cfg :=
  if_in AllocUTape_eval_cov_ok AllocUTape_eval_ok (cst gZero).

Definition Rand_eval : (<<discr Z>> * state)%type -> giryM cfg :=
  gProd \o (gMap' (ValU \o LitVU \o LitIntU) \o unifN_base \o fst △ gRet \o snd).

Definition URand_eval : state -> giryM cfg :=
  gProd \o (cst (gMap' (ValU \o LitVU \o LitRealU) unif_base) △ gRet).

Definition RandT_eval : (<<discr Z>> * <<discr loc>> * state)%type -> giryM cfg :=
  if_in RandT_eval_cov_noTape (cst gZero) $                      (*  No tape *)
  if_in RandT_eval_cov_boundMismatch RandT_eval_boundMismatch $  (*  Yes tape but mismatch bound *)
  if_in RandT_eval_cov_nextEmpty RandT_eval_nextEmpty $          (*  Yes tape, bounds match, but empty *)
  RandT_eval_ok.                                                 (*  Yes tape, bounds match, next nonempty *)

Definition URandT_eval : (<<discr loc>> * state)%type -> giryM cfg :=
  if_in URandT_eval_cov_noTape (cst gZero) $                      (*  No tape *)
  if_in URandT_eval_cov_nextEmpty URandT_eval_nextEmpty $         (*  Yes tape, but empty *)
  URandT_eval_ok.                                                 (*  Yes tape, next nonempty *)

Lemma AllocTape_eval_meas_fun  : measurable_fun setT AllocTape_eval. Admitted.
Lemma AllocUTape_eval_meas_fun : measurable_fun setT AllocUTape_eval. Admitted.
Lemma Rand_eval_meas_fun       : measurable_fun setT Rand_eval. Admitted.
Lemma RandT_eval_meas_fun      : measurable_fun setT RandT_eval. Admitted.
Lemma URand_eval_meas_fun      : measurable_fun setT URand_eval. Admitted.
Lemma URandT_eval_meas_fun     : measurable_fun setT URandT_eval. Admitted.

Hint Resolve AllocTape_eval_meas_fun  : mf_fun.
Hint Resolve AllocUTape_eval_meas_fun : mf_fun.
Hint Resolve Rand_eval_meas_fun       : mf_fun.
Hint Resolve RandT_eval_meas_fun      : mf_fun.
Hint Resolve URand_eval_meas_fun      : mf_fun.
Hint Resolve URandT_eval_meas_fun     : mf_fun.

(*


(*
    | AllocTape (Val (LitV (LitInt z))) =>
        let ι := fresh_loc σ1.(tapes) in
        giryM_ret R ((Val $ LitV $ LitLbl ι, state_upd_tapes <[ι := {| btape_tape := emptyTape ; btape_bound := (Z.to_nat z) |} ]> σ1) : cfg)
*)

Definition rand_allocTapeE : (<<discr Z>> * state)%type -> <<discr loc>> :=
  ssrfun.comp fresh $ ssrfun.comp tapes snd.


Definition new_btape : <<discr Z>> -> btape :=
  fun z => (Z.to_nat z, emptyTape).

Lemma new_btape_meas : measurable_fun setT new_btape.
Proof.
  (* <<discr Z>> is discrete *)
Admitted.


Definition rand_allocTapeS : (<<discr Z>> * state)%type -> state :=
  ssrfun.comp state_of_prod $
  mProd
    (mProd (ssrfun.comp heap snd)
      (ssrfun.comp hp_updateC $
        mProd
          (ssrfun.comp fresh $ ssrfun.comp tapes snd)
          (mProd
            (ssrfun.comp Some $ ssrfun.comp new_btape fst)
            (ssrfun.comp tapes snd))))
    (ssrfun.comp utapes snd).


Definition rand_allocTape_ok_cov : set (<<discr Z>> * state) :=
  setX setT $ preimage tapes (hp_finite _).

Lemma rand_allocTape_ok_cov_meas : measurable rand_allocTape_ok_cov.
Proof. Admitted.

(*  state_upd_tapes <[ (fresh_loc x.2.(tapes)) := {| btape_tape := emptyTape ; btape_bound := Z.to_nat x.1 |} ]> x.2. *)

Lemma rand_allocTapeE_meas : measurable_fun rand_allocTape_ok_cov  rand_allocTapeE. Admitted.
Hint Resolve rand_allocTapeE_meas : measlang.

Lemma rand_allocTapeS_meas : measurable_fun rand_allocTape_ok_cov  rand_allocTapeS. Admitted.
Hint Resolve rand_allocTapeS_meas : measlang.

(*
    | AllocUTape =>
        let ι := fresh_loc σ1.(utapes) in
        giryM_ret R ((Val $ LitV $ LitLbl ι, state_upd_utapes <[ ι := emptyTape ]> σ1) : cfg)
*)

Definition rand_allocUTapeE : state -> <<discr loc>> :=
  ssrfun.comp fresh utapes.

Definition rand_allocUTapeS : state -> state :=
  ssrfun.comp state_of_prod $
  mProd (mProd heap tapes)
  (ssrfun.comp hp_updateC $
    mProd
      (ssrfun.comp fresh utapes)
      (mProd (ssrfun.comp Some $ cst emptyTape) utapes)).


Definition rand_allocUTape_ok_cov : set state :=
  preimage tapes (hp_finite _).

Lemma rand_allocUTape_ok_cov_meas : measurable rand_allocTape_ok_cov.
Proof. Admitted.

(*   state_upd_utapes <[ (fresh_loc x.(utapes)) := emptyTape ]> x. *)

Lemma rand_allocUTapeE_meas : measurable_fun rand_allocUTape_ok_cov rand_allocUTapeE. Admitted.
Hint Resolve rand_allocUTapeE_meas : measlang.

Lemma rand_allocUTapeS_meas : measurable_fun rand_allocUTape_ok_cov  rand_allocUTapeS. Admitted.
Hint Resolve rand_allocUTapeS_meas : measlang.





(**  Rand no tape *)

(*
    | Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)) =>
        giryM_map
          (m_discr (fun (n : 'I_(S (Z.to_nat N))) => ((Val $ LitV $ LitInt $ fin_to_nat n, σ1) : cfg)))
          (giryM_unif (Z.to_nat N))
*)
(*
Definition rand_rand_E (x : (<<discr Z>> * state)%type) : <<discr Z>>. Admitted.

Definition rand_rand_S (x : (<<discr Z>> * state)%type) : state. Admitted.

Lemma rand_rand_E_meas : measurable_fun setT rand_rand_E. Admitted.
Hint Resolve rand_rand_E_meas : measlang.

Lemma rand_rand_S_meas : measurable_fun setT rand_rand_S. Admitted.
Hint Resolve rand_rand_S_meas : measlang.
*)


Definition ZtoNat' : <<discr Z>> -> <<discr nat>> := Z.to_nat.

Lemma ZtoNat'_measurable : measurable_fun setT ZtoNat'.
Proof. (* Discrete *) Admitted.

Definition giryM_unif' : <<discr Z>> -> giryM <<discr Z>>. Admitted.

Lemma giryM_unif'_meas : measurable_fun setT giryM_unif'. (* Discrete *) Admitted.

Definition rand_rand_aux : <<discr Z>> -> giryM expr :=
  ssrfun.comp
    (gMap' (ssrfun.comp ValU $ ssrfun.comp LitVU $ LitIntU ))
    giryM_unif'.
(*
  m_discr (fun z =>
    giryM_map (giryM_unif' (Z.to_nat z)) $
    ssrfun.comp ValU $
    ssrfun.comp LitVU $
    LitIntU).
*)

Lemma rand_rand_aux_meas : measurable_fun setT rand_rand_aux.
Proof.
  have H : (measurable_fun [set: <<discr Z>>] (ValU \o (LitVU \o LitIntU))).
  { mcrunch_compC ValU_meas_fun.
    mcrunch_compC LitVU_meas_fun.
    by eauto with measlang.
  }
  eapply (@measurable_comp _ _ _ _ _ _ setT).
  { by eapply @measurableT. }
  { by eapply subsetT. }
  { have -> : ((gMap' (ValU \o (LitVU \o LitIntU))) = (gMap H));
      last by eapply @gMap_meas_fun.
    admit.
    (* Don't do this here
    rewrite /giryM_map_external/extern_if.
    admit. *)
  }
  { by eauto with measlang. }
Admitted.
Hint Resolve rand_rand_aux_meas : measlang.

Definition rand_rand : (<<discr Z>> * state)%type -> giryM cfg :=
  ssrfun.comp gProd $
  mProd
    (ssrfun.comp rand_rand_aux fst)
    (ssrfun.comp gRet snd).

Lemma rand_rand_meas : measurable_fun setT rand_rand.
Proof.
  unfold rand_rand.
  eapply (@measurable_comp _ _ _ _ _ _ setT).
  { by eapply @measurableT. }
  { by eapply subsetT. }
  { by eapply @gProd_meas_fun. }
  mcrunch_prod.
  { eapply (@measurable_comp _ _ _ _ _ _ setT).
    { by eapply @measurableT. }
    { by eapply subsetT. }
    { by apply rand_rand_aux_meas. }
    { by eauto with measlang. }
  }
  eapply (@measurable_comp _ _ _ _ _ _ setT).
  { by eapply @measurableT. }
  { by eapply subsetT. }
  { by apply gRet_meas_fun. }
  by eauto with measlang.
Qed.
Hint Resolve rand_rand_meas : measlang.

(**  URand no tape *)


(** Uniform distrubtion over real number literal expressions on the interval *)
Definition rand_urand_aux : giryM expr :=
  gMap'
    (ssrfun.comp ValU $ ssrfun.comp LitVU $ LitRealU )
    unif_base_ax.

Definition rand_urand : state -> giryM cfg :=
  ssrfun.comp gProd $
  mProd (cst $ rand_urand_aux) gRet.

Lemma rand_urand_meas : measurable_fun setT rand_urand.
Proof.
  eapply (@measurable_comp _ _ _ _ _ _ setT).
  { by eapply @measurableT. }
  { by eapply subsetT. }
  { by eapply @gProd_meas_fun. }
  mcrunch_prod.
  { by eauto with measlang. }
  { by apply gRet_meas_fun. }
Qed.
Hint Resolve rand_urand_meas : measlang.

(**  Rand with tape *)
(*
  Definition cover_randE           : set cfg := [set c | ∃ N σ,          c = (Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)), σ) ].
  Definition cover_randT_notape    : set cfg := [set c | ∃ N l σ,        c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = None ].
  Definition cover_randT_mismatch  : set cfg := [set c | ∃ N l b σ,      c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = Some b /\ (bool_decide (b.(btape_bound) = Z.to_nat N) = false)].
  Definition cover_randT_empty     : set cfg := [set c | ∃ N l b σ,      c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = Some b /\ (bool_decide (b.(btape_bound) = Z.to_nat N) = true) /\ (b.(btape_tape) !! 0) = None].
  Definition cover_randT           : set cfg := [set c | ∃ N l b n σ,    c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = Some b /\ (bool_decide (b.(btape_bound) = Z.to_nat N) = true) /\ (b.(btape_tape) !! 0) = Some n].
 *)


(* Looking up gives None when the tape is not allocated *)
Definition auxcov_randT_noTape : set (<<discr Z>> * <<discr loc>> * state)%type :=
  (preimage (ssrfun.comp hp_evalC $ mProd (ssrfun.comp snd fst) (ssrfun.comp heap snd)) option_cov_None).
(*
  [set x | tapes x.2 !! x.1.2 = None ].
*)




Definition auxcov_randT_boundMismatch : set (<<discr Z>> * <<discr loc>> * state)%type. Admitted.


(*
  [set x | ∃ b, tapes x.2 !! x.1.2 = Some b /\
                (bool_decide (btape_bound b = Z.to_nat x.1.1) = false) ].
*)
Definition auxcov_randT_nextEmpty : set (<<discr Z>> * <<discr loc>> * state)%type. Admitted.
(*
  [set x | ∃ b, x.2.(tapes) !! x.1.2 = Some b /\
            (bool_decide (btape_bound b = Z.to_nat x.1.1) = false) /\
            (btape_tape b !! 0) = None ].
*)
Definition auxcov_randT_ok : set (<<discr Z>> * <<discr loc>> * state)%type. Admitted.
(*
  [set x | ∃ b, x.2.(tapes) !! x.1.2 = Some b /\
            (bool_decide (b.(btape_bound) = Z.to_nat x.1.1) = false) /\
            ∃ v, (b.(btape_tape) !! 0) = Some v ].
*)

Lemma auxcov_randT_noTape_meas : measurable auxcov_randT_noTape.
Proof. (* Preimage of measurable set under measurable function *) Admitted.
Hint Resolve auxcov_randT_noTape_meas : measlang.

Lemma auxcov_randT_boundMismatch_meas : measurable auxcov_randT_boundMismatch.
Proof. Admitted.
Hint Resolve auxcov_randT_boundMismatch_meas : measlang.

Lemma auxcov_randT_nextEmpty_meas : measurable auxcov_randT_nextEmpty.
Proof. Admitted.
Hint Resolve auxcov_randT_nextEmpty_meas : measlang.

Lemma auxcov_randT_ok_meas : measurable auxcov_randT_ok.
Proof. Admitted.
Hint Resolve auxcov_randT_ok_meas : measlang.


Definition rand_randT_noTape (x : (<<discr Z>> * <<discr loc>> * state)%type) : giryM cfg :=
  gZero.

(*
giryM_map
(m_discr (fun (n : 'I_(S (Z.to_nat N))) => (((Val $ LitV $ LitInt $ fin_to_nat n) : <<discr expr>>), σ1) : cfg))
(giryM_unif (Z.to_nat N))
*)



(* Measurable for each z and l *)
Definition rand_randT_boundMismatch' (z : <<discr Z>>) (l : <<discr loc>>) : (state)%type -> giryM cfg :=
  ssrfun.comp gProd $
  mProd
    (ssrfun.comp (gMap' (ssrfun.comp ValU $ ssrfun.comp LitVU $ LitIntU)) $ (cst (giryM_unif' z)))
    gRet.

(* Measurable because z and l and discrete and countable *)
Definition rand_randT_boundMismatch : (<<discr Z>> * <<discr loc>> * state)%type -> giryM cfg :=
  uncurry (uncurry rand_randT_boundMismatch').


(*
  ssrfun.comp rand_rand $
  mProd (ssrfun.comp fst fst) snd.
*)

(*
giryM_map
  (m_discr (fun (v : 'I_(S (Z.to_nat N))) =>
     (* Fill the tape head with new sample *)
     let τ' := <[ (0 : nat) := Some (v : nat) ]> τ in
     (* Advance the tape *)
     let σ' := state_upd_tapes <[ l := {| btape_tape := (tapeAdvance τ'); btape_bound := M |} ]> σ1 in
     (* Return the new sample and state *)
     ((Val $ LitV $ LitInt $ Z.of_nat v, σ') : cfg)))
 (giryM_unif (Z.to_nat N))
*)

(* Uniform distribution over the states with loc with one sample on the end *)

Definition get_btape : (<<discr loc>> * state)%type -> option btape :=
  ssrfun.comp hp_evalC $
  mProd fst ( ssrfun.comp tapes snd ).

(* Update the tape a location l with a new uniform sample under its tape head *)

(* FIXME: I mean... just look at it *)
Definition tape_sample' (z : <<discr Z>>) (l : <<discr loc>>) : state -> giryM state :=
  ssrfun.comp
    (gMap'
       ((ssrfun.comp state_of_prod $
         mProd
          (mProd
            (ssrfun.comp heap snd)
            (* Update the tape swith label l...*)
            (ssrfun.comp hp_updateC $
             mProd
              (cst l)
              (mProd
                (* new tape is ... get the tape at l, set it to the unif sample *)
                 (ssrfun.comp Some $
                  (* btape *)
                  mProd
                    (* The btape bound *)
                    (ssrfun.comp btape_bound $ of_option $ ssrfun.comp get_btape $ mProd (cst l) snd)
                    (* The btape tape: shifted *)
                    ( mProd
                        (* The position is the old position *)
                        ( ssrfun.comp btape_position $ of_option $ ssrfun.comp get_btape $ mProd (cst l) snd)
                        (* The new tape: Update the old tape *)
                        ( ssrfun.comp sequence_updateC $
                          (mProd
                            (* Update at the tape head position *)
                            ( ssrfun.comp btape_position $ of_option $ ssrfun.comp get_btape $ mProd (cst l) snd)
                            (mProd
                              (* ... to Some of whatever we sampled *)
                              (ssrfun.comp Some fst )
                              ( ssrfun.comp btape_contents $ of_option $ ssrfun.comp get_btape $ mProd (cst l) snd))))))
                (ssrfun.comp tapes snd))))
          (ssrfun.comp utapes snd)) : (<<discr Z>> * state)%type -> state)) $
  ssrfun.comp gProd $
  mProd (cst (giryM_unif' z)) gRet.

Definition tape_sample : (<<discr Z>> * <<discr loc>> * state)%type -> giryM state :=
  uncurry $ uncurry tape_sample'.


(* Tape -> next slot on tape*)
Definition tape_advance : (<<discr loc>> * state)%type -> state :=
  ssrfun.comp state_of_prod $
  mProd
    (mProd
      (ssrfun.comp heap snd)
      (* Update the "tapes" map in the state *)
      (ssrfun.comp hp_updateC $
        (mProd
          fst (* at location l *)
          (mProd
           (* to be the btape at location l but shifted *)
           (ssrfun.comp Some $
            mProd
              (* Bound stays the same *)
              (ssrfun.comp btape_bound $ of_option $ get_btape )
              (* Tape gets advanced *)
              (ssrfun.comp tapeAdvance $ ssrfun.comp snd $  of_option $ get_btape ))
           (ssrfun.comp tapes snd)))))
  (ssrfun.comp utapes snd).

(* Tape -> next item on tape, junk when the next item is none.
   Measurable out of the set of tapes with next item Some, i.e. the range of tape_advance.
 *)


Definition tape_read : (<<discr loc>> * state)%type -> <<discr Z>> :=
  of_option $
  ssrfun.comp sequence_evalC $
  mProd
    (* Get the next position of the tape at loc *)
    (ssrfun.comp fst $ of_option get_btape )
    (* Get the tape at loc *)
    (ssrfun.comp snd $ ssrfun.comp snd $ of_option get_btape).

(*
let σ' := state_upd_tapes <[ l := {| btape_tape := (tapeAdvance τ); btape_bound := M |} ]> σ1 in
(giryM_ret R ((Val $ LitV $ LitInt $ Z.of_nat v, σ') : cfg))
*)
(* Read from and advance the tape *)
Definition rand_randT_ok : (<<discr Z>> * <<discr loc>> * state)%type -> giryM cfg :=
  ssrfun.comp gRet $
  mProd
    ( ssrfun.comp ValU $
      ssrfun.comp LitVU $
      ssrfun.comp LitInt $
      ssrfun.comp tape_read $
      mProd (ssrfun.comp snd fst) snd )
    (ssrfun.comp tape_advance $ mProd (ssrfun.comp snd fst) snd ).


(* When the next tape slot is empty, fill it, and advance. *)
Definition rand_randT_nextEmpty : (<<discr Z>> * <<discr loc>> * state)%type -> giryM cfg :=
  ssrfun.comp
    (gMap' (
      mProd
        (ssrfun.comp ValU $ ssrfun.comp LitVU $ ssrfun.comp LitInt $ snd) (* The expression *)
        (* The state*)
        (ssrfun.comp state_of_prod $
         (mProd (mProd (ssrfun.comp heap $ ssrfun.comp snd fst)
            (* The updated tapes *)
            (ssrfun.comp hp_updateC $
              (* Update the tape at loc... *)
              mProd (ssrfun.comp snd (ssrfun.comp fst fst))
              (mProd
                 (ssrfun.comp Some $
                  (* The new btape *)
                  mProd
                    (* Bound is unchanged *)
                    (ssrfun.comp btape_bound $ of_option $ ssrfun.comp get_btape $ mProd (ssrfun.comp snd (ssrfun.comp fst fst)) (ssrfun.comp snd fst) )
                    (* Tape is the advanced version of.. *)
                    ( mProd
                        (ssrfun.comp Nat.succ $ ssrfun.comp btape_position $ of_option $ ssrfun.comp get_btape $ mProd (ssrfun.comp snd (ssrfun.comp fst fst)) (ssrfun.comp snd fst) )
                        (ssrfun.comp sequence_updateC $
                          mProd
                            (* Update at current tape head *)
                            (ssrfun.comp btape_position $ of_option $ ssrfun.comp get_btape $ mProd (ssrfun.comp snd (ssrfun.comp fst fst)) (ssrfun.comp snd fst) )
                            (mProd
                              (* With value...*)
                              (ssrfun.comp Some snd)
                              (ssrfun.comp btape_contents $ of_option $ ssrfun.comp get_btape $ mProd (ssrfun.comp snd (ssrfun.comp fst fst)) (ssrfun.comp snd fst) )))))
                 (ssrfun.comp tapes $ ssrfun.comp snd fst))
              )
            )
          (ssrfun.comp utapes $ ssrfun.comp snd fst))))) $
  ssrfun.comp gProd $
  (mProd gRet (ssrfun.comp giryM_unif' $ ssrfun.comp fst fst)).

Lemma randT_noTape_meas : measurable_fun auxcov_randT_noTape rand_randT_noTape.
Proof. Admitted.
Hint Resolve randT_noTape_meas : measlang.

Lemma randT_boundMismatch_meas : measurable_fun auxcov_randT_boundMismatch rand_randT_boundMismatch.
Proof. Admitted.
Hint Resolve randT_boundMismatch_meas : measlang.

Lemma randT_nextEmpty_meas : measurable_fun auxcov_randT_nextEmpty rand_randT_nextEmpty.
Proof. Admitted.
Hint Resolve randT_nextEmpty_meas : measlang.

Lemma randT_ok_meas : measurable_fun auxcov_randT_ok rand_randT_ok.
Proof. Admitted.
Hint Resolve randT_ok_meas : measlang.

Definition rand_randT : (<<discr Z>> * <<discr loc>> * state)%type -> giryM cfg :=
  if_in auxcov_randT_noTape rand_randT_noTape $
  if_in auxcov_randT_boundMismatch rand_randT_boundMismatch $
  if_in auxcov_randT_nextEmpty rand_randT_boundMismatch $
  rand_randT_ok.

(*
  let N := x.1.1 in
  let l := x.1.2 in
  let σ1 := x.2 in
  match σ1.(tapes) !! l with
  | Some btape =>
      (* There exists a tape with label l *)
      let τ := btape.(btape_tape) in
      let M := btape.(btape_bound) in
      if (bool_decide (M = Z.to_nat N)) then
        (* Tape bounds match *)
        match (τ !! 0) with
        | Some v => rand_randT_ok x
        | None => rand_randT_nextEmpty x
        end
      else rand_randT_boundMismatch x
        (* Tape bounds do not match *)
        (* Do not advance the tape, but still generate a new sample *)
  | None => rand_randT_noTape x
  end.
*)
(* Covering argument *)
Lemma rand_randT_meas : measurable_fun setT rand_randT.
Proof. Admitted.
Hint Resolve rand_randT_meas : measlang.


(** Urand with tape *)
Definition auxcov_urandT_noTape : set (<<discr loc>> * state)%type. Admitted.
(*
  [set x | tapes x.2 !! x.1 = None ].
*)

Definition auxcov_urandT_nextEmpty : set (<<discr loc>> * state)%type. Admitted.
(*
  [set x | ∃ b, x.2.(tapes) !! x.1 = Some b /\
            (b.(btape_tape) !! 0) = None ].
*)
Definition auxcov_urandT_ok : set (<<discr loc>> * state)%type. Admitted.
(*
  [set x | ∃ b, x.2.(tapes) !! x.1 = Some b /\
            ∃ v, (b.(btape_tape) !! 0) = Some v ].
*)
Lemma auxcov_urandT_noTape_meas : measurable auxcov_urandT_noTape.
Proof. Admitted.
Hint Resolve auxcov_urandT_noTape_meas : measlang.

Lemma auxcov_urandT_nextEmpty_meas : measurable auxcov_urandT_nextEmpty.
Proof. Admitted.
Hint Resolve auxcov_urandT_nextEmpty_meas : measlang.

Lemma auxcov_urandT_ok_meas : measurable auxcov_urandT_ok.
Proof. Admitted.
Hint Resolve auxcov_urandT_ok_meas : measlang.


Definition rand_urandT_noTape (x : (<<discr loc>> * state)%type) : giryM cfg :=
  gZero.

Definition get_utape : (<<discr loc>> * state)%type -> option utape :=
  ssrfun.comp hp_evalC $
  mProd fst ( ssrfun.comp utapes snd ).



Definition rand_urandT_nextEmpty : (<<discr loc>> * state)%type -> giryM cfg :=
  ssrfun.comp (gMap' $
    mProd
      (* The expression *)
      (ssrfun.comp ValU $ ssrfun.comp LitVU $ ssrfun.comp LitReal $ snd)
      (* The state *)
      (ssrfun.comp state_of_prod $
        mProd (mProd (ssrfun.comp (ssrfun.comp heap snd) fst) (ssrfun.comp (ssrfun.comp tapes snd) fst))
        (* Update the utapes *)
        (ssrfun.comp hp_updateC $
          (* At location l*)
         mProd (ssrfun.comp fst fst) (
           mProd
             (ssrfun.comp Some $
                mProd
                  (* Head shifts forward by one*)
                  (ssrfun.comp Nat.succ $ ssrfun.comp fst $ of_option $ ssrfun.comp get_utape fst )
                  (* Tape at old head is updated with sample *)
                  (ssrfun.comp sequence_updateC $
                   mProd (ssrfun.comp fst $ of_option $ ssrfun.comp get_utape fst)
                   (mProd
                      (ssrfun.comp Some snd) (* snd, even though it doesn't typecheck atm *)
                      (ssrfun.comp snd $ of_option $ ssrfun.comp get_utape fst))))
             (ssrfun.comp (ssrfun.comp utapes snd) fst)
          ))
      )
    ) $
  ssrfun.comp gProd $
  mProd gRet (cst (@unif_base_ax R)).


(*
let σ' := state_upd_utapes <[ l := (tapeAdvance τ) ]> σ1 in
(giryM_ret R ((Val $ LitV $ LitReal u, σ') : cfg))
 *)
Definition rand_urandT_ok : (<<discr loc>> * state)%type -> giryM cfg :=
  ssrfun.comp gProd $
  mProd
    (ssrfun.comp gRet $ ssrfun.comp ValU $ ssrfun.comp LitVU $ ssrfun.comp LitReal $
     of_option $ ssrfun.comp sequence_evalC $
     mProd
      (ssrfun.comp fst $ of_option get_utape )
      (ssrfun.comp snd $ of_option get_utape))
  ( ssrfun.comp gRet $
    ssrfun.comp state_of_prod $
    mProd (mProd (ssrfun.comp heap snd) (ssrfun.comp tapes snd) )
    (ssrfun.comp hp_updateC $
     mProd fst
     (mProd
        (ssrfun.comp Some $
          mProd
            (ssrfun.comp Nat.succ $ ssrfun.comp fst $ of_option get_utape )
            ( ssrfun.comp snd $ of_option get_utape ) )
        (ssrfun.comp utapes snd)))).

Lemma urandT_noTape_meas : measurable_fun auxcov_urandT_noTape rand_urandT_noTape.
Proof. Admitted.
Hint Resolve urandT_noTape_meas : measlang.

Lemma urandT_nextEmpty_meas : measurable_fun auxcov_urandT_nextEmpty rand_urandT_nextEmpty.
Proof. Admitted.
Hint Resolve urandT_nextEmpty_meas : measlang.

Lemma urandT_ok_meas : measurable_fun auxcov_urandT_ok rand_urandT_ok.
Proof. Admitted.
Hint Resolve urandT_ok_meas : measlang.

Definition rand_urandT : (<<discr loc>> * state)%type -> giryM cfg :=
  if_in auxcov_urandT_noTape rand_urandT_noTape $
  if_in auxcov_urandT_nextEmpty rand_urandT_nextEmpty $
  rand_urandT_ok .

(*
  let l := x.1 in
  let σ1 := x.2 in
  match utapes σ1 !! l with
  | Some τ =>
      match (τ !! 0) with
      | Some u => rand_urandT_ok x
      | None => rand_urandT_nextEmpty x
      end
  | None => rand_urandT_noTape x
  end.
*)

Lemma rand_urandT_meas : measurable_fun setT rand_urandT.
Proof. Admitted.
Hint Resolve rand_urandT_meas : measlang.
*)
