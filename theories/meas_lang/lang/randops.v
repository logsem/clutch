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

