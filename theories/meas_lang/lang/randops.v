(* TODO cleanup imports *)
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
From clutch.meas_lang.lang Require Export prelude types constructors shapes cover projections tapes state cfg.

Local Open Scope classical_set_scope.
(*
    | AllocTape (Val (LitV (LitInt z))) =>
        let ι := fresh_loc σ1.(tapes) in
        giryM_ret R ((Val $ LitV $ LitLbl ι, state_upd_tapes <[ι := {| btape_tape := emptyTape ; btape_bound := (Z.to_nat z) |} ]> σ1) : cfg)
*)

Definition rand_allocTapeE (x : (<<discr Z>> * state)%type) : <<discr loc>>. Admitted.

Definition rand_allocTapeS (x : (<<discr Z>> * state)%type) : state. Admitted.

Lemma rand_allocTapeE_meas : measurable_fun setT rand_allocTapeE. Admitted.
Hint Resolve rand_allocTapeE_meas : measlang.

Lemma rand_allocTapeS_meas : measurable_fun setT rand_allocTapeS. Admitted.
Hint Resolve rand_allocTapeS_meas : measlang.

(*
    | AllocUTape =>
        let ι := fresh_loc σ1.(utapes) in
        giryM_ret R ((Val $ LitV $ LitLbl ι, state_upd_utapes <[ ι := emptyTape ]> σ1) : cfg)
*)

Definition rand_allocUTapeE (x : state) : <<discr loc>>. Admitted.

Definition rand_allocUTapeS (x : state) : state. Admitted.

Lemma rand_allocUTapeE_meas : measurable_fun setT rand_allocUTapeE. Admitted.
Hint Resolve rand_allocUTapeE_meas : measlang.

Lemma rand_allocUTapeS_meas : measurable_fun setT rand_allocUTapeS. Admitted.
Hint Resolve rand_allocUTapeS_meas : measlang.

(* Each random operation has a pure "core" that is mapped over a set of expressions.
This gets lifted to a cfg -> giryM cfg by adding state, but state is not needed for rand or urand.
 *)

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

Definition rand_rand (x : (<<discr Z>> * state)%type) : giryM cfg. Admitted.

Lemma rand_rand_meas : measurable_fun setT rand_rand. Admitted.
Hint Resolve rand_rand_meas : measlang.



(**  URand no tape *)

(*
    | URand (Val (LitV LitUnit)) => ??
*)
(*
Definition rand_urand_E (x : (((R : realType) : measurableType _) * state)%type) : ((R : realType) : measurableType _). Admitted.

Definition rand_urand_S (x : (((R : realType) : measurableType _) * state)%type) : state. Admitted.

Lemma rand_urand_E_meas : measurable_fun setT rand_urand_E. Admitted.
Hint Resolve rand_urand_E_meas : measlang.

Lemma rand_urand_S_meas : measurable_fun setT rand_urand_S. Admitted.
Hint Resolve rand_urand_S_meas : measlang.
*)

Definition rand_urand (x : state) : giryM cfg. Admitted.

Lemma rand_urand_meas : measurable_fun setT rand_urand. Admitted.
Hint Resolve rand_urand_meas : measlang.

(**  Rand with tape *)
(*
  Definition cover_randE           : set cfg := [set c | ∃ N σ,          c = (Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)), σ) ].
  Definition cover_randT_notape    : set cfg := [set c | ∃ N l σ,        c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = None ].
  Definition cover_randT_mismatch  : set cfg := [set c | ∃ N l b σ,      c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = Some b /\ (bool_decide (b.(btape_bound) = Z.to_nat N) = false)].
  Definition cover_randT_empty     : set cfg := [set c | ∃ N l b σ,      c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = Some b /\ (bool_decide (b.(btape_bound) = Z.to_nat N) = true) /\ (b.(btape_tape) !! 0) = None].
  Definition cover_randT           : set cfg := [set c | ∃ N l b n σ,    c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = Some b /\ (bool_decide (b.(btape_bound) = Z.to_nat N) = true) /\ (b.(btape_tape) !! 0) = Some n].
 *)


Definition auxcov_randT_noTape : set (<<discr Z>> * <<discr loc>> * state)%type :=
  [set x | x.2.(tapes) !! x.1.2 = None ].

Definition auxcov_randT_boundMismatch : set (<<discr Z>> * <<discr loc>> * state)%type :=
  [set x | ∃ b, x.2.(tapes) !! x.1.2 = Some b /\
                (bool_decide (b.(btape_bound) = Z.to_nat x.1.1) = false) ].

Definition auxcov_randT_nextEmpty : set (<<discr Z>> * <<discr loc>> * state)%type :=
  [set x | ∃ b, x.2.(tapes) !! x.1.2 = Some b /\
            (bool_decide (b.(btape_bound) = Z.to_nat x.1.1) = false) /\
            (b.(btape_tape) !! 0) = None ].

Definition auxcov_randT_ok : set (<<discr Z>> * <<discr loc>> * state)%type :=
  [set x | ∃ b, x.2.(tapes) !! x.1.2 = Some b /\
            (bool_decide (b.(btape_bound) = Z.to_nat x.1.1) = false) /\
            ∃ v, (b.(btape_tape) !! 0) = Some v ].


Lemma auxcov_randT_noTape_meas : measurable auxcov_randT_noTape.
Proof. Admitted.
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
  giryM_zero.

(*
giryM_map
(m_discr (fun (n : 'I_(S (Z.to_nat N))) => (((Val $ LitV $ LitInt $ fin_to_nat n) : <<discr expr>>), σ1) : cfg))
(giryM_unif (Z.to_nat N))
*)
Definition rand_randT_boundMismatch (x : (<<discr Z>> * <<discr loc>> * state)%type) : giryM cfg.
Admitted.


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
Definition rand_randT_nextEmpty (x : (<<discr Z>> * <<discr loc>> * state)%type) : giryM cfg.
Admitted.

(*
let σ' := state_upd_tapes <[ l := {| btape_tape := (tapeAdvance τ); btape_bound := M |} ]> σ1 in
(giryM_ret R ((Val $ LitV $ LitInt $ Z.of_nat v, σ') : cfg))
*)
Definition rand_randT_ok (x : (<<discr Z>> * <<discr loc>> * state)%type) : giryM cfg.
Admitted.

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

Program Definition rand_randT (x : (<<discr Z>> * <<discr loc>> * state)%type) : giryM cfg :=
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

(* Covering argument *)
Lemma rand_randT_meas : measurable_fun setT rand_randT.
Proof. Admitted.
Hint Resolve rand_randT_meas : measlang.


(** Urand with tape *)


Definition auxcov_urandT_noTape : set (<<discr loc>> * state)%type :=
  [set x | x.2.(tapes) !! x.1 = None ].


Definition auxcov_urandT_nextEmpty : set (<<discr loc>> * state)%type :=
  [set x | ∃ b, x.2.(tapes) !! x.1 = Some b /\
            (b.(btape_tape) !! 0) = None ].

Definition auxcov_urandT_ok : set (<<discr loc>> * state)%type :=
  [set x | ∃ b, x.2.(tapes) !! x.1 = Some b /\
            ∃ v, (b.(btape_tape) !! 0) = Some v ].

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
  giryM_zero.

 (* giryM_map urand_tape_step unif_base *)
Definition rand_urandT_nextEmpty (x : (<<discr loc>> * state)%type) : giryM cfg.
Admitted.

(*
let σ' := state_upd_utapes <[ l := (tapeAdvance τ) ]> σ1 in
(giryM_ret R ((Val $ LitV $ LitReal u, σ') : cfg))
 *)
Definition rand_urandT_ok (x : (<<discr loc>> * state)%type) : giryM cfg.
Admitted.

Lemma urandT_noTape_meas : measurable_fun auxcov_urandT_noTape rand_urandT_ok.
Proof. Admitted.
Hint Resolve urandT_noTape_meas : measlang.

Lemma urandT_nextEmpty_meas : measurable_fun auxcov_urandT_nextEmpty rand_urandT_ok.
Proof. Admitted.
Hint Resolve urandT_nextEmpty_meas : measlang.

Lemma urandT_ok_meas : measurable_fun auxcov_urandT_ok rand_urandT_ok.
Proof. Admitted.
Hint Resolve urandT_ok_meas : measlang.

Definition rand_urandT (x : (<<discr loc>> * state)%type) : giryM cfg :=
  let l := x.1 in
  let σ1 := x.2 in
  match σ1.(utapes) !! l with
  | Some τ =>
      match (τ !! 0) with
      | Some u => rand_urandT_ok x
      | None => rand_urandT_nextEmpty x
      end
  | None => rand_urandT_noTape x
  end.

Lemma rand_urandT_meas : measurable_fun setT rand_urandT.
Proof. Admitted.
Hint Resolve rand_urandT_meas : measlang.
