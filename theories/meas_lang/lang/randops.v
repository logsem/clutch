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

Section unif.
  Local Open Scope ereal_scope.
  Local Open Scope classical_set_scope.
  (* Uniform space over [0, 1]*)
  Definition unif_base : subprobability _ _ := uniform_prob (@Num.Internals.ltr01 TR).

  (** FIXME: Type conversion *)
  Axiom (unif_base_ax : giryM TR).

End unif.


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

Definition giryM_unif' : <<discr TZ>> -> giryM <<discr TZ>>. Admitted.



Definition rand_rand_aux : <<discr TZ>> -> giryM expr :=
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
  have H : (measurable_fun (T:=TZ) (U:=types_expr_T__canonical__measure_Measurable) [set: TZ] (ValU \o (LitVU \o LitIntU))).
  { mcrunch_compC ValU_measurable.
    mcrunch_compC LitVU_measurable.
    by eauto with measlang.
  }
  eapply (@measurable_comp _ _ _ _ _ _ setT).
  { by eapply @measurableT. }
  { by eapply subsetT. }
  { have -> : ((gMap' (ValU \o (LitVU \o LitIntU))) = (gMap H));
      last by eapply @gMap_measurable.
    intro t.
    admit.
    (* Don't do this here
    rewrite /giryM_map_external/extern_if.
    admit. *)
  }
  { by eauto with measlang. }
Admitted.
Hint Resolve rand_rand_aux_meas : measlang.

Definition rand_rand : (<<discr TZ>> * state)%type -> giryM cfg :=
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
  { by eapply @gProd_measurable. }
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
  { by apply gRet_measurable. }
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
  { by eapply @gProd_measurable. }
  mcrunch_prod.
  { by eauto with measlang. }
  { by apply gRet_measurable. }
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


Definition auxcov_randT_noTape : set (<<discr Z>> * <<discr loc>> * state)%type. Admitted.
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
  gZero.

(*
giryM_map
(m_discr (fun (n : 'I_(S (Z.to_nat N))) => (((Val $ LitV $ LitInt $ fin_to_nat n) : <<discr expr>>), σ1) : cfg))
(giryM_unif (Z.to_nat N))
*)
Definition rand_randT_boundMismatch : (<<discr Z>> * <<discr loc>> * state)%type -> giryM cfg.
Admitted.

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
Definition tape_sample : (<<discr Z>> * <<discr loc>> * state)%type -> giryM state.
Admitted.

(* Tape -> next slot on tape*)
Definition tape_advance : (<<discr loc>> * state)%type -> state.
Admitted.

(* Tape -> next item on tape, junk when the next item is none.
   Measurable out of the set of tapes with next item Some, i.e. the range of tape_advance.

 *)
Definition tape_read : (<<discr loc>> * state)%type -> TZ.
Admitted.

(*
let σ' := state_upd_tapes <[ l := {| btape_tape := (tapeAdvance τ); btape_bound := M |} ]> σ1 in
(giryM_ret R ((Val $ LitV $ LitInt $ Z.of_nat v, σ') : cfg))
*)
Definition rand_randT_ok : (<<discr Z>> * <<discr loc>> * state)%type -> giryM cfg.
Admitted.

(*

  ssrfun.comp giryM_ap $
  mProd
    ( ssrfun.comp giryM_ret $
      ssrfun.comp ValU $
      ssrfun.comp LitVU $
      ssrfun.comp LitInt $
      ssrfun.comp tape_read $
      mProd (ssrfun.comp snd fst) snd )
    ( ssrfun.comp giryM_ret snd ).
*)


(* When the next tape slot is empty, fill it, and advance. *)
Definition rand_randT_nextEmpty : (<<discr Z>> * <<discr loc>> * state)%type -> giryM cfg.
Admitted.

  (*

  ssrfun.comp
  _.
Admitted.

  ssrfun.comp giryM_ap $
  mProd
    (* The uniform distribution on the next integer *)
    (ssrfun.comp (m_discr (fun z =>
      giryM_map_def' (giryM_unif' (Z.to_nat z)) $
      ssrfun.comp ValU $
      ssrfun.comp LitVU $
      LitIntU)) $
     ssrfun.comp fst $
     fst)
    (* The uniform distribution over next tape states *)
    _.
*)

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

Definition rand_randT (x : (<<discr Z>> * <<discr loc>> * state)%type) : giryM cfg. Admitted.
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

Definition rand_urandT (x : (<<discr loc>> * state)%type) : giryM cfg. Admitted.

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
