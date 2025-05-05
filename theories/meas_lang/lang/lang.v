(* TODO cleanup imports *)
Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From stdpp Require Import base gmap. (* numbers binders strings gmap. **)
From mathcomp Require Import functions.
From mathcomp.analysis Require Import reals measure itv lebesgue_measure probability.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp fintype.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export base stdpp_ext.
From clutch.common Require Export locations.
From clutch.meas_lang Require Import ectxi_language ectx_language.
From Coq Require Export Reals.
From clutch.prob.monad Require Export giry.
From mathcomp.analysis Require Export Rstruct.
From mathcomp Require Import classical_sets.
Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude types constructors shapes cover projections tapes state subst pureops heapops randops cfg fill.
(* From Coq Require Import Reals Psatz.
From stdpp Require Export binders strings.
From stdpp Require Import fin.
From stdpp Require Import gmap fin_maps countable fin.
From clutch.prob Require Export distribution.
From clutch.common Require Export language ectx_language ectxi_language locations.
From iris.prelude Require Import options.
From mathcomp Require Import ssrbool eqtype fintype choice all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed normedtype sequences esum numfun measure lebesgue_measure lebesgue_integral. *)
Set Warnings "hiding-delimiting-key".
Set Warnings "+spurious-ssr-injection".

Module meas_lang.

Local Open Scope classical_set_scope.
Section meas_semantics.

(*
Definition test (l : loc) (v : val) (h : hp (option val)) : hp (option val) :=
  <[ l := v ]> h.
*)
(*
Instance : Insert <<discr loc>> btape (hp (option btape)).
intros a b c.
apply (hp_evalC ).
  *)

Notation cfg := (toPackedType expr_cyl.-sigma expr * toPackedType state_display state)%type.

(* TODO: Make this as close to the old definition in Clutch as possible.
    - What stdpp isntances do we need for the new tapes?*)
Definition head_stepM (c : cfg) : giryM cfg :=
  let (e1, σ1) := c in
  match e1 with
  | Rec f x e =>
      gRet ((Val $ RecV f x e, σ1) : cfg)
  | Pair (Val v1) (Val v2) =>
      gRet ((Val $ PairV v1 v2, σ1) : cfg)
  | InjL (Val v) =>
      gRet ((Val $ InjLV v, σ1) : cfg)
  | InjR (Val v) =>
      gRet ((Val $ InjRV v, σ1) : cfg)
  | App (Val (RecV f x e1)) (Val v2) =>
      gRet ((substU' (x, (v2, substU' (f, (RecVC f x e1, e1)))), σ1) : cfg)
  | UnOp op (Val v) =>
      match un_op_eval op v with
        | Some w => gRet ((ValC w, σ1) : cfg)
        | _ => gZero
      end
  | BinOp op (Val v1) (Val v2) =>
      match bin_op_eval op v1 v2 with
        | Some w => gRet ((ValC w, σ1) : cfg)
        | _ => gZero
      end
  | If (Val (LitV (LitBool true))) e1 e2  =>
      gRet ((e1 , σ1) : cfg)
  | If (Val (LitV (LitBool false))) e1 e2 =>
      gRet ((e2 , σ1) : cfg)
  | Fst (Val (PairV v1 v2)) =>
      gRet ((Val v1, σ1) : cfg)
  | Snd (Val (PairV v1 v2)) =>
      gRet ((Val v2, σ1) : cfg)
  | Case (Val (InjLV v)) e1 e2 =>
      gRet ((App e1 (Val v), σ1) : cfg)
  | Case (Val (InjRV v)) e1 e2 =>
      gRet ((App e2 (Val v), σ1) : cfg)
  | Alloc (Val v) =>
      let ℓ := state.fresh (heap σ1) in
      gRet ((ValC $ LitVC $ LitLocC ℓ, state_upd_heap <[ ℓ := (v : val) ]>  σ1) : cfg)

  | Load (Val (LitV (LitLoc l))) =>
      match (((heap σ1) !! l) : option val) with
        | Some v => gRet ((Val v, σ1) : cfg)
        | None => gZero
      end
  | Store (Val (LitV (LitLoc l))) (Val w) =>
      match ((heap σ1) !! l : option val) with
        | Some v => gRet ((Val $ LitV LitUnit, state_upd_heap <[ l := (w : val) ]> σ1) : cfg)
        | None => gZero
      end
  (* Uniform sampling from [0, 1 , ..., N] *)
  | Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)) =>
      gProd (gMap'
        (fun (n : <<discr Z>>) => (Val $ LitV $ LitInt n):expr)
        (unifN_base N),
               gRet σ1
        )
      (* gMap' *)
      (*   (fun (n : <<discr Z>>) => ((Val $ LitV $ LitInt n, σ1) : cfg)) *)
      (*   (unifN_base N) *)
  | AllocTape (Val (LitV (LitInt z))) =>
      if_in AllocTape_eval_cov_ok
        (λ '(x, σ1),
           let ι := state.fresh (tapes σ1) in (* FIXME: stdpp-ify *)
           gRet ((Val $ LitV $ LitLbl ι, state_upd_tapes (fun h => hp_update ι (Some (Z.to_nat z, emptyTape), h)) σ1) : cfg))
        (cst gZero)
        (z, σ1)
      (* let ι := state.fresh (tapes σ1) in (* FIXME: stdpp-ify *) *)
      (* gRet ((Val $ LitV $ LitLbl ι, state_upd_tapes (fun h => hp_update ι (Some (Z.to_nat z, emptyTape), h)) σ1) : cfg) *)
  (* Rand with a tape *)
  | Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))) =>
      match ((tapes σ1) !! l : option btape) with
      | Some (M, (i, τ)) =>
          if (bool_decide (M = Z.to_nat N))
            then
              match (τ i) with
              (* Presample *)
              | Some s =>
                  let σ' := state_upd_tapes (fun h => hp_update l (Some (M, (i + 1, τ)), h)) σ1 in
                  gRet (ValC $ LitVC $ LitInt s , σ')
              (* Next is empty *)
              | None =>
                  gMap'
    (λ x0,
       (ValU (LitVU (LitIntU x0.1)),
        state_of_prod
          (heap x0.2.2,
           hp_update x0.2.1.2
             (Some
                ((of_option hp_evalC (x0.2.1.2, tapes x0.2.2)).1,
                 (S (of_option hp_evalC (x0.2.1.2, tapes x0.2.2)).2.1,
                  sequence_update (of_option hp_evalC (x0.2.1.2, tapes x0.2.2)).2.1
                    (Some x0.1, (of_option hp_evalC (x0.2.1.2, tapes x0.2.2)).2.2))), 
              tapes x0.2.2), utapes x0.2.2))) (gProd (unifN_base N, gRet (N, l, σ1)))
                  (** Rewritten to match that in head_stepM' *)
                  (* gMap' *)
                  (*   (fun (s : <<discr Z>>) => *)
                  (*      let σ' := state_upd_tapes (fun h => hp_update l (Some (M, (i + 1, sequence_update i (Some s, τ))), h)) σ1 in *)
                  (*      ((Val $ LitV $ LitInt s, σ') : cfg)) *)
                  (*   (unifN_base N) *)
              end
            (* Bound mismatch *)
          else
            gMap'
              (λ x0 , (ValU (LitVU (LitIntU x0.1)), x0.2.2))
              (gProd (unifN_base N, gRet (N, l, σ1)))
              (* gMap' *)
              (*   (fun (n : <<discr Z>>) => ((Val $ LitV $ LitInt n, σ1) : cfg)) *)
              (*   (unifN_base N) *)
      (* No tape allocated (get stuck) *)
      | None => gZero
      end

  | AllocUTape =>
      if_in AllocUTape_eval_cov_ok
            (λ σ1, let ι := state.fresh (utapes σ1) in (* FIXME: stdpp-ify *)
                   gRet ((Val $ LitV $ LitLbl ι, state_upd_utapes (fun h => hp_update ι (Some emptyTape, h)) σ1) : cfg)) (cst gZero)
            σ1 
      (* let ι := state.fresh (utapes σ1) in (* FIXME: stdpp-ify *) *)
      (* gRet ((Val $ LitV $ LitLbl ι, state_upd_utapes (fun h => hp_update ι (Some emptyTape, h)) σ1) : cfg) *)
  (* Urand with no tape *)
  | URand (Val (LitV LitUnit)) =>
      gProd (gMap'
        (fun r => (ValC $ LitVC $ LitReal r) : expr)
        unif_base,
               gRet σ1
        )
      (* gMap' *)
      (*   (fun r => (ValC $ LitVC $ LitReal r, σ1) : cfg) *)
      (*   unif_base *)
  (* Urand with a tape *)
  | URand  (Val (LitV (LitLbl l))) =>
      match ((utapes σ1) !! l : option utape) with
      | Some (i, τ) =>
          match (τ i) with
          (* Presample *)
          | Some s =>
              let σ' := state_upd_utapes (fun h => hp_update l (Some (i + 1, τ), h)) σ1 in
              gRet (ValC $ LitVC $ LitReal s , σ')
          (* Next is empty *)
          | None =>
              gMap'
    (λ x0,
       (ValU (LitVU (LitRealU x0.1)),
        state_of_prod
          (heap x0.2.2, tapes x0.2.2,
           hp_update x0.2.1
             (Some
                (S (of_option hp_evalC (x0.2.1, utapes x0.2.2)).1,
                 sequence_update (of_option hp_evalC (x0.2.1, utapes x0.2.2)).1
                   (Some x0.1, (of_option hp_evalC (x0.2.1, utapes x0.2.2)).2)), 
              utapes x0.2.2)))) (gProd (unif_base, gRet (l, σ1)))
              (** Rewritten to match head_stepM' more *)
              (* gMap' *)
              (*   (fun s => *)
              (*      let σ' := state_upd_utapes (fun h => hp_update l (Some (i + 1, sequence_update i (Some s, τ)), h)) σ1 in *)
              (*      ((Val $ LitV $ LitReal s, σ') : cfg)) *)
              (*   (unif_base) *)
          end
      (* No tape allocated (get stuck) *)
      | None => gZero
      end
  | Tick (Val (LitV (LitInt n))) =>
      gRet ((Val $ LitV $ LitUnit, σ1) : cfg)
  | _ => gZero
  end.

Definition cover_rec : set cfg :=
  setI setT $ preimage fst $ ecov_rec.

(* [set c | ∃ v1 v2 σ, c = (Pair (Val v1) (Val v2), σ) ].*)
Definition cover_pair : set cfg :=
  setI setT $ preimage fst $ setI ecov_pair $ preimage 𝜋_PairU $ (ecov_val `*` ecov_val).

(* [set c | ∃ v σ, c = (InjL (Val v), σ) ]. *)
Definition cover_injL : set cfg :=
  setI setT $ preimage fst $ setI ecov_injl $ preimage 𝜋_InjLU $ ecov_val.

(* [set c | ∃ v σ, c = (InjR (Val v), σ) ]. *)
Definition cover_injR : set cfg :=
  setI setT $ preimage fst $ setI ecov_injr $ preimage 𝜋_InjRU $ ecov_val.

(*  [set c | ∃ f x e1 v2 σ,  c = (App (Val (RecV f x e1)) (Val v2) , σ) ]. *)
Definition cover_app : set cfg :=
  setI setT $ preimage fst $ setI ecov_app $ preimage 𝜋_AppU $
  setX (setI ecov_val $ preimage 𝜋_Val_v $ vcov_rec) ecov_val.

Definition cover_unop : set cfg :=
  setX (setI ecov_unop $ preimage 𝜋_UnOpU $ setX setT ecov_val) setT.

Definition cover_binop : set cfg :=
  setX (setI ecov_binop $ preimage 𝜋_BinOpU $ (setX (setX setT ecov_val) ecov_val)) setT.

(* [set e | ∃ N v, e = Alloc (val v)] *)
Definition cover_alloc : set cfg  :=
  setI setT $ preimage fst $ setI ecov_alloc $ preimage 𝜋_AllocU $ ecov_val.

(* [set e | ∃ l e = (Load (Val (LitV (LitLoc l))))] *)
Definition cover_load : set cfg :=
  setI setT $ preimage fst $ setI ecov_load $ preimage 𝜋_LoadU $
  setI ecov_val $ preimage 𝜋_ValU $ setI vcov_lit $ preimage 𝜋_LitVU $ bcov_LitLoc.

(* [set e | ∃ N v, e = Store (Val (LitV (LitLoc L))) (val v)] *)
Definition cover_store : set cfg  :=
  setI setT $ preimage fst $ setI ecov_store $ preimage 𝜋_StoreU $
  setX
    (setI ecov_val $ preimage 𝜋_ValU $ setI vcov_lit $ preimage 𝜋_LitVU $ bcov_LitLoc)
    ecov_val.

(* [set c | ∃ e1 e2 σ, c = (If (Val (LitV (LitBool true))) e1 e2, σ) ]*)
Definition cover_ifT : set cfg :=
  setI setT $ preimage fst $ setI ecov_if $ preimage 𝜋_If_c $ setI ecov_val $
  preimage 𝜋_ValU $ setI vcov_lit $ preimage 𝜋_LitVU $ setI bcov_LitBool $
  preimage 𝜋_LitBoolU $ [set true].

(* [set c | ∃ e1 e2 σ, c = (If (Val (LitV (LitBool false))) e1 e2, σ) ] *)
Definition cover_ifF : set cfg :=
  setI setT $ preimage fst $ setI ecov_if $ preimage 𝜋_If_c $ setI ecov_val $
  preimage 𝜋_ValU $ setI vcov_lit $ preimage 𝜋_LitVU $ setI bcov_LitBool $
  preimage 𝜋_LitBoolU $ [set false].

(* [set c | ∃ v1 v2 σ, c = (Fst (Val (PairV v1 v2)), σ) ] *)
Definition cover_fst : set cfg :=
  setI setT $ preimage fst $ setI ecov_fst $ preimage 𝜋_FstU $ setI ecov_val $
  preimage 𝜋_ValU $ vcov_pair.

(* [set c | ∃ v1 v2 σ, c = (Snd (Val (PairV v1 v2)), σ) ] *)
Definition cover_snd : set cfg :=
  setI setT $ preimage fst $ setI ecov_snd $ preimage 𝜋_SndU $ setI ecov_val $
  preimage 𝜋_ValU $ vcov_pair.

(* [set c | ∃ v e1 e2 σ, c = (Case (Val (InjLV v)) e1 e2, σ) ] *)
Definition cover_caseL : set cfg :=
  setI setT $ preimage fst $ setI ecov_case $ preimage 𝜋_Case_c $ setI ecov_val $
  preimage 𝜋_ValU $ vcov_injlv.

(* [set c | ∃ v e1 e2 σ, c = (Case (Val (InjRV v)) e1 e2, σ) ] *)
Definition cover_caseR : set cfg :=
  setI setT $ preimage fst $ setI ecov_case $ preimage 𝜋_Case_c $ setI ecov_val $
  preimage 𝜋_ValU $ vcov_injrv.

(*  [set c | ∃ z σ,          c = (AllocTape (Val (LitV (LitInt z))), σ) ]. *)
Definition cover_allocTape : set cfg :=
  setI setT $ preimage fst $ setI ecov_alloctape $ preimage 𝜋_AllocTapeU $ setI ecov_val $
  preimage 𝜋_ValU $ setI vcov_lit $ preimage 𝜋_LitVU $ bcov_LitInt.

(* [set c | ∃ σ,            c = (AllocUTape, σ) ] *)
Definition cover_allocUTape : set cfg :=
  setI setT $ preimage fst $ ecov_allocutape.

(* Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)) *)
Definition cover_rand : set cfg :=
  setI setT $ preimage fst $ setI ecov_rand $ preimage 𝜋_RandU $
  setX
    ( setI ecov_val $ preimage 𝜋_ValU $ setI vcov_lit $ preimage 𝜋_LitVU $ bcov_LitInt )
    ( setI ecov_val $ preimage 𝜋_ValU $ setI vcov_lit $ preimage 𝜋_LitVU $ bcov_LitUnit ).

(*  (URand (Val (LitV LitUnit)), σ) *)
Definition cover_urand : set cfg :=
  setI setT $ preimage fst $ setI ecov_urand $ preimage 𝜋_URandU $ setI ecov_val $
  preimage 𝜋_ValU $ setI vcov_lit $ preimage 𝜋_LitVU $ bcov_LitUnit.

Definition cover_randT : set cfg :=
  setI setT $ preimage fst $ setI ecov_rand $ preimage 𝜋_RandU $
  setX
    ( setI ecov_val $ preimage 𝜋_ValU $ setI vcov_lit $ preimage 𝜋_LitVU $ bcov_LitInt )
    ( setI ecov_val $ preimage 𝜋_ValU $ setI vcov_lit $ preimage 𝜋_LitVU $ bcov_LitLbl ).

Definition cover_urandT : set cfg :=
  setI setT $ preimage fst $ setI ecov_urand $ preimage 𝜋_URandU $ setI ecov_val $
  preimage 𝜋_ValU $ setI vcov_lit $ preimage 𝜋_LitVU $ bcov_LitLbl.

(* [set c | ∃ σ n, c = (Tick (Val (LitV (LitInt n))), σ) ]  *)
Definition cover_tick : set cfg :=
  setI setT $ preimage fst $ setI ecov_tick $ preimage 𝜋_TickU $ setI ecov_val $
  preimage 𝜋_ValU $ setI vcov_lit $ preimage 𝜋_LitVU $ bcov_LitInt.

Lemma cover_rec_meas_set : measurable cover_rec.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_pair_meas_set : measurable cover_pair.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_injL_meas_set : measurable cover_injL.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_injR_meas_set : measurable cover_injR.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_app_meas_set : measurable cover_app.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_unop_meas_set : measurable cover_unop.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_binop_meas_set : measurable cover_binop.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_alloc_meas_set : measurable cover_alloc.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_load_meas_set : measurable cover_load.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_store_meas_set : measurable cover_store.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_ifT_meas_set : measurable cover_ifT.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_ifF_meas_set : measurable cover_ifF.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_fst_meas_set : measurable cover_fst.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_snd_meas_set : measurable cover_snd.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_caseL_meas_set : measurable cover_caseL.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_caseR_meas_set : measurable cover_caseR.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_allocTape_meas_set : measurable cover_allocTape.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_allocUTape_meas_set : measurable cover_allocUTape.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_rand_meas_set : measurable cover_rand.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_urand_meas_set : measurable cover_urand.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_randT_meas_set : measurable cover_randT.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_urandT_meas_set : measurable cover_urandT.
Proof. by ms_unfold; ms_solve. Qed.

Lemma cover_tick_meas_set : measurable cover_tick.
Proof. by ms_unfold; ms_solve. Qed.

Hint Resolve cover_rec_meas_set        : mf_set.
Hint Resolve cover_pair_meas_set       : mf_set.
Hint Resolve cover_injL_meas_set       : mf_set.
Hint Resolve cover_injR_meas_set       : mf_set.
Hint Resolve cover_app_meas_set        : mf_set.
Hint Resolve cover_unop_meas_set       : mf_set.
Hint Resolve cover_binop_meas_set      : mf_set.
Hint Resolve cover_alloc_meas_set      : mf_set.
Hint Resolve cover_load_meas_set       : mf_set.
Hint Resolve cover_store_meas_set      : mf_set.
Hint Resolve cover_ifT_meas_set        : mf_set.
Hint Resolve cover_ifF_meas_set        : mf_set.
Hint Resolve cover_fst_meas_set        : mf_set.
Hint Resolve cover_snd_meas_set        : mf_set.
Hint Resolve cover_caseL_meas_set      : mf_set.
Hint Resolve cover_caseR_meas_set      : mf_set.
Hint Resolve cover_allocTape_meas_set  : mf_set.
Hint Resolve cover_allocUTape_meas_set : mf_set.
Hint Resolve cover_rand_meas_set       : mf_set.
Hint Resolve cover_urand_meas_set      : mf_set.
Hint Resolve cover_randT_meas_set      : mf_set.
Hint Resolve cover_urandT_meas_set     : mf_set.
Hint Resolve cover_tick_meas_set       : mf_set.

Definition head_stepM_rec : cfg -> giryM cfg :=
  gRet \o (ValU \o RecVU \o 𝜋_RecU \o fst △ snd).

Definition head_stepM_pair : cfg -> giryM cfg :=
  gRet \o (ValU \o PairVU \o (𝜋_ValU \o 𝜋_Pair_l \o fst △ 𝜋_ValU \o 𝜋_Pair_r \o fst) △ snd).

Definition head_stepM_injL : cfg -> giryM cfg :=
  gRet \o (ValU \o InjLVU \o 𝜋_ValU \o 𝜋_InjLU \o fst △ snd).

Definition head_stepM_injR : cfg -> giryM cfg :=
  gRet \o (ValU \o InjRVU \o 𝜋_ValU \o 𝜋_InjRU \o fst △ snd).

Definition head_stepM_app : cfg -> giryM cfg :=
  let 𝜋_f  := 𝜋_RecV_f \o 𝜋_ValU \o 𝜋_App_l \o fst in
  let 𝜋_x  := 𝜋_RecV_x \o 𝜋_ValU \o 𝜋_App_l \o fst in
  let 𝜋_e1 := 𝜋_RecV_e \o 𝜋_ValU \o 𝜋_App_l \o fst in
  let 𝜋_v2 := 𝜋_ValU \o 𝜋_App_r \o fst in
  gRet \o (substU' \o (𝜋_x △ (𝜋_v2 △ substU' \o (𝜋_f △ (RecVU \o (𝜋_f △ 𝜋_x △ 𝜋_e1) △ 𝜋_e1)))) △ snd).

(*
Definition head_stepM_app' : cfg -> giryM cfg :=
  gRet \o (substU' \o (   𝜋_RecV_f \o 𝜋_ValU \o 𝜋_App_l \o fst
                      △ (𝜋_ValU \o 𝜋_App_r \o fst
                      △ substU' \o (  𝜋_RecV_f \o 𝜋_ValU \o 𝜋_App_l \o fst
                                    △ (RecVU \o (  𝜋_RecV_f \o 𝜋_ValU \o 𝜋_App_l \o fst
                                                 △ 𝜋_RecV_x \o 𝜋_ValU \o 𝜋_App_l \o fst
                                                 △ 𝜋_RecV_e \o 𝜋_ValU \o 𝜋_App_l \o fst )
                                    △ 𝜋_RecV_e \o 𝜋_ValU \o 𝜋_App_l \o fst ))))
           △ snd).
*)


Definition head_stepM_unop : cfg -> giryM cfg :=
  un_op_eval'' \o (𝜋_UnOp_op \o fst △ 𝜋_Val_v \o 𝜋_UnOp_e \o fst △ snd).

Definition head_stepM_binop : cfg -> giryM cfg :=
  bin_op_eval''' \o (𝜋_BinOp_op \o fst △ 𝜋_Val_v \o 𝜋_BinOp_l \o fst △ 𝜋_Val_v \o 𝜋_BinOp_r \o fst △ snd).

Definition head_stepM_alloc : cfg -> giryM cfg :=
  alloc_eval \o (𝜋_ValU \o 𝜋_AllocU \o fst △ snd).

Definition head_stepM_load : cfg -> giryM cfg :=
  load_eval \o (𝜋_LitLoc_l \o 𝜋_LitVU \o 𝜋_ValU \o 𝜋_Load_e \o fst △ snd).

Program Definition head_stepM_store : cfg -> giryM cfg :=
  let 𝜋_l := 𝜋_LitLoc_l \o 𝜋_LitVU \o 𝜋_ValU \o 𝜋_Store_l \o fst in
  let 𝜋_v := 𝜋_ValU \o 𝜋_Store_e \o fst in
  store_eval \o (𝜋_l △ 𝜋_v △ snd).

Definition head_stepM_ifT : cfg -> giryM cfg :=
  gRet \o (𝜋_If_l \o fst △ snd).

Program Definition head_stepM_ifF : cfg -> giryM cfg :=
  gRet \o (𝜋_If_r \o fst △ snd).

Definition head_stepM_fst : cfg -> giryM cfg :=
  gRet \o (ValU \o 𝜋_PairV_l \o 𝜋_ValU \o 𝜋_FstU \o fst △ snd).

Definition head_stepM_snd : cfg -> giryM cfg :=
  gRet \o (ValU \o 𝜋_PairV_r \o 𝜋_ValU \o 𝜋_SndU \o fst △ snd).

Definition head_stepM_caseL : cfg -> giryM cfg :=
  gRet \o (AppU \o (𝜋_Case_l \o fst △ ValU \o 𝜋_InjLVU \o 𝜋_ValU \o 𝜋_Case_c \o fst) △ snd).

Definition head_stepM_caseR : cfg -> giryM cfg :=
  gRet \o (AppU \o (𝜋_Case_r \o fst △ ValU \o 𝜋_InjRVU \o 𝜋_ValU \o 𝜋_Case_c \o fst) △ snd).

Definition head_stepM_allocTape : cfg -> giryM cfg :=
  AllocTape_eval \o (𝜋_LitIntU \o 𝜋_LitVU \o 𝜋_ValU \o 𝜋_AllocTapeU \o fst △ snd).

Definition head_stepM_allocUTape : cfg -> giryM cfg :=
  AllocUTape_eval \o snd.

Definition head_stepM_rand : cfg -> giryM cfg :=
  Rand_eval \o (𝜋_LitIntU \o 𝜋_LitVU \o 𝜋_ValU \o 𝜋_Rand_N \o fst △ snd).

Definition head_stepM_urand : cfg -> giryM cfg :=
  (URand_eval \o snd).

Definition head_stepM_randT : cfg -> giryM cfg :=
  let 𝜋_N := 𝜋_LitIntU \o 𝜋_LitVU \o 𝜋_ValU \o 𝜋_Rand_N \o fst in
  let 𝜋_l := 𝜋_LitLblU \o 𝜋_LitVU \o 𝜋_ValU \o 𝜋_Rand_t \o fst in
  RandT_eval \o ((𝜋_N △ 𝜋_l) △ snd).

Definition head_stepM_urandT : cfg -> giryM cfg :=
  URandT_eval \o (𝜋_LitLblU \o 𝜋_LitVU \o 𝜋_ValU \o 𝜋_URand_e \o fst  △ snd).

Definition head_stepM_tick : cfg -> giryM cfg :=
  gRet \o (cst (ValU $ LitVU $ LitUnitU) △ snd).

Ltac mf_restrictT :=
  match goal with
  | |- (measurable_fun _ _) => apply mathcomp_measurable_fun_restiction_setT; [ try by ms_solve | ]
  end.

(** Ltacs for banging head onto wall *)
(** [destruct!] destructs things in the context *)
Local Ltac destruct_go tac :=
  repeat match goal with
         | H : context [ match ?x with | (y, z) => _ end] |- _ =>
             let y := fresh y in
             let z := fresh z in
             destruct x as [y z]
         | H : ∃ x, _ |- _ => let x := fresh x in destruct H as [x H]
         | H : (ex2 _ _) |- _ => destruct H
         | H: (_*_) |- _ => destruct H                          
         | |- _ => destruct_and!
         | |- _ => destruct_or!
         | |- _ => progress simplify_eq
         | |- _ => tac
    end.

Local Tactic Notation "destruct!/=" := destruct_go ltac:( progress csimpl in * ; simpl).

Local Ltac subset_solver :=
    intros ?; try done; elim; naive_solver.

Local Lemma setIfront {T} (A B: set T): A `&` B = A `&` (A `&` B).
Proof.
  by rewrite setIA setIid.
Qed.

Local Ltac mf_cmp_tree' :=
  eapply @measurable_comp; simpl;
  last (rewrite setIfront;
      apply @measurable_fun_setI1; [by ms_done| by ms_solve |by mf_done]); last first. 

Local Ltac mf_solve' :=
  rewrite setIfront;
  apply @measurable_fun_setI1; [by ms_done| by ms_solve |by mf_done].

Local Lemma set_prod_rewrite {A B} S:
  (([set: A * B] `&` fst @^-1` S) =
   S `*` [set:B]).
Proof.
  rewrite eqEsubset; split; subset_solver.
Qed.

Local Lemma set_rewrite {A} (S1 S2:set A) :
  (S1 `&` S2) = (S1 `&` (S1 `&` S2)).
Proof. 
  rewrite eqEsubset; split; subset_solver.
Qed.

Lemma head_stepM_rec_meas_fun : measurable_fun cover_rec head_stepM_rec.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  mf_prod.
  { simpl; mf_cmp_tree.
    { subset_solver.  }
    mf_cmp_tree.
    mf_cmp_tree.
    { by apply ValU_meas_fun. }
    { by apply RecVU_meas_fun. }
  }
  { mf_restrictT.
    by ms_solve.
  }
Qed.

Lemma head_stepM_pair_meas_fun : measurable_fun cover_pair head_stepM_pair.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  mf_prod.
  { mf_cmp_tree.
    { mf_cmp_tree; [by apply ValU_meas_fun | by apply PairVU_meas_fun]. }
    mf_prod.
    { simpl; mf_cmp_tree.
      { by ms_solve. }
      - subset_solver.
      - eapply measurable_comp; [| |apply 𝜋_ValU_meas|].
        + ms_done.
        + (* Just pushing on the definitions *)
          eauto with projection_subs.
        + (* This is a really annoying trick. Before doing setI1 in this case you want to
             duplicate the intersection with ecov_pair *)
          rewrite set_rewrite.
          apply: measurable_fun_setI1; [ by ms_done | | by apply 𝜋_Pair_l_meas].
          
          (* Now the remaining goal is the preimage intersected with its domain set, which is a lemma
             we already have *)
          apply 𝜋_PairU_meas; try by ms_done.
          ms_prod; by ms_done.
    }
    { (* Should be pretty much the same? *)
      simpl; mf_cmp_tree.
      { by ms_solve. }
      - subset_solver.
      - eapply measurable_comp; [| |apply 𝜋_ValU_meas|].
        + ms_done.
        + (* Just pushing on the definitions *)
          eauto with projection_subs.
        + rewrite set_rewrite.
          apply: measurable_fun_setI1; [ by ms_done | | by apply 𝜋_Pair_r_meas].
          
          (* Now the remaining goal is the preimage intersected with its domain set, which is a lemma
             we already have *)
          apply 𝜋_PairU_meas; try by ms_done.
          ms_prod; by ms_done.
  }
  }
   mf_restrictT. by ms_solve. 
Qed.

Lemma head_stepM_injL_meas_fun       : measurable_fun cover_injL       head_stepM_injL.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  mf_prod.
  { simpl; mf_cmp_tree; first by ms_solve.
    { subset_solver. }
    mf_cmp_tree.
    { subset_solver. }
    mf_cmp_tree.
    mf_cmp_tree.
    { by apply ValU_meas_fun. }
    { by apply InjLVU_meas_fun. }
  }
  { mf_restrictT. by ms_solve. }
Qed. 

Lemma head_stepM_injR_meas_fun       : measurable_fun cover_injR       head_stepM_injR.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  mf_prod.
  { simpl; mf_cmp_tree; first by ms_solve.
    { subset_solver. }
    mf_cmp_tree.
    { subset_solver. }
    mf_cmp_tree.
    mf_cmp_tree.
    { by apply ValU_meas_fun. }
    { by apply InjRVU_meas_fun. }
  }
  { mf_restrictT. by ms_solve. }
Qed.

Lemma head_stepM_app_meas_fun        : measurable_fun cover_app        head_stepM_app.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  mf_prod.
  { mf_cmp_tree; first by apply substU'_measurable.
    (* Fix eta expansion*)
    erewrite (functional_extensionality _ ( _ \o fst)); last first.
    { intros [??]. by simpl. }
    simpl; mf_cmp_tree; [by ms_solve|subset_solver|].
    repeat mf_prod.
    (* Works: eapply @measurable_fun_prod' *)
    - eapply (measurable_comp (f:=𝜋_RecV_x)); [| |apply 𝜋_RecV_x_meas|].
      + ms_done.
      + subset_solver.
      + eapply (measurable_comp (f:=𝜋_ValU)); [| |apply 𝜋_ValU_meas|].
        * ms_done.
        * subset_solver.
        * rewrite set_rewrite. 
          apply: measurable_fun_setI1; [ms_done| |apply 𝜋_App_l_meas].
          apply 𝜋_AppU_meas; try by ms_done.
          ms_prod; last by ms_done.
          apply 𝜋_Val_v_meas; by ms_done.
    - eapply (measurable_comp (f:=𝜋_ValU)); [| |apply 𝜋_ValU_meas|].
      + ms_done.
      + subset_solver.
      + rewrite set_rewrite. 
        apply: measurable_fun_setI1; [ms_done| |apply 𝜋_App_r_meas].
        apply 𝜋_AppU_meas; try by ms_done.
        ms_prod; last by ms_done.
        apply 𝜋_Val_v_meas; by ms_done.
    - eapply (measurable_comp (f:=substU'));
        [| |apply substU'_measurable|];
        [ms_done|subset_solver| ].
      mf_prod.
      + eapply (measurable_comp (f:=𝜋_RecV_f)); [| |apply 𝜋_RecV_f_meas|].
        * ms_done.
        * subset_solver.
        * eapply (measurable_comp (f:=𝜋_ValU)); [| |apply 𝜋_ValU_meas|].
          -- ms_done.
          -- subset_solver.
          -- rewrite set_rewrite. 
             apply: measurable_fun_setI1; [ms_done| |apply 𝜋_App_l_meas].
             apply 𝜋_AppU_meas; try by ms_done.
             ms_prod; last by ms_done.
             apply 𝜋_Val_v_meas; by ms_done.
      + mf_prod.
        * eapply (mathcomp_measurable_fun_ext _ _
                    (RecVU \o
                       (λ x, ((𝜋_RecV_f (𝜋_ValU (𝜋_App_l x))),
                                (𝜋_RecV_x (𝜋_ValU (𝜋_App_l x))),
                                  (𝜋_RecV_e (𝜋_ValU (𝜋_App_l x))))))); last first.
          -- naive_solver.
          -- mf_cmp_tree; first apply RecVU_meas_fun.
             mf_prod; first mf_prod.
             ++ eapply (measurable_comp (f:=𝜋_RecV_f)); [| |apply 𝜋_RecV_f_meas|].
                ** ms_done.
                ** subset_solver.
                **  eapply (measurable_comp (f:=𝜋_ValU)); [| |apply 𝜋_ValU_meas|].
                    --- ms_done.
                    ---  subset_solver.
                    ---   rewrite set_rewrite.
                          apply: measurable_fun_setI1; [ms_done| |apply 𝜋_App_l_meas].
                          apply 𝜋_AppU_meas; try by ms_done.
                          ms_prod; last by ms_done.
                          apply 𝜋_Val_v_meas; by ms_done.
             ++ eapply (measurable_comp (f:=𝜋_RecV_x)); [| |apply 𝜋_RecV_x_meas|].
                ** ms_done.
                ** subset_solver.
                **  eapply (measurable_comp (f:=𝜋_ValU)); [| |apply 𝜋_ValU_meas|].
                    --- ms_done.
                    ---  subset_solver.
                    ---   rewrite set_rewrite.
                          apply: measurable_fun_setI1; [ms_done| |apply 𝜋_App_l_meas].
                          apply 𝜋_AppU_meas; try by ms_done.
                          ms_prod; last by ms_done.
                          apply 𝜋_Val_v_meas; by ms_done. 
             ++ eapply (measurable_comp (f:=𝜋_RecV_e)); [| |apply 𝜋_RecV_e_meas|].
                ** ms_done.
                ** subset_solver.
                **  eapply (measurable_comp (f:=𝜋_ValU)); [| |apply 𝜋_ValU_meas|].
                    --- ms_done.
                    ---  subset_solver.
                    ---   rewrite set_rewrite.
                          apply: measurable_fun_setI1; [ms_done| |apply 𝜋_App_l_meas].
                          apply 𝜋_AppU_meas; try by ms_done.
                          ms_prod; last by ms_done.
                          apply 𝜋_Val_v_meas; by ms_done.
        * eapply (measurable_comp (f:=𝜋_RecV_e)); [| |apply 𝜋_RecV_e_meas|].
          -- ms_done.
          -- subset_solver.
          --  eapply (measurable_comp (f:=𝜋_ValU)); [| |apply 𝜋_ValU_meas|].
              ++ ms_done.
              ++  subset_solver.
              ++  rewrite set_rewrite.
                  apply: measurable_fun_setI1; [ms_done| |apply 𝜋_App_l_meas].
                  apply 𝜋_AppU_meas; try by ms_done.
                  ms_prod; last by ms_done.
                  apply 𝜋_Val_v_meas; by ms_done.
  }
  { mf_restrictT. by ms_solve. }
  Unshelve.
  apply 𝜋_AppU_meas; first ms_done.
  ms_prod; last ms_done.
  apply 𝜋_Val_v_meas; ms_done.
Qed.

Lemma head_stepM_unop_meas_fun       : measurable_fun cover_unop       head_stepM_unop.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  (* Fix eta expansion! *)
  mf_cmp_tree; first by apply un_op_eval''_meas_fun.
  mf_prod; first mf_prod.
  - eapply measurable_comp; [| |apply 𝜋_UnOp_op_meas|].
    { ms_done. }
    { subset_solver. }
    eapply @measurable_fst_restriction.
    ms_done.
  - mf_cmp_fst; first by ms_solve.
    eapply @measurable_comp.
    3: by apply 𝜋_Val_v_meas.
    { by ms_solve. }
    { by subset_solver. }
    rewrite <- (setIid ecov_unop).
    rewrite <- (setIA ecov_unop).
    apply measurable_fun_setI1; [by ms_done| by ms_solve |by mf_done].
  - eapply @measurable_snd_restriction.
    ms_done.
Qed.

Lemma head_stepM_binop_meas_fun      : measurable_fun cover_binop      head_stepM_binop.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by apply bin_op_eval'''_meas_fun.
  mf_prod; last (eapply @measurable_snd_restriction; ms_solve).
  mf_prod; first mf_prod; mf_cmp_fst; try ms_solve.
  - rewrite <- (setIid ecov_binop).
    rewrite <- (setIA ecov_binop).
    apply measurable_fun_setI1; [by ms_done| by ms_solve |by mf_done].
  - eapply @measurable_comp.
    3: by apply 𝜋_Val_v_meas.
    { by ms_solve. }
    { by subset_solver. }
    rewrite <- (setIid ecov_binop).
    rewrite <- (setIA ecov_binop).
    apply measurable_fun_setI1; [by ms_done| by ms_solve |by mf_done].
  - eapply @measurable_comp.
    3: by apply 𝜋_Val_v_meas.
    { by ms_solve. }
    { by subset_solver. }
    rewrite <- (setIid ecov_binop).
    rewrite <- (setIA ecov_binop).
    apply measurable_fun_setI1; [by ms_done| by ms_solve |by mf_done].
Qed.

Lemma head_stepM_alloc_meas_fun      : measurable_fun cover_alloc      head_stepM_alloc.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first apply alloc_eval_meas_fun.
  mf_prod.
  - simpl.
    assert (([set: expr_T * state] `&` fst @^-1` (ecov_alloc `&` 𝜋_AllocU @^-1` ecov_val)) =
            ( (ecov_alloc `&` 𝜋_AllocU @^-1` ecov_val)) `*` [set:state]) as Hrewrite;
      last rewrite Hrewrite.
    { rewrite eqEsubset. split; subset_solver. }
    mf_cmp_fst; first ms_solve.
    mf_cmp_tree'; first apply 𝜋_ValU_meas.
    { subset_solver. }
    ms_solve.
  - eapply @measurable_snd_restriction.
    ms_done.
Qed.

Lemma head_stepM_load_meas_fun       : measurable_fun cover_load       head_stepM_load.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  mf_prod.
  { simpl.
    assert (([set: expr_T * state]`&` fst @^-1`(ecov_load
                  `&` 𝜋_LoadU @^-1` (ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitLoc)))) =  (ecov_load `&` (ecov_load `&` 𝜋_LoadU @^-1` (ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitLoc)))) `*` [set:state]) as Hrewrite;
      last rewrite Hrewrite.
    { rewrite eqEsubset. split; subset_solver. }
    mf_cmp_fst.
    { rewrite setIA.
      rewrite setIid.
      by ms_solve.
    }
    eapply @measurable_comp; simpl; last first.
    { apply @measurable_fun_setI1; [by ms_done| by ms_solve |by mf_done]. }
    2: { rewrite setIA setIid.
         instantiate (1:= (ecov_val `&` (ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitLoc)))).
         subset_solver.
    }
    - eapply @measurable_comp; simpl; last first.
      { 
        apply @measurable_fun_setI1; [by ms_done|ms_solve|by mf_done].
      }
      2: { instantiate (1:= vcov_lit `&` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitLoc)).
           subset_solver.
      }
      2:{ rewrite setIA setIid. ms_solve. }
      eapply @measurable_comp; simpl; last first.
      { apply @measurable_fun_setI1; [by ms_done| by ms_solve |by mf_done]. }
      + apply 𝜋_LitLoc_l_meas.
      + subset_solver.
      + ms_done.
    - ms_solve.
    }
    { mf_restrictT. by ms_solve. }
Qed.

Lemma head_stepM_store_meas_fun      : measurable_fun cover_store      head_stepM_store.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  simpl.
  assert (([set: expr_T * state]
             `&` fst @^-1`
             (ecov_store
                `&` 𝜋_StoreU @^-1`
                ((ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitLoc)) `*` ecov_val))) =  (ecov_store
                `&` 𝜋_StoreU @^-1`
                ((ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitLoc)) `*` ecov_val)) `*` [set:state]) as Hrewrite.
  { rewrite eqEsubset. split; subset_solver. }
  rewrite Hrewrite.
  mf_prod; last (eapply @measurable_snd_restriction; ms_solve).
  mf_prod.
  - assert ((λ x : cfg, 𝜋_LitLoc_l (𝜋_LitVU (𝜋_ValU (𝜋_Store_l x.1)))) =
      (𝜋_LitLoc_l \o 𝜋_LitVU \o 𝜋_ValU \o 𝜋_Store_l \o fst (B:= state))) as Hrewrite'; last rewrite Hrewrite'. 
    { apply functional_extensionality_dep. naive_solver. }
    mf_cmp_fst; first ms_solve.
    eapply @measurable_comp; simpl; last first.
    { rewrite setIfront.
      apply @measurable_fun_setI1; [by ms_done| by ms_solve |by mf_done]. 
    }
    2:{ instantiate (1:= (ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitLoc))).
        subset_solver. 
    }
    2:{ ms_solve. }
    eapply @measurable_comp; simpl; last first.
    { rewrite setIfront.
      apply @measurable_fun_setI1; [by ms_done| by ms_solve |by mf_done]. 
    }
    2:{ instantiate (1:=vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitLoc).
        subset_solver. 
    }
    2:{ ms_solve. }
    eapply @measurable_comp; simpl; last first.
    { rewrite setIfront.
      apply @measurable_fun_setI1; [by ms_done| by ms_solve |by mf_done]. 
    }
    + apply 𝜋_LitLoc_l_meas.
    + subset_solver.
    + ms_solve.
  - assert ((λ x : cfg, 𝜋_ValU (𝜋_Store_e x.1)) =
            ( 𝜋_ValU \o 𝜋_Store_e \o fst (B:= state))) as Hrewrite'; last rewrite Hrewrite'.
    { apply functional_extensionality_dep. naive_solver. }
    mf_cmp_fst; first ms_solve.
    mf_cmp_tree'; first apply 𝜋_ValU_meas.
    { subset_solver. }
    ms_solve.
Qed.

Lemma head_stepM_ifT_meas_fun        : measurable_fun cover_ifT        head_stepM_ifT.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  mf_prod.
  { simpl; mf_cmp_tree; first by ms_solve.
    { subset_solver.  }
    rewrite setIfront.
    apply @measurable_fun_setI1; [by ms_done| by ms_solve |by mf_done]. }
  { mf_restrictT. by ms_solve. }
Qed.

Lemma head_stepM_ifF_meas_fun        : measurable_fun cover_ifF        head_stepM_ifF.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  mf_prod.
  { simpl. mf_cmp_tree; first by ms_solve.
    { subset_solver.  }
    rewrite setIfront.
    apply @measurable_fun_setI1; [by ms_done| by ms_solve |by mf_done]. }
  { mf_restrictT. by ms_solve. }
Qed.

Lemma head_stepM_fst_meas_fun        : measurable_fun cover_fst        head_stepM_fst.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  mf_prod.
  { simpl; mf_cmp_tree; first by ms_solve.
    { subset_solver. }
    mf_cmp_tree; first by ms_solve.
    { subset_solver. }
    mf_cmp_tree.
    { subset_solver. }
    mf_cmp_tree.
    by apply ValU_meas_fun.
  }
  { mf_restrictT. by ms_solve. }
Qed.

Lemma head_stepM_snd_meas_fun        : measurable_fun cover_snd        head_stepM_snd.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  mf_prod.
  { simpl; mf_cmp_tree; first by ms_solve.
    { subset_solver. }
    mf_cmp_tree; first by ms_solve.
    { subset_solver. }
    mf_cmp_tree.
    { subset_solver. }
    mf_cmp_tree.
    by apply ValU_meas_fun. }
  { mf_restrictT. by ms_solve. }
Qed.

Lemma head_stepM_caseL_meas_fun      : measurable_fun cover_caseL      head_stepM_caseL.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  mf_prod.
  {
    mf_cmp_tree; first apply AppU_meas_fun.
    mf_prod.
    - simpl; mf_cmp_tree; first ms_solve.
      + subset_solver.
      + mf_solve'.
    - simpl; mf_cmp_tree; [ms_solve|subset_solver|].
      mf_cmp_tree; [ms_solve|subset_solver|].
      mf_cmp_tree; [subset_solver|mf_cmp_tree].
      apply ValU_meas_fun.
  }
  { mf_restrictT. by ms_solve. }
Qed.

Lemma head_stepM_caseR_meas_fun      : measurable_fun cover_caseR      head_stepM_caseR.
Proof.
  mf_unfold_dom; mf_unfold_fun. 
  mf_cmp_tree; first by mf_done.
  mf_prod.
  { mf_cmp_tree; first apply AppU_meas_fun.
    mf_prod.
    - simpl; mf_cmp_tree; first ms_solve.
      + subset_solver.
      + mf_solve'.
    - simpl; mf_cmp_tree; [ms_solve|subset_solver|].
      mf_cmp_tree; [ms_solve|subset_solver|].
      mf_cmp_tree; [subset_solver|mf_cmp_tree].
      apply ValU_meas_fun.
  }
  { mf_restrictT. by ms_solve. }
Qed.

Lemma head_stepM_allocTape_meas_fun  : measurable_fun cover_allocTape  head_stepM_allocTape.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  mf_prod.
  { simpl.
    assert (([set: expr_T * state]
     `&` fst @^-1`
         (ecov_alloctape
            `&` 𝜋_AllocTapeU @^-1` (ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitInt))))
            = (ecov_alloctape
            `&` 𝜋_AllocTapeU @^-1` (ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitInt))) `*` [set: state]
           ) as Hrewrite; first (rewrite eqEsubset; split; subset_solver ).
    rewrite Hrewrite.
    mf_cmp_fst; first ms_solve.
    mf_cmp_tree'.
    2: { instantiate (1 := (ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitInt))).
         subset_solver.
    }
    2: { ms_solve. }
    mf_cmp_tree'.
    2:{ instantiate (1:=(vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitInt)).
        subset_solver. }
    2:{ ms_solve. }
    mf_cmp_tree'.
    - apply 𝜋_LitIntU_meas.
    - subset_solver.
    - ms_solve. }
  { mf_restrictT. by ms_solve. }
Qed.

Lemma head_stepM_allocUTape_meas_fun : measurable_fun cover_allocUTape head_stepM_allocUTape.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  simpl.
  assert (([set: expr_T * state] `&` fst @^-1` ecov_allocutape) = ecov_allocutape `*` [set:state]).
  { rewrite eqEsubset; split; subset_solver . }
  eapply @measurable_snd_restriction; ms_solve.
Qed.

Lemma head_stepM_rand_meas_fun       : measurable_fun cover_rand       head_stepM_rand.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  mf_prod.
  { simpl.
    assert (([set: expr_T * state]
     `&` fst @^-1`
         (ecov_rand
          `&` 𝜋_RandU @^-1`
              ((ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitInt))
                 `*` (ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitUnit))))) =
            (ecov_rand
          `&` 𝜋_RandU @^-1`
              ((ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitInt))
                 `*` (ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitUnit)))) `*` [set: state]
           ) as Hrewrite.
    { rewrite eqEsubset; split; subset_solver. }
    rewrite Hrewrite.
    mf_cmp_fst; first ms_solve.
    mf_cmp_tree'.
    2:{ instantiate (1:= ((ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitInt))
          )).
        subset_solver. }
    2:{ ms_solve. }
    mf_cmp_tree'.
    2:{ instantiate (1:= (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitInt)).
        subset_solver.
    }
    2:{ ms_solve. }
    mf_cmp_tree'.
    - apply 𝜋_LitIntU_meas.
    - subset_solver.
    - ms_solve.
  }
  { mf_restrictT. by ms_solve. }
Qed.

Lemma head_stepM_urand_meas_fun      : measurable_fun cover_urand      head_stepM_urand.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  simpl.
  eassert (([set: expr_T * state]
     `&` fst @^-1`
         (ecov_urand
            `&` 𝜋_URandU @^-1` (ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitUnit)))) =
           (ecov_urand
            `&` 𝜋_URandU @^-1` (ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitUnit)))`*` [set:state]) as Hrewrite.
  { rewrite eqEsubset; split; subset_solver. }
  rewrite Hrewrite.
  eapply @measurable_snd_restriction; ms_solve.
Qed.

Lemma head_stepM_randT_meas_fun      : measurable_fun cover_randT      head_stepM_randT.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  rewrite set_prod_rewrite.
  mf_prod; last eapply @measurable_snd_restriction; ms_solve.
  mf_prod.
  { apply: measurableX; ms_solve. }
  -  eapply (measurable_comp (F:=(ecov_rand
      `&` 𝜋_RandU @^-1`
          ((ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitInt))
             `*` (ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitLbl)))))); [ms_solve|..].
     + remember (_`&`_) as K. intros ?. simpl.
       intros [[]]; simpl in *. naive_solver.
     + mf_cmp_tree'.
       * instantiate (1:= (ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitInt))).
         mf_cmp_tree.
         -- ms_solve.
         -- subset_solver.
         -- mf_cmp_tree. apply 𝜋_LitIntU_meas.
       * remember ((ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitInt))) as K eqn:Heqn.
         rewrite -Heqn.
         intros ?.  simpl.
         intros. destruct!/=. repeat split; naive_solver.
       * ms_solve.
     + apply: measurable_fst_restriction; last ms_solve.
  - eapply (measurable_comp (F:=(ecov_rand
      `&` 𝜋_RandU @^-1`
          ((ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitInt))
             `*` (ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitLbl)))))); [ms_solve|..].
     + remember (_`&`_) as K. intros ?. simpl.
       intros [[]]; simpl in *. naive_solver.
     + mf_cmp_tree'.
       * instantiate (1:= (ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitLbl))).
         mf_cmp_tree.
         -- ms_solve.
         -- subset_solver.
         -- mf_cmp_tree. apply 𝜋_LitLblU_meas.
       * remember ((ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitLbl))) as K eqn:Heqn.
         rewrite -Heqn.
         intros ?.  simpl.
         intros. destruct!/=. repeat split; naive_solver.
       * ms_solve.
     + apply: measurable_fst_restriction; last ms_solve.
Qed.

Lemma head_stepM_urandT_meas_fun     : measurable_fun cover_urandT     head_stepM_urandT.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  mf_prod.
  { rewrite set_prod_rewrite.
    mf_cmp_fst; first ms_solve.
    mf_cmp_tree'.
    2:{ instantiate (1:= (ecov_val `&` 𝜋_ValU @^-1` (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitLbl))).
        subset_solver. }
    2:{ ms_solve. }
    mf_cmp_tree'.
    2:{ instantiate (1:= (vcov_lit `&` 𝜋_LitVU @^-1` bcov_LitLbl)).
        subset_solver. }
    2:{ ms_solve. }
    mf_cmp_tree'.
    - apply 𝜋_LitLblU_meas.
    - subset_solver.
    - ms_solve. }
  { mf_restrictT. by ms_solve. }
Qed. 

Lemma head_stepM_tick_meas_fun       : measurable_fun cover_tick       head_stepM_tick.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  mf_prod.
  mf_restrictT. by ms_solve.
Qed.

Hint Resolve head_stepM_rec_meas_fun        : mf_fun.
Hint Resolve head_stepM_pair_meas_fun       : mf_fun.
Hint Resolve head_stepM_injL_meas_fun       : mf_fun.
Hint Resolve head_stepM_injR_meas_fun       : mf_fun.
Hint Resolve head_stepM_app_meas_fun        : mf_fun.
Hint Resolve head_stepM_unop_meas_fun       : mf_fun.
Hint Resolve head_stepM_binop_meas_fun      : mf_fun.
Hint Resolve head_stepM_alloc_meas_fun      : mf_fun.
Hint Resolve head_stepM_load_meas_fun       : mf_fun.
Hint Resolve head_stepM_store_meas_fun      : mf_fun.
Hint Resolve head_stepM_ifT_meas_fun        : mf_fun.
Hint Resolve head_stepM_ifF_meas_fun        : mf_fun.
Hint Resolve head_stepM_fst_meas_fun        : mf_fun.
Hint Resolve head_stepM_snd_meas_fun        : mf_fun.
Hint Resolve head_stepM_caseL_meas_fun      : mf_fun.
Hint Resolve head_stepM_caseR_meas_fun      : mf_fun.
Hint Resolve head_stepM_allocTape_meas_fun  : mf_fun.
Hint Resolve head_stepM_allocUTape_meas_fun : mf_fun.
Hint Resolve head_stepM_rand_meas_fun       : mf_fun.
Hint Resolve head_stepM_urand_meas_fun      : mf_fun.
Hint Resolve head_stepM_randT_meas_fun      : mf_fun.
Hint Resolve head_stepM_urandT_meas_fun     : mf_fun.
Hint Resolve head_stepM_tick_meas_fun       : mf_fun.


Definition head_stepM' : cfg -> giryM cfg :=
  if_in cover_rec        head_stepM_rec        $
  if_in cover_pair       head_stepM_pair       $
  if_in cover_injL       head_stepM_injL       $
  if_in cover_injR       head_stepM_injR       $
  if_in cover_app        head_stepM_app        $
  if_in cover_unop       head_stepM_unop       $
  if_in cover_binop      head_stepM_binop      $
  if_in cover_alloc      head_stepM_alloc      $
  if_in cover_load       head_stepM_load       $
  if_in cover_store      head_stepM_store      $
  if_in cover_ifT        head_stepM_ifT        $
  if_in cover_ifF        head_stepM_ifF        $
  if_in cover_fst        head_stepM_fst        $
  if_in cover_snd        head_stepM_snd        $
  if_in cover_caseL      head_stepM_caseL      $
  if_in cover_caseR      head_stepM_caseR      $
  if_in cover_allocTape  head_stepM_allocTape  $
  if_in cover_allocUTape head_stepM_allocUTape $
  if_in cover_rand       head_stepM_rand       $
  if_in cover_urand      head_stepM_urand      $
  if_in cover_randT      head_stepM_randT      $
  if_in cover_urandT     head_stepM_urandT     $
  if_in cover_tick       head_stepM_tick       $
  cst gZero.


(** Slow proof, but can just uncomment *)
Lemma head_stepM'_meas_fun : measurable_fun setT head_stepM'.
  (* rewrite /head_stepM'. *)
(*   (eapply @if_in_meas_fun; [ms_done|ms_solve|rewrite setIidl; [eauto with mf_fun|subset_solver]| *)
(*                              rewrite setIidl; last subset_solver *)
(*   ]). *)
(*   repeat( eapply @if_in_meas_fun; [ms_done|ms_solve|apply @measurable_fun_setI1; [ms_solve|ms_solve|eauto with mf_fun]|]). *)
(*   (* computer goes brrr... *) *)
(*   ms_solve. *)
  (* Qed. *)
Admitted.



Local Ltac unfold_if_in := match goal with | |- context [(if_in ?X _)] => unfold X end.
Local Ltac unfold_RHS := match goal with | |- _ = ?X _ => unfold X end.

Local Ltac smart_intro := match goal with
                     | |- (@ex2 (_*_*_) _ _) => eexists (_,_,_)
                     | |- (@ex2 (_*_) _ _) => eexists (_,_)
                    | |- (@ex2 (_) _ _) => eexists (_)
                    | |- _ => simpl
                     end.
Local Ltac head_step_solver:= repeat split; try done; smart_intro; naive_solver.
Local Ltac reject_right H :=rewrite ifIn_eq_right; last 
         (intros H1; destruct H as [? [[][]]]; destruct H1 as [? [[][]]];
          simpl in *; simplify_eq; simpl in *; simplify_eq; simpl; done).
Local Ltac accept_left H :=rewrite ifIn_eq_left; last done;
        destruct H as [? [[][]]]; simpl in *; simplify_eq; simpl in *; simplify_eq; simpl;
        done.

Lemma bool_decide_asbool P Q: (bool_decide (dec:=Q) P) = (asbool P).
Proof.
  rewrite /bool_decide.
  destruct Q; simpl.
  - by rewrite asboolT.
  - by rewrite asboolF.
Qed.

Lemma head_stepM_head_stepM'_eq : head_stepM = head_stepM'.
  apply functional_extensionality_dep.
  intros [e σ].
  rewrite /head_stepM/head_stepM'.
  repeat unfold_if_in.
  destruct!/=.
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H1].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H2].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H3].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H4].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H5].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H6].
  { rewrite /head_stepM_unop/=/un_op_eval''. clear.
    apply if_in_split.
    - (* un_op ok*)
      intros [[[[H|H]|H]|H] _]; simpl in *; rewrite /un_op_eval'/of_option/𝜋_Some_v/=.
      + accept_left H.
      + reject_right H. accept_left H.
      + do 2 reject_right H. accept_left H.
      + do 3 reject_right H. accept_left H.
    - intros H.
      case_match eqn: H'; last done.
      exfalso. apply H.
      unfold un_op_eval, un_op_eval''_ok in *. simpl. split; last done.
      repeat case_match; try done; simplify_eq.
      + do 2 left. right. repeat split; try done. simpl. naive_solver.
      + repeat left; repeat split; try done; naive_solver.
      + left. right. repeat split; naive_solver.
      + right; repeat split; naive_solver.
  }
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H7].
  { rewrite /head_stepM_binop/=/bin_op_eval'''. clear.
    apply if_in_split.
    - (* bin_op ok*)
      rewrite /bin_op_eval''_ok/bin_op_eval''/of_option/𝜋_Some_v/=/bin_op_eval'.
      rewrite !Logic.or_assoc.
      assert (∀ P Q, P \/ Q <-> P \/ (¬ P /\ Q)) as Hrewrite.
      { split; last naive_solver.
        pose proof lem P as [|]; naive_solver.
      }
      rewrite Hrewrite.
      elim. intros H _; revert H.
      elim.
      { rewrite /bin_op_eval'_cov_eq/safe_val_pair/safe_val.
        intros H. rewrite ifIn_eq_left; last done.
        rewrite /bin_op_eval'_eq.
        rewrite /bin_op_eval'_cov_eq in H.
        rewrite /bin_op_eval'_cov_eq_same/safe_val_pair/safe_val/safe_val_diag/base_lit_diag.
        eapply if_in_split.
        - rewrite /bin_op_eval'_cov_eq_same; intros.
          destruct!/=; rewrite /bin_op_eval/=;
            repeat rewrite bool_decide_eq_true_2; try done; rewrite /lit_is_unboxed;repeat case_match; naive_solver.
        - intros H'. rewrite /bin_op_eval.
          rewrite bool_decide_eq_true_2; last by destruct!/=.
          rewrite /vals_compare_safe/val_is_unboxed/lit_is_unboxed.
          rewrite bool_decide_eq_true_2; last (destruct!/=; repeat case_match; auto).
          simpl. repeat f_equal.
          apply bool_decide_eq_false_2.
          intros ->. apply H'. simpl in *. destruct!/=; eexists (_,_); try done; naive_solver.
      }
      elim. intros K1. rewrite Hrewrite. elim.
      { intros H. rewrite ifIn_eq_right; last done.
        rewrite ifIn_eq_left; last done.
        rewrite /bin_op_eval'_int/=.
        rewrite /bin_op_eval'_cov_int in H. destruct!/=.
        rewrite /bin_op_eval. by rewrite bool_decide_eq_false_2.
      }
      elim. intros K2. rewrite Hrewrite. elim.
      { intros H. do 2 (rewrite ifIn_eq_right; last done).
        rewrite ifIn_eq_left; last done.
        rewrite /bin_op_eval'_real/bin_op_eval_real'/=.
        repeat eapply if_in_split; rewrite /bin_op_eval. 
        - intros []; destruct!/=. rewrite /bin_op_eval'_cov_real in H; destruct!/=; by rewrite bool_decide_eq_false_2.
        - intros []; destruct!/=. rewrite /bin_op_eval'_cov_real in H; destruct!/=; by rewrite bool_decide_eq_false_2.
        - intros []; destruct!/=. rewrite /bin_op_eval'_cov_real in H; destruct!/=; by rewrite bool_decide_eq_false_2.
        - intros []; destruct!/=. rewrite /bin_op_eval'_cov_real in H; destruct!/=; rewrite bool_decide_eq_false_2; last done.
          intros. repeat f_equal.
          rewrite /le_real/=.
          apply bool_decide_asbool.
        - intros []; destruct!/=. rewrite /bin_op_eval'_cov_real in H; destruct!/=; rewrite bool_decide_eq_false_2; last done.
          intros. repeat f_equal.
          apply bool_decide_asbool.
        - intros H1 H2 H3 H4 H5. exfalso. rewrite /bin_op_eval'_cov_real in H. destruct!/=.
          + apply H5. rewrite /bin_op_eval_real'_cov_plus; naive_solver.
          + apply H4. rewrite /bin_op_eval_real'_cov_minus; naive_solver.
          + apply H3. rewrite /bin_op_eval_real'_cov_mul; naive_solver.
          + apply H2. rewrite /bin_op_eval_real'_cov_le; naive_solver.
          + apply H1. rewrite /bin_op_eval_real'_cov_lt; naive_solver.
      }
      elim. intros K3. rewrite Hrewrite. elim.
      { intros H. do 3 (rewrite ifIn_eq_right; last done).
        rewrite ifIn_eq_left; last done.
        rewrite /bin_op_eval'_bool/bin_op_eval_bool/=.
        rewrite /bin_op_eval'_cov_bool in H. destruct!/=; rewrite /bin_op_eval/=; by rewrite bool_decide_eq_false_2.
      }
      elim.
      intros K4.
      intros K5.
      do 4 (rewrite ifIn_eq_right; last done).
      rewrite ifIn_eq_left; last done.
      rewrite /bin_op_eval'_locX/bin_op_eval'_loc/=.
      repeat eapply if_in_split.
      1, 2, 3: intros []; destruct K5; destruct!/=; rewrite /bin_op_eval; rewrite bool_decide_eq_false_2; simpl; try done.
      { rewrite /pureops.loc_le/=. by rewrite bool_decide_asbool. }
      { rewrite /pureops.loc_lt/=. by rewrite bool_decide_asbool. }
      intros H1 H2 H3.
      destruct K5; destruct!/=; exfalso.
      + apply H3; split ;naive_solver.
      + apply H2; split; naive_solver.
      + apply H1; split; naive_solver.
    - rewrite /bin_op_eval. case_match eqn:Heqn1; last done.
      intros H.
      exfalso. apply H.
      rewrite /bin_op_eval''_ok.
      simpl. split; last done.
      case_bool_decide as Heqn2.
      { subst. repeat left.
        case_bool_decide; last done.
        eexists (_,_); last done.
        unfold safe_val_pair, vals_compare_safe,val_is_unboxed, safe_val in *; simpl.
        destruct!/=; repeat case_match; naive_solver.
      }
      repeat case_match; try done; destruct!/=.
      + do 3 left. right. split; naive_solver.
      + left. right.
        rewrite /bin_op_eval_bool in Heqn1. repeat case_match; try done; split; simplify_eq; naive_solver.
      + right. rewrite /bin_op_eval'_cov_locX. rewrite /bin_op_eval_loc in Heqn1. repeat case_match; simplify_eq; simpl in *; simplify_eq; naive_solver.
      + do 2 left. right. rewrite /bin_op_eval'_cov_real/bin_op_eval_real in Heqn1 *.
        repeat case_match; simplify_eq; simpl in *; simplify_eq; naive_solver. }
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H8].
  { (* alloc_eval_cov_ok is not defined yet *)
    admit. }
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H9].
  { (* load_eval_cov_ok is not defined yet *)
    admit. }
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H10].
  { (* store_eval_cov_ok is not defined yet *)
    admit. }
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H11].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H12].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H13].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H14].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H15].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H16].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H17].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H18].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H19].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H20].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H21].
  { unfold_RHS. simpl. unfold_RHS. simpl. clear.
    apply if_in_split.
    { intros [? ? [??[? H ]]]. simplify_eq.
      rewrite /RandT_eval_cov_noTape'/option_cov_None/hp_eval/= in H.
      by rewrite /lookup H/=. }
    intros H1 .
    case_match eqn:Heqn; last first.
    { exfalso. apply H1. rewrite /RandT_eval_cov_noTape. eexists _; first done.
      eexists _; first done. simpl. eexists _; last done.
      rewrite /RandT_eval_cov_noTape'/option_cov_None/hp_eval/=.
      by rewrite /lookup in Heqn.
    }
    case_match. case_match. simplify_eq.
    rewrite /lookup in Heqn.
    apply if_in_split.
    { intros H2.
      rewrite bool_decide_eq_false_2.
      - by rewrite /RandT_eval_boundMismatch/=.
      - rewrite /RandT_eval_cov_boundMismatch in H2.
        destruct H2 as [?? [?? [?[? H2 ]?]]]; simplify_eq.
        simpl in *. rewrite /hp_eval/= in H2.
        intros ->. apply H2. by rewrite /of_option /𝜋_Some_v/= Heqn.
    }
    intros H2.
    case_bool_decide as Heqn'; last first. 
    { apply NNP_P. intros H. apply H2.
      eexists _; first done. eexists _; first done. eexists _; last done.
      rewrite /RandT_eval_cov_boundMismatch'/hp_eval/=; split.
      - rewrite Heqn. rewrite /option_cov_Some. eexists _. naive_solver.
      - by rewrite /of_option/𝜋_Some_v/=Heqn. 
    }
    subst. 
    apply if_in_split.
    { intros [??[??[?[[H3 H4] H5]]]]; simpl in *; simplify_eq.
      rewrite /option_cov_None/= in H5.
      unfold hp_eval, of_option, 𝜋_Some_v in *.
      simpl in *. rewrite Heqn/= in H4 H5. subst.
      rewrite /sequence_eval in H5. rewrite H5.
      by rewrite /RandT_eval_nextEmpty/=.
    }
    intros H3.
    case_match eqn :Heqn'; last first.
    { exfalso. apply H3. rewrite /RandT_eval_cov_nextEmpty.
      repeat eexists _; last done; try done.
      repeat split; simpl.
      - rewrite /hp_eval Heqn/option_cov_Some/=. naive_solver.
      - by rewrite /of_option/hp_eval/𝜋_Some_v/= Heqn.
      - by rewrite /option_cov_None/=/of_option/𝜋_Some_v/=/hp_eval Heqn /= /sequence_eval. 
    }
    rewrite /RandT_eval_ok/=.
    repeat f_equal.
    - by rewrite /of_option/𝜋_Some_v/=/hp_eval Heqn /= /sequence_eval Heqn'.
    - rewrite /state_upd_tapes/=. rewrite /of_option/=/hp_eval Heqn/=. do 8 f_equal. lia.
  }
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H22].
  { unfold_RHS. simpl. unfold_RHS. simpl. clear.
    apply if_in_split.
    { intros [?? [? H ?]]. unfold URandT_eval_cov_noTape', option_cov_None, hp_eval in *. simpl in *; simplify_eq.
      by rewrite /lookup/Lookup_instance_0/hp_eval H.
    }
    intros H1.
    case_match; last first.
    { exfalso. apply H1. repeat eexists _; last done; done. }
    case_match.
    subst.
    apply if_in_split.
    { intros [??[? [[x' H'] H''] ?]].
      simplify_eq.
      unfold lookup, Lookup_instance_0, hp_eval in *. simpl in *.
      simplify_eq.
      unfold  option_cov_None, of_option, 𝜋_Some_v in *. simpl in *.
      rewrite H in H''.
      rewrite /sequence_evalC/sequence_eval/= in H''. rewrite H''.
      by rewrite /URandT_eval_nextEmpty/=. }
    intros H2.
    case_match eqn:H0; last first.
    { exfalso. apply H2.
      repeat eexists _; last done; first done.
      rewrite /URandT_eval_cov_nextEmpty'/=.
      split.
      - rewrite /option_cov_Some/hp_eval/=. setoid_rewrite H. naive_solver.
      - rewrite /option_cov_None/of_option/hp_eval/𝜋_Some_v/=.
        by setoid_rewrite H. 
    }
    rewrite /URandT_eval_ok/=. rewrite /state_upd_utapes/=.
    rewrite /of_option/𝜋_Some_v/hp_evalC/hp_eval/=.
    setoid_rewrite H.
    repeat f_equal.
    - by setoid_rewrite H0.
    - simpl. lia. 
  }
  destruct!/=.
  apply (if_in_split (f1 := (head_stepM_tick))); [intros; destruct!/=; try by unfold_RHS|intros H23].
  simpl in *.
  repeat case_match; try done.
  all: subst; exfalso.
  - apply H1. head_step_solver. 
  - apply H5; head_step_solver. 
  - apply H6; head_step_solver.
  - apply H7; head_step_solver.
  - apply H11; head_step_solver.
  - apply H12; head_step_solver.
  - apply H2; head_step_solver.
  - apply H13; head_step_solver.
  - apply H14; head_step_solver.
  - apply H3; head_step_solver.
  - apply H4; head_step_solver.
  - apply H15; head_step_solver.
  - apply H16; head_step_solver.
  - apply H8; head_step_solver.
  - apply H9; head_step_solver.
  - apply H10; head_step_solver.
  - apply H17; head_step_solver.
  - apply H19; head_step_solver.
  - apply H21; head_step_solver.
  - apply H21; head_step_solver.
  - apply H21; head_step_solver.
  - apply H18; head_step_solver.
  - apply H20; head_step_solver.
  - apply H22; head_step_solver.
  - apply H22; head_step_solver.
  - apply H23; head_step_solver.
Admitted.

Lemma head_stepM_meas_fun : measurable_fun setT head_stepM.
Proof.
  rewrite head_stepM_head_stepM'_eq.
  apply head_stepM'_meas_fun.
Qed.


(** Basic properties about the language *)
Global Instance fill_item_inj Ki : Inj eq eq (curry fill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item (Ki, e))) → is_Some (to_val e).
Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.

Lemma val_head_stuck e1 σ1 : ¬ is_zero (head_stepM (e1, σ1)) → to_val e1 = None.
Proof. destruct e1; try done.
       intros H. exfalso. apply H.
       done.
Qed. 

Lemma head_step_ctx_val Ki e σ1 : ¬ is_zero (head_stepM (fill_item (Ki, e), σ1)) → is_Some (to_val e).
Proof.
  destruct e, Ki; try done; simpl; repeat case_match; intros H'; exfalso; by apply H'.
Qed.

End meas_semantics.



(** A relational characterization of the support of [head_step] to make it easier to
    do inversion and prove reducibility easier c.f. lemma below *)
Inductive head_step_rel : expr -> state -> expr -> state → Prop :=
(* Values *)
| RecS f x e σ :
  head_step_rel (Rec f x e) σ (Val $ RecV f x e) σ
| PairS v1 v2 σ :
  head_step_rel (Pair (Val v1) (Val v2)) σ (Val $ PairV v1 v2) σ
| InjLS v σ :
  head_step_rel (InjL $ Val v) σ (Val $ InjLV v) σ
| InjRS v σ :
  head_step_rel (InjR $ Val v) σ (Val $ InjRV v) σ

(* Pure reductions
| BetaS f x e1 v2 e' σ :
  e' = subst x v2 (subst f (RecV f x e1) e1) →
  head_step_rel (App (Val $ RecV f x e1) (Val v2)) σ e' σ *)
| UnOpS op v v' σ :
  un_op_eval op v = Some v' →
  head_step_rel (UnOp op (Val v)) σ (Val v') σ
(*
| BinOpS op v1 v2 v' σ :
  bin_op_eval op v1 v2 = Some v' →
  head_step_rel (BinOp op (Val v1) (Val v2)) σ (Val v') σ *)
| IfTrueS e1 e2 σ :
  head_step_rel (If (Val $ LitV $ LitBool true) e1 e2) σ e1 σ
| IfFalseS e1 e2 σ :
  head_step_rel (If (Val $ LitV $ LitBool false) e1 e2) σ e2 σ
| FstS v1 v2 σ :
  head_step_rel (Fst (Val $ PairV v1 v2)) σ (Val v1) σ
| SndS v1 v2 σ :
  head_step_rel (Snd (Val $ PairV v1 v2)) σ (Val v2) σ
| CaseLS v e1 e2 σ :
  head_step_rel (Case (Val $ InjLV v) e1 e2) σ (App e1 (Val v)) σ
| CaseRS v e1 e2 σ :
  head_step_rel (Case (Val $ InjRV v) e1 e2) σ (App e2 (Val v)) σ

(* Heap
| AllocNS z N v σ l :
  l = fresh_loc (heap σ) →
  N = Z.to_nat z →
  (0 < N)%nat ->
  head_step_rel
    (AllocN (Val (LitV (LitInt z))) (Val v)) σ
    (Val $ LitV $ LitLoc l) (state_upd_heap_N l N v σ)
| LoadS l v σ :
  σ.(heap) !! l = Some v →
  head_step_rel (Load (Val $ LitV $ LitLoc l)) σ (of_val v) σ
| StoreS l v w σ :
  σ.(heap) !! l = Some v →
  head_step_rel (Store (Val $ LitV $ LitLoc l) (Val w)) σ
    (Val $ LitV LitUnit) (state_upd_heap <[l:=w]> σ)
*)
(* Rand *)
| RandNoTapeS z N (n_int : Z) (n_nat : nat) σ:
  N = Z.to_nat z →
  n_nat < N ->
  Z.of_nat n_nat = n_int ->
  head_step_rel (Rand (Val $ LitV $ LitInt z) (Val $ LitV LitUnit)) σ (Val $ LitV $ LitInt n_int) σ
(*
| AllocTapeS z N σ l :
  l = fresh_loc σ.(tapes) →
  N = Z.to_nat z →
  head_step_rel (AllocTape (Val (LitV (LitInt z)))) σ
    (Val $ LitV $ LitLbl l) (state_upd_tapes <[l := {| btape_tape := emptyTape ; btape_bound := N |}]> σ)
| RandTapeS l z N n b b' σ :
  N = Z.to_nat z →
  σ.(tapes) !! l = Some {| btape_tape := b ; btape_bound := N |} ->
  b !! 0 = Some (Z.to_nat n) ->
  b' = tapeAdvance b ->
  head_step_rel (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl l)))) σ
    (Val $ LitV $ LitInt $ n) (state_upd_tapes <[l := {| btape_tape := b' ; btape_bound := N|}]> σ)
| RandTapeEmptyS l z N (n_nat : nat) (n_int : Z) σ :
  N = Z.to_nat z →
  Z.of_nat n_nat = n_int ->
  n_nat < N ->
  σ.(tapes) !! l = Some {| btape_tape := emptyTape; btape_bound := N |} →
  head_step_rel (Rand (Val (LitV (LitInt z))) (Val $ LitV $ LitLbl l)) σ  (Val $ LitV $ LitInt $ n_int) σ
| RandTapeOtherS l z M N b (n_nat : nat) (n_int : Z) σ :
  N = Z.to_nat z →
  Z.of_nat n_nat = n_int ->
  n_nat < N ->
  σ.(tapes) !! l = Some {| btape_tape := b ; btape_bound := M |} →
  N ≠ M →
  head_step_rel (Rand (Val (LitV (LitInt z))) (Val $ LitV $ LitLbl l)) σ (Val $ LitV $ LitInt n_int) σ

(* Urand *)
| URandNoTapeS (r : R) σ :
  (0 <= r)%R ->
  (r <= 1)%R ->
  head_step_rel (URand (Val $ LitV LitUnit)) σ (Val $ LitV $ LitReal r) σ
| AllocUTapeS σ l :
  l = fresh_loc σ.(tapes) →
  head_step_rel AllocUTape σ
    (Val $ LitV $ LitLbl l) (state_upd_utapes <[l := emptyTape]> σ)
| URandTapeS l b b' r σ :
  σ.(utapes) !! l = Some b ->
  b !! 0 = Some r ->
  b' = tapeAdvance b ->
  head_step_rel (URand (Val (LitV (LitLbl l)))) σ
    (Val $ LitV $ LitReal $ r) (state_upd_utapes <[l := b]> σ)
| URandTapeEmptyS l (r : R) b σ :
  (0 <= r)%R ->
  (r <= 1)%R ->
  σ.(utapes) !! l = Some b →
  head_step_rel (URand (Val $ LitV $ LitLbl l)) σ (Val $ LitV $ LitReal r) σ
*)
(* Tick *)
| TickS σ z :
  head_step_rel (Tick $ Val $ LitV $ LitInt z) σ (Val $ LitV $ LitUnit) σ.

Create HintDb head_step.
Global Hint Constructors head_step_rel : head_step.
(* 0%fin always has non-zero mass, so propose this choice if the reduct is
   unconstrained. *)
Global Hint Extern 1
  (head_step_rel (Rand (Val (LitV _)) (Val (LitV LitUnit))) _ _ _) =>
         eapply (RandNoTapeS _ _ 0%fin) : head_step.
(*
Global Hint Extern 1
  (head_step_rel (Rand (Val (LitV _)) (Val (LitV (LitLbl _)))) _ _ _) =>
         eapply (RandTapeEmptyS _ _ _ 0%fin) : head_step.
Global Hint Extern 1
  (head_step_rel (Rand (Val (LitV _)) (Val (LitV (LitLbl _)))) _ _ _) =>
         eapply (RandTapeOtherS _ _ _ _ _ 0%fin) : head_step.
*)
(*
Ltac inv_head_step :=
  repeat
    match goal with
    | H : context [@bool_decide ?P ?dec] |- _ =>
        try (rewrite bool_decide_eq_true_2 in H; [|done]);
        try (rewrite bool_decide_eq_false_2 in H; [|done]);
        destruct_decide (@bool_decide_reflect P dec); simplify_eq
    | _ => progress simplify_map_eq; simpl in *; inv_distr; repeat case_match; inv_distr
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : is_Some (_ !! _) |- _ => destruct H
    end.

Lemma head_step_support_equiv_rel e1 e2 σ1 σ2 :
  head_step e1 σ1 (e2, σ2) > 0 ↔ head_step_rel e1 σ1 e2 σ2.
Proof.
  split.
  - intros ?. destruct e1; inv_head_step; eauto with head_step.
  - inversion 1; simplify_map_eq/=; try case_bool_decide; simplify_eq; solve_distr; done.
Qed.

Lemma state_step_support_equiv_rel σ1 α σ2 :
  state_step σ1 α σ2 > 0 ↔ state_step_rel σ1 α σ2.
Proof.
  rewrite /state_step. split.
  - case_bool_decide; [|intros; inv_distr].
    case_match. intros ?. inv_distr.
    econstructor; eauto with lia.
  - inversion_clear 1.
    rewrite bool_decide_eq_true_2 // H1. solve_distr.
Qed.

Lemma state_step_head_step_not_stuck e σ σ' α :
  state_step σ α σ' > 0 → (∃ ρ, head_step e σ ρ > 0) ↔ (∃ ρ', head_step e σ' ρ' > 0).
Proof.
  rewrite state_step_support_equiv_rel.
  inversion_clear 1.
  split; intros [[e2 σ2] Hs].
  (* TODO: the sub goals used to be solved by [simplify_map_eq]  *)
  - destruct e; inv_head_step; try by (unshelve (eexists; solve_distr)).
    + destruct (decide (α = l1)); simplify_eq.
      * rewrite lookup_insert in H11. done.
      * rewrite lookup_insert_ne // in H11. rewrite H11 in H7. done.
    + destruct (decide (α = l1)); simplify_eq.
      * rewrite lookup_insert in H11. done.
      * rewrite lookup_insert_ne // in H11. rewrite H11 in H7. done.
    + destruct (decide (α = l1)); simplify_eq.
      * rewrite lookup_insert in H10. done.
      * rewrite lookup_insert_ne // in H10. rewrite H10 in H7. done.
  - destruct e; inv_head_step; try by (unshelve (eexists; solve_distr)).
    + destruct (decide (α = l1)); simplify_eq.
      * apply not_elem_of_dom_2 in H11. done.
      * rewrite lookup_insert_ne // in H7. rewrite H11 in H7.  done.
    + destruct (decide (α = l1)); simplify_eq.
      * rewrite lookup_insert // in H7.
        apply not_elem_of_dom_2 in H11. done.
      * rewrite lookup_insert_ne // in H7. rewrite H11 in H7. done.
    + destruct (decide (α = l1)); simplify_eq.
      * rewrite lookup_insert // in H7.
        apply not_elem_of_dom_2 in H10. done.
      * rewrite lookup_insert_ne // in H7. rewrite H10 in H7. done.
Qed.

*)

Lemma head_step_mass e σ : ¬ is_zero (head_stepM (e, σ)) → is_prob (head_stepM (e, σ)).
Proof.
  assert (is_zero (T:=cfg) gZero) by done.
  rewrite /head_stepM; repeat case_match; try done.
Admitted.

(*
Lemma head_step_mass e σ :
  (∃ ρ, head_step e σ ρ > 0) → SeriesC (head_step e σ) = 1.
Proof.
  intros [[] Hs%head_step_support_equiv_rel].
  inversion Hs;
    repeat (simplify_map_eq/=; solve_distr_mass || case_match; try (case_bool_decide; done)).
Qed.
*)


Definition meas_lang_mixin :
  @MeasEctxiLanguageMixin _ _ _ _ expr val state ectx_item _ _ _ _
    of_val to_val fill_item decomp_item expr_ord head_stepM.
Proof.
  split.
  - by apply ValU_meas_fun.
  - by apply to_val_meas.
  - by apply fill_item_meas_fun.
  - by apply decomp_item_meas_fun.
  - by apply head_stepM_meas_fun.
  - by apply expr_meas_singleton.
  - by apply val_meas_singleton.
  - by apply state_meas_singleton.
  - by apply to_of_val.
  - by apply of_to_val.
  - by apply val_head_stuck.
  - by apply head_step_mass.
  - by apply fill_item_some.
  - by apply fill_item_inj.
  - by apply fill_item_no_val_inj.
  - by apply expr_ord_wf.
  - by apply decomp_expr_ord.
  - by apply decomp_fill_item.
  - by apply decomp_fill_item_2.
  - by apply head_step_ctx_val.
Qed.

End meas_lang.

(** Language *)

Canonical Structure meas_ectxi_lang := MeasEctxiLanguage _ _ _ _ meas_lang.head_stepM meas_lang.meas_lang_mixin.
Canonical Structure meas_ectx_lang := MeasEctxLanguageOfEctxi meas_ectxi_lang.
Canonical Structure meas_lang := MeasLanguageOfEctx meas_ectx_lang.

(* Prefer meas_lang names over ectx_language names. *)
Export meas_lang.
