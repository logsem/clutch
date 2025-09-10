(* TODO cleanup imports *)
Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From stdpp Require Import base gmap. (* numbers binders strings gmap. **)
From mathcomp Require Import functions.
From mathcomp.analysis Require Import measure lebesgue_measure probability.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp fintype.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export base stdpp_ext.
From clutch.common Require Export locations.
From Coq Require Export Reals.
From clutch.prob.monad Require Export giry meas_markov.
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

Require Import mathcomp.reals_stdlib.Rstruct.
Require Import mathcomp.reals.reals.
Set Warnings "hiding-delimiting-key".
Set Warnings "+spurious-ssr-injection".

Local Open Scope classical_set_scope.

Section meas_semantics.

Notation cfg := (toPackedType expr_cyl.-sigma expr * toPackedType state_display state)%type.

(* TODO: Make this as close to the old definition in Clutch as possible.
    - What stdpp isntances do we need for the new tapes?*)
Definition head_step (c : cfg) : giryM cfg :=
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
                  (** Rewritten to match that in head_step' *)
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
              (** Rewritten to match head_step' more *)
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

Definition head_step_rec : cfg -> giryM cfg :=
  gRet \o (ValU \o RecVU \o 𝜋_RecU \o fst △ snd).

Definition head_step_pair : cfg -> giryM cfg :=
  gRet \o (ValU \o PairVU \o (𝜋_ValU \o 𝜋_Pair_l \o fst △ 𝜋_ValU \o 𝜋_Pair_r \o fst) △ snd).

Definition head_step_injL : cfg -> giryM cfg :=
  gRet \o (ValU \o InjLVU \o 𝜋_ValU \o 𝜋_InjLU \o fst △ snd).

Definition head_step_injR : cfg -> giryM cfg :=
  gRet \o (ValU \o InjRVU \o 𝜋_ValU \o 𝜋_InjRU \o fst △ snd).

Definition head_step_app : cfg -> giryM cfg :=
  let 𝜋_f  := 𝜋_RecV_f \o 𝜋_ValU \o 𝜋_App_l \o fst in
  let 𝜋_x  := 𝜋_RecV_x \o 𝜋_ValU \o 𝜋_App_l \o fst in
  let 𝜋_e1 := 𝜋_RecV_e \o 𝜋_ValU \o 𝜋_App_l \o fst in
  let 𝜋_v2 := 𝜋_ValU \o 𝜋_App_r \o fst in
  gRet \o (substU' \o (𝜋_x △ (𝜋_v2 △ substU' \o (𝜋_f △ (RecVU \o (𝜋_f △ 𝜋_x △ 𝜋_e1) △ 𝜋_e1)))) △ snd).

(*
Definition head_step_app' : cfg -> giryM cfg :=
  gRet \o (substU' \o (   𝜋_RecV_f \o 𝜋_ValU \o 𝜋_App_l \o fst
                      △ (𝜋_ValU \o 𝜋_App_r \o fst
                      △ substU' \o (  𝜋_RecV_f \o 𝜋_ValU \o 𝜋_App_l \o fst
                                    △ (RecVU \o (  𝜋_RecV_f \o 𝜋_ValU \o 𝜋_App_l \o fst
                                                 △ 𝜋_RecV_x \o 𝜋_ValU \o 𝜋_App_l \o fst
                                                 △ 𝜋_RecV_e \o 𝜋_ValU \o 𝜋_App_l \o fst )
                                    △ 𝜋_RecV_e \o 𝜋_ValU \o 𝜋_App_l \o fst ))))
           △ snd).
*)


Definition head_step_unop : cfg -> giryM cfg :=
  un_op_eval'' \o (𝜋_UnOp_op \o fst △ 𝜋_Val_v \o 𝜋_UnOp_e \o fst △ snd).

Definition head_step_binop : cfg -> giryM cfg :=
  bin_op_eval''' \o (𝜋_BinOp_op \o fst △ 𝜋_Val_v \o 𝜋_BinOp_l \o fst △ 𝜋_Val_v \o 𝜋_BinOp_r \o fst △ snd).

Definition head_step_alloc : cfg -> giryM cfg :=
  alloc_eval \o (𝜋_ValU \o 𝜋_AllocU \o fst △ snd).

Definition head_step_load : cfg -> giryM cfg :=
  load_eval \o (𝜋_LitLoc_l \o 𝜋_LitVU \o 𝜋_ValU \o 𝜋_Load_e \o fst △ snd).

Program Definition head_step_store : cfg -> giryM cfg :=
  let 𝜋_l := 𝜋_LitLoc_l \o 𝜋_LitVU \o 𝜋_ValU \o 𝜋_Store_l \o fst in
  let 𝜋_v := 𝜋_ValU \o 𝜋_Store_e \o fst in
  store_eval \o (𝜋_l △ 𝜋_v △ snd).

Definition head_step_ifT : cfg -> giryM cfg :=
  gRet \o (𝜋_If_l \o fst △ snd).

Program Definition head_step_ifF : cfg -> giryM cfg :=
  gRet \o (𝜋_If_r \o fst △ snd).

Definition head_step_fst : cfg -> giryM cfg :=
  gRet \o (ValU \o 𝜋_PairV_l \o 𝜋_ValU \o 𝜋_FstU \o fst △ snd).

Definition head_step_snd : cfg -> giryM cfg :=
  gRet \o (ValU \o 𝜋_PairV_r \o 𝜋_ValU \o 𝜋_SndU \o fst △ snd).

Definition head_step_caseL : cfg -> giryM cfg :=
  gRet \o (AppU \o (𝜋_Case_l \o fst △ ValU \o 𝜋_InjLVU \o 𝜋_ValU \o 𝜋_Case_c \o fst) △ snd).

Definition head_step_caseR : cfg -> giryM cfg :=
  gRet \o (AppU \o (𝜋_Case_r \o fst △ ValU \o 𝜋_InjRVU \o 𝜋_ValU \o 𝜋_Case_c \o fst) △ snd).

Definition head_step_allocTape : cfg -> giryM cfg :=
  AllocTape_eval \o (𝜋_LitIntU \o 𝜋_LitVU \o 𝜋_ValU \o 𝜋_AllocTapeU \o fst △ snd).

Definition head_step_allocUTape : cfg -> giryM cfg :=
  AllocUTape_eval \o snd.

Definition head_step_rand : cfg -> giryM cfg :=
  Rand_eval \o (𝜋_LitIntU \o 𝜋_LitVU \o 𝜋_ValU \o 𝜋_Rand_N \o fst △ snd).

Definition head_step_urand : cfg -> giryM cfg :=
  (URand_eval \o snd).

Definition head_step_randT : cfg -> giryM cfg :=
  let 𝜋_N := 𝜋_LitIntU \o 𝜋_LitVU \o 𝜋_ValU \o 𝜋_Rand_N \o fst in
  let 𝜋_l := 𝜋_LitLblU \o 𝜋_LitVU \o 𝜋_ValU \o 𝜋_Rand_t \o fst in
  RandT_eval \o ((𝜋_N △ 𝜋_l) △ snd).

Definition head_step_urandT : cfg -> giryM cfg :=
  URandT_eval \o (𝜋_LitLblU \o 𝜋_LitVU \o 𝜋_ValU \o 𝜋_URand_e \o fst  △ snd).

Definition head_step_tick : cfg -> giryM cfg :=
  gRet \o (cst (ValU $ LitVU $ LitUnitU) △ snd).

Ltac mf_restrictT :=
  match goal with
  | |- (measurable_fun _ _) => apply mathcomp_measurable_fun_restiction_setT; [ try by ms_solve | ]
  end.


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

Lemma head_step_rec_meas_fun : measurable_fun cover_rec head_step_rec.
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

Lemma head_step_pair_meas_fun : measurable_fun cover_pair head_step_pair.
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

Lemma head_step_injL_meas_fun       : measurable_fun cover_injL       head_step_injL.
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

Lemma head_step_injR_meas_fun       : measurable_fun cover_injR       head_step_injR.
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

Lemma head_step_app_meas_fun        : measurable_fun cover_app        head_step_app.
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

Lemma head_step_unop_meas_fun       : measurable_fun cover_unop       head_step_unop.
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

Lemma head_step_binop_meas_fun      : measurable_fun cover_binop      head_step_binop.
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

Lemma head_step_alloc_meas_fun      : measurable_fun cover_alloc      head_step_alloc.
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

Lemma head_step_load_meas_fun       : measurable_fun cover_load       head_step_load.
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

Lemma head_step_store_meas_fun      : measurable_fun cover_store      head_step_store.
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

Lemma head_step_ifT_meas_fun        : measurable_fun cover_ifT        head_step_ifT.
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

Lemma head_step_ifF_meas_fun        : measurable_fun cover_ifF        head_step_ifF.
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

Lemma head_step_fst_meas_fun        : measurable_fun cover_fst        head_step_fst.
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

Lemma head_step_snd_meas_fun        : measurable_fun cover_snd        head_step_snd.
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

Lemma head_step_caseL_meas_fun      : measurable_fun cover_caseL      head_step_caseL.
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

Lemma head_step_caseR_meas_fun      : measurable_fun cover_caseR      head_step_caseR.
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

Lemma head_step_allocTape_meas_fun  : measurable_fun cover_allocTape  head_step_allocTape.
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

Lemma head_step_allocUTape_meas_fun : measurable_fun cover_allocUTape head_step_allocUTape.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  simpl.
  assert (([set: expr_T * state] `&` fst @^-1` ecov_allocutape) = ecov_allocutape `*` [set:state]).
  { rewrite eqEsubset; split; subset_solver . }
  eapply @measurable_snd_restriction; ms_solve.
Qed.

Lemma head_step_rand_meas_fun       : measurable_fun cover_rand       head_step_rand.
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

Lemma head_step_urand_meas_fun      : measurable_fun cover_urand      head_step_urand.
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

Lemma head_step_randT_meas_fun      : measurable_fun cover_randT      head_step_randT.
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

Lemma head_step_urandT_meas_fun     : measurable_fun cover_urandT     head_step_urandT.
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

Lemma head_step_tick_meas_fun       : measurable_fun cover_tick       head_step_tick.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree; first by mf_done.
  mf_prod.
  mf_restrictT. by ms_solve.
Qed.

Hint Resolve head_step_rec_meas_fun        : mf_fun.
Hint Resolve head_step_pair_meas_fun       : mf_fun.
Hint Resolve head_step_injL_meas_fun       : mf_fun.
Hint Resolve head_step_injR_meas_fun       : mf_fun.
Hint Resolve head_step_app_meas_fun        : mf_fun.
Hint Resolve head_step_unop_meas_fun       : mf_fun.
Hint Resolve head_step_binop_meas_fun      : mf_fun.
Hint Resolve head_step_alloc_meas_fun      : mf_fun.
Hint Resolve head_step_load_meas_fun       : mf_fun.
Hint Resolve head_step_store_meas_fun      : mf_fun.
Hint Resolve head_step_ifT_meas_fun        : mf_fun.
Hint Resolve head_step_ifF_meas_fun        : mf_fun.
Hint Resolve head_step_fst_meas_fun        : mf_fun.
Hint Resolve head_step_snd_meas_fun        : mf_fun.
Hint Resolve head_step_caseL_meas_fun      : mf_fun.
Hint Resolve head_step_caseR_meas_fun      : mf_fun.
Hint Resolve head_step_allocTape_meas_fun  : mf_fun.
Hint Resolve head_step_allocUTape_meas_fun : mf_fun.
Hint Resolve head_step_rand_meas_fun       : mf_fun.
Hint Resolve head_step_urand_meas_fun      : mf_fun.
Hint Resolve head_step_randT_meas_fun      : mf_fun.
Hint Resolve head_step_urandT_meas_fun     : mf_fun.
Hint Resolve head_step_tick_meas_fun       : mf_fun.


Definition head_step' : cfg -> giryM cfg :=
  if_in cover_rec        head_step_rec        $
  if_in cover_pair       head_step_pair       $
  if_in cover_injL       head_step_injL       $
  if_in cover_injR       head_step_injR       $
  if_in cover_app        head_step_app        $
  if_in cover_unop       head_step_unop       $
  if_in cover_binop      head_step_binop      $
  if_in cover_alloc      head_step_alloc      $
  if_in cover_load       head_step_load       $
  if_in cover_store      head_step_store      $
  if_in cover_ifT        head_step_ifT        $
  if_in cover_ifF        head_step_ifF        $
  if_in cover_fst        head_step_fst        $
  if_in cover_snd        head_step_snd        $
  if_in cover_caseL      head_step_caseL      $
  if_in cover_caseR      head_step_caseR      $
  if_in cover_allocTape  head_step_allocTape  $
  if_in cover_allocUTape head_step_allocUTape $
  if_in cover_rand       head_step_rand       $
  if_in cover_urand      head_step_urand      $
  if_in cover_randT      head_step_randT      $
  if_in cover_urandT     head_step_urandT     $
  if_in cover_tick       head_step_tick       $
  cst gZero.

(** Slow proof, but can just uncomment *)
Lemma head_step'_meas_fun : measurable_fun setT head_step'.
Proof. Admitted.
(*
Proof. 
  rewrite /head_step'. 
  (eapply @if_in_meas_fun; [ms_done|ms_solve|rewrite setIidl; [eauto with mf_fun|subset_solver]| 
                             rewrite setIidl; last subset_solver 
  ]). 
  repeat( eapply @if_in_meas_fun; [ms_done|ms_solve|apply @measurable_fun_setI1; [ms_solve|ms_solve|eauto with mf_fun]|]). 
  (* computer goes brrr... *) 
  ms_solve. 
Qed.
*)


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

Lemma head_step_head_step'_eq : head_step = head_step'.
Proof. Admitted.
(*
  apply functional_extensionality_dep.
  intros [e σ].
  rewrite /head_step/head_step'.
  repeat unfold_if_in.
  destruct!/=.
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H1].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H2].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H3].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H4].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H5].
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H6].
  { rewrite /head_step_unop/=/un_op_eval''. clear.
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
  { rewrite /head_step_binop/=/bin_op_eval'''. clear.
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
  { unfold_RHS. simpl. unfold_RHS. rewrite /alloc_eval_cov_ok.
    rewrite ifIn_eq_left; last done.
    by rewrite /alloc_eval_ok/=. }
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H9].
  { unfold_RHS. simpl. unfold_RHS.
    apply if_in_split.
    - rewrite /load_eval_cov_ok/=.
      rewrite /hp_eval/lookup.
      intros [a Ha]; rewrite Ha.
      destruct σ as [[[]]].
      rewrite /load_eval_ok/=/hp_evalC/hp_eval/=/uncurry/=/of_option/=/heap/=.
      rewrite /heap/= in Ha. by rewrite Ha/=.
    - case_match eqn:H; last done.
      intros H'. exfalso.
      apply H'. rewrite /load_eval_cov_ok/=/hp_eval. setoid_rewrite H. eexists _. naive_solver.
  }
  apply (if_in_split (f2 := if_in _ _ _)); [intros; destruct!/=; try by unfold_RHS|intros H10].
  { unfold_RHS. simpl. unfold_RHS.
    apply if_in_split.
    - rewrite /store_eval_cov_ok/=/state_heap_alloc_at/=.
      rewrite /hp_eval/lookup.
      intros [a Ha]. by rewrite Ha.
    - case_match eqn:H; last done.
      intros H'. exfalso.
      apply H'.
      rewrite /store_eval_cov_ok/=/state_heap_alloc_at/=/hp_eval/lookup. setoid_rewrite H.
      by eexists _. }
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
      by rewrite /lookup H.
    }
    intros H1.
    case_match; last first.
    { exfalso. apply H1. repeat eexists _; last done; done. }
    case_match.
    subst.
    apply if_in_split.
    { intros [??[? [[x' H'] H''] ?]].
      simplify_eq.
      unfold lookup, hp_eval in *. simpl in *.
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
  apply (if_in_split (f1 := (head_step_tick))); [intros; destruct!/=; try by unfold_RHS|intros H23].
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
Qed.  *)

Lemma head_step_meas_fun : measurable_fun setT head_step.
Proof.
  rewrite head_step_head_step'_eq.
  apply head_step'_meas_fun.
Qed.


(** Basic properties about the language *)
Global Instance fill_item_inj Ki : Inj eq eq (curry fill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item (Ki, e))) → is_Some (to_val e).
Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.

Lemma val_head_stuck e1 σ1 : ¬ is_zero (head_step (e1, σ1)) → to_val e1 = None.
Proof. destruct e1; try done.
       intros H. exfalso. apply H.
       done.
Qed. 

Lemma head_step_ctx_val Ki e σ1 : ¬ is_zero (head_step (fill_item (Ki, e), σ1)) → is_Some (to_val e).
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

Lemma head_step_mass e σ : ¬ is_zero (head_step (e, σ)) → is_prob (head_step (e, σ)).
Proof.
(*   assert (is_zero (T:=cfg) gZero) by done.
  rewrite /head_step; repeat case_match; try done. *)
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

Notation ectx := (list (ectx_item)).

Definition fill (K : (ectx * expr)%type) : expr :=
  foldl (fun e' k => fill_item (k, e')) (snd K) (fst K).

Lemma fill_measurable : measurable_fun setT fill.
Proof with ms_solve; apply list_length_cov_meas_set.
  rewrite /fill.
  assert (setT (T:=ectx* _) = \bigcup_n  (list_length_cov n `*` setT)) as ->.
  { rewrite eqEsubset; split; intros [l s]; simpl; last done.
    intros _.
    exists (length l); first done.
    simpl. split; last done. apply: list_length_cov_length'.
  }
  apply measurable_fun_bigcup.
  { intros. ms_solve. apply list_length_cov_meas_set. }
  intros n; induction n as [|n IHn].
  { simpl. apply: (mathcomp_measurable_fun_ext _ _ (snd)).
    - ms_solve. apply list_length_cov_meas_set.
    - apply: measurable_snd_restriction.
      ms_solve. apply list_length_cov_meas_set.
    - rewrite list_length_cov_0/list_cov_empty. intros []. simpl. by intros [->].
  }
  apply: (mathcomp_measurable_fun_ext _ _ ((λ K : list (ectx_item) * expr,
                                              foldl (λ e' (k : ectx_item), fill_item (k, e')) K.2 K.1) \o (𝜋_cons_vs \o fst △ (fill_item \o (𝜋_cons_v \o fst △ snd))))).
  - ms_solve. apply list_length_cov_meas_set.
  - apply: measurable_comp; [| |apply:IHn |].
    + ms_solve. apply list_length_cov_meas_set.
    + rewrite list_length_cov_Sn. intros [l s]. rewrite /list_cov_cons.
      simpl.
      intros [[][[[?[]]]]]; simpl in *; subst; simpl in *; simplify_eq. naive_solver.
    + mf_prod.
      * ms_solve. apply list_length_cov_meas_set.
      * apply: measurable_comp; [| |apply:𝜋_cons_vs_meas_fun|].
        -- apply list_cov_cons_meas_set.
        -- rewrite list_length_cov_Sn. intros ?. simpl. intros [?[[]]]; by subst.
        -- apply: measurable_fst_restriction. idtac...
      * apply: measurable_compT.
        -- ms_solve. apply list_length_cov_meas_set.
        -- admit. (* apply fill_item_meas. *)
        -- mf_prod; last apply: measurable_snd_restriction.
           ++ idtac...
           ++ apply:  measurable_comp; last apply: measurable_fst_restriction; last first.
              ** idtac...
              ** apply 𝜋_cons_v_meas_fun.
              ** rewrite list_length_cov_Sn. intros ?. simpl.
                 intros [[][[]]]; by subst.
              ** apply list_cov_cons_meas_set.
           ++ idtac...
  - rewrite list_length_cov_Sn. intros []. simpl. rewrite /list_cov_cons/=.
    intros [[[?[]]]]; by subst.
Admitted.
Hint Resolve fill_measurable : measlang.

Lemma fill_app (K1 K2 : ectx) e : fill ((K1 ++ K2), e) = fill (K2, (fill (K1, e))).
Proof. apply foldl_app. Qed.

Lemma fill_cons (k : ectx_item) (K2 : ectx) e : fill ((k :: K2), e) = fill (K2, (fill ([k], e))).
Proof. apply (fill_app [k] K2). Qed.

Lemma fill_not_val K e : to_val e = None → to_val (fill (K, e)) = None.
Proof.
  revert e.
  induction K as [|Ki K] using rev_ind; simpl; first naive_solver.
  intros e Hval; rewrite fill_app/=.
  admit.
  (* apply fill_item_not_val. naive_solver. *)
Admitted.

Program Fixpoint decomp (e : expr) {wf expr_ord e} : ectx * expr :=
  match decomp_item e with
  | Some (Ki, e') => let '(K, e'') := decomp e' in (K ++ [Ki], e'')
  | None => ([], e)
  end.
Solve Obligations with eauto using decomp_ord, expr_ord_wf.
Next Obligation. Admitted.
Next Obligation. Admitted.

Lemma decomp_unfold e :
  decomp e =
    match decomp_item e with
    | Some (Ki, e') => let '(K, e'') := decomp e' in (K ++ [Ki], e'')
    | None => ([], e)
    end.
Proof. Admitted.
(*
  rewrite /decomp WfExtensionality.fix_sub_eq_ext /= -/decomp.
  repeat case_match; try done.
Qed. *)

Lemma decomp_inv_nil e e' :
  decomp e = ([], e') → decomp_item e = None ∧ e = e'.
Proof.
  rewrite decomp_unfold.
  destruct (decomp_item e) as [[Ki e'']|] eqn:Heq; [|by intros [=]].
  destruct (decomp e''). intros [= Hl He].
  assert (l = []) as ->.
  { destruct l; inversion Hl. }
  inversion Hl.
Qed.

(* TODO: move *)
Lemma list_snoc_singleton_inv {A} (l1 l2 : list A) (a1 a2 : A) :
  l1 ++ [a1] = l2 ++ [a2] → l1 = l2 ∧ a1 = a2.
Proof.
  revert l2. induction l1 as [|a l1].
  { intros [| ? []] [=]=>//. }
  intros [].
  { intros [=]; destruct l1; simplify_eq. }
  { intros [= -> []%IHl1]. simplify_eq=>//. }
Qed.

Lemma decomp_inv_cons Ki K e e'' :
  decomp e = (K ++ [Ki], e'') → ∃ e', decomp_item e = Some (Ki, e') ∧ decomp e' = (K, e'').
Proof.
  rewrite decomp_unfold.
  destruct (decomp_item e) as [[Ki' e']|] eqn:Heq'.
  2 : { intros [=]. by destruct K. }
  destruct (decomp e') as [K' e'''] eqn:Heq.
  intros [= [<- <-]%list_snoc_singleton_inv ->].
  eauto.
Qed.

Lemma decomp_fill K e e' : decomp e = (K, e') → fill (K, e') = e.
Proof.
  remember (length K) as n eqn:Heqn.
  revert K e e' Heqn.
  induction n as [|n IHn]; intros K e e' Hn.
  - assert (K= []) as ->.
    { destruct K; simpl in *; first done. lia. }
    intros H. apply decomp_inv_nil in H as [? ->].
    by rewrite /fill.
  - rewrite decomp_unfold.
    case_match; last first.
    { intros; simplify_eq. }
    repeat case_match. simplify_eq.
    intros; simplify_eq.
    rewrite fill_app. apply decomp_fill_item_2.
    etrans; first exact.
    f_equal. f_equal.
    simpl. symmetry. apply IHn; last done.
    rewrite app_length in Hn. simpl in *. lia.
Qed.

Lemma decomp_to_val_emp K e e' : decomp e = (K, e') → is_Some (to_val e') → K = [].
Proof.
  revert e e'. induction K as [|Ki K] using rev_ind; [done|].
  intros ?? (e'' & Hrei & Hre)%decomp_inv_cons Hv.
  specialize (IHK _ _ Hre Hv). simplify_eq.
  apply decomp_inv_nil in Hre as [? ?]; simplify_eq.
  by apply decomp_fill_item_2 in Hrei as [_ ?%eq_None_not_Some].
Qed.

Lemma decomp_fill_comp e e' K K' :  to_val e = None → decomp e = (K', e') → decomp (fill (K, e)) = (flip app K K', e').
Proof.
  revert K' e e'.
  induction K as [|Ki K] using rev_ind.
  { intros ??? =>/=. rewrite app_nil_r //. }
  intros K' e e' Hval Hre. rewrite fill_app /=.
  rewrite decomp_unfold.
  rewrite decomp_fill_item.
  - rewrite (IHK K' _ e') //=.
    rewrite !app_assoc //.
  - simpl. by apply fill_not_val.
Qed.


(*
Lemma decomp_step_by_val K' K_redex e1' e1_redex σ1  :
  fill (K', e1') = fill (K_redex, e1_redex)
  → to_val e1' = None
    → ¬ is_zero (head_step (e1_redex, σ1))
      → ∃ K'' , K_redex = flip app K' K''.
Proof.
  revert K_redex  e1' e1_redex σ1.
  induction K' as [|Ki K IH] using rev_ind => /= K' e1' e1_redex σ1 Hfill; eauto using app_nil_r.
  destruct K' as [|Ki' K' _] using @rev_ind; first rewrite {2}/fill/= in Hfill; simplify_eq/=.
  { intros Hval Hstep. rewrite fill_app in Hstep. apply head_ctx_step_val in Hstep.
    simpl in Hstep.
    eapply fill_not_val in Hval.
    by apply not_eq_None_Some in Hstep. }
  rewrite !fill_app /= in Hfill.
  intros Hval Hstep.
  assert (Ki = Ki') as ->.
  { eapply fill_item_no_val_inj, Hfill; simpl; first by apply fill_not_val.
    apply fill_not_val. by eapply ectxi_language_mixin. }
  simplify_eq. apply fill_item_inj in Hfill. simpl in *.
  eapply IH in Hfill as [K'' ->]; [|done..].
  exists K''. by rewrite assoc.
Qed.
*)

Fixpoint decomp' n (e : expr) :=
  match n with
  | 0 => match decomp_item e with
        | Some _ => None
        | None => Some ([], e)
        end
  | S n' => match decomp_item e with
          | None => None
          | Some (Ki, e') =>
              match decomp' n' e' with
              | Some (K, e'') => Some (K++[Ki], e'')
              | None => None
              end
           end
  end.

Lemma decomp_decomp' n e K e': decomp' n e = Some (K, e') -> decomp e = (K, e').
Proof.
  revert e K e'.
  induction n; simpl.
  - intros. case_match; first done.
    simplify_eq. rewrite decomp_unfold. by case_match.
  - intros. case_match eqn:Hx; last done.
    case_match. subst. case_match eqn:Hy; last done.
    case_match. subst. apply IHn in Hy.
    simplify_eq. rewrite decomp_unfold. by rewrite Hx Hy.
Qed.

Lemma decomp_decomp2' e : decomp' (length (decomp e).1) e = Some (decomp e).
Proof.
  remember (length (decomp e).1) as n eqn:Heqn.
  revert e Heqn.
  induction n; simpl.
  - intros ? Hlength.
    destruct (decomp e) as [l ?] eqn:Heqn.
    assert (l=[]) as ->.
    { by apply nil_length_inv. }
    apply decomp_inv_nil in Heqn as [H ?]. subst. by rewrite H.
  - intros e Hlength.
    case_match eqn:H; last first.
    { rewrite decomp_unfold in Hlength. rewrite H in Hlength.
      simplify_eq.
    }
    case_match.
    subst.
    rewrite decomp_unfold in Hlength. rewrite H in Hlength.
    case_match eqn:H'.
    simpl in *.
    rewrite app_length in Hlength. simpl in *.
    assert (length l = n) by lia.
    subst. erewrite IHn; last by rewrite H'.
    rewrite H'. by rewrite decomp_unfold H H'.
Qed.

  Definition decomp'_meas_set n: measurable (decomp' n @^-1` option_cov_Some).
  Proof.
    induction n.
    - assert (preimage (decomp' 0) option_cov_Some = preimage decomp_item option_cov_None) as ->.
        * rewrite eqEsubset; split; intros ?; simpl; rewrite /option_cov_Some/option_cov_None/=.
          -- intros []. by case_match.
          -- intros ->. naive_solver.
        * rewrite <-setTI.
          admit.
          (*
          apply: decomp_item_meas; ms_solve.
          apply: option_cov_None_meas_set. *)
    - assert (preimage (decomp' (S n)) option_cov_Some =
                (preimage decomp_item (option_cov_Some`&`
                  (preimage (snd \o 𝜋_Some_v) (preimage (decomp' n) option_cov_Some))))
               ) as ->.
        { rewrite eqEsubset; split; intros ?; simpl; rewrite /option_cov_Some/=.
          - intros []. case_match eqn:H1; last done.
            case_match. case_match eqn:H2; last done. case_match.
            subst. simplify_eq. naive_solver.
          - intros [[[] H][[]H']]. rewrite H in H'. simpl in *.
            rewrite H H'. naive_solver.
        }
        rewrite <-setTI.

        (* apply decomp_item_meas; ms_solve; try apply option_cov_Some_meas_set.
        apply: measurable_comp; last first.
        * apply: 𝜋_Some_v_meas_fun.
        * apply measurable_snd_restriction.
          apply: measurableT.
        * done.
        * done.
  Qed. *) Admitted.
  Hint Resolve decomp'_meas_set : measlang.

  (* How to prove this? *)
  Lemma decomp_measurable : measurable_fun setT decomp.
  Proof.
    assert (setT = \bigcup_i (preimage (decomp' i) option_cov_Some)) as Hrewrite; last rewrite Hrewrite.
    { rewrite eqEsubset; split; intros t; simpl; last done.
      intros _.
      exists (length (decomp t).1); first done.
      simpl. rewrite decomp_decomp2'. by eexists _.
    }
    rewrite measurable_fun_bigcup; last first.
    - intros n. apply decomp'_meas_set.
    - intros n.
      induction n as [|n' IHn].
      + assert ((decomp' 0 @^-1` option_cov_Some) =
                setT `&` (decomp_item  @^-1` (option_cov_None))) as ->.
        { rewrite eqEsubset; split; intros ?; rewrite /option_cov_Some/option_cov_None/=.
          - intros [[]]. case_match; by simplify_eq.
          - intros [_ ->]. naive_solver.
        }
        apply: (mathcomp_measurable_fun_ext _ _ (cst []△(λ x,x))).
        * admit. (* apply decomp_item_meas; first done. apply option_cov_None_meas_set. *)
        * mf_prod. ms_solve; last apply option_cov_None_meas_set.
          admit.
          (* apply decomp_item_meas. *)
        * rewrite /option_cov_None/=. intros ?[? H]. by rewrite decomp_unfold H.
      + assert ((decomp' (S n') @^-1` option_cov_Some) =
                preimage decomp_item (option_cov_Some `&` preimage 𝜋_Some_v (setT `*` (decomp' (n') @^-1` option_cov_Some)))) as ->.
        { rewrite eqEsubset; split; intros ?; rewrite /option_cov_Some/=.
          - intros [[]].
            repeat case_match; simplify_eq.
            repeat split; [naive_solver..|].
            simpl. naive_solver.
          - intros [[[]H][?[[]H']]].
            rewrite H in H'. simpl in *. rewrite H H'. naive_solver.
        }
        apply: (mathcomp_measurable_fun_ext _ _
                  ((appU\o fst △ snd)
                    \o ((fst \o snd △ consU \o fst)△snd \o snd)
                     \o ((fst△ cst []) △decomp \o snd)
                     \o (𝜋_Some_v \o decomp_item))).
        { rewrite <-setTI.
          admit.
          (*
          apply: decomp_item_meas; first done.
          apply 𝜋_Some_v_meas_fun; first apply option_cov_Some_meas_set.
          apply measurableX; first done.
          apply decomp'_meas_set. *)
        }
        { apply: (measurable_comp (F:=setT `*` (decomp' n' @^-1` option_cov_Some))).
          - ms_solve. apply decomp'_meas_set.
          - intros []. rewrite /option_cov_Some/=.
            intros [?[[[] H][_ [[] H' ]  ]] H''].
            rewrite H in H' H''.  simpl in *. simplify_eq. rewrite H'.
            naive_solver.
          - mf_cmp_tree.
            + mf_cmp_tree; repeat mf_prod; repeat mf_cmp_tree.
              * apply app_meas_fun.
              * apply: measurable_fst.
              * apply cons_meas_fun.
              * apply: measurable_snd.
            + mf_prod; first (ms_solve; apply decomp'_meas_set).
              * mf_prod; first (ms_solve; apply decomp'_meas_set).
                apply: measurable_fst_restriction. ms_solve. apply decomp'_meas_set.
              * apply snd_setX_meas_fun; first done; first apply decomp'_meas_set.
                done.
          - rewrite <-(setTI (preimage _ _)).
            mf_cmp_tree.
            + ms_solve; [apply 𝜋_Some_v_meas_fun|apply option_cov_Some_meas_set|apply decomp'_meas_set].
            + intros ?. rewrite /option_cov_Some/=.
              intros [?[?[[[]H][?[[]H']]]]H''].
              rewrite H in H' H''. subst. simpl in *.
              naive_solver.
            + apply: measurable_funS; last apply: 𝜋_Some_v_meas_fun.
              * apply option_cov_Some_meas_set.
              * apply subIsetl.
            + ms_solve.
              * admit. (* apply: decomp_item_meas. *)
              * apply 𝜋_Some_v_meas_fun.
              * apply option_cov_Some_meas_set.
              * apply decomp'_meas_set.
            + admit. (* apply decomp_item_meas. *) }
        rewrite /option_cov_Some/=.
        intros ? [[[]H][?[[]H']]].
        rewrite H in H'. simpl in *.
        rewrite H/=. rewrite (decomp_unfold x). rewrite H.
        by erewrite decomp_decomp'.
  Admitted.
  Hint Resolve decomp_measurable : measlang.

  (*
  Lemma head_ctx_step_fill_val K e σ1 : ¬ is_zero (head_step (fill (K, e), σ1)) → is_Some (to_val e) ∨ K = [].
  Proof.
    destruct K as [|Ki K _] using rev_ind; simpl; first by auto.
    rewrite fill_app /=.
    intros H%head_ctx_step_val; eauto using fill_val. simpl in *.
    left.
    destruct (to_val e) eqn:Heqn; first done.
    eapply fill_not_val in Heqn. by erewrite Heqn in H.
  Qed.
  *)

  Lemma fill_val : ∀ K e, is_Some (to_val (curry fill K e)) → is_Some (to_val e).
  Proof. intros K. induction K as [|Ki K IH]=> e //=. Admitted. (* by intros ?%IH%fill_item_val. Qed. *)

  Lemma fill_not_val_idk : ∀ K e, to_val e = None → to_val (curry fill K e) = None.
Proof. intros K e. rewrite !eq_None_not_Some. eauto. Admitted.

(* These are more ectxi_langauge lemmas

    { intros K1 K2 e. by rewrite /fill /= foldl_app. }
    { intros K.
      induction K as [|Ki K IH]; rewrite /Inj.
      { done. }
      { move=> x y.
        unfold curry.
        rewrite fill_cons.
        unfold curry in IH.
        move=> H.
        apply IH in H.
        rewrite /fill//= in H.
        have H' := fill_item_inj Ki x y.
        apply H'.
        by rewrite /curry. }
    }

 *)

(*
  Lemma ectxi_language_sub_redexes_are_values e :
    (∀ Ki e', e = fill_item (Ki, e') → is_Some (to_val e')) →
    sub_redexes_are_values e.
  Proof.
    intros Hsub K e' ->. destruct K as [|Ki K _] using @rev_ind=> //=.
    intros []%eq_None_not_Some.
    simpl in *.
    eapply (fill_val (Λ := meas_ectxi_lang_ectx)), Hsub.
    by rewrite /= fill_app.
  Qed.
*)

  Definition curry_fill_item := curry (fill_item).

  (*
  Global Instance ectxi_lang_ctx_item Ki : MeasLanguageCtx (Λ := meas_ectxi_lang)(curry_fill_item Ki).
  Proof. change (MeasLanguageCtx (Λ := meas_ectxi_lang) (curry fill [Ki])). apply _. Qed.
*)

  Class head_reducible (e : expr) (σ : state ) :=
    head_reducible_step : ¬ is_zero (head_step (e, σ)).
  Definition head_irreducible (e : expr) (σ : state) :=
    is_zero (head_step (e, σ)).
  Definition head_stuck (e : expr) (σ : state) :=
    to_val e = None ∧ head_irreducible e σ.

  (* All non-value redexes are at the root. In other words, all sub-redexes are
     values. *)
  Definition sub_redexes_are_values (e : expr) :=
    ∀ K e', e = fill (K, e') → to_val e' = None → K = (* empty_ectx. *) [].

  Definition fill_liftU : (ectx * (expr * state)) → (expr * state) :=
    mProd
      ( ssrfun.comp fill $
        mProd fst (ssrfun.comp fst snd) )
      ( ssrfun.comp snd snd ).

  Lemma fill_liftU_meas : measurable_fun setT fill_liftU.
  Proof.
    mcrunch_prod.
    { eapply @measurable_compT; first by eauto with measlang.
      { apply fill_measurable. }
      mcrunch_prod.
      { by eauto with measlang. }
      by mcrunch_comp.
    }
    { by mcrunch_comp. }
  Qed.

  Definition fill_lift (K : ectx) : (expr * state) → (expr * state) :=
    fun x => fill_liftU (K, x).

  Lemma fill_lift_meas K: measurable_fun setT (fill_lift K).
  Proof.
    rewrite /fill_lift.
    assert ((λ x, fill_liftU (K, x)) = fill_liftU \o (λ x, (K, x))) as Hrewrite.
    { apply functional_extensionality_dep.
      by intros [??]. }
    rewrite Hrewrite.
    eapply @measurable_comp; [| |apply fill_liftU_meas|]; try done.
    apply pair1_measurable.
  Qed.

  Definition comp_ectx (K1 K2 : ectx) := K1 ++ K2.

  Lemma fill_lift_comp (K1 K2 : ectx) :
    fill_lift (comp_ectx K1 K2) = fill_lift K1 ∘ fill_lift K2.
  Proof.
    extensionality ρ. destruct ρ.
    rewrite /fill_lift/fill_liftU //=.
  Admitted.
  (*
    rewrite -fill_comp //=.
  Qed. *)

  Lemma fill_lift_empty :
    fill_lift [] = (λ ρ, ρ).
  Proof.
    extensionality ρ. destruct ρ.
    rewrite /fill_lift/fill_liftU //= fill_empty //.
  Qed.
  Instance inj_fill (K : ectx) : Inj eq eq (fill_lift K).
  Proof.
    intros [] [].
    move=> [H1 ->].
    have HF : ((curry fill) K) s = ((curry fill) K) s1 by rewrite //=.
    (* by rewrite (fill_inj K _ _ HF).
  Qed.
*) Admitted .


  (** FIXME: What a strange little measurability proof. *)
  Definition prim_step : (toPackedType _ (expr * state)%type) -> giryM (toPackedType _ (expr * state)%type) :=
    λ '(e, σ),
      let '(K, e') := decomp e in
      gMap' (fill_lift K) (head_step (e', σ)).

  Definition prim_step' : (toPackedType _ (expr * state)%type) -> giryM (toPackedType _ (expr  * state)%type) :=
    gMap' fill_liftU \o
    (gProd \o (gRet \o fst △ (head_step \o snd)) \o (fst \o decomp \o fst △ (snd \o decomp \o fst △ snd))).

  Lemma prim_step_prim_step' : prim_step = prim_step'.
    extensionality ρ. destruct ρ as [e s].
    rewrite /prim_step/prim_step'.
    destruct (decomp e) eqn:Hdecomp.
    simpl. rewrite /fill_lift. rewrite Hdecomp/=.
    (* need lemmas about gRet and gMap *)
  Admitted.

  Lemma prim_step_meas: measurable_fun setT prim_step.
  Proof.
    rewrite prim_step_prim_step'.
    rewrite /prim_step'.
    eapply measurable_comp; [| |apply gMap'_meas_fun|].
    { done. }
    { done. }
    { apply fill_liftU_meas. }
    mf_cmp_tree; try done.
    - mf_cmp_tree; try done.
      + eapply @gProd_meas_fun.
      + mf_prod; mf_cmp_tree; try done.
        * apply gRet_meas_fun.
        * apply head_step_meas_fun.
    - mf_prod; repeat mf_cmp_tree; try done.
      + apply decomp_measurable.
      + mf_prod. repeat mf_cmp_tree; try done.
        apply decomp_measurable.
  Qed.

  Lemma fill_not_val_idk2 K e : to_val e = None → to_val (fill (K, e)) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  (* Extra MeasLanguageMixin proofs :
  Definition ectx_lang_mixin : MeasLanguageMixin (@of_val Λ) to_val prim_step.
  Proof. split.
         - by apply ectx_language_mixin.
         - by apply ectx_language_mixin.
         - apply prim_step_meas.
         - by apply ectx_language_mixin.
         - by apply ectx_language_mixin.
         - by apply ectx_language_mixin.
         - by apply ectx_language_mixin.
         - by apply ectx_language_mixin.
         - intros e σ.
           rewrite /prim_step.
           case_match.
           apply decomp_fill in H. subst.
           intros Hneg.
           apply fill_not_val.
           eapply head_not_stuck.
           intros Hzero; apply Hneg.
           apply is_zero_gMap'; [apply fill_lift_meas|done].
         - intros e σ.
           rewrite /prim_step.
           destruct (decomp e) as [K e'] eqn:Heqn.
           apply decomp_fill in Heqn. subst.
           intros Hneg.
           assert (¬ is_zero (head_step (e', σ))).
           { intros Hzero; apply Hneg. apply is_zero_gMap'; last done.
             apply fill_lift_meas.
           }
           unshelve rewrite gMap'_gMap; first apply fill_lift_meas.
           rewrite -is_prob_gMap; last done.
           by apply head_step_mass.
  Qed.
*)

  (*
  Definition head_atomic (a : atomicity) (e : expr Λ) : Prop :=
    ∀ σ e' σ',
      head_step e σ (e', σ') > 0 →
      if a is WeaklyAtomic then irreducible (e', σ') else is_Some (to_val e').
  *)

  (** * Some lemmas about this language *)

  Lemma not_head_reducible e σ : ¬head_reducible e σ ↔ head_irreducible e σ.
  Proof.
    unfold head_reducible, head_irreducible. split.
    { by apply classical.NNP_P. }
    { by apply classical.P_NNP. }
  Qed.

  (** The decomposition into head redex and context is unique.
      In all sensible instances, [comp_ectx K' empty_ectx] will be the same as
      [K'], so the conclusion is [K = K' ∧ e = e'], but we do not require a law
      to actually prove that so we cannot use that fact here. *)
  Lemma head_redex_unique K K' e e' σ :
    fill (K, e) = fill (K', e') →
    head_reducible e σ →
    head_reducible e' σ →
    K = comp_ectx K' [] ∧ e = e'.
  Proof.
    intros Heq H1 H2.
  Admitted.
  (*
    edestruct (step_by_val K' K e' e) as [K'' HK].
    { by symmetry; apply Heq. }
    { by eapply head_not_stuck, H2. }
    { by eapply H1. }
    subst K. move: Heq. rewrite -fill_comp.
    intro HI.
    have HI' := (fill_inj _ _ _ HI).
    rewrite <- HI' in H2.
    destruct (head_ctx_step_val _ _ σ H2) as [HA | HA].
    { exfalso.
      erewrite head_not_stuck in HA; [by destruct HA |].
      by eapply H1. }
    { subst K''.
      split; [done|].
      rewrite <-HI'.
      by rewrite fill_empty. }
  Qed.
*)

  Lemma fill_prim_step_dbind K e1 σ1 :
    to_val e1 = None →
    prim_step ((fill (K, e1)), σ1) = gMap' (fill_lift K) (prim_step (e1, σ1)).
  Proof.
    intros Hval. rewrite /prim_step.
    destruct (decomp e1) as [K1 e1'] eqn:Heq.
    destruct (decomp (fill (K, e1))) as [K1' e1''] eqn:Heq'.
    Admitted.
  (*
    apply (decomp_fill_comp K) in Heq; [|done].
    rewrite Heq in Heq'; simplify_eq.
    (* Need lemmas for gMap', in particular composition of gMaps *)
  Admitted. *)

  (*  head_prim_step_pmf_eq e1 σ1: Same thing but pointwise *)

  Lemma head_prim_step_eq e1 σ1:
    head_reducible e1 σ1 →
    prim_step (e1, σ1) ≡μ head_step (e1, σ1).
  Proof.
    intros Hred.
    rewrite /= /prim_step.
    destruct (decomp e1) as [K e1'] eqn:Heq.
    edestruct (decomp_fill _ _ _ Heq).
    Admitted.
  (*
    destruct (head_ctx_step_val _ _ _ Hred) as [| ->].
    - assert (K = empty_ectx) as -> by eauto using decomp_val_empty.
      rewrite fill_lift_empty fill_empty.
      rewrite gMap'_id.
      reflexivity.
    - rewrite fill_lift_empty fill_empty.
      rewrite gMap'_id.
      reflexivity.
  Qed.
*)

  (* Proof breaks when no @ for some reason *)
  Lemma head_prim_step e1 σ1 : ¬ (is_zero (head_step (e1, σ1))) -> ¬ (is_zero (prim_step (e1, σ1))).
  Proof. intros ?. by rewrite (@head_prim_step_eq _ _ _). Qed.

  (*
  Lemma prim_step_iff e1 e2 σ1 σ2 :
    lt_ereal 0 (prim_step (e1, σ1) [set (e2, σ2)]) ↔
    ∃ K e1' e2',
      fill (K, e1') = e1 ∧
      fill (K, e2') = e2 ∧
      lt_ereal 0 (head_step (e1', σ1) [set (e2', σ2)]).
  Proof.
    split.
    - rewrite /prim_step. intros Hs.
      destruct (decomp e1) as [K e1'] eqn:Heq.
      apply decomp_fill in Heq.
      (** Derive lemmas for gMap' pos *)
      admit.
      (* eapply dmap_pos in Hs as [[] [[=] ?]]. *)
      (* simplify_eq. do 3 eexists; eauto. *)
    - intros (K & e1' & e2' & Hfill1 & Hfill2 & Hs). simplify_eq.
      rewrite fill_prim_step_dbind.
      + (** Lemmas for gMap' pos *)
        admit.
      + eapply head_not_stuck with σ1.
        intros Hzero; rewrite Hzero in Hs.
        * simpl in Hs.
          destroy_mathcomp; simpl in *.
          epose proof elimT (RltbP 0 0) _; first lra.
          Unshelve.
          rewrite /is_true/Is_true in Hs *.
          by case_match.
        * rewrite prod1.
          eapply @measurableX.
          { eapply @expr_meas_points. }
          { eapply @state_meas_points. }
  Admitted.
  *)

  (* Canonical structures pain because of the bundled measurability in head_step. Inline Markov?

  (*  Markov lemmas *)

  Lemma head_step_not_stuck e σ : (¬ is_zero (head_step (e, σ))) → not_stuck (e, σ).
  Proof.
    rewrite /not_stuck /reducible /=. intros Hs.
    erewrite <-head_prim_step_eq in Hs; last done.
    by right.
  Qed.


  Lemma head_val_stuck e σ : is_Some (to_val e) -> (is_zero (head_step (e, σ))).
  Proof.
    pose proof head_not_stuck e σ.
    apply contraPP.
    by intros ->%H.
  Qed.

  Lemma fill_reducible K e σ : reducible (e, σ) → reducible (fill (K, e), σ).
  Proof.
    rewrite /reducible/step/=.
    destruct (decomp e) as [K1 e1] eqn:Heqn1.
    destruct (decomp (fill (K, e))) as [K2 e2] eqn:Heqn2.
    intros H. intros H'. apply H.
    apply is_zero_gMap'; first apply fill_lift_meas.
    erewrite decomp_fill_comp in Heqn2; last done.
    - simplify_eq. (* apply decomp_fill in Heqn1 as Heqn2. subst. *)
      (* rewrite fill_comp in H'. *)
      destruct (to_val e2) eqn:Hval.
      + by apply head_val_stuck.
      + erewrite decomp_fill_comp in H'; last done.
        * eapply gMap'_is_zero; last done. apply fill_lift_meas.
        * apply decomp_fill in Heqn1. subst. by apply fill_not_val.
    - assert (to_val e1 = None).
      { eapply head_not_stuck.
        intros ?.
        apply H.
        eapply is_zero_gMap'; last done.
        apply fill_lift_meas.
      }
      apply decomp_fill in Heqn1. subst.
      by apply fill_not_val.
  Qed.
  Lemma head_prim_reducible e σ : head_reducible e σ → reducible (e, σ).
  Proof. intros.
         by apply head_prim_step.
  Qed.
  Lemma head_prim_fill_reducible e K σ :
    head_reducible e σ → reducible (fill (K, e), σ).
  Proof. intro. by apply fill_reducible, head_prim_reducible. Qed.
  (* Lemma state_step_head_reducible e σ σ' α : *)
  (*   state_step σ α σ' > 0 → head_reducible e σ ↔ head_reducible e σ'. *)
  (* Proof. eapply state_step_head_not_stuck. Qed. *)
  Lemma head_prim_irreducible e σ : irreducible (e, σ) → head_irreducible e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using head_prim_reducible.
  Qed.



  Lemma prim_head_reducible e σ :
    reducible (e, σ) → sub_redexes_are_values e → head_reducible e σ.
  Proof.
    rewrite /reducible/head_reducible/sub_redexes_are_values/=.
    destruct (decomp e) as [K e'] eqn:Heqn1.
    intros Hzero H Hzero'.
    apply Hzero. clear Hzero.
    apply decomp_fill in Heqn1; subst.
    destruct (to_val e') eqn:Heqn2.
    - apply is_zero_gMap'; first apply fill_lift_meas.
      destruct (classical.ExcludedMiddle (is_zero (head_step (e', σ)))) as [|H']; first done.
      apply head_not_stuck in H'. rewrite H' in Heqn2. done.
    - assert (K=empty_ectx) as ->.
      { eapply H; done. }
      rewrite fill_lift_empty in Hzero' *.
      rewrite fill_empty in Hzero'.
      by rewrite gMap'_id.
  Qed.
  Lemma prim_head_irreducible e σ :
    head_irreducible e σ → sub_redexes_are_values e → irreducible (e, σ).
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using prim_head_reducible.
  Qed.

  Lemma head_stuck_stuck e σ :
    head_stuck e σ → sub_redexes_are_values e → stuck (e, σ).
  Proof.
    intros [] ?. split; [by eapply to_final_None_2|].
    by apply prim_head_irreducible.
  Qed.

  (** We dont have anything about atomic i think?*)
  (* Lemma ectx_language_atomic a e : *)
  (*   head_atomic a e → sub_redexes_are_values e → Atomic a e. *)
  (* Proof. *)
  (*   intros Hatomic Hsub σ e' σ' (K & e1' & e2' & <- & <- & Hs)%prim_step_iff. *)
  (*   assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck. *)
  (*   rewrite fill_empty in Hatomic. *)
  (*   eapply Hatomic. rewrite fill_empty. eauto. *)
  (* Qed. *)



  (** Not sure how to express this in measure theortic terms *)
  (*
  Lemma head_reducible_prim_step_ctx K e1 σ1 e2 σ2:
    head_reducible e1 σ1 →
    prim_step (fill K e1) σ1 (e2, σ2) > 0 →
    ∃ e2', e2 = fill K e2' ∧ head_step e1 σ1 (e2', σ2) > 0.
  Proof.
    intros [[e2'' σ2''] HhstepK] (K' & e1' & e2' & HKe1 & HKe2 & Hs)%prim_step_iff.
    symmetry in HKe1.
    edestruct (step_by_val K) as [K'' HK]; eauto using val_head_stuck; simplify_eq/=.
    rewrite -fill_comp in HKe1; simplify_eq.
    exists (fill K'' e2'). rewrite fill_comp. split; [done|].
    destruct (head_ctx_step_val _ _ _ _ HhstepK) as [[]%not_eq_None_Some|HK''].
    { by eapply val_head_stuck. }
    subst. rewrite !fill_empty //.
  Qed.
*)

  (** Following lemma easily derived from head_prim_step_eq*)
  (** propose that we remove this *)
  (* Lemma head_reducible_prim_step e1 σ1 ρ : *)
  (*   head_reducible e1 σ1 → *)
  (*   prim_step e1 σ1 ρ > 0 → head_step e1 σ1 ρ > 0. *)
  (* Proof. *)
  (*   intros. destruct ρ. *)
  (*   edestruct (head_reducible_prim_step_ctx empty_ectx) as (?&?&?); *)
  (*     rewrite ?fill_empty; eauto. *)
  (*   by simplify_eq; rewrite fill_empty. *)
  (* Qed. *)


  (** Following lemma is true by definition *)
  (** propose that we remove this *)
  (* Lemma not_head_reducible_dzero e σ : *)
  (*   head_irreducible e σ → head_step e σ = dzero. *)
  (* Proof. *)
  (*   rewrite /reducible. *)
  (*   intros Hred%not_head_reducible. apply dzero_ext=> ρ. *)
  (*   destruct (Req_dec (head_step e σ ρ) 0); [done|]. *)
  (*   exfalso. apply Hred. *)
  (*   exists ρ. *)
  (*   pose proof (pmf_le_1 (head_step e σ) ρ). *)
  (*   pose proof (pmf_pos (head_step e σ) ρ). *)
  (*   lra. *)
  (* Qed. *)
*)

  (*
  (* Every evaluation context is a context. *)
  Global Program Instance ectx_lang_ctx K : MeasLanguageCtx (curry fill K) := {
      K_measurable := _;
      fill_not_val e := _;
      fill_inj  := _;
      fill_dmap e1 σ1 := _
  }.
  Next Obligation. move=>Ki; apply curry_meas_fun. apply fill_meas. Qed.
  Next Obligation. simpl. apply fill_not_val. Qed.
  Next Obligation. intros K e σ Hval.
                   eapply (fill_prim_step_dbind K e σ) in Hval.
                   erewrite <-gMap'_gMap.
                   simpl in *. by rewrite Hval.
  Qed.


  Record pure_head_step (e1 e2 : expr Λ) := {
    pure_head_step_safe σ1 : head_reducible e1 σ1;
    pure_head_step_det σ1 : is_det (e2, σ1) (head_step (e1, σ1))
  }.

  Lemma pure_head_step_pure_step e1 e2 : pure_head_step e1 e2 → pure_step e1 e2.
  Proof.
    intros [Hp1 Hp2]. split.
    - intros. apply head_prim_step. naive_solver.
    - intros σ. simpl. rewrite -/(prim_step (e1, σ)). erewrite head_prim_step_eq; naive_solver.
  Qed.

  (** This is not an instance because HeapLang's [wp_pure] tactic already takes
      care of handling the evaluation context.  So the instance is redundant.
      If you are defining your own language and your [wp_pure] works
      differently, you might want to specialize this lemma to your language and
      register that as an instance. *)
  Lemma pure_exec_fill K φ n e1 e2 :
    PureExec φ n e1 e2 →
    PureExec φ n (fill (K, e1)) (fill (K, e2)).
  Proof. apply: pure_exec_ctx. Qed.

End ectx_language.
*)



Canonical Structure stateO  := leibnizO (state).
Canonical Structure valO  := leibnizO (val).
Canonical Structure exprO := leibnizO (expr).

Definition cfg  := (expr * state )%type.

Definition fill_lift_idk (K : expr -> expr) : (expr * state ) → (expr * state ) :=
  mProd (ssrfun.comp K fst) snd.

Lemma fill_lift_measurable (K : (expr) -> (expr)) (HK : measurable_fun setT K) :
  @measurable_fun _ _ (expr  * state )%type (expr * state )%type setT (fill_lift_idk K).
Proof.
  mcrunch_prod.
  { mcrunch_comp. }
  { eauto with measlang. }
Qed.

Global Instance inj_fill_lift_idk (K : (expr -> expr )) :
  Inj (=) (=) K →
  Inj (=) (=) (fill_lift_idk K).
Proof. by intros ? [] [] [=->%(inj _) ->]. Qed.

Class MeasLanguageCtx  (K : (expr ) -> (expr ))  := {
  K_measurable : measurable_fun setT K;
  fill_not_val_idk3 e :
    to_val e = None → to_val (K e) = None;
  fill_inj : Inj (=) (=) K;
  fill_dmap e1 σ1 :
    to_val e1 = None →
    prim_step ((K e1), σ1) ≡μ gMap (fill_lift_measurable K K_measurable) (prim_step (e1, σ1))
}.

#[global] Existing Instance fill_inj.

Inductive atomicity := StronglyAtomic | WeaklyAtomic.



Definition meas_lang_markov_mixin : MeasMarkovMixin (prim_step) (ssrfun.comp to_val fst).
Proof.
  constructor.
  { admit. (* by apply language_mixin. } *) }
  { eapply measurable_comp.
    { by eapply @measurableT. }
    { done. }
    { admit. (* by apply language_mixin. } *) }
    { simpl. by eapply @measurable_fst. }
  }
  intros [e σ]; simpl.
  pose proof (lem (is_zero (prim_step (e, σ)))) as [|H]; first done.
Admitted. (*
  pose proof (mixin_val_stuck _ _ _ (language_mixin Λ) _ _ H) as ->.
  rewrite /is_Some.
  naive_solver.
Qed. *)

Canonical Structure meas_lang_markov := MeasMarkov _ _ _ _ (meas_lang_markov_mixin).

Lemma irreducible_meas_set : measurable (irreducible : set (expr * state)%type).
Proof.
  unfold irreducible.
  have H1 : giry_display.-measurable is_zero.
  { intros m T.
    unfold is_zero.
    by eapply eq_gZero_measurable. }
  have X := (@step_meas (meas_lang_markov) _ is_zero).
  have X1 := X _ (H1 _ _).
  rewrite setTI in X1.
  by apply X1.
Qed.

Definition to_val_is_val : set (expr * state) := (preimage to_val option_cov_Some) `*` setT.

Lemma to_val_is_val_meas_set : measurable to_val_is_val.
Proof.
  unfold to_val_is_val.
  apply measurableX; last by eapply @measurableT.
  rewrite <- (setTI (preimage _ _)).
  apply to_val_meas.
  { by eapply @measurableT. }
  { by apply option_cov_Some_meas_set. }
Qed.

(* NOTE: This is fairly different to the Clutch version *)
Class Atomic (a : atomicity) (e : expr) : Prop :=
  atomic σ :
    if a is WeaklyAtomic
      then has_support_in (prim_step (e, σ)) irreducible
      else has_support_in (prim_step (e, σ)) to_val_is_val.

Lemma of_to_val_flip v e : of_val v = e → to_val e = Some v.
Proof. intros <-. by rewrite to_of_val. Qed.
Global Instance of_val_inj : Inj (=) (=) (@of_val).
Proof. by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.


Lemma strongly_atomic_atomic e a :
  Atomic StronglyAtomic e → Atomic a e.
Proof.
  unfold Atomic. destruct a; eauto.
  intros H ?.
  eapply has_support_in_subset; last apply H.
  - apply to_val_is_val_meas_set.
  - apply irreducible_meas_set.
  - rewrite /subset/to_val_is_val/irreducible.
    intros [e' σ']. simpl.
    intros [H1 _].
    destruct (lem (is_zero (prim_step (e', σ')))) as [|H']; first done.
Admitted.
 (*
    apply val_stuck in H'.
    rewrite H' in H1.
    rewrite /option_cov_Some in H1. simpl in H1.
    naive_solver.
Qed. *)

Lemma fill_step e σ `{!MeasLanguageCtx K} :
  (¬ is_zero (prim_step (e, σ))) ->
  (¬ is_zero (prim_step (K e, σ))).
Proof.
  intros Hs.
Admitted.
(*
  rewrite fill_dmap; [| by eapply val_stuck].
  intro Hs'. apply Hs.
  rewrite /is_zero in Hs'.
  rewrite -gMap'_gMap in Hs'.
  eapply gMap'_is_zero; last done. apply fill_lift_measurable.
  apply K_measurable.
Qed. *)

(*
Lemma fill_step_inv e1' σ1 e2 σ2 `{!LanguageCtx K} :
  to_val e1' = None → prim_step (K e1') σ1 (e2, σ2) > 0 →
  ∃ e2', e2 = K e2' ∧ prim_step e1' σ1 (e2', σ2) > 0.
Proof.
  intros Hv. rewrite fill_dmap //.
  intros ([e1 σ1'] & [=]%dret_pos & Hstep)%dbind_pos.
  subst. eauto.
Qed.

(** The following lemma is redundant, see fill_dmap *)
Lemma fill_step_prob e1 σ1 e2 σ2 `{!LanguageCtx K} :
  to_val e1 = None →
  prim_step e1 σ1 (e2, σ2) = prim_step (K e1) σ1 (K e2, σ2).
Proof.
  intros Hv. rewrite fill_dmap //.
  by erewrite (dmap_elem_eq _ (e2, σ2) _ (λ '(e0, σ0), (K e0, σ0))).
Qed.
 *)

(*
Lemma reducible_fill `{!@MeasLanguageCtx Λ K} e σ :
  reducible (e, σ) → reducible (K e, σ).
Proof.
  unfold reducible in *. intros H1 H2. apply H1. simpl in *.
  erewrite fill_dmap in H2; last first.
  { by eapply val_stuck. }
  rewrite -gMap'_gMap in H2.
  eapply gMap'_is_zero; last done.
  apply fill_lift_measurable; apply K_measurable.
Qed.

Lemma reducible_fill_inv `{!@MeasLanguageCtx Λ K} e σ :
  to_val e = None → reducible (K e, σ) → reducible (e, σ).
Proof.
  rewrite /reducible. simpl.
  intros H'.
  erewrite fill_dmap; last done.
  intros H1 H2. apply H1.
  rewrite /is_zero in H2.
  rewrite H2.
  by rewrite gZero_map.
  (* TODO: make measure_eq work with rewrite *)
Qed.
*)

(*
Lemma state_step_reducible e σ σ' α :
  state_step σ α σ' > 0 → reducible (e, σ) ↔ reducible (e, σ').
Proof. apply state_step_not_stuck. Qed.
Lemma state_step_iterM_reducible e σ σ' α n:
  iterM n (λ σ, state_step σ α) σ σ'> 0 → reducible (e, σ) ↔ reducible (e, σ').
Proof.
  revert σ σ'.
  induction n.
  - intros σ σ'. rewrite iterM_O. by intros ->%dret_pos.
  - intros σ σ'. rewrite iterM_Sn. rewrite dbind_pos. elim.
    intros x [??]. pose proof state_step_reducible. naive_solver.
Qed.


Lemma irreducible_fill `{!@MeasLanguageCtx Λ K} e σ :
  to_val e = None → irreducible (e, σ) → irreducible (K e, σ).
Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill_inv. Qed.
Lemma irreducible_fill_inv `{!@MeasLanguageCtx Λ K} e σ :
  irreducible (K e, σ) → irreducible (e, σ).
Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill. Qed.

Lemma not_stuck_fill_inv K `{!@MeasLanguageCtx Λ K} e σ :
  not_stuck (K e, σ) → not_stuck (e, σ).
Proof.
  rewrite /not_stuck /is_final /to_final /= -!not_eq_None_Some.
  intros [?|?].
  - auto using fill_not_val.
  - destruct (decide (to_val e = None)); eauto using reducible_fill_inv.
Qed.

Lemma stuck_fill `{!@MeasLanguageCtx Λ K} e σ :
  stuck (e, σ) → stuck (K e, σ).
Proof. rewrite -!not_not_stuck. eauto using not_stuck_fill_inv. Qed.


Record pure_step (e1 e2 : expr Λ)  := {
  pure_step_safe σ1 : ¬ (is_zero (prim_step (e1, σ1)));
  pure_step_det σ : is_det (e2, σ) (prim_step (e1, σ));
}.

Class PureExec (φ : Prop) (n : nat) (e1 e2 : expr Λ) :=
  pure_exec : φ → relations.nsteps pure_step n e1 e2.

Lemma pure_step_ctx K `{!@MeasLanguageCtx Λ K} e1 e2 :
  pure_step e1 e2 → pure_step (K e1) (K e2).
Proof.
  intros [Hred Hstep]. split.
  { intros σ1.
    eapply (fill_step _); first by apply H.
    by apply Hred. }
  { intros σ.
    rewrite fill_dmap; last by eapply (val_stuck _ σ).
    pose proof Hstep σ as Hdet.
    eapply (is_det_gMap (f:=fill_lift K)) in Hdet.
    - by rewrite gMap'_gMap{1}/fill_lift/= in Hdet.
    - apply fill_lift_measurable. apply K_measurable.
  }
Qed.

Lemma pure_step_nsteps_ctx K `{!@MeasLanguageCtx Λ K} n e1 e2 :
  relations.nsteps pure_step n e1 e2 →
  relations.nsteps pure_step n (K e1) (K e2).
Proof.
  intro H'.
  eapply (nsteps_congruence _ _ _ _ _ _ H' ).
  Unshelve.
  intros x y.
  by apply (pure_step_ctx _).
Qed.

Lemma rtc_pure_step_ctx K `{!@MeasLanguageCtx Λ K} e1 e2 :
  rtc pure_step e1 e2 → rtc pure_step (K e1) (K e2).
Proof.
  intro H'.
  eapply (rtc_congruence _ _ _ _ _ H').
  Unshelve.
  intros x y.
  by apply (pure_step_ctx _).
Qed.

(* We do not make this an instance because it is awfully general. *)
Lemma pure_exec_ctx K `{!@MeasLanguageCtx Λ K} φ n e1 e2 :
  PureExec φ n e1 e2 →
  PureExec φ n (K e1) (K e2).
Proof.
  rewrite /PureExec.
  intros H' p.
  apply (pure_step_nsteps_ctx _).
  by apply (H' p).
Qed.

Lemma PureExec_reducible σ1 φ n e1 e2 :
  φ → PureExec φ (S n) e1 e2 → reducible (e1, σ1).
Proof. move => Hφ /(_ Hφ). inversion_clear 1. apply H. Qed.

Lemma PureExec_not_val `{Inhabited (language.state Λ)} φ n e1 e2 :
  φ → PureExec φ (S n) e1 e2 → to_val e1 = None.
Proof.
  intros Hφ Hex.
  pose proof (PureExec_reducible inhabitant _ _ _ _ Hφ Hex) as K.
  by eapply val_stuck.
Qed.

*)

(* This is a family of frequent assumptions for PureExec *)
Class IntoVal (e : expr) (v : val) :=
  into_val : of_val v = e.

Class AsVal (e : expr) := as_val : ∃ v, of_val v = e.
(* There is no instance [IntoVal → AsVal] as often one can solve [AsVal] more *)
(* efficiently since no witness has to be computed. *)
Global Instance as_vals_of_val vs : TCForall AsVal (of_val <$> vs).
Proof.
  apply TCForall_Forall, Forall_fmap, Forall_true=> v.
  rewrite /AsVal /=; eauto.
Qed.

Lemma as_val_is_Some e :
  (∃ v, of_val v = e) → is_Some (to_val e).
Proof. intros [v <-]. rewrite to_of_val. eauto. Qed.

(*
Lemma fill_is_val e K `{@MeasLanguageCtx Λ K} :
  is_Some (to_val (K e)) → is_Some (to_val e).
Proof. rewrite -!not_eq_None_Some. eauto using fill_not_val. Qed.

Lemma rtc_pure_step_val `{!Inhabited (state)} v e :
  rtc pure_step (of_val v) e → to_val e = Some v.
Proof.
  intros ?; rewrite <- to_of_val.
  f_equal; symmetry; eapply rtc_nf; first done.
  intros [e' [ Hstep ? ]].
  have K := to_of_val v.
  rewrite (val_stuck _ _ (Hstep inhabitant)) in K.
  by inversion K.
Qed.

*)
