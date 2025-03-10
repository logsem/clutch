(** This file proves the basic laws of the ProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export ghost_map.
From clutch.base_logic Require Export error_credits.
From clutch.foxtrot Require Export weakestpre ectx_lifting.
From clutch.con_prob_lang Require Export class_instances.
From clutch.con_prob_lang Require Import tactics lang notation metatheory.
(* From clutch.prob_lang.spec Require Export spec_ra spec_rules spec_tactics. *)
(* From iris.prelude Require Import options. *)

(* Class approxisGS Σ := HeapG { *)
(*   approxisGS_invG : invGS_gen HasNoLc Σ; *)
(*   (* CMRA for the state *) *)
(*   approxisGS_heap : ghost_mapG Σ loc val; *)
(*   approxisGS_tapes : ghost_mapG Σ loc tape; *)
(*   (* ghost names for the state *) *)
(*   approxisGS_heap_name : gname; *)
(*   approxisGS_tapes_name : gname; *)
(*   (* CMRA and ghost name for the spec *) *)
(*   approxisGS_spec :: specG_prob_lang Σ; *)
(*   (* CMRA and ghost name for the error *) *)
(*   approxisGS_error :: ecGS Σ; *)
(* }. *)

(* Class approxisGpreS Σ := ApproxisGpreS { *)
(*   approxisGpreS_iris  :: invGpreS Σ; *)
(*   approxisGpreS_heap  :: ghost_mapG Σ loc val; *)
(*   approxisGpreS_tapes :: ghost_mapG Σ loc tape; *)
(*   approxisGpreS_spcec :: specGpreS Σ; *)
(*   approxisGpreS_err   :: ecGpreS Σ; *)
(* }. *)

(* Definition approxisΣ : gFunctors := *)
(*   #[invΣ; *)
(*     ghost_mapΣ loc val; *)
(*     ghost_mapΣ loc tape; *)
(*     specΣ; *)
(*     ecΣ]. *)
(* Global Instance subG_approxisGPreS {Σ} : subG approxisΣ Σ → approxisGpreS Σ. *)
(* Proof. solve_inG. Qed. *)

(* Definition heap_auth `{approxisGS Σ} := *)
(*   @ghost_map_auth _ _ _ _ _ approxisGS_heap approxisGS_heap_name. *)
(* Definition tapes_auth `{approxisGS Σ} := *)
(*   @ghost_map_auth _ _ _ _ _ approxisGS_tapes approxisGS_tapes_name. *)

(* Global Instance approxisGS_irisGS `{!approxisGS Σ} : approxisWpGS prob_lang Σ := { *)
(*   approxisWpGS_invGS := approxisGS_invG; *)
(*   state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes))%I; *)
(*   err_interp := ec_supply; *)
(* }. *)

(* (** Heap *) *)
(* Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ approxisGS_heap approxisGS_heap_name l dq v) *)
(*   (at level 20, format "l  ↦{ dq }  v") : bi_scope. *)
(* Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I *)
(*   (at level 20, format "l  ↦□  v") : bi_scope. *)
(* Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I *)
(*   (at level 20, format "l  ↦{# q }  v") : bi_scope. *)
(* Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I *)
(*   (at level 20, format "l  ↦  v") : bi_scope. *)

(* (** Tapes *) *)
(* Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ tape _ _ approxisGS_tapes approxisGS_tapes_name l dq v) *)
(*   (at level 20, format "l  ↪{ dq }  v") : bi_scope. *)
(* Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I *)
(*   (at level 20, format "l  ↪□  v") : bi_scope. *)
(* Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I *)
(*   (at level 20, format "l  ↪{# q }  v") : bi_scope. *)
(* Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I *)
(*   (at level 20, format "l  ↪  v") : bi_scope. *)

(* (** User-level tapes *) *)
(* Definition nat_tape `{approxisGS Σ} l (N : nat) (ns : list nat) : iProp Σ := *)
(*   ∃ (fs : list (fin (S N))), ⌜fin_to_nat <$> fs = ns⌝ ∗ l ↪ (N; fs). *)

(* Notation "l ↪N ( M ; ns )" := (nat_tape l M ns)%I *)
(*   (at level 20, format "l  ↪N  ( M ;  ns )") : bi_scope. *)
