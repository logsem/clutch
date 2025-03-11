(** This file proves the basic laws of the ProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export ghost_map.
From clutch.base_logic Require Export error_credits.
From clutch.foxtrot Require Export weakestpre ectx_lifting.
From clutch.con_prob_lang Require Export class_instances.
From clutch.con_prob_lang Require Import tactics lang notation metatheory.
From clutch.con_prob_lang.spec Require Export spec_ra.
From iris.prelude Require Import options.

Class foxtrotGS Σ := HeapG {
  foxtrotGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state *)
  foxtrotGS_heap : ghost_mapG Σ loc val;
  foxtrotGS_tapes : ghost_mapG Σ loc tape;
  (* ghost names for the state *)
  foxtrotGS_heap_name : gname;
  foxtrotGS_tapes_name : gname;
  (* CMRA and ghost name for the spec *)
  foxtrotGS_spec :: specG_con_prob_lang Σ;
  (* CMRA and ghost name for the error *)
  foxtrotGS_error :: ecGS Σ;
}.

Class foxtrotGpreS Σ := FoxtrotGpreS {
  foxtrotGpreS_iris  :: invGpreS Σ;
  foxtrotGpreS_heap  :: ghost_mapG Σ loc val;
  foxtrotGpreS_tapes :: ghost_mapG Σ loc tape;
  foxtrotGpreS_spcec :: specGpreS Σ;
  foxtrotGpreS_err   :: ecGpreS Σ;
}.

Definition foxtrotΣ : gFunctors :=
  #[invΣ;
    ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    specΣ;
    ecΣ].
Global Instance subG_foxtrotGPreS {Σ} : subG foxtrotΣ Σ → foxtrotGpreS Σ.
Proof. solve_inG. Qed.

Definition heap_auth `{foxtrotGS Σ} :=
  @ghost_map_auth _ _ _ _ _ foxtrotGS_heap foxtrotGS_heap_name.
Definition tapes_auth `{foxtrotGS Σ} :=
  @ghost_map_auth _ _ _ _ _ foxtrotGS_tapes foxtrotGS_tapes_name.

Global Instance foxtrotGS_irisGS `{!foxtrotGS Σ} : foxtrotWpGS con_prob_lang Σ := {
  foxtrotWpGS_invGS := foxtrotGS_invG;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes))%I;
  spec_interp ρ := spec_auth ρ;
  fork_post v :=  True%I;
  err_interp := ec_supply;
}.

(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ foxtrotGS_heap foxtrotGS_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Tapes *)
Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ tape _ _ foxtrotGS_tapes foxtrotGS_tapes_name l dq v)
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.

(** User-level tapes *)
Definition nat_tape `{foxtrotGS Σ} l (N : nat) (ns : list nat) : iProp Σ :=
  ∃ (fs : list (fin (S N))), ⌜fin_to_nat <$> fs = ns⌝ ∗ l ↪ (N; fs).

Notation "l ↪N ( M ; ns )" := (nat_tape l M ns)%I
  (at level 20, format "l  ↪N  ( M ;  ns )") : bi_scope.
