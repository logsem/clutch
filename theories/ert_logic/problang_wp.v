(** This file proves the basic laws of the ProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Export ghost_map.
From clutch.ert_logic Require Export expected_time_credits ert_weakestpre (* ectx_lifting *).
From clutch.prob_lang Require Export class_instances.
From clutch.prob_lang Require Export tactics lang notation.
From iris.prelude Require Import options.

Class ert_clutchGS Σ := HeapG {
  clutchGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state *)
  clutchGS_heap : ghost_mapG Σ loc val;
  clutchGS_tapes : ghost_mapG Σ loc tape;
  (* ghost names for the state *)
  clutchGS_heap_name : gname;
  clutchGS_tapes_name : gname;
  (* CMRA and ghost name for the ERT *)
  ert_clutchGS_etc :: etcGS Σ;
}.


Definition progUR : ucmra := optionUR (exclR exprO).
Definition cfgO : ofe := prodO exprO stateO.
Definition cfgUR : ucmra := optionUR (exclR cfgO).

Definition heap_auth `{ert_clutchGS Σ} :=
  @ghost_map_auth _ _ _ _ _ clutchGS_heap clutchGS_heap_name.
Definition tapes_auth `{ert_clutchGS Σ} :=
  @ghost_map_auth _ _ _ _ _ clutchGS_tapes clutchGS_tapes_name.


Global Instance clutchGS_irisGS `{!ert_clutchGS Σ} : irisGS prob_lang Σ := {
  iris_invGS := clutchGS_invG;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes))%I;
  etc_interp ε := (etc_supply ε);
}.

(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ clutchGS_heap clutchGS_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Tapes *)
Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ _ _ _ clutchGS_tapes clutchGS_tapes_name l dq (v : tape))
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.
