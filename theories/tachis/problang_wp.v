(** This file proves the basic laws of the ProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Export ghost_map.
From clutch.tachis Require Export expected_time_credits ert_weakestpre (* ectx_lifting *).
From clutch.prob_lang Require Export class_instances.
From clutch.prob_lang Require Export tactics lang notation.
From iris.prelude Require Import options.

Class tachisGS Σ (cost : Costfun prob_lang) := HeapG {
  tachisGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state *)
  tachisGS_heap : ghost_mapG Σ loc val;
  tachisGS_tapes : ghost_mapG Σ loc tape;
  (* ghost names for the state *)
  tachisGS_heap_name : gname;
  tachisGS_tapes_name : gname;
  (* CMRA and ghost name for the ERT *)
  tachisGS_etc : etcGS Σ;
}.

Definition progUR : ucmra := optionUR (exclR exprO).
Definition cfgO : ofe := prodO exprO stateO.
Definition cfgUR : ucmra := optionUR (exclR cfgO).

Definition heap_auth `{tachisGS Σ} :=
  @ghost_map_auth _ _ _ _ _ tachisGS_heap tachisGS_heap_name.
Definition tapes_auth `{tachisGS Σ} :=
  @ghost_map_auth _ _ _ _ _ tachisGS_tapes tachisGS_tapes_name.

Global Instance tachisGS_tachisWpGSS `{!tachisGS Σ F} : tachisWpGS prob_lang Σ := {
  tachisWpGS_invGS := tachisGS_invG;
  tachisWpGS_etcGS := tachisGS_etc;

  state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes))%I;
  costfun := F
}.

(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ tachisGS_heap tachisGS_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Tapes *)
Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ _ _ _ tachisGS_tapes tachisGS_tapes_name l dq (v : tape))
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.
