(** Primitive ghost-state setup for the generic DP weakest precondition.
    Generalized from [clutch.diffpriv.primitive_laws]: the reusable WP core
    ([weakestpre]/[lifting]/[ectx_lifting]) is imported AS-IS and instantiated
    at [gen_lang S]; the only change here is collapsing the per-distribution
    tape ghost maps (tapes / tapes_laplace / …) into one generic [stape] map. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export ghost_map.
From clutch.base_logic Require Export error_credits_mult error_credits.
From clutch.diffpriv Require Export weakestpre ectx_lifting.
From clutch.gen_prob_lang Require Import lang.
From clutch.gen_prob_lang.spec Require Export spec_ra.
From iris.prelude Require Import options.

Class diffprivGS Σ := HeapG {
  diffprivGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state: a heap and ONE generic sample-tape map *)
  diffprivGS_heap :: ghost_mapG Σ loc val;
  diffprivGS_tapes :: ghost_mapG Σ loc stape;
  diffprivGS_heap_name : gname;
  diffprivGS_tapes_name : gname;
  (* spec-side ghost state *)
  diffprivGS_spec :: specG_prob_lang Σ;
  (* error credits (multiplicative ε and additive δ) *)
  diffprivGS_error_eps :: ecmGS Σ;
  diffprivGS_error_del :: ecGS Σ;
}.

Class diffprivGpreS Σ := DiffprivGpreS {
  diffprivGpreS_iris  :: invGpreS Σ;
  diffprivGpreS_heap  :: ghost_mapG Σ loc val;
  diffprivGpreS_tapes :: ghost_mapG Σ loc stape;
  diffprivGpreS_spec  :: specGpreS Σ;
  diffprivGpreS_err_eps :: ecmGpreS Σ;
  diffprivGpreS_err_del :: ecGpreS Σ;
}.

Definition diffprivΣ : gFunctors :=
  #[invΣ;
    ghost_mapΣ loc val;
    ghost_mapΣ loc stape;
    specΣ;
    ecmΣ;
    ecΣ].
Global Instance subG_diffprivGPreS {Σ} : subG diffprivΣ Σ → diffprivGpreS Σ.
Proof. solve_inG. Qed.

Definition heap_auth `{diffprivGS Σ} :=
  @ghost_map_auth _ _ _ _ _ diffprivGS_heap diffprivGS_heap_name.
Definition stapes_auth `{diffprivGS Σ} :=
  @ghost_map_auth _ _ _ _ _ diffprivGS_tapes diffprivGS_tapes_name.
Definition mult_ec_supply `{diffprivGS Σ} :=
  @ecm_supply _ diffprivGS_error_eps.
Definition add_ec_supply `{diffprivGS Σ} :=
  @ec_supply _ diffprivGS_error_del.

(* The WP ghost-state instance, parametric in the distribution signature [S].
   The [spec_updateGS (lang_markov (gen_lang S))] obligation is discharged by
   [spec_rules_spec_updateGS S] from spec_ra. *)
Global Instance diffprivGS_irisGS `{!diffprivGS Σ} (S : Sig) :
  diffprivWpGS (gen_lang S) Σ := {
  diffprivWpGS_invGS := diffprivGS_invG;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ stapes_auth 1 σ.(stapes))%I;
  err_interp ε δ := ((mult_ec_supply ε) ∗ (add_ec_supply δ))%I;
}.

(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ diffprivGS_heap diffprivGS_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Sample tapes (one generic tape map) *)
Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ stape _ _ diffprivGS_tapes diffprivGS_tapes_name l dq v)
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.
