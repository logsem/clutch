(** This file proves the basic laws of the ProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export ghost_map.
From clutch.base_logic Require Export error_credits_mult error_credits.
From clutch.diffpriv Require Export wp_pw_simple.
From clutch.prob_lang Require Export class_instances.
From clutch.prob_lang Require Import tactics lang notation metatheory.
From clutch.prob_lang.spec Require Export spec_ra spec_rules spec_tactics.
From iris.prelude Require Import options.

Class diffprivGS Σ := HeapG {
  diffprivGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state *)
  diffprivGS_heap : ghost_mapG Σ loc val;
  diffprivGS_tapes : ghost_mapG Σ loc tape;
  (* ghost names for the state *)
  diffprivGS_heap_name : gname;
  diffprivGS_tapes_name : gname;
  (* CMRA and ghost name for the spec *)
  diffprivGS_spec :: specG_prob_lang Σ;
  (* CMRA and ghost names for the error *)
  diffprivGS_error_eps :: ecmGS Σ;
  diffprivGS_error_del :: ecGS Σ;
}.

Class diffprivGpreS Σ := DiffprivGpreS {
  diffprivGpreS_iris  :: invGpreS Σ;
  diffprivGpreS_heap  :: ghost_mapG Σ loc val;
  diffprivGpreS_tapes :: ghost_mapG Σ loc tape;
  diffprivGpreS_spcec :: specGpreS Σ;
  diffprivGpreS_err_eps   :: ecmGpreS Σ;
  diffprivGpreS_err_del   :: ecGpreS Σ;
}.

Definition diffprivΣ : gFunctors :=
  #[invΣ;
    ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    specΣ;
    ecmΣ;
    ecΣ].
Global Instance subG_diffprivGPreS {Σ} : subG diffprivΣ Σ → diffprivGpreS Σ.
Proof. solve_inG. Qed.

Definition heap_auth `{diffprivGS Σ} :=
  @ghost_map_auth _ _ _ _ _ diffprivGS_heap diffprivGS_heap_name.
Definition tapes_auth `{diffprivGS Σ} :=
  @ghost_map_auth _ _ _ _ _ diffprivGS_tapes diffprivGS_tapes_name.
Definition mult_ec_supply `{diffprivGS Σ} :=
  @ecm_supply _ diffprivGS_error_eps.
Definition add_ec_supply `{diffprivGS Σ} :=
  @ec_supply _ diffprivGS_error_del.

Global Instance diffprivGS_irisGS `{!diffprivGS Σ} : diffprivWpGS prob_lang Σ := {
  diffprivWpGS_invGS := diffprivGS_invG;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes))%I;
  err_interp ε δ := ((mult_ec_supply ε) ∗ (add_ec_supply δ))%I;
}.
