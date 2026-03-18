From clutch.diffpriv Require Import adequacy adequacy_rel.
From clutch.diffpriv.examples Require Import
  sparse_vector_technique
  privacy_filter
  auto_avg
  generic_cache
  report_noisy_max.

(** This file checks that the main results of the paper rely only on standard
    axioms: classical reasoning and the axiomatization of the reals, both from
    Rocq's standard library.  Build this file and inspect the output of the
    [Print Assumptions] command below. *)

Definition all_results :=
  (
    @hoare_diffpriv_pure,
    @hoare_diffpriv_pure_list,
    @wp_adequacy,
    @above_threshold_online_AT_spec,
    @SVT_online_diffpriv,
    @SVT_stream_diffpriv,
    @create_filter_private,
    @adaptive_count_diffpriv,
    @exact_cache_dipr,
    @exact_cache_dipr_offline_map,
    @rnm_diffpriv
  ).

Print Assumptions all_results.
