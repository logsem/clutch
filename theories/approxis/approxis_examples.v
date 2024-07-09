From clutch.approxis.examples Require Import prp_prf_weak prp_prf_adaptive rejection_samplers von_neumann_coin b_tree_adt prf_cpa.
(** This is a file containing all the main results of the case studies in the Approxis paper *)

Definition main_results:= (weak_switching_lemma,
                             switching_lemma,
                               rejection_sampler_correct,
                                 naive_equiv_opt,
                                   CPA_bound_realistic
                          ).

Print Assumptions main_results.
