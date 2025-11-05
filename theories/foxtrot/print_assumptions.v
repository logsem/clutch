From clutch.foxtrot Require Import entropy_mixer batch_sampling rejection_samplers von_neumann libsodium nodet_example encryption encryption_unknown algebraic presample_rhs.

Definition all_results :=
  (mixer_eq_rand,
  batch_prog_eq_rand_prog,
  rejection_sampler_prog_eq_rand_prog,
  von_neumann_prog_eq_rand_prog,
  randombytes_uniform_equivalent_ideal,
  prog_eq_unit,
  encryption.encr_prog_eq_rand_prog,
  encr_prog_eq_rand_prog,
  (eq1 , eq2 , eq3 , eq4, eq5, eq6, eq7, eq8),
  presample_RHS_is_unsound    
  ).

Print Assumptions all_results. 

