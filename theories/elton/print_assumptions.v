From clutch.elton Require Export repeat_flip_neg multiple_guess hash_guess basic_hash generic_group.

Definition all_results :=
  (repeat_flip_neg.prog_correct,
     multiple_guess.prog_correct,
       guess_hash,
         basic_hash_game_two_urns,
           guess_group
  ).

Print Assumptions all_results. 
