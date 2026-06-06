From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
 spec_rules spec_ra class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def.

(*Import fingroup.

Import fingroup.fingroup.

Import valgroup_tactics.
*)
Section parallel_composition.

  (*Fixpoint list_args_app (f : val) (op_l : list val) : val :=
    match: op_l with
    | nil => f
    | op_x :: op_{xs} => (f op_x)
    end.*)
  
  
Definition left_composition (f_x f_y : val) : val := λ: "f" "op_x1" "op_x2" "op_y1" "op_y2",
                                                                                                       f_x (f_y "f" "op_y1" "op_y2") "op_x1" "op_x2".

Definition right_composition (f_x : val) (f_y : val) (op_x1 op_x2 : val) : val :=
  λ: "f" "op_x1" "op_x2" "op_y1" "op_y2",
  (left_composition f_y f_x) "f" "op_y1" "op_y2" "op_x1" "op_x2".

End parallel_composition.
