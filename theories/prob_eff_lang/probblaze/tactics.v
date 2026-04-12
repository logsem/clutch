From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import  na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra 
  class_instances.

Module Export Tactics.

Tactic Notation "foldkont" ident(k) open_constr(kctx) :=
    match goal with
    | |- context[KontV ?kont] =>
        unify kont kctx ; set (k := KontV kont)
    end.

  Tactic Notation "foldkont" ident(k) := foldkont k _.

  Tactic Notation "foldkont" := let k := fresh "kont" in foldkont k.

  
End Tactics.
