(** Tactics and lemmas for properness and non-expansiveness. *)
From stdpp Require Export tactics.
From iris.algebra Require Export ofe gmap.
From iris.base_logic Require Export base_logic lib.invariants.
From iris.program_logic Require Import weakestpre.
Import uPred.

(* Hmmm *)
Ltac my_prepare :=
  intros;
  repeat lazymatch goal with
  | |- Proper _ _ => intros ???
  | |- (_ ==> _)%signature _ _ => intros ???
  | |- pointwise_relation _ _ _ _ => intros ?
  end; simplify_eq.

Ltac solve_proper_from_ne :=
  my_prepare;
  solve [repeat first [done | eassumption | apply equiv_dist=>? |
    match goal with
    | [H : _ ≡ _ |- _] => setoid_rewrite equiv_dist in H; rewrite H
    end] ].

Ltac properness :=
  repeat match goal with
  | |- (∃ _: _, _)%I ≡ (∃ _: _, _)%I => apply exist_proper =>?
  | |- (∀ _: _, _)%I ≡ (∀ _: _, _)%I => apply forall_proper =>?
  | |- (_ ∧ _)%I ≡ (_ ∧ _)%I => apply and_proper
  | |- (_ ∨ _)%I ≡ (_ ∨ _)%I => apply or_proper
  | |- (_ → _)%I ≡ (_ → _)%I => apply impl_proper
  | |- (_ -∗ _)%I ≡ (_ -∗ _)%I => apply wand_proper
  | |- (WP _ @ _ {{ _ }})%I ≡ (WP _ @ _ {{ _ }})%I => apply wp_proper =>?
  | |- (▷ _)%I ≡ (▷ _)%I => apply later_proper
  | |- (□ _)%I ≡ (□ _)%I => apply intuitionistically_proper
  | |- (|={_,_}=> _ )%I ≡ (|={_,_}=> _ )%I => apply fupd_proper
  | |- (_ ∗ _)%I ≡ (_ ∗ _)%I => apply sep_proper
  | |- (inv _ _)%I ≡ (inv _ _)%I => apply (contractive_proper _)
  end.
