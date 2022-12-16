(* Example taken from Sangiorgi and Vignudelli's "Environmental Bisimulations
   for Probabilistic Higher-order Languages".

NB: This example was mentioned as open problem in Aleš's thesis.
 *)

From stdpp Require Import namespaces.
From iris.base_logic Require Import invariants na_invariants.
From self.prelude Require Import base.
From self.prob_lang Require Import notation proofmode primitive_laws.
From self.logrel Require Import model rel_rules rel_tactics.

(* A diverging term. *)
Definition Ω : expr := rec: "Ω" "v" := "Ω" "v".

(* We'll have to think about where exactly the tape allocation should happen
   once we get to the proof. *)
Definition pchoice e1 e2 : expr :=
  if: flip "α" then e1 else e2.

Infix "⊕" := pchoice (at level 80) : expr_scope.

Definition M : expr :=
  if: !"x" = #0 then "x" <- #1 ;; #true else Ω.

Definition N : expr :=
  if: !"x" = #0 then "x" <- #1 ;; #false else Ω.

Definition H : expr :=
  let: "x" := ref #0 in
  (λ:<>, M ⊕ N).

Definition K : expr :=
  let: "x" := ref #0 in
  (λ:<>, M) ⊕ (λ:<>, N).

Section proofs.
  Context `{!prelogrelGS Σ}.
  Context `{!lockG Σ}.

  Definition bisimN := nroot.@"bisim".

  Lemma HK :
    ⊢ REL H << K : lrel_unit → lrel_bool.
  Admitted.

  Lemma KH :
    ⊢ REL H << K : lrel_unit → lrel_bool.
  Admitted.

End proofs.
