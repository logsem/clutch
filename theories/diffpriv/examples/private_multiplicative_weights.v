From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.
From clutch.diffpriv.examples Require Import list numeric_sparse_vector_technique.

Section pmw.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

(* In this part, we consider that x is a distribution and is stored in an couple of arrays.
     Each element is of the form: (Edb, Pdb) (we will call it DB)
     where Edp is the array of the databases and Pdb is the array of the probability of each db.
     We assume that queries are of the type DB -> R, and works as the following:
        - Samples an index following the Pdb distribution
        - Executes the query on this db
  *)
  Definition MW : val :=
    λ:"x" "f" "v",
      let: "r" := (if: ("v" >= "f" "x") then (λ:"q", #1 - "f" "q") else "f") in
      (* Need the update *)
      "x".

End pmw.
