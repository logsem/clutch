From stdpp Require Import namespaces.
From iris.base_logic Require Import invariants na_invariants.
From self.prob_lang Require Import notation proofmode primitive_laws spec_rules spec_tactics.
From self.logrel Require Import model rel_rules rel_tactics.
From iris.algebra Require Import auth gmap excl frac agree.
From self.prelude Require Import base.
From self.examples Require Import keyed_hash.

Set Default Proof Using "Type*".

(* A "splittable" pseudo-random number generator derived from a keyed
   hashing function.

   The idea is to be able to generate a collection of separate independent RNGs from a single keyed hash
   by having each RNG use a different key.

   Compare with rng.v, which generates a single rng from a hash function.

*)


Section rng.

  Context (MAX_RNGS_POW : nat).
  Context (MAX_SAMPLES_POW : nat).

  Definition MAX_RNGS : nat := (Nat.pow 2 MAX_RNGS_POW) - 1.
  Definition MAX_SAMPLES : nat := (Nat.pow 2 MAX_SAMPLES_POW) - 1.

  Definition init_rng_gen : val :=
    λ: "_",
      let: "f" := (init_keyed_hash MAX_RNGS_POW MAX_SAMPLES_POW) in
      let: "key_cntr" := ref #0 in
      (* We return an rng "generator" that gets a fresh key from key_cntr (if available) and returns
         an rng function using that key *)
      λ: "_",
        let: "k" := !"key_cntr" in
        if: #MAX_RNGS < "k" then
          NONEV
        else
          "key_cntr" <- "k" + #1;;
          let: "sample_cntr" := ref #0 in
          (λ: "_",
            let: "v" := !"sample_cntr" in
            if: #MAX_SAMPLES < "v" then
              #false
            else
              let: "b" := "f" "k" "v" in
              "sample_cntr" <- "v" + #1;;
              "b").

  Context `{!prelogrelGS Σ}.


End rng.
