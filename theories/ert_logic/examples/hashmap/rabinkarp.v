(** * Rabin Karp string detection *)
From clutch.ert_logic Require Export expected_time_credits ert_weakestpre problang_wp proofmode
  derived_laws cost_models ert_rules.
From clutch.prob_lang Require Import notation tactics metatheory lang.
From iris.proofmode Require Export proofmode.
From Coq Require Export Reals Psatz.
From Coquelicot Require Export Hierarchy.
Require Import Lra.
From clutch.ert_logic.examples.hashmap Require Export hash.
From clutch.ert_logic.examples.lib Require Export list.


Set Default Proof Using "Type*".

Section rabin_karp.

  Context`{!ert_clutchGS Σ CostTick}.

  Variable ascii_size:nat.

  Definition rk_helper : val :=
    (rec: "helper" "s" "p" "hf" "lp" "hp" "idx":=
       if: "idx" < list_length "s" - "lp" + #1
       then
         let: "w":= list_inf "idx" ("idx"+"lp") "s" in
         let: "h":= "hf" "w" in
         tick #1 ;;
         if: "h" = "hp"
         then if: (tick "lp";; "w" = "p")
              then SOME "idx"
              else "helper" "s" "p" "hf" "lp" "hp" ("idx" + #1)
         else "helper" "s" "p" "hf" "lp" "hp" ("idx" + #1)
       else NONE
    ).

  Definition rk : val :=
    λ: "s" "p" "hf",
      let: "lp" := list_length "p" in
      let: "hp" := "hf" "p" in
      match: rk_helper "s" "p" "hf" "lp" "hp" #0
      with
      | SOME "x" => "x"
      | NONE => #(-1)
      end
  .
  
  
End rabin_karp.
