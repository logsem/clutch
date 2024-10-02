From clutch.approxis Require Import approxis map list security_aux option.
From clutch.approxis Require Export bounded_oracle prf.
Set Default Proof Using "Type*".

(** PRF security definitions using the variant of q_calls with explicit bounds
    checks in the code. **)

Section bound_checks.

  Context `{PRF}.

  (* Variable Key Input Output : nat.

     Let keygen PRF_scheme : expr := Fst PRF_scheme.
     Let prf PRF_scheme : expr := Fst (Snd PRF_scheme).
     Let rand_output PRF_scheme : expr := Snd (Snd PRF_scheme). *)

  Let q_calls := q_calls card_input.

  Definition PRF_real_rand : val :=
    λ:"b" "adv" "PRF_scheme" "Q",
      let: "key" := keygen "PRF_scheme" #() in
      let: "prf_key_b" :=
        if: "b" then
          prf "PRF_scheme" "key"
        else
          random_function "key" in
      let: "oracle" := q_calls "Q" "prf_key_b" in
      let: "b'" := "adv" "oracle" in
      "b'".

  Definition wPRF : val :=
    λ:"b" "PRF_scheme" "Q",
      let: "key" := keygen "PRF_scheme" #() in
      let: "prf_key_b" :=
        if: "b" then
          prf "PRF_scheme" "key"
        else
          random_function "key" in
      let: "res" := ref list_nil in
      letrec: "loop" "i" :=
          if: "i" = #0 then #() else
            let: "x" := rand #card_input in
            let: "y" := "prf_key_b" "x" in
            "res" <- list_cons ("x", "y") (!"res") ;;
            "loop" ("i" - #1)
      in
      ("loop" "Q") ;;
      ! "res".

  (* Rosulek, Def. 6.1 (PRF security) *)
  (* NB: Rosulek samples the key from {0,1}^λ, we sample it from [0,card_key]. *)
  Definition PRF_real : val :=
    λ:"PRF_scheme" "Q",
      let: "k" := keygen "PRF_scheme" #() in
      let: "lookup" := prf "PRF_scheme" "k" in
      let: "oracle" := q_calls "Q" "lookup" in
      "oracle".

  Definition PRF_rand : val :=
    λ:"PRF_scheme" "Q",
      let: "lookup" := random_function #() in
      let: "oracle" := q_calls "Q" "lookup" in
      "oracle".

End bounds_check.
