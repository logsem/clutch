From clutch.approxis Require Import approxis map list security_aux option.
From clutch.approxis Require Export bounded_oracle prf.
Set Default Proof Using "Type*".

(** PRF security definitions using the variant of q_calls using semantic typing
    instead of bounds checks. **)
Section sem.

  Context `{PRF}.

  Let q_calls := q_calls_poly.

  Definition PRF_real : val :=
    λ:"Q",
      let: "k" := keygen #() in
      let: "lookup" := prf "k" in
      let: "oracle" := q_calls_poly #() #() "Q" "lookup" in
      "oracle".

  Definition PRF_rand : val :=
    λ:"Q",
      let: "lookup" := random_function card_output #() in
      let: "oracle" := q_calls_poly #() #() "Q" "lookup" in
      "oracle".

End sem.
