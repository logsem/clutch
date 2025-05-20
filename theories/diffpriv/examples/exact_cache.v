From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.
From clutch.diffpriv.examples Require Import list map.

Section xcache.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

  (* SPEC: If M is ε-dp, then exact_cache M qs is ε/k-dp where k = |unique(qs)|. *)
  Definition exact_cache : val :=
    λ:"M" "qs" "db",
      let: "cache" := init_map #() in
      list_fold
        (λ: "acc" "q",
          match: get "cache" "q" with
          | SOME "v" => list_cons "v" "acc"
          | NONE =>
              let: "v" := "M" "q" "db" in
              set "cache" "q" "v" ;;
              list_cons "v" "acc"
          end)
        list_nil "qs".

End xcache.
