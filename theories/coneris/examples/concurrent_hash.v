From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris par spawn spin_lock hash lock.

Set Default Proof Using "Type*".

Section concurrent_hash.
  Variable val_size : nat.
  Variable insert_num : nat.
  Variable max_hash_size : nat.
  Hypothesis max_hash_size_pos: (0<max_hash_size)%nat.

  Context {Hineq : (insert_num <= max_hash_size)%nat}.

  Local Existing Instance spin_lock.
  
  Definition hash_once_prog : val :=
    λ: "h" "lock" "_",
      acquire "lock";;
      "h" (rand #val_size)
      release "lock"
  .

  Definition multiple_parallel : val :=
    rec: "multiple_parallel" "num" "f" :=
      if: "num" ≤ #0 then #() else
       "f" #() ||| "multiple_parallel" ("num"-#1) "f"
  .

  Definition concurrent_hash_prog : expr :=
    let: "h" := init_hash val_size #() in
    let: "lock" := newlock #() in
    multiple_parallel #insert_num (hash_once_prog "h" "lock");;
    "h".

  Context `{!conerisGS Σ, !spawnG Σ}.

  Lemma concurrent_hash_spec :
    {{{ True }}}
      concurrent_hash_prog
      {{{ (f:val), RET f; ∃ m, inv nroot (coll_free_hashfun_amortized val_size max_hash_size f m)}}}.
  Proof.
  Admitted.
  
End concurrent_hash.
