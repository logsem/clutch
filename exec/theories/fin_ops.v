(** * Finite value types and a PRF for the executable SKE instances

    The integers [0..N-1] as a finite value type: a value is its own
    index.  The class [fin_val_type] computes its cardinality from a
    mathcomp [finType]; the executable instances are built in OCaml with a
    descriptor of the type in place of the [finType], and the extraction
    realises [card] (and [prod_fvt], [vg_fvt]) on these descriptors
    ([exec/extract/exec_fin.ml]). *)
From clutch.prob_eff_lang.probblaze Require Import syntax notation.

Definition fin_int_of : val := λ: "x", "x".

Definition fin_of_int (N : nat) : val :=
  λ: "i", if: (#0 ≤ "i") && ("i" < #N) then SOME "i" else NONE.

(** A keyed function into [0..N-1]: [prf k x = (k · x + k) mod N]; keys
    are group elements (integers), nonces integers.  It is far from
    pseudorandom, which the PRF games detect. *)
Definition toy_prf (N : nat) : val := λ: "k" "x", ("k" * "x" + "k") `rem` #N.
