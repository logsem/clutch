From clutch Require Import lib.flip.
From clutch.paris Require Import paris map list.
Set Default Proof Using "Type*".


Section bounded_oracle.
  Local Opaque INR.

  (** Bounded Oracles *)
  Definition q_calls (MAX : Z) : val :=
    λ:"Q" "f" "g",
      let: "counter" := ref #0 in
      λ:"x", if: (BinOp AndOp (! "counter" < "Q") (BinOp AndOp (#0 ≤ "x") ("x" < #MAX)))
             then ("counter" <- !"counter" + #1 ;; "f" "x")
             else "g" "x".
End bounded_oracle.
