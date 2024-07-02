From clutch Require Import lib.flip.
From clutch.paris Require Import paris map list.
Set Default Proof Using "Type*".


Section bounded_oracle.
  Local Opaque INR.

  (** Bounded Oracles. [q_calls MAX Q f x] calls [f x] for the first [Q] invocations
      if 0 <= x <= MAX, and returns None otherwise. *)
  Definition q_calls (MAX : Z) : val :=
    λ:"Q" "f",
      let: "counter" := ref #0 in
      λ:"x", if: (BinOp AndOp (! "counter" < "Q") (BinOp AndOp (#0 ≤ "x") ("x" ≤ #MAX)))
             then ("counter" <- !"counter" + #1 ;; SOME ("f" "x"))
             else NONEV.
End bounded_oracle.
