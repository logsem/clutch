From clutch.approxis Require Import approxis map list security_aux.
From clutch.approxis Require Export bounded_oracle.
Set Default Proof Using "Type*".

Class XOR {Key Support : nat} :=
  { xor : val
  ; xor_sem : nat → nat → nat
  ; xor_bij x : Bij (xor_sem x)
  ; xor_dom x : x < S Key -> (∀ n : nat, n < S Support → xor_sem x n < S Support)

  ; TKey := TInt
  ; TInput := TNat
  ; TOutput := TNat

  (* TODO: should xor be partial? `xor key input` may fail unless 0 <= key <=
     Key /\ 0 <= input <= Input

     If xor were to operate on strings / byte arrays / bit lists instead, it
     may fail if `key` and `input` are of different lengths. *)

  } .

Class XOR_spec `{!approxisRGS Σ} `{XOR} :=
  { XOR_CORRECT_L := ∀ E K (x : Z) (y : nat)
                       (_: (0<=x)%Z)
                       (_: ((Z.to_nat x) < S Key))
                       (_: y < S Key) e A,
      (REL (fill K (of_val #(xor_sem (Z.to_nat x) (y)))) << e @ E : A)
      -∗ REL (fill K (xor #x #y)) << e @ E : A
  ; XOR_CORRECT_R := ∀ E K (x : Z) (y : nat)
                       (_: (0<=x)%Z)
                       (_: ((Z.to_nat x) < S Key))
                       (_: y < S Key) e A,
      (REL e << (fill K (of_val #(xor_sem (Z.to_nat x) (y)))) @ E : A)
      -∗ REL e << (fill K (xor #x #y)) @ E : A
  ; xor_correct_l : XOR_CORRECT_L
  ; xor_correct_r : XOR_CORRECT_R
  ; xor_sem_typed :
    ⊢ (lrel_int_bounded 0 Key → lrel_int_bounded 0 Support → lrel_int_bounded 0 Support)%lrel
        xor xor
  }.

(* Definition XOR_CORRECT_L := forall `{!approxisRGS Σ} E K (x : Z) (y : nat)
                                (_: (0<=x)%Z)
                                (_: ((Z.to_nat x) < S Key))
                                (_: y < S Key) e A,
       (REL (fill K (of_val #(xor_sem (Z.to_nat x) (y)))) << e @ E : A)
       -∗ REL (fill K (xor #x #y)) << e @ E : A.


     Definition XOR_CORRECT_R := ∀ `{!approxisRGS Σ} E K (x : Z) (y : nat)
                                (_: (0<=x)%Z)
                                (_: ((Z.to_nat x) < S Key))
                                (_: y < S Key) e A,
       (REL e << (fill K (of_val #(xor_sem (Z.to_nat x) (y)))) @ E : A)
       -∗ REL e << (fill K (xor #x #y)) @ E : A.

     (* Variable xor : val.
        (** Parameters of the generic PRF-based encryption scheme. *)
        Variable (xor_sem : nat -> nat -> nat).
        Variable H_xor : forall x, Bij (xor_sem x).
        Variable H_xor_dom: forall x, x < S Key -> (∀ n : nat, n < S Input → xor_sem x n < S Output). *)


     Variable (xor_correct_l: XOR_CORRECT_L).
     Variable (xor_correct_r: XOR_CORRECT_R).

     Definition TKey := TNat.
     Definition TInput := TNat.
     Definition TOutput := TNat.

     (* TODO: should xor be partial? `xor key input` may fail unless 0 <= key <=
        Key /\ 0 <= input <= Input

        If xor were to operate on strings / byte arrays / bit lists instead, it
        may fail if `key` and `input` are of different lengths. *)
     Hypothesis xor_typed : (⊢ᵥ xor : (TKey → TInput → TOutput)). *)
