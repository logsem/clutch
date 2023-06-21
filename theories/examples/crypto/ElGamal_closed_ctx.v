From clutch Require Import clutch.
From clutch.examples.crypto Require Import valgroup_Zp ElGamal.

#[local] Definition p := 2^1000 - 1.

Definition EG_p := pk_ots_rnd_ddh (G:=@cg_p p) (cgg:=cgg_p p).

(* Print Assumptions EG_p. *)
