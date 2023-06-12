(* A game based security proof of ElGamal encryption, following Rosulek's "The
   Joy of Crypto". *)
From clutch Require Import clutch.
From clutch.examples.crypto Require Import
  mc_val_instances fingroup_val_inj fingroup_val_inj_example
  fingroup_val_inj_ElGamal.



From mathcomp Require ssrnat.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import zmodp finset ssrbool fingroup.fingroup solvable.cyclic.
Set Warnings "notation-overridden,ambiguous-paths".

Set Default Proof Using "Type*".


Definition EG5 :=
  (pk_ots_rnd_ddh (vg:=vg5) (cg:=cgs5) (G := λ Σ H, @cg5 Σ H) (cgg:=cgg5)).

Print Assumptions EG5.
