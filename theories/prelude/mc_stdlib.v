From Coq Require Import ZArith.
From clutch.prelude Require Import base.

Set Warnings "-hiding-delimiting-key,-overwriting-delimiting-key".
From mathcomp Require Import ssrnat.
Set Warnings "hiding-delimiting-key,overwriting-delimiting-key".
From mathcomp Require Import fintype ssrbool zmodp.

Fact rem_modn (x p : nat) (_ : p <> 0) :
  (Z.rem (Z.of_nat x) (Z.of_nat p))%Z = Z.of_nat (div.modn x p).
Proof.
  rewrite Z.rem_mod => //. 2: lia.
  set (x' := Z.of_nat x). set (p' := Z.of_nat p).
  move hx : x => [|n] .
  { rewrite div.mod0n. lia. }
  rewrite -hx.
  replace (Z.sgn x') with 1%Z by lia.
  replace (Z.abs x') with x' by lia.
  replace (Z.abs p') with p' by lia.
  rewrite Z.mul_1_l.
  rewrite -Nat2Z.inj_mod.
  rewrite {2}(PeanoNat.Nat.div_mod_eq x p).
  set (q := Z.div x' p'). set (r := x mod p).
  rewrite ssrnat.plusE ssrnat.multE ssrnat.mulnC div.modnMDl.
  rewrite div.modn_small ; [reflexivity|].
  unshelve epose proof (PeanoNat.Nat.mod_upper_bound x p _) ; [lia|].
  apply /leP ; lia.
Qed.

Fact leq_zmodp p'' : ∀ (x : 'Z_(S (S p''))), @nat_of_ord (S (S p'')) x ≤ S (S p'').
Proof. rewrite ?Zp_cast // ; intros. move /leP : (leq_ord x). lia. Qed.
