From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real.
Require Import Reals.RIneq.

Set Default Proof Using "Type*".
#[local] Open Scope R.

(** Approximation sequences *)

Unset Printing Coercions.

(* The nearest integer to z/4 *)
Definition RoundedDiv4 (z : Z) : Z :=
  ((z `rem` 2) + (z `quot` 4))%Z.

Theorem RoundindDiv4_bound {z : Z} : Rabs (IZR (RoundedDiv4 z) - (IZR z / 4)) <= 1/2.
Proof.
Admitted.


(* More negative is more precise *)
Definition ApproxSeq (f : Z → Z) (r : R) : Prop :=
  ∀ (z : Z), Rabs (IZR (f z) * powerRZ 2 z - r) <= powerRZ 2 z.

(* The integer z *)
Definition ApproxZ (z : Z) : Z → Z :=
  fun prec => Z.shiftr z prec.

(* Divide by 2^z, for 0 ≤ z. *)
Definition ApproxScal (f : Z → Z) (z : Z) : Z → Z :=
  fun prec => f (Z.add prec z).

(* Add *)
Definition ApproxAdd (f g : Z → Z) : Z → Z :=
  fun prec => RoundedDiv4 (f (Z.sub prec 2) + g (Z.sub prec 2)).

(* Negate *)
Definition ApproxNeg (f : Z → Z) : Z → Z :=
  fun prec => Z.mul (-1)%Z (f prec).

Lemma ApproxZ_correct {z} : ApproxSeq (ApproxZ z) (IZR z).
Proof.
  rewrite /ApproxSeq/ApproxZ//=.
  intros prec.
  destruct (Z_le_gt_dec prec 0).
  { rewrite (Z.shiftr_mul_pow2 z prec l).
    rewrite mult_IZR Rmult_assoc.
    rewrite -{1}(Z2Nat.id (- prec) ltac:(lia) ).
    rewrite -pow_IZR.
    rewrite pow_powerRZ.
    rewrite -powerRZ_add; [|lra].
    replace (Z.to_nat (- prec) + prec)%Z with 0%Z by lia.
    rewrite powerRZ_O Rmult_1_r.
    rewrite Rminus_diag Rabs_R0.
    apply powerRZ_le; lra.
  }
  { (* Rounding bound *)
    admit. }
Admitted.

Lemma ApproxScal_correct {f r z} : (0 <= z)%Z → ApproxSeq f r → ApproxSeq (ApproxScal f z) (r / powerRZ 2 z).
Proof.
  rewrite /ApproxSeq/ApproxScal//=.
  intros Hz H prec.
  eapply (@Rmult_le_reg_r (powerRZ 2 z)).
  { apply powerRZ_lt; lra. }
  rewrite -powerRZ_add; [|lra].
  rewrite -(Rabs_right (powerRZ 2 z) _).
  2: { apply Rle_ge, powerRZ_le; lra. }
  rewrite -Rabs_mult Rcomplements.Rmult_minus_distr_r.
  rewrite Rdiv_def Rmult_assoc Rmult_assoc.
  rewrite (Rabs_right (powerRZ 2 z) _).
  2: { apply Rle_ge, powerRZ_le; lra. }
  rewrite Rinv_l.
  2: { apply powerRZ_NOR; lra. }
  rewrite Rmult_1_r.
  rewrite -powerRZ_add; [|lra].
  apply H.
Qed.

Lemma ApproxAdd_correct {f g r s} : ApproxSeq f r → ApproxSeq g s → ApproxSeq (ApproxAdd f g) (r + s).
Proof.
  rewrite /ApproxSeq/ApproxAdd//=.
  intros Hf Hg z.
  (* Step 1: bound the rounding error (triangle inequality) *)
  replace (IZR (RoundedDiv4 (f (z - 2)%Z + g (z - 2)%Z)) * powerRZ 2 z - (r + s))
    with  ((IZR (RoundedDiv4 (f (z - 2)%Z + g (z - 2)%Z)) * powerRZ 2 z - IZR (f (z - 2)%Z + g (z - 2)%Z) / 4 * powerRZ 2 z) + (IZR ((f (z - 2)%Z + g (z - 2)%Z)) / 4 * powerRZ 2 z - (r + s)))
    by lra.
  etrans; first eapply Rabs_triang.
  rewrite -{4}(Rmult_1_l (powerRZ 2 z)).
  replace (1 * powerRZ 2 z) with (1/2 * powerRZ 2 z + (1/4 * powerRZ 2 z + 1/4 * powerRZ 2 z)) by lra.
  apply Rplus_le_compat.
  { generalize ((f (z + 2)%Z + g (z + 2)%Z))%Z as A; intros ?.
    rewrite -Rcomplements.Rmult_minus_distr_r.
    rewrite Rabs_mult.
    rewrite (Rabs_right (powerRZ 2 z) _).
    2: { apply Rle_ge, powerRZ_le; lra. }
    apply Rmult_le_compat_r.
    { apply powerRZ_le; lra. }
    apply RoundindDiv4_bound.
  }
  (* Step 2: separate the bound (triangle inequality) *)
  rewrite plus_IZR Rdiv_plus_distr Rmult_plus_distr_r.
  replace (IZR (f (z - 2)%Z) / 4 * powerRZ 2 z + IZR (g (z - 2)%Z) / 4 * powerRZ 2 z - (r + s))
    with  ((IZR (f (z - 2)%Z) / 4 * powerRZ 2 z - r) + (IZR (g (z - 2)%Z) / 4 * powerRZ 2 z - s)) by lra.
  etrans; first eapply Rabs_triang.
  have Hpow : / 4 * powerRZ 2 z = powerRZ 2 (z-2)%Z.
  { replace (z - 2)%Z with (z + Z.opp 2)%Z by lia.
    rewrite powerRZ_add; [|lra].
    rewrite powerRZ_neg' //=.
    lra.
  }
  apply Rplus_le_compat.
  { repeat rewrite Rdiv_def.
    rewrite Rmult_1_l.
    rewrite Rmult_assoc Hpow.
    apply Hf.
  }
  { repeat rewrite Rdiv_def.
    rewrite Rmult_1_l.
    rewrite Rmult_assoc Hpow.
    apply Hg.
  }
Qed.

Lemma ApproxNeg_correct {f r} : ApproxSeq f r → ApproxSeq (ApproxNeg f) (-r).
Proof.
  rewrite /ApproxSeq/ApproxNeg//=.
  intros H z.
  etrans; [|apply H].
  rewrite -Rabs_Ropp.
  right.
  f_equal.
  rewrite mult_IZR.
  lra.
Qed.

(** Programs *)

(* x ^ y where 0 <= y*)
Definition Npow : val :=
  rec: "pow" "x" "y" :=
    if: "y" ≤ #0%nat
      then #(1%nat)
      else "x" * ("pow" "x" ("y" - #1)).

(* Constant functions at integer Z. *)
Definition R_ofZ : val :=
  λ: "vZ",
    λ: "prec", "vZ" * (Npow #2 "prec").


Section Lib.
  Context `{!erisGS Σ}.



  Lemma wp_Npow {x y : Z} {E} : ⌜(0 ≤ y)%Z ⌝ ⊢ WP (Npow #x #y) @ E {{ fun v => ⌜v = #(x ^ y)%Z ⌝ }}.
  Proof.
  Admitted.


  (** Approximation Sequence Proofs *)

  (* The value v refines the function f, optionally preserving an invariant I. *)
  Definition IsSeq (v : val) (f : nat → Z) E (I : iProp Σ) : iProp Σ :=
    □ (∀ (prec : nat), I -∗ WP (v #prec) @ E {{ fun zv => ⌜zv = #(f prec)⌝ ∗ I }})%I.


End Lib.




(*

(* Given two values that behave as (Z → Z), compare them starting from 0. *)
Definition R_cmp : val :=
  λ: "v1" "v2",
  (rec: "cmp_loop" "prec" :=
     let: "z1" := "v1" "prec" in
     let: "z2" := "v2" "prec" in
     if:      "z1" < "z2" then #(-1)
     else if: "z2" < "z1" then #1
                          else "cmp_loop" ("prec" + #1))
  "cmp_loop" #0.


Definition R_addZ : val :=
  λ: "vR" "vZ",
    λ: "prec", (R_ofZ "vZ" "prec") + ("vR" "prec").

(* TODO *)
Definition R_addR : val :=
  λ: "vR1 vR2" ,
    λ: "prec",
      let: "z1" := "vR1" ("prec" + #1) in
      let: "z2" := "vR2" ("prec" + #1) in
      ("z1" + "z2") ≫ #1.

Definition R_neg : val :=
  λ: "vR",
    λ: "prec",  #(-1) * ("vR" "prec").

Definition Z_sgn : val :=
  λ: "vZ", if: "vZ" < #0 then #(-1) else #1.

Definition Z_abs : val :=
  λ: "vZ", (Z_sgn "vZ") * "vZ".

(* Multiplication by repeated addition *)
Definition R_mulZ_nonneg : val :=
  λ: "vR",
    (rec: "loop_pos" "i" :=
       if: "i" = #0
         then R_ofZ #0
         else R_addR "vR" ("loop_pos" ("i" - #1)))
    "loop_pos".

Definition R_mulZ : val :=
  λ: "vR" "z", (Z_sgn "vZ") * R_mulZ_nonneg "vR" (Z_abs "z").

(* Likely some off-by-ones. *)
Definition R_ofRand : val :=
  (rec: "loop" "α" "chnk" "prec" :=
     if: "prec" = #0
       then
         #0
       else
         let: "V" := get_chunk "α" "chnk" in
         let: "r" := "loop" "α" (Snd "V") ("prec" - #1) in
         (Fst "V") * (Zpow #2 "prec") + "r").


(* Specify that a value behaves like a particular function Z → Z
   Then, specify that it behaves like a real number similarly to lazy_real
      R as Z -> Z functions *)

Context `{!erisGS Σ}.

(* TODO: How to specify that a value behaves like a given pure function in Eris?  *)
Definition BehavesAsSequence (v : val) (f : nat → Z) E (I : iProp Σ) : iProp Σ :=
  □ (∀ (prec : nat), I -∗ WP (v #prec) @ E {{ fun zv => ⌜zv = #(f prec)⌝ ∗ I }})%I.




(* Can I prove this using chunk_and_tape_seq for lazy_real? *)
(* It is the case for I = True and the constatnt real... *)

(* Convert between bitstreams and partial power streams

   Partial power streams are how I implemented the above, because they are way easier
   for aruthmetic operations. The way to convert them is to get the n'th digit of the binary
   expansion.

    PPS to BS doesn't really make sense outside of the interval [0, 1].

    This might be easier to specify using the CReal-like interval spec (which works
    on PPS on any range natively) and then prove that the BitStream representation plus a
    lazy_real predicate satisfies that.  *)
Definition BS_to_PPS (bs : nat → (fin 2)) : nat → Z. Admitted.
Definition PPS_to_BS (ps : nat → Z) : nat → (fin 2). Admitted.

Definition BehavesAsLazyReal (v : val) (r : R) E (I : iProp Σ) : iProp Σ :=
  ∃ (z : R) (f : nat → (fin 2)),
    ⌜ r = seq_bin_to_R f ⌝ ∗ (BehavesAsSequence v (BS_to_PPS f) E I).
*)
