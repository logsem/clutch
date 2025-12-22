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
  ((z `quot` 4) + ((z `rem` 4) `quot` 2))%Z.

Theorem RoundindDiv4_bound {z : Z} : Rabs (IZR (RoundedDiv4 z) - (IZR z / 4)) <= 1/2.
Proof.
  unfold RoundedDiv4.
  set (q := Z.quot z 4).
  set (r := Z.rem z 4).
  assert (z = 4 * q + r)%Z as Hdiv.
  { subst q r; apply Z.quot_rem'; lia. }
  assert (-4 < r < 4)%Z as Hbound.
  { subst r. assert (Z.abs (z `rem` 4) < 4)%Z; [apply Z.rem_bound_abs; lia | lia]. }
  rewrite Hdiv.
  rewrite plus_IZR.
  replace (IZR (4 * q + r) / 4) with (IZR q + IZR r / 4) by (rewrite plus_IZR mult_IZR; lra).
  replace (IZR q + IZR (r ÷ 2) - (IZR q + IZR r / 4)) with (IZR (r ÷ 2) - IZR r / 4) by lra.
  assert (r = -3 \/ r = -2 \/ r = -1 \/ r = 0 \/ r = 1 \/ r = 2 \/ r = 3)%Z as Hcases by lia.
  destruct Hcases as [Hr|[Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]]].
  1: rewrite Hr; vm_compute; destruct Rcase_abs; lra.
  all: rewrite Hr; vm_compute; destruct Rcase_abs; lra.
Qed.


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
    assert (0 <= prec)%Z as Hprec by lia.
    rewrite (Z.shiftr_div_pow2 z prec Hprec).
    set (q := (z / 2 ^ prec)%Z).
    set (r := (z mod 2 ^ prec)%Z).
    assert (z = (2 ^ prec * q + r))%Z as Hdiv.
    { subst q r. pose proof (Z_div_mod_eq_full z (2 ^ prec)). lia. }
    assert (0 <= r < 2 ^ prec)%Z as Hbound.
    { subst r. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
    rewrite Hdiv.
    rewrite plus_IZR mult_IZR.
    replace (IZR (2 ^ prec)) with (powerRZ 2 prec).
    2: { symmetry. replace (2 ^ prec)%Z with (Zpower_nat 2 (Z.abs_nat prec)) by (rewrite Zpower_nat_Zpower; [reflexivity|lia]). rewrite Zpower_nat_powerRZ_absolu; [|lia]. simpl. reflexivity. }
    replace (IZR q * powerRZ 2 prec - (powerRZ 2 prec * IZR q + IZR r)) with (- IZR r) by lra.
    rewrite Rabs_Ropp Rabs_right.
    2: { apply Rle_ge. replace 0 with (IZR 0) by reflexivity. apply IZR_le. lia. }
    replace (powerRZ 2 prec) with (IZR (2 ^ prec)).
    2: { symmetry. replace (2 ^ prec)%Z with (Zpower_nat 2 (Z.abs_nat prec)) by (rewrite Zpower_nat_Zpower; [reflexivity|lia]). rewrite Zpower_nat_powerRZ_absolu; [|lia]. simpl. reflexivity. }
    apply IZR_le. lia.
  }
Qed.

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
Definition VDiv4Rounded : val :=
  λ: "z", (("z" `quot` #4) + (("z" `rem` #4) `quot` #2)).

Definition R_ofZ : val :=
  λ: "vZ",
    λ: "prec", ("vZ" ≫ "prec").

Definition R_mulPow : val :=
  λ: "f" "vZ",
    λ: "prec", "f" ("vZ" + "prec").

Definition R_plus : val :=
  λ: "f" "g",
    λ: "prec", VDiv4Rounded ("f" ("prec" - #2) + "g" ("prec" - #2)).

Definition R_neg : val :=
  λ: "f",
    λ: "prec", #(- 1) * "f" "prec".


Section Lib.
  Context `{!erisGS Σ}.

  Lemma wp_Npow {x y : Z} {E} : ⌜(0 ≤ y)%Z ⌝ ⊢ WP (Npow #x #y) @ E {{ fun v => ⌜v = #(x ^ y)%Z ⌝ }}.
  Proof.
  Admitted.

  Lemma wp_VDiv4Rounded {z : Z} {E} :
    ⊢ WP (VDiv4Rounded #z) @ E {{ fun v => ⌜v = #(RoundedDiv4 z) ⌝}}.
  Proof. rewrite /VDiv4Rounded/RoundedDiv4. wp_pures. done. Qed.


  (** Approximation Sequence Proofs *)

  (* The value v refines the function f, optionally preserving an invariant I. *)
  Definition IsSeq (v : val) (f : Z → Z) E (I : iProp Σ) : iProp Σ :=
    □ (∀ (prec : Z), I -∗ WP (v #prec) @ E {{ fun zv => ⌜zv = #(f prec)⌝ ∗ I }})%I.

  Lemma wp_R_ofZ {z : Z} {E} :
    ⊢ WP (R_ofZ #z) @ E {{ fun cont => IsSeq cont (ApproxZ z) E True}}.
  Proof.
    rewrite /R_ofZ.
    wp_pures.
    rewrite /IsSeq.
    iModIntro.
    iModIntro.
    iIntros (??).
    wp_pures.
    iModIntro.
    iSplitL; done.
  Qed.

  Lemma wp_R_mulPow {vf : val} {f E I} {z : Z} :
    IsSeq vf f E I ⊢ WP (R_mulPow vf #z) @ E {{ fun cont => IsSeq cont (ApproxScal f z) E I}}.
  Proof.
    iIntros "#Hcont".
    rewrite /R_mulPow/IsSeq/ApproxScal//=.
    wp_pures.
    iModIntro.
    iModIntro.
    iIntros (?) "HI".
    rewrite (Z.add_comm prec).
    wp_pures.
    by iApply "Hcont".
  Qed.

  Lemma wp_R_neg {vf : val} {f E I} :
    IsSeq vf f E I ⊢ WP (R_neg vf) @ E {{ fun cont => IsSeq cont (ApproxNeg f) E I}}.
  Proof.
    iIntros "#Hcont".
    rewrite /R_neg/IsSeq/ApproxNeg.
    wp_pures.
    iModIntro.
    iModIntro.
    iIntros (?) "HI".
    wp_pures.
    wp_bind (vf _).
    iApply pgl_wp_mono.
    2: { by iApply ("Hcont" with "[HI]"). }
    iIntros (?) "[-> ?]".
    wp_pures.
    iModIntro.
    iFrame.
    done.
  Qed.

  Lemma wp_R_plus {vf vg : val} {f g E If Ig}  :
    IsSeq vf f E If ∗ IsSeq vg g E Ig ⊢
      WP (R_plus vf vg) @ E {{ fun cont => IsSeq cont (ApproxAdd f g) E (If ∗ Ig)}}.
  Proof.
    iIntros "[#Hf #Hg]".
    rewrite /R_plus/IsSeq/ApproxAdd//=/VDiv4Rounded//=/RoundedDiv4//=.
    wp_pures.
    iModIntro.
    iModIntro.
    iIntros (prec) "[HIf HIg]".
    wp_pures.
    wp_bind (vg _).
    (* Yikes *)
    iApply (pgl_wp_mono_frame
            ((□ ∀ prec0 : Z, If -∗ WP vf #prec0 @ E {{ zv, ⌜zv = #(f prec0)⌝ ∗ If }})
              ∗ (□ ∀ prec0 : Z, Ig -∗ WP vg #prec0 @ E {{ zv, ⌜zv = #(g prec0)⌝ ∗ Ig }})
              ∗ If)
             with "[HIg] [HIf Hf Hg]").
    2: { by iApply ("Hg" with "[HIg]"). }
    2: { iSplitR; [|iSplitR]; iFrame; done. }
    iIntros (?) "[[#Hf [#Hg HIf]] [-> HIg]]".
    wp_pures.
    wp_bind (vf _).
    iApply (pgl_wp_mono_frame
            ((□ ∀ prec0 : Z, If -∗ WP vf #prec0 @ E {{ zv, ⌜zv = #(f prec0)⌝ ∗ If }})
              ∗ (□ ∀ prec0 : Z, Ig -∗ WP vg #prec0 @ E {{ zv, ⌜zv = #(g prec0)⌝ ∗ Ig }})
              ∗ Ig)
             with "[HIf] [HIg Hg Hf]").
    2: { by iApply ("Hf" with "[HIf]"). }
    2: { iSplitR; [|iSplitR]; iFrame; done. }
    iIntros (?) "[[#Hf [#Hg HIf]] [-> HIg]]".
    wp_pures.
    iModIntro.
    iFrame.
    done.
  Qed.

  (* TODO Compare two CReal numbers *)
  (* TODO: Lift a lazy real to A CReal real *)

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
