(* Group arithmetic for the oblivious transfer of [ot.v]: the bijections
   on exponents that the security proof couples along, and what they do to
   the reference string and to a ciphertext.

   Everything is stated on group elements [g ^+ k] for natural numbers [k]
   below the group order [n], which must be prime.  The underlying facts
   about the field of exponents are those of [examples/ot/ot_bijection.v]. *)

From Stdlib Require Import Lia.
From stdpp Require Import base fin.
From clutch.prelude Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import valgroup.
From clutch.prob_eff_lang.probblaze.examples.ot Require Import ot_bijection ot_common.
From mathcomp Require Import ssreflect ssrbool eqtype choice fintype.
From mathcomp Require ssrnat div prime zmodp ssralg.
Import fingroup.
Import fingroup.fingroup.
Import cyclic.
Import zmodp.
Import ssralg.

#[local] Set Default Proof Using "All".
Set Implicit Arguments.
Unset Strict Implicit.

Section ot_arith.
  Context {vg : val_group} {vgg : @val_group_generator vg}.

  #[local] Notation n := (S (S n'')).
  Context (n_prime : is_true (prime.prime n)).

  #[local] Notation "a ≡ b" := (div.modn a n = div.modn b n) (at level 70).
  #[local] Open Scope group_scope.

  (* A number below [n] as an element of [fin n], the form in which
     [ot_bijection.v] takes exponents. *)
  Lemma below_fin (a : nat) : a ≤ S n'' → ∃ k : fin n, a = fin_to_nat k.
  Proof.
    move=> Ha. have H : (a < n)%nat by lia.
    exists (nat_to_fin H). by rewrite fin_to_nat_to_fin.
  Qed.

  Lemma ssr_lt (a : nat) : a ≤ S n'' → is_true (ssrnat.leq (S a) n).
  Proof. move=> Ha. apply/ssrnat.ltP. lia. Qed.

  (* Every group element is a power of the generator. *)
  Lemma log_g_nat (x : vgG) : ∃ k : nat, k ≤ S n'' ∧ x = g ^+ k.
  Proof.
    destruct (log_g x) as [k ->]. exists (fin_to_nat k). split; last done.
    pose proof (fin_to_nat_lt k). lia.
  Qed.

  (* Exponents that agree modulo the order. *)
  Lemma expg_eq_mod (a b : nat) : a ≡ b → g ^+ a = g ^+ b.
  Proof. move=> H. apply/eqP. rewrite eq_expg_mod_order g_nontriv. by apply/eqP. Qed.

  Lemma expg_eq_mod_inv (a b : nat) : g ^+ a = g ^+ b → a ≡ b.
  Proof. move/eqP. rewrite eq_expg_mod_order g_nontriv. by move/eqP. Qed.

  (* An exponent as an element of the field of order [n]. *)
  Definition expF (a : nat) : 'F_n := (GRing.one 'F_n *+ a)%R.

  Lemma expF_nz (a : nat) : a ≤ S n'' → a ≠ 0%nat → is_true (expF a != 0%R).
  Proof.
    move=> Ha Hnz. apply/eqP => H.
    have Hnat := f_equal (@fintype.nat_of_ord _) H.
    rewrite /expF /= Zp_nat /= in Hnat.
    have Hfp : S (S (Zp_trunc (prime.pdiv n))) = n by rewrite Fp_cast.
    rewrite Hfp div.modn_small in Hnat; first done.
    apply/ssrnat.ltP. lia.
  Qed.

  Lemma expF_nz_unit (a : nat) : a ≤ S n'' → g ^+ a ≠ 1 → is_true (expF a != 0%R).
  Proof. move=> Ha Hk. apply: expF_nz; first done. move=> Hk'. apply: Hk. by rewrite Hk' expg0. Qed.

  (* ---------------------------------------------------------------- *)
  (* The trapdoor.                                                      *)
  (* ---------------------------------------------------------------- *)

  (* [trap a t] is the exponent [t / a]: for a generator [g ^+ a] of the
     reference string, [(g ^+ a) ^+ trap a t = g ^+ t]. *)
  Definition trap (a : nat) : nat → nat := f_ring (expF a).
  (* Its inverse, [t * a]. *)
  Definition untrap (a : nat) : nat → nat := h_ring (expF a).

  Lemma trap_bij (a : nat) : a ≤ S n'' → a ≠ 0%nat → Bij (trap a).
  Proof. move=> Ha Hnz. exact: (f_bij_ring (n_prime := n_prime) (Hnz := expF_nz Ha Hnz) (expF a)). Qed.

  Lemma trap_le (a t : nat) : t ≤ S n'' → trap a t ≤ S n''.
  Proof.
    move=> /ssr_lt Ht. have /ssrnat.ltP H := @f_lt_ring _ n_prime (expF a) _ Ht.
    rewrite /trap. lia.
  Qed.

  Lemma untrap_le (a t : nat) : t ≤ S n'' → untrap a t ≤ S n''.
  Proof.
    move=> /ssr_lt Ht. have /ssrnat.ltP H := @h_lt_ring _ n_prime (expF a) _ Ht.
    rewrite /untrap. lia.
  Qed.

  Lemma trap_exp (a t : nat) :
    a ≤ S n'' → a ≠ 0%nat → t ≤ S n'' → g ^+ a ^+ trap a t = g ^+ t.
  Proof.
    move=> Ha Hnz Ht. rewrite -expgM. apply: expg_eq_mod.
    have Hnz' := expF_nz Ha Hnz. move: Ha Hnz' => /below_fin [k ->] Hnz'.
    exact: (@crs_fin_cancel _ n_prime k t Hnz' (ssr_lt Ht)).
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Masking a ciphertext.                                              *)
  (* ---------------------------------------------------------------- *)

  (* A ciphertext of [m] under the key [(g ^+ a, g ^+ t, g ^+ ku, g ^+ kv)]
     with randomness [r], [s] is
       [(g ^+ a ^+ r * g ^+ t ^+ s,  m * (g ^+ ku ^+ r * g ^+ kv ^+ s))].
     When the key is not degenerate, the ciphertext of [g ^+ km] with
     randomness [r], [s] is the ciphertext of the dummy [g ^+ 1] with
     randomness [mask_r r], [mask_s s]. *)
  Definition nondeg (a t ku kv : nat) : Prop :=
    is_true (expF a * expF kv - inZp t * expF ku != Zp0)%R.

  Definition mask_r (a t km ku kv : nat) : nat → nat :=
    minus_ring (c1' (zmodp.inZp t) (expF a) (expF km) (expF ku) (expF kv)).
  Definition mask_s (a t km ku kv : nat) : nat → nat :=
    plus_ring (c2' (zmodp.inZp t) (expF a) (expF km) (expF ku) (expF kv)).

  Lemma mask_r_bij a t km ku kv : Bij (mask_r a t km ku kv).
  Proof. exact: (minus_ring_bij (n_prime := n_prime)). Qed.
  Lemma mask_s_bij a t km ku kv : Bij (mask_s a t km ku kv).
  Proof. exact: (plus_bij_ring (n_prime := n_prime)). Qed.

  Lemma mask_r_le a t km ku kv (r : nat) : r ≤ S n'' → mask_r a t km ku kv r ≤ S n''.
  Proof.
    move=> /ssr_lt Hr. rewrite /mask_r. set k := c1' _ _ _ _ _.
    have /ssrnat.ltP H := @minus_ring_lt _ n_prime k _ Hr. lia.
  Qed.
  Lemma mask_s_le a t km ku kv (s : nat) : s ≤ S n'' → mask_s a t km ku kv s ≤ S n''.
  Proof.
    move=> /ssr_lt Hs. rewrite /mask_s. set k := c2' _ _ _ _ _.
    have /ssrnat.ltP H := @plus_ring_lt _ n_prime k _ Hs. lia.
  Qed.

  Lemma mask_fst a t km ku kv (r s : nat) :
    a ≤ S n'' → km ≤ S n'' → ku ≤ S n'' → kv ≤ S n'' → r ≤ S n'' → s ≤ S n'' →
    g ^+ a ^+ r * g ^+ t ^+ s
    = g ^+ a ^+ mask_r a t km ku kv r * g ^+ t ^+ mask_s a t km ku kv s.
  Proof.
    move=> /below_fin [a' ->] /below_fin [km' ->] /below_fin [ku' ->] /below_fin [kv' ->] Hr Hs.
    rewrite -!expgM -!expgnDr. apply: expg_eq_mod. symmetry.
    exact: (@enc_fin_cancel1 _ n_prime t a' km' ku' kv' r s (ssr_lt Hr) (ssr_lt Hs)).
  Qed.

  Lemma mask_snd a t km ku kv (r s : nat) :
    a ≤ S n'' → km ≤ S n'' → ku ≤ S n'' → kv ≤ S n'' → r ≤ S n'' → s ≤ S n'' →
    nondeg a t ku kv →
    g ^+ km * (g ^+ ku ^+ r * g ^+ kv ^+ s)
    = g ^+ 1 * (g ^+ ku ^+ mask_r a t km ku kv r * g ^+ kv ^+ mask_s a t km ku kv s).
  Proof.
    move=> /below_fin [a' ->] /below_fin [km' ->] /below_fin [ku' ->] /below_fin [kv' ->] Hr Hs Hnd.
    rewrite -!expgM -!expgnDr !ssrnat.addnA. apply: expg_eq_mod. symmetry.
    exact: (@enc_fin_cancel2 _ n_prime t a' km' ku' kv' r s Hnd (ssr_lt Hr) (ssr_lt Hs)).
  Qed.

  (* The key of slot [1] is not degenerate when the receiver's message
     opens slot [0] and the two trapdoors differ ... *)
  Lemma nondeg_other (a0 a1 t0 t1 ku kv : nat) :
    a0 ≤ S n'' → a0 ≠ 0%nat → a1 ≤ S n'' → t0 ≤ S n'' → t1 ≤ S n'' →
    ku ≤ S n'' → kv ≤ S n'' →
    g ^+ ku ≠ 1 →
    g ^+ kv = g ^+ ku ^+ trap a0 t0 →
    t1 ≠ untrap a1 (trap a0 t0) →
    nondeg a1 t1 ku kv.
  Proof.
    move=> Ha0 Hnz Ha1 Ht0 Ht1 Hku Hkv Hu Hv Hne.
    have Hnz0 := expF_nz Ha0 Hnz. have Hnzu := expF_nz_unit Hku Hu.
    have {Hv} Hv : kv ≡ ssrnat.muln ku (trap a0 t0).
    { apply: expg_eq_mod_inv. by rewrite Hv -expgM. }
    move: Ha0 Ha1 Hku Hkv Hnz0 Hnzu Hv Hne
      => /below_fin [a0' ->] /below_fin [a1' ->] /below_fin [ku' ->] /below_fin [kv' ->]
         Hnz0 Hnzu Hv Hne.
    exact: (@enc_nondeg_other _ n_prime a0' a1' ku' kv' t0 t1 (ssr_lt Ht0) (ssr_lt Ht1) Hnz0 Hnzu Hv Hne).
  Qed.

  (* ... and the key of slot [0] is not degenerate when the receiver's
     message does not open it. *)
  Lemma nondeg_self (a0 t0 ku kv : nat) :
    a0 ≤ S n'' → a0 ≠ 0%nat → t0 ≤ S n'' → ku ≤ S n'' → kv ≤ S n'' →
    g ^+ kv ≠ g ^+ ku ^+ trap a0 t0 →
    nondeg a0 t0 ku kv.
  Proof.
    move=> Ha0 Hnz Ht0 Hku Hkv Hv.
    have Hnz0 := expF_nz Ha0 Hnz.
    have {Hv} Hv : ¬ (kv ≡ ssrnat.muln ku (trap a0 t0)).
    { move=> Hc. apply: Hv. rewrite -expgM. exact: expg_eq_mod. }
    move: Ha0 Hku Hkv Hnz0 Hv => /below_fin [a0' ->] /below_fin [ku' ->] /below_fin [kv' ->] Hnz0 Hv.
    exact: (@enc_nondeg_self _ n_prime a0' ku' kv' t0 (ssr_lt Ht0) Hnz0 Hv).
  Qed.

End ot_arith.

(* The bounds in the form the coupling rules take them. *)
Section ot_arith_lt.
  Context {vg : val_group} {vgg : @val_group_generator vg}.
  #[local] Notation n := (S (S n'')).
  Context (n_prime : is_true (prime.prime n)).

  Lemma trap_lt a (t : nat) : (t < n)%nat → (trap a t < n)%nat.
  Proof. move=> Ht. have := @trap_le _ _ n_prime a t. lia. Qed.
  Lemma untrap_lt a (t : nat) : (t < n)%nat → (untrap a t < n)%nat.
  Proof. move=> Ht. have := @untrap_le _ _ n_prime a t. lia. Qed.
  Lemma mask_r_lt a t km ku kv (r : nat) : (r < n)%nat → (mask_r a t km ku kv r < n)%nat.
  Proof. move=> Hr. have := @mask_r_le _ _ n_prime a t km ku kv r. lia. Qed.
  Lemma mask_s_lt a t km ku kv (s : nat) : (s < n)%nat → (mask_s a t km ku kv s < n)%nat.
  Proof. move=> Hs. have := @mask_s_le _ _ n_prime a t km ku kv s. lia. Qed.
End ot_arith_lt.

#[global] Arguments trap : simpl never.
#[global] Arguments untrap : simpl never.
#[global] Arguments mask_r : simpl never.
#[global] Arguments mask_s : simpl never.
#[global] Opaque trap untrap mask_r mask_s.
