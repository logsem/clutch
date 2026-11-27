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

  (* The generator is not the unit. *)
  Lemma g_ne_1 : g ≠ 1.
  Proof. move=> H. have := @g_nontriv _ vgg. by rewrite H order1. Qed.

  (* A product exponent. *)
  Lemma expg_mul (c : vgG) (a b : nat) : c ^+ (a * b)%nat = c ^+ b ^+ a.
  Proof. change (a * b)%nat with (ssrnat.muln a b). by rewrite ssrnat.mulnC expgM. Qed.

  (* [trap y t * y] is [t] as an exponent of any group element: the
     simulator of the corrupted sender computes [a0 = a1 * y], and the
     receiver's [x] is [a0] for [a1 = trap y x]. *)
  Lemma trap_mul (c : vgG) (y t : nat) :
    y ≤ S n'' → y ≠ 0%nat → t ≤ S n'' → c ^+ (trap y t * y)%nat = c ^+ t.
  Proof.
    move=> Hy Hnz Ht. change (trap y t * y)%nat with (ssrnat.muln (trap y t) y).
    destruct (log_g_nat c) as (k & _ & ->).
    rewrite -!expgM ssrnat.mulnC expgM ssrnat.mulnC expgM (trap_exp Hy Hnz Ht).
    by rewrite -expgM ssrnat.mulnC expgM.
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

  (* ---------------------------------------------------------------- *)
  (* The slot whose generator is [g] itself.                            *)
  (* ---------------------------------------------------------------- *)

  Lemma trap_1 (t : nat) : t ≤ S n'' → trap 1 t = t.
  Proof.
    move=> Ht. have Hlt := @trap_le 1 t Ht.
    have H := @trap_exp 1 t ltac:(lia) ltac:(lia) Ht. rewrite expg1 in H.
    move: (expg_eq_mod_inv H). rewrite !div.modn_small //; apply/ssrnat.ltP; lia.
  Qed.

  Lemma mask_fst1 t km ku kv (r s : nat) :
    km ≤ S n'' → ku ≤ S n'' → kv ≤ S n'' → r ≤ S n'' → s ≤ S n'' →
    g ^+ r * g ^+ t ^+ s
    = g ^+ mask_r 1 t km ku kv r * g ^+ t ^+ mask_s 1 t km ku kv s.
  Proof. move=> *. have := @mask_fst 1 t km ku kv r s. rewrite !expg1. apply; lia. Qed.

  Lemma nondeg_self1 (t0 ku kv : nat) :
    t0 ≤ S n'' → ku ≤ S n'' → kv ≤ S n'' →
    g ^+ kv ≠ g ^+ ku ^+ t0 → nondeg 1 t0 ku kv.
  Proof. move=> Ht0 Hku Hkv Hv. apply: nondeg_self; try lia. by rewrite trap_1. Qed.

  Lemma nondeg_other1 (a1 t0 t1 ku kv : nat) :
    a1 ≤ S n'' → t0 ≤ S n'' → t1 ≤ S n'' → ku ≤ S n'' → kv ≤ S n'' →
    g ^+ ku ≠ 1 → g ^+ kv = g ^+ ku ^+ t0 → t1 ≠ untrap a1 t0 →
    nondeg a1 t1 ku kv.
  Proof.
    move=> Ha1 Ht0 Ht1 Hku Hkv Hu Hv Hne.
    apply (@nondeg_other 1 a1 t0 t1 ku kv); rewrite ?trap_1 //; lia.
  Qed.

End ot_arith.

(* ------------------------------------------------------------------ *)
(* Exponents in the field, and affine couplings.                       *)
(* ------------------------------------------------------------------ *)

(* For the honest case, whose couplings are affine maps of exponents:
   [gexp a = g ^ a] for [a] in the field ['F_n], the program's group
   terms as [gexp] of a field expression, and the coupling [aff a b] that
   maps [r] to [a r + b]. *)
Section ot_field.
  Context {vg : val_group} {vgg : @val_group_generator vg}.

  #[local] Notation n := (S (S n'')).
  Context (n_prime : is_true (prime.prime n)).
  #[local] Open Scope group_scope.
  Import GRing.Theory.

  Lemma Fp_n : S (S (Zp_trunc (prime.pdiv n))) = n.
  Proof. by rewrite Fp_cast. Qed.

  Lemma val_expF (k : nat) : nat_of_ord (expF k) = div.modn k n.
  Proof. rewrite /expF Zp_nat /=. by rewrite Fp_n. Qed.

  Lemma Fval_lt (a : 'F_n) : (nat_of_ord a < n)%nat.
  Proof. have H1 := Fp_n. have /ssrnat.ltP H2 := ltn_ord a. lia. Qed.

  Lemma expF_add (k l : nat) : expF (k + l) = (expF k + expF l)%R.
  Proof. by rewrite /expF mulrnDr. Qed.

  Lemma expF_mul (k l : nat) : expF (k * l) = (expF k * expF l)%R.
  Proof. rewrite /expF. change (k * l)%nat with (ssrnat.muln k l). by rewrite natrM. Qed.

  Lemma expF_val (a : 'F_n) : expF (nat_of_ord a) = a.
  Proof.
    apply val_inj => /=. rewrite val_expF div.modn_small //.
    apply/ssrnat.ltP. apply Fval_lt.
  Qed.

  (* The field, under a name usable outside mathcomp's notations. *)
  Definition Fn : Type := 'F_n.
  Definition Fmul (a b : Fn) : Fn := (a * b)%R.
  Definition Fadd (a b : Fn) : Fn := (a + b)%R.
  Definition F0 : Fn := 0%R.

  Definition gexp (a : 'F_n) : vgG := g ^+ (nat_of_ord a).

  Lemma gexp_nat (k : nat) : g ^+ k = gexp (expF k).
  Proof. rewrite /gexp val_expF. apply: (expg_eq_mod n_prime). by rewrite div.modn_mod. Qed.

  Lemma gexp_add (a b : 'F_n) : gexp (a + b)%R = gexp a * gexp b.
  Proof.
    rewrite -[a]expF_val -[b]expF_val -expF_add -!gexp_nat.
    change (nat_of_ord a + nat_of_ord b)%nat with (ssrnat.addn (nat_of_ord a) (nat_of_ord b)).
    by rewrite expgD.
  Qed.

  Lemma gexp_pow (a : 'F_n) (k : nat) : gexp a ^+ k = gexp (a * expF k)%R.
  Proof.
    rewrite -[a]expF_val -expF_mul -!gexp_nat.
    change (nat_of_ord a * k)%nat with (ssrnat.muln (nat_of_ord a) k).
    by rewrite expgM.
  Qed.

  Lemma gexp_zero : gexp 0%R = 1.
  Proof. by rewrite /gexp /= expg0. Qed.

  Lemma gexp_opp (a : 'F_n) : gexp (- a)%R = (gexp a)^-1.
  Proof.
    apply: (mulgI (gexp a)). by rewrite -gexp_add addrN gexp_zero mulgV.
  Qed.

  (* The affine coupling [r ↦ a r + b], on [0, n), the identity above. *)
  Definition aff (a b : 'F_n) (r : nat) : nat :=
    if bool_decide (r < n)%nat then nat_of_ord (a * expF r + b)%R else r.

  Lemma aff_lt (a b : 'F_n) (r : nat) : (r < n)%nat → (aff a b r < n)%nat.
  Proof. move=> Hr. rewrite /aff bool_decide_eq_true_2 //. apply Fval_lt. Qed.

  Lemma gexp_aff (a b : 'F_n) (r : nat) :
    (r < n)%nat → g ^+ aff a b r = gexp (a * expF r + b)%R.
  Proof. move=> Hr. by rewrite /aff bool_decide_eq_true_2 // gexp_nat expF_val. Qed.

  Lemma expF_inj (r r' : nat) : (r < n)%nat → (r' < n)%nat → expF r = expF r' → r = r'.
  Proof.
    move=> Hr Hr' H. have := f_equal (@nat_of_ord _) H. rewrite !val_expF !div.modn_small //;
      apply/ssrnat.ltP; lia.
  Qed.

  Lemma aff_bij (a b : 'F_n) : is_true (a != 0%R) → Bij (aff a b).
  Proof.
    move=> Ha. split.
    - move=> r r'. rewrite /aff.
      destruct (decide (r < n)%nat) as [Hr|Hr]; destruct (decide (r' < n)%nat) as [Hr'|Hr'].
      + rewrite !bool_decide_eq_true_2 //. move=> H.
        apply: expF_inj => //.
        have H' : (a * expF r = a * expF r')%R by apply: (addIr b); apply: val_inj.
        exact: (mulfI Ha H').
      + rewrite bool_decide_eq_true_2 // bool_decide_eq_false_2 //.
        move=> H. have := Fval_lt (a * expF r + b)%R. rewrite H. lia.
      + rewrite bool_decide_eq_false_2 // bool_decide_eq_true_2 //.
        move=> H. have := Fval_lt (a * expF r' + b)%R. rewrite -H. lia.
      + by rewrite !bool_decide_eq_false_2.
    - move=> y. destruct (decide (y < n)%nat) as [Hy|Hy].
      + exists (nat_of_ord ((expF y - b) / a)%R).
        rewrite /aff bool_decide_eq_true_2; last apply Fval_lt.
        rewrite expF_val mulrC divfK // subrK val_expF div.modn_small //. by apply/ssrnat.ltP.
      + exists y. by rewrite /aff bool_decide_eq_false_2.
  Qed.

  Lemma expF_aff (a b : 'F_n) (r : nat) : (r < n)%nat → expF (aff a b r) = (a * expF r + b)%R.
  Proof. move=> Hr. by rewrite /aff bool_decide_eq_true_2 // expF_val. Qed.

  (* ---------------------------------------------------------------- *)
  (* Step B of the honest OT.                                           *)
  (* ---------------------------------------------------------------- *)

  (* The sender's coupling [r ↦ r + (x - q) s]. *)
  Definition shiftB (X Q : Fn) (s : nat) : nat → nat := aff 1%R ((X - Q) * expF s)%R.

  Lemma shiftB_bij X Q s : Bij (shiftB X Q s).
  Proof. apply aff_bij. exact: oner_neq0. Qed.
  Lemma shiftB_lt X Q s (r : nat) : (r < n)%nat → (shiftB X Q s r < n)%nat.
  Proof. apply aff_lt. Qed.

  Lemma F_shift (Q S R X : 'F_n) : (Q * S + (1 * R + (X - Q) * S) = R + X * S)%R.
  Proof. by rewrite mul1r mulrBl addrCA [(Q * S + _)%R]addrC subrK. Qed.

  (* The ciphertexts: the real sender's and the hybrid's, slot 0 and 1. *)
  Lemma encB_fst0 (x r s : nat) :
    g ^+ r * g ^+ x ^+ s = gexp (Fadd (expF r) (Fmul (expF x) (expF s))).
  Proof. by rewrite !gexp_nat gexp_pow -gexp_add. Qed.

  Lemma encB_fst0' (X Q : Fn) (B : vgG) (r s : nat) :
    (r < n)%nat → B = gexp Q →
    B ^+ s * g ^+ shiftB X Q s r = gexp (Fadd (expF r) (Fmul X (expF s))).
  Proof.
    move=> Hr ->. rewrite gexp_nat expF_aff // gexp_pow -gexp_add /Fadd /Fmul.
    by rewrite F_shift.
  Qed.

  Lemma encB_snd (P X : Fn) (u v : vgG) (r s : nat) :
    u = gexp P → v = gexp (Fmul P X) →
    u ^+ r * v ^+ s = gexp (Fmul P (Fadd (expF r) (Fmul X (expF s)))).
  Proof. move=> -> ->. by rewrite !gexp_pow -gexp_add /Fmul /Fadd mulrDr mulrA. Qed.

  Lemma encB_snd' (P Q X : Fn) (C A : vgG) (r s : nat) :
    (r < n)%nat → C = gexp (Fmul P Q) → A = gexp P →
    C ^+ s * A ^+ shiftB X Q s r = gexp (Fmul P (Fadd (expF r) (Fmul X (expF s)))).
  Proof.
    move=> Hr -> ->. rewrite !gexp_pow expF_aff // -gexp_add /Fmul /Fadd.
    by rewrite -mulrA -mulrDr F_shift.
  Qed.

  Lemma encB_fst1 (y x r s : nat) :
    g ^+ y ^+ r * g ^+ y ^+ x ^+ s
    = gexp (Fmul (expF y) (Fadd (expF r) (Fmul (expF x) (expF s)))).
  Proof. by rewrite !gexp_nat !gexp_pow -gexp_add /Fmul /Fadd mulrDr mulrA. Qed.

  Lemma encB_fst1' (X Q : Fn) (y : nat) (B : vgG) (r s : nat) :
    (r < n)%nat → B = gexp Q →
    (B ^+ s * g ^+ shiftB X Q s r) ^+ y
    = gexp (Fmul (expF y) (Fadd (expF r) (Fmul X (expF s)))).
  Proof. move=> Hr HB. by rewrite encB_fst0' // gexp_pow /Fmul mulrC. Qed.

  (* The receiver's message and the tuple. *)
  Lemma recvB_pow (y z : nat) : g ^+ y ^+ z = gexp (Fmul (expF y) (expF z)).
  Proof. by rewrite gexp_nat gexp_pow. Qed.

  Lemma recvB_aff (y z : nat) :
    (z < n)%nat → g ^+ aff (expF y) F0 z = gexp (Fmul (expF y) (expF z)).
  Proof. move=> Hz. by rewrite gexp_aff // /F0 addr0. Qed.

  Lemma recvB_pow2 (P : Fn) (k x : nat) :
    g ^+ k = gexp P → g ^+ k ^+ x = gexp (Fmul P (expF x)).
  Proof. move=> ->. by rewrite gexp_pow. Qed.

  Lemma recvB_powAC (y x z : nat) : g ^+ y ^+ x ^+ z = g ^+ y ^+ z ^+ x.
  Proof. by rewrite expgAC. Qed.

  (* Decryption of the chosen ciphertext by the receiver, whose message
     is [u = g ^ P0 = gexp P] with [P0 = Yb z]. *)
  Lemma decB (P P0 Yb t : Fn) (m : vgG) (z : nat) :
    gexp P = gexp P0 → P0 = Fmul Yb (expF z) →
    (m * gexp (Fmul P t)) * (gexp (Fmul Yb t) ^+ z)^-1 = m.
  Proof.
    move=> HP HP0. subst P0. rewrite gexp_pow -gexp_opp /Fmul.
    have -> : gexp (P * t)%R = gexp (Yb * expF z * t)%R.
    { by rewrite -[t]expF_val -(gexp_pow P) -(gexp_pow (Fmul Yb (expF z))) HP. }
    by rewrite -mulgA -gexp_add mulrAC subrr gexp_zero mulg1.
  Qed.

  Lemma decB0 (P t : Fn) (m : vgG) (z : nat) :
    gexp P = gexp (expF z) → (m * gexp (Fmul P t)) * (gexp t ^+ z)^-1 = m.
  Proof.
    move=> HP. have H := @decB P (expF z) 1%R t m z HP.
    rewrite /Fmul !mul1r in H. by apply: H.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Step D of the honest OT.                                           *)
  (* ---------------------------------------------------------------- *)

  Definition F1 : Fn := 1%R.
  (* The coefficient [c - p q] of the coupling [α ↦ (c - p q) α + l]. *)
  Definition dcoef (c p q : nat) : Fn := (expF c - expF p * expF q)%R.
  (* The shift [q α] of the coupling [β ↦ β + q α]. *)
  Definition tshift (q a : nat) : Fn := (expF q * expF a)%R.
  (* The value [c] avoids. *)
  Definition pqval (p q : nat) : nat := nat_of_ord (expF p * expF q)%R.

  Lemma pqval_lt p q : (pqval p q < n)%nat.
  Proof. apply Fval_lt. Qed.

  Lemma gpow_ne1 (p : nat) : p ≤ S n'' → p ≠ 0%nat → g ^+ p ≠ 1.
  Proof.
    move=> Hp Hnz H. have : g ^+ p = g ^+ 0 by rewrite expg0.
    move/(expg_eq_mod_inv n_prime). rewrite !div.modn_small //; apply/ssrnat.ltP; lia.
  Qed.

  Lemma dcoef_bij (c p q : nat) (L : Fn) :
    c ≤ S n'' → c ≠ pqval p q → Bij (aff (dcoef c p q) L).
  Proof.
    move=> Hc Hne. apply: aff_bij. rewrite /dcoef subr_eq0. apply/eqP => H.
    apply: Hne. rewrite /pqval -H val_expF div.modn_small //. apply/ssrnat.ltP; lia.
  Qed.

  Lemma tshift_bij (q a : nat) : Bij (aff F1 (tshift q a)).
  Proof. apply: aff_bij. exact: oner_neq0. Qed.

  (* The simulator's ciphertexts are the hybrid's. *)
  Lemma encD_fst0 (q a b : nat) :
    (b < n)%nat → g ^+ aff F1 (tshift q a) b = g ^+ q ^+ a * g ^+ b.
  Proof.
    move=> Hb. rewrite gexp_aff // !gexp_nat gexp_pow -gexp_add /F1 /tshift.
    by rewrite mul1r addrC.
  Qed.

  Lemma encD_fst1 (y q a b : nat) :
    (b < n)%nat → g ^+ y ^+ aff F1 (tshift q a) b = (g ^+ q ^+ a * g ^+ b) ^+ y.
  Proof. move=> Hb. by rewrite -encD_fst0 // expgAC. Qed.

  Lemma encD_snd (c p q l a b : nat) :
    (a < n)%nat → (b < n)%nat →
    g ^+ aff (dcoef c p q) (expF l) a * g ^+ p ^+ aff F1 (tshift q a) b
    = g ^+ l * (g ^+ c ^+ a * g ^+ p ^+ b).
  Proof.
    move=> Ha Hb. rewrite gexp_aff // [g ^+ p]gexp_nat gexp_pow expF_aff //.
    rewrite (gexp_nat l) (gexp_nat c) !gexp_pow -!gexp_add /dcoef /tshift /F1.
    congr gexp.
    rewrite mul1r mulrDr mulrA mulrBl [(_ - _ + expF l)%R]addrC -addrA.
    congr (_ + _)%R.
    by rewrite [(expF p * expF b + _)%R]addrC addrA subrK.
  Qed.

End ot_field.

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
