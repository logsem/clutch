(* We prove that the translation `(λ x, (x + k) mod n) : fin n → fin n` is a
   bijection on `fin n`. This fact is used in the ElGamal security proof. *)

From Coquelicot Require Rcomplements.
From mathcomp Require all_ssreflect ssrnat zmodp fingroup.
From stdpp Require fin.
From clutch.prelude Require Import base zmodp_fin stdpp_ext.

Set Default Proof Using "Type*".

Module bij_fin.
Section bij_fin.
  (* ElGamal bijection on fin n, to match the coupling rules in Clutch. *)
  Variable n : nat.
  Local Notation "'p'" := (S (S n)).
  Variable k : Fin.t p.

  Import all_ssreflect ssrnat zmodp fingroup.

  Let f' (x : 'Z_p) : 'Z_p := (Zp_add (ord_of_fin k) x)%g.
  Let g' (x : 'Z_p) : 'Z_p := Zp_add (Zp_opp (ord_of_fin k)) x.

  Fact f_g' x : f' (g' x) = x.
  Proof. by rewrite /f'/g' Zp_addA (Zp_addC(_ k)) Zp_addNz Zp_add0z. Qed.

  Fact g_f' x : g' (f' x) = x.
  Proof. by rewrite /f'/g' Zp_addA Zp_addNz Zp_add0z. Qed.

  Definition f (c : Fin.t p) : Fin.t p := fin_of_ord (f' (ord_of_fin c)).
  Definition g (c : Fin.t p) : Fin.t p := fin_of_ord (g' (ord_of_fin c)).

  Fact f_g x : f (g x) = x.
  Proof. by rewrite /f/g ord_of_fin_of_ord f_g' fin_of_ord_of_fin. Qed.

  Fact g_f x : g (f x) = x.
  Proof. by rewrite /f/g ord_of_fin_of_ord g_f' fin_of_ord_of_fin. Qed.

  Global Instance f_inj : base.Inj eq eq f.
  Proof. intros x y hf. rewrite -(g_f x) -(g_f y) hf => //. Qed.

  Global Instance f_surj : base.Surj eq f.
  Proof. intros x. exists (g x). by rewrite f_g. Qed.

  Global Instance bij_f : Bij f | 1.
  Proof. constructor; apply _. Qed.

  Global Instance g_inj : base.Inj eq eq g.
  Proof. intros x y hg. rewrite -(f_g x) -(f_g y) hg => //. Qed.

  Global Instance g_surj : base.Surj eq g.
  Proof. intros x. exists (f x). by rewrite g_f. Qed.

  Global Instance bij_g : Bij g | 1.
  Proof. constructor; apply _. Qed.

End bij_fin.
End bij_fin.

Module bij_nat.
Section bij_nat.
  (* ElGamal bijection on nat, to match the coupling rules in Approxis. *)

Fact div_modn_lt : (forall x y, 1 <= y -> div.modn x y < y).
  rewrite /lt.
  intros.
  apply Rcomplements.SSR_leq.
  apply div.ltn_pmod.
  by apply Rcomplements.SSR_leq.
Qed.

Variable n : nat.
Variable k : fin.fin (S n).

Definition mod_plus x :=
          if x <? S n then
            div.modn (k + x) (S n)
          else x.

Definition mod_minus x :=
          if x <? S n then
            div.modn (S n - k + x) (S n)
          else x.

Fact mod_plus_lt : ∀ m : nat, m < S n → mod_plus m < S n.
Proof.
  intros x ?.
  rewrite /mod_plus.
  destruct (x <? (S n)). 2: assumption.
  apply div_modn_lt. lia.
Qed.

Fact mod_minus_lt : ∀ m : nat, m < S n → mod_minus m < S n.
Proof.
  intros x ?.
  rewrite /mod_minus.
  destruct (x <? (S n)). 2: assumption.
  apply div_modn_lt. lia.
Qed.

Fact mod_plus_minus_cancel x : mod_plus (mod_minus x) = x.
Proof.
  rewrite /mod_minus.
  destruct (x <? S n) eqn:Hx.
  - set (fx := (div.modn (S n - k + x) (S n))).
    rewrite /mod_plus.
    destruct (fx <? S n) eqn:Hfx.
    2:{ apply Nat.ltb_nlt in Hfx.
        apply Nat.ltb_lt in Hx.
        opose proof (div_modn_lt (S n - k + x) (S n) _) as H.
        1: lia.
        subst fx.
        opose proof (Hfx H).
        done. }
    subst fx.
    apply Nat.ltb_lt in Hx.
    clear -Hx.
    (* push k in, cancel with -k, use Sn = 0 % Sn, then b/c x < Sn, x%Sn = x *)
    rewrite ssrnat.plusE.
    rewrite ssrnat.minusE.
    rewrite div.modnDmr.
    rewrite assoc.
    rewrite ssrnat.subnKC.
    2:{
      opose proof (fin.fin_to_nat_lt k) as H.
      apply Rcomplements.SSR_leq.
      unfold lt in H. lia.
    }
    rewrite div.modnDl.
    rewrite div.modn_small=> //.
    apply Rcomplements.SSR_leq.
    lia.
  - rewrite /mod_plus.
    rewrite Hx.
    done.
Qed.

Fact mod_minus_plus_cancel x : mod_minus (mod_plus x) = x.
Proof.
  rewrite /mod_plus.
  destruct (x <? S n) eqn:Hx.
  - set (fx := (div.modn (k + x) (S n))).
    rewrite /mod_minus.
    destruct (fx <? S n) eqn:Hfx.
    2:{ apply Nat.ltb_nlt in Hfx.
        apply Nat.ltb_lt in Hx.
        opose proof (div_modn_lt (k + x) (S n) _) as H.
        1: lia.
        subst fx.
        opose proof (Hfx H).
        done. }
    subst fx.
    apply Nat.ltb_lt in Hx.
    clear -Hx.
    rewrite ssrnat.plusE.
    rewrite ssrnat.minusE.
    rewrite div.modnDmr.
    rewrite assoc.
    rewrite ssrnat.subnK.
    2:{
      opose proof (fin.fin_to_nat_lt k) as H.
      apply Rcomplements.SSR_leq.
      unfold lt in H. lia.
    }
    rewrite div.modnDl.
    rewrite div.modn_small=> //.
    apply Rcomplements.SSR_leq.
    lia.
  - rewrite /mod_minus.
    rewrite Hx.
    done.
Qed.

#[export] Instance mod_plus_inj : base.Inj eq eq mod_plus.
Proof. intros x y hf. rewrite -(mod_minus_plus_cancel x) -(mod_minus_plus_cancel y) hf => //. Qed.

#[export] Instance mod_plus_surj : base.Surj eq mod_plus .
Proof. intros x. exists (mod_minus x). by rewrite mod_plus_minus_cancel. Qed.

#[export] Instance mod_plus_bij : Bij mod_plus | 1.
Proof. constructor; apply _. Qed.

#[export] Instance mod_minus_inj : base.Inj eq eq mod_minus.
Proof. intros x y hmod_minus. rewrite -(mod_plus_minus_cancel x) -(mod_plus_minus_cancel y) hmod_minus => //. Qed.

#[export] Instance mod_minus_surj : base.Surj eq mod_minus.
Proof. intros x. exists (mod_plus x). by rewrite mod_minus_plus_cancel. Qed.

#[export] Instance mod_minus_bij : Bij mod_minus | 1.
Proof. constructor; apply _. Qed.

End bij_nat.
End bij_nat.
