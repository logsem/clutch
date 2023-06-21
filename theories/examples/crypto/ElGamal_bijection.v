(* We prove that the translation `(λ x, (x + k) mod n) : fin n → fin n` is a
   bijection on `fin n`. This fact is used in the ElGamal security proof. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect ssrnat zmodp fingroup.
Set Warnings "notation-overridden,ambiguous-paths".

From stdpp Require fin.
From clutch Require Import prelude.zmodp_fin.

Set Default Proof Using "Type*".

Section bij.

  Variable n : nat.
  Local Notation "'p'" := (S (S n)).
  Variable k : Fin.t p.

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

  Fact f_inj : base.Inj eq eq f.
  Proof. intros x y hf. rewrite -(g_f x) -(g_f y) hf => //. Qed.

  Fact f_surj : base.Surj eq f.
  Proof. intros x. exists (g x). by rewrite f_g. Qed.

End bij.

Section bij_lt.
  (* A slightly more general interface to the previous section where instead of
  requiring the parameter `p` to be literally `S (S p')` for some `p'`, we only
  require that `p > 1`. This definition is logically equivalent, easier to
  satisfy, but harder to work with because explicit transports along equalities
  are required to make the types line up. *)

  Variable p : nat.
  Hypothesis hp : p > 1.
  Fact pss : {p' : nat | p = S (S p')}.
  Proof.
    move : hp. move /leP. intros h.
    destruct p. 1: inversion hp. destruct n. 1: inversion hp.
    by exists n.
  Qed.
  Definition p'' := projT1 pss.
  Definition pp' : p = p''.+2 := projT2 pss.

  Definition f'' : Fin.t p -> Fin.t p -> Fin.t p.
  Proof.
    pose proof (f p'') as ff.
    rewrite -pp' in ff.
    exact ff.
  Defined.

  Definition g'' : Fin.t p -> Fin.t p -> Fin.t p.
  Proof.
    pose proof (g p'') as gg.
    rewrite -pp' in gg.
    exact gg.
  Defined.

  Fact g_f'' k x : g'' k (f'' k x) = x.
  Proof.
    pose proof (g_f p'').
    (* pose (@eq_rect _ _ _ _ _ (pp')). *)
    (* unfold f''. *)
    (* rewrite pp' in k, x. *)
  Abort.

  Fact f_g'' k x : f'' k (g'' k x) = x.
  Proof.
  Abort.
End bij_lt.
