From clutch.eris.examples.math Require Import prelude axioms iverson sets piecewise.
From clutch.eris Require Import infinite_tape.
Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(** Additional lemmas about Riemann integration *)

(** Sum of integrals *)
Lemma RInt_add {F1 F2 : R → R} {a b : R} (H1 : ex_RInt F1 a b) (H2 : ex_RInt F2 a b) :
  RInt F1 a b  + RInt F2 a b = RInt (fun x => F1 x + F2 x) a b.
Proof. rewrite RInt_plus; done. Qed.

(** Left scaling of integrand *)
Lemma RInt_Rmult {F : R → R} {a b r : R} (Hex : ex_RInt F a b) : r * RInt F a b = RInt (fun x => r * F x) a b.
Proof.
  replace (λ x : R, r * F x) with (λ x : R, scal r (F x)) by (rewrite /scal//=/mult//=; lra).
  rewrite RInt_scal.
  { rewrite /scal//=/mult//=; lra. }
  done.
Qed.

(** Right scaling of integrand *)
Lemma RInt_Rmult' {F : R → R} {a b r : R} (Hex : ex_RInt F a b) : (RInt F a b) * r = RInt (fun x => F x * r) a b.
Proof.
  replace (λ x : R, F x * r) with (λ x : R, scal r (F x)); last (rewrite /scal//=/mult//=; apply functional_extensionality; intros ?; lra).
  rewrite RInt_scal.
  { rewrite /scal//=/mult//=; lra. }
  done.
Qed.

(** Integrability of left scaling *)
Lemma ex_RInt_Rmult {F : R → R} {a b r : R} : ex_RInt F a b → ex_RInt (fun x => r * F x) a b.
Proof.
  intro H.
  replace (λ x : R, r * F x) with (λ x : R, scal r (F x)); last (apply functional_extensionality; done).
  apply (ex_RInt_scal (V := R_CompleteNormedModule)).
  apply H.
Qed.

(** Integrability of right scaling *)
Lemma ex_RInt_Rmult' {F : R → R} {a b r : R} : ex_RInt F a b → ex_RInt (fun x => F x * r) a b.
Proof.
  intro H.
  replace (λ x : R, F x * r) with (λ x : R, scal r (F x)); last (apply functional_extensionality; rewrite /scal//=/mult//=; intros ?; lra).
  apply (ex_RInt_scal (V := R_CompleteNormedModule)).
  apply H.
Qed.

(** Integrability of monomial *)
Lemma ex_RInt_pow {a b N} : ex_RInt (λ y : R, y ^ N) a b.
Proof.
  apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
  intros ??.
  apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
  by auto_derive.
Qed.

(** Integrability of sum *)
Lemma ex_RInt_add' (f g : R → R) {h : R → R} {a b : R} (Ha : ex_RInt f a b) (Hb : ex_RInt g a b)
   (Hab : a <= b)
   (Hext : ∀ x, a <= x <= b → f x + g x = h x) : ex_RInt h a b.
Proof.
  eapply ex_RInt_ext.
  { rewrite Rmin_left; [|lra].
    rewrite Rmax_right; [|lra].
    intros ??.
    apply Hext.
    lra.
  }
  apply (ex_RInt_plus _ _ _ _ Ha Hb).
Qed.

(** Integrability of sum *)
Lemma ex_RInt_add  {f g : R → R} {a b : R} (Ha : ex_RInt f a b) (Hb : ex_RInt g a b) :
  ex_RInt (fun x => f x + g x) a b.
Proof. apply (ex_RInt_plus _ _ _ _ Ha Hb). Qed.

(** Integrability of square *)
Lemma ex_RInt_square (f  : R -> R) (a b : R) :
  ex_RInt f a b → ex_RInt (fun x => (f x) ^ 2) a b.
Proof.
  intros ?.
  apply (ex_RInt_comp_cts f (fun x => x ^ 2)); [|done].
  intros ?.
  apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
  by auto_derive.
Qed.

(** Integrability of product *)
Lemma ex_RInt_mult (f g : R -> R) (a b : R) :
  ex_RInt f a b ->  ex_RInt g a b ->
  ex_RInt (λ y : R, f y * g y) a b.
Proof.
  intros H1 H2.
  replace (λ y : R, f y * g y) with (λ y : R, (1/4) * ((f y + g y) ^ 2 - (f y - g y) ^ 2)); last first.
  { apply functional_extensionality; intros ?. lra. }
  apply ex_RInt_Rmult.
  apply (ex_RInt_minus (V := R_CompleteNormedModule)).
  { apply ex_RInt_square. by apply (ex_RInt_plus (V := R_CompleteNormedModule)). }
  { apply ex_RInt_square. by apply (ex_RInt_minus (V := R_CompleteNormedModule)). }
Qed.

Lemma ex_RInt_mult_PCts (f g : R -> R) (a b : R) :
  PCts f a b -> PCts g a b ->
  ex_RInt (λ y : R, f y * g y) a b.
Proof. intros ??. apply PCts_RInt. apply PCts_mult; done. Qed.

Lemma ex_RInt_mult_IPCts (f g : R -> R) (a b : R) :
  IPCts f -> IPCts g ->
  ex_RInt (λ y : R, f y * g y) a b.
Proof. intros ??. apply PCts_RInt. apply PCts_mult; apply IPCts_PCts; done. Qed.

(** Integral of monomial *)
Lemma RInt_pow {a b N} : RInt (λ x : R, x ^ N) a b = b ^ (N + 1)%nat / (N + 1)%nat - a ^ (N + 1)%nat / (N + 1)%nat.
Proof.
  have H : (λ x : R, x ^ N) = (Derive.Derive (λ x : R, x ^ (N+1)%nat * / (N +1)%nat)).
  { apply functional_extensionality.
    intros x.
    rewrite Derive.Derive_scal_l.
    rewrite Derive.Derive_pow; [|by auto_derive].
    rewrite Derive.Derive_id.
    replace (Init.Nat.pred (N + 1)) with N; last lia.
    rewrite Rmult_comm Rmult_1_r -Rmult_assoc.
    rewrite Rinv_l; [lra|].
    apply not_0_INR; lia.
  }
  rewrite H.
  rewrite RInt_Derive; [lra| |].
  { intros ??. by auto_derive. }
  { intros ??.
    rewrite -H.
    apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
    by auto_derive.
  }
Qed.

(** Integrability of finite sum *)
Lemma ex_RInt_sum_n {a b M} {F : nat → R → R} :
  (∀ n, ex_RInt (F n) a b) → ex_RInt (λ x : R, sum_n (λ n : nat, F n x) M) a b .
Proof.
 intro H.
 induction M.
 { replace (λ x : R, sum_n (λ n : nat, F n x) 0) with (λ x : R, F 0%nat x).
   { apply H. }
   apply functional_extensionality; intros ?.
   by rewrite sum_O.
 }
 { replace (λ x : R, sum_n (λ n : nat, F n x) (S M)) with
     (λ x : R, sum_n (λ n : nat, F n x) M + F (S M) x); last first.
   { apply functional_extensionality; intros ?.
     rewrite sum_Sn.
     rewrite /plus//=/zero//=.
   }
   apply (ex_RInt_plus (V := R_CompleteNormedModule));  done.
 }
Qed.


(** Integrability of function with internalized domain *)
Lemma ex_RInt_dom {F : R → R} {a b : R} : ex_RInt (fun x => Iverson (Ioo a b) x * F x) a b ↔ ex_RInt F a b.
Proof.
intros.
unfold Ioo, Iverson.
split.
{ intros H.
  eapply ex_RInt_ext; [|apply H].
  intros ??.
  simpl.
  rewrite decide_True; lra.
}
{ intros H.
  eapply ex_RInt_ext; [|apply H].
  intros ??.
  simpl.
  rewrite decide_True; lra.
}
Qed.

(** Alter a function at one point *)
Definition poke (f : R → R) (a z : R) : R → R := fun x =>
  if (decide (x = a)) then z else f x.

(** Integrability of function with one point different *)
Lemma ex_RInt_poke {a b c z : R} (f : R → R) (Hf : ex_RInt f a b) (Hi : a < c < b):
  ex_RInt (poke f c z) a b.
Proof.
  apply (ex_RInt_Chasles  _ _ c).
  { apply (@ex_RInt_ext _ f).
    { intro x. rewrite Rmin_left; try lra. rewrite Rmax_right; try lra. intros ?.
      rewrite /poke. case_decide; try lra. }
    { eapply (@ex_RInt_Chasles_1 R_CompleteNormedModule); last eapply Hf. lra. }
  }
  { apply (@ex_RInt_ext _ f).
    { intro x. rewrite Rmin_left; try lra. rewrite Rmax_right; try lra. intros ?.
      rewrite /poke. case_decide; try lra. }
    { eapply (@ex_RInt_Chasles_2 R_CompleteNormedModule); last eapply Hf. lra. }
  }
Qed.

(** Integral of function with one point different *)
Lemma RInt_poke {a b c z : R} (f : R → R) (Hf : ex_RInt f a b) (Hi : a < c < b) :
  RInt f a b = RInt (poke f c z) a b.
Proof.
  rewrite -(RInt_Chasles _ _ c).
  3: { eapply (@ex_RInt_Chasles_2 R_CompleteNormedModule); last eapply Hf. lra. }
  2: { eapply (@ex_RInt_Chasles_1 R_CompleteNormedModule); last eapply Hf. lra. }
  rewrite -(RInt_Chasles (poke _ _ _) _ c).
  3: { eapply (@ex_RInt_Chasles_2 R_CompleteNormedModule).
       2: { eapply ex_RInt_poke; [apply Hf |]. lra. }
       lra. }
  2: { eapply (@ex_RInt_Chasles_1 R_CompleteNormedModule).
       2: { eapply ex_RInt_poke; [apply Hf |]. lra. }
       lra. }
  f_equal.
  { apply RInt_ext.
    intro x. rewrite Rmin_left; try lra. rewrite Rmax_right; try lra. intros ?.
    rewrite /poke.
    case_decide; try lra.
  }
  { apply RInt_ext.
    intro x. rewrite Rmin_left; try lra. rewrite Rmax_right; try lra. intros ?.
    rewrite /poke.
    case_decide; try lra.
  }
Qed.


(** Integrability of scalar division *)
Lemma ex_RInt_div (F : R → R) {a b c} : ex_RInt F a b → ex_RInt (fun x => F x / c) a b.
Proof.
  intro H.
  replace (λ x : R, F x / c) with (λ x : R, F x * / c); last first.
  { apply functional_extensionality; intros ?; rewrite Rdiv_def//=. }
  by apply ex_RInt_Rmult'.
Qed.

(** Integrability of change of variables *)
Lemma ex_RInt_shift {F} (H : ∀ a b, ex_RInt F a b) {x y L : R} :
  (ex_RInt (V := R_CompleteNormedModule) (λ y : R, F (y + L)) x y).
Proof.
  apply (ex_RInt_ext (λ y0 : R, scal 1 (F (1 * y0 + L)))).
  - intros x0 Hx0.
    replace (1 * x0 + L) with (x0 + L) by lra.
    rewrite scal_one.
    reflexivity.
  - apply (ex_RInt_comp_lin F 1 L x y).
    apply H.
Qed.
