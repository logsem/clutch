From clutch Require Import clutch.
From clutch.prob_lang Require Import advantage.
From clutch.prob_lang.typing Require Import tychk.
From clutch.clutch.examples.crypto Require Import valgroup advantage_laws.
From clutch.clutch.examples.crypto Require ElGamal_bijection.

From mathcomp Require ssrnat.
From mathcomp Require Import zmodp finset ssrbool fingroup.fingroup solvable.cyclic.
Import valgroup_notation.
From clutch.clutch.examples.crypto Require Import ElGamal.

Set Default Proof Using "Type*".

Section Stream.
Print expr.
Definition eager_stream (N : nat) : val :=
  rec: "f" "x" := (rand #N, λ:<>, "f" "x").

Definition lazy_stream (N : nat) : val :=
  rec: "f" "x" := (#N - (rand #N), λ:<>, "f" "x").

Definition τ := (() → μ: TInt * (() → #0))%ty.

Section Logrel.
  
Context `{!clutchRGS Σ}.
Context {Δ : listO (lrelC Σ)}.

Definition T := Eval cbn in (interp τ Δ).

Lemma sub_lt : forall (n : nat) (x : fin (S n)), n - (fin_to_nat x) < S n.
Proof. intros *. pose proof (fin_to_nat_lt x). lia. Qed.

Definition bij (n : nat) : fin (S n) -> fin (S n) :=
  fun x => nat_to_fin (sub_lt n x).

Lemma minus_inv : forall (n N : nat), n < (S N) -> (N - (N - n)) = n.
Proof. intros n N. lia. Qed.

Theorem refinement : ∀ N, ⊢ refines top (eager_stream N) (lazy_stream N) T.
Proof. iStartProof. rewrite /eager_stream. rewrite /lazy_stream. iIntros (N).
  rel_arrow_val. iIntros (v1 v2 H). destruct H as [eq1 eq2]; subst.
  iLöb as "IH".
  remember (lrel_rec (λne τ0 : ofe_car (lrelC Σ), lrel_prod lrel_int (() → τ0))) as T.
  rel_pure_r; rel_pure_l. rel_pure_l. rel_pure_r.
  rel_couple_UU (bij (Z.to_nat N)).
  remember (refines top (App
    (Val
    (rec: (BNamed "f") (BNamed "x") :=
    (rand Val #(LitInt (Z.of_nat N)), λ: <>, App (Var "f") (Var "x"))))
    (Val #()))
    (App
    (Val
    (rec: (BNamed "f") (BNamed "x") :=
    (Val #(LitInt (Z.of_nat N)) - (rand Val #(LitInt (Z.of_nat N))),
    λ: <>, App (Var "f") (Var "x")))) (Val #())) T) as H.
  rewrite HeqT.
  rewrite lrel_rec_unfold.
  rel_pure_r. rewrite /bij.
  rewrite fin_to_nat_to_fin. rel_pures_l; rel_pures_r.
  rel_values. simpl.
  rewrite /lrel_rec1.  rewrite /lrel_car.
  rewrite -/lrel_car. rewrite -/lrel_rec1. rewrite -/lrel_rec_unfold.
  iModIntro. simpl. iModIntro.
  iExists #n.
  iExists #n. iExists (λ: <>, (rec: "f" "x" := (rand #N, λ: <>, "f" "x"))%V #())%V.
  iExists (λ: <>, (rec: "f" "x" := (#N - rand #N, λ: <>, "f" "x"))%V #())%V.
  iSplit.
  - done.
  - iSplit.
    + assert (eq : (Z.of_nat N - Z.of_nat (Z.to_nat (Z.of_nat N) - fin_to_nat n))%Z =
              Z.of_nat n).
      { pose proof (fin_to_nat_lt n). clear HeqH HeqT.
        Set Printing Coercions. remember (Z.to_nat (Z.of_nat N)) as N' eqn:eqN'.
        rewrite Nat2Z.id in eqN'. subst.
        remember (fin_to_nat n) as n' eqn:eqn'. lia.
      }
      rewrite eq. iPureIntro. reflexivity.
    + iSplitL.
      * rewrite /lrel_int. rewrite /lrel_car. iExists n. done.
      * rewrite /lrel_arr. rewrite /lrel_car. iModIntro.
        iIntros (v1 v2). simpl. iIntros "[%eq1 %eq2]"; subst.
        rel_pure_l; rel_pure_r.
        rel_apply "IH".
  Unshelve.
  {
    apply Build_Bij.
    - rewrite /Inj. intros n m. rewrite /bij.
      intro H.
      assert (eq : fin_to_nat (nat_to_fin (sub_lt (Z.to_nat (Z.of_nat N)) n)) =
                   fin_to_nat (nat_to_fin (sub_lt (Z.to_nat (Z.of_nat N)) m))).
      { rewrite H. reflexivity. }
      rewrite fin_to_nat_to_fin in eq. rewrite fin_to_nat_to_fin in eq.
      remember (Z.to_nat (Z.of_nat N)) as N' eqn:eqN.
      rewrite Nat2Z.id in eqN. subst. pose proof (fin_to_nat_lt n) as H0.
      pose proof (fin_to_nat_lt m) as H1. apply (minus_inv n) in H0.
      apply (minus_inv m) in H1. rewrite eq in H0. rewrite H1 in H0.
      apply fin_to_nat_inj. rewrite H0. reflexivity.
    - rewrite /Surj. rewrite Nat2Z.id. intro n.
      exists (nat_to_fin (sub_lt N n)).
      rewrite /bij.
      assert (H : fin_to_nat (nat_to_fin (sub_lt N (nat_to_fin (sub_lt N n)))) =
                  fin_to_nat n).
      {
        rewrite fin_to_nat_to_fin. rewrite fin_to_nat_to_fin. apply minus_inv.
        pose proof (fin_to_nat_lt n). assumption.
      }
      apply fin_to_nat_inj. rewrite H. reflexivity.
  }
Qed.

Theorem refinement' : ∀ N, ⊢ refines top (eager_stream N) (lazy_stream N) T.
Proof. iStartProof. rewrite /eager_stream. rewrite /lazy_stream. iIntros (N).
  rel_arrow_val. iIntros (v1 v2 H). destruct H as [eq1 eq2]; subst.
  iLöb as "IH".
  remember (lrel_rec (λne τ0 : ofe_car (lrelC Σ), lrel_prod lrel_int (() → τ0))) as T.
  rel_pure_r; rel_pure_l. rel_pure_l. rel_pure_r.
  rel_couple_UU (bij (Z.to_nat N)).
  remember (refines top (App
    (Val
    (rec: (BNamed "f") (BNamed "x") :=
    (rand Val #(LitInt (Z.of_nat N)), λ: <>, App (Var "f") (Var "x"))))
    (Val #()))
    (App
    (Val
    (rec: (BNamed "f") (BNamed "x") :=
    (Val #(LitInt (Z.of_nat N)) - (rand Val #(LitInt (Z.of_nat N))),
    λ: <>, App (Var "f") (Var "x")))) (Val #())) T) as H.
  rewrite HeqT.
  rewrite lrel_rec_unfold.
  rel_pure_r. rewrite /bij.
  rewrite fin_to_nat_to_fin. rel_pures_l; rel_pures_r.
  rel_values. simpl.
  rewrite /lrel_rec1.  rewrite /lrel_car.
  rewrite -/lrel_car. rewrite -/lrel_rec1. rewrite -/lrel_rec_unfold.
  iModIntro. simpl. iModIntro.
  iExists #n.
  iExists #n. iExists (λ: <>, (rec: "f" "x" := (rand #N, λ: <>, "f" "x"))%V #())%V.
  iExists (λ: <>, (rec: "f" "x" := (#N - rand #N, λ: <>, "f" "x"))%V #())%V.
  iSplit.
  - done.
  - iSplit.
    + assert (eq : (Z.of_nat N - Z.of_nat (Z.to_nat (Z.of_nat N) - fin_to_nat n))%Z =
              Z.of_nat n).
      { pose proof (fin_to_nat_lt n). clear HeqH HeqT.
        Set Printing Coercions. remember (Z.to_nat (Z.of_nat N)) as N' eqn:eqN'.
        rewrite Nat2Z.id in eqN'. subst.
        remember (fin_to_nat n) as n' eqn:eqn'. lia.
      }
      rewrite eq. iPureIntro. reflexivity.
    + iSplitL.
      * rewrite /lrel_int. rewrite /lrel_car. iExists n. done.
      * rewrite /lrel_arr. rewrite /lrel_car. iModIntro.
        iIntros (v1 v2). simpl. iIntros "[%eq1 %eq2]"; subst.
        rel_pure_l; rel_pure_r.
        rel_apply "IH".
  Unshelve.
  {
    apply Build_Bij.
    - rewrite /Inj. intros n m. rewrite /bij.
      intro H.
      assert (eq : fin_to_nat (nat_to_fin (sub_lt (Z.to_nat (Z.of_nat N)) n)) =
                   fin_to_nat (nat_to_fin (sub_lt (Z.to_nat (Z.of_nat N)) m))).
      { rewrite H. reflexivity. }
      rewrite fin_to_nat_to_fin in eq. rewrite fin_to_nat_to_fin in eq.
      remember (Z.to_nat (Z.of_nat N)) as N' eqn:eqN.
      rewrite Nat2Z.id in eqN. subst. pose proof (fin_to_nat_lt n) as H0.
      pose proof (fin_to_nat_lt m) as H1. apply (minus_inv n) in H0.
      apply (minus_inv m) in H1. rewrite eq in H0. rewrite H1 in H0.
      apply fin_to_nat_inj. rewrite H0. reflexivity.
    - rewrite /Surj. rewrite Nat2Z.id. intro n.
      exists (nat_to_fin (sub_lt N n)).
      rewrite /bij.
      assert (H : fin_to_nat (nat_to_fin (sub_lt N (nat_to_fin (sub_lt N n)))) =
                  fin_to_nat n).
      {
        rewrite fin_to_nat_to_fin. rewrite fin_to_nat_to_fin. apply minus_inv.
        pose proof (fin_to_nat_lt n). assumption.
      }
      apply fin_to_nat_inj. rewrite H. reflexivity.
  }
Qed.

End Logrel.

End Stream.