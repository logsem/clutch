From Coq Require Import Reals Lia Lra.
From clutch.prelude Require Export Reals_ext Coquelicot_ext Series_ext.
From stdpp Require Export ssreflect.
From Coquelicot Require Import ElemFct RInt RInt_analysis Continuity.

#[local] Open Scope R.

Definition Choose (n k : nat) : R :=
  if bool_decide (k ≤ n)%nat then
    C n k
  else 0%R.

Lemma pascal' (n i : nat) : (Choose n i + Choose n (S i))%R = Choose (S n) (S i).
Proof.
  rewrite /Choose.
  repeat case_bool_decide; try lia; [by rewrite pascal | | lra].
  assert (i = n) as -> by lia.
  rewrite !Rcomplements.C_n_n.
  lra.
Qed.

Lemma Choose_pos (n i : nat) : (0 <= Choose n i)%R.
Proof.
  rewrite /Choose /C.
  case_bool_decide; last done.
  apply Rcomplements.Rdiv_le_0_compat; first apply pos_INR.
  apply Rmult_lt_0_compat;
    rewrite -INR_0;
    apply lt_INR, lt_O_fact.
Qed.

Lemma Choose_n_0 (n : nat) : Choose n 0 = 1.
Proof.
  unfold Choose.
  case_bool_decide; last lia.
  rewrite Rcomplements.C_n_0 //.
Qed.

Lemma Choose_n_n (n : nat) : Choose n n = 1.
Proof.
  unfold Choose.
  case_bool_decide; last lia.
  rewrite Rcomplements.C_n_n //.
Qed.

Lemma Choose_n_1 : ∀ (n : nat), Choose n 1 = n.
Proof.
  elim=>[|n IH]; first done.
  rewrite -pascal' IH Choose_n_0 S_INR.
  lra.
Qed.
