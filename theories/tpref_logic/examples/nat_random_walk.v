(** Almost-sure termination of a simple random walk over the naturals *)
From Coq Require Import Reals Psatz.
From clutch.prob_lang Require Import lang notation.
From clutch.tpref_logic Require Import weakestpre spec primitive_laws proofmode adequacy.
From clutch.prob Require Import distribution markov.
From clutch.tpref_logic.examples Require Import flip.
#[local] Open Scope R.

(** Model *)
Definition nrw_step (n : nat) :=
  match n with
    | 0 => dzero
    | S m => fair_conv_comb (dret m) (dret (S (S m)))
  end.

Definition nrw_to_final (n : nat) : option nat :=
  match n with
    | 0 => Some 0%nat
    | S m => None
  end.

Definition n_random_walk_mixin : MarkovMixin nrw_step nrw_to_final.
Proof. constructor. by intros [] [] []; simplify_eq=>/=. Qed.

Canonical Structure n_random_walk : markov := Markov _ _ n_random_walk_mixin.

(** Termination proof, by hand  *)

Lemma SeriesC_fair_conv_comb `{Countable A} (μ1 μ2 : distr A) :
  SeriesC (fair_conv_comb μ1 μ2) = 0.5 * (SeriesC μ1 + SeriesC μ2).
Proof.
  rewrite -SeriesC_plus // -SeriesC_scal_l.
  apply SeriesC_ext.
  intros.
  rewrite fair_conv_comb_pmf.
  lra.
Qed.


Lemma fair_conv_comb_dbind `{Countable A, Countable B} (f : A → distr B) (μ1 μ2 : distr A):
  (fair_conv_comb μ1 μ2) ≫= f = fair_conv_comb (μ1 ≫= f) (μ2 ≫= f).
Proof.
  rewrite /fair_conv_comb.
  rewrite -dbind_assoc.
  apply Rcoupl_eq_elim.
  eapply Rcoupl_dbind; [ | apply Rcoupl_eq ].
  intros a b ->.
  destruct b; simpl; apply Rcoupl_eq.
Qed.

Lemma nrw_aux (n : nat) :
  SeriesC (lim_exec (S n)) = 0.5 * (SeriesC (lim_exec n) + SeriesC (lim_exec (S (S n)))).
Proof.
  assert (to_final (S n) = None) as Hnone.
  {
    rewrite /to_final/= /nrw_to_final //.
  }
  rewrite {1}lim_exec_step /step_or_final Hnone /step /= /nrw_step.
  rewrite -SeriesC_plus // -SeriesC_scal_l.
  apply SeriesC_ext => z'.
  rewrite fair_conv_comb_dbind.
  do 2 rewrite dret_id_left.
  rewrite fair_conv_comb_pmf /=.
  do 2 rewrite /lim_exec.
  by rewrite Rmult_plus_distr_l.
Qed.


Lemma nrw_aux_2 (n : nat) :
  SeriesC (lim_exec (S (S n))) = 2 * SeriesC (lim_exec (S n)) - SeriesC (lim_exec n).
Proof.
  rewrite (nrw_aux n). lra.
Qed.

Lemma nrw_zero :
  SeriesC (lim_exec 0%nat) = 1.
Proof.
  erewrite lim_exec_final; auto.
  apply dret_mass.
Qed.

Lemma nrw_no_step_down (n : nat) :
  SeriesC (lim_exec (S n)) < (SeriesC (lim_exec n)) ->
  exists k, (SeriesC (lim_exec ((S k)+n)%nat)) < 0.
Proof.
  intros Hlt.
  set (d := SeriesC (lim_exec n) - (SeriesC (lim_exec (S n)))).
  assert (0 < d) as Hd.
  {
    rewrite /d. lra.
  }
  assert (forall k:nat,(forall l:nat, l ≤ k -> SeriesC (lim_exec ((S l) + n)%nat) = SeriesC (lim_exec n) - ((S l)*d)%R)) as Haux.
  {
    induction k.
    - intros [] Hl; simpl in Hl.
      + rewrite /d. simpl. lra.
      + inversion Hl.
    - intros l H.
      + inversion H.
        * rewrite nrw_aux_2.
          fold Nat.add.
          replace (S (k + n)%nat) with (S k + n)%nat; auto.
          rewrite (IHk k); auto.
          destruct k.
          ** simpl. lra.
          ** rewrite IHk; auto. simpl. lra.
       * apply IHk; auto.
  }
  assert (exists r, 0 <= r /\ 1 < r * d) as [r [Hr1 Hr2]].
  {
    exists (1 + (1/d)); split.
    - apply Rplus_le_le_0_compat; [lra | ].
      apply Rcomplements.Rdiv_le_0_compat; lra.
    - rewrite Rmult_plus_distr_r.
      rewrite /Rdiv.
      do 2 rewrite Rmult_1_l.
      rewrite Rinv_l; lra.
  }
  assert (exists l, 1 < (S l * d)) as [k ?].
  {
    destruct (Rcomplements.nfloor_ex r) as [l [Hl1 Hl2]]; auto.
    exists l.
    etrans; [apply Hr2 |].
    apply Rmult_lt_compat_r; auto.
    rewrite S_INR //.
  }
  exists k.
  rewrite (Haux k k); auto.
  apply Rlt_minus.
  eapply Rle_lt_trans; eauto.
Qed.

Lemma nrw_non_decr (n : nat) :
  (SeriesC (lim_exec n)) <= SeriesC (lim_exec (S n)).
Proof.
  destruct (Rle_lt_dec (SeriesC (lim_exec n)) (SeriesC (lim_exec (S n)))) as [H1 | H2]; auto.
  exfalso.
  specialize (nrw_no_step_down n H2) as (k & Hk).
  assert (0 <= SeriesC (lim_exec (S k + n)%nat)); auto.
  lra.
Qed.

Lemma nrw_AST (n : nat) :
  (SeriesC (lim_exec n)) = 1.
Proof.
  induction n.
  - apply nrw_zero.
  - symmetry.
    apply Rle_antisym; auto.
    rewrite -IHn.
    apply nrw_non_decr.
Qed.
