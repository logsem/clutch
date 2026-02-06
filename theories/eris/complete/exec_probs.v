From Stdlib Require Import Reals Psatz.
(* From clutch.common Require Import ectx_language. *)
From clutch.common Require Export language.
(* From clutch.prob_lang Require Export lang. *)
From clutch.prelude Require Import base Coquelicot_ext Reals_ext stdpp_ext classical.
From clutch.prob Require Import graded_predicate_lifting.
From Coquelicot Require Import Rcomplements Rbar Lim_seq.

Local Open Scope R.

Section probp.
  Context `{Λ : language}.

  Context (φ : language.val Λ → Prop).

  Implicit Types ρ : language.cfg Λ.

  Definition probp (n : nat) ρ := prob (exec n ρ) (λ v, negb (bool_decide (φ v))).

  Definition probp_nnr (n : nat) ρ := mknonnegreal (probp n ρ) (prob_ge_0 _ _).

  Lemma probp_le1 (n : nat) ρ : (0 <= 1 - probp n ρ)%R. 
  Proof.
    specialize (pmf_SeriesC (exec n ρ)) as he.
    rewrite /probp. apply -> Rcomplements.Rminus_le_0. auto.
    apply prob_le_1.
  Qed.

  Definition probp_comp (n : nat) ρ := mknonnegreal (1 - probp n ρ) (probp_le1 _ _).

  Lemma probp_rec (n : nat) ρ : 
    language.to_val ρ.1 = None ->
    probp (S n) ρ = Expval (step ρ) (probp n).
  Proof.
    intros.
    rewrite /probp /prob exec_Sn /Expval.
  Admitted.

  Definition lim_probp ρ := real $ Sup_seq (fun n => probp n ρ).

  Lemma lim_probp_rec ρ : 
    lim_probp ρ = Expval (step ρ) lim_probp.
  Proof.
  Admitted.
  (* Lemma AST_pt_lim m ε : 
    SeriesC (lim_exec m) = 1 ->
    ε < 1 -> ∃ n, ε < probp n m.
  Proof.
  Admitted. *)
  (*   intros Hst?.
    rewrite lim_exec_Sup_seq in Hst. intros.
    assert (Lim_seq.is_sup_seq (λ n : nat, Rbar.Finite (SeriesC (exec n m))) (Rbar.Finite 1)). {
      rewrite <- Hst. rewrite rbar_finite_real_eq. 2: {
        apply is_finite_Sup_seq_SeriesC_exec.
      }
      apply Lim_seq.Sup_seq_correct.
    }
    unfold Lim_seq.is_sup_seq in H0.
    assert (0 < 1 - ε). { lra. }
    specialize H0 with (mkposreal (1 - ε) H1).
    simpl in H0. destruct H0 as [H0 [n H2]].
    exists n. rewrite /probp. field_simplify in H2. apply H2.
  Qed. *)

  (* Lemma probp_reducible (n : nat) ρ : 
    language.to_val ρ.1 = None ->
    0 < probp n ρ ->
    reducible ρ.
  Proof.
    rewrite /probp.
    intros. apply SeriesC_gtz_ex in H0; last by intros; case_bool_decide; real_solver.
    (* 2: case_bool_decide. apply pmf_pos. *)
    induction n.
    - destruct H0. rewrite /exec /to_final in H0. simpl in H0.
      rewrite H in H0.
      rewrite dzero_0 in H0. case_bool_decide; simpl in *; real_solver.
    - apply mass_pos_reducible.
      destruct H0.
      simpl in H0.
      rewrite H in H0.
      apply dbind_pos in H0.
      destruct H0 as [ρ' [H0 H1]].
      simpl.
      apply (SeriesC_pos _ ρ').
      + apply pmf_pos.
      + apply pmf_ex_seriesC.
      + apply H1.
  Qed.
 *)
End probp.
