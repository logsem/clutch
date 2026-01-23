From Stdlib Require Import Reals Psatz.
From clutch.common Require Import ectx_language.
From clutch.prob_lang Require Import notation tactics metatheory.
From clutch.prob_lang Require Export lang.
From clutch.prelude Require Import base Coquelicot_ext Reals_ext stdpp_ext classical.

Local Open Scope R.

Section term.

  Context `{Λ : language}.

  Implicit Types ρ : language.cfg Λ.

  Definition pterm (n : nat) ρ := SeriesC (exec n ρ).

  Definition pterm_nnr (n : nat) ρ := mknonnegreal (pterm n ρ) (pmf_SeriesC_ge_0 _).

  Lemma pterm_le1 (n : nat) ρ : (0 <= 1 - pterm n ρ)%R. 
  Proof.
    specialize (pmf_SeriesC (exec n ρ)) as he.
    rewrite /pterm. apply -> Rcomplements.Rminus_le_0. auto.
  Qed.

  Definition pterm_comp (n : nat) ρ := mknonnegreal (1 - pterm n ρ) (pterm_le1 _ _).

  Lemma pterm_rec (n : nat) ρ : 
    language.to_val ρ.1 = None ->
    pterm (S n) ρ = Expval (step ρ) (pterm n).
  Proof.
    intros.
    rewrite /pterm exec_Sn dbind_mass /Expval.
    apply SeriesC_ext. intros.
    rewrite /step_or_final.
    rewrite /to_final. simpl. rewrite H. 
    auto.
  Qed.

  Lemma AST_pt_lim m ε : 
    SeriesC (lim_exec m) = 1 ->
    ε < 1 -> ∃ n, ε < pterm n m.
  Proof.
    intros Hst?.
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
    exists n. rewrite /pterm. field_simplify in H2. apply H2.
  Qed.

  Lemma pterm_reducible (n : nat) ρ : 
    language.to_val ρ.1 = None ->
    0 < pterm n ρ ->
    reducible ρ.
  Proof.
    rewrite /pterm.
    intros. apply SeriesC_gtz_ex in H0.
    2: apply pmf_pos.
    induction n.
    - destruct H0. rewrite /exec /to_final in H0. simpl in H0.
      rewrite H in H0.
      rewrite dzero_0 in H0. lra.
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

End term.
