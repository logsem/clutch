From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements.
From stdpp Require Export countable.
From clutch.prelude Require Export base Coquelicot_ext Reals_ext stdpp_ext.
From clutch.prob Require Export countable_sum distribution.

Open Scope R.

(** TODO: decidablity should really just be a requirement on [f] and has to be threaded through all the
    lemmas and definitions; nothing in this file in itself needs classical reasoning. *)
Existing Instance make_decision | 1000.

Section partial_graded_lifting.
  Context `{Countable A, Countable B}.
  Context (μ1 : distr A) (μ2 : distr B) (f : A → Prop).

  Definition pgl ε :=
    prob μ1 (λ a, negb (bool_decide (f a))) <= ε.

End partial_graded_lifting.

Section pgl_theory.
  Context `{Countable A, Countable B, Countable A'}.

  Lemma pgl_mon_grading (μ : distr A) (f : A → Prop) ε ε' :
    ε <= ε' → pgl μ f ε → pgl μ f ε'.
  Proof.
    rewrite /pgl.
    intros Hleq Hf.
    lra.
  Qed.

  Lemma pgl_mon_pred (μ : distr A) (f g : A → Prop) ε :
    (∀ a, f a → g a) → pgl μ f ε → pgl μ g ε.
  Proof.
    rewrite /pgl.
    intros Himp Hf.
    etrans; last exact.
    apply SeriesC_le.
    - intros; do 2 case_bool_decide; simpl; split; try lra.
      all: try done.
      exfalso. naive_solver.
    - by apply ex_seriesC_filter_bool_pos.
  Qed.

  Lemma pgl_nonneg_grad (μ : distr A) (f : A → Prop) ε :
    pgl μ f ε → 0 <= ε.
  Proof.
    rewrite /pgl.
    intro Hub.
    etrans; last exact.
    apply prob_ge_0.
  Qed.

  Lemma pgl_dret (a : A) (f : A → Prop) :
    f a → pgl (dret a) f 0.
  Proof.
    intros Hfa.
    rewrite /pgl.
    rewrite prob_dret_false; [lra | ].
    rewrite /negb; auto. by case_bool_decide.
  Qed.

  Lemma pgl_dbind (h : A → distr A')
    (μ1 : distr A) (f : A → Prop) (g : A' → Prop) ε ε' :
    0 <= ε → 0 <= ε' →
    (∀ a, f a → pgl (h a) g ε') → pgl μ1 f ε → pgl (dbind h μ1) g (ε + ε').
  Proof.
    rewrite /pgl.
    intros Hε Hε' Hf Hμ1.
    rewrite prob_dbind.
    eassert
      (SeriesC (λ a : A, μ1 a * prob (h a) (λ a0 : A', negb (bool_decide (g a0)))) <=
         SeriesC (λ a : A, if bool_decide (f a) then μ1 a * ε' else μ1 a)) as Haux.
    {
      apply SeriesC_le.
      - intro a.
        case_bool_decide as Hfa; simplify_eq.
        + split.
          * apply Rmult_le_pos; auto.
            apply prob_ge_0.
          * apply Rmult_le_compat_l; auto.
        + assert (prob μ1 (λ a' : A, negb (negb (bool_decide (a = a')))) <= ε) as H3.
          { etrans; last exact.
            rewrite /prob.
            apply SeriesC_le.
            - intro Hfa0; auto.
              do 2 case_bool_decide; simpl; split; try lra; try done.
              by subst.
            - by apply ex_seriesC_filter_bool_pos.
          }
          split.
          * apply Rmult_le_pos; auto.
            apply prob_ge_0.
          * rewrite <- Rmult_1_r.
            apply Rmult_le_compat; auto.
            -- apply prob_ge_0.
            -- done.
            -- apply prob_le_1.
      - destruct (decide (ε' <= 1)) as [Hleq |Hgt].
        + apply (ex_seriesC_le _ μ1); auto.
          intro; case_bool_decide; simplify_eq; split; try lra; auto.
          * apply Rmult_le_pos; auto.
          * rewrite <- Rmult_1_r.
            apply Rmult_le_compat_l; auto.
        + apply (ex_seriesC_le _ (λ a, ε' * μ1 a)); auto.
          * intro; case_bool_decide; simplify_eq; split; try lra; auto.
            ++ apply Rmult_le_pos; auto.
            ++ rewrite <- Rmult_1_l at 1.
               apply Rmult_le_compat_r; auto.
               lra.
          * apply ex_seriesC_scal_l; auto.
    }
    apply (Rle_trans _ _ _ Haux).
    assert (SeriesC (λ a : A, if bool_decide (f a) then μ1 a * ε' else μ1 a) =
              SeriesC (λ a : A, if bool_decide (f a) then μ1 a * ε' else 0) +
                SeriesC (λ a : A, if (negb (bool_decide (f a))) then μ1 a else 0)) as ->.
    {
      rewrite <- SeriesC_plus.
      - apply SeriesC_ext.
        intro a.
        case_bool_decide; simplify_eq; simpl; lra.
      - destruct (decide (ε' <= 1)) as [Hleq |Hgt].
        + apply (ex_seriesC_le _ μ1); auto.
          intro; case_bool_decide; simplify_eq; split; try lra; auto.
          * apply Rmult_le_pos; auto.
          * rewrite <- Rmult_1_r.
            apply Rmult_le_compat_l; auto.
        + apply (ex_seriesC_le _ (λ a, ε' * μ1 a)); auto.
          * intro; case_bool_decide; simplify_eq; split; try lra; auto.
            ++ apply Rmult_le_pos; auto.
            ++ apply Rmult_le_pos; auto.
          * apply ex_seriesC_scal_l; auto.
      - apply (ex_seriesC_le _ μ1); auto.
        intro; case_bool_decide; simplify_eq; simpl; split; try lra; auto.
    }
    rewrite Rplus_comm.
    apply Rplus_le_compat.
    - done.
    - apply (Rle_trans _ (SeriesC (λ a : A, μ1 a * ε'))).
      + apply SeriesC_le.
        * intro; case_bool_decide; simplify_eq; simpl; split; try lra; auto.
          ++ apply Rmult_le_pos; auto.
          ++ apply Rmult_le_pos; auto.
        * apply ex_seriesC_scal_r; auto.
      + rewrite SeriesC_scal_r.
        rewrite <- Rmult_1_l.
        apply Rmult_le_compat_r; auto.
  Qed.

  Lemma pgl_dbind_adv_aux (h : A → distr A')
    (μ : distr A) (g : A' → Prop) (ε : A → R) :
    (∀ a, 0 <= ε a) →
    ex_seriesC (λ a, μ(a) * ε(a)) →
    (∀ a, pgl (h a) g (ε a)) →
    pgl (dbind h μ) g (SeriesC (λ a, μ(a) * ε(a))).
  Proof.
    intros Hε Hex Hg.
    rewrite /pgl.
    rewrite prob_dbind.
    rewrite /pgl in Hg.
    apply SeriesC_le; auto.
    intro n; split; [ | real_solver].
    apply Rmult_le_pos; auto.
    apply prob_ge_0.
  Qed.

  Lemma pgl_dbind_adv (h : A → distr A')
    (μ : distr A) (f : A → Prop) (g : A' → Prop) (ε : R) (ε' : A → R) :
    (0 <= ε) →
    (exists r, forall a, 0 <= ε'(a) <= r) →
    (∀ a, f a → pgl (h a) g (ε' a)) →
    pgl μ f ε →
    pgl (dbind h μ) g (ε + SeriesC (λ a, μ(a) * ε'(a))).
  Proof.
    rewrite /pgl.
    intros Hε (r & Hε') Hg Hf.
    assert (ex_seriesC (λ a, μ(a) * ε'(a))) as Hex.
    {
      eapply (ex_seriesC_le _ (λ a, μ(a) * r)); [ | apply ex_seriesC_scal_r; auto].
      intros a; split; specialize (Hε' a); real_solver.
    }
    rewrite prob_dbind.
    eassert
      (SeriesC (λ a : A, μ a * prob (h a) (λ a0 : A', negb (bool_decide (g a0)))) <=
         SeriesC (λ a : A, if bool_decide (f a) then μ a * ε'(a) else μ a)) as Haux.
    {
      apply SeriesC_le.
      - intro a.
        case_bool_decide as Hfa; simplify_eq.
        + split.
          * apply Rmult_le_pos; auto.
            apply prob_ge_0.
          * apply Rmult_le_compat_l; auto.
        + assert (prob μ (λ a' : A, negb (negb (bool_decide (a = a')))) <= ε) as H3.
          { etrans; last exact. rewrite /prob.
            apply SeriesC_le; last apply ex_seriesC_filter_bool_pos; try done.
            intros; repeat case_bool_decide; split; simpl; try done; try lra.
            exfalso. naive_solver.
          }
          split.
          * apply Rmult_le_pos; auto.
            apply prob_ge_0.
          * rewrite <- Rmult_1_r.
            apply Rmult_le_compat; auto.
            -- apply prob_ge_0.
            -- done.
            -- apply prob_le_1.
      - destruct (decide (1 <= r)).
        + eapply (ex_seriesC_le _ (λ a, μ(a) * r)); [ | apply ex_seriesC_scal_r; auto].
          intros a; split; specialize (Hε' a); case_bool_decide; try real_solver.
          rewrite <- Rmult_1_r at 1. real_solver.
        + eapply (ex_seriesC_le _ μ); auto.
          intros a; split; specialize (Hε' a); case_bool_decide; try real_solver.
    }
    apply (Rle_trans _ _ _ Haux).
    assert (SeriesC (λ a : A, if bool_decide (f a) then μ a * ε' a else μ a) =
              SeriesC (λ a : A, if bool_decide (f a) then μ a * ε' a else 0) +
                SeriesC (λ a : A, if (negb (bool_decide (f a))) then μ a else 0)) as ->.
    {
      rewrite <- SeriesC_plus.
      - apply SeriesC_ext.
        intro a.
        case_bool_decide; simplify_eq; simpl; lra.
      - eapply ex_seriesC_le; [ | apply Hex].
        intros a; specialize (Hε' a); real_solver.
      - eapply (ex_seriesC_le _ μ); auto.
        intros a; specialize (Hε' a); real_solver.
    }
    rewrite Rplus_comm.
    apply Rplus_le_compat.
    - etrans; last exact. erewrite SeriesC_ext; first by rewrite /prob.
      intros; repeat case_bool_decide; by simpl.
    - apply SeriesC_le; auto.
      intros a; specialize (Hε' a); real_solver.
  Qed.

  Lemma pgl_dzero (f : A → Prop) (ε : R) :
    (ε >= 0) → pgl dzero f ε.
  Proof.
    intros Hpos.
    rewrite /pgl.
    rewrite /prob.
    rewrite (SeriesC_ext _ (λ _, 0)); [rewrite SeriesC_0; auto; lra | ].
    intro n; case_bool_decide; simpl; auto.
  Qed.

  Lemma pgl_pos_R (μ : distr A) (f : A → Prop) (ε : R) :
    pgl μ f ε → pgl μ (λ a, f a ∧ μ a > 0) ε.
  Proof.
    rewrite /pgl.
    intros Hμ.
    eset (Q := (λ a, orb (bool_decide (f a)) (bool_decide (μ a <= 0)))).
    apply (Rle_trans _ (prob μ (λ a : A, negb (Q a)))).
    - apply SeriesC_le.
      + intro a; split.
        * case_bool_decide; simpl; auto; lra.
        * rewrite /Q. repeat case_bool_decide; simpl; try lra.
          exfalso. apply H2. split; try naive_solver. lra.
      + apply (ex_seriesC_le _ μ); auto.
        intro a; destruct (Q a); simpl; split; auto; lra.
    - rewrite /Q.
      etrans; last exact Hμ.
      apply SeriesC_le; last apply ex_seriesC_filter_bool_pos; try done.
      intros. repeat case_bool_decide; split; simpl; try lra; try done.
  Qed.

  Lemma pgl_trivial (μ : distr A) (ε : R) :
    (0 <= ε) → pgl μ (λ _, True) ε.
  Proof.
    intros Hμ.
    rewrite /pgl /prob.
    rewrite SeriesC_0; auto.
    intro x.
    by case_bool_decide.
  Qed.

  Lemma pgl_1 (μ : distr A) (ε : R) P:
    (1<=ε) -> pgl μ P ε.
  Proof.
    rewrite /pgl.
    intros; etrans; [apply prob_le_1|done].
  Qed.

  Lemma pgl_and (μ : distr A) (f g : A → Prop) (ε1 ε2 : R) :
    pgl μ f ε1 →
    pgl μ g ε2 →
    pgl μ (λ a, f a /\ g a) (ε1 + ε2).
  Proof.
    rewrite /pgl.
    intros Hf Hg.
    etrans; last apply Rplus_le_compat; try exact.
    rewrite -SeriesC_plus; [|apply ex_seriesC_filter_bool_pos|apply ex_seriesC_filter_bool_pos]; try done.
    apply SeriesC_le.
    + intro a; split; [real_solver | ].
      pose proof (pmf_pos μ a).
      repeat case_bool_decide; simpl; try done; try lra.
      exfalso. naive_solver.
    + apply ex_seriesC_plus; by apply ex_seriesC_filter_bool_pos.
  Qed.

  Lemma pgl_ext (μ : distr A) (f g : A → Prop) ε :
    (∀ a, f a ↔ g a) →
    pgl μ f ε →
    pgl μ g ε.
  Proof.
    rewrite /pgl.
    intros Hequiv Hf.
    etrans; last exact.
    apply SeriesC_le; last by apply ex_seriesC_filter_bool_pos.
    intros; repeat case_bool_decide; simpl; split; try done.
    exfalso; naive_solver.
  Qed.

  Lemma pgl_epsilon_limit `{Eq: EqDecision A} (μ : distr A) f ε':
    ε'>=0 → (∀ ε, ε>ε' → pgl μ f ε) → pgl μ f ε'.
  Proof.
    rewrite /pgl.
    intros Hε' H'.
    intros. apply real_le_limit.
    intros ε Hε.
    rewrite Rle_minus_l.
    apply H'; first lra.
  Qed.

End pgl_theory.

Section ub_instances.

  Lemma ub_unif_err (n : nat) (m : fin (S n)) :
    pgl (dunifP n) (λ x, x <> m) (1/(n+1)).
  Proof.
    rewrite /pgl /prob.
    erewrite (SeriesC_split_elem _ m).
    - erewrite (SeriesC_ext _ (λ n0, if bool_decide (n0 = m) then dunifP n n0 else 0)); last first.
      + intros. simpl. repeat case_bool_decide; simpl; try lra; done.
      + rewrite SeriesC_singleton.
        erewrite (SeriesC_ext _ (λ a, 0)); last first.
        { intro; repeat case_bool_decide; auto. done.
        }
        rewrite SeriesC_0; auto.
        rewrite Rplus_0_r. replace (INR (S n)) with (n+1); try lra.
        rewrite S_INR. lra.
    - intros. case_bool_decide; simpl; try lra.
      pose proof (dunifP_pos n a). lra.
    - apply (ex_seriesC_le _ (dunifP n)); auto.
      intro x; case_bool_decide; real_solver.
  Qed.

  (* More general version *)
  Lemma ub_unif_err_nat (n m : nat) :
    pgl (dunifP n) (λ x, (fin_to_nat x <> m)) (1/(n+1)).
  Proof.
    rewrite /pgl.
    rewrite /prob.
    destruct (le_lt_dec (S n) m) as [Hge | Hlt].
    - erewrite (SeriesC_ext _ (λ a, 0)); last first.
      { intros p.
        assert (fin_to_nat p <> m) as Haux.
        - pose proof (fin_to_nat_lt p) as Hl; lia.
        - by case_bool_decide.
      }
      rewrite SeriesC_0; auto.
      apply Rdiv_le_0_compat; [lra |].
      apply (Rle_lt_trans _ n); [apply pos_INR | lra].
    - set (p := Fin.of_nat_lt Hlt).
      assert (fin_to_nat p = m) as Haux.
      {
        rewrite fin_to_nat_to_fin; auto.
      }
      rewrite (SeriesC_split_elem _ p).
      + erewrite
          (SeriesC_ext _ (λ a : fin (S n), if bool_decide (a = p) then  dunifP n p else 0)); last first.
        { intro. repeat case_bool_decide; simpl; try lra.
          - exfalso. naive_solver.
          - naive_solver. }
        rewrite SeriesC_singleton.
        erewrite (SeriesC_ext _ (λ a, 0)); last first.
        { intro; repeat case_bool_decide; auto.
          exfalso. apply H. assert (fin_to_nat p = fin_to_nat n0).
          - rewrite Haux. done.
          - apply fin_to_nat_inj. done.
        }
        rewrite SeriesC_0; auto.
        rewrite Rplus_0_r.
        rewrite /pmf /dunifP/dunif.
        rewrite S_INR. lra.
      + intros; case_bool_decide; real_solver.
      + apply (ex_seriesC_le _ (dunifP n)); auto.
        intro x; case_bool_decide; real_solver.
  Qed.

  (* Lifting to ints *)
  Lemma ub_unif_err_int (n : nat) (m : Z) :
    pgl (dunifP n) (λ x, (Z.of_nat (fin_to_nat x) <> m)) (1/(n+1)).
  Proof.
    destruct (Z.le_gt_cases 0 m) as [Hpos | Hneg].
    - apply (pgl_ext _ (λ x : fin (S n), fin_to_nat x ≠ Z.to_nat m)); [ | apply ub_unif_err_nat ].
      intro a; split; intro H.
      + zify.
        intro; simplify_eq.
        destruct_or?;destruct_and?; [done | ].
        simplify_eq. lia.
      + zify.
        intro; simplify_eq.
        destruct_or?;destruct_and?; [done | ].
        lia.
    - apply (pgl_ext _ (λ x, True)); [ | apply pgl_trivial ].
      + intro a; split; intro H; auto.
        zify; intro; simplify_eq; lia.
      + apply Rdiv_le_0_compat; [lra |].
        rewrite <- Rplus_0_l at 1.
        apply Rplus_le_lt_compat; [ apply pos_INR | lra].
  Qed.


  (* Even more general version *)
  Lemma ub_unif_err_list_nat (n : nat) (l : list nat) :
    pgl (dunifP n) (λ x, Forall (λ m, fin_to_nat x <> m) l) ((length l)/(n+1)).
  Proof.
    induction l.
    - simpl.
      rewrite /pgl/prob.
      erewrite (SeriesC_ext _ (λ a, 0)); last first.
      { intros p.
        case_bool_decide; simpl; try done.
        exfalso; naive_solver.
      }
      rewrite SeriesC_0; auto.
      apply Rdiv_le_0_compat; [lra |].
      apply (Rle_lt_trans _ n); [apply pos_INR | lra].
    - rewrite cons_length.
      assert (S (length l) / (n + 1) = 1 / (n + 1) + (length l) / (n + 1)) as ->.
      {
        rewrite -Rdiv_plus_distr //.
        rewrite S_INR Rplus_comm.
        auto.
      }
      eapply pgl_ext.
      + intro; symmetry; apply Forall_cons.
      + apply pgl_and.
        * apply ub_unif_err_nat.
        * apply IHl.
  Qed.


  Lemma ub_unif_err_list_int (n : nat) (l : list Z) :
    pgl (dunifP n) (λ x, Forall (λ m, Z.of_nat (fin_to_nat x) <> m) l) ((length l)/(n+1)).
  Proof.
    rewrite /pgl.
    induction l.
    - simpl.
      rewrite /prob.
      erewrite (SeriesC_ext _ (λ a, 0)); last first.
      { intros p.
        case_bool_decide; simpl; try done.
        exfalso; naive_solver.
      }
      rewrite SeriesC_0; auto.
      apply Rdiv_le_0_compat; [lra |].
      apply (Rle_lt_trans _ n); [apply pos_INR | lra].
    - rewrite cons_length.
      assert (S (length l) / (n + 1) = 1 / (n + 1) + (length l) / (n + 1)) as ->.
      {
        rewrite -Rdiv_plus_distr //.
        rewrite S_INR Rplus_comm.
        auto.
      }
      eapply pgl_ext.
      + intro; symmetry; apply Forall_cons.
      + apply pgl_and.
        * eapply pgl_ext ; [ | eapply (ub_unif_err_int _ a) ]; auto.
        * apply IHl.
  Qed.

End ub_instances.


Section total_graded_lifting.
  Context `{Countable A, Countable B}.
  Context (μ1 : distr A) (μ2 : distr B) (f : A → Prop).

  Definition tgl ε :=
    1-ε <= prob μ1 (λ a, (bool_decide (f a))).

End total_graded_lifting.

Section tgl_theory.
  Context `{Countable A, Countable B, Countable A'}.

  Lemma tgl_implies_pgl (μ : distr A) f ε:
    tgl μ f ε → pgl μ f ε.
  Proof.
    rewrite /tgl /pgl /prob.
    intros Htotal.
    erewrite (SeriesC_ext _ (λ a, if bool_decide (f a) then 0 else pmf a)); last first.
    { intros. repeat case_bool_decide; simpl; done. }
    eapply Rplus_le_reg_l.
    rewrite <-SeriesC_split_pred; last first.
    { apply pmf_ex_seriesC. }
    { intros. apply pmf_pos. }
    apply Rle_minus_l.
    trans (1-ε).
    - pose proof (pmf_SeriesC μ). lra.
    - by apply Htotal.
  Qed.

  Lemma tgl_implies_pgl_strong (μ : distr A) f ε:
    tgl μ f ε → pgl μ f (ε - (1 - SeriesC μ)).
  Proof.
    rewrite /tgl /pgl /prob.
    intros Htotal.
    erewrite (SeriesC_ext _ (λ a, if (bool_decide (f a)) then 0 else μ a)); last first.
    { intros. repeat case_bool_decide; by simpl. }
    eapply Rplus_le_reg_l.
    rewrite <-SeriesC_split_pred; last first.
    { apply pmf_ex_seriesC. }
    { intros. apply pmf_pos. }
    apply Rle_minus_l.
    trans (1-ε).
    - pose proof (pmf_SeriesC μ). lra.
    - by apply Htotal.
  Qed.

  Lemma tgl_mon_grading (μ : distr A) (f : A → Prop) ε ε' :
    ε <= ε' → tgl μ f ε → tgl μ f ε'.
  Proof.
    rewrite /tgl.
    intros Hleq Hf.
    lra.
  Qed.

  Lemma tgl_mon_pred (μ : distr A) (f g : A → Prop) ε :
    (∀ a, f a → g a) → tgl μ f ε → tgl μ g ε.
  Proof.
    rewrite /tgl.
    intros Himp Hf.
    etrans; first exact.
    rewrite /prob.
    apply SeriesC_le; last apply ex_seriesC_filter_bool_pos; try done.
    intros.
    repeat case_bool_decide; simpl; split; try lra; try done.
    exfalso; naive_solver.
  Qed.

  Lemma tgl_nonneg_grad (μ : distr A) (f : A → Prop) ε :
    tgl μ f ε → 0 <= ε.
  Proof.
    rewrite /tgl.
    intro Hub.
    set (P := (λ a : A, true)).
    assert (1-ε <= prob μ P).
    { etrans; first exact. apply SeriesC_le; last apply ex_seriesC_filter_bool_pos; try done.
      intros. case_bool_decide; rewrite /P; try done. }
    pose proof (prob_le_1 μ P).
    lra.
  Qed.

  Lemma tgl_dret (a : A) (f : A → Prop) :
    f a → tgl (dret a) f 0.
  Proof.
    intros Hfa. rewrite /tgl.
    rewrite prob_dret_true; [lra | ].
    by case_bool_decide.
  Qed.

  Lemma tgl_dbind (h : A → distr A')
    (μ1 : distr A) (f : A → Prop) (g : A' → Prop) ε ε' :
    0 <= ε → 0 <= ε' →
    (∀ a, f a → tgl (h a) g ε') → tgl μ1 f ε → tgl (dbind h μ1) g (ε + ε').
  Proof.
    rewrite/tgl.
    (* Handle the (ε' > 1) case separately.
       Can't apply tgl_ge_1 b/c A != A'
       This proof can probably be simplified? *)
    destruct (Rge_decision ε' 1).
    { intros ? ? ? ?.
      rewrite /tgl.
      intros. trans 0.
      - lra.
      - apply prob_ge_0. }
    intros Hε Hε' Hf Hμ1.
    rewrite prob_dbind.
    rewrite /tgl in Hf.
    rewrite /tgl in Hμ1.
    eassert
      (SeriesC (λ a : A, if bool_decide (f a) then μ1 a * (1-ε') else 0) <=
         SeriesC (λ a : A, μ1 a * prob (h a) (λ a0 : A', bool_decide (g a0)))) as Haux.
    {
      apply SeriesC_le.
      - intros. split; case_bool_decide; try lra.
        + apply Rmult_le_pos; try lra. apply pmf_pos.
        + apply Rmult_le_compat_l; first apply pmf_pos. apply Hf; first done.
        + apply Rmult_le_pos; first apply pmf_pos. apply prob_ge_0.
      - apply pmf_ex_seriesC_mult_fn. exists 1. split; first apply prob_ge_0.
        apply prob_le_1.
    }
    etrans; last exact.
    trans ((1-ε)*(1-ε')).
    {
      assert (0 <= ε' * ε); last lra.
      apply Rmult_le_pos; lra.
    }
    assert (SeriesC (λ a : A, if bool_decide (f a) then μ1 a * (1 - ε') else 0) =
              (prob μ1 (λ x, bool_decide (f x))) * (1 - ε')) as ->.
    {
      rewrite /prob. rewrite <-SeriesC_scal_r.
      apply SeriesC_ext.
      intros; case_bool_decide; lra.
    }
    apply Rmult_le_compat_r; first lra.
    etrans; first exact.
    apply SeriesC_le; last apply ex_seriesC_filter_bool_pos; try done.
    intros; repeat case_bool_decide; done.
  Qed.

  Lemma tgl_pos_R (μ : distr A) (f : A → Prop) (ε : R) :
    tgl μ f ε → tgl μ (λ a, f a ∧ μ a > 0) ε.
  Proof.
    rewrite /tgl.
    intros Hμ.
    rewrite /tgl in Hμ.
    eset (Q := (λ a, orb (bool_decide (f a)) (bool_decide (μ a <= 0)))).
    apply (Rle_trans _ (prob μ Q)).
    - etrans; first exact. apply SeriesC_le; last apply ex_seriesC_filter_bool_pos; try done.
      rewrite /Q. intros; repeat case_bool_decide; try done. simpl. done.
    - apply SeriesC_le.
      + intro a; split.
        * destruct (Q a); simpl; auto; lra.
        * rewrite /Q. repeat case_bool_decide; try done.
          exfalso.  apply H4. split; try lra. done.
      + apply (ex_seriesC_le _ μ); auto.
        intro a; case_bool_decide; done.
  Qed.

  Lemma tgl_ge_1 (μ : distr A) f ε:
    ε >= 1 →
    tgl μ f ε.
  Proof.
    intros.
    rewrite /tgl.
    intros. trans 0.
    - lra.
    - apply prob_ge_0.
  Qed.

  Lemma tgl_and (μ : distr A) (f g : A → Prop) (ε1 ε2 : R) :
    0 <= ε1 <= 1 → 0 <= ε2 <= 1 →
    tgl μ f ε1 →
    tgl μ g ε2 →
    tgl μ (λ a, f a /\ g a) (ε1 + ε2).
  Proof.
    intros Hf Hg.
    rewrite /tgl. intros.
    assert (1 - ε1 <= prob μ (λ x, bool_decide (f x))).
    { etrans; first exact. intros. apply SeriesC_le; last apply ex_seriesC_filter_bool_pos; try done.
      intros; repeat case_bool_decide; done. }
    trans (1 - ε1 - ε2); first lra.
    trans ( prob μ (λ x, bool_decide (f x)) - ε2); first lra.
    trans (prob μ (λ x, bool_decide (f x) && bool_decide (g x))); last first.
    { apply SeriesC_le.
      - intros. repeat case_bool_decide; split; simpl; try lra; try apply pmf_pos.
        exfalso; naive_solver.
      - apply ex_seriesC_filter_bool_pos; intros.
        + apply pmf_pos.
        + apply pmf_ex_seriesC.
    }
    assert (1 - ε2 <= prob μ (λ x : A, bool_decide (f x) && bool_decide (g x))
                      - prob μ (λ x : A, bool_decide (f x))+1 ); last lra.
    trans (prob μ (λ x, bool_decide (g x))).
    { etrans; first exact. apply SeriesC_le; last apply ex_seriesC_filter_bool_pos; try done.
      intros; repeat case_bool_decide; done. }
    assert (prob μ (λ x : A, bool_decide (g x)) + prob μ (λ x : A, bool_decide (f x))
            - prob μ (λ x : A, bool_decide (f x)&&bool_decide (g x))<= 1); last lra.
    trans (prob μ (λ x, bool_decide (f x)&& negb (bool_decide (g x))
                        || negb(bool_decide (f x))&& bool_decide (g x)
             ) + prob μ (λ x : A, bool_decide (f x) && bool_decide (g x))
          ); last first.
    { rewrite -SeriesC_plus; [|shelve|shelve].
      trans (SeriesC μ); last apply pmf_SeriesC.
      apply SeriesC_le; last apply pmf_ex_seriesC.
      intros n. pose proof (pmf_pos μ n). repeat case_bool_decide; simpl; lra.
    }
    rewrite Rle_minus_l.
    repeat rewrite -SeriesC_plus.
    { apply SeriesC_le; last shelve.
      intros. pose proof (pmf_pos μ n). split; repeat case_bool_decide; simpl; try lra.
    }
    Unshelve.
    all: try apply ex_seriesC_filter_bool_pos.
    all: try apply pmf_pos.
    all: try apply pmf_ex_seriesC.
    - apply (ex_seriesC_le _ (λ x, 2 * μ x)).
      + intros. pose proof (pmf_pos μ n). repeat case_bool_decide; simpl; lra.
      + apply ex_seriesC_scal_l. apply pmf_ex_seriesC.
    - apply (ex_seriesC_le _ (λ x, 2 * μ x)).
      + intros. pose proof (pmf_pos μ n). repeat case_bool_decide; simpl; lra.
      + apply ex_seriesC_scal_l. apply pmf_ex_seriesC.
  Qed.

  Lemma tgl_ext (μ : distr A) (f g : A → Prop) ε :
    (∀ a, f a ↔ g a) →
    tgl μ f ε →
    tgl μ g ε.
  Proof.
    rewrite /tgl.
    intros Hequiv Hf.
    etrans; first exact.
    apply SeriesC_le; last apply ex_seriesC_filter_bool_pos; try done.
    intros; repeat case_bool_decide; naive_solver.
  Qed.

  Lemma tgl_epsilon_limit `{Eq: EqDecision A} (μ : distr A) f ε':
    ε'>=0 → (forall ε, ε>ε' → tgl μ f ε) → tgl μ f ε'.
  Proof.
    rewrite /tgl.
    intros Hε' H'.
    intros. apply real_le_limit.
    intros ε Hε.
    eassert (1 - (ε' + ε) <= prob μ (λ a, bool_decide (f a))).
    { apply H'. lra. }
    etrans; last exact. lra.
  Qed.

  Lemma tgl_termination_ineq (μ : distr A) f ε:
    tgl μ f ε → 1 - ε <= SeriesC μ.
  Proof.
    rewrite /tgl.
    intros H2.
    trans (prob μ (λ x, bool_decide (f x))).
    - etrans; first exact. apply SeriesC_le; last apply ex_seriesC_filter_bool_pos; try done.
      intros. repeat case_bool_decide; done.
    - apply SeriesC_le; last apply pmf_ex_seriesC.
      intros n; case_bool_decide; pose proof (pmf_pos (μ) n); lra.
  Qed.

End tgl_theory.
