From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements.
From stdpp Require Export countable.
From clutch.prelude Require Export base Coquelicot_ext Reals_ext stdpp_ext.
From clutch.prob Require Export countable_sum distribution.

Open Scope R.

Section union_bounds.
  Context `{Countable A, Countable B}.
  Context (μ1 : distr A) (μ2 : distr B) (f : A -> Prop).

 (*
  Definition isAppr (μL : distr (A)) ε : Prop :=
    (forall a, μL a <= μ1 a) /\ SeriesC (λ a, μ1 a - μL a) <= ε.

  Definition isPAppr (μL : distr A) ε : Prop :=
    isAppr μL ε ∧ (∀ (a : A), (μL a > 0) -> P a).
  *)

  Definition ub_lift ε :=
    forall (P : A -> bool), (forall a, f a -> P a = true) -> prob μ1 (λ a, negb (P a)) <= ε.

End union_bounds.

Section ub_theory.
  Context `{Countable A, Countable B, Countable A'}.


  Lemma UB_mon_grading (μ : distr A) (f : A -> Prop) ε ε' :
    ε <= ε' -> ub_lift μ f ε -> ub_lift μ f ε'.
  Proof.
    intros Hleq Hf P HfP.
    specialize (Hf P HfP).
    lra.
  Qed.

  Lemma UB_mon_pred (μ : distr A) (f g : A -> Prop) ε :
    (∀ a, f a -> g a) -> ub_lift μ f ε -> ub_lift μ g ε.
  Proof.
    intros Himp Hf P HgP.
    assert (∀ a : A, f a → P a = true) as HfP; auto.
  Qed.

  (*
  Lemma isAppr_dret (a : A):
    isAppr (dret a) (dret a) 0.
  Proof.
    split; [intros; try lra | ].
    erewrite SeriesC_ext; last first.
    {
      intro n.
      rewrite Rminus_eq_0.
      auto.
    }
    rewrite SeriesC_0; auto; lra.
  Qed.

  Lemma isPAppr_dret (a : A) (P : A → Prop) :
    P a → isPAppr (dret a) P (dret a) 0.
  Proof.
    split; [apply isAppr_dret |].
    intro x.
    rewrite /pmf /= /dret_pmf /=.
    case_bool_decide as Hx; [rewrite Hx //| lra].
  Qed.
  *)

  Lemma ub_nonneg_grad (μ : distr A) (f : A → Prop) ε :
    ub_lift μ f ε -> 0 <= ε.
  Proof.
    rewrite /ub_lift.
    intro Hub.
    set (P := (λ a : A, true)).
    apply (Rle_trans _ (prob μ (λ a, negb (P a)))).
    - apply prob_ge_0.
    - apply Hub; intros; auto.
  Qed.

  Lemma ub_lift_dret (a : A) (f : A → Prop) :
    f a → ub_lift (dret a) f 0.
  Proof.
    intros Hfa P HfP.
    rewrite prob_dret_false; [lra | ].
    rewrite /negb HfP; auto.
  Qed.

  Lemma ub_lift_dbind (h : A → distr A')
    (μ1 : distr A) (f : A → Prop) (g : A' → Prop) ε ε' :
    0 <= ε -> 0 <= ε' ->
      (∀ a, f a → ub_lift (h a) g ε') → ub_lift μ1 f ε → ub_lift (dbind h μ1) g (ε + ε').
  Proof.
    intros Hε Hε' Hf Hμ1 P HP.
    rewrite prob_dbind.
    rewrite /ub_lift in Hf.
    rewrite /ub_lift in Hμ1.
    (* Can we avoid this? *)
    assert (forall a, Decision (f a)).
    { intro. apply make_decision. }
    assert
      (SeriesC (λ a : A, μ1 a * prob (h a) (λ a0 : A', negb (P a0))) <=
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
          { apply Hμ1.
            intro; auto.
            destruct (bool_decide (a = a0)) eqn:Haa0.
            - intro Hfa0; auto.
              destruct Hfa.
              apply bool_decide_eq_true_1 in Haa0.
              rewrite Haa0.
              auto.
            - intro; auto.
          }
          split.
          * apply Rmult_le_pos; auto.
            apply prob_ge_0.
          * rewrite <- Rmult_1_r.
            apply Rmult_le_compat; auto.
            -- apply prob_ge_0.
            -- rewrite /prob in H3.
               setoid_rewrite negb_involutive in H3.
               rewrite <- (SeriesC_singleton' a (μ1 a)); auto.
               assert (forall n : A,
                          (if bool_decide (a = n) then μ1 a else 0)=
                          (if bool_decide (a = n) then μ1 n else 0)) as Haux2.
               { intro; case_bool_decide; simplify_eq; auto. }
               setoid_rewrite Haux2.
               lra.
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
    assert (SeriesC (λ a : A, if bool_decide (f a) then μ1 a * ε' else μ1 a)
                    =
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
    - apply Hμ1; intros.
      apply bool_decide_eq_true_2; auto.
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

 Lemma ub_lift_pos_R (μ : distr A) (f : A -> Prop) (ε : R) :
    ub_lift μ f ε → ub_lift μ (λ a, f a ∧ μ a > 0) ε.
 Proof.
   intros Hμ P HP.
   rewrite /ub_lift in Hμ.
   set (Q := (λ a, orb (P a) (bool_decide (μ a <= 0)))).
   apply (Rle_trans _ (prob μ (λ a : A, negb (Q a)))).
   - apply SeriesC_le.
     + intro a; split.
       * destruct (P a); simpl; auto; lra.
       * rewrite /Q. destruct (P a); simpl; try lra.
         case_bool_decide; simpl; auto; lra.
     + apply (ex_seriesC_le _ μ); auto.
       intro a; destruct (Q a); simpl; split; auto; lra.
   - apply Hμ.
     intros a Hf.
     rewrite /Q.
     case_bool_decide as Hμa.
     + destruct (P a); auto.
     + assert (P a = true) as ->; auto.
       apply HP; split; auto; lra.
 Qed.

End ub_theory.
