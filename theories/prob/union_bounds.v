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
    prob μ1 (λ a, negb (@bool_decide (f a) (make_decision (f a)))) <= ε.

End union_bounds.

Section ub_theory.
  Context `{Countable A, Countable B, Countable A'}.


  Lemma UB_mon_grading (μ : distr A) (f : A -> Prop) ε ε' :
    ε <= ε' -> ub_lift μ f ε -> ub_lift μ f ε'.
  Proof.
    rewrite /ub_lift.
    intros Hleq Hf.
    lra.
  Qed.

  Lemma UB_mon_pred (μ : distr A) (f g : A -> Prop) ε :
    (∀ a, f a -> g a) -> ub_lift μ f ε -> ub_lift μ g ε.
  Proof.
    rewrite /ub_lift.
    intros Himp Hf.
    etrans; last exact.
    apply SeriesC_le.
    - intros; do 2 case_bool_decide; simpl; split; try lra.
      all: try done.
      exfalso. naive_solver.
    - by apply ex_seriesC_filter_bool_pos.
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
    etrans; last exact.
    apply prob_ge_0.
  Qed.
  
  Lemma ub_lift_dret (a : A) (f : A → Prop) :
    f a → ub_lift (dret a) f 0.
  Proof.
    intros Hfa.
    rewrite /ub_lift.
    rewrite prob_dret_false; [lra | ].
    rewrite /negb; auto. by case_bool_decide.
  Qed.

  Lemma ub_lift_dbind (h : A → distr A')
    (μ1 : distr A) (f : A → Prop) (g : A' → Prop) ε ε' :
    0 <= ε -> 0 <= ε' ->
      (∀ a, f a → ub_lift (h a) g ε') → ub_lift μ1 f ε → ub_lift (dbind h μ1) g (ε + ε').
  Proof.
    rewrite /ub_lift.
    intros Hε Hε' Hf Hμ1.
    rewrite prob_dbind.
    (* Can we avoid this? *)
    assert (forall a, Decision (f a)).
    { intro. apply make_decision. }
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
    - rewrite /prob in Hμ1. etrans; last exact.
      erewrite SeriesC_ext; first done.
      intros; simpl. repeat case_bool_decide; done.
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


  Lemma ub_lift_dbind_adv_aux (h : A → distr A')
    (μ : distr A) (g : A' → Prop) (ε : A -> R) :
    (forall a, 0 <= ε(a)) ->
    ex_seriesC (λ a, μ(a) * ε(a)) ->
    (∀ a, ub_lift (h a) g (ε a)) ->
    ub_lift (dbind h μ) g (SeriesC (λ a, μ(a) * ε(a))).
  Proof.
    intros Hε Hex Hg.
    rewrite /ub_lift.
    rewrite prob_dbind.
    rewrite /ub_lift in Hg.
    apply SeriesC_le; auto.
    intro n; split; [ | real_solver].
    apply Rmult_le_pos; auto.
    apply prob_ge_0.
 Qed.


  Lemma ub_lift_dbind_adv (h : A → distr A')
    (μ : distr A) (f : A -> Prop) (g : A' → Prop) (ε : R) (ε' : A -> R) :
    (0 <= ε) ->
    (exists r, forall a, 0 <= ε'(a) <= r) ->
    (∀ a, f a -> ub_lift (h a) g (ε' a)) →
    ub_lift μ f ε ->
    ub_lift (dbind h μ) g (ε + SeriesC (λ a, μ(a) * ε'(a))).
  Proof.
    rewrite /ub_lift.
    intros Hε (r & Hε') Hg Hf.
    assert (ex_seriesC (λ a, μ(a) * ε'(a))) as Hex.
    {
      eapply (ex_seriesC_le _ (λ a, μ(a) * r)); [ | apply ex_seriesC_scal_r; auto].
      intros a; split; specialize (Hε' a); real_solver.
    }
    rewrite prob_dbind.
    (* Can we avoid this? *)
    assert (forall a, Decision (f a)).
    { intro. apply make_decision. }
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
            -- rewrite /prob in H3.
               setoid_rewrite negb_involutive in H3.
               rewrite <- (SeriesC_singleton' a (μ a)); auto.
               assert (forall n : A,
                          (if bool_decide (a = n) then μ a else 0)=
                          (if bool_decide (a = n) then μ n else 0)) as Haux2.
               { intro; case_bool_decide; simplify_eq; auto. }
               setoid_rewrite Haux2.
               lra.
            -- apply prob_le_1.
      - destruct (decide (1 <= r)).
        + eapply (ex_seriesC_le _ (λ a, μ(a) * r)); [ | apply ex_seriesC_scal_r; auto].
          intros a; split; specialize (Hε' a); case_bool_decide; try real_solver.
          rewrite <- Rmult_1_r at 1. real_solver.
        + eapply (ex_seriesC_le _ μ); auto.
          intros a; split; specialize (Hε' a); case_bool_decide; try real_solver.
    }
    apply (Rle_trans _ _ _ Haux).
    assert (SeriesC (λ a : A, if bool_decide (f a) then μ a * ε' a else μ a)
                    =
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

 Lemma ub_lift_dzero (f : A → Prop) (ε : R) :
   (ε >= 0) -> ub_lift dzero f ε.
 Proof.
   intros Hpos.
   rewrite /ub_lift.
   rewrite /prob.
   rewrite (SeriesC_ext _ (λ _, 0)); [rewrite SeriesC_0; auto; lra | ].
   intro n; case_bool_decide; simpl; auto.
 Qed.

 Lemma ub_lift_pos_R (μ : distr A) (f : A -> Prop) (ε : R) :
    ub_lift μ f ε → ub_lift μ (λ a, f a ∧ μ a > 0) ε.
 Proof.
   rewrite /ub_lift.
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
     Unshelve.
     apply make_decision.
 Qed.

 Lemma ub_lift_trivial (μ : distr A) (ε : R) :
   (0 <= ε) -> ub_lift μ (λ _, True) ε.
 Proof.
   intros Hμ.
   rewrite /ub_lift /prob.
   rewrite SeriesC_0; auto.
   intro x.
   by case_bool_decide.
 Qed.

 (* Is there a way to prove this without make_decision? *)
 Lemma ub_lift_and (μ : distr A) (f g : A -> Prop) (ε1 ε2 : R) :
   ub_lift μ f ε1 ->
   ub_lift μ g ε2 ->
   ub_lift μ (λ a, f a /\ g a) (ε1 + ε2).
 Proof.
   rewrite /ub_lift.
   intros Hf Hg.
   pose proof (make_decision_fun f).
   pose proof (make_decision_fun g).
   etrans; last apply Rplus_le_compat; try exact.
   rewrite -SeriesC_plus; [|apply ex_seriesC_filter_bool_pos|apply ex_seriesC_filter_bool_pos]; try done.
   apply SeriesC_le.
   + intro a; split; [real_solver | ].
     pose proof (pmf_pos μ a).
     repeat case_bool_decide; simpl; try done; try lra.
     exfalso. naive_solver.
   + apply ex_seriesC_plus; by apply ex_seriesC_filter_bool_pos.
Qed.

Lemma ub_lift_ext (μ : distr A) (f g : A -> Prop) ε :
  (∀ a, f a <-> g a) ->
  ub_lift μ f ε ->
  ub_lift μ g ε.
Proof.
  rewrite /ub_lift.
  intros Hequiv Hf.
  etrans; last exact.
  apply SeriesC_le; last by apply ex_seriesC_filter_bool_pos.
  intros; repeat case_bool_decide; simpl; split; try done.
  exfalso; naive_solver.
Qed.

Lemma ub_lift_epsilon_limit `{Eq: EqDecision A} (μ : distr A) f ε':
  ε'>=0 -> (forall ε, ε>ε' -> ub_lift μ f ε) -> ub_lift μ f ε'.
Proof.
  rewrite /ub_lift.
  intros Hε' H'.
  intros. apply real_le_limit.
  intros ε Hε.
  rewrite Rle_minus_l.
  apply H'; first lra.
Qed.

End ub_theory.

Section ub_instances.

Lemma ub_unif_err (n : nat) (m : fin (S n)) :
  ub_lift (dunifP n) (λ x, x <> m) (1/(n+1)).
Proof.
  rewrite /ub_lift /prob.
  erewrite (SeriesC_split_elem _ m).
  - erewrite
      (SeriesC_ext ); last first. 
    + intros. instantiate (1:=  λ n0, if bool_decide (n0=m) then dunifP n n0 else 0). simpl.
      repeat case_bool_decide; simpl; try lra. done.
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
  ub_lift (dunifP n) (λ x, (fin_to_nat x <> m)) (1/(n+1)).
Proof.
  rewrite /ub_lift.
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
  ub_lift (dunifP n) (λ x, (Z.of_nat (fin_to_nat x) <> m)) (1/(n+1)).
Proof.
  destruct (Z.le_gt_cases 0 m) as [Hpos | Hneg].
  - apply (ub_lift_ext _ (λ x : fin (S n), fin_to_nat x ≠ Z.to_nat m)); [ | apply ub_unif_err_nat ].
    intro a; split; intro H.
    + zify.
      intro; simplify_eq.
      destruct_or?;destruct_and?; [done | ].
      simplify_eq. lia.
    + zify.
      intro; simplify_eq.
      destruct_or?;destruct_and?; [done | ].
      lia.
  - apply (ub_lift_ext _ (λ x, True)); [ | apply ub_lift_trivial ].
    + intro a; split; intro H; auto.
      zify; intro; simplify_eq; lia.
    + apply Rdiv_le_0_compat; [lra |].
      rewrite <- Rplus_0_l at 1.
      apply Rplus_le_lt_compat; [ apply pos_INR | lra].
Qed.


(* Even more general version *)
Lemma ub_unif_err_list_nat (n : nat) (l : list nat) :
  ub_lift (dunifP n) (λ x, Forall (λ m, fin_to_nat x <> m) l) ((length l)/(n+1)).
Proof.
  induction l.
  - simpl.
    rewrite /ub_lift/prob.
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
    eapply ub_lift_ext.
    + intro; symmetry; apply Forall_cons.
    + apply ub_lift_and.
      * apply ub_unif_err_nat.
      * apply IHl.
Qed.


Lemma ub_unif_err_list_int (n : nat) (l : list Z) :
  ub_lift (dunifP n) (λ x, Forall (λ m, Z.of_nat (fin_to_nat x) <> m) l) ((length l)/(n+1)).
Proof.
  rewrite /ub_lift.
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
    eapply ub_lift_ext.
    + intro; symmetry; apply Forall_cons.
    + apply ub_lift_and.
      * eapply ub_lift_ext ; [ | eapply (ub_unif_err_int _ a) ]; auto.
      * apply IHl.
Qed.

End ub_instances.


Section total_union_bounds.
  Context `{Countable A, Countable B}.
  Context (μ1 : distr A) (μ2 : distr B) (f : A -> Prop).

  Definition total_ub_lift ε :=
    1-ε <= prob μ1 (λ a, (@bool_decide (f a) (make_decision (f a)))).

End total_union_bounds.

Section total_ub_theory.
  Context `{Countable A, Countable B, Countable A'}.

  Lemma total_ub_lift_implies_ub_lift (μ : distr A) f ε:
    total_ub_lift μ f ε -> ub_lift μ f ε.
  Proof.
    rewrite /total_ub_lift /ub_lift /prob.
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

  Lemma total_ub_lift_implies_ub_lift_strong (μ : distr A) f ε:
    total_ub_lift μ f ε -> ub_lift μ f (ε - (1 - SeriesC μ)).
  Proof.
    rewrite /total_ub_lift /ub_lift /prob.
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

  
  Lemma total_UB_mon_grading (μ : distr A) (f : A -> Prop) ε ε' :
    ε <= ε' -> total_ub_lift μ f ε -> total_ub_lift μ f ε'.
  Proof.
    rewrite /total_ub_lift.
    intros Hleq Hf.
    lra.
  Qed.

  Lemma total_UB_mon_pred (μ : distr A) (f g : A -> Prop) ε :
    (∀ a, f a -> g a) -> total_ub_lift μ f ε -> total_ub_lift μ g ε.
  Proof.
    rewrite /total_ub_lift.
    intros Himp Hf.
    etrans; first exact.
    rewrite /prob.
    apply SeriesC_le; last apply ex_seriesC_filter_bool_pos; try done.
    intros.
    repeat case_bool_decide; simpl; split; try lra; try done.
    exfalso; naive_solver.
  Qed.

  Lemma total_ub_nonneg_grad (μ : distr A) (f : A → Prop) ε :
    total_ub_lift μ f ε -> 0 <= ε.
  Proof.
    rewrite /total_ub_lift.
    intro Hub.
    set (P := (λ a : A, true)).
    assert (1-ε <= prob μ P).
    { etrans; first exact. apply SeriesC_le; last apply ex_seriesC_filter_bool_pos; try done.
      intros. case_bool_decide; rewrite /P; try done. }
    pose proof (prob_le_1 μ P).
    lra. 
  Qed.

  Lemma totalub_lift_dret (a : A) (f : A → Prop) :
    f a → total_ub_lift (dret a) f 0.
  Proof.
    intros Hfa. rewrite /total_ub_lift.
    rewrite prob_dret_true; [lra | ].
    by case_bool_decide.
  Qed.

  Lemma total_ub_lift_dbind (h : A → distr A')
    (μ1 : distr A) (f : A → Prop) (g : A' → Prop) ε ε' :
    0 <= ε -> 0 <= ε' ->
    (∀ a, f a → total_ub_lift (h a) g ε') → total_ub_lift μ1 f ε → total_ub_lift (dbind h μ1) g (ε + ε').
  Proof.
    rewrite/total_ub_lift.
    (* Handle the (ε' > 1) case separately.
       Can't apply total_ub_lift_ge_1 b/c A != A'
       This proof can probably be simplified? *)
    destruct (Rge_decision ε' 1).
    { intros ? ? ? ?.
      rewrite /total_ub_lift.
      intros. trans 0.
      - lra.
      - apply prob_ge_0. }
    intros Hε Hε' Hf Hμ1.
    rewrite prob_dbind.
    rewrite /total_ub_lift in Hf.
    rewrite /total_ub_lift in Hμ1.
    (* Can we avoid this? *)
    assert (forall a, Decision (f a)).
    { intro. apply make_decision. }
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
            (prob μ1 (λ x, bool_decide (f x))) * (1 - ε')
           ) as ->.
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


  (* not true if μ < 1)*)
  (* Lemma total_ub_lift_dbind_adv_aux (h : A → distr A') *)
  (*   (μ : distr A) (g : A' → Prop) (ε : A -> R) : *)
  (*   (forall a, 0 <= ε(a)) -> *)
  (*   ex_seriesC (λ a, μ(a) * ε(a)) -> *)
  (*   (∀ a, total_ub_lift (h a) g (ε a)) -> *)
  (*   total_ub_lift (dbind h μ) g (SeriesC (λ a, μ(a) * ε(a))). *)
  (* Proof. *)
  (* Admitted.  *)

  (* skipped for now as not that useful, it might also be untrue if μ < 1 *)
  (* Lemma total_ub_lift_dbind_adv (h : A → distr A') *)
  (*   (μ : distr A) (f : A -> Prop) (g : A' → Prop) (ε : R) (ε' : A -> R) : *)
  (*   (0 <= ε <= 1) -> *)
  (*   (exists r, forall a, 0 <= ε'(a) <= r) -> *)
  (*   (∀ a, f a -> total_ub_lift (h a) g (ε' a)) → *)
  (*   total_ub_lift μ f ε -> *)
  (*   total_ub_lift (dbind h μ) g (ε + SeriesC (λ a, μ(a) * ε'(a))). *)
  (* Proof. *)
  (*   intros Hε (r & Hε') Hg Hf P HP. *)
  (*   assert (ex_seriesC (λ a, μ(a) * ε'(a))) as Hex. *)
  (*   { *)
  (*     eapply (ex_seriesC_le _ (λ a, μ(a) * r)); [ | apply ex_seriesC_scal_r; auto]. *)
  (*     intros a; split; specialize (Hε' a); real_solver. *)
  (*   } *)
  (*   rewrite prob_dbind. *)
  (*   rewrite /ub_lift in Hf. *)
  (*   rewrite /ub_lift in Hg. *)
  (*   (* Can we avoid this? *) *)
  (*   assert (forall a, Decision (f a)). *)
  (*   { intro. apply make_decision. } *)
  (*   assert *)
  (*     (SeriesC (λ a : A, μ a * prob (h a) (λ a0 : A', negb (P a0))) <= *)
  (*        SeriesC (λ a : A, if bool_decide (f a) then μ a * ε'(a) else μ a)) as Haux. *)
  (*   { *)
  (*     apply SeriesC_le. *)
  (*     - intro a. *)
  (*       case_bool_decide as Hfa; simplify_eq. *)
  (*       + split. *)
  (*         * apply Rmult_le_pos; auto. *)
  (*           apply prob_ge_0. *)
  (*         * apply Rmult_le_compat_l; auto. *)
  (*       + assert (prob μ (λ a' : A, negb (negb (bool_decide (a = a')))) <= ε) as H3. *)
  (*         { apply Hf. *)
  (*           intro; auto. *)
  (*           destruct (bool_decide (a = a0)) eqn:Haa0. *)
  (*           - intro Hfa0; auto. *)
  (*             destruct Hfa. *)
  (*             apply bool_decide_eq_true_1 in Haa0. *)
  (*             rewrite Haa0. *)
  (*             auto. *)
  (*           - intro; auto. *)
  (*         } *)
  (*         split. *)
  (*         * apply Rmult_le_pos; auto. *)
  (*           apply prob_ge_0. *)
  (*         * rewrite <- Rmult_1_r. *)
  (*           apply Rmult_le_compat; auto. *)
  (*           -- apply prob_ge_0. *)
  (*           -- rewrite /prob in H3. *)
  (*              setoid_rewrite negb_involutive in H3. *)
  (*              rewrite <- (SeriesC_singleton' a (μ a)); auto. *)
  (*              assert (forall n : A, *)
  (*                        (if bool_decide (a = n) then μ a else 0)= *)
  (*                        (if bool_decide (a = n) then μ n else 0)) as Haux2. *)
  (*              { intro; case_bool_decide; simplify_eq; auto. } *)
  (*              setoid_rewrite Haux2. *)
  (*              lra. *)
  (*           -- apply prob_le_1. *)
  (*     - destruct (decide (1 <= r)). *)
  (*       + eapply (ex_seriesC_le _ (λ a, μ(a) * r)); [ | apply ex_seriesC_scal_r; auto]. *)
  (*         intros a; split; specialize (Hε' a); case_bool_decide; try real_solver. *)
  (*         rewrite <- Rmult_1_r at 1. real_solver. *)
  (*       + eapply (ex_seriesC_le _ μ); auto. *)
  (*         intros a; split; specialize (Hε' a); case_bool_decide; try real_solver. *)
  (*   } *)
  (*   apply (Rle_trans _ _ _ Haux). *)
  (*   assert (SeriesC (λ a : A, if bool_decide (f a) then μ a * ε' a else μ a) *)
  (*           = *)
  (*             SeriesC (λ a : A, if bool_decide (f a) then μ a * ε' a else 0) + *)
  (*               SeriesC (λ a : A, if (negb (bool_decide (f a))) then μ a else 0)) as ->. *)
  (*   { *)
  (*     rewrite <- SeriesC_plus. *)
  (*     - apply SeriesC_ext. *)
  (*       intro a. *)
  (*       case_bool_decide; simplify_eq; simpl; lra. *)
  (*     - eapply ex_seriesC_le; [ | apply Hex]. *)
  (*       intros a; specialize (Hε' a); real_solver. *)
  (*     - eapply (ex_seriesC_le _ μ); auto. *)
  (*       intros a; specialize (Hε' a); real_solver. *)
  (*   } *)
  (*   rewrite Rplus_comm. *)
  (*   apply Rplus_le_compat. *)
  (*   - apply Hf; intros. *)
  (*     apply bool_decide_eq_true_2; auto. *)
  (*   - apply SeriesC_le; auto. *)
  (*     intros a; specialize (Hε' a); real_solver. *)
  (* Qed. *)

  (* NOT TRUE *)
  (* Lemma total_ub_lift_dzero (f : A → Prop) (ε : R) : *)
  (*   (ε >= 0) -> total_ub_lift dzero f ε. *)
  (* Proof. *)
  (*   intros Hpos P HP. *)
  (*   rewrite /prob. *)
  (*   rewrite (SeriesC_ext _ (λ _, 0)); [rewrite SeriesC_0; auto; lra | ]. *)
  (*   intro n; destruct (P n); simpl; auto. *)
  (* Qed. *)

  Lemma total_ub_lift_pos_R (μ : distr A) (f : A -> Prop) (ε : R) :
    total_ub_lift μ f ε → total_ub_lift μ (λ a, f a ∧ μ a > 0) ε.
  Proof.
    rewrite /total_ub_lift.
    intros Hμ.
    rewrite /total_ub_lift in Hμ.
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
        Unshelve.
        apply make_decision.
  Qed.

  (* not true! *)
  (* Lemma ub_lift_trivial (μ : distr A) (ε : R) : *)
  (*   (0 <= ε) -> ub_lift μ (λ _, True) ε. *)
  (* Proof. *)
  (*   intros Hμ P HP. *)
  (*   rewrite /prob. *)
  (*   rewrite SeriesC_0; auto. *)
  (*   intro x. *)
  (*   rewrite (HP x); auto. *)
  (* Qed. *)

  Lemma total_ub_lift_ge_1 (μ : distr A) f ε:
    ε >= 1 ->
    total_ub_lift μ f ε.
  Proof.
    intros.
    rewrite /total_ub_lift.
    intros. trans 0.
    - lra.
    - apply prob_ge_0.
  Qed. 
      
  (* Is there a way to prove this without make_decision? *)
  Lemma total_ub_lift_and (μ : distr A) (f g : A -> Prop) (ε1 ε2 : R) :
    0 <= ε1 <= 1 -> 0 <= ε2 <= 1 -> 
    total_ub_lift μ f ε1 ->
    total_ub_lift μ g ε2 ->
    total_ub_lift μ (λ a, f a /\ g a) (ε1 + ε2).
  Proof.
    intros Hf Hg.
    pose proof (make_decision_fun f).
    pose proof (make_decision_fun g).
    rewrite /total_ub_lift. intros.
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

  Lemma total_ub_lift_ext (μ : distr A) (f g : A -> Prop) ε :
    (∀ a, f a <-> g a) ->
    total_ub_lift μ f ε ->
    total_ub_lift μ g ε.
  Proof.
    rewrite /total_ub_lift.
    intros Hequiv Hf.
    etrans; first exact.
    apply SeriesC_le; last apply ex_seriesC_filter_bool_pos; try done.
    intros; repeat case_bool_decide; naive_solver.
  Qed.

  Lemma total_ub_lift_epsilon_limit `{Eq: EqDecision A} (μ : distr A) f ε':
    ε'>=0 -> (forall ε, ε>ε' -> total_ub_lift μ f ε) -> total_ub_lift μ f ε'.
  Proof.
    rewrite /total_ub_lift.
    intros Hε' H'.
    intros. apply real_le_limit.
    intros ε Hε.
    eassert (1 - (ε' + ε) <= prob μ (λ a, bool_decide (f a))).
    { apply H'. lra. }
    etrans; last exact. lra.
  Qed.

  Lemma total_ub_lift_termination_ineq (μ : distr A) f ε:
    total_ub_lift μ f ε -> 1 - ε <= SeriesC μ.
  Proof.
    rewrite /total_ub_lift.
    intros H2.
    assert (∀ x, Decision (f x)).
    { intros. apply make_decision. }
    trans (prob μ (λ x, bool_decide (f x))).
    - etrans; first exact. apply SeriesC_le; last apply ex_seriesC_filter_bool_pos; try done.
      intros. repeat case_bool_decide; done. 
    - apply SeriesC_le; last apply pmf_ex_seriesC.
      intros n; case_bool_decide; pose proof (pmf_pos (μ) n); lra. 
  Qed.
  
End total_ub_theory.
