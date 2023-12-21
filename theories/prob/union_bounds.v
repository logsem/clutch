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


  Lemma ub_lift_dbind_adv_aux (h : A → distr A')
    (μ : distr A) (g : A' → Prop) (ε : A -> R) :
    (forall a, 0 <= ε(a)) ->
    ex_seriesC (λ a, μ(a) * ε(a)) ->
    (∀ a, ub_lift (h a) g (ε a)) ->
    ub_lift (dbind h μ) g (SeriesC (λ a, μ(a) * ε(a))).
  Proof.
    intros Hε Hex Hg P HP.
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
    intros Hε (r & Hε') Hg Hf P HP.
    assert (ex_seriesC (λ a, μ(a) * ε'(a))) as Hex.
    {
      eapply (ex_seriesC_le _ (λ a, μ(a) * r)); [ | apply ex_seriesC_scal_r; auto].
      intros a; split; specialize (Hε' a); real_solver.
    }
    rewrite prob_dbind.
    rewrite /ub_lift in Hf.
    rewrite /ub_lift in Hg.
    (* Can we avoid this? *)
    assert (forall a, Decision (f a)).
    { intro. apply make_decision. }
    assert
      (SeriesC (λ a : A, μ a * prob (h a) (λ a0 : A', negb (P a0))) <=
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
          { apply Hf.
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
    - apply Hf; intros.
      apply bool_decide_eq_true_2; auto.
    - apply SeriesC_le; auto.
      intros a; specialize (Hε' a); real_solver.
 Qed.

 Lemma ub_lift_dzero (f : A → Prop) (ε : R) :
   (ε >= 0) -> ub_lift dzero f ε.
 Proof.
   intros Hpos P HP.
   rewrite /prob.
   rewrite (SeriesC_ext _ (λ _, 0)); [rewrite SeriesC_0; auto; lra | ].
   intro n; destruct (P n); simpl; auto.
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

 Lemma ub_lift_trivial (μ : distr A) (ε : R) :
   (0 <= ε) -> ub_lift μ (λ _, True) ε.
 Proof.
   intros Hμ P HP.
   rewrite /prob.
   rewrite SeriesC_0; auto.
   intro x.
   rewrite (HP x); auto.
 Qed.

 (* Is there a way to prove this without make_decision? *)
 Lemma ub_lift_and (μ : distr A) (f g : A -> Prop) (ε1 ε2 : R) :
   ub_lift μ f ε1 ->
   ub_lift μ g ε2 ->
   ub_lift μ (λ a, f a /\ g a) (ε1 + ε2).
 Proof.
   intros Hf Hg P HP.
   pose proof (make_decision_fun f).
   pose proof (make_decision_fun g).
   set (PAndF := (λ a, bool_decide (f a) || P a)).
   set (PAndG := (λ a, bool_decide (g a) || P a)).
   epose proof (Hf PAndF _) as Haux1.
   epose proof (Hg PAndG _) as Haux2.
   apply (Rle_trans _ (prob μ (λ a : A, negb (PAndF a)) + prob μ (λ a : A, negb (PAndG a)))); [ | lra ].
   rewrite /prob.
   rewrite -SeriesC_plus.
   - apply SeriesC_le.
     + intro a; split; [real_solver | ].
       assert (0 <= μ a); [auto | ].
       rewrite /PAndF /PAndG.
       destruct (P a) eqn:HPeq; do 2 case_bool_decide; simpl; try lra.
       assert (f a /\ g a) as Haux; auto.
       specialize (HP a Haux).
       destruct (P a); done.
     + apply (ex_seriesC_le _ (λ a, 2* μ a)).
       * intro a.
         assert (0 <= μ a); [auto | ].
         destruct (PAndF a);
         destruct (PAndG a);
         simpl; split; lra.
       * apply ex_seriesC_scal_l; auto.
   - apply (ex_seriesC_le _ μ); auto.
     intros; real_solver.
   - apply (ex_seriesC_le _ μ); auto.
     intros; real_solver.
   Unshelve.
   { intros a Hfa.
     rewrite /PAndF.
     rewrite bool_decide_eq_true_2; auto. }
   { intros a Hga.
     rewrite /PAndG.
     rewrite bool_decide_eq_true_2; auto. }
Qed.

Lemma ub_lift_ext (μ : distr A) (f g : A -> Prop) ε :
  (∀ a, f a <-> g a) ->
  ub_lift μ f ε ->
  ub_lift μ g ε.
Proof.
  intros Hequiv Hf P HP.
  epose proof (Hf P _); auto.
  Unshelve.
  intros.
  by apply HP, Hequiv.
Qed.



End ub_theory.

Section ub_instances.

Lemma ub_unif_err (n : nat) (m : fin (S n)) :
  ub_lift (dunifP n) (λ x, x <> m) (1/(n+1)).
Proof.
  intros P HP.
  rewrite /prob.
  rewrite (SeriesC_split_elem (λ a, if negb (P a) then dunifP n a else 0) m).
  - rewrite
      (SeriesC_ext _ (λ a : fin (S n), if bool_decide (a = m) then if negb (P m) then dunifP n m else 0 else 0)); last first.
    { intro; real_solver. }
    rewrite SeriesC_singleton.
    erewrite (SeriesC_ext _ (λ a, 0)); last first.
    { intro; case_bool_decide; auto.
      rewrite HP; auto.
    }
    rewrite SeriesC_0; auto.
    rewrite Rplus_0_r.
    destruct (P m); simpl.
    +  (* ???????? *)
      apply Rdiv_le_0_compat; [lra |].
      apply (Rle_lt_trans _ n); [apply pos_INR | lra].
    + rewrite /pmf/=.
      destruct n; simpl; lra.
  - intro a; destruct (P a); real_solver.
  - apply (ex_seriesC_le _ (dunifP n)); auto.
    intro x; destruct (P x); real_solver.
Qed.

(* More general version *)
Lemma ub_unif_err_nat (n m : nat) :
  ub_lift (dunifP n) (λ x, (fin_to_nat x <> m)) (1/(n+1)).
Proof.
  intros P HP.
  rewrite /prob.
  destruct (le_lt_dec (S n) m) as [Hge | Hlt].
  - erewrite (SeriesC_ext _ (λ a, 0)); last first.
    { intros p.
      specialize (HP p).
      assert (fin_to_nat p <> m) as Haux.
      - pose proof (fin_to_nat_lt p) as Hl; lia.
      - rewrite HP; simpl; auto.
    }
    rewrite SeriesC_0; auto.
    apply Rdiv_le_0_compat; [lra |].
    apply (Rle_lt_trans _ n); [apply pos_INR | lra].
  - set (p := Fin.of_nat_lt Hlt).
    assert (fin_to_nat p = m) as Haux.
    {
      rewrite fin_to_nat_to_fin; auto.
    }
    rewrite (SeriesC_split_elem (λ a, if negb (P a) then dunifP n a else 0) p).
    + rewrite
        (SeriesC_ext _ (λ a : fin (S n), if bool_decide (a = p) then if negb (P p) then dunifP n p else 0 else 0)); last first.
      { intro; real_solver. }
      rewrite SeriesC_singleton.
      erewrite (SeriesC_ext _ (λ a, 0)); last first.
      { intro; case_bool_decide; auto.
        rewrite HP; auto.
        rewrite -Haux.
        intro H0.
        destruct H.
        apply (fin_to_nat_inj _ _ H0).
      }
      rewrite SeriesC_0; auto.
      rewrite Rplus_0_r.
      destruct (P p); simpl.
      *  (* ???????? *)
        apply Rdiv_le_0_compat; [lra |].
        apply (Rle_lt_trans _ n); [apply pos_INR | lra].
      * rewrite /pmf/=.
        destruct n; simpl; lra.
    + intro a; destruct (P a); real_solver.
    + apply (ex_seriesC_le _ (dunifP n)); auto.
      intro x; destruct (P x); real_solver.
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
  - intros P HP.
    simpl.
    rewrite /prob.
    erewrite (SeriesC_ext _ (λ a, 0)); last first.
    { intros p.
      specialize (HP p).
      rewrite HP; auto.
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
  induction l.
  - intros P HP.
    simpl.
    rewrite /prob.
    erewrite (SeriesC_ext _ (λ a, 0)); last first.
    { intros p.
      specialize (HP p).
      rewrite HP; auto.
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
