From Coq Require Import Reals Lia Lra.
From clutch.prelude Require Export Reals_ext.
From stdpp Require Export ssreflect.
From Coquelicot Require Import PSeries ElemFct RInt RInt_analysis Continuity.

Section MacLaurin.
  
  Lemma fact_R : ∀ (n : nat), (INR (fact (S n)) = (n + 1) * fact n)%R.
  Proof.
    move=>n /=.
    assert (S n * fact n = (n + 1) * fact n) as H by lia.
    simpl in *.
    rewrite H mult_INR plus_INR INR_1 //.
  Qed.

  Lemma continuous_pow : ∀ (n : nat) (t : R), @continuous Hierarchy.R_UniformSpace Hierarchy.R_UniformSpace (λ x, x ^ n)%R t.
    elim=>[|n IH] t /=.
    - apply continuous_const.
    - apply (@continuous_mult Hierarchy.R_UniformSpace Hierarchy.R_AbsRing ); last done.
      apply continuous_id.
  Qed.

  Lemma continuous_pow_minus : ∀ (n : nat) (x t : R), @continuous Hierarchy.R_UniformSpace Hierarchy.R_UniformSpace (λ y, (x - y) ^ n)%R t.
    move=>n x t.
    unshelve eapply (continuous_comp _ _ _ _ (continuous_pow n (x - t))).
    apply (@continuous_minus _ _ Hierarchy.R_NormedModule).
    { apply continuous_const. }
    { apply continuous_id. }
  Qed.
  
  Lemma integral_taylor_lagrange :
    ∀ (f : R → R) (n : nat) (a x : R),
    (∀ t : R,
       (Rmin a x <= t <= Rmax a x)%R →
       ∀ k, k ≤ S n → Derive.ex_derive_n f k t) →
    (∀ t : R,
       (Rmin a x <= t <= Rmax a x)%R →
       @continuous Hierarchy.R_UniformSpace
         Hierarchy.R_UniformSpace
         (Derive.Derive_n f (S n)) t
    ) →
    f x =
    (sum_f_R0
       (λ (k : nat), (x - a)^k / fact k * Derive.Derive_n f k a)
       n
     + / fact n
       * @RInt Hierarchy.R_CompleteNormedModule
           (λ (t : R), Derive.Derive_n f (S n) t * (x - t)^n)
           a x
    )%R.
  Proof.
    move=>f + a x.
    elim=>[|n IH] Sn_derivable Sn_deriv_cont.
    - simpl.
      rewrite Rdiv_1_r Rinv_1 !Rmult_1_l.
      erewrite RInt_ext; last first.
      { move=>t _ /=.
        rewrite Rmult_1_r //.
      }
      rewrite RInt_Derive; first lra.
      {
        move=> t t_bounds.
        by specialize (Sn_derivable t t_bounds 1 ltac:(reflexivity)).
      }
      {
        move=>t t_bounds.
        by apply Sn_deriv_cont.
      }
    - rewrite IH; last first.
      { move=>t t_bounds.
        apply (@Derive.ex_derive_continuous _ Hierarchy.R_NormedModule).
        fold (Derive.ex_derive_n f (S (S n)) t). 
        by apply Sn_derivable.
      }
      { move=> t t_bounds k k_lt_Sn.
        apply Sn_derivable; first assumption.
        lia.
      }
      cbv [sum_f_R0].
      fold (sum_f_R0).
      rewrite !fact_R Rplus_assoc.
      f_equal.
      rewrite Rinv_mult Rdiv_mult_distr (Rdiv_def _ (fact n))
      (Rmult_comm (/ (n + 1)) (/ fact n))
      (Rmult_comm _ (/ fact n))
      !(Rmult_assoc (/ fact n))
      -Rmult_plus_distr_l.
      f_equal.
      etrans.
      + apply (@is_RInt_unique Hierarchy.R_CompleteNormedModule).
        eapply (@is_RInt_scal_derive_r Hierarchy.R_CompleteNormedModule).
        {       
          move=>t t_bounds.
          apply Derive.Derive_correct.
          fold (Derive.ex_derive_n f (S (S n)) t).
          apply Sn_derivable; first assumption.
          lia.
        }
        { move=> t t_bounds.
          instantiate (1 := (λ (t : R),  / (S n) * - ((x - t) ^ (S n)))%R).
          rewrite -(Rmult_div_l ((x - t) ^ n)%R (S n)); last first.
          { rewrite S_INR.
            pose proof (pos_INR n).
            lra.
          }
          rewrite Rdiv_def (Rmult_comm _ (/ S n)).
          apply Derive.is_derive_scal.
          rewrite -(Ropp_involutive (_ * _)).
          apply (@Derive.is_derive_opp _ Hierarchy.R_NormedModule).
          rewrite (Rmult_comm _ (S n)) Ropp_mult_distr_r -(Rmult_1_l ((x - t) ^ n)%R) Ropp_mult_distr_l -Rmult_assoc.
          apply (Derive.is_derive_pow (λ t, (x - t))%R (S n)).
          replace (- (1))%R with (0 - 1)%R; last lra.
          apply (@Derive.is_derive_minus _ Hierarchy.R_NormedModule).
          { apply (@Derive.is_derive_const _ Hierarchy.R_NormedModule). }
          { apply (@Derive.is_derive_id Hierarchy.R_AbsRing). }
        }
        { 
          move=>t t_bounds.
          apply (@continuous_ext Hierarchy.R_UniformSpace Hierarchy.R_UniformSpace (Derive.Derive_n f (S (S n)))); first done.
          by apply Sn_deriv_cont.
        }
        { move=>t _.
          apply continuous_pow_minus.
        }
        rewrite S_INR.
        unfold Hierarchy.scal.
        simpl.
        unfold Hierarchy.mult.
        simpl.
        eapply is_RInt_ext.
        { move=>t _.
          rewrite -Ropp_mult_distr_r Ropp_mult_distr_l Rmult_comm  Rmult_assoc //.
        } 
        apply (@is_RInt_scal Hierarchy.R_NormedModule),
                (@RInt_correct Hierarchy.R_CompleteNormedModule),
                  ex_RInt_continuous.
        move=>t t_bounds.
        apply (@continuous_mult Hierarchy.R_UniformSpace Hierarchy.R_AbsRing ).
        { apply (continuous_pow_minus (S n)). }
        { by apply Sn_deriv_cont. }
      + rewrite !S_INR.
        unfold Hierarchy.minus, Hierarchy.plus, Hierarchy.opp, Hierarchy.scal.
        simpl.
        unfold Hierarchy.mult.
        simpl.
        rewrite !Rminus_diag Rmult_0_l Ropp_0 !Rmult_0_r Rplus_0_l.
        f_equal; first lra.
        rewrite -Ropp_mult_distr_l Ropp_involutive.
        f_equal.
        apply (@RInt_ext Hierarchy.R_CompleteNormedModule).
        move=>t _.
        lra.
  Qed.

  Lemma integral_maclaurin :
    ∀ (f : R → R) (n : nat) (x : R),
    (∀ t : R,
       (Rmin 0 x <= t <= Rmax 0 x)%R →
       ∀ k, k ≤ S n → Derive.ex_derive_n f k t) →
    (∀ t : R,
       (Rmin 0 x <= t <= Rmax 0 x)%R →
       @continuous Hierarchy.R_UniformSpace
         Hierarchy.R_UniformSpace
         (Derive.Derive_n f (S n)) t
    ) →
    f x =
    (sum_f_R0
       (λ (k : nat), x^k / fact k * Derive.Derive_n f k 0)
       n
     + / fact n
       * @RInt Hierarchy.R_CompleteNormedModule
           (λ (t : R), Derive.Derive_n f (S n) t * (x - t)^n)
           0 x
    )%R.
  Proof.
    move=>f n x Sn_derivable Sn_deriv_cont.
    erewrite sum_eq; last first.
    { move=>k _.
      rewrite -{1}(Rminus_0_r x) //.
    }
    by apply integral_taylor_lagrange.
  Qed. 
End MacLaurin.
