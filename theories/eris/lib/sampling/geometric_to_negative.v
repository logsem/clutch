From clutch.eris.lib.sampling.negative_binomial Require Import interface.
From clutch.eris.lib.sampling.geometric Require Import interface.
From clutch.eris.lib.sampling Require Import utils.
From Coquelicot Require Import PSeries ElemFct RInt RInt_analysis Continuity.

Section math.
  
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
 
  Definition f (α : R) (x : R) := exp (α * ln x).
  Lemma f_pow : ∀ (n : nat) (x : R), (0 < x)%R → (f n x = x ^ n)%R.
  Proof.
    move=>n x x_pos.
    unfold f.
    rewrite Rmult_comm -exp_pow exp_ln //.
  Qed.

  Lemma f_plus (α β x: R) : (f (α + β) x = f α x * f β x)%R.
  Proof.
    unfold f.
    rewrite Rmult_plus_distr_r exp_plus //.
  Qed.

  Lemma f_opp (α x : R) : (f (-α) x = / f α x)%R.
  Proof.
    unfold f.
    rewrite -Ropp_mult_distr_l exp_Ropp //.
  Qed.

  Lemma f_pos (α x : R) : (0 < f α x)%R.
  Proof.
    unfold f.
    apply exp_pos.
  Qed.

  Lemma continuous_f (α x : R) : (0 < x)%R → @continuous Hierarchy.R_UniformSpace Hierarchy.R_UniformSpace (f α) x.
  Proof.
    move=>x_pos.
    unfold f.
    apply continuous_exp_comp,
            (@continuous_scal _ _ Hierarchy.R_NormedModule).
    { apply continuous_const. }
    { by apply continuous_ln. }
  Qed.
    
  Lemma is_derive_f : ∀ α x, (0 < x)%R → @Derive.is_derive _ Hierarchy.R_NormedModule (f α) x (α * f (α - 1) x)%R.
  Proof.
    move=>α x x_pos.
    unfold f.
    rewrite Rmult_minus_distr_r Rmult_1_l exp_plus -(ln_Rinv x) // exp_ln; last real_solver.
    rewrite -Rmult_assoc (Rmult_comm _ (/ x)) -Rmult_assoc (Rmult_comm _ α).
    apply (@Derive.is_derive_comp _ Hierarchy.R_NormedModule exp).
    - apply is_derive_exp.
    - apply Derive.is_derive_scal, is_derive_ln, x_pos.
  Qed.

  Lemma derive_f : ∀ α x, (0 < x)%R → Derive.Derive (f α) x = (α * f (α - 1) x)%R.
  Proof.
    move=>α x x_pos.
    apply Derive.is_derive_unique, is_derive_f, x_pos.
  Qed.
  
  Definition g α x := f α (x + 1)%R.

  Lemma g_pos : ∀ (α x : R), (0 < g α x)%R.
  Proof.
    move=>α x.
    unfold g, f.
    apply exp_pos.
  Qed.
  
  Lemma g_plus (α β x: R) : (g (α + β) x = g α x * g β x)%R.
  Proof.
    apply f_plus.
  Qed.
  
  Lemma g_opp (α x: R) : (g (-α) x = / g α x)%R.
  Proof.
    unfold g.
    apply f_opp.
  Qed.
  
  Lemma is_derive_g : ∀ α x, (-1 < x)%R → @Derive.is_derive _ Hierarchy.R_NormedModule (g α) x (α * g (α - 1) x)%R.
  Proof.
    move=>α x x_pos.
    unfold g.
    rewrite -(Rmult_1_l (α * _)%R).
    apply (@Derive.is_derive_comp _ Hierarchy.R_NormedModule (f α)).
    - apply is_derive_f.
      lra.
    - rewrite -{2}(Rplus_0_r 1).
      apply (@Derive.is_derive_plus _ Hierarchy.R_NormedModule id (const 1%R) x 1%R 0%R).
      { apply (@Derive.is_derive_id Hierarchy.R_AbsRing). }
      { apply (@Derive.is_derive_const Hierarchy.R_AbsRing). }
  Qed.

  Lemma derive_g : ∀ α x, (-1 < x)%R → Derive.Derive (g α) x = (α * g (α - 1) x)%R.
  Proof.
    move=>α x x_bound.
    apply Derive.is_derive_unique, is_derive_g, x_bound.
  Qed.

  Lemma continuous_g : ∀ α x, (-1 < x)%R → 
                              @continuous Hierarchy.R_UniformSpace Hierarchy.R_UniformSpace (g α) x.
  Proof.
    move=>α x x_gt.
    apply (@Derive.ex_derive_continuous _ Hierarchy.R_NormedModule).
    eexists.
    by apply is_derive_g.
  Qed.
  
  Fixpoint prod_sub_n (n : nat) (α : R) :=
    match n with
    | 0%R => 1%R
    | S m => (α * prod_sub_n m (α - 1))%R
    end.

  Lemma prod_sub_n_last :
    ∀ (n : nat) (α : R),
    (prod_sub_n (S n) α = prod_sub_n n α * (α - n))%R.
  Proof.
    elim=>[|n IH] α.
    - simpl. lra.
    - rewrite S_INR /=.
      pose proof (IH (α - 1)%R) as H.
      simpl in H.
      rewrite H.
      lra.
  Qed.

  Lemma is_derive_n_g :
    ∀ n α x,
    (-1 < x)%R →
    Derive.is_derive_n (g α) n x ((prod_sub_n n α) * g (α - n) x)%R.
  Proof.
    elim=>[|n IH] α x x_pos;
          first rewrite Rminus_0_r Rmult_1_l //.
    rewrite S_INR prod_sub_n_last Rminus_plus_distr Rmult_assoc -derive_g // -Derive.Derive_scal.
    simpl.
    eapply Derive.is_derive_ext_loc.
    {
      unfold Hierarchy.locally.
      set (half_x :=  ((x + 1) / 2)%R).
      assert (0 < half_x)%R as half_x_pos by (unfold half_x; lra).
      exists {| pos := half_x ; cond_pos := half_x_pos |}.
      simpl.
      move=>y.
      unfold Hierarchy.ball.
      simpl.
      unfold Hierarchy.AbsRing_ball, Hierarchy.abs, Hierarchy.minus, Hierarchy.plus, Hierarchy.opp.
      simpl.
      move=>y_near_x.
      assert (-1 < y)%R as y_pos.
      { unfold half_x in y_near_x.
        apply Rabs_def2 in y_near_x as [y_lt y_gt].
        lra.
      }
      rewrite (Derive.is_derive_n_unique (g α) n _ _ (IH _ _ y_pos)) //.
    }
    apply Derive.Derive_correct, Derive.ex_derive_scal.
    eexists.
    by apply is_derive_g.
  Qed.

  Lemma ex_derive_n_g :
    ∀ n α x,
    (-1 < x)%R →
    Derive.ex_derive_n (g α) n x.
  Proof.
    move=>[//|n] α x x_gt.
    simpl.
    eexists.
    by apply (is_derive_n_g (S n)).
  Qed.

  Definition Rem (α : R) (n : nat) (x : R) :=
    (prod_sub_n (S n) α / fact n *
         @RInt Hierarchy.R_CompleteNormedModule
           (λ t : R,
                g (α - 1) t *
                  ((x - t) / (1 + t)) ^ n) 0 x)%R.


  Definition Coeff (α x : R) : R :=
    if (Rle_dec 0 α)
    then g α (Rmax 0 x)
    else g α (Rmin 0 x).

  Lemma Coeff_pos :
    ∀ (α x : R), (0 < Coeff α x)%R.
  Proof.
    move=>α x.
    unfold Coeff.
    destruct (Rle_dec 0 α);
      apply g_pos.
  Qed.
  
  Lemma f_increasing :
    ∀ (α : R),
    (0 <= α)%R →
    ∀ (x y : R),
    (0 < x <= y)%R →
    (f α x <= f α y)%R.
  Proof.
    move=>α α_pos x y [x_pos y_ge_x].
    unfold f.
    destruct (Req_dec x y) as [-> | x_ne_y]; first reflexivity.
    destruct (Req_dec α 0) as [-> | α_ne_0]; first rewrite !Rmult_0_l //.
    left.
    apply exp_increasing,
            Rmult_lt_compat_l; first lra.
    apply ln_increasing; lra.
  Qed.

  Lemma f_decreasing :
    ∀ (α : R),
    (α < 0)%R →
    ∀ (x y : R),
    (0 < x <= y)%R →
    (f α y <= f α x)%R.
  Proof.
    move=>α α_pos x y [x_pos y_ge_x].
    unfold f.
    destruct (Req_dec x y) as [-> | x_ne_y]; first reflexivity.
    destruct (Req_dec α 0) as [-> | α_ne_0]; first rewrite !Rmult_0_l //.
    left.
    apply exp_increasing,
            Ropp_lt_cancel.
    rewrite !Ropp_mult_distr_l.
    apply Rmult_lt_compat_l; first lra.
    apply ln_increasing; lra.
  Qed.
  
  Lemma Coeff_upper_bound :
    ∀ (α : R) (x : R), 
    (Rabs x < 1)%R →
    ∀ (t : R),
    (Rmin 0 x < t < Rmax 0 x)%R →
    (g α t <= Coeff α x)%R.
  Proof.
    move=>α x x_bounds t t_bounds.
    destruct (Rle_dec 0 x) as [x_ge | x_lt].
    { rewrite Rmin_left in t_bounds; last lra.
      rewrite Rmax_right in t_bounds; last lra.
      unfold Coeff.
      destruct (Rle_dec 0 α).
      - rewrite Rmax_right; last lra.
        unfold g.
        apply f_increasing; lra.
      - rewrite Rmin_left; last lra.
        unfold g.
        apply f_decreasing; lra.
    }
    { rewrite Rmin_right in t_bounds; last lra.
      rewrite Rmax_left in t_bounds; last lra.
      unfold Coeff.
      apply Rabs_def2 in x_bounds as [_ x_gt].
      destruct (Rle_dec 0 α).
      - rewrite Rmax_left; last lra.
        unfold g.
        apply f_increasing; lra.
     - rewrite Rmin_right; last lra.
       unfold g.
       apply f_decreasing; lra.
    } 
  Qed.

  Definition h (x : R) (t : R) := (Rabs (x - t) / (1 + t))%R.

  Lemma h_pos : ∀ (x t : R), (-1 < t)%R → (0 <= h x t)%R.
  Proof.
    move=>x t t_gt.
    unfold h.
    apply Rcomplements.Rdiv_le_0_compat; first apply Rabs_pos.
    lra.
  Qed.
  
  Lemma continuous_h :
    ∀ (x t : R),
    (t ≠ -1)%R →
    @continuous Hierarchy.R_UniformSpace Hierarchy.R_UniformSpace (h x) t.
  Proof.
    move=>x t t_ne_1.
    unfold h.
    apply (@continuous_mult Hierarchy.R_UniformSpace Hierarchy.R_AbsRing).
    { apply continuous_Rabs_comp, (@continuous_minus _ _ Hierarchy.R_NormedModule).
      - apply continuous_const.
      - apply continuous_id.
    }
    { apply continuous_Rinv_comp; last lra.
      { apply (@continuous_plus _ _ Hierarchy.R_NormedModule).
        - apply continuous_const.
        - apply continuous_id.
      }
    }
  Qed.

  Lemma h_max : ∀ (x t : R),
    (Rabs x < 1)%R →
    (Rmin 0 x < t < Rmax 0 x)%R →
    (h x t < Rabs x)%R.
  Proof.
    move=>x t x_bounds t_bounds.
    apply Rabs_def2 in x_bounds as [x_gt x_lt].
    unfold h.
    apply Rcomplements.Rlt_div_l.
    {
      destruct (Rlt_dec 0 x).
      - rewrite Rmin_left in t_bounds; lra.
      - rewrite Rmin_right in t_bounds; lra.
    }
    unfold Rabs at 2.
    destruct (Rcase_abs x).
    { rewrite Rmin_right in t_bounds; last lra.
      rewrite Rmax_left in t_bounds; last lra.
      rewrite Rabs_left; last lra.
      rewrite Ropp_minus_distr Rmult_plus_distr_l Rmult_1_r Rminus_def (Rplus_comm t (-x)).
      apply Rplus_lt_compat_l.
      rewrite -{1}(Rmult_1_l t).
      apply Ropp_lt_cancel.
      rewrite !Ropp_mult_distr_r.
      apply Rmult_lt_compat_r; lra.
    } 
      
    { rewrite Rmin_left in t_bounds; last lra.
      rewrite Rmax_right in t_bounds; last lra.
      rewrite Rabs_right; last lra.
      rewrite Rmult_plus_distr_l Rmult_1_r Rminus_def.
      apply Rplus_lt_compat_l.
      rewrite -{1}(Rmult_1_l t) Ropp_mult_distr_l.
      apply Rmult_lt_compat_r; lra.
    }
  Qed.

  Lemma RInt_pos :
    ∀ (f : R → R) (a b : R),
    (a <= b)%R  →
    (∀ t, (a < t < b)%R → 0 <= f t)%R →
    (@ex_RInt Hierarchy.R_NormedModule f a b) →
    (0 <= @RInt Hierarchy.R_CompleteNormedModule f a b)%R.
  Proof.
    move=>f a b a_le_b f_pos ex_RInt_f.
    replace 0%R with (@RInt Hierarchy.R_CompleteNormedModule (const 0%R) a b); last first.
    { rewrite (@RInt_ext Hierarchy.R_CompleteNormedModule _ (Derive.Derive (const 0%R))); last first.
      { move=>x _.
        rewrite Derive.Derive_const //.
      }
      rewrite RInt_Derive /=; first lra.
      {
        move=>x _.
        apply Derive.ex_derive_const.
      }
      {
        move=>x _.
        apply continuous_const.
      }
    }
    apply RInt_le; try assumption.
    apply ex_RInt_const.
  Qed.
  
  Definition Int (x : R) (n : nat) :=
    (@RInt Hierarchy.R_CompleteNormedModule
           (λ t : R,
                  ((h x t) ^ n)) (Rmin 0 x) (Rmax 0 x))%R.

  Lemma ex_RInt_Int : ∀ (n : nat) (x : R), (-1 < x)%R → @ex_RInt Hierarchy.R_NormedModule (λ t, (h x t) ^ n)%R (Rmin 0 x) (Rmax 0 x).
  Proof.
    move=>n x x_bounds.
    apply (@ex_RInt_continuous Hierarchy.R_CompleteNormedModule).
    move=>t t_bounds.
    unshelve eapply (continuous_comp _ _ _ _ (continuous_pow n _)).
    apply continuous_h.
    rewrite Rmin_left in t_bounds; last apply Rcomplements.Rmin_Rmax.
    rewrite Rmax_right in t_bounds; last apply Rcomplements.Rmin_Rmax.
    destruct (Rlt_dec 0 x).
    { rewrite Rmin_left in t_bounds; lra. }
    { rewrite Rmin_right in t_bounds; lra. }
  Qed.
 
  Lemma Int_pos : ∀ (x : R) (n : nat), (-1 < x)%R → (0 <= Int x n)%R.
  Proof.
    move=>x n x_gt.
    apply RInt_pos; first apply Rcomplements.Rmin_Rmax.
    { move=>t t_bounds.
      apply pow_le, h_pos.
      destruct (Rlt_dec 0 x).
      { rewrite Rmin_left in t_bounds; lra. }
      { rewrite Rmin_right in t_bounds; lra. }
    }
    by apply ex_RInt_Int.
  Qed.
 
  Lemma Int_ratio :
    ∀ (x : R) (n : nat),
    (Rabs x < 1)%R →
    (Int x (S n) <= Rabs x * Int x n)%R.
  Proof.
    move=> x n x_bounds.
    pose proof (Rabs_def2 _ _ x_bounds) as [x_lt x_gt].
    unfold Int.
    pose proof (@RInt_scal Hierarchy.R_CompleteNormedModule (λ t, (h x t)^n)%R (Rmin 0 x) (Rmax 0 x) (Rabs x)) as H.
    unfold Hierarchy.scal in H.
    simpl in H.
    unfold Hierarchy.mult in H.
    simpl in H.
    rewrite -H; last by apply ex_RInt_Int.
    apply RInt_le; first apply Rcomplements.Rmin_Rmax.
    { by apply ex_RInt_Int. }
    { by apply (@ex_RInt_scal Hierarchy.R_NormedModule), ex_RInt_Int. }
    move=>t t_bounds /=.
    apply Rmult_le_compat_r.
    { apply pow_le, h_pos.
      destruct (Rlt_dec 0 x).
      { rewrite Rmin_left in t_bounds; lra. }
      { rewrite Rmin_right in t_bounds; lra. }
    }
    left.
    by apply h_max.
  Qed.

  Lemma Int_0 : ∀ (x : R), Int x 0 = Rabs x.
  Proof.
    move=>x.
    unfold Int.
    simpl.
    rewrite RInt_const.
    unfold Hierarchy.scal.
    simpl.
    unfold Hierarchy.mult.
    simpl.
    rewrite Rmult_1_r.
    unfold Rabs.
    destruct (Rcase_abs x).
    - rewrite Rmax_left; last lra.
      rewrite Rmin_right; lra.
    - rewrite Rmax_right; last lra.
      rewrite Rmin_left; lra.
  Qed.
      
  Lemma Int_upper :
    ∀ (x : R) (n : nat),
    (Rabs x < 1)%R →
    (Int x n <= Rabs x ^ (n + 1))%R.
  Proof.
    move=>x + x_bounds.
    elim=>[|n IH] /=.
    - rewrite Int_0. lra.
    - etrans; first apply Int_ratio; first assumption.
      by apply Rmult_le_compat_l; first apply Rabs_pos.
  Qed.

  Lemma Rabs_RInt_bounds :
    ∀ (f : R → R) (a b : R),
    @ex_RInt Hierarchy.R_NormedModule f a b →
    Rabs (@RInt Hierarchy.R_CompleteNormedModule f a b) = Rabs (@RInt Hierarchy.R_CompleteNormedModule f (Rmin a b) (Rmax a b)).
  Proof.
    move=>f a b ex_RInt_f.
    destruct (Rle_dec a b).
    { rewrite Rmin_left // Rmax_right //. }
    { rewrite Rmin_right; last lra.
      rewrite Rmax_left; last lra.
      rewrite -opp_RInt_swap; first apply Rabs_Ropp.
      by apply ex_RInt_swap.
    }
  Qed.

  Lemma Rabs_div : ∀ (x y : R), (Rabs (x / y) = Rabs x / Rabs y)%R.
  Proof.
    move=>x y.
    rewrite Rabs_mult Rabs_inv //.
  Qed.
  
  Lemma Rem_abs_upper_bound :
    ∀ (α : R) (n : nat) (x : R),
    (Rabs x < 1)%R →
    (Rabs (Rem α n x) <= Coeff (α - 1) x * (Rabs (prod_sub_n (S n) α) / fact n) *
                           (Rabs x)^(n + 1))%R.
  Proof.
    move=>α n x x_bounds.
    pose proof (Rabs_def2 _ _ x_bounds) as [x_gt x_lt].
    move=>[:ex_RInt_g].
    unfold Rem.
    rewrite Rabs_mult Rabs_div (Rabs_right (fact n));
      last apply Rle_ge, pos_INR.
    rewrite (Rmult_comm (Coeff _ _)) (Rmult_assoc _ (Coeff _ _)).
    apply Rmult_le_compat_l.
    { apply Rcomplements.Rdiv_le_0_compat; first apply Rabs_pos.
      apply INR_fact_lt_0.
    }
    rewrite Rabs_RInt_bounds; last first.
    { abstract: ex_RInt_g.
      apply (@ex_RInt_continuous Hierarchy.R_CompleteNormedModule).
      move=>t t_bounds /=.
      unfold g.
      apply (@continuous_mult Hierarchy.R_UniformSpace Hierarchy.R_AbsRing).
      { apply continuous_g.
       destruct (Rlt_dec 0 x).
        { rewrite Rmin_left in t_bounds; lra. }
        { rewrite Rmin_right in t_bounds; lra. }
      }
      unshelve eapply (continuous_comp _ _ _ _ (continuous_pow n _)).
      apply (@continuous_mult Hierarchy.R_UniformSpace Hierarchy.R_AbsRing).
      { apply (@continuous_minus _ _ Hierarchy.R_NormedModule).
      - apply continuous_const.
      - apply continuous_id.
      }
      { apply continuous_Rinv_comp; last first.
        { destruct (Rlt_dec 0 x).
          { rewrite Rmin_left in t_bounds; lra. }
          { rewrite Rmin_right in t_bounds; lra. }
        }
        { apply (@continuous_plus _ _ Hierarchy.R_NormedModule).
          - apply continuous_const.
          - apply continuous_id.
        }
      }
    }
    etrans.
    { apply abs_RInt_le; first apply Rcomplements.Rmin_Rmax.
      destruct (Rlt_dec 0 x).
      {
        rewrite Rmin_left; last lra.
        rewrite Rmax_right //; last lra.
      }
      {
        rewrite Rmin_right; last lra.
        rewrite Rmax_left //; last lra.
        by apply ex_RInt_swap.
      }
      
    }
    erewrite RInt_ext; last first.
    { move=>t t_bounds.
      rewrite Rmin_left in t_bounds; last apply Rcomplements.Rmin_Rmax.
      rewrite Rmax_right in t_bounds; last apply Rcomplements.Rmin_Rmax.
      rewrite Rabs_mult (Rabs_right (g (α - 1) t)); last (apply Rle_ge; left; apply g_pos).
      rewrite -RPow_abs Rabs_div (Rabs_right (1 + t)); last first.
      { destruct (Rlt_dec 0 x).
        { rewrite Rmin_left in t_bounds; lra. }
        { rewrite Rmin_right in t_bounds; lra. }
      }
      by fold (h x t).
    }
    transitivity (Coeff (α - 1) x * Int x n)%R; last first.
    { apply Rmult_le_compat_l; first (left; apply Coeff_pos).
      apply Int_upper, x_bounds.
    }
    pose proof (@RInt_scal Hierarchy.R_CompleteNormedModule) as H.
    unfold Hierarchy.scal in H.
    simpl in H.
    unfold Hierarchy.mult in H.
    simpl in H.
    rewrite -H; last by apply ex_RInt_Int.
    apply RInt_le; first apply Rcomplements.Rmin_Rmax.
    {
      apply (@ex_RInt_continuous Hierarchy.R_CompleteNormedModule).
      rewrite Rmin_left; last apply Rcomplements.Rmin_Rmax.
      rewrite Rmax_right; last apply Rcomplements.Rmin_Rmax.
      move=>t t_bounds.
      apply (@continuous_mult Hierarchy.R_UniformSpace Hierarchy.R_AbsRing).
      { apply continuous_g.
        destruct (Rlt_dec 0 x).
        { rewrite Rmin_left in t_bounds; lra. }
        { rewrite Rmin_right in t_bounds; lra. }
      }
      unshelve eapply (continuous_comp _ _ _ _ (continuous_pow n (h x t))).
      apply continuous_h.
      destruct (Rlt_dec 0 x).
      { rewrite Rmin_left in t_bounds; lra. }
      { rewrite Rmin_right in t_bounds; lra. }
    }
    { by apply (@ex_RInt_scal Hierarchy.R_NormedModule), ex_RInt_Int. }
    move=>t t_bounds.
    apply Rmult_le_compat_r.
    { apply pow_le, h_pos.
      destruct (Rlt_dec 0 x).
      { rewrite Rmin_left in t_bounds; lra. }
      { rewrite Rmin_right in t_bounds; lra. }
    }
    by apply Coeff_upper_bound.
  Qed.

  Lemma lim_seq_dist_0 : 
    ∀ (u : nat → R) (l : R),
    Lim_seq.is_lim_seq (λ n, Rabs (u n - l))%R (Rbar.Finite 0%R) →
    Lim_seq.is_lim_seq u (Rbar.Finite l%R).
  Proof.
    unfold Lim_seq.is_lim_seq,
             Hierarchy.filterlim,
               Hierarchy.filter_le,
                 Hierarchy.Rbar_locally,
                   Hierarchy.locally,
                     Hierarchy.filtermap,
                       Hierarchy.eventually,
                         Hierarchy.ball.
    simpl.
    unfold Hierarchy.AbsRing_ball,
             Hierarchy.abs,
               Hierarchy.minus,
                 Hierarchy.plus,
                   Hierarchy.opp.
    simpl.
    move=>u l lim_dist.
    move=>P [ε P_ε].
    unshelve epose proof (lim_dist (λ x, x < ε)%R _) as [N HN].
    { exists ε.
      move=>x x_bounds.
      rewrite Ropp_0 Rplus_0_r in x_bounds.
      by destruct (Rabs_def2 _ _ x_bounds).
    }
    exists N.
    move=>n N_le_n.
    apply P_ε, HN, N_le_n.
  Qed.
  
  Lemma lim_seq_ratio :
    ∀ (u : nat → R) (l : R),
    Lim_seq.is_lim_seq (λ n, Rabs (u (S n) / u n))%R (Rbar.Finite l) →
    (Rabs l < 1)%R →
    ∀ (N_pos : nat), (∀ n, N_pos ≤ n → u n ≠ 0) →
    Lim_seq.is_lim_seq u (Rbar.Finite 0%R).
  Proof.
    unfold Lim_seq.is_lim_seq,
             Hierarchy.filterlim,
               Hierarchy.filter_le,
                 Hierarchy.Rbar_locally,
                   Hierarchy.locally,
                     Hierarchy.filtermap,
                       Hierarchy.eventually,
                         Hierarchy.ball.
    simpl.
    unfold Hierarchy.AbsRing_ball,
             Hierarchy.abs,
               Hierarchy.minus,
                 Hierarchy.plus,
                   Hierarchy.opp.
    simpl.
    
    move=>u l is_lim_l l_bounds N_pos not_0.
    set (ε := ((1 - Rabs l) / 2)%R).
    unshelve epose proof (is_lim_l (λ (x : R), Rabs (x - l) < ε)%R _) as [N small].
    { unshelve eexists (mkposreal ε _).
      { unfold ε.
        apply Rcomplements.Rdiv_lt_0_compat; lra.
      }
      simpl.
      done.
    }
    assert (-1 < (ε + l) < 1)%R.
    {
      unfold ε, Rabs.
      apply Rabs_def2 in l_bounds as [l_lt l_gt].
      destruct (Rcase_abs l); lra.
    }

    assert (-1 < (l - ε) < 1)%R.
    {
      unfold ε, Rabs.
      apply Rabs_def2 in l_bounds as [l_lt l_gt].
      destruct (Rcase_abs l); lra.
    }

    set (r := (Rmax (ε + l) (ε - l))%R).
    assert ((ε + l) <= r)%R.
    {
      unfold r.
      apply Rmax_l.
    }

    assert (-r <= (l - ε))%R.
    {
      unfold r.
      apply Ropp_le_cancel.
      rewrite Ropp_minus_distr Ropp_involutive.
      apply Rmax_r.
    }
    
    assert (∀ n, N ≤ n → - r < Rabs (u (S n) / u n) < r)%R as eventually_small.
    {
      move=>n N_le_n.
      specialize (small n N_le_n).
      apply Rabs_def2 in small as [small1 small2].
      rewrite Rcomplements.Rlt_minus_l in small1.
      rewrite Rcomplements.Rlt_minus_r in small2.
      split.
      { eapply Rle_lt_trans; first done.
        lra.
      }
      { eapply Rlt_le_trans; first done.
        lra.
      }
    }

    set (N_max := max N N_pos).
    
    assert (∀ n, N_max ≤ n → Rabs (u (S n)) < r * Rabs (u n))%R as eventually_abs.
    {
      move=>n N_le_n.
      pose proof (eventually_small n ltac:(lia)) as [esmall1 esmall2].
      pose proof (not_0 n ltac:(lia)).
      rewrite -Rcomplements.Rlt_div_l; last by apply Rgt_lt, Rabs_pos_lt.
      rewrite -Rabs_div //.
    }

    assert (0 < r < 1)%R.
    {
      split.
      {
        specialize (eventually_small N ltac:(reflexivity)).
        lra.
      }
      apply Rmax_lub_lt;
        lra.
    }
    
    assert (∀ n, N_max < n → (Rabs (u n) < Rabs (u N_max) * r ^ (n - N_max))%R) as lim_u_0.
    {
      elim=>[|n IH] N_max_lt_Sn; first lia.
      assert (N_max ≤ n) as N_max_le_n by lia.
      apply Nat.lt_eq_cases in N_max_le_n.
      destruct N_max_le_n as [N_max_lt_n | <-].
      - specialize (IH N_max_lt_n).
        pose proof (eventually_abs n ltac:(lia)) as u_Sn_lt_r_un.
        etrans; first done.
        simpl.
        replace (S n - N_max) with (S (n - N_max)) by lia.
        rewrite -Rmult_assoc (Rmult_comm _ r) Rmult_assoc.
        apply Rmult_lt_compat_l; first lra.
        exact IH.
      - replace (S N_max - N_max) with 1%nat by lia.
        rewrite pow_1.
        rewrite Rmult_comm.
        by apply eventually_abs.
    }

    move=>P [eps P_eps].
    (* Rabs (u N_max) * r ^ (n - N_max) ≤ eps
     r ^ (n - N_max) ≤ eps / Rabs (u N_max)
     exp(ln r * (n - N_max)) ≤ eps / Rabs (u N_max)
     ln r * (n - N_max) ≤ ln (eps / Rabs (u N_max))
     (n - N_max) ≥ ln (eps / Rabs (u N_max)) / ln r (ln r is ≤ 0)
     n ≥ ln (eps / Rabs (u N_max)) / ln r + N_max
   *)
   set (v := (ln (eps / Rabs (u N_max)) / ln r + N_max)%R).
   pose proof (INR_unbounded v) as [n_tl n_tl_gt].
   exists (n_tl `max` (S N_max)).
   move=>n k_le_n.
   apply P_eps.
   rewrite Ropp_0 Rplus_0_r.
   etrans; first apply lim_u_0; try lia.
   rewrite Rmult_comm Rcomplements.Rlt_div_r; last (apply Rgt_lt, Rabs_pos_lt, not_0; lia).
   rewrite -f_pow /f; last lra.
   rewrite -(exp_ln (eps / _)%R); last first.
   {
     apply Rcomplements.Rdiv_lt_0_compat; first apply cond_pos.
     apply Rabs_pos_lt, not_0.
     lia.
   }
   apply exp_increasing, Ropp_lt_cancel.
   rewrite Ropp_mult_distr_r -Rcomplements.Rlt_div_l; last first.
   {
     apply Ropp_neg.
     rewrite -ln_1.
     apply ln_increasing; lra.
   }
   rewrite -Ropp_div_distr_l Ropp_div_distr_r Ropp_involutive minus_INR; last lia.
   rewrite Rcomplements.Rlt_minus_r.
   fold v.
   assert (n_tl <= n_tl `max` S N_max)%R.
   {
     apply le_INR.
     lia.
   }
   apply le_INR in k_le_n.
   lra.
  Qed.

  Lemma is_INR_dec : ∀ (x : R), {n | x = INR n} + {∀ n, x ≠ INR n}.
  Proof.
    move=>x.
    unshelve epose proof (ClassicalDedekindReals.sig_forall_dec (λ n, x ≠ INR n) _) as H.
    {
      move=>n /=.
      destruct (Req_dec_T x n) as [-> | x_ne_n].
      { right.
        move=>contra.
        apply contra.
        reflexivity.
      }
      by left.
    }
    destruct H as [[n n_eq_x] | not_nat].
    { left.
      exists n.
      lra.
    }
    by right.
  Qed.

  Lemma prod_sub_n_eventually_0 :
    ∀ (k n : nat), k ≤ n → prod_sub_n (S n) k = 0%R.
    move=>k.
    elim=>[|n IH] k_le_n.
    { assert (k = 0) as -> by lia.
      simpl.
      lra.
    } 
    rewrite prod_sub_n_last.
    rewrite Nat.lt_eq_cases in k_le_n.
    destruct k_le_n as [k_lt_Sn | ->].
    { rewrite IH; last lia.
      lra.
    }
    rewrite Rminus_diag.
    lra.
  Qed.

  Lemma prod_sub_n_never_0 :
    ∀ (α : R), (∀ k, α ≠ INR k) → ∀ (n : nat), prod_sub_n n α ≠ 0%R.
  Proof.
    move=>α α_not_nat.
    elim=>[/=|n IH]; first lra.
    rewrite (prod_sub_n_last n α).
    pose proof (α_not_nat n).
    move=>contra.
    apply Rmult_integral in contra.
    lra.
  Qed. 
  
  Lemma upper_bound_eventually_always_or_never_0 :
    ∀ (x : R) (α : R),
    let up := λ n, 
       (Coeff (α - 1) x *
         (Rabs (prod_sub_n (S n) α) / fact n) *
         (Rabs x)^(n + 1))%R in
  (∃ N, ∀ n, N ≤ n → up n = 0%R) ∨ (∀ n, up n ≠ 0%R).
  Proof.
    move=>x α up.
    destruct (Req_dec x 0) as [-> | x_not_0].
    { left.
      exists 0.
      move=>n _.
      unfold up.
      rewrite Rabs_R0 pow_i; last lia.
      rewrite !Rmult_0_r //.
    }
    destruct (is_INR_dec α) as [[n n_eq_α] | α_not_nat].
    { left.
      exists n.
      move=>k n_le_k.
      unfold up.
      rewrite n_eq_α prod_sub_n_eventually_0; last assumption.
      rewrite Rabs_R0.
      lra.
    }
    { right.
      move=>n contra.
      unfold up in contra.
      apply Rmult_integral in contra.
      destruct contra as [contra | contra]; last first.
      { unshelve epose proof (pow_nonzero (Rabs x) (n + 1) _ ).
        { move=>abs_0.
          apply x_not_0,
                  Rcomplements.Rabs_eq_0,
                    abs_0.
        }
        done.
      }
      apply Rmult_integral in contra.
      destruct contra as [contra | contra].
      { pose proof (Coeff_pos (α - 1) x).
        lra.
      }
      pose proof (INR_fact_lt_0 n).
      pose proof (prod_sub_n_never_0 _ α_not_nat (S n)).
      assert (Rabs (prod_sub_n (S n) α) ≠ 0)%R.
      {
        move=>abs_0.
        by apply Rcomplements.Rabs_eq_0 in abs_0.
      }
      assert (0 < Rabs (prod_sub_n (S n) α) / fact n)%R.
      {
        apply Rcomplements.Rdiv_lt_0_compat; last done.
        by apply Rabs_pos_lt.
      }
      lra.
    }
  Qed.
  
  Lemma limit_upper_bound : 
    ∀ (α x : R),
    (Rabs x < 1)%R →
    Lim_seq.is_lim_seq
      (λ (n : nat), Coeff (α - 1) x * (Rabs (prod_sub_n (S n) α) / fact n) * (Rabs x)^(n + 1))%R (Rbar.Finite 0%R).
  Proof.
    move=>α x w_bounds.
    destruct (upper_bound_eventually_always_or_never_0 x α)
      as [[N always_0] | never_0].
    { eapply Lim_seq.is_lim_seq_ext_loc; last apply Lim_seq.is_lim_seq_const.
      simpl.
      exists N.
      move=>n N_le_n.
      symmetry.
      by apply always_0.
    }
    unshelve eapply (lim_seq_ratio _ (Rabs x) _ _ 0 _);
      try rewrite Rabs_Rabsolu //; last first.
    {
      move=>n _.
      apply never_0.
    }
    apply (Lim_seq.is_lim_seq_ext_loc (λ n, Rabs (α - (n + 1)) / (n + 1) * Rabs x)%R).
    { exists 0.
      move=>n _.
      rewrite !(Rmult_assoc (Coeff _ _)) Rdiv_mult_l_l; last first.
      { pose proof (Coeff_pos (α - 1) x). lra. } 
      rewrite prod_sub_n_last fact_R S_INR.
      remember (prod_sub_n (S n) α) as A.
      remember (α - (n + 1))%R as B.
      rewrite pow_add pow_1 -Nat.add_1_r.
      repeat (rewrite Rabs_div || rewrite -RPow_abs || rewrite Rabs_mult).
      fold prod_sub_n.
      rewrite !Rabs_Rabsolu.
      rewrite !(Rabs_right (n + 1)%R); last real_solver.
      rewrite !(Rabs_right (fact n)%R); last real_solver.
      replace (Rabs A * Rabs B / ((n + 1) * fact n))%R with ((Rabs B / (n + 1)) * (Rabs A / fact n))%R; last first.
      { rewrite !Rdiv_def Rinv_mult. lra. }
      rewrite Rmult_assoc -Rmult_div_assoc.
      f_equal.
      rewrite (Rmult_comm _ (Rabs x)) -Rmult_assoc
              (Rmult_comm _ (Rabs x)) Rmult_assoc
              -Rmult_div_assoc -{1}(Rmult_1_r (Rabs x)).
      f_equal.
      rewrite Rdiv_diag //.
      move=>contra.
      specialize (never_0 n).
      apply Rmult_integral in contra as [contra | contra].
      {
        subst A.
        apply Rmult_integral in contra as [contra | contra].
        { rewrite contra in never_0.
          rewrite Rdiv_0_l Rmult_0_r Rmult_0_l // in never_0.
        }
        pose proof (INR_fact_lt_0 n).
        rewrite -Rinv_0 in contra.
        apply Rinv_eq_reg in contra.
        lra.
      }
      { rewrite contra Rmult_0_r // in never_0. }
    }
    rewrite -{2}(Rmult_1_l (Rabs x)).
    apply (Lim_seq.is_lim_seq_scal_r _ (Rabs x) (Rbar.Finite 1%R)).
    apply (Lim_seq.is_lim_seq_ext (λ n, Rabs (1 - α / (n + 1)))%R).
    { move=>n.
      replace (n + 1)%R with (Rabs (n + 1)%R) at 3; last first.
      { rewrite Rabs_right //. real_solver. }
      rewrite -Rabs_div Rdiv_minus_distr -Rabs_Ropp Ropp_minus_distr.
      do 2 f_equal.
      rewrite Rdiv_diag //.
      real_solver.
    }
    rewrite -{3}(Rabs_right 1); last lra.
    apply (Lim_seq.is_lim_seq_abs _ (Rbar.Finite 1%R)).
    apply (Lim_seq.is_lim_seq_minus _ _ (Rbar.Finite 1%R) (Rbar.Finite 0%R)); last first.
    { unfold Rbar.is_Rbar_minus.
      simpl.
      rewrite Ropp_0 -{2}(Rplus_0_r 1).
      by apply Rbar.Rbar_plus_correct.
    } 
    {
      eapply Lim_seq.is_lim_seq_div.
      { apply Lim_seq.is_lim_seq_const. }
      { apply (Lim_seq.is_lim_seq_plus _ _ Rbar.p_infty (Rbar.Finite 1%R)).
        - apply Lim_seq.is_lim_seq_INR.
        - apply Lim_seq.is_lim_seq_const.
        - by apply Rbar.Rbar_plus_correct.
      }
      { done. }
      { simpl.
        apply Rbar.is_Rbar_div_p_infty.
      } 
    }
    { apply Lim_seq.is_lim_seq_const. }
  Qed.
    
  Lemma g_maclaurin : ∀ (α x : R) (n : nat),
    (Rabs x < 1)%R →
    g α x =
    (sum_f_R0
       (λ k : nat,
          x ^ k / fact k *
                (prod_sub_n k α * g (α - k) 0)) n + Rem α n x
       )%R
 .
  Proof.
    move=>α x n x_bounds.
    unfold Rem.
    apply Rabs_def2 in x_bounds as [x_lt x_gt].
    assert (-1 < x < 1)%R as x_bounds by lra.
    rewrite (integral_maclaurin (g α) n x); last first.
    { move=>t t_bounds.
      apply (@Derive.ex_derive_continuous _ Hierarchy.R_NormedModule),
              (ex_derive_n_g (S (S n))).
      destruct (Rlt_ge_dec 0 x);
      [ rewrite Rmin_left in t_bounds | rewrite Rmin_right in t_bounds];
        lra.
    }
    { move=>t t_bounds k _.
      apply ex_derive_n_g.
      destruct (Rlt_ge_dec 0 x);
      [ rewrite Rmin_left in t_bounds | rewrite Rmin_right in t_bounds];
        lra.
    }
    erewrite sum_eq; last first.
    { move=>k _.
      rewrite (Derive.is_derive_n_unique _ _ _ _ (is_derive_n_g k α 0 _)) //.
      lra.
    }
    erewrite RInt_ext; last first.
    { move=>t t_bounds.
      rewrite (Derive.is_derive_n_unique _ _ _ _ (is_derive_n_g (S n) α t _)); last first.
      { destruct (Rlt_ge_dec 0 x);
          [ rewrite Rmin_left in t_bounds | rewrite Rmin_right in t_bounds];
          lra.
      }
      rewrite S_INR Rmult_assoc //.
    }
    f_equal.
    rewrite Rdiv_def (Rmult_comm _ (/ fact n)) Rmult_assoc.
    f_equal.
    rewrite RInt_scal; last first.
    {
      apply ex_RInt_continuous.
      move=>t t_bounds.
      apply (@continuous_mult Hierarchy.R_UniformSpace Hierarchy.R_AbsRing).
      { apply (@Derive.ex_derive_continuous _ Hierarchy.R_NormedModule).
        eexists.
        apply is_derive_g.
        destruct (Rlt_ge_dec 0 x);
          [ rewrite Rmin_left in t_bounds | rewrite Rmin_right in t_bounds];
          lra.
      }
      { apply continuous_pow_minus. }
    }
    f_equal.
    apply RInt_ext.
    move=>t t_bounds.
    rewrite (Rplus_comm n 1) Rminus_plus_distr.
    rewrite g_plus g_opp !Rmult_assoc.
    f_equal.
    unfold g.
    rewrite f_pow /=; last first.
    { destruct (Rlt_ge_dec 0 x);
        [ rewrite Rmin_left in t_bounds | rewrite Rmin_right in t_bounds];
        lra.
    }
    rewrite Rpow_mult_distr pow_inv (Rplus_comm 1 t).
    lra.
  Qed.

 Lemma is_seriesC_g :
   ∀ (α x : R),
    (Rabs x < 1)%R →
    is_seriesC (λ k : nat,
                  x ^ k / fact k *
                        prod_sub_n k α)%R (g α x).
  Proof.
    move=>α x x_bounds.
    apply is_seriesC_is_series_nat.
    apply Series_Ext.is_lim_seq_is_series.
    eapply Lim_seq.is_lim_seq_ext.
    { move=>n.
      rewrite Hierarchy.sum_n_Reals //.
    }
    apply lim_seq_dist_0.
    apply (Lim_seq.is_lim_seq_ext (λ n, Rabs (Rem α n x))).
    { move=>n.
      rewrite -(Rabs_Ropp (_ - g α x)%R) Ropp_minus_distr (g_maclaurin _ _ n); last done.
      erewrite sum_eq; last first.
      {
        move=>k _.
        unfold g, f.
        rewrite Rplus_0_l ln_1 Rmult_0_r exp_0 Rmult_1_r //.
      }
      rewrite Rplus_minus_swap Rminus_diag Rplus_0_l //.
    }
    eapply (Lim_seq.is_lim_seq_le_le (const 0%R) _); last first.
    { by apply (limit_upper_bound α x). }
    { apply Lim_seq.is_lim_seq_const. }
    move=>n.
    split; first apply Rabs_pos.
    by apply Rem_abs_upper_bound.
  Qed.

  Lemma prod_sub_n_opp_nat :
    ∀ (k n : nat), (0 < n) → prod_sub_n k (-n) = (fact (n + k - 1) / fact (n - 1) * (-1)^k)%R.
  Proof.
    elim=>[|k IH] n sum_lt.
    { simpl.
      rewrite Nat.add_0_r Rmult_1_r.
      pose proof (INR_fact_lt_0 (n - 1)).
      rewrite Rdiv_diag; lra.
    }
    rewrite prod_sub_n_last IH //=
            Rminus_def -Ropp_plus_distr
            -(Nat.add_sub_assoc n (S k) 1) /=; last lia.
    rewrite Nat.sub_0_r.
    replace (fact (n + k) : R) with (fact (n + k - 1) * (n + k))%R; last first.
    { destruct n; first lia.
      rewrite S_INR fact_R plus_INR.
      fold Nat.add.
      rewrite /= Nat.sub_0_r.
      lra.
    }
    lra.
  Qed.
    
  Lemma prod_sub_n_choose : ∀ (k n : nat), (0 < n)%nat → (prod_sub_n k (-n) / fact k = interface.choose (k + n - 1) k * (-1)^k)%R.
  Proof.
    move=>k n n_pos.
    rewrite prod_sub_n_opp_nat //.
    unfold interface.choose.
    case_bool_decide; last lia.
    unfold C.
    replace (k + n - 1 - k) with (n - 1) by lia.
    rewrite (Nat.add_comm n k) -Rmult_div_assoc !Rmult_assoc.
    f_equal.
    rewrite Rinv_mult.
    lra.
  Qed.

  Lemma is_seriesC_negative_choose_0 :
    ∀ (q : R),
    is_seriesC (λ k, interface.choose (k - 1) k * q ^ k)%R 1%R.
  Proof.
    move=> q.
    eapply is_seriesC_ext.
    { instantiate (1 := (λ (k : nat), if bool_decide (k = 0) then 1%R else 0%R)).
      move=>i /=.
      case_bool_decide as is_i_0.
      { rewrite is_i_0 interface.choose_n_0 Rmult_1_r //. }
      { unfold interface.choose.
        case_bool_decide; first lia.
        rewrite Rmult_0_l //.
      }
    }
    apply is_seriesC_singleton.
  Qed.

  Lemma is_seriesC_negative_choose_pos :
    ∀ (r : nat) (q : R),
    (0 < r)%nat →
    (Rabs q < 1)%R →
    is_seriesC (λ k, interface.choose (k + r - 1) k * q ^ k)%R (/ ((1 - q)^r))%R.
  Proof.
    move=>r q r_pos q_bounds.
    unfold negative_binom_prob.
    
    assert (0 < (1 - q))%R.
    {
      apply Rabs_def2 in q_bounds.
      lra.
    }
    rewrite -f_pow; last lra.
    rewrite -f_opp.
    rewrite Rminus_def (Rplus_comm 1 (-q)).
    fold (g (-r) (- q)).
    eapply is_seriesC_ext; last apply is_seriesC_g; last rewrite Rabs_Ropp //.
    move=>k /=.
    rewrite Rmult_assoc (Rmult_comm (/ fact k)) -Rdiv_def prod_sub_n_choose //
            -{2}(Rmult_1_l q) Ropp_mult_distr_l Rpow_mult_distr.
    repeat rewrite (Rmult_comm ((-1)^k)) Rmult_assoc.
    rewrite -Rpow_mult_distr -Ropp_mult_distr_l -Ropp_mult_distr_r
            Ropp_involutive Rmult_1_l pow1 Rmult_1_r Rmult_comm //.
  Qed.
 
 Lemma is_seriesC_negative_choose :
    ∀ (r : nat) (q : R),
    (Rabs q < 1)%R →
    is_seriesC (λ k, interface.choose (k + r - 1) k * q ^ k)%R (/ ((1 - q)^r))%R.
  Proof.
    move=>r q q_bounds.
    destruct (Nat.lt_dec 0 r); first by apply is_seriesC_negative_choose_pos.
    replace r with 0 by lia.
    rewrite Rinv_1.
    eapply is_seriesC_ext; last apply is_seriesC_negative_choose_0.
    move=>i /=.
    rewrite Nat.add_0_r //.
  Qed.
 
  Lemma is_seriesC_negative_binomial :
    ∀ (p q r : nat),
    (0 < p ≤ q + 1)%nat →
    is_seriesC (negative_binom_prob p q r) 1%R.
  Proof.
    move=>p q r r_pos p_bounds.
    unfold negative_binom_prob.
    set (s := (p / (q + 1))%R).
    set (t := (1 - s)%R).
    eapply is_seriesC_ext.
    { move=>k.
      rewrite Rmult_assoc (Rmult_comm (s ^ r)%R) -Rmult_assoc //.
    }

    assert (0 < s <= 1)%R.
    {
      assert (0 < q + 1)%R as q1_pos.
      {
        rewrite -INR_1 -plus_INR.
        apply lt_0_INR.
        lia.
      }
      assert (0 < p)%R.
      {
        apply lt_0_INR.
        lia.
      }
      unfold s.
      split.
      - apply Rcomplements.Rdiv_lt_0_compat;
          lra.
      - rewrite -Rcomplements.Rdiv_le_1 // -INR_1 -plus_INR.
        apply le_INR.
        lia.
    }
    
    replace 1%R with (s ^ r * / s ^ r)%R; last first.
    {
      apply Rdiv_diag, pow_nonzero.
      lra.
    }
    rewrite Rmult_comm.
    apply is_seriesC_scal_r.
    replace s with (1 - t)%R by (unfold t; lra).
    apply is_seriesC_negative_choose.
    unfold t;
    apply Rabs_def1; lra.
  Qed.
  
End math.

Section GeometricToNegative.
  Context `{!erisGS Σ}.
  Context `{!geometric_spec geometric}.
  
  Definition negative_of_geometric : val :=
    λ: "α" "p" "q" "r",
      (rec: "loop" "r" :=
          if: ("r" ≤ #0)
          then #0
          else "loop" ("r" - #1) + geometric "α" "p" "q") "r".

  Lemma choose_sum_split_fin : ∀ (r j : nat), interface.choose (j + r) j = SeriesC (λ (i : fin (S j)), interface.choose (i + r - 1) i).
  Proof.
    move=>r j.
    elim: j =>/=[|j IH].
    - rewrite SeriesC_finite_foldr /= !interface.choose_n_0.
      lra.
    - rewrite -interface.pascal' IH (Series_fin_last (S j)).
      f_equal.
      { apply SeriesC_ext.
        move=>n.
        rewrite -fin_S_inj_to_nat //.
      }
      rewrite fin_to_nat_to_fin.
      f_equal; lia.
  Qed.

  Lemma choose_sum_split : ∀ (r j : nat), interface.choose (j + r) j = SeriesC (λ (i : nat), if bool_decide (i ≤ j) then interface.choose (i + r - 1) i else 0%R).
  Proof.
    move=>r j.
    rewrite SeriesC_nat_bounded_fin choose_sum_split_fin //.
  Qed.

  Lemma ex_seriesC_subsingleton_nat :
    ∀ (a : nat) (f : nat → nat) (g : R → R),
    (∀ i j, f i = a → f j = a → i = j) →
    Decision (∃ i, a = f i) →
    ex_seriesC (λ n, if bool_decide (a = f n) then g n else 0%R).
  Proof.
    move=>a f g f_inj_a [[i fi_a] | no_fi_a].
    - apply (ex_seriesC_ext (λ n, if bool_decide (n = i) then g n else 0%R)).
      + move=>n.
        destruct (Nat.eq_dec a (f n)) as [fi_n | fi_not_n].
        { rewrite (f_inj_a i n); try done.
          by do 2 case_bool_decide.
        }
        by do 2 case_bool_decide; subst.
      + apply ex_seriesC_singleton_dependent.
    - apply (ex_seriesC_ext (const 0%R)).
      + move=>i.
        simpl.
        case_bool_decide; last done.
        exfalso.
        apply no_fi_a.
        by eexists.
      + apply ex_seriesC_0.
  Qed.

  Lemma fubini_full:
    ∀ {A : Type} {EqDecision0 : EqDecision A}
      {H : Countable A} {B : Type}
      {EqDecision1 : EqDecision B}
      {H0 : Countable B}
      (h : A → B → R),
    (∀ (a : A) (b : B), (0 <= h a b)%R) →
    ex_seriesC (λ a, SeriesC (λ b, h a b)) →
    (∀ a, ex_seriesC (λ b, h a b)) →
    SeriesC (λ a, SeriesC (λ b, h a b)) = SeriesC (λ b, SeriesC (λ a, h a b)) ∧
    ex_seriesC (λ b, SeriesC (λ a, h a b)) ∧
    (∀ b, ex_seriesC (λ a, h a b)).
  Proof.
    move=> A ? ? B ? ? h h_pos ex_h ex_forall.
    set (h' := λ '(a,b), h a b).
    pose proof (fubini_pos_seriesC h' h_pos ex_forall ex_h).
    pose proof (fubini_pos_seriesC_ex_double h' h_pos ex_forall ex_h).
    pose proof (fubini_pos_seriesC_ex h' h_pos ex_forall ex_h).
    simpl in *.
    auto.
  Qed.

  Lemma forall_and {A : Type} {P Q : A → Prop} :
    (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x).
  Proof.
    move=>H.
    split; apply H.
  Qed.
  
  Lemma negative_sum_geometric_split :
    ∀ (p q r : nat) (D : nat → R) (L : R),
    (0 < p <= q + 1)%nat →
    (∀ (k : nat), 0 <= D k <= L)%R →
    SeriesC (λ (k : nat), negative_binom_prob p q (r + 1) k * D k)%R
    = SeriesC (λ (k : nat), (p / (q + 1)) * (1 - p / (q + 1))^k * SeriesC (λ (i : nat), negative_binom_prob p q r i * (D (k + i)%nat)))%R.
  Proof.
    move=>p q r D L p_bounds D_bounds.
    unfold negative_binom_prob.
    set (s0 := (p / (q + 1))%R). 
    set (s1 := (1 - s0)%R).
    assert (0 < s0 <= 1)%R.
    {
      unfold s0.
      rewrite -INR_1 -plus_INR .
      split.
      - apply Rcomplements.Rdiv_lt_0_compat;
          rewrite -INR_0;
          apply lt_INR;
          lia.
      - rewrite -Rcomplements.Rdiv_le_1.
        + apply le_INR. lia.
        + rewrite -INR_0. apply lt_INR. lia.
    }
    assert (0 <= s1 < 1)%R.
    {
      unfold s1. lra.
    }
    match goal with
    | |- _ = SeriesC (λ k, ?z * SeriesC ?f)%R =>
        set (h k i j := if bool_decide (j = k + i) then (z * f i)%R else 0%R)
    end.
    simpl in h.

    move=>[:series_eq_singl] [:h_pos].
    unshelve epose proof (λ k, fubini_full (h k) _ _ _) as fubini1.
    {
      move=>i j.
      abstract:h_pos k i j.
      unfold h.
      case_bool_decide; last reflexivity.
      apply Rmult_le_pos; apply Rmult_le_pos.
      - lra.
      - apply pow_le. lra.
      - apply Rmult_le_pos; last (apply pow_le; lra).
        apply Rmult_le_pos; last (apply pow_le; lra).
        apply interface.choose_pos.
      - apply D_bounds.
    }
    {
      eapply ex_seriesC_ext.
      {
        abstract: series_eq_singl k.
        move=>i.
        rewrite SeriesC_singleton (Rmult_comm (interface.choose _ _)) !(Rmult_assoc (s0 ^ r)) -Rmult_assoc //.
      }
      apply ex_seriesC_scal_l.
      eapply ex_seriesC_le.
      { move=>i.
        split.
        - apply Rmult_le_pos; last apply D_bounds.
          apply Rmult_le_pos; first apply interface.choose_pos.
          apply pow_le.
          lra.
        - apply Rmult_le_compat_l; last apply D_bounds.
          apply Rmult_le_pos; first apply interface.choose_pos.
          apply pow_le.
          lra.
      } 
      apply ex_seriesC_scal_r.
      eexists.
      apply is_seriesC_negative_choose, Rabs_def1; lra.
    }
    { move=>i.
      apply ex_seriesC_singleton.
    }
    apply forall_and in fubini1 as [fubini1_eq fubini1].
    apply forall_and in fubini1 as [fubini1_ext fubini1_all_ext].

    etrans; last first.
    { apply SeriesC_ext.
      move=>k.
      etrans; last first.
      {
        rewrite -SeriesC_scal_l.
        eapply (SeriesC_ext (λ i, SeriesC (λ (j : nat), h k i j ))).
        move=>n.
        rewrite SeriesC_singleton //.
      }
      rewrite fubini1_eq //.
    }
    
    unshelve epose proof (fubini_full (λ k j, SeriesC (λ i, h k i j)) _ _ _) as (fubini2_eq & fubini2_ext & fubini2_all_ext).
    { move=>k j /=.
      apply SeriesC_ge_0'.
      move=>i.
      apply h_pos.
    }
    { eapply ex_seriesC_ext.
      { move=>k.
        rewrite -fubini1_eq.
        erewrite SeriesC_ext at 2; last first.
        { move=>i.
          rewrite -series_eq_singl //.
        }
        rewrite SeriesC_scal_l //.
      }
      eapply ex_seriesC_le.
      {
        move=>k.
        rewrite (Rmult_assoc s0) (Rmult_comm (s1 ^ k)) -Rmult_assoc Rmult_assoc(Rmult_comm (s1 ^ k)) -Rmult_assoc.
        move=>[:pos3 pos2 pos1].
        split.
        { apply Rmult_le_pos; last (apply pow_le; lra).
          apply Rmult_le_pos.
          - abstract: pos1.
            apply Rmult_le_pos; first lra.
            apply pow_le.
            lra.
          - apply SeriesC_ge_0'.
            move=>i.
            abstract: pos2 i.
            apply Rmult_le_pos; last apply D_bounds.
            abstract: pos3 i.
            apply Rmult_le_pos; last (apply pow_le; lra).
            apply interface.choose_pos.
        }
        apply Rmult_le_compat_r; first (apply pow_le; lra).
        apply Rmult_le_compat_l; first done.
        etrans.
        { apply SeriesC_le.
          - move=>i.
            split; first done.
            by apply Rmult_le_compat_l; last apply D_bounds.
          - apply ex_seriesC_scal_r.
            eexists.
            apply is_seriesC_negative_choose.
            apply Rabs_def1; lra.
        }
        rewrite SeriesC_scal_r.
        erewrite is_seriesC_unique; first done.
        apply is_seriesC_negative_choose.
        apply Rabs_def1; lra.
      }
      apply ex_seriesC_scal_l.
      rewrite -ex_seriesC_nat.
      apply Series.ex_series_geom.
      apply Rabs_def1;
        lra.
    }
    { apply fubini1_ext. }
    rewrite fubini2_eq.

    etrans; last first.
    {
      apply SeriesC_ext.
      move=>j.
      rewrite -fubini_pos_seriesC' //.
    }
    simpl.
    etrans; last first.
    {
      apply SeriesC_ext.
      move=>j.
      etrans; last first.
      {
        apply SeriesC_ext.
        move=>i.
        apply SeriesC_ext.
        move=>k.
        instantiate (1 := λ (k : nat), if bool_decide (i ≤ j) && bool_decide (k = j - i) then (s0 ^ (r + 1) * s1 ^ (k + i) *
     interface.choose (i + r - 1) i * D (k + i)%nat)%R else 0%R).
        simpl.
        rewrite /h !pow_add /=.
        repeat case_bool_decide; simpl; try lia; try lra.
      }
      etrans; last first.
      {
        apply (SeriesC_ext
                 (λ i, if bool_decide (i ≤ j)
                       then
                         SeriesC (λ (k : nat), if bool_decide (k = j - i) then (s0 ^ (r + 1) * s1 ^ (k + i) * interface.choose (i + r - 1) i * D (k + i)%nat)%R else 0%R)
        else 0%R)).
        move=>i.
        case_bool_decide; first done.
        symmetry.
        by apply SeriesC_0.
      }
      etrans; last first.
      {
        apply (SeriesC_ext
                 (λ i, if bool_decide (i ≤ j)
                       then
                         (s0 ^ (r + 1) * s1 ^ j * interface.choose (i + r - 1) i * D j)%R
                 
                       else 0%R)).
        move=>i.
        case_bool_decide as i_j; last lra.
        rewrite -(SeriesC_singleton (j - i) (_ * _)).
        apply SeriesC_ext.
        move=>k.
        case_bool_decide; last done.
        by replace j with (k + i) by lia.
      }
      reflexivity.
    }
    etrans; last first.
    {
      apply (SeriesC_ext  (λ j : nat,
                             SeriesC
                               (λ i : nat,
                                  (s0 ^ (r + 1) * s1 ^ j * D j *
                                   if bool_decide (i ≤ j)
                                   then
                                     interface.choose (i + r - 1) i
                                else 0%R))%R)).
      move=>j.
      apply SeriesC_ext.
      move=>i.
      case_bool_decide; lra.
    }
    apply SeriesC_ext.
    move=>j.
    rewrite SeriesC_scal_l -choose_sum_split.
    replace (j + (r + 1) - 1) with (j + r) by lia.
    lra.
  Qed.
  
  Instance NegativeOfGeometric : negative_binomial_spec negative_of_geometric.
  Proof.
    refine (NegativeSpec _ _ _ _ _ _ _ _ _).
    {
      iIntros (p q p_pos p_lt_Sq r D ε ε_term term_pos D_pos D_sum) "Hterm Herr".
      unfold negative_of_geometric.
      do 8 wp_pure.
      iRevert (D ε ε_term term_pos D_pos D_sum) "Hterm Herr".
      iInduction (r) as [|r] "IH";
        iIntros (D ε ε_term term_pos D_pos D_sum) "Hterm Herr".
      - wp_pures.
        iModIntro.
        iExists 0.
        iSplitR; first done.
        rewrite /negative_binom_prob /choose in D_sum.
        erewrite (SeriesC_ext _ (λ k, if bool_decide (k = 0) then D 0 else 0)) in D_sum; last first.
        { intros k.
          unfold interface.choose.
          do 2 case_bool_decide; try lia; subst; simpl; last lra.
          rewrite Rcomplements.C_n_n.
          lra.
        }
        rewrite SeriesC_singleton in D_sum.
        rewrite -D_sum //.
      - erewrite SeriesC_ext in D_sum; last first.
        { move=> n.
          rewrite -Nat.add_1_r //.
        }
        rewrite negative_sum_geometric_split in D_sum.
        wp_pures.
        wp_bind (geometric _ _ _).
        iApply tgl_wp_wand_r.
        rewrite -(Rplus_half_diag ε_term).
        iPoseProof (ec_split with "Hterm") as "[Hterm_now Hterm_next]"; try lra.
        iSplitL "Hterm_now Herr";
          first wp_apply (twp_geometric_adv_comp _ _ _ _ _ _ _ _ _ D_sum with "Hterm_now Herr").
        iIntros (v) "(%k & -> & H)".
         wp_pure.
         replace (S r - 1 : Z) with (r : Z) by lia.
         wp_bind ((rec: _ _ := _)%V _)%E.
         iApply tgl_wp_wand_r.
         iSplitL.
         { wp_apply ("IH" $! (λ i, (D (k + i))) with "[] [] [] Hterm_next");
             try done.
           iPureIntro.
           lra.
         } 
         iIntros (v) "(%k' & -> & H)".
         wp_pures.
         iModIntro.
         iExists (k' + k).
         iSplitR.
         { iPureIntro.
           f_equal.
           rewrite Nat2Z.inj_add //.
         }
         rewrite Nat.add_comm //.
    }
        Abort.
End GeometricToNegative.
