From Coq Require Import Reals Lia Lra.
From clutch.prelude Require Export Reals_ext Coquelicot_ext Series_ext.
From stdpp Require Export ssreflect.
From Coquelicot Require Import ElemFct RInt RInt_analysis Continuity.
From clutch.eris.lib.sampling.utils Require Import maclaurin.

Section PowerFunction.

  (* General power function *)
  Definition gpow (α : R) (x : R) := exp (α * ln x).
  
  Lemma gpow_pow : ∀ (n : nat) (x : R), (0 < x)%R → (gpow  n x = x ^ n)%R.
  Proof.
    move=>n x x_pos.
    unfold gpow.
    rewrite Rmult_comm -exp_pow exp_ln //.
  Qed.

  Lemma gpow_plus (α β x: R) : (gpow (α + β) x = gpow α x * gpow β x)%R.
  Proof.
    unfold gpow.
    rewrite Rmult_plus_distr_r exp_plus //.
  Qed.

  Lemma gpow_opp (α x : R) : (gpow (-α) x = / gpow α x)%R.
  Proof.
    unfold gpow.
    rewrite -Ropp_mult_distr_l exp_Ropp //.
  Qed.

  Lemma gpow_pos (α x : R) : (0 < gpow α x)%R.
  Proof.
    unfold f.
    apply exp_pos.
  Qed.

   
  Lemma gpow_increasing :
    ∀ (α : R),
    (0 <= α)%R →
    ∀ (x y : R),
    (0 < x <= y)%R →
    (gpow α x <= gpow α y)%R.
  Proof.
    move=>α α_pos x y [x_pos y_ge_x].
    unfold gpow.
    destruct (Req_dec x y) as [-> | x_ne_y]; first reflexivity.
    destruct (Req_dec α 0) as [-> | α_ne_0]; first rewrite !Rmult_0_l //.
    left.
    apply exp_increasing,
            Rmult_lt_compat_l; first lra.
    apply ln_increasing; lra.
  Qed.

  Lemma gpow_decreasing :
    ∀ (α : R),
    (α < 0)%R →
    ∀ (x y : R),
    (0 < x <= y)%R →
    (gpow α y <= gpow α x)%R.
  Proof.
    move=>α α_pos x y [x_pos y_ge_x].
    unfold gpow.
    destruct (Req_dec x y) as [-> | x_ne_y]; first reflexivity.
    destruct (Req_dec α 0) as [-> | α_ne_0]; first rewrite !Rmult_0_l //.
    left.
    apply exp_increasing,
            Ropp_lt_cancel.
    rewrite !Ropp_mult_distr_l.
    apply Rmult_lt_compat_l; first lra.
    apply ln_increasing; lra.
  Qed.
  
  Lemma continuous_gpow (α x : R) : (0 < x)%R → @continuous Hierarchy.R_UniformSpace Hierarchy.R_UniformSpace (gpow α) x.
  Proof.
    move=>x_pos.
    unfold gpow.
    apply continuous_exp_comp,
            (@continuous_scal _ _ Hierarchy.R_NormedModule).
    { apply continuous_const. }
    { by apply continuous_ln. }
  Qed.
    
  Lemma is_derive_gpow : ∀ α x, (0 < x)%R → @Derive.is_derive _ Hierarchy.R_NormedModule (gpow α) x (α * gpow (α - 1) x)%R.
  Proof.
    move=>α x x_pos.
    unfold gpow.
    rewrite Rmult_minus_distr_r Rmult_1_l exp_plus -(ln_Rinv x) // exp_ln; last real_solver.
    rewrite -Rmult_assoc (Rmult_comm _ (/ x)) -Rmult_assoc (Rmult_comm _ α).
    apply (@Derive.is_derive_comp _ Hierarchy.R_NormedModule exp).
    - apply is_derive_exp.
    - apply Derive.is_derive_scal, is_derive_ln, x_pos.
  Qed.

  Lemma derive_gpow : ∀ α x, (0 < x)%R → Derive.Derive (gpow α) x = (α * gpow (α - 1) x)%R.
  Proof.
    move=>α x x_pos.
    apply Derive.is_derive_unique, is_derive_gpow, x_pos.
  Qed.

  (* shifted power function *)
  Definition spow α x := gpow α (x + 1)%R.

  Lemma spow_pos : ∀ (α x : R), (0 < spow α x)%R.
  Proof.
    move=>α x.
    unfold spow.
    apply gpow_pos.
  Qed.
  
  Lemma spow_plus (α β x: R) : (spow (α + β) x = spow α x * spow β x)%R.
  Proof.
    apply gpow_plus.
  Qed.
  
  Lemma spow_opp (α x: R) : (spow (-α) x = / spow α x)%R.
  Proof.
    unfold spow.
    apply gpow_opp.
  Qed.
  
  Lemma is_derive_spow : ∀ α x, (-1 < x)%R → @Derive.is_derive _ Hierarchy.R_NormedModule (spow α) x (α * spow (α - 1) x)%R.
  Proof.
    move=>α x x_pos.
    unfold spow.
    rewrite -(Rmult_1_l (α * _)%R).
    apply (@Derive.is_derive_comp _ Hierarchy.R_NormedModule (gpow α)).
    - apply is_derive_gpow.
      lra.
    - rewrite -{2}(Rplus_0_r 1).
      apply (@Derive.is_derive_plus _ Hierarchy.R_NormedModule id (const 1%R) x 1%R 0%R).
      { apply (@Derive.is_derive_id Hierarchy.R_AbsRing). }
      { apply (@Derive.is_derive_const Hierarchy.R_AbsRing). }
  Qed.

  Lemma derive_spow : ∀ α x, (-1 < x)%R → Derive.Derive (spow α) x = (α * spow (α - 1) x)%R.
  Proof.
    move=>α x x_bound.
    apply Derive.is_derive_unique, is_derive_spow, x_bound.
  Qed.

  Lemma continuous_spow : ∀ α x, (-1 < x)%R → 
                              @continuous Hierarchy.R_UniformSpace Hierarchy.R_UniformSpace (spow α) x.
  Proof.
    move=>α x x_gt.
    apply (@Derive.ex_derive_continuous _ Hierarchy.R_NormedModule).
    eexists.
    by apply is_derive_spow.
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

  Lemma is_derive_n_spow :
    ∀ n α x,
    (-1 < x)%R →
    Derive.is_derive_n (spow α) n x ((prod_sub_n n α) * spow (α - n) x)%R.
  Proof.
    elim=>[|n IH] α x x_pos;
          first rewrite Rminus_0_r Rmult_1_l //.
    rewrite S_INR prod_sub_n_last Rminus_plus_distr Rmult_assoc -derive_spow // -Derive.Derive_scal.
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
      rewrite (Derive.is_derive_n_unique (spow α) n _ _ (IH _ _ y_pos)) //.
    }
    apply Derive.Derive_correct, Derive.ex_derive_scal.
    eexists.
    by apply is_derive_spow.
  Qed.

  Lemma ex_derive_n_spow :
    ∀ n α x,
    (-1 < x)%R →
    Derive.ex_derive_n (spow α) n x.
  Proof.
    move=>[//|n] α x x_gt.
    simpl.
    eexists.
    by apply (is_derive_n_spow (S n)).
  Qed.

  Definition Rem (α : R) (n : nat) (x : R) :=
    (prod_sub_n (S n) α / fact n *
         @RInt Hierarchy.R_CompleteNormedModule
           (λ t : R,
                spow (α - 1) t *
                  ((x - t) / (1 + t)) ^ n) 0 x)%R.


  Definition Coeff (α x : R) : R :=
    if (Rle_dec 0 α)
    then spow α (Rmax 0 x)
    else spow α (Rmin 0 x).

  Lemma Coeff_pos :
    ∀ (α x : R), (0 < Coeff α x)%R.
  Proof.
    move=>α x.
    unfold Coeff.
    destruct (Rle_dec 0 α);
      apply spow_pos.
  Qed.
 
  Lemma Coeff_upper_bound :
    ∀ (α : R) (x : R), 
    (Rabs x < 1)%R →
    ∀ (t : R),
    (Rmin 0 x < t < Rmax 0 x)%R →
    (spow α t <= Coeff α x)%R.
  Proof.
    move=>α x x_bounds t t_bounds.
    destruct (Rle_dec 0 x) as [x_ge | x_lt].
    { rewrite Rmin_left in t_bounds; last lra.
      rewrite Rmax_right in t_bounds; last lra.
      unfold Coeff.
      destruct (Rle_dec 0 α).
      - rewrite Rmax_right; last lra.
        unfold spow.
        apply gpow_increasing; lra.
      - rewrite Rmin_left; last lra.
        unfold spow.
        apply gpow_decreasing; lra.
    }
    { rewrite Rmin_right in t_bounds; last lra.
      rewrite Rmax_left in t_bounds; last lra.
      unfold Coeff.
      apply Rabs_def2 in x_bounds as [_ x_gt].
      destruct (Rle_dec 0 α).
      - rewrite Rmax_left; last lra.
        unfold spow.
        apply gpow_increasing; lra.
     - rewrite Rmin_right; last lra.
       unfold spow.
       apply gpow_decreasing; lra.
    } 
  Qed.

  #[local] Definition integrand (x : R) (t : R) := (Rabs (x - t) / (1 + t))%R.

  Lemma integrand_pos : ∀ (x t : R), (-1 < t)%R → (0 <= integrand x t)%R.
  Proof.
    move=>x t t_gt.
    unfold integrand.
    apply Rcomplements.Rdiv_le_0_compat; first apply Rabs_pos.
    lra.
  Qed.
  
  Lemma continuous_integrand :
    ∀ (x t : R),
    (t ≠ -1)%R →
    @continuous Hierarchy.R_UniformSpace Hierarchy.R_UniformSpace (integrand x) t.
  Proof.
    move=>x t t_ne_1.
    unfold integrand.
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

  Lemma integrand_max : ∀ (x t : R),
    (Rabs x < 1)%R →
    (Rmin 0 x < t < Rmax 0 x)%R →
    (integrand x t < Rabs x)%R.
  Proof.
    move=>x t x_bounds t_bounds.
    apply Rabs_def2 in x_bounds as [x_gt x_lt].
    unfold integrand.
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

  #[local] Definition Int (x : R) (n : nat) :=
    (@RInt Hierarchy.R_CompleteNormedModule
           (λ t : R,
                  ((integrand x t) ^ n)) (Rmin 0 x) (Rmax 0 x))%R.

  Lemma ex_RInt_Int : ∀ (n : nat) (x : R), (-1 < x)%R → @ex_RInt Hierarchy.R_NormedModule (λ t, (integrand x t) ^ n)%R (Rmin 0 x) (Rmax 0 x).
  Proof.
    move=>n x x_bounds.
    apply (@ex_RInt_continuous Hierarchy.R_CompleteNormedModule).
    move=>t t_bounds.
    unshelve eapply (continuous_comp _ _ _ _ (continuous_pow n _)).
    apply continuous_integrand.
    rewrite Rmin_left in t_bounds; last apply Rcomplements.Rmin_Rmax.
    rewrite Rmax_right in t_bounds; last apply Rcomplements.Rmin_Rmax.
    destruct (Rlt_dec 0 x).
    { rewrite Rmin_left in t_bounds; lra. }
    { rewrite Rmin_right in t_bounds; lra. }
  Qed.
 
  Lemma Int_pos : ∀ (x : R) (n : nat), (-1 < x)%R → (0 <= Int x n)%R.
  Proof.
    move=>x n x_gt.
    apply RInt_ge_0; first apply Rcomplements.Rmin_Rmax.
    { by apply ex_RInt_Int. }
    { move=>t t_bounds.
      apply pow_le, integrand_pos.
      destruct (Rlt_dec 0 x).
      { rewrite Rmin_left in t_bounds; lra. }
      { rewrite Rmin_right in t_bounds; lra. }
    }
  Qed.
 
  Lemma Int_ratio :
    ∀ (x : R) (n : nat),
    (Rabs x < 1)%R →
    (Int x (S n) <= Rabs x * Int x n)%R.
  Proof.
    move=> x n x_bounds.
    pose proof (Rabs_def2 _ _ x_bounds) as [x_lt x_gt].
    unfold Int.
    pose proof (@RInt_scal Hierarchy.R_CompleteNormedModule (λ t, (integrand x t)^n)%R (Rmin 0 x) (Rmax 0 x) (Rabs x)) as H.
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
    { apply pow_le, integrand_pos.
      destruct (Rlt_dec 0 x).
      { rewrite Rmin_left in t_bounds; lra. }
      { rewrite Rmin_right in t_bounds; lra. }
    }
    left.
    by apply integrand_max.
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
      unfold spow.
      apply (@continuous_mult Hierarchy.R_UniformSpace Hierarchy.R_AbsRing).
      { apply continuous_spow.
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
      rewrite Rabs_mult (Rabs_right (spow (α - 1) t)); last (apply Rle_ge; left; apply spow_pos).
      rewrite -RPow_abs Rabs_div (Rabs_right (1 + t)); last first.
      { destruct (Rlt_dec 0 x).
        { rewrite Rmin_left in t_bounds; lra. }
        { rewrite Rmin_right in t_bounds; lra. }
      }
      by fold (integrand x t).
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
      { apply continuous_spow.
        destruct (Rlt_dec 0 x).
        { rewrite Rmin_left in t_bounds; lra. }
        { rewrite Rmin_right in t_bounds; lra. }
      }
      unshelve eapply (continuous_comp _ _ _ _ (continuous_pow n (integrand x t))).
      apply continuous_integrand.
      destruct (Rlt_dec 0 x).
      { rewrite Rmin_left in t_bounds; lra. }
      { rewrite Rmin_right in t_bounds; lra. }
    }
    { by apply (@ex_RInt_scal Hierarchy.R_NormedModule), ex_RInt_Int. }
    move=>t t_bounds.
    apply Rmult_le_compat_r.
    { apply pow_le, integrand_pos.
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
   rewrite -gpow_pow /f; last lra.
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
    
  Lemma spow_maclaurin : ∀ (α x : R) (n : nat),
    (Rabs x < 1)%R →
    spow α x =
    (sum_f_R0
       (λ k : nat,
          x ^ k / fact k *
                (prod_sub_n k α * spow (α - k) 0)) n + Rem α n x
       )%R
 .
  Proof.
    move=>α x n x_bounds.
    unfold Rem.
    apply Rabs_def2 in x_bounds as [x_lt x_gt].
    assert (-1 < x < 1)%R as x_bounds by lra.
    rewrite (integral_maclaurin (spow α) n x); last first.
    { move=>t t_bounds.
      apply (@Derive.ex_derive_continuous _ Hierarchy.R_NormedModule),
              (ex_derive_n_spow (S (S n))).
      destruct (Rlt_ge_dec 0 x);
      [ rewrite Rmin_left in t_bounds | rewrite Rmin_right in t_bounds];
        lra.
    }
    { move=>t t_bounds k _.
      apply ex_derive_n_spow.
      destruct (Rlt_ge_dec 0 x);
      [ rewrite Rmin_left in t_bounds | rewrite Rmin_right in t_bounds];
        lra.
    }
    erewrite sum_eq; last first.
    { move=>k _.
      rewrite (Derive.is_derive_n_unique _ _ _ _ (is_derive_n_spow k α 0 _)) //.
      lra.
    }
    erewrite RInt_ext; last first.
    { move=>t t_bounds.
      rewrite (Derive.is_derive_n_unique _ _ _ _ (is_derive_n_spow (S n) α t _)); last first.
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
        apply is_derive_spow.
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
    rewrite spow_plus spow_opp !Rmult_assoc.
    f_equal.
    unfold spow.
    rewrite gpow_pow /=; last first.
    { destruct (Rlt_ge_dec 0 x);
        [ rewrite Rmin_left in t_bounds | rewrite Rmin_right in t_bounds];
        lra.
    }
    rewrite Rpow_mult_distr pow_inv (Rplus_comm 1 t).
    lra.
  Qed.

 Lemma is_series_spow :
   ∀ (α x : R),
    (Rabs x < 1)%R →
    @Series.is_series _ Hierarchy.R_NormedModule
      (λ k : nat,
         x ^ k / fact k *
               prod_sub_n k α)%R (spow α x).
  Proof.
    move=>α x x_bounds.
    apply Series_Ext.is_lim_seq_is_series.
    eapply Lim_seq.is_lim_seq_ext.
    { move=>n.
      rewrite Hierarchy.sum_n_Reals //.
    }
    apply lim_seq_dist_0.
    apply (Lim_seq.is_lim_seq_ext (λ n, Rabs (Rem α n x))).
    { move=>n.
      rewrite -(Rabs_Ropp (_ - spow α x)%R) Ropp_minus_distr (spow_maclaurin _ _ n); last done.
      erewrite sum_eq; last first.
      {
        move=>k _.
        unfold spow, gpow.
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

End PowerFunction.
