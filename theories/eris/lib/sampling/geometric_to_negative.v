From clutch.eris.lib.sampling.negative_binomial Require Import interface.
From clutch.eris.lib.sampling.geometric Require Import interface.
From clutch.eris.lib.sampling Require Import utils.
From Coquelicot Require Import PSeries ElemFct RInt RInt_analysis Continuity.

Section GeometricToNegative.
  Context `{!erisGS Σ}.
  Context `{!geometric_spec geometric galloc}.
  
  Definition negative_of_geometric : val :=
    λ: "α" "p" "q" "r",
      (rec: "loop" "r" :=
          if: ("r" ≤ #0)
          then #0
          else "loop" ("r" - #1) + geometric "α" "p" "q") "r".

  Definition nalloc : val :=
    λ: "p" "q" "r", galloc "p" "q".
  
  Lemma choose_sum_split_fin :
    ∀ (r j : nat),
    interface.choose (j + r) j = SeriesC (λ (i : fin (S j)), interface.choose (i + r - 1) i).
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
  
  Instance NegativeOfGeometric : negative_binomial_spec negative_of_geometric nalloc.
  Proof.
    refine (NegativeSpec _ _ _ _ _ _ _ _ _).
    {
      iIntros (p q p_pos p_lt_Sq r D L ε ε_term term_pos D_bounds D_sum) "Hterm Herr".
      unfold negative_of_geometric.
      do 8 wp_pure.
      iRevert (D L ε ε_term term_pos D_bounds D_sum) "Hterm Herr".
      iInduction (r) as [|r] "IH";
        iIntros (D L ε ε_term term_pos D_bounds D_sum) "Hterm Herr".
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
        rewrite (negative_sum_geometric_split _ _ _ _ L) // in D_sum.
        wp_pures.
        wp_bind (geometric _ _ _).
        iApply tgl_wp_wand_r.
        rewrite -(Rplus_half_diag ε_term).
        iPoseProof (ec_split with "Hterm") as "[Hterm_now Hterm_next]"; try lra.
        iSplitL "Hterm_now Herr";
          first wp_apply (twp_geometric_adv_comp _ _ _ _ _ _ _ _ _ _ D_sum with "Hterm_now Herr").
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
