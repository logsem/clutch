From clutch.eris.lib.sampling Require Import utils.
From Coq Require Import Reals Lia Lra.
From clutch.prelude Require Export Reals_ext.
From stdpp Require Export ssreflect.
From stdpp Require Export base.
From Coquelicot Require Import Rcomplements.
From clutch.eris Require Export total_primitive_laws proofmode.

Section RealSequence.

  #[local] Open Scope R_scope.
  
  Fixpoint P (n : nat) : (nat → R) → R :=
    match n with
    | 0 => λ _, 1%R
    | S m => λ α, (P m α * α m)%R
    end.

  Definition L (n : nat) (α : nat → R) : R := P n (λ i, / (1 - (α i)))%R.

  Lemma P_ext : ∀ (n : nat) (α β : nat → R), (∀ (i : nat), (i < n)%nat → α i = β i) → P n α = P n β.
  Proof.
    elim=>[//|n IH] α β /= α_eq_β.
    rewrite α_eq_β; last lia.
    rewrite (IH α β) // => i i_lt_n.
    apply α_eq_β; last lia.
  Qed.

  Lemma L_ext : ∀ (n : nat) (α β : nat → R), (∀ (i : nat), (i < n)%nat → α i = β i) → L n α = L n β.
  Proof.
    move=>n α β α_eq_β.
    apply P_ext.
    move=>i i_lt_n.
    rewrite α_eq_β //.
  Qed.

  Lemma P_last (n : nat) (α : nat → R) : P (S n) α = P n α * α n.
  Proof.
    trivial.
  Qed.

  Lemma L_last (n : nat) (α : nat → R) : L (S n) α = L n α / (1 - α n).
  Proof.
    trivial.
  Qed.

  Lemma P_gt_0 : ∀ (n : nat) (α : nat → R), (∀ (i : nat), (i < n)%nat → 0 < α i) → 0 < P n α.
  Proof.
    elim=>[//|n IH] α α_gt_0 /=; first lra.
    apply Rmult_lt_0_compat; auto.
  Qed.

  Lemma L_gt_0 : ∀ (n : nat) (α : nat → R), (∀ (i : nat), (i < n)%nat → α i < 1) → 0 < L n α.
  Proof.
    move=>n α α_lt_1.
    apply P_gt_0.
    move=>i i_lt_n.
    apply Rinv_pos.
    specialize (α_lt_1 i i_lt_n).
    lra.
  Qed.

  Lemma P_ge_1 : ∀ (n : nat) (α : nat → R), (∀ (i : nat), (i < n)%nat → 1 <= α i) → 1 <= P n α.
  Proof.
    elim=>[//|n IH] α α_ge_1 /=.
    rewrite -(Rmult_1_l 1).
    apply Rmult_le_compat; [lra | lra | auto..].
  Qed.

  Lemma L_ge_1 : ∀ (n : nat) (α : nat → R), (∀ (i : nat), (i < n)%nat → 0 <= α i < 1) → 1 <= L n α.
  Proof.
    move=>n α α_0_1.
    apply P_ge_1.
    move=>i i_lt_n.
    rewrite -{1}Rinv_1.
    specialize (α_0_1 i i_lt_n).
    apply Rinv_le_contravar; lra.
  Qed.

  Lemma P_gt_1 : ∀ (n : nat) (α : nat → R), (∀ (i : nat), (i ≤ n)%nat → 1 < α i) → 1 < P (S n) α.
  Proof.
    elim=>[|n IH] α α_gt_1 /=.
    { specialize (α_gt_1 0%nat ltac:(reflexivity)). lra. }
    rewrite -(Rmult_1_l 1).
    transitivity (1 * α (S n)).
    { specialize (α_gt_1 (S n)%nat ltac:(reflexivity)). lra. }
    apply Rmult_lt_compat_r.
    { specialize (α_gt_1 (S n)%nat ltac:(reflexivity)). lra. }
    apply IH.
    move=>i i_le_n.
    apply α_gt_1.
    lia.
  Qed.

  Lemma L_gt_1 : ∀ (n : nat) (α : nat → R), (∀ (i : nat), (i ≤ n)%nat → 0 < α i < 1) → 1 < L (S n) α.
  Proof.
    move=>n α α_0_1.
    apply P_gt_1.
    move=>i i_le_n.
    specialize (α_0_1 i i_le_n).
    rewrite -{1}Rinv_1.
    apply Rinv_lt_contravar; lra.
  Qed.

  Lemma P_inv : ∀ (n : nat) (α : nat → R), / P n α = P n (λ k, / α k).
  Proof.
    elim=>[|n IH] α /=; first apply Rinv_1.
    rewrite Rinv_mult IH //.
  Qed.
    
  Lemma L_inv_P : ∀ (n : nat) (α : nat → R), L n α = / P n (λ k, 1 - α k).
  Proof.
    unfold L.
    move=>n α.
    rewrite P_inv //.
  Qed.
  
  Fixpoint α (n : nat) (r : nat → R) (i : nat) : R :=
    match n with
    | 0 => ((1 - / (r 0%nat)) / 2)%R
    | S m =>
        let C := (r m * r (S m) / (r m + r (S m) - 1))%R in
        let r' := λ j, if bool_decide (j = m) then Rmin (r m) C else r j in
        let αr' := α m r' in
        let Lm := L (S m) αr' in
        let a := (Lm - 1) / (r m - 1) in
        let b := 1 - (Lm / (r (S m))) in
        if bool_decide (i = S m)
        then ((a + b) / 2)%R
        else (αr' i)
    end.

  Lemma α_bounds :
    ∀ (n : nat) (r : nat → R),
    (∀ (i : nat), i ≤ n → 1 < r i)%R →
    let αr := α n r in
    (∀ (i : nat), i ≤ n → (0 < αr i < 1)) ∧
    (∀ (i : nat), i ≤ n → (L (S i) αr < r i)%R) ∧
    (∀ (i : nat), (i < n)%nat →
                  (0 < ((L (S i) αr - 1) / (r i - 1)) < αr (S i))%R).
  Proof.
    elim=>[|n IH] r r_bounds αr.
    { split.
      - move=>i i_le_0.
        specialize (r_bounds i i_le_0).
        replace i with 0%nat in * by lia.
        unfold L, P, αr, α.
        split.
        + apply Rdiv_lt_0_compat; last lra.
          rewrite -Rminus_lt_0.
          apply Rinv_lt_cancel; first lra.
          rewrite Rinv_1 Rinv_inv //.
        + rewrite Rlt_div_l; last lra.
          transitivity 1; last lra.
          rewrite -{2}(Rminus_0_r 1).
          apply Rplus_le_lt_compat; first reflexivity.
          apply Ropp_lt_contravar, Rinv_pos.
          lra.
      - split; last lia.
        move=>i i_le_0.
        specialize (r_bounds i i_le_0).
        replace i with 0%nat in * by lia.
        unfold L, P, αr, α.
        rewrite Rmult_1_l.
        apply Rinv_lt_cancel; first lra.
        rewrite Rinv_inv Rlt_minus_r Rdiv_plus_distr -Ropp_div_distr_l
                -Rminus_def Rplus_minus_assoc Rplus_minus_swap
                -{1}(Rmult_1_r (/ r 0%nat)) -Rmult_minus_distr_l.
        replace (1 - / 2) with (1 / 2) by lra.
        rewrite -Rlt_minus_r.
        replace (1 - 1 /2) with (1 * (1 / 2)) by lra.
        apply Rmult_lt_compat_r; first lra.
        apply Rinv_lt_cancel; first lra.
        rewrite Rinv_inv Rinv_1 //.
    }
    set (C := (r n * r (S n) / (r n + r (S n) - 1))%R).
    set (r' := λ j, if bool_decide (j = n) then Rmin (r n) C else r j).
    assert (1 < r n) by (apply r_bounds; lia).
    assert (1 < r (S n)) by (apply r_bounds; lia).
    move=>[:C_gt_1].
    unshelve epose proof (IH r' _) as (IH1 & IH2 & IH3).
    { move=>j j_le_n.
      unfold r'.
      case_bool_decide; last (apply r_bounds; lia).
      apply Rmin_glb_lt; first (apply r_bounds; lia).
      abstract: C_gt_1.
      unfold C.
      rewrite -Rlt_div_r; last lra.
      rewrite Rmult_1_l Rplus_comm Rplus_minus_swap -Rlt_minus_r
              -{2}(Rmult_1_r (r n)) -Rmult_minus_distr_l
              -{1}(Rmult_1_l (r (S n) - 1)).
      apply Rmult_lt_compat_r; lra.
    }
    pose proof (IH2 n ltac:(reflexivity)) as LSn_lt_rn.
    unfold r' at 2 in LSn_lt_rn.
    case_bool_decide as tmp; last lia.
    clear tmp.
    apply Rmin_Rgt_l in LSn_lt_rn as [LSn_lt_rn LSn_lt_C].
    unshelve epose proof (L_gt_1 n (α n r') _) as LSn_gt_1.
    {
      move=>i i_lt_Sn.
      apply IH1.
      lia.
    }
    unfold Rgt in LSn_lt_rn, LSn_lt_C.
    set (Lb := (L (S n) (α n r') - 1) / (r n - 1)).
    set (Rb := 1 - (L (S n) (α n r') / r (S n))).
    set (αSn := (Lb + Rb) / 2).
    
    assert (0 < Lb).
    {
      unfold Lb.
      apply Rmult_lt_0_compat; first lra.
      apply Rinv_pos. lra.
    }
    
    assert (Rb < 1).
    {
      unfold Rb.
      rewrite -{2}(Rminus_0_r 1).
      apply Rplus_le_lt_compat; first reflexivity.
      apply Ropp_lt_contravar, Rmult_lt_0_compat; first lra.
      apply Rinv_pos. lra.
    }

    assert (Lb < Rb) as Lb_lt_Rb.
    {
      unfold Lb, Rb.
      set (LSn := L (S n) (α n r')).
      set (x := r n).
      set (y := r (S n)).
      rewrite Rdiv_plus_distr.
      setoid_rewrite Rdiv_def at 2.
      rewrite -Ropp_mult_distr_l -Rdiv_def -Rminus_def Rlt_minus_l
              -Rplus_minus_swap Rlt_minus_r Rdiv_plus; try (unfold x, y; lra).
      rewrite (Rmult_comm (x - 1) y) Rdiv_mult_distr.
      replace 1%R with ((x - 1) / (x - 1))%R at 3; last first.
      {
        unfold x.
        apply Rdiv_diag.
        lra.
      }
      rewrite -Rdiv_plus_distr -Rmult_plus_distr_l.
      apply Rmult_lt_compat_r.
      { apply Rinv_pos. unfold x. lra. }
      replace (x - 1 + 1) with x by lra.
      rewrite Rlt_div_l; last (unfold y; lra).
      rewrite Rlt_div_r; last (unfold x, y; lra).
      rewrite Rplus_minus_assoc Rplus_comm.
      unfold LSn, x, y.
      by fold C.
    }

    apply Rlt_half_plus in Lb_lt_Rb as αSn_bounds.
    fold αSn in αSn_bounds.
    split; last split.
    - move=>i i_le_Sn.
      unfold αr.
      simpl.
      case_bool_decide.
      + fold C r'.
        fold Lb Rb.
        lra.
      + fold α C r'.
        apply IH1.
        lia.
    - move=>i i_le_Sn.
      destruct (decide (i = S n)) as [-> | i_not_Sn].
      + rewrite L_last.
        unfold αr, α at 2.
        case_bool_decide; last done.
        fold α C r' Lb Rb αSn.
        rewrite Rlt_div_l; last lra.
        rewrite Rmult_comm -Rlt_div_l; last lra.
        rewrite Rlt_minus_r Rplus_comm -Rlt_minus_r.
        rewrite (L_ext _ _ (α n r')); last first.
        {
          move=>i i_lt_Sn.
          unfold α.
          by case_bool_decide; first lia.
        }
        fold Rb.
        lra.
      + rewrite (L_ext _ _ (α n r')); last first.
        {
          move=>j j_lt_Si.
          unfold αr, α at 1.
          by case_bool_decide; first lia.
        }
        specialize (IH2 i ltac:(lia)).
        unfold r' in IH2.
        by case_bool_decide; first subst.
    - move=>i i_lt_Sn.
      rewrite (L_ext _ _ (α n r')); last first.
      {
        move=>j j_lt_Si.
        unfold αr, α at 1.
        by case_bool_decide; first lia.
      }
      unfold αr, α.
      case_bool_decide as Si_Sn.
      + injection Si_Sn as ->.
        fold α C r' Lb Rb αSn.
        lra.
      + specialize (IH3 i ltac:(lia)).
        fold α C r'.
        unfold r' at 2 4 in IH3.
        by case_bool_decide; first subst.
  Qed.

  Definition β (n : nat) (r : nat → R) :=
    let r' k := if bool_decide (k = n) then 2 else r (S k) in
    α n r'.
  
  Lemma β_bounds :
    ∀ (n : nat) (r : nat → R),
    (∀ (i : nat), (i ≤ n)%nat → 1 < r i)%R →
    let βr := β n r in
    (∀ (i : nat),
       (i ≤ n)%nat →
       (0 <= ((L i βr - 1) / (r i - 1)) < βr i ∧ βr i < 1)).
  Proof.
    move=>n r r_gt_1 βr i i_le_n.
    set (r' k := if bool_decide (k = n) then 2 else r (S k)).
    unshelve epose proof (α_bounds n r' _) as (β1 & β2 & β3).
    {
      move=>j j_le_n.
      unfold r'.
      case_bool_decide; first lra.
      apply r_gt_1.
      lia.
    }
    unfold βr, β.
    fold r'.
    destruct i.
    - unfold L, P.
      rewrite Rminus_diag Rdiv_0_l.
      specialize (β1 0%nat ltac:(lia)).
      lra.
    - specialize (β3 i i_le_n).
      specialize (β1 (S i) ltac:(lia)).
      split; last lra.
      unfold r' in β3.
      simpl in β3.
      unfold r'.
      case_bool_decide; first lia.
      lra.
  Qed.
  
End RealSequence.
#[global] Opaque α.

Section Planner.
  
  #[local] Open Scope R_scope.
  
  Context `{!erisGS Σ}.
  Context {A : Type}.
  Context `{Countable A}.
  Context (μ : A → R).
  Context (μ_pos : ∀ (a : A), 0 <= μ a).
  Context (μ_lt_1 : ∀ (a : A), μ a < 1).

  Context (μ_m : R).
  Context (mass_μ_le_1 : μ_m <= 1).
  Context (is_seriesC_μ : is_seriesC μ μ_m).
  
  Context (ψ : list A → iProp Σ).
  Context (Φ : iProp Σ).
  Context (presample_adv_comp :
            ∀ (ε : R) (D : A → R) (L : R)
              (l : list A),
              0 < ε →
              (∀ a, 0 <= D a <= L) →
              SeriesC (λ a, μ a * D a) = ε →
              ψ l ∗ ↯ ε ∗ (∀ a, ↯ (D a) -∗ ψ (l ++ [a]) -∗ Φ)
                      ⊢ Φ
          ).

  Section FixedSuffix.

    Context (l suf : list A).
    Context (μ_gt_0 : ∀ (a : A), a ∈ suf → 0 < μ a).
    Context (ε : R).
    Context (ε_pos : 0 < ε).

    Definition Δ' (n : nat) : option R := μ <$> suf !! n.

    Definition Δ (n : nat) : R :=
      match Δ' n with
      | Some p => p
      | None => / 2
      end.

    Lemma Δ_bounds : ∀ (n : nat), 0 < Δ n < 1.
    Proof using μ_gt_0 μ_lt_1.
      move=>n.
      unfold Δ, Δ'.
      destruct (decide (n < length suf)%nat) as [n_lt_len | n_ge_len].
      - apply lookup_lt_is_Some_2 in n_lt_len as [p eq_p].
        rewrite eq_p /=.
        apply elem_of_list_lookup_2 in eq_p.
        auto.
      - rewrite lookup_ge_None_2 /=; last lia.
        lra.
    Qed.

    Definition r (n : nat) := / (1 - Δ n).
    
    Lemma r_gt_1 : ∀ (n : nat), 1 < r n.
    Proof using μ_gt_0 μ_lt_1.
      move=>n.
      unfold r.
      rewrite -{1}Rinv_1.
      pose proof (Δ_bounds n).
      apply Rinv_lt_contravar; lra.
    Qed.
    
    Definition θ := β (length suf) r.

    Lemma θ_bounds :
      ∀ (i : nat), (i < length suf)%nat → 0 <= (L i θ - 1) / (r i - 1) < θ i ∧ θ i < 1.
    Proof using μ_gt_0 μ_lt_1.
      move=>i i_lt_len.
      apply β_bounds; last lia.
      move=>j _. apply r_gt_1.
    Qed.

    Definition k (n : nat) := (1 + θ n * (Δ n / (1 - Δ n))).

    Definition χ (n : nat) := P n (λ k, 1 - θ k).
    
    Definition ε' (n : nat) := χ n * ε.

    Lemma k_pos : ∀ (i : nat), (i < length suf)%nat → 0 < k i.
    Proof using μ_gt_0 μ_lt_1.
      move=>i i_lt_len.
      unfold k.
      pose proof (θ_bounds i i_lt_len).
      pose proof (Δ_bounds i).
      apply Rplus_lt_0_compat; first lra.
      apply Rmult_lt_0_compat; first lra.
      apply Rmult_lt_0_compat; first lra.
      apply Rinv_pos.
      lra.
    Qed.
    
    Lemma ε'0 : ε' 0%nat = ε.
    Proof. rewrite /ε' Rmult_1_l //. Qed.

    Lemma ε'S : ∀ (i : nat), ε' (S i) = ε' i * (1 - θ i).
    Proof.
      move=>i.
      rewrite /ε' /χ P_last.
      lra.
    Qed.

    Lemma ε'_pos : ∀ (i : nat), i ≤ length suf → 0 < ε' i.
    Proof using ε_pos μ_gt_0 μ_lt_1.
      move=>i i_le_len.
      unfold ε'.
      apply Rmult_lt_0_compat; last done.
      apply P_gt_0.
      move=>j j_lt_i.
      pose proof (θ_bounds j ltac:(lia)).
      lra.
    Qed.
    
    Lemma kχ : ∀ (i : nat), (i < length suf)%nat → 1 < k i * χ i.
    Proof using μ_gt_0 μ_lt_1.
      move=>i i_lt_len.
      unfold k, χ.
      pose proof (θ_bounds i i_lt_len) as [[_ almost_goal] _].
      rewrite Rlt_div_l in almost_goal; last first.
      { pose proof (r_gt_1 i). lra. }
      rewrite Rlt_minus_l in almost_goal. 
      unfold r in almost_goal.
      replace (/ (1 - Δ i) - 1) with (Δ i / (1 - Δ i)) in almost_goal; last first.
      {
        replace (Δ i) with (1 - (1 - Δ i)) at 1 by lra.
        pose proof (Δ_bounds i).
        rewrite Rdiv_minus_distr Rdiv_diag; lra.
      }
      rewrite L_inv_P -{1}(Rmult_1_l (/ P i _))
              -Rdiv_def Rlt_div_l in almost_goal; first lra.
      apply P_gt_0.
      move=>j j_lt_i.
      unshelve epose proof (θ_bounds j _); first by etrans.
      lra.
    Qed.

    Lemma kε' : ∀ (i : nat), (i < length suf)%nat → ε < k i * ε' i.
    Proof using μ_gt_0 μ_lt_1 ε_pos.
      move=>i i_lt_len.
      pose proof (kχ i i_lt_len).
      unfold ε'.
      rewrite -Rmult_assoc -{1}(Rmult_1_l ε).
      by apply Rmult_lt_compat_r.
    Qed.
      
    Lemma presample_suffix_increase :
      ∀ (i : nat),
      (i < length suf)%nat →
      ψ (l ++ take i suf) ∗
      ↯ (ε' i) ∗ 
      ((ψ (l ++ take (S i) suf) ∗ ↯ (ε' (S i)) ∨ ∃ (j : list A), ψ (l ++ j) ∗ ↯ (k i * ε' i)) -∗ Φ)
      ⊢ Φ.
    Proof using ε_pos μ_pos μ_gt_0 μ_lt_1 mass_μ_le_1 is_seriesC_μ presample_adv_comp.
      iIntros (i i_lt_len) "(Hψ & Herr & Hnext)".
      pose proof (lookup_lt_is_Some_2 _ _ i_lt_len) as [c lookup_suf_i].
      rewrite (take_S_r _ _ c) //.
      assert (Δ i = μ c) as Δμ.
      {
        unfold Δ, Δ'.
        rewrite lookup_suf_i //.
      }
      set (D a := if bool_decide (a = c) then ε' (S i) else k i * ε' i).
      assert (∀ a, 0 <= D a <= Rmax (ε' (S i)) (k i * ε' i)) as D_bounds.
      {
        move=>a.
        unfold D.
        pose proof (ε'_pos i ltac:(lia)).
        pose proof (ε'_pos (S i) i_lt_len).
        pose proof (k_pos i i_lt_len).
        pose proof (Rmax_l (ε' (S i)) (k i * ε' i)).
        pose proof (Rmax_r (ε' (S i)) (k i * ε' i)).
        case_bool_decide; nra.
      }
      set (ε_wk := (ε' i * (μ c * (1 - θ i) + (μ_m - μ c) +
                              θ i * (μ c * ((μ_m - μ c) / (1 - μ c)))))%R).
      
      specialize (μ_lt_1 c) as μ_c_lt_1.
      apply elem_of_list_lookup_2 in lookup_suf_i as c_elem_suf.
      specialize (μ_gt_0 c c_elem_suf) as μ_c_gt_0.
      pose proof (θ_bounds i i_lt_len) as [??].
      
      assert (0 < ε_wk) as ε_wk_gt_0.
      { move=> [:μ_m_μ_c_diff].
        apply Rmult_lt_0_compat; first (apply ε'_pos; lia).
        apply Rplus_lt_le_0_compat.
        + apply Rplus_lt_le_0_compat.
          * apply Rmult_lt_0_compat; first done.
            lra.
          * abstract: μ_m_μ_c_diff.
            rewrite -(is_seriesC_unique _ _ is_seriesC_μ).
            apply Rle_0_le_minus, SeriesC_ge_elem; first done.
            by eexists.
        + apply Rmult_le_pos; first lra.
          apply Rmult_le_pos; first apply μ_pos.
          apply Rdiv_le_0_compat; first done.
          lra.
      } 

      iPoseProof (ec_weaken _ ε_wk with "Herr") as "Herr".
      { split; first lra.
        unfold ε_wk.
        rewrite -{2}(Rmult_1_r (ε' i)).
        apply Rmult_le_compat_l; first (apply Rlt_le, ε'_pos; lia).
        rewrite -Rmult_assoc (Rmult_comm (θ i))
                   Rplus_comm Rmult_assoc -Rplus_assoc
                -Rmult_plus_distr_l.
        transitivity (μ c + (μ_m - μ c)); last lra.
        apply Rplus_le_compat_r.
        rewrite -{4}(Rmult_1_r (μ c)).
        apply Rmult_le_compat_l; first apply μ_pos.
        rewrite Rplus_minus_assoc Rplus_minus_swap -{2}(Rmult_1_r (θ i))
                -Rmult_minus_distr_l.
        apply Rminus_le.
        rewrite -Rplus_minus_assoc Rminus_diag Rplus_0_r.
        apply Rmult_le_0_l; first lra.
        apply Rle_minus.
        rewrite -Rdiv_le_1; last lra.
        apply Rplus_le_compat_r.
        lra.
      } 
       
      iApply (presample_adv_comp _ D (Rmax (ε' (S i)) (k i * ε' i)) with "[$Herr $Hψ Hnext]"); try assumption.
      {
        rewrite (SeriesC_split_elem _ c); last first.
        {
          eapply (ex_seriesC_le _ (λ a, μ a * _)).
          { move=>a.
            split; last first.
            - apply Rmult_le_compat_l; last apply D_bounds.
              apply μ_pos.
            - apply Rmult_le_pos; last apply D_bounds.
              apply μ_pos.
          }
          apply ex_seriesC_scal_r.
          by eexists.
        }
        {
          move=>a.
          apply Rmult_le_pos; last apply D_bounds.
          apply μ_pos.
        }
        rewrite SeriesC_singleton_dependent.
        unfold D.
        case_bool_decide; last done.
        rewrite ε'S (SeriesC_ext _ (λ a, k i * ε' i * if bool_decide (a ≠ c) then μ a else 0)); last first.
        {
          move=>a.
          repeat case_bool_decide; try contradiction; lra.
        }
        rewrite SeriesC_scal_l.
        replace (SeriesC _) with (μ_m - μ c); last first.
        { 
          rewrite -(is_seriesC_unique _ _ is_seriesC_μ).
          rewrite (SeriesC_split_elem _ c); last first.
          { by eexists. }
          { exact μ_pos. }
          rewrite SeriesC_singleton_dependent.
          lra.
        }
        unfold k.
        rewrite Δμ.
        rewrite
          Rmult_assoc (Rmult_comm (ε' i) (μ_m - μ c))
          (Rmult_comm (ε' i)) -(Rmult_assoc (μ c))
          -(Rmult_assoc _ (μ_m - μ c)) -Rmult_plus_distr_r /ε_wk.
        lra.
      }
      iIntros (a) "Herr Hψ".
      rewrite /D -!app_assoc.
      case_bool_decide; 
        iApply ("Hnext" with "[Hψ Herr]");
        [subst; iLeft | iRight]; iFrame.
    Qed.

    Definition κ (n : nat) : R := (k n * χ n).

    Lemma κ_def : ∀ n, κ n = (k n * ε' n) / ε.
    Proof using ε_pos.
      move=>n.
      unfold κ, ε', χ.
      rewrite -Rmult_assoc -!Rmult_div_assoc Rdiv_diag; lra.
    Qed.

    Lemma κ_gt_1 : ∀ n, (n < length suf)%nat → 1 < κ n.
    Proof using μ_gt_0 μ_lt_1.
      move=>n n_lt_len.
      by apply kχ.
    Qed.

    Lemma presample_suffix_increase' :
     ∀ (i : nat),
      (i < length suf)%nat →
      ψ (l ++ take i suf) ∗
      ↯ (ε' i) ∗ 
      ((ψ (l ++ take (S i) suf) ∗ ↯ (ε' (S i)) ∨ ∃ (j : list A), ψ (l ++ j) ∗ ↯ (κ i * ε)) -∗ Φ)
      ⊢ Φ.
    Proof using ε_pos μ_pos μ_gt_0 μ_lt_1 mass_μ_le_1 is_seriesC_μ presample_adv_comp.
      move=>i.
      rewrite κ_def Rmult_assoc Rinv_l; last lra.
      rewrite Rmult_1_r.
      apply presample_suffix_increase.
    Qed.

    Fixpoint iter_index {T : Type} (n : nat) (f : nat → T → T) (x : T) : T
      := match n with
         | 0 => x
         | S m => f m (iter_index m f x)
         end.
      
    Definition κ_min_aux (i : nat) : R := iter_index i (λ i m, Rmin (κ i) m) 2.
    
    Definition κ_min : R := κ_min_aux (length suf).

    Lemma κ_min_aux_gt_1 : ∀ (i : nat), i ≤ length suf → 1 < κ_min_aux i.
    Proof using μ_pos μ_gt_0 μ_lt_1.
      unfold κ_min_aux.
      elim=>[|i IH] i_le_suf /=; first lra.
      apply Rmin_glb_lt; first by apply κ_gt_1.
      apply IH.
      lia.
    Qed.

    Definition κ_min_gt_1 : 1 < κ_min := κ_min_aux_gt_1 (length suf) ltac:(reflexivity).

    Lemma κ_min_aux_is_min : ∀ (i j : nat), (j < i ≤ length suf)%nat → κ_min_aux i <= κ j.
    Proof.
      elim=>[|i IH] j i_g_len; first lia.
      unfold κ_min_aux.
      destruct (decide (i = j)) as [-> | i_not_j]; first apply Rmin_l.
      etrans; last apply IH; last lia.
      apply Rmin_r.
    Qed.

    Lemma κ_min_is_min : ∀ (i : nat), (i < length suf)%nat → κ_min <= κ i.
    Proof.
      move=>i i_lt_len.
      by apply κ_min_aux_is_min.
    Qed.
      
    Lemma presample_suffix_partial :
      ∀ (i : nat),
      (i < length suf)%nat →
      ψ l ∗
      ↯ ε ∗ 
      ((ψ (l ++ take (S i) suf) ∗
        ↯ (ε' (S i))
        ∨ ∃ (j : list A),
            ψ (l ++ j) ∗
            ↯ (κ_min * ε)
       ) -∗ Φ
      )
      ⊢ Φ.
    Proof using ε_pos μ_pos μ_gt_0 μ_lt_1 mass_μ_le_1 is_seriesC_μ presample_adv_comp.
      iIntros (i).
      iInduction (i) as [|i] "IH";
        iIntros (Si_lt_len) "(Hψ & Herr & Hnext)".
      - iApply (presample_suffix_increase' 0); first lia.
        rewrite app_nil_r ε'0.
        iFrame.
        iIntros "Hψ".
        iApply "Hnext".
        iDestruct "Hψ" as "[Hψ | (%j & Hψ & Herr)]"; first iFrame.
        iRight.
        iFrame.
        iApply (ec_weaken with "Herr").
        pose proof (κ_min_is_min 0 ltac:(lia)).
        pose proof κ_min_gt_1.
        nra.
      - iApply "IH"; first (iPureIntro; lia).
        iFrame.
        iIntros "[[Hψ Herr] | (%j & Hψ & Herr)]".
        + iApply (presample_suffix_increase' (S i)); first lia.
          iFrame.
          iIntros "[[Hψ Herr] | (%j & Hψ & Herr)]";
            iApply "Hnext";
            [iLeft | iRight];
            iFrame.
          iApply (ec_weaken with "Herr").
          pose proof (κ_min_is_min (S i) ltac:(lia)).
          pose proof κ_min_gt_1.
          nra.
        + iApply "Hnext".
          iRight.
          iFrame.
    Qed.

    Lemma presample_suffix_total :
      ψ l ∗
      ↯ ε ∗ 
      ((ψ (l ++ suf)
        ∨ ∃ (j : list A),
            ψ (l ++ j) ∗
            ↯ (κ_min * ε)
       ) -∗ Φ
      )
      ⊢ Φ.
    Proof using ε_pos μ_pos μ_gt_0 μ_lt_1 mass_μ_le_1 is_seriesC_μ presample_adv_comp.
      iIntros "(Hψ & Herr & Hnext)".
      destruct (decide (suf = [])) as [-> | suf_not_nil].
      {
        iApply "Hnext".
        rewrite app_nil_r.
        by iLeft.
      }
      assert (length suf ≠ 0)%nat.
      {
        move=>len_suf.
        by destruct suf.
      }
      iApply (presample_suffix_partial (length suf - 1)); first lia.
      iFrame.
      replace (S (length suf - 1)) with (length suf) by lia.
      rewrite firstn_all.
      iIntros "[[Hψ _] | (%j & Hψ & Herr)]";
        iApply "Hnext";
        [iLeft | iRight];
        iFrame.
    Qed.
        
  End FixedSuffix.

  Section SuffixFunction.

    Context (l : list A).
    Context {n : nat}.
    Context (suf : list A → list A).
    Context (L : nat).
    Context (suf_bounds :
              ∀ (j : list A), (length (suf (l ++ j)) <= L)%nat).
    Context (range : list A).
    Context (finite_range : ∀ (a : A) (j : list A), a ∈ suf (l ++ j) → a ∈ range).
    Context (μ_gt_0 : ∀ (a : A), a ∈ range → 0 < μ a).
    
    Fixpoint suffixes_of_length (k : nat) : list (list A) :=
      match k with
      | 0 => [[]]
      | S k0 =>
            h ← range ;
            t ← suffixes_of_length k0 ;
            [h::t]
    end.

    Lemma elem_of_bind :
      ∀ {T : Type} (h : T) (l1 : list (list T)),
      let l2 := (t ← l1 ;
                 [h::t]) in
      ∀ (x : T) (t : list T), x::t ∈ l2 ↔ x = h ∧ t ∈ l1.
    Proof.
      move=>T h.
      elim=>[|h1 t1 IH] /= x t /=.
      { split.
        - move=>contra.
          inversion contra.
        - move=>[_ contra].
          inversion contra.
      }
      split.
      - move=>elem.
        apply elem_of_cons in elem as [xt_eq_hh1 | xt_in_t1].
        + injection xt_eq_hh1 as -> ->.
          split; first done.
          constructor.
        + simpl in IH.
          apply IH in xt_in_t1 as [-> elem].
          split; first done.
          by constructor.
      - move=>[-> elem].
        apply elem_of_cons in elem as [-> | t_in_t1];
          first constructor.
        apply elem_of_cons.
        right.
        by apply IH.
    Qed.
    
    Lemma elem_of_cons_bind :
      ∀ {T : Type} (l1 : list T) (l2 : list (list T)),
      let l3 := (h ← l1 ;
                 t ← l2 ;
                 [h::t]) in
      ∀ (h : T) (t : list T), h::t ∈ l3 ↔ h ∈ l1 ∧ t ∈ l2.
    Proof.
      move=>T.
      elim=>[|h1 t1 IH] l2 l3 h t /=.
      { unfold l3. simpl.
        split.
        - move=>contra.
          inversion contra.
        - move=>[contra _].
          inversion contra.
      }
      unfold l3.
      simpl.
      split.
      - move=>elem.
        apply elem_of_app in elem as [elem | elem].
        + apply elem_of_bind in elem as [-> t_in_l2].
          split; last done.
          constructor.
        + apply IH in elem as [h_in_t1 t_in_t2].
          split; last done.
          by constructor.
      - move=>[h_in_h1t1 t_in_l2].
        apply elem_of_app.
        apply elem_of_cons in h_in_h1t1 as [-> | h_in_t1].
        + left.
          by apply elem_of_bind.
        + right.
          by apply IH.
    Qed.
      
    Lemma suffixes_of_length_range :
      ∀ (k : nat) (s : list A),
      length s = k →
      (∀ a, a ∈ s → a ∈ range) →
      s ∈ suffixes_of_length k.
    Proof.
      elim=>[|k IH] s s_len s_range.
      - destruct s; last discriminate.
        simpl.
        constructor.
      - destruct s as [| a t]; first discriminate.
        simpl.
        apply elem_of_cons_bind.
        simpl in s_len.
        split.
        + apply s_range. constructor.
        + apply IH; first lia.
          move=>b b_in_t.
          apply s_range.
          by constructor.
    Qed.

    Lemma suffixes_of_length_from_range :
      ∀ (len : nat) (s : list A),
      s ∈ suffixes_of_length len → (∀ (a : A), a ∈ s → a ∈ range).
    Proof.
      elim=>[|len IH] /= s s_elem a a_in_s.
      { apply elem_of_list_singleton in s_elem as ->.
        contradict a_in_s.
        apply not_elem_of_nil. }
      destruct s as [| h t].
      { contradict a_in_s.
        apply not_elem_of_nil. }
      apply elem_of_cons_bind in s_elem as [h_in_range t_of_len].
      inversion a_in_s as [|??? a_in_t]; subst; first done.
      apply (IH t t_of_len _ a_in_t).
    Qed.
    
    Fixpoint suffixes_up_to_length (k : nat) : list (list A) :=
      match k with
      | 0 => []
      | S k0 => suffixes_of_length k0 ++ suffixes_up_to_length k0
      end.

    Lemma suffixes_up_to_length_range :
      ∀ (k : nat) (s : list A),
      (length s < k)%nat →
      (∀ a, a ∈ s → a ∈ range) →
      s ∈ suffixes_up_to_length k.
    Proof.
      elim=>[|k IH] s s_len s_range /=; first lia.
      rewrite Nat.lt_succ_r Nat.le_lteq in s_len.
      apply elem_of_app.
      destruct s_len as [s_len_lt | s_len_eq].
      - right. by apply IH.
      - left. by apply suffixes_of_length_range.
    Qed.
   
    Definition possible_suffixes : list (list A) := suffixes_up_to_length (S L).
    
    Lemma suf_in_possible_suffixes :
      ∀ (j : list A), suf (l ++ j) ∈ possible_suffixes.
    Proof using finite_range suf_bounds.
      move=>j.
      specialize (suf_bounds j).
      apply suffixes_up_to_length_range; first lia.
      move=>a.
      apply finite_range.
    Qed.

    Lemma possible_suffixes_from_range :
      ∀ (s : list A), s ∈ possible_suffixes → (∀ (a : A), a ∈ s → a ∈ range).
    Proof.
      unfold possible_suffixes.
      generalize (S L) as len.
      elim=>[|len IH] /= s s_possible a a_in_s.
      { contradict s_possible. apply not_elem_of_nil. }
      apply elem_of_app in s_possible as [s_of_len | s_possible].
      { exact (suffixes_of_length_from_range _ _ s_of_len _ a_in_s). }
      { exact (IH s s_possible a a_in_s). }
    Qed.
    
    #[local]
    Definition ξ := foldr (λ s m, Rmin (κ_min s) m) 2 possible_suffixes.

    Lemma ξ_min :
      ∀ (s : list A), s ∈ possible_suffixes → ξ <= κ_min s.
    Proof.
      unfold ξ.
      move:possible_suffixes_from_range.
      generalize possible_suffixes.
      elim=>[|h t IH] from_range s elem; first inversion elem.
      apply elem_of_cons in elem as [-> | elem].
      - simpl.
        apply Rmin_l.
      - simpl.
        etransitivity; last apply IH.
        + apply Rmin_r.
        + move=>x x_in_t.
          apply from_range, elem_of_list_further, x_in_t.
        + assumption.
    Qed.

    Lemma ξ_gt_1 : 1 < ξ.
    Proof using μ_lt_1 μ_pos μ_gt_0.
      unfold ξ.
      move:possible_suffixes_from_range.
      generalize possible_suffixes.
      elim=>[|h t IH] from_range /=; first lra.
      apply Rmin_glb_lt; first apply κ_min_gt_1.
      - move=>a a_in_h.
        apply μ_gt_0, (from_range h); last done.
        constructor.
      - apply IH.
        move=>s s_in_t.
        apply from_range.
        by constructor.
    Qed.
      
    Lemma presample_function_increase :
      ∀ (ε : R) (j1 : list A),
      0 < ε →
      ψ (l ++ j1) ∗
      ↯ ε ∗ 
      ((ψ (l ++ j1 ++ suf (l ++ j1))
        ∨ ∃ (j2 : list A),
           ψ (l ++ j2) ∗
           ↯ (ξ * ε)
       ) -∗ Φ
      )
      ⊢ Φ.
    Proof using
      finite_range
      is_seriesC_μ
      presample_adv_comp
      suf_bounds
      μ_lt_1 μ_pos μ_gt_0 mass_μ_le_1.
      
      iIntros (ε j1 ε_pos) "(Hψ & Herr & Hnext)".
      iApply (presample_suffix_total _ (suf (l ++ j1)) with "[$Herr $Hψ Hnext]"); try done.
      { move=>a a_in_suf.
        apply μ_gt_0, (finite_range _ j1), a_in_suf.
      }
      rewrite -app_assoc.
      iIntros "[HΦ | (%j & Hψ & Herr)]";
        iApply "Hnext"; first iFrame.
      rewrite -app_assoc.
      iRight.
      iFrame.
      iApply (ec_weaken with "Herr").
      pose proof (ξ_min (suf (l ++ j1)) (suf_in_possible_suffixes j1)).
      pose proof ξ_gt_1.
      nra.
    Qed.

    Lemma presample_planner :
      ∀ (ε : R),
      0 < ε →
      ψ l ∗ ↯ ε ∗ 
      (∀ (j : list A), ψ (l ++ j ++ suf (l ++ j)) -∗ Φ)
      ⊢ Φ.
    Proof using
      finite_range
      is_seriesC_μ
      presample_adv_comp
      suf_bounds
      μ_lt_1 μ_pos μ_gt_0 mass_μ_le_1.
      
      rewrite -{1}(app_nil_r l).
      generalize (@nil A).
      iIntros (j1 ε ε_pos) "(Hψ & Herr & Hnext)".
      iRevert (j1) "Hψ Hnext".
      iApply (ec_ind_amp _ ξ _ ε_pos ξ_gt_1 with "[] Herr").
      iModIntro.
      clear ε ε_pos.
      iIntros (ε ε_pos) "#IH Herr %j1 Hψ Hnext".
      iApply (presample_function_increase _ _ ε_pos with "[$Hψ $Herr Hnext]");
        iIntros "[Hψ | (%j2 & Hψ & Herr)]"; first by iApply "Hnext".
      iApply ("IH" with "Herr Hψ Hnext").
    Qed.  

    Lemma dirac_A_singleton (a : A) :
      μ a = 1 → ∀ b, b = a ∨ μ b = 0.
    Proof using
      is_seriesC_μ
      μ_pos
      mass_μ_le_1
    .
      move=> μ_a_1 b.
      apply is_seriesC_unique in is_seriesC_μ as SeriesC_μ.
      pose proof (SeriesC_ge_elem μ a μ_pos (ex_intro _ _ is_seriesC_μ)) as μ_m_ge_μ_a.
      rewrite SeriesC_μ in μ_m_ge_μ_a.
      assert (μ_m = 1) as μ_m_1 by lra.
      rewrite (SeriesC_ext _ (λ x, (if bool_decide (x = a) then μ a else 0%R) + (if bool_decide (x = a) then 0%R else μ x))) in SeriesC_μ; last first.
      {
        move=>x.
        case_bool_decide; subst; lra.
      }
      move=>[:ex_remainder].
      rewrite SeriesC_plus in SeriesC_μ; last first.
      { abstract: ex_remainder.
        apply (ex_seriesC_le _ μ); last by eexists.
        move=>x.
        specialize (μ_pos x).
        case_bool_decide; lra.
      }
      { apply ex_seriesC_singleton. }
      rewrite SeriesC_singleton in SeriesC_μ.
      rewrite μ_a_1 in SeriesC_μ.
      assert (SeriesC
                (λ x : A,
                   if bool_decide (x = a) then 0 else μ x) =
              0) as remainder_is_0 by lra.
      unshelve epose proof (SeriesC_ge_elem  (λ x : A,
                        if bool_decide (x = a)
                        then 0
                        else μ x) b _ _) as μ_b_le.
      { move=>x /=.
        case_bool_decide; first reflexivity.
        specialize (μ_pos x). lra.
      }
      { assumption. }
      simpl in μ_b_le.
      case_bool_decide; first auto.
      rewrite remainder_is_0 in μ_b_le.
      specialize (μ_pos b).
      lra.
    Qed.
    
    Lemma support_singleton_presample_repeat (a : A) :
      μ a = 1 →
      ∀ (k : nat) (ε : R),
      (0 < ε)%R → 
      ψ l ∗ ↯ ε ∗
      (ψ (l ++ repeat a k) -∗ Φ)
      ⊢ Φ.
    Proof using
      is_seriesC_μ
      presample_adv_comp
      μ_pos
      mass_μ_le_1
    .

      iIntros (μ_a_1 k ε ε_pos) "(Hψ & Herr & Hnext)".
      iInduction k as [|k] "IH" forall (ε ε_pos).
      - rewrite app_nil_r.
        by iApply "Hnext".
      - iPoseProof (ec_split_le (ε / 2) with "Herr") as "[Herr1 Herr2]"; first lra.
        unshelve iApply ("IH" $! _ _ with "Hψ Herr1 [Hnext Herr2]").
        { lra. }
        iIntros "Hψ".
        iApply (presample_adv_comp _ (λ b, if bool_decide (b = a) then (ε / 2) else 1) (Rmax (ε / 2) 1) with "[$Herr2 $Hψ Hnext]").
        { lra. }
        { move=>x/=. case_bool_decide; split; first [lra | apply Rmax_l | apply Rmax_r]. }
        { rewrite (SeriesC_ext _
                     (λ b, (if bool_decide (b = a)
                            then ε / 2
                            else 0%R))); last first.
          { move=>b.
            case_bool_decide; subst.
            - rewrite μ_a_1. lra.
            - assert (μ b = 0) as ->.
              { destruct (dirac_A_singleton a μ_a_1 b); [contradiction | done]. }
              lra.
          } 
          rewrite SeriesC_singleton.
          lra.
        }
        iIntros (x) "Herr Htape".
        iApply "Hnext".
        case_bool_decide; subst.
        + rewrite -app_assoc -repeat_cons //.
        + iDestruct (ec_contradict with "Herr") as "[]".
          lra.
    Qed.

    Lemma support_singleton_presample (a : A) :
      μ a = 1 →
      ∀ (ε : R),
      (0 < ε)%R → 
      ψ l ∗ ↯ ε ∗
      (∀ j, ψ (l ++ j ++ suf (l ++ j)) -∗ Φ)
      ⊢ Φ.
    Proof using
      is_seriesC_μ
      presample_adv_comp
      finite_range
      μ_pos μ_gt_0 mass_μ_le_1.

      iIntros (μ_a_1 ε ε_pos) "(Hψ & Herr & Hnext)".
      iApply (support_singleton_presample_repeat _ μ_a_1 (length (suf l)) _ ε_pos with "[$Hψ $Herr Hnext]").
      iIntros "Hψ".
      iApply ("Hnext" $! []).
      simpl.
      rewrite -{2}(app_nil_r l) -(@Forall_eq_repeat _ a (suf (l ++ []))) // Forall_forall.
      move=>b b_in_suf.
      apply finite_range in b_in_suf as b_in_range.
      apply μ_gt_0 in b_in_range.
      by destruct (dirac_A_singleton _ μ_a_1 b); last lra.
    Qed.
  
  End SuffixFunction.
  
End Planner.

Lemma abstract_planner
  `{!erisGS Σ} {A : Type} `{Countable A}
  (μ : A → R) (μ_m : R) (ψ : list A → iProp Σ) (Φ : iProp Σ)
  (l : list A) (suf : list A → list A)
  (L : nat) (range : list A) (ε : R):

  (∀ a : A, (0 <= μ a)%R) →
  (∀ a : A, a ∈ range → (0 < μ a)%R) →

  (μ_m <= 1)%R →
  is_seriesC μ μ_m%R →
  
  (∀ (ε : R) (D : A → R) 
     (L0 : R) (l : list A),
     (0 < ε)%R
     → (∀ a : A, (0 <= D a <= L0)%R)
     → SeriesC (λ a : A, (μ a * D a)%R) =
     ε
     → ψ l ∗ ↯ ε ∗
     (∀ a : A,
        ↯ (D a) -∗ ψ (l ++ [a]) -∗ Φ)
     ⊢ Φ) → 

  (∀ j : list A, length (suf (l ++ j)) <= L) →
  (∀ (a : A) (j : list A), a ∈ suf (l ++ j) → a ∈ range) →

  (0 < ε)%R  →

  ψ l ∗
  ↯ ε ∗
  (∀ j : list A, ψ (l ++ j ++ suf (l ++ j)) -∗  Φ)
  ⊢ Φ.
Proof.
  move=>μ_pos μ_gt_0 mass_μ_le_1 is_seriesC_μ *.
  assert (∀ a, μ a <= 1)%R as μ_le_1.
  {
    move=>a.
    pose proof (SeriesC_ge_elem μ a μ_pos (ex_intro _ _ is_seriesC_μ)).
    transitivity μ_m; last done.
    rewrite -(is_seriesC_unique _ _ is_seriesC_μ) //.
  }
  destruct (decide (∃ a, μ a = 1)) as [[a μ_a_1] | μ_strict].
  { iIntros "(Hψ & Herr & Hnext)".
    unshelve iApply (support_singleton_presample μ _ μ_m _ _ ψ _ _ l suf range _ _ a _ ε); try assumption.
    iFrame.
  }
  eapply presample_planner;
    try done.
  move=>a.
  destruct (μ_le_1 a); first done.
  contradict μ_strict.
  by exists a.
Qed.
