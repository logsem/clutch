From clutch.eris Require Import adequacy.
From clutch.eris Require Import total_weakestpre total_adequacy primitive_laws proofmode.

Print pgl.
Print tgl.

Lemma prob_ext {A : Type} `{Countable A} (μ : distr A) (φ ψ : A → bool) :
  (∀ (a : A), (μ a ≠ 0)%R → φ a = ψ a) →
  prob μ φ = prob μ ψ.
Proof.
  move=>ext.
  unfold prob.
  apply SeriesC_ext=>a.
  destruct (decide (μ a = 0)); subst;
    first by destruct (φ a), (ψ a).
  rewrite ext //.
Qed.
               
Section DistributionAdequacy.

  Set Default Proof Using "Type*".
  
  Context (μ : distr val).
  Context (μ_impl : expr).
  Hypothesis (twp_μ_adv_comp :
               ∀ `{erisGS Σ} (ε : R) (D : val → R) (L : R),
                (0 <= ε)%R →
                (∀ (v : val), 0 <= D v <= L)%R →
                SeriesC (λ (v : val), D v * μ v)%R = ε →
                [[{ ↯ ε }]] μ_impl [[{ v, RET v; ↯ (D v)}]]
             ).
  
  Definition pmf_sum : R := SeriesC μ.
  
  Lemma twp_eq :
    ∀ `{erisGS Σ} (v : val),
    [[{ ↯ (pmf_sum - μ v) }]] μ_impl [[{ RET v; True }]].
  Proof.
    iIntros (Σ erisGS0 v Φ) "Herr HΦ".
    iPoseProof ("HΦ" with "[$]") as "HΦ".
    set (D w := if bool_decide (v = w) then 0%R else 1%R).
    wp_apply (twp_μ_adv_comp (pmf_sum - μ v) D 1%R with "Herr").
    { apply Rle_0_le_minus, pmf_le_SeriesC. }
    { move=>w.
      unfold D.
      case_bool_decide;
        lra.
    }
    { rewrite (SeriesC_ext _ (λ (w : val), μ w - if bool_decide (w = v) then μ v else 0)%R); last first.
      { move=>w.
        unfold D.
        do 2 case_bool_decide;
        subst;
        try done;
        lra.
      }
      rewrite SeriesC_minus; try done; last first.
      { apply ex_seriesC_singleton. } 
      f_equal.
      apply SeriesC_singleton.
    }
    unfold D.
    iIntros (w) "Herr".
    case_bool_decide; subst; first done.
    iDestruct (ec_contradict with "Herr") as "[]". reflexivity.
  Qed.

  Lemma twp_neq :
    ∀ `{erisGS Σ} (v : val),
    [[{ ↯ (μ v) }]] μ_impl [[{ w, RET w; ⌜v ≠ w⌝ }]].
  Proof.
    iIntros (Σ erisGS0 v Φ) "Herr HΦ".
    set (D w := if bool_decide (v = w) then 1%R else 0%R).
    wp_apply (twp_μ_adv_comp (μ v) D 1%R with "Herr").
    { apply pmf_pos. }
    { move=>w.
      unfold D.
      case_bool_decide;
        lra.
    }
    { rewrite (SeriesC_ext _ (λ (w : val), if bool_decide (w = v) then μ v else 0)%R); last first.
      { move=>w.
        unfold D.
        do 2 case_bool_decide;
        subst;
        try done;
        lra.
      }
      apply SeriesC_singleton.
    }
    unfold D.
    iIntros (w) "Herr".
    case_bool_decide; subst.
    { iDestruct (ec_contradict with "Herr") as "[]". reflexivity. }
    by iApply "HΦ".
  Qed.

  Lemma μ_tgl : ∀ `{erisGpreS Σ} (σ : state) (v : val), tgl (lim_exec (μ_impl, σ)) (λ w, v = w) (pmf_sum - μ v).
  Proof.
    iIntros (Σ erisGpreS0 σ v).
    apply (@twp_tgl Σ erisGpreS0).
    { apply Rle_0_le_minus, pmf_le_SeriesC. }
    iIntros (erisGS0) "Herr".
    by iApply (twp_eq v with "Herr").
  Qed.    

  Lemma μ_pgl : ∀ `{erisGpreS Σ} (σ : state) (v : val), pgl (lim_exec (μ_impl, σ)) (λ w, v ≠ w) (μ v).
  Proof.
    iIntros (Σ erisGpreS0 σ v).
    apply (@twp_pgl_lim Σ erisGpreS0); first done.
    iIntros (erisGS0) "Herr".
    wp_apply (twp_neq with "Herr") as (w) "$".
  Qed.

  Lemma pmf_sum_1 :
    ∀ `{erisGpreS Σ} (σ : state) (v : val),
    pmf_sum = 1%R.
  Proof.
    move=>Σ erisGpreS0 σ v.
    specialize (μ_tgl σ v) as μ_tgl0.
    specialize (μ_pgl σ v) as μ_pgl0.
    unfold tgl in μ_tgl0.
    unfold pgl in μ_pgl0.
    rewrite Rminus_plus_distr Rminus_def Ropp_involutive Rplus_comm in μ_tgl0.
    rewrite (prob_ext _ _ (λ w, bool_decide (v = w))) in μ_pgl0; last first.
    { move=>w _. by do 2 case_bool_decide. }
    assert (μ v + (1 - pmf_sum) <= μ v)%R as bounds.
    {
      etrans; first apply μ_tgl0.
      erewrite prob_ext; first done.
      move=>w _ /=.
      by do 2 case_bool_decide.
    }
    rewrite Rplus_minus_assoc Rcomplements.Rle_minus_l in bounds.
    apply Rplus_le_reg_l in bounds.
    assert (pmf_sum <= 1)%R by apply pmf_SeriesC.
    lra.
  Qed.
  
  Lemma μ_impl_is_μ :
    ∀ `{erisGpreS Σ} (σ : state) (v : val),
    prob (lim_exec (μ_impl, σ)) (λ w, bool_decide (v = w)) = μ v.
  Proof.
    move=>Σ erisGpreS0 σ v.
    specialize (μ_tgl σ v) as μ_tgl0.
    specialize (μ_pgl σ v) as μ_pgl0.
    unfold tgl in μ_tgl0.
    unfold pgl in μ_pgl0.
    rewrite pmf_sum_1 // Rminus_plus_distr Rminus_def Ropp_involutive Rminus_diag Rplus_0_l in μ_tgl0.
    rewrite (prob_ext _ _ (λ w, bool_decide (v = w))) in μ_pgl0; last first.
    { move=>w _. by do 2 case_bool_decide. }
    apply Rle_le_eq.
    split; try done.
    erewrite prob_ext; first done.
    move=>w _ /=.
    by do 2 case_bool_decide.
  Qed.
  
End DistributionAdequacy.
