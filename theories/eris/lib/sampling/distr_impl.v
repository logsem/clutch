From clutch.eris Require Import eris distribution_adequacy.
From clutch.eris.lib.sampling Require Import abstract_planner utils.

Section DistributionImplem.

  Class distr_impl (μ : distr val) :=
    MkDistrImpl
      {
        sample : expr;
        
        alloc_tape : expr;
        
        AbsLoc : Type;
        
        own_tape : ∀ `{!erisGS Σ}, AbsLoc → list val → iProp Σ;
        
        is_abs_loc : ∀ `{!erisGS Σ}, AbsLoc →  val → iProp Σ;
        
        loc_unit : val;
        
        twp_distr_adv_comp :
        ∀ `{!erisGS Σ} (D : val → R) (ε : R) (L : R),
          (0 <= ε)%R →
          (∀ (v : val), 0 <= D v <= L)%R →
          ε = SeriesC (λ (v : val) , μ v * D v)%R →
          [[{
                ↯ (ε)
          }]]
            sample loc_unit
          [[{
                (v : val), RET v; 
                ↯ (D v)
          }]];
        
        twp_distr_alloc :
        ∀ `{!erisGS Σ},
         [[{ True }]]
          alloc_tape
         [[{ (Δ : AbsLoc) (α : val), RET α; is_abs_loc Δ α ∗ own_tape Δ [] }]];

        twp_distr_presample_adv_comp : 
        ∀ `{!erisGS Σ}
          (e : expr) (ε : R)
          (Δ : AbsLoc)
          (l : list val)
          (D : val → R)
          (L : R)
          (Φ : val → iProp Σ),
          to_val e = None →
          (0 <= ε)%R →
          (∀ (v : val), 0 <= D v <= L)%R →
          SeriesC (λ (v : val), μ v * D v)%R = ε →
          ↯ (ε) ∗
          own_tape Δ l ∗
          (∀ (v : val),
             own_tape Δ (l ++ [v]) ∗ ↯ (D v) -∗
             WP e [{ v, Φ v }]
          ) ⊢ WP e [{ v, Φ v }];

        twp_distr_load :
        ∀ `{!erisGS Σ}
          (α : val)
          (Δ : AbsLoc)
          (l : list val)
          (v : val),
          [[{ own_tape Δ (v::l) ∗ is_abs_loc Δ α }]]
            sample α
          [[{ RET v; own_tape Δ l }]]
      }.
  
  Lemma distr_presample_planner `{!erisGS Σ} `{!distr_impl μ} :
    ∀ (e : expr)
      (Δ : AbsLoc)
      (l : list val)
      (suf : list val → list val)
      (L : nat)
      (range : list val)
      (Φ : val → iProp Σ),
    to_val e = None →
    (∀ (v : val), v ∈ range → 0 < μ v)%R →
    (∀ j : list val, length (suf (l ++ j)) <= L) →
    (∀ (v : val) (j : list val), v ∈ suf (l ++ j) → v ∈ range) →
    own_tape Δ l ∗
    (∀ (j : list val),
       own_tape Δ (l ++ j ++ suf (l ++ j)) -∗
       WP e [{ v, Φ v }]
    ) ⊢ WP e [{ v, Φ v }].
  Proof.
    iIntros (e Δ l suf L range Φ
               e_not_val range_possible suf_bounds
               suf_fin)
      "(Htape & Hnext)".
    iApply twp_rand_err_pos; auto.
    iIntros (ε ε_pos) "Herr".
    set (ψ (l : list val) := (own_tape Δ l ∗ ∃ εf, (⌜0 < εf⌝%R ∗ ↯ εf))%I).

    wp_apply (abstract_planner μ ψ _ l suf L range (ε / 2)%R (pmf_pos μ) range_possible).
    { pose proof (SeriesC_correct μ (pmf_ex_seriesC μ)) as is_seriesC_SeriesC.
      unshelve epose proof (@pmf_sum_1 μ (sample loc_unit) _ Σ _ inhabitant) as sum_μ.
      { clear.
        iIntros (Σ erisGS0 ε D L ε_pos D_bounds D_sum Φ) "Herr Hnext".
        wp_apply (twp_distr_adv_comp with "Herr Hnext"); try done.
        rewrite -D_sum.
        apply SeriesC_ext=>v.
        lra.
      }
      { apply adequacy.ErisGpreS.
        { constructor.
          - apply invGS_wsat.
          - constructor.
            exact lcGS_inG.
        }
        { exact erisGS_heap. }
        { exact erisGS_tapes. }
        { constructor.
          exact ecGS_inG.
        }
      }
      unfold pmf_sum in sum_μ.
      rewrite sum_μ // in is_seriesC_SeriesC.
    }

    { clear -e_not_val.
      iIntros (ε D L l ε_pos D_bounds D_sum) "([Htape (%εf & %εf_gt_0 & Hfuel)] & Herr & Hnext)".
      iPoseProof (ec_split_le (εf / 2) with "Hfuel") as "[Hfuel1 Hfuel2]".
      { lra. }
      wp_apply (twp_distr_presample_adv_comp _ ε  _ _ D _ _ e_not_val
                  ltac:(lra) D_bounds D_sum
                 with "[$Herr $Htape Hfuel2 Hnext]") as (v) "[Htape Herr]".
      wp_apply ("Hnext" with "Herr").
      iFrame.
      iPureIntro.
      lra.
    }
    { assumption. }
    { assumption. }
    { lra. }
    iPoseProof (ec_split_le (ε / 2) with "Herr") as "[Herr1 Herr2]".
    { lra. }
    iFrame.
    iSplitR; first (iPureIntro; lra).
    iIntros (j) "[Htape _]".
    wp_apply "Hnext".
    iFrame.
  Qed.

End DistributionImplem.
