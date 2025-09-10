From clutch.eris Require Export eris.
From clutch.eris.lib.sampling Require Import distr_impl utils. 

Section GeometricMath.

  Definition geometric_prob (p q k : nat) :=  (p / (q + 1) * (1 - p / (q + 1))^k)%R.
  
  Lemma geometric_prob_pos (p q k : nat) : p ≤ S q → (0 <= geometric_prob p q k)%R.
  Proof.
    move=>p_le_Sq.
    apply le_INR in p_le_Sq.
    rewrite S_INR in p_le_Sq.
    unfold geometric_prob.
    pose proof (pos_INR p).
    pose proof (pos_INR q).
    apply Rmult_le_pos.
    { apply Rcomplements.Rdiv_le_0_compat; lra. }
    { apply pow_le.
      apply Rle_0_le_minus.
      rewrite -Rcomplements.Rdiv_le_1; lra.
    }
  Qed.

  Lemma geometric_prob_S (p q k : nat) : (geometric_prob p q (S k) = (1 - p / (q + 1)) * geometric_prob p q k)%R.
  Proof.
    unfold geometric_prob.
    simpl.
    lra.
  Qed.

  Lemma is_seriesC_geometric_prob (p q : nat) : 0 < p ≤ S q → is_seriesC (geometric_prob p q) 1%R.
  Proof.
    move=>[p_pos p_le_Sq].
    apply le_INR in p_le_Sq.
    rewrite S_INR in p_le_Sq.
    apply lt_INR in p_pos.
    simpl in p_pos.
    unfold geometric_prob.
    replace 1%R with (p / (q + 1) * ((q + 1) / p))%R at 1; last first.
    { rewrite !Rdiv_def Rmult_comm -Rmult_assoc (Rmult_assoc _ _ p) Rinv_l; last lra.
      rewrite Rmult_1_r Rinv_r; lra.
    }
    apply is_seriesC_scal_l.
    apply is_seriesC_is_series_nat.
    replace ((q + 1) / p)%R with (/ (1 - (1 - p / (q + 1))))%R; last first.
    { rewrite Rminus_def Ropp_plus_distr Ropp_involutive
              -Rplus_assoc -Rminus_def Rminus_diag Rplus_0_l Rinv_div //.
    }
    apply Series.is_series_geom.
    apply Rabs_def1.
    { apply Rcomplements.Rlt_minus_l.
      rewrite -{1}(Rplus_0_r 1).
      apply Rplus_le_lt_compat; first reflexivity.
      apply Rcomplements.Rdiv_lt_0_compat; lra.
    }
    { apply (Rlt_le_trans _ 0%R); first lra.
      apply Rle_0_le_minus.
      rewrite -Rcomplements.Rdiv_le_1; lra.
    }
  Qed.

  Program Definition geometric_distr (p q : nat) (p_bounds : 0 < p ≤ S q) : distr nat
    := MkDistr
         (geometric_prob p q)
         (λ k, geometric_prob_pos p q k (proj2 p_bounds))
         (ex_intro _ _ (is_seriesC_geometric_prob p q p_bounds))
         _ .
  Next Obligation.
    move=>p q p_bounds.
    rewrite (is_seriesC_unique _ _ (is_seriesC_geometric_prob p q p_bounds)) //.
  Qed.

End GeometricMath.

Class geometric_spec (geometric_prog geometric_alloc : val) :=
  GeometricSpec
    {
      twp_geometric_adv_comp `{!erisGS Σ} :
      ∀ (p q : nat),
        (0 < p)%nat →
        (p ≤ q + 1)%nat →
        ∀ (D : nat → R) (L : R) (ε : R),
        (∀ (n : nat), 0 <= D n <= L)%R →
        SeriesC (λ k, (geometric_prob p q k * D k)%R) = ε →
        ↯ ε -∗ WP geometric_prog #() #p #q [{ v, ∃ (k : nat), ⌜v = #k⌝ ∗ ↯ (D k) }];

      own_geometric_tape `{!erisGS Σ} (α : loc) (N M : nat) (v : list nat) : iProp Σ;

      twp_geometric_alloc `{!erisGS Σ} (p q : nat) :
      [[{ True }]]
        geometric_alloc #p #q
        [[{ (α : loc), RET #lbl:α; own_geometric_tape α p q [] }]];
      
      twp_geometric_tape `{!erisGS Σ} :
      ∀ (p q : nat) (α : loc) (n : nat) (ns : list nat) (Φ : val → iProp Σ),
        own_geometric_tape α p q (n::ns) -∗
        (own_geometric_tape α p q ns -∗ Φ #n) -∗
        WP geometric_prog #lbl:α #p #q [{ Φ }];
      
      twp_geometric_presample_adv_comp `{!erisGS Σ} :
      ∀ (p q : nat) (α : loc) (ns : list nat)
        (e : expr) 
        (D : nat → R) (L : R) (ε : R)
        (Φ : val → iProp Σ),
        (0 < p)%nat →
        (p ≤ q + 1)%nat →
        to_val e = None → 
        (∀ (n : nat), 0 <= D n <= L)%R →
        SeriesC (λ k, (geometric_prob p q k * D k)%R) = ε →
        own_geometric_tape α p q ns ∗
        ↯ ε ∗ 
        (∀ (i : nat), ↯ (D i) ∗ own_geometric_tape α p q (ns ++ [i]) -∗ WP e [{ Φ }])
        ⊢  WP e [{ Φ }]
    }.

Section GeometricInst.

  Context `{geospec : geometric_spec geo geoalloc}.
  
  Instance geometric_binomial_impl {p q : nat} {p_bounds : 0 < p ≤ S q} :
    distr_impl (dmap (LitV ∘ LitInt ∘ Z.of_nat) (geometric_distr p q p_bounds)).
  Proof using geospec.

    refine (MkDistrImpl _
              (λ: "α", geo "α" #p #q) (λ: <>, geoalloc #p #q)
              loc
              (λ _ _ Δ l, ∃ l', own_geometric_tape Δ p q l' ∗
                            ⌜l = fmap (λ (k : nat), #k) l'⌝)%I
              (λ _ _ Δ α, ⌜α = #lbl:Δ⌝)%I #() _ _ _ _).
    - iIntros (Σ erisGS0 D ε L ε_ge_0 D_bounds D_sum Φ) "Herr HΦ".
      set (D' (k : nat) := D #k).
      wp_pures.
      iPoseProof (twp_geometric_adv_comp p q (proj1 p_bounds) ltac:(lia) D' L _ _ with "Herr") as "HH".
      Unshelve.
      3:{ move=>k. apply D_bounds. }
      { rewrite (dmap_expected_value _ _ _ L) // in D_sum. }
      wp_apply tgl_wp_wand_r.
      iFrame.
      iIntros (?) "(%k & -> & Herr)".
      by iApply "HΦ".
    - iIntros (Σ erisGS0 Φ) "_ HΦ".
      wp_pures.
      wp_apply (twp_geometric_alloc with "[$]") as (α) "Hα".
      iApply "HΦ".
      by iFrame.
    - iIntros (Σ erisGS0 e ε Δ l D L Φ e_not_val ε_ge_0 D_bounds D_sum) "(Herr & (%l' & Htape & ->) & Hnext)".
      set (D' (k : nat) := D #k).
      wp_apply (twp_geometric_presample_adv_comp p q _ _ _ D' _ _ _ (proj1 p_bounds) ltac:(lia) e_not_val with "[$Herr $Htape Hnext]").
      { move=>k. apply D_bounds. }
      { rewrite (dmap_expected_value _ _ _ L) // in D_sum. }
      iIntros (k) "[Herr Htape]".
      wp_apply "Hnext".
      iFrame.
      rewrite fmap_app //.
    - iIntros (Σ erisGS0 α Δ l v Φ) "[(%l' & Htape & %Heq) ->] HΦ".
      destruct l' as [|v' l']; first discriminate.
      injection Heq as -> ->.
      wp_pures.
      wp_apply (twp_geometric_tape with "Htape") as "Htape".
      iApply "HΦ".
      iExists l'.
      by iFrame.
  Defined.

End GeometricInst.
