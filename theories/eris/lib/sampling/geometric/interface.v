From clutch.eris Require Export eris.
From clutch.eris.lib.sampling Require Import utils. 

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


Class geometric_spec (geometric_prog geometric_alloc : val) :=
  GeometricSpec
  {
    twp_geometric_adv_comp  `{!erisGS Σ} :
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
    ∀ (p q r : nat) (α : loc) (n : nat) (ns : list nat) (Φ : val → iProp Σ),
      own_geometric_tape α p q (n::ns) -∗
      (own_geometric_tape α p q ns -∗ Φ #n) -∗
      WP geometric_prog #lbl:α #p #q #r [{ Φ }];
 
    twp_geometric_presample_adv_comp `{!erisGS Σ} :
    ∀ (p q : nat) (α : loc) (l : list nat) (e : expr) (Φ : val → iProp Σ),
      0 < p →
      p ≤ (q + 1) →
      to_val e = None →
      ∀ (r : nat) (D : nat → R) (L : R) (ε : R),
      (∀ (n : nat), 0 <= D n <= L)%R →
      SeriesC (λ k, (geometric_prob p q k * D k)%R) = ε →
      ↯ ε ∗
      own_geometric_tape α p q l ∗
      (∀ (n : nat),
         ↯ (D n) -∗
         own_geometric_tape α p q (l ++ [n]) -∗ WP e [{ Φ }]) ⊢
      WP e [{ Φ }]
  }.
