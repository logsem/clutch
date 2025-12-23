From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real real_decr_trial neg_exp.
From clutch.eris.examples Require Import math.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Definition NegExpSymm : val :=
  λ: "e",
    let: "v" := NegExp #(Z.of_nat 0) in
    let: "b" := rand (#1) in
    ("b", "v").

Section Symmetric.
  Import Hierarchy.
  Context `{!erisGS Σ}.

  Definition NegExpSymm_ρ (_ : fin 2) (k : nat) (x : R) : R :=
    exp (-(x + k))%R / 2.

  Definition NegExpSymm_CreditV (F : fin 2 → nat → R → R)  :=
    (SeriesC (fun (b : fin 2) => SeriesC (fun (k : nat) => RInt (fun x => NegExpSymm_ρ b k x * F b k x) 0 1))).


  Lemma wp_NegExp_sym E (F : fin 2 → nat → R → R) {M}
      (Hnn : ∀ c a b, 0 <= b <= 1 → 0 <= F c a b <= M) (HP : ∀ x x1, PCts (F x x1) 0 1)  :
    ⊢ ↯ (NegExpSymm_CreditV F) -∗
           WP NegExpSymm #() @ E
      {{ p, ∃ (b : fin 2) (vz : nat) (vr : R) (ℓ : val),
            ⌜p = PairV #(fin_to_nat b) (PairV #(Z.of_nat vz) ℓ)⌝ ∗
            lazy_real ℓ vr ∗ ⌜0 <= vr < 1 ⌝ ∗
            ↯(F b vz vr)}}.
  Proof.
    iIntros "Hε".
    rewrite /NegExpSymm.
    wp_pures.
    wp_bind (NegExp _).
    iApply (pgl_wp_mono).
    2: {
      iApply ((@wp_NegExp_gen _ _ E (fun n r => (F (0)%fin n r + F (1)%fin n r) / 2) M) with "[Hε]").
      { intros ???.
        split.
        { apply Rcomplements.Rdiv_le_0_compat; try lra.
          apply Rplus_le_le_0_compat.
          { apply Hnn. lra. }
          { apply Hnn. lra. }
        }
        { suffices  ? :  (F 0%fin a b + F 1%fin a b) <= M + M by lra.
          apply Rplus_le_compat.
          { apply Hnn. lra. }
          { apply Hnn. lra. }
        }
      }
      { intros ?.
        replace (λ r : R, (F 0%fin x1 r + F 1%fin x1 r) / 2)
          with (λ r : R, F 0%fin x1 r * / 2 + F 1%fin x1 r * / 2).
        2: (funexti; lra).
        apply PCts_plus.
        { apply PCts_mult; [apply HP|].
          apply PCts_cts. intros ??. apply Continuity.continuous_const.
        }
        { apply PCts_mult; [apply HP|].
          apply PCts_cts. intros ??. apply Continuity.continuous_const.
        }
      }
      { iApply (ec_eq with "Hε").
        rewrite /NegExpSymm_CreditV.
        rewrite SeriesC_fin2.
        rewrite -SeriesC_plus.
        2: {
          rewrite /NegExpSymm_ρ.
          eapply (ex_seriesC_le _ (λ k : nat, (RInt (λ x : R, exp (- (x + k)) / 2) 0 1) * M)).
          { intros ?.
            split.
            { apply RInt_ge_0; try lra.
              { apply ex_RInt_mult.
                { rewrite /NegExpSymm_ρ//=.
                  apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
                  intros ??.
                  apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
                  by auto_derive.
                }
                { apply PCts_RInt, HP. }
              }
              { intros ??.
                apply Rmult_le_pos.
                {  apply Rcomplements.Rdiv_le_0_compat; try lra.
                   apply Rexp_nn.
                }
                { apply Hnn; lra. }
              }
            }
            { rewrite RInt_Rmult'.
              2: {
                apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
                intros ??.
                apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
                by auto_derive.
              }
              apply RInt_le; try lra.
              { apply ex_RInt_mult.
                { rewrite /NegExpSymm_ρ//=.
                  apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
                  intros ??.
                  apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
                  by auto_derive.
                }
                { apply PCts_RInt, HP. }
              }
              { apply ex_RInt_mult.
                { rewrite /NegExpSymm_ρ//=.
                  apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
                  intros ??.
                  apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
                  by auto_derive.
                }
                { apply ex_RInt_const. }
              }
              { intros ??.
                apply Rmult_le_compat_l; [|apply Hnn; lra].
                apply Rcomplements.Rdiv_le_0_compat; try lra.
                apply Rexp_nn.
              }
            }
          }
          { apply ex_seriesC_scal_r.
            apply (ex_seriesC_RInt (fun n => exp (-n) * / 2)); try lra.
            { intros ???.
              apply Rcomplements.Rdiv_le_0_compat; try lra.
              apply Rexp_nn.
            }
            { apply ex_seriesC_scal_r.
              apply ex_exp_geo_series. }
            { intros ???.
              rewrite Rabs_right.
              2: { apply Rle_ge.
                   apply Rcomplements.Rdiv_le_0_compat; try lra.
                   apply Rexp_nn.
              }
              { rewrite Rdiv_def.
                apply Rmult_le_compat_r; try lra.
                apply exp_mono.
                apply Ropp_le_contravar.
                have ? := pos_INR n. lra.
              }
            }
            { intros ?.
              apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
              intros ??.
              apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
              by auto_derive.
            }
          }
        }
        2: {
          rewrite /NegExpSymm_ρ.
          eapply (ex_seriesC_le _ (λ k : nat, (RInt (λ x : R, exp (- (x + k)) / 2) 0 1) * M)).
          { intros ?.
            split.
            { apply RInt_ge_0; try lra.
              { apply ex_RInt_mult.
                { rewrite /NegExpSymm_ρ//=.
                  apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
                  intros ??.
                  apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
                  by auto_derive.
                }
                { apply PCts_RInt, HP. }
              }
              { intros ??.
                apply Rmult_le_pos.
                {  apply Rcomplements.Rdiv_le_0_compat; try lra.
                   apply Rexp_nn.
                }
                { apply Hnn; lra. }
              }
            }
            { rewrite RInt_Rmult'.
              2: {
                apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
                intros ??.
                apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
                by auto_derive.
              }
              apply RInt_le; try lra.
              { apply ex_RInt_mult.
                { rewrite /NegExpSymm_ρ//=.
                  apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
                  intros ??.
                  apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
                  by auto_derive.
                }
                { apply PCts_RInt, HP. }
              }
              { apply ex_RInt_mult.
                { rewrite /NegExpSymm_ρ//=.
                  apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
                  intros ??.
                  apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
                  by auto_derive.
                }
                { apply ex_RInt_const. }
              }
              { intros ??.
                apply Rmult_le_compat_l; [|apply Hnn; lra].
                apply Rcomplements.Rdiv_le_0_compat; try lra.
                apply Rexp_nn.
              }
            }
          }
          { apply ex_seriesC_scal_r.
            apply (ex_seriesC_RInt (fun n => exp (-n) * / 2)); try lra.
            { intros ???.
              apply Rcomplements.Rdiv_le_0_compat; try lra.
              apply Rexp_nn.
            }
            { apply ex_seriesC_scal_r.
              apply ex_exp_geo_series. }
            { intros ???.
              rewrite Rabs_right.
              2: { apply Rle_ge.
                   apply Rcomplements.Rdiv_le_0_compat; try lra.
                   apply Rexp_nn.
              }
              { rewrite Rdiv_def.
                apply Rmult_le_compat_r; try lra.
                apply exp_mono.
                apply Ropp_le_contravar.
                have ? := pos_INR n. lra.
              }
            }
            { intros ?.
              apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
              intros ??.
              apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
              by auto_derive.
            }
          }
        }
        rewrite /NegExp_CreditV.
        apply SeriesC_ext.
        intros n.
        rewrite RInt_add.
        2: {
          apply ex_RInt_mult.
          { rewrite /NegExpSymm_ρ//=.
            apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
            intros ??.
            apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
            by auto_derive.
          }
          { apply PCts_RInt, HP. }
        }
        2: {
          apply ex_RInt_mult.
          { rewrite /NegExpSymm_ρ//=.
            apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
            intros ??.
            apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
            by auto_derive.
          }
          { apply PCts_RInt, HP. }
        }
        apply RInt_ext.
        intros ??.
        rewrite /NegExpSymm_ρ//=.
        rewrite /NegExp_ρ/NegExp_ρ0//=.
        rewrite Iverson_True.
        2: { lia. }
        rewrite Iverson_True.
        2: { rewrite /Icc. lra. }
        rewrite Nat.sub_0_r.
        lra.
      }
    }
    simpl.
    iIntros (v) "[%k [%r [%l [-> [Hr [% Hec]]]]]]".
    wp_pures.
    wp_apply (wp_couple_rand_adv_comp _ _ _ _ (fun (s : fin 2) => F s k r) with "Hec").
    { intros n. apply Hnn. lra. }
    { rewrite SeriesC_fin2 //=. lra. }
    iIntros (b) "Hec".
    wp_pures.
    iModIntro.
    iExists b, k, r, l.
    iFrame.
    iPureIntro; done.
  Qed.



End Symmetric.
