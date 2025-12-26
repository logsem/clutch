From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real real_decr_trial neg_exp lazy_real_expr.
From clutch.eris.examples Require Import math.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Definition bzu_to_R : fin 2 → nat → R → R :=
  fun b z u => (-1) ^ b * (z + u).

Definition ToLazyReal : val :=
  λ: "e",
    let: "U" := R_ofUnif (Snd (Snd "e")) in
    let: "Z" := R_ofZ (Fst (Snd "e")) in
    let: "ZU" := R_plus "U" "Z" in
    if: (Fst "e" = #1) then R_neg "ZU" else "ZU".

Section ToReal.
  Import Hierarchy.
  Context `{!erisGS Σ}.

  Theorem wp_ToLazyReal E {ℓ : val} {vr vz} {b : fin 2} :
    ⊢ ⌜0 <= vr < 1 ⌝ -∗
      WP ToLazyReal (PairV (#(fin_to_nat b)) (PairV #(Z.of_nat vz) ℓ)) @ E
        {{ fun cont => IsApprox cont (bzu_to_R b vz vr) E (lazy_real ℓ vr) }}.
  Proof.
    iIntros "%".
    rewrite /ToLazyReal.
    wp_pures.
    wp_bind (R_ofUnif _).
    iApply pgl_wp_mono.
    2: { iApply (wp_R_ofUnif vr). }
    rewrite //=.
    iIntros (?) "Happrox".
    wp_pures.
    wp_bind (R_ofZ _).
    iApply (pgl_wp_mono_frame (IsApprox v vr E (lazy_real ℓ vr)) with "[] Happrox").
    2: { iApply wp_R_ofZ. }
    rewrite //=.
    iIntros (?) "[Hvr Hvz]".
    wp_pures.
    wp_bind (R_plus _ _).
    iApply pgl_wp_mono.
    2: { iApply wp_R_plus; iFrame. }
    rewrite //=.
    iIntros (?) "Hadd".
    wp_pures.
    iAssert (IsApprox v1 (vr + IZR vz) E (lazy_real ℓ vr))%I with "[Hadd]" as "Hadd'".
    { iDestruct "Hadd" as "#Hadd'".
      iModIntro.
      iIntros (prec) "HLR".
      iSpecialize ("Hadd'" $! prec with "[HLR]"); iFrame.
      iApply pgl_wp_mono.
      2: iApply "Hadd'".
      rewrite //=.
      iIntros (?) "[% [?[[??]?]]]".
      iExists R2.
      iFrame.
    }
    rewrite -INR_IZR_INZ.
    destruct (bin_fin_to_nat_cases b).
    { rewrite /bzu_to_R.
      rewrite H0 //=.
      wp_pures.
      rewrite Rmult_1_l.
      iModIntro.
      rewrite Rplus_comm.
      iFrame.
    }
    { rewrite /bzu_to_R.
      rewrite H0 //=.
      wp_pures.
      iApply pgl_wp_mono.
      2: { iApply wp_R_neg; iFrame. }
      rewrite //=.
      replace (-1 * 1 * (vz + vr)) with (- (vr + vz)) by lra.
      iIntros (?) "?".
      iFrame.
    }
  Qed.

End ToReal.


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

  Definition NegExpSymm_Closed : R → R := fun x => exp (- Rabs x)%R / 2.

  Definition NegExpSymm_Closed_CreditV (F : R → R) : R :=
    RInt_gen (fun x => NegExpSymm_Closed x * F x) (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty).

  Lemma NegExpSymm_CreditV_eq {M} {F : R → R} (HF : IPCts F) (HBound : ∀ x, 0 <= F x <= M) :
    NegExpSymm_Closed_CreditV F = NegExpSymm_CreditV (fun b n x => F (bzu_to_R b n x)).
  Proof.
    rewrite /NegExpSymm_Closed_CreditV.

    have Lem1 : ex_RInt_gen (λ x : R, exp (- Rabs x) / 2 * F x) (Rbar_locally Rbar.m_infty) (at_point 0).
    { replace (λ x : R, exp (- Rabs x) / 2 * F x) with (λ x : R, exp (- Rabs (- (- x))) / 2 * F (- (- x))).
      2: { funexti. repeat f_equal; OK. }
      apply (@ex_RInt_gen_neg_change_of_var_rev (λ x : R, exp (- Rabs (- x)) / 2 * F (- x))).
      { intros ??.
        apply ex_RInt_mult.
        2: {
          apply ex_RInt_neg; OK.
          apply PCts_RInt.
          apply IPCts_PCts.
          done.
        }
        apply (@ex_RInt_ext _ (λ y : R, exp (- y) / 2)).
        { rewrite Rmin_left; OK.  rewrite Rmax_right; OK.
          intros ??.
          repeat f_equal.
          rewrite Rabs_left; OK.
        }
        apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      replace (λ x : R, exp (- Rabs (- x)) / 2 * F (- x)) with (λ x : R, exp (- Rabs x) / 2 * F (- x)).
      2: { funexti; do 3 f_equal; OK. rewrite Rabs_Ropp. done. }
      eapply (@ex_RInt_gen_Ici_compare_IPCts _ (λ x : R, exp ( - x) * (/ 2 * M))).
      { apply IPCts_mult.
        2: {
          apply IPCts_cts. intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        { apply IPCts_cts.
          intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
      }
      { apply IPCts_mult.
        { apply IPCts_cts. intros ?. apply Laplace_continuous. }
        by apply IPCts_opp.
      }
      { intros ?.
        split.
        { apply Rmult_le_pos; [|apply HBound].
          apply Rcomplements.Rdiv_le_0_compat; OK.
          apply Rexp_nn.
        }
        { rewrite Rdiv_def.
          rewrite Rmult_assoc.
          apply Rmult_le_compat.
          { apply Rexp_nn. }
          { apply Rmult_le_pos; OK. apply HBound. }
          { apply exp_mono.
            apply Ropp_le_contravar.
            apply RRle_abs.
          }
          { apply Rmult_le_compat; OK; apply HBound. }
        }
      }
      { apply ex_RInt_gen_scal_r.
        replace (λ x : R, exp (- x)) with (λ x : R, 1 * exp (- x)) by (funexti; OK).
        apply ex_RInt_gen_exp.
      }
    }

    have Lem2 : ex_RInt_gen (λ x : R, exp (- Rabs x) / 2 * F x) (at_point 0) (Rbar_locally Rbar.p_infty).
    { eapply (@ex_RInt_gen_Ici_compare_IPCts _ (λ x : R, exp (- x) * (/ 2 * M))).
      { apply IPCts_mult.
        2: {
          apply IPCts_cts. intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        { apply IPCts_cts.
          intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
      }
      { apply IPCts_mult; [|done].
        apply IPCts_cts.
        intros ?.
        apply Laplace_continuous.
      }
      { intros ?.
        split.
        { apply Rmult_le_pos; [|apply HBound].
          apply Rcomplements.Rdiv_le_0_compat; OK.
          apply Rexp_nn.
        }
        { rewrite Rdiv_def.
          rewrite Rmult_assoc.
          apply Rmult_le_compat.
          { apply Rexp_nn. }
          { apply Rmult_le_pos; OK. apply HBound. }
          { apply exp_mono.
            apply Ropp_le_contravar.
            apply RRle_abs.
          }
          { apply Rmult_le_compat; OK; apply HBound. }
        }
      }
      { apply ex_RInt_gen_scal_r.
        replace (λ x : R, exp (- x)) with (λ x : R, 1 * exp (- x)) by (funexti; OK).
        apply ex_RInt_gen_exp.
      }
    }

    rewrite -(@RInt_gen_Chasles R_CompleteNormedModule (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty)
               _ _ (λ x : R, NegExpSymm_Closed x * F x) 0).
    2: { rewrite /NegExpSymm_Closed. apply Lem1.  }
    2: { rewrite /NegExpSymm_Closed. apply Lem2. }
    rewrite /plus//=.
    rewrite /NegExpSymm_CreditV.
    rewrite SeriesC_fin2.
    rewrite Rplus_comm.
    replace (λ k : nat, RInt (λ x : R, NegExpSymm_ρ 0 k x * F (bzu_to_R 0 k x)) 0 1)
      with  (λ k : nat, RInt (λ x : R, / 2 * exp (- Rabs (x+k)) * F (k + x)) 0 1).
    2: {
      funext.
      intros k.
      apply RInt_ext.
      rewrite Rmin_left; try lra.
      rewrite Rmax_right; try lra.
      intros ??.
      rewrite /bzu_to_R//= Rmult_1_l.
      f_equal.
      rewrite /NegExpSymm_ρ.
      rewrite Rabs_right; first lra.
      apply Rle_ge.
      have ? := pos_INR k.
      lra.
    }
    replace (λ k : nat, RInt (λ x : R, NegExpSymm_ρ 1 k x * F (bzu_to_R 1 k x)) 0 1)
      with  (λ k : nat, RInt (λ x : R, / 2 * exp (- Rabs (- (x+k))) * F (- (k + x))) 0 1).
    2: {
      funext.
      intros k.
      apply RInt_ext.
      rewrite Rmin_left; try lra.
      rewrite Rmax_right; try lra.
      intros ??.
      rewrite /bzu_to_R//=.
      replace (-1 * 1 * (k + x)) with (- (k + x)) by lra.
      f_equal.
      rewrite /NegExpSymm_ρ//=.
      have ? := pos_INR k.
      rewrite Rabs_left; last lra.
      rewrite Ropp_involutive.
      lra.
    }

    rewrite (@RInt_sep (λ x : R, exp (- Rabs x) / 2 * F x) (fun n => exp (- n) * (/ 2 * M))); first last.
    { intros b.
      apply ex_RInt_mult; [|by apply IPCts_RInt].
      apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
      intros ??.
      apply Laplace_continuous.
    }
    { intros ???.
      split.
      { apply Rmult_le_pos; [|apply HBound].
        apply Rcomplements.Rdiv_le_0_compat; OK.
        apply Rexp_nn.
      }
      { rewrite Rdiv_def Rmult_assoc.
        apply Rmult_le_compat.
        { apply Rexp_nn. }
        { apply Rmult_le_pos; OK.
          apply HBound. }
        { apply exp_mono.
          apply Ropp_le_contravar.
          etrans; last eapply RRle_abs.
          lra.
        }
        { apply Rmult_le_compat; OK; apply HBound. }
      }
    }
    { apply ex_seriesC_scal_r.
      apply ex_exp_geo_series.
      }
    { apply (@ex_RInt_gen_Ici_compare_IPCts _ (fun x => exp (- x) / 2 * M)).
      { apply IPCts_cts. intros ?.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      { apply IPCts_mult; [|done].
        apply IPCts_cts. intros ?.
        apply Laplace_continuous.
      }
      { intros ?.
        split.
        { apply Rmult_le_pos; [|apply HBound].
          apply Rcomplements.Rdiv_le_0_compat; OK.
          apply Rexp_nn.
        }
        { apply Rmult_le_compat.
          { apply Rcomplements.Rdiv_le_0_compat; OK. apply Rexp_nn. }
          { apply HBound. }
          { apply Rmult_le_compat_r; OK.
            apply exp_mono.
            apply Ropp_le_contravar.
            apply RRle_abs.
          }
          { apply HBound. }
        }
      }
      { apply ex_RInt_gen_scal_r.
        replace (λ x : R, exp (- x) / 2) with (λ x : R, /2 * exp (- x)) by (funexti; OK).
        apply ex_RInt_gen_exp.
      }
    }

    rewrite -(FubiniIntegralSeriesC_Strong (fun n => M * /2 *  exp (- n))); first last.
    { intros ?.
      apply ex_RInt_mult.
      { apply (ex_RInt_ext (λ y : R, exp (-(y + n)) / 2)).
        { rewrite Rmin_left; OK. rewrite Rmax_right; OK.
          intros ??.
          f_equal. f_equal. f_equal. rewrite Rabs_right;  OK.
          apply Rle_ge.
          apply Rplus_le_le_0_compat; try lra.
          apply pos_INR.
        }
        { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
          intros ??.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
      }
      { replace (λ y : R, F (y + n)) with (λ y : R, scal 1 (F (1 * y + n))).
        2: { funexti. rewrite /scal//=/mult//= Rmult_1_l. f_equal; lra.  }
        apply (ex_RInt_comp_lin F 1 n 0 1).
        by apply IPCts_RInt.
      }
    }
    { intros ???.
      rewrite Rabs_right.
      2: {
        apply Rle_ge.
        apply Rmult_le_pos.
        { apply Rcomplements.Rdiv_le_0_compat; OK. apply Rexp_nn. }
        { apply HBound. }
      }
      rewrite Rmult_comm.
      rewrite Rdiv_def.
      rewrite (Rmult_comm _ (/ 2)).
      rewrite Rmult_assoc.
      apply Rmult_le_compat.
      { apply HBound. }
      { apply Rmult_le_pos; OK. apply Rexp_nn. }
      { apply HBound. }
      { apply Rmult_le_compat; OK.
        { apply Rexp_nn. }
        apply exp_mono.
        apply Ropp_le_contravar.
        etrans; last eapply RRle_abs.
        lra.
      }
    }
    { apply ex_seriesC_scal_l.
      apply ex_exp_geo_series.
    }
    { intros ???.
      apply Rmult_le_pos.
      { apply Rcomplements.Rdiv_le_0_compat; OK. apply Rexp_nn. }
      { apply HBound. }
    }
    { lra. }

    rewrite -RInt_gen_neg_change_of_var; first last.
    { rewrite /NegExpSymm_Closed. done. }
    { intros ??.
      rewrite /NegExpSymm_Closed.
      apply (ex_RInt_ext (λ x : R, exp (- x) / 2 * F (- x))).
      2: {
        apply ex_RInt_mult.
        { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
          intros ??.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        { apply IPCts_RInt; by apply IPCts_opp. }
      }
      { rewrite Rmin_left; OK.
        rewrite Rmax_right; OK.
        intros ??.
        f_equal.
        f_equal.
        f_equal.
        f_equal.
        rewrite Rabs_left; OK.
      }
    }
    { intros ??.
      apply ex_RInt_mult.
      2: { apply IPCts_RInt; done. }
      rewrite /NegExpSymm_Closed.
      apply (ex_RInt_ext (λ x : R, exp (x) / 2)).
      2: {
        apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      f_equal.
      rewrite Rabs_left; OK.
      f_equal; OK.
    }

    rewrite (@RInt_sep _ (fun n => exp (- n) * (/ 2 * M))); first last.
    { intros ?.
      apply ex_RInt_mult.
      2: { apply IPCts_RInt. apply IPCts_opp. done. }
      rewrite /NegExpSymm_Closed.
      apply (ex_RInt_ext (λ x : R, exp (- (Rabs x)) / 2)).
      2: {
        apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros ??.
        apply Laplace_continuous.
      }
      intros ??.
      do 3 f_equal.
      rewrite Rabs_Ropp; OK.
    }
    { rewrite /NegExpSymm_Closed.
      intros ???.
      split.
      { apply Rmult_le_pos; [|apply HBound].
        apply Rcomplements.Rdiv_le_0_compat; OK.
        apply Rexp_nn.
      }
      { rewrite Rdiv_def Rmult_assoc.
        apply Rmult_le_compat.
        { apply Rexp_nn. }
        { apply Rmult_le_pos; OK.
          apply HBound. }
        {
          apply exp_mono.
          apply Ropp_le_contravar.
          rewrite Rabs_Ropp.
          etrans; last eapply RRle_abs.
          lra.
        }
        { apply Rmult_le_compat; OK; apply HBound. }
      }
    }
    { apply ex_seriesC_scal_r.
      apply ex_exp_geo_series.
      }
    { rewrite /NegExpSymm_Closed.
      apply (@ex_RInt_gen_Ici_compare_IPCts _ (fun x => exp (- x) / 2 * M)).
      { apply IPCts_cts. intros ?.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      { apply IPCts_mult.
        2: { apply IPCts_opp. done. }
        apply IPCts_cts. intros ?.
        replace (λ x0 : R, exp (- Rabs (- x0)) / 2) with (λ x0 : R, exp (- Rabs x0) / 2).
        { apply Laplace_continuous. }
        funexti.
        do 3 f_equal.
        by rewrite Rabs_Ropp.
      }
      { intros ?.
        split.
        { apply Rmult_le_pos; [|apply HBound].
          apply Rcomplements.Rdiv_le_0_compat; OK.
          apply Rexp_nn.
        }
        { apply Rmult_le_compat.
          { apply Rcomplements.Rdiv_le_0_compat; OK. apply Rexp_nn. }
          { apply HBound. }
          { apply Rmult_le_compat_r; OK.
            apply exp_mono.
            apply Ropp_le_contravar.
            rewrite Rabs_Ropp.
            apply RRle_abs.
          }
          { apply HBound. }
        }
      }
      { apply ex_RInt_gen_scal_r.
        replace (λ x : R, exp (- x) / 2) with (λ x : R, /2 * exp (- x)) by (funexti; OK).
        apply ex_RInt_gen_exp.
      }
    }

    rewrite -(FubiniIntegralSeriesC_Strong (fun n => M * /2 *  exp (- n))); first last.
    { rewrite /NegExpSymm_Closed.
      intros ?.
      apply ex_RInt_mult.
      { apply (ex_RInt_ext (λ y : R, exp (-(y + n)) / 2)).
        { rewrite Rmin_left; OK. rewrite Rmax_right; OK.
          intros ??.
          rewrite Rabs_Ropp.
          f_equal. f_equal. f_equal.
          rewrite Rabs_right;  OK.
          apply Rle_ge.
          apply Rplus_le_le_0_compat; try lra.
          apply pos_INR.
        }
        { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
          intros ??.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
      }
      { replace (λ y : R, F (- (y + n))) with (λ y : R, F ((-y) + -n)).
        2: { funexti. f_equal. lra.  }
        replace (λ y : R, F (- y + - n)) with (λ y : R, (-1) * ((-1) * F (- y + - n))) by (funexti; OK).
        apply ex_RInt_Rmult.
        replace (λ x : R, -1 * F (- x + - n)) with (λ x : R, scal (-1) (F ((-1) * x + - n))).
        2: { funexti. rewrite /scal//=/mult//=. f_equal. f_equal. lra.  }
        apply (@ex_RInt_comp_lin ).
        rewrite Rmult_0_r Rplus_0_l.
        apply IPCts_RInt.
        done.
      }
    }
    { rewrite /NegExpSymm_Closed.
      intros ???.
      rewrite Rabs_right.
      2: {
        apply Rle_ge.
        apply Rmult_le_pos.
        { apply Rcomplements.Rdiv_le_0_compat; OK. apply Rexp_nn. }
        { apply HBound. }
      }
      rewrite Rmult_comm.
      rewrite Rdiv_def.
      rewrite (Rmult_comm _ (/ 2)).
      rewrite Rmult_assoc.
      apply Rmult_le_compat.
      { apply HBound. }
      { apply Rmult_le_pos; OK. apply Rexp_nn. }
      { apply HBound. }
      { apply Rmult_le_compat; OK.
        { apply Rexp_nn. }
        rewrite Rabs_Ropp.
        apply exp_mono.
        apply Ropp_le_contravar.
        etrans; last eapply RRle_abs.
        lra.
      }
    }
    { apply ex_seriesC_scal_l.
      apply ex_exp_geo_series.
    }
    { rewrite /NegExpSymm_Closed.
      intros ???.
      apply Rmult_le_pos.
      { apply Rcomplements.Rdiv_le_0_compat; OK. apply Rexp_nn. }
      { apply HBound. }
    }
    { lra. }

    f_equal.
    { f_equal. funexti.
      apply RInt_ext.
      intros ??.
      f_equal; [lra|f_equal; lra].
    }
    { f_equal. funexti.
      apply RInt_ext.
      intros ??.
      rewrite /NegExpSymm_Closed//=.
      f_equal; [lra|f_equal; lra].
    }
  Qed.


  Definition NegExpSymmC : val :=
    λ: "_",
      let: "sample_bzu" := NegExpSymm #() in
      ToLazyReal "sample_bzu".

  Lemma wp_NegExp_Closed_sym E (F : R → R) {M} (Hnn : ∀ c, 0 <= F c <= M) (HP : IPCts F) :
    ⊢ ↯ (NegExpSymm_Closed_CreditV F) -∗
           WP NegExpSymmC #() @ E
      {{ cont, ∃ I r, I ∗ IsApprox cont r E I ∗ ↯(F r) }}.
  Proof.
    iIntros "Hε".
    rewrite /NegExpSymmC.
    wp_pures.
    wp_bind (NegExpSymm _).
    iApply pgl_wp_mono.
    2: {
      iApply (@wp_NegExp_sym E (fun b z r => F (bzu_to_R b z r)) M).
      { intros ????. apply Hnn. }
      { intros ??.
        rewrite /bzu_to_R.
        destruct (bin_fin_to_nat_cases x).
        { rewrite H //=.
          replace (λ r : R, F (1 * (x1 + r))) with (λ r : R, F (x1 + r)).
          2:{ funexti; f_equal; OK. }
          eapply (PCts_shift F (λ r : R, F (x1 + r)) x1 (1 + x1) _ _ (- x1)); OK.
          2: { by apply IPCts_PCts. }
          intros ?.
          rewrite /Ioo//=.
          rewrite Rmin_left; OK.
          rewrite Rmax_right; OK.
          intros ?.
          f_equal; OK.
        }
        { rewrite H //=.
          replace (λ r : R, F (-1 * 1 * (x1 + r))) with (λ r : R, F (((- x1) + - r))).
          2 : { funexti; f_equal; OK. }
          eapply (PCts_shift (fun r => F (-r)) (λ r : R, F (- x1 + - r)) x1 (1 + x1) _ _ (-x1)); OK.
          2: {
            apply IPCts_PCts.
            by apply IPCts_opp.
          }
          intros ??.
          f_equal; OK.
        }
      }
      rewrite (NegExpSymm_CreditV_eq HP Hnn).
      iFrame.
    }
    rewrite //=.
    iIntros (v) "[%b [%z [%r [%l [-> [Hr [% Hec]]]]]]]".
    wp_pures.
    wp_bind (ToLazyReal _).
    iApply (pgl_wp_mono_frame (lazy_real l r ∗ ↯ (F (bzu_to_R b z r))) with "[] [Hr Hec]").
    3: { iFrame. }
    2: { iApply (@wp_ToLazyReal _ _ E _ r); iPureIntro. done. }
    rewrite //=.
    iIntros (?) "[[Hr He] Happrox]".
    iExists (lazy_real l r), (bzu_to_R b z r).
    iFrame.
  Qed.

End Symmetric.


Definition Laplace0 : val :=
  λ: "logε",
    let: "sample_R" := NegExpSymmC #() in
    R_mulPow "sample_R" "logε" .

Section Laplace0.
  Import Hierarchy.
  Context `{!erisGS Σ}.

  Definition Laplace0_μ (ε : R) : R → R :=
    fun x => ε * (exp (- Rabs (ε * x)) / 2).

  (* Credits required by the API *)
  Definition Laplace0_CreditV (ε : R) (F : R → R) : R :=
    RInt_gen (fun x => Laplace0_μ ε x * F x) (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty).

  Lemma Laplace_CreditV_Scale {M} (ε : R) (F : R → R) (Hnn : ∀ r, 0 <= F r <= M) (HP : IPCts F) (He : 0 < ε) :
    Laplace0_CreditV ε F = NegExpSymm_Closed_CreditV (λ r : R, F (r / ε)).
  Proof.
    rewrite /Laplace0_CreditV.
    rewrite /NegExpSymm_Closed_CreditV.

    rewrite -(@RInt_gen_Chasles R_CompleteNormedModule (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty)
           _ _ (λ x : R, Laplace0_μ ε x * F x) 0).
    2: {
      rewrite /Laplace0_μ.
      replace (λ x : R, ε * (exp (- Rabs (ε * x)) / 2) * F x)
         with (λ x : R, ε * (exp (- Rabs (- (ε * (- x)))) / 2) * F (- (- x))).
      2: {
        funexti.
        do 3 f_equal; OK.
        do 3 f_equal.
        lra.
      }
      apply (@ex_RInt_gen_neg_change_of_var_rev (λ x : R, ε * (exp (- Rabs (- (ε * x))) / 2) * F (- x))).
      { intros ??.
        apply ex_RInt_mult.
        2: {
          apply ex_RInt_neg; OK.
          apply PCts_RInt.
          apply IPCts_PCts.
          done.
        }
        apply ex_RInt_Rmult.
        apply (@ex_RInt_ext _ (λ y : R, exp (- (ε * y)) / 2)).
        { rewrite Rmin_left; OK.  rewrite Rmax_right; OK.
          intros ??.
          repeat f_equal.
          rewrite Rabs_Ropp.
          rewrite Rabs_right; OK.
          apply Rle_ge.
          apply Rmult_le_pos; OK.
        }
        apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      replace (λ x : R, ε * (exp (- Rabs (- (ε * x))) / 2) * F (- x))
        with (λ x : R, ε * ((exp (- Rabs ((ε * x))) / 2) * F (- x))).
      2: {
        funexti.
        rewrite Rmult_assoc.
        f_equal.
        f_equal.
        f_equal.
        f_equal.
        f_equal.
        by rewrite Rabs_Ropp.
      }
      apply @ex_RInt_gen_scal_l.
      eapply (@ex_RInt_gen_Ici_compare_IPCts _ (λ x : R, exp ( - (ε * x)) * (/ 2 * M))).
      { apply IPCts_mult.
        2: {
          apply IPCts_cts. intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        { apply IPCts_cts.
          intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
      }
      { apply IPCts_mult.
        2: by apply IPCts_opp.
        replace (λ x : R, exp (- Rabs (ε * x)) / 2)
           with (λ x : R, exp (- Rabs (x / (/ ε))) / 2).
        2: { funexti; do 4 f_equal. rewrite Rdiv_def Rinv_inv. lra. }
        apply (@IPCts_scale (λ x : R, exp (- Rabs (x)) / 2)).
        { by apply Rinv_0_lt_compat. }
        apply IPCts_cts. intros ?. apply Laplace_continuous.
      }
      { intros ?.
        split.
        { apply Rmult_le_pos; [|apply Hnn].
          apply Rcomplements.Rdiv_le_0_compat; OK.
          apply Rexp_nn.
        }
        { rewrite Rdiv_def.
          rewrite Rmult_assoc.
          apply Rmult_le_compat.
          { apply Rexp_nn. }
          { apply Rmult_le_pos; OK. apply Hnn. }
          { apply exp_mono.
            apply Ropp_le_contravar.
            apply RRle_abs.
          }
          { apply Rmult_le_compat; OK; apply Hnn. }
        }
      }
      { apply ex_RInt_gen_scal_r.
        apply (@ex_RInt_gen_scal_change_of_var (λ x : R, exp (- (x)))); OK.
        { intros ??.
          apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
          intros ??.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        replace (λ x : R, exp (- x)) with (λ x : R, 1 * exp (- x)) by (funexti; OK).
        apply ex_RInt_gen_exp.
      }
    }
    2: {
      rewrite /Laplace0_μ.
      eapply (@ex_RInt_gen_Ici_compare_IPCts _ (λ x : R, ε * exp (- (ε * x)) * (/ 2 * M))).
      { apply IPCts_mult.
        2: {
          apply IPCts_cts. intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        { apply IPCts_cts.
          intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
      }
      { apply IPCts_mult.
        { apply IPCts_mult.
          { apply IPCts_cts.
            intros ?.
            apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
            by auto_derive.
          }
          replace (λ x : R, exp (- Rabs (ε * x)) / 2) with (λ x : R, exp (- Rabs (x / (/ ε))) / 2).
          2: {
            funexti.
            do 4 f_equal.
            rewrite Rdiv_def.
            rewrite Rinv_inv.
            lra.
          }
          apply (@IPCts_scale (λ x : R, exp (- Rabs (x)) / 2)).
          { by apply Rinv_0_lt_compat. }
          apply IPCts_cts.
          intros ?.
          apply Laplace_continuous.
        }
        done.
      }
      { intros ?.
        split.
        { apply Rmult_le_pos; [|apply Hnn ].
          apply Rmult_le_pos; OK.
          apply Rcomplements.Rdiv_le_0_compat; OK.
          apply Rexp_nn.
        }
        { rewrite (Rmult_assoc ε).
          rewrite (Rmult_assoc ε).
          apply Rmult_le_compat; OK.
          { apply Rmult_le_pos.
            { apply Rcomplements.Rdiv_le_0_compat; OK.
              apply Rexp_nn.
            }
            { apply Hnn. }
          }
          rewrite Rdiv_def.
          rewrite Rmult_assoc.
          apply Rmult_le_compat.
          { apply Rexp_nn. }
          { apply Rmult_le_pos; OK. apply Hnn. }
          { apply exp_mono.
            apply Ropp_le_contravar.
            apply RRle_abs.
          }
          { apply Rmult_le_compat; OK; apply Hnn. }
        }
      }
      { replace (λ x : R, ε * exp (- (ε * x)) * (/ 2 * M))
          with (λ x : R, ε * (/2 * M * exp (- (ε * x)))) by (funexti; lra).
        apply (@ex_RInt_gen_scal_change_of_var (λ x : R, ε * (/ 2 * M * exp (- (x))))); OK.
        { intros ??.
          apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
          intros ??.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        apply ex_RInt_gen_scal_l.
        apply ex_RInt_gen_exp.
      }
    }

    rewrite -(@RInt_gen_Chasles R_CompleteNormedModule (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty)
           _ _ (λ x : R, NegExpSymm_Closed x * F (x / ε)) 0).
    2: {
      rewrite /NegExpSymm_Closed.
      replace (λ x : R, exp (- Rabs x) / 2 * F (x / ε)) with (λ x : R, exp (- Rabs (- (- x))) / 2 * F (- ((- x) / ε))).
      2: { funexti. repeat f_equal; OK. }
      apply (@ex_RInt_gen_neg_change_of_var_rev (λ x : R, exp (- Rabs (- x)) / 2 * F (- (x / ε)))).
      { intros ??.
        apply ex_RInt_mult.
        2: {
          apply PCts_RInt.
          apply IPCts_PCts.
          replace (λ y : R, F (- (y / ε))) with (λ y : R, F ((- y) / ε)).
          2: { funexti; repeat f_equal. OK. }
          apply (@IPCts_opp (λ y : R, F (y / ε))).
          apply IPCts_scale; OK.
        }
        apply (@ex_RInt_ext _ (λ y : R, exp (- y) / 2)).
        { rewrite Rmin_left; OK.  rewrite Rmax_right; OK.
          intros ??.
          repeat f_equal.
          rewrite Rabs_left; OK.
        }
        apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      replace (λ x : R, exp (- Rabs (- x)) / 2 * F (- (x / ε))) with (λ x : R, exp (- Rabs x) / 2 * F (- (x / ε))).
      2: { funexti; do 3 f_equal; OK. rewrite Rabs_Ropp. done. }
      eapply (@ex_RInt_gen_Ici_compare_IPCts _ (λ x : R, exp ( - x) * (/ 2 * M))).
      { apply IPCts_mult.
        2: {
          apply IPCts_cts. intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        { apply IPCts_cts.
          intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
      }
      { apply IPCts_mult.
        { apply IPCts_cts. intros ?. apply Laplace_continuous. }
        replace (λ y : R, F (- (y / ε))) with (λ y : R, F ((- y) / ε)).
        2: { funexti; repeat f_equal. OK. }
        apply (@IPCts_opp (λ y : R, F (y / ε))).
        apply IPCts_scale; OK.
      }
      { intros ?.
        split.
        { apply Rmult_le_pos; [|apply Hnn].
          apply Rcomplements.Rdiv_le_0_compat; OK.
          apply Rexp_nn.
        }
        { rewrite Rdiv_def.
          rewrite Rmult_assoc.
          apply Rmult_le_compat.
          { apply Rexp_nn. }
          { apply Rmult_le_pos; OK. apply Hnn. }
          { apply exp_mono.
            apply Ropp_le_contravar.
            apply RRle_abs.
          }
          { apply Rmult_le_compat; OK; apply Hnn. }
        }
      }
      { apply ex_RInt_gen_scal_r.
        replace (λ x : R, exp (- x)) with (λ x : R, 1 * exp (- x)) by (funexti; OK).
        apply ex_RInt_gen_exp.
      }
    }
    2: {
      rewrite /NegExpSymm_Closed.
      eapply (@ex_RInt_gen_Ici_compare_IPCts _ (λ x : R, exp (- x) * (/ 2 * M))).
      { apply IPCts_mult.
        2: {
          apply IPCts_cts. intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        { apply IPCts_cts.
          intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
      }
      { apply IPCts_mult.
        { apply IPCts_cts.
          intros ?.
          apply Laplace_continuous.
        }
        by apply IPCts_scale.
      }
      { intros ?.
        split.
        { apply Rmult_le_pos; [|apply Hnn ].
          apply Rcomplements.Rdiv_le_0_compat; OK.
          apply Rexp_nn.
        }
        { rewrite Rdiv_def.
          rewrite Rmult_assoc.
          apply Rmult_le_compat.
          { apply Rexp_nn. }
          { apply Rmult_le_pos; OK. apply Hnn. }
          { apply exp_mono.
            apply Ropp_le_contravar.
            apply RRle_abs.
          }
          { apply Rmult_le_compat; OK; apply Hnn. }
        }
      }
      { apply ex_RInt_gen_scal_r.
        replace (λ x : R, exp (- x)) with (λ x : R, 1 * exp (- x)) by (funexti; OK).
        apply ex_RInt_gen_exp.
      }
    }

    have HF1 : ex_RInt_gen (λ x : R, exp (- Rabs (ε * x)) / 2 * F x) (at_point 0) (Rbar_locally Rbar.p_infty).
    { eapply (@ex_RInt_gen_Ici_compare_IPCts _ (λ x : R, exp (- (ε * x)) * (/ 2 * M))).
      { apply IPCts_mult.
        2: {
          apply IPCts_cts. intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        { apply IPCts_cts.
          intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
      }
      { apply IPCts_mult; [|done].
        replace (λ x : R, exp (- Rabs (ε * x)) / 2) with (λ x : R, exp (- Rabs (x / (/ ε))) / 2).
        2: {
          funexti.
          do 4 f_equal.
          rewrite Rdiv_def.
          rewrite Rinv_inv.
          lra.
        }
        apply (@IPCts_scale (λ x : R, exp (- Rabs (x)) / 2)).
        { by apply Rinv_0_lt_compat. }
        apply IPCts_cts.
        intros ?.
        apply Laplace_continuous.
      }
      { intros ?.
        rewrite Rdiv_def.
        rewrite Rmult_assoc.
        split.
        { apply Rmult_le_pos; [apply Rexp_nn|].
          apply Rmult_le_pos; OK.
          apply Hnn.
        }
        { apply Rmult_le_compat; OK.
          { apply Rexp_nn. }
          { apply Rmult_le_pos; OK. apply Hnn. }
          { apply exp_mono.
            apply Ropp_le_contravar.
            apply RRle_abs.
          }
          apply Rmult_le_compat; OK; apply Hnn.
        }
      }
      { replace (λ x : R, exp (- (ε * x)) * (/ 2 * M))
          with (λ x : R,  (/2 * M * exp (- (ε * x)))) by (funexti; lra).
        apply (@ex_RInt_gen_scal_change_of_var (λ x : R, (/ 2 * M * exp (- (x))))); OK.
        { intros ??.
          apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
          intros ??.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        apply ex_RInt_gen_exp.
      }
    }

    have HF2 : ex_RInt_gen (λ x : R, exp (- Rabs (- (ε * x))) / 2 * F (- ε * (x / ε))) (at_point 0) (Rbar_locally Rbar.p_infty).
    { replace (λ x : R, exp (- Rabs (- (ε * x))) / 2 * F (- ε * (x / ε)))
        with  (λ x : R, exp (- Rabs (ε * x)) / 2 * F (- x)); OK.
      2: {
          funexti.
          f_equal.
          2: {
            f_equal.
            rewrite -Ropp_mult_distr_l.
            f_equal.
            rewrite Rmult_comm.
            rewrite Rmult_assoc.
            rewrite Rmult_inv_l; OK.
          }
          rewrite Rabs_Ropp.
          OK.
      }

      eapply (@ex_RInt_gen_Ici_compare_IPCts _ (λ x : R, exp (- (ε * x)) * (/ 2 * M))).
      { apply IPCts_mult.
        2: {
          apply IPCts_cts. intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        { apply IPCts_cts.
          intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
      }
      { apply IPCts_mult.
        2: { apply IPCts_opp. OK. }
        replace (λ x : R, exp (- Rabs (ε * x)) / 2) with (λ x : R, exp (- Rabs (x / (/ ε))) / 2).
        2: {
          funexti.
          do 4 f_equal.
          rewrite Rdiv_def.
          rewrite Rinv_inv.
          lra.
        }
        apply (@IPCts_scale (λ x : R, exp (- Rabs (x)) / 2)).
        { by apply Rinv_0_lt_compat. }
        apply IPCts_cts.
        intros ?.
        apply Laplace_continuous.
      }
      { intros ?.
        rewrite Rdiv_def.
        rewrite Rmult_assoc.
        split.
        { apply Rmult_le_pos; [apply Rexp_nn|].
          apply Rmult_le_pos; OK.
          apply Hnn.
        }
        { apply Rmult_le_compat; OK.
          { apply Rexp_nn. }
          { apply Rmult_le_pos; OK. apply Hnn. }
          { apply exp_mono.
            apply Ropp_le_contravar.
            apply RRle_abs.
          }
          apply Rmult_le_compat; OK; apply Hnn.
        }
      }
      { replace (λ x : R, exp (- (ε * x)) * (/ 2 * M))
          with (λ x : R,  (/2 * M * exp (- (ε * x)))) by (funexti; lra).
        apply (@ex_RInt_gen_scal_change_of_var (λ x : R, (/ 2 * M * exp (- (x))))); OK.
        { intros ??.
          apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
          intros ??.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        apply ex_RInt_gen_exp.
      }
    }

    f_equal.
    { symmetry.
      rewrite /Laplace0_μ.
      rewrite /NegExpSymm_Closed.
      rewrite -RInt_gen_neg_change_of_var; first last.
      { replace (λ x : R, exp (- Rabs x) / 2 * F (x / ε))
          with (λ x : R, exp (- Rabs (/ ε * - x) * ε) / 2 * F (- (/ ε * - x))).
        2: {
          funexti.
          f_equal.
          2: { f_equal. rewrite Rdiv_def. OK.  }
          do 2 f_equal.
          rewrite -Rabs_Ropp.
          rewrite -{2}(Rabs_right ε); OK.
          rewrite Ropp_mult_distr_l_reverse.
          rewrite -Rabs_mult.
          do 2 f_equal.
          rewrite Ropp_mult_distr_r.
          rewrite Rmult_comm.
          rewrite -Rmult_assoc.
          rewrite Rmult_inv_r; OK.
        }

      apply (@ex_RInt_gen_neg_change_of_var_rev (λ x : R, exp (- Rabs (/ ε *  x) * ε) / 2 * F (- (/ ε *  x)))).
      { intros ??.
        apply ex_RInt_mult.
        2: {
          replace (λ y : R, F (- (/ ε * y))) with (λ y : R, F (-y / ε)) by (funexti; rewrite Rdiv_def; f_equal; OK).
          apply PCts_RInt.
          apply IPCts_PCts.
          apply (@IPCts_opp (λ y : R, F (y / ε))).
          apply IPCts_scale; OK.
        }
        apply (@ex_RInt_ext _ (λ y : R, exp (- y) / 2)).
        { rewrite Rmin_left; OK.  rewrite Rmax_right; OK.
          intros ??.
          repeat f_equal.
          rewrite Rabs_right; OK.
          2: {
            apply Rle_ge.
            apply Rmult_le_pos; OK.
            apply Rlt_le.
            apply Rinv_0_lt_compat; OK.
          }
          rewrite -Ropp_mult_distr_l.
          f_equal.
          rewrite Rmult_comm.
          rewrite -Rmult_assoc.
          rewrite Rmult_inv_r; OK.
        }
        apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      replace (λ x : R, exp (- Rabs (/ ε * x) * ε ) / 2 * F (- ( / ε * x)))
        with  (λ x : R, exp (- Rabs x) / 2 * F (- (/ε * x))); OK.
      2: {
      funexti.
      do 4 f_equal.
      rewrite -{2}(Rabs_right ε); OK.
      rewrite Ropp_mult_distr_l_reverse.
      rewrite -Rabs_mult.
      do 2 f_equal.
      rewrite Rmult_comm.
      rewrite -Rmult_assoc.
      rewrite Rmult_inv_r; OK.
      }

      eapply (@ex_RInt_gen_Ici_compare_IPCts _ (λ x : R, exp (- (x)) * (/ 2 * M))).
      { apply IPCts_mult.
        2: {
          apply IPCts_cts. intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        { apply IPCts_cts.
          intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
      }
      { apply IPCts_mult.
        2: {
          replace (λ y : R, F (- (/ ε * y))) with (λ y : R, F (-y / ε)) by (funexti; rewrite Rdiv_def; f_equal; OK).
          apply (@IPCts_opp (λ y : R, F (y / ε))).
          apply IPCts_scale; OK.
      }
        apply IPCts_cts.
        intros ?.
        apply Laplace_continuous.
      }
      { intros ?.
        rewrite Rdiv_def.
        rewrite Rmult_assoc.
        split.
        { apply Rmult_le_pos; [apply Rexp_nn|].
          apply Rmult_le_pos; OK.
          apply Hnn.
        }
        { apply Rmult_le_compat; OK.
          { apply Rexp_nn. }
          { apply Rmult_le_pos; OK. apply Hnn. }
          { apply exp_mono.
            apply Ropp_le_contravar.
            apply RRle_abs.
          }
          apply Rmult_le_compat; OK; apply Hnn.
        }
      }
      {
        apply ex_RInt_gen_scal_r.
        replace (λ x : R, exp (- x)) with (λ x : R, 1 * exp (- x)) by (funexti; OK).
        apply ex_RInt_gen_exp.
      }
      }



      { intros ??.
        apply IPCts_RInt.
        apply IPCts_mult; [|].
        2: { apply (@IPCts_opp (λ x : R, F (x / ε))). apply IPCts_scale; OK. }
        apply IPCts_cts.
        intros ?.
        replace (λ x0 : R, exp (- Rabs (- x0)) / 2) with (λ x0 : R, exp (- Rabs (x0)) / 2).
        2: { funexti; rewrite Rabs_Ropp. OK. }
        apply Laplace_continuous.
      }
      { intros ??.
        apply IPCts_RInt.
        apply IPCts_mult; [|].
        2: { apply IPCts_scale; OK. }
        apply IPCts_cts.
        intros ?.
        apply Laplace_continuous.
      }




      rewrite -RInt_gen_neg_change_of_var; first last.
      { replace
          (λ x : R, ε * (exp (- Rabs (ε * x)) / 2) * F x) with
          (λ x : R, ε * exp (- Rabs (ε * - x)) / 2 * F ((ε * - (-x) / ε))).
        2: {
          funexti.
          do 3 f_equal.
          2: {
            rewrite Ropp_involutive.
            rewrite Rmult_comm.
            rewrite Rdiv_def.
            rewrite Rmult_assoc.
            rewrite Rmult_inv_r; OK.
          }
          rewrite -Rmult_assoc.
          rewrite -Rdiv_def.
          do 4 f_equal.
          rewrite -Rabs_Ropp.
          f_equal; OK.
        }

      apply (@ex_RInt_gen_neg_change_of_var_rev (λ x : R, ε * exp (- Rabs (ε * x)) / 2 * F (ε * - x / ε))).
      { intros ??.
        apply ex_RInt_mult.
        2: {
          replace (λ y : R, F (ε * - y / ε)) with (λ y : R, F (- y)).
          2: { funexti. f_equal.
            rewrite Rmult_comm.
            rewrite Rdiv_def.
            rewrite Rmult_assoc.
            rewrite Rmult_inv_r; OK.
          }
          apply PCts_RInt.
          apply IPCts_PCts.
          apply IPCts_opp. OK.
        }

        apply (@ex_RInt_ext _ (λ y : R, ε * exp (- (ε * y)) / 2)).
        { rewrite Rmin_left; OK.  rewrite Rmax_right; OK.
          intros ??.
          repeat f_equal.
          rewrite Rabs_right; OK.
          apply Rle_ge.
          apply Rmult_le_pos; OK.
        }
        apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      replace (λ x : R, ε * exp (- Rabs (ε * x)) / 2 * F (ε * - x / ε))
         with (λ x : R, ε * (exp (- Rabs (ε * x)) / 2 * F (- x))).
      2: {
        funexti.
        repeat rewrite Rmult_assoc.
        do 4 f_equal.
        rewrite Rmult_comm.
        rewrite Rdiv_def.
        repeat rewrite -Ropp_mult_distr_l.
        f_equal.
        rewrite Rmult_assoc.
        rewrite Rmult_inv_r; OK.
      }
      apply ex_RInt_gen_scal_l.



      eapply (@ex_RInt_gen_Ici_compare_IPCts _ (λ x : R, exp (- (ε * x)) * (/ 2 * M))).
      { apply IPCts_mult.
        2: {
          apply IPCts_cts. intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        { apply IPCts_cts.
          intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
      }
      { apply IPCts_mult.
        2: {
          apply IPCts_opp.
          OK.
      }
        apply IPCts_cts.
        intros ?.
        apply Laplace_continuous_scaled.
      }
      { intros ?.
        rewrite Rdiv_def.
        rewrite Rmult_assoc.
        split.
        { apply Rmult_le_pos; [apply Rexp_nn|].
          apply Rmult_le_pos; OK.
          apply Hnn.
        }
        { apply Rmult_le_compat; OK.
          { apply Rexp_nn. }
          { apply Rmult_le_pos; OK. apply Hnn. }
          { apply exp_mono.
            apply Ropp_le_contravar.
            apply RRle_abs.
          }
          apply Rmult_le_compat; OK; apply Hnn.
        }
      }
      {
        apply ex_RInt_gen_scal_r.
        apply (@ex_RInt_gen_scal_change_of_var (λ x : R, exp (- (x)))); OK.
        { intros ??.
          apply IPCts_RInt.
          apply IPCts_cts.
          intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        replace (λ x : R, exp (- x)) with (λ x : R, 1 * exp (- x)) by (funexti; OK).
        apply ex_RInt_gen_exp.
      }
      }
      { intros ??.
        apply IPCts_RInt.
        apply IPCts_mult; [|].
        2: { apply (@IPCts_opp (λ x : R, F x)); OK. }
        apply IPCts_mult.
        { apply IPCts_cts.
          intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        apply IPCts_cts.
        intros ?.
        replace (λ x0 : R, (exp (- Rabs (ε * - x0)) / 2))
          with  (λ x0 : R, (exp (- Rabs (ε * x0)) / 2)).
        2: {
          funexti.
          do 3 f_equal.
          rewrite -Rabs_Ropp.
          f_equal; OK.
        }
        apply Laplace_continuous_scaled.
      }
      { intros ??.
        apply IPCts_RInt.
        apply IPCts_mult; [|OK].
        apply IPCts_mult.
        { apply IPCts_cts.
          intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        apply IPCts_cts.
        intros ?.
        apply Laplace_continuous_scaled.
      }

      replace (λ x : R, ε * (exp (- Rabs (ε * - x)) / 2) * F (- x))
         with (λ x : R, ε * ((exp (- Rabs (- (ε * x))) / 2) * F (- ε * (x / ε)))).
      2: {
        funexti.
        repeat rewrite Rmult_assoc.
        do 3 f_equal.
        { do 2 f_equal; OK. }
        f_equal.
        rewrite -Ropp_mult_distr_l.
        f_equal.
        rewrite Rmult_comm.
        rewrite Rmult_assoc.
        rewrite Rmult_inv_l; OK.
      }
      rewrite -RInt_gen_scal_l.
      2: { OK. }
      rewrite -{2}(Rinv_inv ε).

      rewrite -(@RInt_gen_scal_change_of_var (λ x : R, exp (- Rabs (- (ε * x))) / 2 * F (- ε * (x / ε))) (/ε)).
      { f_equal.
        funexti.
        f_equal; [|f_equal; OK].
        2: {
          replace (- x / ε) with (-1 * (x / ε)) by OK.
          replace (- ε * (/ ε * x / ε)) with (-1 * (ε * (/ ε * x / ε))) by OK.
          f_equal.
          repeat rewrite -Rmult_assoc.
          rewrite Rdiv_def.
          rewrite Rmult_inv_r; OK.
        }
        do 4 f_equal.
        do 2 rewrite Ropp_mult_distr_r.
        rewrite -Rmult_assoc.
        rewrite Rmult_inv_r; OK.
      }
      { apply Rinv_0_lt_compat; OK. }
      { intros ??.
        apply IPCts_RInt.
        apply IPCts_mult; [|].
        2: {
          replace (λ x : R, F (- ε * (x / ε))) with (λ x : R, F (- x)).
          2: {
            funexti.
            f_equal.
            rewrite Rdiv_def.
            rewrite -Ropp_mult_distr_l; f_equal.
            rewrite Rmult_comm Rmult_assoc Rmult_inv_l; OK.
          }
          by apply IPCts_opp.
        }
        replace (λ x : R, exp (- Rabs (- (ε * x))) / 2) with
          (λ x : R, exp (- Rabs (- (x / (/ ε)))) / 2).
        2: {
          funexti.
          do 5 f_equal.
          rewrite Rdiv_def Rinv_inv.
          lra.
        }
        apply (@IPCts_scale (λ x : R, exp (- Rabs (- x)) / 2)).
        {  apply Rinv_0_lt_compat; OK. }
        replace (λ x : R, exp (- Rabs (- x)) / 2) with (λ x : R, exp (- Rabs x) / 2).
        2: { funexti. do 3 f_equal. by rewrite Rabs_Ropp. }
        apply IPCts_cts.
        intros ?.
        apply Laplace_continuous.
      }
      { intros ??.
        apply IPCts_RInt.
        apply IPCts_mult.
        { replace
            (λ x : R, exp (- Rabs (- (ε * (/ ε * x)))) / 2) with
            (λ x : R, exp (- Rabs x) / 2).
          2: { funexti. do 3 f_equal. rewrite Rabs_Ropp. rewrite -Rmult_assoc. rewrite Rmult_inv_r; OK. f_equal; OK. }
          apply IPCts_cts.
          intros ?.
          apply Laplace_continuous.
        }
        replace (λ x : R, F (- ε * (/ ε * x / ε)))
           with (λ x : R, F ((- x) / ε)).
        2: { funexti; f_equal. rewrite Rdiv_def; OK.
             do 2 rewrite -Ropp_mult_distr_l.
             f_equal.
             repeat rewrite -Rmult_assoc.
             rewrite Rmult_inv_r; OK.
        }
        apply (@IPCts_opp (λ x : R, F (x / ε))).
        apply IPCts_scale; OK.
      }
      done.
    }
    { symmetry.
      rewrite /Laplace0_μ.
      rewrite /NegExpSymm_Closed.
      replace (λ x : R, ε * (exp (- Rabs (ε * x)) / 2) * F x)
         with (λ x : R, ε * ((exp (- Rabs (ε * x)) / 2) * F x)) by (funexti; OK).
      rewrite -RInt_gen_scal_l.
      2:  done.
      rewrite -{2}(Rinv_inv ε).
      rewrite -(@RInt_gen_scal_change_of_var (λ x : R, (exp (- Rabs (ε * x)) / 2) * F (x)) (/ε)).
      { f_equal.
        funexti.
        f_equal; [|f_equal; OK].
        do 4 f_equal.
        rewrite -Rmult_assoc.
        rewrite Rmult_inv_r; OK.
      }
      { apply Rinv_0_lt_compat; OK. }
      { intros ??.
        apply IPCts_RInt.
        apply IPCts_mult; [|done].
        apply IPCts_cts.
        intros ?.
        apply Laplace_continuous_scaled.
      }
      { intros ??.
        apply IPCts_RInt.
        apply IPCts_mult.
        { replace (λ x : R, exp (- Rabs (ε * (/ ε * x))) / 2) with (λ x : R, exp (- Rabs x) / 2).
          2: { funexti. do 4 f_equal. rewrite -Rmult_assoc. rewrite Rmult_inv_r; OK. }
          apply IPCts_cts.
          intros ?.
          apply Laplace_continuous.
        }
        replace (λ x : R, F (/ ε * x)) with (λ x : R, F (x / ε)).
        2: { funexti; f_equal. rewrite Rdiv_def; OK. }
        apply IPCts_scale; OK.
      }
      done.
    }
  Qed.

  Lemma wp_Laplace0 E (F : R → R) {M} (logε : Z) (Hnn : ∀ r, 0 <= F r <= M) (HP : IPCts F) :
    ⊢ ↯ (Laplace0_CreditV (powerRZ 2 logε) F) -∗
          WP Laplace0 #logε @ E {{ cont, ∃ I r, I ∗ IsApprox cont r E I ∗ ↯(F r) }}.
  Proof.
    iIntros "Hε".
    rewrite /Laplace0.
    wp_pures.
    wp_bind (NegExpSymmC _).
    iApply pgl_wp_mono.
    2: {
      iApply (@wp_NegExp_Closed_sym _ _ E (fun r => F (r / powerRZ 2 logε)) M).
      { intros ?. apply Hnn. }
      { apply IPCts_scale; try done.
        apply powerRZ_lt.
        lra.
      }
      iApply (ec_eq with "Hε").
      erewrite Laplace_CreditV_Scale; try done.
      apply powerRZ_lt. lra.
    }
    rewrite //=.
    iIntros (?) "[%I [%r [I [HA He]]]]".
    wp_pures.
    wp_bind (R_mulPow _ _).
    iApply (pgl_wp_mono_frame (I ∗ ↯ (F (r / powerRZ 2 logε))) with "[HA] [I He]").
    3: { iFrame. }
    2: { iApply wp_R_mulPow; iExact "HA". }
    rewrite //=.
    iIntros (?) "[[I HA] He]".
    iExists I, (r / powerRZ 2 logε).
    iFrame.
  Qed.

End Laplace0.

Definition Laplace : val :=
  λ: "logε" "μ",
    let: "sample" := Laplace0 "logε" in
    R_plus "μ" "sample" .

Section Laplace.
  Import Hierarchy.
  Context `{!erisGS Σ}.

  Definition Laplace_μ (ε μ : R) : R → R :=
    fun x => Laplace0_μ ε (x - μ).

  Definition Laplace_CreditV (ε μ : R) (F : R → R) : R :=
    RInt_gen (fun x => Laplace_μ ε μ x  * F x) (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty).

  Lemma Laplace0_IPCts {ε} : IPCts (Laplace0_μ ε).
  Proof.
    rewrite /Laplace0_μ.
    apply IPCts_cts.
    intros x.
    eapply @Continuity.continuous_mult; [apply Continuity.continuous_const|].
    eapply @Laplace_continuous_scaled.
  Qed.

  Lemma Laplace_exist1 {M} (ε μ : R) (F : R → R) (Hnn : ∀ r, 0 <= F r <= M) (HP : IPCts F) (He : 0 < ε) :
    ex_RInt_gen (λ x : R, Laplace0_μ ε x * F (x + μ)) (at_point 0) (Rbar_locally Rbar.p_infty).
  Proof.
    eapply (@ex_RInt_gen_Ici_compare_IPCts _ (λ x : R, Laplace0_μ ε x * M)).
    { apply IPCts_mult.
      { apply Laplace0_IPCts. }
      { apply IPCts_cts. apply Continuity.continuous_const. }
    }
    { apply IPCts_mult.
      { apply Laplace0_IPCts. }
      { replace (λ x : R, F (x + μ)) with (λ x : R, F (μ + x)) by (funexti; f_equal; OK).
        by apply IPCts_shift.
      }
    }
    { intros; split.
      { apply Rmult_le_pos.
        { rewrite /Laplace0_μ.
          apply Rmult_le_pos; OK.
          rewrite Rdiv_def.
          apply Rmult_le_pos; OK.
          apply Rexp_nn.
        }
        { apply Hnn. }
      }
      { apply Rmult_le_compat.
        { rewrite /Laplace0_μ.
          apply Rmult_le_pos; OK.
          rewrite Rdiv_def.
          apply Rmult_le_pos; OK.
          apply Rexp_nn.
        }
        { apply Hnn. }
        { done. }
        { apply Hnn. }
      }
    }
    { rewrite /Laplace0_μ.
      apply (@ex_RInt_gen_scal_change_of_var (λ x : R, ε * (exp (- Rabs (x)) / 2) * M) ε); OK.
      { intros ??.
        eapply @ex_RInt_continuous.
        intros ??.
        apply @Continuity.continuous_mult; try apply Continuity.continuous_const.
        apply @Continuity.continuous_mult; try apply Continuity.continuous_const.
        apply @Laplace_continuous.
      }
      apply ex_RInt_gen_scal_r.
      apply ex_RInt_gen_scal_l.
      replace (λ x : R, 1 * exp (- Rabs x) / 2) with (λ x : R, /2 * exp (- Rabs x)) by (funexti; OK).
      apply (@ex_RInt_gen_ext_eq_Ici (λ x : R, / 2 * exp (- x))).
      { intros ??. rewrite Rabs_right; OK. }
      eapply ex_RInt_gen_exp.
    }
  Qed.


  Lemma Laplace_exist2 {M} (ε μ : R) (F : R → R) (Hnn : ∀ r, 0 <= F r <= M) (HP : IPCts F) (He : 0 < ε) :
    ex_RInt_gen (λ x : R, Laplace0_μ ε x * F (- x + μ)) (at_point 0) (Rbar_locally Rbar.p_infty).
  Proof.
    eapply (@ex_RInt_gen_Ici_compare_IPCts _ (λ x : R, Laplace0_μ ε x * M)).
    { apply IPCts_mult.
      { apply Laplace0_IPCts. }
      { apply IPCts_cts. apply Continuity.continuous_const. }
    }
    { apply IPCts_mult.
      { apply Laplace0_IPCts. }
      { apply (@IPCts_opp (λ x : R, F (x + μ))).
        replace (λ x : R, F (x + μ)) with (λ x : R, F (μ + x)) by (funexti; f_equal; OK).
        by apply IPCts_shift.
      }
    }
    { intros; split.
      { apply Rmult_le_pos.
        { rewrite /Laplace0_μ.
          apply Rmult_le_pos; OK.
          rewrite Rdiv_def.
          apply Rmult_le_pos; OK.
          apply Rexp_nn.
        }
        { apply Hnn. }
      }
      { apply Rmult_le_compat.
        { rewrite /Laplace0_μ.
          apply Rmult_le_pos; OK.
          rewrite Rdiv_def.
          apply Rmult_le_pos; OK.
          apply Rexp_nn.
        }
        { apply Hnn. }
        { done. }
        { apply Hnn. }
      }
    }
    { rewrite /Laplace0_μ.
      apply (@ex_RInt_gen_scal_change_of_var (λ x : R, ε * (exp (- Rabs (x)) / 2) * M) ε); OK.
      { intros ??.
        eapply @ex_RInt_continuous.
        intros ??.
        apply @Continuity.continuous_mult; try apply Continuity.continuous_const.
        apply @Continuity.continuous_mult; try apply Continuity.continuous_const.
        apply @Laplace_continuous.
      }
      apply ex_RInt_gen_scal_r.
      apply ex_RInt_gen_scal_l.
      replace (λ x : R, exp (- Rabs x) / 2) with (λ x : R, /2 * exp (- Rabs x)) by (funexti; OK).
      apply (@ex_RInt_gen_ext_eq_Ici (λ x : R, / 2 * exp (- x))).
      { intros ??. rewrite Rabs_right; OK. }
      eapply ex_RInt_gen_exp.
    }
  Qed.

  Lemma Laplace_CreditV_eq {M} (ε μ : R) (F : R → R) (Hnn : ∀ r, 0 <= F r <= M) (HP : IPCts F) (He : 0 < ε) :
    Laplace_CreditV ε μ F = Laplace0_CreditV ε (λ r : R, F (μ + r)).
  Proof.
    rewrite /Laplace_CreditV/Laplace0_CreditV.
    rewrite /Laplace_μ.
    (* 1. Chasles to split the positive and negative integrals *)

    rewrite -(@RInt_gen_Chasles R_CompleteNormedModule (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty) _ _  (λ x : R, Laplace0_μ ε (x - μ) * F x) μ); first last.
    { replace μ with (- (- μ)) by OK.
      replace (λ x : R, Laplace0_μ ε (x - - - μ) * F x)
         with (λ x : R, Laplace0_μ ε (- μ + x) * F (- μ + x + μ)).
      2: { funexti; OK. repeat (f_equal; OK). }
      apply (@ex_RInt_gen_shift (λ x : R, Laplace0_μ ε x * F (x + μ)) (- μ)).
      { intros ?.
        apply IPCts_RInt.
        apply IPCts_mult.
        { apply Laplace0_IPCts. }
        { replace (λ x : R, F (x + μ)) with (λ x : R, F (μ + x)) by (funexti; f_equal; OK).
          by apply IPCts_shift.
        }
      }
      eapply @Laplace_exist1; OK.
    }
    { replace μ with (- (- μ)) by OK.
      replace (λ x : R, Laplace0_μ ε (x - - - μ) * F x)
         with (λ x : R, Laplace0_μ ε (- μ + x) * F (- μ + x + μ)).
      2: { funexti; OK. repeat (f_equal; OK). }
      apply (@ex_RInt_gen_shift_neg (λ x : R, Laplace0_μ ε x * F (x + μ)) (- μ)).
      { intros ?.
        apply IPCts_RInt.
        apply IPCts_mult.
        { apply Laplace0_IPCts. }
        { replace (λ x : R, F (x + μ)) with (λ x : R, F (μ + x)) by (funexti; f_equal; OK).
          by apply IPCts_shift.
        }
      }
      (* Flip the negative side *)
      replace (λ x : R, Laplace0_μ ε x * F (x + μ))
         with (λ x : R, Laplace0_μ ε (- - x) * F (- -x + μ)) by (funexti; repeat (f_equal; OK)).
      eapply (@ex_RInt_gen_neg_change_of_var_rev (λ x : R, Laplace0_μ ε (- x) * F (- x + μ))).
      { intros ??.
        apply IPCts_RInt.
        apply IPCts_mult.
        { apply IPCts_opp.
          apply Laplace0_IPCts. }
        { eapply (@IPCts_opp (λ x : R, F (x + μ))).
          replace (λ x : R, F (x + μ)) with (λ x : R, F (μ + x)) by (funexti; f_equal; OK).
          by apply IPCts_shift.
        }
      }
      { replace (λ x : R, Laplace0_μ ε (- x) * F (- x + μ))
           with (λ x : R, Laplace0_μ ε (x) * F (- x + μ)).
        2: {
          funexti. f_equal; OK.
          rewrite /Laplace0_μ//=.
          rewrite -Rabs_Ropp.
          repeat (f_equal; OK).
        }
        eapply @Laplace_exist2; OK.
      }
    }

    rewrite -(@RInt_gen_Chasles R_CompleteNormedModule (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty) _ _  (λ x : R, Laplace0_μ ε x * F (μ + x)) 0); first last.
    { replace (λ x : R, Laplace0_μ ε x * F (μ + x)) with  (λ x : R, Laplace0_μ ε x * F (x + μ)) by (funexti; repeat (f_equal; OK)).
      eapply @Laplace_exist1; OK.
    }
    { (* Flip the negative side *)
      replace (λ x : R, Laplace0_μ ε x * F (μ + x))
         with (λ x : R, Laplace0_μ ε (- - x) * F (- -x + μ)) by (funexti; repeat (f_equal; OK)).
      eapply (@ex_RInt_gen_neg_change_of_var_rev (λ x : R, Laplace0_μ ε (- x) * F (- x + μ))).
      { intros ??.
        apply IPCts_RInt.
        apply IPCts_mult.
        { apply IPCts_opp.
          apply Laplace0_IPCts. }
        { eapply (@IPCts_opp (λ x : R, F (x + μ))).
          replace (λ x : R, F (x + μ)) with (λ x : R, F (μ + x)) by (funexti; f_equal; OK).
          by apply IPCts_shift.
        }
      }
      replace (λ x : R, Laplace0_μ ε (- x) * F (- x + μ))
         with (λ x : R, Laplace0_μ ε (x) * F (- x + μ)).
      2: {
        funexti. f_equal; OK.
        rewrite /Laplace0_μ//=.
        rewrite -Rabs_Ropp.
        repeat (f_equal; OK).
      }
      eapply @Laplace_exist2; OK.
    }

    f_equal.
    { erewrite (RInt_gen_shift_neg (-μ)); first last.
      { replace (λ x : R, Laplace0_μ ε x * F (μ + x))
           with (λ x : R, Laplace0_μ ε (- - x) * F (- -x + μ)) by (funexti; repeat (f_equal; OK)).
        eapply (@ex_RInt_gen_neg_change_of_var_rev (λ x : R, Laplace0_μ ε (- x) * F (- x + μ))).
        { intros ??.
          apply IPCts_RInt.
          apply IPCts_mult.
          { apply IPCts_opp.
            apply Laplace0_IPCts. }
          { eapply (@IPCts_opp (λ x : R, F (x + μ))).
            replace (λ x : R, F (x + μ)) with (λ x : R, F (μ + x)) by (funexti; f_equal; OK).
            by apply IPCts_shift.
          }
        }
        { replace (λ x : R, Laplace0_μ ε (- x) * F (- x + μ))
             with (λ x : R, Laplace0_μ ε (x) * F (- x + μ)).
          2: {
            funexti. f_equal; OK.
            rewrite /Laplace0_μ//=.
            rewrite -Rabs_Ropp.
            repeat (f_equal; OK).
          }
          eapply @Laplace_exist2; OK.
        }
      }
      { intros ?.
        apply IPCts_RInt.
        apply IPCts_mult.
        { apply Laplace0_IPCts. }
        { replace (λ x : R, F (x + μ)) with (λ x : R, F (μ + x)) by (funexti; f_equal; OK).
          by apply IPCts_shift.
        }
      }
      repeat (f_equal; OK).
      funexti.
      repeat (f_equal; OK).
    }
    { (* Apply the shifting lemma *)
      rewrite (RInt_gen_shift (-μ)); first last.
      { replace (λ x : R, Laplace0_μ ε x * F (μ + x)) with  (λ x : R, Laplace0_μ ε x * F (x + μ)) by (funexti; repeat (f_equal; OK)).
        eapply @Laplace_exist1; OK.
      }
      { intros ?.
        apply IPCts_RInt.
        apply IPCts_mult.
        { apply Laplace0_IPCts. }
        { replace (λ x : R, F (x + μ)) with (λ x : R, F (μ + x)) by (funexti; f_equal; OK).
          by apply IPCts_shift.
        }
      }
      rewrite Ropp_involutive.
      f_equal; funexti; f_equal; f_equal; OK.
    }
  Qed.

  Lemma wp_Laplace E (F : R → R) {M} (logε : Z) (μcont : val) μI (μ : R) (Hnn : ∀ r, 0 <= F r <= M) (HP : IPCts F) :
    ⊢ ↯ (Laplace_CreditV (powerRZ 2 logε) μ F) -∗
      IsApprox μcont μ E μI -∗
      WP Laplace #logε μcont @ E {{ cont, ∃ I r, I ∗ IsApprox cont r E (μI ∗ I) ∗ ↯(F r) }}.
  Proof.
    iIntros "Hε Hcont".
    rewrite /Laplace.
    wp_pures.
    wp_bind (Laplace0 _).
    iApply (pgl_wp_mono_frame (IsApprox μcont μ E μI) with "[Hε] Hcont").
    2: {
      iApply (@wp_Laplace0 _ _ E (fun r => F (μ + r)) M).
      { intros ?. apply Hnn. }
      { by apply IPCts_shift. }
      iApply (ec_eq with "Hε").
      erewrite Laplace_CreditV_eq; try done.
      apply powerRZ_lt. OK.
    }
    rewrite //=.
    iIntros (?) "[Hcont [%I [%r [I [HA He]]]]]".
    wp_pures.
    wp_bind (R_plus _ _).
    iApply (pgl_wp_mono_frame (I ∗ ↯ (F (μ + r))) with "[HA Hcont] [I He]").
    3: { iFrame. }
    2: { iApply wp_R_plus. iFrame. }
    rewrite //=.
    iIntros (?) "[[I HA] He]".
    iExists I, (μ + r).
    iFrame.
  Qed.

End Laplace.


Section AccuracyBound.
  Context `{!erisGS Σ}.
  Import Hierarchy.

  (* A function which is 1 outside of the range [-L, L] *)
  Definition AccF (L : R) : R → R := (fun x => Iverson (Iio (-L)) x + Iverson (Ioi L) x).

  Lemma AccF_IPCts L (HL : 0 <= L) : IPCts (AccF L).
  Proof.
    rewrite /IPCts.
    exists (fun _ => 1).
    exists (List.cons (fun _ => -1, -L, L) List.nil).
    split; last split.
    { intros ?.
      rewrite /fsum//=.
      rewrite /AccF.
      symmetry.
      rewrite {1}/Iverson.
      case_decide; rewrite /Icc//= in H; rewrite Rmin_left in H; OK; rewrite Rmax_right in H; OK.
      { rewrite Iverson_False.
        2: { rewrite /Iio. OK. }
        rewrite Iverson_False.
        2: { rewrite /Ioi. OK. }
        OK.
      }
      { rewrite {1} /Iverson.
        rewrite /Ioi//=.
        case_decide; rewrite /Iio in H0.
        { rewrite Iverson_False; OK. }
        { rewrite Iverson_True; OK. }
      }
    }
    { apply Forall_singleton.
      rewrite /IntervalFun_continuity.
      intros ??.
      apply Continuity.continuous_const.
    }
    {
      intros ?.
      apply Continuity.continuous_const.
    }
  Qed.

  Lemma Laplace_Int_AccF {L} {μ ε} :
    0 <= L ->
    RInt_gen (λ r : R, Laplace_μ ε μ r * AccF L (r - μ)) (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty) = exp (- L).
  Proof.
    (*
    rewrite -NegExp_Int.
    rewrite /AccF.
    apply neg_exp_accuracy_chasles.
    *)
  Admitted.


  Lemma wp_Laplace_Accuracy E (β : R) (Hβ : 0 < β <= 1) (logε : Z) (μcont : val) μI (μ : R) :
    ⊢ ↯ β -∗
    IsApprox μcont μ E μI -∗
      WP Laplace #logε μcont @ E
        {{ cont, ∃ I r, I ∗ IsApprox cont r E (μI ∗ I) ∗ ⌜Rabs (r - μ) <= ln (/ β) ⌝}}.
  Proof.
    iIntros "Hε Happrox".
    iApply (pgl_wp_mono with "[Hε Happrox]").
    2: {
      iApply (wp_Laplace E (M := (1 + 1)) (fun r => AccF ((ln (/ β))) (r - μ)) _ _ _ μ with "[Hε]").
      { intros x. rewrite /AccF.
        split.
        { apply Rplus_le_le_0_compat; apply Iverson_nonneg. }
        { apply Rplus_le_compat; apply Iverson_le_1. }
      }
      { replace (λ r : R, AccF (ln (/ β)) (r - μ)) with (λ r : R, AccF (ln (/ β)) ( - μ + r)) by (funexti; f_equal; OK).
        apply IPCts_shift.
        apply AccF_IPCts.
        rewrite ln_Rinv; OK.
        suffices ? : ln β <= 0 by OK.
        rewrite -ln_1.
        apply Rcomplements.ln_le; OK.
      }
      { iApply (ec_eq with "Hε").
        rewrite /Laplace_CreditV.
        rewrite Laplace_Int_AccF.
        - rewrite ln_Rinv; OK.
          rewrite Ropp_involutive.
          rewrite exp_ln; OK.
        - rewrite -ln_1.
          apply Rcomplements.ln_le; first lra.
          rewrite -Rdiv_1_l.
          apply Rcomplements.Rle_div_r; lra.
      }
      { iApply "Happrox". }
    }
    intros v.
    rewrite //=.
    iIntros "[%I [%r [? [? He]]]]".
    iExists I.
    iExists r.
    iFrame.
    rewrite /AccF/Iverson.
    case_decide.
    { iExFalso. iApply (ec_contradict with "He"). case_decide; OK. }
    case_decide.
    { iExFalso. iApply (ec_contradict with "He"). OK. }
    rewrite /Iio//= in H.
    rewrite /Ioi//= in H0.
    iPureIntro.
    apply Rabs_le.
    split; OK.
  Qed.

End AccuracyBound.
