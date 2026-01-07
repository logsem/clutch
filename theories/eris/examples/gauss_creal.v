From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real real_decr_trial bern_geo half_bern_neg_exp bern_iter selector lazy_real_adequacy gauss lazy_real_expr.
From clutch.eris.examples Require Import math.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Definition GaussSymm : val :=
  λ: "e",
    let: "v" := G2 #() in
    let: "b" := rand (#1) in
    ("b", ((Snd "v"), (Fst "v"))).

Definition Gauss : val :=
  λ: "_",
    let: "sample_bzu" := GaussSymm #() in
    ToLazyReal "sample_bzu".

Section Symmetric.
  Import Hierarchy.
  Context `{!erisGS Σ}.

  Definition GaussSymm_ρ (_ : fin 2) (k : nat) (x : R) : R :=
    exp ((-(x+k)^2)/2) / Norm2 / 2.

  Definition GaussSymm_CreditV (F : fin 2 → nat → R → R)  :=
    (SeriesC (fun (b : fin 2) => SeriesC (fun (k : nat) => RInt (fun x => GaussSymm_ρ b k x * F b k x) 0 1))).

  Definition GaussNorm : R :=
    2 * Norm2.
    (* I think there's no reason to compute this. *)
    (* RInt_gen (fun x => exp (-x^2 / 2)) (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty). *)

  Lemma GaussNorm_nn : 0 < GaussNorm.
  Proof.
    rewrite /GaussNorm.
    apply Rmult_lt_0_compat; OK.
    apply Norm2_nn.
  Qed.

  Lemma GaussNorm_Norm2 : GaussNorm = 2 * Norm2.
  Proof.
    rewrite /GaussNorm//=.
  Qed.

  Definition Gauss_ρ (x : R) : R :=
    exp (-x^2 / 2) / GaussNorm.

  Definition Gauss_CreditV (F : R → R)  :=
    RInt_gen (fun x => Gauss_ρ x * F x) (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty).

  Lemma Gauss_Closed_ex_pos (F : R → R) {M} (Hnn : ∀ x, 0 <= F x <= M) (HP : IPCts F)  :
    ex_RInt_gen (λ x : R, Gauss_ρ x * F x) (at_point 0) (Rbar_locally Rbar.p_infty).
  Proof.
    apply (@ex_RInt_gen_Ici_compare_IPCts _ (λ x : R, Gauss_ρ x * M)).
    { apply IPCts_cts.
      rewrite /Gauss_ρ//=.
      intros ?.
      apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
      by auto_derive.
    }
    { apply IPCts_mult.
      { apply IPCts_cts.
        rewrite /Gauss_ρ//=.
        intros ?.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      apply HP.
    }
    { intros ?.
      split.
      { apply Rmult_le_pos.
        { rewrite /Gauss_ρ.
          apply Rcomplements.Rdiv_le_0_compat; [apply Rexp_nn |apply GaussNorm_nn].
        }
        { apply Hnn. }
      }
      apply Rmult_le_compat.
      { rewrite /Gauss_ρ.
        apply Rcomplements.Rdiv_le_0_compat; [apply Rexp_nn |apply GaussNorm_nn].
      }
      { apply Hnn. }
      { OK. }
      { apply Hnn. }
    }
    apply ex_RInt_gen_scal_r.
    rewrite /Gauss_ρ.
    replace (λ x : R, exp (- x ^ 2 / 2) / GaussNorm) with (λ x : R, exp (- x ^ 2 / 2) * / GaussNorm) by (funexti; OK).
    apply ex_RInt_gen_scal_r.
    apply ex_RInt_gen_gauss.
  Qed.

  Lemma Gauss_Closed_ex_neg (F : R → R) {M} (Hnn : ∀ x, 0 <= F x <= M) (HP : IPCts F) :
    ex_RInt_gen (λ x : R, Gauss_ρ x * F x) (Rbar_locally Rbar.m_infty) (at_point 0).
  Proof.
    replace (λ x : R, Gauss_ρ x * F x) with (λ x : R, Gauss_ρ (- x) * F (- (- x))).
    2: {
      funexti.
      f_equal; [|f_equal; OK].
      rewrite /Gauss_ρ.
      do 4 f_equal.
      OK.
    }
    apply (@ex_RInt_gen_neg_change_of_var_rev (λ x : R, Gauss_ρ x * F (- x))).
    { intros ??.
      apply IPCts_RInt.
      apply IPCts_mult.
      { apply IPCts_cts.
        rewrite /Gauss_ρ//=.
        intros ?.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      apply IPCts_opp, HP.
    }
    eapply (Gauss_Closed_ex_pos (M := M) (fun x => F (- x))).
    { intros ?; apply Hnn. }
    { apply IPCts_opp, HP. }
  Qed.

  Lemma Gauss_Closed_Symm (F : R → R) {M} (Hnn : ∀ x, 0 <= F x <= M) (HP : IPCts F)  :
    RInt_gen (λ x : R, Gauss_ρ x * F x) (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty) =
    plus (RInt_gen (λ x : R, Gauss_ρ x * F x) (Rbar_locally Rbar.m_infty) (at_point 0))
         (RInt_gen (λ x : R, Gauss_ρ x * F x) (at_point 0) (Rbar_locally Rbar.p_infty)).
  Proof.
    symmetry.
    apply RInt_gen_Chasles.
    { eapply Gauss_Closed_ex_neg; OK. }
    { eapply Gauss_Closed_ex_pos; OK. }
  Qed.


  Lemma Gauss_Closed (F : R → R) {M} (Hnn : ∀ x, 0 <= F x <= M) (HP : IPCts F)  :
    Gauss_CreditV F = GaussSymm_CreditV (λ (b : fin 2) (z : nat) (u : R), F (bzu_to_R b z u)).
  Proof.
    rewrite /Gauss_CreditV.
    rewrite /GaussSymm_CreditV.
    erewrite Gauss_Closed_Symm; OK.
    rewrite SeriesC_fin2 //=.
    rewrite Rplus_comm.
    f_equal.
    { (* Flip the improper integral *)
      rewrite -RInt_gen_neg_change_of_var; first last.
      { eapply Gauss_Closed_ex_neg; OK. }
      { intros ??.
        apply IPCts_RInt.
        apply IPCts_mult.
        { apply IPCts_cts.
          rewrite /Gauss_ρ//=.
          intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        apply IPCts_opp, HP.
      }
      { intros ??.
        apply IPCts_RInt.
        apply IPCts_mult.
        { apply IPCts_cts.
          rewrite /Gauss_ρ//=.
          intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        apply HP.
      }
      (* Apply Sep *)
      rewrite (@RInt_sep _ (fun _ => 666)); first last.
      { intros ?.
        apply IPCts_RInt.
        apply IPCts_mult.
        { apply IPCts_cts.
          rewrite /Gauss_ρ//=.
          intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        apply IPCts_opp, HP.
      }
      { admit. }
      { admit. }
      { replace (λ x : R, Gauss_ρ (- x) * F (- x)) with (λ x : R, Gauss_ρ x * F (- x)).
        2: {
          funexti.
          f_equal.
          rewrite /Gauss_ρ.
          do 4 f_equal.
          OK.
        }
        eapply Gauss_Closed_ex_pos; OK.
        apply IPCts_opp, HP.
      }
      (* Apply Fubini *)
      rewrite (FubiniIntegralSeriesC_Strong (fun _ => 666)); first last.
      { intros ?.
        apply ex_RInt_mult.
        { rewrite /GaussSymm_ρ//=.
          apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
          intros ??.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        { rewrite /bzu_to_R//=.
          (* Change of variables, then IPCts *)
          replace (λ y : R, F (-1 * 1 * (n + y)))
             with (λ y : R, -1 * (scal (-1) (F (-1 * y + -n)))).
          2: {
            funexti.
            rewrite /scal//=/mult//= -Rmult_assoc.
            replace (-1 * -1) with 1 by OK.
            rewrite Rmult_1_l; f_equal.
            OK.
          }
          apply ex_RInt_mult; [apply ex_RInt_const|].
          apply (@ex_RInt_comp_lin R_CompleteNormedModule _ (-1) (- n) 0 1).
          apply PCts_RInt.
          by apply IPCts_PCts.
        }
      }
      { admit. }
      { admit. }
      { intros ???.
        apply Rmult_le_pos.
        2: { apply Hnn. }
        rewrite /GaussSymm_ρ.
        rewrite -Rdiv_mult_distr.
        apply Rmult_le_pos; OK.
        { apply Rexp_nn. }
        apply Rlt_le.
        apply Rinv_0_lt_compat.
        apply Rmult_lt_0_compat; OK.
        apply Norm2_nn.
      }
      { OK. }
      rewrite /bzu_to_R//=.
      rewrite /Gauss_ρ/GaussSymm_ρ//=.
      apply RInt_ext.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      apply SeriesC_ext.
      intros ?.
      f_equal; [|f_equal; OK].
      rewrite -Rdiv_mult_distr.
      rewrite GaussNorm_Norm2.
      f_equal; OK.
      do 3 f_equal.
      OK.
    }
    { (* Apply Sep *)
      rewrite (@RInt_sep _ (fun _ => 666)); first last.
      { intros ?.
        apply IPCts_RInt.
        apply IPCts_mult.
        { apply IPCts_cts.
          rewrite /Gauss_ρ//=.
          intros ?.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        apply HP.
      }
      { admit. }
      { admit. }
      { eapply Gauss_Closed_ex_pos; OK. }
      (* Apply Fubini *)
      rewrite (FubiniIntegralSeriesC_Strong (fun _ => 666)); first last.
      { intros ?.
        apply ex_RInt_mult.
        { rewrite /GaussSymm_ρ//=.
          apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
          intros ??.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        { rewrite /bzu_to_R//=.
          (* Change of variables, then IPCts *)
          replace (λ y : R, F (1 * (n + y)))
             with (λ y : R, (scal 1 (F (1 * y + n)))).
          2: {
            funexti.
            rewrite /scal//=/mult//=.
            rewrite Rmult_1_l; f_equal.
            OK.
          }
          apply (@ex_RInt_comp_lin R_CompleteNormedModule _ (1) (n) 0 1).
          apply PCts_RInt.
          by apply IPCts_PCts.
        }
      }
      { admit. }
      { admit. }
      { intros ???.
        apply Rmult_le_pos.
        2: { apply Hnn. }
        rewrite /GaussSymm_ρ.
        rewrite -Rdiv_mult_distr.
        apply Rmult_le_pos; OK.
        { apply Rexp_nn. }
        apply Rlt_le.
        apply Rinv_0_lt_compat.
        apply Rmult_lt_0_compat; OK.
        apply Norm2_nn.
      }
      { OK. }
      rewrite /bzu_to_R//=.
      rewrite /Gauss_ρ/GaussSymm_ρ//=.
      apply RInt_ext.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      apply SeriesC_ext.
      intros ?.
      f_equal; [|f_equal; OK].
      rewrite -Rdiv_mult_distr.
      rewrite GaussNorm_Norm2.
      f_equal; OK.
    }
  Admitted.

  Lemma wp_GaussSymm E (F : fin 2 → nat → R → R) {M}
      (Hnn : ∀ c a b, 0 <= F c a b <= M) (HP : ∀ x x1, PCts (F x x1) 0 1)  :
    ⊢ ↯ (GaussSymm_CreditV F) -∗
           WP GaussSymm #() @ E
      {{ p, ∃ (b : fin 2) (vz : nat) (vr : R) (ℓ : val),
            ⌜p = PairV #(fin_to_nat b) (PairV #(Z.of_nat vz) ℓ)⌝ ∗
            lazy_real ℓ vr ∗ ⌜0 <= vr < 1 ⌝ ∗
            ↯(F b vz vr)}}.
  Proof.
    iIntros "Hε".
    rewrite /GaussSymm.
    wp_pures.
    wp_bind (G2 _).
    iApply (pgl_wp_mono).
    2: {
      iApply ((@wp_G2 _ _ E (fun n r => (F (0)%fin n r + F (1)%fin n r) / 2) M) with "[Hε]").
      { intros ??.
        split.
        { apply Rcomplements.Rdiv_le_0_compat; try lra.
          apply Rplus_le_le_0_compat.
          { apply Hnn. }
          { apply Hnn. }
        }
        { suffices  ? :  (F 0%fin x k + F 1%fin x k) <= M + M by lra.
          apply Rplus_le_compat.
          { apply Hnn. }
          { apply Hnn. }
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
        rewrite /GaussSymm_CreditV.
        rewrite SeriesC_fin2.
        have HB : ∀ b, ex_seriesC (λ k : nat, RInt (λ x : R, GaussSymm_ρ 0 k x * F b k x) 0 1).
        { intros b.
          rewrite /GaussSymm_ρ.
          eapply (ex_seriesC_le _ (λ k : nat, RInt (λ x : R, exp (- (x + k) ^ 2 / 2) / Norm2 / 2) 0 1 * M)).
          { intros ?.
            split.
            { apply RInt_ge_0; OK.
              { apply ex_RInt_mult.
                { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
                  intros ??.
                  apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
                  by auto_derive.
                }
                apply PCts_RInt, HP.
              }
              intros ??.
              apply Rmult_le_pos.
              { do 2 rewrite Rdiv_def.
                apply Rcomplements.Rdiv_le_0_compat; OK.
                apply Rcomplements.Rdiv_le_0_compat; [|apply Norm2_nn].
                apply Rexp_nn.
              }
              apply Hnn.
            }
            { rewrite RInt_Rmult'.
              2: {
                apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
                intros ??.
                apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
                by auto_derive.
              }
              apply RInt_le; OK.
              2: {
                apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
                intros ??.
                apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
                by auto_derive.
              }
              { apply ex_RInt_mult.
                { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
                  intros ??.
                  apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
                  by auto_derive.
                 }
                apply PCts_RInt, HP.
               }
              intros ??.
              repeat rewrite Rdiv_def.
              repeat rewrite Rmult_assoc.
              apply Rmult_le_compat.
              { apply Rexp_nn.  }
              { apply Rmult_le_pos.
                { apply Rlt_le, Rinv_0_lt_compat, Norm2_nn. }
                apply Rmult_le_pos; OK.
                apply Hnn.
              }
              2: {
                repeat rewrite -Rmult_assoc.
                apply Rmult_le_compat; OK.
                { apply Rmult_le_pos; OK.
                  apply Rlt_le, Rinv_0_lt_compat, Norm2_nn.
                }
                { apply Hnn. }
                { apply Hnn. }
              }
              OK.
            }
          }
          apply ex_seriesC_scal_r.
          apply (ex_seriesC_RInt (fun n => exp (- (n) ^ 2 / 2) * /Norm2 * / 2)); try lra.
          { intros ???.
            apply Rcomplements.Rdiv_le_0_compat; OK.
            apply Rcomplements.Rdiv_le_0_compat; [|apply Norm2_nn].
            apply Rexp_nn.
          }
          { apply ex_seriesC_scal_r.
            apply ex_seriesC_scal_r.
            apply Norm1_ex.
          }
          { intros ???.
            rewrite Rabs_right.
            2: {
              apply Rle_ge.
              apply Rcomplements.Rdiv_le_0_compat; OK.
              apply Rcomplements.Rdiv_le_0_compat; [|apply Norm2_nn].
              apply Rexp_nn.
            }
            rewrite Rdiv_def.
            rewrite Rdiv_def.
            repeat rewrite Rmult_assoc.
            apply Rmult_le_compat; OK.
            { apply Rexp_nn. }
            { apply Rmult_le_pos; OK. apply Rlt_le, Rinv_0_lt_compat, Norm2_nn. }
            apply exp_mono.
            do 2 rewrite Rdiv_def.
            do 2 rewrite Ropp_mult_distr_l_reverse.
            apply Ropp_le_contravar.
            apply Rmult_le_compat; OK.
            { apply pow2_ge_0. }
            apply pow_incr; OK.
            have ? := pos_INR n.
            OK.
          }
          { intros ?.
            apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
            intros ??.
            apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
            by auto_derive.
          }
        }
        rewrite -SeriesC_plus; OK.
        rewrite /G2_CreditV.
        apply SeriesC_ext.
        intros n.
        rewrite RInt_add.
        2: {
          apply ex_RInt_mult.
          { rewrite /GaussSymm_ρ//=.
            apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
            intros ??.
            apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
            by auto_derive.
          }
          { apply PCts_RInt, HP. }
        }
        2: {
          apply ex_RInt_mult.
          { rewrite /GaussSymm_ρ//=.
            apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
            intros ??.
            apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
            by auto_derive.
          }
          { apply PCts_RInt, HP. }
        }
        apply RInt_ext.
        intros ??.
        rewrite /GaussSymm_ρ//=.
        rewrite /G2_μ.
        rewrite Rdiv_plus_distr.
        rewrite Rmult_plus_distr_l.
        f_equal; OK.
        { repeat rewrite Rdiv_def. OK. }
        { repeat rewrite Rdiv_def. OK. }
      }
    }
    simpl.
    iIntros (v) "[%k [%r [%l [Hr [% [-> Hec]]]]]]".
    wp_pures.
    wp_apply (wp_couple_rand_adv_comp _ _ _ _ (fun (s : fin 2) => F s k r) with "Hec").
    { intros n. apply Hnn. }
    { rewrite SeriesC_fin2 //=. lra. }
    iIntros (b) "Hec".
    wp_pures.
    iModIntro.
    iExists b, k, r, l.
    iFrame.
    iPureIntro; OK.
  Qed.

  Lemma wp_Gauss E (F : R → R) {M} (Hnn : ∀ x, 0 <= F x <= M) (HP : IPCts F)  :
    ⊢ ↯ (Gauss_CreditV F) -∗
      WP Gauss #() @ E {{ cont, ∃ I r, I ∗ IsApprox cont r E (I) ∗ ↯(F r) }}.
  Proof.
    iIntros "He".
    rewrite /Gauss.
    wp_pures.
    wp_bind (GaussSymm _).
    iApply (pgl_wp_mono).
    2: {
      iApply (@wp_GaussSymm E (fun b z u => F (bzu_to_R b z u)) M with "[He]").
      { intros ???; apply Hnn. }
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
      { iApply (ec_eq with "He").
        eapply Gauss_Closed; OK.
      }
    }
    simpl.
    iIntros (v) "[%[%[%[%[-> [H1 [% H2]]]]]]]".
    wp_pures.
    iApply (pgl_wp_mono_frame (lazy_real ℓ vr ∗ ↯ (F (bzu_to_R b vz vr))) with "[] [H1 H2]").
    3: { iFrame. }
    2: { iApply (@wp_ToLazyReal _ _ E _ _); iPureIntro. done. }
    rewrite //=.
    iIntros (?) "[[Hr He] Happrox]".
    iExists (lazy_real ℓ vr), (bzu_to_R b vz vr).
    iFrame.
  Qed.

End Symmetric.
