From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real real_decr_trial.
From clutch.eris.examples Require Import math.
From clutch.eris.examples.math Require Import iverson_tactics.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Section pmf.

  Definition Geo_μ (𝛾 : R) (N : nat) : nat → R :=
    fun n => Iverson (uncurry le) (N, n) * 𝛾 ^ (n - N) * (1 - 𝛾).

End pmf.

Section credits.
  Import Hierarchy.

  Definition Geo_CreditV (F : nat → R) (𝛾 : R) (N : nat) : R :=
    SeriesC (fun n => (F n) * Geo_μ 𝛾 N n).

  Lemma Geo_μnn {𝛾 N n} (H : 0 <= 𝛾 <= 1) : 0 <= Geo_μ 𝛾 (N + 1) n.
  Proof.
    rewrite /Geo_μ.
    apply Rmult_le_pos; [|lra].
    apply Iverson_Rmult_nonneg.
    apply pow_le.
    lra.
  Qed.

  Lemma Geo_CreditV_nn {F 𝛾 N} (Hnn : ∀ r, 0 <= F r) (H𝛾 : 0 <= 𝛾 <= 1) : 0 <= Geo_CreditV F 𝛾 N.
  Proof.
    rewrite /Geo_CreditV.
    apply SeriesC_ge_0'.
    intro n.
    apply Rmult_le_pos; [auto|].
    rewrite /Geo_μ.
    apply Rmult_le_pos; [|lra].
    apply Iverson_Rmult_nonneg.
    apply pow_le.
    lra.
  Qed.

  Local Definition g (F : nat → R) (𝛾 : R) (N : nat) : bool → R := fun b =>
    Iverson is_true b * Geo_CreditV F 𝛾 (N + 1) +
    Iverson (not ∘ is_true) b * F N.

  Local Lemma g_nn {F 𝛾 N b} (Hnn : ∀ r, 0 <= F r) (H𝛾 : 0 <= 𝛾 <= 1) : 0 <= g F 𝛾 N b.
  Proof.
    rewrite /g. apply Rplus_le_le_0_compat;
      apply Iverson_Rmult_nonneg; [apply Geo_CreditV_nn; auto | auto].
  Qed.

  Local Lemma g_expectation {F 𝛾 N M} (Hnn : ∀ r, 0 <= F r <= M) (* (Hex : ex_seriesC F) *) (H𝛾 : 0 <= 𝛾 <= 1) :
    Geo_CreditV F 𝛾 N = 𝛾 * Geo_CreditV F 𝛾 (N + 1) + (1 - 𝛾) * F N.
  Proof.
    rewrite/Geo_CreditV.
    rewrite -SeriesC_scal_l.
    replace (λ x : nat, 𝛾 * (F x * Geo_μ 𝛾 (N + 1) x)) with (λ x : nat, F x * (𝛾 * Geo_μ 𝛾 (N + 1) x)); last first.
    { apply functional_extensionality; intros ?. lra. }
    replace (1 - 𝛾) with (Geo_μ 𝛾 N N); last first.
    { rewrite /Geo_μ.
      rewrite Nat.sub_diag pow_O.
      rewrite Iverson_True; last (simpl; lia).
      lra.
    }
    replace (Geo_μ 𝛾 N N * F N) with
            (SeriesC (fun n : nat => Iverson (fun x => x = N) n * (F n * Geo_μ 𝛾 N n))); last first.
    { rewrite (SeriesC_Iverson_singleton N); [lra|intuition]. }
    rewrite -SeriesC_plus.
    3: {
      rewrite -ex_seriesC_nat.
      apply ex_series_eventually0.
      exists (N + 1)%nat.
      intros n Hn.
      rewrite Iverson_False; [lra|lia].
    }
    2: {
      apply (ex_seriesC_le _ (λ x : nat, M * (𝛾 * Geo_μ 𝛾 (N + 1) x))).
      { intros n.
        split.
        { apply Rmult_le_pos; [apply Hnn|].
          apply Rmult_le_pos; OK.
          apply Geo_μnn.
          OK.
        }
        { apply Rmult_le_compat; OK.
          { apply Hnn. }
          { apply Rmult_le_pos; OK. apply Geo_μnn. OK. }
          { apply Hnn. }
        }
      }
      { apply ex_seriesC_scal_l.
        rewrite /Geo_μ.
        apply (ex_SeriesC_nat_shiftN_r (N + 1)%nat).
        rewrite /compose//=.
        replace (λ x : nat, 𝛾 * (Iverson (uncurry le) ((N + 1)%nat, (x + (N + 1))%nat) * 𝛾 ^ (x + (N + 1) - (N + 1)) * (1 - 𝛾)))
           with (λ x : nat, 𝛾 ^ (x + 1) * (1 - 𝛾)); last first.
        { funexti.
          replace (x + (N + 1) - (N + 1))%nat with x by OK.
          rewrite Iverson_True; [|rewrite /uncurry; OK].
          replace (x + 1)%nat with (S x) by OK.
          simpl. OK. }
        replace (λ x : nat, 𝛾 ^ (x + 1) * (1 - 𝛾)) with ((λ x : nat, 𝛾 ^ x * (1 - 𝛾)) ∘ S); last first.
        { funexti. rewrite /uncurry//=. replace (x + 1)%nat with (S x) by OK. simpl; OK. }
        apply ex_SeriesC_nat_shift.
        apply Geo_ex_SeriesC; OK.
      }
    }
    f_equal; apply functional_extensionality; intros n.
    rewrite /Iverson.
    case_decide.
    { rewrite /Geo_μ.
      rewrite Iverson_True; [|simpl; lia].
      rewrite Iverson_False; [|simpl; lia].
      lra.
    }
    { rewrite Rmult_0_l Rplus_0_r.
      rewrite /Geo_μ.
      rewrite {1}/Iverson//=.
      case_decide.
      { rewrite Iverson_True; [|simpl; lia].
        f_equal.
        rewrite Rmult_1_l Rmult_1_l.
        rewrite -Rmult_assoc; f_equal.
        rewrite tech_pow_Rmult.
        f_equal. lia.
    }
    rewrite Iverson_False; [|simpl; lia].
    lra.
    }
  Qed.

End credits.

Section program.
  Context `{!erisGS Σ}.
  Context (e : val).
  Context (𝛾 : R) (H𝛾 : 0 <= 𝛾 <= 1).
  Context (wp_e : forall E (F : bool → R), (∀ b, 0 <= F b) →
            (⊢ ((↯(𝛾 * F true + (1 - 𝛾) * F false) -∗
                 WP e #() @ E {{ vb, ∃ b : bool, ⌜vb = #b ⌝ ∗ ↯(F b) }}) : iProp Σ))).

  Definition GeoTrial : val := rec: "trial" "N" := if: e #() then "trial" ("N" + #1) else "N".

    Theorem wp_Geo {M} {E} F {N} (Hnn : ∀ r, 0 <= F r <= M) (* (Hex : ex_seriesC F) *) :
    ↯(Geo_CreditV F 𝛾 N) -∗ WP GeoTrial #N @ E {{ vn, ∃ n : nat, ⌜vn = #n ⌝ ∗ ↯(F n) }}.
  Proof.
    revert N.
    iStartProof.
    iLöb as "IH".
    iIntros (N) "Hε".
    rewrite /GeoTrial.
    wp_pure.
    wp_bind (e _).
    iApply (pgl_wp_mono_frame (□ _) with "[Hε] IH"); last first.
    { iApply (wp_e E (g F 𝛾 N)); [intro b; apply (g_nn); OK | ].
      { apply Hnn. }
      rewrite /g. simp_iverson.
      erewrite g_expectation; OK.
    }
    iIntros (v) "(#IH & [%b [-> Hε]])".
    destruct b.
    { wp_pure.
      wp_pure.
      iSpecialize ("IH" $!(Init.Nat.add N 1)  with "[Hε]"); last (rewrite Nat2Z.inj_add; iApply "IH").
      rewrite /g. by simp_iverson.
    }
    { wp_pures.
      iModIntro; iExists N.
      iSplitR; first done.
      rewrite /g. by simp_iverson.
    }
  Qed.

End program.
