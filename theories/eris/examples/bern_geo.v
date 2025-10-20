From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real indicators real_decr_trial.
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

  Lemma Geo_CreditV_nn {F 𝛾 N} (Hnn : ∀ r, 0 <= F r) (H𝛾 : 0 <= 𝛾 <= 1) : 0 <= Geo_CreditV F 𝛾 N.
  Proof. Admitted.

  Local Definition g (F : nat → R) (𝛾 : R) (N : nat) : bool → R := fun b =>
    Iverson is_true b * Geo_CreditV F 𝛾 (N + 1) +
    Iverson (not ∘ is_true) b * F N.

  Local Lemma g_nn {F 𝛾 N b} (Hnn : ∀ r, 0 <= F r) (H𝛾 : 0 <= 𝛾 <= 1) : 0 <= g F 𝛾 N b.
  Proof. Admitted.

  Local Lemma g_expectation {F 𝛾 N} :
    Geo_CreditV F 𝛾 N = 𝛾 * Geo_CreditV F 𝛾 (N + 1) + (1 - 𝛾) * F N.
  Proof. Admitted.

End credits.

Section program.
  Context `{!erisGS Σ}.
  Context (e : val).
  Context (𝛾 : R) (H𝛾 : 0 <= 𝛾 <= 1).
  Context (wp_e : forall E (F : bool → R), (∀ b, 0 <= F b) →
            (⊢ ((↯(𝛾 * F true + (1 - 𝛾) * F false) -∗
                 WP e #() @ E {{ vb, ∃ b : bool, ⌜vb = #b ⌝ ∗ ↯(F b) }}) : iProp Σ))).

  Definition GeoTrial : val := rec: "trial" "N" := if: e #() then "trial" ("N" + #1) else "N".

  Theorem wp_Geo {E} F {N} (Hnn : ∀ r, 0 <= F r) :
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
    { iApply (wp_e E (g F 𝛾 N)); [intro b; by apply (g_nn Hnn H𝛾) | ].
      rewrite /g.
      rewrite Iverson_True; [|intuition]; rewrite Iverson_False; [|intuition].
      rewrite Iverson_False; [|intuition]; rewrite Iverson_True; [|intuition].
      do 2 rewrite Rmult_1_l Rmult_0_l.
      rewrite Rplus_0_r Rplus_0_l.
      by rewrite g_expectation.
    }
    iIntros (v) "(#IH & [%b [-> Hε]])".
    destruct b.
    { wp_pure.
      wp_pure.
      iSpecialize ("IH" $!(Init.Nat.add N 1)  with "[Hε]"); last (rewrite Nat2Z.inj_add; iApply "IH").
      rewrite /g.
      rewrite Iverson_True; [|intuition]; rewrite Iverson_False; [|intuition].
      by rewrite Rmult_1_l Rmult_0_l Rplus_0_r.
    }
    { wp_pures.
      iModIntro; iExists N.
      iSplitR; first done.
      rewrite /g.
      rewrite Iverson_False; [|intuition]; rewrite Iverson_True; [|intuition].
      by rewrite Rmult_1_l Rmult_0_l Rplus_0_l.
    }
  Qed.

End program.
