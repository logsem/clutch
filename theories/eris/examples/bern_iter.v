From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real indicators real_decr_trial.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Section pmf.

  Definition Iter_μ (𝛾 : R) (N : nat) : bool → R :=
    fun b => Iverson is_true b * 𝛾 ^ N  + Iverson (not ∘ is_true) b * (1 - 𝛾 ^ N).

End pmf.

Section credits.
  Import Hierarchy.

  Definition Iter_CreditV (F : bool → R) (𝛾 : R) (N : nat) : R :=
    ((𝛾 ^ N) * F true + (1 - (𝛾 ^ N)) * F false).

  Lemma Iter_CreditV_nn {F 𝛾 N} (Hnn : ∀ r, 0 <= F r) (H𝛾 : 0 <= 𝛾 <= 1) : 0 <= Iter_CreditV F 𝛾 N.
  Proof. Admitted.

  Definition g (F : bool → R) (𝛾 : R) (N : nat) : bool → R :=
    fun b => Iverson is_true b * Iter_CreditV F 𝛾 N + Iverson (not ∘ is_true) b * F false.

  Local Lemma g_nn {F 𝛾 N b} (Hnn : ∀ r, 0 <= F r) (H𝛾 : 0 <= 𝛾 <= 1) : 0 <= g F 𝛾 N b.
  Proof. Admitted.

  Local Lemma g_expectation {F 𝛾 N'} :
    (Iter_CreditV F 𝛾 (S N')) =  (𝛾 * g F 𝛾 N' true + (1 - 𝛾) * g F 𝛾 N' false).
  Proof.
    rewrite /Iter_CreditV.
    rewrite /g.
    rewrite Iverson_True; [|intuition].
    rewrite Iverson_False; [|intuition].
    rewrite Iverson_False; [|intuition].
    rewrite Iverson_True; [|intuition].
    rewrite /Iter_CreditV.
    repeat rewrite Rmult_1_l.
    repeat rewrite Rmult_0_l.
    repeat rewrite Rplus_0_l.
    repeat rewrite Rplus_0_r.
    rewrite Rmult_plus_distr_l.
    rewrite -Rmult_assoc tech_pow_Rmult.
    rewrite Rplus_assoc.
    f_equal.
    rewrite -Rmult_assoc Rmult_minus_distr_l Rmult_1_r tech_pow_Rmult.
    lra.
  Qed.

End credits.

Section program.
  Context `{!erisGS Σ}.
  Context (e : val).
  Context (𝛾 : R) (H𝛾 : 0 <= 𝛾 <= 1).
  Context (wp_e : forall E (F : bool → R), (∀ b, 0 <= F b) →
            (⊢ ((↯(𝛾 * F true + (1 - 𝛾) * F false) -∗
                 WP e #() @ E {{ vb, ∃ b : bool, ⌜vb = #b ⌝ ∗ ↯(F b) }}) : iProp Σ))).

  Definition IterTrial : val :=
    rec: "trial" "k" := if: "k" = #0 then #true else if: e #() then "trial" ("k" - #1) else #false.

  Theorem wp_Iter E {F N} (Hnn : ∀ r, 0 <= F r) :
    ↯(Iter_CreditV F 𝛾 N) -∗ WP IterTrial #N @ E {{ vb, ∃ b : bool, ⌜vb = #b ⌝ ∗ ↯(F b) }}.
  Proof.
    iStartProof.
    iInduction N as [|N'] "IH".
    { iIntros "Hε".
      rewrite /IterTrial.
      wp_pures.
      iModIntro; iExists true; iSplitR; try done.
      rewrite /Iter_CreditV.
      by rewrite pow_O Rminus_diag Rmult_0_l Rmult_1_l Rplus_0_r.
    }
    { iIntros "Hε".
      rewrite /IterTrial.
      wp_pures.
      wp_bind (e _).
      iApply (pgl_wp_mono_frame (□ _) with "[Hε] IH"); last first.
      { iApply (wp_e E (g F 𝛾 N')); [intro b; apply g_nn; done | ].
        by rewrite g_expectation.
      }
      iIntros (v) "(#IH & [%b [-> Hε]])".
      destruct b.
      { wp_pure.
        wp_pure.
        replace (Z.sub (Z.of_nat (S N')) 1) with (Z.of_nat N') by lia.
        iApply "IH".
        rewrite /g.
        rewrite Iverson_True; [|intuition]; rewrite Iverson_False; [|intuition].
        by rewrite Rmult_0_l Rmult_1_l Rplus_0_r.
      }
      { wp_pures.
        iModIntro; iExists false.
        iSplitR; first done.
        rewrite /g.
        rewrite Iverson_False; [|intuition]; rewrite Iverson_True; [|intuition].
        by rewrite Rmult_1_l Rmult_0_l Rplus_0_l.
      }
    }
  Qed.

End program.
