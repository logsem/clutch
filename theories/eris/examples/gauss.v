From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real indicators real_decr_trial bern_geo half_bern_neg_exp bern_iter.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Section pmf.

  Definition Norm1 : R := SeriesC (fun (k : nat) => exp ((-k^2)/2)).

  Definition G1_μ : nat → R := fun k => exp ((-k^2)/2) / Norm1.

End pmf.


Section credits.
  Import Hierarchy.

  Definition G1_CreditV (F : nat → R) := SeriesC (fun (k : nat) => G1_μ k * F k).

  Definition G1_h (F : nat → R) (k : nat) : bool -> R :=
    fun b => Iverson is_true b * F k + Iverson (not ∘ is_true) b * G1_CreditV F.

  Definition G1_f (F : nat → R) : nat -> R := fun k =>
    (exp (-k*(k-1)/2)) * G1_h F k true + (1 - (exp (-k*(k-1)/2))) * G1_h F k false.

  Lemma G1_CreditV_nn {F} (Hnn : ∀ r, 0 <= F r) : 0 <= G1_CreditV F.
  Proof. Admitted.

  Lemma G1_h_nn {F k b} (Hnn : ∀ r, 0 <= F r) : 0 <= G1_h F k b.
  Proof. Admitted.

  Lemma G1_f_nn {F k} (Hnn : ∀ r, 0 <= F r) : 0 <= G1_f F k.
  Proof. Admitted.
  (*
  Lemma G1_expectation_1 {F} : G1_CreditV F = Geo_CreditV F (BNEHalf_μ true) 0.
  Proof. Admitted.
  *)

(*
  Local Lemma G1_h_expectation {F 𝛾 N'} :
    (Iter_CreditV F 𝛾 (S N')) =  (𝛾 * g F 𝛾 N' true + (1 - 𝛾) * g F 𝛾 N' false).
  Proof.
  Qed.
*)

End credits.

Section program.
  Context `{!erisGS Σ}.

  Definition G1 : val :=
    rec: "trial" "_" :=
      let: "k" := GeoTrial BNEHalf #0 in
      if: IterTrial BNEHalf ("k" * ("k" - #1)) then "k" else "trial" #().

  Theorem wp_G1 {E F} (Hnn : ∀ r, 0 <= F r) :
    ↯(G1_CreditV F) -∗ WP G1 #() @ E {{ vn, ∃ n : nat, ⌜vn = #n ⌝ ∗ ↯(F n) }}.
  Proof.
    iStartProof.
    iLöb as "IH".
    iIntros "Hε".
    rewrite /G1.
    wp_pures.
    wp_bind (GeoTrial BNEHalf _).
    iApply (pgl_wp_mono_frame (□ _) with "[Hε] IH"); last first.
    { rewrite -Nat2Z.inj_0.
      wp_apply (wp_Geo _ (exp (-1 / 2)) _  _ (G1_f F)).
      { admit. }
      { admit. }
    }
    iIntros (v) "(#IH & [%n [-> Hε]])".
    wp_pures.
    wp_bind (IterTrial BNEHalf _).
    iApply (pgl_wp_mono_frame (□ _) with "[Hε] IH"); last first.
    { wp_pures.
      replace (Z.mul n (Z.sub n 1)) with (Z.of_nat (Nat.mul n (Nat.sub n 1))) by admit.
      iApply (wp_Iter BNEHalf (exp (-1 / 2)) _ _ _ (F := G1_h F n)).
      { admit. }
      { admit. }
    }
    iIntros (v) "(#IH & [%b [-> Hε]])".
    destruct b.
    { wp_pures.
      iModIntro.
      iExists n.
      iSplitR; first done.
      admit. }
    { wp_pure.
      iApply "IH".
      admit.
    }
  Admitted.

End program.
