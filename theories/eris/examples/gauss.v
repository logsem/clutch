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
    (exp (-(k*(k-1))%nat/2)) * G1_h F k true + (1 - (exp (-(k*(k-1))%nat/2))) * G1_h F k false.

  Lemma G1_CreditV_nn {F} (Hnn : ∀ r, 0 <= F r) : 0 <= G1_CreditV F.
  Proof. Admitted.

  Lemma G1_h_nn {F k b} (Hnn : ∀ r, 0 <= F r) : 0 <= G1_h F k b.
  Proof. Admitted.

  Lemma G1_f_nn {F k} (Hnn : ∀ r, 0 <= F r) : 0 <= G1_f F k.
  Proof. Admitted.

  Lemma G1_f_expectation {F} : G1_CreditV F = Geo_CreditV (G1_f F) (exp (-1 / 2)) 0.
  Proof. Admitted.

  (* TODO: Solve and move me *)
  Lemma Rexp_half_bound : 0 <= exp (-1 / 2) <= 1.
  Proof. Admitted.

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
      { by intros ?; apply G1_f_nn, Hnn. }
      { by rewrite G1_f_expectation. }
      Unshelve.
      { exact Rexp_half_bound. }
      { iIntros (E' F' HF') "Hε".
        iApply wp_BNEHalf; [done|].
        iApply (ec_eq with "Hε").
        rewrite /BNEHalf_CreditV/BNEHalf_μ.
        lra.
      }
    }
    iIntros (v) "(#IH & [%n [-> Hε]])".
    wp_pures.
    wp_bind (IterTrial BNEHalf _).
    iApply (pgl_wp_mono_frame (□ _) with "[Hε] IH"); last first.
    { wp_pures.
      replace (Z.mul n (Z.sub n 1)) with (Z.of_nat (Nat.mul n (Nat.sub n 1))); last first.
      { destruct n; [lia|].
        rewrite Nat2Z.inj_mul; f_equal.
        apply Nat2Z.inj_sub.
        lia.
      }
      iApply (wp_Iter BNEHalf (exp (-1 / 2)) _ _ _ (F := G1_h F n)).
      { by intros ?; apply G1_h_nn, Hnn. }
      { iApply (ec_eq with "Hε").
        rewrite /G1_f/Iter_CreditV.
        f_equal; f_equal; rewrite exp_pow; repeat f_equal; lra.
      }
      Unshelve.
      { exact Rexp_half_bound. }
      { iIntros (E' F' HF') "Hε".
        iApply wp_BNEHalf; [done|].
        iApply (ec_eq with "Hε").
        rewrite /BNEHalf_CreditV/BNEHalf_μ.
        lra.
      }
    }
    iIntros (v) "(#IH & [%b [-> Hε]])".
    destruct b.
    { wp_pures.
      iModIntro.
      iExists n.
      iSplitR; first done.
      iApply (ec_eq with "Hε").
      rewrite /G1_h.
      rewrite Iverson_True; [|intuition]; rewrite Iverson_False; [|intuition].
      by rewrite Rmult_1_l Rmult_0_l Rplus_0_r.
    }
    { wp_pure.
      iApply "IH".
      iApply (ec_eq with "Hε").
      rewrite /G1_h.
      rewrite Iverson_False; [|intuition]; rewrite Iverson_True; [|intuition].
      by rewrite Rmult_0_l Rmult_1_l Rplus_0_l.
    }
  Qed.

End program.
