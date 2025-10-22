From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real indicators real_decr_trial bern_geo half_bern_neg_exp bern_iter selector.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Section pmf.
  Import Hierarchy.

  Definition Norm1 : R := SeriesC (fun (k : nat) => exp ((-k^2)/2)).

  Definition G1_μ : nat → R := fun k => exp ((-k^2)/2) / Norm1.

  Definition Norm2 : R := SeriesC (fun (k : nat) => RInt (fun x => exp ((-(x+k)^2)/2)) 0 1).

  Definition G2_μ : nat -> R → R := fun k x => exp ((-(x+k)^2)/2) / Norm2.

End pmf.


Section credits.
  Import Hierarchy.

  Definition G1_CreditV (F : nat → R) := SeriesC (fun (k : nat) => G1_μ k * F k).

  Definition G2_CreditV (F : nat → R → R) :=
    SeriesC (fun (k : nat) => RInt (fun x => G2_μ k x * F k x) 0 1).

  Definition G1_h (F : nat → R) (k : nat) : bool -> R :=
    fun b => Iverson is_true b * F k + Iverson (not ∘ is_true) b * G1_CreditV F.

  Definition G1_f (F : nat → R) : nat -> R := fun k =>
    (exp (-(k*(k-1))%nat/2)) * G1_h F k true + (1 - (exp (-(k*(k-1))%nat/2))) * G1_h F k false.

  Definition G2_s (F : nat → R → R) (k : nat) (x : R) : bool → R := fun b =>
     Iverson is_true b * F k x +
     Iverson (not ∘ is_true) b * G2_CreditV F.

  Definition G2_g (F : nat → R → R) (k : nat) : R → R := fun x =>
    (exp (-x*(2*k+x)/2)) * G2_s F k x true +
    (1 - exp (-x*(2*k+x)/2)) * G2_s F k x false.

  Definition G2_f (F : nat → R → R) : nat → R := fun k =>
     RInt (G2_g F k) 0 1.

  Lemma G1_CreditV_nn {F} (Hnn : ∀ r, 0 <= F r) : 0 <= G1_CreditV F.
  Proof. Admitted.

  Lemma G2_CreditV_nn {F} (Hnn : ∀ k r, 0 <= F k r) : 0 <= G2_CreditV F.
  Proof. Admitted.

  Lemma G1_h_nn {F k b} (Hnn : ∀ r, 0 <= F r) : 0 <= G1_h F k b.
  Proof. Admitted.

  Lemma G1_f_nn {F k} (Hnn : ∀ r, 0 <= F r) : 0 <= G1_f F k.
  Proof. Admitted.

  Lemma G1_f_expectation {F} : G1_CreditV F = Geo_CreditV (G1_f F) (exp (-1 / 2)) 0.
  Proof. Admitted.

  Lemma G2_s_nn {F k x b} : 0 <= G2_s F k x b.
  Proof. Admitted.

  Lemma G2_g_nn {F k x} : 0 <= G2_g F k x.
  Proof. Admitted.

  Lemma G2_f_nn {F k} : 0 <= G2_f F k.
  Proof. Admitted.

  Lemma G2_f_expectation {F} : G2_CreditV F = G1_CreditV (G2_f F).
  Proof. Admitted.

  Lemma G2_g_RInt {F k} : is_RInt (G2_g F k) 0 1 (G2_f F k).
  Proof. Admitted.

  (* TODO: Solve and move me *)
  Lemma Rexp_half_bound : 0 <= exp (-1 / 2) <= 1.
  Proof. Admitted.

  Local Lemma Rexp_ineq {z : R} {k : nat} : 0 <= exp (- z * (2 * k + z) / (2 * k + 2)) <= 1.
  Proof. Admitted.

  Local Lemma Rexp_eq {z : R} {k : nat} : exp (- z * (2 * k + z) / 2) = exp (- z * (2 * k + z) / (2 * k + 2)) ^ (k + 1).
  Proof. Admitted.

End credits.

Section program.
  Context `{!erisGS Σ}.

  Definition G1 : val :=
    rec: "trial" "_" :=
      let: "k" := GeoTrial BNEHalf #0 in
      if: IterTrial BNEHalf ("k" * ("k" - #1)) then "k" else "trial" #().

  Definition G2 : val :=
    rec: "trial" "_" :=
      let: "k" := G1 #() in
      let: "x" := init #() in
      if: IterTrial (λ: "_", B "k" "x") ("k" + #1) then ("x", "k") else "trial" #().

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
      iApply (wp_Iter BNEHalf (exp (-1 / 2)) _ True _ _ (F := G1_h F n)).
      { by intros ?; apply G1_h_nn, Hnn. }
      { iSplitL; [|done].
        iApply (ec_eq with "Hε").
        rewrite /G1_f/Iter_CreditV.
        f_equal; f_equal; rewrite exp_pow; repeat f_equal; lra.
      }
      Unshelve.
      { exact Rexp_half_bound. }
      { iIntros (E' F' HF') "(Hε & HI)".
        iFrame.
        iApply wp_BNEHalf; [done|].
        iApply (ec_eq with "Hε").
        rewrite /BNEHalf_CreditV/BNEHalf_μ.
        lra.
      }
    }
    iIntros (v) "(#IH & [%b [-> [Hε _]]])".
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

  Theorem wp_G2 {E F} (Hnn : ∀ x k , 0 <= F x k ) :
    ↯(G2_CreditV F) -∗
    WP G2 #() @ E {{ vp, ∃ k : nat, ∃ r : R, ∃ l : val, lazy_real l r  ∗ ⌜vp = PairV l #k ⌝ ∗ ↯(F k r) }}.
  Proof.
    rewrite /G2.
    iLöb as "IH".
    iIntros "Hε".
    wp_pures.
    wp_bind (G1 _).
    iApply (pgl_wp_mono_frame (□ _) with "[Hε] IH"); last first.
    { iApply (wp_G1 (F := G2_f F)).
      { intros ?; apply G2_f_nn; auto. }
      iApply (ec_eq with "Hε").
      apply G2_f_expectation.
    }
    iIntros (v) "(#IH & [%k [-> Hε]])".
    wp_pures.
    wp_apply wp_init; first done.
    iIntros (x) "Hx".
    iApply (wp_lazy_real_presample_adv_comp _ _ x _ (G2_f F k) (G2_g F k)); auto.
    { intros ??. apply G2_g_nn; auto. }
    { apply G2_g_RInt. }
    iFrame.
    iIntros (z) "(Hε & Hx)".
    wp_pures.
    wp_bind (IterTrial _ _).
    iApply (pgl_wp_mono_frame (□ _) with "[Hε Hx] IH"); last first.
    { rewrite /G2_g.
      replace (Z.add (Z.of_nat k) 1) with (Z.of_nat (k + 1)%nat) by lia.
      iApply (@wp_Iter _ _ _ (exp (- z * (2 * k + z) / (2*k+2))) _ (lazy_real x z) _ _ (G2_s F k z)).
      { intros ?. apply G2_s_nn. }
      { iFrame.
        iApply (ec_eq with "Hε").
        rewrite /Iter_CreditV.
        rewrite Rexp_eq.
        f_equal; f_equal.
      }
      Unshelve.
      { apply Rexp_ineq. }
      { iIntros (E' F' Hf') "(Hε & HI)".
        wp_pure.
        iApply wp_B; first done.
        rewrite /B_CreditV.
        iFrame.
      }
    }
    iIntros (v) "(#IH & [%b [-> [Hε Hx]]])".
    destruct b.
    { (* TODO: Keep access to the lazy real *)
      wp_pures.
      iModIntro; iExists k, z, x.
      iFrame.
      iSplitR; first done.
      rewrite /G2_s.
      iPoseProof (ec_split _ _ with "Hε") as "(Hε & _)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply G2_CreditV_nn, Hnn ]. }
      iApply (ec_eq with "Hε").
      rewrite Iverson_True; [lra|done].
    }
    { wp_pure.
      iApply "IH".
      rewrite /G2_s.
      iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply G2_CreditV_nn, Hnn ]. }
      iApply (ec_eq with "Hε").
      rewrite Iverson_True; [lra|done].
    }
  Qed.

End program.
