From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real indicators.
Set Default Proof Using "Type*".
#[local] Open Scope R.


Section pmf.

  (* NB. Using nat instead of int so the SeriesC is a little bit easier to work with.
     All values bumped by 1. *)
  Definition C_μ (m : nat) : nat → R := fun n =>
    Iverson (eq 0) n * (1 / (2 * m + 2)) +
    Iverson (eq 1) n * (1 / (2 * m + 2)) +
    Iverson (eq 2) n * (m / (2 * m + 2)).

  Definition Bii_μ (k : nat) (x : R) : bool → R := fun b =>
    Iverson is_true b * (1 - (2*k+x)/(2*k+2)) + Iverson (not ∘ is_true) b * (1 - (2*k+x)/(2*k+2)).

  Definition S_μ0 (k : nat) (x y : R) : nat → R := fun n =>
    (y^n / fact n) * ((2*k+x)/(2*k+2))^n -
    (y^(n+1) / fact (n+1)) * ((2*k+x)/(2*k+2))^(n+1).

  Definition S_μ (k : nat) (x y : R) (N : nat) : nat → R := fun n =>
    Iverson (le N) n * S_μ0 k x y (n - N).

  Definition B_μ (k : nat) (x : R) : bool → R := fun b =>
    Iverson is_true b * (exp (-(2*k+x)/(2*k+2))) + Iverson (not ∘ is_true) b * (exp (-(2*k+x)/(2*k+2))).


End pmf.

Section credits.
  Import Hierarchy.

  Definition C_CreditV (F : nat → R) m :=
    (1 / (m + 2)) * F 0%nat +
    (1 / (m + 2)) * F 1%nat +
    (m / (m + 2)) * F 2%nat.

  Definition Bii_CreditV (F : bool → R) k x :=
    Bii_μ k x false * F false + Bii_μ k x true * F true.

  Definition Bii_g F x : R → R := fun r =>
    Iverson (Rle x) r * F true +
    Iverson (Rge x) r * F false.

  Definition Bii_h F x : nat → R := fun n =>
    Iverson (eq 0) n * F true +
    Iverson (eq 1) n * RInt (Bii_g F x) 0 1 +
    Iverson (eq 2) n * F false.

  Lemma C_CreditV_nn {F m} (Hnn : ∀ r, 0 <= F r) : 0 <= C_CreditV F m.
  Proof. Admitted.

  Lemma Bii_CreditV_nn {F k x} (Hnn : ∀ r, 0 <= F r) : 0 <= Bii_CreditV F k x.
  Proof. Admitted.

  Lemma Bii_h_nn {F k x} (Hnn : ∀ r, 0 <= F r) : 0 <= Bii_h F k x.
  Proof. Admitted.

  Lemma Bii_g_nn {F k x} (Hnn : ∀ r, 0 <= F r) : 0 <= x <= 1 → 0 <= Bii_g F k x.
  Proof. Admitted.

  Lemma Bii_f_expectation {F k x} : Bii_CreditV F k x = C_CreditV (Bii_h F x) (2 * k)%nat.
  Proof.
    rewrite /Bii_CreditV.
    rewrite /C_CreditV.
    rewrite /Bii_μ.
    rewrite /Bii_h.
  Admitted.

  Lemma Bii_g_correct {F x} : is_RInt (Bii_g F x) 0 1 (RInt (Bii_g F x) 0 1).
  Proof. Admitted.

End credits.


Section program.
  Context `{!erisGS Σ}.

  Definition C : val  :=
    λ: "m",
      let: "v" := rand ("m" + #1) in
      if: "v" = #0 then #0 else if: "v" = #1 then #1 else #2.

  Definition Bii : val :=
    λ: "k" "x",
      let: "f" := C (#2 * "k") in
      let: "r" := init #() in
      ("f" = #0) || (("f" = #1) && (cmp "x" "r" = #(-1))).

  Theorem wp_C {E F} (m : nat) (Hnn : ∀ r, 0 <= F r) :
    ↯(C_CreditV F m) -∗ WP C #m @ E {{ vn, ∃ n : nat, ⌜vn = #n ⌝ ∗ ⌜n = 0%nat \/ n = 1%nat \/ n = 2%nat⌝∗ ↯(F n) }}.
  Proof.
    iIntros "Hε".
    rewrite /C.
    wp_pures.

    (* I hate fin >:( *)
    have HF0 : (0 < (S (Z.to_nat (m + 1))))%nat by lia.
    have HF1 : (1 < (S (Z.to_nat (m + 1))))%nat by lia.
    pose F0 : fin (S (Z.to_nat (m + 1))) := Fin.of_nat_lt HF0.
    pose F1 : fin (S (Z.to_nat (m + 1))) := Fin.of_nat_lt HF1.
    pose C_F := fun (n : fin (S (Z.to_nat (m + 1)))) =>
      Iverson (eq F0) n * (1 / (m + 2) * F 0%nat) +
      Iverson (eq F1) n * (1 / (m + 2) * F 1%nat) +
      Iverson (fun n' => ¬ n' = F0 ∧ ¬ n' = F1) n * (m / (m + 2) * F 2%nat).
    wp_apply (wp_couple_rand_adv_comp _ _ _ _ C_F with "Hε").
    { admit. }
    { rewrite /C_CreditV.
      unfold C_F.
      admit. }
    iIntros (n) "Hε".
    (* Probably true, stupid fin *)
  Admitted.

  Theorem wp_Bii {E F} (k : nat) xα x (Hnn : ∀ r, 0 <= F r) :
    ↯(Bii_CreditV F k x) ∗ lazy_real xα x -∗
    WP Bii #k xα @ E {{ vb, ∃ b : bool, ⌜vb = #b ⌝ ∗ ↯(F b) ∗ lazy_real xα x }}.
  Proof.
    iIntros "(Hε & Hx)".
    rewrite /Bii.
    wp_pures.
    wp_bind (C _).
    iApply (pgl_wp_mono_frame _ with "[Hε] Hx"); last first.
    { replace (Z.mul 2 (Z.of_nat k)) with (Z.of_nat (2 * k)%nat) by lia.
      wp_apply (wp_C (F:=Bii_h F x)).
      { by intros ?; apply Bii_h_nn, Hnn. }
      { iApply (ec_eq with "Hε"); by rewrite Bii_f_expectation. }
    }
    iIntros (v) "(Hx & [%vn [-> [%Hc Hε]]])".
    destruct Hc as [->|[-> | ->]].
    { wp_pures.
      wp_apply wp_init; first done.
      iIntros (?) "?".
      wp_pures.
      iModIntro; iExists true; iFrame.
      iSplitR; first done.
      iApply (ec_eq with "Hε").
      rewrite /Bii_h//=.
      rewrite Iverson_True; [rewrite Rmult_1_l|done].
      rewrite Iverson_False; [rewrite Rmult_0_l|done].
      rewrite Iverson_False; [rewrite Rmult_0_l|done].
      lra.
    }
    { wp_pures.
      wp_apply wp_init; first done.
      iIntros (r) "Hr".
      iApply (wp_lazy_real_presample_adv_comp _ _ r _ (Bii_h F x 1) (Bii_g F x)); auto.
      { intros ??. apply Bii_g_nn; auto. }
      { rewrite /Bii_h.
        rewrite Iverson_False; [rewrite Rmult_0_l Rplus_0_l|simpl; lra].
        rewrite Iverson_True; [rewrite Rmult_1_l|done].
        rewrite Iverson_False; [rewrite Rmult_0_l Rplus_0_r|simpl; lra].
        exact Bii_g_correct.
      }
      iSplitL "Hr"; [done|].
      iSplitL "Hε"; [done|].
      iIntros (rv) "(Hε & Hr)".
      wp_pures.
      wp_apply (wp_cmp with "[Hr Hx]"); first iFrame.
      iIntros (cv) "(Hx & Hr & %Hc)".
      destruct Hc as [[-> Hc'] | [-> Hc']].
      { wp_pures.
        iModIntro; iExists _; iSplitR; first done.
        iFrame.
        rewrite /Bii_g.
        iPoseProof (ec_split _ _ with "Hε") as "(Hε & _)".
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
        rewrite Iverson_True; [|done].
        rewrite Rmult_1_l.
        done.
      }
      { wp_pures.
        iModIntro; iExists _; iSplitR; first done.
        iFrame.
        iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
        rewrite Iverson_True; [|lra].
        by rewrite Rmult_1_l.
      }
    }
    { wp_pures.
      wp_apply wp_init; first done.
      iIntros (?) "?".
      wp_pures.
      iModIntro; iExists false; iFrame.
      iSplitR; first done.
      iApply (ec_eq with "Hε").
      rewrite /Bii_h//=.
      rewrite Iverson_False; [rewrite Rmult_0_l|lra].
      rewrite Iverson_False; [rewrite Rmult_0_l|lra].
      rewrite Iverson_True; [rewrite Rmult_1_l|done].
      lra.
    }
  Qed.

End program.
