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

  Definition S_CreditV (F : nat → R) k x y N : R :=
    SeriesC (fun n => S_μ k x y N n * F n).

  Definition B_CreditV (F : bool → R) k x : R :=
    (exp (-(2*k+x)/(2*k+2))) * F true +
    (exp (-(2*k+x)/(2*k+2))) * F false.

  Definition Bii_g F x : R → R := fun r =>
    Iverson (Rle x) r * F true +
    Iverson (Rge x) r * F false.

  Definition Bii_h F x : nat → R := fun n =>
    Iverson (eq 0) n * F true +
    Iverson (eq 1) n * RInt (Bii_g F x) 0 1 +
    Iverson (eq 2) n * F false.

  Definition S_hz F k x N z : bool → R := fun b =>
    Iverson is_true b * F N +
    Iverson (not ∘ is_true) b * S_CreditV F k x z (N + 1).

  Definition S_g F k x y N : R → R := fun z =>
    Iverson (Rle y) z * F N +
    Iverson (Rge y) z * (Bii_μ k x false * S_hz F k x N z false + Bii_μ k x true * S_hz F k x N z true).

  Lemma C_CreditV_nn {F m} (Hnn : ∀ r, 0 <= F r) : 0 <= C_CreditV F m.
  Proof. Admitted.

  Lemma Bii_CreditV_nn {F k x} (Hnn : ∀ r, 0 <= F r) : 0 <= Bii_CreditV F k x.
  Proof. Admitted.

  Lemma S_CreditV_nn {F k x y N} (Hnn : ∀ r, 0 <= F r) : 0 <= S_CreditV F k x y N.
  Proof. Admitted.

  Lemma B_CreditV_nn {F k x} (Hnn : ∀ r, 0 <= F r) : 0 <= B_CreditV F k x.
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

  Lemma S_hz_nn {F k x N z w} (Hnn : ∀ r, 0 <= F r) : 0 <= S_hz F k x N z w.
  Proof. Admitted.

  Lemma S_g_nn {F k x z N r} (Hnn : ∀ r, 0 <= F r) : 0 <= S_g F k x z N r.
  Proof. Admitted.

  Lemma S_nn_1 {F k x z N} (Hnn : ∀ r, 0 <= F r) :
    0 <= Bii_μ k x false * S_hz F k x N z false + Bii_μ k x true * S_hz F k x N z true.
  Proof. Admitted.

  Lemma S_g_expectation {F k x y N} : is_RInt (S_g F k x y N) 0 1 (S_CreditV F k x y N).
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

  Definition S : val :=
    rec: "trial" "k" "x" "y" "N" :=
      let: "z" := init #() in
      if: (cmp "y" "z" = #(-1)) || (Bii "k" "x") then "N" else "trial" "k" "x" "z" ("N" + #1%nat).

  Definition B : val :=
    λ: "k" "x", (S "k" "x" "x" #0%nat) `rem` #2 = #0.

  Theorem wp_C {E F} (m : nat) (Hnn : ∀ r, 0 <= F r) :
    ↯(C_CreditV F m) -∗ WP C #m @ E {{ vn, ∃ n : nat, ⌜vn = #n ⌝ ∗ ⌜n = 0%nat \/ n = 1%nat \/ n = 2%nat⌝∗ ↯(F n) }}.
  Proof.
    iIntros "Hε".
    rewrite /C.
    wp_pures.
    (* I hate fin >:( *)
    have HF0 : (0 < (Coq.Init.Datatypes.S (Z.to_nat (m + 1))))%nat by lia.
    have HF1 : (1 < (Coq.Init.Datatypes.S (Z.to_nat (m + 1))))%nat by lia.
    pose F0 : fin (Coq.Init.Datatypes.S  (Z.to_nat (m + 1))) := Fin.of_nat_lt HF0.
    pose F1 : fin (Coq.Init.Datatypes.S (Z.to_nat (m + 1))) := Fin.of_nat_lt HF1.
    pose C_F := fun (n : fin (Coq.Init.Datatypes.S  (Z.to_nat (m + 1)))) =>
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

  Theorem wp_S {E F} (k : nat) xα x (Hnn : ∀ r, 0 <= F r) :
    ∀ yα y N , ↯(S_CreditV F k x y N) ∗ lazy_real xα x ∗ lazy_real yα y -∗
    WP S #k xα yα #N @ E {{ vn, ∃ n : nat, ⌜vn = #n ⌝ ∗ ↯(F n) ∗ lazy_real xα x }}.
  Proof.
    iLöb as "IH".
    iIntros (yα y N) "(Hε & Hx & Hy)".
    rewrite {2}/S.
    wp_pures.
    wp_apply wp_init; first done.
    iIntros (zα) "Hz".
    iApply (wp_lazy_real_presample_adv_comp _ _ zα _ (S_CreditV F k x y N) (S_g F k x y N)); auto.
    { intros ??. apply S_g_nn; auto. }
    { apply S_g_expectation. }
    iSplitL "Hz"; [done|].
    iSplitL "Hε"; [done|].
    iIntros (z) "(Hε & Hz)".
    wp_pures.
    wp_apply (wp_cmp with "[Hy Hz]"); first iFrame.
    iIntros (c) "(Hy & Hz & %Hcmp)".
    destruct Hcmp as [[-> Hc'] | [-> Hc']].
    { wp_pures.
      iModIntro; iExists N; iFrame; iSplitR; first done.
      rewrite /S_g.
      iPoseProof (ec_split _ _ with "Hε") as "(Hε & _)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply S_nn_1; auto ]. }
      rewrite Iverson_True; [rewrite Rmult_1_l|done].
      done.
    }
    { wp_pures.
      rewrite /S_g.
      iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply S_nn_1; auto ]. }
      rewrite Iverson_True; [rewrite Rmult_1_l|lra].
      wp_bind (Bii _ _).
      iApply (pgl_wp_mono_frame (□ _ ∗ _  ∗ _)%I with "[Hx Hε ] [IH Hy Hz]"); last first.
      { iSplitR; first iExact "IH". iSplitL "Hy"; first iExact "Hy". iExact "Hz". }
      { iApply (@wp_Bii _ (S_hz F k x N z)); last iFrame.
        iIntros (?). apply S_hz_nn; auto. }
      iIntros (bv) "((#IH & Hy & Hz) & [%b [-> [Hε Hx]]])".
      destruct b.
      { wp_pures.
        iModIntro; iExists N; iFrame; iSplitR; first done.
        rewrite /S_hz.
        iPoseProof (ec_split _ _ with "Hε") as "(Hε & _)".
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply S_CreditV_nn; auto ]. }
        rewrite Iverson_True; [rewrite Rmult_1_l|intuition].
        done.
      }
      { do 2 wp_pure.
        rewrite -Nat2Z.inj_add.
        iApply "IH".
        iFrame.
        rewrite /S_hz.
        iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply S_CreditV_nn; auto ]. }
        rewrite Iverson_True; [rewrite Rmult_1_l|intuition].
        done.
      }
    }
  Qed.

  Theorem wp_B {E F} (k : nat) xα x (Hnn : ∀ r, 0 <= F r) :
    ↯(B_CreditV F k x) ∗ lazy_real xα x  -∗
    WP B #k xα @ E {{ vb, ∃ b : bool, ⌜vb = #b ⌝ ∗ ↯(F b) ∗ lazy_real xα x }}.
  Proof.
    iIntros "(Hε & Hx)".
    rewrite /B.
    wp_pures.
    wp_bind (S _ _ _ _).
    iApply (pgl_wp_mono with "[Hx Hε] "); last first.
    { iApply wp_S.
      (* TODO: Credit distribution for B *)
      Unshelve.

      (* TODO: FIXME: lazy_real being duplicated is a problem!
         We could add a wrapper function that does the 0th iterate, and only calls S
         once a fresh y is allocated.

         Note that x must be in the precondition and postcondition of this lemma, but
         y can be thrown away. *)
    (* iIntros (v) "[%n [-> [Hε Hx]]]". *)
  Admitted.

End program.
