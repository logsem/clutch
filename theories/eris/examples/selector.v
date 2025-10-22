From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real indicators half_bern_neg_exp.
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
    Iverson is_true b * (exp (-x*(2*k+x)/(2*k+2))) + Iverson (not ∘ is_true) b * (1 - exp (-x*(2*k+x)/(2*k+2))).


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

  Definition B_CreditV (F : bool → R) (k : nat) (x : R) : R :=
    (exp (-x*(2*k+x)/(2*k+2))) * F true +
    (1 - exp (-x*(2*k+x)/(2*k+2))) * F false.

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

  Definition B_g (F : bool → R) : nat → R := fun z =>
    Iverson Zeven z * F (true) +
    Iverson (not ∘ Zeven) z * F (false).

  Lemma C_CreditV_nn {F m} (Hnn : ∀ r, 0 <= F r) (Hm : 0 <= m) : 0 <= C_CreditV F m.
  Proof.
    rewrite /C_CreditV.
    apply Rplus_le_le_0_compat; [apply Rplus_le_le_0_compat |].
    { apply Rmult_le_pos; auto. apply Rle_mult_inv_pos; try lra. }
    { apply Rmult_le_pos; auto. apply Rle_mult_inv_pos; try lra. }
    { apply Rmult_le_pos; auto. apply Rle_mult_inv_pos; try lra. }
  Qed.

  Lemma Bii_μ_nn {k x b} (Hx : 0 <= x <= 1) : 0 <= Bii_μ k x b.
  Proof.
    rewrite /Bii_μ.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg| auto ]).
    { apply error_credits.Rle_0_le_minus.
      rewrite -Rcomplements.Rdiv_le_1.
      { apply Rplus_le_compat; [lra|lra]. }
      { apply Rplus_le_lt_0_compat; try lra.
        apply Rmult_le_pos; try lra.
        apply pos_INR. }
    }
    { apply error_credits.Rle_0_le_minus.
      rewrite -Rcomplements.Rdiv_le_1.
      { apply Rplus_le_compat; [lra|lra]. }
      { apply Rplus_le_lt_0_compat; try lra.
        apply Rmult_le_pos; try lra.
        apply pos_INR. }
    }
  Qed.


  Lemma S_μ0_nn {x k y x'} (Hx : 0 <= x <= 1) (Hy : 0 <= y <= 1) : 0 <= S_μ0 k x y x'.
  Proof.
    rewrite /S_μ0.
    apply error_credits.Rle_0_le_minus.
    apply Rmult_le_compat.
    { apply Rcomplements.Rdiv_le_0_compat.
      { apply pow_le; lra. }
      { apply INR_fact_lt_0. }
    }
    { apply pow_le.
      apply Rcomplements.Rdiv_le_0_compat.
      { apply Rplus_le_le_0_compat; [|lra]. apply Rmult_le_pos; [lra|apply pos_INR]. }
      { apply Rplus_le_lt_0_compat; [|lra]. apply Rmult_le_pos; [lra|apply pos_INR]. }
    }
    { apply Rmult_le_compat.
      { apply pow_le; lra. }
      { rewrite -(Rmult_1_l (/ _)).
        apply Rcomplements.Rdiv_le_0_compat; [lra|].
        apply INR_fact_lt_0.
      }
      { rewrite -(Rmult_1_r (y ^ x')).
        rewrite pow_add pow_1.
        apply Rmult_le_compat; try lra.
        apply pow_le; lra.
      }
      { apply Rcomplements.Rinv_le_contravar.
        { apply INR_fact_lt_0. }
        apply le_INR.
        apply fact_le.
        lia.
      }
    }
    {
      rewrite -(Rmult_1_r (_ ^ x')).
      rewrite pow_add pow_1.
      apply Rmult_le_compat; try lra.
      { apply pow_le.
        apply Rcomplements.Rdiv_le_0_compat.
        { apply Rplus_le_le_0_compat; [|lra]. apply Rmult_le_pos; [lra|apply pos_INR]. }
        { apply Rplus_le_lt_0_compat; [|lra]. apply Rmult_le_pos; [lra|apply pos_INR]. }
      }
      { apply Rcomplements.Rdiv_le_0_compat.
        { apply Rplus_le_le_0_compat; [|lra]. apply Rmult_le_pos; [lra|apply pos_INR]. }
        { apply Rplus_le_lt_0_compat; [|lra]. apply Rmult_le_pos; [lra|apply pos_INR]. }
      }
      { rewrite -Rcomplements.Rdiv_le_1.
        { apply Rplus_le_compat; [lra|lra]. }
        { apply Rplus_le_lt_0_compat; try lra.
          apply Rmult_le_pos; try lra.
          apply pos_INR. }
        }
      }
  Qed.

  Lemma S_μ_nn {x k y N x'} (Hx : 0 <= x <= 1) (Hy : 0 <= y <= 1) : 0 <= S_μ k x y N x'.
  Proof.
    rewrite /S_μ.
    apply Rmult_le_pos; first apply Iverson_nonneg.
    apply S_μ0_nn; auto.
  Qed.

  Lemma Bii_CreditV_nn {F k x} (Hnn : ∀ r, 0 <= F r) (Hx : 0 <= x <= 1) : 0 <= Bii_CreditV F k x.
  Proof.
    rewrite /Bii_CreditV.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Bii_μ_nn; auto | auto ]).
  Qed.

  Lemma S_CreditV_nn {F k x y N} (Hnn : ∀ r, 0 <= F r) (Hx : 0 <= x <= 1) (Hy : 0 <= y <= 1) : 0 <= S_CreditV F k x y N.
  Proof.
    rewrite /S_CreditV.
    apply SeriesC_ge_0'.
    intros x'.
    apply Rmult_le_pos; last auto.
    apply S_μ_nn; auto.
  Qed.

  Lemma B_CreditV_nn {F k x} (Hnn : ∀ r, 0 <= F r) (Hx : 0 <= x <= 1) : 0 <= B_CreditV F k x.
  Proof.
    rewrite /B_CreditV.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [| auto ]).
    { apply Rexp_range.
      apply Rcomplements.Rmult_le_0_r; first apply Rcomplements.Rmult_le_0_r.
      { lra. }
      { apply Rplus_le_le_0_compat; [|lra]. apply Rmult_le_pos; [lra|apply pos_INR]. }
      rewrite -(Rmult_1_l (/ _)).
      apply Rle_mult_inv_pos; [lra|].
      apply Rplus_le_lt_0_compat; [|lra].
      apply Rmult_le_pos; [lra|apply pos_INR].
    }
    { apply error_credits.Rle_0_le_minus.
      apply Rexp_range.
      apply Rcomplements.Rmult_le_0_r; first apply Rcomplements.Rmult_le_0_r.
      { lra. }
      { apply Rplus_le_le_0_compat; [|lra]. apply Rmult_le_pos; [lra|apply pos_INR]. }
      rewrite -(Rmult_1_l (/ _)).
      apply Rle_mult_inv_pos; [lra|].
      apply Rplus_le_lt_0_compat; [|lra].
      apply Rmult_le_pos; [lra|apply pos_INR].
    }
  Qed.

  Lemma Bii_g_ex_RInt {F k} (Hnn : ∀ r, 0 <= F r) : ex_RInt (Bii_g F k) 0 1.
  Proof. Admitted.

  Lemma Bii_g_nn {F k x} (Hnn : ∀ r, 0 <= F r) : 0 <= x <= 1 → 0 <= Bii_g F k x.
  Proof.
    intro H.
    rewrite /Bii_g.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg | auto ]).
  Qed.

  Lemma Bii_h_nn {F k x} (Hnn : ∀ r, 0 <= F r) : 0 <= Bii_h F k x.
  Proof.
    rewrite /Bii_h.
    apply Rplus_le_le_0_compat; first apply (Rplus_le_le_0_compat); apply Rmult_le_pos;
      try auto; try (apply Iverson_nonneg; auto).
    apply RInt_ge_0; try lra.
    { apply Bii_g_ex_RInt; auto. }
    intros ??.
    apply Bii_g_nn; auto.
    lra.
  Qed.

  Lemma Bii_g_correct {F x} : is_RInt (Bii_g F x) 0 1 (RInt (Bii_g F x) 0 1).
  Proof. Admitted.


  Lemma Bii_f_expectation {F k x} : Bii_CreditV F k x = C_CreditV (Bii_h F x) (2 * k)%nat.
  Proof.
    rewrite /Bii_CreditV.
    rewrite /C_CreditV.
    rewrite /Bii_μ.
    rewrite /Bii_h.
  Admitted.


  Lemma S_hz_nn {F k x N z w} (Hnn : ∀ r, 0 <= F r) (H : 0 <= x <= 1) (Hy : 0 <= z <= 1) : 0 <= S_hz F k x N z w.
  Proof.
    rewrite /S_hz.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg | auto ]).
    apply S_CreditV_nn; auto.
  Qed.

  Lemma S_g_nn {F k x z N r} (Hnn : ∀ r, 0 <= F r) (H : 0 <= x <= 1) (Hy : 0 <= r <= 1) : 0 <= S_g F k x z N r.
  Proof.
    rewrite /S_g.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg | auto ]).
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Bii_μ_nn; auto | auto ]).
    { apply S_hz_nn; auto. }
    { apply S_hz_nn; auto. }
  Qed.

  Lemma S_nn_1 {F k x z N} (Hnn : ∀ r, 0 <= F r) (H : 0 <= x <= 1) (Hz : 0 <= z <= 1) :
    0 <= Bii_μ k x false * S_hz F k x N z false + Bii_μ k x true * S_hz F k x N z true.
  Proof.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Bii_μ_nn; auto | auto ]).
    { apply S_hz_nn; auto. }
    { apply S_hz_nn; auto. }
  Qed.

  Lemma S_g_expectation {F k x y N} : is_RInt (S_g F k x y N) 0 1 (S_CreditV F k x y N).
  Proof. Admitted.

  Lemma B_g_nn {F b} (Hnn : ∀ r, 0 <= F r) :  0 <= B_g F b.
  Proof.
    rewrite /B_g.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg | auto ]).
  Qed.

  Lemma B_g_expectation {F k x} : B_CreditV F k x = S_CreditV (B_g F) k x x 0.
  Proof.
    rewrite /B_CreditV.
    rewrite /S_CreditV.
    rewrite /B_g.
    (* Split the series *)
    rewrite /S_μ.
    rewrite /S_μ0.
    (* Apply exp t.s. to both *)
  Admitted.

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

  (* The first iterate of S so that we do not need to duplicate x. All other iterates are fine. *)
  Definition S0 : val :=
    λ: "k" "x",
      let: "z" := init #() in
      if: (cmp "x" "z" = #(-1)) || (Bii "k" "x") then #0 else S "k" "x" "z" #1%nat.

  Definition B : val :=
    λ: "k" "x", (S0 "k" "x") `rem` #2 = #0.

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
    { intro n. rewrite /C_F.
      apply Rplus_le_le_0_compat; first apply (Rplus_le_le_0_compat); apply Rmult_le_pos;
        try auto; try (apply Iverson_nonneg; auto).
      all: apply Rmult_le_pos; auto; apply Rle_mult_inv_pos; try lra.
      { apply Rplus_le_lt_0_compat; [|lra]. apply pos_INR. }
      { apply Rplus_le_lt_0_compat; [|lra]. apply pos_INR. }
      { apply pos_INR. }
      { apply Rplus_le_lt_0_compat; [|lra]. apply pos_INR. }
    }
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
      iIntros (rv) "(% & Hε & Hr)".
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
    ∀ yα y N , ↯(S_CreditV F k x y N) ∗ lazy_real xα x ∗ lazy_real yα y ∗ ⌜0 <= x <= 1 ⌝ ∗ ⌜0 <= y <= 1⌝ -∗
    WP S #k xα yα #N @ E {{ vn, ∃ n : nat, ⌜vn = #n ⌝ ∗ ↯(F n) ∗ lazy_real xα x }}.
  Proof.
    iLöb as "IH".
    iIntros (yα y N) "(Hε & Hx & Hy & % & %)".
    rewrite {2}/S.
    wp_pures.
    wp_apply wp_init; first done.
    iIntros (zα) "Hz".
    iApply (wp_lazy_real_presample_adv_comp _ _ zα _ (S_CreditV F k x y N) (S_g F k x y N)); auto.
    { intros ??. apply S_g_nn; auto. }
    { apply S_g_expectation. }
    iSplitL "Hz"; [done|].
    iSplitL "Hε"; [done|].
    iIntros (z) "(% & Hε & Hz)".
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
        iFrame.
        iPureIntro; auto.
      }
    }
  Qed.

  Theorem wp_S0 {E F} (k : nat) xα x (Hnn : ∀ r, 0 <= F r) :
    ↯(S_CreditV F k x x 0) ∗ lazy_real xα x ∗ ⌜ 0 <= x <= 1 ⌝ -∗
    WP S0 #k xα @ E {{ vn, ∃ n : nat, ⌜vn = #n ⌝ ∗ ↯(F n) ∗ lazy_real xα x }}.
  Proof.
    iIntros "(Hε & Hx & %)".
    rewrite /S0.
    wp_pures.
    wp_apply wp_init; first done.
    iIntros (zα) "Hz".
    iApply (wp_lazy_real_presample_adv_comp _ _ zα _ (S_CreditV F k x x 0) (S_g F k x x 0)); auto.
    { intros ??. apply S_g_nn; auto. }
    { apply S_g_expectation. }
    iSplitL "Hz"; [done|].
    iSplitL "Hε"; [done|].
    iIntros (z) "(% & Hε & Hz)".
    wp_pures.
    wp_apply (wp_cmp with "[Hx Hz]"); first iFrame.
    iIntros (c) "(Hx & Hz & %Hcmp)".
    destruct Hcmp as [[-> Hc'] | [-> Hc']].
    { wp_pures.
      iModIntro; iExists 0%nat; iFrame; iSplitR; first done.
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
      iApply (pgl_wp_mono_frame (_ )%I with "[Hx Hε ] Hz"); last first.
      { iApply (@wp_Bii _ (S_hz F k x _ _)); last iFrame.
        iIntros (?). apply S_hz_nn; auto. }
      iIntros (bv) "(Hz & [%b [-> [Hε Hx]]])".
      destruct b.
      { wp_pures.
        iModIntro; iExists 0%nat; iFrame; iSplitR; first done.
        rewrite /S_hz.
        iPoseProof (ec_split _ _ with "Hε") as "(Hε & _)".
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply S_CreditV_nn; auto ]. }
        rewrite Iverson_True; [rewrite Rmult_1_l|intuition].
        done.
      }
      { wp_pure.
        iApply wp_S; auto.
        iFrame.
        rewrite /S_hz.
        iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply S_CreditV_nn; auto ]. }
        rewrite Iverson_True; [rewrite Rmult_1_l|intuition].
        iFrame. by iPureIntro.
      }
    }
  Qed.

  Theorem wp_B {E F} (k : nat) xα x (Hnn : ∀ r, 0 <= F r) :
    ↯(B_CreditV F k x) ∗ lazy_real xα x ∗ ⌜0 <= x <= 1 ⌝ -∗
    WP B #k xα @ E {{ vb, ∃ b : bool, ⌜vb = #b ⌝ ∗ ↯(F b) ∗ lazy_real xα x }}.
  Proof.
    iIntros "(Hε & Hx)".
    rewrite /B.
    wp_pures.
    wp_bind (S0 _ _).
    iApply (pgl_wp_mono with "[Hx Hε] "); last first.
    { iApply (wp_S0 (F:=B_g F)).
      { intros ?; apply B_g_nn; auto. }
      iFrame.
      iApply (ec_eq with "Hε").
      apply B_g_expectation.
    }
    iIntros (v) "[%n [-> [Hec Hx]]]".
    iFrame.
    wp_pures.
    iModIntro.
    case_bool_decide.
    { iExists true; iSplitR; first done.
      rewrite /B_g.
      iPoseProof (ec_split _ _ with "Hec") as "(Hε & _)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | auto ]. }
      iApply (ec_eq with "Hε").
      rewrite Iverson_True; [by rewrite Rmult_1_l|].
      inversion H as [H'].
      apply Z.rem_mod_eq_0 in H'; [|lia].
      by apply Zeven_bool_iff; rewrite Zeven_mod H' //.
    }
    { iExists false; iSplitR; first done.
      iPoseProof (ec_split _ _ with "Hec") as "(_ & Hε)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | auto ]. }
      iApply (ec_eq with "Hε").
      rewrite Iverson_True; [by rewrite Rmult_1_l|].
      rewrite //=.
      intro Hk; apply H. f_equal.
      apply Zeven_bool_iff in Hk.
      rewrite Zeven_mod in Hk.
      apply Zeq_bool_eq in Hk.
      apply (Z.rem_mod_eq_0 n 2 ) in Hk; [by f_equal|lia].
    }
  Qed.

End program.
