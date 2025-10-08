From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real indicators.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Section pmf.

  (* The PMF for lazyGeoR starting with N=0 *)
  Definition μ0 (x : R) (n : nat) : R :=
    ((x ^ n) / fact n) - ((x ^ (n + 1)) / fact (n + 1)).

  (* The PMF for the trial starting at 0, over the integers *)
  Definition μZ (x : R) (z : Z) : R :=
    Iverson (Z.le 0%Z) z * μ0 x (Z.to_nat z).

  (* The PMF for lazyGeoR starting with N=i *)
  Definition μ (x : R) (i n : nat) : R :=
    Iverson (uncurry le) (i, n) * μ0 x (n - i).

  Theorem μ_not_supp {x i n} (H : lt n i) : μ x i n = 0.
  Proof. rewrite /μ Iverson_False //=; [lra|lia]. Qed.

  Theorem μ_supp {x i n} (H : ¬ lt n i) : μ x i n = μ0 x (n - i).
  Proof. rewrite /μ Iverson_True //=; [lra|lia]. Qed.

  Theorem μ_base {x n} : μ x 0 n = μ0 x n.
  Proof. rewrite μ_supp; [f_equal; lia| lia]. Qed.

  Lemma μ0nn {x n} : 0 <= μ0 x n.
  Proof. rewrite /μ0. Admitted.

  Lemma μnn {x i n} : 0 <= μ x i n.
  Proof. rewrite /μ. apply Rmult_le_pos; [apply Iverson_nonneg|apply μ0nn]. Qed.

End pmf.

Section credits.
  Import Hierarchy.

  (* Expected number of credits to execute lazyGeoR i x *)
  Definition CreditV (F : nat → R) (i : nat) (x : R) : R :=
    SeriesC (fun n : nat => μ x i n * F n).

  Definition CreditV0 (F : Z → R) (x : R) : R :=
    SeriesC (fun z : Z => μZ x z * F z).

  (* Credit distribution function *)
  Definition g (F : nat → R) (i : nat) (x : R) : R → R := fun y =>
    Iverson (uncurry Rle) (y, x) * CreditV F (i + 1) y +
    Iverson (uncurry Rge) (y, x) * F i.

  Lemma CreditV_nonneg {F i x} (Hnn : ∀ n, 0 <= F n) : 0 <= CreditV F i x.
  Proof. rewrite /CreditV. apply SeriesC_ge_0'. intro n. apply Rmult_le_pos; [apply μnn |apply Hnn]. Qed.

  Lemma g_nonneg {F N rx r} (Hnn : ∀ n, 0 <= F n) : 0 <= g F N rx r.
  Proof.
    rewrite /g. apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg|]).
    { apply CreditV_nonneg, Hnn. }
    { apply Hnn. }
  Qed.

  Theorem g_expectation {F N rx} : is_RInt (g F N rx) 0 1 (CreditV F N rx).
  Proof.
  Admitted.

End credits.


Section trial.
  Context `{!erisGS Σ}.

  (* Tail-recursive geometric trial, which allocates new lazy reals in the loop. *)
  Definition lazyGeoR : val :=
    rec: "trial" "N" "x" :=
      let: "y" := init #() in
      if: (cmp "y" "x" = #(-1)) then
        "trial" ("N" + #1) "y" (* y < x *)
      else
        "N".

  Lemma wp_lazyGeoR_gen (F : nat → R) (Hnn : ∀ n, 0 <= F n) E :
    ⊢ ∀ N x rx, lazy_real x rx ∗ ↯ (CreditV F N rx) -∗ WP lazyGeoR #N x @ E {{ z, ∃ n : nat, ⌜z = #n⌝ ∗ ↯ (F n) }}.
  Proof.
    iLöb as "IH".
    rewrite {2}/lazyGeoR.
    iIntros (N x rx) "(Hx & Hε)".
    do 3 wp_pure.
    wp_apply wp_init; first done.
    iIntros (y) "Hv".
    iApply (wp_lazy_real_presample_adv_comp _ _ y _ (CreditV F N rx) (g F N rx)); auto.
    { intros ??. by apply g_nonneg, Hnn. }
    { exact g_expectation. }
    iFrame.
    iIntros (ry) "(Hε & Hy)".
    wp_pures.
    wp_apply (wp_cmp with "[Hx Hy]"); first iFrame.
    iIntros (vcmp) "(Hy & Hx & [[%Hcmp %Hie]|[%Hcmp %Hie]])".
    - rewrite Hcmp//=.
      do 3 wp_pure.
      rewrite /lazyGeoR.
      replace ((Z.add (Z.of_nat N) 1)) with (Z.of_nat (Nat.add N 1)) by lia.
      iApply "IH".
      iFrame.
      rewrite /g.
      iPoseProof (ec_split _ _ with "Hε") as "(Hε & _)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply CreditV_nonneg, Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      rewrite Iverson_True; [by rewrite Rmult_1_l | rewrite /uncurry//=].
    - rewrite Hcmp//=.
      do 2 wp_pure.
      iModIntro.
      iExists N; iSplitR; first by iPureIntro.
      rewrite /g.
      iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply CreditV_nonneg, Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      rewrite Iverson_True; [by rewrite Rmult_1_l | rewrite /uncurry//=; lra].
  Qed.

  Definition lazyGeoR0 : expr := (lazyGeoR #0)%E.

  (* Version of the above spec we may want to use in the following proofs... describes the PMF over
     all integers. *)
  Lemma wp_lazyGeoR0 (F : Z → R) (Hnn : ∀ z, 0 <= F z) E :
    ⊢ ∀ x rx, lazy_real x rx ∗ ↯ (CreditV0 F rx) -∗ WP lazyGeoR0 x @ E {{ z, ∃ z' : Z, ⌜z = #z'⌝ ∗ ↯ (F z') }}.
  Proof.
    iIntros (x rx) "(Hr & Hε)".
    unfold lazyGeoR0.
    pose F' : nat → R := fun n => F n.
    iPoseProof (wp_lazyGeoR_gen F' $! 0%nat x rx with "[Hr Hε]") as "Hspec".
    { intro n. apply Hnn. }
    { replace (CreditV0 F rx) with (CreditV F' 0 rx); first iFrame.
      rewrite /CreditV0/CreditV.
      (* Split the series over the integers in half *)
      admit.
    }
    iApply pgl_wp_mono; [|iFrame].
    intro v.
    iStartProof.
    iIntros "[%n [% Hε]]".
    iExists n.
    iFrame. done.
  Admitted.

End trial.
