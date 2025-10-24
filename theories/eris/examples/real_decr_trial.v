From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real indicators.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Section pmf.

  (* The PMF for lazyDecrR starting with N=0 *)
  Definition RealDecrTrial_μ0 (x : R) (n : nat) : R :=
    ((x ^ n) / fact n) - ((x ^ (n + 1)) / fact (n + 1)).

  (* The PMF for the trial starting at 0, over the integers *)
  Definition RealDecrTrial_μZ (x : R) (z : Z) : R :=
    Iverson (Z.le 0%Z) z * RealDecrTrial_μ0 x (Z.to_nat z).

  (* The PMF for lazyDecrR starting with N=i *)
  Definition RealDecrTrial_μ (x : R) (i n : nat) : R :=
    Iverson (uncurry le) (i, n) * RealDecrTrial_μ0 x (n - i).

  Theorem RealDecrTrial_μ_not_supp {x i n} (H : lt n i) : RealDecrTrial_μ x i n = 0.
  Proof. rewrite /RealDecrTrial_μ Iverson_False //=; [lra|lia]. Qed.

  Theorem RealDecrTrial_μ_supp {x i n} (H : ¬ lt n i) : RealDecrTrial_μ x i n = RealDecrTrial_μ0 x (n - i).
  Proof. rewrite /RealDecrTrial_μ Iverson_True //=; [lra|lia]. Qed.

  Theorem RealDecrTrial_μ_base {x n} : RealDecrTrial_μ x 0 n = RealDecrTrial_μ0 x n.
  Proof. rewrite RealDecrTrial_μ_supp; [f_equal; lia| lia]. Qed.

  Lemma RealDecrTrial_μ0nn {x n} (Hx : 0 <= x <= 1) : 0 <= RealDecrTrial_μ0 x n.
  Proof.
    rewrite /RealDecrTrial_μ0.
    apply error_credits.Rle_0_le_minus.
    replace (x ^ (n + 1) / fact (n + 1)) with ((x ^ (n + 1)) * (1 / fact (n + 1))) by lra.
    replace (x ^ n / fact n) with ((x ^ n) * (1 / fact n)) by lra.
    apply Rmult_le_compat.
    { apply pow_le; lra. }
    { apply Rcomplements.Rdiv_le_0_compat; [lra|]. apply INR_fact_lt_0. }
    { rewrite pow_add pow_1.
      rewrite -{2}(Rmult_1_l (x^n)) Rmult_comm.
      apply Rmult_le_compat; try lra.
      apply pow_le; lra. }
    rewrite Rdiv_1_l Rdiv_1_l.
    apply Rcomplements.Rinv_le_contravar.
    { apply INR_fact_lt_0. }
    { apply le_INR.
      apply fact_le.
      lia.
    }
  Qed.

  Lemma RealDecrTrial_μnn {x i n} (H : 0 <= x <= 1) : 0 <= RealDecrTrial_μ x i n.
  Proof. rewrite /RealDecrTrial_μ. apply Rmult_le_pos; [apply Iverson_nonneg|apply RealDecrTrial_μ0nn; auto]. Qed.

End pmf.

Section credits.
  Import Hierarchy.

  (* Expected number of credits to execute lazyDecrR i x *)
  Definition RealDecrTrial_CreditV (F : nat → R) (i : nat) (x : R) : R :=
    SeriesC (fun n : nat => RealDecrTrial_μ x i n * F n).

  Definition RealDecrTrial_CreditV0 (F : Z → R) (x : R) : R :=
    SeriesC (fun z : Z => RealDecrTrial_μZ x z * F z).

  (* Credit distribution function *)
  Definition g (F : nat → R) (i : nat) (x : R) : R → R := fun y =>
    Iverson (uncurry Rle) (y, x) * RealDecrTrial_CreditV F (i + 1) y +
    Iverson (uncurry Rge) (y, x) * F i.

  Lemma CreditV_nonneg {F i x} (Hnn : ∀ n, 0 <= F n) (H : 0 <= x <= 1) : 0 <= RealDecrTrial_CreditV F i x.
  Proof. rewrite /RealDecrTrial_CreditV. apply SeriesC_ge_0'. intro n. apply Rmult_le_pos; [apply RealDecrTrial_μnn; auto |apply Hnn]. Qed.

  Lemma g_nonneg {F N rx r} (Hnn : ∀ n, 0 <= F n) (H : 0 <= r <= 1) : 0 <= g F N rx r.
  Proof.
    rewrite /g. apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg|]).
    { apply CreditV_nonneg; auto. }
    { apply Hnn. }
  Qed.

  Lemma g_ex_RInt {F N rx} : ex_RInt (g F N rx) 0 1.
  Proof. Admitted.

  Lemma RInt_add {F1 F2 : R → R} {a b : R} (H1 : ex_RInt F1 a b) (H2 : ex_RInt F2 a b) :
    RInt F1 a b  + RInt F2 a b = RInt (fun x => F1 x + F2 x) a b.
  Proof. Admitted.

  Lemma RInt_Rmult {F : R → R} {a b r : R} : r * RInt F a b = RInt (fun x => r * F x) a b.
  Proof. Admitted.

  Lemma RInt_Iverson_ge {rx F} (Hrx : 0 <= rx <= 1) :
    RInt (λ x : R, Iverson (uncurry Rge) (x, rx) * F x) 0 1 =  RInt (λ x : R, F x) rx 1.
  Proof. Admitted.

  Lemma RInt_Iverson_le {rx F} (Hrx : 0 <= rx <= 1) :
    RInt (λ x : R, Iverson (uncurry Rle) (x, rx) * F x) 0 1 =  RInt (λ x : R, F x) 0 rx.
  Proof. Admitted.

  Lemma RInt_RealDecrTrial_μ {rx N n} :
    RInt (λ x : R, RealDecrTrial_μ x N n) 0 rx =
    Iverson (uncurry eq) (N, n) * (rx - rx ^ 2 / 2) +
    Iverson (uncurry lt) (N, n) * RealDecrTrial_μ rx N (n + 1).
  Proof.
    rewrite {1}/RealDecrTrial_μ.
    rewrite -RInt_Rmult.
    rewrite {1}/RealDecrTrial_μ0.
    rewrite {1}/Iverson//=.
    case_decide; last first.
    { rewrite Iverson_False; [|simpl; lia].
      rewrite Iverson_False; [|simpl; lia].
      lra. }
    { destruct (le_lt_eq_dec _ _ H).
      { rewrite Iverson_False; [|simpl; lia].
        rewrite Iverson_True; [|simpl; lia].
        rewrite Rmult_1_l Rmult_0_l Rmult_1_l.
        rewrite Rplus_0_l.
        rewrite /RealDecrTrial_μ.
        rewrite Iverson_True; [|simpl; lia].
        rewrite Rmult_1_l.
        rewrite /RealDecrTrial_μ0.
        (* Compute *)
        admit. }
      { rewrite Iverson_True; [|simpl; lia].
        rewrite Iverson_False; [|simpl; lia].
        rewrite Rmult_1_l Rmult_0_l Rmult_1_l.
        rewrite Rplus_0_r.
        rewrite e.
        (* Compute *)
        admit. }
    }
  Admitted.


  Theorem g_expectation {F N rx} (Hrx : 0 <= rx <= 1) : is_RInt (g F N rx) 0 1 (RealDecrTrial_CreditV F N rx).
  Proof.
    suffices H : RInt (g F N rx) 0 1 = RealDecrTrial_CreditV F N rx.
    { rewrite -H. apply (RInt_correct (V := R_CompleteNormedModule)), g_ex_RInt. }
    rewrite /g.
    rewrite -RInt_add.
    3: admit.
    2: admit.
    rewrite {1}/RealDecrTrial_CreditV.
    replace
      (λ x : R, Iverson (uncurry Rle) (x, rx) * SeriesC (λ n : nat, RealDecrTrial_μ x (N + 1) n * F n)) with
      (λ x : R, SeriesC (λ n : nat, Iverson (uncurry Rle) (x, rx) * RealDecrTrial_μ x (N + 1) n * F n)); last first.
    { apply functional_extensionality; intros ?.
      rewrite -SeriesC_scal_l.
      f_equal; apply functional_extensionality; intros ?.
      lra.
    }
    replace
      (RInt (λ x : R, SeriesC (λ n : nat, Iverson (uncurry Rle) (x, rx) * RealDecrTrial_μ x (N + 1) n * F n)) 0 1) with
      (SeriesC (λ n : nat, RInt (λ x : R, Iverson (uncurry Rle) (x, rx) * RealDecrTrial_μ x (N + 1) n * F n) 0 1)); last first.
    { (* Deploy the Foob *) admit. }
    rewrite (@RInt_Iverson_ge rx (fun x => F N) Hrx).
    rewrite RInt_const/scal//=/mult//=.
    replace
      (λ n : nat, RInt (λ x : R, Iverson (uncurry Rle) (x, rx) * RealDecrTrial_μ x (N + 1) n * F n) 0 1) with
      (λ n : nat, RInt (λ x : R, RealDecrTrial_μ x (N + 1) n * F n) 0 rx); last first.
    { apply functional_extensionality; intros n.
      rewrite -(@RInt_Iverson_le rx (fun x => RealDecrTrial_μ x (N + 1) n * F n) Hrx).
      f_equal. apply functional_extensionality; intros ?; lra. }
    replace
      (λ n : nat, RInt (λ x : R, RealDecrTrial_μ x (N + 1) n * F n) 0 rx) with
      (λ n : nat, F n * RInt (λ x : R, RealDecrTrial_μ x (N + 1) n) 0 rx); last first.
    { apply functional_extensionality; intros ?.
      admit.
    }
    replace
      (λ n : nat, F n * RInt (λ x : R, RealDecrTrial_μ x (N + 1) n) 0 rx) with
      (λ n : nat, F n * (Iverson (uncurry eq) ((N+1)%nat, n) * (rx - rx ^ 2 / 2) + Iverson (uncurry lt) ((N+1)%nat, n) * RealDecrTrial_μ rx (N+1)%nat (n + 1))); last first.
    { apply functional_extensionality; intros ?. by rewrite RInt_RealDecrTrial_μ. }
    rewrite /RealDecrTrial_CreditV.
    rewrite /RealDecrTrial_μ.
    rewrite /RealDecrTrial_μ0.
    (* ?? *)
  Admitted.

End credits.


Section trial.
  Context `{!erisGS Σ}.

  (* Tail-recursive geometric trial, which allocates new lazy reals in the loop. *)
  Definition lazyDecrR : val :=
    rec: "trial" "N" "x" :=
      let: "y" := init #() in
      if: (cmp "y" "x" = #(-1)) then
        "trial" ("N" + #1) "y" (* y < x *)
      else
        "N".

  Lemma wp_lazyDecrR_gen (F : nat → R) (Hnn : ∀ n, 0 <= F n) E :
    ⊢ ∀ N x rx, lazy_real x rx ∗ ⌜0 <= rx <= 1 ⌝ ∗ ↯ (RealDecrTrial_CreditV F N rx) -∗
                WP lazyDecrR #N x @ E {{ z, ∃ n : nat, ⌜z = #n⌝ ∗ ↯ (F n) ∗ lazy_real x rx }}.
  Proof.
    iLöb as "IH".
    rewrite {2}/lazyDecrR.
    iIntros (N x rx) "(Hx & % & Hε)".
    do 3 wp_pure.
    wp_apply wp_init; first done.
    iIntros (y) "Hv".
    iApply (wp_lazy_real_presample_adv_comp _ _ y _ (RealDecrTrial_CreditV F N rx) (g F N rx)); auto.
    { intros ??. apply g_nonneg; auto. }
    { apply g_expectation; auto. }
    iSplitL "Hv"; first done.
    iSplitL "Hε"; first done.
    iIntros (ry) "(% & Hε & Hy)".
    wp_pures.
    wp_apply (wp_cmp with "[Hx Hy]"); first iFrame.
    iIntros (vcmp) "(Hy & Hx & [[%Hcmp %Hie]|[%Hcmp %Hie]])".
    - rewrite Hcmp//=.
      do 3 wp_pure.
      rewrite /lazyDecrR.
      replace ((Z.add (Z.of_nat N) 1)) with (Z.of_nat (Nat.add N 1)) by lia.
      iSpecialize ("IH" $! (N+1)%nat y ry with "[Hy Hε]").
      { iFrame.
        iSplitR; first done.
        rewrite /g.
        iPoseProof (ec_split _ _ with "Hε") as "(Hε & _)".
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply CreditV_nonneg; auto]. }
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
        rewrite Iverson_True; [by rewrite Rmult_1_l | rewrite /uncurry//=].
      }
      iFrame.
      iApply pgl_wp_mono; last done.
      iIntros (?) "(%z & ? & ? & ?)"; iExists _; auto.
    - rewrite Hcmp//=.
      do 2 wp_pure.
      iModIntro.
      iExists N; iSplitR; first by iPureIntro.
      iSplitR "Hx"; last done.
      rewrite /g.
      iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply CreditV_nonneg; auto ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      rewrite Iverson_True; [by rewrite Rmult_1_l | rewrite /uncurry//=; lra].
  Qed.


End trial.
