From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real indicators real_decr_trial.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Section pmf.
   Definition BNEHalf_μ (b : bool) : R :=
     Iverson is_true b * exp (-1/2)%R +
     Iverson (not ∘ is_true) b * (1 - exp (-1/2)%R).

End pmf.

Section credits.
  Import Hierarchy.

  Definition BNEHalf_CreditV (F : bool → R) : R :=
    (F true) * BNEHalf_μ true + (F false) * BNEHalf_μ false.

  Lemma BNEHalf_μ_nn {b} : 0 <= BNEHalf_μ b.
  Proof.
    rewrite /BNEHalf_μ.
    apply Rplus_le_le_0_compat.
    { apply Rmult_le_pos; [apply Iverson_nonneg| auto ]. apply Rexp_nn. }
    { apply Rmult_le_pos; [apply Iverson_nonneg| auto ].
      apply error_credits.Rle_0_le_minus.
      have ? := @Rexp_range (Rdiv (-1) 2).
      lra.
    }
  Qed.

  Lemma BNEHalf_CreditV_nn {F} (Hnn : ∀ r, 0 <= F r) : 0 <= BNEHalf_CreditV F.
  Proof.
    rewrite /BNEHalf_CreditV.
    apply Rplus_le_le_0_compat.
    { apply Rmult_le_pos; auto. apply BNEHalf_μ_nn. }
    { apply Rmult_le_pos; auto. apply BNEHalf_μ_nn. }
  Qed.

  Local Definition LiftF (F : bool -> R) : nat -> R :=
    fun n => F (Z.eqb (n `rem` 2)%Z 1%Z).

  Local Definition g (F : bool → R) : R → R := fun r =>
    Iverson (fun x => Rle x 0.5) r * RealDecrTrial_CreditV (LiftF F) 0 r +
    Iverson (fun x  => not (Rle x 0.5)) r * F (true).

  Local Lemma g_nn {F r} (Hnn : ∀ r, 0 <= F r) (Hr : 0 <= r <= 1) : 0 <= g F r.
  Proof.
    rewrite /g.
    apply Rplus_le_le_0_compat.
    { apply Rmult_le_pos; [apply Iverson_nonneg| auto ].
      apply CreditV_nonneg; auto.
      intros ?; rewrite /LiftF//=.
    }
    { apply Rmult_le_pos; [apply Iverson_nonneg| auto ]. }
  Qed.

  Local Lemma g_ex_RInt {F} : ex_RInt (g F) 0 1.
  Proof. Admitted.

  Local Lemma g_expectation {F} : is_RInt (g F) 0 1 (BNEHalf_CreditV F).
  Proof.
    suffices H : RInt (g F) 0 1 = BNEHalf_CreditV F.
    { rewrite -H. apply (RInt_correct (V := R_CompleteNormedModule)), g_ex_RInt. }
    rewrite /g.
    rewrite -RInt_add.
    3: admit.
    2: admit.
    rewrite RInt_Iverson_le; [|lra].
    rewrite RInt_Iverson_ge'; [|lra].
    rewrite RInt_const/scal//=/mult//=.
    rewrite /RealDecrTrial_CreditV.
    replace (RInt (λ x : R, SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * LiftF F n)) 0 0.5)
       with (SeriesC (λ n : nat, RInt (λ x : R, RealDecrTrial_μ x 0 n * LiftF F n) 0 0.5)); last first.
    { (* Deploy the Foob *) admit. }
    replace (λ n : nat, RInt (λ x : R, RealDecrTrial_μ x 0 n * LiftF F n) 0 0.5)
       with (λ n : nat, LiftF F n * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5); last first.
    { apply functional_extensionality; intros n. by rewrite -RInt_Rmult' Rmult_comm /LiftF. }
    rewrite /LiftF.
    replace (SeriesC (λ n : nat, F (n `rem` 2 =? 1)%Z * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5))
       with ((SeriesC (λ n : nat, Iverson Zeven  n * F (n `rem` 2 =? 1)%Z * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5)) +
             (SeriesC (λ n : nat, Iverson (not ∘ Zeven) n * F (n `rem` 2 =? 1)%Z * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5)));
        last first.
    { rewrite -SeriesC_plus.
      3: admit.
      2: admit.
      f_equal; apply functional_extensionality; intro n.
      rewrite Rmult_assoc Rmult_assoc.
      rewrite -Rmult_plus_distr_r.
      rewrite -{2}(Rmult_1_l (_* RInt _ _ _)).
      f_equal.
      apply Iverson_add_neg.
    }
    replace (SeriesC (λ n : nat, Iverson Zeven n * F (n `rem` 2 =? 1)%Z * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5))
       with (SeriesC (λ n : nat, (Iverson Zeven n * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5)) * F false );
       last first.
    { rewrite -SeriesC_scal_r.
      f_equal; apply functional_extensionality; intro n.
      rewrite /Iverson//=.
      case_decide; [|lra].
      rewrite Rmult_1_l Rmult_1_l Rmult_comm.
      f_equal; f_equal; symmetry.
      apply Zeven_bool_iff in H.
      eapply (ssrbool.introF (Z.eqb_spec _ _)).
      rewrite Zeven_mod in H.
      apply Zeq_bool_eq in H.
      apply (Z.rem_mod_eq_0 n 2 ) in H; [rewrite H; lia|lia].
    }
    replace (SeriesC (λ n : nat, Iverson (not ∘ Zeven) n * F (n `rem` 2 =? 1)%Z * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5))
       with (SeriesC (λ n : nat, Iverson (not ∘ Zeven) n * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5) * F true);
      last first.
    { rewrite -SeriesC_scal_r.
      f_equal; apply functional_extensionality; intro n.
      rewrite /Iverson//=.
      case_decide; [|lra].
      rewrite Rmult_1_l Rmult_1_l Rmult_comm.
      f_equal; f_equal; symmetry.
      eapply (ssrbool.introT (Z.eqb_spec _ _)).
      destruct (Zeven_odd_dec n); [intuition|].
      destruct (Zodd_ex _ z) as [m Hm].
      rewrite Hm.
      rewrite Z.add_rem; try lia.
      rewrite Z.mul_comm.
      rewrite Z.rem_mul; try lia.
      rewrite Zplus_0_l //=.
    }
    have HIntegral (n : nat) : RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5 = RealDecrTrial_μ0 (0.5) (n+1)%nat.
    { rewrite /RealDecrTrial_μ//=.
      rewrite Iverson_True; [|simpl; lia].
      rewrite /RealDecrTrial_μ0.
      (* Compute *)
      admit.
    }
    replace (λ n : nat, Iverson Zeven n * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5)
       with (λ n : nat, Iverson Zeven n * RealDecrTrial_μ0 0.5 (n+1)%nat); last first.
    { f_equal; apply functional_extensionality; intro n; by rewrite HIntegral. }
    replace (λ n : nat, Iverson (not ∘ Zeven) n * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5)
       with (λ n : nat, Iverson (not ∘ Zeven) n * RealDecrTrial_μ0 0.5 (n+1)%nat); last first.
    { f_equal; apply functional_extensionality; intro n; by rewrite HIntegral. }
    rewrite Rplus_assoc.
    rewrite -Rmult_plus_distr_r.
    rewrite Rplus_comm (Rmult_comm _ (F false)) (Rmult_comm _ (F true)).
    rewrite /BNEHalf_CreditV.
    f_equal; f_equal.
    { (* Gaussian Taylor series *) admit. }
    { (* Gaussian Taylor series *) admit. }
  Admitted.

End credits.


Section program.
  Context `{!erisGS Σ}.

  (* A lazy real is less than or equal to one half, ie. the first bit is zero. *)
  Definition LeHalf : val :=
    λ: "x",
      let: "c1n" := get_chunk (Fst "x") (Snd "x") in
      let: "res" := cmpZ (Fst "c1n") #1 in
      (* First bit is 0: res is -1, number is at most 1/2, return #true
         First bit is 1: res is 0, number is at least 1/2, return #false *)
      "res" = #0.

  Definition LeHalf_spec (r : R) : bool := bool_decide (Rle r (0.5)%R).

  Theorem wp_LeHalf E v r :
    lazy_real v r -∗ WP LeHalf v @ E {{ vb, ⌜vb = #(LeHalf_spec r) ⌝ ∗ lazy_real v r }}.
  Proof.
    iIntros "Hr".
    iDestruct "Hr" as (l α f -> ->) "Hr".
    iDestruct "Hr" as (zs f') "(%Hf & Hc & Hα)".
    rewrite /LeHalf /get_chunk; wp_pures.
    destruct zs as [|z zs].
    { rewrite /chunk_list//=.
      wp_apply (wp_load with "Hc").
      iIntros "Hc".
      wp_pures.
      wp_apply (wp_rand_infinite_tape with "Hα").
      iIntros "Hα".
      wp_pures.
      wp_apply (wp_alloc with "[//]").
      iIntros (ℓ) "Hℓ".
      wp_pures.
      wp_apply (wp_store with "[Hc]"); first iFrame.
      iIntros "Hc'".
      wp_pures.
      wp_apply (wp_cmpZ with "[//]").
      iIntros "_".
      wp_pures.
      iModIntro.
      iSplit.
      { iPureIntro; simpl; f_equal.
        rewrite Hf /append_bin_seq /LeHalf_spec //=.
        replace (λ n : nat, f' n) with f' by done.
        (* The terms seq_bin_to_R_leading0 seq_bin_to_R_leading1 should do the trick, but there is
           dependent types trouble in destructing f' 0 *)
        admit.
      }
      iExists l, α, f.
      iSplitR; first done.
      iSplitR; first done.
      iExists [f' 0%nat], (λ n : nat, f' (S n)).
      iFrame.
      iPureIntro.
      rewrite Hf /append_bin_seq//=.
      apply functional_extensionality; by intros [|].
    }
    { rewrite /chunk_list.
      iDestruct "Hc" as (l') "(Hc & Hlist)".
      wp_apply (wp_load with "Hc").
      iIntros "Hc".
      wp_pures.
      wp_apply (wp_cmpZ with "[//]").
      iIntros "_".
      wp_pures.
      iModIntro.
      iSplit.
      { iPureIntro; simpl; f_equal.
        (* Similar to above. *)
        admit. }
      { iExists l, α, f.
        iSplitR; first done.
        iSplitR; first done.
        unfold chunk_and_tape_seq.
        iExists (z::zs), f'.
        iFrame.
        done.
    }
  Admitted.

  Definition BNEHalf : val :=
    λ: "_",
    let: "x" := init #() in
    if: LeHalf "x" then
      let: "y" := lazyDecrR #Nat.zero "x" in
      ("y" `rem` #2%Z = #1%Z)
    else
      #true.

  Theorem wp_BNEHalf E {F} (Hnn : ∀ r, 0 <= F r) :
    ↯(BNEHalf_CreditV F) -∗ WP BNEHalf #() @ E {{ vb , ∃ b : bool, ⌜vb = #b ⌝ ∗ ↯(F b) }}.
  Proof.
    iIntros "Hε".
    unfold BNEHalf.
    wp_pure.
    wp_apply wp_init; first done.
    iIntros (x) "Hx".
    iApply (wp_lazy_real_presample_adv_comp _ _ x _ (BNEHalf_CreditV F) (g F)); auto.
    { intros ??; apply g_nn; auto. }
    { by apply g_expectation. }
    iFrame.
    iIntros (r) "(%Hrange & Hε & Hx)".
    wp_pures.
    wp_bind (LeHalf _).
    iApply (pgl_wp_mono_frame with "[Hx] Hε"); last iApply (wp_LeHalf with "Hx").
    rewrite /LeHalf_spec//=.
    iIntros (v) "(Hε & -> & Hr)".
    case_bool_decide.
    { wp_pures.
      rewrite /g//=.
      iPoseProof (ec_split _ _ with "Hε") as "(Hε & _)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply CreditV_nonneg; auto]. intro n. apply Hnn. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      wp_bind (lazyDecrR _ _).
      iApply (pgl_wp_mono with "[Hr Hε]"); last first.
      { iApply (wp_lazyDecrR_gen (LiftF F)); [rewrite /LiftF//=|].
        iFrame.
        iSplitR; first auto.
        rewrite Iverson_True; auto.
        rewrite Rmult_1_l.
        iFrame.
      }
      rewrite /LiftF//=.
      iIntros (vb) "(%n & -> & Hε & Hx)".
      wp_pures.
      iModIntro.
      iExists _; iFrame.
      iPureIntro.
      f_equal.
      destruct (n `rem` 2 =? 1)%Z as [|] eqn:Hb.
      { by rewrite (ssrbool.elimT (Z.eqb_spec _ _) Hb) //=. }
      { have Hb' := (ssrbool.elimF (Z.eqb_spec _ _) Hb).
        case_bool_decide; auto.
        inversion H0; intuition.
      }
    }
    { wp_pures.
      iModIntro.
      iExists true.
      iSplitR; first done.
      rewrite /g.
      iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply CreditV_nonneg; auto ]. intro n. apply Hnn. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      rewrite Iverson_True; auto.
      rewrite Rmult_1_l.
      iFrame.
    }
  Qed.

End program.
