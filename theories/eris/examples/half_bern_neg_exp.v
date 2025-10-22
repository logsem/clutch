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
     match b with
     | true => exp (-1/2)%R
     | false => 1 - exp (-1/2)%R
     end.

End pmf.

Section credits.
  Import Hierarchy.


  Definition BNEHalf_CreditV (F : bool → R) : R :=
    (F true) * BNEHalf_μ true + (F false) * BNEHalf_μ false.

  Lemma BNEHalf_CreditV_nn {F} (Hnn : ∀ r, 0 <= F r) : 0 <= BNEHalf_CreditV F.
  Proof. Admitted.

  Local Definition LiftF (F : bool -> R) : nat -> R :=
    fun n => F (Z.eqb (n `rem` 2)%Z 1%Z).

  Local Definition g (F : bool → R) : R → R := fun r =>
    Iverson (fun x => Rle x 0.5) r * RealDecrTrial_CreditV (LiftF F) 0 r +
    Iverson (fun x  => not (Rle x 0.5)) r * F (true).

  Local Lemma g_nn {F r} (Hnn : ∀ r, 0 <= F r) : 0 <= g F r.
  Proof. Admitted.

  Local Lemma g_expectation {F} : is_RInt (g F) 0 1 (BNEHalf_CreditV F).
  Proof. Admitted.

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
    { by intros ??; apply g_nn, Hnn. }
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
