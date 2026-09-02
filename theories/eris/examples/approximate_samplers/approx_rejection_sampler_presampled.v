(** * Examples related to rejection samplers with a bounded number of attempts *)
From clutch.eris Require Export eris error_rules.
From clutch.eris Require Export examples.approximate_samplers.approx_sampler_lib.
From Coquelicot Require Import Series.
From Stdlib Require Import Lra.

Set Default Proof Using "Type*".

Section presampled_flip2.
  (** Demonstration of using the planner rule instead of the higher-order spec *)
  (** This proof is fairly idiomatic Iris and does not need to do manual credit accounting *)
  Local Open Scope R.
  Context `{!erisGS Σ}.

  Lemma tapes_flip2_safe (ε : nonnegreal) E :
    0 < ε ->
    ⊢ ↯ε -∗
      WP
        let: "α" := (alloc #(Z.succ 0)) in
        gen_rejection_sampler
        (λ: "_", Pair (rand("α")#1) (rand("α") #1))
        (λ: "sample", (((Fst "sample") = #1) && ((Snd "sample") = #1)))
        @ E [{ v, ⌜ v = (#1%Z, #1%Z)%V ⌝ }].
  Proof.
    iIntros (?) "Hcr".
    wp_bind (alloc _)%I.
    wp_apply (twp_alloc_tape); auto.
    iIntros (α) "Hα".
    rewrite Z2Nat.inj_succ; try lia.
    wp_apply (twp_presample_planner_aligned _ _ _ _ _ _ _ _ [1%fin; 1%fin]); auto; [apply H|].
    iFrame.
    iIntros "[%junk Hα] /=".
    pose flip2_junk_inv k s : iProp Σ := (∃ j, α ↪ (S (Z.to_nat 0); j ++ s) ∗ ⌜length j = (2 * k)%nat ⌝)%I.
    iAssert (flip2_junk_inv _ _ _ (length (junk ++ block_pad (Z.to_nat 0) 2 junk) `div` 2) _) with "[Hα]" as "Hinv".
    { rewrite /flip2_junk_inv app_assoc.
      iExists _; iFrame; iPureIntro.
      apply Nat.Div0.div_exact.
      rewrite length_app.
      apply (blocks_aligned (Z.to_nat 0%nat) 2%nat).
      lia.
    }
    do 11 wp_pure.
    iInduction (length (junk ++ block_pad (Z.to_nat 0) 2 junk) `div` 2) as [|k'] "IH".
    - rewrite /flip2_junk_inv /=.
      iDestruct "Hinv" as "[%j (Hα & %Hl)] /=".
      rewrite (nil_length_inv _ Hl) /=.
      wp_pures.
      wp_bind (Rand _ _); wp_apply (twp_rand_tape with "Hα"); iIntros "Hα".
      wp_bind (Rand _ _); wp_apply (twp_rand_tape with "Hα"); iIntros "Hα".
      wp_pures.
      iModIntro; eauto.
    - rewrite /flip2_junk_inv.
      iDestruct "Hinv" as "[%j (Hα & %Hl)] /=".
      rewrite Nat.mul_succ_r Nat.add_comm /= in Hl.
      destruct j as [| s0 j0]. { simpl in Hl. exfalso; lia. }
      destruct j0 as [| s1 j']. { simpl in Hl. exfalso; lia. }
      wp_pures.
      wp_bind (Rand _ _); wp_apply (twp_rand_tape with "Hα"); iIntros "Hα".
      wp_bind (Rand _ _); wp_apply (twp_rand_tape with "Hα"); iIntros "Hα".
      iSpecialize ("IH" with "[Hα]").
      { iExists _; iFrame; iPureIntro. do 2 rewrite length_cons in Hl. congruence. }
      wp_pures.
      case_bool_decide; [wp_pures; case_bool_decide|].
      + wp_pures. iModIntro; iPureIntro.
        rewrite H0 H1. done.
      + wp_pure. iApply "IH".
      + do 2 wp_pure; iApply "IH".
  Qed.
End presampled_flip2.
