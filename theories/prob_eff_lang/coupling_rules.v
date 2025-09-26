From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext fin.
From clutch.common Require Import locations.
From clutch.approxis Require Import app_weakestpre.
From clutch.prob_eff_lang Require Import lifting.
From clutch.prob_eff_lang Require Import notation tactics metatheory erasure.
From clutch.prob_eff_lang Require Import spec_rules spec_ra.
From clutch.prob_eff_lang Require Export primitive_laws weakestpre lang.

Section rules.
  Context `{!probeffGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.


(** * rand(N) ~ rand(N) coupling *)
  (*
    There should be an easier proof of this using wp_couple_rand_rand_inj,
    but that uses an injective function nat -> nat as opposed to fin (S N) -> fin (S N)
  *)
  Lemma ewp_couple_rand_rand N f `{Bij nat nat f} z K E Φ Ψ :
    TCEq N (Z.to_nat z) →
    (forall n:nat, (n < S N)%nat -> (f n < S N)%nat) →
    ( ⤇ fill K (rand #z) -∗
     ▷ (∀ n, ⌜ n ≤ N ⌝ ∗ ⤇ fill K #(f n) -∗ Φ #n) -∗
     EWP rand #z @ E <| Ψ |> {{ v, Φ v }} ).
  Proof.
    iIntros (H0 Hdom) "Hr HΨ".
    destruct (restr_bij_fin (S N) f Hdom) as [ff [Hbij Hff]].
    iApply ewp_lift_step_prog_couple; [done|done|].
    iIntros (σ1 e1' σ1' ε) "[Hσ [Hs Hε]]".
    iDestruct (spec_auth_prog_agree with "Hs Hr") as %->. simpl.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".

    replace ε with (0 + ε)%NNR; last first.
    { apply nnreal_ext; simpl; lra. }
    iApply (prog_coupl_steps _ _ _
              (λ ρ2 ρ2',
                ∃ (n : fin _), ρ2 = (Val #n, σ1) ∧ ρ2' = (fill K #(f n), σ1')))
    ; [done| | |..].
    { eexists. simpl. apply head_step_prim_step. apply head_step_support_equiv_rel. constructor; done. }
    { apply reducible_fill. eexists. simpl. apply head_step_prim_step. apply head_step_support_equiv_rel. constructor; done. }
    { simpl.
      rewrite /= fill_dmap //.
      rewrite /= -(dret_id_right (prim_step _ _)) /=.
      apply ARcoupl_exact.
      eapply Rcoupl_dmap.
      eapply Rcoupl_mono.
      - apply (Rcoupl_rand_rand _ ff).
        by rewrite H0.
      - intros [] [] (b & [=] & [=])=>/=.
        simplify_eq.
        rewrite Hff. eauto. }
    iIntros (e2 σ2 e2' σ2' (b & [= -> ->] & [= -> ->])) "!> !>".
    iMod (spec_update_prog with "Hs Hr") as "[$ Hr]".
    iMod "Hclose" as "_".
    replace (0 + ε)%NNR with ε; last first.
    { apply nnreal_ext; simpl; lra. }
    iFrame.
    iApply ewp_value.
    iApply "HΨ".
    iFrame.
    iPureIntro.
    apply fin_to_nat_le.
    Unshelve.
    { rewrite -H0; apply Fin.F1. } 
    { rewrite -H0; apply Fin.F1. } 
  Qed.

  (** * rand(unit, N) ~ state_step(α', N) coupling *)
  Lemma ewp_couple_rand_tape N f `{Bij nat nat f} z E α ns Φ Ψ :
    TCEq N (Z.to_nat z) →
    (∀ n, n < S N -> f n < S N)%nat →
    α ↪ₛN (N; ns) -∗
    ▷ (∀ n, α ↪ₛN (N; ns ++ [f n]) ∗ ⌜ n ≤ N ⌝ -∗ Φ #n) -∗
    EWP
      rand #z @ E <| Ψ |>
    {{ v, Φ v }}.
  Proof.
    iIntros (H0 Hdom) "Hαs HΦ". 
    iDestruct "Hαs" as (fs) "(<-&Hαs)".
    destruct (restr_bij_fin (S N) f Hdom) as [ff [Hbij Hff]].
    iApply ewp_lift_step_prog_couple; [done|done|].
    iIntros (σ1 e1' σ1' ε) "[[Hh1 Ht1] [Hauth2 Herr]]".
    iDestruct (spec_auth_lookup_tape with "Hauth2 Hαs") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε) with (0+ε)%NNR at 2 by (apply nnreal_ext; simpl; lra).
    iApply prog_coupl_step_l_erasable; [done| |..].
    { eexists. simpl. apply head_step_prim_step.
      apply head_step_support_equiv_rel. constructor; done. }
    { apply ARcoupl_exact.
      eapply (Rcoupl_rand_state _ ff); eauto.
      rewrite -H0//. }
    { by eapply state_step_erasable. }
    iIntros (??? (n & [= -> ->] & ->)).
    iMod (spec_auth_update_tape (_; fs ++ [ff _]) with "Hauth2 Hαs") as "[Htapes Hαs]".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iFrame.
    iApply ewp_value.
    iApply ("HΦ" $! _ with "[$Hαs]").
    iPureIntro.
    rewrite fmap_app -Hff.
    split; auto.
    apply fin_to_nat_le.
    Unshelve.
    rewrite -H0; apply Fin.F1.
  Qed.

End rules.
