(* Pitts & Stark's awkward example, following the ReLoC formalisation. *)

From iris.algebra Require Import csum excl.
From clutch Require Export clutch.
Set Default Proof Using "Type*".

Definition oneshotR := csumR (exclR unitR) (agreeR unitR).
Class oneshotG Σ := { oneshot_inG :: inG Σ oneshotR }.
Definition oneshotΣ : gFunctors := #[GFunctor oneshotR].
Global Instance subG_oneshotΣ {Σ} : subG oneshotΣ Σ → oneshotG Σ.
Proof. solve_inG. Qed.

Section proofs.
  Context `{!clutchRGS Σ}.

  Definition awkwardN := nroot.@"awkward".

  Lemma refinement1 :
    ⊢ REL
      let: "x" := ref #1 in
      (λ: "f", "f" #();; !"x")
    <<
      (λ: "f", "f" #();; #1)
    : (() → ()) → lrel_int.
  Proof.
    rel_alloc_l x as "Hx".
    repeat rel_pure_l.
    iApply (refines_na_alloc (x ↦ #1)%I awkwardN).
    iSplitL => //.
    iIntros "#Hinv".
    rel_pures_r.
    rel_arrow.
    iIntros (f1 f2) "#Hff".
    rel_rec_l. rel_rec_r.
    iApply (refines_seq with "[Hff]").
    - iApply refines_app; eauto.
      rel_values; eauto.
    - iApply (refines_na_inv with "[$Hinv]"); [done|].
      iIntros "[Hx Hclose]".
      rel_load_l.
      iApply (refines_na_close with "[- $Hclose $Hx]").
      rel_values.
  Qed.

  Definition pending γ `{oneshotG Σ} := own γ (Cinl (Excl ())).
  Definition shot γ `{oneshotG Σ} := own γ (Cinr (to_agree ())).
  Lemma new_pending `{oneshotG Σ} : ⊢ |==> ∃ γ, pending γ.
  Proof. by apply own_alloc. Qed.
  Lemma shoot γ `{oneshotG Σ} : pending γ ⊢ |==> shot γ.
  Proof.
    apply own_update.
    intros n [f |]; simpl; eauto.
    destruct f; simpl; try by inversion 1.
  Qed.
  Definition shootN := nroot .@ "shootN".
  Lemma shot_not_pending γ `{oneshotG Σ} :
    shot γ -∗ pending γ -∗ False.
  Proof.
    iIntros "Hs Hp".
    iPoseProof (own_valid_2 with "Hs Hp") as "H".
    iDestruct "H" as %[].
  Qed.

  Lemma refinement2 `{oneshotG Σ} :
    ⊢ REL
      let: "x" := ref #0 in
      (λ: "f", "x" <- #1;; "f" #();; !"x")
    <<
      (let: "x" := ref #1 in
       λ: "f", "f" #();; !"x")
    : (() → ()) → lrel_int.
  Proof.
    rel_alloc_l x as "Hx".
    rel_alloc_r y as "Hy".
    repeat rel_pure_l; repeat rel_pure_r.
    iMod new_pending as (γ) "Ht".
    set (P := ((x ↦ #0 ∗ pending γ ∨ x ↦ #1 ∗ shot γ) ∗ y ↦ₛ #1)%I).
    iApply (refines_na_alloc P shootN).
    iSplitL ; [ iFrame ; iLeft ; iFrame |].
    iIntros "#Hinv".
    iApply refines_arrow.
    iIntros "!#" (f1 f2) "#Hf".
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "(HP & Hclose)".
    rel_let_l. rel_let_r.
    unfold P.
    iDestruct "HP" as "([(Hx & Hp) | (Hx & #Hs)] & Hy)" ;
    rel_store_l ; rel_pures_l.
    - iMod (shoot γ with "Hp") as "#Hs".
      iApply (refines_na_close with "[-$Hclose]").
      iSplitL. { iFrame. iRight. by iFrame. }
      iApply (refines_seq with "[Hf]").
      + iApply (refines_app with "Hf").
        by rel_values.
      + iApply (refines_na_inv with "[$Hinv]"); [done|].
        iIntros "([[[Hx >Hp] | [Hx Hs']] Hy] & Hclose)".
        { iExFalso. iApply (shot_not_pending with "Hs Hp"). }
        rel_load_l.
        rel_load_r.
        iApply (refines_na_close with "[-$Hclose]"). iSplitL.
        { iModIntro. iFrame. iRight; by iFrame. }
        rel_values.
    - iApply (refines_na_close with "[-$Hclose]"). iSplitL.
      { iModIntro. iFrame. iRight; by iFrame. }
      iApply (refines_seq with "[Hf]"); auto.
      + iApply (refines_app with "Hf").
        by rel_values.
      + iApply (refines_na_inv with "[$Hinv]"); [done|].
        iIntros "([[[Hx >Hp] | [Hx Hs']] Hy] & Hclose)".
        { iExFalso. iApply (shot_not_pending with "Hs Hp"). }
        rel_load_l.
        rel_load_r.
        iApply (refines_na_close with "[-$Hclose]"). iSplitL.
        { iModIntro. iFrame. iRight; by iFrame. }
        rel_values.
  Qed.

  Lemma refinement25 `{oneshotG Σ} :
    ⊢ REL
      (λ: "f", "f" #();; #1)
    <<
      (let: "x" := ref #0 in
       (λ: "f", "x" <- #1;; "f" #();; !"x"))
    : (() → ()) → lrel_int.
  Proof.
    rel_alloc_r x as "Hx".
    repeat rel_pure_r.
    iMod new_pending as (γ) "Ht".
    set (P := ((x ↦ₛ #0 ∗ pending γ ∨ x ↦ₛ #1 ∗ shot γ))%I).
    iApply (refines_na_alloc P shootN).
    iSplitL ; [ iFrame ; iLeft ; iFrame |].
    iIntros "#Hinv".
    rel_pure_l.
    iApply refines_arrow.
    iIntros "!#" (f1 f2) "#Hf".
    repeat rel_pure_l. repeat rel_pure_r.
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "(>[[Hx Hp] | [Hx #Hs]] & Hclose)" ;
      rel_store_r; repeat rel_pure_r.
    - iMod (shoot γ with "Hp") as "#Hs".
      iApply (refines_na_close with "[-$Hclose]"). iSplitL.
      { iModIntro. iFrame. iRight; by iFrame. }
      iApply (refines_seq with "[Hf]"); auto.
      + iApply (refines_app with "Hf").
        rel_values.
      + iApply (refines_na_inv with "[$Hinv]"); [done|].
        iIntros "[[[>Hx >Hp] | [>Hx _]] Hclose]";
          rel_load_r.
        { iExFalso. iApply (shot_not_pending with "Hs Hp"). }
        iApply (refines_na_close with "[-$Hclose]"). iSplitL.
        { iModIntro. iFrame. iRight; by iFrame. }
        rel_values.
    - iApply (refines_na_close with "[-$Hclose]"). iSplitL.
      { iModIntro. iFrame. iRight; by iFrame. }
      iApply (refines_seq with "[Hf]"); auto.
      + iApply (refines_app with "Hf").
        rel_values.
      + iApply (refines_na_inv with "[$Hinv]"); [done|].
        iIntros "[[[>Hx >Hp] | [>Hx _]] Hclose]";
          rel_load_r.
        { iExFalso. iApply (shot_not_pending with "Hs Hp"). }
        iApply (refines_na_close with "[-$Hclose]"). iSplitL.
        { iModIntro. iFrame. iRight; by iFrame. }
        rel_values.
  Qed.
End proofs.
