(* The security of [AUTH]: against one-shot environments, the protocol over
   the raw network and the simulated authenticated channel [S_AUTH ∘f F_AUTH]
   are within [2/q], for a group of prime order [q].

   The proof is a chain of three steps, each a relation between factories:
     AUTH = AUTH_of MAC     ≈ AUTH_of MAC_pad     exactly   (auth_mac)
     AUTH_of MAC_pad        ≈ AUTH_of MAC_ideal   1/q per MAC instance (auth_mac)
     AUTH_of MAC_ideal      ≈ S_AUTH ∘f F_AUTH    exactly   (auth_prf)
   The middle step costs error credits for both MAC instances, which is why
   the environment is one-shot: every session would cost [2/q] again. *)

From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory mode adequacy.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage comp_operators uc_systems uc_advantage.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def.
From clutch.prob_eff_lang.probblaze.examples.auth Require Import auth_def auth_typing auth_mac auth_prf.
From Stdlib Require Import Reals Psatz.

Import fingroup.
Import fingroup.fingroup.

Section lift.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Import valgroup_notation.
  #[local] Open Scope R_scope.

  Lemma ref_cpy_alloc (τ : sem_ty Σ) (l1 l2 : loc) (w1 w2 : val) :
    l1 ↦ w1 -∗ l2 ↦ₛ w2 -∗ τ w1 w2 ={⊤}=∗ (Refᶜ τ)%T #l1 #l2.
  Proof.
    iIntros "Hl1 Hl2 Hτ".
    iMod (na_inv_alloc _ _ (tyN.@(l1,l2)) (∃ w1 w2, l1 ↦ w1 ∗ l2 ↦ₛ w2 ∗ τ w1 w2)%I with "[Hl1 Hl2 Hτ]") as "#Hinv".
    { iNext. iExists _, _. iFrame. }
    iModIntro. iExists l1, l2. by iFrame "Hinv".
  Qed.

  (* The session of [AUTH_of], at concrete MAC instances and receiver state. *)
  Lemma auth_sess_inst (va va' vb vb' : val) (d1 d1' d2 d2' r1 r1' r2 r2' : loc) :
    MACT va va' -∗ MACT vb vb' -∗ (Refᶜ 𝔹)%T #d1 #d1' -∗ (Refᶜ 𝔹)%T #d2 #d2' -∗
    (Refᶜ (Option 𝔾))%T #r1 #r1' -∗ (Refᶜ (Option 𝔾))%T #r2 #r2' -∗
    BREL val_subst "res2" #r2 (val_subst "res1" #r1 (val_subst "dec2" #d2 (val_subst "dec1" #d1
           (val_subst "macb" vb (val_subst "maca" va (auth_sess "maca" "macb" "dec1" "dec2" "res1" "res2"))))))
      ≤ val_subst "res2" #r2' (val_subst "res1" #r1' (val_subst "dec2" #d2' (val_subst "dec1" #d1'
           (val_subst "macb" vb' (val_subst "maca" va' (auth_sess "maca" "macb" "dec1" "dec2" "res1" "res2"))))))
      <|iLblSig_to_iLblThy ⟨⟩%R|> {{ τ__F raw chan }}.
  Proof using All.
    iIntros "Ha Hb Hd1 Hd2 Hr1 Hr2".
    iPoseProof auth_sess_typed as "#H". rewrite /sem_typed /tc_opaque.
    iDestruct ("H" $! (<[ "res2" := (#r2, #r2') ]> (<[ "res1" := (#r1, #r1') ]> (<[ "dec2" := (#d2, #d2') ]>
                       (<[ "dec1" := (#d1, #d1') ]> (<[ "macb" := (vb, vb') ]> (<[ "maca" := (va, va') ]> ∅))))))
                with "[Ha Hb Hd1 Hd2 Hr1 Hr2]") as "H'".
    { rewrite !env_sem_typed_cons env_sem_typed_empty.
      iSplitL "Ha"; first (iExists _, _; iSplit; [iPureIntro; by simplify_map_eq|done]).
      iSplitL "Hb"; first (iExists _, _; iSplit; [iPureIntro; by simplify_map_eq|done]).
      iSplitL "Hd1"; first (iExists _, _; iSplit; [iPureIntro; by simplify_map_eq|done]).
      iSplitL "Hd2"; first (iExists _, _; iSplit; [iPureIntro; by simplify_map_eq|done]).
      iSplitL "Hr1"; first (iExists _, _; iSplit; [iPureIntro; by simplify_map_eq|done]).
      iSplitL "Hr2"; first (iExists _, _; iSplit; [iPureIntro; by simplify_map_eq|done]).
      done. }
    iRevert "H'". rewrite !fmap_insert !fmap_empty. cbn [fst snd].
    repeat first [rewrite subst_map_insert | rewrite delete_insert_ne; last done
                 | rewrite delete_empty | rewrite subst_map_empty].
    iIntros "H'". iApply (brel_wand with "H'"). iIntros "!# % % [$ _]".
  Qed.

  (* The protocol over two instances of [M] and over two instances of [M'],
     at one-shot environments, from a relation between one instance of each
     that costs [ε]. *)
  Lemma AUTH_of_err (M M' : val) (ε : R) :
    (⊢ ↯ ε -∗ BREL (M #()%V) ≤ (M' #()%V) <|⊥|> {{ MACT }}) →
    ⊢ ↯ ε -∗ ↯ ε -∗ (fac OS (τ__F raw chan)) (AUTH_of M) (AUTH_of M').
  Proof using All.
    iIntros (HM) "H1 H2". rewrite /fac /sem_ty_mbang /sem_ty_arr /=. iIntros (u1 u2) "[-> ->]".
    rewrite /AUTH_of. brel_pures_l. brel_pures_r.
    iApply (brel_bind [AppRCtx _] [AppRCtx _] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS _ _ [] [] with "[] [H1]"); [iApply to_iThy_le_refl|by iApply HM|].
    simpl. iIntros (va va') "#Ha". brel_pures_l. brel_pures_r.
    iApply (brel_bind [AppRCtx _] [AppRCtx _] _ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS _ _ [] [] with "[] [H2]"); [iApply to_iThy_le_refl|by iApply HM|].
    simpl. iIntros (vb vb') "#Hb". brel_pures_l. brel_pures_r.
    brel_alloc_l d1 as "Hd1". brel_pures_l. brel_alloc_l d2 as "Hd2". brel_pures_l.
    brel_alloc_l r1 as "Hr1". brel_pures_l. brel_alloc_l r2 as "Hr2".
    brel_alloc_r d1' as "Hd1'". brel_pures_r. brel_alloc_r d2' as "Hd2'". brel_pures_r.
    brel_alloc_r r1' as "Hr1'". brel_pures_r. brel_alloc_r r2' as "Hr2'".
    iMod (ref_cpy_alloc 𝔹 d1 d1' with "Hd1 Hd1' []") as "#Rd1"; first by iExists false.
    iMod (ref_cpy_alloc 𝔹 d2 d2' with "Hd2 Hd2' []") as "#Rd2"; first by iExists false.
    iMod (ref_cpy_alloc (Option 𝔾) r1 r1' with "Hr1 Hr1' []") as "#Rr1"; first (iExists _, _; iLeft; by repeat iSplit).
    iMod (ref_cpy_alloc (Option 𝔾) r2 r2' with "Hr2 Hr2' []") as "#Rr2"; first (iExists _, _; iLeft; by repeat iSplit).
    brel_pures_l 2%nat. brel_pures_r 2%nat.
    iApply (auth_sess_inst with "Ha Hb Rd1 Rd2 Rr1 Rr2").
  Qed.
End lift.

Section adv_auth.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{Hpre : probblazeRGpreS Σ}.
  #[local] Notation q := (S (S n'')).
  #[local] Open Scope R_scope.

  (* The group order is prime: a forged tag hits one key value out of [q]. *)
  Hypothesis Hq : is_true (prime.prime q).

  Theorem adv_AUTH (A : val) :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (fac OS (τ__F raw chan) → 𝔹)%T) →
    advantage A AUTH (S_AUTH ∘f F_AUTH)%fac #true <= 2 / q.
  Proof using All.
    intros HA.
    assert (0 <= 1 / q) by (apply Rcomplements.Rdiv_le_0_compat; [lra|apply lt_0_INR; lia]).
    eapply (advantage_triangle _ _ AUTH_pad _ _ 0 (2 / q)); last lra.
    { (* the pad step is exact *)
      apply (advantage_zero A AUTH AUTH_pad true (λ H : probblazeRGS Σ, fac OS (τ__F raw chan))); first exact HA.
      - intros HRGS. iApply sem_typed_val. iApply (AUTH_of_typed (G := G _ _)). iApply MAC_MAC_pad.
      - intros HRGS. iApply sem_typed_val. iApply (AUTH_of_typed (G := G _ _)). iApply MAC_pad_MAC. }
    eapply (advantage_triangle _ _ AUTH_ideal _ _ (2 / q) 0); last lra.
    { (* the forgery step: [1/q] per direction *)
      apply (brel_advantage A AUTH_pad AUTH_ideal (λ H : probblazeRGS Σ, fac OS (τ__F raw chan)) (2 / q));
        [lra|exact HA|split].
      - intros HRGS. iIntros "Hε". iApply brel_value. iIntros "$ !>".
        replace (2 / q) with (1 / q + 1 / q) by lra.
        iDestruct (ec_split with "Hε") as "[H1 H2]"; [done|done|].
        iApply (AUTH_of_err (G := G _ _) MAC_pad MAC_ideal (1 / q) with "H1 H2").
        iIntros "H". by iApply (MAC_pad_MAC_ideal_body (G := G _ _) Hq with "H").
      - intros HRGS. iIntros "Hε". iApply brel_value. iIntros "$ !>".
        replace (2 / q) with (1 / q + 1 / q) by lra.
        iDestruct (ec_split with "Hε") as "[H1 H2]"; [done|done|].
        iApply (AUTH_of_err (G := G _ _) MAC_ideal MAC_pad (1 / q) with "H1 H2").
        iIntros "H". by iApply (MAC_ideal_MAC_pad_body (G := G _ _) Hq with "H"). }
    { (* the ideal protocol is the simulated functionality *)
      apply (advantage_zero A AUTH_ideal (S_AUTH ∘f F_AUTH)%fac true (λ H : probblazeRGS Σ, fac OS (τ__F raw chan)));
        first exact HA.
      - intros HRGS. iApply sem_typed_sub_ty; first iApply fac_MS_le. iApply (AUTH_ideal_SIM_F (G := G _ _)).
      - intros HRGS. iApply sem_typed_sub_ty; first iApply fac_MS_le. iApply (SIM_F_AUTH_ideal (G := G _ _)). }
  Qed.

End adv_auth.
