(* [DH_KE] and [DH_KE_v] are two placements of the same setup around the same
   core; at the one-shot type [τ__F chan gk] they are related in both
   directions.  The proof allocates the setup of one side eagerly and of the
   other side at the first (and only) client call, pairs the allocated tapes
   and references in invariants, and then uses the typing of the core. *)

From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import comp_operators primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory logic.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import def_dhke dhke_common.
From clutch.prob_eff_lang.probblaze.examples.AUTH Require Import auth_def auth_typing.


Section dhke_v_relation.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  Import valgroup_notation.
  #[local] Notation n := (S n'').

  Lemma DH_KE_closed : is_closed_expr ∅ DH_KE.
  Proof. is_closed. Qed.

  (* Substituting the setup values into the core. *)
  Lemma dh_core_subst (f e α β l1 l2 : val) :
    subst_map {["f" := f; "effs" := e; "α" := α; "β" := β; "l1" := l1; "l2" := l2]}
      (dh_core "f" "effs" "α" "β" "l1" "l2") = dh_core f e α β l1 l2.
  Proof. rewrite /dh_core. simpl. by simplify_map_eq. Qed.

  (* The environment of [dh_core_typed], from the related setup values. *)
  Lemma dh_core_env (θ θ₂ : sem_row Σ) (f1 f2 e1 e2 : val) (α1 α2 β1 β2 l11 l12 l21 l22 : loc) :
    (∀ᵣ θ₁, gk θ₁ -{ sem_row_union (¡θ₁) θ }-∘ 𝟙)%T f1 f2 -∗
    chan θ₂ e1 e2 -∗
    invariants.inv (logN .@ (α1, α2)) (α1 ↪ (n; []) ∗ α2 ↪ₛ (n; [])) -∗
    invariants.inv (logN .@ (β1, β2)) (β1 ↪ (n; []) ∗ β2 ↪ₛ (n; [])) -∗
    invariants.inv (tyN .@ (l11, l12)) (∃ w1 w2, l11 ↦ w1 ∗ l12 ↦ₛ w2 ∗ (Option ℕ)%T w1 w2) -∗
    invariants.inv (tyN .@ (l21, l22)) (∃ w1 w2, l21 ↦ w1 ∗ l22 ↦ₛ w2 ∗ (Option ℕ)%T w1 w2) -∗
    [("f", (∀ᵣ θ₁, gk θ₁ -{ sem_row_union (¡θ₁) θ }-∘ 𝟙)%T); ("effs", chan θ₂);
     ("α", sem_ty_tape); ("β", sem_ty_tape); ("l1", Refᶜ (Option ℕ)); ("l2", Refᶜ (Option ℕ))]
      ⊨ₑ {["f" := (f1, f2); "effs" := (e1, e2); "α" := (#lbl:α1, #lbl:α2); "β" := (#lbl:β1, #lbl:β2);
            "l1" := (#l11, #l12); "l2" := (#l21, #l22)]}.
  Proof.
    iIntros "Hf He #Hα #Hβ #Hl1 #Hl2".
    rewrite !env_sem_typed_cons env_sem_typed_empty.
    iSplitL "Hf". { iExists _, _. iFrame. by simplify_map_eq. }
    iSplitL "He". { iExists _, _. iFrame. by simplify_map_eq. }
    iSplitR. { iExists _, _. iSplit; first by simplify_map_eq. iExists α1, α2, n. by iFrame "Hα". }
    iSplitR. { iExists _, _. iSplit; first by simplify_map_eq. iExists β1, β2, n. by iFrame "Hβ". }
    iSplitR. { iExists _, _. iSplit; first by simplify_map_eq. iExists l11, l12. by iFrame "Hl1". }
    iSplitR; last done. { iExists _, _. iSplit; first by simplify_map_eq. iExists l21, l22. by iFrame "Hl2". }
  Qed.

  Lemma option_nat_none : ⊢ ((Option ℕ)%T : sem_ty Σ) NONEV NONEV.
  Proof. iExists _, _. iLeft. done. Qed.

  Lemma DH_KE_le_DH_KE_v : ⊢ sem_typed [] DH_KE DH_KE_v ⊥ (τ__F chan gk) [].
  Proof using All.
    iIntros "!# %vs _".
    rewrite (subst_map_is_closed_empty _ _ DH_KE_closed) (subst_map_is_closed_empty _ _ DH_KE_v_closed).
    rewrite DH_KE_core_eq /DH_KE_v.
    (* eager setup on the left *)
    iApply (brel_alloctape_l [AppRCtx _] _). iIntros "!> %α1 Hα1". brel_pures_l.
    iApply (brel_alloctape_l [AppRCtx _] _). iIntros "!> %β1 Hβ1". brel_pures_l.
    iApply (brel_alloc_l _ _ _ [AppRCtx _]). iIntros "!> %l11 Hl11". brel_pures_l.
    iApply (brel_alloc_l _ _ _ [AppRCtx _]). iIntros "!> %l21 Hl21". brel_pures_l.
    iModIntro. iSplit; last done.
    iIntros (θ f1 f2) "Hf". brel_pures_l. brel_pures_r.
    iModIntro.
    iIntros (θ₂ e1 e2) "He". brel_pures_l 1%nat. brel_pures_r 1%nat.
    (* lazy setup on the right *)
    iApply (brel_alloctape_r [AppRCtx _] _). iIntros "%α2 Hα2". brel_pures_r.
    iApply (brel_alloctape_r [AppRCtx _] _). iIntros "%β2 Hβ2". brel_pures_r.
    iApply (brel_alloc_r _ _ _ _ [AppRCtx _]). iIntros "%l12 Hl12". brel_pures_r.
    iApply (brel_alloc_r _ _ _ _ [AppRCtx _]). iIntros "%l22 Hl22". brel_pures_r 2%nat.
    (* pair the setup *)
    iDestruct (tapeN_to_empty with "Hα1") as "Hα1".
    iDestruct (tapeN_to_empty with "Hβ1") as "Hβ1".
    iMod (inv_alloc (logN.@(α1,α2)) _ (α1 ↪ (n; []) ∗ α2 ↪ₛ (n; []))%I with "[$Hα1 $Hα2]") as "#Hα".
    iMod (inv_alloc (logN.@(β1,β2)) _ (β1 ↪ (n; []) ∗ β2 ↪ₛ (n; []))%I with "[$Hβ1 $Hβ2]") as "#Hβ".
    iMod (inv_alloc (tyN.@(l11,l12)) _ (∃ w1 w2, l11 ↦ w1 ∗ l12 ↦ₛ w2 ∗ (Option ℕ)%T w1 w2)%I
            with "[Hl11 Hl12]") as "#Hl1".
    { iNext. iExists _, _. iFrame. iApply option_nat_none. }
    iMod (inv_alloc (tyN.@(l21,l22)) _ (∃ w1 w2, l21 ↦ w1 ∗ l22 ↦ₛ w2 ∗ (Option ℕ)%T w1 w2)%I
            with "[Hl21 Hl22]") as "#Hl2".
    { iNext. iExists _, _. iFrame. iApply option_nat_none. }
    (* the core *)
    iPoseProof (dh_core_typed θ θ₂) as "#Hcore". rewrite /sem_typed /tc_opaque.
    iDestruct ("Hcore" with "[Hf He]") as "H".
    { iApply (dh_core_env with "Hf He Hα Hβ Hl1 Hl2"). }
    rewrite !fmap_insert !fmap_empty !dh_core_subst. iEval (cbn [fst snd]) in "H".
    iApply (brel_wand with "H"). iIntros "!# % % [$ _]".
  Qed.

  Lemma DH_KE_v_le_DH_KE : ⊢ sem_typed [] DH_KE_v DH_KE ⊥ (τ__F chan gk) [].
  Proof using All.
    iIntros "!# %vs _".
    rewrite (subst_map_is_closed_empty _ _ DH_KE_closed) (subst_map_is_closed_empty _ _ DH_KE_v_closed).
    rewrite DH_KE_core_eq /DH_KE_v.
    (* eager setup on the right *)
    iApply (brel_alloctape_r [AppRCtx _] _). iIntros "%α2 Hα2". brel_pures_r.
    iApply (brel_alloctape_r [AppRCtx _] _). iIntros "%β2 Hβ2". brel_pures_r.
    iApply (brel_alloc_r _ _ _ _ [AppRCtx _]). iIntros "%l12 Hl12". brel_pures_r.
    iApply (brel_alloc_r _ _ _ _ [AppRCtx _]). iIntros "%l22 Hl22". brel_pures_r.
    iModIntro. iSplit; last done.
    iIntros (θ f1 f2) "Hf". brel_pures_l. brel_pures_r.
    iModIntro.
    iIntros (θ₂ e1 e2) "He". brel_pures_l 1%nat. brel_pures_r 1%nat.
    (* lazy setup on the left *)
    iApply (brel_alloctape_l [AppRCtx _] _). iIntros "!> %α1 Hα1". brel_pures_l.
    iApply (brel_alloctape_l [AppRCtx _] _). iIntros "!> %β1 Hβ1". brel_pures_l.
    iApply (brel_alloc_l _ _ _ [AppRCtx _]). iIntros "!> %l11 Hl11". brel_pures_l.
    iApply (brel_alloc_l _ _ _ [AppRCtx _]). iIntros "!> %l21 Hl21". brel_pures_l 2%nat.
    iDestruct (tapeN_to_empty with "Hα1") as "Hα1".
    iDestruct (tapeN_to_empty with "Hβ1") as "Hβ1".
    iMod (inv_alloc (logN.@(α1,α2)) _ (α1 ↪ (n; []) ∗ α2 ↪ₛ (n; []))%I with "[$Hα1 $Hα2]") as "#Hα".
    iMod (inv_alloc (logN.@(β1,β2)) _ (β1 ↪ (n; []) ∗ β2 ↪ₛ (n; []))%I with "[$Hβ1 $Hβ2]") as "#Hβ".
    iMod (inv_alloc (tyN.@(l11,l12)) _ (∃ w1 w2, l11 ↦ w1 ∗ l12 ↦ₛ w2 ∗ (Option ℕ)%T w1 w2)%I
            with "[Hl11 Hl12]") as "#Hl1".
    { iNext. iExists _, _. iFrame. iApply option_nat_none. }
    iMod (inv_alloc (tyN.@(l21,l22)) _ (∃ w1 w2, l21 ↦ w1 ∗ l22 ↦ₛ w2 ∗ (Option ℕ)%T w1 w2)%I
            with "[Hl21 Hl22]") as "#Hl2".
    { iNext. iExists _, _. iFrame. iApply option_nat_none. }
    iPoseProof (dh_core_typed θ θ₂) as "#Hcore". rewrite /sem_typed /tc_opaque.
    iDestruct ("Hcore" with "[Hf He]") as "H".
    { iApply (dh_core_env with "Hf He Hα Hβ Hl1 Hl2"). }
    rewrite !fmap_insert !fmap_empty !dh_core_subst. iEval (cbn [fst snd]) in "H".
    iApply (brel_wand with "H"). iIntros "!# % % [$ _]".
  Qed.

End dhke_v_relation.
