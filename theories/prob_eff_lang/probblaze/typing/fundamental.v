From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext. 
From clutch.prob_eff_lang.probblaze Require Import metatheory notation syntax semantics sem_judgement sem_def.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws compatibility.
From clutch.prob_eff_lang.probblaze Require Import sem_env.
From clutch.prob_eff_lang.probblaze Require Import types.
From clutch.prob_eff_lang.probblaze Require Import interp logic.

Section fundamental.
  Context `{!probblazeRGS Σ}.

Lemma ctx_dom_env_dom x Γ :
  ∀ η μ δ ξ, x ∉ ctx_dom Γ → x ∉ env_dom ((λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> Γ).
Proof.
  intros η μ δ ξ Hnin. induction Γ as [| (y, κ) Γ' IH]; simpl.
  - rewrite env_dom_nil. apply not_elem_of_nil.
  - rewrite env_dom_cons. apply not_elem_of_cons. split.
    + intros ->. apply Hnin. rewrite /ctx_dom /=. set_solver.
    + apply IH. rewrite /ctx_dom /= in Hnin. set_solver.
Qed.

(* Extract the bare relational interpretation of a value from its semantic
   value-typing judgement, at a given interpretation environment. *)
Lemma sem_val_related_interp (v : val) (τ : type) η μ δ ξ :
  (⊢ ⊨ᵥ v ≤log≤ v : τ) → ⊢ interp._ty η μ δ τ ξ v v.
Proof.
  iIntros (H). iPoseProof H as "H". iDestruct ("H" $! η μ δ ξ) as "H'".
  iEval (rewrite /sem_val_typed /tc_opaque) in "H'". iApply "H'".
Qed.

Theorem fundamental Δ Γ1 e ρ τ Γ2 :
  Δ .| Γ1 ⊢ₜ e : ρ : τ ⊣ Γ2 → ⊢ 〈Δ;Γ1〉 ⊨ₜ e ≤log≤ e : ρ : τ ⫤ Γ2
  with fundamental_val v τ :
    ⊢ᵥ v : τ → ⊢ ⊨ᵥ v ≤log≤ v : τ
  with fundamental_pure Γ e τ :
    Γ ⊢ₚ e : τ → ⊢ bin_log_pure_related Γ e e τ.
Proof.
  - intros Ht. destruct Ht; iIntros (η μ δ ξ vs Hδ).
    + (* Var_typed *) iApply sem_typed_var.
    + (* Val_typed *) iApply sem_typed_val; by iApply fundamental_val.
    + (* Pure_typed *) rewrite fmap_app. iApply sem_typed_oval.
      by iApply fundamental_pure.
    + (* Pair_typed *) iApply sem_typed_pair_gen ;
        (* waiting for syntactic rule for sem_row.RowTypeSub *)
        [admit|apply fundamental in Ht1 as Ht|apply fundamental in Ht2 as Ht];
        iPoseProof Ht as "Ht"; iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* Fst_typed *) iApply sem_typed_fst_expr. apply fundamental in Ht.
      iPoseProof Ht as "Ht". iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* Snd_typed *) iApply sem_typed_snd_expr. apply fundamental in Ht.
      iPoseProof Ht as "Ht". iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* InjL_typed *) iApply sem_typed_left_inj. apply fundamental in Ht.
      iPoseProof Ht as "Ht". iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* InjR_typed *) iApply sem_typed_right_inj. apply fundamental in Ht.
      iPoseProof Ht as "Ht". iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* Match_typed *) iApply sem_typed_match;
        [ destruct x; [|eapply ctx_dom_env_dom]; apply H
        | destruct x; [|eapply ctx_dom_env_dom]; apply H0
        | destruct y; [|eapply ctx_dom_env_dom]; apply H1
        | destruct y; [|eapply ctx_dom_env_dom]; apply H2
        | apply fundamental in Ht1; iPoseProof Ht1 as "Ht";
            iApply ("Ht" $! _ _ _ _ ∅ Hδ)
        | apply fundamental in Ht2; iPoseProof Ht2 as "Ht";
            destruct x; iApply ("Ht" $! _ _ _ _ ∅ Hδ)
        | apply fundamental in Ht3; iPoseProof Ht3 as "Ht";
            destruct y; iApply ("Ht" $! _ _ _ _ ∅ Hδ) ].
    + (* If_typed *) iApply sem_typed_if;
        [ apply fundamental in Ht1; iPoseProof Ht1 as "Ht";
            iApply ("Ht" $! _ _ _ _ ∅ Hδ)
        | apply fundamental in Ht2; iPoseProof Ht2 as "Ht";
            iApply ("Ht" $! _ _ _ _ ∅ Hδ)
        | apply fundamental in Ht3; iPoseProof Ht3 as "Ht";
            iApply ("Ht" $! _ _ _ _ ∅ Hδ) ].
    + (* Rec_typed *) admit.
    + (* App_typed *) admit.
    + (* TAbsElim_typed *) admit.
    + (* RAbsElim_typed *) admit.
    + (* MAbsElim_typed *) admit.
    + (* TAlloc *) iApply sem_typed_alloc. apply fundamental in Ht.
      iPoseProof Ht as "Ht". iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* TLoad *) admit.
    + (* TStore *) admit.
    + (* TAllocTape *) admit.
    + (* TRand *) admit.
    + (* TRandU *) admit.
    + (* TFold *) admit.
    + (* TUnfold *) admit.
    + (* TPack *) admit.
    + (* TUnpack *) admit.
    + (* Effect_typed *) admit.
    + (* Do_typed *) admit.
    + (* DeepHandle_typed *) admit.
    + (* ShallowHandle_typed *) admit.
    + (* Sub_typed *) admit.
    + (* Contraction_typed *) admit.
    + (* Weakening_typed *) destruct x; simpl.
      * apply fundamental in Ht. iPoseProof Ht as "Ht".
        iApply ("Ht" $! _ _ _ _ ∅ Hδ).
      * iApply sem_typed_weaken. apply fundamental in Ht.
        iPoseProof Ht as "Ht". iApply ("Ht" $! _ _ _ _ ∅ Hδ).
  - intros Hv. destruct Hv; iIntros (η μ δ ξ).
    + (* Unit_val_typed *) rewrite /sem_val_typed /=. iModIntro. done.
    + (* Int_val_typed *) rewrite /sem_val_typed /=. iModIntro. eauto.
    + (* Nat_val_typed *) rewrite /sem_val_typed /=. iModIntro. eauto.
    + (* Bool_val_typed *) rewrite /sem_val_typed /=. iModIntro. eauto.
    + (* Pair_val_typed *) apply fundamental_val in Hv1, Hv2.
      rewrite /sem_val_typed /=. iModIntro.
      iExists v1, v1, v2, v2. iSplit; first done. iSplit; first done.
      iSplitL; [iApply (sem_val_related_interp _ _ _ _ _ _ Hv1)
               |iApply (sem_val_related_interp _ _ _ _ _ _ Hv2)].
    + (* InjL_val_typed *) apply fundamental_val in Hv.
      rewrite /sem_val_typed /=. iModIntro. iExists v, v. iLeft.
      iSplit; first done. iSplit; first done.
      iApply (sem_val_related_interp _ _ _ _ _ _ Hv).
    + (* InjR_val_typed *) apply fundamental_val in Hv.
      rewrite /sem_val_typed /=. iModIntro. iExists v, v. iRight.
      iSplit; first done. iSplit; first done.
      iApply (sem_val_related_interp _ _ _ _ _ _ Hv).
    + (* Rec_val_typed *) admit.
    + (* TAbs_val_typed *) apply fundamental_val in Hv.
      rewrite /sem_val_typed /=. iModIntro. iIntros (τ0).
      iApply (sem_val_related_interp v τ (τ0 :: η) μ δ ξ Hv).
    + (* RAbs_val_typed *) apply fundamental_val in Hv.
      rewrite /sem_val_typed /=. iModIntro. iIntros (θ).
      iApply (sem_val_related_interp v τ η μ δ (θ :: ξ) Hv).
    + (* MAbs_val_typed *) apply fundamental_val in Hv.
      rewrite /sem_val_typed /=. iModIntro. iIntros (m).
      iApply (sem_val_related_interp v τ η (m :: μ) δ ξ Hv).
  - intros Hp. destruct Hp; iIntros (η μ δ ξ).
    + (* Val_pure_typed *) apply fundamental_val in H. iPoseProof H as "H".
      iSpecialize ("H" $! η μ δ ξ). iApply sem_oval_typed_val. iApply "H".
    + (* Rec_pure_typed *) admit.
    + (* Pair_pure_typed *)
      (* Blocked: building the product [prel] needs both component value
         relations simultaneously, hence two copies of [env_sem_typed Γ' vs].
         The pure Pair rule places no [MultiC Γ] (mode/persistence) side
         condition on Γ, so [interp Γ ⊨ₑ vs] is not persistent in general
         (e.g. for a linear-arrow binding), and the env cannot be duplicated.
         Helper [sem_oval_typed_pair] (compatibility.v) discharges this once
         [∀ vs, Persistent (Γ ⊨ₑ vs)] is available. *)
      admit.
    + (* InjL_pure_typed *) iApply sem_oval_typed_injl.
      apply fundamental_pure in Hp. iPoseProof Hp as "H".
      iApply ("H" $! η μ δ ξ).
    + (* InjR_pure_typed *) iApply sem_oval_typed_injr.
      apply fundamental_pure in Hp. iPoseProof Hp as "H".
      iApply ("H" $! η μ δ ξ).
    + (* Var_pure_typed *) iApply sem_oval_typed_var.
    + (* BangIntro_pure_typed *) admit.
    + (* TAbs_pure_typed *) admit.
    + (* RAbs_pure_typed *) admit.
    + (* MAbs_pure_typed *) admit.
Admitted.

End fundamental.
