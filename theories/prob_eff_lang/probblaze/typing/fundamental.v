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
    + (* TAbsElim_typed *)
      iApply (sem_typed_type_cong _ _ _ _ _ _ _
                (interp.ty_subst_single η μ δ ξ τ τ')).
      iApply (sem_typed_TApp (λ α, interp._ty (α :: η) μ δ τ ξ)
                (interp._ty η μ δ τ' ξ)).
      apply fundamental in Ht. iPoseProof Ht as "Ht".
      iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* RAbsElim_typed *)
      iApply (sem_typed_type_cong _ _ _ _ _ _ _
                (interp.row_subst_single η μ δ ξ τ ρ')).
      iApply (sem_typed_RApp (λ θ, interp._ty η μ δ τ (θ :: ξ))
                _ (interp._row η μ δ ρ' ξ)).
      apply fundamental in Ht. iPoseProof Ht as "Ht".
      iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* MAbsElim_typed *)
      iApply (sem_typed_type_cong _ _ _ _ _ _ _
                (interp.mode_subst_single η μ δ ξ τ m)).
      iApply (sem_typed_MApp (λ ν, interp._ty η (ν :: μ) δ τ ξ)
                _ (interp._mode μ m)).
      apply fundamental in Ht. iPoseProof Ht as "Ht".
      iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* TAlloc *) iApply sem_typed_alloc. apply fundamental in Ht.
      iPoseProof Ht as "Ht". iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* TLoad *) iApply sem_typed_load_expr. apply fundamental in Ht.
      iPoseProof Ht as "Ht". iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* TStore *) admit.
    + (* TAllocTape *) iApply sem_typed_alloctape. apply fundamental in Ht.
      iPoseProof Ht as "Ht". iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* TRand *)
      (* BLOCKED: needs a coupling lemma that reads TWO labelled (tape)
         [Rand] operations in a single step so they yield equal values
         (to inhabit [sem_ty_nat]).  The interp of the tape argument is
         [sem_ty_tape], whose invariant holds two EMPTY same-[N] tapes
         [α1 ↪ (N;[])] and [α2 ↪ₛ (N;[])].  The available probblaze
         coupling primitives only couple a labelled tape with an
         UNLABELLED rand ([brel_couple_TU]/[brel_couple_UT],
         [wp_couple_tape_rand]/[wp_couple_rand_tape]) or fragment-couple
         two tapes by presampling ([brel_couple_TT_frag]); none couples
         two labelled empty-tape reads.  Deterministic [step_rand] on the
         right spec tape is impossible since the tape is empty, and the
         presampling coupling cannot be performed under the regular [inv]
         of [sem_ty_tape] (it is not a single atomic step).  Missing:
         a [brel_couple_tape_tape] / [wp_couple_tape_tape] coupling rule
         (probabilistic core, out of scope per task). *)
      admit.
    + (* TRandU *) iApply sem_typed_randu;
        [apply fundamental in Ht1 as Ht | apply fundamental in Ht2 as Ht];
        iPoseProof Ht as "Ht"; iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* TFold *)
      iApply (sem_typed_fold (λ α, interp._ty (α :: η) μ δ τ ξ)).
      iApply (sem_typed_type_cong _ _ _ _ _ _ _
                (symmetry (interp.ty_subst_single η μ δ ξ τ (μ: τ)%ty))).
      apply fundamental in Ht. iPoseProof Ht as "Ht".
      iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* TUnfold *)
      iApply (sem_typed_type_cong _ _ _ _ _ _ _
                (interp.ty_subst_single η μ δ ξ τ (μ: τ)%ty)).
      iApply (sem_typed_unfold (λ α, interp._ty (α :: η) μ δ τ ξ)).
      apply fundamental in Ht. iPoseProof Ht as "Ht".
      iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* TPack *)
      iApply (sem_typed_pack (λ α, interp._ty (α :: η) μ δ τ ξ)
                (interp._ty η μ δ τ' ξ)).
      iApply (sem_typed_type_cong _ _ _ _ _ _ _
                (symmetry (interp.ty_subst_single η μ δ ξ τ τ'))).
      apply fundamental in Ht. iPoseProof Ht as "Ht".
      iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* TUnpack *)
      (* The [TUnpack] statement bug fix in [types.v] (shifting the body's
         effect [ρ] and output ctx [Γ3] by [ren (+1)], consistently with the
         already-shifted [Γ2]/[τ2]) makes the shift-cancellation go through:
         instantiating the body IH at the extended type-env [τ0::η] and
         transporting along [sem_typed_sub] with the weakening lemmas
         [interp.ctx_tweaken] (ctx), [interp.row_tweaken] (effect) and
         [interp.ty_tweaken] (result) reconciles it with the OUTER
         [interp_η ρ]/[interp_η Γ2]/[interp_η Γ3]/[interp_η τ2] required by
         [sem_typed_unpack_gen].  The two added freshness premises
         [x ∉ ctx_dom Γ2/Γ3] discharge the binder-non-clash side conditions
         of [sem_typed_unpack_gen] via [ctx_dom_env_dom]; the binder-general
         lemma [sem_typed_unpack_gen] handles the [BAnon] case. *)
      iApply (sem_typed_unpack_gen (λ τ0, interp._ty (τ0 :: η) μ δ τ ξ)
                _ _ _ ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ)) <$> Γ2)).
      { destruct x as [|s]; [done|]. by eapply ctx_dom_env_dom. }
      { destruct x as [|s]; [done|]. by eapply ctx_dom_env_dom. }
      { apply fundamental in Ht1. iPoseProof Ht1 as "Ht".
        iApply ("Ht" $! _ _ _ _ ∅ Hδ). }
      iIntros (τ0).
      apply fundamental in Ht2. iPoseProof Ht2 as "Ht".
      iSpecialize ("Ht" $! (τ0 :: η) μ δ ξ ∅ Hδ).
      iEval (cbn [ctx_insert fmap list_fmap]) in "Ht".
      iApply (sem_typed_sub with "[][][][] Ht").
      { rewrite /env_le /tc_opaque. iModIntro. iIntros (γ) "H".
        destruct x as [|s]; [by rewrite ctx_tweaken|].
        rewrite !env_sem_typed_cons. iDestruct "H" as "[$ H]".
        by rewrite ctx_tweaken. }
      { rewrite /env_le /tc_opaque. iModIntro. iIntros (γ) "H".
        by rewrite ctx_tweaken. }
      { iEval (rewrite (interp.row_tweaken ρ τ0 η μ δ ξ)).
        iApply sem_row.row_le_refl. }
      { iEval (rewrite (interp.ty_tweaken τ2 τ0 η μ δ ξ)).
        iApply sem_types.ty_le_refl. }
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
    + (* TAbs_pure_typed *)
      (* The [TAbs_pure] rule shifts its premise context by [⤉] (a fresh
         TYPE binder), so the body IH at the EXTENDED type-env [α::η]
         cancels the shift via [interp.ctx_tweaken]. *)
      iApply (sem_typed_TLam (λ α, interp._ty (α :: η) μ δ τ ξ)).
      iIntros (α). apply fundamental_pure in Hp. iPoseProof Hp as "H".
      iSpecialize ("H" $! (α :: η) μ δ ξ).
      rewrite /sem_oval_typed /tc_opaque.
      iModIntro. iIntros (vs) "Henv".
      iApply "H". by rewrite interp.ctx_tweaken.
    + (* RAbs_pure_typed *)
      (* The [RAbs_pure] rule row-shifts its premise context, so the body
         IH at the EXTENDED row-env [θ::ξ] cancels the shift via
         [interp.ctx_rweaken]. *)
      iApply (sem_typed_RLam (λ θ, interp._ty η μ δ τ (θ :: ξ))).
      iIntros (θ). apply fundamental_pure in Hp. iPoseProof Hp as "H".
      iSpecialize ("H" $! η μ δ (θ :: ξ)).
      rewrite /sem_oval_typed /tc_opaque.
      iModIntro. iIntros (vs) "Henv".
      iApply "H". by rewrite interp.ctx_rweaken.
    + (* MAbs_pure_typed *)
      (* The [MAbs_pure] rule mode-shifts its premise context, so the body
         IH at the EXTENDED mode-env [ν::μ] cancels the shift via
         [interp.ctx_mweaken]. *)
      iApply (sem_typed_MLam (λ ν, interp._ty η (ν :: μ) δ τ ξ)).
      iIntros (ν). apply fundamental_pure in Hp. iPoseProof Hp as "H".
      iSpecialize ("H" $! η (ν :: μ) δ ξ).
      rewrite /sem_oval_typed /tc_opaque.
      iModIntro. iIntros (vs) "Henv".
      iApply "H". by rewrite interp.ctx_mweaken.
Admitted.

End fundamental.
