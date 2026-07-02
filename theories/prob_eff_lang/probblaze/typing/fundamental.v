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

(* Expose ONLY the top-level constructor under [lbl_resolve] on BOTH related
   terms, so the compatibility lemmas fire while the (opaque) [lbl_resolve]
   on the immediate subexpressions stays intact -- it then matches verbatim
   the form produced by the recursive [fundamental] IH.  Exactly one branch
   fires per [destruct]ed constructor; cheap (single rewrite, opaque body). *)
Ltac push_lr_one :=
  first [ rewrite lbl_resolve_rec
        | rewrite lbl_resolve_app | rewrite lbl_resolve_unop
        | rewrite lbl_resolve_binop | rewrite lbl_resolve_if
        | rewrite lbl_resolve_pair | rewrite lbl_resolve_fst
        | rewrite lbl_resolve_snd | rewrite lbl_resolve_injl
        | rewrite lbl_resolve_injr | rewrite lbl_resolve_case
        | rewrite lbl_resolve_allocn | rewrite lbl_resolve_load
        | rewrite lbl_resolve_store | rewrite lbl_resolve_alloctape
        | rewrite lbl_resolve_rand | rewrite lbl_resolve_effect
        | rewrite lbl_resolve_do_label | rewrite lbl_resolve_do_name
        | rewrite lbl_resolve_handle_label | rewrite lbl_resolve_handle_name
        | idtac ].
Ltac push_lr := push_lr_one; push_lr_one.

Lemma ctx_dom_env_dom x Γ :
  ∀ η μ δ ξ, x ∉ ctx_dom Γ → x ∉ env_dom ((λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> Γ).
Proof.
  intros η μ δ ξ Hnin. induction Γ as [| (y, κ) Γ' IH]; simpl.
  - rewrite env_dom_nil. apply not_elem_of_nil.
  - rewrite env_dom_cons. apply not_elem_of_cons. split.
    + intros ->. apply Hnin. rewrite /ctx_dom /=. set_solver.
    + apply IH. rewrite /ctx_dom /= in Hnin. set_solver.
Qed.

(* In a well-typed term every free effect NAME [s] is either in [dom Δ] or
   bound by an enclosing [Effect s].  So resolving by a map [m] DISJOINT from
   [dom Δ] is the identity (the in-scope [Do (EffName s)] all have
   [s ∈ dom Δ], hence [s ∉ dom m]; the [Effect s] binder deletes [s] from
   [m]).  A PURE term is typed without any effect context, so its body is
   even effect-free and resolution is the identity for ANY [m].  These
   collapse the [lbl_resolve] wrapper to the literal expression at the
   [Pure]/value interfaces, where [fundamental_pure]/[fundamental_val] work
   on the literal expression. *)
Lemma typed_lbl_resolve_id Δ Γ1 e ρ τ Γ2 :
  Δ .| Γ1 ⊢ₜ e : ρ : τ ⊣ Γ2 → ∀ rm, dom rm ## dom Δ → lbl_resolve rm e = e
  with pure_lbl_resolve_id Δ Γ e τ :
  Δ ..| Γ ⊢ₚ e : τ → ∀ rm, dom rm ## dom Δ → lbl_resolve rm e = e.
Proof.
  - intros Ht. induction Ht; intros rm Hdm;
      (* Structural cases: push [lbl_resolve] through constructors and the
         desugaring [Lam]/[Rec] wrappers (e.g. [Match]/[TUnpack]), then close
         each typed subexpression by its IH (same [Δ], same [Hdm]).  Repeat to
         reach subexpressions nested under desugaring wrappers. *)
      rewrite ?lbl_resolve_val ?lbl_resolve_var
              ?lbl_resolve_app ?lbl_resolve_unop ?lbl_resolve_binop
              ?lbl_resolve_if ?lbl_resolve_pair ?lbl_resolve_fst
              ?lbl_resolve_snd ?lbl_resolve_injl ?lbl_resolve_injr
              ?lbl_resolve_case ?lbl_resolve_allocn ?lbl_resolve_load
              ?lbl_resolve_store ?lbl_resolve_alloctape ?lbl_resolve_rand
              ?lbl_resolve_rec;  (* [rec] last: also pushes desugaring Lams *)
      repeat match goal with
        | IH : ∀ rm, dom rm ## dom ?D → lbl_resolve rm ?e0 = ?e0
          |- context[lbl_resolve rm ?e0] => rewrite (IH rm Hdm)
        end;
      try reflexivity.
    (* Remaining goals (order-independent): [Pure] (delegate), [Effect]
       (fresh binder), and [Do]/[Handle] with in-scope effect NAME [s]
       ([Δ !! s = Some ()], so [s ∉ dom rm]).  Hypotheses matched by shape. *)
    all: first
      [ (* Pure *) match goal with
          Hp : _ ..| _ ⊢ₚ _ : _ |- _ => by rewrite (pure_lbl_resolve_id _ _ _ _ Hp)
        end
      | (* Effect (fresh binder [s]) *)
        rewrite lbl_resolve_effect; f_equal;
          match goal with
            IH : ∀ rm, dom rm ## dom (<[?z:=tt]> _) → _ |- _ =>
              erewrite IH; [reflexivity|rewrite dom_insert_L; set_solver]
          end
      | (* Do (EffName s), [s ∈ dom Δ] disjoint from [rm] *)
        rewrite lbl_resolve_do_name;
          match goal with Hs : _ !! ?z = Some () |- _ =>
            replace (rm !! z) with (@None label) by
              (symmetry; apply not_elem_of_dom; apply elem_of_dom_2 in Hs;
               set_solver)
          end; simpl;
          match goal with
            IH : ∀ rm, dom rm ## dom _ → lbl_resolve rm ?e0 = ?e0 |- _ =>
              erewrite IH; [reflexivity|eassumption]
          end
      | (* Handle (EffName s); handler args are [Lam]-wrapped *)
        rewrite lbl_resolve_handle_name;
          match goal with Hs : _ !! ?z = Some () |- _ =>
            replace (rm !! z) with (@None label) by
              (symmetry; apply not_elem_of_dom; apply elem_of_dom_2 in Hs;
               set_solver)
          end; simpl; rewrite ?lbl_resolve_rec;
          repeat match goal with
            IH : ∀ rm, dom rm ## dom _ → lbl_resolve rm ?e0 = ?e0
            |- context[lbl_resolve _ ?e0] => erewrite IH by eassumption
          end; reflexivity ].
  - intros Hp. induction Hp; intros rm Hdm;
      rewrite ?lbl_resolve_val ?lbl_resolve_var ?lbl_resolve_rec
              ?lbl_resolve_pair ?lbl_resolve_injl ?lbl_resolve_injr;
      repeat match goal with
             | IH : ∀ rm, dom rm ## dom Δ → lbl_resolve rm ?e0 = ?e0
               |- context[lbl_resolve rm ?e0] => rewrite (IH rm)
             end;
      try reflexivity; try done.
    + (* Rec_pure: body typed under [∅], resolution is identity for any rm. *)
      f_equal. by apply (typed_lbl_resolve_id _ _ _ _ _ _ H3 rm). 
Qed.

Lemma disjointness_ctx_sem_jugdment Γ1 e e' η μ δ ρ ξ τ Γ2 :
 □(erase_ctx η μ δ ξ (le.row_to_disj_ctx ρ) -∗ sem_typed Γ1 e e' (interp._row η μ δ ρ ξ) τ Γ2) -∗
  sem_typed Γ1 e e' (interp._row η μ δ ρ ξ) τ Γ2.
Proof.
  iIntros "#H".
  iIntros (vs) "!# Hvs".
  iApply brel_learn.
  iIntros "#Hvalid #Hdistinct".
  iPoseProof erase_ctx_row_to_disj_ctx as "#HD".
  iCombine "Hdistinct Hvalid" as "Hvd".
  iDestruct ("HD" with "Hvd") as "Herase".
  iDestruct ("H" with "Herase") as "Hrel".
  iDestruct ("Hrel" with "Hvs") as "Hbrel".
  done.
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
  with fundamental_pure Δ Γ e τ :
    Δ ..| Γ ⊢ₚ e : τ → ⊢ bin_log_pure_related Δ Γ e e τ.
Proof.
  - intros Ht. destruct Ht; iIntros (η μ δ ξ' Hδ).
    + (* Var_typed *) rewrite !lbl_resolve_var. iApply sem_typed_var. 
    + (* Val_typed *) rewrite !lbl_resolve_val.
      iApply sem_typed_val; by iApply fundamental_val.
    + (* Pure_typed *)
      rewrite fmap_app. iApply sem_typed_oval.
      by iApply fundamental_pure.
    + (* Pair_typed *)
      (* The new [ρ R⪯T τ2] premise supplies the [RowTypeSub] typeclass
         argument of [sem_typed_pair_gen] via [row_type_sub_sound]. *)
      push_lr.
      iApply sem_typed_pair_gen;
        [by eapply interp.row_type_sub_sound|apply fundamental in Ht1 as Ht|apply fundamental in Ht2 as Ht];
        iPoseProof Ht as "Ht"; iApply ("Ht" $! _ _ _ _ Hδ).
    + (* Fst_typed *) push_lr. iApply sem_typed_fst_expr. apply fundamental in Ht.
      iPoseProof Ht as "Ht". by iApply "Ht". 
    + (* Snd_typed *) push_lr. iApply sem_typed_snd_expr. apply fundamental in Ht.
      iPoseProof Ht as "Ht". by iApply "Ht". 
    + (* InjL_typed *) push_lr. iApply sem_typed_left_inj. apply fundamental in Ht.
      iPoseProof Ht as "Ht". by iApply "Ht". 
    + (* InjR_typed *) push_lr. iApply sem_typed_right_inj. apply fundamental in Ht.
      iPoseProof Ht as "Ht". by iApply "Ht". 
    + (* Match_typed *) push_lr. iApply sem_typed_match;
        [ destruct x; [|eapply ctx_dom_env_dom]; apply H
        | destruct x; [|eapply ctx_dom_env_dom]; apply H0
        | destruct y; [|eapply ctx_dom_env_dom]; apply H1
        | destruct y; [|eapply ctx_dom_env_dom]; apply H2
        | apply fundamental in Ht1; iPoseProof Ht1 as "Ht";
          by iApply "Ht"
        | apply fundamental in Ht2; iPoseProof Ht2 as "Ht";
            destruct x ; by iApply "Ht" 
        | apply fundamental in Ht3; iPoseProof Ht3 as "Ht";
            destruct y; by iApply "Ht"].
    + (* If_typed *) push_lr. iApply sem_typed_if;
        [ apply fundamental in Ht1; iPoseProof Ht1 as "Ht";
            by iApply "Ht"
        | apply fundamental in Ht2; iPoseProof Ht2 as "Ht";
          by iApply "Ht"
        | apply fundamental in Ht3; iPoseProof Ht3 as "Ht";
          by iApply "Ht" ].
    + (* Rec_typed *)
      (* The conclusion context is [Γ ;; Γ'] (= [Γ ++ Γ']) and the type is
         [![m](arr)]; route via [sem_typed_oval] to peel [Γ'] off the
         oval-typing of [Γ], then [sem_oval_typed_ufun_rec] builds the
         recursive closure.  The captured env [interp Γ] is [MultiE] via
         [multi_env_sound] (using the strengthened [le.MultiC Γ] premise);
         freshness comes from [ctx_dom_env_dom].  The body context of
         [sem_oval_typed_ufun_rec] matches the IH context definitionally:
         [interp (<[f]><[x]>Γ) = (f, ![m]arr) ::? (x, τ) ::? interp Γ]. *)
      push_lr.
      rewrite /ctx_append fmap_app /=.
      iApply sem_typed_oval.
      pose proof (multi_env_sound Γ H2 η μ δ ξ') as HME.
      iApply (@sem_oval_typed_ufun_rec _ _ (interp._ty η μ δ τ ξ')
                (interp._row η μ δ ρ ξ') (interp._ty η μ δ κ ξ')
                (interp._mode μ m) _ f x
                (lbl_resolve (resolve_l Δ δ) e)
                (lbl_resolve (resolve_r Δ δ) e) HME).
      { destruct x as [|s]; [done|]. by eapply ctx_dom_env_dom. }
      { destruct f as [|s]; [done|]. by eapply ctx_dom_env_dom. }
      { exact H. }
      apply fundamental in Ht. iPoseProof Ht as "Ht".
      iSpecialize ("Ht" $! η μ δ ξ' Hδ).
      destruct f as [|sf]; destruct x as [|sx]; simpl in *; iApply "Ht".
    + (* App_typed *) 
      iApply disjointness_ctx_sem_jugdment.
      iIntros "!# #HD".
      iApply (sem_typed_app_gen (interp._ty η μ δ τ ξ') (interp._row η μ δ ρ' ξ') (interp._row η μ δ ρ ξ') (interp._row η μ δ ρ'' ξ') ).
      { by eapply row_type_sub_sound in H1. }
      { by eapply row_env_sub_sound in H2. }
      { eapply row_le_sound in H. by iApply H. }
      { eapply row_le_sound in H0. by iApply H0. }
      { apply fundamental in Ht2.
        iPoseProof Ht2 as "Ht2".
        by iApply "Ht2". }
      { apply fundamental in Ht1.
        iPoseProof Ht1 as "Ht1".
        by iApply "Ht1". }
    + (* TAbsElim_typed *)
      iApply (sem_typed_type_cong _ _ _ _ _ _ _
                (interp.ty_subst_single η μ δ ξ' τ τ')).
      iApply (sem_typed_TApp (λ α, interp._ty (α :: η) μ δ τ ξ')
                (interp._ty η μ δ τ' ξ')).
      apply fundamental in Ht. iPoseProof Ht as "Ht".
      by iApply "Ht". 
    + (* RAbsElim_typed *)
      iApply (sem_typed_type_cong _ _ _ _ _ _ _
                (interp.row_subst_single η μ δ ξ' τ ρ')).
      iApply (sem_typed_RApp (λ θ, interp._ty η μ δ τ (θ :: ξ'))
                _ (interp._row η μ δ ρ' ξ')).
      apply fundamental in Ht. iPoseProof Ht as "Ht".
      by iApply "Ht". 
    + (* MAbsElim_typed *)
      iApply (sem_typed_type_cong _ _ _ _ _ _ _
                (interp.mode_subst_single η μ δ ξ' τ m)).
      iApply (sem_typed_MApp (λ ν, interp._ty η (ν :: μ) δ τ ξ')
                _ (interp._mode μ m)).
      apply fundamental in Ht. iPoseProof Ht as "Ht".
      by iApply "Ht". 
    + (* TAlloc *) push_lr. iApply sem_typed_alloc. apply fundamental in Ht.
      iPoseProof Ht as "Ht". by iApply "Ht". 
    + (* TLoad *) push_lr. simpl. rewrite !lbl_resolve_var. iApply sem_typed_load. 
    + (* TStore *)
      (* Linear-reference store. *)
      push_lr.
      rewrite !lbl_resolve_var. simpl.
      iApply sem_typed_store. 
      apply fundamental in Ht. 
        iPoseProof Ht as "Ht"; by iApply "Ht". 
    + (* TAllocTape *) push_lr. iApply sem_typed_alloctape. apply fundamental in Ht.
      iPoseProof Ht as "Ht". by iApply "Ht". 
    + (* TRand *)
      (* The labelled-tape [Rand].  Uses the new coupling primitive
         [wp_couple_rand_lbl_rand_lbl] (coupling_rules.v), applied via
         [sem_typed_rand] (compatibility.v) under [brel_atomic_l] + the
         [sem_ty_tape] invariant: both empty-tape reads step together in
         one atomic step to equal values, so [sem_ty_nat] holds. *)
      push_lr. iApply sem_typed_rand;
        [apply fundamental in Ht1 as Ht | apply fundamental in Ht2 as Ht];
        iPoseProof Ht as "Ht"; by iApply "Ht".
    + (* TRandU *) push_lr. iApply sem_typed_randu;
        [apply fundamental in Ht1 as Ht | apply fundamental in Ht2 as Ht];
        iPoseProof Ht as "Ht"; by iApply "Ht". 
    + (* TFold *)
      iApply (sem_typed_fold (λ α, interp._ty (α :: η) μ δ τ ξ')).
      iApply (sem_typed_type_cong _ _ _ _ _ _ _
                (symmetry (interp.ty_subst_single η μ δ _ τ (μ: τ)%ty))).
      apply fundamental in Ht. iPoseProof Ht as "Ht".
      by iApply "Ht". 
    + (* TUnfold *)
      iApply (sem_typed_type_cong _ _ _ _ _ _ _
                (interp.ty_subst_single η μ δ _ τ (μ: τ)%ty)).
      iApply (sem_typed_unfold (λ α, interp._ty (α :: η) μ δ τ _)).
      apply fundamental in Ht. iPoseProof Ht as "Ht".
      by iApply "Ht". 
    + (* TPack *)
      iApply (sem_typed_pack (λ α, interp._ty (α :: η) μ δ τ _)
                (interp._ty η μ δ τ' _)).
      iApply (sem_typed_type_cong _ _ _ _ _ _ _
                (symmetry (interp.ty_subst_single η μ δ _ τ τ'))).
      apply fundamental in Ht. iPoseProof Ht as "Ht".
      by iApply "Ht". 
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
      iApply (sem_typed_unpack_gen (λ τ0, interp._ty (τ0 :: η) μ δ τ ξ')
                _ _ _ ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ2)).
      { destruct x as [|s]; [done|]. by eapply ctx_dom_env_dom. }
      { destruct x as [|s]; [done|]. by eapply ctx_dom_env_dom. }
      { apply fundamental in Ht1. iPoseProof Ht1 as "Ht".
        by iApply "Ht".  }
      iIntros (τ0).
      apply fundamental in Ht2. iPoseProof Ht2 as "Ht".
      iSpecialize ("Ht" $! (τ0 :: η) μ δ ξ' Hδ).
      iEval (cbn [ctx_insert fmap list_fmap]) in "Ht".
      iApply (sem_typed_sub with "[][][][] Ht").
      { rewrite /env_le /tc_opaque. iModIntro. iIntros (γ) "H".
        destruct x as [|s]; [by rewrite ctx_tweaken|].
        rewrite !env_sem_typed_cons. iDestruct "H" as "[$ H]".
        by rewrite ctx_tweaken. }
      { rewrite /env_le /tc_opaque. iModIntro. iIntros (γ) "H".
        by rewrite ctx_tweaken. }
      { iEval (rewrite (interp.row_tweaken ρ τ0 η μ δ ξ')).
        iApply sem_row.row_le_refl. }
      { iEval (rewrite (interp.ty_tweaken τ2 τ0 η μ δ ξ')).
        iApply sem_types.ty_le_refl. }
    + (* Effect_typed *)
      (* MECHANISED.  The δ-resolved goal is
           [effect s (lbl_resolve (delete s (resolve_l Δ δ)) e)]  /  [... _r ...].
         Route via the binder-general [sem_typed_effect_gen] and thread the IH
         at [δ' := <[s:=(l1,l2)]>δ]: [resolve_map_insert] +
         [lbl_resolve_insert_subst] align the body ([lbl_subst s l · lbl_resolve
         (delete s ..)] = [lbl_resolve (<[s:=l]>..)]) and the precondition
         [dom (<[s]>Δ) ⊆ dom δ'] follows from [Hδ].  The IH's δ'-interpretations
         are then reconciled with the goal's δ-interpretations:
           - result type [interp τ]:  δ-irrelevant ([interp.ty_delta_irrel],
             [s∉τ]) via [sem_typed_type_cong];
           - effect row [interp Abs_ρ = sem_row_cons (interp (SAbs s)) (interp ρ)]:
             the head [interp (SAbs s) = sem_sig_eff (δ'!!!s).1 (δ'!!!s).2 ⊥ ⊤ =
             sem_sig_bottom l1 l2] is DEFINITIONAL ([δ'!!!s = (l1,l2)]) and the
             tail is δ-irrelevant ([interp.row_delta_irrel], [s∉ρ]) — combined
             via [sem_typed_row_cong];
           - contexts [interp Γ1]/[interp Γ2]:  pointwise δ-irrelevant
             ([interp.ctx_elem_delta_irrel]), via [sem_typed_env_cong].  Both
             [s∉Γ1] and [s∉Γ2] are extracted from the freshness premise, now
             taken over [Γ1 ++ Γ2] ([vars._ctx] distributes over [++]). *)
      iApply sem_typed_effect_gen. simpl.
      apply fundamental in Ht.
      iIntros (l1 l2).
      iPoseProof Ht as "Ht".
      rewrite /bin_log_related.
      iSpecialize ("Ht" $! η μ (<[s:=(l1,l2)]>δ) ξ').
      iSpecialize ("Ht" with "[]").
      { iPureIntro. rewrite !dom_insert_L. set_solver. }
      rewrite (resolve_map_insert fst Δ δ s (l1,l2))
              (resolve_map_insert snd Δ δ s (l1,l2)).
      rewrite -!lbl_resolve_insert_subst.
      destruct H as (Hctx & Hrow & Hty).
      assert (s ∉ vars._ctx Γ1) as HΓ1
        by (intros Hin; apply Hctx;
            rewrite /vars._ctx fmap_app union_list_app_L; set_solver).
      assert (s ∉ vars._ctx Γ2) as HΓ2
        by (intros Hin; apply Hctx;
            rewrite /vars._ctx fmap_app union_list_app_L; set_solver).
      assert (interp._ty η μ (<[s:=(l1,l2)]>δ) τ ξ' ≡ interp._ty η μ δ τ ξ')
        as Hτeq by (by apply (interp.ty_delta_irrel δ s (l1,l2))).
      assert (interp._row η μ (<[s:=(l1,l2)]>δ) Abs_ρ ξ'
              ≡ sem_row.sem_row_cons (sem_sig.sem_sig_bottom l1 l2)
                  (interp._row η μ δ ρ ξ')) as Hρeq.
      { subst Abs_ρ; simpl.
        rewrite (interp.row_delta_irrel δ s (l1,l2) ρ η μ ξ' Hrow)
                lookup_total_insert_eq /=. reflexivity. }
      assert (∀ (Γ0 : list (string*type)), s ∉ vars._ctx Γ0 →
        env_equiv_pw
          ((λ '(s0, τ0), (s0, interp._ty η μ δ τ0 ξ')) <$> Γ0)
          ((λ '(s0, τ0), (s0, interp._ty η μ (<[s:=(l1,l2)]>δ) τ0 ξ'))
             <$> Γ0)) as Henv.
      { intros Γ0 HΓ0. rewrite /env_equiv_pw.
        induction Γ0 as [|[x α] Γ0' IH]; simpl; [constructor|].
        constructor.
        - split; [done|]. symmetry.
          apply (interp.ctx_elem_delta_irrel δ s (l1,l2) ((x,α)::Γ0') x α);
            [done|by left].
        - apply IH. intros Hin. apply HΓ0.
          rewrite /vars._ctx /= in Hin |- *. set_solver. }
      iApply (sem_typed_row_cong _ _ _ _ _ _ _ (symmetry Hρeq)).
      iApply (sem_typed_type_cong _ _ _ _ _ _ _ (symmetry Hτeq)).
      iApply (sem_typed_env_cong _ _ _ _ _ _ _ _ (Henv Γ1 HΓ1) (Henv Γ2 HΓ2)).
      iApply "Ht".
    + (* Do_typed *)
      (* With [bin_log_related] now relating the δ-resolved expression, the
         goal carries [Do (EffLabel (δ!!!s).1) (lbl_resolve_l e)] on the left
         and [Do (EffLabel (δ!!!s).2) (lbl_resolve_r e)] on the right (since
         [s ∈ dom Δ ⊆ dom δ]).  This matches [sem_typed_do]'s conclusion
         [do: op.1 e1 / do: op.2 e2] with [op := δ!!!s].  The row head aligns
         DEFINITIONALLY with [interp (SFlip m (SSig s ι κ))]; the result type
         [interp (κ.[τ/])] is reconciled with [B (interp τ)] by
         [ty_subst_single]+[sem_typed_type_cong]; the mode side condition by
         [mode_env_sound] from [m m⪯C Γ2]. *)
      rewrite !lbl_resolve_do_name.
      rewrite !resolve_map_lookup H0 /=.
      iApply (sem_typed_type_cong _ _ _ _ _ _ _
                (interp.ty_subst_single η μ δ ξ' κ τ)).
      pose proof (interp.mode_env_sound m Γ2 H η μ δ ξ') as Hms.
      iApply (@sem_typed_do _ _ (interp._mode μ m) (interp._ty η μ δ τ ξ')
                _ (δ !!! s)
                (λ α, interp._ty (α :: η) μ δ ι ξ')
                (λ α, interp._ty (α :: η) μ δ κ ξ') _ _ _ _ Hms).
      apply fundamental in Ht. iPoseProof Ht as "Ht".
      iApply (sem_typed_type_cong _ _ _ _ _ _ _
                (symmetry (interp.ty_subst_single η μ δ ξ' ι τ))).
      by iApply "Ht". 
    + (* DeepHandle_typed *)
      (* The lbl_resolve front-matter goes through:
         [rewrite !lbl_resolve_handle_name !resolve_map_lookup H /=]
         resolves the effect NAME [s] to the label [δ!!!s] (since
         [s ∈ dom Δ ⊆ dom δ]) and [rewrite !lbl_resolve_rec] pushes through
         the [Lam x (Lam k h)]/[Lam y r] wrappers (effect names are a
         SEPARATE namespace from value binders, so [lbl_resolve_rec] does not
         delete [x]/[k]/[y]), leaving the clean goal
           [interp (Γ1;;Γ3) ⊨ Handle Deep m (δ!!!s).1 (lbl_l e)
              (λ:x k, lbl_l h) (λ:y, lbl_l r) ≤ ...
              : sem_row_cons (interp σ) (interp ρ0) : interp τ' ⊣ interp Γ3]
         which IS the [handle:] notation (mode [m] picks
         [sem_typed_deep_handler_MS]/[_OS] after [destruct m]).

         GENUINE OBSTACLE — row-shape mismatch between this syntactic rule and
         the available compatibility lemma.  [sem_typed_deep_handler_{MS,OS}]
         is a DISCHARGING handler: body at [σ_sem · ρ'_sem], OUTPUT [ρ'_sem]
         (the handled signature is removed from the output), clauses [h]/[r]
         typed at [ρ'_sem].  But the syntactic [DeepHandle_typed] is a
         FORWARDING handler: body [e : ρ' = RCons (SFlip m (SSig s ι κ)) ρ0]
         (so [interp ρ' = proto · interp ρ0], matching [σ_sem := proto],
         [ρ'_sem := interp ρ0]), yet the conclusion is
         [ρ = RCons σ ρ0] with [eff_name_from_sig σ = s] — i.e. an
         [s]-signature [σ] is KEPT at the head of the output, and the clauses
         [h]/[r] are typed at [ρ] (with [σ]), NOT at [ρ0].  Reconciling
         [interp ρ0] (compat output / clause row) with [interp σ · interp ρ0]
         (syntactic output / clause row) would need BOTH
         [interp ρ0 ≤ᵣ interp σ · interp ρ0] (to lift the output via
         [sem_typed_sub_row]) AND [interp σ · interp ρ0 ≤ᵣ interp ρ0] (to feed
         the clauses) — contradictory for a non-vacuous [σ].  Closing this
         needs a NEW compatibility lemma for a forwarding handler whose output
         re-installs [σ] (out of scope of the lbl_resolve refinement; the
         four existing handler lemmas are all discharging). *)
      destruct m.
      * (* DeepHandle OS *)
        rewrite !lbl_resolve_handle_name.
        rewrite !resolve_map_lookup H0 /=.
        rewrite !lbl_resolve_rec.
        unfold ctx_append. rewrite fmap_app.
        pose proof (multi_env_sound Γ3 H η μ δ ξ') as HME.
        pose proof (sig_labels_eff_name σ η μ δ ξ') as Hlbl.
        rewrite H1 in Hlbl.
        destruct x as [|xs]; [| destruct k as [|ks]; [| destruct y as [|ys]]].
        4:{
          iApply (sem_typed_deep_handler_OS (δ !!! s)
                    (λ α, interp._ty (α :: η) μ δ ι ξ')
                    (λ α, interp._ty (α :: η) μ δ κ ξ')
                    (interp._ty η μ δ τ ξ')
                    (interp._ty η μ δ τ' ξ')
                    (interp._eff_sig η μ δ σ ξ')
                    (interp._row η μ δ ρ0 ξ')
                    _ _ _ xs ys ks _ _ _ _ _ _
                    _ _ _ _ _ _ Hlbl).
          - apply fundamental in Ht1. iPoseProof Ht1 as "Ht".
            iApply ("Ht" $! η μ δ ξ' Hδ).
          - iIntros (α). apply fundamental in Ht3. iPoseProof Ht3 as "Ht".
            iSpecialize ("Ht" $! (α :: η) μ δ ξ' Hδ).
            iEval (cbn [ctx_insert fmap list_fmap]) in "Ht".
            iApply (sem_typed_row_cong _ _ _ _ _ _ _
                      (symmetry (row_tweaken ρ α η μ δ ξ'))).
            iApply (sem_typed_type_cong _ _ _ _ _ _ _
                      (symmetry (ty_tweaken τ' α η μ δ ξ'))).
            assert (Htail : ∀ (Γ0 : ctx), env_equiv_pw
                      ((λ '(s0, τ0), (s0, interp._ty η μ δ τ0 ξ')) <$> Γ0)
                      ((λ '(s0, τ0), (s0, interp._ty (α :: η) μ δ τ0 ξ')) <$>
                         ((λ '(x, α0), (x, Autosubst_Classes.subst
                             (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0))
                            <$> Γ0)))
              by (intros Γ0; induction Γ0 as [|[z β] Γ0' IH]; simpl; [constructor|];
                  constructor; [split; [done|]|exact IH];
                  simpl; symmetry; apply (ty_tweaken β α η μ δ ξ')).
            assert (Hhead : (interp._ty (α :: η) μ δ
                         (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) ρ }-[ OS
                          ]-> Autosubst_Classes.subst
                                (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ')
                         ξ')
                      ≡ sem_types.sem_ty_mbang OS
                  (sem_types.sem_ty_arr
                     (sem_row.sem_row_cons (interp._eff_sig η μ δ σ ξ')
                        (interp._row η μ δ ρ0 ξ'))
                     (interp._ty (α :: η) μ δ κ ξ') (interp._ty η μ δ τ' ξ'))).
            { change (interp._ty (α :: η) μ δ
                         (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) ρ }-[ OS
                          ]-> Autosubst_Classes.subst
                                (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ')
                         ξ')
                with (sem_types.sem_ty_mbang OS
                  (sem_types.sem_ty_arr
                     (interp._row (α :: η) μ δ
                        (rename_type_row (Autosubst_Basics.lift 1%nat) ρ) ξ')
                     (interp._ty (α :: η) μ δ κ ξ')
                     (interp._ty (α :: η) μ δ (Autosubst_Classes.subst
                         (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ') ξ'))).
              rewrite (row_tweaken ρ α η μ δ ξ') (ty_tweaken τ' α η μ δ ξ').
              reflexivity. }
            assert (Hin : env_equiv_pw
                ((xs, interp._ty (α :: η) μ δ ι ξ')
                 :: (ks, sem_types.sem_ty_mbang OS
                       (sem_types.sem_ty_arr
                          (sem_row.sem_row_cons (interp._eff_sig η μ δ σ ξ')
                             (interp._row η μ δ ρ0 ξ'))
                          (interp._ty (α :: η) μ δ κ ξ') (interp._ty η μ δ τ' ξ')))
                    :: ((λ '(s0, τ0), (s0, interp._ty η μ δ τ0 ξ')) <$> Γ3))
                ((xs, interp._ty (α :: η) μ δ ι ξ')
                 :: (ks, interp._ty (α :: η) μ δ
                       (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) ρ }-[ OS
                        ]-> Autosubst_Classes.subst
                              (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ')
                       ξ')
                    :: ((λ '(s0, τ0), (s0, interp._ty (α :: η) μ δ τ0 ξ')) <$>
                        ((λ '(x, α0), (x, Autosubst_Classes.subst
                            (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0))
                           <$> Γ3)))).
            { constructor; [split; [reflexivity|reflexivity]|].
              constructor; [split; [reflexivity| exact (symmetry Hhead)]|].
              exact (Htail Γ3). }
            iApply (sem_typed_env_cong _ _ _ _ _ _ _ _ Hin (Htail Γ3)).
            iApply "Ht".
          - apply fundamental in Ht2. iPoseProof Ht2 as "Ht".
            iSpecialize ("Ht" $! η μ δ ξ' Hδ).
            iEval (cbn [ctx_insert ctx_append fmap list_fmap]) in "Ht".
            rewrite fmap_app.
            iApply "Ht".
        }
        all: admit. (* BAnon binder subcases: see report *)
      * (* DeepHandle MS *)
        rewrite !lbl_resolve_handle_name.
        rewrite !resolve_map_lookup H0 /=.
        rewrite !lbl_resolve_rec.
        unfold ctx_append. rewrite fmap_app.
        pose proof (multi_env_sound Γ3 H η μ δ ξ') as HME.
        pose proof (sig_labels_eff_name σ η μ δ ξ') as Hlbl.
        rewrite H1 in Hlbl.
        destruct x as [|xs]; [| destruct k as [|ks]; [| destruct y as [|ys]]].
        4:{
          iApply (sem_typed_deep_handler_MS (δ !!! s)
                    (λ α, interp._ty (α :: η) μ δ ι ξ')
                    (λ α, interp._ty (α :: η) μ δ κ ξ')
                    MS
                    (interp._ty η μ δ τ ξ')
                    (interp._ty η μ δ τ' ξ')
                    (interp._eff_sig η μ δ σ ξ')
                    (interp._row η μ δ ρ0 ξ')
                    _ _ _ xs ys ks _ _ _ _ _ _
                    _ _ _ _ _ _ Hlbl).
          - apply fundamental in Ht1. iPoseProof Ht1 as "Ht".
            iApply ("Ht" $! η μ δ ξ' Hδ).
          - iIntros (α). apply fundamental in Ht3. iPoseProof Ht3 as "Ht".
            iSpecialize ("Ht" $! (α :: η) μ δ ξ' Hδ).
            iEval (cbn [ctx_insert fmap list_fmap]) in "Ht".
            iApply (sem_typed_row_cong _ _ _ _ _ _ _
                      (symmetry (row_tweaken ρ α η μ δ ξ'))).
            iApply (sem_typed_type_cong _ _ _ _ _ _ _
                      (symmetry (ty_tweaken τ' α η μ δ ξ'))).
            assert (Htail : ∀ (Γ0 : ctx), env_equiv_pw
                      ((λ '(s0, τ0), (s0, interp._ty η μ δ τ0 ξ')) <$> Γ0)
                      ((λ '(s0, τ0), (s0, interp._ty (α :: η) μ δ τ0 ξ')) <$>
                         ((λ '(x, α0), (x, Autosubst_Classes.subst
                             (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0))
                            <$> Γ0)))
              by (intros Γ0; induction Γ0 as [|[z β] Γ0' IH]; simpl; [constructor|];
                  constructor; [split; [done|]|exact IH];
                  simpl; symmetry; apply (ty_tweaken β α η μ δ ξ')).
            assert (Hhead : (interp._ty (α :: η) μ δ
                         (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) ρ }-[ MS
                          ]-> Autosubst_Classes.subst
                                (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ')
                         ξ')
                      ≡ sem_types.sem_ty_mbang MS
                  (sem_types.sem_ty_arr
                     (sem_row.sem_row_cons (interp._eff_sig η μ δ σ ξ')
                        (interp._row η μ δ ρ0 ξ'))
                     (interp._ty (α :: η) μ δ κ ξ') (interp._ty η μ δ τ' ξ'))).
            { change (interp._ty (α :: η) μ δ
                         (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) ρ }-[ MS
                          ]-> Autosubst_Classes.subst
                                (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ')
                         ξ')
                with (sem_types.sem_ty_mbang MS
                  (sem_types.sem_ty_arr
                     (interp._row (α :: η) μ δ
                        (rename_type_row (Autosubst_Basics.lift 1%nat) ρ) ξ')
                     (interp._ty (α :: η) μ δ κ ξ')
                     (interp._ty (α :: η) μ δ (Autosubst_Classes.subst
                         (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ') ξ'))).
              rewrite (row_tweaken ρ α η μ δ ξ') (ty_tweaken τ' α η μ δ ξ').
              reflexivity. }
            assert (Hin : env_equiv_pw
                ((xs, interp._ty (α :: η) μ δ ι ξ')
                 :: (ks, sem_types.sem_ty_mbang MS
                       (sem_types.sem_ty_arr
                          (sem_row.sem_row_cons (interp._eff_sig η μ δ σ ξ')
                             (interp._row η μ δ ρ0 ξ'))
                          (interp._ty (α :: η) μ δ κ ξ') (interp._ty η μ δ τ' ξ')))
                    :: ((λ '(s0, τ0), (s0, interp._ty η μ δ τ0 ξ')) <$> Γ3))
                ((xs, interp._ty (α :: η) μ δ ι ξ')
                 :: (ks, interp._ty (α :: η) μ δ
                       (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) ρ }-[ MS
                        ]-> Autosubst_Classes.subst
                              (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ')
                       ξ')
                    :: ((λ '(s0, τ0), (s0, interp._ty (α :: η) μ δ τ0 ξ')) <$>
                        ((λ '(x, α0), (x, Autosubst_Classes.subst
                            (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0))
                           <$> Γ3)))).
            { constructor; [split; [reflexivity|reflexivity]|].
              constructor; [split; [reflexivity| exact (symmetry Hhead)]|].
              exact (Htail Γ3). }
            iApply (sem_typed_env_cong _ _ _ _ _ _ _ _ Hin (Htail Γ3)).
            iApply "Ht".
          - apply fundamental in Ht2. iPoseProof Ht2 as "Ht".
            iSpecialize ("Ht" $! η μ δ ξ' Hδ).
            iEval (cbn [ctx_insert ctx_append fmap list_fmap]) in "Ht".
            rewrite fmap_app.
            iApply "Ht".
        }
        all: admit. (* BAnon binder subcases: see report *)
    + (* ShallowHandle_typed *)
      (* Same lbl_resolve front-matter and the same row-shape mismatch as
         [DeepHandle_typed] above: the body row resolves to
         [proto · interp ρ0] (matching [sem_typed_shallow_handler_{MS,OS}]'s
         [σ_sem := proto], [ρ'_sem := interp ρ0]), but the syntactic
         conclusion / clause row is [ρ = RCons σ ρ0] (an [s]-signature [σ]
         kept at the head), whereas the discharging compatibility lemma's
         output / clause row is the bare tail [interp ρ0].  The extra premise
         here, [H1 : ρ R⪯C Γ3], does not close the gap (it is a
         row-context-sub side condition, not the [interp ρ0 ↔ interp σ·ρ0]
         reconciliation).  Needs the same NEW forwarding-handler compatibility
         lemma. *)
      destruct m.
      * (* ShallowHandle OS *)
        rewrite !lbl_resolve_handle_name.
        rewrite !resolve_map_lookup H0 /=.
        rewrite !lbl_resolve_rec.
        unfold ctx_append. rewrite fmap_app.
        pose proof (multi_env_sound Γ3 H η μ δ ξ') as HME.
        pose proof (sig_labels_eff_name σ η μ δ ξ') as Hlbl.
        rewrite H1 in Hlbl.
        destruct x as [|xs]; [| destruct k as [|ks]; [| destruct y as [|ys]]].
        4:{
          iApply (sem_typed_shallow_handler_OS (δ !!! s)
                    (λ α, interp._ty (α :: η) μ δ ι ξ')
                    (λ α, interp._ty (α :: η) μ δ κ ξ')
                    (interp._ty η μ δ τ ξ')
                    (interp._ty η μ δ τ' ξ')
                    (interp._eff_sig η μ δ σ ξ')
                    (interp._row η μ δ ρ0 ξ')
                    _ _ _ xs ys ks _ _ _ _ _ _
                    _ _ _ _ _ _ Hlbl).
          - apply fundamental in Ht1. iPoseProof Ht1 as "Ht".
            iApply ("Ht" $! η μ δ ξ' Hδ).
          - iIntros (α). apply fundamental in Ht3. iPoseProof Ht3 as "Ht".
            iSpecialize ("Ht" $! (α :: η) μ δ ξ' Hδ).
            iEval (cbn [ctx_insert fmap list_fmap]) in "Ht".
            iApply (sem_typed_row_cong _ _ _ _ _ _ _
                      (symmetry (row_tweaken ρ α η μ δ ξ'))).
            iApply (sem_typed_type_cong _ _ _ _ _ _ _
                      (symmetry (ty_tweaken τ' α η μ δ ξ'))).
            assert (Htail : ∀ (Γ0 : ctx), env_equiv_pw
                      ((λ '(s0, τ0), (s0, interp._ty η μ δ τ0 ξ')) <$> Γ0)
                      ((λ '(s0, τ0), (s0, interp._ty (α :: η) μ δ τ0 ξ')) <$>
                         ((λ '(x, α0), (x, Autosubst_Classes.subst
                             (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0))
                            <$> Γ0)))
              by (intros Γ0; induction Γ0 as [|[z β] Γ0' IH]; simpl; [constructor|];
                  constructor; [split; [done|]|exact IH];
                  simpl; symmetry; apply (ty_tweaken β α η μ δ ξ')).
            assert (Hhead : (interp._ty (α :: η) μ δ
                         (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) ρ' }-[ OS
                          ]-> Autosubst_Classes.subst
                                (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ)
                         ξ')
                      ≡ sem_types.sem_ty_mbang OS
                  (sem_types.sem_ty_arr
                     (sem_row.sem_row_cons
                        (sem_sig.sem_sig_flip_mbang OS
                           (sem_sig.sem_sig_eff (δ !!! s).1 (δ !!! s).2
                              (λ α0 : sem_ty Σ, interp._ty (α0 :: η) μ δ ι ξ')
                              (λ α0 : sem_ty Σ, interp._ty (α0 :: η) μ δ κ ξ')))
                        (interp._row η μ δ ρ0 ξ'))
                     (interp._ty (α :: η) μ δ κ ξ') (interp._ty η μ δ τ ξ'))).
            { change (interp._ty (α :: η) μ δ
                         (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) ρ' }-[ OS
                          ]-> Autosubst_Classes.subst
                                (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ)
                         ξ')
                with (sem_types.sem_ty_mbang OS
                  (sem_types.sem_ty_arr
                     (interp._row (α :: η) μ δ
                        (rename_type_row (Autosubst_Basics.lift 1%nat) ρ') ξ')
                     (interp._ty (α :: η) μ δ κ ξ')
                     (interp._ty (α :: η) μ δ (Autosubst_Classes.subst
                         (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ) ξ'))).
              rewrite (row_tweaken ρ' α η μ δ ξ') (ty_tweaken τ α η μ δ ξ').
              reflexivity. }
            assert (Hin : env_equiv_pw
                ((xs, interp._ty (α :: η) μ δ ι ξ')
                 :: (ks, sem_types.sem_ty_mbang OS
                       (sem_types.sem_ty_arr
                          (sem_row.sem_row_cons
                             (sem_sig.sem_sig_flip_mbang OS
                                (sem_sig.sem_sig_eff (δ !!! s).1 (δ !!! s).2
                                   (λ α0 : sem_ty Σ, interp._ty (α0 :: η) μ δ ι ξ')
                                   (λ α0 : sem_ty Σ, interp._ty (α0 :: η) μ δ κ ξ')))
                             (interp._row η μ δ ρ0 ξ'))
                          (interp._ty (α :: η) μ δ κ ξ') (interp._ty η μ δ τ ξ')))
                    :: ((λ '(s0, τ0), (s0, interp._ty η μ δ τ0 ξ')) <$> Γ3))
                ((xs, interp._ty (α :: η) μ δ ι ξ')
                 :: (ks, interp._ty (α :: η) μ δ
                       (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) ρ' }-[ OS
                        ]-> Autosubst_Classes.subst
                              (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ)
                       ξ')
                    :: ((λ '(s0, τ0), (s0, interp._ty (α :: η) μ δ τ0 ξ')) <$>
                        ((λ '(x, α0), (x, Autosubst_Classes.subst
                            (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0))
                           <$> Γ3)))).
            { constructor; [split; [reflexivity|reflexivity]|].
              constructor; [split; [reflexivity| exact (symmetry Hhead)]|].
              exact (Htail Γ3). }
            iApply (sem_typed_env_cong _ _ _ _ _ _ _ _ Hin (Htail Γ3)).
            iApply "Ht".
          - apply fundamental in Ht2. iPoseProof Ht2 as "Ht".
            iSpecialize ("Ht" $! η μ δ ξ' Hδ).
            iEval (cbn [ctx_insert ctx_append fmap list_fmap]) in "Ht".
            rewrite fmap_app.
            iApply "Ht".
        }
        all: admit. (* BAnon binder subcases: see report *)
      * (* ShallowHandle MS *)
        rewrite !lbl_resolve_handle_name.
        rewrite !resolve_map_lookup H0 /=.
        rewrite !lbl_resolve_rec.
        unfold ctx_append. rewrite fmap_app.
        pose proof (multi_env_sound Γ3 H η μ δ ξ') as HME.
        pose proof (sig_labels_eff_name σ η μ δ ξ') as Hlbl.
        rewrite H1 in Hlbl.
        destruct x as [|xs]; [| destruct k as [|ks]; [| destruct y as [|ys]]].
        4:{
          iApply (sem_typed_shallow_handler_MS (δ !!! s)
                    (λ α, interp._ty (α :: η) μ δ ι ξ')
                    (λ α, interp._ty (α :: η) μ δ κ ξ')
                    MS
                    (interp._ty η μ δ τ ξ')
                    (interp._ty η μ δ τ' ξ')
                    (interp._eff_sig η μ δ σ ξ')
                    (interp._row η μ δ ρ0 ξ')
                    _ _ _ xs ys ks _ _ _ _ _ _
                    _ _ _ _ _ _ Hlbl).
          - apply fundamental in Ht1. iPoseProof Ht1 as "Ht".
            iApply ("Ht" $! η μ δ ξ' Hδ).
          - iIntros (α). apply fundamental in Ht3. iPoseProof Ht3 as "Ht".
            iSpecialize ("Ht" $! (α :: η) μ δ ξ' Hδ).
            iEval (cbn [ctx_insert fmap list_fmap]) in "Ht".
            iApply (sem_typed_row_cong _ _ _ _ _ _ _
                      (symmetry (row_tweaken ρ α η μ δ ξ'))).
            iApply (sem_typed_type_cong _ _ _ _ _ _ _
                      (symmetry (ty_tweaken τ' α η μ δ ξ'))).
            assert (Htail : ∀ (Γ0 : ctx), env_equiv_pw
                      ((λ '(s0, τ0), (s0, interp._ty η μ δ τ0 ξ')) <$> Γ0)
                      ((λ '(s0, τ0), (s0, interp._ty (α :: η) μ δ τ0 ξ')) <$>
                         ((λ '(x, α0), (x, Autosubst_Classes.subst
                             (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0))
                            <$> Γ0)))
              by (intros Γ0; induction Γ0 as [|[z β] Γ0' IH]; simpl; [constructor|];
                  constructor; [split; [done|]|exact IH];
                  simpl; symmetry; apply (ty_tweaken β α η μ δ ξ')).
            assert (Hhead : (interp._ty (α :: η) μ δ
                         (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) ρ' }-[ MS
                          ]-> Autosubst_Classes.subst
                                (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ)
                         ξ')
                      ≡ sem_types.sem_ty_mbang MS
                  (sem_types.sem_ty_arr
                     (sem_row.sem_row_cons
                        (sem_sig.sem_sig_flip_mbang MS
                           (sem_sig.sem_sig_eff (δ !!! s).1 (δ !!! s).2
                              (λ α0 : sem_ty Σ, interp._ty (α0 :: η) μ δ ι ξ')
                              (λ α0 : sem_ty Σ, interp._ty (α0 :: η) μ δ κ ξ')))
                        (interp._row η μ δ ρ0 ξ'))
                     (interp._ty (α :: η) μ δ κ ξ') (interp._ty η μ δ τ ξ'))).
            { change (interp._ty (α :: η) μ δ
                         (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) ρ' }-[ MS
                          ]-> Autosubst_Classes.subst
                                (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ)
                         ξ')
                with (sem_types.sem_ty_mbang MS
                  (sem_types.sem_ty_arr
                     (interp._row (α :: η) μ δ
                        (rename_type_row (Autosubst_Basics.lift 1%nat) ρ') ξ')
                     (interp._ty (α :: η) μ δ κ ξ')
                     (interp._ty (α :: η) μ δ (Autosubst_Classes.subst
                         (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ) ξ'))).
              rewrite (row_tweaken ρ' α η μ δ ξ') (ty_tweaken τ α η μ δ ξ').
              reflexivity. }
            assert (Hin : env_equiv_pw
                ((xs, interp._ty (α :: η) μ δ ι ξ')
                 :: (ks, sem_types.sem_ty_mbang MS
                       (sem_types.sem_ty_arr
                          (sem_row.sem_row_cons
                             (sem_sig.sem_sig_flip_mbang MS
                                (sem_sig.sem_sig_eff (δ !!! s).1 (δ !!! s).2
                                   (λ α0 : sem_ty Σ, interp._ty (α0 :: η) μ δ ι ξ')
                                   (λ α0 : sem_ty Σ, interp._ty (α0 :: η) μ δ κ ξ')))
                             (interp._row η μ δ ρ0 ξ'))
                          (interp._ty (α :: η) μ δ κ ξ') (interp._ty η μ δ τ ξ')))
                    :: ((λ '(s0, τ0), (s0, interp._ty η μ δ τ0 ξ')) <$> Γ3))
                ((xs, interp._ty (α :: η) μ δ ι ξ')
                 :: (ks, interp._ty (α :: η) μ δ
                       (κ -{ rename_type_row (Autosubst_Basics.lift 1%nat) ρ' }-[ MS
                        ]-> Autosubst_Classes.subst
                              (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) τ)
                       ξ')
                    :: ((λ '(s0, τ0), (s0, interp._ty (α :: η) μ δ τ0 ξ')) <$>
                        ((λ '(x, α0), (x, Autosubst_Classes.subst
                            (Autosubst_Classes.ren (Autosubst_Basics.lift 1%nat)) α0))
                           <$> Γ3)))).
            { constructor; [split; [reflexivity|reflexivity]|].
              constructor; [split; [reflexivity| exact (symmetry Hhead)]|].
              exact (Htail Γ3). }
            iApply (sem_typed_env_cong _ _ _ _ _ _ _ _ Hin (Htail Γ3)).
            iApply "Ht".
          - apply fundamental in Ht2. iPoseProof Ht2 as "Ht".
            iSpecialize ("Ht" $! η μ δ ξ' Hδ).
            iEval (cbn [ctx_insert ctx_append fmap list_fmap]) in "Ht".
            rewrite fmap_app.
            iApply "Ht".
        }
        all: admit. (* BAnon binder subcases: see report *)
    + (* Sub_typed *)
      (* Transport the body derivation along [sem_typed_sub] (compatibility.v),
         discharging the four subtyping premises by the soundness lemmas run
         under the [erase_ctx η μ δ ξ' (row_to_disj_ctx ρ)] bundle that
         [disjointness_ctx_sem_jugdment] supplies: the two environment premises
         by [ctx_le_sound], the row premise by [row_le_sound] (which handles the
         [@ b] annotation), the type premise by [ty_le_sound], and the body by
         the IH [fundamental] on [Ht]. *)
      iApply disjointness_ctx_sem_jugdment. iIntros "!# #HD".
      iApply (sem_typed_sub
                ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ1)
                ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ1')
                ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ2)
                ((λ '(s, τ0), (s, interp._ty η μ δ τ0 ξ')) <$> Γ2')
                _ _
                (interp._row η μ δ ρ ξ') (interp._row η μ δ ρ' ξ')
                (interp._ty η μ δ τ ξ') (interp._ty η μ δ τ' ξ')).
      * iApply (ctx_le_sound _ _ _ H with "HD").
      * iApply (ctx_le_sound _ _ _ H0 with "HD").
      * iApply (row_le_sound _ _ _ _ _ _ _ _ H1 with "HD").
      * iApply (ty_le_sound _ _ _ _ _ _ _ H2 with "HD").
      * apply fundamental in Ht. iPoseProof Ht as "Ht".
        iApply ("Ht" $! η μ δ ξ' Hδ).
    + (* Contraction_typed *)
      (* Now sound after removing [le.TBangRef_le]: the contracted type
         [κ] is [le.MultiT], so its interpretation is a semantic [MultiT]
         (via [interp.multi_ty_sound]), which is the side condition of
         [sem_typed_contraction]. *)
      destruct x as [|s]; simpl;
        [ apply fundamental in Ht; iPoseProof Ht as "Ht";
          by iApply "Ht"
        | pose proof (multi_ty_sound κ H η μ δ ξ') as Hmt;
          iApply (sem_typed_contraction _ _ _ _ _ _
                    (interp._ty η μ δ κ ξ'));
          apply fundamental in Ht; iPoseProof Ht as "Ht";
          by iApply "Ht" ].
    + (* Weakening_typed *) destruct x; simpl.
      * apply fundamental in Ht. iPoseProof Ht as "Ht".
        by iApply "Ht". 
      * iApply sem_typed_weaken. apply fundamental in Ht.
        iPoseProof Ht as "Ht". by iApply "Ht". 
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
    + (* Rec_val_typed *)
      (* The captured context is [∅] so [MultiE []] is trivial and no rule
         strengthening is needed (cf. [Rec_typed]/[Rec_pure_typed]).  We
         build the recursive-closure oval at the empty env with
         [sem_oval_typed_ufun_rec] (mode [MS], since the value type uses the
         MS arrow [-{ρ}->]) and read off the value relation by specialising
         it at [∅]: [Rec f x e] is already a value, so [prel] of it at [∅]
         collapses to the [sem_ty_mbang MS arr] relation on [RecV f x e].
         The IH context [interp (<[f]><[x]>∅) = (f, ![MS]arr) ::? (x,τ1)
         ::? []] matches the body shape of [sem_oval_typed_ufun_rec]. *)
      rewrite /sem_val_typed /=.
      iAssert (sem_oval_typed [] (rec: f x := e) (rec: f x := e)
        (sem_types.sem_ty_mbang MS (sem_types.sem_ty_arr
           (interp._row η μ δ ρ ξ) (interp._ty η μ δ τ1 ξ)
           (interp._ty η μ δ τ2 ξ)))) as "#Hov".
      { iApply (@sem_oval_typed_ufun_rec _ _ (interp._ty η μ δ τ1 ξ)
                  (interp._row η μ δ ρ ξ) (interp._ty η μ δ τ2 ξ) MS [] f x
                  e e _).
        { destruct x as [|s];
            [intros []|rewrite env_dom_nil; apply not_elem_of_nil]. }
        { destruct f as [|s];
            [intros []|rewrite env_dom_nil; apply not_elem_of_nil]. }
        { (* [f ≠ x] side condition: discharged directly by the new
             [Rec_val_typed] premise [H] (which is the same proposition).
             This closes the previously-admitted [f = x] sub-case: when
             [f = BNamed sf] and [x = BNamed sx], [H] gives
             [BNamed sf ≠ x], contradicting [f = x]. *)
          exact H. }
        apply fundamental in H0. iPoseProof H0 as "H".
        iSpecialize ("H" $! η μ δ ξ (empty_subseteq (dom δ))).
        (* [Δ = ∅] here, so [resolve_l/r ∅ δ = ∅] and [lbl_resolve] is the
           identity, matching the literal body of [sem_oval_typed_ufun_rec]. *)
        iEval (rewrite !resolve_map_empty !lbl_resolve_empty) in "H".
        destruct f as [|sf]; destruct x as [|sx]; simpl in *; iApply "H". }
      rewrite /sem_oval_typed /tc_opaque. iModIntro.
      iSpecialize ("Hov" $! ∅ with "[]"); first by rewrite env_sem_typed_empty.
      rewrite !fmap_empty !subst_map_empty /pure_weakestpre.prel /=.
      (* [Rec f x e] is an expr (not a [Val]); it pure-steps in one step to
         the value [RecV f x e].  Read off the value relation by
         destructing the [prel] reduction witnesses and pinning them to
         [RecV f x e] via determinism of pure reduction. *)
      iDestruct "Hov" as (v1 v2 n1 n2) "(%Hns & Hτ)".
      destruct Hns as [Hns1 Hns2].
      assert (Hr : nsteps pure_step 1 (Rec f x e) (Val (RecV f x e)))
        by apply (pure_recc f x e I).
      pose proof (pure_weakestpre.nsteps_pure_step_det _ _ _ _ _ Hns1 Hr)
        as ->.
      pose proof (pure_weakestpre.nsteps_pure_step_det _ _ _ _ _ Hns2 Hr)
        as ->.
      iApply "Hτ".
    + (* TAbs_val_typed *) apply fundamental_val in Hv.
      rewrite /sem_val_typed /=. iModIntro. iIntros (τ0).
      iApply (sem_val_related_interp v τ (τ0 :: η) μ δ ξ Hv).
    + (* RAbs_val_typed *) apply fundamental_val in Hv.
      rewrite /sem_val_typed /=. iModIntro. iIntros (θ).
      iApply (sem_val_related_interp v τ η μ δ (θ :: ξ) Hv).
    + (* MAbs_val_typed *) apply fundamental_val in Hv.
      rewrite /sem_val_typed /=. iModIntro. iIntros (m).
      iApply (sem_val_related_interp v τ η (m :: μ) δ ξ Hv).
  - intros Hp. destruct Hp; iIntros (η μ δ ξ Hδ).
    + (* Val_pure_typed *) apply fundamental_val in H. iPoseProof H as "H".
      iSpecialize ("H" $! η μ δ ξ). iApply sem_oval_typed_val. iApply "H".
    + (* Rec_pure_typed *)
      (* Mirror of [Rec_typed] at the pure (oval) level.  The [Rec_pure]
         rule's premise context is [<[x]><[f]>Γ1] (argument binder [x]
         outer, recursive binder [f] inner), so the IH context matches
         [sem_oval_typed_ufun_rec_xf]'s body shape
         [(x,τ) ::? (f, ![m]arr) ::? interp Γ1] definitionally — no reorder
         needed.  [MultiE (interp Γ1)] from [multi_env_sound] (strengthened
         [le.MultiC Γ1]); freshness from [ctx_dom_env_dom]. *)
      pose proof (multi_env_sound Γ1 H2 η μ δ ξ) as HME.
      iApply sem_oval_typed_ufun_rec_xf.
      { destruct x as [|s]; [done|]. by eapply ctx_dom_env_dom. }
      { destruct f as [|s]; [done|]. by eapply ctx_dom_env_dom. }
      { exact H. }
      apply fundamental in H3. iPoseProof H3 as "Ht".
      iSpecialize ("Ht" $! η μ δ ξ (empty_subseteq (dom δ))).
      destruct f as [|sf]; destruct x as [|sx]; simpl in *; iApply "Ht".
    + (* Pair_pure_typed *)
      (* Now sound after removing [le.TBangRef_le] and adding the
         [le.MultiC Γ] premise: it interprets to [MultiE (interp Γ)] (via
         [interp.multi_env_sound]), which (through [multi_env_persistent])
         discharges the [∀ vs, Persistent (Γ ⊨ₑ vs)] side condition of
         [sem_oval_typed_pair], needed to build the product [prel]. *)
      simpl. pose proof (multi_env_sound Γ H η μ δ ξ) as HME.
      by iApply sem_oval_typed_pair;
        [ apply fundamental_pure in Hp1; iPoseProof Hp1 as "H1";
          iApply ("H1" $! η μ δ ξ)
        | apply fundamental_pure in Hp2; iPoseProof Hp2 as "H2";
          iApply ("H2" $! η μ δ ξ) ].
    + (* InjL_pure_typed *) iApply sem_oval_typed_injl.
      apply fundamental_pure in Hp. iPoseProof Hp as "H".
      by iApply "H".
    + (* InjR_pure_typed *) iApply sem_oval_typed_injr. 
      apply fundamental_pure in Hp. iPoseProof Hp as "H".
      by iApply "H".
    + (* Var_pure_typed *) iApply sem_oval_typed_var.
    + (* BangIntro_pure_typed *)
      (* Now sound after removing [le.TBangRef_le]: the premise [m m⪯C Γ]
         interprets to a semantic mode-env subtyping
         [(interp._mode μ m) ₘ⪯ₑ interp Γ] (via [interp.mode_env_sound]),
         which is the side condition of [sem_typed_mbang]. *)
      simpl. pose proof (mode_env_sound m Γ H η μ δ ξ) as Hmode.
      iApply (sem_typed_mbang (interp._mode μ m)).
      apply fundamental_pure in Hp. iPoseProof Hp as "H".
      by iApply "H".
    + (* TAbs_pure_typed *)
      (* The [TAbs_pure] rule shifts its premise context by [⤉] (a fresh
         TYPE binder), so the body IH at the EXTENDED type-env [α::η]
         cancels the shift via [interp.ctx_tweaken]. *)
      iApply (sem_typed_TLam (λ α, interp._ty (α :: η) μ δ τ ξ)).
      iIntros (α). apply fundamental_pure in Hp. iPoseProof Hp as "H".
      rewrite /sem_oval_typed /tc_opaque.
      iModIntro. iIntros (vs) "Henv".
      iApply "H"; first done. by rewrite interp.ctx_tweaken.
    + (* RAbs_pure_typed *)
      (* The [RAbs_pure] rule row-shifts its premise context, so the body
         IH at the EXTENDED row-env [θ::ξ] cancels the shift via
         [interp.ctx_rweaken]. *)
      iApply (sem_typed_RLam (λ θ, interp._ty η μ δ τ (θ :: ξ))).
      iIntros (θ). apply fundamental_pure in Hp. iPoseProof Hp as "H".
      rewrite /sem_oval_typed /tc_opaque.
      iModIntro. iIntros (vs) "Henv".
      iApply "H"; first done. by rewrite interp.ctx_rweaken.
    + (* MAbs_pure_typed *)
      (* The [MAbs_pure] rule mode-shifts its premise context, so the body
         IH at the EXTENDED mode-env [ν::μ] cancels the shift via
         [interp.ctx_mweaken]. *)
      iApply (sem_typed_MLam (λ ν, interp._ty η (ν :: μ) δ τ ξ)).
      iIntros (ν). apply fundamental_pure in Hp. iPoseProof Hp as "H".
      rewrite /sem_oval_typed /tc_opaque.
      iModIntro. iIntros (vs) "Henv".
      iApply "H"; first done. by rewrite interp.ctx_mweaken.
Admitted.

End fundamental.
