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
  with pure_lbl_resolve_id Γ e τ :
  Γ ⊢ₚ e : τ → ∀ rm, lbl_resolve rm e = e.
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
          Hp : _ ⊢ₚ _ : _ |- _ => by rewrite (pure_lbl_resolve_id _ _ _ Hp)
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
  - intros Hp. induction Hp; intros rm;
      rewrite ?lbl_resolve_val ?lbl_resolve_var ?lbl_resolve_rec
              ?lbl_resolve_pair ?lbl_resolve_injl ?lbl_resolve_injr;
      repeat match goal with
             | IH : ∀ rm, lbl_resolve rm ?e0 = ?e0
               |- context[lbl_resolve rm ?e0] => rewrite (IH rm)
             end;
      try reflexivity.
    + (* Rec_pure: body typed under [∅], resolution is identity for any rm. *)
      f_equal. apply (typed_lbl_resolve_id _ _ _ _ _ _ H3 rm).
      rewrite dom_empty_L. set_solver.
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
    + (* Var_typed *) rewrite !lbl_resolve_var. iApply sem_typed_var.
    + (* Val_typed *) rewrite !lbl_resolve_val.
      iApply sem_typed_val; by iApply fundamental_val.
    + (* Pure_typed *)
      (* [e] is pure, hence effect-free: collapse [lbl_resolve] back to the
         literal [e] (matching the literal-expression [bin_log_pure_related]
         provided by [fundamental_pure]). *)
      rewrite !(pure_lbl_resolve_id _ _ _ H).
      rewrite fmap_app. iApply sem_typed_oval.
      by iApply fundamental_pure.
    + (* Pair_typed *)
      (* The new [ρ R⪯T τ2] premise supplies the [RowTypeSub] typeclass
         argument of [sem_typed_pair_gen] via [row_type_sub_sound]. *)
      push_lr.
      match goal with Hrt : _ R⪯T _ |- _ =>
        pose proof (interp.row_type_sub_sound δ _ _ Hrt η μ ξ) as Hrts
      end.
      iApply sem_typed_pair_gen;
        [apply fundamental in Ht1 as Ht|apply fundamental in Ht2 as Ht];
        iPoseProof Ht as "Ht"; iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* Fst_typed *) push_lr. iApply sem_typed_fst_expr. apply fundamental in Ht.
      iPoseProof Ht as "Ht". iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* Snd_typed *) push_lr. iApply sem_typed_snd_expr. apply fundamental in Ht.
      iPoseProof Ht as "Ht". iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* InjL_typed *) push_lr. iApply sem_typed_left_inj. apply fundamental in Ht.
      iPoseProof Ht as "Ht". iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* InjR_typed *) push_lr. iApply sem_typed_right_inj. apply fundamental in Ht.
      iPoseProof Ht as "Ht". iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* Match_typed *) push_lr. iApply sem_typed_match;
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
    + (* If_typed *) push_lr. iApply sem_typed_if;
        [ apply fundamental in Ht1; iPoseProof Ht1 as "Ht";
            iApply ("Ht" $! _ _ _ _ ∅ Hδ)
        | apply fundamental in Ht2; iPoseProof Ht2 as "Ht";
            iApply ("Ht" $! _ _ _ _ ∅ Hδ)
        | apply fundamental in Ht3; iPoseProof Ht3 as "Ht";
            iApply ("Ht" $! _ _ _ _ ∅ Hδ) ].
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
      pose proof (multi_env_sound Γ H2 η μ δ ξ) as HME.
      iApply (@sem_oval_typed_ufun_rec _ _ (interp._ty η μ δ τ ξ)
                (interp._row η μ δ ρ ξ) (interp._ty η μ δ κ ξ)
                (interp._mode μ m) _ f x
                (lbl_resolve (resolve_l Δ δ) e)
                (lbl_resolve (resolve_r Δ δ) e) HME).
      { destruct x as [|s]; [done|]. by eapply ctx_dom_env_dom. }
      { destruct f as [|s]; [done|]. by eapply ctx_dom_env_dom. }
      { exact H. }
      apply fundamental in Ht. iPoseProof Ht as "Ht".
      iSpecialize ("Ht" $! η μ δ ξ vs Hδ).
      destruct f as [|sf]; destruct x as [|sx]; simpl in *; iApply "Ht".
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
    + (* TAlloc *) push_lr. iApply sem_typed_alloc. apply fundamental in Ht.
      iPoseProof Ht as "Ht". iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* TLoad *) push_lr. iApply sem_typed_load_expr. apply fundamental in Ht.
      iPoseProof Ht as "Ht". iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* TStore *)
      (* Linear-reference store.  The new [ρ R⪯T τ] premise supplies the
         [RowTypeSub] typeclass argument of [sem_typed_store_expr] (which
         carries the stored value across the ref subexpression's effects)
         via [row_type_sub_sound]. *)
      push_lr.
      match goal with Hrt : _ R⪯T _ |- _ =>
        pose proof (interp.row_type_sub_sound δ _ _ Hrt η μ ξ) as Hrts
      end.
      iApply sem_typed_store_expr;
        [apply fundamental in Ht2 as Ht|apply fundamental in Ht1 as Ht];
        iPoseProof Ht as "Ht"; iApply ("Ht" $! _ _ _ _ ∅ Hδ).
    + (* TAllocTape *) push_lr. iApply sem_typed_alloctape. apply fundamental in Ht.
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
    + (* TRandU *) push_lr. iApply sem_typed_randu;
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
    + (* Effect_typed *)
      (* BLOCKED — model/statement gap, NOT a missing compatibility lemma.
         Goal: interp Γ1 ⊨ (Effect s e) ≤ (Effect s e) : interp ρ : interp τ
         ⫤ interp Γ2.  [Effect s e] reduces (head_step, semantics.v:1297) to
         [lbl_subst s l e] for a fresh label [l]; the generalised effect
         compatibility lemma (sem_typed_effect, with arbitrary binder [s] and
         Γ1≠Γ2) therefore needs the hypothesis
           ∀ l1 l2, sem_typed (interp Γ1) (lbl_subst s l1 e)(lbl_subst s l2 e)
                      (sem_row_cons (sem_sig_bottom l1 l2) (interp ρ))
                      (interp τ) (interp Γ2).
         The head signature aligns DEFINITIONALLY: with δ':=<[s:=(l1,l2)]>δ,
           interp._eff_sig η μ δ' (SAbs s) ξ
             = sem_sig_bottom (δ'!!!s).1 (δ'!!!s).2
         (reflexivity: SAbs s := SSig s TBot TTop, interp TBot/TTop = ⊥/⊤ =
         sem_sig_bottom's False/True args).  The fresh side condition
         [vars._fresh s Γ1 ρ τ] makes interp of Γ1/ρ/τ δ-irrelevant at [s], so
         a δ-irrelevance lemma reconciles the indices.  THE WALL: the only way
         to obtain the [lbl_subst s l1 e] hypothesis is the recursion
         [fundamental Ht] at δ', but it yields [sem_typed ... e e ...] with the
         RAW body [e] (Δ-bound name [s], i.e. [Do (EffName s) …] occurrences),
         NOT the label-substituted [lbl_subst s l1 e].  [sem_typed] (and the
         fundamental statement [bin_log_related], interp.v:80) relate the
         expression LITERALLY (only [subst_map] of value vars; no δ-driven
         [lbl_subst]); [Do (EffName _)] is irreducible (head_step = dzero,
         semantics.v:1334, listed stuck at 85/177) so [obs_refines]'s left-hand
         [WP (Do (EffName s) v) {{…}}] is unprovable and the SSig/SAbs protocol
         theory ([iLblSig_to_iLblThy], sem_sig_eff expects [do: (EffLabel _) v])
         cannot fire on it either.  Hence the IH hypothesis is the wrong
         expression and is itself unprovable for any [e] that performs the
         effect — the same wall recurses through the Do_typed case below.
         FIX needs a model/statement change (out of task scope, off-limits):
         either [bin_log_related]/[sem_typed] must apply a δ-driven label
         substitution to the related expression (resolve every [EffName s],
         s∈dom δ, to [EffLabel (δ!!!s)]) before the BREL, or the interp of
         [Do]/[Effect]/[Handle] must be label-resolved.  No add-only lemma
         bridges [Do (EffName s)] and [Do (EffLabel l)] at the BREL level
         because they have genuinely different operational behaviour. *)
      admit.
    + (* Do_typed *)
      (* BLOCKED — same root cause as Effect_typed (the [EffName] vs
         [EffLabel] wall); NOT a missing compatibility lemma.
         Goal: interp Γ1 ⊨ (do: s e) ≤ (do: s e) : interp ρ : interp(κ.[τ/])
         ⫤ interp Γ2, where [do: s e = Do (EffName s) e] (coercion
         EffName : string >-> eff_val) and ρ = RCons (SFlip m (SSig s ι κ)) ρ'.
         The intended map to [sem_typed_do] with op := δ!!!s, m':=interp._mode
         μ m, A:=λα,interp._ty(α::η)μ δ ι ξ, B:=λα,interp._ty(α::η)μ δ κ ξ
         aligns the row head DEFINITIONALLY:
           interp._eff_sig η μ δ (SFlip m (SSig s ι κ)) ξ
             = sem_sig_flip_mbang (interp._mode μ m)
                 (sem_sig_eff (δ!!!s).1 (δ!!!s).2 A B)   (reflexivity)
         and the result type [interp (κ.[τ/])] reconciles with [B (interp τ)]
         via [interp.ty_subst_single] + [sem_typed_type_cong]; the mode side
         condition is supplied by [interp.mode_env_sound] from [m m⪯C Γ2].
         THE WALL: [sem_typed_do]'s conclusion is over [do: op.1 e =
         Do (EffLabel (δ!!!s).1) e] but the goal is [do: s e =
         Do (EffName s) e].  [iApply sem_typed_do] FAILS to unify
         [Do (EffLabel (δ!!!s).1) ?e] with [Do (EffName s) e]
         (EffLabel ≠ EffName).
         There is no name-based [sem_typed_do]: [Do (EffName s)] is irreducible
         (head_step = dzero) and the SSig protocol theory expects
         [do: (EffLabel (δ!!!s).1) v], so [brel_introduction] cannot fire and
         [obs_refines]'s left [WP] is unprovable.  FIX needs the SAME model/
         statement change as Effect_typed (δ-driven label resolution of the
         related expression in [bin_log_related]/[sem_typed], or label-resolved
         interp of [Do]); off-limits per task. *)
      admit.
    + (* DeepHandle_typed *) admit.
    + (* ShallowHandle_typed *) admit.
    + (* Sub_typed *) admit.
    + (* Contraction_typed *)
      (* Now sound after removing [le.TBangRef_le]: the contracted type
         [κ] is [le.MultiT], so its interpretation is a semantic [MultiT]
         (via [interp.multi_ty_sound]), which is the side condition of
         [sem_typed_contraction]. *)
      destruct x as [|s]; simpl;
        [ apply fundamental in Ht; iPoseProof Ht as "Ht";
          iApply ("Ht" $! _ _ _ _ ∅ Hδ)
        | pose proof (multi_ty_sound κ H η μ δ ξ) as Hmt;
          iApply (sem_typed_contraction _ _ _ _ _ _
                    (interp._ty η μ δ κ ξ));
          apply fundamental in Ht; iPoseProof Ht as "Ht";
          iApply ("Ht" $! _ _ _ _ ∅ Hδ) ].
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
        iSpecialize ("H" $! η μ δ ξ ∅ (empty_subseteq (dom δ))).
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
  - intros Hp. destruct Hp; iIntros (η μ δ ξ).
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
      iApply (@sem_oval_typed_ufun_rec_xf _ _ (interp._ty η μ δ τ ξ)
                (interp._row η μ δ ρ ξ) (interp._ty η μ δ κ ξ)
                (interp._mode μ m) _ f x e e HME).
      { destruct x as [|s]; [done|]. by eapply ctx_dom_env_dom. }
      { destruct f as [|s]; [done|]. by eapply ctx_dom_env_dom. }
      { exact H. }
      apply fundamental in H3. iPoseProof H3 as "Ht".
      iSpecialize ("Ht" $! η μ δ ξ ∅ (empty_subseteq (dom δ))).
      iEval (rewrite !resolve_map_empty !lbl_resolve_empty) in "Ht".
      destruct f as [|sf]; destruct x as [|sx]; simpl in *; iApply "Ht".
    + (* Pair_pure_typed *)
      (* Now sound after removing [le.TBangRef_le] and adding the
         [le.MultiC Γ] premise: it interprets to [MultiE (interp Γ)] (via
         [interp.multi_env_sound]), which (through [multi_env_persistent])
         discharges the [∀ vs, Persistent (Γ ⊨ₑ vs)] side condition of
         [sem_oval_typed_pair], needed to build the product [prel]. *)
      simpl. pose proof (multi_env_sound Γ H η μ δ ξ) as HME.
      iApply sem_oval_typed_pair;
        [ apply fundamental_pure in Hp1; iPoseProof Hp1 as "H1";
          iApply ("H1" $! η μ δ ξ)
        | apply fundamental_pure in Hp2; iPoseProof Hp2 as "H2";
          iApply ("H2" $! η μ δ ξ) ].
    + (* InjL_pure_typed *) iApply sem_oval_typed_injl.
      apply fundamental_pure in Hp. iPoseProof Hp as "H".
      iApply ("H" $! η μ δ ξ).
    + (* InjR_pure_typed *) iApply sem_oval_typed_injr.
      apply fundamental_pure in Hp. iPoseProof Hp as "H".
      iApply ("H" $! η μ δ ξ).
    + (* Var_pure_typed *) iApply sem_oval_typed_var.
    + (* BangIntro_pure_typed *)
      (* Now sound after removing [le.TBangRef_le]: the premise [m m⪯C Γ]
         interprets to a semantic mode-env subtyping
         [(interp._mode μ m) ₘ⪯ₑ interp Γ] (via [interp.mode_env_sound]),
         which is the side condition of [sem_typed_mbang]. *)
      simpl. pose proof (mode_env_sound m Γ H η μ δ ξ) as Hmode.
      iApply (sem_typed_mbang (interp._mode μ m)).
      apply fundamental_pure in Hp. iPoseProof Hp as "H".
      iApply ("H" $! η μ δ ξ).
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
