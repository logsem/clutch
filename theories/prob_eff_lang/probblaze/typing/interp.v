From clutch.prob_eff_lang.probblaze Require Import logic sem_sig sem_row sem_types sem_def syntax types sem_judgement sem_env mode.
From iris.algebra Require Export list gmap.
From Autosubst Require Import Autosubst.


Module interp. 

  Definition _mode (μ : list mode) (m : vmode) : mode :=
    match m with 
    | MVar i => μ !!! i
    | OS => syntax.OS
    | MS => syntax.MS
    end.
  
  Global Instance effname_lookup_total : LookupTotal eff_name (label * label) (gmap eff_name (label * label)).
  Proof. eapply map_lookup_total. Defined.

  #[refine] Fixpoint _eff_sig `{!probblazeRGS Σ}
    (η : list (sem_ty Σ))
    (μ : list mode) 
    (δ : gmap eff_name (label * label))
    (σ : eff_sig) : listO (sem_row Σ) -n> sem_sig Σ :=
    match σ with
    | SSig s α β => λne ξ, let ops := δ !!! s in sem_sig_eff ops.1 ops.2 (λ τ', _ty (τ' :: η) μ δ α ξ) (λ τ', _ty (τ' :: η) μ δ β ξ)
    | SFlip m e => λne ξ, sem_sig_flip_mbang (_mode μ m) (_eff_sig η μ δ e ξ)
    end 
      with _row `{!probblazeRGS Σ}
           (η : list (sem_ty Σ))
           (μ : list mode)
           (δ : gmap eff_name (label * label))
           (ρ : row) : listO (sem_row Σ) -n> sem_row Σ :=
      match ρ with
      | RNil => λne _, ⊥
      | RVar i =>  λne ξ, ξ !!! i
      | RFlip m ρ => λne ξ, sem_row_flip_mbang (_mode μ m) (_row η μ δ ρ ξ)
      | RCons e ρ => λne ξ, sem_row_cons (_eff_sig η μ δ e ξ) (_row η μ δ ρ ξ)
      (* | RRec ρ' => fun H => λne ξ, sem_row_rec' (λne ρ'', _row n μ δ ρ' _ (ρ'' :: ξ)) *)
      | RUnion ρ1 ρ2 => λne ξ, sem_row_union (_row η μ δ ρ1 ξ) (_row η μ δ ρ2 ξ)
      end 
      with _ty `{!probblazeRGS Σ}
           (η : list (sem_ty Σ))
           (μ : list mode)
           (δ : gmap eff_name (label * label))
           (τ : type) : listO (sem_row Σ) -n> sem_ty Σ :=
        match τ with
        | TBot => λne _, ⊥
        | TTop => λne _, ⊤
        | TUnit => λne _, sem_ty_unit
        | TInt => λne _, sem_ty_int
        | TNat => λne _, sem_ty_nat
        | TBool => λne _, sem_ty_bool
        | TTape => λne _, sem_ty_tape
        | TRef τ => λne ξ, sem_ty_ref (_ty η μ δ τ ξ)
        | TProd τ1 τ2 => λne ξ, sem_ty_prod (_ty η μ δ τ1 ξ) (_ty η μ δ τ2 ξ)
        | TSum τ1 τ2 => λne ξ, sem_ty_sum (_ty η μ δ τ1 ξ) (_ty η μ δ τ2 ξ)
        | TBang m τ => λne ξ, sem_ty_mbang (_mode μ m) (_ty η μ δ τ ξ)
        | TArrow α ρ β => λne ξ, sem_ty_arr (_row η μ δ ρ ξ) (_ty η μ δ α ξ) (_ty η μ δ β ξ)
        | TForallM τ => λne ξ, sem_ty_mode_forall (λ m, _ty η (m :: μ) δ τ ξ)
        | TForallR τ => λne ξ, sem_ty_row_forall (λ ρ, _ty η μ δ τ (ρ :: ξ))
        | TForallT τ => λne ξ, sem_ty_type_forall (λ τ', _ty (τ' :: η) μ δ τ ξ)
        | TExists τ => λne ξ, sem_ty_exists (λ τ', _ty (τ' :: η) μ δ τ ξ)
        | TRec τ => λne ξ, sem_ty_rec (λ τ', _ty (τ' :: η) μ δ τ ξ)
        | TVar i => λne _, η !!! i
        end.
  Proof. 
    all: try exact probblazeRGS0; try apply probblazeRGS_probblazeGS.
    1 : apply effname_lookup_total. 
    all: try (intros ????; by repeat f_equiv).
    all: intros ????; simpl; f_equiv; intros ?; by f_equiv. 
  Defined.
  
  (* The interpretation of a context [Γ] at a given interpretation env. *)
  Definition _env `{!probblazeRGS Σ} η μ δ ξ (Γ : ctx) :=
    ((λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> Γ).

End interp.

(* -------------------------------------------------------------------------- *)
(** Resolution maps for the semantic judgement.

    [bin_log_related Δ ... e e' ...] relates the δ-RESOLVED expressions: every
    free effect NAME [s ∈ dom Δ] is replaced by the LEFT label [(δ!!!s).1]
    on the left and the RIGHT label [(δ!!!s).2] on the right (the protocol of
    [interp._eff_sig] at [SSig s] expects [do: (EffLabel (δ!!!s).1) v] on the
    left and [do: (EffLabel (δ!!!s).2) v] on the right; [Do (EffName s)] is
    operationally stuck).  The resolution domain is exactly [dom Δ] (guaranteed
    [⊆ dom δ]), so it is the empty map -- hence the identity -- whenever
    [Δ = ∅] (e.g. inside [Rec]/value bodies, typed under [∅]). *)
Definition resolve_map (proj : label * label → label)
    (Δ : gmap eff_name unit) (δ : gmap eff_name (label * label))
    : gmap string label :=
  map_imap (λ s (_ : unit), Some (proj (δ !!! s))) Δ.

Notation resolve_l Δ δ := (resolve_map fst Δ δ).
Notation resolve_r Δ δ := (resolve_map snd Δ δ).

Lemma resolve_map_lookup proj Δ δ s :
  resolve_map proj Δ δ !! s
  = (λ _ : unit, proj (δ !!! s)) <$> (Δ !! s).
Proof.
  rewrite /resolve_map map_lookup_imap /=.
  destruct (Δ !! s) as [u|] eqn:HΔ; rewrite HΔ /=; by [destruct u|].
Qed.

Lemma resolve_map_empty proj δ : resolve_map proj ∅ δ = ∅.
Proof. apply map_eq=> s. by rewrite resolve_map_lookup lookup_empty. Qed.

(* Extending [Δ] with [s] and [δ] with its labels extends the resolution map
   with the corresponding label, leaving the rest intact. *)
Lemma resolve_map_insert proj Δ δ (s : eff_name) lp :
  resolve_map proj (<[s:=tt]> Δ) (<[s:=lp]> δ)
  = <[s := proj lp]> (resolve_map proj Δ δ).
Proof.
  apply map_eq=> s'.
  destruct (decide (s = s')) as [->|Hne].
  - rewrite resolve_map_lookup lookup_insert_eq /=
            lookup_total_insert_eq lookup_insert_eq //.
  - rewrite (lookup_insert_ne (resolve_map proj Δ δ) s s' (proj lp) Hne)
            !resolve_map_lookup
            (lookup_insert_ne Δ s s' tt Hne)
            (lookup_total_insert_ne δ s s' lp Hne) //.
Qed.

(* (* Freshness ([s ∉ dom Δ]) makes [s] absent from the resolution map, so
      deleting it is a no-op (used to discharge the [Effect] binder). *)
   Lemma resolve_map_delete_fresh proj Δ δ s :
     s ∉ dom Δ → delete s (resolve_map proj Δ δ) = resolve_map proj Δ δ.
   Proof.
     intros Hs. apply delete_id. rewrite resolve_map_lookup.
     by rewrite (not_elem_of_dom_1 _ _ Hs).
   Qed. *)

(* Keep [resolve_map] from unfolding to [map_imap] during unification: the
   semantic-typing cases only need it via the lemmas above, and unfolding it
   eagerly under [lbl_resolve] makes [iApply] of the compatibility lemmas
   blow up. *)
Global Opaque resolve_map.

Notation "⟦ Γ ⟧*" := (env_sem_typed Γ).

(** * The semantic typing judgement *)
Section bin_log_related.
  Context `{!probblazeRGS Σ}.

  Definition bin_log_related (E : coPset)
             (Δ : stringmap unit) (Γ1 : list (string * type))
             (e e' : expr) (ρ : row) (τ : type) (Γ2 : list (string * type)) : iProp Σ :=
    (∀ (η : list (sem_ty Σ))
       (μ : list mode)
       (δ : gmap eff_name (label * label))
       (ξ : list (sem_row Σ)),
        ⌜ dom Δ ⊆ dom δ ⌝ -∗
       let Γ1'  :=  (λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> Γ1 in
       let Γ2' :=  (λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> Γ2 in
       let ρ' := (interp._row η μ δ ρ ξ) in
       let τ' := interp._ty η μ δ τ ξ in
       sem_typed Γ1' (lbl_resolve (resolve_l Δ δ) e)
                     (lbl_resolve (resolve_r Δ δ) e') ρ' τ' Γ2').

        (* ⟦ (λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> Γ1 ⟧* vs -∗
              BREL (subst_map (fst <$> vs) e)
               ≤ (subst_map (snd <$> vs) e') @ E <| iLblSig_to_iLblThy (interp._row η μ δ ρ ξ) |> {{λ v1 v2, interp._ty η μ δ τ ξ v1 v2 
                                                                                                             ∗ ⟦ (λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> Γ2 ⟧* vs}})%I. *)
  
  Definition bin_log_val_related (v v' : val) (τ : type) : iProp Σ :=
    ∀ (η : list (sem_ty Σ))
      (μ : list mode)
      (δ : gmap eff_name (label * label))
      (ξ : list (sem_row Σ)), sem_val_typed v v' (interp._ty η μ δ τ ξ).

  Definition bin_log_pure_related (Δ : stringmap unit) (Γ : list (string * type)) (e e' : expr) (τ : type) : iProp Σ :=
    ∀ (η : list (sem_ty Σ))
      (μ : list mode)
      (δ : gmap eff_name (label * label))
      (ξ : list (sem_row Σ)),
      ⌜ dom Δ ⊆ dom δ ⌝ -∗
      let Γ'  :=  (λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> Γ in
      let τ' := (interp._ty η μ δ τ ξ) in
      sem_oval_typed Γ' (lbl_resolve (resolve_l Δ δ) e)
                        (lbl_resolve (resolve_r Δ δ) e') τ'.


End bin_log_related.

Notation "〈 E ';' Δ ';' Γ1 〉 ⊨ₜ e '≤log≤' e' : ρ : τ ⫤ Γ2" :=
  (bin_log_related E Δ Γ1 e%E e'%E ρ (τ)%ty Γ2)
  (at level 100, E at next level, Δ at next level, Γ1 at next level, e, e' at next level, ρ at next level, 
   τ at next level, Γ2 at level 200,
   format "'[hv' 〈 E ';'  Δ ';'  Γ1 〉  ⊨ₜ  '/  ' e  '/' '≤log≤'  '/  ' e'  : ρ : τ ⫤ Γ2 ']'").
Notation "〈 Δ ';' Γ1 〉 ⊨ₜ e '≤log≤' e' : ρ : τ ⫤ Γ2" :=
  (bin_log_related ⊤ Δ Γ1 e%E e'%E ρ (τ)%ty Γ2)
  (at level 100, Δ at next level, Γ1 at next level, e, e' at next level, ρ at next level, 
   τ at next level, Γ2 at level 200,
   format "'[hv' 〈 Δ ';'  Γ1 〉  ⊨ₜ  '/  ' e  '/' '≤log≤'  '/  ' e'  : ρ : τ ⫤ Γ2 ']'").

Notation "⊨ᵥ v '≤log≤' v' : τ" :=
  (bin_log_val_related v%V v'%V (τ)%ty)
    (at level 100, v, v' at next level,
       τ at level 200,
         format "'[hv' ⊨ᵥ  '/  ' v  '/' '≤log≤'  '/  ' v'  : τ ']'").

Notation "⟨ Δ ';' Γ ⟩ ⊨ₚ e '≤log≤' e' : τ" :=
  (bin_log_pure_related e%E e'%E (τ)%ty)
    (at level 100,  e, e' at next level,
       τ at level 200,
         format "'[hv' ⟨ Δ ';' Γ ⟩ ⊨ₚ  '/  ' e  '/' '≤log≤'  '/  ' e'  : τ ']'").


(* ======================================================================= *)
(** * Interpretation vs. syntactic substitution                            *)
(*                                                                          *)
(*  Scaffolding for the fundamental theorem's abstraction-elimination /     *)
(*  fold / pack cases.  We derive a mutual induction scheme for the         *)
(*  type / row / eff_sig syntax and prove the type-dimension RENAMING       *)
(*  lemma [ty_ren] (interp commutes with a reindexing of the type-env η),   *)
(*  together with the OFE-congruence ([Proper]) instances the congruence    *)
(*  steps need.  The three single-substitution lemmas (T1/T2/T3) are        *)
(*  stated at the end; see the long comment there for their current status. *)
(* ======================================================================= *)

Scheme type_mut := Induction for type Sort Prop
with row_mut := Induction for row Sort Prop
with eff_sig_mut := Induction for eff_sig Sort Prop.

(* Mutual induction scheme on the syntactic subtyping derivations
   [le._eff_sig] / [le._row] / [le._type].  Unlike the auto-generated
   [le._type_ind] (which does NOT carry the induction hypotheses for the
   mutually-recursive [_row]/[_eff_sig] occurrences, e.g. in the
   [TArrow_le] case), this scheme threads all three predicates [P]/[P0]/[P1]
   so subtyping soundness can be proven by simultaneous induction. *)
Scheme le_eff_sig_mut := Induction for le._eff_sig Sort Prop
with le_row_mut := Induction for le._row Sort Prop
with le_type_mut := Induction for le._type Sort Prop.

(* The combined scheme proves the CONJUNCTION of the three predicates with
   one set of case-hypotheses and one uniform set of IH names, so the
   soundness proof can be a single simultaneous induction. *)
Combined Scheme le_subtyping_mut from
  le_eff_sig_mut, le_row_mut, le_type_mut.

Section interp_subst.
  Context `{!probblazeRGS Σ}.

  (* --- OFE-congruence support ---------------------------------------- *)
  (* sem_types.v leaves the [≡]-Proper instances for the polymorphic      *)
  (* builders commented out / Admitted, but the NonExpansive ones are     *)
  (* available; we package the [≡] versions here (via [equiv_dist]) so    *)
  (* that [f_equiv] can drive the congruence steps below.                 *)

  Local Instance mode_forall_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@sem_ty_mode_forall Σ _).
  Proof.
    intros C C' HC. apply equiv_dist=> n.
    apply sem_ty_type_forall_mode_ne=> m. by apply equiv_dist.
  Qed.
  Local Instance type_forall_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@sem_ty_type_forall Σ _).
  Proof.
    intros C C' HC. apply equiv_dist=> n.
    apply sem_ty_type_forall_ne=> τ'. by apply equiv_dist.
  Qed.
  Local Instance row_forall_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@sem_ty_row_forall Σ _).
  Proof.
    intros C C' HC. apply equiv_dist=> n.
    apply sem_ty_type_forall_row_ne=> ρ. by apply equiv_dist.
  Qed.
  Local Instance rec_proper : Proper ((≡) ==> (≡)) (@sem_ty_rec Σ).
  Proof. apply ne_proper. apply _. Qed.
  Local Instance row_union_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (@sem_row_union Σ).
  Proof. apply ne_proper_2. solve_proper. Qed.
  Local Instance sig_eff_proper op1 op2 :
    Proper (pointwise_relation _ (≡) ==> pointwise_relation _ (≡) ==> (≡))
      (@sem_sig_eff Σ op1 op2).
  Proof.
    intros A A' HA B B' HB. apply equiv_dist=> n.
    apply sem_sig_eff_ne; intros τ'; by apply equiv_dist.
  Qed.

  (* Extending the type-env [η] on both sides by the same [τ'] turns a    *)
  (* reindexing [f] into [upren f].                                       *)
  Local Lemma up_ren_env (τ' : sem_ty Σ) (η η' : list (sem_ty Σ))
    (f : var → var) :
    (∀ i, η' !!! i ≡ η !!! (f i)) →
    ∀ i, (τ' :: η') !!! i ≡ (τ' :: η) !!! (upren f i).
  Proof.
    intros Hf [|i]; first done.
    rewrite !lookup_total_cons_ne_0 //.
  Qed.

  (** Type-dimension RENAMING.  Interpreting [rename f τ] in env [η] is the
      same as interpreting [τ] in any env [η'] that [f]-reindexes into [η].
      Unconditionally true; proved by mutual induction over type/row/sig. *)
  Lemma ty_ren :
    (∀ (τ : type) (η η' : list (sem_ty Σ)) (μ : list mode)
        (δ : gmap eff_name (label*label)) (ξ : list (sem_row Σ))
        (f : var → var),
        (∀ i, η' !!! i ≡ η !!! (f i)) →
        interp._ty η' μ δ τ ξ ≡ interp._ty η μ δ (rename f τ) ξ).
  Proof.
    intros τ. induction τ using type_mut
      with (P0 := λ ρ, ∀ η η' μ δ ξ f,
              (∀ i, η' !!! i ≡ η !!! (f i)) →
              interp._row η' μ δ ρ ξ ≡
                interp._row η μ δ (rename_type_row f ρ) ξ)
           (P1 := λ e, ∀ η η' μ δ ξ f,
              (∀ i, η' !!! i ≡ η !!! (f i)) →
              interp._eff_sig η' μ δ e ξ ≡
                interp._eff_sig η μ δ (rename_type_eff_sig f e) ξ);
      intros η η' μ δ ξ f Hf; simpl; eauto.
    all: try (by f_equiv; try intros ?τ; eauto using up_ren_env).
    all: try (do 2 f_equiv; try intros ?τ; eauto using up_ren_env).
  Qed.

  (** δ-IRRELEVANCE.  [interp._ty] depends on [δ] only through [δ !!! s] at
      each [SSig s] node.  So updating [δ] at a name [s] absent from the
      free effect names leaves the interpretation unchanged.  Used in the
      [Effect] fundamental case to reconcile the IH (taken at the extended
      [δ' := <[s:=(l1,l2)]>δ]) with the OUTER [δ] for the fresh [s]. *)
  Lemma ty_delta_irrel (δ : gmap eff_name (label*label))
    (s : eff_name) (lp : label * label) :
    (∀ (τ : type) (η : list (sem_ty Σ)) (μ : list mode)
        (ξ : list (sem_row Σ)),
        s ∉ vars._ty τ →
        interp._ty η μ (<[s:=lp]> δ) τ ξ ≡ interp._ty η μ δ τ ξ).
  Proof.
    intros τ. induction τ using type_mut
      with (P0 := λ ρ, ∀ η μ ξ, s ∉ vars._row ρ →
              interp._row η μ (<[s:=lp]> δ) ρ ξ ≡ interp._row η μ δ ρ ξ)
           (P1 := λ e, ∀ η μ ξ, s ∉ vars._eff_sig vars._ty e →
              interp._eff_sig η μ (<[s:=lp]> δ) e ξ ≡
                interp._eff_sig η μ δ e ξ);
      intros η μ ξ Hs; simpl in *; eauto.
    all: rewrite ?lookup_total_insert_ne; unfold vars._row, vars._row_pre, vars._eff_sig in *.
    all: try (by f_equiv; intros x; eauto).
    all: try (by f_equiv; eauto; set_solver).
    - f_equiv; intros x; eauto; set_solver.
    - set_solver.
  Qed.

  (* The eff_sig / row companions, by the same [type_mut] induction but
     concluding on the [_eff_sig] / [_row] predicate. *)
  Lemma eff_sig_delta_irrel (δ : gmap eff_name (label*label))
    (s : eff_name) (lp : label * label) :
    (∀ (e : eff_sig) (η : list (sem_ty Σ)) (μ : list mode)
        (ξ : list (sem_row Σ)),
        s ∉ vars._eff_sig vars._ty e →
        interp._eff_sig η μ (<[s:=lp]> δ) e ξ ≡
          interp._eff_sig η μ δ e ξ).
  Proof.
    intros e. induction e; intros η μ ξ Hs; simpl in *.
    - (* SSig: type-args via [ty_delta_irrel]; the head label is [δ !!! s0]
         with [s ≠ s0] (freshness). *)
      rewrite lookup_total_insert_ne; [|set_solver].
      f_equiv; intros τ'; apply ty_delta_irrel;
        unfold vars._eff_sig in Hs; set_solver.
    - (* SFlip *) f_equiv. by apply IHe.
  Qed.

  Lemma row_delta_irrel (δ : gmap eff_name (label*label))
    (s : eff_name) (lp : label * label) :
    (∀ (ρ : row) (η : list (sem_ty Σ)) (μ : list mode)
        (ξ : list (sem_row Σ)),
        s ∉ vars._row ρ →
        interp._row η μ (<[s:=lp]> δ) ρ ξ ≡ interp._row η μ δ ρ ξ).
  Proof.
    intros ρ. induction ρ; intros η μ ξ Hs;
      unfold vars._row, vars._row_pre in *; simpl in *.
    - done.
    - f_equiv; [apply (eff_sig_delta_irrel δ)|apply IHρ];
        unfold vars._eff_sig, vars._row, vars._row_pre in *; set_solver.
    - done.
    - f_equiv. apply IHρ.
      unfold vars._row, vars._row_pre in *; set_solver.
    - f_equiv; [apply IHρ1|apply IHρ2];
        unfold vars._row, vars._row_pre in *; set_solver.
  Qed.

  (* Per-element context δ-irrelevance (the env equality used by [sem_typed]
     is set-/membership-based; this gives the pointwise type-irrelevance that
     a future [Effect] proof can lift to the whole environment). *)
  Lemma ctx_elem_delta_irrel (δ : gmap eff_name (label*label))
    (s : eff_name) (lp : label * label)
    (Γ : list (string * type)) (x : string) (α : type)
    (η : list (sem_ty Σ)) (μ : list mode) (ξ : list (sem_row Σ)) :
    s ∉ vars._ctx Γ → (x, α) ∈ Γ →
    interp._ty η μ (<[s:=lp]> δ) α ξ ≡ interp._ty η μ δ α ξ.
  Proof.
    intros Hs Hin. apply ty_delta_irrel. intros Hα. apply Hs.
    rewrite /vars._ctx elem_of_union_list. eexists. split; [|exact Hα].
    by apply (list_elem_of_fmap_2' (λ '(_, α), vars._ty α) Γ (x, α)).
  Qed.

  (* For a type parallel-subst [σ], extending [η] by [τ'] (a type binder)
     turns [σ] into [up σ]; the shifted entries are reconciled by ty_ren. *)
  Local Lemma up_subst_env (τ' : sem_ty Σ) (η η' : list (sem_ty Σ))
    (μ : list mode) (δ : gmap eff_name (label*label))
    (ξ : list (sem_row Σ)) (σ : var → type) :
    (∀ i, η' !!! i ≡ interp._ty η μ δ (σ i) ξ) →
    ∀ i, (τ' :: η') !!! i ≡ interp._ty (τ' :: η) μ δ ((up σ) i) ξ.
  Proof.
    intros Hσ [|i]; first done.
    rewrite lookup_total_cons_ne_0 //=. asimpl.
    rewrite -rename_subst.
    rewrite -(ty_ren (σ i) (τ' :: η) η μ δ ξ (+1)).
    - apply Hσ.
    - intros j. by rewrite lookup_total_cons_ne_0.
  Qed.

  (* --- Mode-dimension helpers ---------------------------------------- *)
  Local Lemma mode_ren (μ μ' : list mode) (f : var → var) (vm : vmode) :
    (∀ i, μ' !!! (f i) = μ !!! i) →
    interp._mode μ' (rename f vm) = interp._mode μ vm.
  Proof. intros Hf. destruct vm; simpl; [done|done|apply Hf]. Qed.

  Local Lemma up_mode_env (m' : mode) (μ μ' : list mode) (σ : var → vmode) :
    (∀ i, μ' !!! i = interp._mode μ (σ i)) →
    ∀ i, (m' :: μ') !!! i = interp._mode (m' :: μ) ((up σ) i).
  Proof.
    intros Hσ [|i]; first done.
    rewrite lookup_total_cons_ne_0 //=. asimpl.
    rewrite -rename_subst.
    rewrite (mode_ren μ (m' :: μ) (+1) (σ i)).
    - apply Hσ.
    - intros j. by rewrite lookup_total_cons_ne_0.
  Qed.

  Local Lemma mode_subst_pt (μ μ' : list mode) (σ : var → vmode)
    (vm : vmode) :
    (∀ i, μ' !!! i = interp._mode μ (σ i)) →
    interp._mode μ (vm.[σ]) = interp._mode μ' vm.
  Proof.
    intros Hσ. destruct vm; simpl; [done|done|]. by rewrite Hσ.
  Qed.

  (** MODE parallel substitution.  Interpreting [τ.|[σm]] reindexes the
      mode-env [μ] by [σm].  Proved by mutual induction; the cross-sort
      binders need only [up_mode_env]/[mode_subst_pt]. *)
  Lemma ty_msubst :
    (∀ (τ : type) (η : list (sem_ty Σ)) (μ μ' : list mode)
        (δ : gmap eff_name (label*label)) (ξ : list (sem_row Σ))
        (σ : var → vmode),
        (∀ i, μ' !!! i = interp._mode μ (σ i)) →
        interp._ty η μ' δ τ ξ ≡ interp._ty η μ δ (τ.|[σ]) ξ).
  Proof.
    intros τ. induction τ using type_mut
      with (P0 := λ ρ, ∀ η μ μ' δ ξ σ,
              (∀ i, μ' !!! i = interp._mode μ (σ i)) →
              interp._row η μ' δ ρ ξ ≡ interp._row η μ δ (ρ.|[σ]) ξ)
           (P1 := λ e, ∀ η μ μ' δ ξ σ,
              (∀ i, μ' !!! i = interp._mode μ (σ i)) →
              interp._eff_sig η μ' δ e ξ ≡
                interp._eff_sig η μ δ (e.|[σ]) ξ);
      intros η μ μ' δ ξ σ Hσ; simpl; eauto.
    all: try (by f_equiv; eauto).
    all: try (by f_equiv; intros x; eauto using up_mode_env).
    all: erewrite <-?mode_subst_pt by done; by f_equiv; eauto.
  Qed.

  (* Extending [ξ] on both sides by the same [ρ'] turns a row reindexing
     [f] into [upren f]. *)
  Local Lemma up_ren_row_env (ρ' : sem_row Σ) (ξ ξ' : list (sem_row Σ))
    (f : var → var) :
    (∀ i, ξ' !!! i ≡ ξ !!! (f i)) →
    ∀ i, (ρ' :: ξ') !!! i ≡ (ρ' :: ξ) !!! (upren f i).
  Proof.
    intros Hf [|i]; first done.
    rewrite !lookup_total_cons_ne_0 //.
  Qed.

  (** ROW-dimension RENAMING.  Interpreting [rename f ρ] in [ξ] is the same
      as interpreting [ρ] in any [ξ'] that [f]-reindexes into [ξ]. *)
  Lemma row_ren :
    (∀ (τ : type) (η : list (sem_ty Σ)) (μ : list mode)
        (δ : gmap eff_name (label*label)) (ξ ξ' : list (sem_row Σ))
        (f : var → var),
        (∀ i, ξ' !!! i ≡ ξ !!! (f i)) →
        interp._ty η μ δ τ ξ' ≡ interp._ty η μ δ (rename_row_type f τ) ξ).
  Proof.
    intros τ. induction τ using type_mut
      with (P0 := λ ρ, ∀ η μ δ ξ ξ' f,
              (∀ i, ξ' !!! i ≡ ξ !!! (f i)) →
              interp._row η μ δ ρ ξ' ≡ interp._row η μ δ (rename f ρ) ξ)
           (P1 := λ e, ∀ η μ δ ξ ξ' f,
              (∀ i, ξ' !!! i ≡ ξ !!! (f i)) →
              interp._eff_sig η μ δ e ξ' ≡
                interp._eff_sig η μ δ (rename_row_eff_sig f e) ξ);
      intros η μ δ ξ ξ' f Hf; simpl; eauto.
    all: try (by f_equiv; eauto).
    all: try (by f_equiv; intros ?x; eauto using up_ren_row_env).
  Qed.

  Lemma row_ren_row (ρ : row) (η : list (sem_ty Σ)) (μ : list mode)
    (δ : gmap eff_name (label*label)) (ξ ξ' : list (sem_row Σ))
    (f : var → var) :
    (∀ i, ξ' !!! i ≡ ξ !!! (f i)) →
    interp._row η μ δ ρ ξ' ≡ interp._row η μ δ (rename f ρ) ξ.
  Proof.
    revert η μ δ ξ ξ' f.
    induction ρ using row_mut
      with (P := λ τ, ∀ η μ δ ξ ξ' f,
              (∀ i, ξ' !!! i ≡ ξ !!! (f i)) →
              interp._ty η μ δ τ ξ' ≡
                interp._ty η μ δ (rename_row_type f τ) ξ)
           (P1 := λ e, ∀ η μ δ ξ ξ' f,
              (∀ i, ξ' !!! i ≡ ξ !!! (f i)) →
              interp._eff_sig η μ δ e ξ' ≡
                interp._eff_sig η μ δ (rename_row_eff_sig f e) ξ);
      intros η μ δ ξ ξ' f Hf; simpl.
    all: lazymatch goal with
         | |- _ ≡ _ =>
           solve [ done
                 | apply Hf
                 | f_equiv; eauto using up_ren_row_env
                 | f_equiv; intros ?; eauto using up_ren_row_env ]
         end.
  Qed.

  (* ROW projection of [ty_ren] (TYPE renaming on a row). *)
  Lemma ty_ren_row (ρ : row) (η η' : list (sem_ty Σ)) (μ : list mode)
    (δ : gmap eff_name (label*label)) (ξ : list (sem_row Σ))
    (f : var → var) :
    (∀ i, η' !!! i ≡ η !!! (f i)) →
    interp._row η' μ δ ρ ξ ≡ interp._row η μ δ (rename_type_row f ρ) ξ.
  Proof.
    revert η η' μ δ ξ f.
    induction ρ using row_mut
      with (P := λ τ, ∀ η η' μ δ ξ f,
              (∀ i, η' !!! i ≡ η !!! (f i)) →
              interp._ty η' μ δ τ ξ ≡ interp._ty η μ δ (rename f τ) ξ)
           (P1 := λ e, ∀ η η' μ δ ξ f,
              (∀ i, η' !!! i ≡ η !!! (f i)) →
              interp._eff_sig η' μ δ e ξ ≡
                interp._eff_sig η μ δ (rename_type_eff_sig f e) ξ);
      intros η η' μ δ ξ f Hf; simpl.
    all: lazymatch goal with
         | |- _ ≡ _ =>
           solve [ done
                 | apply Hf
                 | f_equiv; eauto using up_ren_env
                 | f_equiv; intros ?; eauto using up_ren_env ]
         end.
  Qed.

  (* ROW weakening: a freshly-bound TYPE var does not affect a type-shifted
     row.  Corollary of [ty_ren_row]. *)
  Lemma row_tweaken (ρ : row) (τ' : sem_ty Σ) (η : list (sem_ty Σ))
    (μ : list mode) (δ : gmap eff_name (label*label))
    (ξ : list (sem_row Σ)) :
    interp._row (τ' :: η) μ δ (rename_type_row (+1) ρ) ξ
      ≡ interp._row η μ δ ρ ξ.
  Proof.
    symmetry. apply (ty_ren_row ρ (τ' :: η) η μ δ ξ (+1)).
    intros i. rewrite lookup_total_cons_ne_0 //.
  Qed.

  (* ROW weakening on TYPES: a freshly-bound ROW var does not affect a
     row-shifted type.  Corollary of [row_ren] (type projection). *)
  Lemma ty_rweaken (τ : type) (η : list (sem_ty Σ)) (μ : list mode)
    (δ : gmap eff_name (label*label)) (ρ' : sem_row Σ)
    (ξ : list (sem_row Σ)) :
    interp._ty η μ δ (rename_row_type (+1) τ) (ρ' :: ξ)
      ≡ interp._ty η μ δ τ ξ.
  Proof.
    symmetry. apply (row_ren τ η μ δ (ρ' :: ξ) ξ (+1)).
    intros i. rewrite lookup_total_cons_ne_0 //.
  Qed.

  (* ROW projection of [ty_msubst] (mode parallel subst on a row). *)
  Lemma ty_msubst_row (ρ : row) (η : list (sem_ty Σ)) (μ μ' : list mode)
    (δ : gmap eff_name (label*label)) (ξ : list (sem_row Σ))
    (σ : var → vmode) :
    (∀ i, μ' !!! i = interp._mode μ (σ i)) →
    interp._row η μ' δ ρ ξ ≡ interp._row η μ δ (ρ.|[σ]) ξ.
  Proof.
    revert η μ μ' δ ξ σ.
    induction ρ using row_mut
      with (P := λ τ, ∀ η μ μ' δ ξ σ,
              (∀ i, μ' !!! i = interp._mode μ (σ i)) →
              interp._ty η μ' δ τ ξ ≡ interp._ty η μ δ (τ.|[σ]) ξ)
           (P1 := λ e, ∀ η μ μ' δ ξ σ,
              (∀ i, μ' !!! i = interp._mode μ (σ i)) →
              interp._eff_sig η μ' δ e ξ ≡
                interp._eff_sig η μ δ (e.|[σ]) ξ);
      intros η μ μ' δ ξ σ Hσ; simpl.
    all: lazymatch goal with
         | |- _ ≡ _ =>
           solve [ done
                 | (erewrite <-mode_subst_pt by done); f_equiv;
                     eauto using up_mode_env
                 | f_equiv; intros ?; eauto using up_mode_env
                 | f_equiv; eauto using up_mode_env ]
         end.
  Qed.

  (* MODE weakening: a freshly-bound mode does not affect a mode-shifted
     type/row.  Corollaries of [ty_msubst]/[ty_msubst_row]. *)
  Lemma ty_mweaken (τ : type) (η : list (sem_ty Σ)) (m : mode)
    (μ : list mode) (δ : gmap eff_name (label*label))
    (ξ : list (sem_row Σ)) :
    interp._ty η (m :: μ) δ (τ.|[ren (+1) : var → vmode]) ξ
      ≡ interp._ty η μ δ τ ξ.
  Proof.
    symmetry. apply (ty_msubst τ η (m :: μ) μ δ ξ (ren (+1))).
    intros i. destruct i; simpl; by rewrite ?lookup_total_cons_ne_0.
  Qed.

  Lemma row_mweaken (ρ : row) (η : list (sem_ty Σ)) (m : mode)
    (μ : list mode) (δ : gmap eff_name (label*label))
    (ξ : list (sem_row Σ)) :
    interp._row η (m :: μ) δ (ρ.|[ren (+1) : var → vmode]) ξ
      ≡ interp._row η μ δ ρ ξ.
  Proof.
    symmetry. apply (ty_msubst_row ρ η (m :: μ) μ δ ξ (ren (+1))).
    intros i. destruct i; simpl; by rewrite ?lookup_total_cons_ne_0.
  Qed.

  (* ROW weakening: a freshly-bound row does not affect a row-shifted row.
     Corollary of [row_ren_row]. *)
  Lemma row_rweaken (ρ : row) (η : list (sem_ty Σ)) (μ : list mode)
    (δ : gmap eff_name (label*label)) (ρ' : sem_row Σ)
    (ξ : list (sem_row Σ)) :
    interp._row η μ δ (rename (+1) ρ) (ρ' :: ξ) ≡ interp._row η μ δ ρ ξ.
  Proof.
    symmetry. apply (row_ren_row ρ η μ δ (ρ' :: ξ) ξ (+1)).
    intros i. rewrite lookup_total_cons_ne_0 //.
  Qed.

  (* For a row parallel-subst [σ], extending [ξ] by [ρ'] (a row binder)
     turns [σ] into [up σ]; shifted entries reconciled by [row_rweaken]. *)
  Local Lemma up_row_env (ρ' : sem_row Σ) (η : list (sem_ty Σ))
    (μ : list mode) (δ : gmap eff_name (label*label))
    (ξ ξ' : list (sem_row Σ)) (σ : var → row) :
    (∀ i, ξ' !!! i ≡ interp._row η μ δ (σ i) ξ) →
    ∀ i, (ρ' :: ξ') !!! i ≡ interp._row η μ δ ((up σ) i) (ρ' :: ξ).
  Proof.
    intros Hσ [|i]; first done.
    rewrite lookup_total_cons_ne_0 //=. asimpl.
    rewrite -rename_subst row_rweaken. apply Hσ.
  Qed.

  (** ROW parallel substitution.  Interpreting [τ.|[σ]] reindexes the
      row-env [ξ] by [σ].  Cross-sort binders: type binders leave [ξ]/[σ];
      the mode binder ([TForallM]) extends [μ] and mode-shifts the
      substitutends, reconciled by [row_mweaken]; the row binder
      ([TForallR]) uses [up_row_env]. *)
  Lemma ty_rsubst :
    (∀ (τ : type) (η : list (sem_ty Σ)) (μ : list mode)
        (δ : gmap eff_name (label*label)) (ξ ξ' : list (sem_row Σ))
        (σ : var → row),
        (∀ i, ξ' !!! i ≡ interp._row η μ δ (σ i) ξ) →
        interp._ty η μ δ τ ξ' ≡ interp._ty η μ δ (τ.|[σ]) ξ).
  Proof.
    intros τ. induction τ using type_mut
      with (P0 := λ ρ, ∀ (η : list (sem_ty Σ)) (μ : list mode)
              (δ : gmap eff_name (label*label)) (ξ ξ' : list (sem_row Σ))
              (σ : var → row),
              (∀ i, ξ' !!! i ≡ interp._row η μ δ (σ i) ξ) →
              interp._row η μ δ ρ ξ' ≡ interp._row η μ δ (ρ.[σ]) ξ)
           (P1 := λ e, ∀ (η : list (sem_ty Σ)) (μ : list mode)
              (δ : gmap eff_name (label*label)) (ξ ξ' : list (sem_row Σ))
              (σ : var → row),
              (∀ i, ξ' !!! i ≡ interp._row η μ δ (σ i) ξ) →
              interp._eff_sig η μ δ e ξ' ≡
                interp._eff_sig η μ δ (e.|[σ]) ξ);
      intros η μ δ ξ ξ' σ Hσ; simpl.
    all: lazymatch goal with
         | |- _ ≡ _ =>
           solve
             [ done | apply Hσ
             | f_equiv; intros m;
                 match goal with IH : _ |- _ => apply IH end;
                 intros i; rewrite row_mweaken; apply Hσ
             | f_equiv; intros τ';
                 match goal with IH : _ |- _ => apply IH end;
                 intros i; rewrite row_tweaken; apply Hσ
             | f_equiv; eauto using up_row_env
             | f_equiv; intros ?; eauto using up_row_env ]
         end.
  Qed.

  (** TYPE parallel substitution.  Interpreting [τ.[σ]] reindexes the
      type-env [η] by [σ].  Cross-sort binders: the mode binder
      ([TForallM]) mode-shifts the substitutends ([ty_mweaken]); the row
      binder ([TForallR]) row-shifts them ([ty_rweaken]); the type binders
      use [up_subst_env]. *)
  Lemma ty_tsubst :
    (∀ (τ : type) (η η' : list (sem_ty Σ)) (μ : list mode)
        (δ : gmap eff_name (label*label)) (ξ : list (sem_row Σ))
        (σ : var → type),
        (∀ i, η' !!! i ≡ interp._ty η μ δ (σ i) ξ) →
        interp._ty η' μ δ τ ξ ≡ interp._ty η μ δ (τ.[σ]) ξ).
  Proof.
    intros τ. induction τ using type_mut
      with (P0 := λ ρ, ∀ (η η' : list (sem_ty Σ)) (μ : list mode)
              (δ : gmap eff_name (label*label)) (ξ : list (sem_row Σ))
              (σ : var → type),
              (∀ i, η' !!! i ≡ interp._ty η μ δ (σ i) ξ) →
              interp._row η' μ δ ρ ξ ≡ interp._row η μ δ (ρ.|[σ]) ξ)
           (P1 := λ e, ∀ (η η' : list (sem_ty Σ)) (μ : list mode)
              (δ : gmap eff_name (label*label)) (ξ : list (sem_row Σ))
              (σ : var → type),
              (∀ i, η' !!! i ≡ interp._ty η μ δ (σ i) ξ) →
              interp._eff_sig η' μ δ e ξ ≡
                interp._eff_sig η μ δ (e.|[σ]) ξ);
      intros η η' μ δ ξ σ Hσ; simpl.
    all: lazymatch goal with
         | |- _ ≡ _ =>
           solve
             [ done | apply Hσ
             | f_equiv; intros m;
                 match goal with IH : _ |- _ => apply IH end;
                 intros i; rewrite ty_mweaken; apply Hσ
             | f_equiv; intros ρ';
                 match goal with IH : _ |- _ => apply IH end;
                 intros i; rewrite ty_rweaken; apply Hσ
             | f_equiv; eauto using up_subst_env
             | f_equiv; intros ?; eauto using up_subst_env ]
         end.
  Qed.

  (** ** The three single-substitution lemmas (T1/T2/T3).
      Each is the single-substitution ([_ .: ids]) corollary of the
      corresponding parallel-substitution lemma proved above. *)

  Lemma ty_subst_single (η : list (sem_ty Σ)) (μ : list mode)
    (δ : gmap eff_name (label*label)) (ξ : list (sem_row Σ))
    (τ τ' : type) :
    interp._ty η μ δ (τ.[τ'/]) ξ
      ≡ interp._ty (interp._ty η μ δ τ' ξ :: η) μ δ τ ξ.
  Proof.
    symmetry.
    refine (ty_tsubst τ η (interp._ty η μ δ τ' ξ :: η) μ δ ξ (τ' .: ids) _).
    intros [|i]; first done.
    rewrite lookup_total_cons_ne_0 //.
  Qed.

  Lemma row_subst_single (η : list (sem_ty Σ)) (μ : list mode)
    (δ : gmap eff_name (label*label)) (ξ : list (sem_row Σ))
    (τ : type) (ρ' : row) :
    interp._ty η μ δ (τ.|[ρ'/]) ξ
      ≡ interp._ty η μ δ τ (interp._row η μ δ ρ' ξ :: ξ).
  Proof.
    symmetry.
    refine
      (ty_rsubst τ η μ δ ξ (interp._row η μ δ ρ' ξ :: ξ) (ρ' .: ids) _).
    intros [|i]; first done.
    rewrite lookup_total_cons_ne_0 //.
  Qed.

  Lemma mode_subst_single (η : list (sem_ty Σ)) (μ : list mode)
    (δ : gmap eff_name (label*label)) (ξ : list (sem_row Σ))
    (τ : type) (m : vmode) :
    interp._ty η μ δ (τ.|[m/]) ξ
      ≡ interp._ty η (interp._mode μ m :: μ) δ τ ξ.
  Proof.
    symmetry.
    refine (ty_msubst τ η μ (interp._mode μ m :: μ) δ ξ (m .: ids) _).
    intros [|i]; first done.
    rewrite lookup_total_cons_ne_0 //.
  Qed.

  (* TYPE weakening: a freshly-bound TYPE var does not affect a type-shifted
     type.  Corollary of [ty_ren] (the [.[ren (+1)]] shift used by the
     context-shift operator [⤉]).  Used by the [TUnpack] fundamental case. *)
  Lemma ty_tweaken (τ : type) (τ' : sem_ty Σ) (η : list (sem_ty Σ))
    (μ : list mode) (δ : gmap eff_name (label*label))
    (ξ : list (sem_row Σ)) :
    interp._ty (τ' :: η) μ δ (τ.[ren (+1)]) ξ ≡ interp._ty η μ δ τ ξ.
  Proof.
    rewrite -rename_subst. symmetry.
    apply (ty_ren τ (τ' :: η) η μ δ ξ (+1)).
    intros i. rewrite lookup_total_cons_ne_0 //.
  Qed.

  (** [interp._ty] is NONEXPANSIVE in the type-env [η] (pointwise [dist]).
      Proved by mutual induction over type/row/sig.  Needed to obtain the
      [NonExpansive C] side condition of [sem_typed_fold]/[sem_typed_unfold]
      for [C := λ α, interp._ty (α :: η) μ δ τ ξ]. *)
  Lemma ty_ne_env :
    (∀ (τ : type) (η η' : list (sem_ty Σ)) (μ : list mode)
        (δ : gmap eff_name (label*label)) (ξ : list (sem_row Σ)) (n : nat),
        (∀ i, η !!! i ≡{n}≡ η' !!! i) →
        interp._ty η μ δ τ ξ ≡{n}≡ interp._ty η' μ δ τ ξ).
  Proof.
    intros τ. induction τ using type_mut
      with (P0 := λ ρ, ∀ η η' μ δ ξ n,
              (∀ i, η !!! i ≡{n}≡ η' !!! i) →
              interp._row η μ δ ρ ξ ≡{n}≡ interp._row η' μ δ ρ ξ)
           (P1 := λ e, ∀ η η' μ δ ξ n,
              (∀ i, η !!! i ≡{n}≡ η' !!! i) →
              interp._eff_sig η μ δ e ξ ≡{n}≡ interp._eff_sig η' μ δ e ξ);
      intros η η' μ δ ξ n Hf; simpl; eauto.
    all: try (by f_equiv; eauto).
    all: try (by f_equiv; intros x; eauto).
    all: try (f_equiv; intros τ'; apply IHτ; (intros [|i]; [done|apply Hf])).
    f_equiv; intros τ';
      [apply IHτ|apply IHτ0]; (intros [|i]; [done|apply Hf]).
  Qed.

  Global Instance interp_ty_head_ne (η : list (sem_ty Σ)) (μ : list mode)
    (δ : gmap eff_name (label*label)) (τ : type) (ξ : list (sem_row Σ)) :
    NonExpansive (λ α, interp._ty (α :: η) μ δ τ ξ).
  Proof.
    intros n x y Hxy. apply ty_ne_env. intros [|i]; [done|done].
  Qed.

  (* CONTEXT weakening: a freshly-bound TYPE var does not affect the
     interpretation of a type-shifted context [⤉Γ].  Pointwise corollary
     of [ty_tweaken], lifted to [env_sem_typed].  Used by the [TUnpack]
     fundamental case to cancel the [⤉Γ2]/[⤉Γ3] shifts at the extended
     type-env [τ'::η]. *)
  Lemma ctx_tweaken (Γ : ctx) (τ' : sem_ty Σ) (η : list (sem_ty Σ))
    (μ : list mode) (δ : gmap eff_name (label*label))
    (ξ : list (sem_row Σ)) (γ : gmap string (val*val)) :
    env_sem_typed
      ((λ '(s, α), (s, interp._ty (τ' :: η) μ δ α ξ)) <$> (⤉ Γ)) γ
    ⊣⊢
    env_sem_typed
      ((λ '(s, α), (s, interp._ty η μ δ α ξ)) <$> Γ) γ.
  Proof.
    induction Γ as [|[s α] Γ' IH]; simpl.
    - done.
    - rewrite !env_sem_typed_cons. rewrite IH.
      do 4 f_equiv. intros v2. f_equiv.
      exact (ty_tweaken α τ' η μ δ ξ a v2).
  Qed.

  (* CONTEXT weakening for a freshly-bound ROW var: a row-shifted context
     interpreted at the extended row-env [ρ'::ξ] agrees with the original.
     Pointwise corollary of [ty_rweaken], lifted to [env_sem_typed].  Used
     by the [RAbs_pure] fundamental case. *)
  Lemma ctx_rweaken (Γ : ctx) (ρ' : sem_row Σ) (η : list (sem_ty Σ))
    (μ : list mode) (δ : gmap eff_name (label*label))
    (ξ : list (sem_row Σ)) (γ : gmap string (val*val)) :
    env_sem_typed
      ((λ '(s, α), (s, interp._ty η μ δ α (ρ' :: ξ)))
         <$> ((λ '(x, α), (x, rename_row_type (+1) α)) <$> Γ)) γ
    ⊣⊢
    env_sem_typed
      ((λ '(s, α), (s, interp._ty η μ δ α ξ)) <$> Γ) γ.
  Proof.
    induction Γ as [|[s α] Γ' IH]; simpl.
    - done.
    - rewrite !env_sem_typed_cons. rewrite IH.
      do 4 f_equiv. intros v2. f_equiv.
      exact (ty_rweaken α η μ δ ρ' ξ a v2).
  Qed.

  (* CONTEXT weakening for a freshly-bound MODE var: a mode-shifted context
     interpreted at the extended mode-env [m::μ] agrees with the original.
     Pointwise corollary of [ty_mweaken], lifted to [env_sem_typed].  Used
     by the [MAbs_pure] fundamental case. *)
  Lemma ctx_mweaken (Γ : ctx) (m : mode) (η : list (sem_ty Σ))
    (μ : list mode) (δ : gmap eff_name (label*label))
    (ξ : list (sem_row Σ)) (γ : gmap string (val*val)) :
    env_sem_typed
      ((λ '(s, α), (s, interp._ty η (m :: μ) δ α ξ))
         <$> ((λ '(x, α), (x, α.|[ren (+1) : var → vmode])) <$> Γ)) γ
    ⊣⊢
    env_sem_typed
      ((λ '(s, α), (s, interp._ty η μ δ α ξ)) <$> Γ) γ.
  Proof.
    induction Γ as [|[s α] Γ' IH]; simpl.
    - done.
    - rewrite !env_sem_typed_cons. rewrite IH.
      do 4 f_equiv. intros v2. f_equiv.
      exact (ty_mweaken α η m μ δ ξ a v2).
  Qed.
End interp_subst.

Section labels.
  Context `{probblazeRGS Σ}.

  (* ============================================================== *)
  (* PHASE 1: discharge of [erase_ctx (row_to_disj_ctx ρ)] from the *)
  (* ambient label-validity + distinctness of the interpreted row.  *)
  (* (Added: label-structure lemmas for [interp._row].)             *)
  Lemma sig_labels_eff_name (e : eff_sig) η μ δ ξ :
    sem_sig_labels Σ (interp._eff_sig η μ δ e ξ)
    = δ !!! le.eff_name_from_sig e.
  Proof.
    induction e as [s α β| m e IH]; simpl.
    - by destruct (δ !!! s).
    - by rewrite /sem_sig_flip_mbang /= IH.
  Qed.

  Fixpoint row_labels_l (ρ : row) (ξ : list (sem_row Σ)) (δ : gmap eff_name (label*label)) : list label :=
    match ρ with
    | RNil => []
    | RVar i => labels_l (iLblSig_to_iLblThy (sem_row_car (ξ !!! (i : nat))))
    | RCons e ρ' => (δ !!! le.eff_name_from_sig e).1 :: @row_labels_l ρ' ξ δ
    | RFlip _ ρ' => @row_labels_l ρ' ξ δ
    | RUnion ρ1 ρ2 => @row_labels_l ρ1 ξ δ ++ @row_labels_l ρ2 ξ δ
    end.

  Lemma labels_l_interp_row (ρ : row) η μ δ ξ :
    labels_l (iLblSig_to_iLblThy (interp._row η μ δ ρ ξ)) = row_labels_l ρ ξ δ.
  Proof.
    induction ρ as [|e ρ' IH|i|m ρ' IH|ρ1 IH1 ρ2 IH2] in η, μ |- *.
    all: simpl.
    - done.
    - rewrite labels_l_cons (sig_labels_eff_name e η μ δ ξ) /=.
      f_equal. apply IH.
    - done.
    - rewrite iThyIfMono_iLblSig_to_iThyIfMono labels_l_to_iThyIfMono. apply IH.
    - rewrite /sem_row_union /= iLblSig_to_iLblThy_app labels_l_app.
      f_equal; [apply IH1|apply IH2].
  Qed.

  Fixpoint row_labels_r (ρ : row) (ξ : list (sem_row Σ)) (δ : gmap eff_name (label*label)) : list label :=
    match ρ with
    | RNil => []
    | RVar i => labels_r (iLblSig_to_iLblThy (sem_row_car (ξ !!! (i : nat))))
    | RCons e ρ' => (δ !!! le.eff_name_from_sig e).2 :: row_labels_r ρ' ξ δ
    | RFlip _ ρ' => row_labels_r ρ' ξ δ
    | RUnion ρ1 ρ2 => row_labels_r ρ1 ξ δ ++ row_labels_r ρ2 ξ δ
    end.

  Lemma labels_r_interp_row (ρ : row) η μ δ ξ :
    labels_r (iLblSig_to_iLblThy (interp._row η μ δ ρ ξ)) = row_labels_r ρ ξ δ.
  Proof.
    induction ρ as [|e ρ' IH|i|m ρ' IH|ρ1 IH1 ρ2 IH2] in η, μ |- *.
    all: simpl.
    - done.
    - rewrite labels_r_cons (sig_labels_eff_name e η μ δ ξ) /=.
      f_equal. apply IH.
    - done.
    - rewrite iThyIfMono_iLblSig_to_iThyIfMono labels_r_to_iThyIfMono. apply IH.
    - rewrite /sem_row_union /= iLblSig_to_iLblThy_app labels_r_app.
      f_equal; [apply IH1|apply IH2].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* PERMUTATION decomposition: separate the concrete (name) labels from
     the abstract (row-variable) labels. *)
  Definition name_labels_l (ss : gmultiset eff_name) (δ : gmap eff_name (label*label)) : list label :=
    (λ s, (δ !!! s).1) <$> elements ss.

  Fixpoint var_labels_l (ρ : row) (ξ : list (sem_row Σ)) : list label :=
    match ρ with
    | RNil => []
    | RVar i => labels_l (iLblSig_to_iLblThy (sem_row_car (ξ !!! (i : nat))))
    | RCons _ ρ' => var_labels_l ρ' ξ
    | RFlip _ ρ' => var_labels_l ρ' ξ
    | RUnion ρ1 ρ2 => var_labels_l ρ1 ξ ++ var_labels_l ρ2 ξ
    end.

  Lemma row_labels_l_split (ρ : row) ξ δ :
    row_labels_l ρ ξ δ ≡ₚ name_labels_l (le.conc_sigs ρ) δ ++ var_labels_l ρ ξ.
  Proof.
    induction ρ as [|e ρ' IH|i|m ρ' IH|ρ1 IH1 ρ2 IH2]; simpl.
    - done.
    - rewrite /name_labels_l gmultiset_elements_disj_union fmap_app
        gmultiset_elements_singleton /=. by rewrite IH.
    - rewrite /name_labels_l gmultiset_elements_empty /=. done.
    - apply IH.
    - rewrite /name_labels_l gmultiset_elements_disj_union fmap_app.
      rewrite IH1 IH2. solve_Permutation.
  Qed.

  (* Peel the [s]-occurrence off the front of a name-label list. *)
  Lemma name_labels_l_remove (ss : gmultiset eff_name) δ s :
    s ∈ ss → name_labels_l ss δ ≡ₚ (δ !!! s).1 :: name_labels_l (ss ∖ {[+ s +]}) δ.
  Proof.
    intros Hs. rewrite /name_labels_l.
    rewrite {1}(gmultiset_disj_union_difference' s ss Hs).
    by rewrite gmultiset_elements_disj_union gmultiset_elements_singleton fmap_app.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* MEMBERSHIP.  One characterisation per label list, each an [↔].
     These replace the former half-direction family
     [elem_of_row_labels_l_conc] / [elem_of_name_labels_l_mono] /
     [elem_of_var_labels_l_mono] / [elem_of_var_in_row_labels]: each of
     those was one direction of one of these, and the monotonicity
     statements are now the one-line consequence of transporting the
     witness along the subset hypothesis. *)

  Lemma elem_of_name_labels_l (ss : gmultiset eff_name) δ l :
    l ∈ name_labels_l ss δ ↔ ∃ s, s ∈ ss ∧ l = (δ !!! s).1.
  Proof.
    rewrite /name_labels_l list_elem_of_fmap.
    setoid_rewrite gmultiset_elem_of_elements. naive_solver.
  Qed.

  Lemma elem_of_var_labels_l (ρ : row) ξ l :
    l ∈ var_labels_l ρ ξ
    ↔ ∃ i, i ∈ le.abst_sigs ρ
         ∧ l ∈ labels_l (iLblSig_to_iLblThy (sem_row_car (ξ !!! (i:nat)))).
  Proof.
    induction ρ as [|e ρ' IH|i|m ρ' IH|ρ1 IH1 ρ2 IH2]; simpl.
    - rewrite elem_of_nil. split; [done|].
      intros (j & Hj & _). by apply elem_of_empty in Hj.
    - exact IH.
    - setoid_rewrite elem_of_singleton. naive_solver.
    - exact IH.
    - rewrite elem_of_app IH1 IH2. setoid_rewrite elem_of_union. naive_solver.
  Qed.

  Lemma elem_of_row_labels_l (ρ : row) ξ δ l :
    l ∈ row_labels_l ρ ξ δ
    ↔ (∃ s, s ∈ le.conc_sigs ρ ∧ l = (δ !!! s).1)
    ∨ (∃ i, i ∈ le.abst_sigs ρ
          ∧ l ∈ labels_l (iLblSig_to_iLblThy (sem_row_car (ξ !!! (i:nat))))).
  Proof.
    by rewrite row_labels_l_split elem_of_app
               elem_of_name_labels_l elem_of_var_labels_l.
  Qed.

  (* ------------------------- RIGHT-SIDE COPIES ----------------------- *)

  Definition name_labels_r (ss : gmultiset eff_name) (δ : gmap eff_name (label*label)) : list label :=
    (λ s, (δ !!! s).2) <$> elements ss.

  Fixpoint var_labels_r (ρ : row) (ξ : list (sem_row Σ)) : list label :=
    match ρ with
    | RNil => []
    | RVar i => labels_r (iLblSig_to_iLblThy (sem_row_car (ξ !!! (i : nat))))
    | RCons _ ρ' => var_labels_r ρ' ξ
    | RFlip _ ρ' => var_labels_r ρ' ξ
    | RUnion ρ1 ρ2 => var_labels_r ρ1 ξ ++ var_labels_r ρ2 ξ
    end.

  Lemma row_labels_r_split (ρ : row) ξ δ :
    row_labels_r ρ ξ δ ≡ₚ name_labels_r (le.conc_sigs ρ) δ ++ var_labels_r ρ ξ.
  Proof.
    induction ρ as [|e ρ' IH|i|m ρ' IH|ρ1 IH1 ρ2 IH2]; simpl.
    - done.
    - rewrite /name_labels_r gmultiset_elements_disj_union fmap_app
        gmultiset_elements_singleton /=. by rewrite IH.
    - rewrite /name_labels_r gmultiset_elements_empty /=. done.
    - apply IH.
    - rewrite /name_labels_r gmultiset_elements_disj_union fmap_app.
      rewrite IH1 IH2. solve_Permutation.
  Qed.

  Lemma name_labels_r_remove (ss : gmultiset eff_name) δ s :
    s ∈ ss → name_labels_r ss δ ≡ₚ (δ !!! s).2 :: name_labels_r (ss ∖ {[+ s +]}) δ.
  Proof.
    intros Hs. rewrite /name_labels_r.
    rewrite {1}(gmultiset_disj_union_difference' s ss Hs).
    by rewrite gmultiset_elements_disj_union gmultiset_elements_singleton fmap_app.
  Qed.

  Lemma elem_of_name_labels_r (ss : gmultiset eff_name) δ l :
    l ∈ name_labels_r ss δ ↔ ∃ s, s ∈ ss ∧ l = (δ !!! s).2.
  Proof.
    rewrite /name_labels_r list_elem_of_fmap.
    setoid_rewrite gmultiset_elem_of_elements. naive_solver.
  Qed.

  Lemma elem_of_var_labels_r (ρ : row) ξ l :
    l ∈ var_labels_r ρ ξ
    ↔ ∃ i, i ∈ le.abst_sigs ρ
         ∧ l ∈ labels_r (iLblSig_to_iLblThy (sem_row_car (ξ !!! (i:nat)))).
  Proof.
    induction ρ as [|e ρ' IH|i|m ρ' IH|ρ1 IH1 ρ2 IH2]; simpl.
    - rewrite elem_of_nil. split; [done|].
      intros (j & Hj & _). by apply elem_of_empty in Hj.
    - exact IH.
    - setoid_rewrite elem_of_singleton. naive_solver.
    - exact IH.
    - rewrite elem_of_app IH1 IH2. setoid_rewrite elem_of_union. naive_solver.
  Qed.

  Lemma elem_of_row_labels_r (ρ : row) ξ δ l :
    l ∈ row_labels_r ρ ξ δ
    ↔ (∃ s, s ∈ le.conc_sigs ρ ∧ l = (δ !!! s).2)
    ∨ (∃ i, i ∈ le.abst_sigs ρ
          ∧ l ∈ labels_r (iLblSig_to_iLblThy (sem_row_car (ξ !!! (i:nat))))).
  Proof.
    by rewrite row_labels_r_split elem_of_app
               elem_of_name_labels_r elem_of_var_labels_r.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Characterise lookups in [row_to_disj_ctx ρ]. *)
  (* NOTE: only used to prove erase_ctx_row_to_disj_ctx *)
  Lemma lookup_row_to_disj_ctx (ρ : row) s ss js :
    le.row_to_disj_ctx ρ !! s = Some (ss, js) ↔
      s ∈ le.conc_sigs ρ ∧ ss = le.conc_sigs ρ ∖ {[+ s +]}
      ∧ js = le.abst_sigs ρ.
  Proof.
    unfold le.row_to_disj_ctx.
    rewrite lookup_set_to_map.
    - split.
      + intros (s' & Hs' & Heq). simplify_eq/=.
        apply gmultiset_elem_of_dom in Hs'. done.
      + intros (Hs & -> & ->). exists s.
        split; [by apply gmultiset_elem_of_dom|done].
    - intros y y' _ _ Heq. simpl in Heq. done.
  Qed.

End labels.

Section erase_ctx.
  Context `{!probblazeRGS Σ}.

  (* The ownership + disjointness facts a derivation [_row D b ρ ρ'] may
     need: for every concrete label [s] recorded in [D] together with an
     inner row [ρ0] whose concrete/abstract signatures are dominated by the
     disjointness data of [s], the dynamic label [δ !!! s] is owned and is
     fresh for [ρ0].  This is precisely the premise bundle of
     [sem_row.row_le_erase] applied at [(δ!!!s).1]/[(δ!!!s).2]/[ρ0],
     uniformly over all interpretation environments [η μ ξ]. *)
  Definition erase_ctx δ ξ (D : le.disj_ctx) : iProp Σ :=
    □ (∀ (s : eff_name) (ss : gmultiset eff_name) (js : gset nat)
         (ρ0 : row),
          ⌜ D !! s = Some (ss, js) ⌝ -∗
          ⌜ le.conc_sigs ρ0 ⊆ ss ⌝ -∗
          ⌜ le.abst_sigs ρ0 ⊆ js ⌝ -∗
          is_label (δ !!! s).1 DfracDiscarded ∗
          spec_labels_frag (δ !!! s).2 DfracDiscarded ∗
          ⌜ (δ !!! s).1
              ∉ row_labels_l ρ0 ξ δ ⌝ ∗
          ⌜ (δ !!! s).2
              ∉ @row_labels_r Σ ρ0 ξ δ ⌝)%I.

  Global Instance erase_ctx_persistent D δ ξ : Persistent (erase_ctx δ ξ D).
  Proof. apply _. Qed.

  Lemma erase_ctx_empty δ ξ : ⊢ erase_ctx δ ξ ∅.
  Proof.
    rewrite /erase_ctx. iIntros "!#" (s ss js ρ0 Hlk).
    rewrite lookup_empty in Hlk. done.
  Qed.


  (* NOTE: used to prove TForallT *)
  (* Lemma erase_ctx_extend_ty η μ δ ξ D α :
       ⊢ erase_ctx η μ δ ξ D -∗ erase_ctx (α :: η) μ δ ξ D.
     Proof.
       iIntros "#HD !# % % % % % % %".
       iSpecialize ("HD" $! _ _ _ _).
       rewrite !labels_r_interp_row.
       rewrite !labels_l_interp_row.
       by iApply "HD".
     Qed.

     (* NOTE: used to prove TForallM *)
     Lemma erase_ctx_extend_mode η μ δ ξ D m :
       ⊢ erase_ctx η μ δ ξ D -∗ erase_ctx η (m :: μ) δ ξ D.
     Proof.
       iIntros "#HD !# % % % % % % %".
       iSpecialize ("HD" $! _ _ _ _).
       rewrite !labels_r_interp_row.
       rewrite !labels_l_interp_row.
       by iApply "HD".
     Qed.  *)

  (* ------------------------------------------------------------------ *)
  (* ATOM-LEVEL CONSEQUENCES OF [erase_ctx].                             *)
  (*                                                                     *)
  (* [erase_ctx] quantifies over *every* row [ρ0] whose signatures are    *)
  (* dominated by the disjointness data [(ss, js)] of [s].  By            *)
  (* [elem_of_row_labels_l] a row contributes exactly one label per       *)
  (* concrete name plus whatever its row variables contribute, so the     *)
  (* quantifier carries no more information than its instances at the     *)
  (* two *atom* rows: the one-signature row [RCons (SSig t ⊥ ⊥) RNil],    *)
  (* whose labels are exactly [(δ !!! t)], and the bare variable row      *)
  (* [RVar i], whose labels are exactly those of [ξ !!! i].               *)
  (*                                                                     *)
  (* Those two instances are what every *producer* of an [erase_ctx]      *)
  (* actually has to hand: merging two disjointness contexts is a         *)
  (* pointwise union of names and variables, and reading one off a        *)
  (* [NoDup] hypothesis is a head-of-list argument.  Packaging them once  *)
  (* here keeps that argument out of the callers -- without introducing a *)
  (* second definition of the predicate itself. *)
  Lemma erase_ctx_atoms δ ξ D s (ss : gmultiset eff_name) (js : gset nat) :
    D !! s = Some (ss, js) →
    erase_ctx δ ξ D -∗
    is_label (δ !!! s).1 DfracDiscarded ∗
    spec_labels_frag (δ !!! s).2 DfracDiscarded ∗
    ⌜ (∀ t, t ∈ ss → (δ !!! s).1 ≠ (δ !!! t).1 ∧ (δ !!! s).2 ≠ (δ !!! t).2)
    ∧ (∀ i, i ∈ js →
          (δ !!! s).1
            ∉ labels_l (iLblSig_to_iLblThy (sem_row_car (ξ !!! (i:nat))))
        ∧ (δ !!! s).2
            ∉ labels_r (iLblSig_to_iLblThy (sem_row_car (ξ !!! (i:nat)))) ) ⌝.
  Proof.
    iIntros (Hlk) "#HD".
    (* one concrete name at a time, via the one-signature row *)
    iAssert (⌜∀ t, t ∈ ss →
               (δ !!! s).1 ≠ (δ !!! t).1 ∧ (δ !!! s).2 ≠ (δ !!! t).2⌝)%I as %Hnm.
    { iIntros (t Ht).
      assert (Hc : le.conc_sigs (RCons (SSig t TBot TBot) RNil) ⊆ ss)
        by (cbn [le.conc_sigs le.eff_name_from_sig]; multiset_solver).
      assert (Ha : le.abst_sigs (RCons (SSig t TBot TBot) RNil) ⊆ js)
        by (cbn [le.abst_sigs]; set_solver).
      iDestruct ("HD" $! s ss js (RCons (SSig t TBot TBot) RNil)
                  with "[//] [//] [//]") as "(_ & _ & %Hfl & %Hfr)".
      cbn [row_labels_l row_labels_r le.eff_name_from_sig] in Hfl, Hfr.
      iPureIntro. split; intros Heq.
      - apply Hfl. rewrite Heq. apply list_elem_of_here.
      - apply Hfr. rewrite Heq. apply list_elem_of_here. }
    (* one row variable at a time, via the bare variable row *)
    iAssert (⌜∀ i, i ∈ js →
               (δ !!! s).1
                 ∉ labels_l (iLblSig_to_iLblThy (sem_row_car (ξ !!! (i:nat))))
             ∧ (δ !!! s).2
                 ∉ labels_r (iLblSig_to_iLblThy (sem_row_car (ξ !!! (i:nat))))⌝)%I
      as %Hvr.
    { iIntros (i Hi).
      assert (Hc : le.conc_sigs (RVar i) ⊆ ss)
        by (cbn [le.conc_sigs]; multiset_solver).
      assert (Ha : le.abst_sigs (RVar i) ⊆ js)
        by (cbn [le.abst_sigs]; set_solver).
      iDestruct ("HD" $! s ss js (RVar i) with "[//] [//] [//]")
        as "(_ & _ & %Hfl & %Hfr)".
      cbn [row_labels_l row_labels_r] in Hfl, Hfr.
      iPureIntro. split; assumption. }
    (* ownership does not depend on [ρ0]; read it off at the empty row *)
    assert (Hc0 : le.conc_sigs RNil ⊆ ss)
      by (cbn [le.conc_sigs]; multiset_solver).
    assert (Ha0 : le.abst_sigs RNil ⊆ js)
      by (cbn [le.abst_sigs]; set_solver).
    iDestruct ("HD" $! s ss js RNil with "[//] [//] [//]")
      as "(#Ho1 & #Ho2 & _ & _)".
    iFrame "Ho1 Ho2". iPureIntro. split; [exact Hnm|exact Hvr].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE PHASE-1 LEMMA: discharge [erase_ctx (row_to_disj_ctx ρ)] from
     label-validity + distinctness of the interpreted row, AT EVERY [ξ].
     Ownership is [ξ]-independent; freshness depends only on [ξ].
     An occurrence of [δ !!! s] in [ρ0]'s labels is, by
     [elem_of_row_labels_l], either a concrete name of [ρ0] -- hence one of
     [conc_sigs ρ ∖ {[+ s +]}] -- or a row variable of [ρ0] -- hence one of
     [ρ]; the head of the [NoDup] hypothesis rules out both, once the
     [s]-occurrence has been peeled off with [name_labels_l_remove]. *)
  Lemma erase_ctx_row_to_disj_ctx η μ δ ξ (ρ : row) :
    (logic.valid (iLblSig_to_iLblThy (interp._row η μ δ ρ ξ))
     ∗ ⌜ logic.distinct (iLblSig_to_iLblThy (interp._row η μ δ ρ ξ)) ⌝)
    -∗ erase_ctx δ ξ (le.row_to_disj_ctx ρ).
  Proof.
    iIntros "#Hvd". rewrite /erase_ctx.
    iIntros "!#" (s ss js ρ0 Hlk Hc Ha).
    apply lookup_row_to_disj_ctx in Hlk as (Hs & -> & ->).
    iDestruct "Hvd" as "[[Hvl Hvr] %Hdist]".
    destruct Hdist as [Hndl Hndr].
    rewrite /distinct_l (labels_l_interp_row ρ η μ δ ξ) in Hndl.
    rewrite /distinct_r (labels_r_interp_row ρ η μ δ ξ) in Hndr.
    (* Peel the [s]-occurrence off the front of each label list. *)
    rewrite row_labels_l_split (name_labels_l_remove _ δ s Hs) in Hndl.
    rewrite row_labels_r_split (name_labels_r_remove _ δ s Hs) in Hndr.
    cbn [app] in Hndl, Hndr.
    apply NoDup_cons in Hndl as [Hnl _].
    apply NoDup_cons in Hndr as [Hnr _].
    (* OWNERSHIP from valid (a big-sep over the label list) *)
    iSplitL "Hvl"; [|iSplitL "Hvr"].
    - rewrite /logic.valid_l (labels_l_interp_row ρ _ _ _ ξ).
      iApply (big_sepL_elem_of with "Hvl").
      rewrite elem_of_row_labels_l. left. exists s. split; [exact Hs|reflexivity].
    - rewrite /logic.valid_r (labels_r_interp_row ρ _ _ _ ξ).
      iApply (big_sepL_elem_of with "Hvr").
      rewrite elem_of_row_labels_r. left. exists s. split; [exact Hs|reflexivity].
    - iPureIntro. split.
      + intros [(t & Ht & Heq)|(i & Hi & Hl)]%elem_of_row_labels_l.
        * assert (Hts : t ∈ le.conc_sigs ρ ∖ {[+ s +]})
            by (eapply gmultiset_elem_of_subseteq; eauto).
          apply Hnl. rewrite elem_of_app. left.
          rewrite elem_of_name_labels_l. exists t. split; [exact Hts|exact Heq].
        * assert (Hij : i ∈ le.abst_sigs ρ) by (eapply elem_of_weaken; eauto).
          apply Hnl. rewrite elem_of_app. right.
          rewrite elem_of_var_labels_l. exists i. split; [exact Hij|exact Hl].
      + intros [(t & Ht & Heq)|(i & Hi & Hl)]%elem_of_row_labels_r.
        * assert (Hts : t ∈ le.conc_sigs ρ ∖ {[+ s +]})
            by (eapply gmultiset_elem_of_subseteq; eauto).
          apply Hnr. rewrite elem_of_app. left.
          rewrite elem_of_name_labels_r. exists t. split; [exact Hts|exact Heq].
        * assert (Hij : i ∈ le.abst_sigs ρ) by (eapply elem_of_weaken; eauto).
          apply Hnr. rewrite elem_of_app. right.
          rewrite elem_of_var_labels_r. exists i. split; [exact Hij|exact Hl].
  Qed.

  Lemma extend_erase_ctx ρ' D η μ δ ξ :
    erase_ctx δ ξ D -∗ distinct' (iLblSig_to_iLblThy (interp._row η μ δ ρ' ξ)) -∗
    logic.valid (iLblSig_to_iLblThy (interp._row η μ δ ρ' ξ)) -∗
    erase_ctx δ ξ (le.update_disj_ctx ρ' D).
  Proof.
    iIntros "#HD #Hd #Hv".
    iDestruct (erase_ctx_row_to_disj_ctx η μ δ ξ ρ' with "[$Hv $Hd]")
      as "#Hrow".
    rewrite /erase_ctx /le.update_disj_ctx /le.merge_ctx.
    iIntros "!#" (s ss js ρ0 Hlk Hc Ha).
    apply lookup_union_with_Some in Hlk as [(Hlk1&Hlk2) | [(Hlk1&Hlk2) | Hb]].
    (* [row_to_disj_ctx ρ'] only: discharge directly from [Hrow]. *)
    1: by iApply ("Hrow" $! s ss js ρ0 with "[//] [//] [//]").
    (* [D] only: discharge directly from [HD]. *)
    1: by iApply ("HD" $! s ss js ρ0 with "[//] [//] [//]").
    (* Both: [ss = ss1 ∪ ss2] and [js = js1 ∪ js2]. *)
    destruct Hb as ([ss1 js1] & [ss2 js2] & Hlk1 & Hlk2 & Heq).
    simpl in Heq. injection Heq as <- <-.
    iDestruct (erase_ctx_atoms δ ξ _ s ss1 js1 Hlk1 with "Hrow")
      as "(#Ho1 & #Ho2 & %Hat1)".
    iDestruct (erase_ctx_atoms δ ξ _ s ss2 js2 Hlk2 with "HD")
      as "(_ & _ & %Hat2)".
    destruct Hat1 as [Hn1 Hv1]. destruct Hat2 as [Hn2 Hv2].
    iFrame "Ho1 Ho2". iPureIntro. split.
    - intros [(t & Ht & Heq)|(i & Hi & Hl)]%elem_of_row_labels_l.
      + assert (Htu : t ∈ ss1 ∪ ss2)
          by (eapply gmultiset_elem_of_subseteq; eauto).
        apply gmultiset_elem_of_union in Htu as [Ht1|Ht2].
        * destruct (Hn1 t Ht1) as [Hne _]. by apply Hne.
        * destruct (Hn2 t Ht2) as [Hne _]. by apply Hne.
      + assert (Hiu : i ∈ js1 ∪ js2) by (eapply elem_of_weaken; eauto).
        apply elem_of_union in Hiu as [Hi1|Hi2].
        * destruct (Hv1 i Hi1) as [Hnl _]. by apply Hnl.
        * destruct (Hv2 i Hi2) as [Hnl _]. by apply Hnl.
    - intros [(t & Ht & Heq)|(i & Hi & Hl)]%elem_of_row_labels_r.
      + assert (Htu : t ∈ ss1 ∪ ss2)
          by (eapply gmultiset_elem_of_subseteq; eauto).
        apply gmultiset_elem_of_union in Htu as [Ht1|Ht2].
        * destruct (Hn1 t Ht1) as [_ Hne]. by apply Hne.
        * destruct (Hn2 t Ht2) as [_ Hne]. by apply Hne.
      + assert (Hiu : i ∈ js1 ∪ js2) by (eapply elem_of_weaken; eauto).
        apply elem_of_union in Hiu as [Hi1|Hi2].
        * destruct (Hv1 i Hi1) as [_ Hnr]. by apply Hnr.
        * destruct (Hv2 i Hi2) as [_ Hnr]. by apply Hnr.
  Qed.


End erase_ctx.

Section semantic_subtyping.
 Context `{!probblazeRGS Σ}.

 Definition sem_mode_le (m m' : vmode) : iProp Σ :=
    □ (∀ μ, (interp._mode μ m) ≤ₘ (interp._mode μ m')).

 Definition label_mono_row (b : bool) ρ ρ' δ ξ := if b then True else @row_labels_l Σ ρ ξ δ ⊆+ row_labels_l ρ' ξ δ ∧ row_labels_r ρ ξ δ ⊆+ row_labels_r ρ' ξ δ.
 Definition sem_sig_le D σ σ' : iProp Σ :=
   □ (∀ η μ δ ξ, erase_ctx δ ξ D -∗
                 interp._eff_sig η μ δ σ ξ ≤ₛ interp._eff_sig η μ δ σ' ξ).
 Definition sem_row_le D (b : bool) ρ ρ' : iProp Σ :=
   □ (∀ η μ δ ξ, erase_ctx δ ξ D -∗
                 ⌜ label_mono_row b ρ ρ' δ ξ ⌝ ∗ 
                 (interp._row η μ δ ρ ξ ≤ᵣ interp._row η μ δ ρ' ξ)).
 Definition sem_ty_le D α β : iProp Σ :=
   □ (∀ η μ δ ξ, erase_ctx δ ξ D -∗
                 interp._ty η μ δ α ξ ≤ₜ interp._ty η μ δ β ξ).
 Definition sem_env_le D Γ Γ' : iProp Σ :=
   □ (∀ η μ δ ξ, erase_ctx δ ξ D -∗
                 interp._env η μ δ ξ Γ ≤ₑ interp._env η μ δ ξ Γ').
End semantic_subtyping.
