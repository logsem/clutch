From clutch.prob_eff_lang.probblaze Require Import logic sem_sig sem_row sem_types sem_def syntax types sem_judgement.
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
  Proof. apply map_lookup_total. Defined.

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
  
End interp.

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
       (ξ : list (sem_row Σ))
       (vs : stringmap (val * val)),
        ⌜ dom Δ ⊆ dom δ ⌝ -∗
       let Γ1'  :=  (λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> Γ1 in
       let Γ2' :=  (λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> Γ2 in
       let ρ' := (interp._row η μ δ ρ ξ) in
       let τ' := interp._ty η μ δ τ ξ in
       sem_typed Γ1' e e' ρ' τ' Γ2').

        (* ⟦ (λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> Γ1 ⟧* vs -∗
              BREL (subst_map (fst <$> vs) e)
               ≤ (subst_map (snd <$> vs) e') @ E <| iLblSig_to_iLblThy (interp._row η μ δ ρ ξ) |> {{λ v1 v2, interp._ty η μ δ τ ξ v1 v2 
                                                                                                             ∗ ⟦ (λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> Γ2 ⟧* vs}})%I. *)
  
  Definition bin_log_val_related (v v' : val) (τ : type) : iProp Σ :=
    ∀ (η : list (sem_ty Σ))
      (μ : list mode)
      (δ : gmap eff_name (label * label))
      (ξ : list (sem_row Σ)), sem_val_typed v v' (interp._ty η μ δ τ ξ).

  Definition bin_log_pure_related (Γ : list (string * type)) (e e' : expr) (τ : type) : iProp Σ :=
    ∀ (η : list (sem_ty Σ))
      (μ : list mode)
      (δ : gmap eff_name (label * label))
      (ξ : list (sem_row Σ)), 
      let Γ'  :=  (λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> Γ in
      let τ' := (interp._ty η μ δ τ ξ) in
      sem_oval_typed Γ' e e' τ'.


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

Notation "Γ ⊨ₚ e '≤log≤' e' : τ" :=
  (bin_log_pure_related e%E e'%E (τ)%ty)
    (at level 100,  e, e' at next level,
       τ at level 200,
         format "'[hv' Γ ⊨ₚ  '/  ' e  '/' '≤log≤'  '/  ' e'  : τ ']'").


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
      intros η η' μ δ ξ f Hf; simpl.
    - done.
    - done.
    - done.
    - done.
    - done.
    - done.
    - by f_equiv; apply IHτ.
    - done.
    - f_equiv; [apply IHτ1|apply IHτ2]; done.
    - f_equiv; [apply IHτ1|apply IHτ2]; done.
    - f_equiv; [apply IHτ2|apply IHτ1|apply IHτ3]; done.
    - f_equiv; intros m; by apply IHτ.
    - f_equiv; intros τ'; apply IHτ; by apply up_ren_env.
    - f_equiv; intros ρ; by apply IHτ.
    - f_equiv; intros τ'; apply IHτ; by apply up_ren_env.
    - f_equiv; intros τ'; apply IHτ; by apply up_ren_env.
    - apply Hf.
    - by f_equiv; apply IHτ.
    - done.
    - f_equiv; [apply IHτ|apply IHτ0]; done.
    - done.
    - f_equiv; by apply IHτ.
    - f_equiv; [apply IHτ|apply IHτ0]; done.
    - f_equiv; intros τ'; [apply IHτ|apply IHτ0]; by apply up_ren_env.
    - f_equiv; by apply IHτ.
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
      intros η μ μ' δ ξ σ Hσ; simpl.
    - done.
    - done.
    - done.
    - done.
    - done.
    - done.
    - by f_equiv; apply IHτ.
    - done.
    - f_equiv; [apply IHτ1|apply IHτ2]; done.
    - f_equiv; [apply IHτ1|apply IHτ2]; done.
    - f_equiv; [apply IHτ2|apply IHτ1|apply IHτ3]; done.
    - f_equiv; intros m; apply IHτ; by apply up_mode_env.
    - f_equiv; intros τ'; by apply IHτ.
    - f_equiv; intros ρ; by apply IHτ.
    - f_equiv; intros τ'; by apply IHτ.
    - f_equiv; intros τ'; by apply IHτ.
    - done.
    - erewrite <-mode_subst_pt by done. by f_equiv; apply IHτ.
    - done.
    - f_equiv; [apply IHτ|apply IHτ0]; done.
    - done.
    - erewrite <-mode_subst_pt by done. by f_equiv; apply IHτ.
    - f_equiv; [apply IHτ|apply IHτ0]; done.
    - f_equiv; intros τ'; [apply IHτ|apply IHτ0]; done.
    - erewrite <-mode_subst_pt by done. by f_equiv; apply IHτ.
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
      intros η μ δ ξ ξ' f Hf; simpl.
    - done.
    - done.
    - done.
    - done.
    - done.
    - done.
    - by f_equiv; apply IHτ.
    - done.
    - f_equiv; [apply IHτ1|apply IHτ2]; done.
    - f_equiv; [apply IHτ1|apply IHτ2]; done.
    - f_equiv; [apply IHτ2|apply IHτ1|apply IHτ3]; done.
    - f_equiv; intros m; by apply IHτ.
    - f_equiv; intros τ'; by apply IHτ.
    - f_equiv; intros ρ; apply IHτ; by apply up_ren_row_env.
    - f_equiv; intros τ'; by apply IHτ.
    - f_equiv; intros τ'; by apply IHτ.
    - done.
    - by f_equiv; apply IHτ.
    - done.
    - f_equiv; [apply IHτ|apply IHτ0]; done.
    - apply Hf.
    - f_equiv; by apply IHτ.
    - f_equiv; [apply IHτ|apply IHτ0]; done.
    - f_equiv; intros τ'; [apply IHτ|apply IHτ0]; done.
    - f_equiv; by apply IHτ.
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
      intros η η' μ δ ξ n Hf; simpl.
    - done.
    - done.
    - done.
    - done.
    - done.
    - done.
    - by f_equiv; apply IHτ.
    - done.
    - f_equiv; [apply IHτ1|apply IHτ2]; done.
    - f_equiv; [apply IHτ1|apply IHτ2]; done.
    - f_equiv; [apply IHτ2|apply IHτ1|apply IHτ3]; done.
    - by f_equiv; intros m; apply IHτ.
    - f_equiv; intros τ'; apply IHτ; (intros [|i]; [done|apply Hf]).
    - by f_equiv; intros ρ; apply IHτ.
    - f_equiv; intros τ'; apply IHτ; (intros [|i]; [done|apply Hf]).
    - f_equiv; intros τ'; apply IHτ; (intros [|i]; [done|apply Hf]).
    - apply Hf.
    - by f_equiv; apply IHτ.
    - done.
    - f_equiv; [apply IHτ|apply IHτ0]; done.
    - done.
    - f_equiv; by apply IHτ.
    - f_equiv; [apply IHτ|apply IHτ0]; done.
    - f_equiv; intros τ';
        [apply IHτ|apply IHτ0]; (intros [|i]; [done|apply Hf]).
    - f_equiv; by apply IHτ.
  Qed.

  Global Instance interp_ty_head_ne (η : list (sem_ty Σ)) (μ : list mode)
    (δ : gmap eff_name (label*label)) (τ : type) (ξ : list (sem_row Σ)) :
    NonExpansive (λ α, interp._ty (α :: η) μ δ τ ξ).
  Proof.
    intros n x y Hxy. apply ty_ne_env. intros [|i]; [done|done].
  Qed.

End interp_subst.
