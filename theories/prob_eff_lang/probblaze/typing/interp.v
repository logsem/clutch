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

End interp_subst.

(* ======================================================================= *)
(** ** The three single-substitution lemmas (T1/T2/T3) — STATUS            *)
(*                                                                          *)
(*  They are deliberately NOT stated as [Admitted] lemmas, because as       *)
(*  literally requested (for an ARBITRARY substitutend) each is FALSE       *)
(*  against the current [types.v] substitution operations — admitting them  *)
(*  would inject unsound facts into the development.  Each fails in a        *)
(*  binder case where the syntactic substitution does NOT shift the         *)
(*  substitutend's variables of the *other* sorts, while [interp] DOES      *)
(*  extend the corresponding environment.  Concrete counterexamples:        *)
(*                                                                          *)
(*  (T1) interp._ty η μ δ (τ.[τ'/]) ξ                                       *)
(*         ≡ interp._ty (interp._ty η μ δ τ' ξ :: η) μ δ τ ξ                *)
(*       FALSE.  Take τ := TForallM (TVar 0), τ' := TBang (MVar 0) TUnit.   *)
(*       [subst_type] at TForallM/TForallR keeps σ unshifted               *)
(*       ([TForallM α => TForallM α.[σ]]), so                              *)
(*         LHS = ∀ₘ m', ![ m' ] 𝟙   (bound mode m')                         *)
(*         RHS = ∀ₘ m', ![ μ!!!0 ] 𝟙 (fixed μ!!!0).                         *)
(*       Closing TForallM needs τ' mode-closed; TForallR needs τ'           *)
(*       row-closed.                                                        *)
(*                                                                          *)
(*  (T2) interp._ty η μ δ (τ.|[ρ'/]) ξ                                      *)
(*         ≡ interp._ty η μ δ τ (interp._row η μ δ ρ' ξ :: ξ)               *)
(*       FALSE for mode-open ρ': [hsubst_row_type] at TForallM keeps σ      *)
(*       unshifted ([TForallM α => TForallM α.|[σ]]) while interp extends   *)
(*       μ.  (The TForallR case is fine — [up σ] is used there.)            *)
(*                                                                          *)
(*  (T3) interp._ty η μ δ (τ.|[m/]) ξ                                       *)
(*         ≡ interp._ty η (interp._mode μ m :: μ) δ τ ξ                     *)
(*       FALSE.  [hsubst_vmode_type] does NOT recurse into the BODY of      *)
(*       TBang: [TBang m τ => TBang m.[σ] τ] leaves [τ] unsubstituted.      *)
(*       Take τ := TBang OS (TBang (MVar 0) TUnit):                         *)
(*         LHS = ![OS] (![ μ!!!0 ] 𝟙)                                       *)
(*         RHS = ![OS] (![ interp._mode μ m ] 𝟙),                           *)
(*       which differ whenever interp._mode μ m ≠ μ!!!0 (e.g. m = MVar 1).  *)
(*       (The TForallM case itself IS fine, via [up_mode_env] above.)       *)
(*                                                                          *)
(*  PROVED & reusable above: the type-dimension renaming lemma [ty_ren]     *)
(*  (unconditional) and the OFE-congruence [Proper] instances / env-shift   *)
(*  helpers.  To obtain T1/T2/T3 one must either add a closedness           *)
(*  side-condition on the substitutend, or fix the [types.v] substitution   *)
(*  operations (in particular the TBang-body omission in                    *)
(*  [hsubst_vmode_type], and the missing other-sort shifts at               *)
(*  TForallM/TForallR in [subst_type]/[hsubst_row_type]).                   *)
(* ======================================================================= *)
