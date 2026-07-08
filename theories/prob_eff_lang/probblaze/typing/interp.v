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

(* Freshness ([s ∉ dom Δ]) makes [s] absent from the resolution map, so
   deleting it is a no-op (used to discharge the [Effect] binder). *)
Lemma resolve_map_delete_fresh proj Δ δ s :
  s ∉ dom Δ → delete s (resolve_map proj Δ δ) = resolve_map proj Δ δ.
Proof.
  intros Hs. apply delete_id. rewrite resolve_map_lookup.
  by rewrite (not_elem_of_dom_1 _ _ Hs).
Qed.

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
      intros η μ ξ Hs; simpl in *.
    (* type ctors: TBot TTop TUnit TBool TInt TNat *)
    - done. - done. - done. - done. - done. - done.
    - by f_equiv; apply IHτ.                              (* TRef *)
    - done.                                               (* TTape *)
    - f_equiv; [apply IHτ1|apply IHτ2]; set_solver.       (* TProd *)
    - f_equiv; [apply IHτ1|apply IHτ2]; set_solver.       (* TSum *)
    - f_equiv; [apply IHτ2|apply IHτ1|apply IHτ3]; set_solver. (* TArrow *)
    - f_equiv; intros m; by apply IHτ.                    (* TForallM *)
    - f_equiv; intros τ'; by apply IHτ.                   (* TForallT *)
    - f_equiv; intros ρ; by apply IHτ.                    (* TForallR *)
    - f_equiv; intros τ'; by apply IHτ.                   (* TExists *)
    - f_equiv; intros τ'; by apply IHτ.                   (* TRec *)
    - done.                                               (* TVar *)
    - by f_equiv; apply IHτ.                              (* TBang *)
    (* row ctors: RNil RCons RVar RFlip RUnion *)
    - done.
    - f_equiv; [apply IHτ|apply IHτ0]; (unfold vars._row, vars._row_pre, vars._eff_sig in *; set_solver).
    - done.
    - f_equiv; apply IHτ; (unfold vars._row, vars._row_pre, vars._eff_sig in *; set_solver).
    - f_equiv; [apply IHτ|apply IHτ0]; (unfold vars._row, vars._row_pre, vars._eff_sig in *; set_solver).
    (* eff_sig ctors: SSig SFlip *)
    - rewrite lookup_total_insert_ne; [|(unfold vars._row, vars._row_pre, vars._eff_sig in *; set_solver)].
      f_equiv; intros tau; [apply IHτ|apply IHτ0]; (unfold vars._row, vars._row_pre, vars._eff_sig in *; set_solver).
    - f_equiv; apply IHτ; (unfold vars._row, vars._row_pre, vars._eff_sig in *; set_solver).
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

  (* ===================================================================== *)
  (** ** Soundness of the syntactic [le.MultiT] predicate                  *)
  (*                                                                        *)
  (*  [le.MultiT τ = ∅ ⊢ₗ τ ≤T ![MS] τ].  We show that whenever a syntactic *)
  (*  type is [le.MultiT], its interpretation is a semantic [MultiT].       *)
  (*  The proof factors through a STRUCTURAL "copyable shape" predicate     *)
  (*  [MultiP], for which the semantic direction [MultiP τ → MultiT(interp)] *)
  (*  is a full structural proof using the [sem_types.v] instances.         *)

  (* Auxiliary semantic instances. *)
  Lemma multi_ty_nat_sem : MultiT (@sem_ty_nat Σ).
  Proof.
    constructor. iIntros "!# %v1 %v2 (%n & -> & ->)".
    iApply bi.intuitionistically_intuitionistically_if.
    iIntros "!#". by iExists n.
  Qed.

  (* [![m] τ] is copyable as soon as [τ] is, for ANY (semantic) mode [m]. *)
  Lemma multi_ty_mbang_gen (sm : mode) (τ : sem_ty Σ) `{! MultiT τ} :
    MultiT (sem_ty_mbang sm τ).
  Proof.
    constructor. iIntros "!# %v1 %v2 H".
    iAssert (□ (sem_ty_mbang sm τ v1 v2))%I with "[H]" as "#H'".
    { rewrite /sem_ty_mbang. destruct sm; simpl.
      - pose proof (multi_ty_persistent τ v1 v2) as Hpers.
        iDestruct "H" as "#H". by iModIntro.
      - iDestruct "H" as "#H". by iModIntro. }
    iApply bi.intuitionistically_intuitionistically_if. iModIntro.
    by iApply "H'".
  Qed.




  (* The vmode preorder [le._mode] is a lattice with [OS] bottom and
     [MS] top; in particular [MS ≤M OS] is NOT derivable. *)
  Lemma le_mode_char m1 m2 :
    le._mode m1 m2 → m1 = OS ∨ m2 = MS ∨ m1 = m2.
  Proof.
    intros Hm. induction Hm.
    - by left.
    - by right; left.
    - destruct IHHm1 as [E1|[E1|E1]]; destruct IHHm2 as [E2|[E2|E2]];
        subst; first [ by left | by right; left | by right; right
                     | discriminate ].
    - by right; right.
  Qed.

 

  
  

  (* ===================================================================== *)
  (** ** Soundness of syntactic subtyping ([le._eff_sig]/[le._row]/        *)
  (*      [le._type])                                                       *)
  (*                                                                        *)
  (*  We show that the three mutually-defined syntactic subtyping           *)
  (*  judgements imply the corresponding semantic ones on interpretations.  *)
  (*  Proved by simultaneous induction with the combined scheme             *)
  (*  [le_type_mut].                                                        *)
  (*                                                                        *)
  (*  The ONLY rule that is not premise-free is [RErase_le], which erases a *)
  (*  freshly-allocated bottom signature [SAbs s] from the head of a row.   *)
  (*  Its semantic counterpart [sem_row.row_le_erase] requires both         *)
  (*  LABEL-OWNERSHIP ([is_label]/[spec_labels_frag] for the dynamic label  *)
  (*  [δ !!! s]) and FRESHNESS ([δ !!! s] not among the labels of the       *)
  (*  inner row).  Neither is available from the bare [≤ᵣ]; both come from  *)
  (*  the disjointness context [D] (which records that [s] is concrete in   *)
  (*  the ambient row and disjoint from the inner row).  We thread this via *)
  (*  a persistent [erase_ctx] hypothesis bundle, defined below, which is   *)
  (*  exactly what the erase rule consumes.                                 *)

  (* Soundness of the syntactic mode order [le._mode]: it interprets to the
     semantic mode order [≤ₘ] under any mode-env [μ].  (Used by the
     [SFlipComp_le]/[RFlipComp_le]/[TBangComp_le] cases.) *)
  Lemma mode_le_sound (m m' : vmode) (μ : list mode) :
    (⊢ₗ m ≤M m') → ⊢ (interp._mode μ m) ≤ₘ@{Σ} (interp._mode μ m').
  Proof.
    intros Hm. induction Hm; simpl.
    - iApply mode_le_OS.
    - iApply mode_le_MS.
    - iApply (mode_le_trans with "[] []"); [iApply IHHm1|iApply IHHm2].
    - iApply mode_le_refl.
  Qed.

  (* (* The effect-name interpretation [δ] is fixed throughout (no subtyping
        constructor binds an effect name), but the TYPE/ROW/MODE environments
        [η]/[ξ]/[μ] are EXTENDED by the binders ([SSig]/[TForall*]), so the
        three soundness predicates must quantify over them. *)
     Variable (δ : gmap eff_name (label*label)). *)

  (* The ownership + disjointness facts a derivation [_row D b ρ ρ'] may
     need: for every concrete label [s] recorded in [D] together with an
     inner row [ρ0] whose concrete/abstract signatures are dominated by the
     disjointness data of [s], the dynamic label [δ !!! s] is owned and is
     fresh for [ρ0].  This is precisely the premise bundle of
     [sem_row.row_le_erase] applied at [(δ!!!s).1]/[(δ!!!s).2]/[ρ0],
     uniformly over all interpretation environments [η μ ξ]. *)
  Definition erase_ctx η μ δ ξ (D : le.disj_ctx) : iProp Σ :=
    □ (∀ (s : eff_name) (ss : gmultiset eff_name) (js : gset nat)
         (ρ0 : row),
         ⌜ D !! s = Some (ss, js) ⌝ -∗
         ⌜ le.conc_sigs ρ0 ⊆ ss ⌝ -∗
         ⌜ le.abst_sigs ρ0 ⊆ js ⌝ -∗
         is_label (δ !!! s).1 DfracDiscarded ∗
         spec_labels_frag (δ !!! s).2 DfracDiscarded ∗
         ⌜ (δ !!! s).1
             ∉ labels_l (iLblSig_to_iLblThy (interp._row η μ δ ρ0 ξ)) ⌝ ∗
         ⌜ (δ !!! s).2
             ∉ labels_r (iLblSig_to_iLblThy (interp._row η μ δ ρ0 ξ)) ⌝)%I.

  Global Instance erase_ctx_persistent D η μ δ ξ : Persistent (erase_ctx η μ δ ξ D).
  Proof. apply _. Qed.

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
  (* LABEL MONOTONICITY of [≤R] along a [@false] derivation.

     A [@false] subtyping derivation never uses [RErase_le] (that
     constructor is [@true]-only), so it cannot DROP any concrete label;
     every other constructor either preserves, permutes, or EXTENDS the
     concrete-label list.  Hence the [row_labels_*] lists are related by
     [⊆+] (sub-multiset).  This supplies the two side-conditions of
     [sem_row.row_le_cons_comp] (the [RCons_le] case) and the
     cross-disjointness preservation needed by the union case.

     First: subtyping of signatures preserves the effect NAME, so the
     head label [(δ !!! eff_name_from_sig _).k] matches on both sides. *)
  Lemma sig_le_eff_name (D : le.disj_ctx) (σ σ' : eff_sig) :
    D ⊢ₗ σ ≤S σ' → le.eff_name_from_sig σ = le.eff_name_from_sig σ'.
  Proof.
    induction 1; simpl; congruence.
  Qed.

  (* The generalised statement (left labels), carrying [b = false] as a
     hypothesis so the [@true]-only [RErase_le] case is vacuous.  All
     other cases follow by [⊆+] reasoning on the concrete label lists. *)
  Lemma row_le_false_row_labels_l (D : le.disj_ctx) b (ρ ρ' : row) ξ δ :
    D ⊢ₗ ρ ≤R ρ' @ b → b = false →
    row_labels_l ρ ξ δ ⊆+ row_labels_l ρ' ξ δ.
  Proof.
    induction 1 as
      [D b|D b i|D b ρ σ|D b σ σ' ρ|D b σ σ' ρ ρ' Hσ Hρ IH
      |D b ρ1 ρ2 ρ1' ρ2' _ IH1 _ IH2|D s ρ ss js Hlk Hc Ha
      |D b ρ1 ρ2 ρ3 _ IH1 _ IH2|D b m|D b m σ ρ|D b m ρ1 ρ2
      |D b ρ|D b m ρ|D b m ρ|D b m ρ|D b m' m ρ' ρ Hm _ IH] in |- *;
      intros Hbf; simpl; try done.
    - (* RExtend_le: [ρ ⊆+ head :: ρ] *)
      apply submseteq_cons; reflexivity.
    - (* RSwap_le *)
      apply submseteq_swap.
    - (* RCons_le: heads equal via [sig_le_eff_name]; tails by IH *)
      rewrite (sig_le_eff_name D σ σ' Hσ).
      apply submseteq_skip, IH; reflexivity.
    - (* RUnion_le *)
      apply submseteq_app; [by apply IH1|by apply IH2].
    - (* RTrans_le *)
      etrans; [by apply IH1|by apply IH2].
    - (* RFlipComp_le: [RFlip] is transparent for labels; tail by IH.
         (The [@true]-only [RErase_le] and the [RFlipUnion_le] cases
         are closed by [try done] above: [discriminate] resp. equal
         label lists.) *)
      by apply IH.
  Qed.

  Lemma row_le_false_row_labels_r (D : le.disj_ctx) b (ρ ρ' : row) ξ δ :
    D ⊢ₗ ρ ≤R ρ' @ b → b = false →
    row_labels_r ρ ξ δ ⊆+ row_labels_r ρ' ξ δ.
  Proof.
    induction 1 as
      [D b|D b i|D b ρ σ|D b σ σ' ρ|D b σ σ' ρ ρ' Hσ Hρ IH
      |D b ρ1 ρ2 ρ1' ρ2' _ IH1 _ IH2|D s ρ ss js Hlk Hc Ha
      |D b ρ1 ρ2 ρ3 _ IH1 _ IH2|D b m|D b m σ ρ|D b m ρ1 ρ2
      |D b ρ|D b m ρ|D b m ρ|D b m ρ|D b m' m ρ' ρ Hm _ IH] in |- *;
      intros Hbf; simpl; try done.
    - apply submseteq_cons; reflexivity.
    - apply submseteq_swap.
    - rewrite (sig_le_eff_name D σ σ' Hσ).
      apply submseteq_skip, IH; reflexivity.
    - apply submseteq_app; [by apply IH1|by apply IH2].
    - etrans; [by apply IH1|by apply IH2].
    - by apply IH.
  Qed.

  (* The interp-level corollaries: the LEFT/RIGHT label LISTS of the
     interpreted rows are sub-multisets along a [@false] derivation. *)
  Lemma row_le_false_labels_l (D : le.disj_ctx) (ρ ρ' : row) η μ δ ξ :
    D ⊢ₗ ρ ≤R ρ' @ false →
    labels_l (iLblSig_to_iLblThy (interp._row η μ δ ρ ξ))
      ⊆+ labels_l (iLblSig_to_iLblThy (interp._row η μ δ ρ' ξ)).
  Proof.
    intros Hle. rewrite !labels_l_interp_row.
    by eapply row_le_false_row_labels_l.
  Qed.

  Lemma row_le_false_labels_r (D : le.disj_ctx) (ρ ρ' : row) η μ δ ξ :
    D ⊢ₗ ρ ≤R ρ' @ false →
    labels_r (iLblSig_to_iLblThy (interp._row η μ δ ρ ξ))
      ⊆+ labels_r (iLblSig_to_iLblThy (interp._row η μ δ ρ' ξ)).
  Proof.
    intros Hle. rewrite !labels_r_interp_row.
    by eapply row_le_false_row_labels_r.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* MEMBERSHIP: a concrete name [s] of [ρ] contributes [(δ!!!s).1]. *)

  Lemma elem_of_row_labels_l_conc (ρ : row) ξ δ s :
    s ∈ le.conc_sigs ρ → (δ !!! s).1 ∈ row_labels_l ρ ξ δ.
  Proof.
    induction ρ as [|e ρ' IH|i|m ρ' IH|ρ1 IH1 ρ2 IH2]; simpl;
      rewrite ?gmultiset_elem_of_empty ?gmultiset_elem_of_disj_union
              ?gmultiset_elem_of_singleton.
    - by intros [].
    - intros [-> | Hin]; [by left | right; by apply IH].
    - by intros [].
    - apply IH.
    - rewrite elem_of_app. intros [?|?]; [left; by apply IH1|right; by apply IH2].
  Qed.

  Lemma elem_of_row_labels_r_conc (ρ : row) ξ δ s :
    s ∈ le.conc_sigs ρ → (δ !!! s).2 ∈ row_labels_r ρ ξ δ.
  Proof.
    induction ρ as [|e ρ' IH|i|m ρ' IH|ρ1 IH1 ρ2 IH2]; simpl;
      rewrite ?gmultiset_elem_of_empty ?gmultiset_elem_of_disj_union
              ?gmultiset_elem_of_singleton.
    - by intros [].
    - intros [-> | Hin]; [by left | right; by apply IH].
    - by intros [].
    - apply IH.
    - rewrite elem_of_app. intros [?|?]; [left; by apply IH1|right; by apply IH2].
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

  Lemma elem_of_name_labels_l_mono (X Y : gmultiset eff_name) l δ :
    X ⊆ Y → l ∈ name_labels_l X δ → l ∈ name_labels_l Y δ.
  Proof.
    intros Hsub. rewrite /name_labels_l !list_elem_of_fmap.
    intros (s & -> & Hs). exists s. split; [done|].
    apply gmultiset_elem_of_elements.
    apply gmultiset_elem_of_elements in Hs.
    by eapply gmultiset_elem_of_subseteq.
  Qed.

  Lemma elem_of_var_labels_l_mono (ρ0 ρ : row) ξ l :
    le.abst_sigs ρ0 ⊆ le.abst_sigs ρ →
    l ∈ var_labels_l ρ0 ξ →
    (∃ i, i ∈ le.abst_sigs ρ
       ∧ l ∈ labels_l (iLblSig_to_iLblThy (sem_row_car (ξ !!! (i:nat))))).
  Proof.
    intros Hsub Hin.
    (* extract the witness var from ρ0 via the structure of var_labels_l *)
    assert (∃ i, i ∈ le.abst_sigs ρ0
       ∧ l ∈ labels_l (iLblSig_to_iLblThy (sem_row_car (ξ !!! (i:nat)))))
      as (i & Hi & Hl).
    { clear Hsub. induction ρ0 as [|e ρ' IH|i|m ρ' IH|ρ1 IH1 ρ2 IH2]; simpl in *.
      - by apply elem_of_nil in Hin.
      - destruct (IH Hin) as (j & Hj & Hl). by exists j.
      - exists i. split; [by apply elem_of_singleton|done].
      - destruct (IH Hin) as (j & Hj & Hl). by exists j.
      - apply elem_of_app in Hin as [Hin|Hin].
        + destruct (IH1 Hin) as (j & Hj & Hl). exists j.
          split; [by apply elem_of_union; left|done].
        + destruct (IH2 Hin) as (j & Hj & Hl). exists j.
          split; [by apply elem_of_union; right|done]. }
    exists i. split; [by apply Hsub|done].
  Qed.

  (* The abstract labels of [ρ] are also among [row_labels_l ρ]. *)
  Lemma elem_of_var_in_row_labels (ρ : row) ξ i l :
    i ∈ le.abst_sigs ρ →
    l ∈ labels_l (iLblSig_to_iLblThy (sem_row_car (ξ !!! (i:nat)))) →
    l ∈ var_labels_l ρ ξ.
  Proof.
    induction ρ as [|e ρ' IH|j|m ρ' IH|ρ1 IH1 ρ2 IH2]; simpl.
    - by intros ?%elem_of_empty.
    - apply IH.
    - intros ->%elem_of_singleton. done.
    - apply IH.
    - intros [?|?]%elem_of_union ?; apply elem_of_app;
        [left; by apply IH1|right; by apply IH2].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* FRESHNESS: the crux.  Discharged from NoDup (distinct). *)
  Lemma fresh_left (ρ ρ0 : row) ξ δ s :
    NoDup (row_labels_l ρ ξ δ) →
    s ∈ le.conc_sigs ρ →
    le.conc_sigs ρ0 ⊆ le.conc_sigs ρ ∖ {[+ s +]} →
    le.abst_sigs ρ0 ⊆ le.abst_sigs ρ →
    (δ !!! s).1 ∉ row_labels_l ρ0 ξ δ.
  Proof.
    intros Hnd Hs Hc Ha Hin.
    (* permute [ρ]'s labels to expose the s-occurrence *)
    rewrite (row_labels_l_split ρ) in Hnd.
    pose proof (gmultiset_disj_union_difference' s (le.conc_sigs ρ) Hs)
      as Hdecomp.
    rewrite Hdecomp in Hnd.
    rewrite /name_labels_l gmultiset_elements_disj_union fmap_app
      gmultiset_elements_singleton /= in Hnd.
    apply NoDup_cons in Hnd as [Hnotin _].
    apply Hnotin. apply elem_of_app.
    (* classify the ρ0-membership *)
    rewrite (row_labels_l_split ρ0) in Hin.
    apply elem_of_app in Hin as [Hin|Hin].
    - (* concrete name of ρ0: lands in (conc_sigs ρ ∖ {[s]}) name labels *)
      left. by eapply (elem_of_name_labels_l_mono _ _ _ _ Hc).
    - (* abstract var of ρ0: lands in var labels of ρ *)
      right.
      destruct (elem_of_var_labels_l_mono ρ0 ρ ξ _ Ha Hin) as (i & Hi & Hl).
      by eapply elem_of_var_in_row_labels.
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

  Lemma elem_of_name_labels_r_mono (X Y : gmultiset eff_name) l δ :
    X ⊆ Y → l ∈ name_labels_r X δ → l ∈ name_labels_r Y δ.
  Proof.
    intros Hsub. rewrite /name_labels_r !list_elem_of_fmap.
    intros (s & -> & Hs). exists s. split; [done|].
    apply gmultiset_elem_of_elements.
    apply gmultiset_elem_of_elements in Hs.
    by eapply gmultiset_elem_of_subseteq.
  Qed.

  Lemma elem_of_var_labels_r_mono (ρ0 ρ : row) ξ l :
    le.abst_sigs ρ0 ⊆ le.abst_sigs ρ →
    l ∈ var_labels_r ρ0 ξ →
    (∃ i, i ∈ le.abst_sigs ρ
       ∧ l ∈ labels_r (iLblSig_to_iLblThy (sem_row_car (ξ !!! (i:nat))))).
  Proof.
    intros Hsub Hin.
    assert (∃ i, i ∈ le.abst_sigs ρ0
       ∧ l ∈ labels_r (iLblSig_to_iLblThy (sem_row_car (ξ !!! (i:nat)))))
      as (i & Hi & Hl).
    { clear Hsub. induction ρ0 as [|e ρ' IH|i|m ρ' IH|ρ1 IH1 ρ2 IH2]; simpl in *.
      - by apply elem_of_nil in Hin.
      - destruct (IH Hin) as (j & Hj & Hl). by exists j.
      - exists i. split; [by apply elem_of_singleton|done].
      - destruct (IH Hin) as (j & Hj & Hl). by exists j.
      - apply elem_of_app in Hin as [Hin|Hin].
        + destruct (IH1 Hin) as (j & Hj & Hl). exists j.
          split; [by apply elem_of_union; left|done].
        + destruct (IH2 Hin) as (j & Hj & Hl). exists j.
          split; [by apply elem_of_union; right|done]. }
    exists i. split; [by apply Hsub|done].
  Qed.

  Lemma elem_of_var_in_row_labels_r (ρ : row) ξ i l :
    i ∈ le.abst_sigs ρ →
    l ∈ labels_r (iLblSig_to_iLblThy (sem_row_car (ξ !!! (i:nat)))) →
    l ∈ var_labels_r ρ ξ.
  Proof.
    induction ρ as [|e ρ' IH|j|m ρ' IH|ρ1 IH1 ρ2 IH2]; simpl.
    - by intros ?%elem_of_empty.
    - apply IH.
    - intros ->%elem_of_singleton. done.
    - apply IH.
    - intros [?|?]%elem_of_union ?; apply elem_of_app;
        [left; by apply IH1|right; by apply IH2].
  Qed.

  Lemma fresh_right (ρ ρ0 : row) ξ δ s :
    NoDup (row_labels_r ρ ξ δ) →
    s ∈ le.conc_sigs ρ →
    le.conc_sigs ρ0 ⊆ le.conc_sigs ρ ∖ {[+ s +]} →
    le.abst_sigs ρ0 ⊆ le.abst_sigs ρ →
    (δ !!! s).2 ∉ row_labels_r ρ0 ξ δ.
  Proof.
    intros Hnd Hs Hc Ha Hin.
    rewrite (row_labels_r_split ρ) in Hnd.
    pose proof (gmultiset_disj_union_difference' s (le.conc_sigs ρ) Hs)
      as Hdecomp.
    rewrite Hdecomp in Hnd.
    rewrite /name_labels_r gmultiset_elements_disj_union fmap_app
      gmultiset_elements_singleton /= in Hnd.
    apply NoDup_cons in Hnd as [Hnotin _].
    apply Hnotin. apply elem_of_app.
    rewrite (row_labels_r_split ρ0) in Hin.
    apply elem_of_app in Hin as [Hin|Hin].
    - left. by eapply (elem_of_name_labels_r_mono _ _ _ _ Hc).
    - right.
      destruct (elem_of_var_labels_r_mono ρ0 ρ ξ _ Ha Hin) as (i & Hi & Hl).
      by eapply elem_of_var_in_row_labels_r.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Characterise lookups in [row_to_disj_ctx ρ]. *)
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

  (* ------------------------------------------------------------------ *)
  (* THE PHASE-1 LEMMA: discharge [erase_ctx (row_to_disj_ctx ρ)] from
     label-validity + distinctness of the interpreted row, AT EVERY [ξ].
     Ownership is [ξ]/[η]/[μ]-independent; freshness depends only on [ξ].
     The hypothesis quantifies over [ξ] because [erase_ctx] does. *)
  Lemma erase_ctx_row_to_disj_ctx η μ δ ξ (ρ : row) :
       (logic.valid (iLblSig_to_iLblThy (interp._row η μ δ ρ ξ))
       ∗ ⌜ logic.distinct (iLblSig_to_iLblThy (interp._row η μ δ ρ ξ)) ⌝)
    -∗ erase_ctx η μ δ ξ (le.row_to_disj_ctx ρ).
  Proof.
    iIntros "#Hvd". rewrite /erase_ctx.
    iIntros "!#" (s ss js ρ0 Hlk Hc Ha).
    apply lookup_row_to_disj_ctx in Hlk as (Hs & -> & ->).
    iDestruct "Hvd" as "[[Hvl Hvr] %Hdist]".
    destruct Hdist as [Hndl Hndr].
    rewrite /distinct_l (labels_l_interp_row ρ η μ δ ξ) in Hndl.
    rewrite /distinct_r (labels_r_interp_row ρ η μ δ ξ) in Hndr.
    (* OWNERSHIP from valid (a big-sep over the label list) *)
    iSplitL "Hvl"; [|iSplitL "Hvr"].
    - rewrite /logic.valid_l (labels_l_interp_row ρ _ _ _ ξ).
      iApply (big_sepL_elem_of with "Hvl").
      by apply elem_of_row_labels_l_conc.
    - rewrite /logic.valid_r (labels_r_interp_row ρ _ _ _ ξ).
      iApply (big_sepL_elem_of with "Hvr").
      by apply elem_of_row_labels_r_conc.
    - (* FRESHNESS, both sides, via [fresh_left]/[fresh_right] *)
      iPureIntro. split.
      + rewrite (labels_l_interp_row ρ0 η μ δ ξ).
        by eapply (fresh_left ρ ρ0 ξ δ s).
      + rewrite (labels_r_interp_row ρ0 η μ δ ξ).
        by eapply (fresh_right ρ ρ0 ξ δ s).
  Qed.

  Lemma erase_ctx_extend_ty η μ δ ξ D α :
    ⊢ erase_ctx η μ δ ξ D -∗ erase_ctx (α :: η) μ δ ξ D.
  Proof.
    iIntros "#HD !# % % % % % % %".
    iSpecialize ("HD" $! _ _ _ _).
    rewrite !labels_r_interp_row.
    rewrite !labels_l_interp_row.
    by iApply "HD".
  Qed. 

  Lemma erase_ctx_extend_mode η μ δ ξ D m :
    ⊢ erase_ctx η μ δ ξ D -∗ erase_ctx η (m :: μ) δ ξ D.
  Proof.
    iIntros "#HD !# % % % % % % %".
    iSpecialize ("HD" $! _ _ _ _).
    rewrite !labels_r_interp_row.
    rewrite !labels_l_interp_row.
    by iApply "HD".
  Qed. 

 (* Lemma erase_ctx_extend_row η μ δ ξ D θ :
       ⊢ erase_ctx η μ δ ξ D -∗ erase_ctx η μ δ (θ :: ξ) D.
     Proof.
       iIntros "#HD !# % % % % % % %".
       iSpecialize ("HD" $! _ _ _ _).
       rewrite !labels_r_interp_row.
       rewrite !labels_l_interp_row.
       iApply "HD".
     Qed . *)

  (* The three per-judgement predicates.  Each quantifies over the
     interpretation environments [η μ ξ] (extended by binders), takes the
     [erase_ctx] hypothesis bundle (only used by [RErase_le]), and yields
     the corresponding semantic subtyping. *)
  Definition sem_sig_le D σ σ' : iProp Σ :=
    □ (∀ η μ δ ξ, erase_ctx η μ δ ξ D -∗
     interp._eff_sig η μ δ σ ξ ≤ₛ interp._eff_sig η μ δ σ' ξ).
  (* Why is the boolean not used? *)
  Definition sem_row_le D (b : bool) ρ ρ' : iProp Σ :=
    □ (∀ η μ δ ξ, erase_ctx η μ δ ξ D -∗
     interp._row η μ δ ρ ξ ≤ᵣ interp._row η μ δ ρ' ξ).
  Definition sem_ty_le D α β : iProp Σ :=
    □ (∀ η μ δ ξ, erase_ctx η μ δ ξ D -∗
     interp._ty η μ δ α ξ ≤ₜ interp._ty η μ δ β ξ).

  Lemma arr_extend_D ρ' D η μ δ ξ : 
     erase_ctx η μ δ ξ D -∗ distinct' (iLblSig_to_iLblThy (interp._row η μ δ ρ' ξ)) -∗
     logic.valid (iLblSig_to_iLblThy (interp._row η μ δ ρ' ξ)) -∗
     erase_ctx η μ δ ξ (le.update_disj_ctx ρ' D).
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
    (* Both: the merged entry has [ss = ss1 ∪ ss2], [js = js1 ∪ js2].  Every
       concrete name / row variable of [ρ0] lands in one of the two summands,
       so freshness of [(δ !!! s)] against [ρ0] is reconstructed element-wise
       from the per-side facts [Hm1] ([Hrow]) and [Hm2] ([HD]). *)
    destruct Hb as ([ss1 js1] & [ss2 js2] & Hlk1 & Hlk2 & Heq).
    simpl in Heq. injection Heq as <- <-.
    iAssert (⌜∀ ρa, le.conc_sigs ρa ⊆ ss1 → le.abst_sigs ρa ⊆ js1 →
      (δ !!! s).1 ∉ row_labels_l ρa ξ δ
      ∧ (δ !!! s).2 ∉ row_labels_r ρa ξ δ⌝)%I as %Hm1.
    { iIntros (ρa Hca Haa).
      iDestruct ("Hrow" $! s ss1 js1 ρa with "[//] [//] [//]")
        as "(_ & _ & %Hfl & %Hfr)".
      rewrite (labels_l_interp_row ρa η μ δ ξ) in Hfl.
      rewrite (labels_r_interp_row ρa η μ δ ξ) in Hfr.
      iPureIntro; split; assumption. }
    iAssert (⌜∀ ρa, le.conc_sigs ρa ⊆ ss2 → le.abst_sigs ρa ⊆ js2 →
      (δ !!! s).1 ∉ row_labels_l ρa ξ δ
      ∧ (δ !!! s).2 ∉ row_labels_r ρa ξ δ⌝)%I as %Hm2.
    { iIntros (ρa Hca Haa).
      iDestruct ("HD" $! s ss2 js2 ρa with "[//] [//] [//]")
        as "(_ & _ & %Hfl & %Hfr)".
      rewrite (labels_l_interp_row ρa η μ δ ξ) in Hfl.
      rewrite (labels_r_interp_row ρa η μ δ ξ) in Hfr.
      iPureIntro; split; assumption. }
    (* Ownership does not depend on [ρ0]; read it off [D] at the empty row. *)
    assert (Hc0 : le.conc_sigs RNil ⊆ ss2)
      by (cbn [le.conc_sigs]; multiset_solver).
    assert (Ha0 : le.abst_sigs RNil ⊆ js2)
      by (cbn [le.abst_sigs]; set_solver).
    iDestruct ("HD" $! s ss2 js2 RNil with "[//] [//] [//]")
      as "(#Hown1 & #Hown2 & _)".
    iSplit; [iApply "Hown1"|].
    iSplit; [iApply "Hown2"|].
    iSplit.
    - iPureIntro.
      rewrite (labels_l_interp_row ρ0 η μ δ ξ).
      intros Hin. rewrite row_labels_l_split elem_of_app in Hin.
      destruct Hin as [Hn | Hvr].
      + rewrite /name_labels_l list_elem_of_fmap in Hn.
        destruct Hn as (t & Heqt & Ht). apply gmultiset_elem_of_elements in Ht.
        assert (Htu : t ∈ ss1 ∪ ss2)
          by (eapply gmultiset_elem_of_subseteq; eauto).
        apply gmultiset_elem_of_union in Htu as [Ht1 | Ht2].
        * assert (Hp1 : le.conc_sigs (RCons (SSig t TBot TBot) RNil) ⊆ ss1)
            by (cbn [le.conc_sigs le.eff_name_from_sig]; multiset_solver).
          assert (Hp2 : le.abst_sigs (RCons (SSig t TBot TBot) RNil) ⊆ js1)
            by (cbn [le.abst_sigs]; set_solver).
          destruct (Hm1 _ Hp1 Hp2) as [Hnl _].
          apply Hnl. cbn [row_labels_l le.eff_name_from_sig].
          rewrite Heqt. apply list_elem_of_here.
        * assert (Hp1 : le.conc_sigs (RCons (SSig t TBot TBot) RNil) ⊆ ss2)
            by (cbn [le.conc_sigs le.eff_name_from_sig]; multiset_solver).
          assert (Hp2 : le.abst_sigs (RCons (SSig t TBot TBot) RNil) ⊆ js2)
            by (cbn [le.abst_sigs]; set_solver).
          destruct (Hm2 _ Hp1 Hp2) as [Hnl _].
          apply Hnl. cbn [row_labels_l le.eff_name_from_sig].
          rewrite Heqt. apply list_elem_of_here.
      + destruct (elem_of_var_labels_l_mono ρ0 ρ0 ξ _ (reflexivity _) Hvr)
          as (i & Hi & Hl).
        assert (Hiu : i ∈ js1 ∪ js2) by (eapply elem_of_weaken; eauto).
        apply elem_of_union in Hiu as [Hi1 | Hi2].
        * assert (Hp1 : le.conc_sigs (RVar i) ⊆ ss1)
            by (cbn [le.conc_sigs]; multiset_solver).
          assert (Hp2 : le.abst_sigs (RVar i) ⊆ js1)
            by (cbn [le.abst_sigs]; set_solver).
          destruct (Hm1 _ Hp1 Hp2) as [Hnl _].
          apply Hnl. cbn [row_labels_l]. exact Hl.
        * assert (Hp1 : le.conc_sigs (RVar i) ⊆ ss2)
            by (cbn [le.conc_sigs]; multiset_solver).
          assert (Hp2 : le.abst_sigs (RVar i) ⊆ js2)
            by (cbn [le.abst_sigs]; set_solver).
          destruct (Hm2 _ Hp1 Hp2) as [Hnl _].
          apply Hnl. cbn [row_labels_l]. exact Hl.
    - iPureIntro.
      rewrite (labels_r_interp_row ρ0 η μ δ ξ).
      intros Hin. rewrite row_labels_r_split elem_of_app in Hin.
      destruct Hin as [Hn | Hvr].
      + rewrite /name_labels_r list_elem_of_fmap in Hn.
        destruct Hn as (t & Heqt & Ht). apply gmultiset_elem_of_elements in Ht.
        assert (Htu : t ∈ ss1 ∪ ss2)
          by (eapply gmultiset_elem_of_subseteq; eauto).
        apply gmultiset_elem_of_union in Htu as [Ht1 | Ht2].
        * assert (Hp1 : le.conc_sigs (RCons (SSig t TBot TBot) RNil) ⊆ ss1)
            by (cbn [le.conc_sigs le.eff_name_from_sig]; multiset_solver).
          assert (Hp2 : le.abst_sigs (RCons (SSig t TBot TBot) RNil) ⊆ js1)
            by (cbn [le.abst_sigs]; set_solver).
          destruct (Hm1 _ Hp1 Hp2) as [_ Hnr].
          apply Hnr. cbn [row_labels_r le.eff_name_from_sig].
          rewrite Heqt. apply list_elem_of_here.
        * assert (Hp1 : le.conc_sigs (RCons (SSig t TBot TBot) RNil) ⊆ ss2)
            by (cbn [le.conc_sigs le.eff_name_from_sig]; multiset_solver).
          assert (Hp2 : le.abst_sigs (RCons (SSig t TBot TBot) RNil) ⊆ js2)
            by (cbn [le.abst_sigs]; set_solver).
          destruct (Hm2 _ Hp1 Hp2) as [_ Hnr].
          apply Hnr. cbn [row_labels_r le.eff_name_from_sig].
          rewrite Heqt. apply list_elem_of_here.
      + destruct (elem_of_var_labels_r_mono ρ0 ρ0 ξ _ (reflexivity _) Hvr)
          as (i & Hi & Hl).
        assert (Hiu : i ∈ js1 ∪ js2) by (eapply elem_of_weaken; eauto).
        apply elem_of_union in Hiu as [Hi1 | Hi2].
        * assert (Hp1 : le.conc_sigs (RVar i) ⊆ ss1)
            by (cbn [le.conc_sigs]; multiset_solver).
          assert (Hp2 : le.abst_sigs (RVar i) ⊆ js1)
            by (cbn [le.abst_sigs]; set_solver).
          destruct (Hm1 _ Hp1 Hp2) as [_ Hnr].
          apply Hnr. cbn [row_labels_r]. exact Hl.
        * assert (Hp1 : le.conc_sigs (RVar i) ⊆ ss2)
            by (cbn [le.conc_sigs]; multiset_solver).
          assert (Hp2 : le.abst_sigs (RVar i) ⊆ js2)
            by (cbn [le.abst_sigs]; set_solver).
          destruct (Hm2 _ Hp1 Hp2) as [_ Hnr].
          apply Hnr. cbn [row_labels_r]. exact Hl.
  Qed.
    
    

  (* Combined soundness of the three syntactic subtyping judgements, by ONE
     simultaneous induction (combined scheme [le_subtyping_mut]).  The
     per-case tactics and IH names are uniform.  Cases left as documented
     [admit]s (the genuine gaps, collected here):
     - [SFlipComp_le]/[RFlipComp_le] are now DISCHARGED: the Inductive's
       mode premise was corrected from [m' ≤M m] to [m ≤M m'] (the typo
       noted previously), which is exactly the direction the ANTITONE
       semantic [sig/row_le_mfbang_comp] needs ([mode_le_sound] + the IH).
     - [RCons_le]: now DISCHARGED.  The two LABEL submseteq side-conditions
       of [row_le_cons_comp] follow from label-monotonicity of [≤ᵣ] along
       the [@false] row premise, proved here as
       [row_le_false_labels_l]/[_r] (induction on the [@false] derivation;
       [RErase_le] is [@true]-only so no label is ever dropped).
     - [RUnion_le]: DISCHARGED at [b = false] via [sem_row.row_le_union']
       (a closeable variant of [row_le_union] taking the two cross-
       disjointness label submseteq facts, supplied by
       [row_le_false_labels_l]/[_r]).  The [b = true] sub-case still routes
       through the upstream-admitted [row_le_union]: at [b = true]
       [RErase_le] may drop labels, so label-monotonicity (hence the
       cross-disjointness preservation) no longer holds structurally.
     - [RFlipUnion_le]: DISCHARGED via [sem_row.row_le_flip_union]
       (flip distributes over union: equal underlying theory lists,
       [map] over [++]).
     - [TArrow_le]: premises live at [D' = update_disj_ctx ρ' D]; the IHs
       need [erase_ctx D'] but we only have [erase_ctx D], and
       [erase_ctx D → erase_ctx D'] is not provable (D' has larger ss/js +
       new entries from [ρ']; their ownership/freshness needs the ambient
       row's [valid]).  THE central remaining gap.
     - [TRec_le]: STILL ADMITTED.  [ty_le_rec] needs the PARAMETRIC monotone
       premise [∀ α' β', α' ≤ₜ β' -∗ C₁ α' ≤ₜ C₂ β'] (to relate the differing
       recursive occurrences in the Löb unfold); the combined-scheme IH
       supplies only the DIAGONAL [∀ γ, C₁ γ ≤ₜ C₂ γ].  Bridging them needs
       env-monotonicity of [interp._ty] in the recursion variable (fails
       without positivity) or strengthening the whole induction to two
       related environments (out of scope).  See the case body.
     [RErase_le] (the linchpin) IS discharged here, via [erase_ctx] +
     [sem_row.row_le_erase].  ([RFlipCons_le] is closed via
     [row_le_mfbang_dist_cons], itself [Admitted] upstream.) *)
  Lemma subtyping_sound_all :
    (∀ D σ σ', D ⊢ₗ σ ≤S σ' → ⊢ sem_sig_le D σ σ') ∧
    (∀ D b ρ ρ', D ⊢ₗ ρ ≤R ρ' @ b → ⊢ sem_row_le D b ρ ρ') ∧
    (∀ D α β, D ⊢ₗ α ≤T β → ⊢ sem_ty_le D α β).
  Proof.
    apply le_subtyping_mut.
    all : intros; iIntros (????) "!# #He"; simpl.
    (* effect-signature cases *)
    - iApply sig_le_eff; iIntros "!#" (αs);
      [iApply H | iApply H0];
        by iApply erase_ctx_extend_ty.
    - iApply sig_le_mfbang_intro.
    - iApply sig_le_mfbang_elim_ms.
    - iApply sig_le_mfbang_idemp.
    - iApply sig_le_mfbang_intro.
    - iApply (sig_le_mfbang_comp with "[] []").
      + iApply mode_le_sound; exact _m.
      + by iApply H.
    (* row cases *)
    - iApply row_le_refl.
    - iApply row_le_refl.
    - iApply row_le_cons_extend.
    - iApply row_le_swap_second.
    - iApply row_le_cons_comp; last first.
      + by iApply H0.
      + by iApply H.
      (* RCons_le: the two LABEL submseteq side-conditions follow from
         label-monotonicity of [≤R] along the [@false] row premise [_r]. *)
      + by eapply row_le_false_labels_r.
      + by eapply row_le_false_labels_l.
    - (* RUnion_le.  At [b = false] the cross-disjointness side-condition
         of [row_le_union'] is supplied by label-monotonicity of [≤R]
         ([row_le_false_labels_l]/[_r]); the [b = true] sub-case still
         routes through the (upstream-admitted) [row_le_union], since at
         [b = true] [RErase_le] may drop labels and label-monotonicity no
         longer holds. *)
      iApply (row_le_union' with "[] []");
          [ by eapply row_le_false_labels_l
          | by eapply row_le_false_labels_l
          | by eapply row_le_false_labels_r
          | by eapply row_le_false_labels_r
          | by iApply H | by iApply H0 ].
    - iDestruct ("He" $! s ss js ρ with "[//] [//] [//]")
        as "(Hl1 & Hl2 & %Hnl & %Hnr)".
      iApply (row_le_erase with "Hl1 Hl2"); done.
    - iApply (row_le_trans with "[] []"); [by iApply H|by iApply H0].
    - iApply row_le_mfbang_elim_nil.
    - iApply row_le_mfbang_dist_cons.
    - (* RFlipUnion_le: flip distributes over union; both sides have the
         same underlying theory list ([map] over [++]). *)
      iApply row_le_flip_union.
    - iApply row_le_mfbang_elim_ms.
    - iApply row_le_mfbang_intro.
    - iApply row_le_mfbang_idemp.
    - iApply row_le_mfbang_intro.
    - iApply (row_le_mfbang_comp with "[] []").
      + iApply mode_le_sound; exact _m.
      + by iApply H.
    (* type cases *)
    - iApply ty_le_refl.
    - iApply (ty_le_trans with "[] []"); [by iApply H|by iApply H0].
    - iApply ty_le_bot.
    - iIntros "!#" (v1 v2) "_". done.
    - iIntros (??) "!# Hτ1 % % Hα". iApply brel_learn. iIntros "#Hd #Hv".
      iDestruct (arr_extend_D with "[$He]") as "HD'".
      iSpecialize ("HD'" with "Hd Hv"). 
      iDestruct (H with "HD'") as "Hαα".
      iDestruct ("Hαα" with "Hα") as "Hα'".
      iDestruct ("Hτ1" with "Hα'") as "Hbrel".
      iApply brel_introduction_mono.
      { by iApply H0. }
      iApply (brel_wand with "Hbrel").
      iIntros (??) "!# Hβ". by iApply H1.
    - iApply ty_le_ref; by iApply H.
    - iApply ty_le_type_forall; iIntros (α'); iApply H; by iApply erase_ctx_extend_ty.
    (* Following case was removed from the syntactic rules *)
    (* - iApply ty_le_row_forall; iIntros (θ). iApply H. admit. *) 
    - iApply ty_le_mode_forall; iIntros (ν); iApply H; by iApply erase_ctx_extend_mode.
    (* - iApply ty_le_rec.
         (* TRec_le: STILL ADMITTED.  [ty_le_rec] (sem_types.v) requires the
            PARAMETRIC monotone premise
              [□ (∀ α' β', α' ≤ₜ β' -∗ C₁ α' ≤ₜ C₂ β')]
            (the Löb unfold step relates the recursive occurrences
            [μₜ C₁] / [μₜ C₂], which DIFFER, so it must thread [α' ≤ₜ β']
            through the body).  Here [C₁ τ' = interp._ty (τ'::η) α] and
            [C₂ τ' = interp._ty (τ'::η) β], and the combined-scheme IH [H]
            supplies only the DIAGONAL [∀ γ, C₁ γ ≤ₜ C₂ γ] ([H (γ::η)]).
            Deriving the parametric form from the diagonal would need
            environment-monotonicity of [interp._ty] in the head (de Bruijn
            0) variable, which fails without a positivity restriction on the
            recursion variable; equivalently it requires STRENGTHENING the
            whole [le_subtyping_mut] induction to relate TWO pointwise-[≤ₜ]
            environments (changing [Psig]/[Prow]/[Pty] and re-proving every
            case).  That restructuring is out of scope (add-only); cf.
            [TArrow_le], the other remaining gap. *)
         admit. *)
    - iApply (ty_le_prod with "[] []"); [by iApply H|by iApply H0].
    - iApply (ty_le_sum with "[] []"); [by iApply H|by iApply H0].
    - iApply ty_le_mbang_intro_bool.
    - iApply ty_le_mbang_intro_unit.
    - iApply ty_le_mbang_intro_int.
    - iIntros "!#" (v1 v2) "#Hnat". rewrite /sem_ty_mbang.
      iApply bi.intuitionistically_intuitionistically_if. by iModIntro.
    - iApply ty_le_mbang_intro_top.
    - iApply ty_le_mbang_intro_os.
    - iApply ty_le_mbang_idemp.
    - iApply ty_le_mbang_elim.
    - iApply ty_le_mbang_elim.
    - iApply (ty_le_mbang_comp with "[] []");
        [iApply mode_le_sound; exact _m | by iApply H].
    - iApply ty_le_type_forall_mbang.
    - iApply ty_le_mbang_type_forall.
    - iApply ty_le_row_forall_mbang.
    - iApply ty_le_mbang_row_forall.
    - (* TNat_le_TInt: a nat literal [#n] is the int literal [#(Z.of_nat n)]. *)
      iIntros "!#" (v1 v2) "Hnat". iDestruct "Hnat" as (n) "[-> ->]".
      iExists (Z.of_nat n). done.
  Qed.

  (* The three named soundness lemmas, projected from [subtyping_sound_all]. *)
  Lemma sig_le_sound_open D σ σ' :
    D ⊢ₗ σ ≤S σ' → ⊢ sem_sig_le D σ σ'.
  Proof. apply subtyping_sound_all. Qed.

  Lemma row_le_sound_open D b ρ ρ' :
    D ⊢ₗ ρ ≤R ρ' @ b → ⊢ sem_row_le D b ρ ρ'.
  Proof. apply subtyping_sound_all. Qed.

  Lemma ty_le_sound_open D α β :
    D ⊢ₗ α ≤T β → ⊢ sem_ty_le D α β.
  Proof. apply subtyping_sound_all. Qed.

  (* ===================================================================== *)
  (** ** User-facing soundness statements                                  *)
  (*                                                                        *)
  (*  These are the target lemmas of the subtyping-soundness goal.  They    *)
  (*  thread the [erase_ctx D] hypothesis bundle (needed by [RErase_le];    *)
  (*  see the module comment) and expose [η μ ξ] explicitly.  [sig]/[ty]    *)
  (*  are premise-free in the syntactic judgement but carry [erase_ctx]     *)
  (*  because [TArrow_le] reaches through [_row] into the erase machinery.  *)

  Lemma sig_le_sound D σ σ' (η : list (sem_ty Σ)) (μ : list mode) δ
    (ξ : list (sem_row Σ)) :
    D ⊢ₗ σ ≤S σ' →
    erase_ctx η μ δ ξ D -∗
    interp._eff_sig η μ δ σ ξ ≤ₛ interp._eff_sig η μ δ σ' ξ.
  Proof. intros H. iApply (sig_le_sound_open _ _ _ H). Qed.

  Lemma row_le_sound D b ρ ρ' (η : list (sem_ty Σ)) (μ : list mode) δ
    (ξ : list (sem_row Σ)) :
    D ⊢ₗ ρ ≤R ρ' @ b →
    erase_ctx η μ δ ξ D -∗
    interp._row η μ δ ρ ξ ≤ᵣ interp._row η μ δ ρ' ξ.
  Proof. intros H. iApply (row_le_sound_open _ _ _ _ H). Qed.

  Lemma ty_le_sound D α β (η : list (sem_ty Σ)) (μ : list mode) δ
    (ξ : list (sem_row Σ)) :
    D ⊢ₗ α ≤T β →
    erase_ctx η μ δ ξ D -∗
    interp._ty η μ δ α ξ ≤ₜ interp._ty η μ δ β ξ.
  Proof. intros H. iApply (ty_le_sound_open _ _ _ H). Qed.

 (* [erase_ctx] holds vacuously at the EMPTY disjointness context: the    *)
  (* [RErase_le] premise bundle quantifies over keys [s] with              *)
  (* [∅ !! s = Some _], which is unsatisfiable.  This is what lets us run   *)
  (* [row_le_sound] at [∅] (the context used by [le.OnceR]/[le.MultiT]).   *)
  Lemma erase_ctx_empty η μ δ ξ : ⊢ erase_ctx η μ δ ξ ∅.
  Proof.
    rewrite /erase_ctx. iIntros "!#" (s ss js ρ0 Hlk).
    rewrite lookup_empty in Hlk. done.
  Qed.

  Lemma multi_ty_sound (τ : type) :
    le.MultiT τ → ∀ η μ δ ξ, MultiT (interp._ty η μ δ τ ξ).
  Proof.
    intros H ????. unfold le.MultiT in H. eapply ty_le_sound in H.
    constructor.
    iApply H. iApply erase_ctx_empty.
  Qed.
  
  (* The interpretation of a context [Γ] at a given interpretation env. *)
  Notation interp_env η μ δ ξ Γ :=
    ((λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> Γ).

  (* Soundness of [le.MultiC]: a syntactically multi context interprets to
     a semantic [MultiE].  Forall-lift of [multi_ty_sound]. *)
  Lemma multi_env_sound (Γ : ctx) :
    le.MultiC Γ → ∀ η μ δ ξ, MultiE (interp_env η μ δ ξ Γ).
  Proof.
    intros Hm η μ δ ξ. induction Γ as [|[x τ] Γ' IH]; simpl.
    - apply multi_env_nil.
    - apply Forall_cons in Hm as [Hτ HΓ'].
      apply multi_env_cons; first by apply IH.
      by apply multi_ty_sound.
  Qed.

  (* Soundness of [le._mode_type]: note [m m⪯T τ] forces [m ∈ {OS, MS}]. *)
  Lemma mode_type_sound (m : vmode) (τ : type) :
    m m⪯T τ → ∀ η μ δ ξ, (interp._mode μ m) ₘ⪯ₜ (interp._ty η μ δ τ ξ).
  Proof.
    intros Hm η μ δ ξ. inv Hm; simpl.
    - apply mode_type_sub_os.
    - apply mode_type_sub_multi_ty. by apply multi_ty_sound.
  Qed.

  (* Soundness of [le._mode_ctx]: a syntactic mode-context judgement
     interprets to a semantic mode-env-subtyping. *)
  Lemma mode_env_sound (m : vmode) (Γ : ctx) :
    m m⪯C Γ → ∀ η μ δ ξ, (interp._mode μ m) ₘ⪯ₑ (interp_env η μ δ ξ Γ).
  Proof.
    intros Hm η μ δ ξ. induction Hm as [m'|m' x τ Γ' Hτ HΓ' IH]; simpl.
    - apply mode_env_sub_nil.
    - destruct x as [|s]; simpl.
      + apply IH.
      + apply mode_env_sub_cons; first apply IH.
        by apply mode_type_sound.
  Qed.

  (* ===================================================================== *)
  (** ** Soundness of the row-substructurality judgements                  *)
  (*      ([le._row_type] / [le._row_ctx])                                  *)
  (*                                                                        *)
  (*  These are the wrappers consumed by the [Pair_typed]/[TStore]/[App]    *)
  (*  cases of [fundamental]: they turn a syntactic [ρ R⪯T τ] / [ρ R⪯C Γ]   *)
  (*  derivation into the semantic [RowTypeSub]/[RowEnvSub] typeclasses     *)
  (*  expected by the compatibility lemmas [sem_typed_pair_gen] etc.        *)

 

  (* Soundness of [le.OnceR].                                               *)
  (*                                                                        *)
  (*  The semantic [OnceR ρ] (sem_row.v) is the one-shot property           *)
  (*  [⊢ ¡ ρ ≤ᵣ ρ] with [¡ = sem_row_flip_mbang OS].  The syntactic         *)
  (*  [le.OnceR ρ] (types.v) is [∃ b, ∅ ⊢ₗ RFlip OS ρ ≤R ρ @ b]; under      *)
  (*  [row_le_sound] (run at [∅] via [erase_ctx_empty]) its interpretation  *)
  (*  is [¡[interp._mode μ OS] (interp ρ) ≤ᵣ interp ρ], and                 *)
  (*  [interp._mode μ OS = OS] definitionally, so this is exactly the       *)
  (*  semantic [OnceR] field [⊢ ¡ (interp ρ) ≤ᵣ interp ρ].                  *)
  Lemma once_row_sound (ρ : row) :
    le.OnceR ρ → ∀ η μ δ ξ, OnceR (interp._row η μ δ ρ ξ).
  Proof.
    intros [b0 Hle] η0 μ0 ξ0. constructor.
    iApply (row_le_sound _ _ _ _ _ _ _ _ Hle). iApply erase_ctx_empty.
  Qed.

  (* Soundness of [le._row_type]: turns [ρ R⪯T τ] into the semantic         *)
  (* [RowTypeSub] typeclass.  The [Multi_le] case is fully proved (via      *)
  (* [multi_ty_sound] + the existing [row_type_sub_multi_ty] instance); the *)
  (* [Once_le] case is sound modulo [once_row_sound] above. *)
  Lemma row_type_sub_sound (ρ : row) (τ : type) :
    ρ R⪯T τ → ∀ η μ δ ξ,
      RowTypeSub (interp._row η μ δ ρ ξ) (interp._ty η μ δ τ ξ).
  Proof.
    intros Hsub η0 μ0 δ0 ξ0. destruct Hsub as [ρ' τ' Honce | ρ' τ' Hmulti].
    - apply row_type_sub_once.
      by apply (once_row_sound _ Honce).
    - pose proof (multi_ty_sound _ Hmulti η0 μ0 δ0 ξ0) as Hm.
      by apply row_type_sub_multi_ty.
  Qed.

  (* Soundness of [le._row_ctx]: turns [ρ R⪯C Γ] into the semantic          *)
  (* [RowEnvSub] typeclass.  Mirrors [mode_env_sound]: induction on the     *)
  (* derivation, [Nil] via [row_env_sub_nil], [Cons] via [row_env_sub_cons] *)
  (* fed by [row_type_sub_sound].  The [BAnon] binder leaves [Γ] unchanged. *)
  Lemma row_env_sub_sound (ρ : row) (Γ : ctx) :
    ρ R⪯C Γ → ∀ η μ δ ξ,
      RowEnvSub (interp._row η μ δ ρ ξ) (interp_env η μ δ ξ Γ).
  Proof.
    intros Hsub η0 μ0 δ0 ξ0.
    induction Hsub as [ρ'|ρ' x τ Γ' Hτ HΓ' IH]; simpl.
    - apply row_env_sub_nil.
    - destruct x as [|s]; simpl.
      + apply IH.
      + apply row_env_sub_cons; first apply IH.
        by apply (row_type_sub_sound _ _ Hτ).
  Qed.

  (* Soundness of context subtyping [le._ctx].  The syntactic [D ⊢ₗ Γ ≤C Γ']
     interprets to an [env_le] between the pointwise-interpreted contexts.
     [le._ctx] recurses on [Γ'], so we induct on [Γ']: the [[]] case is the
     unconditional [env_le_nil]; the cons case uses [env_le_bring_forth] to
     surface the matched entry [(x,t')] out of [Γ = pre ++ (x,t') :: post],
     [env_le_cons] with [ty_le_sound] on the head and the IH on the tail
     (both under the [erase_ctx] bundle), combined by [env_le_trans]. *)
  Lemma ctx_le_sound (D : le.disj_ctx) (Γ Γ' : ctx) :
    D ⊢ₗ Γ ≤C Γ' → ∀ η μ δ ξ,
      erase_ctx η μ δ ξ D -∗
      interp_env η μ δ ξ Γ ≤ₑ interp_env η μ δ ξ Γ'.
  Proof.
    revert Γ. induction Γ' as [|[x t] Γ'_tail IH]; intros Γ Hle η μ δ ξ.
    - iIntros "#Herase". simpl. iApply env_le_nil.
    - iIntros "#Herase". simpl in Hle.
      destruct Hle as (t' & pre & post & -> & Ht & Htail).
      (* [(x,t')] sits at position [length pre] in the interpreted [Γ]. *)
      assert (Hnth : nth_error ((λ '(s, τ), (s, interp._ty η μ δ τ ξ))
                                  <$> (pre ++ (x, t') :: post))
                       (length pre) = Some (x, interp._ty η μ δ t' ξ)).
      { rewrite fmap_app /=. rewrite (nth_error_app2 _ _ (n := length pre)).
        { rewrite length_fmap Nat.sub_diag //. }
        rewrite length_fmap //. }
      (* Deleting it leaves the interpretation of [pre ++ post]. *)
      assert (Hdel : list_delete (length pre)
                       ((λ '(s, τ), (s, interp._ty η μ δ τ ξ))
                          <$> (pre ++ (x, t') :: post))
                     = (λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> (pre ++ post)).
      { rewrite !fmap_app /=.
        rewrite -(length_fmap (λ '(s, τ), (s, interp._ty η μ δ τ ξ)) pre).
        apply delete_middle. }
      simpl.
      iApply (env_le_trans _ ((x, interp._ty η μ δ t' ξ)
                :: ((λ '(s, τ), (s, interp._ty η μ δ τ ξ)) <$> (pre ++ post)))).
      + rewrite -Hdel.
        iApply (env_le_bring_forth _ (length pre) x (interp._ty η μ δ t' ξ) Hnth).
      + iApply env_le_cons.
        * iApply (IH _ Htail with "Herase").
        * iApply (ty_le_sound _ _ _ _ _ _ _ Ht with "Herase").
  Qed.

End interp_subst.
