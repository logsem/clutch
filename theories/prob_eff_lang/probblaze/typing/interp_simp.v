From clutch.prob_eff_lang.probblaze Require Import logic sem_sig sem_row sem_types sem_def syntax sem_judgement mode.
From clutch.prob_eff_lang.probblaze.typing Require Import types interp.

(** * Unfolding lemmas for the interpretation (PLAN.md, Stage E)

    One equation per constructor of [type], [row], [eff_sig] and [vmode],
    each proved by [reflexivity].  They are registered in the rewrite
    database [interp_simp]; the tactic [interp_simp] rewrites with them.

    Unlike [simpl], rewriting unfolds exactly one layer of the
    interpretation per step and never unfolds the semantic type formers
    ([sem_ty_arr], [sem_ty_mbang], ...).  Like every [rewrite], it does not
    go under binders: below [TForallR]/[TForallT]/[TForallM]/[TExists]/[TRec]
    the body stays as [interp._ty … (θ :: ξ)] (resp. [τ' :: η], [m :: μ])
    until the binder is introduced (e.g. by [ty_le_row_forall] and
    [iIntros]); then [interp_simp] applies again.

    [RVar]/[TVar]/[MVar] at a literal index into a literal list reduce with
    the [_lookup] lemmas below ([(θ :: ξ) !!! 0 = θ], ...). *)

Section interp_simp.
  Context `{!probblazeRGS Σ}.
  Implicit Types (η : list (sem_ty Σ)) (μ : list mode)
    (δ : gmap eff_name (label * label)) (ξ : list (sem_row Σ)).

  (** ** Modes *)
  Lemma interp_MVar μ i : interp._mode μ (MVar i) = μ !!! i.
  Proof. reflexivity. Qed.
  Lemma interp_OS μ : interp._mode μ OS = syntax.OS.
  Proof. reflexivity. Qed.
  Lemma interp_MS μ : interp._mode μ MS = syntax.MS.
  Proof. reflexivity. Qed.

  (** ** Types *)
  Lemma interp_TBot η μ δ ξ : interp._ty η μ δ TBot ξ = (⊥ : sem_ty Σ).
  Proof. reflexivity. Qed.
  Lemma interp_TTop η μ δ ξ : interp._ty η μ δ TTop ξ = (⊤ : sem_ty Σ).
  Proof. reflexivity. Qed.
  Lemma interp_TUnit η μ δ ξ : interp._ty η μ δ TUnit ξ = sem_ty_unit.
  Proof. reflexivity. Qed.
  Lemma interp_TBool η μ δ ξ : interp._ty η μ δ TBool ξ = sem_ty_bool.
  Proof. reflexivity. Qed.
  Lemma interp_TInt η μ δ ξ : interp._ty η μ δ TInt ξ = sem_ty_int.
  Proof. reflexivity. Qed.
  Lemma interp_TNat η μ δ ξ : interp._ty η μ δ TNat ξ = sem_ty_nat.
  Proof. reflexivity. Qed.
  Lemma interp_TTape η μ δ ξ : interp._ty η μ δ TTape ξ = sem_ty_tape.
  Proof. reflexivity. Qed.
  Lemma interp_TRef η μ δ τ ξ :
    interp._ty η μ δ (TRef τ) ξ = sem_ty_ref (interp._ty η μ δ τ ξ).
  Proof. reflexivity. Qed.
  Lemma interp_TRefC η μ δ τ ξ :
    interp._ty η μ δ (TRefC τ) ξ = sem_ty_ref_cpy (interp._ty η μ δ τ ξ).
  Proof. reflexivity. Qed.
  Lemma interp_TProd η μ δ τ1 τ2 ξ :
    interp._ty η μ δ (TProd τ1 τ2) ξ
    = sem_ty_prod (interp._ty η μ δ τ1 ξ) (interp._ty η μ δ τ2 ξ).
  Proof. reflexivity. Qed.
  Lemma interp_TSum η μ δ τ1 τ2 ξ :
    interp._ty η μ δ (TSum τ1 τ2) ξ
    = sem_ty_sum (interp._ty η μ δ τ1 ξ) (interp._ty η μ δ τ2 ξ).
  Proof. reflexivity. Qed.
  Lemma interp_TBang η μ δ m τ ξ :
    interp._ty η μ δ (TBang m τ) ξ
    = sem_ty_mbang (interp._mode μ m) (interp._ty η μ δ τ ξ).
  Proof. reflexivity. Qed.
  Lemma interp_TArrow η μ δ α ρ β ξ :
    interp._ty η μ δ (TArrow α ρ β) ξ
    = sem_ty_arr (interp._row η μ δ ρ ξ) (interp._ty η μ δ α ξ) (interp._ty η μ δ β ξ).
  Proof. reflexivity. Qed.
  Lemma interp_TForallM η μ δ τ ξ :
    interp._ty η μ δ (TForallM τ) ξ
    = sem_ty_mode_forall (λ m, interp._ty η (m :: μ) δ τ ξ).
  Proof. reflexivity. Qed.
  Lemma interp_TForallR η μ δ τ ξ :
    interp._ty η μ δ (TForallR τ) ξ
    = sem_ty_row_forall (λ θ, interp._ty η μ δ τ (θ :: ξ)).
  Proof. reflexivity. Qed.
  Lemma interp_TForallT η μ δ τ ξ :
    interp._ty η μ δ (TForallT τ) ξ
    = sem_ty_type_forall (λ α, interp._ty (α :: η) μ δ τ ξ).
  Proof. reflexivity. Qed.
  Lemma interp_TExists η μ δ τ ξ :
    interp._ty η μ δ (TExists τ) ξ
    = sem_ty_exists (λ α, interp._ty (α :: η) μ δ τ ξ).
  Proof. reflexivity. Qed.
  Lemma interp_TRec η μ δ τ ξ :
    interp._ty η μ δ (TRec τ) ξ
    = sem_ty_rec (λ α, interp._ty (α :: η) μ δ τ ξ).
  Proof. reflexivity. Qed.
  Lemma interp_TVar η μ δ i ξ : interp._ty η μ δ (TVar i) ξ = η !!! i.
  Proof. reflexivity. Qed.

  (** ** Rows *)
  Lemma interp_RNil η μ δ ξ : interp._row η μ δ RNil ξ = (⊥ : sem_row Σ).
  Proof. reflexivity. Qed.
  Lemma interp_RVar η μ δ i ξ : interp._row η μ δ (RVar i) ξ = ξ !!! i.
  Proof. reflexivity. Qed.
  Lemma interp_RFlip η μ δ m ρ ξ :
    interp._row η μ δ (RFlip m ρ) ξ
    = sem_row_flip_mbang (interp._mode μ m) (interp._row η μ δ ρ ξ).
  Proof. reflexivity. Qed.
  Lemma interp_RCons η μ δ σ ρ ξ :
    interp._row η μ δ (RCons σ ρ) ξ
    = sem_row_cons (interp._eff_sig η μ δ σ ξ) (interp._row η μ δ ρ ξ).
  Proof. reflexivity. Qed.
  Lemma interp_RUnion η μ δ ρ1 ρ2 ξ :
    interp._row η μ δ (RUnion ρ1 ρ2) ξ
    = sem_row_union (interp._row η μ δ ρ1 ξ) (interp._row η μ δ ρ2 ξ).
  Proof. reflexivity. Qed.

  (** ** Signatures *)
  Lemma interp_SSig η μ δ s α β ξ :
    interp._eff_sig η μ δ (SSig s α β) ξ
    = sem_sig_eff (δ !!! s).1 (δ !!! s).2
        (λ τ', interp._ty (τ' :: η) μ δ α ξ) (λ τ', interp._ty (τ' :: η) μ δ β ξ).
  Proof. reflexivity. Qed.
  Lemma interp_SFlip η μ δ m σ ξ :
    interp._eff_sig η μ δ (SFlip m σ) ξ
    = sem_sig_flip_mbang (interp._mode μ m) (interp._eff_sig η μ δ σ ξ).
  Proof. reflexivity. Qed.

  (** ** Lookups at literal indices (variables of all three sorts) *)
  Lemma interp_lookup_cons_0 {A} `{!Inhabited A} (x : A) (l : list A) :
    (x :: l) !!! 0%nat = x.
  Proof. reflexivity. Qed.
  Lemma interp_lookup_cons_S {A} `{!Inhabited A} (x : A) (l : list A) i :
    (x :: l) !!! S i = l !!! i.
  Proof. reflexivity. Qed.

  (** ** Contexts *)
  Lemma interp_env_nil η μ δ ξ : interp._env η μ δ ξ [] = [].
  Proof. reflexivity. Qed.
  Lemma interp_env_cons η μ δ ξ x τ Γ :
    interp._env η μ δ ξ ((x, τ) :: Γ) = (x, interp._ty η μ δ τ ξ) :: interp._env η μ δ ξ Γ.
  Proof. reflexivity. Qed.
End interp_simp.

Global Hint Rewrite @interp_MVar @interp_OS @interp_MS
  @interp_TBot @interp_TTop @interp_TUnit @interp_TBool @interp_TInt
  @interp_TNat @interp_TTape @interp_TRef @interp_TRefC @interp_TProd
  @interp_TSum @interp_TBang @interp_TArrow @interp_TForallM
  @interp_TForallR @interp_TForallT @interp_TExists @interp_TRec
  @interp_TVar
  @interp_RNil @interp_RVar @interp_RFlip @interp_RCons @interp_RUnion
  @interp_SSig @interp_SFlip
  @interp_lookup_cons_0 @interp_lookup_cons_S
  @interp_env_nil @interp_env_cons : interp_simp.

(** [interp_simp] unfolds every interpretation occurrence that is not under
    a binder, one constructor at a time, until none is left. *)
Tactic Notation "interp_simp" := autorewrite with interp_simp.
Tactic Notation "interp_simp" "in" hyp(H) := autorewrite with interp_simp in H.
