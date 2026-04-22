From clutch.prob_eff_lang.probblaze Require Import logic sem_sig sem_row sem_types sem_def syntax types.

Module interp. 

  Definition _mode (μ : list mode) (m : vmode) : mode :=
    match m with 
    | MVar i => μ !!! i
    | OS => syntax.OS
    | MS => syntax.MS
    end.

  (* TODO: construct a contractive constructor for SemRow *)
  (* Definition sem_row_rec1 {Σ} (C : sem_row Σ -n> sem_row Σ) (rec : sem_row Σ) : sem_row Σ :=
       SemRow (sem_row_car (C rec))%I _.
     Global Instance lrel_rec1_contractive C : Contractive (lrel_rec1 C).
     Proof.
       intros n. intros P Q HPQ.
       unfold lrel_rec1. intros w1 w2. rewrite {1 4}/lrel_car /=.
       f_contractive. f_equiv. by apply C.
     Qed. *)

  (* Definition sem_row_rec_pre {Σ} (C : sem_row Σ → sem_row Σ)
       (rec : sem_row Σ) : sem_row Σ := (λ v1 v2, ▷ (∃ rec', rec ≡ rec' ∧ C rec' v1 v2))%I.
     Global Instance sem_ty_rec_pre_contractive {Σ} (C : sem_ty Σ → sem_ty Σ) :
       Contractive (sem_ty_rec_pre C).
     Proof. solve_contractive. Qed. *)
  (* TODO: figure out RRec *)
  Fixpoint _eff_sig `{!probblazeRGS Σ}
    (n : list (sem_ty Σ))
    (ξ : list (sem_row Σ))
    (μ : list mode) 
    (δ : gmap eff_name (label * label))
    (σ : eff_sig) : sem_sig Σ :=
    match σ with
    | SSig s α β =>
        sem_sig_eff (δ !!! s).1 (δ !!! s).2 ((λ τ', _ty (τ' :: n) ξ μ δ α)) (λ τ', _ty (τ' :: n) ξ μ δ β)
    | SFlip m e =>
        sem_sig_flip_mbang (_mode μ m) (_eff_sig n ξ μ δ e)
    end 
  with _row `{!probblazeRGS Σ}
    (n : list (sem_ty Σ))
    (ξ : list (sem_row Σ))
    (μ : list mode)
    (δ : gmap eff_name (label * label))
    (ρ : row) : sem_row Σ :=
         match ρ with
         | RNil => ⊥
         | RVar i => ξ !!! i
         | RFlip m ρ => sem_row_flip_mbang (_mode μ m) (_row n ξ μ δ ρ)
         | RCons e ρ => sem_row_cons (_eff_sig n ξ μ δ e) (_row n ξ μ δ ρ)
         | RRec ρ => (* sem_row_rec ((λ ρ', _row n (ρ' :: ξ) μ δ ρ)) *) ⊥
         end 
  with _ty `{!probblazeRGS Σ}
    (n : list (sem_ty Σ))
    (ξ : list (sem_row Σ))
    (μ : list mode)
    (δ : gmap eff_name (label * label))
    (τ : type) : sem_ty Σ :=
         match τ with
         | TBot => ⊥
         | TTop => ⊤
         | TUnit => sem_ty_unit
         | TInt => sem_ty_int
         | TNat => sem_ty_nat
         | TBool => sem_ty_bool
         | TTape => sem_ty_tape
         | TRef τ => sem_ty_ref (_ty n ξ μ δ τ)
         | TProd τ1 τ2 => sem_ty_prod (_ty n ξ μ δ τ1) (_ty n ξ μ δ τ2)
         | TSum τ1 τ2 => sem_ty_sum (_ty n ξ μ δ τ1) (_ty n ξ μ δ τ2)
         | TBang m τ => sem_ty_mbang (_mode μ m) (_ty n ξ μ δ τ)
         | TArrow α ρ β => sem_ty_arr (_row n ξ μ δ ρ) (_ty n ξ μ δ α) (_ty n ξ μ δ β)
         | TForallM τ => sem_ty_mode_forall (λ m, _ty n ξ (m :: μ) δ τ)
         | TForallR τ => sem_ty_row_forall (λ ρ, _ty n (ρ :: ξ) μ δ τ)
         | TForallT τ => sem_ty_type_forall (λ τ', _ty (τ' :: n) ξ μ δ τ)
         | TExists τ => sem_ty_exists (λ τ', _ty (τ' :: n) ξ μ δ τ)
         | TRec τ => sem_ty_rec (λ τ', _ty (τ' :: n) ξ μ δ τ)
         | TVar i => n !!! i
         end.

End interp.
