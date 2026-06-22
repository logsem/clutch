From clutch.prob_eff_lang.probblaze Require Import logic sem_sig sem_row sem_types sem_def syntax types.
From iris.algebra Require Export list gmap.


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
    (n : list (sem_ty Σ))
    (μ : list mode) 
    (δ : gmap eff_name (label * label))
    (σ : eff_sig) : listO (sem_row Σ) -n> sem_sig Σ :=
    match σ with
    | SSig s α β => λne ξ, let ops := δ !!! s in sem_sig_eff ops.1 ops.2 (λ τ', _ty (τ' :: n) μ δ α ξ) (λ τ', _ty (τ' :: n) μ δ β ξ)
    | SFlip m e => λne ξ, sem_sig_flip_mbang (_mode μ m) (_eff_sig n μ δ e ξ)
    end 
      with _row `{!probblazeRGS Σ}
           (n : list (sem_ty Σ))
           (μ : list mode)
           (δ : gmap eff_name (label * label))
           (ρ : row) : listO (sem_row Σ) -n> sem_row Σ :=
      match ρ with
      | RNil => λne _, ⊥
      | RVar i =>  λne ξ, ξ !!! i
      | RFlip m ρ => λne ξ, sem_row_flip_mbang (_mode μ m) (_row n μ δ ρ ξ)
      | RCons e ρ => λne ξ, sem_row_cons (_eff_sig n μ δ e ξ) (_row n μ δ ρ ξ)
      (* | RRec ρ' => fun H => λne ξ, sem_row_rec' (λne ρ'', _row n μ δ ρ' _ (ρ'' :: ξ)) *)
      | RUnion ρ1 ρ2 => λne ξ, sem_row_union (_row n μ δ ρ1 ξ) (_row n μ δ ρ2 ξ)
      end 
      with _ty `{!probblazeRGS Σ}
           (n : list (sem_ty Σ))
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
        | TRef τ => λne ξ, sem_ty_ref (_ty n μ δ τ ξ)
        | TProd τ1 τ2 => λne ξ, sem_ty_prod (_ty n μ δ τ1 ξ) (_ty n μ δ τ2 ξ)
        | TSum τ1 τ2 => λne ξ, sem_ty_sum (_ty n μ δ τ1 ξ) (_ty n μ δ τ2 ξ)
        | TBang m τ => λne ξ, sem_ty_mbang (_mode μ m) (_ty n μ δ τ ξ)
        | TArrow α ρ β => λne ξ, sem_ty_arr (_row n μ δ ρ ξ) (_ty n μ δ α ξ) (_ty n μ δ β ξ)
        | TForallM τ => λne ξ, sem_ty_mode_forall (λ m, _ty n (m :: μ) δ τ ξ)
        | TForallR τ => λne ξ, sem_ty_row_forall (λ ρ, _ty n μ δ τ (ρ :: ξ))
        | TForallT τ => λne ξ, sem_ty_type_forall (λ τ', _ty (τ' :: n) μ δ τ ξ)
        | TExists τ => λne ξ, sem_ty_exists (λ τ', _ty (τ' :: n) μ δ τ ξ)
        | TRec τ => λne ξ, sem_ty_rec (λ τ', _ty (τ' :: n) μ δ τ ξ)
        | TVar i => λne _, n !!! i
        end.
  Proof. 
    all: try exact probblazeRGS0; try apply probblazeRGS_probblazeGS.
    1 : apply effname_lookup_total. 
    all: try (intros ????; by repeat f_equiv).
    all: intros ????; simpl; f_equiv; intros ?; by f_equiv. 
  Qed. 

  (* #[refine] Fixpoint _eff_sig `{!probblazeRGS Σ}
       (n : list (sem_ty Σ))
       (μ : list mode) 
       (δ : gmap eff_name (label * label))
       (σ : eff_sig)
       (Hwf : wf_eff_sig σ) : listO (sem_row Σ) -n> sem_sig Σ :=
       match σ as x return (wf_eff_sig x -> (listO (sem_row Σ) -n> sem_sig Σ)) with
       | SSig s α β => fun H => 
           λne ξ, let ops := δ !!! s in sem_sig_eff ops.1 ops.2 (λ τ', _ty (τ' :: n) μ δ α (wf_eff_sig_SSig_1 s α β H) ξ) (λ τ', _ty (τ' :: n) μ δ β (wf_eff_sig_SSig_2 s α β _) ξ)
       | SFlip m e => fun H => 
           λne ξ, sem_sig_flip_mbang (_mode μ m) (_eff_sig n μ δ e (wf_eff_sig_SFlip m e H) ξ)
       end Hwf
     with _row `{!probblazeRGS Σ}
       (n : list (sem_ty Σ))
       (μ : list mode)
       (δ : gmap eff_name (label * label))
       (ρ : row)
       `(Hwf : wf_row v ρ) : listO (sem_row Σ) -n> sem_row Σ :=
            match ρ as x return (wf_row v x -> (listO (sem_row Σ) -n> sem_row Σ)) with
            | RNil => fun _ => λne _, ⊥
            | RVar i => fun _ => λne ξ, ξ !!! i
            | RFlip m ρ => fun H => λne ξ, sem_row_flip_mbang (_mode μ m) (_row n μ δ ρ (wf_row_RFlip v m ρ H) ξ)
            | RCons e ρ => fun H => λne ξ, sem_row_cons (_eff_sig n μ δ e (wf_row_eff_sig v ρ e H) ξ) (_row n μ δ ρ (wf_row_RCons v e ρ H) ξ)
            | RRec ρ' => fun H => λne ξ, sem_row_rec' (λne ρ'', _row n μ δ ρ' _ (ρ'' :: ξ))
            | RUnion ρ1 ρ2 => fun H => λne ξ, sem_row_union (_row n μ δ ρ1 (wf_row_union_1 v ρ1 ρ2 H) ξ) (_row n μ δ ρ2 (wf_row_union_2 v ρ1 ρ2 H) ξ)
            end Hwf
     with _ty `{!probblazeRGS Σ}
       (n : list (sem_ty Σ))
       (μ : list mode)
       (δ : gmap eff_name (label * label))
       (τ : type)
       (Hwf : wf_type τ) : listO (sem_row Σ) -n> sem_ty Σ :=
            match τ as x return (wf_type x -> (listO (sem_row Σ) -n> sem_ty Σ)) with
            | TBot => fun _ => λne _, ⊥
            | TTop => fun _ => λne _, ⊤
            | TUnit => fun _ => λne _, sem_ty_unit
            | TInt => fun _ => λne _, sem_ty_int
            | TNat => fun _ => λne _, sem_ty_nat
            | TBool => fun _ => λne _, sem_ty_bool
            | TTape => fun _ => λne _, sem_ty_tape
            | TRef τ => fun H => λne ξ, sem_ty_ref (_ty n μ δ τ _ ξ)
            | TProd τ1 τ2 => fun H => λne ξ, sem_ty_prod (_ty n μ δ τ1 _ ξ) (_ty n μ δ τ2 _ ξ)
            | TSum τ1 τ2 => fun H => λne ξ, sem_ty_sum (_ty n μ δ τ1 _ ξ) (_ty n μ δ τ2 _ ξ)
            | TBang m τ => fun H => λne ξ, sem_ty_mbang (_mode μ m) (_ty n μ δ τ _ ξ)
            | TArrow α ρ β => fun H => λne ξ, sem_ty_arr (_row n μ δ ρ (wf_type_row α ρ β _) ξ) (_ty n μ δ α _ ξ) (_ty n μ δ β _ ξ)
            | TForallM τ => fun H => λne ξ, sem_ty_mode_forall (λ m, _ty n (m :: μ) δ τ _ ξ)
            | TForallR τ => fun H => λne ξ, sem_ty_row_forall (λ ρ, _ty n μ δ τ _ (ρ :: ξ))
            | TForallT τ => fun H => λne ξ, sem_ty_type_forall (λ τ', _ty (τ' :: n) μ δ τ _ ξ)
            | TExists τ => fun H => λne ξ, sem_ty_exists (λ τ', _ty (τ' :: n) μ δ τ _ ξ)
            | TRec τ => fun H => λne ξ, sem_ty_rec (λ τ', _ty (τ' :: n) μ δ τ _ ξ)
            | TVar i => fun _ => λne _, n !!! i
            end Hwf.
     Proof.
       - apply effname_lookup_total. 
       - done.
       - done.
       - done. 
       - intros ????. simpl. f_equiv; intros ?; f_equiv; try done.
       - done.
       - intros ????. do 2 f_equiv; done.
       - done.
       - done.
       - intros ????. f_equiv; f_equiv; done.
       - apply list_lookup_total.
       - intros ????. by f_equiv. 
       - done.
       - intros ????. by f_equiv; f_equiv.
       - done.
       - exact (v + 1).
       - done. 
       - intros ????. by do 2 f_equiv.
       - intros ????. apply fixpoint_ne. solve_proper. 
       - done.
       - done.
       - intros ????; f_equiv; by f_equiv.
       - apply probblazeRGS_probblazeGS. 
       - done.
       - done.
       - intros ????. f_equiv. f_equiv. done. 
       - done.
       - naive_solver.
       - done.
       - naive_solver.
       - intros ????. by f_equiv; f_equiv.
       - done.
       - naive_solver.
       - done.
       - naive_solver.
       - intros ????. by f_equiv; f_equiv.
       - done.
       - done.
       - done.
       - done.
       - naive_solver.
       - done.
       - naive_solver.
       - intros ????. by do 2 f_equiv.
       - done.
       - done.
       - done.
       - intros ????. by do 3 f_equiv.
       - done.
       - done.
       - done.
       - intros ????. by do 3 f_equiv.
       - done.
       - done.
       - done.
       - intros ????. by do 4 f_equiv.
       - apply probblazeRGS_probblazeGS.
       - done.
       - done.
       - intros ????. by do 3 f_equiv.
       - done.
       - done.
       - intros ????; f_equiv. intros ?. f_equiv. done.
       - done.
       - done.
       - intros ????. by do 2f_equiv.
     Qed. *)

End interp.
