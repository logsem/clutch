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

  (* Global Instance semrow_lookup_toal : LookupTotal Autosubst_Derive.var (sem_row Σ) (gmap  *)

  #[refine] Fixpoint _eff_sig `{!probblazeRGS Σ}
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
  Qed.



 (*  Fixpoint _row_pre `{!probblazeRGS Σ} 
       (μ : list mode) 
       (ξ : (list (sem_row Σ)) )
       (eff : eff_sig → sem_sig Σ) 
       (f : (list mode) → list (sem_row Σ) → (eff_sig → sem_sig Σ) → row → sem_row Σ → sem_row Σ) `{∀ μ ξ eff ρ, Contractive (f μ ξ eff ρ)}
       (ρ : row) : sem_row Σ :=
       match ρ with
       | RNil => ⊥
       | RVar i => ξ !!! i
       | RFlip m ρ => sem_row_flip_mbang (_mode μ m) (_row_pre μ ξ eff f ρ)
       | RCons e ρ => sem_row_cons (eff e) (_row_pre μ ξ eff f ρ)
       | RRec ρ => sem_row_rec (f μ ξ eff ρ)
       end. 
     
     Lemma wf_row_contractive `{!probblazeRGS Σ} ρ μ ξ eff
       (f : (list mode) → list (sem_row Σ) → (eff_sig → sem_sig Σ) → row → sem_row Σ → sem_row Σ)
    `{∀ μ ξ eff ρ, Contractive (f μ ξ eff ρ)} `{wf_row 0 ρ} : Contractive (λ ρ', _row_pre μ (ρ' :: ξ) eff f ρ).
     Proof. 
       intros ????. 
       induction ρ.
       - done.
       - simpl. f_equiv. simpl in wf_row0. by apply IHρ.
       - simpl. simpl in wf_row0. admit. 
       - simpl. f_equiv. by apply IHρ.
       - simpl. (* simpl. apply IHρ. done. *) admit.
     Admitted. 
    
     Lemma contractive_test `{!probblazeRGS Σ} μ ξ eff ρ : Contractive (λ f, _row_pre μ ξ eff f ρ).
    
     Definition _row_pre_fix `{wf_row 0 ρ} μ ξ eff := fixpoint (λ f, _row_pre μ ξ eff f ρ).
    
     (* TODO: construct a contractive constructor for SemRow *)
     Definition sem_row_rec1 {Σ} (C : sem_row Σ -n> sem_row Σ) (rec : sem_row Σ) : sem_row Σ :=
       SemRow (sem_row_car (C rec))%I _.
     Global Instance lrel_rec1_contractive C : Contractive (lrel_rec1 C).
     Proof.
       intros n. intros P Q HPQ.
       unfold lrel_rec1. intros w1 w2. rewrite {1 4}/lrel_car /=.
       f_contractive. f_equiv. by apply C.
     Qed.
    
     Definition sem_row_rec_pre {Σ} (C : sem_row Σ → sem_row Σ)
       (rec : sem_row Σ) : sem_row Σ := (λ v1 v2, ▷ (∃ rec', rec ≡ rec' ∧ C rec' v1 v2))%I.
     Global Instance sem_ty_rec_pre_contractive {Σ} (C : sem_ty Σ → sem_ty Σ) :
       Contractive (sem_ty_rec_pre C).
     Proof. solve_contractive. Qed. *)

  (* TODO: figure out  *)
  (* From Equations Require Import Equations. *)

  (* We use 'struct' to tell Equations this is standard structural recursion. *)
  (* Equations _eff_sig `{!probblazeRGS Σ}
       (n : list (sem_ty Σ)) (ξ : list (sem_row Σ)) (μ : list mode) 
       (δ : gmap eff_name (label * label)) (σ : eff_sig) (Hwf : wf_eff_sig σ) : sem_sig Σ :=
     
       _eff_sig n ξ μ δ (SSig s α β) Hwf :=
         sem_sig_eff (δ !!! s).1 (δ !!! s).2 
           (λ τ', _ty (τ' :: n) ξ μ δ α _) 
           (λ τ', _ty (τ' :: n) ξ μ δ β _) ;
     
       _eff_sig n ξ μ δ (SFlip m e) Hwf :=
         sem_sig_flip_mbang (_mode μ m) (_eff_sig n ξ μ δ e _)
     
     where _row `{!probblazeRGS Σ}
             (n : list (sem_ty Σ)) (ξ : list (sem_row Σ)) (μ : list mode)
             (δ : gmap eff_name (label * label)) (ρ : row) (Hwf : wf_row v ρ) : sem_row Σ :=
     
       _row n ξ μ δ RNil Hwf := ⊥ ;
     
       _row n ξ μ δ (RVar i) Hwf := ξ !!! i ;
     
       _row n ξ μ δ (RFlip m ρ) Hwf := 
         sem_row_flip_mbang (_mode μ m) (_row n ξ μ δ ρ _) ;
     
       _row n ξ μ δ (RCons e ρ) Hwf := 
         sem_row_cons (_eff_sig n ξ μ δ e _) (_row n ξ μ δ ρ _) ;
     
       _row n ξ μ δ (RRec ρ') Hwf := 
         let f := _row in _ ;
     
     where _ty `{!probblazeRGS Σ}
             (n : list (sem_ty Σ)) (ξ : list (sem_row Σ)) (μ : list mode)
             (δ : gmap eff_name (label * label)) (τ : type) (Hwf : wf_type τ) : sem_ty Σ :=
     
       _ty n ξ μ δ TBot Hwf     := ⊥ ;
     
       _ty n ξ μ δ TTop Hwf     := ⊤ ;
     
       _ty n ξ μ δ TUnit Hwf    := sem_ty_unit ;
     
       _ty n ξ μ δ TInt Hwf     := sem_ty_int ;
     
       _ty n ξ μ δ TNat Hwf     := sem_ty_nat ;
     
       _ty n ξ μ δ TBool Hwf    := sem_ty_bool ;
     
       
     
       _ty n ξ μ δ (TVar i) Hwf := n !!! i. *)

  Program Definition  _row_pre `{!probblazeRGS Σ}
    (n : list (sem_ty Σ))
    (ξ : list (sem_row Σ))
    (μ : list mode)
    (δ : gmap eff_name (label * label))
    (ρ : row)
    `(Hwf : wf_row v ρ) f_sig
    ( Hpair : 
      { f_row |  ∀ n' ξ' μ' δ' ρ'' v' (Hwf' : ∀ {v1 ρ1}, wf_row v1 ρ1),  ∀ n, Proper ((@dist_later _ _ list_dist n) ==> (@dist _ _ sem_row_dist n)) (λ ξ'', f_row n' (ξ'' ++ ξ') μ' δ' ρ'' (v' + (length ξ'')) (@Hwf' (v' + (length ξ'')) ρ'')) } )
    (* `(Hcont :∀ n' ξ' μ' δ' ρ'' v' Hwf',  ∀ n, Proper ((@dist_later _ _ sem_row_dist n) ==> (@dist _ _ sem_row_dist n)) (λ ρ', f_row n' (ρ' :: ξ') μ' δ' ρ'' (v' + 1) Hwf')) *)
    : sem_row Σ :=
     let (f_row, Hcontr) := Hpair in
         match ρ with
         | RNil => ⊥
         | RVar i => ξ !!! i
         | RFlip m ρ => sem_row_flip_mbang (_mode μ m) (f_row n ξ μ δ ρ v (wf_row_RFlip v m ρ _))
         | RCons e ρ => sem_row_cons (f_sig n ξ μ δ e (wf_row_eff_sig v ρ e _)) (f_row n ξ μ δ ρ v (wf_row_RCons v e ρ _))
         | RRec ρ' => @sem_row_rec Σ (λ ρ'', f_row n (ρ'' :: ξ) μ δ ρ' (v + 1) (wf_row_RRec v ρ' Hwf)) _
         end.
  Next Obligation. intros; by subst. Defined.
  Next Obligation. intros; by subst. Defined.
  Next Obligation. intros; by subst. Defined.
  Next Obligation. intros; subst. Admitted. (* intros. subst. apply Hwf. Defined. *)
  Next Obligation. Admitted.
 (*    intros. simpl.  subst.
       intros x y Hdist.
       eapply Hcontr. constructor.
       intros ??. f_equiv. 
       by apply Hdist.
    Defined. *)

  Local Instance contractive_row_pre `{!probblazeRGS Σ} f_sig
  {Hprop : ∀ n' μ' δ' e' Hwf', ∀ n, Proper (@dist _ _ list_dist n ==> @dist _ _ sem_sig_dist n) (λ ξ', f_sig n' ξ' μ' δ' e' Hwf')}

  ( Hpair : 
    { f_row |  ∀ n' μ' δ' ρ'' v' Hwf',  ∀ n, Proper ((@dist_later _ _ list_dist n) ==> (@dist _ _ sem_row_dist n)) (λ ξ', f_row n' ξ' μ' δ' ρ'' (v' + 1) Hwf') } )
    (* `(Hcont :  ∀ n' ξ' μ' δ' ρ'' v' Hwf', 
         ∀ n, Proper ((@dist_later _ _ sem_row_dist n) ==> (@dist _ _ sem_row_dist n)) 
                (λ ρ', f_row n' (ρ' :: ξ') μ' δ' ρ'' (v' + 1) Hwf')) *)
  n' μ δ ρ `(Hwf : wf_row (v + 1) ρ) : 
    ∀ n, Proper ((@dist_later _ _ list_dist n) ==> (@dist _ _ sem_row_dist n)) (λ ξ', @_row_pre Σ _ n' ξ' μ δ ρ (v + 1) Hwf f_sig Hpair).
  Proof.
    generalize dependent v. destruct Hpair as (f_row&Hcontr).
    induction ρ; intros ??????; simpl; try done.
    - apply sem_row_cons_contractive.
      + destruct n; first apply dist_later_0. 
        apply dist_later_S in H. apply dist_later_S. 
        by apply Hprop.
      + by eapply Hcontr.
    - simpl in Hwf. assert (v ≠ 0) as Hneq by lia. rewrite !lookup_total_cons_ne_0; try done.
    - f_equiv. by eapply Hcontr. 
    - apply fixpoint_ne. intros ρ'.
      

f_equiv.  rewrite sem_row_rec_unfold. 
      erewrite (sem_row_rec_unfold (λ ρ'', f_row n' (ρ'' :: y :: ξ) _ _ _ _ _)).
      
      (* eapply Hcont. *)
admit.
  Admitted.    

  (* Inductive contractive_row_fix `{!probblazeRGS Σ} f_sig  n' ξ μ δ ρ `(Hwf : wf_row v ρ) : 
       ∀ n, Proper ((@dist_later _ _ sem_row_dist n) ==> (@dist _ _ sem_row_dist n)) (λ ρ', _row_pre n' (ρ' :: ξ) μ δ ρ Hwf f_sig contractive_row_fix). *)

  Definition type_row_interp := ∀ `{probblazeRGS Σ},
      list (sem_ty Σ)
      → list (sem_row Σ)
      → list mode
      → gmap eff_name (label * label)
      → ∀ (ρ : row) {v : nat},
          wf_row v ρ
          → (list (sem_ty Σ) → list (sem_row Σ) → list mode → gmap eff_name (label * label) → ∀ x3 : eff_sig, wf_eff_sig x3 → sem_sig Σ)
          → sem_row Σ.
  
  Fixpoint _row_pre2 `{probblazeRGS Σ} (n : list (sem_ty Σ)) (ξ : list (sem_row Σ)) (μ : list mode) 
    (δ : gmap eff_name (label*label))
    (ρ : row) (v : nat) (Hwf : wf_row v ρ) 
    (f_sig : (list (sem_ty Σ) → list (sem_row Σ) 
              → list mode → gmap eff_name (label * label) → ∀ x3 : eff_sig, wf_eff_sig x3 → sem_sig Σ)) :
 { X : (sem_row Σ) → sem_row Σ
 | (* (∀ n', Proper ((@dist_later _ _ sem_row_dist n') ==> @dist _ _ sem_row_dist n') (λ ρ', X  (ρ' :: ξ))) *)
   Contractive X  }. 
  Proof. 
    set f := (λ n ξ μ δ ρ v Hwf,  _row_pre2 Σ H n ξ μ δ ρ v Hwf f_sig).
    eexists ((λ ρ'' : sem_row Σ, @_row_pre Σ H n (ρ'' :: ξ) μ δ ρ v Hwf f_sig f)).
    eapply contractive_row_pre.
    Unshelve.
    2 : { apply f. 

    unshelve esplit.
    - unfold type_row_interp. intros.
      destruct (_row_pre2 Σ0 H0 X X0 H1 H2 ρ0 v0 H3 X1) as (_row_pre2'&Hcontr).
      apply (_row_pre2' Σ0 H0 X X0 H1 H2 ρ0 v0 H3 X1).
    - simpl. destruct (_row_pre2 Σ H n ξ μ δ ρ v Hwf f_sig) as (?&Hcontr).
      apply Hcontr.
      unshelve eapply _row_pre; try done.
      + intros. eapply _row_pre2; try done.
      + intros ???????. simpl. admit.
    - simpl. admit.
  Admitted.         

  
  Program Fixpoint _eff_sig `{!probblazeRGS Σ}
    (n : list (sem_ty Σ))
    (ξ : list (sem_row Σ))
    (μ : list mode) 
    (δ : gmap eff_name (label * label))
    (σ : eff_sig)
    (Hwf : wf_eff_sig σ) : sem_sig Σ :=
    match σ with
    | SSig s α β =>
        sem_sig_eff (δ !!! s).1 (δ !!! s).2 ((λ τ', _ty (τ' :: n) ξ μ δ α (wf_eff_sig_SSig_1 s α β _))) (λ τ', _ty (τ' :: n) ξ μ δ β (wf_eff_sig_SSig_2 s α β _))
    | SFlip m e =>
        sem_sig_flip_mbang (_mode μ m) (_eff_sig n ξ μ δ e (wf_eff_sig_SFlip m e _))
    end 
  with _row `{H : probblazeRGS Σ}
    (n : list (sem_ty Σ))
    (ξ : list (sem_row Σ))
    (μ : list mode)
    (δ : gmap eff_name (label * label))
    (ρ : row)
    `(Hwf : wf_row v ρ) : sem_row Σ := let (f, _) := _row_pre2 n ξ μ δ ρ v Hwf _eff_sig in f Σ H n ξ μ δ ρ v Hwf _eff_sig
  with _ty `{!probblazeRGS Σ}
    (n : list (sem_ty Σ))
    (ξ : list (sem_row Σ))
    (μ : list mode)
    (δ : gmap eff_name (label * label))
    (τ : type)
    (Hwf : wf_type τ) : sem_ty Σ :=
         match τ with
         | TBot => ⊥
         | TTop => ⊤
         | TUnit => sem_ty_unit
         | TInt => sem_ty_int
         | TNat => sem_ty_nat
         | TBool => sem_ty_bool
         | TTape => sem_ty_tape
         | TRef τ => sem_ty_ref (_ty n ξ μ δ τ _)
         | TProd τ1 τ2 => sem_ty_prod (_ty n ξ μ δ τ1 _) (_ty n ξ μ δ τ2 _)
         | TSum τ1 τ2 => sem_ty_sum (_ty n ξ μ δ τ1 _) (_ty n ξ μ δ τ2 _)
         | TBang m τ => sem_ty_mbang (_mode μ m) (_ty n ξ μ δ τ _)
         | TArrow α ρ β => sem_ty_arr (_row n ξ μ δ ρ (wf_type_row α ρ β _)) (_ty n ξ μ δ α _) (_ty n ξ μ δ β _)
         | TForallM τ => sem_ty_mode_forall (λ m, _ty n ξ (m :: μ) δ τ _)
         | TForallR τ => sem_ty_row_forall (λ ρ, _ty n (ρ :: ξ) μ δ τ _)
         | TForallT τ => sem_ty_type_forall (λ τ', _ty (τ' :: n) ξ μ δ τ _)
         | TExists τ => sem_ty_exists (λ τ', _ty (τ' :: n) ξ μ δ τ _)
         | TRec τ => sem_ty_rec (λ τ', _ty (τ' :: n) ξ μ δ τ _)
         | TVar i => n !!! i
         end.
  Solve Obligations of _eff_sig with (intros; by subst). 
  Solve Obligations of _ty with (intros; subst; repeat (done || destruct Hwf || destruct H0)). 
  

Next Obligation. intros; subst. destruct Hwf.
  Next Obligation of _ty. intros; subst. destruct Hwf. Defined.
  Next Obligation of _ty. intros; subst. by destruct Hwf. Defined.
  Next Obligation of _ty. intros; simplify_eq. simpl in *. by destruct Hwf. Defined.
  Next Obligation of _ty. intros; simplify_eq. simpl in *. by destruct Hwf. Defined.
  Next Obligation of _ty. intros; simplify_eq. simpl in *. by destruct Hwf. Defined.
  Next Obligation of _ty. intros; simplify_eq. by simpl in *. Defined.
  Next Obligation of _ty. intros; simplify_eq. simpl in *. by destruct Hwf. Defined.
  Next Obligation of _ty. intros; simplify_eq. simpl in *. by destruct Hwf. Defined.
  Next Obligation of _ty. intros; simplify_eq. simpl in *. destruct Hwf. by destruct H0. Defined.
  Next Obligation of _ty. intros; simplify_eq. by simpl in *. Defined.
  Next Obligation of _ty. intros; simplify_eq. by simpl in *. Defined.
  Next Obligation of _ty. intros; simplify_eq. by simpl in *. Defined.
  Next Obligation of _ty. intros; simplify_eq. by simpl in *. Defined.
  Next Obligation of _ty. intros; simplify_eq. by simpl in *. Defined.


  Program Fixpoint _eff_sig `{!probblazeRGS Σ}
    (n : list (sem_ty Σ))
    (ξ : list (sem_row Σ))
    (μ : list mode) 
    (δ : gmap eff_name (label * label))
    (σ : eff_sig)
    (Hwf : wf_eff_sig σ) : sem_sig Σ :=
    match σ with
    | SSig s α β =>
        sem_sig_eff (δ !!! s).1 (δ !!! s).2 ((λ τ', _ty (τ' :: n) ξ μ δ α (wf_eff_sig_SSig_1 s α β _))) (λ τ', _ty (τ' :: n) ξ μ δ β (wf_eff_sig_SSig_2 s α β _))
    | SFlip m e =>
        sem_sig_flip_mbang (_mode μ m) (_eff_sig n ξ μ δ e (wf_eff_sig_SFlip m e _))
    end 
  with _row `{!probblazeRGS Σ}
    (n : list (sem_ty Σ))
    (ξ : list (sem_row Σ))
    (μ : list mode)
    (δ : gmap eff_name (label * label))
    (ρ : row)
    `(Hwf : wf_row v ρ) : sem_row Σ :=
         match ρ with
         | RNil => ⊥
         | RVar i => ξ !!! i
         | RFlip m ρ => sem_row_flip_mbang (_mode μ m) (_row n ξ μ δ ρ (wf_row_RFlip v m ρ _))
         | RCons e ρ => sem_row_cons (_eff_sig n ξ μ δ e (wf_row_eff_sig v ρ e _)) (_row n ξ μ δ ρ (wf_row_RCons v e ρ _))
         | RRec ρ' => let f := _row in _
         end 
  with _ty `{!probblazeRGS Σ}
    (n : list (sem_ty Σ))
    (ξ : list (sem_row Σ))
    (μ : list mode)
    (δ : gmap eff_name (label * label))
    (τ : type)
    (Hwf : wf_type τ) : sem_ty Σ :=
         match τ with
         | TBot => ⊥
         | TTop => ⊤
         | TUnit => sem_ty_unit
         | TInt => sem_ty_int
         | TNat => sem_ty_nat
         | TBool => sem_ty_bool
         | TTape => sem_ty_tape
         | TRef τ => sem_ty_ref (_ty n ξ μ δ τ _)
         | TProd τ1 τ2 => sem_ty_prod (_ty n ξ μ δ τ1 _) (_ty n ξ μ δ τ2 _)
         | TSum τ1 τ2 => sem_ty_sum (_ty n ξ μ δ τ1 _) (_ty n ξ μ δ τ2 _)
         | TBang m τ => sem_ty_mbang (_mode μ m) (_ty n ξ μ δ τ _)
         | TArrow α ρ β => sem_ty_arr (_row n ξ μ δ ρ (wf_type_row α ρ β _)) (_ty n ξ μ δ α _) (_ty n ξ μ δ β _)
         | TForallM τ => sem_ty_mode_forall (λ m, _ty n ξ (m :: μ) δ τ _)
         | TForallR τ => sem_ty_row_forall (λ ρ, _ty n (ρ :: ξ) μ δ τ _)
         | TForallT τ => sem_ty_type_forall (λ τ', _ty (τ' :: n) ξ μ δ τ _)
         | TExists τ => sem_ty_exists (λ τ', _ty (τ' :: n) ξ μ δ τ _)
         | TRec τ => sem_ty_rec (λ τ', _ty (τ' :: n) ξ μ δ τ _)
         | TVar i => n !!! i
         end.
  Next Obligation. intros. by subst. Defined.
  Next Obligation. intros; by subst. Defined.
  Next Obligation of _eff_sig. intros; by subst. Defined.
  Next Obligation of _ty. intros; by subst. Defined.
  Next Obligation of _ty. intros; simplify_eq. simpl in *. by destruct Hwf. Defined.
  Next Obligation of _ty. intros; simplify_eq. simpl in *. by destruct Hwf. Defined.
  Next Obligation of _ty. intros; simplify_eq. simpl in *. by destruct Hwf. Defined.
  Next Obligation of _ty. intros; simplify_eq. simpl in *. by destruct Hwf. Defined.
  Next Obligation of _ty. intros; simplify_eq. by simpl in *. Defined.
  Next Obligation of _ty. intros; simplify_eq. simpl in *. by destruct Hwf. Defined.
  Next Obligation of _ty. intros; simplify_eq. simpl in *. by destruct Hwf. Defined.
  Next Obligation of _ty. intros; simplify_eq. simpl in *. destruct Hwf. by destruct H0. Defined.
  Next Obligation of _ty. intros; simplify_eq. by simpl in *. Defined.
  Next Obligation of _ty. intros; simplify_eq. by simpl in *. Defined.
  Next Obligation of _ty. intros; simplify_eq. by simpl in *. Defined.
  Next Obligation of _ty. intros; simplify_eq. by simpl in *. Defined.
  Next Obligation of _ty. intros; simplify_eq. by simpl in *. Defined.
  Next Obligation. intros; by subst. Defined.
  Next Obligation. intros; by subst. Defined.
  Next Obligation. intros; by subst. Defined.
  Next Obligation. 
    intros. 
    unshelve eapply (sem_row_rec (λ ρ'', _row _ _ n (ρ'' :: ξ) μ δ ρ' _ (wf_row_RRec v ρ' _))); [done|by subst|subst].
    intros. intros ???. induction ρ'; simpl.
    - Set Transparent _row. unfold _row.
    

f_equiv.
    induction ρ'; simpl.
    - 
    
f_equiv.
  Defined.
 

  

  
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
         | TArrow α ρ β => sem_ty_arr (_row_pre μ ξ (_eff_sig n ξ μ δ) (_ty n ξ μ δ) (_row_pre μ ξ  ρ) (_ty n ξ μ δ α) (_ty n ξ μ δ β)
         | TForallM τ => sem_ty_mode_forall (λ m, _ty n ξ (m :: μ) δ τ)
         | TForallR τ => sem_ty_row_forall (λ ρ, _ty n (ρ :: ξ) μ δ τ)
         | TForallT τ => sem_ty_type_forall (λ τ', _ty (τ' :: n) ξ μ δ τ)
         | TExists τ => sem_ty_exists (λ τ', _ty (τ' :: n) ξ μ δ τ)
         | TRec τ => sem_ty_rec (λ τ', _ty (τ' :: n) ξ μ δ τ)
         | TVar i => n !!! i
         end.


  Definition _env `{!probblazeRGS Σ}
    (η : list (sem_ty Σ))
    (ξ : list (sem_row Σ))
    (μ : list mode)
    (δ : gmap eff_name (label * label))
    (Γ : ctx) : env Σ :=
    (λ '(x, τ), (x, _ty η ξ μ δ τ)) <$> Γ.



End interp.

Notation "⟦ Γ ⟧*" := (env_sem_typed Γ).
Notation "V⟦ η ; ξ ; μ ; δ ; α ⟧" := (interp._ty      η ξ μ δ α).
Notation "R⟦ η ; ξ ; μ ; δ ; ρ ⟧" := (interp._row     η ξ μ δ ρ).
Notation "S⟦ η ; ξ ; μ ; δ ; σ ⟧" := (interp._eff_sig η ξ μ δ σ).

Module interp_le.

  (* Interpretation of a disjointness context. *)
  Definition _disj_ctx `{!probblazeRGS Σ}
    (η : list (sem_ty Σ))
    (ξ : list (sem_row Σ))
    (μ : list mode)
    (δ : gmap eff_name (label * label))
    (D : le.disj_ctx) : iProp Σ :=
    (* the labels  *)
    logic.valid ((λ '(l1,l2), ([l1],[l2], ⊥)) <$> ((δ !!!.) <$> (elements (dom D)))).
    (* valid, i.e. allocated*)
    labeled_effects.Eff
      ((δ !!!.) <$> (elements (dom D))) ∗
    (* distinct from ss (eff_names) and js (row vars) *)
    ⌜ map_Forall (λ (s : eff_name) '(ss, js),
        (δ !!! s) ∉ ((δ !!!.) <$> (elements ss)) ∧
        (δ !!! s) ∉ R⟦ η ; ξ ; δ ; RVar <$> elements js ⟧.*1
      ) D ⌝.



