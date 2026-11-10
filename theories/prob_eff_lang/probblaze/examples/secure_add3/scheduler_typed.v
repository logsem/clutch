From Autosubst Require Import Autosubst.
From clutch.prob_eff_lang.probblaze Require Import syntax semantics notation.
From clutch.prob_eff_lang.probblaze.typing Require Import types.

(** A syntactically typed environment that acts as a scheduler.

    [Zsched] receives a re-entrant scenario [R], starts two sessions, sets both
    aside when they wait, and resumes them in the order they were started --
    not last-in-first-out, which is all an environment can do by nesting.

    A session is set aside by returning its continuation from the handler
    clause instead of resuming it: a paused session is the value [InjR k],
    a finished one [InjL v].  Holding two paused sessions at once relies on
    [Let_typed]. *)

(* A paused or finished session.  The continuation's row is empty: its
   effects on Z's own label are handled by the deep handler it captured. *)
Definition St : type := (μ: (() + ![OS] (() -∘ TVar 0)))%ty.

(* The scenario: given a client that may perform effects [θ], it runs with
   effects [θ]. *)
Definition T : type := (∀R: ((() -{ RVar 0 }-> ()) -{ RVar 0 }-> ()))%ty.

Definition Zsched : val :=
  λ: "R",
    effect "w"
    let: "run" := (λ: <>,
      handle: "R" (λ: <>, do: "w" #()%V) with
      | effect "w" <>, rec "k" => InjR "k"
      | return <> => InjL #()%V
      end) in
    let: "step" := (λ: "s",
      match: rec_unfold "s" with
        InjL <> => InjL #()%V
      | InjR "k" => "k" #()%V
      end) in
    let: "s1" := "run" #()%V in
    let: "s2" := "run" #()%V in
    let: "s1" := "step" "s1" in
    let: "s2" := "step" "s2" in
    #true.

(* Rows and types used in the derivation. *)
Local Notation ρZ := (RCons (SAbs "w") RNil).
Local Notation ρw := (RCons (SFlip syntax.OS (SSig "w" TUnit TUnit)) RNil).
Local Notation RunT := (() ⇾ St)%ty.
Local Notation StepT := (St ⇾ St)%ty.

(* Small derived rules for building the derivation below. *)

Ltac solve_fresh :=
  first [ done | intros []
        | unfold ctx_dom; simpl; unfold elem_of, elem_binder_string; set_solver ].

Ltac once_nil := constructor; exists true; apply le.RFlipNil_le.

(* [![m] (τ -{ RCons (SAbs s) RNil }-∘ κ) ≤ ![m] (τ -∘ κ)], in a context whose
   row contains the (absent) signature of [s]. *)
Ltac erase_absent :=
  eapply le.TBangComp_le; [apply le.MRefl_le|];
  eapply (le.TArrow_le _ _ _ _ _ _ _ true); [apply le.TRefl_le| |apply le.TRefl_le];
  eapply le.RErase_le; [vm_compute; reflexivity|done|done].

Lemma typed_perm Δ Γ Γ' e ρ τ Γ2 :
  Γ ≡ₚ Γ' →
  Δ .| Γ' ⊢ₜ e : ρ : τ ⊣ Γ2 → Δ .| Γ ⊢ₜ e : ρ : τ ⊣ Γ2.
Proof.
  intros Hp He.
  eapply (Sub_typed _ _ Γ' _ Γ2 _ ρ false _ τ); [|apply CRefl_le|apply RRefl_le|apply le.TRefl_le|done].
  by eapply _ctx_perm_right; [apply CRefl_le|].
Qed.

Lemma typed_perm_out Δ Γ e ρ τ Γ2 Γ2' :
  Γ2' ≡ₚ Γ2 →
  Δ .| Γ ⊢ₜ e : ρ : τ ⊣ Γ2' → Δ .| Γ ⊢ₜ e : ρ : τ ⊣ Γ2.
Proof.
  intros Hp He.
  eapply (Sub_typed _ _ Γ _ Γ2' _ ρ false _ τ); [apply CRefl_le| |apply RRefl_le|apply le.TRefl_le|done].
  by eapply _ctx_perm_right; [apply CRefl_le|].
Qed.

Lemma typed_row_cons Δ Γ e σ τ Γ2 :
  Δ .| Γ ⊢ₜ e : RNil : τ ⊣ Γ2 → Δ .| Γ ⊢ₜ e : RCons σ RNil : τ ⊣ Γ2.
Proof.
  intros He.
  eapply (Sub_typed _ _ Γ _ Γ2 _ RNil true _ τ); [apply CRefl_le|apply CRefl_le|apply le.RExtend_le|apply le.TRefl_le|done].
Qed.

Lemma typed_val_row Δ Γ v σ τ :
  ⊢ᵥ v : τ → Δ .| Γ ⊢ₜ Val v : RCons σ RNil : τ ⊣ Γ.
Proof. intros Hv. by apply typed_row_cons, Val_typed. Qed.

(* Use a duplicable variable without consuming it. *)
Lemma typed_var_dup Δ (x : string) τ Γ :
  le.MultiT τ →
  Δ .| (x, τ) :: Γ ⊢ₜ Var x : RNil : τ ⊣ (x, τ) :: Γ.
Proof.
  intros Hτ. apply (Contraction_typed _ _ _ _ _ _ x τ Hτ). apply Var_typed.
Qed.

(* Strip the [!] of a variable's type when using it. *)
Lemma typed_var_bang Δ (x : string) (m : vmode) τ Γ :
  Δ .| (x, (![m] τ)%ty) :: Γ ⊢ₜ Var x : RNil : τ ⊣ Γ.
Proof.
  eapply (Sub_typed _ _ _ _ Γ _ RNil false _ (![m] τ)%ty);
    [apply CRefl_le|apply CRefl_le|apply RRefl_le|apply le.TBangElim_le|apply Var_typed].
Qed.

(* Use (and consume) a variable anywhere in the context. *)
Lemma typed_var_at Δ Γ Γ' (x : string) τ σ :
  Γ ≡ₚ (x, τ) :: Γ' →
  Δ .| Γ ⊢ₜ Var x : RCons σ RNil : τ ⊣ Γ'.
Proof. intros Hp. apply typed_row_cons. eapply typed_perm; [done|apply Var_typed]. Qed.

(* Call a function variable [f : τ ⇾ κ] without consuming it.  Its row is
   empty, so other (possibly affine) variables may be in scope. *)
Lemma typed_call Δ Γ1 Γ2 (f : string) e τ κ σ :
  (f, (τ ⇾ κ)%ty) ∈ Γ2 →
  Δ .| Γ1 ⊢ₜ e : RCons σ RNil : τ ⊣ Γ2 →
  Δ .| Γ1 ⊢ₜ App (Var f) e : RCons σ RNil : κ ⊣ Γ2.
Proof.
  intros Hin He.
  apply list_elem_of_split in Hin as (l1 & l2 & ->).
  assert (Hp : l1 ++ (f, (τ ⇾ κ)%ty) :: l2 ≡ₚ (f, (τ ⇾ κ)%ty) :: l1 ++ l2)
    by by rewrite -Permutation_middle.
  eapply (App_typed _ _ _ _ _ _ _ RNil RNil true τ κ);
    [apply le.RExtend_le|apply le.RExtend_le|once_nil|apply RNil_le_ctx|exact He|].
  eapply typed_perm; [exact Hp|]. eapply typed_perm_out; [symmetry; exact Hp|].
  eapply (Sub_typed _ _ _ _ _ _ RNil false _ (τ ⇾ κ)%ty);
    [apply CRefl_le|apply CRefl_le|apply RRefl_le|apply le.TBangElim_le|].
  apply typed_var_dup, le.TBangIdemp1_le.
Qed.

Lemma T_multi : le.MultiT T.
Proof.
  rewrite /le.MultiT /T /=. eapply le.TTrans_le;
    [apply le.TForallR_le, le.TBangIdemp1_le|apply le.TBangTForallRComm2_le].
Qed.

Lemma Zsched_typed : ⊢ᵥ Zsched : (T ⇾ 𝔹).
Proof.
  apply Rec_val_typed; first done. simpl.
  eapply Effect_typed; first (compute; set_solver).
  (* [run]: typed with Z's (absent) label [w] in its row, which is then
     erased from its arrow type, so calling it later is one-shot-safe. *)
  eapply (Let_typed _ _ [] _ _ _ _ _ RunT); [solve_fresh|solve_fresh| |].
  { eapply (Sub_typed _ _ [("R", T)] _ [] _ RNil true _ (() -{ ρZ }-> St)%ty);
      [apply CRefl_le|apply CRefl_le|apply le.RExtend_le|erase_absent|].
    rewrite -(app_nil_r [("R", T)]).
    eapply Rec_typed; [apply (le.ConsM_le _ "R"); [apply le.MS_le, T_multi|apply le.NilM_le]|solve_fresh|solve_fresh|].
    simpl. rewrite -(app_nil_r [("R", T)]).
    eapply (DeepHandle_typed _ _ [] [] syntax.OS "w" _ _ _ _ _ _ RNil (SAbs "w") TUnit St TUnit TUnit);
      [first [constructor | done | intros [] | vm_compute; reflexivity] .. | | |].
    - (* The session: [R] applied to a client that performs [w] one-shot. *)
      eapply (App_typed _ _ [("R", T)] [] _ _ _ RNil ρw true (() -{ ρw }-> ())%ty TUnit);
        [apply le.RExtend_le|apply RRefl_le|once_nil|constructor| |].
      + apply typed_row_cons. rewrite -(app_nil_l [("R", T)]).
        eapply Rec_typed; [constructor|solve_fresh|solve_fresh|]. simpl.
        eapply (Do_typed _ _ "w" _ RNil TUnit TUnit TUnit OS);
          [constructor|vm_compute; reflexivity|simpl; apply typed_val_row; constructor].
      + eapply (Sub_typed _ _ _ _ _ _ RNil true _ ((() -{ ρw }-> ()) -{ ρw }-> ())%ty);
          [apply CRefl_le|apply CRefl_le|apply le.RNil_le|apply le.TBangElim_le|].
        eapply (RAbsElim_typed _ _ _ _ _ ρw ((() -{ RVar 0 }-> ()) -{ RVar 0 }-> ())%ty).
        apply Var_typed.
    - (* Return clause: the session finished. *)
      simpl. rewrite /St. apply TFold. asimpl. apply InjL_typed. apply typed_val_row. constructor.
    - (* Effect clause: return [k] as a paused session.  Its row still
         mentions the absent [w]; erasing it gives [St], free of labels. *)
      rewrite /St. simpl. asimpl. apply TFold. asimpl. apply InjR_typed.
      eapply (Sub_typed _ _ _ _ [] _ RNil true);
        [apply CRefl_le|apply CRefl_le|apply le.RExtend_le| |apply Var_typed].
      erase_absent. }
  (* [step]: resume a paused session once. *)
  eapply (Let_typed _ _ [("run", RunT)] _ _ _ _ _ StepT); [solve_fresh|solve_fresh| |].
  { apply typed_row_cons. rewrite /ctx_insert -(app_nil_l [("run", RunT)]).
    eapply Rec_typed; [constructor|solve_fresh|done|]. simpl.
    eapply (Match_typed _ _ [] [] _ _ _ _ _ _ TUnit (![OS] (() -∘ St))%ty); [solve_fresh .. | | |].
    - eapply (TUnfold _ _ _ _ (() + ![OS] (() -∘ TVar 0))%ty). apply Var_typed.
    - simpl. rewrite /St. apply TFold. asimpl. apply InjL_typed. apply Val_typed. constructor.
    - eapply (App_typed _ _ [("k", (![OS] (() -∘ St))%ty)] [] _ _ _ RNil RNil true TUnit St);
        [apply RRefl_le|apply RRefl_le|once_nil|apply RNil_le_ctx|apply Val_typed; constructor|apply typed_var_bang]. }
  (* [s1 := run ()]. *)
  eapply (Let_typed _ _ [("step", StepT); ("run", RunT)] _ _ _ _ _ St); [solve_fresh|solve_fresh| |].
  { eapply typed_call; [|apply typed_val_row; constructor]. by repeat constructor. }
  (* [s2 := run ()] while [s1] is paused. *)
  eapply (Let_typed _ _ [("s1", St); ("step", StepT); ("run", RunT)] _ _ _ _ _ St); [solve_fresh|solve_fresh| |].
  { eapply typed_call; [|apply typed_val_row; constructor]. by repeat constructor. }
  (* Resume [s1] first, then [s2]: first-in-first-out. *)
  eapply (Let_typed _ _ [("s2", St); ("step", StepT); ("run", RunT)] _ _ _ _ _ St); [solve_fresh|solve_fresh| |].
  { eapply typed_call; [|eapply typed_var_at; solve_Permutation]. by repeat constructor. }
  eapply (Let_typed _ _ [("s1", St); ("step", StepT); ("run", RunT)] _ _ _ _ _ St); [solve_fresh|solve_fresh| |].
  { eapply typed_call; [|eapply typed_var_at; solve_Permutation]. by repeat constructor. }
  (* Drop the remaining sessions. *)
  eapply (Sub_typed _ _ [] _ [] _ RNil true _ 𝔹%ty);
    [exact I|exact I|apply le.RExtend_le|apply le.TRefl_le|apply Val_typed; constructor].
Qed.
