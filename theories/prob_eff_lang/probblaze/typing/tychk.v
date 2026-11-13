From Autosubst Require Import Autosubst.
From clutch.prob_eff_lang.probblaze Require Import syntax semantics notation.
From clutch.prob_eff_lang.probblaze.typing Require Import types.

(** * Algorithmic layer for the syntactic type system (PLAN.md, Stage C).

    - C1: side predicates of the typing rules ([le.MultiT], [le.MultiC],
      [m m⪯T τ], [m m⪯C Γ], [ρ R⪯T τ], [ρ R⪯C Γ], [le.OnceR]) as hints in
      the database [tychk]; entry point [tychk_side].
    - C2: context operations (lookup by name, delete, bring to front,
      weakening of input and output), all derived from [Sub_typed] with
      [CRefl_le], [_ctx_perm_left], [_ctx_perm_right], [CTrans_le].
    - C3: row subtyping: a normal form (signatures + atoms), the two
      round-trip lemmas, and the solver [row_le_solve] for
      [D ⊢ₗ ρ' ≤R ρ @ b].  Signatures are matched up to a fragment of [≤S]
      (reflexivity, flip idempotence, MS flip elimination/introduction,
      mode composition), atoms up to the same fragment of [≤R]; [SAbs]
      signatures are erased at flag [true] ([RErase_le]).  [le.OnceR] is
      solved through [row_le_solve].
    - Tests of C1-C3, including re-proofs of [typed_var_bang] and
      [typed_call] of examples/secure_add3/scheduler_typed.v from the
      lemmas and hints of this file only.
    - C4: one derived rule per construct in algorithmic form ([*_alg]),
      and the annotation wrappers [tyann], [sigann] (PLAN.md section 4).
    - Stage D: the driver [tychk] for [⊢ᵥ v : τ], [Δ .| Γ ⊢ₜ e : ρ : τ ⊣ Γ2]
      and [Δ ..| Γ ⊢ₚ e : τ]; smoke tests at the end, regression targets in
      typing/tychk_tests.v. *)

(* ================================================================== *)
(** * Basic tactics (verbatim from scheduler_typed.v:51-55)            *)
(* ================================================================== *)

Ltac solve_fresh :=
  first [ done | intros []
        | unfold ctx_dom; simpl; unfold elem_of, elem_binder_string; set_solver ].

Ltac once_nil := constructor; exists true; apply le.RFlipNil_le.

(* [erase_absent] (scheduler_typed.v:59) is subsumed by [row_le_solve] on
   the row premise of [le.TArrow_le] (see [test_erase_absent] in C3). *)

Create HintDb tychk.

(* ================================================================== *)
(** * C1: [le.MultiT]                                                  *)
(* ================================================================== *)

Lemma shift_disj_ctx_empty : le.shift_disj_ctx ∅ = ∅.
Proof. by rewrite /le.shift_disj_ctx fmap_empty. Qed.

(* Base types: τ ≤ ![MS] τ. *)
Lemma MultiT_bool : le.MultiT TBool.
Proof. apply le.TBangBool_le. Qed.
Lemma MultiT_unit : le.MultiT TUnit.
Proof. apply le.TBangUnit_le. Qed.
Lemma MultiT_int : le.MultiT TInt.
Proof. apply le.TBangInt_le. Qed.
Lemma MultiT_nat : le.MultiT TNat.
Proof. apply le.TBangNat_le. Qed.
Lemma MultiT_top : le.MultiT TTop.
Proof. apply le.TBangTop_le. Qed.
Lemma MultiT_bot : le.MultiT TBot.
Proof. apply le.TBot_le. Qed.

(* ![MS] τ ≤ ![MS] ![MS] τ.  This also covers [τ ⇾ κ] and [τ -{ρ}-> κ],
   which unfold to [TBang MS (TArrow _ _ _)]. *)
Lemma MultiT_bang τ : le.MultiT (![MS] τ)%ty.
Proof. apply le.TBangIdemp1_le. Qed.

(* α * β ≤ ![MS] α * ![MS] β ≤ ![MS] (α * β) *)
Lemma MultiT_prod α β :
  le.MultiT α → le.MultiT β → le.MultiT (α * β)%ty.
Proof.
  intros Hα Hβ. rewrite /le.MultiT.
  eapply le.TTrans_le;
    [apply le.TProd_le; [exact Hα|exact Hβ]|apply le.TBangProd1_le].
Qed.

Lemma MultiT_sum α β :
  le.MultiT α → le.MultiT β → le.MultiT (α + β)%ty.
Proof.
  intros Hα Hβ. rewrite /le.MultiT.
  eapply le.TTrans_le;
    [apply le.TSum_le; [exact Hα|exact Hβ]|apply le.TBangSum1_le].
Qed.

(* Quantified types.  [T_multi] of scheduler_typed.v is the instance
   [α := ![MS] _] of [MultiT_forallR].  [TForallR_le] shifts the
   disjointness context; the premise is stated at [∅], hence
   [shift_disj_ctx_empty]. *)
Lemma MultiT_forallR α : le.MultiT α → le.MultiT (TForallR α).
Proof.
  intros Hα. rewrite /le.MultiT.
  eapply le.TTrans_le;
    [apply le.TForallR_le; rewrite shift_disj_ctx_empty; exact Hα
    |apply le.TBangTForallRComm2_le].
Qed.

Lemma MultiT_forallT α : le.MultiT α → le.MultiT (TForallT α).
Proof.
  intros Hα. rewrite /le.MultiT.
  eapply le.TTrans_le;
    [apply le.TForallT_le, Hα|apply le.TBangTForallTComm2_le].
Qed.

(* No rule commutes [TBang] with [TForallM] / [TExists] / [TRec] / [TRef] /
   [TArrow] / [TTape] in types.v, so [MultiT] for those (and for type
   variables and abstract types) is left as a residual goal.  [∀M:] is the
   follow-up of PLAN.md section 10. *)

(* Copyable references are copyable whatever their payload
   ([TBangRefC_le], PLAN.md section 2). *)
Lemma MultiT_refc τ : le.MultiT (TRefC τ).
Proof. apply le.TBangRefC_le. Qed.

#[export] Hint Resolve MultiT_bool MultiT_unit MultiT_int MultiT_nat MultiT_top
     MultiT_bot MultiT_bang MultiT_prod MultiT_sum
     MultiT_forallR MultiT_forallT MultiT_refc : tychk.

(* ================================================================== *)
(** * C1: [le.MultiC]  ([Forall MultiT (snd <$> Γ)])                   *)
(* ================================================================== *)

Lemma MultiC_nil : le.MultiC [].
Proof. rewrite /le.MultiC. constructor. Qed.

Lemma MultiC_cons (x : string) τ Γ :
  le.MultiT τ → le.MultiC Γ → le.MultiC ((x, τ) :: Γ).
Proof.
  intros Hτ HΓ. rewrite /le.MultiC /=. constructor; [exact Hτ|exact HΓ].
Qed.

(* Same for the [<[ x :=c τ ]>] form ([x : binder]). *)
Lemma MultiC_insert (x : binder) τ Γ :
  le.MultiT τ → le.MultiC Γ → le.MultiC (<[ x :=c τ ]> Γ).
Proof. intros Hτ HΓ. destruct x; [exact HΓ|by apply MultiC_cons]. Qed.

Lemma MultiC_app Γ1 Γ2 :
  le.MultiC Γ1 → le.MultiC Γ2 → le.MultiC (Γ1 ++ Γ2).
Proof.
  rewrite /le.MultiC fmap_app. intros H1 H2. by apply Forall_app.
Qed.

Lemma MultiC_ctx_append Γ1 Γ2 :
  le.MultiC Γ1 → le.MultiC Γ2 → le.MultiC (Γ1 ;; Γ2).
Proof. apply MultiC_app. Qed.

(* Use a [MultiC] hypothesis on one entry. *)
Lemma MultiC_elem (x : string) τ Γ :
  le.MultiC Γ → (x, τ) ∈ Γ → le.MultiT τ.
Proof.
  rewrite /le.MultiC Forall_forall. intros H Hin. apply H.
  apply list_elem_of_fmap. exists (x, τ). split; [done|exact Hin].
Qed.

#[export] Hint Resolve MultiC_nil MultiC_cons MultiC_insert MultiC_app
     MultiC_ctx_append : tychk.

(* ================================================================== *)
(** * C1: [m m⪯T τ], [m m⪯C Γ]                                         *)
(* ================================================================== *)

Lemma mode_type_OS τ : OS m⪯T τ.
Proof. apply le.OS_le. Qed.
Lemma mode_type_MS τ : le.MultiT τ → MS m⪯T τ.
Proof. apply le.MS_le. Qed.

Lemma mode_ctx_nil m : m m⪯C [].
Proof. apply le.NilM_le. Qed.

Lemma mode_ctx_insert m (x : binder) τ Γ :
  m m⪯T τ → m m⪯C Γ → m m⪯C (<[ x :=c τ ]> Γ).
Proof. intros. by apply le.ConsM_le. Qed.

Lemma mode_ctx_cons m (x : string) τ Γ :
  m m⪯T τ → m m⪯C Γ → m m⪯C ((x, τ) :: Γ).
Proof.
  intros. change ((x, τ) :: Γ) with (<[ BNamed x :=c τ ]> Γ).
  by apply le.ConsM_le.
Qed.

Lemma mode_ctx_app m Γ1 Γ2 :
  m m⪯C Γ1 → m m⪯C Γ2 → m m⪯C (Γ1 ++ Γ2).
Proof.
  induction 1 as [|m' x τ Γ Hτ HΓ IH]; intros H2; [done|].
  destruct x as [|x]; simpl; [by apply IH|].
  apply mode_ctx_cons; [done|by apply IH].
Qed.

Lemma mode_ctx_ctx_append m Γ1 Γ2 :
  m m⪯C Γ1 → m m⪯C Γ2 → m m⪯C (Γ1 ;; Γ2).
Proof. apply mode_ctx_app. Qed.

(* OS needs nothing of the context; MS reduces to [MultiT] entrywise.  A mode
   variable [MVar i] is a residual goal. *)
#[export] Hint Resolve mode_type_OS mode_type_MS mode_ctx_nil
     mode_ctx_cons mode_ctx_insert mode_ctx_app mode_ctx_ctx_append : tychk.

(* If the mode is MS the context is MultiC. *)
Lemma mode_ctx_MS_of_MultiC Γ : le.MultiC Γ → MS m⪯C Γ.
Proof.
  induction Γ as [|[x τ] Γ IH]; intros HΓ; [apply mode_ctx_nil|].
  inversion HΓ as [|? ? Hτ HΓ']; subst.
  apply mode_ctx_cons; [by apply mode_type_MS|by apply IH].
Qed.

(* ================================================================== *)
(** * C1: [ρ R⪯T τ], [ρ R⪯C Γ]  ([le.OnceR] is solved in C3)          *)
(* ================================================================== *)

(* [OnceR ρ := ∃ b, ∅ ⊢ ¡[OS] ρ ≤R ρ @ b].  The general solver
   [once_solve] (C3, below) normalises [¡[OS] ρ]; this is the base case. *)
Lemma OnceR_nil : le.OnceR RNil.
Proof. exists true. apply le.RFlipNil_le. Qed.
#[export] Hint Resolve OnceR_nil : tychk.

Lemma row_type_multi ρ τ : le.MultiT τ → ρ R⪯T τ.
Proof. apply le.Multi_le. Qed.
Lemma row_type_once ρ τ : le.OnceR ρ → ρ R⪯T τ.
Proof. apply le.Once_le. Qed.
(* [once_nil] as a lemma. *)
Lemma row_type_nil τ : RNil R⪯T τ.
Proof. once_nil. Qed.

(* Multi route first (structural in τ), then the Once route (structural in ρ).
   An [Extern] so that the premise is closed by [tychk] or the whole
   alternative fails (no half-solved goals left behind). *)
#[export] Hint Extern 2 (le._row_type _ _) =>
  first [ apply le.Multi_le; solve [auto with tychk]
        | apply le.Once_le;  solve [auto with tychk] ] : tychk.

Lemma row_ctx_nil ρ : ρ R⪯C [].
Proof. apply le.NilR_le. Qed.

Lemma row_ctx_insert ρ (x : binder) τ Γ :
  ρ R⪯T τ → ρ R⪯C Γ → ρ R⪯C (<[ x :=c τ ]> Γ).
Proof. intros. by apply le.ConsR_le. Qed.

Lemma row_ctx_cons ρ (x : string) τ Γ :
  ρ R⪯T τ → ρ R⪯C Γ → ρ R⪯C ((x, τ) :: Γ).
Proof.
  intros. change ((x, τ) :: Γ) with (<[ BNamed x :=c τ ]> Γ).
  by apply le.ConsR_le.
Qed.

Lemma row_ctx_app ρ Γ1 Γ2 :
  ρ R⪯C Γ1 → ρ R⪯C Γ2 → ρ R⪯C (Γ1 ++ Γ2).
Proof.
  induction 1 as [|ρ' x τ Γ Hτ HΓ IH]; intros H2; [done|].
  destruct x as [|x]; simpl; [by apply IH|].
  apply row_ctx_cons; [done|by apply IH].
Qed.

Lemma row_ctx_ctx_append ρ Γ1 Γ2 :
  ρ R⪯C Γ1 → ρ R⪯C Γ2 → ρ R⪯C (Γ1 ;; Γ2).
Proof. apply row_ctx_app. Qed.

(* [RNil_le_ctx] is in types.v (derived_rules): RNil R⪯C Γ for all Γ. *)
#[export] Hint Resolve RNil_le_ctx : tychk.
#[export] Hint Resolve row_ctx_nil row_ctx_cons row_ctx_insert row_ctx_app
     row_ctx_ctx_append : tychk.

(* Entry point for side goals.  (Named [tychk_side] so that the name
   [tychk] stays free for the Stage D driver.) *)
Ltac tychk_side := first [ done | solve [auto with tychk] | solve [eauto 10 with tychk] ].

(* ================================================================== *)
(** * C2: context operations                                           *)
(* ================================================================== *)

(* [ctx_insert] on a named binder is a cons, so every lemma below stated for
   [(x, τ) :: Γ] applies to [<[ x :=c τ ]> Γ] by unification. *)
Lemma ctx_insert_named (x : string) τ Γ : <[ x :=c τ ]> Γ = (x, τ) :: Γ.
Proof. done. Qed.
Lemma ctx_insert_anon τ Γ : <[ BAnon :=c τ ]> Γ = Γ.
Proof. done. Qed.

Lemma ctx_dom_nil : ctx_dom [] = ∅.
Proof. done. Qed.
Lemma ctx_dom_cons (y : string) τ Γ : ctx_dom ((y, τ) :: Γ) = {[y]} ∪ ctx_dom Γ.
Proof. done. Qed.

(** ** Subtyping steps on the contexts, the row and the type *)

(* Change the input / output contexts by [≤C]. *)
Lemma typed_sub_ctx Δ Γ1 Γ1' Γ2 Γ2' e ρ τ :
  let D := le.row_to_disj_ctx ρ in
  D ⊢ₗ Γ1 ≤C Γ1' → D ⊢ₗ Γ2' ≤C Γ2 →
  Δ .| Γ1' ⊢ₜ e : ρ : τ ⊣ Γ2' → Δ .| Γ1 ⊢ₜ e : ρ : τ ⊣ Γ2.
Proof.
  intros D H1 H2 He.
  eapply (Sub_typed _ _ Γ1' _ Γ2' _ ρ false _ τ);
    [exact H1|exact H2|apply RRefl_le|apply le.TRefl_le|exact He].
Qed.

(* Change the result type (covariantly). *)
Lemma typed_sub_type Δ Γ Γ2 e ρ τ τ' :
  le.row_to_disj_ctx ρ ⊢ₗ τ' ≤T τ →
  Δ .| Γ ⊢ₜ e : ρ : τ' ⊣ Γ2 → Δ .| Γ ⊢ₜ e : ρ : τ ⊣ Γ2.
Proof.
  intros Hτ He.
  eapply (Sub_typed _ _ Γ _ Γ2 _ ρ false _ τ');
    [apply CRefl_le|apply CRefl_le|apply RRefl_le|exact Hτ|exact He].
Qed.

(* Change the row (covariantly). *)
Lemma typed_row_sub Δ Γ Γ2 e ρ ρ' b τ :
  le.row_to_disj_ctx ρ ⊢ₗ ρ' ≤R ρ @ b →
  Δ .| Γ ⊢ₜ e : ρ' : τ ⊣ Γ2 → Δ .| Γ ⊢ₜ e : ρ : τ ⊣ Γ2.
Proof.
  intros Hρ He.
  eapply (Sub_typed _ _ Γ _ Γ2 _ ρ' b _ τ);
    [apply CRefl_le|apply CRefl_le|exact Hρ|apply le.TRefl_le|exact He].
Qed.

(* An effect-free derivation can be used at any row ([RBot_le]). *)
Lemma typed_row_nil Δ Γ Γ2 e ρ τ :
  Δ .| Γ ⊢ₜ e : RNil : τ ⊣ Γ2 → Δ .| Γ ⊢ₜ e : ρ : τ ⊣ Γ2.
Proof. apply (typed_row_sub _ _ _ _ _ _ true), le.RBot_le. Qed.

(** ** Permutations *)

(* verbatim (scheduler_typed.v:64) *)
Lemma typed_perm Δ Γ Γ' e ρ τ Γ2 :
  Γ ≡ₚ Γ' →
  Δ .| Γ' ⊢ₜ e : ρ : τ ⊣ Γ2 → Δ .| Γ ⊢ₜ e : ρ : τ ⊣ Γ2.
Proof.
  intros Hp He.
  eapply (Sub_typed _ _ Γ' _ Γ2 _ ρ false _ τ); [|apply CRefl_le|apply RRefl_le|apply le.TRefl_le|done].
  by eapply _ctx_perm_right; [apply CRefl_le|].
Qed.

(* verbatim (scheduler_typed.v:73) *)
Lemma typed_perm_out Δ Γ e ρ τ Γ2 Γ2' :
  Γ2' ≡ₚ Γ2 →
  Δ .| Γ ⊢ₜ e : ρ : τ ⊣ Γ2' → Δ .| Γ ⊢ₜ e : ρ : τ ⊣ Γ2.
Proof.
  intros Hp He.
  eapply (Sub_typed _ _ Γ _ Γ2' _ ρ false _ τ); [apply CRefl_le| |apply RRefl_le|apply le.TRefl_le|done].
  by eapply _ctx_perm_right; [apply CRefl_le|].
Qed.

(* Bring the entry [(x, τ)] at a known position to the FRONT of the input
   context, where [Var_typed] (and [Contraction_typed]) can consume it.
   [Permutation_middle : a :: l1 ++ l2 ≡ₚ l1 ++ a :: l2]. *)
Lemma typed_front Δ pre post (x : string) τ e ρ κ Γ2 :
  Δ .| (x, τ) :: pre ++ post ⊢ₜ e : ρ : κ ⊣ Γ2 →
  Δ .| pre ++ (x, τ) :: post ⊢ₜ e : ρ : κ ⊣ Γ2.
Proof.
  intros He. eapply typed_perm; [|exact He]. symmetry. apply Permutation_middle.
Qed.

(* Same for the output context. *)
Lemma typed_front_out Δ Γ pre post (x : string) τ e ρ κ :
  Δ .| Γ ⊢ₜ e : ρ : κ ⊣ (x, τ) :: pre ++ post →
  Δ .| Γ ⊢ₜ e : ρ : κ ⊣ pre ++ (x, τ) :: post.
Proof.
  intros He. eapply typed_perm_out; [|exact He]. apply Permutation_middle.
Qed.

(** ** Deleting entries *)

(* [le._ctx D Γ Γ'] holds when Γ has (more specific) entries for all of Γ',
   so Γ may carry extra entries: dropping one is a subtyping step. *)
Lemma ctx_drop_head D (x : string) τ Γ : D ⊢ₗ (x, τ) :: Γ ≤C Γ.
Proof.
  induction Γ as [|[y t] Γ IH]; simpl; [exact I|].
  exists t, [(x, τ)], Γ. split; [reflexivity|].
  split; [apply le.TRefl_le|exact IH].
Qed.

Lemma ctx_drop D pre post (x : string) τ :
  D ⊢ₗ pre ++ (x, τ) :: post ≤C pre ++ post.
Proof.
  apply (_ctx_perm_left D ((x, τ) :: pre ++ post)).
  - apply ctx_drop_head.
  - apply Permutation_middle.
Qed.

(* A suffix can always be dropped. *)
Lemma ctx_app_le D Γ k : D ⊢ₗ Γ ++ k ≤C Γ.
Proof.
  induction Γ as [|[x t] Γ IH]; simpl; [exact I|].
  exists t, [], (Γ ++ k). split; [done|]. split; [apply le.TRefl_le|exact IH].
Qed.

(* More generally, any sub-multiset of a context is above it. *)
Lemma ctx_sub_le D Γ Γ' : Γ' ⊆+ Γ → D ⊢ₗ Γ ≤C Γ'.
Proof.
  intros [k Hk]%submseteq_Permutation.
  apply (_ctx_perm_left D (Γ' ++ k)); [apply ctx_app_le|by symmetry].
Qed.

(* Weakening of the input context at an arbitrary position (the primitive
   [Weakening_typed] only weakens the head). *)
Lemma typed_weaken Δ pre post (x : string) τ e ρ κ Γ2 :
  Δ .| pre ++ post ⊢ₜ e : ρ : κ ⊣ Γ2 →
  Δ .| pre ++ (x, τ) :: post ⊢ₜ e : ρ : κ ⊣ Γ2.
Proof.
  intros He.
  eapply typed_sub_ctx; [apply ctx_drop|apply CRefl_le|exact He].
Qed.

(* Forget an entry of the OUTPUT context. *)
Lemma typed_drop_out Δ Γ pre post (x : string) τ e ρ κ :
  Δ .| Γ ⊢ₜ e : ρ : κ ⊣ pre ++ (x, τ) :: post →
  Δ .| Γ ⊢ₜ e : ρ : κ ⊣ pre ++ post.
Proof.
  intros He.
  eapply typed_sub_ctx; [apply CRefl_le|apply ctx_drop|exact He].
Qed.

(* Weakening by sub-multisets, on either side. *)
Lemma typed_weaken_sub Δ Γ Γ' e ρ κ Γ2 :
  Γ' ⊆+ Γ →
  Δ .| Γ' ⊢ₜ e : ρ : κ ⊣ Γ2 → Δ .| Γ ⊢ₜ e : ρ : κ ⊣ Γ2.
Proof.
  intros Hs He. eapply typed_sub_ctx; [by apply ctx_sub_le|apply CRefl_le|exact He].
Qed.

Lemma typed_out_sub Δ Γ e ρ κ Γ2 Γ2' :
  Γ2 ⊆+ Γ2' →
  Δ .| Γ ⊢ₜ e : ρ : κ ⊣ Γ2' → Δ .| Γ ⊢ₜ e : ρ : κ ⊣ Γ2.
Proof.
  intros Hs He. eapply typed_sub_ctx; [apply CRefl_le|by apply ctx_sub_le|exact He].
Qed.

(** ** Lookup by name: [ctx_pick] *)

(* [ctx_pick x Γ τ Γ']: [Γ] has an entry [(x, τ)], and [Γ'] is [Γ] without
   it.  [solve_ctx_pick] computes [τ] and [Γ'] for a concrete [Γ] by
   structural search; it picks the FIRST entry named [x] whose type unifies
   with the given [τ] (usually an evar or a pattern such as [![MS] ?τ]). *)
Definition ctx_pick (x : string) (Γ : ctx) (τ : type) (Γ' : ctx) : Prop :=
  Γ ≡ₚ (x, τ) :: Γ'.

Lemma ctx_pick_here x τ Γ : ctx_pick x ((x, τ) :: Γ) τ Γ.
Proof. rewrite /ctx_pick. reflexivity. Qed.

Lemma ctx_pick_there x y τ τ' Γ Γ' :
  ctx_pick x Γ τ Γ' → ctx_pick x ((y, τ') :: Γ) τ ((y, τ') :: Γ').
Proof. rewrite /ctx_pick => ->. apply perm_swap. Qed.

Lemma ctx_pick_elem x Γ τ Γ' : ctx_pick x Γ τ Γ' → (x, τ) ∈ Γ.
Proof. rewrite /ctx_pick => ->. by left. Qed.

Lemma ctx_pick_sub x Γ τ Γ' : ctx_pick x Γ τ Γ' → Γ' ⊆+ Γ.
Proof. rewrite /ctx_pick => ->. by apply submseteq_cons. Qed.

Ltac solve_ctx_pick :=
  first [ apply ctx_pick_here | apply ctx_pick_there; solve_ctx_pick ].

(* Bring an entry to the front of the input / output context. *)
Lemma typed_pick Δ x Γ τ Γ' e ρ κ Γ2 :
  ctx_pick x Γ τ Γ' →
  Δ .| (x, τ) :: Γ' ⊢ₜ e : ρ : κ ⊣ Γ2 → Δ .| Γ ⊢ₜ e : ρ : κ ⊣ Γ2.
Proof. apply typed_perm. Qed.

Lemma typed_pick_out Δ Γ e ρ κ x Γ2 τ Γ2' :
  ctx_pick x Γ2 τ Γ2' →
  Δ .| Γ ⊢ₜ e : ρ : κ ⊣ (x, τ) :: Γ2' → Δ .| Γ ⊢ₜ e : ρ : κ ⊣ Γ2.
Proof. intros Hp. apply typed_perm_out. by symmetry. Qed.

(* Delete an entry of the input (weakening) / output context. *)
Lemma typed_weaken_pick Δ x Γ τ Γ' e ρ κ Γ2 :
  ctx_pick x Γ τ Γ' →
  Δ .| Γ' ⊢ₜ e : ρ : κ ⊣ Γ2 → Δ .| Γ ⊢ₜ e : ρ : κ ⊣ Γ2.
Proof. intros Hp. apply typed_weaken_sub. by eapply ctx_pick_sub. Qed.

Lemma typed_drop_out_pick Δ Γ e ρ κ x Γ2 τ Γ2' :
  ctx_pick x Γ2' τ Γ2 →
  Δ .| Γ ⊢ₜ e : ρ : κ ⊣ Γ2' → Δ .| Γ ⊢ₜ e : ρ : κ ⊣ Γ2.
Proof. intros Hp. apply typed_out_sub. by eapply ctx_pick_sub. Qed.

(** ** Delete every entry with a given name: [ctx_without] *)

(* Needed after a binder: the binder rules require [x ∉ ctx_dom Γ2], and
   dropping the shadowed entries is the only derivation available
   (PLAN.md section 8). *)
Definition ctx_without (x : string) (Γ Γ' : ctx) : Prop :=
  Γ' ⊆+ Γ ∧ x ∉ ctx_dom Γ'.

Lemma ctx_without_nil x : ctx_without x [] [].
Proof. split; [done|]. rewrite ctx_dom_nil. set_solver. Qed.

Lemma ctx_without_hit x τ Γ Γ' :
  ctx_without x Γ Γ' → ctx_without x ((x, τ) :: Γ) Γ'.
Proof. intros [H1 H2]. split; [by apply submseteq_cons|done]. Qed.

Lemma ctx_without_miss x y τ Γ Γ' :
  x ≠ y → ctx_without x Γ Γ' → ctx_without x ((y, τ) :: Γ) ((y, τ) :: Γ').
Proof.
  intros Hne [H1 H2]. split; [by apply submseteq_skip|].
  rewrite ctx_dom_cons. set_solver.
Qed.

Ltac solve_ctx_without :=
  first [ apply ctx_without_nil
        | apply ctx_without_hit; solve_ctx_without
        | apply ctx_without_miss; [done|solve_ctx_without] ].

Lemma typed_without Δ x Γ Γ' e ρ κ Γ2 :
  ctx_without x Γ Γ' →
  Δ .| Γ' ⊢ₜ e : ρ : κ ⊣ Γ2 → Δ .| Γ ⊢ₜ e : ρ : κ ⊣ Γ2.
Proof. intros [Hs _]. by apply typed_weaken_sub. Qed.

Lemma typed_without_out Δ x Γ e ρ κ Γ2 Γ2' :
  ctx_without x Γ2' Γ2 →
  Δ .| Γ ⊢ₜ e : ρ : κ ⊣ Γ2' → Δ .| Γ ⊢ₜ e : ρ : κ ⊣ Γ2.
Proof. intros [Hs _]. by apply typed_out_sub. Qed.

(** ** Rows and values *)

(* verbatim (scheduler_typed.v:82) *)
Lemma typed_row_cons Δ Γ e σ τ Γ2 :
  Δ .| Γ ⊢ₜ e : RNil : τ ⊣ Γ2 → Δ .| Γ ⊢ₜ e : RCons σ RNil : τ ⊣ Γ2.
Proof.
  intros He.
  eapply (Sub_typed _ _ Γ _ Γ2 _ RNil true _ τ); [apply CRefl_le|apply CRefl_le|apply le.RExtend_le|apply le.TRefl_le|done].
Qed.

(* scheduler_typed.v:89, generalised from [RCons σ RNil] to any row. *)
Lemma typed_val_row Δ Γ v ρ τ :
  ⊢ᵥ v : τ → Δ .| Γ ⊢ₜ Val v : ρ : τ ⊣ Γ.
Proof. intros Hv. by apply typed_row_nil, Val_typed. Qed.

(** ** Variables *)

(* verbatim (scheduler_typed.v:94): use a duplicable head variable without
   consuming it. *)
Lemma typed_var_dup Δ (x : string) τ Γ :
  le.MultiT τ →
  Δ .| (x, τ) :: Γ ⊢ₜ Var x : RNil : τ ⊣ (x, τ) :: Γ.
Proof.
  intros Hτ. apply (Contraction_typed _ _ _ _ _ _ x τ Hτ). apply Var_typed.
Qed.

(* verbatim (scheduler_typed.v:102): strip a [!] when consuming the head. *)
Lemma typed_var_bang Δ (x : string) (m : vmode) τ Γ :
  Δ .| (x, (![m] τ)%ty) :: Γ ⊢ₜ Var x : RNil : τ ⊣ Γ.
Proof.
  eapply (Sub_typed _ _ _ _ Γ _ RNil false _ (![m] τ)%ty);
    [apply CRefl_le|apply CRefl_le|apply RRefl_le|apply le.TBangElim_le|apply Var_typed].
Qed.

(* scheduler_typed.v:110, generalised to any row: consume a variable
   anywhere. *)
Lemma typed_var_at Δ Γ Γ' (x : string) τ ρ :
  Γ ≡ₚ (x, τ) :: Γ' →
  Δ .| Γ ⊢ₜ Var x : ρ : τ ⊣ Γ'.
Proof. intros Hp. apply typed_row_nil. eapply typed_perm; [done|apply Var_typed]. Qed.

(* Consume the entry at a given position. *)
Lemma typed_var_pos Δ pre post (x : string) τ ρ :
  Δ .| pre ++ (x, τ) :: post ⊢ₜ Var x : ρ : τ ⊣ pre ++ post.
Proof. apply typed_row_nil, typed_front, Var_typed. Qed.

(* Consume the head with a result-type coercion [τ' ≤ τ]: [typed_var_bang]
   is the case [τ' := ![m] τ], [le.TBangElim_le]. *)
Lemma typed_var_le Δ (x : string) τ' τ ρ Γ :
  le.row_to_disj_ctx ρ ⊢ₗ τ' ≤T τ →
  Δ .| (x, τ') :: Γ ⊢ₜ Var x : ρ : τ ⊣ Γ.
Proof.
  intros Hτ. eapply typed_sub_type; [exact Hτ|]. apply typed_row_nil, Var_typed.
Qed.

(* Copy a [MultiT] entry located anywhere, without consuming it
   (generalises [typed_var_dup] to arbitrary positions and rows). *)
Lemma typed_var_copy Δ pre post (x : string) τ ρ :
  le.MultiT τ →
  Δ .| pre ++ (x, τ) :: post ⊢ₜ Var x : ρ : τ ⊣ pre ++ (x, τ) :: post.
Proof.
  intros Hτ. apply typed_row_nil, typed_front, typed_front_out.
  by apply typed_var_dup.
Qed.

(* Copy an entry of type [![MS] τ] and strip the bang (the variable part of
   [typed_call]).  [TBangIdemp1_le] discharges the [MultiT] side condition. *)
Lemma typed_var_copy_bang Δ pre post (x : string) τ ρ :
  Δ .| pre ++ (x, (![MS] τ)%ty) :: post ⊢ₜ Var x : ρ : τ
    ⊣ pre ++ (x, (![MS] τ)%ty) :: post.
Proof.
  apply typed_row_nil, typed_front, typed_front_out.
  eapply (Sub_typed _ _ _ _ _ _ RNil false _ (![MS] τ)%ty);
    [apply CRefl_le|apply CRefl_le|apply RRefl_le|apply le.TBangElim_le|].
  apply typed_var_dup, le.TBangIdemp1_le.
Qed.

(* The same four operations, located by name ([ctx_pick]). *)
Lemma typed_var_take Δ (x : string) Γ τ Γ' ρ :
  ctx_pick x Γ τ Γ' → Δ .| Γ ⊢ₜ Var x : ρ : τ ⊣ Γ'.
Proof. apply typed_var_at. Qed.

Lemma typed_var_take_le Δ (x : string) Γ τ' τ Γ' ρ :
  ctx_pick x Γ τ' Γ' →
  le.row_to_disj_ctx ρ ⊢ₗ τ' ≤T τ →
  Δ .| Γ ⊢ₜ Var x : ρ : τ ⊣ Γ'.
Proof. intros Hp Hτ. eapply typed_pick; [exact Hp|]. by apply typed_var_le. Qed.

Lemma typed_var_take_bang Δ (x : string) Γ (m : vmode) τ Γ' ρ :
  ctx_pick x Γ (![m] τ)%ty Γ' → Δ .| Γ ⊢ₜ Var x : ρ : τ ⊣ Γ'.
Proof. intros Hp. eapply typed_var_take_le; [exact Hp|apply le.TBangElim_le]. Qed.

Lemma typed_var_copy_pick Δ (x : string) Γ τ Γ' ρ :
  ctx_pick x Γ τ Γ' → le.MultiT τ → Δ .| Γ ⊢ₜ Var x : ρ : τ ⊣ Γ.
Proof.
  intros Hp Hτ. apply typed_row_nil.
  eapply typed_pick; [exact Hp|]. eapply typed_pick_out; [exact Hp|].
  by apply typed_var_dup.
Qed.

Lemma typed_var_copy_bang_pick Δ (x : string) Γ τ Γ' ρ :
  ctx_pick x Γ (![MS] τ)%ty Γ' → Δ .| Γ ⊢ₜ Var x : ρ : τ ⊣ Γ.
Proof.
  intros Hp. eapply typed_sub_type; [apply le.TBangElim_le|].
  eapply typed_var_copy_pick; [exact Hp|apply le.TBangIdemp1_le].
Qed.

(* scheduler_typed.v:117, generalised to any row: call [f : τ ⇾ κ] without
   consuming it. *)
Lemma typed_call Δ Γ1 Γ2 (f : string) e τ κ ρ :
  (f, (τ ⇾ κ)%ty) ∈ Γ2 →
  Δ .| Γ1 ⊢ₜ e : ρ : τ ⊣ Γ2 →
  Δ .| Γ1 ⊢ₜ App (Var f) e : ρ : κ ⊣ Γ2.
Proof.
  intros Hin He.
  apply list_elem_of_split in Hin as (l1 & l2 & ->).
  assert (Hp : l1 ++ (f, (τ ⇾ κ)%ty) :: l2 ≡ₚ (f, (τ ⇾ κ)%ty) :: l1 ++ l2)
    by by rewrite -Permutation_middle.
  eapply (App_typed _ _ _ _ _ _ _ RNil RNil true τ κ);
    [apply le.RBot_le|apply le.RBot_le|once_nil|apply RNil_le_ctx|exact He|].
  eapply typed_perm; [exact Hp|]. eapply typed_perm_out; [symmetry; exact Hp|].
  eapply (Sub_typed _ _ _ _ _ _ RNil false _ (τ ⇾ κ)%ty);
    [apply CRefl_le|apply CRefl_le|apply RRefl_le|apply le.TBangElim_le|].
  apply typed_var_dup, le.TBangIdemp1_le.
Qed.

(* ================================================================== *)
(** * C3: row normal form (from probe_tychk_row.v)                     *)
(* ================================================================== *)

(* A row in normal form is a list of signatures in front of a union of
   atoms; an atom is a row variable (or an opaque row) under flips. *)
Fixpoint norm_row (ρ : row) : list eff_sig * list row :=
  match ρ with
  | RNil => ([], [])
  | RCons σ ρ => let '(ss, vs) := norm_row ρ in (σ :: ss, vs)
  | RVar i => ([], [RVar i])
  | RFlip m ρ => let '(ss, vs) := norm_row ρ in (map (SFlip m) ss, map (RFlip m) vs)
  | RUnion ρ1 ρ2 =>
      let '(ss1, vs1) := norm_row ρ1 in
      let '(ss2, vs2) := norm_row ρ2 in (ss1 ++ ss2, vs1 ++ vs2)
  end.

Definition denorm (p : list eff_sig * list row) : row :=
  let '(ss, vs) := p in foldr RCons (foldr RUnion RNil vs) ss.

(* Congruences.  RUnion_le / RCons_le premises are at flag false, hence the ∀ b. *)
Lemma RUnion_cong D b ρ1 ρ2 ρ1' ρ2' :
  (∀ b, D ⊢ₗ ρ1 ≤R ρ1' @ b) → (∀ b, D ⊢ₗ ρ2 ≤R ρ2' @ b) →
  D ⊢ₗ RUnion ρ1 ρ2 ≤R RUnion ρ1' ρ2' @ b.
Proof. intros H1 H2. apply le.RUnion_le; [apply H1|apply H2]. Qed.

Lemma Cs_cong D b ss r r' :
  (∀ b, D ⊢ₗ r ≤R r' @ b) → D ⊢ₗ foldr RCons r ss ≤R foldr RCons r' ss @ b.
Proof.
  intros H. revert b; induction ss as [|σ ss IH]; intros b; simpl; [apply H|].
  apply le.RCons_le; [apply SRefl_le|apply IH].
Qed.

(* Union over a cons-prefix, both directions. *)
Lemma union_Cs_1 D b ss r1 r2 :
  D ⊢ₗ RUnion (foldr RCons r1 ss) r2 ≤R foldr RCons (RUnion r1 r2) ss @ b.
Proof.
  revert b; induction ss as [|σ ss IH]; intros b; simpl; [apply RRefl_le|].
  eapply le.RTrans_le; [apply RUnion_cong; [intros; apply le.RUnionCons1_le|intros; apply RRefl_le]|].
  eapply le.RTrans_le; [apply le.RUnionAssoc2_le|].
  eapply le.RTrans_le; [apply le.RUnionCons2_le|].
  apply le.RCons_le; [apply SRefl_le|apply IH].
Qed.

Lemma union_Cs_2 D b ss r1 r2 :
  D ⊢ₗ foldr RCons (RUnion r1 r2) ss ≤R RUnion (foldr RCons r1 ss) r2 @ b.
Proof.
  revert b; induction ss as [|σ ss IH]; intros b; simpl; [apply RRefl_le|].
  eapply le.RTrans_le; [apply le.RCons_le; [apply SRefl_le|apply IH]|].
  eapply le.RTrans_le; [apply le.RUnionCons1_le|].
  eapply le.RTrans_le; [apply le.RUnionAssoc1_le|].
  apply RUnion_cong; [intros; apply le.RUnionCons2_le|intros; apply RRefl_le].
Qed.

(* Flattening of nested unions of atoms. *)
Lemma union_Us_1 D b vs1 vs2 :
  D ⊢ₗ RUnion (foldr RUnion RNil vs1) (foldr RUnion RNil vs2) ≤R foldr RUnion RNil (vs1 ++ vs2) @ b.
Proof.
  revert b; induction vs1 as [|v vs1 IH]; intros b; simpl; [apply le.RUnionNilRight2_le|].
  eapply le.RTrans_le; [apply le.RUnionAssoc2_le|].
  apply RUnion_cong; [intros; apply RRefl_le|apply IH].
Qed.

Lemma union_Us_2 D b vs1 vs2 :
  D ⊢ₗ foldr RUnion RNil (vs1 ++ vs2) ≤R RUnion (foldr RUnion RNil vs1) (foldr RUnion RNil vs2) @ b.
Proof.
  revert b; induction vs1 as [|v vs1 IH]; intros b; simpl; [apply le.RUnionNilRight1_le|].
  eapply le.RTrans_le; [|apply le.RUnionAssoc1_le].
  apply RUnion_cong; [intros; apply RRefl_le|apply IH].
Qed.

(* Flip distribution. *)
Lemma flip_Cs D b m ss r :
  D ⊢ₗ RFlip m (foldr RCons r ss) ≤R foldr RCons (RFlip m r) (map (SFlip m) ss) @ b.
Proof.
  revert b; induction ss as [|σ ss IH]; intros b; simpl; [apply RRefl_le|].
  eapply le.RTrans_le; [apply le.RFlipCons_le|].
  apply le.RCons_le; [apply SRefl_le|apply IH].
Qed.

Lemma flip_Us D b m vs :
  D ⊢ₗ RFlip m (foldr RUnion RNil vs) ≤R foldr RUnion RNil (map (RFlip m) vs) @ b.
Proof.
  revert b; induction vs as [|v vs IH]; intros b; simpl; [apply le.RFlipNil_le|].
  eapply le.RTrans_le; [apply le.RFlipUnion_le|].
  apply RUnion_cong; [intros; apply RRefl_le|apply IH].
Qed.

(* Converses of flip_Cs / flip_Us, using RFlipConsInv_le / RFlipUnionInv_le
   and RFlipIntro_le for the empty row. *)
Lemma flip_Cs_inv D b m ss r :
  D ⊢ₗ foldr RCons (RFlip m r) (map (SFlip m) ss) ≤R RFlip m (foldr RCons r ss) @ b.
Proof.
  revert b; induction ss as [|σ ss IH]; intros b; simpl; [apply RRefl_le|].
  eapply le.RTrans_le; [|apply le.RFlipConsInv_le].
  apply le.RCons_le; [apply SRefl_le|apply IH].
Qed.

Lemma flip_Us_inv D b m vs :
  D ⊢ₗ foldr RUnion RNil (map (RFlip m) vs) ≤R RFlip m (foldr RUnion RNil vs) @ b.
Proof.
  revert b; induction vs as [|v vs IH]; intros b; simpl; [apply le.RFlipIntro_le|].
  eapply le.RTrans_le; [|apply le.RFlipUnionInv_le].
  apply RUnion_cong; [intros; apply RRefl_le|apply IH].
Qed.

Lemma union_denorm_1 D b ss1 vs1 ss2 vs2 :
  D ⊢ₗ RUnion (denorm (ss1, vs1)) (denorm (ss2, vs2)) ≤R denorm (ss1 ++ ss2, vs1 ++ vs2) @ b.
Proof.
  simpl. rewrite foldr_app.
  eapply le.RTrans_le; [apply union_Cs_1|]. apply Cs_cong; intros b'.
  eapply le.RTrans_le; [apply le.RUnionComm_le|].
  eapply le.RTrans_le; [apply union_Cs_1|]. apply Cs_cong; intros b''.
  eapply le.RTrans_le; [apply le.RUnionComm_le|]. apply union_Us_1.
Qed.

Lemma union_denorm_2 D b ss1 vs1 ss2 vs2 :
  D ⊢ₗ denorm (ss1 ++ ss2, vs1 ++ vs2) ≤R RUnion (denorm (ss1, vs1)) (denorm (ss2, vs2)) @ b.
Proof.
  simpl. rewrite foldr_app.
  eapply le.RTrans_le; [|apply union_Cs_2]. apply Cs_cong; intros b'.
  eapply le.RTrans_le; [|apply le.RUnionComm_le].
  eapply le.RTrans_le; [|apply union_Cs_2]. apply Cs_cong; intros b''.
  eapply le.RTrans_le; [|apply le.RUnionComm_le]. apply union_Us_2.
Qed.

Lemma norm_denorm_le D b ρ : D ⊢ₗ ρ ≤R denorm (norm_row ρ) @ b.
Proof.
  revert b; induction ρ; intros b; simpl.
  - constructor.
  - destruct (norm_row ρ) as [ss vs]; simpl in *.
    eapply le.RCons_le; [apply SRefl_le|apply IHρ].
  - apply le.RUnionNilLeft1_le.
  - destruct (norm_row ρ) as [ss vs]; simpl in *.
    eapply le.RTrans_le; [apply le.RFlipComp_le; [apply le.MRefl_le|apply IHρ]|].
    eapply le.RTrans_le; [apply flip_Cs|]. apply Cs_cong; intros; apply flip_Us.
  - destruct (norm_row ρ1) as [ss1 vs1] eqn:E1; destruct (norm_row ρ2) as [ss2 vs2] eqn:E2.
    eapply le.RTrans_le; [apply RUnion_cong; [apply IHρ1|apply IHρ2]|].
    apply union_denorm_1.
Qed.

Lemma denorm_norm_le D b ρ : D ⊢ₗ denorm (norm_row ρ) ≤R ρ @ b.
Proof.
  revert b; induction ρ; intros b; simpl in *.
  - constructor.
  - destruct (norm_row ρ) as [ss vs]; simpl in *.
    eapply le.RCons_le; [apply SRefl_le|by apply IHρ].
  - apply le.RUnionNilLeft2_le.
  - destruct (norm_row ρ) as [ss vs]; simpl in *.
    eapply le.RTrans_le; [|apply le.RFlipComp_le; [apply le.MRefl_le|apply IHρ]].
    eapply le.RTrans_le; [|apply flip_Cs_inv].
    apply Cs_cong; intros; apply flip_Us_inv.
  - destruct (norm_row ρ1) as [ss1 vs1] eqn:E1; destruct (norm_row ρ2) as [ss2 vs2] eqn:E2.
    eapply le.RTrans_le; [apply union_denorm_2|].
    apply RUnion_cong; intros; [apply IHρ1|apply IHρ2].
Qed.

(** ** Reified rows: opaque sub-rows as atoms *)

(* [norm_row] gets stuck on a row that is not built from constructors (a
   Coq variable [ρ : row], [rename_type_row (+1) ρ], …).  The solver
   therefore reifies the row first; anything that is not a constructor
   becomes an atom [XAtom ρ], treated like [RVar i]. *)
Inductive rsyn :=
| XNil
| XCons (σ : eff_sig) (r : rsyn)
| XFlip (m : vmode) (r : rsyn)
| XUnion (r1 r2 : rsyn)
| XAtom (ρ : row).

Fixpoint rsyn_row (r : rsyn) : row :=
  match r with
  | XNil => RNil
  | XCons σ r => RCons σ (rsyn_row r)
  | XFlip m r => RFlip m (rsyn_row r)
  | XUnion r1 r2 => RUnion (rsyn_row r1) (rsyn_row r2)
  | XAtom ρ => ρ
  end.

Fixpoint rsyn_norm (r : rsyn) : list eff_sig * list row :=
  match r with
  | XNil => ([], [])
  | XCons σ r => let '(ss, vs) := rsyn_norm r in (σ :: ss, vs)
  | XAtom ρ => ([], [ρ])
  | XFlip m r => let '(ss, vs) := rsyn_norm r in (map (SFlip m) ss, map (RFlip m) vs)
  | XUnion r1 r2 =>
      let '(ss1, vs1) := rsyn_norm r1 in
      let '(ss2, vs2) := rsyn_norm r2 in (ss1 ++ ss2, vs1 ++ vs2)
  end.

Lemma rsyn_norm_le1 D b r : D ⊢ₗ rsyn_row r ≤R denorm (rsyn_norm r) @ b.
Proof.
  revert b; induction r as [|σ r IH|m r IH|r1 IH1 r2 IH2|ρ]; intros b; simpl.
  - constructor.
  - destruct (rsyn_norm r) as [ss vs]; simpl in *.
    eapply le.RCons_le; [apply SRefl_le|apply IH].
  - destruct (rsyn_norm r) as [ss vs]; simpl in *.
    eapply le.RTrans_le; [apply le.RFlipComp_le; [apply le.MRefl_le|apply IH]|].
    eapply le.RTrans_le; [apply flip_Cs|]. apply Cs_cong; intros; apply flip_Us.
  - destruct (rsyn_norm r1) as [ss1 vs1]; destruct (rsyn_norm r2) as [ss2 vs2].
    eapply le.RTrans_le; [apply RUnion_cong; [apply IH1|apply IH2]|].
    apply union_denorm_1.
  - apply le.RUnionNilLeft1_le.
Qed.

Lemma rsyn_norm_le2 D b r : D ⊢ₗ denorm (rsyn_norm r) ≤R rsyn_row r @ b.
Proof.
  revert b; induction r as [|σ r IH|m r IH|r1 IH1 r2 IH2|ρ]; intros b; simpl.
  - constructor.
  - destruct (rsyn_norm r) as [ss vs]; simpl in *.
    eapply le.RCons_le; [apply SRefl_le|apply IH].
  - destruct (rsyn_norm r) as [ss vs]; simpl in *.
    eapply le.RTrans_le; [|apply le.RFlipComp_le; [apply le.MRefl_le|apply IH]].
    eapply le.RTrans_le; [|apply flip_Cs_inv].
    apply Cs_cong; intros; apply flip_Us_inv.
  - destruct (rsyn_norm r1) as [ss1 vs1]; destruct (rsyn_norm r2) as [ss2 vs2].
    eapply le.RTrans_le; [apply union_denorm_2|].
    apply RUnion_cong; [apply IH1|apply IH2].
  - apply le.RUnionNilLeft2_le.
Qed.

Lemma rsyn_le_intro D b r1 r2 :
  D ⊢ₗ denorm (rsyn_norm r1) ≤R denorm (rsyn_norm r2) @ b →
  D ⊢ₗ rsyn_row r1 ≤R rsyn_row r2 @ b.
Proof.
  intros H. eapply le.RTrans_le; [apply rsyn_norm_le1|].
  eapply le.RTrans_le; [exact H|apply rsyn_norm_le2].
Qed.

Ltac reify_row ρ :=
  lazymatch ρ with
  | RNil => constr:(XNil)
  | RCons ?σ ?r => let x := reify_row r in constr:(XCons σ x)
  | RFlip ?m ?r => let x := reify_row r in constr:(XFlip m x)
  | RUnion ?r1 ?r2 =>
      let x1 := reify_row r1 in let x2 := reify_row r2 in constr:(XUnion x1 x2)
  | _ => constr:(XAtom ρ)
  end.

(** ** Matching signatures up to [≤S] and atoms up to [≤R] *)

Ltac mode_le_solve :=
  first [ apply le.MRefl_le | apply le.MOS_le | apply le.MMS_le ].

(* The fragment of [≤S] used by the solver.  [≤S] has no transitivity rule
   (and transitivity is not admissible: [σ ≤S ¡[m] ¡[m] σ] is not
   derivable), so only single rules plus congruence under flips. *)
Ltac sig_le_solve :=
  first [ apply SRefl_le
        | apply le.SFlipIdemp1_le
        | apply le.SFlipIdemp2_le
        | apply le.SFlipElim_le
        | apply le.SFlipIntro_le
        | apply le.SFlipComp_le; [mode_le_solve|sig_le_solve] ].

(* Atoms ([RVar i] or opaque rows under flips); [≤R] has [RTrans_le], but the
   solver only needs single rules plus congruence. *)
Ltac atom_le_solve :=
  first [ apply RRefl_le
        | apply le.RFlipIdemp1_le
        | apply le.RFlipIdemp2_le
        | apply le.RFlipElim_le
        | apply le.RFlipIntro_le
        | apply le.RFlipComp_le; [mode_le_solve|atom_le_solve] ].

(** ** Inclusion of normal forms *)

(* [sfront D σ Y Y']: some signature of [Y] is above [σ]; [Y'] is [Y]
   without it. *)
Definition sfront (D : le.disj_ctx) (σ : eff_sig) (Y Y' : row) : Prop :=
  ∀ b, D ⊢ₗ RCons σ Y' ≤R Y @ b.

Lemma sfront_here D σ σ' Y : D ⊢ₗ σ ≤S σ' → sfront D σ (RCons σ' Y) Y.
Proof. intros H b. apply le.RCons_le; [exact H|apply RRefl_le]. Qed.

Lemma sfront_there D σ τ Y Y' : sfront D σ Y Y' → sfront D σ (RCons τ Y) (RCons τ Y').
Proof.
  intros H b. eapply le.RTrans_le; [apply le.RSwap_le|].
  apply le.RCons_le; [apply SRefl_le|apply H].
Qed.

Lemma spick_le D b σ X Y Y' :
  sfront D σ Y Y' → D ⊢ₗ X ≤R Y' @ false → D ⊢ₗ RCons σ X ≤R Y @ b.
Proof.
  intros Hf HX. eapply le.RTrans_le; [|apply Hf].
  apply le.RCons_le; [apply SRefl_le|exact HX].
Qed.

(* [afront D a Y Y']: some atom of the union [Y] is above [a]. *)
Definition afront (D : le.disj_ctx) (a Y Y' : row) : Prop :=
  ∀ b, D ⊢ₗ RUnion a Y' ≤R Y @ b.

Lemma union_swap D b a c Y :
  D ⊢ₗ RUnion a (RUnion c Y) ≤R RUnion c (RUnion a Y) @ b.
Proof.
  eapply le.RTrans_le; [apply le.RUnionAssoc1_le|].
  eapply le.RTrans_le; [apply le.RUnion_le; [apply le.RUnionComm_le|apply RRefl_le]|].
  apply le.RUnionAssoc2_le.
Qed.

Lemma afront_here D a c Y : D ⊢ₗ a ≤R c @ false → afront D a (RUnion c Y) Y.
Proof. intros H b. apply le.RUnion_le; [exact H|apply RRefl_le]. Qed.

Lemma afront_there D a c Y Y' : afront D a Y Y' → afront D a (RUnion c Y) (RUnion c Y').
Proof.
  intros H b. eapply le.RTrans_le; [apply union_swap|].
  apply le.RUnion_le; [apply RRefl_le|apply H].
Qed.

Lemma apick_le D b a X Y Y' :
  afront D a Y Y' → D ⊢ₗ X ≤R Y' @ false → D ⊢ₗ RUnion a X ≤R Y @ b.
Proof.
  intros Hf HX. eapply le.RTrans_le; [|apply Hf].
  apply le.RUnion_le; [apply RRefl_le|exact HX].
Qed.

(* Signatures of the target that are not matched are dropped ([RExtend_le]). *)
Lemma drop_sig_le D b X σ Y : D ⊢ₗ X ≤R Y @ b → D ⊢ₗ X ≤R RCons σ Y @ b.
Proof. intros H. eapply le.RTrans_le; [exact H|apply le.RExtend_le]. Qed.

(* Signature search, exact: first syntactically equal signature. *)
Ltac sfind_eq :=
  first [ apply sfront_here;
          lazymatch goal with |- _ ⊢ₗ ?σ ≤S ?σ' => constr_eq σ σ'; apply SRefl_le end
        | apply sfront_there; sfind_eq ].

(* Signature search up to [≤S], with backtracking over the candidates. *)
Ltac sfind_le :=
  (apply sfront_here; solve [sig_le_solve]) + (apply sfront_there; sfind_le).

Ltac afind :=
  (apply afront_here; solve [atom_le_solve]) + (apply afront_there; afind).

(** ** Erasure of absent signatures ([RErase_le], flag [true] only) *)

(* The side conditions of [RErase_le] as a boolean, so that the [Decision]
   instances are resolved here once and not on computed multiset terms. *)
Definition erase_check (D : le.disj_ctx) (s : eff_name) (ρ : row) : bool :=
  match D !! s with
  | Some (ss, js) => bool_decide (le.conc_sigs ρ ⊆ ss) && bool_decide (le.abst_sigs ρ ⊆ js)
  | None => false
  end.

Lemma erase_check_le D s ρ :
  erase_check D s ρ = true → D ⊢ₗ RCons (SAbs s) ρ ≤R ρ @ true.
Proof.
  rewrite /erase_check. destruct (D !! s) as [[ss js]|] eqn:E; [|done].
  intros [H1 H2]%andb_true_iff.
  eapply le.RErase_le; [exact E|by apply bool_decide_eq_true in H1|by apply bool_decide_eq_true in H2].
Qed.

(* [T] mentions no hypothesis and no evar.  [vm_compute] on a term with a
   free variable can diverge (and crash coqc): it normalises under the
   well-founded-recursion guards of stdpp's finite maps. *)
Ltac assert_ground T :=
  assert_fails (has_evar T);
  assert_fails (idtac; match goal with x : _ |- _ => lazymatch T with context [x] => idtac end end).

(* [D ⊢ₗ RCons (SAbs s) X ≤R X @ true], decided by computation (as
   [erase_absent] in scheduler_typed.v:59 decides [D !! s]).  Only tried
   when [D], [s] and [X] are ground. *)
Ltac erase_head :=
  lazymatch goal with
  | |- le._row ?D true (RCons ?σ ?X) _ =>
      assert_ground constr:((D, σ, X));
      eapply le.RTrans_le; [apply erase_check_le; vm_compute; reflexivity|]
  end.

(* Erasure needs the [SAbs] at the head of the source, and only at flag
   [true], which is lost as soon as a signature is matched ([RCons_le] takes
   its tail at [false]).  So [SAbs] signatures are pulled to the head of the
   source and erased first.  [sfront_src σ X X']: [X] has [σ]; [X'] is [X]
   without it. *)
Definition sfront_src (σ : eff_sig) (X X' : row) : Prop :=
  ∀ D b, D ⊢ₗ X ≤R RCons σ X' @ b.

Lemma src_here σ X : sfront_src σ (RCons σ X) X.
Proof. intros D b. apply RRefl_le. Qed.

Lemma src_there σ τ X X' : sfront_src σ X X' → sfront_src σ (RCons τ X) (RCons τ X').
Proof.
  intros H D b. eapply le.RTrans_le; [|apply le.RSwap_le].
  apply le.RCons_le; [apply SRefl_le|apply H].
Qed.

Lemma src_pull D b σ X X' Y :
  sfront_src σ X X' → D ⊢ₗ RCons σ X' ≤R Y @ b → D ⊢ₗ X ≤R Y @ b.
Proof. intros Hf H. eapply le.RTrans_le; [apply Hf|exact H]. Qed.

(* Finds an [SAbs] in the signature prefix, with backtracking. *)
Ltac sabs_find :=
  (lazymatch goal with
   | |- sfront_src _ (RCons (SAbs _) _) _ => apply src_here
   | |- sfront_src _ (RCons (SSig _ TBot TTop) _) _ => apply src_here
   end) + (apply src_there; sabs_find).

(* [row_incl sfind] proves [D ⊢ₗ X ≤R Y @ b] for [X], [Y] in normal form:
   at flag [true], [SAbs] signatures of [X] are erased where possible
   ([sabs_find] + [erase_head]); then every signature of [X] is matched with
   a distinct signature of [Y] ([sfind]), every atom of [X] with a distinct
   atom of [Y] ([afind]); the rest of [Y] is dropped.  No contraction:
   [{σ, σ} ≤ {σ}] fails. *)
Ltac row_incl sfind :=
  lazymatch goal with
  | |- _ ⊢ₗ RNil ≤R _ @ _ => apply le.RBot_le
  | |- _ ⊢ₗ RCons _ _ ≤R _ @ true =>
      first [ eapply src_pull; [sabs_find|erase_head; row_incl sfind]
            | eapply spick_le; [sfind|row_incl sfind] ]
  | |- _ ⊢ₗ RCons _ _ ≤R _ @ _ => eapply spick_le; [sfind|row_incl sfind]
  | |- _ ⊢ₗ _ ≤R RCons _ _ @ _ => apply drop_sig_le; row_incl sfind
  | |- _ ⊢ₗ RUnion _ _ ≤R _ @ _ => eapply apick_le; [afind|row_incl sfind]
  end.

Ltac row_norm_intro :=
  lazymatch goal with
  | |- let _ := _ in _ => let D := fresh "D" in intros D; subst D; row_norm_intro
  | |- le._row ?D ?b ?ρ1 ?ρ2 =>
      let x1 := reify_row ρ1 in
      let x2 := reify_row ρ2 in
      apply (rsyn_le_intro D b x1 x2);
      cbn [rsyn_norm denorm foldr app map]
  end.

(* [row_le_solve] proves [D ⊢ₗ ρ' ≤R ρ @ b]: normalise both sides, then
   inclusion with exact signature matching; if that fails, inclusion up to
   [≤S] with backtracking. *)
Ltac row_le_solve :=
  first [ apply RRefl_le
        | apply le.RBot_le
        | row_norm_intro;
          first [ row_incl sfind_eq | row_incl sfind_le ] ].

#[export] Hint Extern 5 (le._row _ _ _ _) => solve [row_le_solve] : tychk.

(** ** [le.OnceR] *)

(* [OnceR ρ] is [∃ b, ∅ ⊢ₗ ¡[OS] ρ ≤R ρ @ b].  Normalising [¡[OS] ρ] puts
   [SFlip OS] on every signature and [RFlip OS] on every atom of [ρ]; the
   inclusion closes by [SFlipIdemp1_le] / [RFlipIdemp1_le] when every
   signature and atom of [ρ] is one-shot flipped.  A plain [RVar i], an
   unflipped signature (e.g. [SAbs s]) or an MS-flipped one is not
   one-shot, and stays a residual goal. *)
Ltac once_solve :=
  lazymatch goal with
  | |- le.OnceR _ =>
      first [ exists true; apply le.RFlipNil_le
            | exists true; apply le.RFlipIdemp1_le
            | exists true; row_le_solve ]
  end.

#[export] Hint Extern 1 (le.OnceR _) => solve [once_solve] : tychk.

(* ================================================================== *)
(** * Tests                                                            *)
(* ================================================================== *)

Section tests.

(** ** C3: probe tests *)

Local Lemma test1 D b σ1 σ2 σ3 :
  D ⊢ₗ RCons σ2 RNil ≤R RCons σ1 (RCons σ2 (RCons σ3 RNil)) @ b.
Proof. row_le_solve. Qed.

Local Lemma test2 D b σ1 σ2 σ3 :
  D ⊢ₗ RUnion (RCons σ3 RNil) (RCons σ1 RNil) ≤R RCons σ1 (RCons σ2 (RCons σ3 RNil)) @ b.
Proof. row_le_solve. Qed.

Local Lemma test3 D b σ1 σ2 σ3 :
  D ⊢ₗ RCons σ3 (RCons σ2 (RCons σ1 RNil)) ≤R RUnion (RCons σ1 RNil) (RUnion RNil (RCons σ2 (RCons σ3 RNil))) @ b.
Proof. row_le_solve. Qed.

Local Lemma test_neg D b σ1 σ2 :
  D ⊢ₗ RCons σ2 RNil ≤R RCons σ1 RNil @ b.
Proof. Fail row_le_solve. Abort.

Local Lemma test4 D b σ1 σ2 i :
  D ⊢ₗ RCons σ1 (RVar i) ≤R RUnion (RVar i) (RCons σ2 (RCons σ1 RNil)) @ b.
Proof. row_le_solve. Qed.

Local Lemma test5 D b m σ1 σ2 :
  D ⊢ₗ RCons (SFlip m σ1) RNil ≤R RFlip m (RCons σ1 (RCons σ2 RNil)) @ b.
Proof. row_le_solve. Qed.

Local Lemma test6 D b m σ1 σ2 i :
  D ⊢ₗ RUnion (RFlip m (RVar i)) (RCons (SFlip m σ2) RNil)
       ≤R RFlip m (RCons σ1 (RCons σ2 (RVar i))) @ b.
Proof. row_le_solve. Qed.

(** ** C3: opaque rows *)

Local Lemma test_opaque D b σ ρ ρ' :
  D ⊢ₗ RUnion ρ' (RCons σ ρ) ≤R RCons σ (RUnion ρ ρ') @ b.
Proof. row_le_solve. Qed.

Local Lemma test_opaque_extend D b σ1 σ2 ρ :
  D ⊢ₗ ρ ≤R RCons σ1 (RCons σ2 ρ) @ b.
Proof. row_le_solve. Qed.

(** ** C3: signatures up to [≤S] *)

Local Lemma test_sig_idemp D b m σ1 σ2 :
  D ⊢ₗ RCons (SFlip m (SFlip m σ1)) RNil ≤R RCons σ2 (RCons (SFlip m σ1) RNil) @ b.
Proof. row_le_solve. Qed.

Local Lemma test_sig_elim D b σ1 σ2 :
  D ⊢ₗ RCons (SFlip MS σ1) (RCons σ2 RNil) ≤R RCons σ2 (RCons σ1 RNil) @ b.
Proof. row_le_solve. Qed.

(* MS is above OS: [SFlip MS σ ≤S SFlip OS σ] by [SFlipComp_le]. *)
Local Lemma test_sig_comp D b σ :
  D ⊢ₗ RCons (SFlip MS σ) RNil ≤R RCons (SFlip OS σ) RNil @ b.
Proof. row_le_solve. Qed.

(* Needs backtracking: [σ1] fits both [SFlip OS σ1] (by [SFlipIntro_le])
   and [σ1]; exact matching takes the right one. *)
Local Lemma test_sig_bt D b σ1 :
  D ⊢ₗ RCons σ1 (RCons (SFlip OS σ1) RNil) ≤R RCons (SFlip OS σ1) (RCons σ1 RNil) @ b.
Proof. row_le_solve. Qed.

(* Needs backtracking in the [≤S] pass: the first candidate for
   [SFlip MS σ1] is [SFlip OS σ1] (by [SFlipComp_le]), but then
   [SFlip OS σ1] finds no partner. *)
Local Lemma test_sig_bt2 D b σ1 σ2 :
  D ⊢ₗ RCons (SFlip MS σ1) (RCons (SFlip OS (SFlip OS σ1)) (RCons σ2 RNil))
       ≤R RCons (SFlip OS σ1) (RCons σ2 (RCons σ1 RNil)) @ b.
Proof. row_le_solve. Qed.

Local Lemma test_atom_idemp D b m i :
  D ⊢ₗ RFlip m (RFlip m (RVar i)) ≤R RFlip m (RVar i) @ b.
Proof. row_le_solve. Qed.

(* No contraction. *)
Local Lemma test_no_contraction D b σ :
  D ⊢ₗ RCons σ (RCons σ RNil) ≤R RCons σ RNil @ b.
Proof. Fail row_le_solve. Abort.

(** ** C3: erasure *)

(* The row premise of [erase_absent] (scheduler_typed.v:59). *)
Local Lemma test_erase_absent :
  le.row_to_disj_ctx (RCons (SAbs "w") RNil) ⊢ₗ RCons (SAbs "w") RNil ≤R RNil @ true.
Proof. row_le_solve. Qed.

(* [erase_absent] itself, through [TArrow_le]. *)
Local Lemma test_erase_absent_arrow (m : vmode) τ κ :
  le.row_to_disj_ctx (RCons (SAbs "w") RNil)
    ⊢ₗ (![m] (τ -{ RCons (SAbs "w") RNil }-∘ κ)) ≤T (![m] (τ -∘ κ)).
Proof.
  eapply le.TBangComp_le; [apply le.MRefl_le|].
  eapply (le.TArrow_le _ _ _ _ _ _ _ true); [apply le.TRefl_le|row_le_solve|apply le.TRefl_le].
Qed.

(* Erasure with a remaining signature whose name is in the ambient row. *)
Local Lemma test_erase_rest σ :
  le.row_to_disj_ctx (RCons (SAbs "w") (RCons (SSig "v" TUnit TUnit) RNil))
    ⊢ₗ RCons (SAbs "w") (RCons (SSig "v" TUnit TUnit) RNil)
       ≤R RCons σ (RCons (SSig "v" TUnit TUnit) RNil) @ true.
Proof. row_le_solve. Qed.

(* An [SAbs] behind another signature is pulled to the front first. *)
Local Lemma test_erase_inner :
  le.row_to_disj_ctx (RCons (SAbs "w") (RCons (SSig "v" TUnit TUnit) RNil))
    ⊢ₗ RCons (SSig "v" TUnit TUnit) (RCons (SAbs "w") RNil)
       ≤R RCons (SSig "v" TUnit TUnit) RNil @ true.
Proof. row_le_solve. Qed.

(* Two absent signatures. *)
Local Lemma test_erase_two :
  le.row_to_disj_ctx (RCons (SAbs "w") (RCons (SAbs "u") RNil))
    ⊢ₗ RCons (SAbs "u") (RCons (SAbs "w") RNil) ≤R RNil @ true.
Proof. row_le_solve. Qed.

(* Erasure fails when the rest mentions a name not in the ambient row;
   here the [SAbs] must be matched instead. *)
Local Lemma test_erase_match :
  le.row_to_disj_ctx (RCons (SAbs "w") RNil)
    ⊢ₗ RCons (SAbs "w") (RCons (SSig "v" TUnit TUnit) RNil)
       ≤R RCons (SSig "v" TUnit TUnit) (RCons (SAbs "w") RNil) @ true.
Proof. row_le_solve. Qed.

(* A [let]-bound disjointness context, as in the premises of [App_typed]. *)
Local Lemma test_let ρ :
  let D := le.row_to_disj_ctx ρ in D ⊢ₗ RCons (SAbs "w") ρ ≤R RCons (SAbs "w") (RUnion RNil ρ) @ true.
Proof. row_le_solve. Qed.

(* Not at flag false. *)
Local Lemma test_erase_false :
  le.row_to_disj_ctx (RCons (SAbs "w") RNil) ⊢ₗ RCons (SAbs "w") RNil ≤R RNil @ false.
Proof. Fail row_le_solve. Abort.

(** ** C1: [le.OnceR] *)

Local Lemma test_once_flip σ : le.OnceR (RCons (SFlip OS σ) RNil).
Proof. once_solve. Qed.

Local Lemma test_once_flip2 σ1 σ2 i :
  le.OnceR (RCons (SFlip OS σ1) (RCons (SFlip OS σ2) (RFlip OS (RVar i)))).
Proof. once_solve. Qed.

(* [SFlip MS σ] is equivalent to [σ] ([SFlipElim_le], [SFlipIntro_le]), so
   it is not one-shot. *)
Local Lemma test_once_ms σ : le.OnceR (RCons (SFlip MS σ) RNil).
Proof. Fail once_solve. Abort.

(* The row [ρw] of scheduler_typed.v (mode written with the coercion from
   [syntax.mode]). *)
Local Lemma test_once_w :
  le.OnceR (RCons (SFlip syntax.OS (SSig "w" TUnit TUnit)) RNil).
Proof. once_solve. Qed.

Local Lemma test_once_hint σ τ : RCons (SFlip OS σ) RNil R⪯T τ.
Proof. tychk_side. Qed.

Local Lemma test_once_neg i : le.OnceR (RVar i).
Proof. Fail once_solve. Abort.

(** ** C1: side predicates *)

Local Lemma test_multiC :
  le.MultiC [("x", TInt); ("f", (TInt ⇾ TInt)%ty); ("p", (TBool * (TUnit + TNat))%ty)].
Proof. tychk_side. Qed.

Local Lemma test_multiC_empty : le.MultiC ∅.
Proof. tychk_side. Qed.

Local Lemma test_mode_MS :
  MS m⪯C [("x", TInt); ("f", (TInt ⇾ TInt)%ty)].
Proof. tychk_side. Qed.

Local Lemma test_mode_MS_coerced :
  syntax.MS m⪯C [("x", TInt); ("f", (TInt ⇾ TInt)%ty)].
Proof. tychk_side. Qed.

Local Lemma test_mode_OS τ : OS m⪯C [("x", τ); ("y", TInt)].
Proof. tychk_side. Qed.

Local Lemma test_row_ctx σ τ :
  RCons (SFlip OS σ) RNil R⪯C [("x", τ); ("y", TInt)].
Proof. tychk_side. Qed.

Local Lemma test_multi_coerced τ :
  le.MultiT (TBang syntax.MS τ * (TBool + TUnit))%ty.
Proof. tychk_side. Qed.

Local Lemma test_multi_forallR :
  le.MultiT (∀R: ((() -{ RVar 0 }-> ()) -{ RVar 0 }-> ()))%ty.
Proof. tychk_side. Qed.

(** ** C2: context operations *)

Local Lemma test_take Δ τ :
  Δ .| [("a", TInt); ("b", τ); ("c", TBool)] ⊢ₜ Var "b" : RNil : τ
     ⊣ [("a", TInt); ("c", TBool)].
Proof. apply typed_var_take. solve_ctx_pick. Qed.

Local Lemma test_copy Δ σ :
  Δ .| [("a", TInt); ("b", TBool)] ⊢ₜ Var "b" : RCons σ RNil : TBool
     ⊣ [("a", TInt); ("b", TBool)].
Proof. eapply typed_var_copy_pick; [solve_ctx_pick|tychk_side]. Qed.

Local Lemma test_without Δ e ρ κ Γ2 :
  Δ .| [("b", TBool)] ⊢ₜ e : ρ : κ ⊣ Γ2 →
  Δ .| [("a", TInt); ("b", TBool); ("a", TUnit)] ⊢ₜ e : ρ : κ ⊣ Γ2.
Proof. intros He. eapply typed_without; [|exact He]. solve_ctx_without. Qed.

(** ** Smoke test: scheduler_typed.v helpers from C1/C2 only *)

(* [typed_var_bang] (scheduler_typed.v:102). *)
Local Lemma typed_var_bang' Δ (x : string) (m : vmode) τ Γ :
  Δ .| (x, (![m] τ)%ty) :: Γ ⊢ₜ Var x : RNil : τ ⊣ Γ.
Proof. eapply typed_var_take_bang. solve_ctx_pick. Qed.

(* [typed_call] (scheduler_typed.v:117). *)
Local Lemma typed_call' Δ Γ1 Γ2 (f : string) e τ κ σ :
  (f, (τ ⇾ κ)%ty) ∈ Γ2 →
  Δ .| Γ1 ⊢ₜ e : RCons σ RNil : τ ⊣ Γ2 →
  Δ .| Γ1 ⊢ₜ App (Var f) e : RCons σ RNil : κ ⊣ Γ2.
Proof.
  intros Hin He. apply list_elem_of_split in Hin as (pre & post & ->).
  eapply (App_typed _ _ _ _ _ _ _ RNil RNil true τ κ);
    [row_le_solve|row_le_solve|tychk_side|tychk_side|exact He|].
  apply typed_var_copy_bang.
Qed.

(* A call by name in a concrete context, as in [Zsched_typed]:
   [let: "s1" := "step" "s1"], with the argument consumed and the function
   copied.  The typing premises go first so that [τ] is known before the
   side conditions ([RNil R⪯T τ] would otherwise instantiate an evar). *)
Local Lemma test_call_by_name Δ σ τ κ :
  Δ .| [("s1", τ); ("step", (τ ⇾ κ)%ty); ("run", (() ⇾ τ)%ty)]
     ⊢ₜ App (Var "step") (Var "s1") : RCons σ RNil : κ
     ⊣ [("step", (τ ⇾ κ)%ty); ("run", (() ⇾ τ)%ty)].
Proof.
  eapply (App_typed _ _ _ _ _ _ _ RNil RNil true);
    [idtac|idtac|idtac|idtac
    |eapply typed_var_take; solve_ctx_pick
    |eapply typed_var_copy_bang_pick; solve_ctx_pick].
  all: first [row_le_solve|tychk_side].
Qed.

(* [typed_var_at] (scheduler_typed.v:110). *)
Local Lemma typed_var_at' Δ Γ Γ' (x : string) τ σ :
  Γ ≡ₚ (x, τ) :: Γ' →
  Δ .| Γ ⊢ₜ Var x : RCons σ RNil : τ ⊣ Γ'.
Proof. intros Hp. eapply typed_pick; [exact Hp|]. by apply typed_var_take, ctx_pick_here. Qed.

End tests.

(* ================================================================== *)
(** * C4: rules in algorithmic form                                    *)
(* ================================================================== *)

(** Each lemma below is a derived rule whose premises are ordered for the
    driver [tychk] (Stage D): the typing premises come in evaluation order
    (right operand first), so that each output context is known before it
    is used; side conditions come after the premises that fix their evars.
    Inputs are [Δ], the input context, the expression and the row; the type
    is checked (an evar when it is to be synthesised); the output context
    is always computed (an evar). *)

(** ** Annotations (PLAN.md section 4)

    Identity wrappers, so that theorem statements keep the plain expression:
    a proof [change]s the program to its annotated copy (convertible) and
    calls [tychk].  [simpl never] keeps [simpl]/[cbn] from removing them
    before the driver has read them. *)
Definition tyann (_ : type) (e : expr) : expr := e.
Definition sigann (_ : eff_name) (_ _ : type) (e : expr) : expr := e.
Arguments tyann : simpl never.
Arguments sigann : simpl never.

(** ** Contexts *)

(* The driver always computes the output context; a required output is
   reached by weakening. *)
Lemma typed_out_le Δ Γ e ρ κ Γ2 Γ2' :
  Δ .| Γ ⊢ₜ e : ρ : κ ⊣ Γ2' → Γ2 ⊆+ Γ2' → Δ .| Γ ⊢ₜ e : ρ : κ ⊣ Γ2.
Proof. intros He Hs. by eapply typed_out_sub. Qed.

Lemma sub_pick (x : string) τ l1 l2 l2' :
  ctx_pick x l2 τ l2' → l1 ⊆+ l2' → (x, τ) :: l1 ⊆+ l2.
Proof. rewrite /ctx_pick => -> Hs. by apply submseteq_skip. Qed.

Ltac solve_submseteq :=
  first [ reflexivity
        | apply submseteq_nil_l
        | eapply sub_pick; [solve_ctx_pick|solve_submseteq] ].

Lemma elem_of_ctx_dom (y : string) Γ : y ∈ ctx_dom Γ ↔ ∃ τ, (y, τ) ∈ Γ.
Proof.
  induction Γ as [|[z t] Γ IH].
  - rewrite /ctx_dom /=. split; [set_solver|]. intros [? Hin]. set_solver.
  - change (ctx_dom ((z, t) :: Γ)) with ({[z]} ∪ ctx_dom Γ).
    rewrite elem_of_union elem_of_singleton IH. split.
    + intros [->|[τ Hin]]; [exists t; set_solver|exists τ; set_solver].
    + intros [τ Hin]. apply elem_of_cons in Hin as [[= -> ->]|Hin]; [by left|].
      right. by exists τ.
Qed.

Lemma ctx_dom_submseteq (x : binder) Γ Γ' :
  Γ' ⊆+ Γ → x ∉ ctx_dom Γ → x ∉ ctx_dom Γ'.
Proof.
  destruct x as [|x]; [intros _ _ []|].
  intros Hs Hx Hx'. apply Hx.
  change (x ∈ ctx_dom Γ). change (x ∈ ctx_dom Γ') in Hx'.
  apply elem_of_ctx_dom in Hx' as [τ Hin]. apply elem_of_ctx_dom.
  exists τ. by eapply elem_of_submseteq.
Qed.

Lemma ctx_dom_submseteq_s (x : string) Γ Γ' :
  Γ' ⊆+ Γ → x ∉ ctx_dom Γ → x ∉ ctx_dom Γ'.
Proof. apply (ctx_dom_submseteq (BNamed x)). Qed.

(** *** Dropping the entries shadowed by a binder *)

Definition ctx_without_b (x : binder) (Γ Γ' : ctx) : Prop :=
  Γ' ⊆+ Γ ∧ x ∉ ctx_dom Γ'.

Lemma cwb_anon Γ : ctx_without_b BAnon Γ Γ.
Proof. split; [done|]. intros []. Qed.

Lemma cwb_named (x : string) Γ Γ' :
  ctx_without x Γ Γ' → ctx_without_b (BNamed x) Γ Γ'.
Proof. intros [H1 H2]. split; [exact H1|exact H2]. Qed.

Ltac solve_without_b :=
  lazymatch goal with
  | |- ctx_without_b BAnon _ _ => apply cwb_anon
  | |- ctx_without_b (BNamed _) _ _ => apply cwb_named; solve_ctx_without
  end.

(** *** Joining the outputs of two branches ([If], [Match]) *)

(* [Γ3] is computed as the multiset intersection of the two outputs,
   without the entries named by the branch binders. *)
Definition ctx_join (x y : binder) (Γa Γb Γ3 : ctx) : Prop :=
  Γ3 ⊆+ Γa ∧ Γ3 ⊆+ Γb ∧ x ∉ ctx_dom Γ3 ∧ y ∉ ctx_dom Γ3.

(** *** Splitting a context for a closure ([Rec], pure judgement) *)

(* [ctx_split Γ Γm Γc Γr]: [Γ] is [Γm] (moved into the closure) and [Γr]
   (the rest); [Γc] lists copies of entries of [Γr] (copyable entries the
   closure captures without consuming them). *)
Definition ctx_split (Γ Γm Γc Γr : ctx) : Prop :=
  Γ ≡ₚ Γm ++ Γr ∧ Forall (λ p, p ∈ Γr) Γc.

Lemma split_rest Γ : ctx_split Γ [] [] Γ.
Proof. split; [done|constructor]. Qed.

Lemma split_move p Γ Γm Γc Γr :
  ctx_split Γ Γm Γc Γr → ctx_split (p :: Γ) (p :: Γm) Γc Γr.
Proof. intros [Hp HF]. split; [by rewrite Hp|done]. Qed.

Lemma split_keep p Γ Γm Γc Γr :
  ctx_split Γ Γm Γc Γr → ctx_split (p :: Γ) Γm Γc (p :: Γr).
Proof.
  intros [Hp HF]. split.
  - rewrite Hp. apply Permutation_middle.
  - eapply Forall_impl; [exact HF|]. intros q Hq. set_solver.
Qed.

Lemma split_copy p Γ Γm Γc Γr :
  ctx_split Γ Γm Γc Γr → ctx_split (p :: Γ) Γm (p :: Γc) (p :: Γr).
Proof.
  intros Hs. destruct (split_keep p _ _ _ _ Hs) as [Hp HF]. split; [done|].
  constructor; [set_solver|done].
Qed.

(** *** Contraction of a list of copyable entries *)

Lemma typed_contract_one Δ (x : string) τ Γ e ρ κ Γ2 :
  le.MultiT τ → (x, τ) ∈ Γ →
  Δ .| (x, τ) :: Γ ⊢ₜ e : ρ : κ ⊣ Γ2 → Δ .| Γ ⊢ₜ e : ρ : κ ⊣ Γ2.
Proof.
  intros Hτ Hin He.
  apply list_elem_of_split in Hin as (pre & post & ->).
  apply typed_front.
  apply (Contraction_typed _ (pre ++ post) _ _ _ _ (BNamed x) τ Hτ).
  eapply typed_perm; [|exact He]. cbn [ctx_insert].
  apply perm_skip, Permutation_middle.
Qed.

Lemma typed_contract_list Δ Γc Γ e ρ κ Γ2 :
  le.MultiC Γc → Forall (λ p, p ∈ Γ) Γc →
  Δ .| Γc ++ Γ ⊢ₜ e : ρ : κ ⊣ Γ2 → Δ .| Γ ⊢ₜ e : ρ : κ ⊣ Γ2.
Proof.
  induction Γc as [|[x τ] Γc IH]; intros HM HF He; [exact He|].
  rewrite /le.MultiC fmap_cons in HM. apply Forall_cons in HM as [Hτ HM].
  apply Forall_cons in HF as [Hin HF].
  apply IH; [exact HM|exact HF|].
  apply (typed_contract_one _ x τ); [exact Hτ| |exact He].
  set_solver.
Qed.

(** ** Values: [⊢ᵥ v : τ] *)

Lemma val_sub_alg v κ τ : ⊢ᵥ v : κ → ∅ ⊢ₗ κ ≤T τ → ⊢ᵥ v : τ.
Proof. intros Hv Hle. by eapply Sub_val_typed. Qed.

(* An integer literal is a natural when it is non-negative. *)
Lemma Nat_val_alg (z : Z) : (0 ≤ z)%Z → ⊢ᵥ LitV (LitInt z) : ℕ.
Proof. intros Hz. rewrite -(Z2Nat.id z Hz). apply Nat_val_typed. Qed.

(* A closed function at a bare arrow: [Rec_val_typed] at mode [MS] (so a
   recursive function may call itself several times), then [TBangElim_le]
   (as in [DH_real_typed], dhke_common.v). *)
Lemma Rec_val_bare f x e τ1 ρ τ2 :
  match f with BNamed f => BNamed f ≠ x | BAnon => True end →
  ∅ .| <[f:=c τ1 -{ ρ }-[MS]-> τ2]>(<[x:=c τ1]> ∅) ⊢ₜ e : ρ : τ2 ⊣ ∅ →
  ⊢ᵥ RecV f x e : TArrow τ1 ρ τ2.
Proof.
  intros Hf He. eapply val_sub_alg; [by apply Rec_val_typed|]. apply le.TBangElim_le.
Qed.

(** ** Expressions: leaves *)

Lemma Var_copy_alg Δ (x : string) Γ τx Γ' τ ρ :
  ctx_pick x Γ τx Γ' → le.MultiT τx → le.row_to_disj_ctx ρ ⊢ₗ τx ≤T τ →
  Δ .| Γ ⊢ₜ Var x : ρ : τ ⊣ Γ.
Proof.
  intros Hp HM Hle. eapply typed_sub_type; [exact Hle|].
  by eapply typed_var_copy_pick.
Qed.

Lemma Var_take_alg Δ (x : string) Γ τx Γ' τ ρ :
  ctx_pick x Γ τx Γ' → le.row_to_disj_ctx ρ ⊢ₗ τx ≤T τ →
  Δ .| Γ ⊢ₜ Var x : ρ : τ ⊣ Γ'.
Proof. apply typed_var_take_le. Qed.

Lemma tyann_alg Δ Γ1 Γ2 e ρ τ τ' :
  Δ .| Γ1 ⊢ₜ e : ρ : τ' ⊣ Γ2 → le.row_to_disj_ctx ρ ⊢ₗ τ' ≤T τ →
  Δ .| Γ1 ⊢ₜ tyann τ' e : ρ : τ ⊣ Γ2.
Proof. intros He Hle. by eapply typed_sub_type. Qed.

(** ** Functions *)

(* [Rec_typed] with the closure computed by [ctx_split]: [Γm] is moved into
   the closure, [Γc] is copied (contraction), [Γr] is the output. *)
Lemma Rec_alg Δ Γ Γm Γc Γr f x e (m : vmode) ρ0 τ κ ρ :
  ctx_split Γ Γm Γc Γr → le.MultiC Γc →
  match f with BNamed f => BNamed f ≠ x ∧ le.MultiC (Γc ++ Γm) | BAnon => m m⪯C (Γc ++ Γm) end →
  f ∉ ctx_dom (Γc ++ Γm) → x ∉ ctx_dom (Γc ++ Γm) →
  Δ .| <[ f :=c (τ -{ ρ0 }-[m]-> κ)%ty ]> <[ x :=c τ ]> (Γc ++ Γm) ⊢ₜ e : ρ0 : κ ⊣ ∅ →
  Δ .| Γ ⊢ₜ Rec f x e : ρ : τ -{ ρ0 }-[m]-> κ ⊣ Γr.
Proof.
  intros [Hp HF] HM Hf Hfx Hxx He.
  apply typed_row_nil. eapply typed_perm; [exact Hp|].
  apply (typed_contract_list _ Γc); [exact HM| |].
  { eapply Forall_impl; [exact HF|]. intros p Hin. set_solver. }
  rewrite app_assoc. by apply (Rec_typed _ (Γc ++ Γm) Γr).
Qed.

(* At a bare arrow: [Rec_alg], then [TBangElim_le]. *)
Lemma Rec_alg_bare Δ Γ Γm Γc Γr f x e (m : vmode) ρ0 τ κ ρ :
  ctx_split Γ Γm Γc Γr → le.MultiC Γc →
  match f with BNamed f => BNamed f ≠ x ∧ le.MultiC (Γc ++ Γm) | BAnon => m m⪯C (Γc ++ Γm) end →
  f ∉ ctx_dom (Γc ++ Γm) → x ∉ ctx_dom (Γc ++ Γm) →
  Δ .| <[ f :=c (τ -{ ρ0 }-[m]-> κ)%ty ]> <[ x :=c τ ]> (Γc ++ Γm) ⊢ₜ e : ρ0 : κ ⊣ ∅ →
  Δ .| Γ ⊢ₜ Rec f x e : ρ : TArrow τ ρ0 κ ⊣ Γr.
Proof.
  intros. eapply typed_sub_type; [apply le.TBangElim_le|]. by eapply Rec_alg.
Qed.

(* The pure judgement, for closures at quantified types (no introduction
   rule for quantifiers exists in [typed]). *)
Lemma Pure_alg Δ Γ Γm Γc Γr e τ ρ :
  ctx_split Γ Γm Γc Γr → le.MultiC Γc →
  Δ ..| Γc ++ Γm ⊢ₚ e : τ →
  Δ .| Γ ⊢ₜ e : ρ : τ ⊣ Γr.
Proof.
  intros [Hp HF] HM He.
  apply typed_row_nil. eapply typed_perm; [exact Hp|].
  apply (typed_contract_list _ Γc); [exact HM| |].
  { eapply Forall_impl; [exact HF|]. intros p Hin. set_solver. }
  rewrite app_assoc. by apply (Pure_typed _ (Γc ++ Γm) Γr).
Qed.

(** *** Application *)

(* [fn_coerce F A]: an expression of type [F] can be used at type [A].  The
   driver builds it from the type [F] of the function position: strip
   [TBang] ([TBangElim_le]) and instantiate quantifiers ([RAbsElim_typed],
   [TAbsElim_typed], [MAbsElim_typed]) until a bare arrow is reached. *)
Definition fn_coerce (F A : type) : Prop :=
  ∀ Δ Γ Γ' e ρ, Δ .| Γ ⊢ₜ e : ρ : F ⊣ Γ' → Δ .| Γ ⊢ₜ e : ρ : A ⊣ Γ'.

Lemma fnc_refl F : fn_coerce F F.
Proof. by intros ?????. Qed.

Lemma fnc_bang m F A : fn_coerce F A → fn_coerce (TBang m F) A.
Proof.
  intros H Δ Γ Γ' e ρ He. apply H.
  eapply typed_sub_type; [apply le.TBangElim_le|exact He].
Qed.

Lemma fnc_rall α (ρi : row) F A : α.|[ρi/] = F → fn_coerce F A → fn_coerce (TForallR α) A.
Proof. intros <- H Δ Γ Γ' e ρ He. apply H. by apply RAbsElim_typed. Qed.

Lemma fnc_tall α (τi : type) F A : α.[τi/] = F → fn_coerce F A → fn_coerce (TForallT α) A.
Proof. intros <- H Δ Γ Γ' e ρ He. apply H. by apply TAbsElim_typed. Qed.

Lemma fnc_mall α (mi : vmode) F A : α.|[mi/] = F → fn_coerce F A → fn_coerce (TForallM α) A.
Proof. intros <- H Δ Γ Γ' e ρ He. apply H. by apply MAbsElim_typed. Qed.

(* [App_typed] with both side rows fixed by the function: the function
   position is typed at row [ρ1] ([RNil] for a variable or a value, else the
   ambient [ρ]), the latent row [ρf] is the one of the function's arrow; the
   flag is [true].  [F] is the type of the function position (known before
   the argument is typed, see [peek_fn]). *)
Lemma App_alg Δ Γ1 Γ2 Γ3 e1 e2 ρ ρ1 F τ ρf κ κ' :
  fn_coerce F (TArrow τ ρf κ) →
  le.row_to_disj_ctx ρ ⊢ₗ κ ≤T κ' →
  Δ .| Γ1 ⊢ₜ e2 : ρ : τ ⊣ Γ2 →
  Δ .| Γ2 ⊢ₜ e1 : ρ1 : F ⊣ Γ3 →
  le.row_to_disj_ctx ρ ⊢ₗ ρ1 ≤R ρ @ true → le.row_to_disj_ctx ρ ⊢ₗ ρf ≤R ρ @ true →
  ρ1 R⪯T τ → ρf R⪯C Γ3 →
  Δ .| Γ1 ⊢ₜ App e1 e2 : ρ : κ' ⊣ Γ3.
Proof.
  intros Hc Hκ H2 H1 Hr1 Hrf Ht Hc3.
  eapply typed_sub_type; [exact Hκ|].
  eapply (App_typed _ _ _ _ _ _ _ ρ1 ρf true τ κ);
    [exact Hr1|exact Hrf|exact Ht|exact Hc3|exact H2|].
  apply Hc. exact H1.
Qed.

(* The same with the premises in the order needed when the type of the
   function position cannot be found in advance: the argument is typed
   first (synthesised), then the function, then the coercion. *)
Lemma App_alg_late Δ Γ1 Γ2 Γ3 e1 e2 ρ ρ1 F τ ρf κ κ' :
  Δ .| Γ1 ⊢ₜ e2 : ρ : τ ⊣ Γ2 →
  Δ .| Γ2 ⊢ₜ e1 : ρ1 : F ⊣ Γ3 →
  fn_coerce F (TArrow τ ρf κ) →
  le.row_to_disj_ctx ρ ⊢ₗ κ ≤T κ' →
  le.row_to_disj_ctx ρ ⊢ₗ ρ1 ≤R ρ @ true → le.row_to_disj_ctx ρ ⊢ₗ ρf ≤R ρ @ true →
  ρ1 R⪯T τ → ρf R⪯C Γ3 →
  Δ .| Γ1 ⊢ₜ App e1 e2 : ρ : κ' ⊣ Γ3.
Proof. intros H2 H1 Hc Hκ. by eapply App_alg. Qed.

(** *** Binders *)

Lemma Let_alg Δ Γ1 Γ2 Γ2' Γ3 Γ3' (x : binder) e1 e2 ρ τ κ :
  Δ .| Γ1 ⊢ₜ e1 : ρ : τ ⊣ Γ2 →
  ctx_without_b x Γ2 Γ2' →
  Δ .| <[ x :=c τ ]> Γ2' ⊢ₜ e2 : ρ : κ ⊣ Γ3 →
  ctx_without_b x Γ3 Γ3' →
  Δ .| Γ1 ⊢ₜ (let: x := e1 in e2) : ρ : κ ⊣ Γ3'.
Proof.
  intros H1 [Hs2 Hx2] H2 [Hs3 Hx3].
  eapply Let_typed; [exact Hx2|exact Hx3| |].
  - by eapply typed_out_sub.
  - by eapply typed_out_sub.
Qed.

Lemma LetPair_alg Δ Γ1 Γ2 Γ2a Γ2' Γ3 Γ3a Γ3' (x1 x2 : string) e1 e2 ρ τ1 τ2 κ :
  x1 ≠ x2 →
  Δ .| Γ1 ⊢ₜ e1 : ρ : τ1 * τ2 ⊣ Γ2 →
  ctx_without_b x1 Γ2 Γ2a → ctx_without_b x2 Γ2a Γ2' →
  Δ .| <[ x1 :=c τ1 ]> <[ x2 :=c τ2 ]> Γ2' ⊢ₜ e2 : ρ : κ ⊣ Γ3 →
  ctx_without_b x1 Γ3 Γ3a → ctx_without_b x2 Γ3a Γ3' →
  Δ .| Γ1 ⊢ₜ (let, (x1, x2) := e1 in e2) : ρ : κ ⊣ Γ3'.
Proof.
  intros Hne H1 [Hs2a Hx2a] [Hs2 Hx2] H2 [Hs3a Hx3a] [Hs3 Hx3].
  apply LetPair_typed with (Γ2 := Γ2') (τ1 := τ1) (τ2 := τ2);
    [exact (ctx_dom_submseteq_s x1 _ _ Hs2 Hx2a)|exact Hx2
    |exact (ctx_dom_submseteq_s x1 _ _ Hs3 Hx3a)|exact Hx3|exact Hne| |].
  - eapply typed_out_sub; [|exact H1]. etrans; [exact Hs2|exact Hs2a].
  - eapply typed_out_sub; [|exact H2]. etrans; [exact Hs3|exact Hs3a].
Qed.

Lemma Match_alg Δ Γ1 Γ2 Γ2x Γ2' Γa Γb Γ3 e0 (x y : binder) e1 e2 ρ τ1 τ2 τ3 :
  Δ .| Γ1 ⊢ₜ e0 : ρ : τ1 + τ2 ⊣ Γ2 →
  ctx_without_b x Γ2 Γ2x → ctx_without_b y Γ2x Γ2' →
  Δ .| <[ x :=c τ1 ]> Γ2' ⊢ₜ e1 : ρ : τ3 ⊣ Γa →
  Δ .| <[ y :=c τ2 ]> Γ2' ⊢ₜ e2 : ρ : τ3 ⊣ Γb →
  ctx_join x y Γa Γb Γ3 →
  Δ .| Γ1 ⊢ₜ match: e0 with InjL x => e1 | InjR y => e2 end : ρ : τ3 ⊣ Γ3.
Proof.
  intros H0 [Hs1 Hx1] [Hs2 Hy2] H1 H2 (Ha & Hb & Hx3 & Hy3).
  eapply (Match_typed _ _ Γ2'); [exact (ctx_dom_submseteq x _ _ Hs2 Hx1)|exact Hx3|exact Hy2|exact Hy3| | |].
  - eapply typed_out_sub; [|exact H0]. etrans; [exact Hs2|exact Hs1].
  - eapply typed_out_sub; [exact Ha|exact H1].
  - eapply typed_out_sub; [exact Hb|exact H2].
Qed.

Lemma If_alg Δ Γ1 Γ2 Γa Γb Γ3 e0 e1 e2 ρ τ :
  Δ .| Γ1 ⊢ₜ e0 : ρ : 𝔹 ⊣ Γ2 →
  Δ .| Γ2 ⊢ₜ e1 : ρ : τ ⊣ Γa →
  Δ .| Γ2 ⊢ₜ e2 : ρ : τ ⊣ Γb →
  ctx_join BAnon BAnon Γa Γb Γ3 →
  Δ .| Γ1 ⊢ₜ If e0 e1 e2 : ρ : τ ⊣ Γ3.
Proof.
  intros H0 H1 H2 (Ha & Hb & _ & _).
  eapply If_typed; [exact H0|eapply typed_out_sub; [exact Ha|exact H1]|eapply typed_out_sub; [exact Hb|exact H2]].
Qed.

(** *** Operators, pairs, sums *)

Lemma BinOp_alg Δ Γ1 Γ2 Γ3 ι κ τ' τ ρ e1 e2 op :
  syn_typed_bin_op op ι κ τ' →
  Δ .| Γ1 ⊢ₜ e2 : ρ : κ ⊣ Γ2 → Δ .| Γ2 ⊢ₜ e1 : ρ : ι ⊣ Γ3 →
  le.row_to_disj_ctx ρ ⊢ₗ τ' ≤T τ →
  Δ .| Γ1 ⊢ₜ BinOp op e1 e2 : ρ : τ ⊣ Γ3.
Proof. intros Hop H2 H1 Hle. eapply typed_sub_type; [exact Hle|]. by eapply BinOp_typed. Qed.

Lemma UnOp_alg Δ Γ1 Γ2 κ τ' τ ρ e op :
  syn_typed_un_op op κ τ' →
  Δ .| Γ1 ⊢ₜ e : ρ : κ ⊣ Γ2 →
  le.row_to_disj_ctx ρ ⊢ₗ τ' ≤T τ →
  Δ .| Γ1 ⊢ₜ UnOp op e : ρ : τ ⊣ Γ2.
Proof. intros Hop H Hle. eapply typed_sub_type; [exact Hle|]. by eapply UnOp_typed. Qed.

Lemma Pair_alg Δ Γ1 Γ2 Γ3 e1 e2 ρ τ1 τ2 :
  Δ .| Γ1 ⊢ₜ e2 : ρ : τ2 ⊣ Γ2 → Δ .| Γ2 ⊢ₜ e1 : ρ : τ1 ⊣ Γ3 →
  ρ R⪯T τ2 →
  Δ .| Γ1 ⊢ₜ Pair e1 e2 : ρ : τ1 * τ2 ⊣ Γ3.
Proof. intros H2 H1 Hr. by eapply Pair_typed. Qed.

Lemma Fst_alg Δ Γ1 Γ2 e ρ τ1 τ2 τ :
  Δ .| Γ1 ⊢ₜ e : ρ : τ1 * τ2 ⊣ Γ2 → le.row_to_disj_ctx ρ ⊢ₗ τ1 ≤T τ →
  Δ .| Γ1 ⊢ₜ Fst e : ρ : τ ⊣ Γ2.
Proof. intros H Hle. eapply typed_sub_type; [exact Hle|]. by eapply Fst_typed. Qed.

Lemma Snd_alg Δ Γ1 Γ2 e ρ τ1 τ2 τ :
  Δ .| Γ1 ⊢ₜ e : ρ : τ1 * τ2 ⊣ Γ2 → le.row_to_disj_ctx ρ ⊢ₗ τ2 ≤T τ →
  Δ .| Γ1 ⊢ₜ Snd e : ρ : τ ⊣ Γ2.
Proof. intros H Hle. eapply typed_sub_type; [exact Hle|]. by eapply Snd_typed. Qed.

(** *** Recursive types *)

Lemma TFold_alg Δ Γ1 Γ2 e ρ τ τ' :
  τ.[(μ: τ)%ty/] = τ' →
  Δ .| Γ1 ⊢ₜ e : ρ : τ' ⊣ Γ2 → Δ .| Γ1 ⊢ₜ e : ρ : (μ: τ) ⊣ Γ2.
Proof. intros <-. apply TFold. Qed.

Lemma TUnfold_alg Δ Γ1 Γ2 e ρ τ τ' κ :
  Δ .| Γ1 ⊢ₜ e : ρ : (μ: τ) ⊣ Γ2 →
  τ.[(μ: τ)%ty/] = τ' →
  le.row_to_disj_ctx ρ ⊢ₗ τ' ≤T κ →
  Δ .| Γ1 ⊢ₜ rec_unfold e : ρ : κ ⊣ Γ2.
Proof. intros He <- Hle. eapply typed_sub_type; [exact Hle|]. by apply TUnfold. Qed.

(** *** References and sampling *)

Lemma LoadC_alg Δ Γ1 Γ2 e ρ τ κ :
  Δ .| Γ1 ⊢ₜ e : ρ : refᶜ τ ⊣ Γ2 → le.MultiT τ →
  le.row_to_disj_ctx ρ ⊢ₗ τ ≤T κ →
  Δ .| Γ1 ⊢ₜ Load e : ρ : κ ⊣ Γ2.
Proof. intros He HM Hle. eapply typed_sub_type; [exact Hle|]. by apply LoadC_typed. Qed.

Lemma StoreC_alg Δ Γ1 Γ2 Γ3 e1 e2 ρ τ κ :
  Δ .| Γ1 ⊢ₜ e2 : ρ : τ ⊣ Γ2 → Δ .| Γ2 ⊢ₜ e1 : ρ : refᶜ τ ⊣ Γ3 →
  ρ R⪯T τ → le.row_to_disj_ctx ρ ⊢ₗ () ≤T κ →
  Δ .| Γ1 ⊢ₜ Store e1 e2 : ρ : κ ⊣ Γ3.
Proof. intros H2 H1 Hr Hle. eapply typed_sub_type; [exact Hle|]. by eapply StoreC_typed. Qed.

(* Affine (typestate) references, on a variable. *)
Lemma TLoad_alg Δ (x : string) Γ τ Γ' ρ κ :
  ctx_pick x Γ (ref τ)%ty Γ' → le.row_to_disj_ctx ρ ⊢ₗ τ ≤T κ →
  Δ .| Γ ⊢ₜ Load (Var x) : ρ : κ ⊣ (x, (ref ⊤)%ty) :: Γ'.
Proof.
  intros Hp Hle. eapply typed_sub_type; [exact Hle|]. apply typed_row_nil.
  eapply typed_pick; [exact Hp|]. apply (TLoad _ Γ' x τ).
Qed.

Lemma TRandU_alg Δ Γ1 Γ2 Γ3 e1 e2 ρ τ :
  Δ .| Γ1 ⊢ₜ e2 : ρ : () ⊣ Γ2 → Δ .| Γ2 ⊢ₜ e1 : ρ : ℤ ⊣ Γ3 →
  le.row_to_disj_ctx ρ ⊢ₗ ℕ ≤T τ →
  Δ .| Γ1 ⊢ₜ Rand e1 e2 : ρ : τ ⊣ Γ3.
Proof. intros H2 H1 Hle. eapply typed_sub_type; [exact Hle|]. by eapply TRandU. Qed.

Lemma TRand_alg Δ Γ1 Γ2 Γ3 e1 e2 ρ τ :
  Δ .| Γ1 ⊢ₜ e2 : ρ : TTape ⊣ Γ2 → Δ .| Γ2 ⊢ₜ e1 : ρ : ℤ ⊣ Γ3 →
  le.row_to_disj_ctx ρ ⊢ₗ ℕ ≤T τ →
  Δ .| Γ1 ⊢ₜ Rand e1 e2 : ρ : τ ⊣ Γ3.
Proof. intros H2 H1 Hle. eapply typed_sub_type; [exact Hle|]. by eapply TRand. Qed.

Lemma TAllocTape_alg Δ Γ1 Γ2 e ρ τ :
  Δ .| Γ1 ⊢ₜ e : ρ : ℤ ⊣ Γ2 → le.row_to_disj_ctx ρ ⊢ₗ TTape ≤T τ →
  Δ .| Γ1 ⊢ₜ AllocTape e : ρ : τ ⊣ Γ2.
Proof. intros H Hle. eapply typed_sub_type; [exact Hle|]. by apply TAllocTape. Qed.

(** *** Effects and handlers *)

(* The output is weakened before the freshness check, so that only the
   entries the context needs are checked. *)
Lemma Effect_alg Δ Γ1 Γ2 Γ2' e s ρ τ :
  (<[ s := () ]> Δ) .| Γ1 ⊢ₜ e : RCons (SAbs s) ρ : τ ⊣ Γ2' →
  Γ2 ⊆+ Γ2' →
  vars._fresh s (Γ1 ++ Γ2) ρ τ →
  Δ .| Γ1 ⊢ₜ Effect s e : ρ : τ ⊣ Γ2.
Proof. intros He Hs Hf. eapply Effect_typed; [exact Hf|]. by eapply typed_out_sub. Qed.

(* [Do_typed] at a row where the signature is anywhere: [ρh] puts it at
   the head ([row_le_solve] proves [ρh ≤ ρ]). *)
Lemma Do_alg Δ Γ1 Γ2 (s : string) e ρ ρ0 (m : vmode) ι κ τi ι' κ' τ :
  le.row_to_disj_ctx ρ ⊢ₗ RCons (SFlip m (SSig s ι κ)) ρ0 ≤R ρ @ true →
  Δ !! s = Some () →
  ι.[τi/] = ι' → κ.[τi/] = κ' →
  Δ .| Γ1 ⊢ₜ e : RCons (SFlip m (SSig s ι κ)) ρ0 : ι' ⊣ Γ2 →
  m m⪯C Γ2 →
  le.row_to_disj_ctx ρ ⊢ₗ κ' ≤T τ →
  Δ .| Γ1 ⊢ₜ Do (EffName s) e : ρ : τ ⊣ Γ2.
Proof.
  intros Hρ HΔ <- <- He Hm Hτ.
  eapply (Sub_typed _ _ Γ1 _ Γ2 _ (RCons (SFlip m (SSig s ι κ)) ρ0) true _ (κ.[τi/]));
    [apply CRefl_le|apply CRefl_le|exact Hρ|exact Hτ|].
  by eapply Do_typed.
Qed.

(* [DeepHandle_typed]: the frame [Γ3] (copyable, threaded to both clauses
   and returned) is a list of copies of entries of the input context. *)
Lemma DeepHandle_alg Δ Γin Γ2 Γ2x Γ2' Γ3 (m : mode) (s : string) e (x k y : binder) h r
    ρ0 σ τ τ' ι κ :
  Forall (λ p, p ∈ Γin) Γ3 → le.MultiC Γ3 →
  Δ !! s = Some () → le.eff_name_from_sig σ = s →
  x ∉ ctx_dom Γ3 → k ∉ ctx_dom Γ3 → x ≠ k → y ∉ ctx_dom Γ3 →
  Δ .| Γin ⊢ₜ e : RCons (SFlip m (SSig s ι κ)) ρ0 : τ ⊣ Γ2 →
  ctx_without_b x Γ2 Γ2x → ctx_without_b y Γ2x Γ2' →
  Δ .| <[ y :=c τ ]> (Γ2' ;; Γ3) ⊢ₜ r : RCons σ ρ0 : τ' ⊣ Γ3 →
  Δ .| <[ x :=c ι ]> <[ k :=c ![m] (κ -{ rename_type_row (+1) (RCons σ ρ0) }-∘ τ'.[ren (+1)]) ]> (⤉ Γ3)
    ⊢ₜ h : rename_type_row (+1) (RCons σ ρ0) : τ'.[ren (+1)] ⊣ (⤉ Γ3) →
  Δ .| Γin ⊢ₜ Handle Deep m s e (Lam x (Lam k h)) (Lam y r) : RCons σ ρ0 : τ' ⊣ Γ3.
Proof.
  intros HF HM HΔ Hσ Hx3 Hk3 Hxk Hy3 He [Hs1 Hx2] [Hs2 Hy2] Hr Hh.
  apply (typed_contract_list _ Γ3); [exact HM|exact HF|].
  eapply typed_perm; [apply Permutation_app_comm|].
  eapply (DeepHandle_typed _ _ Γ2'); [exact HM|exact HΔ|exact Hσ
    |exact (ctx_dom_submseteq x _ _ Hs2 Hx2)|exact Hx3|exact Hk3|exact Hxk|exact Hy2|exact Hy3
    | |exact Hr|exact Hh].
  eapply typed_out_sub; [|exact He]. etrans; [exact Hs2|exact Hs1].
Qed.

Lemma ShallowHandle_alg Δ Γin Γ2 Γ2x Γ2' Γ3 (m : mode) (s : string) e (x k y : binder) h r
    ρ0 σ τ τ' ι κ :
  Forall (λ p, p ∈ Γin) Γ3 → le.MultiC Γ3 →
  Δ !! s = Some () → le.eff_name_from_sig σ = s →
  x ∉ ctx_dom Γ3 → k ∉ ctx_dom Γ3 → x ≠ k → y ∉ ctx_dom Γ3 →
  RCons σ ρ0 R⪯C Γ3 →
  Δ .| Γin ⊢ₜ e : RCons (SFlip m (SSig s ι κ)) ρ0 : τ ⊣ Γ2 →
  ctx_without_b x Γ2 Γ2x → ctx_without_b y Γ2x Γ2' →
  Δ .| <[ y :=c τ ]> (Γ2' ;; Γ3) ⊢ₜ r : RCons σ ρ0 : τ' ⊣ Γ3 →
  Δ .| <[ x :=c ι ]> <[ k :=c ![m] (κ -{ rename_type_row (+1) (RCons (SFlip m (SSig s ι κ)) ρ0) }-∘ τ.[ren (+1)]) ]> (⤉ Γ3)
    ⊢ₜ h : rename_type_row (+1) (RCons σ ρ0) : τ'.[ren (+1)] ⊣ (⤉ Γ3) →
  Δ .| Γin ⊢ₜ Handle Shallow m s e (Lam x (Lam k h)) (Lam y r) : RCons σ ρ0 : τ' ⊣ Γ3.
Proof.
  intros HF HM HΔ Hσ Hx3 Hk3 Hxk Hy3 HR He [Hs1 Hx2] [Hs2 Hy2] Hr Hh.
  apply (typed_contract_list _ Γ3); [exact HM|exact HF|].
  eapply typed_perm; [apply Permutation_app_comm|].
  eapply (ShallowHandle_typed _ _ Γ2'); [exact HM|exact HΔ|exact Hσ
    |exact (ctx_dom_submseteq x _ _ Hs2 Hx2)|exact Hx3|exact Hk3|exact Hxk|exact Hy2|exact Hy3
    |exact HR| |exact Hr|exact Hh].
  eapply typed_out_sub; [|exact He]. etrans; [exact Hs2|exact Hs1].
Qed.

(* A row whose head is not the handled signature is rearranged first. *)
Lemma typed_row_le Δ Γ Γ2 e ρ ρ' τ :
  le.row_to_disj_ctx ρ ⊢ₗ ρ' ≤R ρ @ true →
  Δ .| Γ ⊢ₜ e : ρ' : τ ⊣ Γ2 → Δ .| Γ ⊢ₜ e : ρ : τ ⊣ Γ2.
Proof. apply typed_row_sub. Qed.

(* ================================================================== *)
(** * Stage D: the driver [tychk]                                       *)
(* ================================================================== *)

(** ** Free variables

    Only used to decide what a closure captures and which copyable entries
    a handler frame needs; the derivations never depend on it (dropping or
    keeping an entry is always a sound derivation step). *)
Definition binder_rm (b : binder) (l : list string) : list string :=
  match b with BAnon => l | BNamed y => List.filter (λ z, negb (String.eqb z y)) l end.

Fixpoint expr_fv (e : expr) : list string :=
  match e with
  | Val _ => []
  | Var x => [x]
  | Rec f x e => binder_rm f (binder_rm x (expr_fv e))
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | AllocN e1 e2 | Store e1 e2 | Rand e1 e2 =>
      expr_fv e1 ++ expr_fv e2
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Load e | AllocTape e | Effect _ e | Do _ e =>
      expr_fv e
  | If e0 e1 e2 | Case e0 e1 e2 | Handle _ _ _ e0 e1 e2 => expr_fv e0 ++ expr_fv e1 ++ expr_fv e2
  end.

(* [lazy] does not look inside values, so opaque values cost nothing; an
   opaque sub-expression leaves a stuck term in the list. *)
Ltac fv_of e := eval lazy in (expr_fv e).

(* [y] may occur in [l]: a list that did not compute counts as containing
   every name. *)
Ltac fv_mem y l :=
  lazymatch l with
  | [] => fail
  | ?z :: ?l' => first [constr_eq y z | fv_mem y l']
  | _ => idtac
  end.

Ltac binder_ne n b :=
  lazymatch b with
  | BAnon => idtac
  | BNamed ?z => assert_fails (constr_eq n z)
  end.

(** ** Normalisation and lookup *)

Ltac head_of t := lazymatch t with ?f _ => head_of f | _ => t end.

Ltac norm_ctx Γ := eval cbv [ctx_insert ctx_append app empty empty_ctx] in Γ.

Ltac tychk_norm :=
  lazymatch goal with
  | |- typed ?Δ ?Γ ?e ?ρ ?τ ?Γ2 =>
      let Γ' := norm_ctx Γ in change (typed Δ Γ' e ρ τ Γ2)
  | |- pure_typed ?Δ ?Γ ?e ?τ =>
      let Γ' := norm_ctx Γ in change (pure_typed Δ Γ' e τ)
  end.

(* The type of the first entry named [x]. *)
Ltac ctx_lookup x Γ :=
  lazymatch Γ with
  | (x, ?t) :: _ => t
  | _ :: ?Γ' => ctx_lookup x Γ'
  end.

(* The row at which the function position of an application is typed. *)
Ltac fn_row e ρ :=
  lazymatch e with
  | Var _ => constr:(RNil)
  | Val _ => constr:(RNil)
  | tyann _ (Var _) => constr:(RNil)
  | tyann _ (Val _) => constr:(RNil)
  | _ => ρ
  end.

(* [ctx_inter Γa Γb Γ3]: [Γ3] is in both outputs of a branching rule. *)
Definition ctx_inter (Γa Γb Γ3 : ctx) : Prop := Γ3 ⊆+ Γa ∧ Γ3 ⊆+ Γb.

Lemma inter_nil Γb : ctx_inter [] Γb [].
Proof. split; apply submseteq_nil_l. Qed.
Lemma inter_empty Γa Γb : ctx_inter Γa Γb [].
Proof. split; apply submseteq_nil_l. Qed.
Lemma inter_same Γ : ctx_inter Γ Γ Γ.
Proof. done. Qed.
Lemma inter_keep (n : string) t Γa Γb Γb' Γ3 :
  ctx_pick n Γb t Γb' → ctx_inter Γa Γb' Γ3 → ctx_inter ((n, t) :: Γa) Γb ((n, t) :: Γ3).
Proof.
  intros Hp [Ha Hb]. split; [by apply submseteq_skip|]. by eapply sub_pick.
Qed.
Lemma inter_drop p Γa Γb Γ3 : ctx_inter Γa Γb Γ3 → ctx_inter (p :: Γa) Γb Γ3.
Proof. intros [Ha Hb]. split; [by apply submseteq_cons|done]. Qed.
Lemma join_intro x y Γa Γb Γ3 :
  ctx_inter Γa Γb Γ3 → x ∉ ctx_dom Γ3 → y ∉ ctx_dom Γ3 → ctx_join x y Γa Γb Γ3.
Proof. intros [Ha Hb] Hx Hy. done. Qed.

Ltac solve_inter x y :=
  lazymatch goal with
  | |- ctx_inter [] _ _ => apply inter_nil
  | |- ctx_inter ((?n, ?t) :: _) _ _ =>
      first [ binder_ne n x; binder_ne n y;
              eapply inter_keep; [solve_ctx_pick|solve_inter x y]
            | apply inter_drop; solve_inter x y ]
  | |- ctx_inter _ _ _ => first [apply inter_same | apply inter_empty]
  end.

Ltac solve_join :=
  lazymatch goal with
  | |- ctx_join ?x ?y _ _ _ =>
      apply join_intro; [solve_inter x y|solve_fresh|solve_fresh]
  end.

(** ** Side conditions *)

(* [le.MultiT], unfolding type definitions at the head when the hints of
   [tychk] do not apply directly. *)
Ltac tychk_multi :=
  lazymatch goal with
  | |- le.MultiT ?τ =>
      first [ solve [tychk_side]
            | let τ' := eval hnf in τ in
              tryif constr_eq τ τ' then fail
              else (change (le.MultiT τ'); tychk_multi) ]
  end.


(* Frame of a handler: copies of the copyable entries the clauses use. *)
Ltac solve_frame fvs x k y :=
  lazymatch goal with
  | |- _ ⊆+ [] => apply submseteq_nil_l
  | |- _ ⊆+ (?n, ?t) :: _ =>
      tryif (fv_mem n fvs; binder_ne n x; binder_ne n k; binder_ne n y;
             assert_succeeds (assert (le.MultiT t) by tychk_multi))
      then (apply submseteq_skip; solve_frame fvs x k y)
      else (apply submseteq_cons; solve_frame fvs x k y)
  | |- _ ⊆+ _ => apply submseteq_nil_l
  end.

Ltac tychk_multiC :=
  lazymatch goal with
  | |- le.MultiC [] => apply MultiC_nil
  | |- le.MultiC (_ :: _) => apply MultiC_cons; [tychk_multi|tychk_multiC]
  | |- le.MultiC (_ ++ _) => apply MultiC_app; tychk_multiC
  | |- le.MultiC ?Γ => let Γ' := norm_ctx Γ in
                      tryif constr_eq Γ Γ' then tychk_side else (change (le.MultiC Γ'); tychk_multiC)
  end.

Ltac tychk_mode_ty :=
  lazymatch goal with
  | |- _ m⪯T ?τ => first [apply mode_type_OS | apply mode_type_MS; tychk_multi]
  end.

Ltac tychk_modeC :=
  lazymatch goal with
  | |- _ m⪯C [] => apply mode_ctx_nil
  | |- _ m⪯C (_ :: _) => apply mode_ctx_cons; [tychk_mode_ty|tychk_modeC]
  | |- _ m⪯C (_ ++ _) => apply mode_ctx_app; tychk_modeC
  | |- ?m m⪯C ?Γ => let Γ' := norm_ctx Γ in
                     tryif constr_eq Γ Γ' then tychk_side else (change (m m⪯C Γ'); tychk_modeC)
  end.

Ltac tychk_row_ty :=
  lazymatch goal with
  | |- _ R⪯T _ => first [ apply le.Once_le; solve [once_solve]
                        | apply le.Multi_le; tychk_multi ]
  end.

Ltac tychk_rowC :=
  lazymatch goal with
  | |- _ R⪯C [] => apply row_ctx_nil
  | |- RNil R⪯C _ => apply RNil_le_ctx
  | |- _ R⪯C (_ :: _) => apply row_ctx_cons; [tychk_row_ty|tychk_rowC]
  | |- ?ρ R⪯C ?Γ => let Γ' := norm_ctx Γ in
                     tryif constr_eq Γ Γ' then tychk_side else (change (ρ R⪯C Γ'); tychk_rowC)
  end.

(* All side predicates; fails when the predicate cannot be shown (the
   driver then leaves it as a residual goal). *)
Ltac tychk_sideD :=
  lazymatch goal with
  | |- le.MultiT _ => tychk_multi
  | |- le.MultiC _ => tychk_multiC
  | |- _ m⪯T _ => tychk_mode_ty
  | |- _ m⪯C _ => tychk_modeC
  | |- _ R⪯T _ => tychk_row_ty
  | |- _ R⪯C _ => tychk_rowC
  | |- le.OnceR _ => once_solve
  | |- _ => tychk_side
  end.

Ltac side_or_leave := try solve [tychk_sideD].
Ltac row_le_or_leave := try solve [row_le_solve].

Ltac mode_le_solve' :=
  first [ apply le.MRefl_le | apply le.MOS_le | apply le.MMS_le ].

(** ** Subtyping [D ⊢ₗ α ≤T β] *)

(* Reflexivity (by unification, so an evar on either side is
   instantiated), then structural rules; type definitions are unfolded at
   the head when nothing else applies.  Rows are compared with
   [row_le_solve] at flag [true]. *)
Ltac ty_le_solve :=
  lazymatch goal with
  | |- let _ := _ in _ => let D := fresh "D" in intros D; subst D; ty_le_solve
  | |- le._type ?D ?α ?β =>
      first
        [ apply le.TRefl_le
        | ty_le_struct
        | let α' := eval hnf in α in
          let β' := eval hnf in β in
          tryif (constr_eq α α'; constr_eq β β') then fail
          else (change (le._type D α' β'); ty_le_solve) ]
  end
with ty_le_struct :=
  lazymatch goal with
  | |- _ ⊢ₗ TTop ≤T TTop => apply le.TRefl_le
  | |- _ ⊢ₗ _ ≤T TTop => apply le.TTop_le
  | |- _ ⊢ₗ TBot ≤T _ => apply le.TBot_le
  | |- _ ⊢ₗ TNat ≤T TInt => apply le.TNat_le_TInt
  | |- _ ⊢ₗ TBang _ _ ≤T TBang _ _ =>
      first [ apply le.TBangComp_le; [mode_le_solve'|ty_le_solve]
            | eapply le.TTrans_le; [apply le.TBangElim_le|ty_le_solve] ]
  | |- _ ⊢ₗ TBang _ _ ≤T _ => eapply le.TTrans_le; [apply le.TBangElim_le|ty_le_solve]
  | |- _ ⊢ₗ ?α ≤T TBang ?m ?β =>
      first [ apply le.TBangUnit_le | apply le.TBangBool_le | apply le.TBangInt_le
            | apply le.TBangNat_le | apply le.TBangTop_le | apply le.TBangRefC_le
            | lazymatch α with
              | TProd _ _ => eapply le.TTrans_le; [apply le.TProd_le; ty_le_solve|apply le.TBangProd1_le]
              | TSum _ _ => eapply le.TTrans_le; [apply le.TSum_le; ty_le_solve|apply le.TBangSum1_le]
              end
            | eapply le.TTrans_le; [apply le.TBangOS_le|];
              apply le.TBangComp_le; [mode_le_solve'|ty_le_solve] ]
  | |- _ ⊢ₗ TArrow _ _ _ ≤T TArrow _ _ _ =>
      eapply (le.TArrow_le _ _ _ _ _ _ _ true); [ty_le_solve|row_le_solve|ty_le_solve]
  | |- _ ⊢ₗ TProd _ _ ≤T TProd _ _ => apply le.TProd_le; ty_le_solve
  | |- _ ⊢ₗ TSum _ _ ≤T TSum _ _ => apply le.TSum_le; ty_le_solve
  | |- _ ⊢ₗ TRef _ ≤T TRef _ => apply le.TRef_le; ty_le_solve
  | |- _ ⊢ₗ TForallT _ ≤T TForallT _ => apply le.TForallT_le; ty_le_solve
  | |- _ ⊢ₗ TForallR _ ≤T TForallR _ => apply le.TForallR_le; ty_le_solve
  | |- _ ⊢ₗ TForallM _ ≤T TForallM _ => apply le.TForallM_le; ty_le_solve
  end.

Ltac ty_le_or_leave := try solve [ty_le_solve].

(* [α.[σ] = ?β], [α.|[σ] = ?β]: compute the substitution. *)
Ltac ty_eq_simpl := first [ simpl; reflexivity | asimpl; reflexivity | reflexivity ].

Ltac solve_lookup := first [ reflexivity | vm_compute; reflexivity | by simplify_map_eq ].

Ltac solve_vars_fresh :=
  lazymatch goal with
  | |- vars._fresh ?s ?Γ ?ρ ?τ => assert_ground constr:((s, Γ, ρ, τ)); compute; set_solver
  end.

Ltac rec_binder_ok := first [ exact I | done | (cbn; done) ].

(* Mode / [MultiC] premise of [Rec_alg] and [Rec_pure_typed]. *)
Ltac rec_mode :=
  cbv beta iota;
  lazymatch goal with
  | |- _ ∧ _ => split; [done|side_or_leave]
  | |- _ => side_or_leave
  end.

(* The type of a function position with its quantifiers instantiated:
   [fnc_build ρi] proves [fn_coerce F ?A] for a known [F], instantiating
   row quantifiers with [ρi] (the ambient row). *)
Ltac fnc_build ρi :=
  lazymatch goal with
  | |- fn_coerce (TArrow _ _ _) _ => apply fnc_refl
  | |- fn_coerce (TBang _ _) _ => apply fnc_bang; fnc_build ρi
  | |- fn_coerce (TForallR ?α) _ => eapply (fnc_rall α ρi); [ty_eq_simpl|fnc_build ρi]
  | |- fn_coerce (TForallT ?α) _ => eapply (fnc_tall α); [ty_eq_simpl|fnc_build ρi]
  | |- fn_coerce (TForallM ?α) _ => eapply (fnc_mall α); [ty_eq_simpl|fnc_build ρi]
  | |- fn_coerce ?F ?A =>
      let F' := eval hnf in F in
      tryif constr_eq F F' then fail "tychk: not a function type:" F
      else (change (fn_coerce F' A); fnc_build ρi)
  end.

(* Bang the arrows under a quantifier prefix (the pure judgement only
   produces banged arrows). *)
Ltac bang_under_q m τ :=
  lazymatch τ with
  | TForallR ?α => let α' := bang_under_q m α in constr:(TForallR α')
  | TForallT ?α => let α' := bang_under_q m α in constr:(TForallT α')
  | TForallM ?α => let α' := bang_under_q m α in constr:(TForallM α')
  | TArrow _ _ _ => constr:(TBang m τ)
  | _ => τ
  end.

Definition ty_of (τ : type) : Prop := True.

Lemma Forall_sub (Γ3 Γ : ctx) : Γ3 ⊆+ Γ → Forall (λ p, p ∈ Γ) Γ3.
Proof. intros Hs. apply Forall_forall. intros p Hp. by eapply elem_of_submseteq. Qed.

(* The signature of [s] in a row: [(m, ι, κ, ρ0)] with the row equal to
   [RCons (SFlip m (SSig s ι κ)) ρ0] up to permutation; a bare signature
   is a multi-shot one ([SFlipElim_le]). *)
Ltac find_sig s ρ :=
  match ρ with
  | RCons (SFlip ?m (SSig s ?ι ?κ)) ?ρ' => constr:((m, ι, κ, ρ'))
  | RCons (SSig s ?ι ?κ) ?ρ' => constr:((MS, ι, κ, ρ'))
  | RCons ?σ ?ρ' =>
      let r := find_sig s ρ' in
      lazymatch r with (?m, ?ι, ?κ, ?ρ0) => constr:((m, ι, κ, RCons σ ρ0)) end
  end.

Create HintDb tychk_val.
Create HintDb tychk_expr.

(** ** The driver *)

(* [tychk_val]: [⊢ᵥ v : τ].  [tychk_expr]: [Δ .| Γ ⊢ₜ e : ρ : τ ⊣ Γ2]
   (wraps a concrete output in [typed_out_le]).  [tychk_dispatch]: one rule
   by the shape of [e].  [peek_ty]: the type of a function position,
   before its argument is typed. *)
Ltac tychk_val :=
  lazymatch goal with
  | |- ⊢ᵥ ?v : ?τ =>
    lazymatch v with
    | LitV LitUnit =>
        first [apply Unit_val_typed | eapply val_sub_alg; [apply Unit_val_typed|ty_le_solve]]
    | LitV (LitBool _) =>
        first [apply Bool_val_typed | eapply val_sub_alg; [apply Bool_val_typed|ty_le_solve]]
    | LitV (LitInt _) =>
        lazymatch τ with
        | TNat => first [apply Nat_val_typed | apply Nat_val_alg; lia]
        | _ => first [ apply Int_val_typed
                     | eapply val_sub_alg; [first [apply Nat_val_typed|apply Int_val_typed]|ty_le_solve] ]
        end
    | PairV _ _ =>
        first [ apply Pair_val_typed; tychk_val
              | eapply val_sub_alg; [apply Pair_val_typed; tychk_val|ty_le_solve] ]
    | InjLV _ =>
        first [ apply InjL_val_typed; tychk_val
              | eapply val_sub_alg; [apply InjL_val_typed; tychk_val|ty_le_solve] ]
    | InjRV _ =>
        first [ apply InjR_val_typed; tychk_val
              | eapply val_sub_alg; [apply InjR_val_typed; tychk_val|ty_le_solve] ]
    | RecV _ _ _ => tychk_val_rec
    | _ =>
        first [ solve [eauto with tychk_val tychk]
              | eapply val_sub_alg; [solve [eauto with tychk_val tychk]|ty_le_solve]
              | let v' := eval hnf in v in
                tryif constr_eq v v' then fail
                else (change (⊢ᵥ v' : τ); tychk_val)
              | tryif is_evar τ then fail "tychk: cannot synthesise the type of" v
                else idtac (* residual: an opaque value *) ]
    end
  end

with tychk_val_rec :=
  lazymatch goal with
  | |- ⊢ᵥ RecV ?f ?x ?e : ?τ =>
    lazymatch τ with
    | TBang _ (TArrow _ _ _) => apply Rec_val_typed; [rec_binder_ok|tychk_expr]
    | TArrow _ _ _ => apply Rec_val_bare; [rec_binder_ok|tychk_expr]
    | TForallR _ => apply RAbs_val_typed; tychk_val_rec
    | TForallT _ => apply TAbs_val_typed; tychk_val_rec
    | TForallM _ => apply MAbs_val_typed; tychk_val_rec
    | _ => tryif is_evar τ then fail "tychk: annotate the function"
           else let τ' := eval hnf in τ in
                tryif constr_eq τ τ' then fail "tychk: a function cannot have type" τ
                else (change (⊢ᵥ RecV f x e : τ'); tychk_val_rec)
    end
  end

with tychk_expr :=
  lazymatch goal with
  | |- typed _ _ ?e _ _ ?Γ2 =>
      tychk_norm;
      tryif is_evar Γ2 then tychk_dispatch
      else lazymatch e with
           | Effect _ _ => tychk_dispatch
           | _ => eapply typed_out_le; [tychk_dispatch|solve_submseteq]
           end
  end

with tychk_fold_or tac :=
  lazymatch goal with
  | |- typed _ _ _ _ ?τ _ =>
      tryif is_evar τ then tac
      else let τ' := eval hnf in τ in
           lazymatch τ' with
           | TRec _ => eapply TFold_alg; [ty_eq_simpl|tychk_dispatch]
           | _ => tac
           end
  end

with peek_ty Γ ρ e :=
  lazymatch goal with
  | |- ty_of ?T =>
    lazymatch e with
    | Var ?x => let t := ctx_lookup x Γ in unify T t; exact I
    | tyann ?t _ => unify T t; exact I
    | Val ?v => assert (val_typed v T) by (solve [tychk_val]); exact I
    | App (Val rec_unfold) ?e' =>
        let M := open_constr:(_ : type) in
        assert (ty_of M) by (solve [peek_ty Γ ρ e']);
        let M' := eval hnf in M in
        lazymatch M' with
        | TRec ?τ => let τ' := eval simpl in (τ.[TRec τ/]) in unify T τ'
        end; exact I
    | App ?e1 _ =>
        let F := open_constr:(_ : type) in
        assert (ty_of F) by (solve [peek_ty Γ ρ e1]);
        let a := open_constr:(_ : type) in
        let r := open_constr:(_ : row) in
        let k := open_constr:(_ : type) in
        assert (fn_coerce F (TArrow a r k)) by (solve [fnc_build ρ]);
        unify T k; exact I
    | Fst ?e' =>
        let P := open_constr:(_ : type) in
        assert (ty_of P) by (solve [peek_ty Γ ρ e']);
        let P' := eval hnf in P in
        lazymatch P' with TProd ?a _ => unify T a end; exact I
    | Snd ?e' =>
        let P := open_constr:(_ : type) in
        assert (ty_of P) by (solve [peek_ty Γ ρ e']);
        let P' := eval hnf in P in
        lazymatch P' with TProd _ ?b => unify T b end; exact I
    end
  end

with tychk_var :=
  lazymatch goal with
  | |- typed _ _ (Var _) _ _ _ =>
      first [ eapply Var_copy_alg; [solve_ctx_pick|solve [tychk_multi]|ty_le_solve]
            | eapply Var_take_alg; [solve_ctx_pick|ty_le_solve]
            | eapply Var_take_alg; [solve_ctx_pick|] ]
  end

with tychk_app :=
  lazymatch goal with
  | |- typed _ ?Γ (App ?e1 ?e2) ?ρ _ _ =>
    let ρ1 := fn_row e1 ρ in
    let F := open_constr:(_ : type) in
    tryif (assert (ty_of F) by (solve [peek_ty Γ ρ e1]))
    then (lazymatch goal with H : ty_of F |- _ => clear H end;
          eapply (App_alg _ _ _ _ _ _ ρ ρ1 F);
            [ fnc_build ρ | ty_le_or_leave | tychk_expr | tychk_expr
            | row_le_or_leave | row_le_or_leave | side_or_leave | side_or_leave ])
    else (eapply (App_alg_late _ _ _ _ _ _ ρ ρ1);
            [ tychk_expr | tychk_expr | fnc_build ρ | ty_le_or_leave
            | row_le_or_leave | row_le_or_leave | side_or_leave | side_or_leave ])
  end

with tychk_rec :=
  lazymatch goal with
  | |- typed ?Δ ?Γ (Rec ?f ?x ?b) ?ρ ?τ ?Γ2 =>
    let fvs := fv_of (Rec f x b) in
    lazymatch τ with
    | TBang ?m (TArrow ?τ1 ?ρ0 ?κ) =>
        eapply (Rec_alg _ _ _ _ _ f x b m ρ0 τ1 κ);
          [solve_split fvs|tychk_multiC|rec_mode|solve_fresh|solve_fresh|tychk_expr]
    | TArrow ?τ1 ?ρ0 ?κ =>
        let m := lazymatch f with BAnon => constr:(OS) | _ => constr:(MS) end in
        eapply (Rec_alg_bare _ _ _ _ _ f x b m ρ0 τ1 κ);
          [solve_split fvs|tychk_multiC|rec_mode|solve_fresh|solve_fresh|tychk_expr]
    | TForallR _ => tychk_rec_pure fvs
    | TForallT _ => tychk_rec_pure fvs
    | TForallM _ => tychk_rec_pure fvs
    | _ => tryif is_evar τ then fail "tychk: annotate the function (tyann)"
           else let τ' := eval hnf in τ in
                tryif constr_eq τ τ' then fail "tychk: a function cannot have type" τ
                else (change (typed Δ Γ (Rec f x b) ρ τ' Γ2); tychk_rec)
    end
  end

with tychk_rec_pure fvs :=
  lazymatch goal with
  | |- typed _ _ (Rec ?f _ _) _ ?τ _ =>
      let m := lazymatch f with BAnon => constr:(OS) | _ => constr:(MS) end in
      let τ' := bang_under_q m τ in
      eapply (typed_sub_type _ _ _ _ _ _ τ'); [ty_le_solve|];
      eapply Pure_alg; [solve_split fvs|tychk_multiC|tychk_pure]
  end

with tychk_pure :=
  lazymatch goal with
  | |- pure_typed _ _ ?e ?τ =>
    tychk_norm;
    lazymatch τ with
    | TForallR _ => apply RAbs_pure_typed; tychk_pure_shift
    | TForallT _ => apply TAbs_pure_typed; tychk_pure_shift
    | TForallM _ => apply MAbs_pure_typed; tychk_pure_shift
    | _ => lazymatch e with
           | Rec _ _ _ =>
               apply Rec_pure_typed; [rec_mode|solve_fresh|solve_fresh|tychk_expr]
           | Val _ => apply Val_pure_typed; tychk_val
           end
    end
  end

with tychk_pure_shift :=
  lazymatch goal with
  | |- pure_typed ?Δ ?Γ ?e ?τ => let Γ' := eval simpl in Γ in change (pure_typed Δ Γ' e τ); tychk_pure
  end

with solve_split fvs :=
  lazymatch goal with
  | |- ctx_split [] _ _ _ => apply split_rest
  | |- ctx_split ((?n, ?t) :: _) _ _ _ =>
      tryif fv_mem n fvs
      then (tryif assert_succeeds (assert (le.MultiT t) by tychk_multi)
            then apply split_copy else apply split_move)
      else apply split_keep;
      solve_split fvs
  | |- ctx_split _ _ _ _ => apply split_rest
  end

with tychk_do :=
  lazymatch goal with
  | |- typed _ _ (Do (EffName ?s) _) ?ρ _ _ =>
    let r := find_sig s ρ in
    lazymatch r with
    | (?m, ?ι, ?κ, ?ρ0) =>
        eapply (Do_alg _ _ _ s _ ρ ρ0 m ι κ TUnit);
          [ row_le_or_leave | solve_lookup | ty_eq_simpl | ty_eq_simpl | tychk_expr
          | side_or_leave | ty_le_or_leave ]
    end
  end

with tychk_handle :=
  lazymatch goal with
  | |- typed ?Δ ?Γ (sigann ?s ?ι ?κ (Handle ?hs ?m (EffName ?s') ?e
                     (Rec BAnon ?x (Rec BAnon ?k ?h)) (Rec BAnon ?y ?r))) ?ρ ?τ ?Γ2 =>
    change (typed Δ Γ (Handle hs m (EffName s') e
                     (Rec BAnon x (Rec BAnon k h)) (Rec BAnon y r)) ρ τ Γ2);
    let fvs := fv_of (App (Rec BAnon x (Rec BAnon k h)) (Rec BAnon y r)) in
    lazymatch ρ with
    | RCons ?σ ?ρ0 =>
      lazymatch hs with
      | Deep =>
          eapply (DeepHandle_alg _ _ _ _ _ _ m s' e x k y h r ρ0 σ _ τ ι κ);
            [ apply Forall_sub; solve_frame fvs x k y
            | side_or_leave | solve_lookup | reflexivity
            | solve_fresh | solve_fresh | done | solve_fresh
            | tychk_expr | solve_without_b | solve_without_b
            | tychk_expr | tychk_handler_clause ]
      | Shallow =>
          eapply (ShallowHandle_alg _ _ _ _ _ _ m s' e x k y h r ρ0 σ _ τ ι κ);
            [ apply Forall_sub; solve_frame fvs x k y
            | side_or_leave | solve_lookup | reflexivity
            | solve_fresh | solve_fresh | done | solve_fresh | side_or_leave
            | tychk_expr | solve_without_b | solve_without_b
            | tychk_expr | tychk_handler_clause ]
      end
    end
  end

with tychk_handler_clause :=
  lazymatch goal with
  | |- typed ?Δ ?Γ ?e ?ρ ?τ ?Γ2 =>
      let Γ' := eval simpl in Γ in
      let ρ' := eval simpl in ρ in
      let τ' := eval simpl in τ in
      let Γ2' := eval simpl in Γ2 in
      change (typed Δ Γ' e ρ' τ' Γ2'); tychk_expr
  end

with tychk_dispatch :=
  lazymatch goal with
  | |- typed ?Δ ?Γ ?e ?ρ ?τ ?Γ2 =>
    lazymatch e with
    | tyann _ _ => eapply tyann_alg; [tychk_expr|ty_le_or_leave]
    | sigann _ _ _ _ => tychk_handle
    | Var _ => tychk_var
    | Val _ => tychk_fold_or ltac:(eapply typed_val_row; tychk_val)
    | App (Rec BAnon (BNamed ?x2) (App (Rec BAnon (BNamed ?x1)
            (App (Rec BAnon (BNamed ?x2') _) (Snd (Var ?x2''))))
            (Fst (Var ?x2''')))) _ =>
        eapply LetPair_alg;
          [done|tychk_expr|solve_without_b|solve_without_b|tychk_expr|solve_without_b|solve_without_b]
    | App (Rec BAnon _ _) _ =>
        eapply Let_alg; [tychk_expr|solve_without_b|tychk_expr|solve_without_b]
    | App (Val rec_unfold) _ =>
        eapply TUnfold_alg; [tychk_expr|ty_eq_simpl|ty_le_or_leave]
    | App ?e1 ?e2 =>
        (* an expression constant in function position ([sample]) is
           unfolded first: it may be a [let] *)
        let h := head_of e1 in
        tryif (is_const h; assert_fails (constr_eq h tyann))
        then (let e1' := eval hnf in e1 in
              tryif constr_eq e1 e1' then tychk_app
              else (change (typed Δ Γ (App e1' e2) ρ τ Γ2); tychk_dispatch))
        else tychk_app
    | Rec _ _ _ => tychk_rec
    | BinOp _ _ _ =>
        eapply BinOp_alg; [constructor|tychk_expr|tychk_expr|ty_le_or_leave]
    | UnOp _ _ => eapply UnOp_alg; [constructor|tychk_expr|ty_le_or_leave]
    | If _ _ _ => eapply If_alg; [tychk_expr|tychk_expr|tychk_expr|solve_join]
    | Case _ (Rec BAnon _ _) (Rec BAnon _ _) =>
        eapply Match_alg;
          [tychk_expr|solve_without_b|solve_without_b|tychk_expr|tychk_expr|solve_join]
    | Pair _ _ => tychk_fold_or ltac:(eapply Pair_alg; [tychk_expr|tychk_expr|side_or_leave])
    | Fst _ => eapply Fst_alg; [tychk_expr|ty_le_or_leave]
    | Snd _ => eapply Snd_alg; [tychk_expr|ty_le_or_leave]
    | InjL _ => tychk_fold_or ltac:(eapply InjL_typed; tychk_expr)
    | InjR _ => tychk_fold_or ltac:(eapply InjR_typed; tychk_expr)
    | AllocN _ _ =>
        lazymatch τ with
        | TRef _ => eapply TAlloc; tychk_expr
        | _ => eapply AllocC_typed; tychk_expr
        end
    | Load (Var ?x) =>
        let t := ctx_lookup x Γ in
        lazymatch t with
        | TRef _ => eapply TLoad_alg; [solve_ctx_pick|ty_le_or_leave]
        | _ => eapply LoadC_alg; [tychk_expr|side_or_leave|ty_le_or_leave]
        end
    | Load _ => eapply LoadC_alg; [tychk_expr|side_or_leave|ty_le_or_leave]
    | Store ?e1 _ =>
        let R := open_constr:(_ : type) in
        tryif (assert (ty_of R) by (solve [peek_ty Γ ρ e1]))
        then (lazymatch goal with H : ty_of R |- _ => clear H end;
              let R' := eval hnf in R in
              lazymatch R' with
              | TRefC ?t => eapply (StoreC_alg _ _ _ _ _ _ _ t);
                              [tychk_expr|tychk_expr|side_or_leave|ty_le_or_leave]
              end)
        else (eapply StoreC_alg; [tychk_expr|tychk_expr|side_or_leave|ty_le_or_leave])
    | AllocTape _ => eapply TAllocTape_alg; [tychk_expr|ty_le_or_leave]
    | Rand _ (Val (LitV LitUnit)) => eapply TRandU_alg; [tychk_expr|tychk_expr|ty_le_or_leave]
    | Rand _ _ => eapply TRand_alg; [tychk_expr|tychk_expr|ty_le_or_leave]
    | Effect _ _ =>
        eapply Effect_alg; [tychk_expr|solve_submseteq|try solve_vars_fresh]
    | Do (EffName _) _ => tychk_do
    | Handle _ _ _ _ _ _ => fail "tychk: annotate the handler with sigann"
    | _ => first [ solve [eauto with tychk_expr]
                 | let e' := eval hnf in e in
                   tryif constr_eq e e' then fail
                   else (change (typed Δ Γ e' ρ τ Γ2); tychk_dispatch)
                 | fail "tychk: no rule for" e ]
    end
  end.

Ltac tychk :=
  lazymatch goal with
  | |- ⊢ᵥ _ : _ => tychk_val
  | |- typed _ _ _ _ _ _ => tychk_expr
  | |- pure_typed _ _ _ _ => tychk_pure
  | _ => fail "tychk: not a typing goal"
  end.

(* ================================================================== *)
(** * Smoke tests of the driver                                        *)
(* ================================================================== *)

Section driver_tests.

Local Lemma drv_lit : ∅ .| [] ⊢ₜ (#1 + #2)%E : RNil : ℤ ⊣ [].
Proof. tychk. Qed.

Local Lemma drv_let :
  ∅ .| [("x", TInt)] ⊢ₜ (let: "y" := "x" + #1 in ("y", "x"))%E : RNil : (ℤ * ℤ) ⊣ [].
Proof. tychk. Qed.

Local Lemma drv_fun : ⊢ᵥ (λ: "a" "b", ("a" * "b") `rem` #7)%V : (ℤ ⇾ ℤ ⇾ ℤ).
Proof. tychk. Qed.

(* The copyable-reference test of tests.v, with the payload annotated. *)
Local Lemma drv_refc :
  ∅ .| [] ⊢ₜ (let: "r" := tyann (refᶜ (() + ℤ))%ty (ref NONE) in
              match: ! "r" with
                NONE => "r" <- SOME #1
              | SOME "x" => #()%V
              end)%E : RNil : () ⊣ [].
Proof. tychk. Qed.

(* A residual goal: the latent row of [f] is abstract, so [row_le_solve]
   cannot show it below the ambient row; the driver leaves exactly that
   side condition. *)
Local Lemma drv_residual (ρa : row) (Hρ : ∀ D b, D ⊢ₗ ρa ≤R RNil @ b) :
  ∅ .| [("f", TArrow TInt ρa TInt)] ⊢ₜ ("f" #1)%E : RNil : ℤ ⊣ [].
Proof.
  tychk.
  lazymatch goal with |- _ ⊢ₗ ρa ≤R RNil @ _ => apply Hρ end.
Qed.

End driver_tests.
