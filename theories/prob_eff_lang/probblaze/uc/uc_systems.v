(* Systems as factories.

   A *session* is a value of a session type such as [τ__F τ τ']
   (comp_operators): it takes its client, any number of times (the calls
   share the session's state), and then its environment ports.  A *system* (a protocol, an ideal functionality, a simulator, or a
   composition of these) is a *factory*: a value [λ: <>, e] of type
   [fac m τ := 𝟙 -{⟨⟩}-[m]-> τ] whose call evaluates [e], i.e. allocates the
   state of a fresh session and returns it.  The mode [m] is the number of
   sessions the environment may create: one ([OS]) or any ([MS]).

   A composite of systems is a system: [fac_op o F G] is the factory whose
   session calls [F] and [G] and composes the two sessions with the session
   operator [o].  Every system being a value, substitution never enters one,
   so no closedness premises are needed anywhere, and the hybrid contexts of
   the composition theorem apply values to values.

   Typing, congruence and associativity are proved once for [fac_op] and
   instantiated for the three operators.  The operators are written with the
   same symbols as the session-level ones, in [factory_scope] (delimited
   [%fac]); a file working with systems opens that scope.  See DESIGN.md. *)

From iris.proofmode Require Import base proofmode classes.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze.uc Require Import comp_operators.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory logic valgroup mode.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.

Import valgroup_tactics.

(* ------------------------------------------------------------------ *)
(* Composition of systems.                                             *)
(* ------------------------------------------------------------------ *)

(* The composite of the systems [F] and [G] by the session operator [o]:
   its session calls both factories (right to left, like any application)
   and composes the sessions. *)
Definition fac_op (o : val) (F G : val) : val :=
  (λ: <>, o (F #()%V) (G #()%V))%V.

(* The same as a program, for a context with a hole: it evaluates to
   [fac_op] in four pure steps ([fac_app_pure], uc_theorem). *)
Definition fac_app (o : val) : val :=
  λ: "F" "G", λ: <>, o ("F" #()%V) ("G" #()%V).

(* The pure-step tactics may call a composite, or a lifted operator,
   without unfolding it. *)
#[global] Instance fac_op_as_recv o F G : AsRecV (fac_op o F G) BAnon BAnon _ := eq_refl.
#[global] Instance fac_app_as_recv o : AsRecV (fac_app o) BAnon "F" _ := eq_refl.
(* The session operators as well. *)
#[global] Instance func_comp_as_recv : AsRecV func_comp BAnon "F" _ := eq_refl.
#[global] Instance parallel_composition_as_recv : AsRecV parallel_composition BAnon "F" _ := eq_refl.
#[global] Instance functionality_composition_as_recv : AsRecV functionality_composition BAnon "F" _ := eq_refl.

Declare Scope factory_scope.
Delimit Scope factory_scope with fac.
Notation "F ∘f G" := (fac_op func_comp F G) (at level 10) : factory_scope.
Notation "F ||ᵣ G" := (fac_op parallel_composition F G) (at level 10) : factory_scope.
Notation "F '∘F' G" := (fac_op functionality_composition F G) (at level 10) : factory_scope.
(* The program-level operators, for contexts. *)
Notation "e1 ∘fₚ e2" := (fac_app func_comp e1 e2) (at level 10) : factory_scope.
Notation "e1 ||ᵣₚ e2" := (fac_app parallel_composition e1 e2) (at level 10) : factory_scope.
Notation "e1 '∘Fₚ' e2" := (fac_app functionality_composition e1 e2) (at level 10) : factory_scope.

Section systems.
  Context `{!probblazeRGS Σ}.
  Import typed_hint_modes.

  (* ---------------------------------------------------------------- *)
  (* Semantic typing of the session-level operators.                   *)
  (* ---------------------------------------------------------------- *)


  (* [func_comp] hands [F] the client [λ r, G f r]: the application [G f] is
     delayed behind an η-expansion.  [eta_ty τ] says that this delay preserves
     [τ].  It holds for one-shot arrows and is closed under [∀ᵣ], which covers
     the client types of [τ__F] and [τ__f]. *)
  Definition eta_ty (τ : sem_ty Σ) : iProp Σ :=
    ∀ g1 g2 x1 x2 : val,
      BREL g1 x1 ≤ g2 x2 <| [] |> {{ τ }} -∗ τ (λ: "r", g1 x1 "r")%V (λ: "r", g2 x2 "r")%V.

  Lemma eta_ty_arr ρ τ κ : ⊢ eta_ty (τ -{ ρ }-∘ κ).
  Proof.
    iIntros (g1 g2 x1 x2) "Hg". rewrite /sem_ty_arr /=.
    iIntros (w1 w2) "Hw". brel_pures_l; brel_pures_r.
    iApply (brel_bind [AppLCtx _] [AppLCtx _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS _ _ [] [] with "[] Hg"); first iApply to_iThy_le_refl.
    simpl. iIntros (v1 v2) "Hv". by iApply "Hv".
  Qed.

  Lemma eta_ty_row_forall (C : sem_row Σ → sem_ty Σ) :
    (∀ θ, ⊢ eta_ty (C θ)) → ⊢ eta_ty (∀ᵣ θ, C θ).
  Proof.
    intros HC. iIntros (g1 g2 x1 x2) "Hg". rewrite /sem_ty_row_forall /=. iIntros (θ).
    iApply HC. iApply (brel_wand with "Hg"). iIntros "!# % % H". iApply "H".
  Qed.

  Lemma eta_ty_τf (τ1 τ2 : sem_row Σ → sem_ty Σ) θ : ⊢ eta_ty (τ__f θ τ1 τ2).
  Proof. apply eta_ty_row_forall => θ1. apply eta_ty_row_forall => θ2. apply eta_ty_arr. Qed.

  Lemma sem_oval_typed_eta (g x : string) τ M :
    g ≠ "r" → x ≠ "r" → (⊢ eta_ty M) →
    ⊢ sem_oval_typed [(x, τ); (g, τ ⊸ M)] (λ: "r", g x "r") (λ: "r", g x "r") M.
  Proof.
    iIntros (Hg Hx HM) "!# %vs HΓ /=".
    rewrite !env_sem_typed_cons env_sem_typed_empty.
    iDestruct "HΓ" as "([%x1 [%x2 [%Hvx Hx]]] & [%g1 [%g2 [%Hvg Hg]]] & _)".
    simplify_map_eq. rewrite /pure_weakestpre.prel /=. iExists _, _, 1%nat, 1%nat.
    iSplit; first (iPureIntro; repeat split; by apply pure_recc).
    iApply HM. by iApply "Hg".
  Qed.

  (* The closure that takes the client is unrestricted, so it may capture
     only the two (persistent) sessions. *)
  Lemma func_comp_val_typed (T1 M T4 : sem_row Σ → sem_ty Σ) :
    (∀ θ, ⊢ eta_ty (M θ)) →
    ⊢ ⊨ᵥ func_comp ≤ func_comp :
      ((∀ᵣ θ, M θ → T4 θ) ⊸ (∀ᵣ θ, T1 θ → M θ) ⊸ (∀ᵣ θ, T1 θ → T4 θ))%T.
  Proof.
    intros HM.
    iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
    iApply sem_typed_closure; first done.
    iApply (sem_typed_oval _ [_]). iApplyT sem_oval_typed_afun.
    iApply (sem_typed_oval _ [_; _]). iApply sem_typed_RLam. iIntros (θ).
    iApplyT sem_oval_typed_ufun. simpl.
    iApplyT sem_typed_app_fun_nil; first iApply row_le_refl.
    - iApplyT (sem_typed_sub_env _ [("f", T1 θ); ("G", T1 θ ⊸ M θ); ("F", _)]).
      { iApply env_le_cons; last iApply ty_le_refl.
        iApply env_le_cons; [iApply env_le_refl|].
        iApply ty_le_trans; [iApply ty_le_row_forall_inst|iApply ty_le_mbang_elim]. }
      iApply (sem_typed_oval _ [("f", _); ("G", _)] [("F", _)]).
      iApply sem_oval_typed_eta; [done|done|apply HM].
    - iApplyT sem_typed_sub_ty; last typed_var.
      iApply ty_le_trans; [iApply ty_le_row_forall_inst|iApply ty_le_mbang_elim].
      Unshelve. all: solve_typed_side.
  Qed.

  Lemma parallel_comp_val_typed (τ1 τ1' τ2 τ2' : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ parallel_composition ≤ parallel_composition :
      (τ__F τ2 τ2' ⊸ τ__F τ1 τ1' ⊸ ∀ᵣ θ, τ__f θ τ1' τ2' → τ__f θ τ1 τ2)%T.
  Proof.
    iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
    iApply sem_typed_closure; first done.
    iApply (sem_typed_oval _ [_]). iApplyT sem_oval_typed_afun.
    iApply (sem_typed_oval _ [_; _]). iApply sem_typed_RLam. iIntros (θ).
    iApplyT sem_oval_typed_ufun.
    iApply (sem_typed_oval _ [_; _; _]). iApply sem_typed_RLam. iIntros (θ1).
    iApply sem_typed_RLam. iIntros (θ2).
    iApplyT sem_oval_typed_afun. simpl.
    iApplyT sem_typed_pair_elim; first typed_var.
    iApplyT sem_typed_app_fun_nil.
    2: typed_var.
    2: { iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApply (sem_typed_oval _ [_; _; _])|].
         2: { iApplyT sem_typed_sub_ty; last typed_var.
              iApply ty_le_trans; first iApply (ty_le_row_forall_inst _ (sem_row_union (¡ θ1) θ)).
              iApply ty_le_trans; first iApply ty_le_mbang_elim.
              iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|iApply ty_le_row_forall_inst]. }
         iApply sem_typed_RLam. iIntros (θh). iApplyT sem_oval_typed_afun. simpl.
         iApplyT sem_typed_app_fun_nil.
         2: typed_var.
         2: { iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApply (sem_typed_oval _ [_; _])|].
              2: { iApplyT sem_typed_sub_ty; last typed_var.
                   iApply ty_le_trans; first iApply (ty_le_row_forall_inst _ (sem_row_union (¡ θh) θ)).
                   iApply ty_le_trans; first iApply ty_le_mbang_elim.
                   iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|iApply ty_le_row_forall_inst]. }
              iApply sem_typed_RLam. iIntros (θh2). iApplyT sem_oval_typed_afun. simpl.
              iApplyT sem_typed_app_fun_nil.
              2: { iApply sem_typed_sub_nil. iApplyT sem_typed_pair; typed_var. }
              2: { iApplyT sem_typed_sub_ty; last typed_var.
                   iApply ty_le_trans; first iApply ty_le_row_forall_inst. iApply ty_le_row_forall_inst. }
              iApply row_le_refl. }
         row_le_submseteq. }
    row_le_submseteq.
    Unshelve. all: solve_typed_side.
  Qed.

  Lemma functionality_comp_val_typed (τ1' τ1 τF τ2 : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ functionality_composition ≤ functionality_composition :
      (τ__F τ2 τF ⊸ (∀ᵣ θ, τ1' θ → τ__f θ τ1 τF) ⊸ ∀ᵣ θ, τ1' θ → τ__f θ τ1 τ2)%T.
  Proof.
    iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
    iApply sem_typed_closure; first done.
    iApply (sem_typed_oval _ [_]). iApplyT sem_oval_typed_afun.
    iApply (sem_typed_oval _ [_; _]). iApply sem_typed_RLam. iIntros (θ).
    iApplyT sem_oval_typed_ufun.
    iApply (sem_typed_oval _ [_; _; _]). iApply sem_typed_RLam. iIntros (θ1).
    iApply sem_typed_RLam. iIntros (θ2).
    iApplyT sem_oval_typed_afun. simpl.
    iApplyT sem_typed_pair_elim; first typed_var.
    iApplyT sem_typed_app_fun_nil.
    2: typed_var.
    2: { iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApply (sem_typed_oval _ [_; _; _])|].
         2: { iApplyT sem_typed_sub_ty; last typed_var.
              iApply ty_le_trans; first iApply (ty_le_row_forall_inst _ (sem_row_union (¡ θ1) θ)).
              iApply ty_le_trans; first iApply ty_le_mbang_elim.
              iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|iApply ty_le_row_forall_inst]. }
         iApply sem_typed_RLam. iIntros (θF). iApplyT sem_oval_typed_afun. simpl.
         iApplyT sem_typed_app_fun_nil.
         2: { iApply sem_typed_sub_nil. iApplyT sem_typed_pair; typed_var. }
         2: { iApplyT sem_typed_sub_ty; last first.
              { iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|typed_var|].
                iApplyT sem_typed_sub_ty; last typed_var.
                iApply ty_le_trans; first iApply ty_le_row_forall_inst. iApply ty_le_mbang_elim. }
              rewrite /τ__f. iApply ty_le_trans; first iApply (ty_le_row_forall_inst _ θ1).
              iApply (ty_le_row_forall_inst _ θF). }
         row_le_submseteq. }
    row_le_submseteq.
    Unshelve. all: solve_typed_side.
  Qed.


  (* ---------------------------------------------------------------- *)
  (* Factories.                                                         *)
  (* ---------------------------------------------------------------- *)

  (* The type of a system of mode [m] with session type [τ]. *)
  Definition fac (m : mode) (τ : sem_ty Σ) : sem_ty Σ := (𝟙 -{ ⟨⟩ }-[ m ]-> τ)%T.

  Global Instance fac_MS_multi τ : MultiT (fac MS τ) := multi_ty_mbang _.

  Lemma fac_le (m : mode) τ τ' : ⊢ τ ≤ₜ τ' -∗ fac m τ ≤ₜ fac m τ'.
  Proof.
    iIntros "#H". iApply ty_le_mbang_comp; first iApply mode_le_refl.
    iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|iApply "H"].
  Qed.

  (* A multi-session factory is a factory of any mode. *)
  Lemma fac_MS_le (m : mode) τ : ⊢ fac MS τ ≤ₜ fac m τ.
  Proof. destruct m; [iApply (ty_le_mbang_elim MS)|iApply ty_le_refl]. Qed.

  (* A relation between two sessions is a relation between their factories,
     at any mode. *)
  Lemma fac_closure (m : mode) e1 e2 τ :
    ⊢ sem_typed [] e1 e2 ⊥ τ [] -∗ ⊨ᵥ (λ: <>, e1)%V ≤ (λ: <>, e2)%V : fac m τ.
  Proof. iIntros "#He". by iApply (sem_typed_closure _ _ _ BAnon BAnon _ _ m). Qed.

  (* Calling a factory. *)
  Lemma sem_typed_fac_call (m : mode) Γ1 Γ2 F1 F2 τ :
    ⊢ sem_typed Γ1 F1 F2 ⟨⟩ (fac m τ) Γ2 -∗ sem_typed Γ1 (F1 #()%V) (F2 #()%V) ⟨⟩ τ Γ2.
  Proof.
    iIntros "#HF".
    iApply (sem_typed_app_gen 𝟙%T ⟨⟩%R ⟨⟩%R ⟨⟩%R τ with "[] [] [] []");
      [iApply row_le_refl|iApply row_le_refl
      |iApply sem_typed_sub_ty; [iApply (ty_le_mbang_elim m)|iApply "HF"]
      |iApply sem_typed_unit].
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Composition: typing and congruence.                                *)
  (* ---------------------------------------------------------------- *)

  (* Related systems have related composites, at any mode. *)
  Lemma fac_op_typed (m : mode) (o F F' G G' : val) (τF τG τ : sem_ty Σ) :
    ⊢ ⊨ᵥ o ≤ o : (τF ⊸ τG ⊸ τ)%T -∗
      ⊨ᵥ F ≤ F' : fac m τF -∗
      ⊨ᵥ G ≤ G' : fac m τG -∗
      ⊨ᵥ fac_op o F G ≤ fac_op o F' G' : fac m τ.
  Proof.
    iIntros "#Ho #HF #HG". rewrite /fac_op.
    iApply (sem_typed_closure _ _ _ BAnon BAnon _ _ m); first done. simpl.
    iApplyT sem_typed_app_nil; last first.
    { iApply sem_typed_fac_call. iApply sem_typed_val. iApply "HG". }
    iApplyT sem_typed_app_nil; last first.
    { iApply sem_typed_fac_call. iApply sem_typed_val. iApply "HF". }
    iApply sem_typed_val. iApply "Ho".
  Qed.

  Lemma func_comp_f_typed_gen (m : mode) (F F' G G' : val) (T1 M T4 : sem_row Σ → sem_ty Σ) :
    (∀ θ, ⊢ eta_ty (M θ)) →
    ⊢ ⊨ᵥ F ≤ F' : fac m (∀ᵣ θ, M θ → T4 θ) -∗
      ⊨ᵥ G ≤ G' : fac m (∀ᵣ θ, T1 θ → M θ) -∗
      ⊨ᵥ (F ∘f G)%fac ≤ (F' ∘f G')%fac : fac m (∀ᵣ θ, T1 θ → T4 θ).
  Proof. intros HM. iApply fac_op_typed. by iApply func_comp_val_typed. Qed.

  Lemma func_comp_f_typed (m : mode) (F F' G G' : val) (τ1 τ2 τ3 : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ F ≤ F' : fac m (τ__F τ1 τ2) -∗
      ⊨ᵥ G ≤ G' : fac m (τ__F τ2 τ3) -∗
      ⊨ᵥ (F ∘f G)%fac ≤ (F' ∘f G')%fac : fac m (τ__F τ1 τ3).
  Proof.
    iApply func_comp_f_typed_gen. intros θ. apply eta_ty_row_forall => θ1. apply eta_ty_arr.
  Qed.

  Lemma parallel_comp_f_typed (m : mode) (F F' G G' : val) (τ1 τ1' τ2 τ2' : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ F ≤ F' : fac m (τ__F τ2 τ2') -∗
      ⊨ᵥ G ≤ G' : fac m (τ__F τ1 τ1') -∗
      ⊨ᵥ (F ||ᵣ G)%fac ≤ (F' ||ᵣ G')%fac : fac m (∀ᵣ θ, τ__f θ τ1' τ2' → τ__f θ τ1 τ2).
  Proof. iApply fac_op_typed. iApply parallel_comp_val_typed. Qed.

  Lemma functionality_comp_f_typed (m : mode) (F F' G G' : val) (τ1' τ1 τF τ2 : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ F ≤ F' : fac m (τ__F τ2 τF) -∗
      ⊨ᵥ G ≤ G' : fac m (∀ᵣ θ, τ1' θ → τ__f θ τ1 τF) -∗
      ⊨ᵥ (F ∘F G)%fac ≤ (F' ∘F G')%fac : fac m (∀ᵣ θ, τ1' θ → τ__f θ τ1 τ2).
  Proof. iApply fac_op_typed. iApply functionality_comp_val_typed. Qed.

  (* ---------------------------------------------------------------- *)
  (* The program-level operators, for contexts.                         *)
  (* ---------------------------------------------------------------- *)

  Lemma fac_app_val_typed (m : mode) (o : val) (τF τG τ : sem_ty Σ) :
    ⊢ ⊨ᵥ o ≤ o : (τF ⊸ τG ⊸ τ)%T -∗
      ⊨ᵥ fac_app o ≤ fac_app o : (fac m τF ⊸ fac m τG ⊸ fac m τ)%T.
  Proof.
    iIntros "#Ho".
    iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
    iApply sem_typed_closure; first done.
    iApply (sem_typed_oval _ [_]). iApplyT (sem_oval_typed_afun (fac m τG) ⟨⟩%R _ "G").
    iApply (sem_typed_oval _ [_; _]).
    (* the thunk captures the two factories; it is one-shot or multi-shot
       with them *)
    destruct m;
      [iApplyT (sem_oval_typed_afun 𝟙%T ⟨⟩%R _ BAnon)
      |iApplyT (sem_oval_typed_ufun 𝟙%T ⟨⟩%R _ _ BAnon BAnon)]; simpl;
      (iApplyT sem_typed_app_nil; last first; [iApply sem_typed_fac_call; typed_var|]);
      (iApplyT sem_typed_app_nil; last first; [iApply sem_typed_fac_call; typed_var|]);
      iApply sem_typed_val; iApply "Ho".
    Unshelve. all: solve_typed_side.
  Qed.

  Lemma func_comp_app_typed_gen (m : mode) (T1 M T4 : sem_row Σ → sem_ty Σ) :
    (∀ θ, ⊢ eta_ty (M θ)) →
    ⊢ ⊨ᵥ fac_app func_comp ≤ fac_app func_comp :
        (fac m (∀ᵣ θ, M θ → T4 θ) ⊸ fac m (∀ᵣ θ, T1 θ → M θ) ⊸ fac m (∀ᵣ θ, T1 θ → T4 θ))%T.
  Proof. intros HM. iApply fac_app_val_typed. by iApply func_comp_val_typed. Qed.

  Lemma func_comp_app_typed (m : mode) (τ1 τ2 τ3 : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ fac_app func_comp ≤ fac_app func_comp :
        (fac m (τ__F τ1 τ2) ⊸ fac m (τ__F τ2 τ3) ⊸ fac m (τ__F τ1 τ3))%T.
  Proof.
    iApply func_comp_app_typed_gen. intros θ. apply eta_ty_row_forall => θ1. apply eta_ty_arr.
  Qed.

  Lemma parallel_comp_app_typed (m : mode) (τ1 τ1' τ2 τ2' : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ fac_app parallel_composition ≤ fac_app parallel_composition :
        (fac m (τ__F τ2 τ2') ⊸ fac m (τ__F τ1 τ1') ⊸ fac m (∀ᵣ θ, τ__f θ τ1' τ2' → τ__f θ τ1 τ2))%T.
  Proof. iApply fac_app_val_typed. iApply parallel_comp_val_typed. Qed.

  Lemma functionality_comp_app_typed (m : mode) (τ1' τ1 τF τ2 : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ fac_app functionality_composition ≤ fac_app functionality_composition :
        (fac m (τ__F τ2 τF) ⊸ fac m (∀ᵣ θ, τ1' θ → τ__f θ τ1 τF) ⊸ fac m (∀ᵣ θ, τ1' θ → τ__f θ τ1 τ2))%T.
  Proof. iApply fac_app_val_typed. iApply functionality_comp_val_typed. Qed.

  (* ---------------------------------------------------------------- *)
  (* Associativity, lifted from the session level.                     *)
  (* ---------------------------------------------------------------- *)

  (* A session-level law  o1 (o2 f g) j ≃ o1' f (o2' g j),  given as a
     relation between the session terms for related [f], [g], [j] (the
     [_core] lemmas of [comp_operators]), and its mirror image. *)
  Definition sess_law (o1 o2 o1' o2' : val) (τF τG τJ τ : sem_ty Σ) : Prop :=
    ∀ (f1 f2 g1 g2 j1 j2 : expr) (vs : gmap string (val * val)),
      ⊢ brel ⊤ f1 f2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, τF v1 v2 ∗ [] ⊨ₑ vs) -∗
        brel ⊤ g1 g2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, τG v1 v2 ∗ [] ⊨ₑ vs) -∗
        brel ⊤ j1 j2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, τJ v1 v2 ∗ [] ⊨ₑ vs) -∗
        brel ⊤ (o1 (o2 f1 g1) j1) (o1' f2 (o2' g2 j2)) (iLblSig_to_iLblThy ⊥)
          (λ v1 v2, τ v1 v2 ∗ [] ⊨ₑ vs).

  Definition sess_law_R (o1 o2 o1' o2' : val) (τF τG τJ τ : sem_ty Σ) : Prop :=
    ∀ (f1 f2 g1 g2 j1 j2 : expr) (vs : gmap string (val * val)),
      ⊢ brel ⊤ f1 f2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, τF v1 v2 ∗ [] ⊨ₑ vs) -∗
        brel ⊤ g1 g2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, τG v1 v2 ∗ [] ⊨ₑ vs) -∗
        brel ⊤ j1 j2 (iLblSig_to_iLblThy ⊥) (λ v1 v2, τJ v1 v2 ∗ [] ⊨ₑ vs) -∗
        brel ⊤ (o1 f1 (o2 g1 j1)) (o1' (o2' f2 g2) j2) (iLblSig_to_iLblThy ⊥)
          (λ v1 v2, τ v1 v2 ∗ [] ⊨ₑ vs).

  (* Such a law holds for the composites, at any mode: call the composite,
     create J's session (it is created before the inner composite's
     session on both sides), reduce the inner composite's call, and hand the
     remaining session terms to the law. *)
  Lemma fac_assoc_L (m : mode) (o1 o2 o1' o2' F F' G G' J J' : val) (τF τG τJ τ : sem_ty Σ) :
    sess_law o1 o2 o1' o2' τF τG τJ τ →
    ⊢ ⊨ᵥ F ≤ F' : fac m τF -∗ ⊨ᵥ G ≤ G' : fac m τG -∗ ⊨ᵥ J ≤ J' : fac m τJ -∗
      ⊨ᵥ fac_op o1 (fac_op o2 F G) J ≤ fac_op o1' F' (fac_op o2' G' J') : fac m τ.
  Proof.
    rewrite /sem_val_typed /tc_opaque /fac /sem_ty_mbang /sem_ty_arr /=.
    iIntros (Hlaw) "#HF #HG #HJ !#".
    destruct m; simpl; [|iModIntro]; iIntros (u1 u2) "[-> ->]";
      brel_pures';
      iPoseProof ("HJ" $! #()%V #()%V with "[//]") as "HJ'";
      (iApply (brel_bind' [_] [_; _]); [iApply traversable_to_iThy_nil|]);
      (assert (to_iThyIfMono OS [] = []) as <- by done);
      (iApply (brel_mono OS with "[] [$HJ']"); [iApply to_iThy_le_refl|simpl]);
      iIntros (sJ sJ') "HsJ";
      brel_pures';
      iPoseProof (Hlaw (F #()%V) (F' #()%V) (G #()%V) (G' #()%V) sJ sJ' ∅ with "[] [] [HsJ]") as "H";
      first [ (iApply (brel_wand with "(HF [//])"); by iIntros "!# % % $")
            | (iApply (brel_wand with "(HG [//])"); by iIntros "!# % % $")
            | (iApply brel_value; iIntros "$ !>"; by iFrame)
            | (iApply (brel_wand with "H"); by iIntros "!# % % [$ _]") ].
  Qed.

  Lemma fac_assoc_R (m : mode) (o1 o2 o1' o2' F F' G G' J J' : val) (τF τG τJ τ : sem_ty Σ) :
    sess_law_R o1 o2 o1' o2' τF τG τJ τ →
    ⊢ ⊨ᵥ F ≤ F' : fac m τF -∗ ⊨ᵥ G ≤ G' : fac m τG -∗ ⊨ᵥ J ≤ J' : fac m τJ -∗
      ⊨ᵥ fac_op o1 F (fac_op o2 G J) ≤ fac_op o1' (fac_op o2' F' G') J' : fac m τ.
  Proof.
    rewrite /sem_val_typed /tc_opaque /fac /sem_ty_mbang /sem_ty_arr /=.
    iIntros (Hlaw) "#HF #HG #HJ !#".
    destruct m; simpl; [|iModIntro]; iIntros (u1 u2) "[-> ->]";
      brel_pures';
      iPoseProof ("HJ" $! #()%V #()%V with "[//]") as "HJ'";
      (iApply (brel_bind' [_; _] [_]); [iApply traversable_to_iThy_nil|]);
      (assert (to_iThyIfMono OS [] = []) as <- by done);
      (iApply (brel_mono OS with "[] [$HJ']"); [iApply to_iThy_le_refl|simpl]);
      iIntros (sJ sJ') "HsJ";
      brel_pures';
      iPoseProof (Hlaw (F #()%V) (F' #()%V) (G #()%V) (G' #()%V) sJ sJ' ∅ with "[] [] [HsJ]") as "H";
      first [ (iApply (brel_wand with "(HF [//])"); by iIntros "!# % % $")
            | (iApply (brel_wand with "(HG [//])"); by iIntros "!# % % $")
            | (iApply brel_value; iIntros "$ !>"; by iFrame)
            | (iApply (brel_wand with "H"); by iIntros "!# % % [$ _]") ].
  Qed.

  (* The eight laws. *)

  Lemma func_comp_f_assoc (m : mode) (F F' G G' J J' : val) (τ1 τ2 τ3 τ4 : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ F ≤ F' : fac m (τ__F τ1 τ2) -∗ ⊨ᵥ G ≤ G' : fac m (τ__F τ2 τ3) -∗ ⊨ᵥ J ≤ J' : fac m (τ__F τ3 τ4) -∗
      ⊨ᵥ (F ∘f (G ∘f J))%fac ≤ ((F' ∘f G') ∘f J')%fac : fac m (τ__F τ1 τ4).
  Proof. iApply fac_assoc_R. intros ??????. apply func_comp_assoc_core. Qed.

  Lemma func_comp_f_assoc_rev (m : mode) (F F' G G' J J' : val) (τ1 τ2 τ3 τ4 : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ F ≤ F' : fac m (τ__F τ1 τ2) -∗ ⊨ᵥ G ≤ G' : fac m (τ__F τ2 τ3) -∗ ⊨ᵥ J ≤ J' : fac m (τ__F τ3 τ4) -∗
      ⊨ᵥ ((F ∘f G) ∘f J)%fac ≤ (F' ∘f (G' ∘f J'))%fac : fac m (τ__F τ1 τ4).
  Proof. iApply fac_assoc_L. intros ??????. apply func_comp_assoc_rev_core. Qed.

  (* [(F ∘f G) ||ᵣ J ≃ F ∘F (G ||ᵣ J)]: a functionality [F] over a composite
     that uses the port of [G]. *)
  Lemma func_comp_parallel_comp_f_assoc (m : mode) (F F' G G' J J' : val) (τ1 τ2 τG τ1' τ2' : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ F ≤ F' : fac m (τ__F τ2 τG) -∗ ⊨ᵥ G ≤ G' : fac m (τ__F τG τ1') -∗ ⊨ᵥ J ≤ J' : fac m (τ__F τ1 τ2') -∗
      ⊨ᵥ ((F ∘f G) ||ᵣ J)%fac ≤ (F' ∘F (G' ||ᵣ J'))%fac : fac m (∀ᵣ θ, τ__f θ τ2' τ1' → τ__f θ τ1 τ2).
  Proof. iApply fac_assoc_L. intros ??????. apply func_comp_parallel_comp_assoc_core. Qed.

  Lemma func_comp_parallel_comp_f_assoc_rev (m : mode) (F F' G G' J J' : val) (τ1 τ2 τG τ1' τ2' : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ F ≤ F' : fac m (τ__F τ2 τG) -∗ ⊨ᵥ G ≤ G' : fac m (τ__F τG τ1') -∗ ⊨ᵥ J ≤ J' : fac m (τ__F τ1 τ2') -∗
      ⊨ᵥ (F ∘F (G ||ᵣ J))%fac ≤ ((F' ∘f G') ||ᵣ J')%fac : fac m (∀ᵣ θ, τ__f θ τ2' τ1' → τ__f θ τ1 τ2).
  Proof. iApply fac_assoc_R. intros ??????. apply func_comp_parallel_comp_assoc_rev_core. Qed.

  (* [(F ∘F G) ∘f J ≃ F ∘F (G ∘f J)], for a two-port [J] ("gen") and for a
     one-port [J]. *)
  Lemma functionality_comp_func_comp_f_assoc_gen (m : mode) (F F' G G' J J' : val)
      (τ1 τ2 τ1' τF : sem_row Σ → sem_ty Σ) (τJ : sem_row Σ → sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ F ≤ F' : fac m (∀ᵣ θ, (∀ᵣ θF, τF θF -{ sem_row_union (¡θF)%R θ }-∘ 𝟙) → ∀ᵣ θ1, τ2 θ1 -{ sem_row_union (¡θ1)%R θ }-∘ 𝟙) -∗
      ⊨ᵥ G ≤ G' : fac m (∀ᵣ θ, (∀ᵣ θJ1, ∀ᵣ θJ2, τJ θJ1 θJ2 -{ sem_row_union (¡θJ1)%R (sem_row_union (¡θJ2)%R θ) }-∘ 𝟙) → (∀ᵣ θ1, (∀ᵣ θ2, (τ1 θ1 × τF θ2) -{ sem_row_union (¡θ1)%R (sem_row_union (¡θ2)%R θ) }-∘ 𝟙))) -∗
      ⊨ᵥ J ≤ J' : fac m (∀ᵣ θ, (τ1' θ) → (∀ᵣ θJ1, ∀ᵣ θJ2, (τJ θJ1 θJ2) -{ sem_row_union (¡θJ1)%R (sem_row_union (¡θJ2)%R θ) }-∘ 𝟙)) -∗
      ⊨ᵥ ((F ∘F G) ∘f J)%fac ≤ (F' ∘F (G' ∘f J'))%fac :
        fac m (∀ᵣ θ, (τ1' θ) → (∀ᵣ θ1, ∀ᵣ θ2, ((τ1 θ1) × (τ2 θ2)) -{ sem_row_union (¡ θ1)%R (sem_row_union (¡ θ2)%R θ) }-∘ 𝟙)).
  Proof. iApply fac_assoc_L. intros ??????. apply functionality_comp_func_comp_assoc_gen_core. Qed.

  Lemma functionality_comp_func_comp_f_assoc_gen_rev (m : mode) (F F' G G' J J' : val)
      (τ1 τ2 τ1' τF : sem_row Σ → sem_ty Σ) (τJ : sem_row Σ → sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ F ≤ F' : fac m (∀ᵣ θ, (∀ᵣ θF, τF θF -{ sem_row_union (¡θF)%R θ }-∘ 𝟙) → ∀ᵣ θ1, τ2 θ1 -{ sem_row_union (¡θ1)%R θ }-∘ 𝟙) -∗
      ⊨ᵥ G ≤ G' : fac m (∀ᵣ θ, (∀ᵣ θJ1, ∀ᵣ θJ2, τJ θJ1 θJ2 -{ sem_row_union (¡θJ1)%R (sem_row_union (¡θJ2)%R θ) }-∘ 𝟙) → (∀ᵣ θ1, (∀ᵣ θ2, (τ1 θ1 × τF θ2) -{ sem_row_union (¡θ1)%R (sem_row_union (¡θ2)%R θ) }-∘ 𝟙))) -∗
      ⊨ᵥ J ≤ J' : fac m (∀ᵣ θ, (τ1' θ) → (∀ᵣ θJ1, ∀ᵣ θJ2, (τJ θJ1 θJ2) -{ sem_row_union (¡θJ1)%R (sem_row_union (¡θJ2)%R θ) }-∘ 𝟙)) -∗
      ⊨ᵥ (F ∘F (G ∘f J))%fac ≤ ((F' ∘F G') ∘f J')%fac :
        fac m (∀ᵣ θ, (τ1' θ) → (∀ᵣ θ1, ∀ᵣ θ2, ((τ1 θ1) × (τ2 θ2)) -{ sem_row_union (¡ θ1)%R (sem_row_union (¡ θ2)%R θ) }-∘ 𝟙)).
  Proof. iApply fac_assoc_R. intros ??????. apply functionality_comp_func_comp_assoc_gen_rev_core. Qed.

  Lemma functionality_comp_func_comp_f_assoc (m : mode) (F F' G G' J J' : val)
      (τ1 τ2 τ1' τJ τF : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ F ≤ F' : fac m (∀ᵣ θ, (∀ᵣ θF, τF θF -{ sem_row_union (¡θF)%R θ }-∘ 𝟙) → ∀ᵣ θ1, τ2 θ1 -{ sem_row_union (¡θ1)%R θ }-∘ 𝟙) -∗
      ⊨ᵥ G ≤ G' : fac m (∀ᵣ θ, (∀ᵣ θJ, τJ θJ -{ sem_row_union (¡θJ)%R θ }-∘ 𝟙) → ∀ᵣ θ1, ∀ᵣ θ2, (τ1 θ1 × τF θ2) -{ sem_row_union (¡θ2)%R (sem_row_union (¡θ1)%R θ) }-∘ 𝟙) -∗
      ⊨ᵥ J ≤ J' : fac m (∀ᵣ θ, ∀ᵣ θJ, τ1' θ → τJ θJ -{ sem_row_union (¡θJ)%R θ }-∘ 𝟙) -∗
      ⊨ᵥ ((F ∘F G) ∘f J)%fac ≤ (F' ∘F (G' ∘f J'))%fac :
        fac m (∀ᵣ θ, (τ1' θ) → (∀ᵣ θ1, ∀ᵣ θ2, ((τ1 θ1) × (τ2 θ2)) -{ sem_row_union (¡ θ1)%R (sem_row_union (¡ θ2)%R θ) }-∘ 𝟙)).
  Proof. iApply fac_assoc_L. intros ??????. apply functionality_comp_func_comp_assoc_core. Qed.

  Lemma functionality_comp_func_comp_f_assoc_rev (m : mode) (F F' G G' J J' : val)
      (τ1 τ2 τ1' τJ τF : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ F ≤ F' : fac m (∀ᵣ θ, (∀ᵣ θF, τF θF -{ sem_row_union (¡θF)%R θ }-∘ 𝟙) → ∀ᵣ θ1, τ2 θ1 -{ sem_row_union (¡θ1)%R θ }-∘ 𝟙) -∗
      ⊨ᵥ G ≤ G' : fac m (∀ᵣ θ, (∀ᵣ θJ, τJ θJ -{ sem_row_union (¡θJ)%R θ }-∘ 𝟙) → ∀ᵣ θ1, ∀ᵣ θ2, (τ1 θ1 × τF θ2) -{ sem_row_union (¡θ2)%R (sem_row_union (¡θ1)%R θ) }-∘ 𝟙) -∗
      ⊨ᵥ J ≤ J' : fac m (∀ᵣ θ, ∀ᵣ θJ, τ1' θ → τJ θJ -{ sem_row_union (¡θJ)%R θ }-∘ 𝟙) -∗
      ⊨ᵥ (F ∘F (G ∘f J))%fac ≤ ((F' ∘F G') ∘f J')%fac :
        fac m (∀ᵣ θ, (τ1' θ) → (∀ᵣ θ1, ∀ᵣ θ2, ((τ1 θ1) × (τ2 θ2)) -{ sem_row_union (¡ θ1)%R (sem_row_union (¡ θ2)%R θ) }-∘ 𝟙)).
  Proof. iApply fac_assoc_R. intros ??????. apply functionality_comp_func_comp_assoc_rev_core. Qed.

End systems.
