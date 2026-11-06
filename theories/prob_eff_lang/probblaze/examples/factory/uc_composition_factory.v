(* The UC composition theorem of [uc_composition] in factory form, with
   unrestricted functionalities.

   The environment gets the composed system as the factory
   [λ<>, (Pf () ||ᵣ A₀) ∘f ρ], and both realisation games are stated for
   factories, at the multi-session type [𝟙 → τ].  Every functionality takes
   its client with [→] ([τ__Fu] instead of [τ__F]), so a session may be used
   any number of times.  Only π is a black box: it is given as a factory [Pf],
   about which nothing is assumed beyond its advantage bound.  The other
   components are closed, typed expressions.

   Both reductions are a β-step with a factory as the argument
   ([advantage_reduction_f]), so they hold for any [A₀] and [ρ], also ones
   that allocate state when evaluated.  Substituting a factory [λ<>, e] for
   "t" leaves a call [(λ<>, e) ()] in the next hybrid; the perfect steps
   around the reductions remove it ([sem_typed_call_l]/[_r]).  The perfect
   steps are the unrestricted lemmas of [comp_operators_u]. *)

From iris.proofmode Require Import base proofmode classes.
From clutch.prob_eff_lang.probblaze Require Import comp_operators primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory semantics adequacy.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze Require Import mode advantage uc_composition factory_advantage.
From clutch.prob_eff_lang.probblaze.examples Require Import dhke_typing comp_operators_u.
From Stdlib Require Import Reals Psatz.

#[local] Open Scope R_scope.
#[local] Set Default Proof Using "All".

Section factory_operator_typing.
  Context `{!probblazeRGS Σ}.
  Import typed_hint_modes.

  Lemma func_comp_typed_u (S F : expr) (T1 M T4 : sem_row Σ → sem_ty Σ) `{!∀ θ, EtaT (M θ)} :
    ⊢ sem_typed [] S S ⊥ (∀ᵣ θ, M θ → T4 θ)%T [] -∗
      sem_typed [] F F ⊥ (∀ᵣ θ, T1 θ → M θ)%T [] -∗
      sem_typed [] (S ∘f F) (S ∘f F) ⊥ (∀ᵣ θ, T1 θ → T4 θ)%T [].
  Proof.
    iIntros "#HS #HF".
    iApplyT sem_typed_app_nil; last iApply "HF".
    iApplyT sem_typed_app_nil; last iApply "HS".
    iApply sem_typed_val. iApply func_comp_val_typed_u.
  Qed.

  (* The hybrid context [(□ ||ᵣ A₀) ∘f ρ] is a congruence. *)
  Lemma hybrid_cong_u (X1 X2 A₀ ρ : expr) (τc τJ1 τJ2 τA τH : sem_row Σ → sem_ty Σ) :
    is_closed_expr ∅ X1 → is_closed_expr ∅ X2 → is_closed_expr ∅ A₀ → is_closed_expr ∅ ρ →
    ⊢ sem_typed [] X1 X2 ⊥ (τ__Fu τH τJ2) [] -∗
      sem_typed [] A₀ A₀ ⊥ (τ__Fu τA τJ1) [] -∗
      sem_typed [] ρ ρ ⊥ (∀ᵣ θ, τc θ → τ__f θ τJ1 τJ2)%T [] -∗
      sem_typed [] ((X1 ||ᵣ A₀) ∘f ρ) ((X2 ||ᵣ A₀) ∘f ρ) ⊥ (∀ᵣ θ, τc θ → τ__f θ τA τH)%T [].
  Proof.
    iIntros (HX1 HX2 HA₀ Hρ) "#HX #HA₀ #Hρ".
    iApply func_comp_left_u; [by apply closed_parallel|by apply closed_parallel|done|done| |iApply "Hρ"].
    iApply parallel_comp_right_u; [done|done|done|done|iApply "HX"|iApply "HA₀"].
  Qed.

  (* The open term [(t () ||ᵣ A₀) ∘f ρ], for a factory [t]. *)
  Lemma ctx_hybrid_factory_typed (A₀ ρ : expr) (τc τJ1 τJ2 τA τH : sem_row Σ → sem_ty Σ) :
    ⊢ sem_typed [] A₀ A₀ ⊥ (τ__Fu τA τJ1) [] -∗
      sem_typed [] ρ ρ ⊥ (∀ᵣ θ, τc θ → τ__f θ τJ1 τJ2)%T [] -∗
      sem_typed [("t", 𝟙 → τ__Fu τH τJ2)%T] ((("t" #()%V) ||ᵣ A₀) ∘f ρ) ((("t" #()%V) ||ᵣ A₀) ∘f ρ) ⊥
        (∀ᵣ θ, τc θ → τ__f θ τA τH)%T [].
  Proof.
    iIntros "#HA₀ #Hρ".
    iApplyT sem_typed_app_nil; last first.
    { iApply (sem_typed_frame_env_gen _ [_]). iApply "Hρ". }
    iApplyT sem_typed_app_nil; last first.
    - iApplyT sem_typed_app_nil; last first.
      { iApply (sem_typed_frame_env_gen _ [_]). iApply "HA₀". }
      iApplyT sem_typed_app_nil; last first.
      { iApplyT sem_typed_app_nil; last iApply sem_typed_unit. typed_cont. }
      iApply sem_typed_val. iApply parallel_comp_val_typed_u.
    - iApply sem_typed_val. iApply func_comp_val_typed_u.
    Unshelve. all: solve_typed_side.
  Qed.

  (* The open term [S ∘F t ()], for a factory [t]. *)
  Lemma ctx_sim_factory_typed (S : expr) (τc τA τF τH : sem_row Σ → sem_ty Σ) :
    ⊢ sem_typed [] S S ⊥ (τ__Fu τH τF) [] -∗
      sem_typed [("t", 𝟙 → ∀ᵣ θ, τc θ → τ__f θ τA τF)%T] (S ∘F ("t" #()%V)) (S ∘F ("t" #()%V)) ⊥
        (∀ᵣ θ, τc θ → τ__f θ τA τH)%T [].
  Proof.
    iIntros "#HS".
    iApplyT sem_typed_app_nil; last first.
    { iApplyT sem_typed_app_nil; last iApply sem_typed_unit. typed_cont. }
    iApplyT sem_typed_app_nil; last iApply "HS".
    iApply sem_typed_val. iApply functionality_comp_val_typed_u.
    Unshelve. all: solve_typed_side.
  Qed.

  (* A reduction [λ t. A (λ<>, C)] is a typed environment for factories. *)
  Lemma factory_adv_typed (A : val) (C : expr) (α β : sem_ty Σ) `{!MultiT α} :
    ⊢ sem_val_typed A A ((𝟙 → β) → 𝔹)%T -∗
      sem_typed [("t", α)] C C ⊥ β [] -∗
      sem_val_typed (λ: "t", A (λ: <>, C))%V (λ: "t", A (λ: <>, C))%V (α → 𝔹)%T.
  Proof.
    iIntros "#HA #HC".
    iApply (sem_typed_closure _ _ _ BAnon "t" _ _ MS); first done. simpl.
    iApplyT sem_typed_app_nil.
    - iApply sem_typed_val. iApply sem_val_typed_sub; last iApply "HA". iApply ty_le_mbang_elim.
    - iApply (sem_typed_oval _ [_] []). iApplyT sem_oval_typed_ufun. simpl. iApply "HC".
    Unshelve. all: solve_typed_side.
  Qed.

  (* The shapes in which [functionality_comp_func_comp_assoc_u] wants the
     simulator [S'] and the functionality [G]; as
     [sem_typed_sim_assoc_shape]/[sem_typed_fun_assoc_shape]. *)
  Lemma sem_typed_sim_assoc_shape_u (S' : expr) (τG τA τF : sem_row Σ → sem_ty Σ) :
    ⊢ sem_typed [] S' S' ⊥ (∀ᵣ θ, (∀ᵣ θJ, τG θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙) → τ__f θ τA τF)%T [] -∗
      sem_typed [] S' S' ⊥ (∀ᵣ θ, (∀ᵣ θJ, τG θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙) →
          ∀ᵣ θ1, ∀ᵣ θ2, (τA θ1 × τF θ2) -{ sem_row_union (¡θ2) (sem_row_union (¡θ1) θ) }-∘ 𝟙)%T [].
  Proof.
    iIntros "#HS'". iApply sem_typed_sub_ty; last iApply "HS'".
    iApply ty_le_row_forall; iIntros (θ).
    iApply ty_le_mbang_comp; first iApply mode_le_refl.
    iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|].
    rewrite /τ__f. iApply ty_le_row_forall; iIntros (θ1). iApply ty_le_row_forall; iIntros (θ2).
    iApply ty_le_arr; [row_le_submseteq|iApply ty_le_refl|iApply ty_le_refl].
  Qed.

  Lemma sem_typed_fun_assoc_shape_u (G : expr) (τc τG : sem_row Σ → sem_ty Σ) :
    ⊢ sem_typed [] G G ⊥ (∀ᵣ θ, τc θ → ∀ᵣ θJ, τG θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙)%T [] -∗
      sem_typed [] G G ⊥ (∀ᵣ θ, ∀ᵣ θJ, τc θ → τG θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙)%T [].
  Proof.
    iIntros "#HG". iApply sem_typed_sub_ty; last iApply "HG".
    iApply ty_le_row_forall; iIntros (θ).
    iIntros "!# %v1 %v2 #H %θJ". rewrite /sem_ty_mbang /sem_ty_arr /=.
    iIntros "!# %w1 %w2 Hw".
    iApply (brel_wand with "(H Hw)"). iIntros "!# %u1 %u2 Hu". iApply "Hu".
  Qed.

End factory_operator_typing.

Lemma closed_call (e : expr) : is_closed_expr ∅ e → is_closed_expr ∅ ((λ: <>, e)%V #()%V).
Proof. intros He. by apply closed_app. Qed.

Section uc_composition_factory.
  Context `{!probblazeRGpreS Σ}.

  (* The types are those of [uc_composition], with [→] for every client. *)
  Theorem uc_composition_factory
      (Pf : val) (S F S' G A₀ ρ : expr) (b : bool) (ε_π ε_ρ : val → R)
      (τc τJ1 τJ2 τA τF τH τG : ∀ `{probblazeRGS Σ}, sem_row Σ → sem_ty Σ) :
    is_closed_expr ∅ S → is_closed_expr ∅ F → is_closed_expr ∅ A₀ → is_closed_expr ∅ ρ →
    is_closed_expr ∅ S' → is_closed_expr ∅ G →
    (∀ `{probblazeRGS Σ}, ⊢ sem_typed [] S S ⊥ (τ__Fu τH τF) []) →
    (∀ `{probblazeRGS Σ}, ⊢ sem_typed [] F F ⊥ (τ__Fu τF τJ2) []) →
    (∀ `{probblazeRGS Σ}, ⊢ sem_typed [] A₀ A₀ ⊥ (τ__Fu τA τJ1) []) →
    (∀ `{probblazeRGS Σ}, ⊢ sem_typed [] ρ ρ ⊥ (∀ᵣ θ, τc θ → τ__f θ τJ1 τJ2)%T []) →
    (∀ `{probblazeRGS Σ}, ⊢ sem_typed [] S' S' ⊥
        (∀ᵣ θ, (∀ᵣ θJ, τG θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙) → τ__f θ τA τF)%T []) →
    (∀ `{probblazeRGS Σ}, ⊢ sem_typed [] G G ⊥
        (∀ᵣ θ, τc θ → ∀ᵣ θJ, τG θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙)%T []) →
    (* π realises F in the H-hybrid world with simulator S *)
    (∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A ((𝟙 → τ__Fu τH τJ2) → 𝔹)%T) →
       advantage A Pf (λ: <>, S ∘f F)%V #b <= ε_π A) →
    (* ρ realises G in the (F, A₀)-hybrid world with simulator S' *)
    (∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A ((𝟙 → ∀ᵣ θ, τc θ → τ__f θ τA τF) → 𝔹)%T) →
       advantage A (λ: <>, (F ||ᵣ A₀) ∘f ρ)%V (λ: <>, S' ∘f G)%V #b <= ε_ρ A) →
    (* the composed protocol realises G with the composed simulator S ∘F S' *)
    ∀ A : val,
      (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A ((𝟙 → ∀ᵣ θ, τc θ → τ__f θ τA τH) → 𝔹)%T) →
      advantage A (λ: <>, ((Pf #()%V) ||ᵣ A₀) ∘f ρ)%V (λ: <>, (S ∘F S') ∘f G)%V #b
        <= ε_π (λ: "t", A (λ: <>, (("t" #()%V) ||ᵣ A₀) ∘f ρ))%V
         + ε_ρ (λ: "t", A (λ: <>, S ∘F ("t" #()%V)))%V.
  Proof.
    intros HSc HFc HA₀c Hρc HS'c HGc HS HF HA₀ Hρ HS' HG Hπ Hρ' A HA.
    (* The type of the composed systems. *)
    set (β := λ H : probblazeRGS Σ, (∀ᵣ θ, τc H θ → τ__f θ (τA H) (τH H))%T).
    assert (is_closed_expr ∅ (S ∘f F)) as HSF by by apply closed_func_comp.
    assert (is_closed_expr ∅ (F ||ᵣ A₀)) as HFA by by apply closed_parallel.
    assert (is_closed_expr ∅ ((S ∘f F) ||ᵣ A₀)) as HSFA by by apply closed_parallel.
    assert (is_closed_expr ∅ (S ∘F (F ||ᵣ A₀))) as HSFA' by by apply closed_functionality.
    assert (is_closed_expr ∅ ((F ||ᵣ A₀) ∘f ρ)) as HFAρ by by apply closed_func_comp.
    assert (is_closed_expr ∅ (S' ∘f G)) as HS'G by by apply closed_func_comp.
    assert (∀ e (w : val), is_closed_expr ∅ e → val_subst "t" w e = e) as Hsub.
    { intros e w He. apply (subst_is_closed ∅); [done|set_solver]. }
    (* The typings of [S ∘f F] and [S' ∘f G]. *)
    assert (∀ H : probblazeRGS Σ, ⊢ sem_typed [] (S ∘f F) (S ∘f F) ⊥ (τ__Fu (τH H) (τJ2 H)) []) as HSFt.
    { intros HRGS.
      iApply (func_comp_typed_u _ _ _ (λ θ, ∀ᵣ θ₁, τF HRGS θ₁ -{ sem_row_union (¡θ₁) θ }-∘ 𝟙)%T);
        [iApply HS|iApply HF]. }
    assert (∀ H : probblazeRGS Σ,
              ⊢ sem_typed [] (S' ∘f G) (S' ∘f G) ⊥ (∀ᵣ θ, τc H θ → τ__f θ (τA H) (τF H))%T [])
      as HS'Gt.
    { intros HRGS.
      iApply (func_comp_typed_u _ _ _ (λ θ, ∀ᵣ θJ, τG HRGS θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙)%T);
        [iApply HS'|iApply HG]. }
    (* The chain of hybrids, all factories:
         λ<>, (Pf () ||ᵣ A₀) ∘f ρ
       ≤ λ<>, ((λ<>, S ∘f F) () ||ᵣ A₀) ∘f ρ        [Hπ, by β]
       ≃ λ<>, ((S ∘f F) ||ᵣ A₀) ∘f ρ              [the call]
       ≃ λ<>, (S ∘F (F ||ᵣ A₀)) ∘f ρ              [associativity]
       ≃ λ<>, S ∘F ((F ||ᵣ A₀) ∘f ρ)              [associativity]
       ≃ λ<>, S ∘F ((λ<>, (F ||ᵣ A₀) ∘f ρ) ())     [the call]
       ≤ λ<>, S ∘F ((λ<>, S' ∘f G) ())            [Hρ', by β]
       ≃ λ<>, S ∘F (S' ∘f G)                      [the call]
       ≃ λ<>, (S ∘F S') ∘f G                      [associativity]          *)
    eapply (advantage_triangle _ _ (λ: <>, (((λ: <>, S ∘f F)%V #()%V) ||ᵣ A₀) ∘f ρ)%V _ _
              (ε_π (λ: "t", A (λ: <>, (("t" #()%V) ||ᵣ A₀) ∘f ρ))%V)
              (ε_ρ (λ: "t", A (λ: <>, S ∘F ("t" #()%V)))%V)); last lra.
    - (* the protocol side *)
      etrans; first apply (advantage_reduction_f A "t" ((("t" #()%V) ||ᵣ A₀) ∘f ρ) _ _ Pf (λ: <>, S ∘f F)%V).
      1-2: by rewrite /= !Hsub.
      apply Hπ. intros HRGS.
      iApply factory_adv_typed; first iApply HA.
      iApply ctx_hybrid_factory_typed; [iApply HA₀|iApply Hρ].
    - (* the simulator side *)
      eapply (advantage_triangle _ _ (λ: <>, ((S ∘f F) ||ᵣ A₀) ∘f ρ)%V _ _ 0); last (rewrite Rplus_0_l; reflexivity).
      { apply (advantage_zero_f _ _ _ _ β); [exact HA| |]; intros HRGS.
        - iApply hybrid_cong_u; [by apply closed_call|done|done|done| |iApply HA₀|iApply Hρ].
          iApply sem_typed_call_l; [done|iApply HSFt].
        - iApply hybrid_cong_u; [done|by apply closed_call|done|done| |iApply HA₀|iApply Hρ].
          iApply sem_typed_call_r; [done|iApply HSFt]. }
      eapply (advantage_triangle _ _ (λ: <>, (S ∘F (F ||ᵣ A₀)) ∘f ρ)%V _ _ 0); last (rewrite Rplus_0_l; reflexivity).
      { apply (advantage_zero_f _ _ _ _ β); [exact HA| |]; intros HRGS.
        - iApply func_comp_left_u; [done|done|done|done| |iApply Hρ].
          iApply func_comp_parallel_comp_assoc_u; [done|done|done|iApply HS|iApply HF|iApply HA₀].
        - iApply func_comp_left_u; [done|done|done|done| |iApply Hρ].
          iApply func_comp_parallel_comp_assoc_rev_u; [done|done|done|iApply HS|iApply HF|iApply HA₀]. }
      eapply (advantage_triangle _ _ (λ: <>, S ∘F ((F ||ᵣ A₀) ∘f ρ))%V _ _ 0); last (rewrite Rplus_0_l; reflexivity).
      { apply (advantage_zero_f _ _ _ _ β); [exact HA| |]; intros HRGS.
        - iApply (functionality_comp_func_comp_assoc_gen_u _ _ _ _ _ _ (λ θ1 θ2, (τJ1 HRGS θ1 × τJ2 HRGS θ2)%T));
            [done|done|done|iApply HS| |iApply Hρ].
          iApply parallel_comp_right_u; [done|done|done|done|iApply HF|iApply HA₀].
        - iApply (functionality_comp_func_comp_assoc_gen_rev_u _ _ _ _ _ _ (λ θ1 θ2, (τJ1 HRGS θ1 × τJ2 HRGS θ2)%T));
            [done|done|done|iApply HS| |iApply Hρ].
          iApply parallel_comp_right_u; [done|done|done|done|iApply HF|iApply HA₀]. }
      eapply (advantage_triangle _ _ (λ: <>, S ∘F ((λ: <>, (F ||ᵣ A₀) ∘f ρ)%V #()%V))%V _ _ 0);
        last (rewrite Rplus_0_l; reflexivity).
      { apply (advantage_zero_f _ _ _ _ β); [exact HA| |]; intros HRGS.
        - iApply functionality_comp_cong_u; [done|done|done|by apply closed_call| |iApply HS].
          iApply sem_typed_call_r; first done.
          iApply hybrid_cong_u; [done|done|done|done|iApply HF|iApply HA₀|iApply Hρ].
        - iApply functionality_comp_cong_u; [done|done|by apply closed_call|done| |iApply HS].
          iApply sem_typed_call_l; first done.
          iApply hybrid_cong_u; [done|done|done|done|iApply HF|iApply HA₀|iApply Hρ]. }
      eapply (advantage_triangle _ _ (λ: <>, S ∘F ((λ: <>, S' ∘f G)%V #()%V))%V _ _ _ 0);
        last (rewrite Rplus_0_r; reflexivity).
      { etrans; first apply (advantage_reduction_f A "t" (S ∘F ("t" #()%V)) _ _
                               (λ: <>, (F ||ᵣ A₀) ∘f ρ)%V (λ: <>, S' ∘f G)%V).
        1-2: by rewrite /= !Hsub.
        apply Hρ'. intros HRGS.
        iApply factory_adv_typed; first iApply HA.
        iApply ctx_sim_factory_typed. iApply HS. }
      eapply (advantage_triangle _ _ (λ: <>, S ∘F (S' ∘f G))%V _ _ 0 0); last lra.
      { apply (advantage_zero_f _ _ _ _ β); [exact HA| |]; intros HRGS.
        - iApply functionality_comp_cong_u; [done|done|by apply closed_call|done| |iApply HS].
          iApply sem_typed_call_l; [done|iApply HS'Gt].
        - iApply functionality_comp_cong_u; [done|done|done|by apply closed_call| |iApply HS].
          iApply sem_typed_call_r; [done|iApply HS'Gt]. }
      apply (advantage_zero_f _ _ _ _ β); [exact HA| |]; intros HRGS.
      + iApply (functionality_comp_func_comp_assoc_rev_u _ _ _ _ _ _ (τG HRGS));
          [done|done|done|iApply HS
          |iApply sem_typed_sim_assoc_shape_u; iApply HS'
          |iApply sem_typed_fun_assoc_shape_u; iApply HG].
      + iApply (functionality_comp_func_comp_assoc_u _ _ _ _ _ _ (τG HRGS));
          [done|done|done|iApply HS
          |iApply sem_typed_sim_assoc_shape_u; iApply HS'
          |iApply sem_typed_fun_assoc_shape_u; iApply HG].
  Qed.

End uc_composition_factory.
