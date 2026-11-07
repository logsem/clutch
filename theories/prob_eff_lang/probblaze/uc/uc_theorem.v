(* The UC composition theorem for systems as factories (DESIGN.md §6).

   A protocol [π] realises an ideal functionality [F] in the [H]-hybrid
   world with simulator [S] if  H ∘f π ≈ S ∘f F  (the real system [Rπ]
   below is [H ∘f π]: the theorem only sees its environment ports [τH] and
   its advantage bound), and a protocol [ρ] realises [G] in the [F]-hybrid
   world (its other subroutines collected in the side functionality [A₀])
   with simulator [S'] if  (F ||ᵣ A₀) ∘f ρ ≈ S' ∘f G.  Then

       ((H ∘f π) ||ᵣ A₀) ∘f ρ   ≈   (S ∘F S') ∘f G

   and the advantage of an environment [A] against the composed system is
   bounded by the advantages of [A ∘ (λ x. (x ||ᵣ A₀) ∘f ρ)] against π's
   realisation and of [A ∘ (λ x. S ∘F x)] against ρ's realisation.

   All systems are values, so:
   - the perfect steps are the associativity of [uc_systems];
   - the two reductions are [advantage_reduction_ctx] for a context made of
     values; the context is the program-level operator applied to the
     hole, which evaluates to the composite ([hybrid_pure], [fac_app_pure]);
   - only the components that occur in the two contexts or get rearranged
     ([S], [F], [A₀], [ρ], [S'], [G]) are typed; nothing is assumed about
     the real system [Rπ] beyond its advantage bound.

   [uc_composition_f] is the variant without a side functionality. *)

From iris.proofmode Require Import base proofmode classes.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze.uc Require Import comp_operators.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory semantics adequacy.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_systems uc_advantage.
From Stdlib Require Import Reals Psatz.

#[local] Open Scope R_scope.
#[local] Open Scope factory_scope.
#[local] Set Default Proof Using "All".

(* ------------------------------------------------------------------ *)
(* The program-level operators evaluate to the composites.             *)
(* ------------------------------------------------------------------ *)

Lemma fac_app_pure (o F G : val) : rtc pure_step (fac_app o F G) (fac_op o F G).
Proof.
  rewrite /fac_app /fac_op.
  eapply rtc_l.
  { apply (@language.pure_step_ctx _ _ (fill_ctx_no_handler [AppLCtx G] eq_refl)),
      nsteps_once_inv, (pure_exec (φ := True)); done. }
  simpl. eapply rtc_l.
  { apply (@language.pure_step_ctx _ _ (fill_ctx_no_handler [AppLCtx G] eq_refl)),
      nsteps_once_inv, (pure_exec (φ := True)); done. }
  simpl. eapply rtc_l.
  { apply nsteps_once_inv, (pure_exec (φ := True)); done. }
  simpl. eapply rtc_l.
  { apply nsteps_once_inv, (pure_exec (φ := True)); done. }
  done.
Qed.

(* The two contexts through which the environment observes the two
   realisations, and their values. *)
Definition hybrid_ctx (A₀ ρ : val) : ectx :=
  [AppLCtx ρ; AppRCtx (fac_app func_comp); AppLCtx A₀; AppRCtx (fac_app parallel_composition)].
Definition sim_ctx (S : val) : ectx :=
  [AppRCtx (fac_app functionality_composition S)].
Definition hybrid_ctx_f (ρ : val) : ectx :=
  [AppLCtx ρ; AppRCtx (fac_app func_comp)].
Definition sim_ctx_f (S : val) : ectx :=
  [AppRCtx (fac_app func_comp S)].

Lemma hybrid_pure (A₀ ρ v : val) :
  rtc pure_step (fill (hybrid_ctx A₀ ρ) v) ((v ||ᵣ A₀) ∘f ρ).
Proof.
  etrans.
  { apply (rtc_congruence (R := pure_step) (fill [AppLCtx ρ; AppRCtx (fac_app func_comp)]) pure_step
             (fac_app parallel_composition v A₀) (fac_op parallel_composition v A₀)).
    - intros ???. by apply (@language.pure_step_ctx _ _
        (fill_ctx_no_handler [AppLCtx ρ; AppRCtx (fac_app func_comp)] eq_refl)).
    - apply fac_app_pure. }
  apply fac_app_pure.
Qed.

Lemma sim_pure (S v : val) : rtc pure_step (fill (sim_ctx S) v) (S ∘F v).
Proof. apply fac_app_pure. Qed.
Lemma hybrid_f_pure (ρ v : val) : rtc pure_step (fill (hybrid_ctx_f ρ) v) (v ∘f ρ).
Proof. apply fac_app_pure. Qed.
Lemma sim_f_pure (S v : val) : rtc pure_step (fill (sim_ctx_f S) v) (S ∘f v).
Proof. apply fac_app_pure. Qed.

(* ------------------------------------------------------------------ *)
(* Typed contexts and simulator shapes.                                *)
(* ------------------------------------------------------------------ *)

Section contexts.
  Context `{!probblazeRGS Σ}.
  Import typed_hint_modes.

  (* The hybrid-world context [λ x. (x ||ᵣ A₀) ∘f ρ], as an open term in [x]. *)
  Lemma ctx_hybrid_typed (m : mode) (A₀ ρ : val) (τc τJ1 τJ2 τA τH : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ A₀ ≤ A₀ : fac m (τ__F τA τJ1) -∗
      ⊨ᵥ ρ ≤ ρ : fac m (∀ᵣ θ, τc θ ⊸ τ__f θ τJ1 τJ2) -∗
      sem_typed [("v", fac m (τ__F τH τJ2))] (fill (hybrid_ctx A₀ ρ) "v") (fill (hybrid_ctx A₀ ρ) "v") ⊥
        (fac m (∀ᵣ θ, τc θ ⊸ τ__f θ τA τH)) [].
  Proof.
    iIntros "#HA₀ #Hρ". simpl.
    iApplyT sem_typed_app_nil; last first.
    { iApply (sem_typed_frame_env_gen _ [_]). iApply sem_typed_val. iApply "Hρ". }
    iApplyT sem_typed_app_nil; last first.
    - iApplyT sem_typed_app_nil; last first.
      { iApply (sem_typed_frame_env_gen _ [_]). iApply sem_typed_val. iApply "HA₀". }
      iApplyT sem_typed_app_nil; last typed_var.
      iApply sem_typed_val. iApply parallel_comp_app_typed.
    - iApply sem_typed_val. iApply func_comp_app_typed_gen. intros θ. apply eta_ty_τf.
    Unshelve. all: solve_typed_side.
  Qed.

  (* The simulator context [λ x. S ∘F x]. *)
  Lemma ctx_sim_typed (m : mode) (S : val) (τc τA τF τH : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ S ≤ S : fac m (τ__F τH τF) -∗
      sem_typed [("v", fac m (∀ᵣ θ, τc θ ⊸ τ__f θ τA τF))] (fill (sim_ctx S) "v") (fill (sim_ctx S) "v") ⊥
        (fac m (∀ᵣ θ, τc θ ⊸ τ__f θ τA τH)) [].
  Proof.
    iIntros "#HS". simpl.
    iApplyT sem_typed_app_nil; last typed_var.
    iApplyT sem_typed_app_nil; last (iApply sem_typed_val; iApply "HS").
    iApply sem_typed_val. iApply functionality_comp_app_typed.
    Unshelve. all: solve_typed_side.
  Qed.

  (* The same without a side functionality: [λ x. x ∘f ρ] and [λ x. S ∘f x]. *)
  Lemma ctx_hybrid_f_typed (m : mode) (ρ : val) (τc τJ τH : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ ρ ≤ ρ : fac m (τ__F τJ τc) -∗
      sem_typed [("v", fac m (τ__F τH τJ))] (fill (hybrid_ctx_f ρ) "v") (fill (hybrid_ctx_f ρ) "v") ⊥
        (fac m (τ__F τH τc)) [].
  Proof.
    iIntros "#Hρ". simpl.
    iApplyT sem_typed_app_nil; last first.
    { iApply (sem_typed_frame_env_gen _ [_]). iApply sem_typed_val. iApply "Hρ". }
    iApplyT sem_typed_app_nil; last typed_var.
    iApply sem_typed_val. iApply func_comp_app_typed.
    Unshelve. all: solve_typed_side.
  Qed.

  Lemma ctx_sim_f_typed (m : mode) (S : val) (τc τF τH : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ S ≤ S : fac m (τ__F τH τF) -∗
      sem_typed [("v", fac m (τ__F τF τc))] (fill (sim_ctx_f S) "v") (fill (sim_ctx_f S) "v") ⊥
        (fac m (τ__F τH τc)) [].
  Proof.
    iIntros "#HS". simpl.
    iApplyT sem_typed_app_nil; last typed_var.
    iApplyT sem_typed_app_nil; last (iApply sem_typed_val; iApply "HS").
    iApply sem_typed_val. iApply func_comp_app_typed.
    Unshelve. all: solve_typed_side.
  Qed.

  (* The shapes in which [functionality_comp_func_comp_f_assoc] wants a
     simulator [S'] over a one-port functionality and that functionality
     [G]: [S']'s output row in the other order, and [G]'s port quantifier
     outside the arrow.  Both are subtyping. *)
  Lemma sim_assoc_shape_le (τG τA τF : sem_row Σ → sem_ty Σ) :
    ⊢ (∀ᵣ θ, (∀ᵣ θJ, τG θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙) ⊸ τ__f θ τA τF)%T ≤ₜ
      (∀ᵣ θ, (∀ᵣ θJ, τG θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙) ⊸
          ∀ᵣ θ1, ∀ᵣ θ2, (τA θ1 × τF θ2) -{ sem_row_union (¡θ2) (sem_row_union (¡θ1) θ) }-∘ 𝟙)%T.
  Proof.
    iApply ty_le_row_forall; iIntros (θ).
    iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|].
    rewrite /τ__f. iApply ty_le_row_forall; iIntros (θ1). iApply ty_le_row_forall; iIntros (θ2).
    iApply ty_le_arr; [row_le_submseteq|iApply ty_le_refl|iApply ty_le_refl].
  Qed.

  Lemma fun_assoc_shape_le (τc τG : sem_row Σ → sem_ty Σ) :
    ⊢ (∀ᵣ θ, τc θ ⊸ ∀ᵣ θJ, τG θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙)%T ≤ₜ
      (∀ᵣ θ, ∀ᵣ θJ, τc θ ⊸ τG θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙)%T.
  Proof.
    iApply ty_le_row_forall; iIntros (θ).
    iIntros "!# %v1 %v2 H %θJ".
    iDestruct (ty_le_arr with "[] [] []") as "Hle";
      [iApply row_le_refl|iApply ty_le_refl|iApply (ty_le_row_forall_inst _ θJ)|].
    iApply ("Hle" with "H").
  Qed.

End contexts.

(* ------------------------------------------------------------------ *)
(* The composition theorem.                                            *)
(* ------------------------------------------------------------------ *)

Section uc_composition.
  Context `{!probblazeRGpreS Σ}.

  (* Interface types (all indexed by a row):
       τc  : the client interface of ρ
       τJ1 : what ρ needs from A₀;  τJ2 : what ρ needs from F (and from H ∘f π)
       τA  : A₀'s environment ports
       τF  : F's environment ports
       τH  : the environment ports of the real system Rπ = H ∘f π (and of S)
       τG  : the environment port of G, handled by the simulator S'       *)
  Theorem uc_composition (m : mode)
      (Rπ S F A₀ ρ S' G : val) (b : bool) (ε_π ε_ρ : val → R)
      (τc τJ1 τJ2 τA τF τH τG : ∀ `{probblazeRGS Σ}, sem_row Σ → sem_ty Σ) :
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ S ≤ S : fac m (τ__F τH τF)) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ F ≤ F : fac m (τ__F τF τJ2)) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ A₀ ≤ A₀ : fac m (τ__F τA τJ1)) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ ρ ≤ ρ : fac m (∀ᵣ θ, τc θ ⊸ τ__f θ τJ1 τJ2)) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ S' ≤ S' :
        fac m (∀ᵣ θ, (∀ᵣ θJ, τG θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙) ⊸ τ__f θ τA τF)) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ G ≤ G :
        fac m (∀ᵣ θ, τc θ ⊸ ∀ᵣ θJ, τG θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙)) →
    (* π realises F in the H-hybrid world with simulator S *)
    (∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (fac m (τ__F τH τJ2) → 𝔹)%T) →
       advantage A Rπ (S ∘f F) #b <= ε_π A) →
    (* ρ realises G in the (F, A₀)-hybrid world with simulator S' *)
    (∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (fac m (∀ᵣ θ, τc θ ⊸ τ__f θ τA τF) → 𝔹)%T) →
       advantage A ((F ||ᵣ A₀) ∘f ρ) (S' ∘f G) #b <= ε_ρ A) →
    (* the composed protocol realises G with the composed simulator S ∘F S' *)
    ∀ A : val,
      (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (fac m (∀ᵣ θ, τc θ ⊸ τ__f θ τA τH) → 𝔹)%T) →
      advantage A ((Rπ ||ᵣ A₀) ∘f ρ) ((S ∘F S') ∘f G) #b
        <= ε_π (λ: "v", A (("v" ||ᵣₚ A₀) ∘fₚ ρ))%V + ε_ρ (λ: "v", A (S ∘Fₚ "v"))%V.
  Proof.
    intros HS HF HA₀ Hρ HS' HG Hπ Hρ' A HA.
    (* The type of the composed systems. *)
    set (β := λ H : probblazeRGS Σ, fac m (∀ᵣ θ, τc H θ ⊸ τ__f θ (τA H) (τH H))%T).
    (* The chain of hybrids:
         (Rπ ||ᵣ A₀) ∘f ρ
       ≤ ((S ∘f F) ||ᵣ A₀) ∘f ρ          [Hπ, through the hybrid context]
       ≃ (S ∘F (F ||ᵣ A₀)) ∘f ρ          [associativity]
       ≃ S ∘F ((F ||ᵣ A₀) ∘f ρ)          [associativity]
       ≤ S ∘F (S' ∘f G)                  [Hρ', through the simulator context]
       ≃ (S ∘F S') ∘f G                  [associativity]                        *)
    eapply (advantage_triangle _ _ (((S ∘f F) ||ᵣ A₀) ∘f ρ)); first last.
    { reflexivity. }
    - (* the simulator side *)
      eapply (advantage_triangle _ _ ((S ∘F (F ||ᵣ A₀)) ∘f ρ) _ _ 0); first last.
      { rewrite Rplus_0_l. reflexivity. }
      2: { apply (advantage_zero _ _ _ _ β); [exact HA| |]; intros HRGS; iApply sem_typed_val.
           - iApply func_comp_f_typed_gen; [intros θ; apply eta_ty_τf| |iApply Hρ].
             iApply func_comp_parallel_comp_f_assoc; [iApply HS|iApply HF|iApply HA₀].
           - iApply func_comp_f_typed_gen; [intros θ; apply eta_ty_τf| |iApply Hρ].
             iApply func_comp_parallel_comp_f_assoc_rev; [iApply HS|iApply HF|iApply HA₀]. }
      eapply (advantage_triangle _ _ (S ∘F ((F ||ᵣ A₀) ∘f ρ)) _ _ 0); first last.
      { rewrite Rplus_0_l. reflexivity. }
      2: { apply (advantage_zero _ _ _ _ β); [exact HA| |]; intros HRGS; iApply sem_typed_val.
           - iApply (functionality_comp_func_comp_f_assoc_gen _ _ _ _ _ _ _ _ _ _ _
                       (λ θ1 θ2, (τJ1 HRGS θ1 × τJ2 HRGS θ2)%T));
               [iApply HS| |iApply Hρ].
             iApply parallel_comp_f_typed; [iApply HF|iApply HA₀].
           - iApply (functionality_comp_func_comp_f_assoc_gen_rev _ _ _ _ _ _ _ _ _ _ _
                       (λ θ1 θ2, (τJ1 HRGS θ1 × τJ2 HRGS θ2)%T));
               [iApply HS| |iApply Hρ].
             iApply parallel_comp_f_typed; [iApply HF|iApply HA₀]. }
      eapply (advantage_triangle _ _ (S ∘F (S' ∘f G)) _ _ _ 0); first last.
      { rewrite Rplus_0_r. reflexivity. }
      1: { apply (advantage_zero _ _ _ _ β); [exact HA| |]; intros HRGS; iApply sem_typed_val.
           - iApply (functionality_comp_func_comp_f_assoc_rev _ _ _ _ _ _ _ _ _ _ (τG HRGS));
               [iApply HS
               |iApply sem_val_typed_sub; [iApply fac_le; iApply sim_assoc_shape_le|iApply HS']
               |iApply sem_val_typed_sub; [iApply fac_le; iApply fun_assoc_shape_le|iApply HG]].
           - iApply (functionality_comp_func_comp_f_assoc _ _ _ _ _ _ _ _ _ _ (τG HRGS));
               [iApply HS
               |iApply sem_val_typed_sub; [iApply fac_le; iApply sim_assoc_shape_le|iApply HS']
               |iApply sem_val_typed_sub; [iApply fac_le; iApply fun_assoc_shape_le|iApply HG]]. }
      (* the reduction through the simulator context *)
      etrans; first apply (advantage_pure_l_rev _ [] (fill (sim_ctx S) ((F ||ᵣ A₀) ∘f ρ)) _ _);
        [done|apply sim_pure|].
      etrans; first apply (advantage_pure_r_rev _ [] _ (fill (sim_ctx S) (S' ∘f G)) _);
        [done|apply sim_pure|].
      change (S ∘Fₚ "v")%fac with (fill (sim_ctx S) "v").
      etrans; first apply (advantage_reduction_ctx A (sim_ctx S)).
      { done. }
      { intros vs w Hw. simpl. by rewrite Hw. }
      apply Hρ'. intros HRGS.
      iApply ctx_adv_typed; first iApply HA. iApply ctx_sim_typed. iApply HS.
    - (* the protocol side *)
      etrans; first apply (advantage_pure_l_rev _ [] (fill (hybrid_ctx A₀ ρ) Rπ) _ _);
        [done|apply hybrid_pure|].
      etrans; first apply (advantage_pure_r_rev _ [] _ (fill (hybrid_ctx A₀ ρ) (S ∘f F)) _);
        [done|apply hybrid_pure|].
      change (("v" ||ᵣₚ A₀) ∘fₚ ρ)%fac with (fill (hybrid_ctx A₀ ρ) "v").
      etrans; first apply (advantage_reduction_ctx A (hybrid_ctx A₀ ρ)).
      { done. }
      { intros vs w Hw. simpl. by rewrite Hw. }
      apply Hπ. intros HRGS.
      iApply ctx_adv_typed; first iApply HA. iApply ctx_hybrid_typed; [iApply HA₀|iApply Hρ].
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Without a side functionality: ρ runs directly on top of F, every   *)
  (* component is a one-port system and the bookkeeping is              *)
  (* [func_comp_f_assoc].                                               *)
  (* ---------------------------------------------------------------- *)

  (* Interface types:
       τc : the client interface of ρ (and of G)
       τJ : what ρ needs, i.e. F's client interface
       τF : F's environment ports      τH : the environment ports of Rπ = H ∘f π and of S
       τG : G's environment ports, handled by S'                                   *)
  Theorem uc_composition_f (m : mode)
      (Rπ S F S' G ρ : val) (b : bool) (ε_π ε_ρ : val → R)
      (τc τJ τF τH τG : ∀ `{probblazeRGS Σ}, sem_row Σ → sem_ty Σ) :
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ S ≤ S : fac m (τ__F τH τF)) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ F ≤ F : fac m (τ__F τF τJ)) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ ρ ≤ ρ : fac m (τ__F τJ τc)) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ S' ≤ S' : fac m (τ__F τF τG)) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ G ≤ G : fac m (τ__F τG τc)) →
    (* π realises F in the H-hybrid world with simulator S *)
    (∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (fac m (τ__F τH τJ) → 𝔹)%T) →
       advantage A Rπ (S ∘f F) #b <= ε_π A) →
    (* ρ realises G in the F-hybrid world with simulator S' *)
    (∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (fac m (τ__F τF τc) → 𝔹)%T) →
       advantage A (F ∘f ρ) (S' ∘f G) #b <= ε_ρ A) →
    ∀ A : val,
      (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (fac m (τ__F τH τc) → 𝔹)%T) →
      advantage A (Rπ ∘f ρ) ((S ∘f S') ∘f G) #b
        <= ε_π (λ: "v", A ("v" ∘fₚ ρ))%V + ε_ρ (λ: "v", A (S ∘fₚ "v"))%V.
  Proof.
    intros HS HF Hρ HS' HG Hπ Hρ' A HA.
    set (β := λ H : probblazeRGS Σ, fac m (τ__F (τH H) (τc H))).
    (*   Rπ ∘f ρ  ≤  (S ∘f F) ∘f ρ  ≃  S ∘f (F ∘f ρ)  ≤  S ∘f (S' ∘f G)  ≃  (S ∘f S') ∘f G   *)
    eapply (advantage_triangle _ _ ((S ∘f F) ∘f ρ)); first last.
    { reflexivity. }
    - eapply (advantage_triangle _ _ (S ∘f (F ∘f ρ)) _ _ 0); first last.
      { rewrite Rplus_0_l. reflexivity. }
      2: { apply (advantage_zero _ _ _ _ β); [exact HA| |]; intros HRGS; iApply sem_typed_val.
           - iApply func_comp_f_assoc_rev; [iApply HS|iApply HF|iApply Hρ].
           - iApply func_comp_f_assoc; [iApply HS|iApply HF|iApply Hρ]. }
      eapply (advantage_triangle _ _ (S ∘f (S' ∘f G)) _ _ _ 0); first last.
      { rewrite Rplus_0_r. reflexivity. }
      1: { apply (advantage_zero _ _ _ _ β); [exact HA| |]; intros HRGS; iApply sem_typed_val.
           - iApply func_comp_f_assoc; [iApply HS|iApply HS'|iApply HG].
           - iApply func_comp_f_assoc_rev; [iApply HS|iApply HS'|iApply HG]. }
      etrans; first apply (advantage_pure_l_rev _ [] (fill (sim_ctx_f S) (F ∘f ρ)) _ _);
        [done|apply sim_f_pure|].
      etrans; first apply (advantage_pure_r_rev _ [] _ (fill (sim_ctx_f S) (S' ∘f G)) _);
        [done|apply sim_f_pure|].
      change (S ∘fₚ "v")%fac with (fill (sim_ctx_f S) "v").
      etrans; first apply (advantage_reduction_ctx A (sim_ctx_f S)).
      { done. }
      { intros vs w Hw. simpl. by rewrite Hw. }
      apply Hρ'. intros HRGS.
      iApply ctx_adv_typed; first iApply HA. iApply ctx_sim_f_typed. iApply HS.
    - etrans; first apply (advantage_pure_l_rev _ [] (fill (hybrid_ctx_f ρ) Rπ) _ _);
        [done|apply hybrid_f_pure|].
      etrans; first apply (advantage_pure_r_rev _ [] _ (fill (hybrid_ctx_f ρ) (S ∘f F)) _);
        [done|apply hybrid_f_pure|].
      change ("v" ∘fₚ ρ)%fac with (fill (hybrid_ctx_f ρ) "v").
      etrans; first apply (advantage_reduction_ctx A (hybrid_ctx_f ρ)).
      { done. }
      { intros vs w Hw. simpl. by rewrite Hw. }
      apply Hπ. intros HRGS.
      iApply ctx_adv_typed; first iApply HA. iApply ctx_hybrid_f_typed. iApply Hρ.
  Qed.

End uc_composition.
