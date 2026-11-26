(* Modules as functions between interfaces (uc_eff/DESIGN.md).

   A module is a closed value that takes the operations it uses and
   returns the operations it offers; applying it creates an instance (it
   allocates the instance's state).  Its type is

       Mod X Y  =  ∀θ. X θ → Y θ

   for interfaces [X], [Y]: types indexed by the row of the operations.

   - a functionality [F : Mod Adv_F Ports] takes its adversarial operations
     and returns its ports;
   - a protocol [ρ : Mod Ports_F Ports] takes the ports below and returns
     its own;
   - a simulator [S : Mod Adv_R Adv_F] takes the real adversarial operations
     and returns the ideal ones: its clauses, as functions sharing its state.

   There is one composition operator, [g ⊳ f = λ a. g (f a)]: a protocol on
   a functionality is [ρ ⊳ F], a simulator attached to a functionality is
   [F ⊳ S], two simulators compose to [S' ⊳ S].  Moving a simulator past a
   protocol is associativity.

   Modules are put side by side with the tensor [f ⊗ g]; a simulator that
   leaves the other side alone is [S ⊗ id_mod], and it is moved out of a
   tensor by the interchange law.

   The module type takes a mode, [ModM m X Y = ∀θ. X θ -[m]-> Y θ]:
   [Mod = ModM MS] for modules the environment may instantiate any number
   of times, [ModA = ModM OS] for modules it instantiates once (statements
   with a statistical bound).  The operator lemmas are proved for the
   functions [X θ ⊸ Y θ] at one row ([*_arr]) and lifted to either mode
   ([ModM_intro], [ModM_map2], [ModM_map3]); the composition theorem holds
   in either mode.  A bound for every environment of [Mod]s is one for
   every environment of [ModA]s ([advantage_Mod_ModA]). *)

From iris.proofmode Require Import base proofmode classes.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory semantics logic adequacy mode.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_compat.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage uc_advantage.
From Stdlib Require Import Reals Psatz.

#[local] Open Scope R_scope.
#[local] Set Default Proof Using "All".

(* ------------------------------------------------------------------ *)
(* Composition.                                                        *)
(* ------------------------------------------------------------------ *)

(* The composite of two modules: a value, for values [g] and [f]. *)
Definition comp_op (g f : val) : val := (λ: "a", g (f "a"))%V.

(* The same as a program, for contexts with a hole; it evaluates to
   [comp_op] ([comp_app_pure]). *)
Definition comp_app : val := λ: "g" "f" "a", "g" ("f" "a").

Declare Scope mod_scope.
Delimit Scope mod_scope with md.
Notation "g ⊳ f" := (comp_op g f) (at level 40, left associativity) : mod_scope.

Lemma comp_app_pure (g f : val) : rtc pure_step (comp_app g f) (comp_op g f).
Proof.
  rewrite /comp_app /comp_op.
  eapply rtc_l.
  { apply (@language.pure_step_ctx _ _ (fill_ctx_no_handler [AppLCtx f] eq_refl)),
      nsteps_once_inv, (pure_exec (φ := True)); done. }
  simpl. eapply rtc_l.
  { apply (@language.pure_step_ctx _ _ (fill_ctx_no_handler [AppLCtx f] eq_refl)),
      nsteps_once_inv, (pure_exec (φ := True)); done. }
  simpl. eapply rtc_l.
  { apply nsteps_once_inv, (pure_exec (φ := True)); done. }
  simpl. eapply rtc_l.
  { apply nsteps_once_inv, (pure_exec (φ := True)); done. }
  done.
Qed.

(* ------------------------------------------------------------------ *)
(* Tensor.                                                             *)
(* ------------------------------------------------------------------ *)

(* Two modules side by side: the composite takes a pair of interfaces and
   returns a pair of interfaces. *)
Definition tens_op (f g : val) : val :=
  (λ: "a", let: "u" := f (Fst "a") in let: "v" := g (Snd "a") in ("u", "v"))%V.

Definition tens_app : val :=
  λ: "f" "g" "a", let: "u" := "f" (Fst "a") in let: "v" := "g" (Snd "a") in ("u", "v").

Notation "f ⊗ g" := (tens_op f g) (at level 35, right associativity) : mod_scope.

(* The identity module. *)
Definition id_mod : val := λ: "a", "a".

Lemma tens_app_pure (f g : val) : rtc pure_step (tens_app f g) (tens_op f g).
Proof.
  rewrite /tens_app /tens_op.
  eapply rtc_l.
  { apply (@language.pure_step_ctx _ _ (fill_ctx_no_handler [AppLCtx g] eq_refl)),
      nsteps_once_inv, (pure_exec (φ := True)); done. }
  simpl. eapply rtc_l.
  { apply (@language.pure_step_ctx _ _ (fill_ctx_no_handler [AppLCtx g] eq_refl)),
      nsteps_once_inv, (pure_exec (φ := True)); done. }
  simpl. eapply rtc_l.
  { apply nsteps_once_inv, (pure_exec (φ := True)); done. }
  simpl. eapply rtc_l.
  { apply nsteps_once_inv, (pure_exec (φ := True)); done. }
  done.
Qed.

Section modules.
  Context `{!probblazeRGS Σ}.

  (* The type of a module from interface [X] to interface [Y], in mode [m]:
     at [MS] the environment may instantiate it any number of times, at
     [OS] once. *)
  Definition ModM (m : mode) (X Y : sem_row Σ → sem_ty Σ) : sem_ty Σ :=
    (∀ᵣ θ, X θ -[m]-> Y θ)%T.

  (* A module. *)
  Definition Mod (X Y : sem_row Σ → sem_ty Σ) : sem_ty Σ := ModM MS X Y.

  (* A module that the environment may instantiate only once.  Statements
     with a statistical bound are about such modules: the bound is spent
     when the module is instantiated. *)
  Definition ModA (X Y : sem_row Σ → sem_ty Σ) : sem_ty Σ := ModM OS X Y.

  Global Instance ModM_MS_persistent X Y v1 v2 : Persistent (ModM MS X Y v1 v2).
  Proof. rewrite /ModM /sem_ty_row_forall /sem_ty_mbang /=. apply _. Qed.

  Global Instance Mod_persistent X Y v1 v2 : Persistent (Mod X Y v1 v2).
  Proof. rewrite /Mod. apply _. Qed.

  (* A module is a one-instance module. *)
  Lemma Mod_ModA X Y v1 v2 : Mod X Y v1 v2 ⊢ ModA X Y v1 v2.
  Proof.
    rewrite /Mod /ModA /ModM /sem_ty_row_forall /sem_ty_mbang /=.
    iIntros "H" (θ). iDestruct ("H" $! θ) as "#H'". done.
  Qed.

  Lemma Mod_ModA_typed v1 v2 X Y : ⊨ᵥ v1 ≤ v2 : Mod X Y ⊢ ⊨ᵥ v1 ≤ v2 : ModA X Y.
  Proof.
    rewrite /sem_val_typed /tc_opaque. iIntros "#H !>". by iApply Mod_ModA.
  Qed.

  (* An environment for one-instance modules is an environment for
     modules. *)
  Lemma env_ModA_Mod (A : val) X Y :
    ⊨ᵥ A ≤ A : (ModA X Y → 𝔹) ⊢ ⊨ᵥ A ≤ A : (Mod X Y → 𝔹).
  Proof.
    rewrite /sem_val_typed /tc_opaque /sem_ty_mbang /sem_ty_arr /=.
    iIntros "#HA !> !>" (v1 v2) "Hv". iApply "HA". by iApply Mod_ModA.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Lifting statements about the functions of one row to modules.      *)
  (* ---------------------------------------------------------------- *)

  (* The operator lemmas below are proved for the functions [X θ ⊸ Y θ]
     that a module is at each row, and lifted to modules of any mode. *)
  Lemma ModM_intro m X Y v1 v2 :
    (∀ θ, ⊢ (X θ ⊸ Y θ)%T v1 v2) → ⊢ ModM m X Y v1 v2.
  Proof.
    intros H. rewrite /ModM /sem_ty_row_forall /sem_ty_mbang.
    iIntros (θ). destruct m; simpl.
    - iApply H.
    - iModIntro. iApply H.
  Qed.

  Lemma ModM_map2 m X1 Y1 X2 Y2 X Y v1 v1' v2 v2' w w' :
    (∀ θ, ⊢ (X1 θ ⊸ Y1 θ)%T v1 v1' -∗ (X2 θ ⊸ Y2 θ)%T v2 v2' -∗ (X θ ⊸ Y θ)%T w w') →
    ⊢ ModM m X1 Y1 v1 v1' -∗ ModM m X2 Y2 v2 v2' -∗ ModM m X Y w w'.
  Proof.
    intros H. rewrite /ModM /sem_ty_row_forall /sem_ty_mbang.
    iIntros "H1 H2" (θ). iSpecialize ("H1" $! θ). iSpecialize ("H2" $! θ).
    destruct m; simpl.
    - iApply (H with "H1 H2").
    - iDestruct "H1" as "#H1". iDestruct "H2" as "#H2". iModIntro.
      iApply (H with "H1 H2").
  Qed.

  Lemma ModM_map3 m X1 Y1 X2 Y2 X3 Y3 X Y v1 v1' v2 v2' v3 v3' w w' :
    (∀ θ, ⊢ (X1 θ ⊸ Y1 θ)%T v1 v1' -∗ (X2 θ ⊸ Y2 θ)%T v2 v2' -∗
            (X3 θ ⊸ Y3 θ)%T v3 v3' -∗ (X θ ⊸ Y θ)%T w w') →
    ⊢ ModM m X1 Y1 v1 v1' -∗ ModM m X2 Y2 v2 v2' -∗ ModM m X3 Y3 v3 v3' -∗
      ModM m X Y w w'.
  Proof.
    intros H. rewrite /ModM /sem_ty_row_forall /sem_ty_mbang.
    iIntros "H1 H2 H3" (θ). iSpecialize ("H1" $! θ). iSpecialize ("H2" $! θ).
    iSpecialize ("H3" $! θ). destruct m; simpl.
    - iApply (H with "H1 H2 H3").
    - iDestruct "H1" as "#H1". iDestruct "H2" as "#H2". iDestruct "H3" as "#H3".
      iModIntro. iApply (H with "H1 H2 H3").
  Qed.

  (* Calling a function of the empty row, keeping a frame [P]: a module
     body runs without effects, so the interfaces it holds, which may be
     affine, are kept across the calls it makes. *)
  Lemma brel_call_nil (A B : sem_ty Σ) (P : iProp Σ) (f1 f2 w1 w2 : val) K1 K2 R :
    (∀ l1s, NeutralEctx l1s K1) → (∀ l2s, NeutralEctx l2s K2) →
    ⊢ (A ⊸ B)%T f1 f2 -∗ A w1 w2 -∗ P -∗
      □ (∀ v1 v2, B v1 v2 -∗ P -∗
           BREL fill K1 (Val v1) ≤ fill K2 (Val v2) <|iLblSig_to_iLblThy ⟨⟩%R|> {{ R }}) -∗
      BREL fill K1 (f1 w1) ≤ fill K2 (f2 w2) <|iLblSig_to_iLblThy ⟨⟩%R|> {{ R }}.
  Proof.
    iIntros (HK1 HK2) "Hf Hw HP #Hc".
    iApply (brel_bind K1 K2); [by iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand _ _ _ (λ v1 v2, B v1 v2 ∗ P)%I with "[Hf Hw HP]"); last first.
    { iIntros "!# % % [HB HP]". iApply ("Hc" with "HB HP"). }
    iApply (brel_mono_on_prop _ _ _ P with "[] HP").
    { iApply (row_type_sub (ρ := ⟨⟩%R) (τ := λ _ _, P) $! #()%V #()%V). }
    rewrite /sem_ty_arr /=. iApply ("Hf" with "Hw").
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Composition: typing, associativity.                                *)
  (* ---------------------------------------------------------------- *)

  Lemma comp_arr (g g' f f' : val) (X Y Z : sem_ty Σ) :
    ⊢ (Y ⊸ Z)%T g g' -∗ (X ⊸ Y)%T f f' -∗ (X ⊸ Z)%T (comp_op g f) (comp_op g' f').
  Proof.
    iIntros "Hg Hf". rewrite {3}/sem_ty_arr. iIntros (a1 a2) "Ha". rewrite /comp_op.
    brel_pures_l. brel_pures_r.
    iApply (brel_call_nil X Y ((Y ⊸ Z)%T g g') f f' a1 a2 [AppRCtx _] [AppRCtx _]
              with "Hf Ha Hg").
    iIntros "!>" (b1 b2) "Hb Hg". simpl. iApply ("Hg" with "Hb").
  Qed.

  Lemma comp_op_sem m (g g' f f' : val) (X Y Z : sem_row Σ → sem_ty Σ) :
    ⊢ ModM m Y Z g g' -∗ ModM m X Y f f' -∗ ModM m X Z (comp_op g f) (comp_op g' f').
  Proof. iApply ModM_map2. intros θ. iApply comp_arr. Qed.

  Lemma comp_op_typed m (g g' f f' : val) (X Y Z : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ g ≤ g' : ModM m Y Z -∗ ⊨ᵥ f ≤ f' : ModM m X Y -∗
      ⊨ᵥ comp_op g f ≤ comp_op g' f' : ModM m X Z.
  Proof.
    rewrite /sem_val_typed /tc_opaque. iIntros "#Hg #Hf !>".
    iApply (comp_op_sem with "Hg Hf").
  Qed.

  (* Associativity, with congruence, in both directions. *)
  Lemma comp_assoc_arr (h h' g g' f f' : val) (X Y Z W : sem_ty Σ) :
    ⊢ (Z ⊸ W)%T h h' -∗ (Y ⊸ Z)%T g g' -∗ (X ⊸ Y)%T f f' -∗
      (X ⊸ W)%T (comp_op h (comp_op g f)) (comp_op (comp_op h' g') f').
  Proof.
    iIntros "Hh Hg Hf". rewrite {4}/sem_ty_arr. iIntros (a1 a2) "Ha". rewrite /comp_op.
    brel_pures_l. brel_pures_r.
    iApply (brel_call_nil X Y ((Z ⊸ W)%T h h' ∗ (Y ⊸ Z)%T g g') f f' a1 a2
              [AppRCtx _; AppRCtx _] [AppRCtx _] with "Hf Ha [$Hh $Hg]").
    iIntros "!>" (b1 b2) "Hb [Hh Hg]". simpl. brel_pures_r.
    iApply (brel_call_nil Y Z ((Z ⊸ W)%T h h') g g' b1 b2 [AppRCtx _] [AppRCtx _]
              with "Hg Hb Hh").
    iIntros "!>" (c1 c2) "Hc Hh". simpl. iApply ("Hh" with "Hc").
  Qed.

  Lemma comp_assoc_rev_arr (h h' g g' f f' : val) (X Y Z W : sem_ty Σ) :
    ⊢ (Z ⊸ W)%T h h' -∗ (Y ⊸ Z)%T g g' -∗ (X ⊸ Y)%T f f' -∗
      (X ⊸ W)%T (comp_op (comp_op h g) f) (comp_op h' (comp_op g' f')).
  Proof.
    iIntros "Hh Hg Hf". rewrite {4}/sem_ty_arr. iIntros (a1 a2) "Ha". rewrite /comp_op.
    brel_pures_l. brel_pures_r.
    iApply (brel_call_nil X Y ((Z ⊸ W)%T h h' ∗ (Y ⊸ Z)%T g g') f f' a1 a2
              [AppRCtx _] [AppRCtx _; AppRCtx _] with "Hf Ha [$Hh $Hg]").
    iIntros "!>" (b1 b2) "Hb [Hh Hg]". simpl. brel_pures_l.
    iApply (brel_call_nil Y Z ((Z ⊸ W)%T h h') g g' b1 b2 [AppRCtx _] [AppRCtx _]
              with "Hg Hb Hh").
    iIntros "!>" (c1 c2) "Hc Hh". simpl. iApply ("Hh" with "Hc").
  Qed.

  Lemma comp_op_assoc m (h h' g g' f f' : val) (X Y Z W : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ h ≤ h' : ModM m Z W -∗ ⊨ᵥ g ≤ g' : ModM m Y Z -∗ ⊨ᵥ f ≤ f' : ModM m X Y -∗
      ⊨ᵥ comp_op h (comp_op g f) ≤ comp_op (comp_op h' g') f' : ModM m X W.
  Proof.
    rewrite /sem_val_typed /tc_opaque. iIntros "#Hh #Hg #Hf !>".
    iApply (ModM_map3 with "Hh Hg Hf"). intros θ. iApply comp_assoc_arr.
  Qed.

  Lemma comp_op_assoc_rev m (h h' g g' f f' : val) (X Y Z W : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ h ≤ h' : ModM m Z W -∗ ⊨ᵥ g ≤ g' : ModM m Y Z -∗ ⊨ᵥ f ≤ f' : ModM m X Y -∗
      ⊨ᵥ comp_op (comp_op h g) f ≤ comp_op h' (comp_op g' f') : ModM m X W.
  Proof.
    rewrite /sem_val_typed /tc_opaque. iIntros "#Hh #Hg #Hf !>".
    iApply (ModM_map3 with "Hh Hg Hf"). intros θ. iApply comp_assoc_rev_arr.
  Qed.

  (* An environment extended by a protocol, or by a simulator, is an
     environment. *)
  Lemma env_under_typed m (A g : val) (X Y Z : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ A ≤ A : (ModM m X Z → 𝔹) -∗ ⊨ᵥ g ≤ g : ModM m Y Z -∗
      ⊨ᵥ (λ: "v", A (comp_app g "v"))%V ≤ (λ: "v", A (comp_app g "v"))%V
        : (ModM m X Y → 𝔹).
  Proof.
    rewrite /sem_val_typed /tc_opaque. iIntros "#HA #Hg".
    rewrite /sem_ty_mbang /sem_ty_arr /=.
    iIntros "!> !>" (v1 v2) "Hv". rewrite /comp_app.
    brel_pures_l. brel_pures_r.
    iApply "HA". iApply (comp_op_sem with "Hg Hv").
  Qed.

  Lemma env_over_typed m (A f : val) (X Y Z : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ A ≤ A : (ModM m X Z → 𝔹) -∗ ⊨ᵥ f ≤ f : ModM m X Y -∗
      ⊨ᵥ (λ: "v", A (comp_app "v" f))%V ≤ (λ: "v", A (comp_app "v" f))%V
        : (ModM m Y Z → 𝔹).
  Proof.
    rewrite /sem_val_typed /tc_opaque. iIntros "#HA #Hf".
    rewrite /sem_ty_mbang /sem_ty_arr /=.
    iIntros "!> !>" (v1 v2) "Hv". rewrite /comp_app.
    brel_pures_l. brel_pures_r.
    iApply "HA". iApply (comp_op_sem with "Hv Hf").
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Tensor: typing, identity, interchange.                             *)
  (* ---------------------------------------------------------------- *)

  (* The product of two interfaces. *)
  Definition IProd (X Y : sem_row Σ → sem_ty Σ) : sem_row Σ → sem_ty Σ :=
    λ θ, (X θ × Y θ)%T.

  Lemma tens_arr (f f' g g' : val) (X Y X' Y' : sem_ty Σ) :
    ⊢ (X ⊸ Y)%T f f' -∗ (X' ⊸ Y')%T g g' -∗
      ((X × X') ⊸ (Y × Y'))%T (tens_op f g) (tens_op f' g').
  Proof.
    iIntros "Hf Hg". rewrite {3}/sem_ty_arr. iIntros (a1 a2) "Ha".
    iDestruct "Ha" as (x1 x2 y1 y2) "(-> & -> & Hx & Hy)". rewrite /tens_op.
    try (try brel_pures_l). try (try brel_pures_r).
    iApply (brel_call_nil X Y (X' y1 y2 ∗ (X' ⊸ Y')%T g g') f f' x1 x2
              [AppRCtx _] [AppRCtx _] with "Hf Hx [$Hy $Hg]").
    iIntros "!>" (u1 u2) "Hu [Hy Hg]". simpl. try (try brel_pures_l). try (try brel_pures_r).
    iApply (brel_call_nil X' Y' (Y u1 u2) g g' y1 y2 [AppRCtx _] [AppRCtx _]
              with "Hg Hy Hu").
    iIntros "!>" (v1 v2) "Hv Hu". simpl. try (try brel_pures_l). try (try brel_pures_r).
    iModIntro. iExists _, _, _, _. by iFrame.
  Qed.

  Lemma tens_op_sem m (f f' g g' : val) (X Y X' Y' : sem_row Σ → sem_ty Σ) :
    ⊢ ModM m X Y f f' -∗ ModM m X' Y' g g' -∗
      ModM m (IProd X X') (IProd Y Y') (tens_op f g) (tens_op f' g').
  Proof. iApply ModM_map2. intros θ. iApply tens_arr. Qed.

  Lemma tens_op_typed m (f f' g g' : val) (X Y X' Y' : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ f ≤ f' : ModM m X Y -∗ ⊨ᵥ g ≤ g' : ModM m X' Y' -∗
      ⊨ᵥ tens_op f g ≤ tens_op f' g' : ModM m (IProd X X') (IProd Y Y').
  Proof.
    rewrite /sem_val_typed /tc_opaque. iIntros "#Hf #Hg !>".
    iApply (tens_op_sem with "Hf Hg").
  Qed.

  Lemma id_mod_typed m (X : sem_row Σ → sem_ty Σ) : ⊢ ⊨ᵥ id_mod ≤ id_mod : ModM m X X.
  Proof.
    rewrite /sem_val_typed /tc_opaque. iModIntro. iApply ModM_intro. intros θ.
    rewrite /sem_ty_arr. iIntros (a1 a2) "Ha". rewrite /id_mod.
    try (try brel_pures_l). try (try brel_pures_r). by iModIntro.
  Qed.

  (* Interchange, with congruence, in both directions: a module beside [h]
     composed below is composed below beside the identity. *)
  Lemma tens_interchange_arr (g g' f f' h h' : val) (X Y Z X' Y' : sem_ty Σ) :
    ⊢ (Y ⊸ Z)%T g g' -∗ (X ⊸ Y)%T f f' -∗ (X' ⊸ Y')%T h h' -∗
      ((X × X') ⊸ (Z × Y'))%T (tens_op (comp_op g f) h)
                               (comp_op (tens_op g' h') (tens_op f' id_mod)).
  Proof.
    iIntros "Hg Hf Hh". rewrite {4}/sem_ty_arr. iIntros (a1 a2) "Ha".
    iDestruct "Ha" as (x1 x2 y1 y2) "(-> & -> & Hx & Hy)". rewrite /tens_op /comp_op /id_mod.
    try (try brel_pures_l). try (try brel_pures_r).
    iApply (brel_call_nil X Y (X' y1 y2 ∗ (Y ⊸ Z)%T g g' ∗ (X' ⊸ Y')%T h h') f f' x1 x2
              [AppRCtx _; AppRCtx _] [AppRCtx _; AppRCtx _] with "Hf Hx [$Hy $Hg $Hh]").
    iIntros "!>" (u1 u2) "Hu (Hy & Hg & Hh)". simpl. try (try brel_pures_l). try (try brel_pures_r).
    iApply (brel_call_nil Y Z (X' y1 y2 ∗ (X' ⊸ Y')%T h h') g g' u1 u2 [AppRCtx _] [AppRCtx _]
              with "Hg Hu [$Hy $Hh]").
    iIntros "!>" (w1 w2) "Hw [Hy Hh]". simpl. try (try brel_pures_l). try (try brel_pures_r).
    iApply (brel_call_nil X' Y' (Z w1 w2) h h' y1 y2 [AppRCtx _] [AppRCtx _]
              with "Hh Hy Hw").
    iIntros "!>" (v1 v2) "Hv Hw". simpl. try (try brel_pures_l). try (try brel_pures_r).
    iModIntro. iExists _, _, _, _. by iFrame.
  Qed.

  Lemma tens_interchange_rev_arr (g g' f f' h h' : val) (X Y Z X' Y' : sem_ty Σ) :
    ⊢ (Y ⊸ Z)%T g g' -∗ (X ⊸ Y)%T f f' -∗ (X' ⊸ Y')%T h h' -∗
      ((X × X') ⊸ (Z × Y'))%T (comp_op (tens_op g h) (tens_op f id_mod))
                               (tens_op (comp_op g' f') h').
  Proof.
    iIntros "Hg Hf Hh". rewrite {4}/sem_ty_arr. iIntros (a1 a2) "Ha".
    iDestruct "Ha" as (x1 x2 y1 y2) "(-> & -> & Hx & Hy)". rewrite /tens_op /comp_op /id_mod.
    try (try brel_pures_l). try (try brel_pures_r).
    iApply (brel_call_nil X Y (X' y1 y2 ∗ (Y ⊸ Z)%T g g' ∗ (X' ⊸ Y')%T h h') f f' x1 x2
              [AppRCtx _; AppRCtx _] [AppRCtx _; AppRCtx _] with "Hf Hx [$Hy $Hg $Hh]").
    iIntros "!>" (u1 u2) "Hu (Hy & Hg & Hh)". simpl. try (try brel_pures_l). try (try brel_pures_r).
    iApply (brel_call_nil Y Z (X' y1 y2 ∗ (X' ⊸ Y')%T h h') g g' u1 u2 [AppRCtx _] [AppRCtx _]
              with "Hg Hu [$Hy $Hh]").
    iIntros "!>" (w1 w2) "Hw [Hy Hh]". simpl. try (try brel_pures_l). try (try brel_pures_r).
    iApply (brel_call_nil X' Y' (Z w1 w2) h h' y1 y2 [AppRCtx _] [AppRCtx _]
              with "Hh Hy Hw").
    iIntros "!>" (v1 v2) "Hv Hw". simpl. try (try brel_pures_l). try (try brel_pures_r).
    iModIntro. iExists _, _, _, _. by iFrame.
  Qed.

  Lemma tens_interchange m (g g' f f' h h' : val) (X Y Z X' Y' : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ g ≤ g' : ModM m Y Z -∗ ⊨ᵥ f ≤ f' : ModM m X Y -∗ ⊨ᵥ h ≤ h' : ModM m X' Y' -∗
      ⊨ᵥ tens_op (comp_op g f) h ≤ comp_op (tens_op g' h') (tens_op f' id_mod)
        : ModM m (IProd X X') (IProd Z Y').
  Proof.
    rewrite /sem_val_typed /tc_opaque. iIntros "#Hg #Hf #Hh !>".
    iApply (ModM_map3 with "Hg Hf Hh"). intros θ. iApply tens_interchange_arr.
  Qed.

  Lemma tens_interchange_rev m (g g' f f' h h' : val) (X Y Z X' Y' : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ g ≤ g' : ModM m Y Z -∗ ⊨ᵥ f ≤ f' : ModM m X Y -∗ ⊨ᵥ h ≤ h' : ModM m X' Y' -∗
      ⊨ᵥ comp_op (tens_op g h) (tens_op f id_mod) ≤ tens_op (comp_op g' f') h'
        : ModM m (IProd X X') (IProd Z Y').
  Proof.
    rewrite /sem_val_typed /tc_opaque. iIntros "#Hg #Hf #Hh !>".
    iApply (ModM_map3 with "Hg Hf Hh"). intros θ. iApply tens_interchange_rev_arr.
  Qed.

  (* An environment extended by a module beside the one it is given is an
     environment. *)
  Lemma env_beside_typed m (A h : val) (X Y X' Y' : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ A ≤ A : (ModM m (IProd X X') (IProd Y Y') → 𝔹) -∗ ⊨ᵥ h ≤ h : ModM m X' Y' -∗
      ⊨ᵥ (λ: "v", A (tens_app "v" h))%V ≤ (λ: "v", A (tens_app "v" h))%V
        : (ModM m X Y → 𝔹).
  Proof.
    rewrite /sem_val_typed /tc_opaque. iIntros "#HA #Hh".
    rewrite /sem_ty_mbang /sem_ty_arr /=.
    iIntros "!> !>" (v1 v2) "Hv". rewrite /tens_app.
    brel_pures_l. brel_pures_r.
    iApply "HA". iApply (tens_op_sem with "Hv Hh").
  Qed.

End modules.

(* ------------------------------------------------------------------ *)
(* The composition theorem.                                            *)
(* ------------------------------------------------------------------ *)

Section uc_composition.
  Context `{!probblazeRGpreS Σ}.
  #[local] Open Scope mod_scope.

  (* Interfaces:
       XH : the real adversarial interface (of [Rw] and of the simulator [S])
       XF : the adversarial interface of [F]
       XG : the adversarial interface of [G]
       PF : the ports of [F] (and of [Rw]), used by the protocol [ρ]
       P  : the ports of [ρ] (and of [G])

     [Rw] realises [F] with the simulator [S]; [ρ] on [F] realises [G] with
     the simulator [S'].  Then [ρ] on [Rw] realises [G] with the simulator
     [S' ⊳ S].  Nothing is assumed about [Rw] beyond its advantage bound.

     The theorem holds in either mode [m]: for modules ([MS]) and for
     one-instance modules ([OS]), whose environments create one instance. *)
  Theorem uc_composition (m : mode) (Rw S F ρ S' G : val) (b : bool) (ε ε' : val → R)
      (XH XF XG PF P : ∀ `{probblazeRGS Σ}, sem_row Σ → sem_ty Σ) :
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ S ≤ S : ModM m XH XF) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ F ≤ F : ModM m XF PF) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ ρ ≤ ρ : ModM m PF P) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ S' ≤ S' : ModM m XF XG) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ G ≤ G : ModM m XG P) →
    (* [Rw] realises [F] with [S] *)
    (∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (ModM m XH PF → 𝔹)%T) →
       advantage A Rw (F ⊳ S) #b <= ε A) →
    (* [ρ] on [F] realises [G] with [S'] *)
    (∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (ModM m XF P → 𝔹)%T) →
       advantage A (ρ ⊳ F) (G ⊳ S') #b <= ε' A) →
    ∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (ModM m XH P → 𝔹)%T) →
      advantage A (ρ ⊳ Rw) (G ⊳ (S' ⊳ S)) #b
        <= ε (λ: "v", A (comp_app ρ "v"))%V + ε' (λ: "v", A (comp_app "v" S))%V.
  Proof.
    intros HS HF Hρ HS' HG H1 H2 A HA.
    set (β := λ H : probblazeRGS Σ, @ModM Σ H m (XH H) (P H)).
    (*   ρ ∘ Rw  ≤  ρ ∘ (F ∘ S)  ≃  (ρ ∘ F) ∘ S  ≤  (G ∘ S') ∘ S  ≃  G ∘ (S' ∘ S)   *)
    apply (advantage_triangle _ _ (ρ ⊳ (F ⊳ S)) _ _
             (ε (λ: "v", A (comp_app ρ "v"))%V)
             (ε' (λ: "v", A (comp_app "v" S))%V)); [| |lra].
    - (* through the protocol *)
      etrans; first apply (advantage_pure_l_rev _ [] (comp_app ρ Rw) _ _);
        [done|apply comp_app_pure|].
      etrans; first apply (advantage_pure_r_rev _ [] _ (comp_app ρ (F ⊳ S)) _);
        [done|apply comp_app_pure|].
      etrans; first apply (advantage_reduction_ctx A [AppRCtx (comp_app ρ)]).
      { done. }
      { intros vs w Hw. simpl. by rewrite Hw. }
      apply H1. intros HRGS. iApply env_under_typed; [iApply HA|iApply Hρ].
    - apply (advantage_triangle _ _ ((ρ ⊳ F) ⊳ S) _ _ 0
               (ε' (λ: "v", A (comp_app "v" S))%V)); [| |lra].
      { apply (advantage_zero _ _ _ _ β); [exact HA| |]; intros HRGS; iApply sem_typed_val.
        - iApply comp_op_assoc; [iApply Hρ|iApply HF|iApply HS].
        - iApply comp_op_assoc_rev; [iApply Hρ|iApply HF|iApply HS]. }
      apply (advantage_triangle _ _ ((G ⊳ S') ⊳ S) _ _
               (ε' (λ: "v", A (comp_app "v" S))%V) 0); [| |lra].
      + (* over the simulator *)
        etrans; first apply (advantage_pure_l_rev _ [] (comp_app (ρ ⊳ F) S) _ _);
          [done|apply comp_app_pure|].
        etrans; first apply (advantage_pure_r_rev _ [] _ (comp_app (G ⊳ S') S) _);
          [done|apply comp_app_pure|].
        etrans; first apply (advantage_reduction_ctx A [AppLCtx S; AppRCtx comp_app]).
        { done. }
        { intros vs w Hw. simpl. by rewrite Hw. }
        apply H2. intros HRGS. iApply env_over_typed; [iApply HA|iApply HS].
      + apply (advantage_zero _ _ _ _ β); [exact HA| |]; intros HRGS; iApply sem_typed_val.
        * iApply comp_op_assoc_rev; [iApply HG|iApply HS'|iApply HS].
        * iApply comp_op_assoc; [iApply HG|iApply HS'|iApply HS].
  Qed.

  (* A bound for every environment of modules is a bound for every
     environment of one-instance modules. *)
  Lemma advantage_Mod_ModA (e e' : expr) (b : bool) (ε : val → R)
      (X Y : ∀ `{probblazeRGS Σ}, sem_row Σ → sem_ty Σ) :
    (∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (Mod X Y → 𝔹)%T) →
       advantage A e e' #b <= ε A) →
    ∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (ModA X Y → 𝔹)%T) →
      advantage A e e' #b <= ε A.
  Proof.
    intros H A HA. apply H. intros HRGS. iApply env_ModA_Mod. iApply HA.
  Qed.

End uc_composition.
