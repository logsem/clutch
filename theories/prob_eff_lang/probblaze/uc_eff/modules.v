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
   tensor by the interchange law. *)

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

  (* The type of a module from interface [X] to interface [Y]. *)
  Definition Mod (X Y : sem_row Σ → sem_ty Σ) : sem_ty Σ := (∀ᵣ θ, X θ → Y θ)%T.

  Global Instance Sys_persistent X Y v1 v2 : Persistent (Mod X Y v1 v2).
  Proof. rewrite /Mod /sem_ty_row_forall /sem_ty_mbang /=. apply _. Qed.

  (* Composition: typing and congruence. *)
  Lemma comp_op_typed (g g' f f' : val) (X Y Z : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ g ≤ g' : Mod Y Z -∗ ⊨ᵥ f ≤ f' : Mod X Y -∗
      ⊨ᵥ comp_op g f ≤ comp_op g' f' : Mod X Z.
  Proof.
    rewrite /sem_val_typed /tc_opaque /Mod /sem_ty_row_forall /sem_ty_mbang /sem_ty_arr /=.
    iIntros "#Hg #Hf !> %θ !>" (a1 a2) "Ha". rewrite /comp_op.
    brel_pures_l. brel_pures_r.
    iApply (brel_bind' [AppRCtx _] [AppRCtx _]).
    { iApply traversable_to_iThy; intros; apply _. }
    iApply (brel_wand with "[Ha]"); first by iApply "Hf".
    iIntros "!>" (b1 b2) "Hb". simpl. by iApply "Hg".
  Qed.

  (* Associativity, with congruence, in both directions. *)
  Lemma comp_op_assoc (h h' g g' f f' : val) (X Y Z W : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ h ≤ h' : Mod Z W -∗ ⊨ᵥ g ≤ g' : Mod Y Z -∗ ⊨ᵥ f ≤ f' : Mod X Y -∗
      ⊨ᵥ comp_op h (comp_op g f) ≤ comp_op (comp_op h' g') f' : Mod X W.
  Proof.
    rewrite /sem_val_typed /tc_opaque /Mod /sem_ty_row_forall /sem_ty_mbang /sem_ty_arr /=.
    iIntros "#Hh #Hg #Hf !> %θ !>" (a1 a2) "Ha". rewrite /comp_op.
    brel_pures_l. brel_pures_r.
    iApply (brel_bind' [AppRCtx _; AppRCtx _] [AppRCtx _]).
    { iApply traversable_to_iThy; intros; apply _. }
    iApply (brel_wand with "[Ha]"); first by iApply "Hf".
    iIntros "!>" (b1 b2) "Hb". simpl. brel_pures_r.
    iApply (brel_bind' [AppRCtx _] [AppRCtx _]).
    { iApply traversable_to_iThy; intros; apply _. }
    iApply (brel_wand with "[Hb]"); first by iApply "Hg".
    iIntros "!>" (c1 c2) "Hc". simpl. by iApply "Hh".
  Qed.

  Lemma comp_op_assoc_rev (h h' g g' f f' : val) (X Y Z W : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ h ≤ h' : Mod Z W -∗ ⊨ᵥ g ≤ g' : Mod Y Z -∗ ⊨ᵥ f ≤ f' : Mod X Y -∗
      ⊨ᵥ comp_op (comp_op h g) f ≤ comp_op h' (comp_op g' f') : Mod X W.
  Proof.
    rewrite /sem_val_typed /tc_opaque /Mod /sem_ty_row_forall /sem_ty_mbang /sem_ty_arr /=.
    iIntros "#Hh #Hg #Hf !> %θ !>" (a1 a2) "Ha". rewrite /comp_op.
    brel_pures_l. brel_pures_r.
    iApply (brel_bind' [AppRCtx _] [AppRCtx _; AppRCtx _]).
    { iApply traversable_to_iThy; intros; apply _. }
    iApply (brel_wand with "[Ha]"); first by iApply "Hf".
    iIntros "!>" (b1 b2) "Hb". simpl. brel_pures_l.
    iApply (brel_bind' [AppRCtx _] [AppRCtx _]).
    { iApply traversable_to_iThy; intros; apply _. }
    iApply (brel_wand with "[Hb]"); first by iApply "Hg".
    iIntros "!>" (c1 c2) "Hc". simpl. by iApply "Hh".
  Qed.

  (* An environment extended by a protocol, or by a simulator, is an
     environment. *)
  Lemma env_under_typed (A g : val) (X Y Z : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ A ≤ A : (Mod X Z → 𝔹) -∗ ⊨ᵥ g ≤ g : Mod Y Z -∗
      ⊨ᵥ (λ: "v", A (comp_app g "v"))%V ≤ (λ: "v", A (comp_app g "v"))%V
        : (Mod X Y → 𝔹).
  Proof.
    iIntros "#HA #Hg".
    rewrite /sem_val_typed /tc_opaque /sem_ty_mbang /sem_ty_arr /=.
    iIntros "!> !>" (v1 v2) "#Hv". rewrite /comp_app.
    brel_pures_l. brel_pures_r.
    iAssert (⊨ᵥ v1 ≤ v2 : Mod X Y)%I as "Hv'"; first (rewrite /sem_val_typed /tc_opaque; by iModIntro).
    iPoseProof (comp_op_typed g g v1 v2 with "Hg Hv'") as "Hc".
    rewrite /sem_val_typed /tc_opaque. iApply "HA". iApply "Hc".
  Qed.

  Lemma env_over_typed (A f : val) (X Y Z : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ A ≤ A : (Mod X Z → 𝔹) -∗ ⊨ᵥ f ≤ f : Mod X Y -∗
      ⊨ᵥ (λ: "v", A (comp_app "v" f))%V ≤ (λ: "v", A (comp_app "v" f))%V
        : (Mod Y Z → 𝔹).
  Proof.
    iIntros "#HA #Hf".
    rewrite /sem_val_typed /tc_opaque /sem_ty_mbang /sem_ty_arr /=.
    iIntros "!> !>" (v1 v2) "#Hv". rewrite /comp_app.
    brel_pures_l. brel_pures_r.
    iAssert (⊨ᵥ v1 ≤ v2 : Mod Y Z)%I as "Hv'"; first (rewrite /sem_val_typed /tc_opaque; by iModIntro).
    iPoseProof (comp_op_typed v1 v2 f f with "Hv' Hf") as "Hc".
    rewrite /sem_val_typed /tc_opaque. iApply "HA". iApply "Hc".
  Qed.


  (* ---------------------------------------------------------------- *)
  (* Tensor: typing, identity, interchange.                             *)
  (* ---------------------------------------------------------------- *)

  (* The product of two interfaces. *)
  Definition IProd (X Y : sem_row Σ → sem_ty Σ) : sem_row Σ → sem_ty Σ :=
    λ θ, (X θ × Y θ)%T.

  (* A module body runs without effects, so the interfaces it holds, which
     may be affine, are kept across the calls it makes. *)
  Lemma tens_op_typed (f f' g g' : val) (X Y X' Y' : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ f ≤ f' : Mod X Y -∗ ⊨ᵥ g ≤ g' : Mod X' Y' -∗
      ⊨ᵥ tens_op f g ≤ tens_op f' g' : Mod (IProd X X') (IProd Y Y').
  Proof.
    rewrite /sem_val_typed /tc_opaque /Mod /sem_ty_row_forall.
    iIntros "#Hf #Hg !> %θ". rewrite {3}/sem_ty_mbang {3}/sem_ty_arr /=.
    iIntros "!>" (a1 a2) "Ha". rewrite /IProd /sem_ty_prod.
    iDestruct "Ha" as (x1 x2 y1 y2) "(-> & -> & Hx & Hy)". rewrite /tens_op.
    try (try brel_pures_l). try (try brel_pures_r).
    iApply (brel_call_frame ⟨⟩%R ⟨⟩%R (X θ) (Y θ) (X' θ y1 y2) f f' x1 x2 [AppRCtx _] [AppRCtx _]
              with "[] [] Hx Hy").
    { iApply row_le_mfbang_elim_nil. }
    { iApply "Hf". }
    iIntros "!>" (u1 u2) "Hu Hy". simpl. try (try brel_pures_l). try (try brel_pures_r).
    iApply (brel_call_frame ⟨⟩%R ⟨⟩%R (X' θ) (Y' θ) (Y θ u1 u2) g g' y1 y2 [AppRCtx _] [AppRCtx _]
              with "[] [] Hy Hu").
    { iApply row_le_mfbang_elim_nil. }
    { iApply "Hg". }
    iIntros "!>" (v1 v2) "Hv Hu". simpl. try (try brel_pures_l). try (try brel_pures_r).
    iModIntro. iExists _, _, _, _. by iFrame.
  Qed.

  Lemma id_mod_typed (X : sem_row Σ → sem_ty Σ) : ⊢ ⊨ᵥ id_mod ≤ id_mod : Mod X X.
  Proof.
    rewrite /sem_val_typed /tc_opaque /Mod /sem_ty_row_forall /sem_ty_mbang /sem_ty_arr /=.
    iIntros "!> %θ !>" (a1 a2) "Ha". rewrite /id_mod. try (try brel_pures_l). try (try brel_pures_r).
    by iModIntro.
  Qed.

  (* Interchange, with congruence, in both directions: a module beside [h]
     composed below is composed below beside the identity. *)
  Lemma tens_interchange (g g' f f' h h' : val) (X Y Z X' Y' : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ g ≤ g' : Mod Y Z -∗ ⊨ᵥ f ≤ f' : Mod X Y -∗ ⊨ᵥ h ≤ h' : Mod X' Y' -∗
      ⊨ᵥ tens_op (comp_op g f) h ≤ comp_op (tens_op g' h') (tens_op f' id_mod)
        : Mod (IProd X X') (IProd Z Y').
  Proof.
    rewrite /sem_val_typed /tc_opaque /Mod /sem_ty_row_forall.
    iIntros "#Hg #Hf #Hh !> %θ". rewrite {4}/sem_ty_mbang {4}/sem_ty_arr /=.
    iIntros "!>" (a1 a2) "Ha". rewrite /IProd /sem_ty_prod.
    iDestruct "Ha" as (x1 x2 y1 y2) "(-> & -> & Hx & Hy)". rewrite /tens_op /comp_op /id_mod.
    try (try brel_pures_l). try (try brel_pures_r).
    iApply (brel_call_frame ⟨⟩%R ⟨⟩%R (X θ) (Y θ) (X' θ y1 y2) f f' x1 x2
              [AppRCtx _; AppRCtx _] [AppRCtx _; AppRCtx _] with "[] [] Hx Hy").
    { iApply row_le_mfbang_elim_nil. }
    { iApply "Hf". }
    iIntros "!>" (u1 u2) "Hu Hy". simpl. try (try brel_pures_l). try (try brel_pures_r).
    iApply (brel_call_frame ⟨⟩%R ⟨⟩%R (Y θ) (Z θ) (X' θ y1 y2) g g' u1 u2 [AppRCtx _] [AppRCtx _]
              with "[] [] Hu Hy").
    { iApply row_le_mfbang_elim_nil. }
    { iApply "Hg". }
    iIntros "!>" (w1 w2) "Hw Hy". simpl. try (try brel_pures_l). try (try brel_pures_r).
    iApply (brel_call_frame ⟨⟩%R ⟨⟩%R (X' θ) (Y' θ) (Z θ w1 w2) h h' y1 y2 [AppRCtx _] [AppRCtx _]
              with "[] [] Hy Hw").
    { iApply row_le_mfbang_elim_nil. }
    { iApply "Hh". }
    iIntros "!>" (v1 v2) "Hv Hw". simpl. try (try brel_pures_l). try (try brel_pures_r).
    iModIntro. iExists _, _, _, _. by iFrame.
  Qed.

  Lemma tens_interchange_rev (g g' f f' h h' : val) (X Y Z X' Y' : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ g ≤ g' : Mod Y Z -∗ ⊨ᵥ f ≤ f' : Mod X Y -∗ ⊨ᵥ h ≤ h' : Mod X' Y' -∗
      ⊨ᵥ comp_op (tens_op g h) (tens_op f id_mod) ≤ tens_op (comp_op g' f') h'
        : Mod (IProd X X') (IProd Z Y').
  Proof.
    rewrite /sem_val_typed /tc_opaque /Mod /sem_ty_row_forall.
    iIntros "#Hg #Hf #Hh !> %θ". rewrite {4}/sem_ty_mbang {4}/sem_ty_arr /=.
    iIntros "!>" (a1 a2) "Ha". rewrite /IProd /sem_ty_prod.
    iDestruct "Ha" as (x1 x2 y1 y2) "(-> & -> & Hx & Hy)". rewrite /tens_op /comp_op /id_mod.
    try (try brel_pures_l). try (try brel_pures_r).
    iApply (brel_call_frame ⟨⟩%R ⟨⟩%R (X θ) (Y θ) (X' θ y1 y2) f f' x1 x2
              [AppRCtx _; AppRCtx _] [AppRCtx _; AppRCtx _] with "[] [] Hx Hy").
    { iApply row_le_mfbang_elim_nil. }
    { iApply "Hf". }
    iIntros "!>" (u1 u2) "Hu Hy". simpl. try (try brel_pures_l). try (try brel_pures_r).
    iApply (brel_call_frame ⟨⟩%R ⟨⟩%R (Y θ) (Z θ) (X' θ y1 y2) g g' u1 u2 [AppRCtx _] [AppRCtx _]
              with "[] [] Hu Hy").
    { iApply row_le_mfbang_elim_nil. }
    { iApply "Hg". }
    iIntros "!>" (w1 w2) "Hw Hy". simpl. try (try brel_pures_l). try (try brel_pures_r).
    iApply (brel_call_frame ⟨⟩%R ⟨⟩%R (X' θ) (Y' θ) (Z θ w1 w2) h h' y1 y2 [AppRCtx _] [AppRCtx _]
              with "[] [] Hy Hw").
    { iApply row_le_mfbang_elim_nil. }
    { iApply "Hh". }
    iIntros "!>" (v1 v2) "Hv Hw". simpl. try (try brel_pures_l). try (try brel_pures_r).
    iModIntro. iExists _, _, _, _. by iFrame.
  Qed.

  (* An environment extended by a module beside the one it is given is an
     environment. *)
  Lemma env_beside_typed (A h : val) (X Y X' Y' : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ A ≤ A : (Mod (IProd X X') (IProd Y Y') → 𝔹) -∗ ⊨ᵥ h ≤ h : Mod X' Y' -∗
      ⊨ᵥ (λ: "v", A (tens_app "v" h))%V ≤ (λ: "v", A (tens_app "v" h))%V
        : (Mod X Y → 𝔹).
  Proof.
    iIntros "#HA #Hh".
    rewrite /sem_val_typed /tc_opaque /sem_ty_mbang /sem_ty_arr /=.
    iIntros "!> !>" (v1 v2) "#Hv". rewrite /tens_app.
    brel_pures_l. brel_pures_r.
    iAssert (⊨ᵥ v1 ≤ v2 : Mod X Y)%I as "Hv'"; first (rewrite /sem_val_typed /tc_opaque; by iModIntro).
    iPoseProof (tens_op_typed v1 v2 h h with "Hv' Hh") as "Hc".
    rewrite /sem_val_typed /tc_opaque. iApply "HA". iApply "Hc".
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
     [S' ⊳ S].  Nothing is assumed about [Rw] beyond its advantage bound. *)
  Theorem uc_composition (Rw S F ρ S' G : val) (b : bool) (ε ε' : val → R)
      (XH XF XG PF P : ∀ `{probblazeRGS Σ}, sem_row Σ → sem_ty Σ) :
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ S ≤ S : Mod XH XF) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ F ≤ F : Mod XF PF) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ ρ ≤ ρ : Mod PF P) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ S' ≤ S' : Mod XF XG) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ G ≤ G : Mod XG P) →
    (* [Rw] realises [F] with [S] *)
    (∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (Mod XH PF → 𝔹)%T) →
       advantage A Rw (F ⊳ S) #b <= ε A) →
    (* [ρ] on [F] realises [G] with [S'] *)
    (∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (Mod XF P → 𝔹)%T) →
       advantage A (ρ ⊳ F) (G ⊳ S') #b <= ε' A) →
    ∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (Mod XH P → 𝔹)%T) →
      advantage A (ρ ⊳ Rw) (G ⊳ (S' ⊳ S)) #b
        <= ε (λ: "v", A (comp_app ρ "v"))%V + ε' (λ: "v", A (comp_app "v" S))%V.
  Proof.
    intros HS HF Hρ HS' HG H1 H2 A HA.
    set (β := λ H : probblazeRGS Σ, @Mod Σ H (XH H) (P H)).
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

End uc_composition.
