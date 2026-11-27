(* Two-way interfaces and linking (uc_eff/DESIGN.md, section 11).

   [modules.v] links modules in one direction: a module takes the
   operations of the boundary below it and offers the operations of the
   boundary above, and [g ⊳ f] is functor application.  Here a boundary
   carries operations in both directions:

     X.up    offered by the component below to the one above
             (ports; the adversary's operations offered to a module)
     X.down  offered by the component above to the one below
             (ports the adversary may call; callbacks)

   In an OCaml-like notation, a module from boundary [X] (below) to
   boundary [Y] (above) is a functor whose argument for the module above
   is lazy (it is looked up when used):

     module M (Below : X.up) (Above : unit -> Y.down) : sig
       val down : X.down           (* what it offers below: available at once *)
       val init : unit -> Y.up     (* the rest of its set-up; what it offers above *)
     end

   and linking [g ∘ f] (f below, g above) is a recursive module group

     module rec F = f (X_up) (fun () -> G.down)
            and G = g (F.init ()) (Z_down)

   implemented the way OCaml implements [module rec]: [F] receives a
   placeholder for [G.down], a reference, which is filled as soon as
   [G.down] exists.  Looking it up before that diverges (OCaml raises
   [Undefined_recursive_module]).

   The split of a module into [down] and [init] makes nested links behave
   like one flat [module rec] group: the placeholder for a module's
   [down] is filled right after the module's first stage, whatever the
   nesting, so [(h ∘ g) ∘ f] and [h ∘ (g ∘ f)] run the same steps in the
   same order.  Without it, the time at which a placeholder is filled
   depends on the nesting, and associativity fails for set-ups that call
   through a link.

   In this file, for either mode (modules [MS], one-instance modules [OS]):
   - [ModL m X Y], the type of a two-way module;
   - [link], with its typing ([link_eq], [link_typed]);
   - associativity ([link_assoc]);
   - environments extended by a module above or below ([env_under_link],
     [env_over_link]);
   - the composition theorem ([uc_composition_link]);
   - one-way modules as two-way modules ([embed], [link_embed]), and the
     bridge from one-way security statements ([advantage_embed],
     [realises_embed]). *)

From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From iris.bi Require Import monpred.
From iris.proofmode Require Import monpred.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory semantics logic adequacy mode.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_compat.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage uc_advantage.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules eq_modules.
From Stdlib Require Import Reals Psatz.

#[local] Set Default Proof Using "All".

(* ------------------------------------------------------------------ *)
(* The code.                                                           *)
(* ------------------------------------------------------------------ *)

(* Looking up a placeholder. *)
Definition getter : val :=
  λ: "r" <>, match: !"r" with NONE => loop #()%V | SOME "y" => "y" end.

(* [link g f]: [f] below, [g] above.

     let link g f (x_up, z_down) =
       let r = ref None in
       let (x_down, f_init) = f (x_up, fun () -> get r) in
       (x_down, fun () ->
          let y_up = f_init () in
          let (y_down, g_init) = g (y_up, z_down) in
          r := Some y_down;
          g_init ())                                                     *)
Definition link (g f : val) : val :=
  λ: "a",
    let: "r" := ref NONE in
    let: "fr" := f (Fst "a", getter "r") in
    (Fst "fr",
     λ: <>,
       let: "yu" := (Snd "fr") #()%V in
       let: "gr" := g ("yu", Snd "a") in
       "r" <- SOME (Fst "gr");;
       (Snd "gr") #()%V).

(* The same as a program, for contexts with a hole; it evaluates to
   [link] ([link_app_pure]). *)
Definition link_app : val :=
  λ: "g" "f" "a",
    let: "r" := ref NONE in
    let: "fr" := "f" (Fst "a", getter "r") in
    (Fst "fr",
     λ: <>,
       let: "yu" := (Snd "fr") #()%V in
       let: "gr" := "g" ("yu", Snd "a") in
       "r" <- SOME (Fst "gr");;
       (Snd "gr") #()%V).

Lemma link_app_pure (g f : val) : rtc pure_step (link_app g f) (link g f).
Proof.
  rewrite /link_app /link.
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


(* A one-way module as a two-way module that offers nothing below and
   looks nothing up above; its set-up is all in the second stage.

     let embed f (x_up, _) = ((), fun () -> f x_up)                     *)
Definition embed (f : val) : val := λ: "a", (#()%V, λ: <>, f (Fst "a")).

Definition embed_app : val := λ: "f" "a", (#()%V, λ: <>, "f" (Fst "a")).

Lemma embed_app_pure (f : val) : rtc pure_step (embed_app f) (embed f).
Proof.
  rewrite /embed_app /embed.
  eapply rtc_l.
  { apply nsteps_once_inv, (pure_exec (φ := True)); done. }
  simpl. eapply rtc_l.
  { apply nsteps_once_inv, (pure_exec (φ := True)); done. }
  done.
Qed.

Section links.
  Context `{!probblazeRGS Σ}.
  #[local] Open Scope bi_scope.

  (* ---------------------------------------------------------------- *)
  (* Types.                                                             *)
  (* ---------------------------------------------------------------- *)

  (* A two-way module from boundary [(Xu, Xd)] below to [(Yu, Yd)] above:
     it takes what the boundary below offers it, [Xu], and a way to look
     up what the boundary above offers it, [𝟙 → Yd]; it returns what it
     offers below, [Xd], and its set-up, which returns what it offers
     above, [Yu]. *)
  Definition ModL (m : mode) (Xu Xd Yu Yd : sem_row Σ → sem_ty Σ) : sem_ty Σ :=
    ModM m (λ θ, (Xu θ × (𝟙 → Yd θ))%T) (λ θ, (Xd θ × (𝟙 ⊸ Yu θ))%T).

  Global Instance ModL_MS_persistent Xu Xd Yu Yd v1 v2 :
    Persistent (ModL MS Xu Xd Yu Yd v1 v2).
  Proof. rewrite /ModL. apply _. Qed.

  Global Instance eq_lift_persistent (τ : sem_ty Σ) vl vr :
    (∀ v1 v2, Persistent (τ v1 v2)) → Persistent (⟪ τ ⟫ vl vr).
  Proof.
    intros Hτ. apply monPred_persistent=> d. rewrite eq_lift_at. apply Hτ.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Rules.                                                             *)
  (* ---------------------------------------------------------------- *)

  (* Calling a function of the empty row, keeping a frame [P]. *)
  Lemma eq_call_nil (A B : sem_ty Σ) (P : iPropD Σ) (fl fr wl wr : val) Kl Kr R :
    (∀ l1s, NeutralEctx l1s Kl) → (∀ l2s, NeutralEctx l2s Kr) →
    ⊢ ⟪ A ⊸ B ⟫ fl fr -∗ ⟪ A ⟫ wl wr -∗ P -∗
      □ (∀ vl vr, ⟪ B ⟫ vl vr -∗ P -∗
           EQ fill Kl (Val vl) ≈ fill Kr (Val vr) <|iLblSig_to_iLblThy ⟨⟩%R|> {{ R }}) -∗
      EQ fill Kl (fl wl) ≈ fill Kr (fr wr) <|iLblSig_to_iLblThy ⟨⟩%R|> {{ R }}.
  Proof.
    intros ??. iStartProof (iProp _). iIntros (d) "Hf Hw HP #Hc".
    iEval (rewrite eq_lift_at) in "Hf". iEval (rewrite eq_lift_at) in "Hw".
    destruct d; rewrite eq_rel_at /pick /=.
    - iApply (brel_call_nil A B (P Fwd) with "Hf Hw HP").
      iIntros "!>" (v1 v2) "HB HP". iApply (eq_rel_at_elim_const Fwd).
      iApply ("Hc" $! v1 v2 with "[HB] HP"). by rewrite eq_lift_at.
    - iApply (brel_call_nil A B (P Bwd) with "Hf Hw HP").
      iIntros "!>" (v1 v2) "HB HP". iApply (eq_rel_at_elim_const Bwd).
      iApply ("Hc" $! v2 v1 with "[HB] HP"). by rewrite eq_lift_at.
  Qed.

  (* A persistent function of the empty row is an affine one. *)
  Lemma eq_lift_arr_ms_aff (A B : sem_ty Σ) fl fr : ⟪ A → B ⟫ fl fr ⊢ ⟪ A ⊸ B ⟫ fl fr.
  Proof. rewrite eq_lift_mbang /=. iIntros "#H". done. Qed.

  (* Typings and self-equivalences of values. *)
  Lemma val_typed_eq (v : val) (τ : sem_ty Σ) : (⊢ ⊨ᵥ v ≤ v : τ) → ⊢ ⟪ τ ⟫ v v.
  Proof.
    rewrite /sem_val_typed /tc_opaque. intros H. split=> d.
    rewrite monPred_at_emp eq_lift_at. iIntros "_". iDestruct H as "#H".
    destruct d; done.
  Qed.

  (* A closed proof gives a typing in each direction (a closed proof is
     persistent, whatever [τ]). *)
  Lemma eq_typed_l (vl vr : val) (τ : sem_ty Σ) : (⊢ ⟪ τ ⟫ vl vr) → ⊢ ⊨ᵥ vl ≤ vr : τ.
  Proof.
    intros [H]. specialize (H Fwd). rewrite monPred_at_emp eq_lift_at /pick /= in H.
    rewrite /sem_val_typed /tc_opaque. iModIntro. by iApply H.
  Qed.

  Lemma eq_typed_r (vl vr : val) (τ : sem_ty Σ) : (⊢ ⟪ τ ⟫ vl vr) → ⊢ ⊨ᵥ vr ≤ vl : τ.
  Proof.
    intros [H]. specialize (H Bwd). rewrite monPred_at_emp eq_lift_at /pick /= in H.
    rewrite /sem_val_typed /tc_opaque. iModIntro. by iApply H.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Lifting statements about one row to modules of any mode.           *)
  (* ---------------------------------------------------------------- *)

  (* What a two-way module is at one row. *)
  Definition LArr (Xu Xd Yu Yd : sem_row Σ → sem_ty Σ) (θ : sem_row Σ) : sem_ty Σ :=
    ((Xu θ × (𝟙 → Yd θ)) ⊸ (Xd θ × (𝟙 ⊸ Yu θ)))%T.

  Lemma ModL_unfold m Xu Xd Yu Yd : ModL m Xu Xd Yu Yd = (∀ᵣ θ, ![m] (LArr Xu Xd Yu Yd θ))%T.
  Proof. done. Qed.

  (* [iModIntro] does not introduce [□?m] for an abstract mode [m]; the
     lifting lemmas split on [m] once. *)
  Lemma eq_mod_map2 m (A1 A2 A : sem_row Σ → sem_ty Σ) v1 v1' v2 v2' w w' :
    (∀ θ, ⊢ ⟪ A1 θ ⟫ v1 v1' -∗ ⟪ A2 θ ⟫ v2 v2' -∗ ⟪ A θ ⟫ w w') →
    ⊢ ⟪ ∀ᵣ θ, ![m] (A1 θ) ⟫ v1 v1' -∗ ⟪ ∀ᵣ θ, ![m] (A2 θ) ⟫ v2 v2' -∗
      ⟪ ∀ᵣ θ, ![m] (A θ) ⟫ w w'.
  Proof.
    intros H. rewrite !eq_lift_forall. iIntros "H1 H2" (θ).
    iSpecialize ("H1" $! θ). iSpecialize ("H2" $! θ). rewrite !eq_lift_mbang.
    destruct m; simpl.
    - iApply (H with "H1 H2").
    - iDestruct "H1" as "#H1". iDestruct "H2" as "#H2". iModIntro.
      iApply (H with "H1 H2").
  Qed.

  Lemma eq_mod_map3 m (A1 A2 A3 A : sem_row Σ → sem_ty Σ) v1 v1' v2 v2' v3 v3' w w' :
    (∀ θ, ⊢ ⟪ A1 θ ⟫ v1 v1' -∗ ⟪ A2 θ ⟫ v2 v2' -∗ ⟪ A3 θ ⟫ v3 v3' -∗ ⟪ A θ ⟫ w w') →
    ⊢ ⟪ ∀ᵣ θ, ![m] (A1 θ) ⟫ v1 v1' -∗ ⟪ ∀ᵣ θ, ![m] (A2 θ) ⟫ v2 v2' -∗
      ⟪ ∀ᵣ θ, ![m] (A3 θ) ⟫ v3 v3' -∗ ⟪ ∀ᵣ θ, ![m] (A θ) ⟫ w w'.
  Proof.
    intros H. rewrite !eq_lift_forall. iIntros "H1 H2 H3" (θ).
    iSpecialize ("H1" $! θ). iSpecialize ("H2" $! θ). iSpecialize ("H3" $! θ).
    rewrite !eq_lift_mbang. destruct m; simpl.
    - iApply (H with "H1 H2 H3").
    - iDestruct "H1" as "#H1". iDestruct "H2" as "#H2". iDestruct "H3" as "#H3".
      iModIntro. iApply (H with "H1 H2 H3").
  Qed.

  (* ---------------------------------------------------------------- *)
  (* The placeholder of a link.                                         *)
  (* ---------------------------------------------------------------- *)

  Definition NL : namespace := nroot .@ "link".

  (* Empty on both sides, or filled on both sides with related values.
     The interface [D] offered across the link must be persistent: it is
     looked up any number of times. *)
  Definition link_inv (D : sem_ty Σ) (r r' : loc) : iPropD Σ :=
    (r ↦ₗ NONEV ∗ r' ↦ᵣ NONEV) ∨ (∃ y y', r ↦ₗ SOMEV y ∗ r' ↦ᵣ SOMEV y' ∗ □ ⟪ D ⟫ y y').

  Lemma getter_eq (D : sem_ty Σ) (r r' : loc) :
    eq_na_inv NL (link_inv D r r') ⊢
    ⟪ 𝟙 → D ⟫ (λ: <>, match: !#r with NONE => loop #()%V | SOME "y" => "y" end)%V
              (λ: <>, match: !#r' with NONE => loop #()%V | SOME "y" => "y" end)%V.
  Proof.
    iIntros "#Hinv". rewrite eq_lift_mbang /=. iModIntro.
    iApply eq_lift_arr. iIntros (ul ur) "Hu".
    iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
    eq_pures_l. eq_pures_r.
    iApply (eq_na_open _ _ NL); first done. iFrame "Hinv". iIntros "[H Hclose]".
    iDestruct "H" as "[[>Hr >Hr']|(%y & %y' & >Hr & >Hr' & #Hy)]"; eq_load_l; eq_load_r;
      iApply eq_na_close_rule; iFrame "Hclose".
    - iSplitL "Hr Hr'"; first (iNext; iLeft; iFrame). eq_pures_l. eq_pures_r.
      iApply eq_loop.
    - iSplitL "Hr Hr'"; first (iNext; iRight; iExists _, _; iFrame "#"; iFrame).
      eq_pures_lr. try (try eq_pures_l). try (try eq_pures_r). iApply eq_value. by iModIntro.
  Qed.

  (* Filling a placeholder. *)
  Lemma link_fill (D : sem_ty Σ) (r r' : loc) (y y' : val) Kl Kr X R :
    eq_na_inv NL (link_inv D r r') ∗ □ ⟪ D ⟫ y y' ∗
    EQ fill Kl #()%V ≈ fill Kr #()%V <|X|> {{ R }}
    ⊢ EQ fill Kl (#r <- SOMEV y) ≈ fill Kr (#r' <- SOMEV y') <|X|> {{ R }}.
  Proof.
    iIntros "(#Hinv & #Hy & H)".
    iApply (eq_na_open _ _ NL); first done. iFrame "Hinv". iIntros "[H' Hclose]".
    iAssert (▷ ∃ v v', r ↦ₗ v ∗ r' ↦ᵣ v')%I with "[H']" as (v v') "[>Hr >Hr']".
    { iNext. iDestruct "H'" as "[[??]|(% & % & ? & ? & _)]"; iExists _, _; iFrame. }
    eq_store_l. eq_store_r.
    iApply eq_na_close_rule. iFrame "Hclose".
    iSplitL "Hr Hr'"; first (iNext; iRight; iExists _, _; iFrame "#"; iFrame).
    done.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Typing of a link.                                                  *)
  (* ---------------------------------------------------------------- *)

  (* At one row.  The modules are affine (mode [OS]): the one above is
     carried in the frame of the calls before it. *)
  Lemma link_arr_eq θ (g g' f f' : val) (Xu Xd Yu Yd Zu Zd : sem_row Σ → sem_ty Σ) :
    (∀ θ v1 v2, Persistent (Yd θ v1 v2)) →
    ⊢ ⟪ LArr Yu Yd Zu Zd θ ⟫ g g' -∗ ⟪ LArr Xu Xd Yu Yd θ ⟫ f f' -∗
      ⟪ LArr Xu Xd Zu Zd θ ⟫ (link g f) (link g' f').
  Proof.
    iIntros (HYd) "Hg Hf". rewrite {3}/LArr.
    iApply eq_lift_arr. iIntros (al ar) "Ha".
    iEval (rewrite eq_lift_prod) in "Ha".
    iDestruct "Ha" as (xul xur zdl zdr) "(-> & -> & Hxu & #Hzd)".
    rewrite /link /getter. eq_pures_l. eq_alloc_l r as "Hr". eq_pures_l.
    eq_pures_r. eq_alloc_r r' as "Hr'". eq_pures_r.
    iApply (eq_na_alloc (link_inv (Yd θ) r r') NL).
    iSplitL "Hr Hr'"; first (iNext; iLeft; iFrame). iIntros "#Hinv".
    iDestruct (getter_eq with "Hinv") as "#Hget".
    (* The module below. *)
    eq_reshape_l (f _). eq_reshape_r (f' _).
    iApply (eq_call_nil (Xu θ × (𝟙 → Yd θ)) (Xd θ × (𝟙 ⊸ Yu θ)) (⟪ LArr Yu Yd Zu Zd θ ⟫ g g')
              with "Hf [Hxu] Hg"); try (intros; apply _).
    { iEval (rewrite eq_lift_prod). iExists _, _, _, _. by iFrame "#∗". }
    iIntros "!>" (frl frr) "Hfr Hg". simpl.
    iEval (rewrite eq_lift_prod) in "Hfr".
    iDestruct "Hfr" as (xdl xdr kfl kfr) "(-> & -> & Hxd & Hkf)".
    eq_pures_l. eq_pures_r.
    iApply eq_value. iModIntro. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iFrame "Hxd".
    (* The set-up of the link. *)
    iApply eq_lift_arr. iIntros (ul ur) "Hu".
    iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
    eq_pures_l. eq_pures_r.
    eq_reshape_l (kfl _). eq_reshape_r (kfr _).
    iApply (eq_call_nil 𝟙 (Yu θ) (⟪ LArr Yu Yd Zu Zd θ ⟫ g g') with "Hkf [] Hg");
      try (intros; apply _).
    { by iEval (rewrite eq_lift_unit). }
    iIntros "!>" (yul yur) "Hyu Hg". simpl. eq_pures_l. eq_pures_r.
    (* The module above. *)
    eq_reshape_l (g _). eq_reshape_r (g' _).
    iApply (eq_call_nil (Yu θ × (𝟙 → Zd θ)) (Yd θ × (𝟙 ⊸ Zu θ)) emp%I
              with "Hg [Hyu] []"); try (intros; apply _).
    { iEval (rewrite eq_lift_prod). iExists _, _, _, _. by iFrame "#∗". }
    { done. }
    iIntros "!>" (grl grr) "Hgr _". simpl.
    iEval (rewrite eq_lift_prod) in "Hgr".
    iDestruct "Hgr" as (ydl ydr kgl kgr) "(-> & -> & #Hyd & Hkg)".
    eq_pures_l. eq_pures_r.
    (* Fill the placeholder. *)
    eq_reshape_l (#r <- _)%E. eq_reshape_r (#r' <- _)%E.
    iApply link_fill. iFrame "Hinv Hyd". eq_pures_l. eq_pures_r.
    (* The set-up of the module above. *)
    eq_reshape_l (kgl _). eq_reshape_r (kgr _).
    iApply (eq_call_nil 𝟙 (Zu θ) emp%I with "Hkg [] []"); try (intros; apply _).
    { by iEval (rewrite eq_lift_unit). }
    { done. }
    iIntros "!>" (zul zur) "Hzu _". simpl. iApply eq_value. by iModIntro.
  Qed.

  Lemma link_eq m (g g' f f' : val) (Xu Xd Yu Yd Zu Zd : sem_row Σ → sem_ty Σ) :
    (∀ θ v1 v2, Persistent (Yd θ v1 v2)) →
    ⊢ ⟪ ModL m Yu Yd Zu Zd ⟫ g g' -∗ ⟪ ModL m Xu Xd Yu Yd ⟫ f f' -∗
      ⟪ ModL m Xu Xd Zu Zd ⟫ (link g f) (link g' f').
  Proof.
    intros HYd. rewrite !ModL_unfold. apply eq_mod_map2=> θ. by apply link_arr_eq.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Associativity.                                                     *)
  (* ---------------------------------------------------------------- *)

  (* [h ∘ (g ∘ f)] and [(h ∘ g) ∘ f] run the same calls in the same order:
       f, f's set-up, g, fill Y, g's set-up, h, fill Z, h's set-up.
     They differ only in when the placeholder for [Z] is allocated: at the
     start on the left, just before [g] on the right, a step of one side
     alone.  At one row, with [g] and [h] carried in the frames. *)
  Lemma link_assoc_arr θ (h h' g g' f f' : val)
      (Xu Xd Yu Yd Zu Zd Wu Wd : sem_row Σ → sem_ty Σ) :
    (∀ θ v1 v2, Persistent (Yd θ v1 v2)) → (∀ θ v1 v2, Persistent (Zd θ v1 v2)) →
    ⊢ ⟪ LArr Zu Zd Wu Wd θ ⟫ h h' -∗ ⟪ LArr Yu Yd Zu Zd θ ⟫ g g' -∗
      ⟪ LArr Xu Xd Yu Yd θ ⟫ f f' -∗
      ⟪ LArr Xu Xd Wu Wd θ ⟫ (link h (link g f)) (link (link h' g') f').
  Proof.
    iIntros (HY HZ) "Hh Hg Hf". rewrite {4}/LArr.
    iApply eq_lift_arr. iIntros (al ar) "Ha".
    iEval (rewrite eq_lift_prod) in "Ha".
    iDestruct "Ha" as (xul xur wdl wdr) "(-> & -> & Hxu & #Hwd)".
    rewrite /link /getter.
    (* Left: the placeholders for [Z] and [Y]. *)
    eq_pures_l. eq_alloc_l rZ as "HrZ". eq_pures_l.
    eq_alloc_l rY as "HrY". eq_pures_l.
    (* Right: the placeholder for [Y]. *)
    eq_pures_r. eq_alloc_r rY' as "HrY'". eq_pures_r.
    iApply (eq_na_alloc (link_inv (Yd θ) rY rY') NL).
    iSplitL "HrY HrY'"; first (iNext; iLeft; iFrame). iIntros "#HinvY".
    iDestruct (getter_eq with "HinvY") as "#HgetY".
    (* f *)
    eq_reshape_l (f _). eq_reshape_r (f' _).
    iApply (eq_call_nil (Xu θ × (𝟙 → Yd θ)) (Xd θ × (𝟙 ⊸ Yu θ))
              (rZ ↦ₗ NONEV ∗ ⟪ LArr Yu Yd Zu Zd θ ⟫ g g' ∗ ⟪ LArr Zu Zd Wu Wd θ ⟫ h h')%I
              with "Hf [Hxu] [$HrZ $Hg $Hh]"); try (intros; apply _).
    { iEval (rewrite eq_lift_prod). iExists _, _, _, _. by iFrame "#∗". }
    iIntros "!>" (frl frr) "Hfr (HrZ & Hg & Hh)". simpl.
    iEval (rewrite eq_lift_prod) in "Hfr".
    iDestruct "Hfr" as (xdl xdr kfl kfr) "(-> & -> & Hxd & Hkf)".
    eq_pures_l. eq_pures_r.
    iApply eq_value. iModIntro. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iFrame "Hxd".
    iApply eq_lift_arr. iIntros (ul ur) "Hu".
    iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
    eq_pures_l. eq_pures_r.
    (* f's set-up *)
    eq_reshape_l (kfl _). eq_reshape_r (kfr _).
    iApply (eq_call_nil 𝟙 (Yu θ)
              (rZ ↦ₗ NONEV ∗ ⟪ LArr Yu Yd Zu Zd θ ⟫ g g' ∗ ⟪ LArr Zu Zd Wu Wd θ ⟫ h h')%I
              with "Hkf [] [$HrZ $Hg $Hh]"); try (intros; apply _).
    { by iEval (rewrite eq_lift_unit). }
    iIntros "!>" (yul yur) "Hyu (HrZ & Hg & Hh)". simpl. eq_pures_l. eq_pures_r.
    (* Right: the placeholder for [Z]. *)
    eq_alloc_r rZ' as "HrZ'". eq_pures_r.
    iApply (eq_na_alloc (link_inv (Zd θ) rZ rZ') NL).
    iSplitL "HrZ HrZ'"; first (iNext; iLeft; iFrame). iIntros "#HinvZ".
    iDestruct (getter_eq with "HinvZ") as "#HgetZ".
    (* g *)
    eq_reshape_l (g _). eq_reshape_r (g' _).
    iApply (eq_call_nil (Yu θ × (𝟙 → Zd θ)) (Yd θ × (𝟙 ⊸ Zu θ)) (⟪ LArr Zu Zd Wu Wd θ ⟫ h h')
              with "Hg [Hyu] Hh"); try (intros; apply _).
    { iEval (rewrite eq_lift_prod). iExists _, _, _, _. by iFrame "#∗". }
    iIntros "!>" (grl grr) "Hgr Hh". simpl.
    iEval (rewrite eq_lift_prod) in "Hgr".
    iDestruct "Hgr" as (ydl ydr kgl kgr) "(-> & -> & #Hyd & Hkg)".
    eq_pures_l. eq_pures_r.
    (* fill Y *)
    eq_reshape_l (#rY <- _)%E. eq_reshape_r (#rY' <- _)%E.
    iApply link_fill. iFrame "HinvY Hyd". eq_pures_l. eq_pures_r.
    (* g's set-up *)
    eq_reshape_l (kgl _). eq_reshape_r (kgr _).
    iApply (eq_call_nil 𝟙 (Zu θ) (⟪ LArr Zu Zd Wu Wd θ ⟫ h h') with "Hkg [] Hh");
      try (intros; apply _).
    { by iEval (rewrite eq_lift_unit). }
    iIntros "!>" (zul zur) "Hzu Hh". simpl. eq_pures_l. eq_pures_r.
    (* h *)
    eq_reshape_l (h _). eq_reshape_r (h' _).
    iApply (eq_call_nil (Zu θ × (𝟙 → Wd θ)) (Zd θ × (𝟙 ⊸ Wu θ)) emp%I
              with "Hh [Hzu] []"); try (intros; apply _).
    { iEval (rewrite eq_lift_prod). iExists _, _, _, _. by iFrame "#∗". }
    { done. }
    iIntros "!>" (hrl hrr) "Hhr _". simpl.
    iEval (rewrite eq_lift_prod) in "Hhr".
    iDestruct "Hhr" as (zdl zdr khl khr) "(-> & -> & #Hzd & Hkh)".
    eq_pures_l. eq_pures_r.
    (* fill Z *)
    eq_reshape_l (#rZ <- _)%E. eq_reshape_r (#rZ' <- _)%E.
    iApply link_fill. iFrame "HinvZ Hzd". eq_pures_l. eq_pures_r.
    (* h's set-up *)
    eq_reshape_l (khl _). eq_reshape_r (khr _).
    iApply (eq_call_nil 𝟙 (Wu θ) emp%I with "Hkh [] []"); try (intros; apply _).
    { by iEval (rewrite eq_lift_unit). }
    { done. }
    iIntros "!>" (wul wur) "Hwu _". simpl. iApply eq_value. by iModIntro.
  Qed.

  Lemma link_assoc m (h h' g g' f f' : val) (Xu Xd Yu Yd Zu Zd Wu Wd : sem_row Σ → sem_ty Σ) :
    (∀ θ v1 v2, Persistent (Yd θ v1 v2)) → (∀ θ v1 v2, Persistent (Zd θ v1 v2)) →
    ⊢ ⟪ ModL m Zu Zd Wu Wd ⟫ h h' -∗ ⟪ ModL m Yu Yd Zu Zd ⟫ g g' -∗
      ⟪ ModL m Xu Xd Yu Yd ⟫ f f' -∗
      ⟪ ModL m Xu Xd Wu Wd ⟫ (link h (link g f)) (link (link h' g') f').
  Proof.
    intros HY HZ. rewrite !ModL_unfold. apply eq_mod_map3=> θ. by apply link_assoc_arr.
  Qed.

  (* Associativity as typings in both directions. *)
  Lemma link_assoc_typed m (h g f : val) (Xu Xd Yu Yd Zu Zd Wu Wd : sem_row Σ → sem_ty Σ) :
    (∀ θ v1 v2, Persistent (Yd θ v1 v2)) → (∀ θ v1 v2, Persistent (Zd θ v1 v2)) →
    (⊢ ⊨ᵥ h ≤ h : ModL m Zu Zd Wu Wd) → (⊢ ⊨ᵥ g ≤ g : ModL m Yu Yd Zu Zd) →
    (⊢ ⊨ᵥ f ≤ f : ModL m Xu Xd Yu Yd) →
    (⊢ ⊨ᵥ link h (link g f) ≤ link (link h g) f : ModL m Xu Xd Wu Wd) ∧
    (⊢ ⊨ᵥ link (link h g) f ≤ link h (link g f) : ModL m Xu Xd Wu Wd).
  Proof.
    intros HY HZ Hh Hg Hf.
    assert (⊢ ⟪ ModL m Xu Xd Wu Wd ⟫ (link h (link g f)) (link (link h g) f)) as H.
    { iApply (link_assoc m h h g g f f Xu Xd Yu Yd Zu Zd Wu Wd HY HZ);
        iApply val_typed_eq; done. }
    split; [apply eq_typed_l|apply eq_typed_r]; exact H.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* One-directional typing, and environments.                          *)
  (* ---------------------------------------------------------------- *)

  (* [link_eq] read in one direction: entailment in the logic of [eq/]
     holds direction by direction. *)
  Lemma link_typed m (g g' f f' : val) (Xu Xd Yu Yd Zu Zd : sem_row Σ → sem_ty Σ) :
    (∀ θ v1 v2, Persistent (Yd θ v1 v2)) →
    ⊢ ModL m Yu Yd Zu Zd g g' -∗ ModL m Xu Xd Yu Yd f f' -∗
      ModL m Xu Xd Zu Zd (link g f) (link g' f').
  Proof.
    intros HY. pose proof (link_eq m g g' f f' Xu Xd Yu Yd Zu Zd HY) as [H].
    specialize (H Fwd). rewrite monPred_at_emp in H.
    iIntros "Hg Hf". iPoseProof (H with "[//]") as "H".
    iEval (rewrite monPred_at_wand) in "H".
    iSpecialize ("H" $! Fwd with "[//] [Hg]"); first by rewrite eq_lift_at.
    iEval (rewrite monPred_at_wand) in "H".
    iSpecialize ("H" $! Fwd with "[//] [Hf]"); first by rewrite eq_lift_at.
    by rewrite eq_lift_at.
  Qed.

  (* An environment extended by a module above the one it is given, or
     below it, is an environment. *)
  Lemma env_under_link m (A g : val) (Xu Xd Yu Yd Zu Zd : sem_row Σ → sem_ty Σ) :
    (∀ θ v1 v2, Persistent (Yd θ v1 v2)) →
    ⊢ ⊨ᵥ A ≤ A : (ModL m Xu Xd Zu Zd → 𝔹) -∗ ⊨ᵥ g ≤ g : ModL m Yu Yd Zu Zd -∗
      ⊨ᵥ (λ: "v", A (link_app g "v"))%V ≤ (λ: "v", A (link_app g "v"))%V
        : (ModL m Xu Xd Yu Yd → 𝔹).
  Proof.
    intros HY. rewrite /sem_val_typed /tc_opaque. iIntros "#HA #Hg".
    rewrite /sem_ty_mbang /sem_ty_arr /=.
    iIntros "!> !>" (v1 v2) "Hv". rewrite /link_app.
    brel_pures_l. brel_pures_r.
    iApply "HA". iApply (link_typed with "Hg Hv").
  Qed.

  Lemma env_over_link m (A f : val) (Xu Xd Yu Yd Zu Zd : sem_row Σ → sem_ty Σ) :
    (∀ θ v1 v2, Persistent (Yd θ v1 v2)) →
    ⊢ ⊨ᵥ A ≤ A : (ModL m Xu Xd Zu Zd → 𝔹) -∗ ⊨ᵥ f ≤ f : ModL m Xu Xd Yu Yd -∗
      ⊨ᵥ (λ: "v", A (link_app "v" f))%V ≤ (λ: "v", A (link_app "v" f))%V
        : (ModL m Yu Yd Zu Zd → 𝔹).
  Proof.
    intros HY. rewrite /sem_val_typed /tc_opaque. iIntros "#HA #Hf".
    rewrite /sem_ty_mbang /sem_ty_arr /=.
    iIntros "!> !>" (v1 v2) "Hv". rewrite /link_app.
    brel_pures_l. brel_pures_r.
    iApply "HA". iApply (link_typed with "Hv Hf").
  Qed.

End links.

(* ------------------------------------------------------------------ *)
(* The composition theorem, for two-way modules.                       *)
(* ------------------------------------------------------------------ *)

Section uc_composition_link.
  #[local] Open Scope R_scope.
  Context `{!probblazeRGpreS Σ}.

  (* Boundaries (each with an up and a down part):
       XH : the real adversarial interface (of [Rw] and of [S])
       XF : the adversarial interface of [F]
       XG : the adversarial interface of [G]
       PF : the ports of [F] (and of [Rw]), used by [ρ]
       P  : the ports of [ρ] (and of [G])
     What is offered down across the internal boundaries [XF], [XG], [PF]
     is persistent (multi-use operations).

     [Rw] realises [F] with [S]; [ρ] on [F] realises [G] with [S'].  Then
     [ρ] on [Rw] realises [G] with [S' ∘ S].  In OCaml-like terms the
     ideal world is [module rec G' = G (S'') and S'' = S' (S)].  The
     theorem holds in either mode [m]: for modules ([MS]) and for
     one-instance modules ([OS]). *)
  Theorem uc_composition_link (m : mode) (Rw S F ρ S' G : val) (b : bool) (ε ε' : val → R)
      (XHu XHd XFu XFd XGu XGd PFu PFd Pu Pd : ∀ `{probblazeRGS Σ}, sem_row Σ → sem_ty Σ) :
    (∀ `{probblazeRGS Σ} θ v1 v2, Persistent (XFd θ v1 v2)) →
    (∀ `{probblazeRGS Σ} θ v1 v2, Persistent (XGd θ v1 v2)) →
    (∀ `{probblazeRGS Σ} θ v1 v2, Persistent (PFd θ v1 v2)) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ S ≤ S : ModL m XHu XHd XFu XFd) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ F ≤ F : ModL m XFu XFd PFu PFd) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ ρ ≤ ρ : ModL m PFu PFd Pu Pd) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ S' ≤ S' : ModL m XFu XFd XGu XGd) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ G ≤ G : ModL m XGu XGd Pu Pd) →
    (* [Rw] realises [F] with [S] *)
    (∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (ModL m XHu XHd PFu PFd → 𝔹)%T) →
       advantage A Rw (link F S) #b <= ε A) →
    (* [ρ] on [F] realises [G] with [S'] *)
    (∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (ModL m XFu XFd Pu Pd → 𝔹)%T) →
       advantage A (link ρ F) (link G S') #b <= ε' A) →
    ∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (ModL m XHu XHd Pu Pd → 𝔹)%T) →
      advantage A (link ρ Rw) (link G (link S' S)) #b
        <= ε (λ: "v", A (link_app ρ "v"))%V + ε' (λ: "v", A (link_app "v" S))%V.
  Proof.
    intros HXF HXG HPF HS HF Hρ HS' HG H1 H2 A HA.
    set (β := λ H : probblazeRGS Σ, @ModL Σ H m (XHu H) (XHd H) (Pu H) (Pd H)).
    (*   ρ ∘ Rw  ≤  ρ ∘ (F ∘ S)  ≃  (ρ ∘ F) ∘ S  ≤  (G ∘ S') ∘ S  ≃  G ∘ (S' ∘ S)   *)
    apply (advantage_triangle _ _ (link ρ (link F S)) _ _
             (ε (λ: "v", A (link_app ρ "v"))%V)
             (ε' (λ: "v", A (link_app "v" S))%V)); [| |lra].
    - (* through the protocol *)
      etrans; first apply (advantage_pure_l_rev _ [] (link_app ρ Rw) _ _);
        [done|apply link_app_pure|].
      etrans; first apply (advantage_pure_r_rev _ [] _ (link_app ρ (link F S)) _);
        [done|apply link_app_pure|].
      etrans; first apply (advantage_reduction_ctx A [AppRCtx (link_app ρ)]).
      { done. }
      { intros vs w Hw. simpl. by rewrite Hw. }
      apply H1. intros HRGS. iApply env_under_link; [iApply HA|iApply Hρ].
    - apply (advantage_triangle _ _ (link (link ρ F) S) _ _ 0
               (ε' (λ: "v", A (link_app "v" S))%V)); [| |lra].
      { apply (advantage_zero _ _ _ _ β); [exact HA| |]; intros HRGS; iApply sem_typed_val.
        - iApply (proj1 (link_assoc_typed m ρ F S _ _ _ _ _ _ _ _ _ _ (Hρ _) (HF _) (HS _))).
        - iApply (proj2 (link_assoc_typed m ρ F S _ _ _ _ _ _ _ _ _ _ (Hρ _) (HF _) (HS _))). }
      apply (advantage_triangle _ _ (link (link G S') S) _ _
               (ε' (λ: "v", A (link_app "v" S))%V) 0); [| |lra].
      + (* over the simulator *)
        etrans; first apply (advantage_pure_l_rev _ [] (link_app (link ρ F) S) _ _);
          [done|apply link_app_pure|].
        etrans; first apply (advantage_pure_r_rev _ [] _ (link_app (link G S') S) _);
          [done|apply link_app_pure|].
        etrans; first apply (advantage_reduction_ctx A [AppLCtx S; AppRCtx link_app]).
        { done. }
        { intros vs w Hw. simpl. by rewrite Hw. }
        apply H2. intros HRGS. iApply env_over_link; [iApply HA|iApply HS].
      + apply (advantage_zero _ _ _ _ β); [exact HA| |]; intros HRGS; iApply sem_typed_val.
        * iApply (proj2 (link_assoc_typed m G S' S _ _ _ _ _ _ _ _ _ _ (HG _) (HS' _) (HS _))).
        * iApply (proj1 (link_assoc_typed m G S' S _ _ _ _ _ _ _ _ _ _ (HG _) (HS' _) (HS _))).
  Qed.

End uc_composition_link.

(* ------------------------------------------------------------------ *)
(* One-way modules as two-way modules.                                 *)
(* ------------------------------------------------------------------ *)

Section embedding.
  Context `{!probblazeRGS Σ}.
  #[local] Open Scope bi_scope.

  (* The trivial down-interface. *)
  Definition Unit : sem_row Σ → sem_ty Σ := λ _, 𝟙%T.

  Global Instance Unit_persistent θ v1 v2 : Persistent (Unit θ v1 v2).
  Proof. rewrite /Unit /sem_ty_unit. apply _. Qed.

  Lemma eq_mod_map1 m (A1 A : sem_row Σ → sem_ty Σ) v1 v1' w w' :
    (∀ θ, ⊢ ⟪ A1 θ ⟫ v1 v1' -∗ ⟪ A θ ⟫ w w') →
    ⊢ ⟪ ∀ᵣ θ, ![m] (A1 θ) ⟫ v1 v1' -∗ ⟪ ∀ᵣ θ, ![m] (A θ) ⟫ w w'.
  Proof.
    intros H. rewrite !eq_lift_forall. iIntros "H1" (θ).
    iSpecialize ("H1" $! θ). rewrite !eq_lift_mbang. destruct m; simpl.
    - iApply (H with "H1").
    - iDestruct "H1" as "#H1". iModIntro. iApply (H with "H1").
  Qed.

  Lemma ModM_unfold m (X Y : sem_row Σ → sem_ty Σ) :
    ModM m X Y = (∀ᵣ θ, ![m] (X θ ⊸ Y θ))%T.
  Proof. done. Qed.

  (* An embedded module is typed. *)
  Lemma embed_arr_eq θ (f f' : val) (X Y : sem_row Σ → sem_ty Σ) :
    ⊢ ⟪ X θ ⊸ Y θ ⟫ f f' -∗ ⟪ LArr X Unit Y Unit θ ⟫ (embed f) (embed f').
  Proof.
    iIntros "Hf". rewrite /LArr /Unit. iApply eq_lift_arr. iIntros (al ar) "Ha".
    iEval (rewrite eq_lift_prod) in "Ha".
    iDestruct "Ha" as (xul xur dl dr) "(-> & -> & Hxu & _)".
    rewrite /embed. eq_pures_l. eq_pures_r.
    iApply eq_value. iModIntro. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done).
    iSplit; first by iEval (rewrite eq_lift_unit).
    iApply eq_lift_arr. iIntros (ul ur) "Hu".
    iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
    eq_pures_l. eq_pures_r.
    iApply (eq_call_nil (X θ) (Y θ) emp%I _ _ _ _ [] [] with "Hf Hxu []");
      try (intros; apply _).
    { done. }
    iIntros "!>" (yl yr) "Hy _". simpl. iApply eq_value. by iModIntro.
  Qed.

  Lemma embed_eq m (f f' : val) (X Y : sem_row Σ → sem_ty Σ) :
    ⊢ ⟪ ModM m X Y ⟫ f f' -∗ ⟪ ModL m X Unit Y Unit ⟫ (embed f) (embed f').
  Proof. rewrite ModM_unfold ModL_unfold. apply eq_mod_map1=> θ. apply embed_arr_eq. Qed.

  Lemma embed_typed m (f f' : val) (X Y : sem_row Σ → sem_ty Σ) :
    ⊢ ModM m X Y f f' -∗ ModL m X Unit Y Unit (embed f) (embed f').
  Proof.
    pose proof (embed_eq m f f' X Y) as [H]. specialize (H Fwd). rewrite monPred_at_emp in H.
    iIntros "Hf". iPoseProof (H with "[//]") as "H".
    iEval (rewrite monPred_at_wand) in "H".
    iSpecialize ("H" $! Fwd with "[//] [Hf]"); first by rewrite eq_lift_at.
    by rewrite eq_lift_at.
  Qed.

  (* Linking embedded modules is embedding their composite.  The link's
     placeholder is allocated and filled on the left only, and never
     looked up. *)
  Lemma link_embed_arr θ (g g' f f' : val) (X Y Z : sem_row Σ → sem_ty Σ) :
    ⊢ ⟪ Y θ ⊸ Z θ ⟫ g g' -∗ ⟪ X θ ⊸ Y θ ⟫ f f' -∗
      ⟪ LArr X Unit Z Unit θ ⟫ (link (embed g) (embed f)) (embed (comp_op g' f')).
  Proof.
    iIntros "Hg Hf". rewrite /LArr /Unit. iApply eq_lift_arr. iIntros (al ar) "Ha".
    iEval (rewrite eq_lift_prod) in "Ha".
    iDestruct "Ha" as (xul xur dl dr) "(-> & -> & Hxu & #Hd)".
    rewrite /link /embed /getter /comp_op.
    eq_pures_l. eq_alloc_l r as "Hr". eq_pures_l. eq_pures_r.
    iApply eq_value. iModIntro. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done).
    iSplit; first by iEval (rewrite eq_lift_unit).
    iApply eq_lift_arr. iIntros (ul ur) "Hu".
    iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
    eq_pures_l. eq_pures_r.
    (* f *)
    eq_reshape_l (f _). eq_reshape_r (f' _).
    iApply (eq_call_nil (X θ) (Y θ) (r ↦ₗ NONEV ∗ ⟪ Y θ ⊸ Z θ ⟫ g g')%I
              with "Hf Hxu [$Hr $Hg]"); try (intros; apply _).
    iIntros "!>" (yl yr) "Hy [Hr Hg]". simpl. eq_pures_l. try (try eq_pures_r).
    (* the placeholder, on the left only *)
    eq_store_l. eq_pures_l.
    (* g *)
    eq_reshape_l (g _). eq_reshape_r (g' _).
    iApply (eq_call_nil (Y θ) (Z θ) emp%I with "Hg Hy []"); try (intros; apply _).
    { done. }
    iIntros "!>" (zl zr) "Hz _". simpl. iApply eq_value. by iModIntro.
  Qed.

  Lemma link_embed m (g g' f f' : val) (X Y Z : sem_row Σ → sem_ty Σ) :
    ⊢ ⟪ ModM m Y Z ⟫ g g' -∗ ⟪ ModM m X Y ⟫ f f' -∗
      ⟪ ModL m X Unit Z Unit ⟫ (link (embed g) (embed f)) (embed (comp_op g' f')).
  Proof.
    rewrite !ModM_unfold ModL_unfold. apply eq_mod_map2=> θ. apply link_embed_arr.
  Qed.

  (* An environment for two-way modules is one for one-way modules. *)
  Lemma env_embed m (A : val) (X Y : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ A ≤ A : (ModL m X Unit Y Unit → 𝔹) -∗
      ⊨ᵥ (λ: "v", A (embed_app "v"))%V ≤ (λ: "v", A (embed_app "v"))%V : (ModM m X Y → 𝔹).
  Proof.
    rewrite /sem_val_typed /tc_opaque. iIntros "#HA".
    rewrite /sem_ty_mbang /sem_ty_arr /=.
    iIntros "!> !>" (v1 v2) "Hv". rewrite /embed_app.
    brel_pures_l. brel_pures_r.
    iApply "HA". iApply (embed_typed with "Hv").
  Qed.

End embedding.

Section embedding_advantage.
  #[local] Open Scope R_scope.
  Context `{!probblazeRGpreS Σ}.

  (* A statement about one-way modules holds for their embeddings. *)
  Lemma advantage_embed m (Rw I : val) (b : bool) (ε : val → R)
      (X Y : ∀ `{probblazeRGS Σ}, sem_row Σ → sem_ty Σ) :
    (∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (ModM m X Y → 𝔹)%T) →
       advantage A Rw I #b <= ε A) →
    ∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (ModL m X Unit Y Unit → 𝔹)%T) →
      advantage A (embed Rw) (embed I) #b <= ε (λ: "v", A (embed_app "v"))%V.
  Proof.
    intros H A HA.
    etrans; first apply (advantage_pure_l_rev _ [] (embed_app Rw) _ _);
      [done|apply embed_app_pure|].
    etrans; first apply (advantage_pure_r_rev _ [] _ (embed_app I) _);
      [done|apply embed_app_pure|].
    etrans; first apply (advantage_reduction_ctx A [AppRCtx embed_app]).
    { done. }
    { intros vs w Hw. simpl. by rewrite Hw. }
    apply H. intros HRGS. iApply env_embed. iApply HA.
  Qed.

  (* The bridge from the one-way case studies: if [R] realises [F] with
     [S] as one-way modules, then [embed R] realises [embed F] with
     [embed S] as two-way modules, with the ideal world linked. *)
  Lemma realises_embed m (Rw F S : val) (b : bool) (ε : val → R)
      (X Y Z : ∀ `{probblazeRGS Σ}, sem_row Σ → sem_ty Σ) :
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ F ≤ F : ModM m Y Z) →
    (∀ `{probblazeRGS Σ}, ⊢ ⊨ᵥ S ≤ S : ModM m X Y) →
    (∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (ModM m X Z → 𝔹)%T) →
       advantage A Rw (comp_op F S) #b <= ε A) →
    ∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (ModL m X Unit Z Unit → 𝔹)%T) →
      advantage A (embed Rw) (link (embed F) (embed S)) #b <= ε (λ: "v", A (embed_app "v"))%V.
  Proof.
    intros HF HS H A HA.
    apply (advantage_triangle _ _ (embed (comp_op F S)) _ _
             (ε (λ: "v", A (embed_app "v"))%V) 0); [| |lra].
    - by apply (advantage_embed m _ _ _ _ X Z).
    - apply (advantage_zero _ _ _ _ (λ H : probblazeRGS Σ, @ModL Σ H m (X H) Unit (Z H) Unit));
        [exact HA| |]; intros HRGS; iApply sem_typed_val.
      + iApply eq_typed_r. iApply link_embed; iApply val_typed_eq; [iApply HF|iApply HS].
      + iApply eq_typed_l. iApply link_embed; iApply val_typed_eq; [iApply HF|iApply HS].
  Qed.

End embedding_advantage.
