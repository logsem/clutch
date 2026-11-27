(* A mutant of oblivious transfer reversal that leaks Bob's choice, and
   an environment that detects the leak with every simulator.

   The mutant Bob, [TO_R_LEAK], is [TO_R] with an extra adversarial
   operation [tell]: after he has received Alice's message, he tells the
   adversary his choice [c].  The ideal transfer gives the simulator
   nothing that depends on [c], so the mutant does not realise it: an
   environment that chose [c] checks whether the adversary was told [c].

   The leak comes after Bob has received Alice's message, and Bob can
   receive it only if the parties run out of order: Bob waits in the OT
   for Alice's choice, Alice waits in the OT for Bob's messages, and Bob
   waits on the channel for Alice's message.  An environment whose
   adversarial operations are plain functions runs the parties
   last-in-first-out, and then both never finish (see [ot_rev_schedule.v]),
   so it never sees [tell]; in a model with only such environments the
   mutant would pass as secure.  The environment here pauses the parties
   at the adversarial operations with a handler and resumes them in the
   order above.

   The results:
   - [sched_leak_correct], [sched_leak_real]: with the mutant parties on
     the ideal OT and a channel, the environment returns [true] with
     probability [1].
   - [SCHED_LEAK_typed]: the environment has the environments' type
     [Mod TOHNetL TPorts → 𝔹].
   - [SCHED_LEAK_typed_gen] with [negb], [F_TO_H_neg_eq]: the environment
     for [c] and the environment for [¬c] are related with results
     [b] and [¬b], on the ideal transfer with any typed simulator; the
     transfer does not show the difference to the simulator.
   - [to_h_leak_insecure]: hence for every typed simulator [S] there is a
     choice [c] for which the environment has advantage at least [1/2]
     between the mutant and the ideal transfer with [S]. *)

From iris.proofmode Require Import base proofmode classes environments.
From iris.base_logic.lib Require Import na_invariants.
From iris.bi Require Import monpred.
From iris.proofmode Require Import monpred.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory semantics logic adequacy mode.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_valgroup eq_compat.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules eq_modules auth ot ot_rev ot_rev_proof
  ot_rev_typing ot_rev_schedule.

Import valgroup_tactics.

#[local] Set Default Proof Using "All".

Section ot_rev_leak.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.

  (* Bob, telling the adversary his choice once he has Alice's message. *)
  Definition TO_R_LEAK : val :=
    λ: "res",
      let, ("net", "tell") := "res" in
      let, ("sport", "recv") := "net" in

      λ: "c",
        let: "snd" := "sport" #()%V in
        let: "r" := flip #()%V in
        "snd" (gbit "r", gbit (bxor "r" "c"));;
        let: "m" := "recv" #()%V in
        "tell" "c";;
        bxor "m" "r".

  (* The parties, with [tell] passed through to Bob. *)
  Definition PARTIES_TO_LEAK : val :=
    λ: "res",
      let, ("otab", "tell") := "res" in
      let, ("ot", "ab") := "otab" in
      let, ("sport", "rport") := "ot" in
      let, ("send", "recv") := "ab" in
      (TO_S ("rport", "send"), TO_R_LEAK (("sport", "recv"), "tell")).

  Definition HYB_TO_H_LEAK : val := (PARTIES_TO_LEAK ⊳ ((F_OT_H ⊗ F_OAUTH) ⊗ id_mod))%md.

  (* The environment, for Alice's bits [(x0, x1)] and Bob's choice [c]:
     the schedule of [SCHED_ENV], with [tell] storing into a cell; it
     returns [true] when the cell holds [c].  The cell starts at [false],
     which is [c] for [c = false]; what matters is that the result for [c]
     and for [¬c] differ whenever the cell is the same. *)
  Definition SCHED_LEAK (x0 x1 c : bool) : val :=
    λ: "W",
      let: "cell" := ref #false in
      (effect "w"
        let: "adv" := (((λ: <>, (do: "w" #()%V);; (λ: <>, #()%V), λ: <>, do: "w" #()%V),
                        (λ: <>, #()%V, λ: <>, do: "w" #()%V)),
                       λ: "b", "cell" <- "b") in
        let, ("alice", "bob") := "W" "adv" in
        let: "sB" :=
          handle: "bob" #c with
          | effect "w" <>, "k" => InjR "k"
          | return "y" => InjL "y"
          end in
        let: "sA" :=
          handle: "alice" (#x0, #x1) with
          | effect "w" <>, "k" => InjR "k"
          | return "y" => InjL "y"
          end in
        let: "sB" :=
          match: "sB" with
            InjL "y" => InjL "y"
          | InjR "k" =>
              handle: "k" #()%V with
              | effect "w" <>, "k" => InjR "k"
              | return "y" => InjL "y"
              end
          end in
        let: "sA" :=
          match: "sA" with
            InjL "y" => InjL "y"
          | InjR "k" =>
              handle: "k" #()%V with
              | effect "w" <>, "k" => InjR "k"
              | return "y" => InjL "y"
              end
          end in
        let: "sB" :=
          match: "sB" with
            InjL "y" => InjL "y"
          | InjR "k" =>
              handle: "k" #()%V with
              | effect "w" <>, "k" => InjR "k"
              | return "y" => InjL "y"
              end
          end in
        #()%V);;
      if: !"cell" then #c else #(negb c).

End ot_rev_leak.

Section ot_rev_leak_types.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.

  (* The adversarial interface of the mutant: the honest one and [tell]. *)
  Definition TOHNetL (θ : sem_row Σ) : sem_ty Σ := (TOHNet θ × (𝔹 -{ θ }-> 𝟙))%T.

  (* Booleans [b] on the left and [f b] on the right: [𝔹] for [f = id]. *)
  Definition sem_ty_boolf (f : bool → bool) : sem_ty Σ :=
    (λ v1 v2, ∃ b : bool, ⌜v1 = #b ∧ v2 = #(f b)⌝)%I.

  (* The ports, with Bob's choice related by [sem_ty_boolf f] and his
     output by [TO]: [TPorts] for [f = id] and [TO = 𝔹]. *)
  Definition PortsB (f : bool → bool) (TO : sem_ty Σ) (θ : sem_row Σ) : sem_ty Σ :=
    (TSPort θ × (sem_ty_boolf f -{ ¡ θ }-∘ TO))%T.

End ot_rev_leak_types.

Section ot_rev_leak_proof.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.

  (* With the mutant parties, the environment returns [true]. *)
  Lemma sched_leak_correct (x0 x1 c : bool) :
    ⊢ BREL #true ≤ SCHED_LEAK x0 x1 c HYB_TO_H_LEAK <|⊥|> {{ λ v1 v2, ⌜v1 = v2⌝ }}.
  Proof.
    rewrite /SCHED_LEAK. brel_pures_r. brel_alloc_r cell as "Hcell". brel_pures_r.
    brel_effect_r w as "Hw".
    rewrite /HYB_TO_H_LEAK /comp_op /tens_op /id_mod /PARTIES_TO_LEAK /F_OT_H /F_OAUTH /TO_S
      /TO_R_LEAK /bxor /ungbit /gbit /ot_rev.flip is_unit.
    brel_pures_r. brel_alloc_r ch as "Hch". brel_pures_r. brel_alloc_r mm as "Hmm". brel_pures_r.
    brel_alloc_r box as "Hbox". brel_pures_r.
    (* Bob, until he waits in the OT for Alice's choice. *)
    brel_handle_r kB "HkB". brel_pures_r.
    destruct x0, x1, c;
      ((* Alice, until she waits in the OT for Bob's messages. *)
       brel_pures_r; brel_store_r; brel_pures_r; brel_handle_r kA "HkA"; brel_pures_r;
       (* Bob, resumed: his mask, his OT messages, and his wait on the
          channel. *)
       brel_cont_r; brel_pures_r; brel_load_r; brel_pures_r;
       brel_sample_r; iIntros (k Hk);
       assert (k = 0%nat ∨ k = 1%nat)%type as [-> | ->] by (simpl in Hk; lia);
       brel_pures_r; brel_store_r; brel_pures_r; brel_handle_r kB2 "HkB2"; brel_pures_r;
       (* Alice, resumed: her OT output, and her message. *)
       brel_cont_r; brel_pures_r; brel_load_r; brel_pures_r;
       brel_eq_r; rewrite ?bd_gg ?bd_1g; brel_pures_r; brel_store_r; brel_pures_r;
       (* Bob, resumed: Alice's message, the leak, and his output; then the
          environment reads the cell. *)
       brel_cont_r; brel_pures_r; brel_load_r; brel_pures_r; brel_store_r; brel_pures_r;
       brel_load_r; brel_pures_r;
       by iModIntro).
  Qed.

End ot_rev_leak_proof.

Section ot_rev_leak_typing.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.

  Ltac solve_dom :=
    first
      [ by intros []
      | rewrite ?env_dom_cons ?env_dom_app ?env_dom_nil;
        repeat (apply not_elem_of_cons; split; [intros ?; simplify_eq|]);
        apply not_elem_of_nil ].

  Ltac lift_nil :=
    iApply sem_typed_sub;
    [iApply env_le_refl|iApply env_le_refl|iApply row_le_nil|iApply ty_le_refl|].

  Lemma sem_typed_boolf (f : bool → bool) Γ (b : bool) :
    ⊢ sem_typed Γ #b #(f b) ⟨⟩ (sem_ty_boolf f) Γ.
  Proof.
    iIntros (γ) "!# HΓ //=".
    iApply brel_value. iFrame. iIntros. iFrame. by iExists b.
  Qed.

  (* The environment, for [c] on the left and [f c] on the right, for an
     [f] that commutes with negation. *)
  Lemma SCHED_LEAK_typed_gen (f : bool → bool) (TO : sem_ty Σ) (x0 x1 c : bool) :
    (∀ b, f (negb b) = negb (f b)) →
    ⊢ ⊨ᵥ SCHED_LEAK x0 x1 c ≤ SCHED_LEAK x0 x1 (f c)
        : (Mod TOHNetL (PortsB f TO) → sem_ty_boolf f).
  Proof.
    intros Hf. rewrite /SCHED_LEAK -Hf.
    iApply sem_typed_closure; first done. simpl.
    set (M := Mod TOHNetL (PortsB f TO)).
    (* The cell. *)
    iApply (sem_typed_let (Refᶜ 𝔹) _ _ _ [("W", M)]); [solve_dom|solve_dom| |].
    { iApply sem_typed_alloc_cpy. iApply sem_typed_bool. }
    simpl.
    iApply (sem_typed_seq 𝟙 _ _ _ [("cell", Refᶜ 𝔹)]).
    - (* The schedule, keeping a copy of the cell. *)
      iApply (sem_typed_sub _ (("cell", Refᶜ 𝔹) :: ("cell", Refᶜ 𝔹) :: [("W", M)]));
        [iApply env_le_contraction|iApply env_le_refl|iApply row_le_refl|iApply ty_le_refl|].
      iApply (sem_typed_frame_gen _ _ _ _ "cell" (Refᶜ 𝔹) _ []).
      iApply sem_typed_effect_gen. iIntros (l1 l2). simpl.
      change (sem_sig_bottom l1 l2 · ⟨⟩)%R with (ρw (Σ := Σ) l1 l2).
      set (θ := θw (Σ := Σ) l1 l2).
      (* The adversarial operations; [tell] takes the cell. *)
      iApply (sem_typed_let (TOHNetL θ) _ _ _ [("W", M)]); [solve_dom|solve_dom| |].
      { lift_nil. rewrite /TOHNetL. iApply sem_typed_pair.
        - iApply (sem_typed_oval _ [("cell", Refᶜ 𝔹)] [("W", M)]).
          iApply sem_oval_typed_ufun; [solve_dom|solve_dom|done|]. simpl.
          lift_nil.
          iApply (sem_typed_store_cpy_gen 𝔹 ⟨⟩%R _ [("cell", Refᶜ 𝔹)]); iApply sem_typed_var.
        - iApply adv_typed. }
      simpl.
      (* The world. *)
      iApply (sem_typed_pair_elim (TSPort θ) _ (sem_ty_boolf f -{ ¡ θ }-∘ TO)%T _ _ []);
        [solve_dom|solve_dom|solve_dom|solve_dom|done| |].
      { iApply (sem_typed_app_gen (TOHNetL θ) ⟨⟩%R (ρw l1 l2) ⟨⟩%R (PortsB f TO θ) _
                  [("W", M)] []).
        - iApply row_le_nil.
        - iApply row_le_nil.
        - iApply sem_typed_sub; [iApply env_le_refl|iApply env_le_refl|iApply row_le_refl
                                |iApply ty_le_mbang_elim|].
          rewrite /M /Mod /ModM.
          iApply (sem_typed_RApp (λ θ', (TOHNetL θ' -[MS]-> PortsB f TO θ')%T)).
          iApply sem_typed_var.
        - lift_nil. iApply sem_typed_var. }
      simpl.
      (* Bob, until he pauses. *)
      iApply (sem_typed_let (St l1 l2 TO) _ _ _ [("alice", TSPort θ)]); [solve_dom|solve_dom| |].
      { iApply (sem_typed_frame_gen [("bob", (sem_ty_boolf f -{ ¡ θ }-∘ TO)%T)] _ _ _
                  "alice" (TSPort θ) _ []).
        iApply pause_typed.
        iApply (sem_typed_app_gen (sem_ty_boolf f) ⟨⟩%R θ (¡ θ)%R TO _
                  [("bob", (sem_ty_boolf f -{ ¡ θ }-∘ TO)%T)] []).
        - iApply row_le_nil.
        - iApply row_le_flip_θw.
        - iApply sem_typed_var.
        - lift_nil. iApply sem_typed_boolf. }
      simpl.
      (* Alice, until she pauses. *)
      iApply (sem_typed_let (St l1 l2 𝟙) _ _ _ [("sB", St l1 l2 TO)]); [solve_dom|solve_dom| |].
      { iApply (sem_typed_frame_gen [("alice", TSPort θ)] _ _ _ "sB" (St l1 l2 TO) _ []).
        iApply pause_typed.
        iApply (sem_typed_app_gen (𝔹 × 𝔹)%T ⟨⟩%R θ (¡ θ)%R 𝟙%T _ [("alice", TSPort θ)] []).
        - iApply row_le_nil.
        - iApply row_le_flip_θw.
        - iApply sem_typed_var.
        - lift_nil. iApply sem_typed_pair; iApply sem_typed_bool. }
      simpl.
      (* Bob, Alice, Bob, resumed. *)
      iApply (sem_typed_let (St l1 l2 TO) _ _ _ [("sA", St l1 l2 𝟙)]); [solve_dom|solve_dom| |].
      { iApply (sem_typed_frame_gen [("sB", St l1 l2 TO)] _ _ _ "sA" (St l1 l2 𝟙) _ []).
        iApply resume_typed. }
      simpl.
      iApply (sem_typed_let (St l1 l2 𝟙) _ _ _ [("sB", St l1 l2 TO)]); [solve_dom|solve_dom| |].
      { iApply (sem_typed_frame_gen [("sA", St l1 l2 𝟙)] _ _ _ "sB" (St l1 l2 TO) _ []).
        iApply resume_typed. }
      simpl.
      iApply (sem_typed_let (St l1 l2 TO) _ _ _ [("sA", St l1 l2 𝟙)]); [solve_dom|solve_dom| |].
      { iApply (sem_typed_frame_gen [("sB", St l1 l2 TO)] _ _ _ "sA" (St l1 l2 𝟙) _ []).
        iApply resume_typed. }
      simpl.
      (* Both states are dropped. *)
      iApply (sem_typed_sub _ _ _ [("sB", St l1 l2 TO); ("sA", St l1 l2 𝟙)]);
        [iApply env_le_refl|iApply env_le_nil|iApply row_le_nil|iApply ty_le_refl|].
      iApply sem_typed_unit.
    - (* The cell against [c]. *)
      iApply (sem_typed_if [("cell", Refᶜ 𝔹)] [] []).
      + iApply sem_typed_load_cpy. iApply sem_typed_var.
      + iApply sem_typed_boolf.
      + iApply sem_typed_boolf.
  Qed.

  (* The environment is an environment of the mutant. *)
  Lemma SCHED_LEAK_typed (x0 x1 c : bool) :
    ⊢ ⊨ᵥ SCHED_LEAK x0 x1 c ≤ SCHED_LEAK x0 x1 c : (Mod TOHNetL TPorts → 𝔹).
  Proof. iApply (SCHED_LEAK_typed_gen (λ b, b) 𝔹%T x0 x1 c). done. Qed.

End ot_rev_leak_typing.

Section ot_rev_leak_ideal.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  #[local] Open Scope bi_scope.

  Lemma eq_lift_bool_neg vl vr :
    eq_lift (Σ := Σ) (sem_ty_boolf negb) vl vr ⊣⊢ ∃ b : bool, ⌜vl = #b ∧ vr = #(negb b)⌝.
  Proof.
    split=> d. rewrite monPred_at_exist eq_lift_at. setoid_rewrite monPred_at_pure.
    destruct d; rewrite /pick /sem_ty_boolf /=; iSplit; iIntros "[%b [-> ->]]".
    all: first [by iExists b | iExists (negb b); iPureIntro; by destruct b].
  Qed.

  Lemma eq_top vl vr : ⊢ ⟪ (⊤ : sem_ty Σ) ⟫ vl vr.
  Proof. split=> d. rewrite monPred_at_emp eq_lift_at /sem_ty_top. by iIntros. Qed.

  (* The ideal transfer, with Bob's choices [c] and [¬c] on the two
     sides: the adversary is called the same way, and Bob's outputs are
     not related. *)
  Lemma F_TO_H_neg_eq : ⊢ ⟪ Mod TOHAdv (PortsB negb ⊤) ⟫ F_TO_H F_TO_H.
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /TOHAdv. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (ral rar rbl rbr) "(-> & -> & Hra & Hrb)".
    rewrite /F_TO_H.
    eq_pures_l. eq_alloc_l xs as "Hxs". eq_pures_l.
    eq_pures_r. eq_alloc_r xs' as "Hxs'". eq_pures_r.
    iApply (eq_na_alloc (box_rel_gen bits xs xs') (NTH .@ "xs")).
    iSplitL "Hxs Hxs'"; first (iNext; iLeft; iFrame). iIntros "#Ixs".
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iApply eq_value. iModIntro. rewrite /PortsB. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iSplitL "Hra".
    - (* Alice *)
      rewrite /TSPort. iApply eq_lift_arr. iIntros (xl xr) "Hx".
      iEval (rewrite eq_lift_prod) in "Hx".
      iDestruct "Hx" as (x0l x0r x1l x1r) "(-> & -> & Hx0 & Hx1)".
      iEval (rewrite eq_lift_bool) in "Hx0". iDestruct "Hx0" as %(x0 & -> & ->).
      iEval (rewrite eq_lift_bool) in "Hx1". iDestruct "Hx1" as %(x1 & -> & ->).
      eq_pures'.
      assert (bits (#x0, #x1)%V) as Hb by (by exists x0, x1).
      eq_reshape_l (Store _ _). eq_reshape_r (Store _ _).
      iApply (eq_na_store_box _ _ _ _ _ _ _ _ _ Hb with "Ixs"). eq_pures'.
      iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T 𝟙%T emp%I ral rar _ _ [] [] with "Hρ Hra [] []");
        try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
      iIntros "!>" (??) "Hu _". by iApply eq_value.
    - (* Bob *)
      iApply eq_lift_arr. iIntros (cl cr) "Hc".
      iEval (rewrite eq_lift_bool_neg) in "Hc". iDestruct "Hc" as %(c & -> & ->).
      eq_pures'.
      eq_reshape_l (rbl _). eq_reshape_r (rbr _).
      iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T 𝟙%T emp%I with "Hρ Hrb [] []");
        try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
      iIntros "!>" (??) "Hu _". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      eq_reshape_l (Load _). eq_reshape_r (Load _).
      iApply (eq_na_load_box with "Ixs"). iIntros (w) "%Hw".
      destruct Hw as [->|(? & (x0 & x1 & ->) & ->)].
      { eq_pures'. iApply eq_loop. }
      destruct c; eq_pures'; iApply eq_value; iModIntro; iApply eq_top.
  Qed.

  (* The ideal transfer with any typed simulator. *)
  Lemma IDEAL_neg_typed (S : val) :
    ⊢ ⊨ᵥ S ≤ S : Mod TOHNetL TOHAdv -∗
      ⊨ᵥ (F_TO_H ⊳ S)%md ≤ (F_TO_H ⊳ S)%md : Mod TOHNetL (PortsB negb ⊤).
  Proof.
    iIntros "HS". iApply (comp_op_typed with "[] HS").
    iApply eq_val_typed. iApply F_TO_H_neg_eq.
  Qed.

End ot_rev_leak_ideal.

(* Two results have probability at most [1] together. *)
Lemma pmf_two `{Countable A} (μ : distr A) (a b : A) :
  a ≠ b → (μ a + μ b <= 1)%R.
Proof.
  intros Hab.
  rewrite -(SeriesC_singleton a (μ a)) -(SeriesC_singleton b (μ b)).
  rewrite -SeriesC_plus; [|apply ex_seriesC_singleton|apply ex_seriesC_singleton].
  etrans; last apply (pmf_SeriesC μ).
  apply SeriesC_le; last done.
  intros x. pose proof (pmf_pos μ a). pose proof (pmf_pos μ b). pose proof (pmf_pos μ x).
  split; repeat case_bool_decide; subst; try congruence; lra.
Qed.

Section ot_rev_leak_adequacy.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  #[local] Open Scope R_scope.

  (* With the mutant parties, the environment returns [true] with
     probability [1]. *)
  Theorem sched_leak_real (x0 x1 c : bool) σ :
    lim_exec (SCHED_LEAK x0 x1 c HYB_TO_H_LEAK, σ) #true = 1.
  Proof. apply brel_lim_exec_1. intros HRGS. iApply sched_leak_correct. Qed.

  (* On the ideal transfer with a typed simulator, the environment for [c]
     returns [true] at most as often as the one for [¬c] returns
     [false]. *)
  Lemma sched_leak_ideal_neg (S : val) (x0 x1 c : bool) σ :
    (∀ `{!probblazeRGS Σ}, ⊢ ⊨ᵥ S ≤ S : Mod TOHNetL TOHAdv) →
    lim_exec (SCHED_LEAK x0 x1 c (F_TO_H ⊳ S)%md, σ) #true <=
      lim_exec (SCHED_LEAK x0 x1 (negb c) (F_TO_H ⊳ S)%md, σ) #false.
  Proof.
    intros HS.
    assert (ARcoupl (lim_exec (SCHED_LEAK x0 x1 c (F_TO_H ⊳ S)%md, σ))
              (lim_exec (SCHED_LEAK x0 x1 (negb c) (F_TO_H ⊳ S)%md, σ))
              (λ v1 v2, ∃ b : bool, v1 = #b ∧ v2 = #(negb b))%type 0) as Hc.
    { apply (brel_refines_coupling Σ (λ _, sem_ty_boolf negb)).
      - iIntros (? v1 v2) "(%b & %Hb)". iPureIntro. by exists b.
      - intros HRGS.
        iPoseProof (SCHED_LEAK_typed_gen (G := G HRGS) negb ⊤%T x0 x1 c ltac:(done)) as "HA".
        iPoseProof (IDEAL_neg_typed S with "[]") as "HI"; first iApply HS.
        rewrite /sem_val_typed /=. iDestruct "HA" as "#HA". iDestruct "HI" as "#HI".
        rewrite /sem_ty_arr /sem_ty_mbang /=.
        iDestruct ("HA" with "HI") as "$". }
    set (f := λ v : val, if bool_decide (v = #true) then 1 else 0).
    set (g := λ v : val, if bool_decide (v = #false) then 1 else 0).
    assert (∀ a, 0 <= f a <= 1) as Hf by (intros a; rewrite /f; case_bool_decide; lra).
    assert (∀ a, 0 <= g a <= 1) as Hg by (intros a; rewrite /g; case_bool_decide; lra).
    have Hfg : ∀ a b' : val, (∃ b : bool, a = #b ∧ b' = #(negb b))%type → f a <= g b'.
    { intros a b' (b & -> & ->). rewrite /f /g. destruct b; simpl; repeat case_bool_decide;
        simplify_eq; lra. }
    specialize (Hc f g Hf Hg Hfg).
    rewrite Rplus_0_r in Hc.
    rewrite (SeriesC_ext _ (λ v, if bool_decide (v = #true)
                                then lim_exec (SCHED_LEAK x0 x1 c (F_TO_H ⊳ S)%md, σ) v else 0))
      in Hc.
    2: { intros v. rewrite /f. case_bool_decide; lra. }
    rewrite (SeriesC_ext (λ v, _ * g v) (λ v, if bool_decide (v = #false)
                                then lim_exec (SCHED_LEAK x0 x1 (negb c) (F_TO_H ⊳ S)%md, σ) v
                                else 0)) in Hc.
    2: { intros v. rewrite /g. case_bool_decide; lra. }
    by rewrite !SeriesC_singleton_dependent in Hc.
  Qed.

  (* The mutant does not realise the ideal transfer: with every typed
     simulator, the environment for one of the two choices has advantage
     at least [1/2]. *)
  Theorem to_h_leak_insecure (S : val) (x0 x1 : bool) :
    (∀ `{!probblazeRGS Σ}, ⊢ ⊨ᵥ S ≤ S : Mod TOHNetL TOHAdv) →
    ∃ c : bool, 1/2 <= advantage (SCHED_LEAK x0 x1 c) HYB_TO_H_LEAK (F_TO_H ⊳ S)%md #true.
  Proof.
    intros HS.
    set (σ := @inhabitant state state_inhabited).
    set (p c := lim_exec (SCHED_LEAK x0 x1 c (F_TO_H ⊳ S)%md, σ) #true).
    (* [p true + p false <= 1] *)
    have Hneg := sched_leak_ideal_neg S x0 x1 true σ HS.
    have Hsum := pmf_two (lim_exec (SCHED_LEAK x0 x1 false (F_TO_H ⊳ S)%md, σ))
                   #true #false ltac:(done).
    have Hd : ∀ c, 1 - p c <= advantage (SCHED_LEAK x0 x1 c) HYB_TO_H_LEAK (F_TO_H ⊳ S)%md #true.
    { intros c. etrans; last apply pr_dist_le_advantage.
      rewrite /pr_dist /= sched_leak_real. apply Rle_abs. }
    destruct (Rle_dec (p true) (1/2)).
    - exists true. etrans; last apply Hd. lra.
    - exists false. etrans; last apply Hd. apply Rnot_le_lt in n.
      rewrite /p /= in n Hneg Hsum |- *. lra.
  Qed.

End ot_rev_leak_adequacy.
