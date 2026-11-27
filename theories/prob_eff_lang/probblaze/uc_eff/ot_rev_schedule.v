(* An environment that schedules the parties of oblivious transfer
   reversal out of order, and the proof that under it both parties finish
   with the right outputs.

   The environment instantiates the hybrid world [HYB_TO_H] (Alice and Bob
   on the honest ideal OT and a channel) with adversarial operations that
   perform an effect [w], and runs each party's port under a handler that
   pauses the party at [w], returning its continuation.  It then runs:

     Bob's port        until he waits in the OT for Alice's choice;
     Alice's port      until she waits in the OT for Bob's messages;
     Bob, resumed      until he waits on the channel for Alice's message;
     Alice, resumed    until she has sent it and returns;
     Bob, resumed      until he returns [x_c].

   Neither order of nested calls achieves this: an environment whose
   adversarial operations are plain functions can only run the parties
   last-in-first-out, and then whichever party is called second waits for
   the first, which cannot run until the second returns.  The pausing
   handler is what lets the environment leave a party waiting, run the
   other, and come back.

   The results:
   - [sched_to_correct], [sched_to_completes]: on the hybrid world the run
     returns [true] with probability [1], for all inputs: both parties
     finish and Bob outputs [x_c].
   - [SCHED_ENV_typed]: the environment has the environments' type
     [Mod TOHNet TPorts → 𝔹], so the security theorem of the honest
     reversal covers it.
   - [sched_to_ideal_completes]: hence, by [to_h_security], the ideal world
     (the ideal transfer with its simulator) also completes under this
     schedule with Bob's output [x_c]. *)

From iris.proofmode Require Import base proofmode classes environments.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory semantics logic adequacy mode.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules auth ot ot_rev ot_rev_proof.

Import valgroup_tactics.

#[local] Set Default Proof Using "All".

Section ot_rev_schedule.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.

  (* The environment, for Alice's bits [(x0, x1)] and Bob's choice [c],
     given the world [W]: [true] when Bob's output is [x_c].  Every
     adversarial operation that a party waits in performs [w], whose
     signature is [𝟙 ⇒ 𝟙]; [run_s] pauses and then returns the sender's
     second-phase operation, which does not pause.  A party runs under a
     shallow handler for [w] that pauses it: the handler returns the
     party's result, or its continuation, which the environment resumes
     later under a new handler. *)
  Definition SCHED_ENV (x0 x1 c : bool) : val :=
    λ: "W",
      effect "w"
      let: "adv" := ((λ: <>, (do: "w" #()%V);; (λ: <>, #()%V), λ: <>, do: "w" #()%V),
                     (λ: <>, #()%V, λ: <>, do: "w" #()%V)) in
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
      match: "sB" with
        InjL "y" => if: "y" then #(if c then x1 else x0) else #(negb (if c then x1 else x0))
      | InjR <> => #false
      end.

  (* The run on the hybrid world: Alice and Bob on the honest ideal OT and
     a channel. *)
  Definition SCHED_TO (x0 x1 c : bool) : expr := SCHED_ENV x0 x1 c HYB_TO_H.

End ot_rev_schedule.

(* Handling an operation on the right, found under one or two frames
   outside the handler and up to eight inside it. *)
Ltac brel_handle_r_in Ko k Hk :=
  first
    [ iApply (brel_handle_os_r Ko [AppRCtx _])
    | iApply (brel_handle_os_r Ko [AppRCtx _; AppRCtx _])
    | iApply (brel_handle_os_r Ko [AppRCtx _; AppRCtx _; AppRCtx _])
    | iApply (brel_handle_os_r Ko [AppRCtx _; AppRCtx _; AppRCtx _; AppRCtx _])
    | iApply (brel_handle_os_r Ko [AppRCtx _; AppRCtx _; AppRCtx _; AppRCtx _; AppRCtx _])
    | iApply (brel_handle_os_r Ko
                [AppRCtx _; AppRCtx _; AppRCtx _; AppRCtx _; AppRCtx _; AppRCtx _])
    | iApply (brel_handle_os_r Ko
                [AppRCtx _; AppRCtx _; AppRCtx _; AppRCtx _; AppRCtx _; AppRCtx _; AppRCtx _])
    | iApply (brel_handle_os_r Ko
                [AppRCtx _; AppRCtx _; AppRCtx _; AppRCtx _; AppRCtx _; AppRCtx _; AppRCtx _;
                 AppRCtx _]) ];
  [ simpl; set_solver | iIntros (k) Hk ].

Ltac brel_handle_r k Hk :=
  first [ brel_handle_r_in open_constr:([AppRCtx _]) k Hk
        | brel_handle_r_in open_constr:([AppRCtx _; AppRCtx _]) k Hk ].

(* A sample on the right only, found in its evaluation context. *)
Lemma tac_brel_randU_r `{!probblazeRGS Σ} E K Δ eₛ eₜ N z X R :
  TCEq N (Z.to_nat z) →
  IntoCtx eₜ (TCEq (rand #z)%E) K →
  envs_entails Δ (∀ n : nat, ⌜n ≤ N⌝ -∗ brel E eₛ (fill K (Val #n)) X R) →
  envs_entails Δ (brel E eₛ eₜ X R).
Proof.
  rewrite envs_entails_unseal. intros HN [e' -> <-] H. rewrite H.
  iIntros "H". iApply brel_randU_r. iIntros (n Hn). by iApply "H".
Qed.

Tactic Notation "brel_sample_r" :=
  iStartProof; eapply tac_brel_randU_r; [tc_solve|tc_solve|simpl].

Section ot_rev_schedule_proof.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.

  Lemma sched_to_correct (x0 x1 c : bool) :
    ⊢ BREL #true ≤ SCHED_TO x0 x1 c <|⊥|> {{ λ v1 v2, ⌜v1 = v2⌝ }}.
  Proof.
    rewrite /SCHED_TO /SCHED_ENV. brel_pures_r.
    brel_effect_r w as "Hw".
    rewrite /HYB_TO_H /comp_op /tens_op /PARTIES_TO /F_OT_H /F_OAUTH /TO_S /TO_R
      /bxor /ungbit /gbit /ot_rev.flip is_unit.
    brel_pures_r. brel_alloc_r ch as "Hch". brel_pures_r. brel_alloc_r mm as "Hmm". brel_pures_r.
    brel_alloc_r box as "Hbox". brel_pures_r.
    (* Bob, until he waits in the OT for Alice's choice. *)
    brel_handle_r kB "HkB". brel_pures_r.
    destruct x0, x1, c;
      ((* Alice, until she waits in the OT for Bob's messages. *)
       brel_pures_r; brel_store_r; brel_pures_r; brel_handle_r kA "HkA"; brel_pures_r;
       (* Bob, resumed: Alice has chosen; his mask, his OT messages, and his
          wait on the channel. *)
       brel_cont_r; brel_pures_r; brel_load_r; brel_pures_r;
       brel_sample_r; iIntros (k Hk);
       assert (k = 0%nat ∨ k = 1%nat)%type as [-> | ->] by (simpl in Hk; lia);
       brel_pures_r; brel_store_r; brel_pures_r; brel_handle_r kB2 "HkB2"; brel_pures_r;
       (* Alice, resumed: her OT output, and her message. *)
       brel_cont_r; brel_pures_r; brel_load_r; brel_pures_r;
       brel_eq_r; rewrite ?bd_gg ?bd_1g; brel_pures_r; brel_store_r; brel_pures_r;
       (* Bob, resumed: Alice's message, and his output. *)
       brel_cont_r; brel_pures_r; brel_load_r; brel_pures_r;
       by iModIntro).
  Qed.

End ot_rev_schedule_proof.

Section ot_rev_schedule_typing.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.

  (* The signature of [w] inside the handlers, one-shot, and the row the
     world is instantiated at. *)
  Definition σw (l1 l2 : label) : sem_sig Σ := (¡ (sem_sig_eff l1 l2 (λ _, 𝟙%T) (λ _, 𝟙%T)))%S.
  Definition θw (l1 l2 : label) : sem_row Σ := (σw l1 l2 · ⟨⟩)%R.

  (* A label just allocated has the bottom signature: no operation, so
     one-shot. *)
  Global Instance sig_bottom_once (l1 l2 : label) : OnceS (sem_sig_bottom l1 l2 : sem_sig Σ).
  Proof.
    constructor. rewrite /sem_sig_flip_mbang. iSplit; first done.
    iIntros (e1 e2 Φ) "!# H". simpl. iDestruct "H" as (Q) "[H _]".
    iDestruct "H" as (αs v1 v2 -> ->) "[[] _]".
  Qed.

  (* The ports run at [¡θ], inside a handler whose body runs at [θ]. *)
  Lemma row_le_flip_θw l1 l2 : ⊢ (¡ (θw l1 l2))%R ≤ᵣ θw l1 l2.
  Proof. rewrite /θw /σw. apply row_le_mfbang_elim. Qed.

  Lemma do_w_typed (l1 l2 : label) Γ :
    ⊢ sem_typed Γ (do: l1 #()%V) (do: l2 #()%V) (θw l1 l2) 𝟙 Γ.
  Proof.
    iApply (sem_typed_do OS 𝟙%T ⟨⟩%R (l1, l2) (λ _, 𝟙%T) (λ _, 𝟙%T)).
    iApply sem_typed_sub; [iApply env_le_refl|iApply env_le_refl|iApply row_le_nil|iApply ty_le_refl|].
    iApply sem_typed_unit.
  Qed.

  (* The adversarial operations: the ones a party waits in perform [w]. *)
  Lemma adv_typed (l1 l2 : label) Γ :
    ⊢ sem_typed Γ
        ((λ: <>, (do: l1 #()%V);; (λ: <>, #()%V), λ: <>, do: l1 #()%V),
         (λ: <>, #()%V, λ: <>, do: l1 #()%V))
        ((λ: <>, (do: l2 #()%V);; (λ: <>, #()%V), λ: <>, do: l2 #()%V),
         (λ: <>, #()%V, λ: <>, do: l2 #()%V))
        ⟨⟩ (TOHNet (θw l1 l2)) Γ.
  Proof.
    rewrite /TOHNet /OTHAdv /LNet.
    iApply sem_typed_pair; iApply sem_typed_pair.
    - (* deliver *)
      iApply (sem_typed_oval _ []). iApply sem_oval_typed_ufun; [set_solver|set_solver|done|]. simpl.
      iApply do_w_typed.
    - (* leak *)
      iApply (sem_typed_oval _ []). iApply sem_oval_typed_ufun; [set_solver|set_solver|done|]. simpl.
      iApply sem_typed_sub; [iApply env_le_refl|iApply env_le_refl|iApply row_le_nil|iApply ty_le_refl|].
      iApply sem_typed_unit.
    - (* run_r *)
      iApply (sem_typed_oval _ []). iApply sem_oval_typed_afun; first set_solver. simpl.
      iApply sem_typed_sub; [iApply env_le_refl|iApply env_le_refl|iApply row_le_mfbang_intro
                            |iApply ty_le_refl|].
      iApply do_w_typed.
    - (* run_s *)
      iApply (sem_typed_oval _ []). iApply sem_oval_typed_afun; first set_solver. simpl.
      iApply sem_typed_seq.
      + iApply sem_typed_sub; [iApply env_le_refl|iApply env_le_refl|iApply row_le_mfbang_intro
                              |iApply ty_le_refl|].
        iApply do_w_typed.
      + iApply sem_typed_sub; [iApply env_le_refl|iApply env_le_refl|iApply row_le_nil
                              |iApply ty_le_refl|].
        iApply (sem_typed_oval _ []). iApply sem_oval_typed_afun; first set_solver. simpl.
        iApply sem_typed_sub; [iApply env_le_refl|iApply env_le_refl|iApply row_le_nil
                              |iApply ty_le_refl|].
        iApply sem_typed_unit.
  Qed.

  (* The row of the environment's body: the label of [w] just
     allocated, with the bottom signature outside the handlers. *)
  Definition ρw (l1 l2 : label) : sem_row Σ := (sem_sig_bottom l1 l2 · ⟨⟩)%R.

  Global Instance ρw_once (l1 l2 : label) : OnceR (ρw l1 l2).
  Proof. rewrite /ρw. eapply row_cons_once; [apply sig_bottom_once|apply row_nil_once]. Qed.

  (* A paused or finished run of a party with result [τ]. *)
  Definition St (l1 l2 : label) (τ : sem_ty Σ) : sem_ty Σ :=
    (τ + (𝟙 -{ θw l1 l2 }-[OS]-> τ))%T.

  Ltac solve_dom :=
    first
      [ by intros []
      | rewrite ?env_dom_cons ?env_dom_app ?env_dom_nil;
        repeat (apply not_elem_of_cons; split; [intros ?; simplify_eq|]);
        apply not_elem_of_nil ].

  Ltac lift_nil :=
    iApply sem_typed_sub;
    [iApply env_le_refl|iApply env_le_refl|iApply row_le_nil|iApply ty_le_refl|].

  (* A party's run under the pausing handler. *)
  Lemma pause_typed (l1 l2 : label) Γ1 τ e1 e2 :
    ⊢ sem_typed Γ1 e1 e2 (θw l1 l2) τ [] -∗
      sem_typed Γ1
        (handle: e1 with | effect l1 <>, "k" => InjR "k" | return "y" => InjL "y" end)
        (handle: e2 with | effect l2 <>, "k" => InjR "k" | return "y" => InjL "y" end)
        (ρw l1 l2) (St l1 l2 τ) [].
  Proof.
    iIntros "#He". iEval (rewrite -(app_nil_r Γ1)).
    iApply (sem_typed_shallow_handler_OS (l1, l2) (λ _, 𝟙%T) (λ _, 𝟙%T) τ (St l1 l2 τ)
              (sem_sig_bottom l1 l2) ⟨⟩%R Γ1 [] [] BAnon "y" "k");
      [done|done|solve_dom|done|solve_dom|solve_dom|done| | |].
    - rewrite /θw /σw. iApply "He".
    - iIntros (α). simpl. iApply sem_typed_injr. lift_nil. iApply sem_typed_var.
    - simpl. iApply sem_typed_injl. lift_nil. iApply sem_typed_var.
  Qed.

  (* Resuming a paused run, finished runs unchanged. *)
  Lemma resume_typed (l1 l2 : label) (s : string) τ :
    ⊢ sem_typed [(s, St l1 l2 τ)]
        (match: s with
           InjL "y" => InjL "y"
         | InjR "k" =>
             handle: "k" #()%V with | effect l1 <>, "k" => InjR "k" | return "y" => InjL "y" end
         end)
        (match: s with
           InjL "y" => InjL "y"
         | InjR "k" =>
             handle: "k" #()%V with | effect l2 <>, "k" => InjR "k" | return "y" => InjL "y" end
         end)
        (ρw l1 l2) (St l1 l2 τ) [].
  Proof.
    iApply (sem_typed_match_split [] [] τ (𝟙 -{ θw l1 l2 }-[OS]-> τ)%T (St l1 l2 τ) (ρw l1 l2)
              [(s, St l1 l2 τ)] [] [] [] [] [] [] "y" "k");
      [solve_dom|solve_dom|solve_dom|solve_dom| | | | | | |].
    - lift_nil. iApply sem_typed_var.
    - iApply env_le_refl.
    - simpl. iApply sem_typed_injl. lift_nil. iApply sem_typed_var.
    - iApply env_le_refl.
    - iApply env_le_refl.
    - simpl. iApply pause_typed.
      iApply (sem_typed_app_gen 𝟙%T ⟨⟩%R (θw l1 l2) (θw l1 l2) τ _ [("k", (𝟙 -{ θw l1 l2 }-[OS]-> τ)%T)] []).
      + iApply row_le_nil.
      + iApply row_le_refl.
      + iApply sem_typed_sub; [iApply env_le_refl|iApply env_le_refl|iApply row_le_refl
                              |iApply ty_le_mbang_elim|].
        iApply sem_typed_var.
      + lift_nil. iApply sem_typed_unit.
    - iApply env_le_refl.
  Qed.

  (* The environment is an environment of the honest reversal: it is
     related to itself at the environments' type. *)
  Lemma SCHED_ENV_typed (x0 x1 c : bool) :
    ⊢ ⊨ᵥ SCHED_ENV x0 x1 c ≤ SCHED_ENV x0 x1 c : (Mod TOHNet TPorts → 𝔹).
  Proof.
    rewrite /SCHED_ENV.
    iApply sem_typed_closure; first done. simpl.
    iApply sem_typed_effect_gen. iIntros (l1 l2). simpl.
    change (sem_sig_bottom l1 l2 · ⟨⟩)%R with (ρw l1 l2).
    set (θ := θw l1 l2).
    (* The adversarial operations. *)
    iApply (sem_typed_let (TOHNet θ) _ _ _ [("W", Mod TOHNet TPorts)]); [solve_dom|solve_dom| |].
    { lift_nil. iApply adv_typed. }
    simpl.
    (* The world, at the row [θ] of [w]. *)
    iApply (sem_typed_pair_elim (TSPort θ) _ (TPort θ) _ _ []);
      [solve_dom|solve_dom|solve_dom|solve_dom|done| |].
    { iApply (sem_typed_app_gen (TOHNet θ) ⟨⟩%R (ρw l1 l2) ⟨⟩%R (TSPort θ × TPort θ)%T _
                [("W", Mod TOHNet TPorts)] []).
      - iApply row_le_nil.
      - iApply row_le_nil.
      - iApply sem_typed_sub; [iApply env_le_refl|iApply env_le_refl|iApply row_le_refl
                              |iApply ty_le_mbang_elim|].
        rewrite /Mod /ModM. iApply (sem_typed_RApp (λ θ', (TOHNet θ' -[MS]-> TPorts θ')%T)).
        iApply sem_typed_var.
      - lift_nil. iApply sem_typed_var. }
    simpl.
    (* Bob, until he pauses. *)
    iApply (sem_typed_let (St l1 l2 𝔹) _ _ _ [("alice", TSPort θ)]); [solve_dom|solve_dom| |].
    { iApply (sem_typed_frame_gen [("bob", TPort θ)] _ _ _ "alice" (TSPort θ) _ []).
      iApply pause_typed.
      iApply (sem_typed_app_gen 𝔹%T ⟨⟩%R θ (¡ θ)%R 𝔹%T _ [("bob", TPort θ)] []).
      - iApply row_le_nil.
      - iApply row_le_flip_θw.
      - iApply sem_typed_var.
      - lift_nil. iApply sem_typed_bool. }
    simpl.
    (* Alice, until she pauses. *)
    iApply (sem_typed_let (St l1 l2 𝟙) _ _ _ [("sB", St l1 l2 𝔹)]); [solve_dom|solve_dom| |].
    { iApply (sem_typed_frame_gen [("alice", TSPort θ)] _ _ _ "sB" (St l1 l2 𝔹) _ []).
      iApply pause_typed.
      iApply (sem_typed_app_gen (𝔹 × 𝔹)%T ⟨⟩%R θ (¡ θ)%R 𝟙%T _ [("alice", TSPort θ)] []).
      - iApply row_le_nil.
      - iApply row_le_flip_θw.
      - iApply sem_typed_var.
      - lift_nil. iApply sem_typed_pair; iApply sem_typed_bool. }
    simpl.
    (* Bob, Alice, Bob, resumed. *)
    iApply (sem_typed_let (St l1 l2 𝔹) _ _ _ [("sA", St l1 l2 𝟙)]); [solve_dom|solve_dom| |].
    { iApply (sem_typed_frame_gen [("sB", St l1 l2 𝔹)] _ _ _ "sA" (St l1 l2 𝟙) _ []).
      iApply resume_typed. }
    simpl.
    iApply (sem_typed_let (St l1 l2 𝟙) _ _ _ [("sB", St l1 l2 𝔹)]); [solve_dom|solve_dom| |].
    { iApply (sem_typed_frame_gen [("sA", St l1 l2 𝟙)] _ _ _ "sB" (St l1 l2 𝔹) _ []).
      iApply resume_typed. }
    simpl.
    iApply (sem_typed_let (St l1 l2 𝔹) _ _ _ [("sA", St l1 l2 𝟙)]); [solve_dom|solve_dom| |].
    { iApply (sem_typed_frame_gen [("sB", St l1 l2 𝔹)] _ _ _ "sA" (St l1 l2 𝟙) _ []).
      iApply resume_typed. }
    simpl.
    (* Bob's output against [x_c]; Alice's state is dropped. *)
    iApply (sem_typed_sub _ _ _ [("sA", St l1 l2 𝟙)]);
      [iApply env_le_refl|iApply env_le_nil|iApply row_le_refl|iApply ty_le_refl|].
    iApply (sem_typed_match_split [] [] 𝔹 (𝟙 -{ θ }-[OS]-> 𝔹)%T 𝔹 (ρw l1 l2)
              [("sB", St l1 l2 𝔹); ("sA", St l1 l2 𝟙)] [("sA", St l1 l2 𝟙)]
              [("sA", St l1 l2 𝟙)] [("sA", St l1 l2 𝟙)] [("sA", St l1 l2 𝟙)] [("sA", St l1 l2 𝟙)]
              [("sA", St l1 l2 𝟙)] "y" BAnon);
      [solve_dom|solve_dom|solve_dom|solve_dom| | | | | | |].
    - lift_nil. iApply sem_typed_var.
    - iApply env_le_refl.
    - simpl. iApply sem_typed_if.
      + lift_nil. iApply sem_typed_var.
      + lift_nil. iApply sem_typed_bool.
      + lift_nil. iApply sem_typed_bool.
    - iApply env_le_refl.
    - iApply env_le_refl.
    - simpl. lift_nil. iApply sem_typed_bool.
    - iApply env_le_refl.
  Qed.

End ot_rev_schedule_typing.

(* An advantage bounds the distance in every initial state. *)
Lemma pr_dist_le_advantage (A X Y : expr) (v : val) σ :
  (nonneg (pr_dist (A X) (A Y) σ σ v) <= advantage A X Y v)%R.
Proof.
  rewrite /advantage /= /advantage_R. destruct completeness as [x [ub lub]]. simpl.
  apply ub. by exists σ.
Qed.

Section brel_lim_exec.
  Context `{Hpre : probblazeRGpreS Σ}.
  #[local] Open Scope R_scope.

(* A program that is related to a value [v], with equal results, returns
   [v] with probability [1]. *)
Lemma brel_lim_exec_1 (e : expr) (v : val) σ :
  (∀ `{!probblazeRGS Σ}, ⊢ BREL v ≤ e <|⊥|> {{ λ v1 v2, ⌜v1 = v2⌝ }}) →
  lim_exec (e, σ) v = 1.
Proof.
  intros Hrel.
  assert (ARcoupl (lim_exec (Val v, σ)) (lim_exec (e, σ)) (λ v1 v2, v1 = v2) 0) as Hc.
  { apply (brel_refines_coupling Σ (λ _ v1 v2, ⌜v1 = v2⌝)%I).
    - iIntros (? v1 v2) "$".
    - intros HRGS. iApply Hrel. }
  apply Rle_antisym; first apply pmf_le_1.
  set (f := λ w : val, if bool_decide (w = v) then 1 else 0).
  assert (∀ a, 0 <= f a <= 1) as Hf.
  { intros a. rewrite /f. case_bool_decide; lra. }
  specialize (Hc f f Hf Hf ltac:(by intros a b ->)).
  rewrite Rplus_0_r (lim_exec_final (Val v, σ) v) // in Hc.
  rewrite (SeriesC_ext (λ a, dret v a * f a) (λ a, if bool_decide (a = v) then 1 else 0))
    in Hc.
  2: { intros a. rewrite /f /pmf /= /dret_pmf. by repeat case_bool_decide; simplify_eq; lra. }
  rewrite SeriesC_singleton in Hc.
  rewrite (SeriesC_ext _ (λ b, if bool_decide (b = v) then lim_exec (e, σ) b else 0)) in Hc.
  2: { intros b. rewrite /f. case_bool_decide; lra. }
  by rewrite SeriesC_singleton_dependent in Hc.
Qed.

End brel_lim_exec.

Section ot_rev_schedule_adequacy.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  #[local] Open Scope R_scope.

  (* Under the schedule, the run terminates with Bob's output [x_c]
     with probability [1], for all inputs and from any state. *)
  Theorem sched_to_completes (x0 x1 c : bool) σ :
    lim_exec (SCHED_TO x0 x1 c, σ) #true = 1.
  Proof. apply brel_lim_exec_1. intros HRGS. iApply sched_to_correct. Qed.

  (* The environment is one the security theorem of the honest reversal
     covers, so the ideal world, the ideal transfer with its simulator,
     completes under the same schedule with the same outputs. *)
  Theorem sched_to_ideal_completes (x0 x1 c : bool) σ :
    lim_exec (SCHED_ENV x0 x1 c IDEAL_TO_H, σ) #true = 1.
  Proof.
    have Hadv := @to_h_security vg cg vgg Σ Hpre G (SCHED_ENV x0 x1 c)
                   (λ HRGS, SCHED_ENV_typed (G := G HRGS) x0 x1 c).
    have Hd := pr_dist_le_advantage (SCHED_ENV x0 x1 c) HYB_TO_H IDEAL_TO_H #true σ.
    specialize (Hadv vgg). specialize (Hd vg cg vgg vg cg vgg).
    have Hreal := sched_to_completes x0 x1 c σ. rewrite /SCHED_TO in Hreal.
    rewrite /pr_dist /= Hreal in Hd.
    have Habs : Rabs (1 - lim_exec (SCHED_ENV x0 x1 c IDEAL_TO_H, σ) #true) = 0.
    { simpl in Hadv. apply Rle_antisym; [etrans; [exact Hd|exact Hadv]|apply Rabs_pos]. }
    revert Habs. rewrite /Rabs. destruct (Rcase_abs _); lra.
  Qed.

End ot_rev_schedule_adequacy.
