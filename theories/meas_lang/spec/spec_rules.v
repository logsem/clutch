(** Rules for updating the specification program. *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.meas_lang Require Import lang notation tactics exec_lang.
From clutch.meas_lang Require Import language ectxi_language.
From clutch.meas_lang.lang Require Import types.
From clutch.meas_lang.spec Require Export spec_ra.

  Context `{!measG_prob_lang Σ, invGS_gen hasLc Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val_T → iProp Σ.
  (* Implicit Types σ : state_T. *)
  Implicit Types e : expr_T.
  Implicit Types v : val_T.
  Implicit Types l : loc.


  (* If I make the terms be of type
      ectxi_language.exprT lang.meas_ectxi_lang
    then I can state fill but not PureExec.

    If I make the terms be of type
      lang.exprT meas_lang
    I can state PureExec but not fill.

    The same situation arises in Approxis, but there, Rocq is able to realize that the types are the same.
    Why not here?

    I can try making them be of type
      types.expr,
    the unerlying type, just like how it's done in Approxis, but then I get

      > Error: The term "expr" has type "measure.Measurable.type (measure.sigma_display expr_cyl)"
      > which should be Set, Prop or Type.

    This is despite the fact that
      Check measure.Measurable.type
      > measure.Measurable.type : measure.measure_display → Type
    Rocq is not convinced that this Type is a Type.


    I can try using the types used for the cylinder constuction
      expr_T.
    Rocq understand that this type is a type, but PureExec expects it to
    have type
      measure.Measurable.sort (language.expr ?Λ)

    I can try changing PureExec to not use e, but use toPacked of e,
      but I get the error

      The term "toPacked e" has type "measure.Measurable.sort (toPackedType ?d expr_T)"
      while it is expected to have type
      "measure.Measurable.sort (language.expr ?Λ)".

    I can try specializing Λ to be be meas_lang perhaps?

   *)

  (** Pure reductions *)
  Lemma step_pure E K e e' (P : Prop) n:
    P →
    PureExec P n e e' →
    ⤇ fill K e ⊢ spec_update E (⤇ fill K e').
  Proof.
    iIntros (HP Hex) "HK". rewrite spec_update_unseal.
    iIntros ([??]) "Hs".
    iDestruct (spec_auth_prog_agree with "[$] [$]") as "->".
    iMod (spec_update_prog (fill K e') with "[$][$]") as "[HK Hs]".
    iModIntro. iExists _, n. iFrame. iPureIntro.
    eapply (stepN_PureExec_ctx  (fill K) P 0); [done|done|].
    rewrite dret_1_1 //.
  Qed.

  (*
  (** Alloc, load, and store *)
  Lemma step_alloc E K e v :
    IntoVal e v →
    ⤇ fill K (ref e) ⊢ spec_update E (∃ l, ⤇ fill K (#l) ∗ l ↦ₛ v).
  Proof.
    iIntros (<-) "HK". rewrite spec_update_unseal.
    iIntros ([? σ]) "Hs".
    iDestruct (spec_auth_prog_agree with "[$] [$]") as "->".
    iMod (spec_auth_heap_alloc with "Hs") as "[Hs Hl]".
    iMod (spec_update_prog (fill K _) with "[$][$]") as "[HK Hs]".
    iModIntro. iExists (fill K _, _), 1.
    iFrame "HK".
    iSplit; last first.
    { iExists _. iFrame. }
    iPureIntro.
    eapply stepN_det_step_ctx; [apply _| |]; last first.
    { by apply dret_1_1. }
    solve_step.
    apply dret_1_1.
    rewrite state_upd_heap_singleton //.
  Qed.

  Lemma step_load E K l q v:
    ⤇ fill K (!#l) ∗ l ↦ₛ{q} v
    ⊢ spec_update E (⤇ fill K (of_val v) ∗ l ↦ₛ{q} v).
  Proof.
    iIntros "[HK Hl]". rewrite spec_update_unseal.
    iIntros ([? σ]) "Hs".
    iDestruct (spec_auth_prog_agree with "[$] [$]") as "->".
    iMod (spec_update_prog (fill K v) with "[$][$]") as "[Hauth Hj]".
    iDestruct (spec_auth_lookup_heap with "Hauth Hl") as %?.
    iModIntro. iExists _, 1. iFrame.
    iPureIntro.
    eapply stepN_det_step_ctx; [apply _| |]; last first.
    { by apply dret_1_1. }
    solve_step.
  Qed.

  Lemma step_store E K l v' e v:
    IntoVal e v →
    ⤇ fill K (#l <- e) ∗ l ↦ₛ v'
    ⊢ spec_update E (⤇ fill K #() ∗ l ↦ₛ v).
  Proof.
    iIntros (<-) "[HK Hl]". rewrite spec_update_unseal.
    iIntros ([? σ]) "Hs".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "->".
    iMod (spec_update_prog  (fill K #()) with "[$][$]") as "[Hauth Hj]".
    iDestruct (spec_auth_lookup_heap with "Hauth Hl") as %?.
    iMod (spec_auth_update_heap with "Hauth Hl") as "[Hauth $]".
    iModIntro. iExists (fill K #(), state_upd_heap <[l:=v]> σ), 1.
    iFrame. iPureIntro.
    eapply stepN_det_step_ctx; [apply _| |]; last first.
    { by apply dret_1_1. }
    solve_step.
  Qed.

  (** AllocTape and Rand (non-empty tape)  *)
  Lemma step_alloctape E K N z :
    TCEq N (Z.to_nat z) →
    ⤇ fill K (alloc #z) ⊢ spec_update E (∃ l, ⤇ fill K (#lbl:l) ∗ l ↪ₛ (N; [])).
  Proof.
    iIntros (->) "HK". rewrite spec_update_unseal.
    iIntros ([? σ]) "Hs".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "->".
    iMod (spec_update_prog (fill K #(LitLbl (fresh_loc σ.(tapes)))) with "[$] [$]") as "[Hauth Hj]".
    iMod (spec_auth_tape_alloc with "Hauth") as "[Hauth Hl]".
    iModIntro. iExists _, 1. iFrame.
    iPureIntro.
    eapply stepN_det_step_ctx; [apply _| |]; last first.
    { by apply dret_1_1. }
    solve_step.
  Qed.

  Lemma step_rand E K l N z n ns :
    TCEq N (Z.to_nat z) →
    ⤇ fill K (rand(#lbl:l) #z) ∗ l ↪ₛ (N; n :: ns)
      ⊢ spec_update E (⤇ fill K #n ∗ l ↪ₛ (N; ns)).
  Proof.
    iIntros (->) "[HK Hl]". rewrite spec_update_unseal.
    iIntros ([? σ]) "Hs".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "->".
    iMod (spec_update_prog (fill K #n) with "[$] [$]") as "[Hauth Hj]".
    iDestruct (spec_auth_lookup_tape with "Hauth Hl") as %?.
    iMod (spec_auth_update_tape with "Hauth Hl") as "[Hauth $]".
    iModIntro. iExists (fill K #n, (state_upd_tapes <[l:=_]> σ)), 1.
    iFrame.
    iPureIntro.
    eapply stepN_det_step_ctx; [apply _| |]; last first.
    { by apply dret_1_1. }
    solve_step. case_bool_decide; [|lia]. by apply dret_1_1.
  Qed.


  (** AllocTape and Rand (nat tape)  *)
  Lemma step_allocnattape E K N z :
    TCEq N (Z.to_nat z) →
    ⤇ fill K (alloc #z) ⊢ spec_update E (∃ l, ⤇ fill K (#lbl:l) ∗ l ↪ₛN (N; [])).
  Proof.
    iIntros (->) "HK".
    iMod (step_alloctape with "HK") as (l) "(HK & Hl)".
    rewrite spec_update_unseal.
    iIntros ([? σ]) "Hs".
    iModIntro.
    iExists _,0. iFrame.
    iPureIntro.
    split; [|done].
    rewrite stepN_O //.
    by apply dret_1.
  Qed.


  Lemma step_randnat E K l N z n ns :
    TCEq N (Z.to_nat z) →
    ⤇ fill K (rand(#lbl:l) #z) ∗ l ↪ₛN (N; n :: ns)
      ⊢ spec_update E (⤇ fill K #n ∗ ⌜ n ≤ N ⌝ ∗ l ↪ₛN (N; ns)).
  Proof.
    iIntros (->) "[HK Hl]".
    iDestruct (read_spec_tape_head with "Hl") as (x xs) "(Hl&<-&Hcont)".
    iMod (step_rand with "[$HK $Hl]") as "(HK & Hl)".
    iDestruct ("Hcont" with "Hl") as "Hl".
    rewrite spec_update_unseal.
    iIntros ([? σ]) "Hs".
    iModIntro.
    iExists _,0. iFrame.
    iPureIntro.
    split; [| pose proof (fin_to_nat_lt x); lia].
    rewrite stepN_O //.
    by apply dret_1.
  Qed.

*)
End rules.
