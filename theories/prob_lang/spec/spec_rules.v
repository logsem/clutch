(** Rules for updating the specification program. *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.base_logic Require Import spec_update.
From clutch.prob_lang Require Import lang notation tactics metatheory exec_lang.
From clutch.prob_lang.spec Require Export spec_ra.

#[global] Instance spec_rules_spec_updateGS `{!specGS Σ} :
  spec_updateGS (lang_markov prob_lang) Σ := Spec_updateGS spec_auth.

Section rules.
  Context `{!specGS Σ, invGS_gen hasLc Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

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
    iFrame.
    iSplit; last first.
    { iExists _. iFrame. }
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

End rules.
