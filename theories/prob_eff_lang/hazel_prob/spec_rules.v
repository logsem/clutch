(** Rules for updating the specification program. *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.common Require Import locations language.
From clutch.prob_eff_lang.hazel_prob Require Import lang notation.
From clutch.prob_eff_lang.hazel_prob Require Import spec_ra exec_lang tactics.

Section rules.
  Context `{!specG_prob_eff_lang Σ, invGS_gen hasLc Σ}.
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
    eapply (stepN_PureExec_ctx  (K) P 0); [done|done|].
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
    eapply stepN_det_step_ctx; last first.
    { by apply dret_1_1. }
    simpl.
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
    eapply stepN_det_step_ctx; last first.
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
    eapply stepN_det_step_ctx; last first.
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
    eapply stepN_det_step_ctx; last first.
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
    eapply stepN_det_step_ctx; last first.
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


End rules.
