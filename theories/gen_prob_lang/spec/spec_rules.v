(** Rules for updating the specification program ([gen_prob_lang]).

    Ported from [prob_lang/spec/spec_rules.v].  The generic, non-sampling rules
    (pure steps, heap alloc/load/store) are unchanged modulo the [gen_prob_lang]
    imports.  The per-distribution sampling rules ([step_rand], [step_randnat],
    [step_alloctape_laplace], [step_laplace]) are replaced by the two generic
    analogues [step_alloc_sample_tape] and [step_sample_tape], built on the
    single generic spec tape map provided by [spec_ra.v]. *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.common Require Import language.
From clutch.gen_prob_lang Require Import lang notation tactics exec_lang.
From clutch.gen_prob_lang.spec Require Export spec_ra.

(** [gen_prob_lang]'s tactics file does not provide [solve_step] (there is no
    canonical [language] structure to pin it to), so we define it locally,
    mirroring [prob_lang/tactics.v]. *)
#[local] Ltac solve_step :=
  simpl;
  match goal with
  | |- (prim_step _ _).(pmf) _ = 1%R  =>
      rewrite head_prim_step_eq /= ;
        simplify_map_eq ; solve_distr
  | |- (head_step _ _ _).(pmf) _ = 1%R  => simplify_map_eq; solve_distr
  | |- (head_step _ _ _).(pmf) _ > 0%R  => eauto with head_step
  end.

Section rules.
  Context (S : Sig).
  Context `{!specG_prob_lang Σ, invGS_gen hasLc Σ}.
  Notation Λ := (gen_lang S).
  (* Pin [fill] to the [gen_prob_lang] evaluation contexts (there is no canonical
     [ectxLanguage] structure to infer it from).  We use the [ectxLanguage] of
     [gen_lang S] so that the [ectx_lang_ctx] [LanguageCtx] instance applies. *)
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang S)).
  (* Pin the spec-update modality to the markov chain of [gen_lang S]; the
     signature [S] is otherwise phantom in the proposition argument. *)
  Local Notation spec_update :=
    (@spec_update (lang_markov (gen_lang S)) Σ _ _ _).
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

  (** Pure reductions *)
  Lemma step_pure E K e e' (P : Prop) n:
    P →
    @PureExec Λ P n e e' →
    ⤇ fill K e ⊢ spec_update E (⤇ fill K e').
  Proof.
    iIntros (HP Hex) "HK". rewrite spec_update_unseal.
    iIntros ([??]) "Hs".
    iDestruct (spec_auth_prog_agree with "[$] [$]") as "->".
    iMod (spec_update_prog (fill K e') with "[$][$]") as "[HK Hs]".
    iModIntro. iExists _, n. iFrame. iPureIntro.
    eapply (@stepN_PureExec_ctx S (fill K) (ectx_lang_ctx K) P 0 n); [done|done|].
    rewrite dret_1_1 //.
  Qed.

  (** Alloc, load, and store *)
  Lemma step_alloc E K e v :
    @IntoVal Λ e v →
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
    eapply (@stepN_det_step_ctx S (fill K) (ectx_lang_ctx K)); last first.
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
    eapply (@stepN_det_step_ctx S (fill K) (ectx_lang_ctx K)); last first.
    { by apply dret_1_1. }
    solve_step.
  Qed.

  Lemma step_store E K l v' e v:
    @IntoVal Λ e v →
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
    eapply (@stepN_det_step_ctx S (fill K) (ectx_lang_ctx K)); last first.
    { by apply dret_1_1. }
    solve_step.
  Qed.

  (** Generic sample-tape allocation.  [AllocSampleTape i (Val pv)]
      deterministically allocates a fresh, empty tape with descriptor
      [(i, pv, [])]. *)
  Lemma step_alloc_sample_tape E K (i : nat) (pv : val) :
    ⤇ fill K (AllocSampleTape i (Val pv)) ⊢
      spec_update E (∃ l, ⤇ fill K (#lbl:l) ∗ l ↪ₛ (i, pv, [])).
  Proof.
    iIntros "HK". rewrite spec_update_unseal.
    iIntros ([? σ]) "Hs".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "->".
    iMod (spec_update_prog (fill K #(LitLbl (fresh_loc σ.(stapes)))) with "[$] [$]") as "[Hauth Hj]".
    iMod (spec_auth_tape_alloc with "Hauth") as "[Hauth Hl]".
    iModIntro. iExists _, 1. iFrame.
    iPureIntro.
    eapply (@stepN_det_step_ctx S (fill K) (ectx_lang_ctx K)); last first.
    { by apply dret_1_1. }
    solve_step. by apply dret_1_1.
  Qed.

  (** Generic labelled sampling on a non-empty tape.  When the tape descriptor
      [(i, pv, ·)] matches the sampling arguments and the tape has a head value
      [x], the step deterministically consumes [x]. *)
  Lemma step_sample_tape E K (i : nat) (pv x : val) (xs : list val) l :
    ⤇ fill K (Sample i (Val pv) (Val #lbl:l)) ∗ l ↪ₛ (i, pv, x :: xs)
      ⊢ spec_update E (⤇ fill K (Val x) ∗ l ↪ₛ (i, pv, xs)).
  Proof.
    iIntros "[HK Hl]". rewrite spec_update_unseal.
    iIntros ([? σ]) "Hs".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "->".
    iMod (spec_update_prog (fill K (Val x)) with "[$] [$]") as "[Hauth Hj]".
    iDestruct (spec_auth_lookup_tape with "Hauth Hl") as %?.
    iMod (spec_auth_update_tape (i, pv, xs) with "Hauth Hl") as "[Hauth $]".
    iModIntro. iExists (fill K (Val x), (state_upd_stapes <[l:=(i, pv, xs)]> σ)), 1.
    iFrame.
    iPureIntro.
    eapply (@stepN_det_step_ctx S (fill K) (ectx_lang_ctx K)); last first.
    { by apply dret_1_1. }
    solve_step. case_bool_decide as Hd; [|destruct Hd; done].
    by apply dret_1_1.
  Qed.

End rules.
