(** Compatibility rules (generic DP, [gen_prob_lang]).

    Ported from [diffpriv/compatibility].  The [refines_rand_tape] /
    [refines_rand_unit] compatibility lemmas are omitted: they build on the
    [prob_lang]-only uniform-[rand] coupling rules, which have no
    [gen_prob_lang] counterpart, and the generalized type system has no sampling
    typing rule, so [fundamental] never needs them. *)
From stdpp Require Import namespaces.
From clutch.gen_diffpriv Require Import primitive_laws proofmode model rel_tactics app_rel_rules.
From clutch.gen_prob_lang Require Import notation lang.

Section compatibility.
  (* [Sg] is introduced (implicitly) by the [diffprivRGS Sg Σ] generalization,
     mirroring [model]; this keeps [Sg] an *implicit* leading argument of the
     compatibility lemmas, so the positional applications in [fundamental]
     ([refines_seq (interp …)], [bin_log_related_app Δ Γ …]) line up. *)
  Context `{!diffprivRGS Sg Σ}.
  Canonical Structure gen_ectxi_lang_cmp := gen_ectxi_lang Sg.
  Canonical Structure gen_ectx_lang_cmp := gen_ectx_lang Sg.
  Canonical Structure gen_lang_cmp := gen_lang Sg.
  Canonical Structure gen_markov_cmp := lang_markov (gen_lang Sg).
  #[local] Existing Instance spec_rules_spec_updateGS.
  #[local] Instance spec_updateGS_cmp : spec_updateGS gen_markov_cmp Σ :=
    spec_rules_spec_updateGS Sg.
  Implicit Types e : expr.

  Local Ltac value_case :=
    try rel_pure_l; try rel_pure_r; rel_values.

  (* The standard [tp_store]/[tp_load] tactics route the spec evaluation
     context through [tp_bind_helper], whose [lazymatch] expects an
     [@ectx_language.fill]-headed term.  Here the spec redex sits at the top of
     the (empty) context introduced by [refines_atomic_l], which displays with
     the derived [@ectxi_language.fill] head, so [tp_bind_helper] does not fire.
     The context is empty, so the [tac_tp_*] bind premise is closed by
     [reflexivity] directly. *)
  Local Ltac tp_store' :=
    iStartProof;
    eapply tac_tp_store;
    [tc_solve | iAssumptionCore | reflexivity | tc_solve
    | simpl; reflexivity | iAssumptionCore | reduction.pm_reduce].
  Local Ltac tp_load' :=
    iStartProof;
    eapply tac_tp_load;
    [tc_solve | iAssumptionCore | reflexivity | iAssumptionCore
    | simpl; reflexivity | reduction.pm_reduce].

  Local Tactic Notation "rel_bind_ap" uconstr(e1) uconstr(e2) constr(IH) ident(v) ident(w) constr(Hvs) :=
    rel_bind_l e1;
    rel_bind_r e2;
    iApply (refines_bind with IH);
    iIntros (v w) (Hvs); simpl.

  Lemma refines_pair e1 e2 e1' e2' A B :
    (REL e1 << e1' : A) -∗
    (REL e2 << e2' : B) -∗
    REL (e1, e2) << (e1', e2') : A * B.
  Proof.
    iIntros "IH1 IH2".
    rel_bind_ap e2 e2' "IH2" v2 v2' "Hvv2".
    rel_bind_ap e1 e1' "IH1" v1 v1' "Hvv1".
    value_case.
    iExists _, _, _, _; eauto.
  Qed.

  Lemma refines_injl e e' τ1 τ2 :
    (REL e << e' : τ1) -∗
    REL InjL e << InjL e' : τ1 + τ2.
  Proof.
    iIntros "IH".
    rel_bind_ap e e' "IH" v v' "Hvv".
    value_case.
    iExists _,_ ; eauto.
  Qed.

  Lemma refines_injr e e' τ1 τ2 :
    (REL e << e' : τ2) -∗
    REL InjR e << InjR e' : τ1 + τ2.
  Proof.
    iIntros "IH".
    rel_bind_ap e e' "IH" v v' "Hvv".
    value_case.
    iExists _,_ ; eauto.
  Qed.

  Lemma refines_app e1 e2 e1' e2' A B :
    (REL e1 << e1' : A → B) -∗
    (REL e2 << e2' : A) -∗
    REL App e1 e2 << App e1' e2' : B.
  Proof.
    iIntros "IH1 IH2".
    rel_bind_ap e2 e2' "IH2" v v' "Hvv".
    rel_bind_ap e1 e1' "IH1" f f' "Hff".
    by iApply "Hff".
  Qed.

  Lemma refines_seq A e1 e2 e1' e2' B :
    (REL e1 << e1' : A) -∗
    (REL e2 << e2' : B) -∗
    REL (e1;; e2) << (e1';; e2') : B.
  Proof.
    iIntros "IH1 IH2".
    rel_bind_ap e1 e1' "IH1" v v' "#Hvv".
    repeat rel_pure_l. repeat rel_pure_r.
    done.
  Qed.

  Lemma refines_pack (A : lrel Σ) e e' (C : lrel Σ → lrel Σ) :
    (REL e << e' : C A) -∗
    REL e << e' : ∃ A, C A.
  Proof.
    iIntros "H".
    rel_bind_ap e e' "H" v v' "Hvv".
    value_case.
    iModIntro. iExists A. done.
  Qed.

  Lemma refines_forall e e' (C : lrel Σ → lrel Σ) :
    □ (∀ A, REL e << e' : C A) -∗
    REL (λ: <>, e)%V << (λ: <>, e')%V : ∀ A, C A.
  Proof.
    iIntros "#H".
    rel_values. iModIntro.
    iIntros (A ? ?) "_ !#".
    rel_rec_l. rel_rec_r. iApply "H".
  Qed.

Tactic Notation "rel_store_l_atomic" := rel_apply_l refines_store_l.

  Lemma refines_store e1 e2 e1' e2' A :
    (REL e1 << e1' : ref A) -∗
    (REL e2 << e2' : A) -∗
    REL e1 <- e2 << e1' <- e2' : ().
  Proof.
    iIntros "IH1 IH2".
    rel_bind_ap e2 e2' "IH2" w w' "IH2".
    rel_bind_ap e1 e1' "IH1" v v' "IH1".
    iDestruct "IH1" as (l l') "(% & % & Hinv)"; simplify_eq/=.
    iApply (refines_atomic_l _ _ _ []); simpl.
    iIntros (K') "Hr".
    iInv (logN .@ (l,l')) as (v v') "[Hv1 [>Hv2 #Hv]]" "Hclose".
    iModIntro.
    tp_store'.
    wp_store.
    iMod ("Hclose" with "[Hv1 Hv2 IH2]") as "_".
    { iNext; iExists _, _; simpl; iFrame. }
    iModIntro. iExists _. iFrame.
    value_case.
  Qed.

  Lemma refines_load e e' A :
    (REL e << e' : ref A) -∗
    REL !e << !e' : A.
  Proof.
    iIntros "H".
    rel_bind_ap e e' "H" v v' "H".
    iDestruct "H" as (l l' -> ->) "#H".
    iApply (refines_atomic_l _ _ _ []); simpl.
    iIntros (K') "Hr".
    iInv (logN .@ (l,l')) as (w w') "[Hw1 [>Hw2 #Hw]]" "Hclose"; simpl.
    iModIntro.
    tp_load'.
    wp_load.
    iMod ("Hclose" with "[Hw1 Hw2]") as "_".
    { iNext. iExists w,w'; by iFrame. }
    iModIntro. iExists _. iFrame.
    value_case.
  Qed.

End compatibility.
