(** Primitive ghost-state setup for the generic DP weakest precondition.
    Generalized from [clutch.diffpriv.primitive_laws]: the reusable WP core
    ([weakestpre]/[lifting]/[ectx_lifting]) is imported AS-IS and instantiated
    at [gen_lang S]; the only change here is collapsing the per-distribution
    tape ghost maps (tapes / tapes_laplace / …) into one generic [stape] map. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export ghost_map.
From clutch.base_logic Require Export error_credits_mult error_credits.
From clutch.diffpriv Require Export weakestpre ectx_lifting.
From clutch.gen_prob_lang Require Export class_instances.
From clutch.gen_prob_lang Require Import tactics lang notation metatheory.
From clutch.gen_prob_lang.spec Require Export spec_ra.
From iris.prelude Require Import options.

(* [S] is a phantom parameter that fixes the language [gen_lang S] so the WP's
   [Wp]/[diffprivWpGS] instance resolves (expr/val are S-independent, so S can't
   be recovered from the expression). *)
Class diffprivGS (Sg : Sig) Σ := HeapG {
  diffprivGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state: a heap and ONE generic sample-tape map *)
  diffprivGS_heap :: ghost_mapG Σ loc val;
  diffprivGS_tapes :: ghost_mapG Σ loc stape;
  diffprivGS_heap_name : gname;
  diffprivGS_tapes_name : gname;
  (* spec-side ghost state *)
  diffprivGS_spec :: specG_prob_lang Σ;
  (* error credits (multiplicative ε and additive δ) *)
  diffprivGS_error_eps :: ecmGS Σ;
  diffprivGS_error_del :: ecGS Σ;
}.

Class diffprivGpreS Σ := DiffprivGpreS {
  diffprivGpreS_iris  :: invGpreS Σ;
  diffprivGpreS_heap  :: ghost_mapG Σ loc val;
  diffprivGpreS_tapes :: ghost_mapG Σ loc stape;
  diffprivGpreS_spec  :: specGpreS Σ;
  diffprivGpreS_err_eps :: ecmGpreS Σ;
  diffprivGpreS_err_del :: ecGpreS Σ;
}.

Definition diffprivΣ : gFunctors :=
  #[invΣ;
    ghost_mapΣ loc val;
    ghost_mapΣ loc stape;
    specΣ;
    ecmΣ;
    ecΣ].
Global Instance subG_diffprivGPreS {Σ} : subG diffprivΣ Σ → diffprivGpreS Σ.
Proof. solve_inG. Qed.

Definition heap_auth `{diffprivGS Sg Σ} :=
  @ghost_map_auth _ _ _ _ _ diffprivGS_heap diffprivGS_heap_name.
Definition stapes_auth `{diffprivGS Sg Σ} :=
  @ghost_map_auth _ _ _ _ _ diffprivGS_tapes diffprivGS_tapes_name.
Definition mult_ec_supply `{diffprivGS Sg Σ} :=
  @ecm_supply _ diffprivGS_error_eps.
Definition add_ec_supply `{diffprivGS Sg Σ} :=
  @ec_supply _ diffprivGS_error_del.

(* The WP ghost-state instance, parametric in the distribution signature [S].
   The [spec_updateGS (lang_markov (gen_lang S))] obligation is discharged by
   [spec_rules_spec_updateGS S] from spec_ra. *)
Global Instance diffprivGS_irisGS `{!diffprivGS Sg Σ} :
  diffprivWpGS (gen_lang Sg) Σ := {
  diffprivWpGS_invGS := diffprivGS_invG;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ stapes_auth 1 σ.(stapes))%I;
  err_interp ε δ := ((mult_ec_supply ε) ∗ (add_ec_supply δ))%I;
}.

(* Pin the spec-update instance via the in-context [diffprivGS Sg]: the generic
   [spec_rules_spec_updateGS] is ∀S, so [spec_interp]/[spec_coupl]/[spec_update]
   on a (signature-independent) [cfg] otherwise leave [S] an evar.  Keying off
   the [diffprivGS Sg] hypothesis recovers [S] = [Sg] automatically, so no
   per-development [spec_updateGS] instance is needed. *)
Global Instance diffprivGS_spec_updateGS `{!diffprivGS Sg Σ} :
  spec_updateGS (lang_markov (gen_lang Sg)) Σ := spec_rules_spec_updateGS Sg.

(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ diffprivGS_heap diffprivGS_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Sample tapes (one generic tape map) *)
Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ stape _ _ diffprivGS_tapes diffprivGS_tapes_name l dq v)
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.

(** Sampling WP rules (parametric in the distribution signature [S]). *)
Section rules.
  Context `{!diffprivGS Sg Σ}.
  (* Fix the [gen_lang Sg] canonical-structure chain so the WP lemmas
     resolve: the [Wp] instance is keyed on [expr Λ]/[val Λ], and the
     ectx-lifting lemmas need [LanguageOfEctx ?Λ =?= gen_lang Sg]. *)
  Canonical Structure gen_ectxi_lang_Sg := gen_ectxi_lang Sg.
  Canonical Structure gen_ectx_lang_Sg := gen_ectx_lang Sg.
  Canonical Structure gen_lang_Sg := gen_lang Sg.

  (* Allocate a fresh sample tape for family [i] with parameter value [pv]. *)
  Lemma wp_alloc_sample_tape (i : nat) (pv : val) E s :
    {{{ True }}}
      AllocSampleTape i (Val pv) @ s; E
    {{{ (α : loc), RET (LitV (LitLbl α)); α ↪ (i, pv, []) }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1) "(Hh & Ht) !# /=".
    solve_red.
    iIntros "!>" (e2 σ2 Hs); inv_head_step.
    iMod (ghost_map_insert (fresh_loc σ1.(stapes)) (i, pv, []) with "Ht") as "[$ Hl]".
    { apply not_elem_of_dom, fresh_loc_is_fresh. }
    iFrame. iModIntro. by iApply "HΦ".
  Qed.

  (* Read the head presampled value off a tape (deterministic). *)
  Lemma wp_sample_tape (i : nat) (pv x : val) (xs : list val) (α : loc) E s :
    {{{ ▷ α ↪ (i, pv, x :: xs) }}}
      Sample i (Val pv) (Val (LitV (LitLbl α))) @ s; E
    {{{ RET x; α ↪ (i, pv, xs) }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1) "(Hh & Ht) !#".
    iDestruct (ghost_map_lookup with "Ht Hl") as %?.
    solve_red.
    iIntros "!>" (e2 σ2 Hs); inv_head_step.
    (* the index/param-mismatch branch is absurd (we own this very tape) *)
    2:{ exfalso. apply H1. done. }
    iMod (ghost_map_update (i, pv, xs) with "Ht Hl") as "[$ Hl]".
    iFrame. iModIntro. by iApply "HΦ".
  Qed.

  (* Direct (no-tape) probabilistic sampling from family [i] at parameter [pv].
     Reducibility comes from mass-1 ⟹ nonempty support ([SeriesC_gtz_ex]); the
     result is guaranteed to lie in the support of [μ = sig_sample Sg i pv]. *)
  Lemma wp_sample (i : nat) (pv : val) (μ : distr val) E s :
    sig_sample Sg i pv = Some μ →
    {{{ True }}}
      Sample i (Val pv) (Val (LitV LitUnit)) @ s; E
    {{{ (v : val), RET v; ⌜(μ v > 0)%R⌝ }}}.
  Proof.
    iIntros (Hμ Φ) "_ HΦ".
    iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1) "Hσ !#".
    iSplitR.
    { iPureIntro.
      destruct (SeriesC_gtz_ex μ (pmf_pos μ)) as [v Hv].
      { rewrite (sig_sample_mass _ _ _ _ Hμ); lra. }
      eexists (_, _). apply head_step_support_equiv_rel.
      by eapply SampleNoTapeS. }
    iIntros "!>" (e2 σ2 Hs). inv_head_step.
    iModIntro. iFrame. iApply ("HΦ" $! x). by iPureIntro.
  Qed.

  (** Heap rules (ported from [diffpriv/primitive_laws]; [Load]→[Deref]). *)
  Lemma wp_rec_löb E f x e Φ (Ψ : val → iProp Σ) :
    □ ( □ (∀ (v : val), Ψ v -∗ WP (rec: f x := e)%V v @ E {{ Φ }}) -∗
       ∀ (v : val), Ψ v -∗ WP (subst' x v (subst' f (rec: f x := e) e)) @ E {{ Φ }}) -∗
    ∀ (v : val), Ψ v -∗ WP (rec: f x := e)%V v @ E {{ Φ }}.
  Proof.
    iIntros "#Hrec". iLöb as "IH". iIntros (v) "HΨ".
    iApply lifting.wp_pure_step_later; first done.
    iNext. iApply ("Hrec" with "[] HΨ"). iIntros "!>" (w) "HΨ".
    iApply ("IH" with "HΨ").
  Qed.

  Lemma wp_alloc E v s :
    {{{ True }}} Alloc (Val v) @ s; E {{{ l, RET LitV (LitLoc l); l ↦ v }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1) "[Hh Ht] !#".
    solve_red.
    iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
    iMod ((ghost_map_insert (fresh_loc σ1.(heap)) v) with "Hh") as "[? Hl]".
    { apply not_elem_of_dom, fresh_loc_is_fresh. }
    iFrame.
    rewrite map_union_empty -insert_union_singleton_l.
    iFrame.
    iIntros "!>". by iApply "HΦ".
  Qed.

  Lemma wp_allocN_seq (N : nat) (z : Z) E v s :
    TCEq N (Z.to_nat z) →
    (0 < N)%Z →
    {{{ True }}}
      AllocN (Val $ LitV $ LitInt $ z) (Val v) @ s; E
    {{{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 N, (l +ₗ (i : nat)) ↦ v }}}.
  Proof.
    iIntros (-> Hn Φ) "_ HΦ".
    iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1) "[Hh Ht] !#".
    iSplit.
    { iPureIntro.
      rewrite /head_reducible.
      eexists.
      apply head_step_support_equiv_rel.
      econstructor; eauto.
      lia.
    }
    iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
    iMod ((ghost_map_insert_big _ _ with "Hh")) as "[$ Hl]".
    iIntros "!>". iFrame.
    iApply "HΦ".
    iInduction (H) as [ | ?] "IH" forall (σ1).
    - simpl.
      iSplit; auto.
      rewrite map_union_empty.
      rewrite loc_add_0.
      by rewrite big_sepM_singleton.
    - rewrite seq_S.
      rewrite heap_array_replicate_S_end.
      iPoseProof (big_sepM_union _ _ _ _ with "Hl") as "[H1 H2]".
      iApply big_sepL_app.
      iSplitL "H1".
      + iApply "IH".
        { iPureIntro. lia. }
        iApply "H1".
      + simpl. iSplit; auto.
        by rewrite big_sepM_singleton.
        Unshelve.
        {
          apply heap_array_map_disjoint.
          intros.
          apply not_elem_of_dom_1.
          by apply fresh_loc_offset_is_fresh.
        }
        apply heap_array_map_disjoint.
        intros.
        apply not_elem_of_dom_1.
        rewrite dom_singleton.
        apply not_elem_of_singleton_2.
        intros H2.
        apply loc_add_inj in H2.
        rewrite length_replicate in H1.
        lia.
  Qed.

  Lemma wp_deref E l dq v s :
    {{{ ▷ l ↦{dq} v }}} Deref (Val $ LitV $ LitLoc l) @ s; E {{{ RET v; l ↦{dq} v }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1) "[Hh Ht] !#".
    iDestruct (ghost_map_lookup with "Hh Hl") as %?.
    solve_red.
    iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
    iFrame. iModIntro. by iApply "HΦ".
  Qed.

  Lemma wp_store E l v' v s :
    {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
    {{{ RET LitV LitUnit; l ↦ v }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1) "[Hh Ht] !#".
    iDestruct (ghost_map_lookup with "Hh Hl") as %?.
    solve_red.
    iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
    iMod (ghost_map_update with "Hh Hl") as "[$ Hl]".
    iFrame. iModIntro. by iApply "HΦ".
  Qed.

End rules.
