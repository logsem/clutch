(** Core relational rules (generic DP, [gen_prob_lang]).

    Ported from [diffpriv/app_rel_rules].  The structural / heap rules carry
    over verbatim once the relational ghost state is generalized to
    [diffprivRGS Sg Σ] and the [gen_lang Sg] canonical-structure chain is
    pinned in the section.

    The original file also contained a large family of [rand]/tape coupling
    rules ([refines_couple_*], [refines_rand*], [refines_alloctape_*]) built on
    the [prob_lang]-specific uniform-[rand] machinery and the [↪N]/[↪ₛN]
    rand-tape notation.  In [gen_prob_lang] sampling goes through an abstract
    distribution signature (one generic [stape] tape, coupled via the
    [coupling_rules]), there is no uniform [rand] operation, and the generalized
    type system carries NO sampling typing rule — so these rand-specific
    relational rules have no callers downstream ([compatibility]/[fundamental]
    have no sampling case) and no underlying lemmas to build on.  They are
    therefore omitted from this port. *)
From stdpp Require Import coPset namespaces.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list.
From clutch.common Require Import language ectx_language ectxi_language locations.
From clutch.prelude Require Import fin.
From clutch.gen_prob_lang.spec Require Import spec_ra spec_rules spec_tactics.
From clutch.diffpriv Require Import ectx_lifting weakestpre.
From clutch.gen_diffpriv Require Import model.
From clutch.gen_diffpriv Require Export proofmode primitive_laws coupling_rules.
From clutch.base_logic Require Export spec_update.
(* import gen_prob_lang.lang LAST so concrete expr/val/state shadow the
   [language] record projections re-exported transitively *)
From clutch.gen_prob_lang Require Import notation lang.

Section rules.
  Context (Sg : Sig).
  Let gen_markov_arr := lang_markov (gen_lang Sg).
  Context `{!diffprivRGS Sg Σ}.
  (* Pin the spec-update instance at [Sg] so the spec [tp_*] tactics and the
     [spec_update]-based RHS rules resolve their [spec_updateGS] obligation. *)
  #[local] Existing Instance spec_rules_spec_updateGS.
  #[local] Instance spec_updateGS_arr : spec_updateGS gen_markov_arr Σ :=
    spec_rules_spec_updateGS Sg.
  Implicit Types A : lrel Σ.
  Implicit Types e : expr.
  Implicit Types v w : val.

  (* Pin [fill] to the gen evaluation contexts (no global canonical language).
     We use the [ectx_language] [fill] (as in [coupling_rules]) so the spec
     [tp_*] tactics, whose [tp_bind_helper] matches on [@ectx_language.fill],
     fire.  It is definitionally equal to the [@ectxi_language.fill] used by
     [refines_def], so the bridge is by conversion. *)
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

  Local Existing Instance pure_exec_fill.

  (** * Primitive rules *)

  (** ([fupd_refines] is defined in [model.v]) *)

  (** ** Forward reductions on the LHS *)

  Lemma refines_pure_l E n
    (K' : list (@ectxi_language.ectx_item (gen_ectxi_lang Sg))) e e' t A ϕ :
    PureExec (Λ := gen_lang Sg) ϕ n e e' →
    ϕ →
    ▷^n (REL fill K' e' << t @ E : A)
    ⊢ REL fill K' e << t @ E : A.
  Proof.
    intros Hpure Hϕ.
    rewrite refines_eq /refines_def.
    iIntros "IH" (j ε) "Hs Hnais Herr Hpos".
    wp_pures.
    iApply ("IH" with "Hs Hnais Herr Hpos").
  Qed.

  Lemma refines_wp_l E K e1 t A :
    (WP e1 {{ v,
        REL fill K (of_val v) << t @ E : A }})%I
    ⊢ REL fill K e1 << t @ E : A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "He" (K' ε) "Hs Hnais Herr Hpos /=".
    iApply wp_bind.
    iApply (wp_wand with "He").
    iIntros (v) "Hv".
    iApply ("Hv" with "Hs Hnais Herr Hpos").
  Qed.

  Lemma refines_atomic_l (E E' : coPset) K e1 t A
    (Hatomic : Atomic (Λ := gen_lang Sg) StronglyAtomic e1) :
    (∀ K', ⤇ fill K' t ={⊤, E'}=∗
             WP e1 @ E' {{ v,
              |={E', ⊤}=> ∃ t', ⤇ fill K' t' ∗
              REL fill K (of_val v) << t' @ E : A }})%I
   ⊢ REL fill K e1 << t @ E : A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "Hlog" (K' ε) "Hs Hnais Herr Hpos /=".
    iApply wp_bind. iApply wp_atomic; auto.
    iMod ("Hlog" with "Hs") as "He". iModIntro.
    iApply (wp_wand with "He").
    iIntros (v) "Hlog".
    iMod "Hlog" as (t') "[Hr Hlog]".
    iApply ("Hlog" with "Hr Hnais Herr Hpos").
  Qed.

  (** ** Forward reductions on the RHS *)
  Lemma refines_pure_r E K' e e' t A n ϕ :
    PureExec (Λ := gen_lang Sg) ϕ n e e' →
    ϕ →
    (REL t << fill K' e' @ E : A)
      ⊢ REL t << fill K' e @ E : A.
  Proof.
    rewrite refines_eq /refines_def => Hpure Hϕ.
    iIntros "Hlog" (j ε) "Hj Hnais Herr Hpos /=".
    tp_pures ; auto.
    iApply ("Hlog" with "Hj Hnais Herr Hpos").
  Qed.

  (* A helper lemma for proving the stateful reductions for the RHS below *)
  Lemma refines_step_r E K' e1 e2 A :
    (∀ k, ⤇ fill k e2 -∗
         spec_update ⊤ (∃ v, ⤇ fill k (of_val v) ∗
                             REL e1 << fill K' (of_val v) @ E : A))
    ⊢ REL e1 << fill K' e2 @ E : A.
  Proof.
    rewrite refines_eq /refines_def /=.
    iIntros "He" (K'' ε) "Hs Hnais Herr Hpos /=".
    rewrite -fill_app.
    iMod ("He" with "Hs") as (v) "[Hs He]".
    rewrite fill_app.
    iSpecialize ("He" with "Hs Hnais Herr Hpos").
    by iApply "He".
  Qed.

  (* Variant of refines_step_r that doesn't require full evaluation. *)
  Lemma refines_steps_r E e1 e2 e2' A K' :
    (∀ K, (⤇ fill K e2 -∗ spec_update ⊤ (⤇ fill K e2')))
    ⊢ (|={⊤}=> refines E e1 (fill K' e2') A)
      -∗ refines E e1 (fill K' e2) A.
  Proof.
    iIntros "upd >Hlog".
    rewrite refines_eq /refines_def.
    iIntros (??) "???".
    simpl.
    rewrite -fill_app.
    iDestruct ("upd" with "[$]") as ">?".
    rewrite fill_app.
    iApply ("Hlog" with "[$][$][$]").
  Qed.

  Lemma refines_alloc_r E K e v t A :
    @IntoVal (gen_lang Sg) e v →
    (∀ l : loc, l ↦ₛ v -∗ REL t << fill K (of_val #l) @ E : A)%I
      ⊢ REL t << fill K (ref e) @ E : A.
  Proof.
    intros <-.
    iIntros "Hlog".
    iApply refines_step_r.
    iIntros (K') "HK'".
    tp_alloc as l "Hl".
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_load_r E K l q v t A :
    l ↦ₛ{q} v ⊢
      (l ↦ₛ{q} v -∗ REL t << fill K (of_val v) @ E : A)
    -∗ REL t << (fill K !#l) @ E : A.
  Proof.
    iIntros "Hl Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    tp_load.
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_store_r E K l e e' v v' A :
    @IntoVal (gen_lang Sg) e' v' →
    l ↦ₛ v ⊢
      (l ↦ₛ v' -∗ REL e << fill K (of_val #()) @ E : A)
    -∗ REL e << fill K (#l <- e') @ E : A.
  Proof.
    iIntros (<-) "Hl Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    tp_store. iModIntro. iExists _. iFrame.
    by iApply "Hlog".
  Qed.

  (** This rule is useful for proving that functions refine each other *)
  Lemma refines_arrow_val (v v' : val) A A' :
    □(∀ v1 v2, A v1 v2 -∗
      REL App v (of_val v1) << App v' (of_val v2) : A') ⊢
    REL (of_val v) << (of_val v') : (A → A')%lrel.
  Proof.
    iIntros "#H".
    iApply refines_ret. iModIntro.
    iModIntro. iIntros (v1 v2) "HA".
    iSpecialize ("H" with "HA").
    by iApply "H".
  Qed.

  (** * Some derived (symbolic execution) rules *)

  (** ** Stateful reductions on the LHS *)

  Lemma refines_alloc_l K E e v t A :
    @IntoVal (gen_lang Sg) e v →
    (▷ (∀ l : loc, l ↦ v -∗
           REL fill K (of_val #l) << t @ E : A))
    ⊢ REL fill K (ref e) << t @ E : A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_wp_l.
    wp_alloc l as "Hl". by iApply "Hlog".
  Qed.

  Lemma refines_load_l K E l q t A :
    (∃ v',
      ▷(l ↦{q} v') ∗
      ▷(l ↦{q} v' -∗ (REL fill K (of_val v') << t @ E : A)))
    ⊢ REL fill K (! #l) << t @ E : A.
  Proof.
    iIntros "[%v' [Hl Hlog]]".
    iApply refines_wp_l.
    wp_load. by iApply "Hlog".
  Qed.

  Lemma refines_store_l K E l e v' t A :
    @IntoVal (gen_lang Sg) e v' →
    (∃ v, ▷ l ↦ v ∗
      ▷(l ↦ v' -∗ REL fill K (of_val #()) << t @ E : A))
    ⊢ REL fill K (#l <- e) << t @ E : A.
  Proof.
    iIntros (<-) "[%v [Hl Hlog]]".
    iApply refines_wp_l.
    wp_store. by iApply "Hlog".
  Qed.

  Lemma refines_wand E e1 e2 A A' :
    (REL e1 << e2 @ E : A) ⊢
    (∀ v1 v2, A v1 v2 ={⊤}=∗ A' v1 v2) -∗
    REL e1 << e2 @ E : A'.
  Proof.
    iIntros "He HAA".
    iApply (refines_bind [] [] with "He").
    iIntros (v v') "HA /=". iApply refines_ret.
    by iApply "HAA".
  Qed.

  Lemma refines_arrow (v v' : val) A A' :
    □ (∀ v1 v2 : val, □(REL of_val v1 << of_val v2 : A) -∗
      REL App v (of_val v1) << App v' (of_val v2) : A') ⊢
    REL (of_val v) << (of_val v') : (A → A')%lrel.
  Proof.
    iIntros "#H".
    iApply refines_arrow_val; eauto.
    iModIntro. iIntros (v1 v2) "#HA".
    iApply "H". iModIntro.
    by iApply refines_ret.
  Qed.

  Lemma refines_get_ec E e e' A :
    (∀ ε : R, ↯ ε -∗ ⌜(0 < ε)%R⌝ -∗ REL e << e' @ E : A) ⊢
    (REL e << e' @ E : A).
  Proof.
    iIntros "H".
    rewrite refines_eq /refines_def.
    iIntros (K ε) "Hfill Hown Herr %Hpos".
    replace (ε) with (ε / 2 + ε / 2)%R by lra.
    iDestruct (ec_split with "Herr") as "[Herr1 Herr2]";
      [lra|lra|].
    iApply ("H" with "Herr1 [] Hfill Hown Herr2"); iPureIntro; lra.
  Qed.

  Lemma refines_ind_amp E e e' A (k : R) :
    (1 < k)%R ->
    □ (∀ (ε : R),
          ⌜(0 < ε)%R⌝ -∗ □(↯ (k * ε) -∗ (REL e << e' @ E : A))
          -∗ ↯ ε -∗ (REL e << e' @ E : A))%I
      ⊢ REL e << e' @ E : A.
  Proof.
    intros Hk.
    iIntros "#IH".
    iApply refines_get_ec.
    iIntros (ε) "Herr %Hpos".
    iApply (ec_ind_amp _ k with "[IH] Herr"); auto.
  Qed.

  Lemma refines_arrow_val_err (v v' : val) A A' k :
    (1 < k)%R ->
    □ (∀ ε,
          ⌜ (0 < ε)%R ⌝ -∗
          □ ( ↯ ((k * ε)) -∗ ∀ v1 v2, A v1 v2 -∗ REL App v (of_val v1) << App v' (of_val v2) : A' ) -∗
                ↯ ε -∗ ∀ v1 v2, A v1 v2 -∗ REL App v (of_val v1) << App v' (of_val v2) : A')
      ⊢ REL (of_val v) << (of_val v') : (A → A')%lrel.
  Proof.
    iIntros (Hk) "#H".
    iApply refines_ret. iModIntro.
    iModIntro.
    iIntros (v1 v2) "HA".
    iApply refines_get_ec.
    iIntros (ε') "Herr' %Hpos'".
    iRevert (v1 v2) "HA".
    by iApply (ec_ind_amp _ k); auto.
  Qed.

End rules.
