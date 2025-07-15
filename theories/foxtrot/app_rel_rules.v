(** Core relational rules *)
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import
     coq_tactics ltac_tactics
     reduction.
From clutch.prelude Require Import stdpp_ext.
From clutch.common Require Import con_language con_ectxi_language locations.
From clutch.con_prob_lang Require Import class_instances notation tactics lang.
From clutch.con_prob_lang.spec Require Export spec_tactics.
From clutch.foxtrot Require Import primitive_laws model proofmode.

Section rules.
  Context `{!foxtrotRGS Σ}.
  Implicit Types A : lrel Σ.
  Implicit Types e : expr.
  Implicit Types v w : val.

  Local Existing Instance pure_exec_fill.

  (** * Primitive rules *)

  (** ([fupd_refines] is defined in [logrel_binary.v]) *)

  (** ** Forward reductions on the LHS *)

  Lemma refines_pure_l E n
    (K' : list ectx_item) e e' t A ϕ :
    PureExec ϕ n e e' →
    ϕ →
    ▷^n (REL fill K' e' << t @ E : A)
    ⊢ REL fill K' e << t @ E : A.
  Proof.
    intros Hpure Hϕ.
    rewrite refines_eq /refines_def.
    iIntros "IH" (K j) "Hs Hnais".
    wp_pures.
    iApply ("IH" with "Hs Hnais").
  Qed.
  
  Lemma refines_wp_l E K e1 t A :
    (WP e1 {{ v,
        REL fill K (of_val v) << t @ E : A }})%I
    ⊢ REL fill K e1 << t @ E : A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "He" (K' j) "Hs Hnais".
    iApply wp_bind.
    iApply (wp_wand with "He").
    iIntros (v) "Hv".
    iApply ("Hv" with "Hs Hnais").
  Qed.

  Lemma refines_pure_r E K' e e' t A n ϕ :
    PureExec ϕ n e e' →
    ϕ →
    (REL t << fill K' e' @ E : A)
      ⊢ REL t << fill K' e @ E : A.
  Proof.
    rewrite refines_eq /refines_def => Hpure Hϕ.
    iIntros "Hlog" (? j) "Hj Hnais /=".
    tp_pures j; auto.
    iApply ("Hlog" with "Hj Hnais").
  Qed.

  Lemma refines_step_r E K' e1 e2 A :
    (∀ k j, j ⤇ fill k e2 -∗
         pupd E E (∃ v, j ⤇ fill k (of_val v) ∗
                             REL e1 << fill K' (of_val v) @ E : A))
    ⊢ REL e1 << fill K' e2 @ E : A.
  Proof.
    rewrite refines_eq /refines_def /=.
    iIntros "He" (? j) "Hs Hnais /=".
    rewrite -fill_app.
    iMod ("He" with "Hs") as (v) "[Hs He]".
    rewrite fill_app.
    iSpecialize ("He" with "Hs Hnais").
    by iApply "He".
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

  

  Lemma refines_alloc_l K E e v t A :
    IntoVal e v →
    (▷ (∀ l : loc, l ↦ v -∗
           REL fill K (of_val #l) << t @ E : A))
    ⊢ REL fill K (ref e) << t @ E : A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_wp_l.
    wp_alloc l as "Hl". by iApply "Hlog".
  Qed.

  Lemma refines_alloctape_l K E N z t A :
    TCEq N (Z.to_nat z) →
    (▷ (∀ α : loc, α ↪N (N; []) -∗ REL fill K (of_val #lbl:α) << t @ E : A))%I
    ⊢ REL fill K (alloc #z) << t @ E : A.
  Proof.
    iIntros (->) "Hlog".
    iApply refines_wp_l.
    by wp_apply (wp_alloc_tape with "[//]").
  Qed.
  
  Lemma refines_alloc_r E K e v t A :
    IntoVal e v →
    (∀ l : loc, l ↦ₛ v -∗ REL t << fill K (of_val #l) @ E : A)%I
      ⊢ REL t << fill K (ref e) @ E : A.
  Proof.
    intros <-.
    iIntros "Hlog". simpl.
    iApply refines_step_r ; simpl.
    iIntros (? j) "HK'".
    tp_alloc j as l "Hl".
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_alloctape_r E K N z t A :
    TCEq N (Z.to_nat z) →
    (∀ α : loc, α ↪ₛN (N; []) -∗ REL t << fill K (of_val #lbl:α) @ E : A)%I
    ⊢ REL t << fill K (alloc #z) @ E : A.
  Proof.
    iIntros (->) "Hlog".
    iApply refines_step_r.
    iIntros (K' j) "HK'".
    tp_allocnattape j α as "Hα".
    iModIntro. iExists _. iFrame.
    iApply "Hlog".
    iFrame; auto.
  Qed.
  
End rules.
