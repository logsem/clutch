(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Core ReLoC rules *)
From stdpp Require Import coPset namespaces.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list.
From self.program_logic Require Import ectx_lifting.
From self.prob_lang Require Import lang spec_rules spec_tactics proofmode.
From self.logrel Require Import model.

Section rules.
  Context `{!prelogrelGS Σ}.
  Implicit Types A : lrel Σ.
  Implicit Types e : expr.
  Implicit Types v w : val.

  Local Existing Instance pure_exec_fill.

  (** * Primitive rules *)

  (** ([fupd_refines] is defined in [logrel_binary.v]) *)

  (** ** Forward reductions on the LHS *)

  Lemma refines_pure_l E F n
    (K' : list ectx_item) e e' t A ϕ :
    PureExec ϕ n e e' →
    ϕ →
    ▷^n (REL fill K' e' << t @ E ; F : A)
    ⊢ REL fill K' e << t @ E ; F : A.
  Proof.
    intros Hpure Hϕ.
    rewrite refines_eq /refines_def.
    iIntros "IH" (j) "Hs Hnais".
    wp_pures. iApply ("IH" with "Hs Hnais").
  Qed.

  Lemma refines_wp_l E F K e1 t A :
    (WP e1 @ E {{ v,
        REL fill K (of_val v) << t @ E ; F : A }})%I -∗
    REL fill K e1 << t @ E ; F : A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "He" (K') "Hs Hnais /=".
    iApply wp_bind.
    iApply (wp_wand with "He").
    iIntros (v) "Hv".
    iApply ("Hv" with "Hs Hnais").
  Qed.

  Lemma refines_atomic_l (E1 E2 F : coPset) K e1 t A
    (Hatomic : Atomic WeaklyAtomic e1) :
    (∀ K', refines_right K' t ={E1,E2}=∗
             WP e1 @ E2 {{ v,
              |={E2, E1}=> ∃ t', refines_right K' t' ∗
              REL fill K (of_val v) << t' @ E1 ; F : A }})%I -∗
   REL fill K e1 << t @ E1 ; F: A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "Hlog" (K') "Hs Hnais /=".
    iApply wp_bind. iApply wp_atomic; auto.
    iMod ("Hlog" with "Hs") as "He". iModIntro.
    iApply (wp_wand with "He").
    iIntros (v) "Hlog".
    iMod "Hlog" as (t') "[Hr Hlog]".
    iApply ("Hlog" with "Hr Hnais").
  Qed.

  (** ** Forward reductions on the RHS *)

  Lemma refines_pure_r E F K' e e' t A n
    (Hspec : nclose specN ⊆ E) ϕ :
    PureExec ϕ n e e' →
    ϕ →
    (REL t << fill K' e' @ E ; F : A)
    ⊢ REL t << fill K' e @ E ; F : A.
  Proof.
    rewrite refines_eq /refines_def => Hpure Hϕ.
    iIntros "Hlog" (j) "Hj Hnais /=".
    tp_pures j ; auto.
    iApply ("Hlog" with "Hj Hnais").
  Qed.

  Lemma refines_right_bind K' K e :
    refines_right K' (fill K e) ≡ refines_right (K ++ K') e.
  Proof. rewrite /refines_right /=. by rewrite fill_app. Qed.

  Definition refines_right_bind' := refines_right_bind.

  (* A helper lemma for proving the stateful reductions for the RHS below *)
  Lemma refines_step_r E F K' e1 e2 A :
    (∀ k, refines_right k e2 ={E}=∗
         ∃ v, refines_right k (of_val v) ∗ REL e1 << fill K' (of_val v) @ E ; F : A) -∗
    REL e1 << fill K' e2 @ E ; F : A.
  Proof.
    rewrite refines_eq /refines_def /=.
    iIntros "He" (K'') "Hs Hnais /=".
    rewrite refines_right_bind /=.
    iMod ("He" with "Hs") as (v) "[Hs He]".
    rewrite -refines_right_bind'.
    iSpecialize ("He" with "Hs Hnais").
    by iApply "He".
  Qed.

  Lemma refines_alloc_r E F K e v t A
    (Hmasked : nclose specN ⊆ E) :
    IntoVal e v →
    (∀ l : loc, l ↦ₛ v -∗ REL t << fill K (of_val #l) @ E ; F : A)%I
    -∗ REL t << fill K (ref e) @ E ; F : A.
  Proof.
    rewrite /IntoVal. intros <-.
    iIntros "Hlog". simpl.
    iApply refines_step_r ; simpl.
    iIntros (K') "HK'".
    tp_alloc K' as l "Hl".
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_load_r E F K l q v t A
    (Hmasked : nclose specN ⊆ E) :
    l ↦ₛ{q} v -∗
    (l ↦ₛ{q} v -∗ REL t << fill K (of_val v) @ E ; F : A)
    -∗ REL t << (fill K !#l) @ E ; F : A.
  Proof.
    iIntros "Hl Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    tp_load k.
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_store_r E F K l e e' v v' A
    (Hmasked : nclose specN ⊆ E) :
    IntoVal e' v' →
    l ↦ₛ v -∗
    (l ↦ₛ v' -∗ REL e << fill K (of_val #()) @ E ; F : A) -∗
    REL e << fill K (#l <- e') @ E ; F : A.
  Proof.
    rewrite /IntoVal. iIntros (<-) "Hl Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk". simpl.
    tp_store k. iModIntro. iExists _. iFrame.
    by iApply "Hlog".
  Qed.

  Lemma refines_alloctape_r E F K t A
    (Hmasked : nclose specN ⊆ E) :
    (∀ α : loc, α ↪ₛ [] -∗ REL t << fill K (of_val #lbl:α) @ E ; F : A)%I
    -∗ REL t << fill K alloc @ E ; F : A.
  Proof.
    rewrite /IntoVal.
    iIntros "Hlog".
    iApply refines_step_r.
    iIntros (K') "HK'".
    tp_alloctape K' as α "Hα".
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_flip_r E F K α b bs t A
    (Hmasked : nclose specN ⊆ E) :
    α ↪ₛ (b :: bs)
    -∗ (α ↪ₛ bs -∗ REL t << fill K (of_val #b) @ E ; F : A)
    -∗ REL t << (fill K (flip #lbl:α)) @ E ; F : A.
  Proof.
    iIntros "Hα Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    tp_flip k.
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  (** This rule is useful for proving that functions refine each other *)
  Lemma refines_arrow_val E1 E2 (v v' : val) A A' :
    □(∀ v1 v2, A v1 v2 -∗
      REL App v (of_val v1) << App v' (of_val v2) @ E2 : A') -∗
    REL (of_val v) << (of_val v') @ E1 : (A →{E2} A')%lrel.
  Proof.
    iIntros "#H".
    iApply refines_ret. iModIntro.
    iModIntro. iIntros (v1 v2) "HA".
    iSpecialize ("H" with "HA").
    by iApply "H".
  Qed.

  (** * Some derived (symbolic execution) rules *)

  (** ** Stateful reductions on the LHS *)

  Lemma refines_alloc_l K E F e v t A :
    IntoVal e v →
    (▷ (∀ l : loc, l ↦ v -∗
           REL fill K (of_val #l) << t @ E ; F : A))
    -∗ REL fill K (ref e) << t @ E ; F : A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_wp_l.
    wp_alloc l. by iApply "Hlog".
  Qed.

  Lemma refines_load_l K E F l q t A :
    (∃ v',
      ▷(l ↦{q} v') ∗
      ▷(l ↦{q} v' -∗ (REL fill K (of_val v') << t @ E ; F : A)))
    -∗ REL fill K (! #l) << t @ E ; F : A.
  Proof.
    iIntros "[%v' [Hl Hlog]]".
    iApply refines_wp_l.
    wp_load. by iApply "Hlog".
  Qed.

  Lemma refines_store_l K E F l e v' t A :
    IntoVal e v' →
    (∃ v, ▷ l ↦ v ∗
      ▷(l ↦ v' -∗ REL fill K (of_val #()) << t @ E ; F : A))
    -∗ REL fill K (#l <- e) << t @ E ; F : A.
  Proof.
    iIntros (<-) "[%v [Hl Hlog]]".
    iApply refines_wp_l.
    wp_store. by iApply "Hlog".
  Qed.

  Lemma refines_alloctape_l K E F t A :
    (▷ (∀ α : loc, α ↪ [] -∗
           REL fill K (of_val #lbl:α) << t @ E ; F : A))%I
    -∗ REL fill K alloc << t @ E ; F : A.
  Proof.
    iIntros "Hlog".
    iApply refines_wp_l.
    by wp_apply (wp_alloc_tape with "[//]").
  Qed.

  Lemma refines_flip_l E F K α b bs t A :
    (▷ α ↪ (b :: bs) ∗
     ▷ (α ↪ bs -∗ REL fill K (of_val #b) << t @ E ; F : A))
    -∗ REL fill K (flip #lbl:α) << t @ E ; F : A.
  Proof.
    iIntros "[Hα Hlog]".
    iApply refines_wp_l.
    by wp_apply (wp_flip with "Hα").
  Qed.

  Lemma refines_wand E F e1 e2 A A' :
    (REL e1 << e2 @ E ; F : A) -∗
    (∀ v1 v2, A v1 v2 ={E}=∗ A' v1 v2) -∗
    REL e1 << e2 @ E ; F : A'.
  Proof.
    iIntros "He HAA".
    iApply (refines_bind [] [] with "He").
    iIntros (v v') "HA /=". iApply refines_ret.
    by iApply "HAA".
  Qed.

  Lemma refines_arrow E1 E2 (v v' : val) A A' :
    □ (∀ v1 v2 : val, □(REL of_val v1 << of_val v2 @ E1 : A) -∗
      REL App v (of_val v1) << App v' (of_val v2) @ E2 : A') -∗
    REL (of_val v) << (of_val v') @ E1 : (A →{E2} A')%lrel.
  Proof.
    iIntros "#H".
    iApply refines_arrow_val; eauto.
    iModIntro. iIntros (v1 v2) "#HA".
    iApply "H". iModIntro.
    by iApply refines_ret.
  Qed.

  Lemma refines_couple_tapes E F e1 e2 A α αₛ bs bsₛ
    (Hmasked : nclose specN ⊆ E) :
    to_val e1 = None →
    ((αₛ ↪ₛ bsₛ ∗ α ↪ bs ∗
       ((∃ b, αₛ ↪ₛ (bsₛ ++ [b]) ∗ α ↪ (bs ++ [b]))
       -∗ REL e1 << e2 @ E ; F : A)))
    ⊢ REL e1 << e2 @ E ; F : A.
  Proof.
    iIntros (e1ev) "(Hαs & Hα & Hlog)".
    rewrite refines_eq /refines_def.
    iIntros (K2) "[#Hs He2] Hnais /=".
    wp_apply wp_couple_tapes; [done|done|].
    iFrame "Hα Hαs".
    iSplit; [done|].
    iIntros "[%b [Hαs Hα]]".
    iApply ("Hlog" with "[Hα Hαs] [$Hs $He2] Hnais").
    iExists _. iFrame.
  Qed.

  Lemma refines_couple_flips_l K K' E F α A (Hmasked : nclose specN ⊆ E) :
    α ↪ [] ∗
      (∀ (b : bool), α ↪ [] -∗ REL fill K (Val #b) << fill K' (Val #b) @ E ; F : A)
    ⊢ REL fill K (flip #lbl:α) << fill K' (flip #()) @ E ; F : A.
  Proof.
    iIntros "[Hα Hcnt]".
    rewrite refines_eq /refines_def.
    iIntros (K2) "[#Hs Hspec] Hnais /=".
    wp_apply wp_bind.
    wp_apply wp_couple_flips_l; [done|].
    rewrite -fill_app.
    iFrame "Hs Hα Hspec".
    iIntros (b) "[Hα Hspec]".
    iApply wp_value.
    rewrite fill_app.
    iSpecialize ("Hcnt" with "Hα [$Hspec $Hs] Hnais").
    wp_apply (wp_mono with "Hcnt").
    iIntros (v) "[% ([? ?] &?&?)]".
    iExists _. iFrame.
  Qed.

  Lemma refines_couple_flips_r K K' E F α A (Hmasked : nclose specN ⊆ E) :
    α ↪ₛ [] ∗
      (∀ (b : bool), α ↪ₛ [] -∗ REL fill K (Val #b) << fill K' (Val #b) @ E ; F : A)
    ⊢ REL fill K (flip #()) << fill K' (flip #lbl:α) @ E ; F : A.
  Proof.
    iIntros "[Hα Hcnt]".
    rewrite refines_eq /refines_def.
    iIntros (K2) "[#Hs Hspec] Hnais /=".
    wp_apply wp_bind.
    wp_apply wp_couple_flips_r; [done|].
    rewrite -fill_app.
    iFrame "Hs Hα Hspec".
    iIntros (b) "[Hα Hspec]".
    iApply wp_value.
    rewrite fill_app.
    iSpecialize ("Hcnt" with "Hα [$Hspec $Hs] Hnais").
    wp_apply (wp_mono with "Hcnt").
    iIntros (v) "[% ([? ?] &?&?)]".
    iExists _. iFrame.
  Qed.

  Lemma refines_couple_flips_lr K K' E F A (Hmasked : nclose specN ⊆ E) :
      (∀ (b : bool), REL fill K (Val #b) << fill K' (Val #b) @ E ; F : A)
    ⊢ REL fill K (flip #()) << fill K' (flip #()) @ E ; F : A.
  Proof.
    iIntros "Hcnt".
    rewrite refines_eq /refines_def.
    iIntros (K2) "[#Hs Hspec] Hnais /=".
    wp_apply wp_bind.
    wp_apply wp_couple_flips_lr; [done|].
    rewrite -fill_app.
    iFrame "Hs Hspec".
    iIntros (b) "Hspec".
    iApply wp_value.
    rewrite fill_app.
    iSpecialize ("Hcnt" with "[$Hspec $Hs] Hnais").
    wp_apply (wp_mono with "Hcnt").
    iIntros (v) "[% ([? ?] &?&?)]".
    iExists _. iFrame.
  Qed.

End rules.
