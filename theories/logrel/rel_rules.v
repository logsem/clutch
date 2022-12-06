(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Core ReLoC rules *)
From stdpp Require Import coPset namespaces.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list.
From self.program_logic Require Import ectx_lifting.
From self.prob_lang Require Import lang spec_rules spec_tactics ctx_subst proofmode.
From self.logrel Require Import model.

Section rules.
  Context `{!prelocGS Σ}.
  Implicit Types A : lrel Σ.
  Implicit Types e : expr.
  Implicit Types v w : val.

  Local Existing Instance pure_exec_fill.

  (** * Primitive rules *)

  (** ([fupd_refines] is defined in [logrel_binary.v]) *)

  (** ** Forward reductions on the LHS *)

  Lemma refines_pure_l n
    (K' : list ectx_item) e e' t A ϕ :
    PureExec ϕ n e e' →
    ϕ →
    ▷^n (REL fill K' e' << t : A)
    ⊢ REL fill K' e << t : A.
  Proof.
    intros Hpure Hϕ.
    rewrite refines_eq /refines_def.
    iIntros "IH" ; iIntros (j) "Hs".
    iModIntro. wp_pures.
    iApply fupd_wp. iApply ("IH" with "Hs").
  Qed.

  Lemma refines_masked_l E n
    (K' : list ectx_item) e e' t A ϕ :
    PureExec ϕ n e e' →
    ϕ →
    (REL fill K' e' << t @ E : A)
    ⊢ REL fill K' e << t @ E : A.
  Proof.
    intros Hpure Hϕ.
    rewrite refines_eq /refines_def.
    iIntros "IH" ; iIntros (j) "Hs /=".
    iMod ("IH" with "Hs") as "IH".
    iModIntro. by wp_pures.
  Qed.

  Lemma refines_wp_l K e1 t A :
    (WP e1 {{ v,
        REL fill K (of_val v) << t : A }})%I -∗
    REL fill K e1 << t : A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "He".
    iIntros (j) "Hs /=".
    iModIntro. iApply wp_bind.
    iApply (wp_wand with "He").
    iIntros (v) "Hv".
    by iMod ("Hv" with "Hs").
  Qed.

  Lemma refines_atomic_l (E : coPset) K e1 t A
        (Hatomic : Atomic WeaklyAtomic e1) :
   (|={⊤,E}=> WP e1 @ E {{ v,
     REL fill K (of_val v) << t @ E : A }})%I -∗
   REL fill K e1 << t : A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "Hlog".
    iIntros (j) "Hs /=". iModIntro.
    iApply wp_bind. iApply wp_atomic; auto.
    iMod "Hlog" as "He". iModIntro.
    iApply (wp_wand with "He").
    iIntros (v) "Hlog".
    by iApply ("Hlog" with "Hs").
  Qed.

  (** ** Forward reductions on the RHS *)

  Lemma refines_pure_r E K' e e' t A n
    (Hspec : nclose specN ⊆ E) ϕ :
    PureExec ϕ n e e' →
    ϕ →
    (REL t << fill K' e' @ E : A)
    ⊢ REL t << fill K' e @ E : A.
  Proof.
    rewrite refines_eq /refines_def => Hpure Hϕ.
    iIntros "Hlog". iIntros (j) "Hj /=".
    tp_pures j ; auto.
    iApply ("Hlog" with "Hj").
  Qed.

  Lemma refines_right_bind K' K e :
    refines_right K' (fill K e) ≡ refines_right (K ++ K') e.
  Proof. rewrite /refines_right /=. by rewrite fill_app. Qed.

  Definition refines_right_bind' := refines_right_bind.

  (* A helper lemma for proving the stateful reductions for the RHS below *)
  Lemma refines_step_r E K' e1 e2 A :
    (∀ k, refines_right k e2 ={E}=∗
         ∃ v, refines_right k (of_val v) ∗ REL e1 << fill K' (of_val v) @ E : A) -∗
    REL e1 << fill K' e2 @ E : A.
  Proof.
    rewrite refines_eq /refines_def /=.
    iIntros "He".
    iIntros (K'') "Hs /=".
    rewrite refines_right_bind /=.
    iMod ("He" with "Hs") as (v) "[Hs He]".
    rewrite -refines_right_bind'.
    iSpecialize ("He" with "Hs").
    by iApply "He".
  Qed.

  Lemma refines_alloc_r E K e v t A
    (Hmasked : nclose specN ⊆ E) :
    IntoVal e v →
    (∀ l : loc, l ↦ₛ v -∗ REL t << fill K (of_val #l) @ E : A)%I
    -∗ REL t << fill K (ref e) @ E : A.
  Proof.
    rewrite /IntoVal. intros <-.
    iIntros "Hlog". simpl.
    iApply refines_step_r ; simpl.
    iIntros (K') "HK'".
    tp_alloc K' as l "Hl".
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_load_r E K l q v t A
    (Hmasked : nclose specN ⊆ E) :
    l ↦ₛ{q} v -∗
    (l ↦ₛ{q} v -∗ REL t << fill K (of_val v) @ E : A)
    -∗ REL t << (fill K !#l) @ E : A.
  Proof.
    iIntros "Hl Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    tp_load k.
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_store_r E K l e e' v v' A
    (Hmasked : nclose specN ⊆ E) :
    IntoVal e' v' →
    l ↦ₛ v -∗
    (l ↦ₛ v' -∗ REL e << fill K (of_val #()) @ E : A) -∗
    REL e << fill K (#l <- e') @ E : A.
  Proof.
    rewrite /IntoVal. iIntros (<-) "Hl Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk". simpl.
    tp_store k. iModIntro. iExists _. iFrame.
    by iApply "Hlog".
  Qed.

  Lemma refines_alloctape_r E K t A
    (Hmasked : nclose specN ⊆ E) :
    (∀ α : loc, α ↪ₛ [] -∗ REL t << fill K (of_val #lbl:α) @ E : A)%I
    -∗ REL t << fill K alloc @ E : A.
  Proof.
    rewrite /IntoVal.
    iIntros "Hlog".
    iApply refines_step_r.
    iIntros (K') "HK'".
    tp_alloctape K' as α "Hα".
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_flip_r E K α b bs t A
    (Hmasked : nclose specN ⊆ E) :
    α ↪ₛ (b :: bs)
    -∗ (α ↪ₛ bs -∗ REL t << fill K (of_val #b) @ E : A)
    -∗ REL t << (fill K (flip #lbl:α)) @ E : A.
  Proof.
    iIntros "Hα Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    tp_flip k.
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  (** This rule is useful for proving that functions refine each other *)
  Lemma refines_arrow_val (v v' : val) A A' :
    □(∀ v1 v2, A v1 v2 -∗
      REL App v (of_val v1) << App v' (of_val v2) : A') -∗
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
    IntoVal e v →
    (|={⊤,E}=> ▷ (∀ l : loc, l ↦ v -∗
           REL fill K (of_val #l) << t @ E : A))%I
    -∗ REL fill K (ref e) << t : A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog". iModIntro.
    wp_alloc l. by iApply "Hlog".
  Qed.

  Lemma refines_load_l K E l q t A :
    (|={⊤,E}=> ∃ v',
      ▷(l ↦{q} v') ∗
      ▷(l ↦{q} v' -∗ (REL fill K (of_val v') << t @ E : A)))%I
    -∗ REL fill K (! #l) << t : A.
  Proof.
    iIntros "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog" as (v') "[Hl Hlog]". iModIntro.
    wp_load. by iApply "Hlog".
  Qed.

  Lemma refines_store_l K E l e v' t A :
    IntoVal e v' →
    (|={⊤,E}=> ∃ v, ▷ l ↦ v ∗
      ▷(l ↦ v' -∗ REL fill K (of_val #()) << t @ E : A))
    -∗ REL fill K (#l <- e) << t : A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog" as (v) "[Hl Hlog]". iModIntro.
    wp_store. by iApply "Hlog".
  Qed.

  Lemma refines_alloctape_l K E t A :
    (|={⊤,E}=> ▷ (∀ α : loc, α ↪ [] -∗
           REL fill K (of_val #lbl:α) << t @ E : A))%I
    -∗ REL fill K alloc << t : A.
  Proof.
    iIntros "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog". iModIntro.
    iApply (wp_alloc_tape _ _ with "[//]"). iIntros "!>" (l) "?". by iApply "Hlog".
  Qed.

  Lemma refines_flip_l E K α b bs t A :
    (|={⊤,E}=> ▷ α ↪ (b :: bs)
               ∗ ▷ (α ↪ bs -∗ REL fill K (of_val #b) << t @ E : A))
    -∗ REL fill K (flip #lbl:α) << t : A.
  Proof.
    iIntros "Hlog".
    iApply refines_atomic_l.
    iMod "Hlog" as "[Hα Hlog]". iModIntro.
    iApply (wp_flip with "Hα").
    by iApply "Hlog".
  Qed.

  Lemma refines_wand E e1 e2 A A' :
    (REL e1 << e2 @ E : A) -∗
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
      REL App v (of_val v1) << App v' (of_val v2) : A') -∗
    REL (of_val v) << (of_val v') : (A → A')%lrel.
  Proof.
    iIntros "#H".
    iApply refines_arrow_val; eauto.
    iModIntro. iIntros (v1 v2) "#HA".
    iApply "H". iModIntro.
    by iApply refines_ret.
  Qed.

End rules.
