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

  Lemma refines_pure_l n
    (K' : list ectx_item) e e' t A ϕ :
    PureExec ϕ n e e' →
    ϕ →
    ▷^n (REL fill K' e' << t : A)
    ⊢ REL fill K' e << t : A.
  Proof.
    intros Hpure Hϕ.
    rewrite refines_eq /refines_def.
    iIntros "IH" (K j) "Hs".
    wp_pures.
    by iApply ("IH" with "Hs").
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
    iIntros "IH" ; iIntros (K j) "Hs /=".
    wp_pures.
    iApply ("IH" with "Hs").
  Qed.
  
  Lemma refines_wp_l E K e1 t A :
    (WP e1 {{ v,
        REL fill K (of_val v) << t @ E: A }})%I
    ⊢ REL fill K e1 << t @ E: A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "He" (K' j) "Hs".
    iApply wp_bind.
    iApply (wp_wand with "He").
    iIntros (v) "Hv".
    by iApply ("Hv" with "Hs").
  Qed.

  Lemma refines_pure_r E K' e e' t A n ϕ :
    PureExec ϕ n e e' →
    ϕ →
    (REL t << fill K' e' @ E : A)
      ⊢ REL t << fill K' e @ E : A.
  Proof.
    rewrite refines_eq /refines_def => Hpure Hϕ.
    iIntros "Hlog" (? j) "Hj /=".
    tp_pures j; auto.
    by iApply ("Hlog" with "[$]").
  Qed.

  Lemma refines_atomic_l (E E' : coPset) K e1 t A  
    (Hatomic : Atomic StronglyAtomic e1) :
    (∀ K' j , j ⤇ fill K' t ={⊤, E'}=∗
             WP e1 @ E' {{ v,
              |={E', ⊤}=> ∃ t', j ⤇ fill K' t' ∗
              REL fill K (of_val v) << t' @ E : A }})%I
   ⊢ REL fill K e1 << t @ E : A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "Hlog" (K' j) "Hs /=".
    iApply wp_bind. iApply wp_atomic; auto.
    iMod ("Hlog" with "Hs") as "He". iModIntro.
    iApply (wp_wand with "He").
    iIntros (v) "Hlog".
    iMod "Hlog" as (t') "[Hr Hlog]".
    iApply ("Hlog" with "Hr ").
  Qed.
  Lemma pupd_fupd' E1 E2 P:
    E2⊆E1->
    pupd E1 E1 P -∗ pupd E1 E2 (|={E2,E1}=>P).
  Proof.
    rewrite pupd_unseal/pupd_def.
    intros.
    iIntros "H" (???) "(?&?&?)".
    iMod ("H" with "[$]") as "H".
    iModIntro.
    iApply spec_coupl_mono; last done.
    iIntros (???) ">(?&?&?&?)".
    iApply (fupd_mask_intro); first done.
    iIntros "Hclose".
    iFrame.
    by iMod "Hclose".
  Qed.

  
  Lemma refines_step_r E K' e1 e2 A :
    (∀ k j, j ⤇ fill k e2 -∗
         pupd E E (∃ v, j ⤇ fill k (of_val v) ∗
                             REL e1 << fill K' (of_val v) @ E : A))
    ⊢ REL e1 << fill K' e2 @ E : A.
  Proof.
    rewrite refines_eq /refines_def /=.
    iIntros "He" (? j) "Hs /=".
    rewrite -fill_app.
    iMod ("He" with "Hs") as (v) "[Hs He]".
    rewrite fill_app.
    iSpecialize ("He" with "Hs").
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
           REL fill K (of_val #l) << t @ E : A))%I
    ⊢ REL fill K (ref e) << t @ E: A.

  Proof.
    iIntros (<-) "Hlog".
    iApply refines_wp_l.
    wp_alloc l as "Hl". by iApply "Hlog".
  Qed.
    (* iIntros (<-) "Hlog". *)
  (*   iApply refines_atomic_l; auto. *)
  (*   iIntros. iApply "Hlog". iModIntro. *)
  (*   wp_alloc l as "Hl". by iApply "Hlog". *)
  (* Qed. *)

  Lemma refines_alloctape_l K E N z t A :
    TCEq N (Z.to_nat z) →
    (▷ (∀ α : loc, α ↪N (N; []) -∗ REL fill K (of_val #lbl:α) << t @ E : A))%I
    ⊢ REL fill K (alloc #z) << t @ E: A.
  Proof.
    iIntros (->) "Hlog".
    iApply refines_wp_l.
    by wp_apply (wp_alloc_tape with "[//]").
  Qed. 
  (*   iIntros (->) "Hlog". *)
  (*   iApply refines_atomic_l. *)
  (*   iMod "Hlog". iModIntro. *)
  (*   by wp_apply (wp_alloc_tape with "[//]"). *)
  (* Qed. *)
  
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

  Lemma refines_fork e e' :
    (REL e << e' : ()%lrel) -∗
    REL Fork e << Fork e' : ().
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "H".
    iIntros (K j) "Hs /=".
    tp_fork j as k' "Hk'".
    rewrite -(fill_empty e').
    iSpecialize ("H" with "Hk'").
    iApply (wp_fork with "[H]").
    - iNext. iApply (wp_wand with "H"). eauto.
    - iModIntro. iExists _. iFrame. 
      eauto with iFrame.
  Qed.

  Lemma refines_xchg_l K E l e v' t A :
    IntoVal e v' →
    (∃ v, ▷ l ↦ v ∗
      ▷(l ↦ v' -∗ REL fill K (of_val v) << t @ E : A))
    ⊢ REL fill K (Xchg #l e) << t @ E: A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_wp_l.
    iDestruct "Hlog" as (v) "[Hl Hlog]".
    iApply (wp_xchg _ _ _ v' with "[$]"); auto.
  Qed. 
  (*   iIntros (<-) "Hlog". *)
  (*   iApply refines_atomic_l; auto. *)
  (*   iMod "Hlog" as (v) "[Hl Hlog]". iModIntro. *)
  (*   iApply (wp_xchg _ _ _ v' with "Hl"); auto. *)
  (* Qed. *)

  Lemma refines_cmpxchg_l K E l e1 e2 v1 v2 t A :
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    val_is_unboxed v1 →
    (∃ v', ▷ l ↦ v' ∗
     (⌜v' ≠ v1⌝ -∗ ▷ (l ↦ v' -∗ REL fill K (of_val (v', #false)) << t @ E : A)) ∧
     (⌜v' = v1⌝ -∗ ▷ (l ↦ v2 -∗ REL fill K (of_val (v', #true)) << t @ E : A)))
    ⊢ REL fill K (CmpXchg #l e1 e2) << t @ E: A.
  Proof.
    iIntros (<- <-?) "Hlog".
    iApply refines_wp_l.
    iDestruct "Hlog" as (v') "[Hl Hlog]". 
    destruct (decide (v' = v1)).
    - (* CmpXchg successful *) subst.
      iApply (wp_cmpxchg_suc with "Hl"); eauto.
      { by right. }
      iDestruct "Hlog" as "[_ Hlog]".
      iSpecialize ("Hlog" with "[]"); eauto.
    - (* CmpXchg failed *)
      iApply (wp_cmpxchg_fail with "Hl"); eauto.
      { by right. }
      iDestruct "Hlog" as "[Hlog _]".
      iSpecialize ("Hlog" with "[]"); eauto.
  Qed.
  (*   iIntros (<-<-?) "Hlog". *)
  (*   iApply refines_atomic_l; auto. *)
  (*   iMod "Hlog" as (v') "[Hl Hlog]". iModIntro. *)
  (*   destruct (decide (v' = v1)). *)
  (*   - (* CmpXchg successful *) subst. *)
  (*     iApply (wp_cmpxchg_suc with "Hl"); eauto. *)
  (*     { by right. } *)
  (*     iDestruct "Hlog" as "[_ Hlog]". *)
  (*     iSpecialize ("Hlog" with "[]"); eauto. *)
  (*   - (* CmpXchg failed *) *)
  (*     iApply (wp_cmpxchg_fail with "Hl"); eauto. *)
  (*     { by right. } *)
  (*     iDestruct "Hlog" as "[Hlog _]". *)
  (*     iSpecialize ("Hlog" with "[]"); eauto. *)
  (* Qed. *)

  Lemma refines_faa_l K E l e2 (i2 : Z) t A :
    IntoVal e2 #i2 →
    (∃ (i1 : Z), ▷ l ↦ #i1 ∗
     ▷ (l ↦ #(i1 + i2) -∗ REL fill K (of_val #i1) << t @ E : A))
    ⊢ REL fill K (FAA #l e2) << t @ E: A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_wp_l; auto.
    iDestruct "Hlog" as (i1) "[Hl Hlog]".
    wp_faa. iModIntro.
    by iApply "Hlog".
  Qed.

  Lemma refines_xchg_r E K l e1 v1 v t A :
    IntoVal e1 v1 →
    l ↦ₛ v ⊢
    (l ↦ₛ v1 -∗ REL t << fill K (of_val v) @ E : A)
    -∗ REL t << fill K (Xchg #l e1) @ E : A.
  Proof.
    rewrite /IntoVal. iIntros (<-) "Hl Hlog".
    iApply refines_step_r.
    iIntros (k j) "Hk".
    tp_xchg j. iExists v. iModIntro. iFrame.
    by iApply "Hlog".
  Qed.

  Lemma refines_cmpxchg_fail_r E K l e1 e2 v1 v2 v t A :
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    vals_compare_safe v v1 →
    v ≠ v1 →
    l ↦ₛ v ⊢
    (l ↦ₛ v -∗ REL t << fill K (of_val (v, #false)) @ E : A)
    -∗ REL t << fill K (CmpXchg #l e1 e2) @ E : A.
  Proof.
    rewrite /IntoVal. iIntros (<-<-??) "Hl Hlog".
    iApply refines_step_r.
    iIntros (k j) "Hk".
    tp_cmpxchg_fail j.
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_cmpxchg_suc_r E K l e1 e2 v1 v2 v t A :
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    vals_compare_safe v v1 →
    v = v1 →
    l ↦ₛ v ⊢
    (l ↦ₛ v2 -∗ REL t << fill K (of_val (v, #true)) @ E : A)
    -∗ REL t << fill K (CmpXchg #l e1 e2) @ E : A.
  Proof.
    rewrite /IntoVal. iIntros (<-<-??) "Hl Hlog".
    iApply refines_step_r.
    iIntros (k j) "Hk".
    tp_cmpxchg_suc j.
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_faa_r E K l e2 (i1 i2 : Z) t A :
    IntoVal e2 #i2 →
    l ↦ₛ #i1 -∗
    (l ↦ₛ #(i1+i2) -∗ REL t << fill K (of_val #i1) @ E : A)
    -∗ REL t << fill K (FAA #l e2) @ E : A.
  Proof.
    rewrite /IntoVal. iIntros (<-) "Hl Hlog".
    iApply refines_step_r.
    iIntros (k j) "Hk".
    tp_faa j.
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  
End rules.
