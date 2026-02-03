(** Core relational rules *)
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import
     coq_tactics ltac_tactics
     reduction.
From clutch.prelude Require Import stdpp_ext.
From clutch.common Require Import language ectxi_language locations.
From clutch.delay_prob_lang Require Import class_instances notation tactics lang.
From clutch.elton Require Import primitive_laws proofmode.
From clutch.elton.unary_rel Require Import unary_model.

Section rules.
  Context `{!eltonGS Σ}.
  Implicit Types A : lrel Σ.
  Implicit Types e : expr.
  Implicit Types v w : val.

  Local Existing Instance pure_exec_fill.

  (** * Primitive rules *)

  (** ([fupd_refines] is defined in [logrel_binary.v]) *)

  (** ** Forward reductions on the LHS *)

  Lemma refines_pure n e e' A ϕ K' :
    PureExec ϕ n e e' →
    ϕ →
    ▷^n (REL fill K' e' : A)
    ⊢ REL fill K' e : A.
  Proof.
    intros Hpure Hϕ.
    rewrite refines_eq /refines_def.
    iIntros. by wp_pures.
  Qed.

  Lemma refines_masked_l n
    (K' : list ectx_item) e e' A ϕ :
    PureExec ϕ n e e' →
    ϕ →
    (REL fill K' e' : A)
    ⊢ REL fill K' e : A.
  Proof.
    intros Hpure Hϕ.
    rewrite refines_eq /refines_def.
    iIntros "IH". 
    by wp_pures.
  Qed.
  
  Lemma refines_wp_l K e1 A :
    (WP e1 {{ v,
        REL fill K (of_val v) : A }})%I
    ⊢ REL fill K e1: A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros.
    iApply pgl_wp_bind.
    iApply (pgl_wp_wand with "[$]").
    by iIntros (v) "Hv".
  Qed.

  (* Lemma refines_pure_r K' e e' t A n ϕ : *)
  (*   PureExec ϕ n e e' → *)
  (*   ϕ → *)
  (*   (REL t << fill K' e' : A) *)
  (*     ⊢ REL t << fill K' e : A. *)
  (* Proof. *)
  (*   rewrite refines_eq /refines_def => Hpure Hϕ. *)
  (*   iIntros "Hlog" (? j) "Hj /=". *)
  (*   tp_pures j; auto. *)
  (*   by iApply ("Hlog" with "[$]"). *)
  (* Qed. *)

  Lemma refines_atomic_l (E : coPset) K e1 A  
    (Hatomic : Atomic StronglyAtomic e1) :
    (|={⊤, E}=>
             WP e1 @ E {{ v,
              |={E, ⊤}=> 
              REL fill K (of_val v) : A }})%I
   ⊢ REL fill K e1 : A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "Hlog" .
    iApply pgl_wp_bind.
  Abort. 
    (* iApply pgl_wp_atomic; auto. *)
  (* Qed. *)
  
  Lemma pupd_fupd' E1 E2 P:
    E2⊆E1->
    pupd E1 E1 P -∗ pupd E1 E2 (|={E2,E1}=>P).
  Proof.
    rewrite pupd_unseal/pupd_def.
    intros.
    iIntros "H" (???) "(?&?)".
    iMod ("H" with "[$]") as "H".
    iModIntro.
    iApply state_step_coupl_mono; last done.
    iIntros (???) ">(?&?&->&?)".
    iApply (fupd_mask_intro); first done.
    iIntros "Hclose".
    iFrame.
    iSplit; first done.
    by iMod "Hclose".
  Qed.

  
  (* Lemma refines_step_r K' e1 e2 A : *)
  (*   (∀ k j, j ⤇ fill k e2 -∗ *)
  (*        pupd ⊤ ⊤ (∃ v, j ⤇ fill k (of_val v) ∗ *)
  (*                            REL e1 << fill K' (of_val v) : A)) *)
  (*   ⊢ REL e1 << fill K' e2 : A. *)
  (* Proof. *)
  (*   rewrite refines_eq /refines_def /=. *)
  (*   iIntros "He" (? j) "Hs /=". *)
  (*   rewrite -fill_app. *)
  (*   iMod ("He" with "Hs") as (v) "[Hs He]". *)
  (*   rewrite fill_app. *)
  (*   iSpecialize ("He" with "Hs"). *)
  (*   by iApply "He". *)
  (* Qed. *)
  
  (** This rule is useful for proving that functions refine each other *)
  Lemma refines_arrow_val (v : val) A A' :
    □(∀ v1, A v1 -∗
      REL App v (of_val v1)  : A') ⊢
    REL (of_val v) : (A → A')%lrel.
  Proof.
    iIntros "#H".
    iApply refines_ret. iModIntro.
    iModIntro. iIntros (v1) "HA".
    iSpecialize ("H" with "HA").
    unfold_rel.
    iApply "H".
  Qed.
  
  Lemma refines_arrow (v : val) A A' :
    □ (∀ v1 : val, □(REL of_val v1 : A) -∗
      REL App v (of_val v1) : A') ⊢
    REL (of_val v)  : (A → A')%lrel.
  Proof.
    iIntros "#H".
    iApply refines_arrow_val; eauto.
    iModIntro. iIntros (v1) "#HA".
    iApply "H". iModIntro.
    by iApply refines_ret.
  Qed.

  Lemma refines_wand e1 A A' :
    (REL e1 : A) ⊢
    (∀ v1, A v1 ={⊤}=∗ A' v1) -∗
    REL e1 : A'.
  Proof.
    iIntros "He HAA".
    iApply (refines_bind [] with "He").
    iIntros (v) "HA /=". iApply refines_ret.
    by iApply "HAA".
  Qed.
  

  Lemma refines_alloc_l K e v A :
    IntoVal e v →
    (▷ (∀ l : loc, l ↦ v -∗
           REL fill K (of_val #l) : A))%I
    ⊢ REL fill K (ref e) : A.
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
  
  (* Lemma refines_alloc_r K e v t A : *)
  (*   IntoVal e v → *)
  (*   (∀ l : loc, l ↦ₛ v -∗ REL t << fill K (of_val #l) : A)%I *)
  (*     ⊢ REL t << fill K (ref e) : A. *)
  (* Proof. *)
  (*   intros <-. *)
  (*   iIntros "Hlog". simpl. *)
  (*   iApply refines_step_r ; simpl. *)
  (*   iIntros (? j) "HK'". *)
  (*   tp_alloc j as l "Hl". *)
  (*   iModIntro. iExists _. iFrame. by iApply "Hlog". *)
  (* Qed. *)

  (* Lemma refines_alloctape_r K N z t A : *)
  (*   TCEq N (Z.to_nat z) → *)
  (*   (∀ α : loc, α ↪ₛN (N; []) -∗ REL t << fill K (of_val #lbl:α) : A)%I *)
  (*   ⊢ REL t << fill K (alloc #z) : A. *)
  (* Proof. *)
  (*   iIntros (->) "Hlog". *)
  (*   iApply refines_step_r. *)
  (*   iIntros (K' j) "HK'". *)
  (*   tp_allocnattape j α as "Hα". *)
  (*   iModIntro. iExists _. iFrame. *)
  (*   iApply "Hlog". *)
  (*   iFrame; auto. *)
  (* Qed. *)

  (* Lemma refines_fork e : *)
  (*   (REL e : ()%lrel) -∗ *)
  (*   REL Fork e : (). *)
  (* Proof. *)
  (*   rewrite refines_eq /refines_def. *)
  (*   iIntros "H". *)
  (*   (* iIntros (K j) "Hs /=". *) *)
  (*   (* tp_fork j as k' "Hk'". *) *)
  (*   (* rewrite -(fill_empty e'). *) *)
  (*   wp_apply (wp_fork with "[-]"); last done. *)
  (*   iNext. *)
  (*   by iApply (wp_wand with "[$]"). *)
  (* Qed. *)

  (* Lemma refines_xchg_l K l e v' A : *)
  (*   IntoVal e v' → *)
  (*   (∃ v, ▷ l ↦ v ∗ *)
  (*     ▷(l ↦ v' -∗ REL fill K (of_val v) : A)) *)
  (*   ⊢ REL fill K (Xchg #l e) : A. *)
  (* Proof. *)
  (*   iIntros (<-) "Hlog". *)
  (*   iApply refines_wp_l. *)
  (*   iDestruct "Hlog" as (v) "[Hl Hlog]". *)
  (*   iApply (wp_xchg _ _ _ v' with "[$]"); auto. *)
  (* Qed.  *)
  (* (*   iIntros (<-) "Hlog". *) *)
  (* (*   iApply refines_atomic_l; auto. *) *)
  (* (*   iMod "Hlog" as (v) "[Hl Hlog]". iModIntro. *) *)
  (* (*   iApply (wp_xchg _ _ _ v' with "Hl"); auto. *) *)
  (* (* Qed. *) *)

  (* Lemma refines_cmpxchg_l K l e1 e2 v1 v2 A : *)
  (*   IntoVal e1 v1 → *)
  (*   IntoVal e2 v2 → *)
  (*   val_is_unboxed v1 → *)
  (*   (∃ v', ▷ l ↦ v' ∗ *)
  (*    (⌜v' ≠ v1⌝ -∗ ▷ (l ↦ v' -∗ REL fill K (of_val (v', #false)) : A)) ∧ *)
  (*    (⌜v' = v1⌝ -∗ ▷ (l ↦ v2 -∗ REL fill K (of_val (v', #true)) : A))) *)
  (*   ⊢ REL fill K (CmpXchg #l e1 e2) : A. *)
  (* Proof. *)
  (*   iIntros (<- <-?) "Hlog". *)
  (*   iApply refines_wp_l. *)
  (*   iDestruct "Hlog" as (v') "[Hl Hlog]".  *)
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
  (* (*   iIntros (<-<-?) "Hlog". *) *)
  (* (*   iApply refines_atomic_l; auto. *) *)
  (* (*   iMod "Hlog" as (v') "[Hl Hlog]". iModIntro. *) *)
  (* (*   destruct (decide (v' = v1)). *) *)
  (* (*   - (* CmpXchg successful *) subst. *) *)
  (* (*     iApply (wp_cmpxchg_suc with "Hl"); eauto. *) *)
  (* (*     { by right. } *) *)
  (* (*     iDestruct "Hlog" as "[_ Hlog]". *) *)
  (* (*     iSpecialize ("Hlog" with "[]"); eauto. *) *)
  (* (*   - (* CmpXchg failed *) *) *)
  (* (*     iApply (wp_cmpxchg_fail with "Hl"); eauto. *) *)
  (* (*     { by right. } *) *)
  (* (*     iDestruct "Hlog" as "[Hlog _]". *) *)
  (* (*     iSpecialize ("Hlog" with "[]"); eauto. *) *)
  (* (* Qed. *) *)

  (* Lemma refines_faa_l K l e2 (i2 : Z) A : *)
  (*   IntoVal e2 #i2 → *)
  (*   (∃ (i1 : Z), ▷ l ↦ #i1 ∗ *)
  (*    ▷ (l ↦ #(i1 + i2) -∗ REL fill K (of_val #i1) : A)) *)
  (*   ⊢ REL fill K (FAA #l e2) : A. *)
  (* Proof. *)
  (*   iIntros (<-) "Hlog". *)
  (*   iApply refines_wp_l; auto. *)
  (*   iDestruct "Hlog" as (i1) "[Hl Hlog]". *)
  (*   wp_faa. iModIntro. *)
  (*   by iApply "Hlog". *)
  (* Qed. *)

  (* Lemma refines_xchg_r K l e1 v1 v t A : *)
  (*   IntoVal e1 v1 → *)
  (*   l ↦ₛ v ⊢ *)
  (*   (l ↦ₛ v1 -∗ REL t << fill K (of_val v) : A) *)
  (*   -∗ REL t << fill K (Xchg #l e1) : A. *)
  (* Proof. *)
  (*   rewrite /IntoVal. iIntros (<-) "Hl Hlog". *)
  (*   iApply refines_step_r. *)
  (*   iIntros (k j) "Hk". *)
  (*   tp_xchg j. iExists v. iModIntro. iFrame. *)
  (*   by iApply "Hlog". *)
  (* Qed. *)

  (* Lemma refines_cmpxchg_fail_r K l e1 e2 v1 v2 v t A : *)
  (*   IntoVal e1 v1 → *)
  (*   IntoVal e2 v2 → *)
  (*   vals_compare_safe v v1 → *)
  (*   v ≠ v1 → *)
  (*   l ↦ₛ v ⊢ *)
  (*   (l ↦ₛ v -∗ REL t << fill K (of_val (v, #false)) : A) *)
  (*   -∗ REL t << fill K (CmpXchg #l e1 e2) : A. *)
  (* Proof. *)
  (*   rewrite /IntoVal. iIntros (<-<-??) "Hl Hlog". *)
  (*   iApply refines_step_r. *)
  (*   iIntros (k j) "Hk". *)
  (*   tp_cmpxchg_fail j. *)
  (*   iModIntro. iExists _. iFrame. by iApply "Hlog". *)
  (* Qed. *)

  (* Lemma refines_cmpxchg_suc_r K l e1 e2 v1 v2 v t A : *)
  (*   IntoVal e1 v1 → *)
  (*   IntoVal e2 v2 → *)
  (*   vals_compare_safe v v1 → *)
  (*   v = v1 → *)
  (*   l ↦ₛ v ⊢ *)
  (*   (l ↦ₛ v2 -∗ REL t << fill K (of_val (v, #true)) : A) *)
  (*   -∗ REL t << fill K (CmpXchg #l e1 e2) : A. *)
  (* Proof. *)
  (*   rewrite /IntoVal. iIntros (<-<-??) "Hl Hlog". *)
  (*   iApply refines_step_r. *)
  (*   iIntros (k j) "Hk". *)
  (*   tp_cmpxchg_suc j. *)
  (*   iModIntro. iExists _. iFrame. by iApply "Hlog". *)
  (* Qed. *)

  (* Lemma refines_faa_r K l e2 (i1 i2 : Z) t A : *)
  (*   IntoVal e2 #i2 → *)
  (*   l ↦ₛ #i1 -∗ *)
  (*   (l ↦ₛ #(i1+i2) -∗ REL t << fill K (of_val #i1) : A) *)
  (*   -∗ REL t << fill K (FAA #l e2) : A. *)
  (* Proof. *)
  (*   rewrite /IntoVal. iIntros (<-) "Hl Hlog". *)
  (*   iApply refines_step_r. *)
  (*   iIntros (k j) "Hk". *)
  (*   tp_faa j. *)
  (*   iModIntro. iExists _. iFrame. by iApply "Hlog". *)
  (* Qed. *)

  
End rules.
