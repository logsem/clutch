(** * Derived laws for [flip] *)
From iris.base_logic Require Import invariants na_invariants.
From self.prob_lang Require Import notation proofmode primitive_laws spec_rules spec_tactics.
From self.logrel Require Import model rel_rules rel_tactics.
From self.prelude Require Import base.
From self.examples.lib Require Import conversion. 

Definition flipL (e : expr) := int_to_bool (rand #1%nat from e)%E.
Definition flip := flipL #().
Definition allocB := alloc #1%nat.

Notation "l ↪b bs" := (l ↪ (1; bool_to_fin <$> (bs : list bool)))%I
  (at level 20, format "l  ↪b  bs") : bi_scope.
Notation "l ↪ₛb bs" := (l ↪ₛ (1; bool_to_fin <$> (bs : list bool)))%I
  (at level 20, format "l  ↪ₛb  bs") : bi_scope.

Section specs.
  Context `{clutchRGS Σ}.
   
  Lemma wp_allocB_tape E :
    {{{ True }}} allocB @ E {{{ α, RET #lbl:α; α ↪b [] }}}.
  Proof. iIntros (Φ) "_ HΦ". by iApply wp_alloc_tape. Qed.

  Lemma wp_flip E :
    {{{ True }}} flip @ E {{{ (b : bool), RET #(LitBool b); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /flip /flipL.
    wp_bind (rand _ from _)%E.
    wp_apply (wp_rand 1 with "[//]").
    iIntros (?) "_ /=".
    wp_apply (wp_int_to_bool with "[//]").
    iIntros "_".
    by iApply "HΦ".
  Qed.

  Lemma wp_flip_tape E α b bs :
    {{{ ▷ α ↪b (b :: bs) }}} flipL #lbl:α @ E {{{ RET #(LitBool b); α ↪b bs }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ". rewrite /flip /flipL. 
    wp_bind (rand _ from _)%E.   
    wp_apply (wp_rand_tape 1 with "Hl").
    iIntros "Hl /=".
    wp_apply (wp_int_to_bool with "[//]").
    iIntros "_".
    rewrite Z_to_bool_of_nat bool_to_fin_to_nat_inv.
    by iApply "HΦ".
  Qed.

  Lemma wp_flip_tape_empty E α :
    {{{ ▷ α ↪b [] }}} flipL #lbl:α @ E {{{ b, RET #(LitBool b); α ↪b [] }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ". rewrite /flip /flipL.
    wp_bind (rand _ from _)%E.
    wp_apply (wp_rand_tape_empty with "Hl").
    iIntros (n) "Hl /=".
    wp_apply (wp_int_to_bool with "[//]").
    iIntros "_".
    by iApply "HΦ".
  Qed.

  Lemma refines_right_allocB_tape E K :
    nclose specN ⊆ E →
    refines_right K allocB ={E}=∗ ∃ α, refines_right K (#lbl: α) ∗ α ↪ₛb [].
  Proof.
    iIntros (?) "(?&?)".
    iMod (step_alloctape with "[$]") as (α) "[? ?]"; [done|].
    iModIntro; iExists _; iFrame. done. 
  Qed. 

  Lemma refines_right_flip_tape E K α (b : bool) bs :
    nclose specN ⊆ E →
    α ↪ₛb (b :: bs) -∗
    refines_right K (flipL #lbl:α) ={E}=∗ refines_right K #(LitBool b) ∗ α ↪ₛb bs.
  Proof.
    iIntros (?) "Hα Hr". rewrite /flipL.    
    tp_bind (rand _ from _ )%E.
    rewrite refines_right_bind.
    iDestruct "Hr" as "[#Hinv Hr]".
    iMod (step_rand with "[$]") as "(_ & Hj & Hl) /="; [done|].
    iMod (refines_right_int_to_bool with "[$Hinv $Hj]") as "Hr"; [done|].
    rewrite Z_to_bool_of_nat bool_to_fin_to_nat_inv.
    by iFrame "Hr Hl". 
  Qed.

  (** * Tape allocation  *)
  Lemma refines_allocB_tape_l K E N z t A :
    TCEq N (Z.to_nat z) →
    (▷ (∀ α : loc, α ↪b [] -∗ REL fill K (of_val #lbl:α) << t @ E : A))%I
    -∗ REL fill K allocB << t @ E : A.
  Proof. iIntros (?) "?". by iApply refines_alloctape_l. Qed.

  Lemma refines_allocB_tape_r E K N z t A :
    TCEq N (Z.to_nat z) →
    (∀ α : loc, α ↪ₛb [] -∗ REL t << fill K (of_val #lbl:α) @ E : A)%I
    -∗ REL t << fill K allocB @ E : A.
  Proof. iIntros (?) "?". by iApply refines_alloctape_r. Qed. 

  (** * Unlabelled flip *)
  Lemma refines_flip_l E K t A :
     ▷ (∀ (b : bool), REL fill K (of_val #b) << t @ E : A)
    -∗ REL fill K flip << t @ E : A.
  Proof.
    iIntros "Hlog".
    iApply refines_wp_l.
    wp_apply (wp_flip with "[//]").
    eauto. 
  Qed.

  (* TODO: [refines_flip_r] *)
  
  (** * Labelled flip  *)
  Lemma refines_flipL_empty_l K E α A e :
    α ↪b [] ∗
      (∀ (b : bool), α ↪b [] -∗ REL fill K (Val #b) << e @ E : A)
    ⊢ REL fill K (flipL #lbl:α) << e @ E : A.
  Proof.
    iIntros "[Hα H]".
    iApply refines_wp_l.
    by wp_apply (wp_flip_tape_empty with "Hα"). 
  Qed.     

  Lemma refines_flipL_empty_r K E α A e :
    to_val e = None →
    α ↪ₛb [] ∗
      (∀ (b : bool), α ↪ₛb [] -∗ REL e << fill K (Val #b) @ E : A)
    ⊢ REL e << fill K (flipL #lbl:α) @ E : A.
  Proof.
    iIntros (ev) "[Hα H]". rewrite /flipL. 
    rel_bind_r (rand _ from _)%E.
    rel_apply_r refines_rand_empty_r; [done|].
    iFrame.
    iIntros (n) "Hα".
    rel_apply_r refines_step_r.
    iIntros (K') "Hr".
    iMod (refines_right_int_to_bool with "[$]"); [done|].
    iModIntro; iExists _; iFrame.
    by iApply "H".
  Qed.
  
  Lemma refines_flipL_l E K α b bs t A :
    (▷ α ↪b (b :: bs) ∗
     ▷ (α ↪b bs -∗ REL fill K (of_val #b) << t @ E : A))
    -∗ REL fill K (flipL #lbl:α) << t @ E : A.
  Proof.
    iIntros "[Hα Hlog]".
    iApply refines_wp_l.
    by wp_apply (wp_flip_tape with "Hα").
  Qed.

  Lemma refines_flipL_r E K α b bs t A :
    α ↪ₛb (b :: bs)
    -∗ (α ↪ₛb bs -∗ REL t << fill K (of_val #b) @ E : A)
    -∗ REL t << (fill K (flipL #lbl:α)) @ E : A.
  Proof.
    iIntros "Hα Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    iMod (refines_right_flip_tape with "[$] [$]") as "[? ?]"; [done|]. 
    iModIntro; iExists _; iFrame. iApply ("Hlog" with "[$]").
  Qed.

  (** * Coupling rules (equality) *)
  Lemma refines_couple_flip_tapes E e1 e2 A α αₛ bs bsₛ :
    to_val e1 = None →
    (αₛ ↪ₛb bsₛ ∗ α ↪b bs ∗
       (∀ b, αₛ ↪ₛb (bsₛ ++ [b]) ∗ α ↪b (bs ++ [b]) -∗ REL e1 << e2 @ E : A))
    ⊢ REL e1 << e2 @ E : A.
  Proof.
    iIntros (?) "(Hαs & Hα & Hlog)".
    iApply refines_couple_tapes; [done|iFrame].
    iIntros (n) "[? ?]".
    destruct (bool_to_fin_surj n) as [b <-].
    rewrite -list_fmap_singleton -!fmap_app. 
    iApply ("Hlog" $! b). iFrame. 
  Qed.

  Lemma refines_couple_tape_flip K' E α A bs e :
    to_val e = None →
    α ↪b bs ∗
      (∀ b, α ↪b (bs ++ [b]) -∗ REL e << fill K' (of_val #b) @ E : A)
    ⊢ REL e << fill K' flip @ E : A.
  Proof.
    iIntros (?) "[Hα Hcnt]". rewrite /flip/flipL.
    rel_bind_r (rand _ from _)%E.    
    rel_apply_r refines_couple_tape_rand; [done|iFrame].
    iIntros (n) "Hα".
    destruct (bool_to_fin_surj n) as [b <-].
    rewrite -list_fmap_singleton -!fmap_app.
    iSpecialize ("Hcnt" with "Hα").
    rel_apply_r refines_step_r.
    iIntros (K'') "Hr".
    iMod (refines_right_int_to_bool with "[$]"); [done|].
    iModIntro; iExists _; iFrame.
    rewrite Z_to_bool_of_nat bool_to_fin_to_nat_inv //.
  Qed.     

  Lemma refines_couple_flip_tape K E α A bs e :
    α ↪ₛb bs ∗
      (∀ b, α ↪ₛb (bs ++ [b]) -∗ REL fill K (of_val #b) << e @ E : A)
    ⊢ REL fill K flip << e @ E : A.
  Proof.
    iIntros "[Hαs Hcnt]". rewrite /flip/flipL.
    rel_bind_l (rand _ from _)%E.    
    rel_apply_l refines_couple_rand_tape; iFrame.    
    iIntros (n) "Hα".
    destruct (bool_to_fin_surj n) as [b <-].
    rewrite -list_fmap_singleton -!fmap_app.
    iSpecialize ("Hcnt" with "Hα").
    iApply refines_wp_l.
    wp_apply (wp_int_to_bool with "[//]").
    iIntros "_".
    rewrite Z_to_bool_of_nat bool_to_fin_to_nat_inv //.
  Qed.     

  Lemma refines_couple_flipL_flip K K' E α A :
    α ↪b [] ∗
      (∀ b : bool, α ↪b [] -∗ REL fill K (of_val #b) << fill K' (of_val #b) @ E : A)
    ⊢ REL fill K (flipL #lbl:α) << fill K' flip @ E : A.
  Proof.
    iIntros "(Hα & H)".
    iApply refines_couple_tape_flip.
    { rewrite fill_not_val //. }
    iFrame => /=. iIntros (b) "Hα".
    iApply (refines_flipL_l _ _ _ b []).
    iFrame. iApply "H".
  Qed.

  Lemma refines_couple_flip_flipL K K' E α A :
    α ↪ₛb [] ∗
      (∀ b : bool, α ↪ₛb [] -∗ REL fill K (of_val #b) << fill K' (of_val #b) @ E : A)
    ⊢ REL fill K flip << fill K' (flipL #lbl:α) @ E : A.
  Proof.
    iIntros "(Hα & H)".
    iApply refines_couple_flip_tape.
    iFrame.
    iIntros (n) "Hα".
    iApply (refines_flipL_r with "Hα").
    iIntros "α". by iApply "H".
  Qed.

  Lemma refines_couple_flip_flip K K' E A :
    (∀ b : bool, REL fill K (of_val #b) << fill K' (of_val #b) @ E : A)
    ⊢ REL fill K flip << fill K' flip @ E : A.
  Proof.
    iIntros "Hcnt". rewrite /flip/flipL.
    rel_bind_l (rand _ from _)%E.
    rel_bind_r (rand _ from _)%E.
    rel_apply_l refines_couple_rands_lr.
    iIntros (n).
    iApply refines_wp_l.
    wp_apply (wp_int_to_bool with "[//]").
    iIntros "_".
    rel_apply_r refines_step_r.
    iIntros (K'') "Hr".
    iMod (refines_right_int_to_bool with "[$]"); [done|].
    iModIntro; iExists _; iFrame.
    done. 
  Qed.     

  (* TODO: non-equality couplings *)
  
End specs.   


  
