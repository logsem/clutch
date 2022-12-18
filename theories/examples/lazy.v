From stdpp Require Import namespaces.
From iris.base_logic Require Import invariants na_invariants.
From self.prob_lang Require Import notation proofmode primitive_laws spec_rules.
From self.logrel Require Import model rel_rules rel_tactics.
From self.examples Require Import lock.
From self.prelude Require Import base.

Set Default Proof Using "Type*".

Definition lazy_lk α : expr :=
  let:"s" := ref NONEV in
  let: "lk" := newlock #() in
  (λ:"_u",
    acquire "lk" ;;
    let:"r" := match: !"s" with
               | NONE => let: "b" := flip α in
                         "s" <- SOME "b" ;;
                         "b"
               | SOME "b" => "b" end
    in
    release "lk" ;;
    "r").

Definition lazy α : expr :=
  let:"s" := ref NONEV in
  (λ:"_u",
     match: !"s" with
     | NONE => let: "b" := flip α in
               "s" <- SOME "b" ;;
               "b"
     | SOME "b" => "b" end
  ).

Definition eager α : expr :=
  let:"b" := flip α in
  (λ:"_u", "b").

Definition lazy_lk' : expr :=
  let: "α" := alloc in lazy_lk "α".

Definition lazy' : expr :=
  let: "α" := alloc in lazy "α".

Definition eager' : expr :=
  let: "α" := alloc in eager "α".

Definition lazy_no_tapes : expr := lazy #().

Definition eager_no_tapes : expr := eager #().

Section proofs.
  Context `{!prelogrelGS Σ}.
  Context `{!lockG Σ}.

  Definition coinN := nroot.@"coins".

  (* Warmup: the flips have already been resolved. *)
  Lemma lazy_lk_eager_refinement e1 e2 α β b bs bs' :
    e1 = #lbl:α -> e2 = #lbl:β ->
    α ↪ (b::bs) ∗ β ↪ₛ (b::bs')
    -∗ REL lazy_lk e1 << eager e2 : lrel_unit → lrel_bool.
  Proof.
    iIntros (-> ->) "[Hα Hβ]". rewrite /lazy_lk /eager.
    rel_alloc_l l as "Hl" ; rel_pures_l ; rel_flip_r.
    rel_apply_l (refines_newlock_l coinN
                   (l ↦ NONEV ∗ α ↪ (b::bs) ∨ l ↦ SOMEV #b)%I
                  with "[-]") ; [by eauto with iFrame|].
    iIntros (lk γ) "!> #Hlk /=". rel_pures_l ; rel_pures_r.
    rel_arrow ; iIntros (v1 v2) "_".
    rel_pure_r ; rel_pure_l.
    rel_apply_l (refines_acquire_l with "Hlk").
    iIntros "!> Hlocked HI".
    rel_pures_l.
    iDestruct "HI" as "[[l_None α_b] | l_Some_b]" ; rel_load_l ; rel_pures_l.
    1: rel_flip_l ; rel_pures_l ; rel_store_l ; rel_pures_l.
    all: rel_apply_l (refines_release_l with "Hlk Hlocked [-]") ;
      [iFrame | iNext] ;
      rel_pures_l ; rel_values.
  Qed.

  Lemma lazy_lk_eager_refinement' :
    ⊢ REL lazy_lk' << eager' : lrel_unit → lrel_bool.
  Proof.
    rewrite /lazy_lk' /eager'.
    rel_alloctape_l α as "Hα".
    rel_alloctape_r β as "Hβ".
    rel_pures_l ; rel_pures_r.
    iApply (refines_couple_tapes with "[$Hα $Hβ]"); [done|done|].
    iIntros "(%b & Hβ & Hα)".
    iApply lazy_lk_eager_refinement ; auto ; iFrame.
  Qed.

  Lemma lazy_lk_eager_refinement'' α β :
    (REL α << β : lrel_tape)
      ⊢ REL lazy_lk α << eager β : lrel_unit → lrel_bool.
  Proof.
  Admitted.

  Lemma eager_lazy_lk_refinement e1 e2 α β b bs bs' :
    e1 = #lbl:α -> e2 = #lbl:β ->
    α ↪ (b::bs) ∗ β ↪ₛ (b::bs')
    -∗ REL eager e1 << lazy_lk e2 : lrel_unit → lrel_bool.
  Proof.
    iIntros (-> ->) "[Hα Hβ]". rewrite /lazy_lk /eager.
    rel_alloc_r l as "Hl" ; rel_pures_r ; rel_flip_l.
    rel_apply_r (refines_newlock_r).
    iIntros (lk) "Hlk".
    iMod (inv_alloc coinN _
           (is_locked_r lk false ∗
              (β ↪ₛ (b::bs') ∗ l ↦ₛ NONEV ∨ l ↦ₛ SOMEV #b))%I
            with "[-]") as "#Hinv" ;
      [by eauto with iFrame|].
    rel_pures_l ; rel_pures_r.
    rel_arrow ; iIntros (v1 v2) "_". rel_pure_r.
    (* We need to open Hinv in order to acquire the lock on the right. In order
       to use the invariant, we need to step on the left to produce a later. *)
    rel_bind_l (_ _).
    iApply refines_atomic_l .
    iIntros (K') "Hr".
    iInv coinN as "Hlk" "Hclose". iModIntro.
    wp_pures.
    iDestruct "Hlk" as "[Hlk [(Hβ & Hl) | Hl]]".
    Admitted.
    (* { rel_apply_r (refines_acquire_r with "Hlk"). *)

    (*   rel_apply_r (refines_acquire_r with "Hlk"); *)
    (*   iIntros "Hlk" ; rel_pure_r ; rel_load_r ; rel_pures_r. *)
    (*   1: rel_flip_r ; rel_pures_r ; rel_store_r ; rel_pures_r. *)
    (* all: rel_apply_r (refines_release_r with "Hlk [-]") ; iIntros "Hlk" ; *)
    (*   rel_pures_r ; rel_values. *)
    (* all: iMod ("Hclose" with "[Hlk Hl]") ; [iFrame | eauto]. *)
  (* Qed. *)

  Lemma eager_lazy_lk_refinement' :
    ⊢ REL eager' << lazy_lk' : lrel_unit → lrel_bool.
  Proof using lockG0 prelogrelGS0 Σ.
    rewrite /lazy_lk' /eager'.
    rel_alloctape_l α as "Hα" ; rel_alloctape_r β as "Hβ".
    rel_pures_l ; rel_pures_r.
    iApply (refines_couple_tapes with "[$Hα $Hβ]"); [done|done|].
    iIntros "(%b & Hβ & Hα)".
    iApply eager_lazy_lk_refinement ; auto ; iFrame.
  Qed.

  Lemma eager_lazy_refinement e1 e2 α β b bs bs' :
    e1 = #lbl:α -> e2 = #lbl:β ->
    α ↪ (b::bs) ∗ β ↪ₛ (b::bs')
    -∗ REL eager e1 << lazy e2 : lrel_unit → lrel_bool.
  Proof using lockG0 prelogrelGS0 Σ.
    iIntros (-> ->) "[Hα Hβ]". rewrite /lazy /eager.
    rel_alloc_r l as "Hl" ; rel_pures_r ; rel_flip_l.
    set (P := ((β ↪ₛ (b::bs') ∗ l ↦ₛ NONEV) ∨ (β ↪ₛ bs' ∗ l ↦ₛ SOMEV #b))%I).
    (* Allocate the invariant P *)
    iMod (na_inv_alloc prelogrelGS_nais _ coinN P with "[-]") as "#Hinv" ;
      [by subst P ; eauto with iFrame|].
    rel_pures_l ; rel_pures_r.
    rel_arrow ; iIntros (v1 v2) "_". rel_pure_r.
    (* Open the invariant. *)
    iApply (refines_na_inv with "[$Hinv]") ; auto ; iIntros "[HP Hclose]".
    (* Compute to strip the later off ▷ P *)
    rel_pures_l.
    (* Case match the different values of (! #l). *)
    iDestruct "HP" as "[(Hβ & Hl) | (Hβ & Hl)]" ; rel_load_r ; rel_pures_r.
    1: rel_flip_r ; rel_pures_r ; rel_store_r ; rel_pures_r.
    (* Re-establish the invariant *)
    all: iAssert (▷ P)%I with "[Hβ Hl]" as "HP" ; [subst P ; eauto with iFrame|].
    (* We have two ways to finish up, either via the return rule that gives us
       back the left-over part of the token, or via the general relational rule
       for closing invariants. *)
    - rel_values_na ; iIntros "Hnais".
      iDestruct ("Hclose" with "[-]") as "Hnais" ; iFrame.
      (* TODO: why is the iMod "Hnais" needed? Shouldn't iModIntro already
         strip the |={⊤}=> off? *)
      iMod "Hnais" ; iModIntro.
      iFrame ; eauto.
    - iApply (refines_na_close with "[$Hclose $HP]"). rel_values.
  Qed.

  Lemma eager_lazy_refinement' :
    ⊢ REL eager' << lazy' : lrel_unit → lrel_bool.
  Proof.
    rewrite /lazy' /eager'.
    rel_alloctape_l α as "Hα" ; rel_alloctape_r β as "Hβ".
    rel_pures_l ; rel_pures_r.
    iApply (refines_couple_tapes with "[$Hα $Hβ]"); [done|done|].
    iIntros "(%b & Hβ & Hα)".
    iApply eager_lazy_refinement ; auto ; iFrame.
  Qed.

  (* This is exactly the same as the symmetric refinement, mutatis mutandis. *)
  Lemma lazy_eager_refinement e1 e2 α β b bs bs' :
    e1 = #lbl:α -> e2 = #lbl:β ->
    α ↪ (b::bs) ∗ β ↪ₛ (b::bs')
    -∗ REL lazy e1 << eager e2 : lrel_unit → lrel_bool.
  Proof using lockG0 prelogrelGS0 Σ.
    iIntros (-> ->) "[Hα Hβ]". rewrite /lazy /eager.
    rel_alloc_l l as "Hl" ; rel_pures_l ; rel_flip_r.
    set (P := ((α ↪ (b::bs) ∗ l ↦ NONEV) ∨ (α ↪ bs ∗ l ↦ SOMEV #b))%I).
    iMod (na_inv_alloc prelogrelGS_nais _ coinN P with "[-]") as "#Hinv" ;
      [by subst P ; eauto with iFrame|].
    rel_pures_l ; rel_pures_r.
    rel_arrow ; iIntros (v1 v2) "_". rel_pure_r.
    iApply (refines_na_inv with "[$Hinv]") ; auto ; iIntros "[HP Hclose]".
    rel_pures_l.
    iDestruct "HP" as "[(Hβ & Hl) | (Hβ & Hl)]" ; rel_load_l ; rel_pures_l.
    1: rel_flip_l ; rel_pures_l ; rel_store_l ; rel_pures_l.
    all: iAssert (▷ P)%I with "[Hβ Hl]" as "HP" ; [subst P ; eauto with iFrame|].
    all: iApply (refines_na_close with "[$Hclose $HP]") ; rel_values.
  Qed.

  Lemma lazy_lazy_no_tapes_refinement :
    ⊢ REL lazy' << lazy_no_tapes : lrel_unit → lrel_bool.
  Proof.
    rewrite /lazy' /lazy_no_tapes /lazy.
    rel_alloctape_l α as "Hα".
    rel_pures_l.
    rel_alloc_l l as "Hl".
    rel_pures_l.
    rel_alloc_r l' as "Hl'".
    rel_pures_r.
    iMod (na_inv_alloc prelogrelGS_nais _ coinN
            (α ↪ [] ∗ (l ↦ NONEV ∗ l' ↦ₛ NONEV ∨ ∃ (b: bool), l ↦ SOMEV #b ∗ l' ↦ₛ SOMEV #b))
           with "[-]") as "#Hinv".
    { iFrame. iLeft. iFrame. }
    rel_arrow_val.
    iIntros (?? [-> ->]).
    rel_pures_l.
    rel_pure_r.
    iApply (refines_na_inv with "[$Hinv]"); [done|done|].
    iIntros "[(Hα & [[Hl Hl'] | >[%b [Hl Hl']]]) Hclose]".
    - rel_load_l. rel_pures_l.
      rel_load_r. rel_pures_r.
      rel_bind_l (flip _)%E.
      rel_bind_r (flip _)%E.
      iApply (refines_couple_flips_l with "[-$Hα]"); [done|].
      iIntros (b) "Hα /=".
      rel_pures_l. rel_store_l. rel_pures_l.
      rel_pures_r. rel_store_r. rel_pures_r.
      iApply (refines_na_close with "[- $Hclose $Hα]").
      iSplitR; [rel_values|].
      iRight. iModIntro. iExists _. iFrame.
    - rel_load_l. rel_pures_l.
      rel_load_r. rel_pures_r.
      iApply (refines_na_close with "[- $Hclose $Hα]").
      iSplitR; [rel_values|].
      iRight. iModIntro. iExists _. iFrame.
  Qed.

  Lemma eager_no_tapes_eager_refinement :
    ⊢ REL eager_no_tapes << eager' : lrel_unit → lrel_bool.
  Proof.
    rewrite /eager_no_tapes /eager' /eager.
    rel_alloctape_r α as "Hα".
    rel_pures_r.
    rel_bind_l (flip _)%E.
    rel_bind_r (flip _)%E.
    iApply (refines_couple_flips_r with "[-$Hα]"); [done|].
    iIntros (b) "Hα /=".
    rel_pures_l.
    rel_pures_r.
    rel_arrow_val.
    iIntros (?? _).
    rel_pures_l.
    rel_pures_r.
    rel_values.
  Qed.

End proofs.
