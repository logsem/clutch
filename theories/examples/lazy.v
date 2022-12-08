From stdpp Require Import namespaces.
From iris Require Import prelude.options base_logic.lib.invariants.
From self.prob_lang Require Import notation proofmode primitive_laws.
From self.logrel Require Import model rel_rules rel_tactics.
From self.examples Require Import lock.

Definition lazy α : expr :=
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

Definition eager α : expr :=
  let:"b" := flip α in
  (λ:"_u", "b").

Section proofs.
  Context `{!prelocGS Σ}.
  Context `{!lockG Σ}.

  Definition coinN := nroot.@"coins".

  (* Warmup: the flips have already been resolved. *)
  Lemma lazy_eager_refinement e1 e2 α β b bs bs' :
    e1 = #lbl:α -> e2 = #lbl:β ->
    α ↪ (b::bs) ∗ β ↪ₛ (b::bs')
    -∗ REL lazy e1 << eager e2 : lrel_unit → lrel_bool.
  Proof using lockG0 prelocGS0 Σ.
    iIntros (-> ->) "[Hα Hβ]". rewrite /lazy /eager.
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

  Definition lazy' : expr :=
    let: "α" := alloc in lazy "α".

  Definition eager' : expr :=
    let: "α" := alloc in eager "α".

  Lemma lazy_eager_refinement' :
    ⊢ REL lazy' << eager' : lrel_unit → lrel_bool.
  Proof using lockG0 prelocGS0 Σ.
    rewrite /lazy' /eager'.
    rel_alloctape_l α as "Hα".
    rel_alloctape_r β as "Hβ".
    rel_pures_l ; rel_pures_r.
    iApply refines_couple_tapes ; [ by unfold lazy | iFrame ].
    iIntros "(%b & Hβ & Hα)".
    iApply lazy_eager_refinement ; auto ; iFrame.
  Qed.

  Lemma lazy_eager_refinement'' α β :
    (REL α << β : lrel_tape)
      ⊢ REL lazy α << eager β : lrel_unit → lrel_bool.
  Proof using lockG0 prelocGS0 Σ.
  Admitted.

  Lemma eager_lazy_refinement e1 e2 α β b bs bs' :
    e1 = #lbl:α -> e2 = #lbl:β ->
    α ↪ (b::bs) ∗ β ↪ₛ (b::bs')
    -∗ REL eager e1 << lazy e2 : lrel_unit → lrel_bool.
  Proof using lockG0 prelocGS0 Σ.
    iIntros (-> ->) "[Hα Hβ]". rewrite /lazy /eager.
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
    iInv coinN as "Hlk" "Hclose". iModIntro.
    wp_pures. iIntros "!> /=".
    iDestruct "Hlk" as "[Hlk [(Hβ & Hl) | Hl]]" ;
      rel_apply_r (refines_acquire_r with "Hlk");
      iIntros "Hlk" ; rel_pure_r ; rel_load_r ; rel_pures_r.
      1: rel_flip_r ; rel_pures_r ; rel_store_r ; rel_pures_r.
    all: rel_apply_r (refines_release_r with "Hlk [-]") ; iIntros "Hlk" ;
      rel_pures_r ; rel_values.
    all: iMod ("Hclose" with "[Hlk Hl]") ; [iFrame | eauto].
  Qed.

  Lemma eager_lazy_refinement' :
    ⊢ REL eager' << lazy' : lrel_unit → lrel_bool.
  Proof using lockG0 prelocGS0 Σ.
    rewrite /lazy' /eager'.
    rel_alloctape_l α as "Hα" ; rel_alloctape_r β as "Hβ".
    rel_pures_l ; rel_pures_r.
    iApply refines_couple_tapes ; [ by unfold lazy | iFrame ].
    iIntros "(%b & Hβ & Hα)".
    iApply eager_lazy_refinement ; auto ; iFrame.
  Qed.

End proofs.
