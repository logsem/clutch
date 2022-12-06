From stdpp Require Import namespaces.
From iris Require Import invariants.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From self Require Import spec_rules rel_rules rel_tactics notation types proofmode model spec_tactics.
From self.examples Require Import lock.

Notation "'match:' e0 'with' | 'NONE' => e1 | 'SOME' x => e2 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing) : expr_scope.
Notation "'match:' e0 'with' | 'SOME' x => e2 | 'NONE' => e1 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing) : expr_scope.

Definition lazy α : expr :=
  let:"s" := ref NONE in
  let: "lk" := newlock #() in
  (λ:"_u",
    acquire "lk" ;;
    let:"r" := match: !"s" with
               | NONE => let: "b" := flip #lbl:α in
                         "s" <- SOME "b" ;;
                         "b"
               | SOME "b" => "b" end
    in
    release "lk" ;;
    "r").

Definition eager α : expr :=
  let:"b" := flip #lbl:α in
  (λ:"_u", "b").

Section proofs.
  Context `{!prelocGS Σ}.
  Context `{!lockG Σ}.

  Definition coinN := nroot.@"coins".

  (* Warmup: the flips have already been resolved. *)
  Lemma lazy_eager_refinement α β b bs bs' :
    (* TODO: should instead assume that REL α << αₛ : lrel_tape *)
    α ↪ (b::bs) ∗ β ↪ₛ (b::bs')
    -∗ REL lazy α << eager β : lrel_unit → lrel_bool.
  Proof using lockG0 prelocGS0 Σ.
    iIntros "[Hα Hβ]". rewrite /lazy /eager.
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

  Lemma eager_lazy_refinement α β b bs bs' :
    α ↪ (b::bs) ∗ β ↪ₛ (b::bs')
    -∗ REL eager α << lazy β : lrel_unit → lrel_bool.
  Proof using lockG0 prelocGS0 Σ.
    iIntros "[Hα Hβ]". rewrite /lazy /eager.
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
