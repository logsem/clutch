(* sem_judgements.v *)

(* This file contains the definition of semantic typing judgments. *)

From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import list.

From stdpp Require Import base gmap.

(* Local imports *)
From clutch.prob_eff_lang.probblaze Require Import notation mode sem_def sem_sig sem_row sem_types logic mode. 

(* Semantic typing judgment. *)

(* The semantic typing judgment is defined to be persistent
 * because we want the persistent resources it uses to only be 
 * from the environment Γ. *)
Definition sem_typed `{!probblazeRGS Σ}
  (Γ1 : env Σ)
  (e1 : expr)
  (e2 : expr)
  (ρ : sem_row Σ)
  (τ : sem_ty Σ) 
  (Γ2 : env Σ) : iProp Σ :=
    tc_opaque (□ (∀ (vs : gmap string (val * val)),
                    env_sem_typed Γ1 vs -∗ 
                    (BREL (subst_map (fst <$> vs) e1) ≤ (subst_map (snd <$> vs) e2) <| iLblSig_to_iLblThy ρ |> {{ λ v1 v2, τ v1 v2 ∗ env_sem_typed Γ2 vs }})))%I.

(* Semantic value typing judgment. *)
(* TODO: define an analogue of pwp (pure weakestpre) *)
(* The semantic value typing judgment only holds for pure expressions that do not perform any effects or reference operations *)
(* Definition sem_oval_typed `{!heapGS Σ}
     (Γ₁ : env Σ)
     (e : expr)
     (τ : sem_ty Σ) : iProp Σ :=
       tc_opaque (□ (∀ (vs : gmap string val),
                       env_sem_typed Γ₁ vs -∗ 
                       (PWP (subst_map vs e) [{ v, τ v }])))%I. *)

Global Instance sem_typed_persistent `{!probblazeRGS Σ} (Γ Γ' : env Σ) e1 e2 ρ τ :
  Persistent (sem_typed Γ e1 e2 ρ τ Γ').
Proof.
  unfold sem_typed, tc_opaque. apply _.
Qed.

(* Global Instance sem_oval_typed_persistent `{!heapGS Σ} (Γ : env Σ) e τ :
     Persistent (sem_oval_typed Γ e τ).
   Proof.
     unfold sem_oval_typed, tc_opaque. apply _.
   Qed. *)

Notation "Γ₁ ⊨ e1 ≤ e2 : ρ : τ ⫤ Γ₂" := (sem_typed Γ₁%EN e1%E e2%E ρ%R τ%T Γ₂%EN)
  (at level 74, e1, e2, ρ, τ at next level) : bi_scope.

Notation "⊨ e1 ≤ e2 : ρ : τ" := (sem_typed [] e1%E e2%E ρ%R τ%T [])
  (at level 74, e1, e2, ρ, τ at next level) : bi_scope.

(* Notation "Γ₁ ⊨ₚ e : α" := (sem_oval_typed Γ₁%EN e%E α%T)
     (at level 74, e, α at next level) : bi_scope.
   
   Notation "⊨ₚ e : α" := (sem_oval_typed [] e%E α%T [])
     (at level 74, e, α at next level) : bi_scope. *)

Definition sem_val_typed `{!probblazeRGS Σ} 
  (v1 v2 : val) 
  (A : sem_ty Σ) : iProp Σ := tc_opaque (□ (A v1 v2))%I.

Notation "⊨ᵥ v1 ≤ v2 : τ" := (sem_val_typed v1%V v2%V τ%T)
  (at level 20, v1, v2, τ at next level) : bi_scope.

(* The value semantic typing judgement is also defined
 * to be persistent, so only persistent values hold for it. *) 
Global Instance sem_typed_val_persistent `{!probblazeRGS Σ} v1 v2 τ :
  Persistent (sem_val_typed v1 v2 τ).
Proof.
  unfold sem_val_typed, tc_opaque. apply _.
Qed.
