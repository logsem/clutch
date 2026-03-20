(* mode.v *)

(* This file contains properties of modes and mode-related definitions. *)

From iris.proofmode Require Import base proofmode.
From iris.algebra Require Import ofe gmap.
From iris.base_logic Require Export iprop upred invariants.

(* Local imports *)
From clutch.prob_eff_lang.probblaze Require Import logic sem_def notation.

Definition mode_glb m m' : mode :=
  match m with
    OS => OS 
  | MS => m'
  end.

Definition mode_lub m m' : mode :=
  match m with
    MS => MS
  | OS => m'
  end.

Global Instance mode_meet : Meet mode := mode_glb.
Global Instance mode_join : Join mode := mode_lub.

Lemma mode_glb_idemp (m : mode) :
  m ⊓ m = m.
Proof. by destruct m. Qed.

Lemma mode_glb_assoc (m₁ m₂ m₃ : mode) :
  m₁ ⊓ (m₂ ⊓ m₃) = ((m₁ ⊓ m₂) ⊓ m₃).
Proof. by destruct m₁. Qed.

Lemma mode_glb_comm (m₁ m₂ : mode) :
  m₁ ⊓ m₂ = m₂ ⊓ m₁.
Proof. by destruct m₁, m₂. Qed.

Lemma mode_glb_os m :
  OS ⊓ m = OS.
Proof. destruct m; eauto. Qed.

Lemma mode_lub_idemp (m : mode) :
  m ⊔ m = m.
Proof. by destruct m. Qed.

Lemma mode_lub_assoc (m₁ m₂ m₃ : mode) :
  m₁ ⊔ (m₂ ⊔ m₃) = ((m₁ ⊔ m₂) ⊔ m₃).
Proof. by destruct m₁. Qed.

Lemma mode_lub_comm (m₁ m₂ : mode) :
  m₁ ⊔ m₂ = m₂ ⊔ m₁.
Proof. by destruct m₁, m₂. Qed.

Lemma mode_lub_ms m :
  MS ⊔ m = MS.
Proof. destruct m; eauto. Qed.

Section mode_sub_typing.

  (* Sub-Typing on Mode *)
  
  Lemma mode_le_refl {Σ} (m : mode) : ⊢ (m ≤ₘ m : iProp Σ).
  Proof. by iLeft. Qed.
  
  Lemma mode_le_trans {Σ} (m1 m2 m3 : mode) : 
    m1 ≤ₘ m2 -∗
    m2 ≤ₘ m3 -∗
    (m1 ≤ₘ m3 : iProp Σ).
  Proof. iIntros "#H12 H23". destruct m1,m2,m3; eauto. Qed.
  
  Lemma mode_le_MS {Σ} (m : mode) : 
    ⊢ (m ≤ₘ MS : iProp Σ).
  Proof. by iRight. Qed.
  
  Lemma mode_lub_le {Σ} (m₁ m₁' m₂ m₂' : mode) :
    m₁ ≤ₘ m₁' -∗ m₂ ≤ₘ m₂' -∗
    m₁ ⊔ m₂ ≤ₘ@{ Σ } m₁' ⊔ m₂'.
  Proof. iIntros "Hm₁₁' Hm₂₂'". destruct m₁,m₂,m₁',m₂'; eauto. Qed.
  
  Lemma mode_le_OS {Σ} (m : mode) : 
    ⊢ (OS ≤ₘ m : iProp Σ).
  Proof. destruct m; eauto. Qed.
  
  Lemma mode_le_OS_inv {Σ} (m : mode) : 
    (m ≤ₘ@{ Σ } OS ) -∗ m ≡ OS.
  Proof.
    iIntros "H". destruct m; first done.
    iDestruct "H" as "%H". inv H.
  Qed.

End mode_sub_typing.

Section mode_type_sub.

  Class ModeTypeSub {Σ} (m : mode) (τ : sem_ty Σ) := {
    mode_type_sub : ⊢ (∀ v1 v2, τ v1 v2 -∗ □? m (τ v1 v2))
  }.
  
  Global Instance mode_type_sub_os {Σ} (τ : sem_ty Σ) : ModeTypeSub OS τ.
  Proof. constructor. iIntros "% % /= $ //". Qed.

End mode_type_sub.
  
Section mode_env_sub.

  Class ModeEnvSub {Σ} (m : mode) (Γ : env Σ) := {
    mode_env_sub : ⊢ (∀ γ, Γ ⊨ₑ γ -∗ □? m (Γ ⊨ₑ γ))
  }.

  Global Instance mode_env_sub_os {Σ} (Γ : env Σ) : ModeEnvSub OS Γ.
  Proof. constructor. iIntros "% /= $ //". Qed.
  
End mode_env_sub.

(* Notations *)
Notation "m ₘ⪯ₜ τ" := (ModeTypeSub m τ%T) (at level 80).
Notation "m ₘ⪯ₑ Γ" := (ModeEnvSub m Γ%T) (at level 80).
