From Autosubst Require Import Autosubst.
From self.prob_lang Require Export lang.
From self.prob_lang Require Import tactics.
From self.typing Require Export contextual_refinement.

(** Alternative formulation of contextual refinement without restricting to
    contexts of the ground type but only observing termination through their
    masses. *)
Definition ctx_refines_alt (Γ : stringmap type)
    (e e' : expr) (τ : type) : Prop := ∀ K σ₀ τ',
  typed_ctx K Γ τ ∅ τ' →
  (SeriesC (lim_exec_val (fill_ctx K e, σ₀)) <= SeriesC (lim_exec_val (fill_ctx K e', σ₀)))%R.

Lemma ctx_refines_impl_alt Γ e1 e2 τ :
  (Γ ⊨ e1 ≤ctx≤ e2 : τ) →
  ctx_refines_alt Γ e1 e2 τ.
Proof.
  intros H K σ0 τ' Hty.
  pose (K' := (CTX_AppR (λ: <>, #true)%E):: K).
  cut (∀ e, lim_exec_val ((e;; #true)%E, σ0) #true = SeriesC (lim_exec_val (e, σ0))).
  - intros Heq. rewrite -2!Heq.
    eapply (H K' σ0 true).
    repeat econstructor; eauto.
  - intros e.
    (* TODO: needs some more facts about [lim_exec_val]*)

Admitted.
