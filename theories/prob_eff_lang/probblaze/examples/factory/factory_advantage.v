(* Factories: a system [e] is given to the environment as the value
   [λ<>, e].  Every call starts a fresh session, so the environment decides
   when, and how often, sessions are created, and it may act before the first
   one.  A system is evaluated (its state allocated) only inside a call.

   - [sem_val_typed_factory]: a relation between two systems is a relation
     between their factories at the multi-session type [𝟙 → τ];
   - [advantage_zero_f]: perfect steps between factories;
   - [advantage_reduction_f]: a reduction [λ x. A (λ<>, C)] applied to a value
     is a β-step and one step of the inner λ to a value.  It is purely
     operational: neither [C] nor the argument needs to be typed;
   - [sem_typed_call_l]/[_r]: calling a factory is a pure step. *)

From iris.proofmode Require Import base proofmode classes.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory semantics adequacy.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze Require Import advantage uc_composition.
From Stdlib Require Import Reals Psatz.

#[local] Open Scope R_scope.
#[local] Set Default Proof Using "All".

Section factory_typing.
  Context `{!probblazeRGS Σ}.

  Lemma sem_val_typed_factory e1 e2 τ :
    ⊢ sem_typed [] e1 e2 ⊥ τ [] -∗ ⊨ᵥ (λ: <>, e1)%V ≤ (λ: <>, e2)%V : (𝟙 → τ)%T.
  Proof. iIntros "#He". by iApply (sem_typed_closure _ _ _ BAnon BAnon _ _ MS). Qed.

  Lemma sem_typed_call_l e1 e2 τ :
    is_closed_expr ∅ e1 →
    ⊢ sem_typed [] e1 e2 ⊥ τ [] -∗ sem_typed [] ((λ: <>, e1)%V #()%V) e2 ⊥ τ [].
  Proof.
    iIntros (Hc) "#He !# %vs Hvs /=". iSpecialize ("He" with "Hvs").
    rewrite (subst_map_is_closed_empty _ _ Hc). by brel_pures_l 1%nat.
  Qed.

  Lemma sem_typed_call_r e1 e2 τ :
    is_closed_expr ∅ e2 →
    ⊢ sem_typed [] e1 e2 ⊥ τ [] -∗ sem_typed [] e1 ((λ: <>, e2)%V #()%V) ⊥ τ [].
  Proof.
    iIntros (Hc) "#He !# %vs Hvs /=". iSpecialize ("He" with "Hvs").
    rewrite (subst_map_is_closed_empty _ _ Hc). by brel_pures_r 1%nat.
  Qed.

End factory_typing.

Section factory_advantage.
  Context `{!probblazeRGpreS Σ}.

  Lemma advantage_zero_f (A : val) (e e' : expr) (b : bool) (τ : ∀ `{probblazeRGS Σ}, sem_ty Σ) :
    (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A ((𝟙 → τ) → 𝔹)%T) →
    (∀ `{probblazeRGS Σ}, ⊢ sem_typed [] e e' ⊥ τ []) →
    (∀ `{probblazeRGS Σ}, ⊢ sem_typed [] e' e ⊥ τ []) →
    advantage A (λ: <>, e)%V (λ: <>, e')%V #b <= 0.
  Proof.
    intros HA He He'. right.
    apply (sem_val_typed_advantage _ _ _ (λ H : probblazeRGS Σ, 𝟙 → τ H)%T); [done|split];
      intros HRGS; iApply sem_val_typed_factory; [iApply He|iApply He'].
  Qed.

  Lemma lim_exec_reduction_f (adv : val) (x : string) (C : expr) (w : val) σ :
    lim_exec ((λ: x, adv (λ: <>, C))%V w, σ) = lim_exec (adv (λ: <>, val_subst x w C)%V, σ).
  Proof.
    rewrite !lim_exec_lim_exec_val.
    pose proof (pure_beta BAnon x (adv (λ: <>, C))%E (RecV BAnon x (adv (λ: <>, C))%E) w) as Hb.
    simpl in Hb.
    rewrite (lim_exec_val_pure_step _ _ _ Hb) //.
    apply (lim_exec_val_pure_step (fill [AppRCtx adv] (Rec BAnon BAnon (val_subst x w C)))
             (fill [AppRCtx adv] (λ: <>, val_subst x w C)%V)); [|done].
    apply (clutch.prob_eff_lang.probblaze.logic.pure_exec_ctx [AppRCtx adv]), pure_recc.
  Qed.

  Lemma advantage_reduction_f (adv : val) (x : string) (C Cv Cv' : expr) (v v' : val) (b : bool) :
    val_subst x v C = Cv → val_subst x v' C = Cv' →
    advantage adv (λ: <>, Cv)%V (λ: <>, Cv')%V #b <= advantage (λ: x, adv (λ: <>, C))%V v v' #b.
  Proof.
    intros <- <-. apply advantage_uniform => σ.
    etrans; last by apply (advantage_ub _ _ _ _ σ).
    right. rewrite /pr_dist /=. by rewrite !lim_exec_reduction_f.
  Qed.

End factory_advantage.
