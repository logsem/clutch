From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic Require Export invariants lib.ghost_map lib.cancelable_invariants.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.

From clutch.common Require Export language.
From clutch.eris Require Export weakestpre total_weakestpre complete_pre lifting ectx_lifting.
From clutch.prob Require Import distribution.
From clutch.base_logic Require Import error_credits.

Local Open Scope R.

Class eris_lang_completeness_gen (Λ : language) (Σ : gFunctors) `{!erisWpGS Λ Σ} `{ecGS Σ} := ErisCompleteness {
  heap_inv : Λ.(state) → iProp Σ;
  (* heap_inv_timeless :> ∀ σ, Timeless (heap_inv σ); *)

  (** [na e] should state that the execution of na does not allocate any new locations in the state *)
  na : Λ.(expr) → Prop;
  na_step : ∀ e σ e' σ', na e → prim_step e σ (e', σ') > 0 → na e';

  (* (** [err φ ρ] is basically prob exec(ρ) φ *)
  err : (Λ.(val) → iProp Σ) → cfg Λ → R;
  (* err_ge0 : ∀ φ ρ, 0 <= err φ ρ;
  err_le1 : ∀ φ ρ, err φ ρ <= 1;
  err_exp : ∀ φ ρ, err φ ρ = Expval (step ρ) (err φ); *)
  err_stuck : ∀ φ ρ, stuck ρ → err φ ρ = 1;
  err_fin : ∀ φ (v : Λ.(val)) σ,
    err φ (of_val v, σ) < 1 →
      heap_inv σ -∗ φ v; *)

  eris_lang_completeness :
    ∀ e1 σ E,
      na e1 →
      reducible (e1, σ) →
      heap_inv σ ={E}=∗
      ((* (↯ ε ∗ heap_inv σ  ∗ ∀ Ψ, ((▷ |={⊤,E}=> ∃ σ1 ε1, 
        ↯ ε1 ∗ heap_inv σ1 ∗
        ∀ e2 σ1' ε1',
          ⌜prim_step e1 σ1 (e2, σ1') > 0⌝ -∗
            ↯ ε1' -∗
              heap_inv σ1' ={E,⊤}=∗ 
                WP e2 @ ⊤ {{ v, Ψ v }}) -∗
        WP e1 @ ⊤ {{ v, Ψ v }})) )*)
      (heap_inv σ ∗ ∀ Ψ (ε1 : cfg Λ → R), 
      ⌜∀ ρ, ε1 ρ = Expval (step ρ) ε1⌝ -∗
      ⌜∀ K e σ, ε1 (fill_lift K (e, σ)) = Expval (step (e, σ)) (ε1 ∘ fill_lift K)⌝ →
        ((▷ |={⊤,E}=> ∃ σ1, 
          heap_inv σ1 ∗ 
          ∀ e2 σ1',
            ⌜prim_step e1 σ1 (e2, σ1') > 0⌝ -∗
              heap_inv σ1' -∗ 
                ↯ (ε1 (e2, σ1')) ={E,⊤}=∗ 
                  WP e2 @ ⊤ {{ v, Ψ v }}) -∗
          ↯ (ε1 (e1, σ)) -∗ WP e1 @ ⊤ {{ v, Ψ v }})) )
}.

Section completeness.
  Context `{!erisWpGS Λ Σ}.
  Context `{!ecGS Σ}.
  Context `{!eris_lang_completeness_gen Λ Σ}.

  Definition stuck_prob {δ : markov} (ρ : mstate δ) : R 
    (* := Inf_seq (fun n => SeriesC (pexec n ρ)) *).
  Admitted.

  Definition err_prob {δ : markov} (ρ : mstate δ) (φ : mstate_ret δ → Prop) : R := 
    prob (lim_exec ρ) (λ a, negb (bool_decide (φ a))).

  Definition err_lb {δ : markov} (φ : mstate_ret δ → Prop) (ρ : mstate δ) : R := Rmax (stuck_prob ρ) (err_prob ρ φ).

  Lemma err_lb_fail_1 {δ : markov} (ρ : mstate δ) v (φ : mstate_ret δ → Prop) :
    to_final ρ = Some v →
    ¬ φ v →
    err_lb φ ρ = 1.
  Admitted.

  Lemma err_lb_stuck_1 {δ : markov} (ρ : mstate δ) (φ : mstate_ret δ → Prop) :
    stuck ρ →
    err_lb φ ρ = 1.
  Admitted.

  Lemma err_lb_step {δ : markov} (ρ : mstate δ) (φ : mstate_ret δ → Prop) :
    err_lb φ ρ = Expval (step ρ) (err_lb φ).
  Admitted.

  Lemma err_lb_fill (e : Λ.(expr)) (σ : Λ.(state)) (φ : Λ.(val) → Prop) K :
    err_lb φ (fill_lift K (e, σ)) = Expval (step (e, σ)) (err_lb φ ∘ fill_lift K).
  Admitted.
  
  Lemma pgl_sem_completeness e σ (φ : Λ.(val) → Prop) :
    na e →
    ↯ (
      err_lb φ (e, σ)
      (* probp (exec 1 (e, σ)) (fun v => ¬ φ v) *)
    ) -∗
    heap_inv σ -∗
    WP e {{v, ⌜φ v⌝}}.
  Proof.
    iLöb as "IH" forall (e σ φ).
    iIntros (Hna) "Herr Hst".
    destruct (to_val e) as [v|] eqn:Hev. {
      eapply of_to_val in Hev. subst e. 
      iApply pgl_wp_value'.
      destruct (decide (φ v)); first by iPureIntro.
      erewrite err_lb_fail_1; simpl; eauto; last by rewrite to_of_val.
      iPoseProof (ec_contradict with "Herr") as "[]".
      lra.
    } 
    destruct (decide (reducible (e, σ))) as [Hred|Hnred]. 2 : {
      iPoseProof (ec_contradict with "Herr") as "[]". 
      (* need to adjust the error credits condition to finish this part *)
      admit.
    }
    iMod (eris_lang_completeness with "Hst") as "H"; eauto.
    iDestruct "H" as "(Hheap & H)". 
    iApply ("H" with "[] [] [Hheap] Herr").
    { iPureIntro. intros. apply err_lb_step. }
    { iPureIntro. intros. apply err_lb_fill. }
    iNext. 
    iFrame "Hheap".
    iModIntro.
    iIntros (??) "%Hstep Hheap Herr".
    iApply ("IH" with "[] Herr Hheap").
    iPureIntro. 
    eapply na_step; eauto.
  Admitted.
    (* iModIntro. iRight. *)
    (* iApply ("H" with "[Hheap] Herr"). iNext.
    iModIntro.
    iExists σ; iFrame.
    iIntros (e' σ') "%Hstep Hheap".
    iModIntro. iIntros "Herr".
    iApply ("IH" with "[] Herr Hheap"); iFrame.
    iPureIntro.
    eapply na_step; eauto.

  

  (* Lemma pgl_wp_completeness e σ (φ : Λ.(val) → iProp Σ) :
    na e →
    ↯ (err φ (e, σ)) -∗
    heap_inv σ -∗
    WP e {{v, φ v}}.
  Proof.
    iLöb as "IH" forall (e σ φ).
    iIntros (Hna) "Herr Hst".
    (* iApply wp_inv_open_maybe. *)
    destruct (to_val e) as [v|] eqn:Hev. {
      eapply of_to_val in Hev. subst e. 
      (* iRight.
      iModIntro. *)
      iApply pgl_wp_value'.
      destruct (decide ((err φ (of_val v, σ)) < 1)); first by iApply err_fin.
      iPoseProof (ec_contradict with "Herr") as "[]". 
      lra.
    } 
    destruct (decide (reducible (e, σ))). 2 : {
      iPoseProof (ec_contradict with "Herr") as "[]". 
      rewrite err_stuck; first lra.
      constructor; auto.
      by rewrite -not_reducible. 
    }
    iMod (eris_lang_completeness with "Hst") as "H"; eauto.
    iDestruct "H" as "(Hheap & H)". 
    (* iModIntro. iRight. *)
    (* iApply ("H" with "[Hheap] Herr"). iNext.
    iModIntro.
    iExists σ; iFrame.
    iIntros (e' σ') "%Hstep Hheap".
    iModIntro. iIntros "Herr".
    iApply ("IH" with "[] Herr Hheap"); iFrame.
    iPureIntro.
    eapply na_step; eauto. *)
  Admitted. *)

*)

End completeness.