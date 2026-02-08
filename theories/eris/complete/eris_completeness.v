From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic Require Export invariants lib.ghost_map lib.cancelable_invariants.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.

From clutch.common Require Export language ectx_language.
From clutch.prob_lang Require Import notation tactics metatheory.
From clutch.prob_lang Require Export lang.
From clutch.eris Require Export weakestpre total_weakestpre lang_completeness proofmode derived_laws error_rules.
From clutch.prob Require Import distribution.
From clutch.eris.complete Require Export ectx_lang_completeness lang_completeness.
From clutch.pure_complete Require Export prob_additional.

Local Open Scope R.

Section Instances.

Context `{!erisGS Σ}.

Definition heap_inv (σ : prob_lang.state) : iProp Σ :=
    ([∗ map] ℓ↦v ∈ σ.(heap),  ℓ ↦ v) 
  ∗ ([∗ map] ι↦α ∈ σ.(tapes), ι ↪ α).

Definition na (e : prob_lang.expr) := ∀ n σ e' σ', 
  pexec n (e, σ) (e', σ') > 0 → dom σ.(heap) = dom σ'.(heap) ∧ dom σ.(tapes) = dom σ'.(tapes).

Lemma na_step : ∀ e σ e' σ', 
  step (e, σ) (e', σ') > 0 → na e'.
Proof.
Admitted.

Lemma na_fill_inv : ∀ e K, 
  na (fill K e) → na e.
Proof.
Admitted.

Lemma na_no_allocN : ∀ {e1 e2}, 
  na (AllocN e1 e2) → 
  False.
Proof.
Admitted.

Lemma na_no_allocTape : ∀ {e1}, 
  na (AllocTape e1) → 
  False.
Proof.
Admitted.

Lemma prob_lang_head_completeness e1 σ E : 
  na e1 →
  head_reducible e1 σ →
  heap_inv σ ={E}=∗
  ((∀ Ψ (ε1 : cfg prob_lang → R), 
    ⌜∀ e σ, head_reducible e σ → ε1 (e, σ) = Expval (step (e, σ)) ε1⌝ →
    ⌜∀ ρ, 0 <= ε1 ρ⌝ →
    ⌜∀ ρ, stuck ρ → ε1 ρ = 1⌝ →
      ((▷ |={⊤,E}=> 
        ∀ e2 σ1',
          ⌜prim_step e1 σ (e2, σ1') > 0⌝ -∗
            heap_inv σ1' -∗ 
              ↯ (ε1 (e2, σ1')) ={E,⊤}=∗ 
                WP e2 @ ⊤ {{ v, Ψ v }}) -∗
        ↯ (ε1 (e1, σ)) -∗ WP e1 @ ⊤ {{ v, Ψ v }}))).
Proof.
  iIntros (Hna Hre) "Hheap".
  pose proof Hre as ((e'&σ')&Hstep).
  iModIntro. iFrame.
  iIntros (Ψ ε1 Hε1 Hε1nn Hε1stuck) "Hind Herr".
  rewrite head_step_support_equiv_rel in Hstep.
  specialize (Hε1 e1 σ Hre).
  specialize (Hε1stuck (e1, σ)).
  rewrite /step //= head_prim_step_eq in Hε1 Hε1stuck.
  induction Hstep; simplify_eq; rewrite /head_step /prob_lang.head_step //= in Hε1 Hε1stuck.
  all: try (rewrite Expval_dret in Hε1; 
    rewrite Hε1; wp_pure; (try iApply fupd_pgl_wp); iMod ("Hind" $! _ with "[] Hheap") as "Hind"; 
    [by iPureIntro; rewrite /prim_step //= head_prim_step_eq /head_step //= dret_1_1 //=; lra|
    by iSpecialize ("Hind" with "Herr"); iMod "Hind"; (try rewrite pgl_wp_value_fupd)]). 
  (* un_op *)
  {
    destruct (un_op_eval op v) eqn : Hop. 
    - rewrite Expval_dret in Hε1. wp_op. rewrite Hε1. 
      iMod ("Hind" $! _ with "[] Hheap") as "Hind".
      + iPureIntro. rewrite /prim_step //= head_prim_step_eq /head_step //= Hop //= dret_1_1 //=; lra.
      + iSpecialize ("Hind" with "Herr"). iMod "Hind". by rewrite pgl_wp_value_fupd.
    - rewrite Hε1stuck; first by iPoseProof (ec_contradict with "Herr") as "[]". 
      rewrite /stuck /irreducible /step //= head_prim_step_eq //=. 
  }
  (* bin_op *)
  {
    destruct (bin_op_eval op v1 v2) eqn : Hop. 
    - rewrite Expval_dret in Hε1. wp_op. rewrite Hε1. 
      iMod ("Hind" $! _ with "[] Hheap") as "Hind".
      + iPureIntro. rewrite /prim_step //= head_prim_step_eq /head_step //= Hop //= dret_1_1 //=; lra.
      + iSpecialize ("Hind" with "Herr"). iMod "Hind". by rewrite pgl_wp_value_fupd.
    - rewrite Hε1stuck; first by iPoseProof (ec_contradict with "Herr") as "[]". 
      rewrite /stuck /irreducible /step //= head_prim_step_eq //=. 
  }
  (* allocN (no) *)
  { by destruct (na_no_allocN Hna). }
  (* load *)
  { 
    destruct (heap σ !! l) eqn : Hσl.
    - rewrite Expval_dret in Hε1. rewrite Hε1. 
      rewrite /heap_inv (big_sepM_delete); eauto.
      iDestruct "Hheap" as "((Hl&Hheap') & Htapes)".
      wp_load. iCombine "Hl Hheap'" as "Hheap".
      rewrite <-(big_sepM_delete (λ l v, l ↦ v)%I _ _  _ Hσl). 
      iCombine "Hheap Htapes" as "Hheap".
      iMod ("Hind" $! _ with "[] Hheap") as "Hind". 
      + iPureIntro. rewrite /prim_step //= head_prim_step_eq /head_step /prob_lang.head_step Hσl //= dret_1_1 //=; lra. 
      + iSpecialize ("Hind" with "Herr"). iMod "Hind". by rewrite pgl_wp_value_fupd.
    - rewrite Hε1stuck; first by iPoseProof (ec_contradict with "Herr") as "[]". 
      rewrite /stuck /irreducible /step //= head_prim_step_eq //=. 
  }
  (* store *)
  {
    destruct (heap σ !! l) eqn : Hσl.
    - rewrite Expval_dret in Hε1. rewrite Hε1. 
      rewrite /heap_inv (big_sepM_delete); eauto.
      iDestruct "Hheap" as "((Hl&Hheap') & Htapes)".
      wp_store. iCombine "Hl Hheap'" as "Hheap". 
      rewrite <-(big_sepM_insert_delete (λ l v, l ↦ v)%I).
      iCombine "Hheap Htapes" as "Hheap".
      iMod ("Hind" $! _ with "[] [Hheap]") as "Hind". 
      + iPureIntro. rewrite /prim_step //= head_prim_step_eq /head_step /prob_lang.head_step Hσl dret_1_1 //=; lra.
      + by rewrite /state_upd_heap.
      + iSpecialize ("Hind" with "Herr"). iMod "Hind". by rewrite pgl_wp_value_fupd.
    - rewrite Hε1stuck; first by iPoseProof (ec_contradict with "Herr") as "[]". 
      rewrite /stuck /irreducible /step //= head_prim_step_eq //=. 
  }
  (* rand *)
  {
    (* weird *)
    iApply (pgl_wp_strong_mono ⊤ _ _ (λ v, |={⊤}=> Ψ v)%I with "[Hheap Herr Hind] []"); try done.
    2 : { iIntros "% H". by iApply "H". }

    wp_apply (wp_rand_exp_fin _ _ _ _ (λ n0 : fin (S (Z.to_nat z)), ε1 (Val #n0, σ)) with "Herr").
    - intros. apply Hε1nn.
    - rewrite Hε1 Expval_dmap //=; first last.
      { apply ex_seriesC_finite. }
      apply SeriesC_ext => n0. 
      rewrite dunif_pmf //=. 
      real_solver.
    - iIntros (n0) "Herr". iMod ("Hind" $! (Val #n0) with "[] Hheap") as "Hind".
      + iPureIntro. rewrite /prim_step //= head_prim_step_eq /head_step /prob_lang.head_step. 
        rewrite dmap_pos. do 2 econstructor; eauto. apply dunifP_pos.
      + iSpecialize ("Hind" with "Herr"). iMod "Hind". by rewrite pgl_wp_value_fupd.
  }
  (* allocTape *)
  { by destruct (na_no_allocTape Hna). }
  (* successful rand on tape *)
  {  
    destruct (tapes σ !! l) eqn : Hσl; inversion H0; simplify_eq.
    case_bool_decide; last done.
    rewrite Expval_dret in Hε1. rewrite Hε1. 
    admit.
  }
  (* rand on empty tape (same as usual rand) *) 
  {
    destruct (tapes σ !! l) eqn : Hσl; inversion H0; simplify_eq.
    case_bool_decide; last done.
    admit.
  }
  (* rand on unmatching tape (same as usual rand)*) 
  {
    destruct (tapes σ !! l) eqn : Hσl; inversion H0; simplify_eq.
    case_bool_decide; first done.
    admit.
  }
  (* laplacian *)
  {
    (* we don't have a proof rule for laplacian in eris? *)
    case_decide; last done.
    admit.
  }
  (* laplacian (zero scale) *)
  {
    case_decide; first done.
    rewrite dmap_dret Expval_dret in Hε1.
    admit.
  }
Admitted.

End Instances.

Global Program Instance prob_lang_ectx_completeness `{erisGS Σ} :
  eris_ectx_lang_completeness_gen prob_ectx_lang Σ := {
  heap_inv := heap_inv;
  na := na;
}.
Next Obligation.
  intros. simpl in H1.
  eapply na_step. rewrite /step //=.
Defined.
Next Obligation.
  intros. by eapply na_fill_inv.
Defined.
Next Obligation.
  intros.
  by apply prob_lang_head_completeness.
Defined.

Lemma prob_lang_pgl_sem_completeness `{erisGS Σ} e σ (φ : val prob_lang → Prop) :
  na e →
  ↯ (err_lb φ (e, σ)) -∗
  heap_inv σ -∗
  WP e {{v, ⌜φ v⌝}}.
Proof.
  iIntros (?) "Herr Hheap".
  iApply (pgl_sem_completeness with "[Herr] [Hheap]"); auto.
Qed.