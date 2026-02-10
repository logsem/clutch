From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic Require Export invariants lib.ghost_map lib.cancelable_invariants.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.

From clutch.common Require Export language ectx_language.
From clutch.prob_lang Require Import notation tactics metatheory.
From clutch.prob_lang Require Export lang.
From clutch.eris Require Export weakestpre total_weakestpre proofmode derived_laws error_rules presample_rules.
From clutch.prob Require Import distribution.
From clutch.eris.complete Require Export ectx_lang_total_completeness lang_total_completeness no_alloc.
From clutch.pure_complete Require Export prob_additional.

Local Open Scope R.

Section Instances.

Context `{!erisGS Σ}.

Definition heap_inv (σ : prob_lang.state) : iProp Σ :=
    ([∗ map] ℓ↦v ∈ σ.(heap),  ℓ ↦ v) 
  ∗ ([∗ map] ι↦α ∈ σ.(tapes), ι ↪ α).

Lemma prob_lang_head_total_completeness e1 σ E : 
  na e1 σ →
  head_reducible e1 σ →
  heap_inv σ ={E}=∗
  ((∀ Ψ (ε1 : nat → cfg → R) n, 
    ⌜∀ e σ, head_reducible e σ → ε1 (S n) (e, σ) = Expval (step (e, σ)) (ε1 n)⌝ →
    ⌜∀ n ρ, 0 <= ε1 n ρ⌝ →
    ⌜∀ n ρ, stuck ρ → ε1 n ρ = 1⌝ →
        ((|={⊤,E}=>  
        ∀ e2 σ1',
            ⌜prim_step e1 σ (e2, σ1') > 0⌝ -∗
            heap_inv σ1' -∗ 
                ↯ (ε1 n (e2, σ1')) ={E,⊤}=∗ 
                WP e2 @ ⊤ [{ v, Ψ v }]) -∗
        ↯ (ε1 (S n) (e1, σ)) -∗ WP e1 @ ⊤ [{ v, Ψ v }]))).
Proof.
  iIntros (Hna Hre) "Hheap".
  pose proof Hre as ((e'&σ')&Hstep).
  iModIntro. iFrame.
  iIntros (Ψ ε1 n Hε1 Hε1nn Hε1stuck) "Hind Herr".
  rewrite head_step_support_equiv_rel in Hstep.
  specialize (Hε1 e1 σ Hre).
  (* specialize (Hε1stuck n (e1, σ)). *)
  rewrite /step //= head_prim_step_eq in Hε1 Hε1stuck.
  induction Hstep; simplify_eq; rewrite /head_step /prob_lang.head_step //= in Hε1 Hε1stuck.
  all: try (rewrite Expval_dret in Hε1; 
    rewrite Hε1; wp_pure; (try iApply fupd_tgl_wp); iMod ("Hind" $! _ with "[] Hheap") as "Hind"; 
    [by iPureIntro; rewrite head_prim_step_eq /head_step //= dret_1_1 //=; lra|
    by iSpecialize ("Hind" with "Herr"); iMod "Hind"; (try rewrite tgl_wp_value_fupd)]). 
  (* un_op *)
  {
    destruct (un_op_eval op v) eqn : Hop. 
    - rewrite Expval_dret in Hε1. wp_op. rewrite Hε1. 
      iMod ("Hind" $! _ with "[] Hheap") as "Hind".
      + iPureIntro. rewrite head_prim_step_eq /head_step //= Hop //= dret_1_1 //=; lra.
      + iSpecialize ("Hind" with "Herr"). iMod "Hind". by rewrite tgl_wp_value_fupd.
    - rewrite Hε1stuck; first by iPoseProof (ec_contradict with "Herr") as "[]". 
      rewrite /stuck /irreducible /step //= head_prim_step_eq //=. 
  }
  (* bin_op *)
  {
    destruct (bin_op_eval op v1 v2) eqn : Hop. 
    - rewrite Expval_dret in Hε1. wp_op. rewrite Hε1. 
      iMod ("Hind" $! _ with "[] Hheap") as "Hind".
      + iPureIntro. rewrite head_prim_step_eq /head_step //= Hop //= dret_1_1 //=; lra.
      + iSpecialize ("Hind" with "Herr"). iMod "Hind". by rewrite tgl_wp_value_fupd.
    - rewrite Hε1stuck; first by iPoseProof (ec_contradict with "Herr") as "[]". 
      rewrite /stuck /irreducible /step //= head_prim_step_eq //=. 
  }
  (* allocN (no) *)
  { by destruct Hna as [H ?]; destruct (na_no_allocN H). }
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
      + iPureIntro. rewrite head_prim_step_eq /ectx_language.head_step /prob_lang.head_step //= Hσl //= dret_1_1 //=; lra.  
      + iSpecialize ("Hind" with "Herr"). iMod "Hind". by rewrite tgl_wp_value_fupd.
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
      + iPureIntro. rewrite head_prim_step_eq /ectx_language.head_step /prob_lang.head_step //= Hσl dret_1_1 //=; lra.
      + by rewrite /state_upd_heap.
      + iSpecialize ("Hind" with "Herr"). iMod "Hind". by rewrite tgl_wp_value_fupd.
    - rewrite Hε1stuck; first by iPoseProof (ec_contradict with "Herr") as "[]". 
      rewrite /stuck /irreducible /step //= head_prim_step_eq //=. 
  }
  (* weird *)
  all : iApply (tgl_wp_strong_mono _ _ ⊤ _ _ (λ v, |={⊤}=> Ψ v)%I with "[Hheap Herr Hind] []"); try done; last by iIntros "% H"; iApply "H".
  (* rand *)
  {
    wp_apply (twp_rand_exp_fin _ _ _ _ (λ n0 : fin (S (Z.to_nat z)), ε1 n (Val #n0, σ)) with "Herr").
    - intros. apply Hε1nn.
    - rewrite Hε1 Expval_dmap //=; first last.
      { apply ex_seriesC_finite. } 
      apply SeriesC_ext => nx. 
      rewrite dunif_pmf //=. 
      real_solver.
    - iIntros (nx) "Herr". iMod ("Hind" $! (Val #nx) with "[] Hheap") as "Hind".
      + iPureIntro. rewrite head_prim_step_eq /head_step /prob_lang.head_step. 
        rewrite dmap_pos. do 2 econstructor; eauto. apply dunifP_pos.
      + iSpecialize ("Hind" with "Herr"). iMod "Hind". by rewrite tgl_wp_value_fupd.
  } 
  (* allocTape (no) *)
  { by destruct Hna as [H ?]; destruct (na_no_allocTape H). }
  (* successful rand on tape *)
  {  
    destruct (tapes σ !! l) eqn : Hσl; inversion H0; simplify_eq.
    case_bool_decide; last done.
    rewrite Expval_dret in Hε1. rewrite Hε1. 
    rewrite /heap_inv (big_sepM_delete _ (tapes σ) l); eauto.
    iDestruct "Hheap" as "(Hheap & (Hl & Htapes'))".
    wp_apply (twp_rand_tape with "Hl").
    iIntros "Hl".
    iCombine "Hl Htapes'" as "Htapes".
    rewrite <-(big_sepM_insert_delete (λ l v, l ↪[erisGS_tapes_name] v)%I).
    iCombine "Hheap Htapes" as "Hheap".
    iMod ("Hind" $! _ with "[] [Hheap]") as "Hind". 
    + iPureIntro. rewrite head_prim_step_eq /ectx_language.head_step /prob_lang.head_step //= Hσl.
      case_bool_decide; last contradiction. rewrite dret_1_1 //=; lra.
    + by rewrite /state_upd_heap.
    + iSpecialize ("Hind" with "Herr"). iMod "Hind". by rewrite tgl_wp_value_fupd.
  }
  (* 
    rand on empty tape (same as usual rand),
    prove this by first presampling
  *) 
  {
    destruct (tapes σ !! l) eqn : Hσl; inversion H0; simplify_eq.
    case_bool_decide; last done.
    rewrite /heap_inv (big_sepM_delete _ (tapes σ) l); eauto.
    iDestruct "Hheap" as "(Hheap & (Hl & Htapes'))".
    iApply (twp_presample_adv_comp _ _ _ _ _ _ _ _ (λ nx, ε1 n (Val #nx, σ))); auto.
    iFrame. iSplitL "Herr".
    - iApply (ec_eq with "Herr").
      rewrite Hε1 Expval_dmap; auto; last apply ex_seriesC_finite.
      apply SeriesC_ext. intros. rewrite dunif_pmf //=. real_solver. 
    - iIntros (nx) "(Herr & Hl)".
      wp_apply (twp_rand_tape with "Hl").
      iIntros "Hl".
      iCombine "Hl Htapes'" as "Htapes".
      rewrite <-(big_sepM_insert_delete (λ l v, l ↪[erisGS_tapes_name] v)%I).
      rewrite insert_id //=.
      iCombine "Hheap Htapes" as "Hheap".
      iMod ("Hind" $! _ with "[] [Hheap]") as "Hind".  
      + iPureIntro. rewrite head_prim_step_eq /ectx_language.head_step /prob_lang.head_step //= Hσl. 
      case_bool_decide; last contradiction. rewrite dmap_pos. do 2 econstructor; eauto. rewrite dunif_pmf. real_solver.
      + by rewrite /state_upd_heap.
      + iSpecialize ("Hind" with "Herr"). iMod "Hind". by rewrite tgl_wp_value_fupd.
  }
  (* rand on unmatching tape (same as usual rand)*) 
  {
    destruct (tapes σ !! l) eqn : Hσl; inversion H0; simplify_eq.
    case_bool_decide; first done.
    rewrite /heap_inv (big_sepM_delete _ (tapes σ) l); eauto.
    iDestruct "Hheap" as "(Hheap & (Hl & Htapes'))".
    iCombine "Herr Hl" as "H".
    wp_apply (twp_rand_exp_fin_tape_mismatch _ _ _ _ _ _ _ (λ n0 : fin (S (Z.to_nat z)), ε1 n (Val #n0, σ)) with "H"); eauto.
    - apply Req_le.
      rewrite Hε1 Expval_dmap //=; first last.
      { apply ex_seriesC_finite. }
      apply SeriesC_ext => nx. 
      rewrite dunif_pmf //=. 
      real_solver.
    - iIntros (nx) "[Herr Hl]". 
      iCombine "Hl Htapes'" as "Htapes".
      rewrite <-(big_sepM_insert_delete (λ l v, l ↪[erisGS_tapes_name] v)%I).
      rewrite insert_id //=.
      iCombine "Hheap Htapes" as "Hheap".
      iMod ("Hind" $! (Val #nx) with "[] Hheap") as "Hind".
    + iPureIntro. rewrite head_prim_step_eq /ectx_language.head_step /prob_lang.head_step //= Hσl.
      case_bool_decide; first contradiction. rewrite dmap_pos. do 2 econstructor; eauto. rewrite dunif_pmf. real_solver.
    + iSpecialize ("Hind" with "Herr"). iMod "Hind". by rewrite tgl_wp_value_fupd.
  }
  (* 
    laplacian,
    omitted since not present in the original eris.
  *)
  { by destruct Hna as [Hi ?]; destruct (na_no_laplace Hi). }
  (* laplacian (zero scale) *)
  { by destruct Hna as [Hi ?]; destruct (na_no_laplace Hi). }
  Unshelve. 
  all : done.
Qed.

End Instances.

Global Program Instance prob_lang_ectx_total_completeness `{erisGS Σ} :
  eris_ectx_lang_total_completeness_gen prob_ectx_lang Σ := {
  heap_inv := heap_inv;
  na := na;
}.
Next Obligation.
  intros. simpl in H1.
  destruct H0.
  eapply na_step; eauto.
Defined.
Next Obligation.
  intros ????? [??]. constructor; auto. 
  eapply na_fill_inv; simpl in *; eauto.
Defined.
Next Obligation.
  intros.
  by apply prob_lang_head_total_completeness.
Defined.

Lemma prob_lang_tgl_sem_completeness `{erisGS Σ} n e σ (φ : val → Prop) :
  na e σ →
  ↯ (err_tlb (δ := lang_markov prob_lang) φ n (e, σ)) -∗
  heap_inv σ -∗
  WP e [{v, ⌜φ v⌝}].
Proof.
  iIntros (?) "Herr Hheap".
  iApply (tgl_sem_completeness with "[Herr] [Hheap]"); simpl; eauto.
Qed. 