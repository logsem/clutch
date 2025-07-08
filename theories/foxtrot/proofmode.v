From clutch.con_prob_lang Require Import lang notation class_instances tactics.
From clutch.con_prob_lang Require Export wp_tactics.
From clutch.foxtrot Require Import weakestpre primitive_laws derived_laws.
From iris.prelude Require Import options.

#[global] Program Instance rel_logic_wptactics_base `{!foxtrotGS Σ} : GwpTacticsBase Σ unit wp.
Next Obligation. intros. by apply wp_value. Qed.
Next Obligation. intros. by apply wp_fupd. Qed.

#[global] Program Instance rel_logic_wptactics_bind `{!foxtrotGS Σ} : GwpTacticsBind Σ unit wp.
Next Obligation. intros. by apply wp_bind. Qed.

#[global] Program Instance rel_logic_wptactics_pure `{!foxtrotGS Σ} : GwpTacticsPure Σ unit true wp.
Next Obligation. intros. by eapply lifting.wp_pure_step_later. Qed.

#[global] Program Instance rel_logic_wptactics_frame_wand `{!foxtrotGS Σ} : GwpTacticsFrameWand Σ unit true wp :=
  Build_GwpTacticsFrameWand _ _ _ _ _.
Next Obligation. iIntros (???????) "H1 H2". by iApply (wp_frame_wand with "[H1][$]"). Qed.


#[global] Program Instance rel_logic_wptactics_heap `{!foxtrotGS Σ} : GwpTacticsHeap Σ unit true wp :=
  Build_GwpTacticsHeap _ _ _ _ (λ l q v, (l ↦{q} v)%I) (λ l q vs, (l ↦∗{q} vs)%I) _ _ _ _.
Next Obligation. intros. by apply wp_alloc. Qed.
Next Obligation. intros. by apply wp_allocN. Qed.
Next Obligation. intros. by apply wp_load. Qed.
Next Obligation. intros. by apply wp_store. Qed.

#[global] Program Instance rel_logic_wptactics_tape `{!foxtrotGS Σ} : GwpTacticsTapes Σ unit true wp :=
  Build_GwpTacticsTapes _ _ _ _ (λ l q N ns, (l ↪N ( N ; ns ))%I) _ _.
Next Obligation. intros. by apply wp_alloc_tape. Qed.
Next Obligation. intros. rewrite (bi.wand_curry (l↪N(N;ns))). by apply wp_rand_tape. Qed.

#[global] Program Instance rel_logic_wptactics_atomic_concurrency `{!foxtrotGS Σ} : GwpTacticsAtomicConcurrency Σ unit true wp :=
  Build_GwpTacticsAtomicConcurrency _ _ _ _ (λ l q v, (l ↦{q} v)%I) _ _ _ _.
Next Obligation. intros. by apply wp_cmpxchg_fail. Qed.
Next Obligation. intros. by apply wp_cmpxchg_suc. Qed. 
Next Obligation. intros. by apply wp_xchg. Qed.
Next Obligation. intros. by apply wp_faa. Qed. 
  
