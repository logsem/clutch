(** Almost-sure termination of a simple random walk  *)
From Coq Require Import Reals Psatz.
From clutch.prob_lang Require Import lang notation.
From clutch.tpref_logic Require Import weakestpre spec primitive_laws proofmode adequacy.
From clutch.prob Require Import distribution markov.
From clutch.tpref_logic.examples Require Import flip.
#[local] Open Scope R.

(** Model *)
Definition rw_step (b : bool) :=
  if b then fair_coin else dzero.

Definition rw_to_final (b : bool) : option bool :=
  if b then None else Some false.

Definition random_walk_mixin : MarkovMixin rw_step rw_to_final.
Proof. constructor. by intros [] [] []; simplify_eq=>/=. Qed.

Canonical Structure random_walk : markov := Markov _ _ random_walk_mixin.

Lemma exec_random_walk n :
  SeriesC (exec n true) = 1 - (1/2)^n.
Proof.
  induction n.
  { rewrite Rminus_eq_0 /= dzero_mass //. }
  rewrite exec_Sn_not_final; [|by eapply to_final_None].
  rewrite /markov.step /=.
  rewrite fair_coin_dbind_mass.
  rewrite IHn.
  erewrite exec_is_final; [|done].
  rewrite dret_mass.
  lra.
Qed.

Lemma random_walk_terminates :
  SeriesC (lim_exec true) = 1.
Proof.
  apply (MCT_seriesC _ (λ n, SeriesC (exec n true))); last first.
  - simpl. setoid_rewrite exec_random_walk.
    intros ϵ. split.
    + intros n. trans 1.
      * apply Rminus_gt_0_lt.
        assert (1 - (1 - (1 / 2) ^ n) = (1 / 2) ^ n) as -> by lra.
        apply pow_lt. lra.
      * rewrite -{1}(Rplus_0_r 1).
        apply Rplus_lt_compat_l, cond_pos.
    + assert (∃ n, (1 / 2) ^ n < ϵ) as [n Hn].
      { case: (pow_lt_1_zero (1/2) _ ϵ (cond_pos ϵ)).
        { apply Rabs_def1; lra. }
        intros n Hn. exists n.
        specialize (Hn n (Nat.le_refl _)).
        by apply Rabs_def2 in Hn as [? ?]. }
      exists n. lra.
  - intros. by eapply SeriesC_correct.
  - eauto.
  - intros. eapply exec_mono.
  - eauto.
Qed.

(** Program  *)
Definition prog_random_walk : expr :=
  let: "c" := ref #true in
  while !"c" do "c" <- flip end.

Section random_walk.
  Context `{!tprG random_walk Σ}.

  Lemma random_walk_ref :
    ⟨⟨⟨ specF true ⟩⟩⟩ prog_random_walk ⟨⟨⟨ RET #(); specF false ⟩⟩⟩.
  Proof.
    rewrite /prog_random_walk.
    iIntros (Φ) "Ha HΦ".
    wp_alloc l as "Hl".
    do 3 wp_pure _.
    iLöb as "IH".
    wp_pures.
    wp_load.
    wp_pures.
    wp_apply (rwp_couple_flip _ (=) with "Ha").
    { simpl. apply Rcoupl_eq. }
    iIntros (b a2) "[Ha <-]".
    wp_store.
    destruct b.
    - wp_apply ("IH" with "Ha HΦ Hl").
    - wp_pures. wp_load. wp_pures. by iApply "HΦ".
  Qed.

End random_walk.

Notation σ₀ := {| heap := ∅; tapes := ∅ |}.
Notation almost_surely_terminates ρ := (SeriesC (lim_exec_val ρ) = 1%R).

Theorem prog_random_walk_terminates :
  almost_surely_terminates (prog_random_walk, σ₀).
Proof.
  eapply Rle_antisym; [done|].
  transitivity (SeriesC (lim_exec true)).
  { by rewrite random_walk_terminates. }
  eapply (wp_refRcoupl_mass (tprΣ bool)).
  iIntros (?) "Ha".
  wp_apply (random_walk_ref with "Ha").
  iIntros "Ha".
  iExists _. iFrame.
  iPureIntro.
  by eapply to_final_Some_2.
Qed.
