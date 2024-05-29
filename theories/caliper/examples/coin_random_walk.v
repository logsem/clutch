(** Almost-sure termination of a simple random walk  *)
From Coq Require Import Reals Psatz.
From self.prob_lang Require Import lang notation.
From self.caliper Require Import weakestpre primitive_laws proofmode adequacy.
From self.prob Require Import distribution markov.
From self.caliper.examples Require Import flip.
#[local] Open Scope R.

(** Model *)
Definition rw_step (b : bool) :=
  if b then fair_coin else dzero.

Definition rw_to_final (b : bool) : option bool :=
  if b then None else Some false.

Definition random_walk_mixin : MarkovMixin rw_step rw_to_final.
Proof. constructor. by intros [] [] []; simplify_eq=>/=. Qed.

Canonical Structure random_walk : markov := Markov _ _ random_walk_mixin.

(** Termination proof, by hand  *)
Lemma exec_random_walk n :
  SeriesC (exec n true) = 1 - (1/2)^n.
Proof.
  induction n.
  { rewrite Rminus_diag /= dzero_mass //. }
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
      * apply Rlt_0_minus.
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

(** Termination proof, using a ranking supermartingale *)
#[global] Program Instance rw_rsm :
  rsm (λ b : mstate random_walk, if b then 2 else 0) 1.
Next Obligation. simpl. real_solver. Qed.
Next Obligation. lra. Qed.
Next Obligation.
  simpl; intros [] Hf=>/=.
  - apply fair_coin_mass.
  - destruct Hf. eauto.
Qed.
Next Obligation. intros [] ?; rewrite /is_final//=. lra. Qed.
Next Obligation.
  intros a Hf.
  apply (ex_seriesC_le _ (λ a', step a a' * 2)); [|by apply ex_seriesC_scal_r].
  intros []; real_solver.
Qed.
Next Obligation.
 intros [] Hf.
- rewrite /Expval /=.
   rewrite SeriesC_bool fair_coin_pmf. lra.
 - destruct Hf. eauto.
Qed.

Lemma random_wal_terminates_alt :
  SeriesC (lim_exec true) = 1.
Proof. eapply rsm_term_limexec. Qed.

(* Using a different while-notation to make the proof look like in the
   paper—here the function is already a value (which blocks substitution). *)

#[local] Notation "'while' e1 'do' e2 'end'" :=
  ((rec: "loop" <> := (if: e1 then e2 ;; "loop" #() else #()))%V #())%E
    (e1, e2 at level 200) : expr_scope.

(** Pure loop  *)
Definition coin_flips : expr :=
  while flip do #() end.

Section coin_flips.
  Context `{!caliperG random_walk Σ}.

  Lemma rwp_coin_flips :
    ⟨⟨⟨ specF true ⟩⟩⟩ coin_flips ⟨⟨⟨ RET #(); specF false ⟩⟩⟩.
  Proof.
    iLöb as "IH".
    iIntros (Φ) "Ha HΦ".
    wp_pures; rewrite -/flip.
    wp_apply (rwp_couple_flip _ (=) with "Ha").
    { simpl. apply Rcoupl_eq. }
    iIntros (b a2) "[Ha <-]".
    destruct b.
    - wp_if. wp_seq. wp_apply ("IH" with "Ha HΦ").
    - wp_if. by iApply "HΦ".
  Qed.

End coin_flips.

Notation σ₀ := {| heap := ∅; tapes := ∅ |}.
Notation almost_surely_terminates ρ := (SeriesC (lim_exec ρ) = 1%R).

Theorem coin_flips_terminates :
  almost_surely_terminates (coin_flips, σ₀).
Proof.
  eapply Rle_antisym; [done|].
  transitivity (SeriesC (lim_exec true)).
  { by rewrite random_walk_terminates. }
  eapply (rwp_soundness_mass (tprΣ random_walk) (λ _, True%I)).
  iIntros (?) "Ha".
  wp_apply (rwp_coin_flips with "Ha"); auto.
Qed.

#[local] Notation "'while' e1 'do' e2 'end'" :=
  ((rec: "loop" <> := (if: e1 then e2 ;; "loop" #() else #())) #())%E
    (e1, e2 at level 200) : expr_scope.

(** Stateful variation  *)
Definition coin_flips_state : expr :=
  let: "c" := ref #true in
  while !"c" do "c" <- flip end.

Section random_walk.
  Context `{!caliperG random_walk Σ}.

  Lemma rwp_coin_flips_state :
    ⟨⟨⟨ specF true ⟩⟩⟩ coin_flips_state ⟨⟨⟨ RET #(); specF false ⟩⟩⟩.
  Proof.
    rewrite /coin_flips_state.
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

Theorem coin_flips_state_terminates :
  almost_surely_terminates (coin_flips_state, σ₀).
Proof.
  eapply Rle_antisym; [done|].
  transitivity (SeriesC (lim_exec true)).
  { by rewrite random_walk_terminates. }
  eapply (rwp_soundness_mass (tprΣ random_walk) (λ _, True%I)).
  iIntros (?) "Ha".
  wp_apply (rwp_coin_flips_state with "Ha"); auto. 
Qed.
