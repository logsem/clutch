From Stdlib Require Import Reals Psatz.
From clutch.prelude Require Import NNRbar.
From clutch.common Require Import language.
From clutch.prob Require Import distribution markov.
From clutch.prob_eff_lang.probblaze Require Import notation semantics logic sem_judgement sem_types sem_def. (* semantics proves that blaze_prob_lang is a lang_markov *)
Set Default Proof Using "Type*".
#[local] Open Scope R_scope.


Definition pr_dist (X Y : expr)
  (σ σ' : state) (v : val) : nonnegreal.
Proof.
  unshelve econstructor.
  1: exact (Rabs ( (( lim_exec (X, σ)) v) - (lim_exec (Y, σ') v) )).
  apply Rabs_pos.
Defined.

Fact pr_dist_triangle' X Y Z σ σ' σ'' v :
  (pr_dist X Z σ σ'' v <= (pr_dist X Y σ σ' v) + (pr_dist Y Z σ' σ'' v)).
Proof.
  rewrite /pr_dist. etrans. 2: apply Rabs_triang. right. simpl. f_equal. lra.
Qed.

Fact pr_dist_triangle X Y Z σ σ' σ'' v ε1 ε2 ε3 :
  ((pr_dist X Y σ σ' v <= ε1) →
   (pr_dist Y Z σ' σ'' v <= ε2) →
   (ε1 + ε2 <= ε3) →
   pr_dist X Z σ σ'' v <= ε3)%R.
Proof.
  intros. etrans.
  1: eapply (pr_dist_triangle' _ Y _ _ σ').
  etrans. 2: eauto. apply Rplus_le_compat => //.
Qed.

(* Quantify over all initial states. Both programs start in the same state.  *)
(* If the adversary is a closed (well-typed) value, the initial state might as well be empty *)
Definition pr_dist_st X Y v := (λ ε : R, ∃ (σ : state), nonneg (pr_dist X Y σ σ v) = ε).

Fact pr_dist_st_bound_1 X Y v : is_upper_bound (pr_dist_st X Y v) 1.
Proof.
  assert (∀ (e : expr) (σ : state) (v : val), 0 <= lim_exec (e, σ) v <= 1)
    as h by by intros ; split.
  intros ε (σ & <-). apply Rabs_le.
  pose (h X σ v). pose (h Y σ v). split ; lra.
Qed.

Fact pr_dist_st_bound X Y v : bound (pr_dist_st X Y v).
Proof.
  exists 1. apply pr_dist_st_bound_1.
Qed.

Fact pr_dist_st_inhabited : forall X Y v, (∃ x : R, pr_dist_st X Y v x).
  intros. rewrite /pr_dist_st.
  exists (pr_dist X Y inhabitant inhabitant v) , inhabitant => //.
Qed.

(* Advantage is defined as the least upper bound of advantage of each state *)
Definition advantage_R (A : expr) X Y v :=
  ` (completeness (pr_dist_st (A X) (A Y) v) (pr_dist_st_bound (A X) (A Y) v) (pr_dist_st_inhabited (A X) (A Y) v)).

Fact advantage_R_pos A X Y v : 0 <= advantage_R A X Y v.
Proof.
  rewrite /advantage_R.
  destruct completeness as [x [ub lub]] => /=.
  rewrite /is_upper_bound in ub.
  etrans. 2: apply ub.
  2:{ rewrite /pr_dist_st. exists inhabitant => //. }
  apply Rabs_pos.
Qed.

Definition advantage (A X Y : expr) (v : val) : nonnegreal.
  econstructor ; apply (advantage_R_pos A X Y v).
Defined.

Lemma advantage_bound_1 A e e' v : (advantage A e e' v <= 1)%R.
Proof.
  simpl. rewrite /advantage_R.
  destruct completeness as [x [ub lub]] => /=.
  apply lub.
  apply pr_dist_st_bound_1.
Qed.

Lemma advantage_uniform (A X Y : expr) v (ε : R) :
  (∀ (σ : state), pr_dist (A X) (A Y) σ σ v <= ε) →
  (advantage A X Y v <= ε).
Proof.
  intros hε. rewrite /advantage/advantage_R => /=.
  destruct completeness as [x [ub lub]] => /=.
  apply lub. intros ε' (σ & hε').
  rewrite -hε'. apply hε.
Qed.

Fact advantage_ub (A X Y : expr) v σ : pr_dist (A X) (A Y) σ σ v <= advantage A X Y v.
Proof.
  rewrite /advantage/advantage_R => /=.
  destruct completeness as [x [ub lub]] => /=.
  apply ub. eexists _. done.
Qed.

Fact advantage_triangle' A X Y Z v :
  (advantage A X Z v <= (advantage A X Y v) + (advantage A Y Z v)).
Proof.
  apply advantage_uniform. intros.
  transitivity (pr_dist (A X) (A Y) σ σ v + (pr_dist (A Y) (A Z) σ σ v)).
  1: apply pr_dist_triangle'.
  eapply Rplus_le_compat => //.
  all: apply advantage_ub.
Qed.

Fact advantage_triangle A X Y Z v ε1 ε2 ε3 :
  ((advantage A X Y v <= ε1) →
   (advantage A Y Z v <= ε2) →
   (ε1 + ε2 <= ε3) →
   advantage A X Z v <= ε3).
Proof.
  intros. etrans.
  1: eapply (advantage_triangle' _ _ Y _ _).
  etrans. 2: eauto.
  apply Rplus_le_compat => //.
Qed.

Fact pr_dist_sym e e' σ σ' v : pr_dist e e' σ σ' v = pr_dist e' e σ' σ v.
Proof. apply nnreal_ext. rewrite /pr_dist => /=. rewrite Rabs_minus_sym. done. Qed.

Fact pr_dist_st_sym e e' v : pr_dist_st e e' v = pr_dist_st e' e v.
Proof.
  rewrite /pr_dist_st.
  apply functional_extensionality_dep => ε.
  f_equal.
  apply functional_extensionality_dep => σ.
  by rewrite pr_dist_sym.
Qed.

Fact advantage_sym A e e' v : advantage A e e' v = advantage A e' e v.
Proof.
  apply nnreal_ext. rewrite /advantage. simpl.
  rewrite /advantage_R. simpl.
  destruct completeness as [x [ub lub]] => /=.
  destruct completeness as [y [ub' lub']] => /=.
  rewrite pr_dist_st_sym in ub'.
  rewrite pr_dist_st_sym in lub'.
  pose proof (lub y ub').
  pose proof (lub' x ub). lra.
Qed.


Theorem brel_advantage `{probblazeRGS Σ} A e e' (τ : sem_ty Σ):
  ∀ (b : bool), (⊢ sem_val_typed A A (τ → 𝔹)%T) ->
                (⊢ sem_val_typed e e' τ)  /\ (⊢ sem_val_typed e' e τ) ->
                nonneg (advantage A e e' #b) = 0%R.
Proof.
Admitted. 
