From clutch.approxis Require Import approxis.
From clutch.approxis Require Export bounded_oracle.
From Coquelicot Require Import Lub.
Set Default Proof Using "Type*".

Definition pr_dist (X Y : expr)
  (σ σ' : state) (v : val) : nonnegreal.
Proof.
  unshelve econstructor.
  1: exact (Rabs ( (( lim_exec (X, σ)) v) - (lim_exec (Y, σ') v) )).
  apply Rabs_pos.
Defined.

Fact pr_dist_triangle' X Y Z σ σ' σ'' v :
  (pr_dist X Z σ σ'' v <= (pr_dist X Y σ σ' v) + (pr_dist Y Z σ' σ'' v))%R.
Proof.
  rewrite /pr_dist. etrans. 2: apply Rabs_triang. right. simpl. f_equal. lra.
Qed.

Fact pr_dist_triangle X Y Z v ε1 ε2 ε3 :
  ((∀ σ σ', pr_dist X Y σ σ' v <= ε1) →
   (∀ σ σ', pr_dist Y Z σ σ' v <= ε2) →
   (ε1 + ε2 <= ε3) →
   ∀ σ σ', pr_dist X Z σ σ' v <= ε3)%R.
Proof.
  intros. etrans.
  1: eapply (pr_dist_triangle' _ Y _ _ σ).
  etrans. 2: eauto.
  apply Rplus_le_compat => //.
Qed.

Definition pr_dist_st X Y v := (λ ε : R, ∃ (σ σ' : state), nonneg (pr_dist X Y σ σ' v) = ε)%R.

Fact pr_dist_st_bound X Y v : bound (pr_dist_st X Y v).
Proof.
  assert (∀ (e : expr) (σ : state) (v : val), 0 <= lim_exec (e, σ) v <= 1)
    as h by by intros ; split.
  exists 1. intros ε (σ & σ' & <-). apply Rabs_le.
  pose (h X σ v). pose (h Y σ' v). split ; lra.
Qed.

Fact pr_dist_st_inhabited : forall X Y v, (∃ x : R, pr_dist_st X Y v x).
  intros.
  rewrite /pr_dist_st.
  exists (pr_dist X Y inhabitant inhabitant v) , inhabitant , inhabitant => //.
Qed.

Definition advantage_R X Y v :=
  ` (completeness (pr_dist_st X Y v) (pr_dist_st_bound X Y v) (pr_dist_st_inhabited X Y v)).

Fact advantage_R_pos X Y v : 0 <= advantage_R X Y v.
Proof.
  rewrite /advantage_R.
  destruct completeness as [x [ub lub]] => /=.
  rewrite /is_upper_bound in ub.
  etrans. 2: apply ub.
  2:{ rewrite /pr_dist_st. exists inhabitant , inhabitant => //. }
  apply Rabs_pos.
Qed.

Definition advantage (X Y : expr) (v : val) : nonnegreal.
  econstructor ; apply (advantage_R_pos X Y v).
Defined.

Lemma advantage_uniform (X Y : expr) v (ε : R) :
  (∀ (σ σ' : state), pr_dist X Y σ σ' v <= ε)%R →
  (advantage X Y v <= ε)%R.
Proof.
  intros hε.
  rewrite /advantage/advantage_R => /=.
  destruct completeness as [x [ub lub]] => /=.
  apply lub.
  intros ε' (σ & σ' & hε').
  rewrite -hε'. apply hε.
Qed.

Fact advantage_ub X Y v σ σ' : pr_dist X Y σ σ' v <= advantage X Y v.
Proof.
  rewrite /advantage/advantage_R => /=.
  destruct completeness as [x [ub lub]] => /=.
  apply ub. eexists _, _. done.
Qed.

Fact advantage_triangle' X Y Z v :
  (advantage X Z v <= (advantage X Y v) + (advantage Y Z v))%R.
Proof.
  apply advantage_uniform.
  intros.
  transitivity (pr_dist X Y σ σ' v + (pr_dist Y Z σ' σ' v)).
  1: apply pr_dist_triangle'.
  eapply Rplus_le_compat => //.
  all: apply advantage_ub.
Qed.

Fact advantage_triangle X Y Z v ε1 ε2 ε3 :
  ((advantage X Y v <= ε1) →
   (advantage Y Z v <= ε2) →
   (ε1 + ε2 <= ε3) →
   advantage X Z v <= ε3)%R.
Proof.
  intros. etrans.
  1: eapply (advantage_triangle' _ Y _ _).
  etrans. 2: eauto.
  apply Rplus_le_compat => //.
Qed.
