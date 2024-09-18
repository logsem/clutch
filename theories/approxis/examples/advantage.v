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

Definition advantage_rbar (X Y : expr) (v : val) :=
  Lub.Lub_Rbar (λ ε : R, ∃ (σ σ' : state), nonneg (pr_dist X Y σ σ' v) = ε)%R.

Fact advantage_0_1 X Y v : Rbar.Rbar_le (Rbar.Finite 0) (advantage_rbar X Y v) /\
                           Rbar.Rbar_le (advantage_rbar X Y v) (Rbar.Finite 1).
Proof.
  rewrite /advantage_rbar.
  set (P := (λ ε : R, ∃ σ0 σ'0 : state, nonneg (pr_dist X Y σ0 σ'0 v) = ε)).
  epose proof (Lub.Lub_Rbar_correct P) as [is_ub least_ub].
  rewrite /Lub.is_ub_Rbar in is_ub.
  split.
Admitted.

Fact advantage_finite X Y v : Rbar.is_finite (advantage_rbar X Y v).
Proof.
  destruct (advantage_0_1 X Y v). by eapply (is_finite_bounded).
Qed.

Definition advantage (X Y : expr) (v : val) : nonnegreal.
Proof.
  unshelve econstructor.
  1: exact (epsilon ((proj1 (Rbar.is_finite_correct (advantage_rbar X Y v))) (advantage_finite _ _ _))).
  set (h := (proj1 (Rbar.is_finite_correct (advantage_rbar X Y v)) (advantage_finite X Y v))).
  opose proof (epsilon_correct _ h) as hh. simpl in hh.
  simpl.
  eapply (proj1 (rbar_le_rle _ _)).
  rewrite -hh.
  apply advantage_0_1.
Defined.

Fact advantage_ub X Y v : forall σ σ', (pr_dist X Y σ σ' v <= advantage X Y v)%R.
Proof.
  intros. rewrite /advantage.
  set (h := (proj1 (Rbar.is_finite_correct (advantage_rbar X Y v)) (advantage_finite X Y v))).
  opose proof (epsilon_correct _ h) as hh. simpl in hh.
  simpl.
  eapply (proj1 (rbar_le_rle _ _)).
  rewrite -hh.
  rewrite /advantage_rbar.
  set (P := (λ ε : R, ∃ σ0 σ'0 : state, nonneg (pr_dist X Y σ0 σ'0 v) = ε)).
  epose proof (Lub.Lub_Rbar_correct P) as [is_ub least_ub].
  rewrite /Lub.is_ub_Rbar in is_ub.
  apply is_ub.
  rewrite /P. exists σ, σ'.
  done.
Qed.

Lemma advantage_uniform (X Y : expr) v (ε : R) :
  (∀ (σ σ' : state), pr_dist X Y σ σ' v <= ε)%R ->
  (Rbar.Rbar_le (advantage_rbar X Y v) (Rbar.Finite ε)).
Proof.
  intros hε.
  rewrite /advantage_rbar.
  set (E := (λ ε0 : R, ∃ (σ σ' : state), nonneg (pr_dist X Y σ σ' v) = ε0)).
  opose proof (Lub.Lub_Rbar_correct E) as h.
  rewrite /Lub.is_lub_Rbar in h.
  destruct h as [h1 h2].
  apply h2.
  rewrite /Lub.is_ub_Rbar.
  intros ε' (σ & σ' & hε').
  apply rbar_le_rle.
  rewrite -hε'. apply hε.
Qed.

Lemma advantage_uniform' (X Y : expr) v (ε : R) :
  (∀ (σ σ' : state), pr_dist X Y σ σ' v <= ε)%R →
  (advantage X Y v <= ε)%R.
Proof.
  intros h.
  opose proof (advantage_uniform _ _ _ _ h).
Admitted.
