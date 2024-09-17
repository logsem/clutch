From clutch.approxis Require Import approxis.
From clutch.approxis Require Export bounded_oracle.
From Coquelicot Require Import Lub.
Set Default Proof Using "Type*".


Definition pr_dist (A : val) (G G' : expr)
  (σ σ' : state) (v : val) :=
  Rabs ( (( lim_exec (A G, σ)) v) - (lim_exec (A G', σ') v) )%R.

Definition advantage (A : val) (G G' : expr) :=
  Lub_Rbar (λ ε : R, ∃ (σ σ' : state) (v : val), pr_dist A G G' σ σ' v = ε)%R.

Lemma advantage_uniform (A : val) (G G' : expr) (ε : R) :
  (∀ (σ σ' : state) (v : val), pr_dist A G G' σ σ' v <= ε)%R ->
  (Rbar.Rbar_le (advantage A G G') (Rbar.Finite ε)).
Proof.
  intros hε.
  rewrite /advantage.
  set (E := (λ ε0 : R, ∃ (σ σ' : state) (v : val), pr_dist A G G' σ σ' v = ε0)).
  opose proof (Lub_Rbar_correct E) as h.
  rewrite /is_lub_Rbar in h.
  destruct h as [h1 h2].
  apply h2.
  rewrite /is_ub_Rbar.
  intros ε' (σ & σ' & v & hε').
  apply rbar_le_rle.
  rewrite -hε'. apply hε.
Qed.
