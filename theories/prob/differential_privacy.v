From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Lim_seq Rbar.
From stdpp Require Export countable.
From clutch.prelude Require Export base Coquelicot_ext Reals_ext stdpp_ext.
From clutch.prob Require Import couplings_exp couplings_dp.

(* TODO define some of the standard metric spaces used as input for diffpriv *)

Definition diffpriv_pure {A B : Type} `{Countable B}
  (d : A → A → R) (f : A → distr B) (ε : R) :=
  ∀ a1 a2,
    d a1 a2 <= 1 →
    ∀ (P : B → Prop),
      prob (f a1) (λ b, bool_decide (P b))
      <=
        exp ε * prob (f a2) (λ b, bool_decide (P b)).

Definition diffpriv_approx {A B : Type} `{Countable B}
  (d : A → A → R) (f : A → distr B) (ε δ : R) :=
  ∀ a1 a2,
    d a1 a2 <= 1 →
    ∀ (P : B → Prop),
      prob (f a1) (λ b, bool_decide (P b))
      <=
        exp ε * prob (f a2) (λ b, bool_decide (P b)) + δ.

Fact Mcoupl_diffpriv {A B : Type} `{Countable B}
  (d : A → A → R) (f : A → distr B) (ε : R) :
  (∀ a1 a2, d a1 a2 <= 1 → Mcoupl (f a1) (f a2) eq ε)
  →
    diffpriv_pure d f ε.
Proof.
  intros cpl.
  intros a1 a2 d12 P.
  eapply (Mcoupl_eq_elim_dp).
  by apply cpl.
Qed.

Fact DPcoupl_diffpriv {A B : Type} `{Countable B}
  (d : A → A → R) (f : A → distr B) (ε δ : R) :
  (∀ a1 a2, d a1 a2 <= 1 → DPcoupl (f a1) (f a2) eq ε δ)
  →
    diffpriv_approx d f ε δ.
Proof.
  intros cpl.
  intros a1 a2 d12 P.
  eapply (DPcoupl_eq_elim_dp).
  by apply cpl.
Qed.

Fact Mcoupl_laplace_isometry (ε : posreal) (loc loc' : Z) :
  Mcoupl (laplace ε loc) (laplace ε loc') (λ z z', z - z' = loc - loc')%Z 0.
Proof.
  intros ?? Hf Hg Hfg.
  rewrite exp_0. ring_simplify.
  rewrite -(SeriesC_translate _ (loc - loc')).
  2:{ intros. apply Rmult_le_pos. 1: auto. apply Hf. }
  2:{ eapply ex_seriesC_le. 2: apply (pmf_ex_seriesC (laplace ε loc)).
      intros z. simpl. split.
      - apply Rmult_le_pos => //. apply Hf.
      - destruct (Hf z). etrans. 2: right ; apply Rmult_1_r.
        apply Rmult_le_compat => //.
  }
  apply SeriesC_le.
  2:{ eapply ex_seriesC_le. 2: apply (pmf_ex_seriesC (laplace ε loc')).
      intros z. simpl. split.
      - apply Rmult_le_pos => //. apply Hg.
      - destruct (Hg z). etrans. 2: right ; apply Rmult_1_r.
        apply Rmult_le_compat => //.
  }
  intros z. split.
  { apply Rmult_le_pos => //. apply Hf. }
  opose proof (Hfg ((z + (loc - loc'))) z _)%Z.
  1: lia.
  apply Rmult_le_compat => //.
  1: apply Hf.
  rewrite /laplace/laplace'/pmf{1 3}/laplace_f/laplace_f_nat.
  right.
  do 7 f_equal. lia.
Qed.

Corollary Mcoupl_laplace_shift (ε : posreal) (loc k : Z) :
  Mcoupl (laplace ε loc) (laplace ε (loc+k)) (λ z z', z+k = z')%Z 0.
Proof.
  eapply Mcoupl_mono. 5: apply Mcoupl_laplace_isometry. all: try done. simpl. intros. lia.
Qed.

Lemma Mcoupl_laplace ε (loc loc' k k' : Z) (Hdist : (Z.abs (k + loc - loc') <= k')%Z) :
  Mcoupl (laplace ε loc) (laplace ε loc') (λ z z', z + k = z')%Z (IZR k' * ε).
Proof.
  intros ?? Hf Hg Hfg.
  rewrite -SeriesC_scal_l.
  assert (∀ z : Z, 0 <= laplace ε loc z * f z).
  { intros. apply Rmult_le_pos => //. apply Hf. }
  rewrite -(SeriesC_translate _ (-k)) => //.
  2:{ eapply ex_seriesC_le. 2: apply (pmf_ex_seriesC (laplace ε loc)).
      intros z. simpl. split => //.
      destruct (Hf z). etrans. 2: right ; apply Rmult_1_r. apply Rmult_le_compat => //.
  }
  apply SeriesC_le.
  2:{ apply ex_seriesC_scal_l.
      eapply ex_seriesC_le. 2: apply (pmf_ex_seriesC (laplace ε loc')).
      intros z. simpl. split.
      - apply Rmult_le_pos => //. apply Hg.
      - destruct (Hg z). etrans. 2: right ; apply Rmult_1_r.
        apply Rmult_le_compat => //.
  }
  intros z. split. { apply Rmult_le_pos => //. apply Hf. }
  rewrite -Rmult_assoc.
  opose proof (Hfg ((z-k))%Z z _). 1: lia.
  apply Rmult_le_compat => //. 1: apply Hf.
  rewrite /laplace/pmf/laplace'. rewrite {1 3}/laplace_f/laplace_f_nat.
  rewrite -Rmult_assoc. rewrite -exp_plus. apply Rmult_le_compat_r.
  { rewrite /laplace_f/laplace_f_nat.
    etrans. 2: right ; apply Rmult_1_l.
    apply Rdiv_le_0_compat ; [lra|].
    eapply Rlt_le_trans; last eapply (SeriesC_ge_elem _ 0%Z).
    - apply exp_pos.
    - intros; left. apply exp_pos.
    - apply ex_seriesC_laplace_f.
  }
  apply exp_mono.
  field_simplify. rewrite -Rmult_minus_distr_l.
  rewrite Rmult_comm. apply Rmult_le_compat_l => //. 1: pose (cond_pos ε) ; lra.
  rewrite !INR_IZR_INZ !Z2Nat.id ; try lia.
  qify_r ; zify_q ; ring_simplify ; replace (Z.pos (1*1)) with 1%Z by lia ; ring_simplify.
  clear -Hdist. lia.
Qed.

(* As before but with the exact bound as error factor. *)
Corollary Mcoupl_laplace_alt ε loc loc' k :
  Mcoupl (laplace ε loc) (laplace ε loc') (λ z z', z + k = z')%Z (IZR (Z.abs (k+loc-loc'))*ε).
Proof.
  eapply Mcoupl_mono. 5: apply (Mcoupl_laplace ε loc loc' k (Z.abs (k + loc - loc'))). all: done.
Qed.

(* The two formulations are in fact equivalent: we can recover the lemma from the corollary. *)
#[local] Fact Mcoupl_laplace_alt_proof ε (loc loc' k k' : Z) (Hdist : (Z.abs (k + loc - loc') <= k')%Z) :
  Mcoupl (laplace ε loc) (laplace ε loc') (λ z z', z + k = z')%Z (IZR k' * ε).
Proof.
  eapply Mcoupl_mono ; last first. 1: apply (Mcoupl_laplace_alt ε loc loc' k).
  all: simpl ; try done. apply Rmult_le_compat_r. 1: pose (cond_pos ε) ; lra.
  apply IZR_le. assumption.
Qed.

(* Simple case where the distributions are both located at z. *)
Corollary Mcoupl_laplace_translate_res ε z k :
  Mcoupl (laplace ε z) (laplace ε z) (λ x y, x + k = y)%Z (IZR (Z.abs k)*ε).
Proof.
  eapply Mcoupl_mono. 5: apply (Mcoupl_laplace ε z z k (Z.abs k)). all: done || lia.
Qed.

Corollary Mcoupl_laplace_translate_loc ε loc loc' k (_ : ((Z.abs (loc - loc')) <= k)%Z) :
  Mcoupl (laplace ε loc) (laplace ε loc') eq (IZR k*ε).
Proof.
  eapply Mcoupl_mono. 5: apply (Mcoupl_laplace ε loc loc' 0 k). all: done || simpl ; lia.
Qed.

Corollary Mcoupl_laplace_diffpriv loc loc' ε :
  IZR (Z.abs (loc - loc')) <= 1 →
  Mcoupl (laplace ε loc) (laplace ε loc') eq ε.
Proof.
  intros. replace (pos ε) with (IZR 1 * ε)%R by lra.
  eapply Mcoupl_laplace_translate_loc. by apply le_IZR.
Qed.

Fact diffpriv_laplace ε :
  diffpriv_pure (λ x y, IZR (Z.abs (x - y))) (laplace ε) ε.
Proof.
  apply Mcoupl_diffpriv. intros. by apply Mcoupl_laplace_diffpriv.
Qed.
