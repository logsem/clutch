From Stdlib Require Import Reals Psatz.
From Stdlib.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Lim_seq Rbar.
From stdpp Require Export countable.
From clutch.prelude Require Export base Coquelicot_ext Reals_ext stdpp_ext.
From clutch.prob Require Import couplings_exp couplings_dp couplings_rdp.

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

Fact diffpriv_approx_pure {A B : Type} `{Countable B} (d : A → A → R) (f : A → distr B) (ε : R)
  : diffpriv_approx d f ε 0 → diffpriv_pure d f ε.
Proof. intros h ????. etrans. 1: apply h. 1: eassumption. lra. Qed.

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


(** * Rényi-DP couplings for the discrete Gaussian *)

Lemma gauss_f_eq (σ : posreal) (w : Z) :
  gauss_f σ w = exp (- (IZR w)^2 / (2 * σ^2)).
Proof.
  rewrite /gauss_f/gauss_f_nat.
  assert (INR (Z.to_nat (Z.abs w)) = Rabs (IZR w)) as ->.
  { rewrite INR_IZR_INZ Z2Nat.id; [|lia].
    rewrite abs_IZR //. }
  rewrite pow2_abs //.
Qed.

Lemma gauss_norm_pos (σ : posreal) : 0 < SeriesC (λ z : Z, gauss_f σ z).
Proof.
  eapply Rlt_le_trans; last eapply (SeriesC_ge_elem _ 0%Z).
  - rewrite /gauss_f/gauss_f_nat. apply exp_pos.
  - intros z. rewrite /gauss_f/gauss_f_nat. left. apply exp_pos.
  - apply ex_seriesC_gauss_f.
Qed.

Lemma gauss_pos (loc : Z) (σ : posreal) (z : Z) : 0 < gauss loc σ z.
Proof.
  rewrite /gauss/gauss'{1}/pmf{1}/pmf.
  apply Rdiv_lt_0_compat.
  - rewrite /gauss_f/gauss_f_nat. apply exp_pos.
  - apply gauss_norm_pos.
Qed.

(** Summability of arbitrarily shifted Gaussian sums, by domination with a
    scaled Gaussian of standard deviation [sqrt 2 * σ]. *)
Lemma ex_seriesC_gauss_shift (σ : posreal) (m : R) :
  ex_seriesC (λ z : Z, exp (- (IZR z - m)^2 / (2 * σ^2))).
Proof.
  assert (0 < sqrt 2 * σ) as Hσ'.
  { apply Rmult_lt_0_compat; [apply Rlt_sqrt2_0|apply cond_pos]. }
  set (σ' := mkposreal _ Hσ').
  pose proof (cond_pos σ) as Hσ.
  assert (0 < σ^2) as Hσ2 by nra.
  apply (ex_seriesC_le _ (λ z, exp (m^2 / (2 * σ^2)) * gauss_f σ' z)).
  2:{ apply ex_seriesC_scal_l, ex_seriesC_gauss_f. }
  intro z; split; [left; apply exp_pos|].
  rewrite gauss_f_eq.
  assert ((pos σ') ^ 2 = 2 * σ ^ 2) as Hsq'.
  { rewrite /σ' /=.
    pose proof (sqrt_sqrt 2 ltac:(lra)). nra. }
  rewrite Hsq'.
  rewrite -exp_plus.
  apply exp_mono.
  assert (m ^ 2 / (2 * σ ^ 2) + - IZR z ^ 2 / (2 * (2 * σ ^ 2)) -
          (- (IZR z - m) ^ 2 / (2 * σ ^ 2)) =
          (IZR z - 2 * m)^2 / (4 * σ^2)) as Hdiff.
  { field; lra. }
  pose proof (pow2_ge_0 (IZR z - 2 * m)).
  assert (0 <= (IZR z - 2 * m)^2 / (4 * σ^2)).
  { apply Rdiv_le_0_compat; lra. }
  lra.
Qed.

(** The discrete Gaussian theta sum is maximized at integer shifts.  This is
    Lemma 5 of Canonne, Kamath & Steinke, "The Discrete Gaussian for
    Differential Privacy" (NeurIPS 2020), where it is proven via Poisson
    summation; we assume it here. *)
Lemma gauss_sum_shift_le (σ : posreal) (m : R) :
  SeriesC (λ z : Z, exp (- (IZR z - m)^2 / (2 * σ^2))) <=
  SeriesC (λ z : Z, exp (- (IZR z)^2 / (2 * σ^2))).
Admitted.

Lemma dmap_shift_pmf (μ : distr Z) (t z : Z) :
  dmap (λ x, (x + t)%Z) μ z = μ (z - t)%Z.
Proof.
  rewrite dmap_unfold_pmf.
  rewrite (SeriesC_ext _ (λ a, if bool_decide (a = (z - t))%Z then μ a else 0)).
  { rewrite SeriesC_singleton_dependent //. }
  intro a.
  case_bool_decide as H1; case_bool_decide as H2; try lia.
  - rewrite Rmult_1_r //.
  - ring.
Qed.

Fact RDPcoupl_gauss_isometry (σ : posreal) (loc loc' : Z) (α : R) :
  (1 <= α) ->
  RDPcoupl (gauss loc σ) (gauss loc' σ) (λ z z', z - z' = loc - loc')%Z α 0.
Proof.
  intros Hα.
  assert (gauss loc σ = dmap (λ z, (z + (loc - loc'))%Z) (gauss loc' σ)) as ->.
  { apply distr_ext => z.
    rewrite dmap_shift_pmf.
    change (gauss' σ (z - loc)%Z = gauss' σ ((z - (loc - loc')) - loc')%Z).
    f_equal. lia. }
  eapply RDPcoupl_mono.
  6: apply (RDPcoupl_dmap_l (λ z, (z + (loc - loc'))%Z)),
       (RDPcoupl_eq_refl _ _ 0); [done|lra|apply gauss_pos].
  all: try done; try lra.
  intros x y (x0 & <- & ->).
  lia.
Qed.

Corollary RDPcoupl_gauss_shift (σ : posreal) (loc k : Z) (α : R) :
  (1 <= α) ->
  RDPcoupl (gauss loc σ) (gauss (loc+k) σ) (λ z z', z+k = z')%Z α 0.
Proof.
  intros Hα.
  eapply RDPcoupl_mono. 6: apply RDPcoupl_gauss_isometry. all: try done; try lra. simpl. intros. lia.
Qed.

Lemma RDPcoupl_gauss σ (loc loc' k : Z) (Hdist : (Z.abs (loc - loc') <= k)%Z) (α : R) :
  (1 <= α) ->
  RDPcoupl (gauss loc σ) (gauss loc' σ) (λ z z', z = z')%Z  α (((IZR k)^2)/(2 * (σ^2))).
Proof.
  intros Hα.
  pose proof (cond_pos σ) as Hσ.
  assert (0 < σ^2) as Hσ2 by nra.
  pose proof (gauss_norm_pos σ) as HN.
  set (N := SeriesC (λ z : Z, gauss_f σ z)) in HN.
  set (m := α * IZR loc + (1 - α) * IZR loc').
  set (K := α * (α - 1) * (IZR loc - IZR loc')^2 / (2 * σ^2)).
  assert (0 < rpow N α) as HNα by (by apply rpow_pos).
  assert (0 < rpow N (1 - α)) as HNα' by (by apply rpow_pos).
  (* completing the square in the α-th moment of the likelihood ratio *)
  assert (∀ z : Z,
    rpow (gauss loc σ z) α * rpow (gauss loc' σ z) (1 - α) =
    exp K / N * exp (- (IZR z - m)^2 / (2 * σ^2))) as Hpt.
  { intro z.
    change (gauss loc σ z) with (gauss' σ (z - loc)%Z).
    change (gauss loc' σ z) with (gauss' σ (z - loc')%Z).
    change (gauss' σ (z - loc)%Z) with (gauss_f σ (z - loc)%Z / N).
    change (gauss' σ (z - loc')%Z) with (gauss_f σ (z - loc')%Z / N).
    rewrite !gauss_f_eq !minus_IZR.
    rewrite /Rdiv.
    rewrite (rpow_mult_distr (exp _) (/ N) α); [|apply exp_pos].
    rewrite (rpow_mult_distr (exp _) (/ N) (1 - α)); [|apply exp_pos].
    rewrite !rpow_exp !rpow_inv //.
    trans (exp (α * (- (IZR z - IZR loc)^2 * /(2*σ^2)) +
                (1-α) * (- (IZR z - IZR loc')^2 * /(2*σ^2))) *
           / (rpow N α * rpow N (1-α))).
    { rewrite exp_plus Rinv_mult.
      rewrite (Rinv_mult (rpow N α)).
      ring. }
    rewrite -rpow_plus //.
    replace (α + (1 - α)) with 1 by ring.
    rewrite rpow_1_r //.
    replace (α * (- (IZR z - IZR loc)^2 * /(2*σ^2)) +
             (1-α) * (- (IZR z - IZR loc')^2 * /(2*σ^2)))
      with (K + - (IZR z - m)^2 * /(2*σ^2)).
    2:{ rewrite /K /m /Rdiv. field. lra. }
    rewrite exp_plus. ring. }
  apply RDPcoupl_eq_intro => //.
  - apply gauss_pos.
  - eapply ex_seriesC_ext.
    { intro z. rewrite Hpt //. }
    apply ex_seriesC_scal_l, ex_seriesC_gauss_shift.
  - rewrite (SeriesC_ext _
      (λ z, exp K / N * exp (- (IZR z - m)^2/(2*σ^2))));
      [|intro z; apply Hpt].
    rewrite SeriesC_scal_l.
    trans (exp K / N * N).
    { apply Rmult_le_compat_l.
      { apply Rdiv_le_0_compat; [left; apply exp_pos|done]. }
      etrans; [apply gauss_sum_shift_le|].
      apply Req_le.
      apply SeriesC_ext => z.
      rewrite gauss_f_eq //. }
    replace (exp K / N * N) with (exp K) by (field; lra).
    apply exp_mono.
    rewrite /K.
    assert (Rabs (IZR loc - IZR loc') <= IZR k) as Habs.
    { rewrite -minus_IZR -abs_IZR. by apply IZR_le. }
    assert (- IZR k <= IZR loc - IZR loc' <= IZR k) as [Hlo Hhi].
    { by apply Rabs_le_between. }
    assert ((IZR loc - IZR loc')^2 <= (IZR k)^2) as Hsq by nra.
    assert (0 <= α * (α - 1)) as Hαα by nra.
    assert (α * (α - 1) * (IZR loc - IZR loc')^2 <=
            α * (α - 1) * IZR k^2) as Hnum.
    { apply Rmult_le_compat_l; done. }
    rewrite /Rdiv.
    trans (α * (α - 1) * IZR k^2 * / (2*σ^2)).
    { apply Rmult_le_compat_r; [|done].
      left. apply Rinv_0_lt_compat. lra. }
    apply Req_le. ring.
Qed.