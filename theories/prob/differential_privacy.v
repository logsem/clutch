From Stdlib Require Import Reals Psatz.
From Stdlib.ssr Require Import ssreflect ssrfun.
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

(** ** Metric (group-bound) approximate DP *)

(** Group-bound δ factor: at input distance [c] an [(ε,δ)] mechanism's additive
    term is [δ · grp ε c] (NOT linear [c·δ]).  [grp ε c = Σ_{i<c} e^{iε}] for
    integer [c]; [grp ε 1 = 1] (so [c=1] recovers the classic additive [δ]); at
    [δ=0] the whole term vanishes (pure metric DP).  Shared home for the factor
    also used by [gen_diffpriv.diffpriv_rules.hoare_diffpriv_metric]. *)
Definition grp (eps c : R) : R := (exp (c * eps) - 1) / (exp eps - 1).

Lemma grp_nonneg eps c : 0 <= eps -> 0 <= c -> 0 <= grp eps c.
Proof.
  intros Heps Hc. rewrite /grp.
  destruct (Rle_lt_or_eq_dec 0 eps Heps) as [Hpos | Heq].
  - apply Rcomplements.Rdiv_le_0_compat.
    + assert (Hce : 0 <= c * eps) by (apply Rmult_le_pos; lra).
      cut (1 <= exp (c * eps)); [lra|].
      rewrite -exp_0. destruct (Rle_lt_or_eq_dec 0 _ Hce) as [Hlt | <-].
      * left. by apply exp_increasing.
      * lra.
    + cut (1 < exp eps); [lra|]. rewrite -exp_0. apply exp_increasing. lra.
  - rewrite -Heq Rmult_0_r exp_0. rewrite Rminus_diag Rdiv_0_r. lra.
Qed.

Lemma grp_1 eps : 0 < eps -> grp eps 1 = 1.
Proof.
  intros Hpos. rewrite /grp Rmult_1_l.
  apply Rdiv_diag.
  cut (1 < exp eps); [lra|]. rewrite -exp_0. apply exp_increasing. lra.
Qed.

Lemma grp_comp eps c c' : 0 < eps -> 0 < c ->
  grp eps c * grp (c * eps) c' = grp eps (c * c').
Proof.
  intros Heps Hc. rewrite /grp.
  replace (c' * (c * eps)) with ((c * c') * eps) by ring.
  field. split.
  - cut (1 < exp eps); [lra|]. rewrite -exp_0. apply exp_increasing. lra.
  - assert (0 < c * eps) by (apply Rmult_lt_0_compat; lra).
    cut (1 < exp (c * eps)); [lra|]. rewrite -exp_0. apply exp_increasing. lra.
Qed.

(** Metric ADP: at input distance [c], multiplicative factor [e^{c·ε}] and
    additive term [δ · grp ε c].  [δ=0] is pure metric DP; [c=1] recovers
    [diffpriv_approx] ([diffpriv_metric_approx] below).  The [c]-general adjacency
    drops [diffpriv_pure]'s hardcoded [≤1] — so adequacy corollaries state the
    distance directly, with no metric-scaling ([dDB/IZR C]) hack.  Meta-level
    counterpart of [hoare_diffpriv_metric]. *)
Definition diffpriv_metric {A B : Type} `{Countable B}
  (d : A → A → R) (f : A → distr B) (ε δ : R) :=
  ∀ a1 a2 c,
    d a1 a2 <= c →
    ∀ (P : B → Prop),
      prob (f a1) (λ b, bool_decide (P b))
      <=
        exp (c * ε) * prob (f a2) (λ b, bool_decide (P b)) + δ * grp ε c.

(** Constructor: a per-distance DP coupling at the metric profile yields
    [diffpriv_metric] (no chaining — the mechanism supplies the distance-[c]
    coupling directly). *)
Fact DPcoupl_diffpriv_metric {A B : Type} `{Countable B}
  (d : A → A → R) (f : A → distr B) (ε δ : R) :
  (∀ a1 a2 c, d a1 a2 <= c → DPcoupl (f a1) (f a2) eq (c * ε) (δ * grp ε c))
  → diffpriv_metric d f ε δ.
Proof. intros cpl a1 a2 c d12 P. eapply DPcoupl_eq_elim_dp. by apply cpl. Qed.

(** Metric ADP at adjacency ([c=1], where [grp ε 1 = 1]) is exactly classic
    [diffpriv_approx]. *)
Fact diffpriv_metric_approx {A B : Type} `{Countable B}
  (d : A → A → R) (f : A → distr B) (ε δ : R) :
  0 < ε → diffpriv_metric d f ε δ → diffpriv_approx d f ε δ.
Proof.
  intros Hε h a1 a2 d12 P. specialize (h a1 a2 1 d12 P).
  rewrite Rmult_1_l (grp_1 _ Hε) Rmult_1_r in h. exact h.
Qed.

(** ** Converse: metric DP from classic ADP via group-privacy chaining *)

(** Prepend recurrence: the load-bearing identity for the group-privacy
    induction.  [grp ε (c+1) = e^ε · grp ε c + 1]. *)
Lemma grp_rec eps c : 0 < eps -> grp eps (c + 1) = exp eps * grp eps c + 1.
Proof.
  intros Heps.
  assert (He : exp eps - 1 <> 0).
  { cut (1 < exp eps); [lra|]. rewrite -exp_0. apply exp_increasing. lra. }
  rewrite /grp.
  replace ((c + 1) * eps) with (eps + c * eps) by ring.
  rewrite exp_plus. field. exact He.
Qed.

(** [grp ε ·] is monotone in the distance. *)
Lemma grp_mono_c eps c c' : 0 < eps -> c <= c' -> grp eps c <= grp eps c'.
Proof.
  intros Heps Hcc'. rewrite /grp. unfold Rdiv. apply Rmult_le_compat_r.
  - left. apply Rinv_0_lt_compat.
    cut (1 < exp eps); [lra|]. rewrite -exp_0. apply exp_increasing. lra.
  - cut (exp (c * eps) <= exp (c' * eps)); [lra|].
    assert (Hle : c * eps <= c' * eps) by (apply Rmult_le_compat_r; lra).
    destruct (Rle_lt_or_eq_dec _ _ Hle) as [Hlt | Heq].
    + apply Rlt_le. by apply exp_increasing.
    + rewrite Heq. lra.
Qed.

(** Unit-step interpolation path of length [n] from [a] to [b]: a sequence of
    [n] adjacent (distance-[≤1]) steps. *)
Inductive adj_path {A} (d : A → A → R) : nat → A → A → Prop :=
| adj_path_O a : adj_path d 0 a a
| adj_path_S n a b c : d a b <= 1 → adj_path d n b c → adj_path d (S n) a c.

(** Group privacy: chaining [n] adjacent steps multiplies the privacy budget to
    [(n·ε, δ·grp ε n)]. *)
Lemma diffpriv_approx_group {A B : Type} `{Countable B}
  (d : A → A → R) (f : A → distr B) (ε δ : R) :
  0 < ε → 0 <= δ → diffpriv_approx d f ε δ →
  ∀ n a b, adj_path d n a b →
    ∀ P, prob (f a) (λ x, bool_decide (P x))
         <= exp (INR n * ε) * prob (f b) (λ x, bool_decide (P x)) + δ * grp ε (INR n).
Proof.
  intros Hε Hδ Happ n a b Hpath. induction Hpath as [a | n a b c Hab Hpath IH]; intros P.
  - (* BASE: n = 0, a = a *)
    rewrite INR_0 Rmult_0_l exp_0.
    assert (Hg0 : grp ε 0 = 0).
    { rewrite /grp Rmult_0_l exp_0. replace (1 - 1) with 0 by lra. apply Rdiv_0_l. }
    rewrite Hg0. lra.
  - (* STEP *)
    specialize (Happ a b Hab P).
    specialize (IH P).
    rewrite S_INR.
    replace ((INR n + 1) * ε) with (ε + INR n * ε) by ring.
    rewrite exp_plus.
    rewrite (grp_rec ε (INR n) Hε).
    (* Happ : prob(f a) <= exp ε * prob(f b) + δ
       IH   : prob(f b) <= exp(INR n·ε) * prob(f c) + δ*grp ε (INR n)
       Goal : prob(f a) <= exp ε * exp(INR n·ε) * prob(f c) + δ*(exp ε * grp ε (INR n) + 1) *)
    assert (Hexp : 0 <= exp ε) by (left; apply exp_pos).
    assert (Hmul : exp ε * prob (f b) (λ x, bool_decide (P x))
                   <= exp ε * (exp (INR n * ε) * prob (f c) (λ x, bool_decide (P x))
                               + δ * grp ε (INR n))).
    { apply Rmult_le_compat_l; [exact Hexp | exact IH]. }
    nra.
Qed.

(** Converse of [diffpriv_metric_approx]: under a path-metric hypothesis (any
    pair at distance [≤c] is joined by a unit-step path of integer length [≤c]),
    classic ADP implies metric ADP. *)
Lemma diffpriv_metric_of_approx {A B : Type} `{Countable B}
  (d : A → A → R) (f : A → distr B) (ε δ : R)
  (Hpath : ∀ a b c, d a b <= c → ∃ n, INR n <= c ∧ adj_path d n a b) :
  0 < ε → 0 <= δ → diffpriv_approx d f ε δ → diffpriv_metric d f ε δ.
Proof.
  intros Hε Hδ Happ a1 a2 c d12 P.
  destruct (Hpath a1 a2 c d12) as (n & Hn & Hp).
  pose proof (diffpriv_approx_group d f ε δ Hε Hδ Happ n a1 a2 Hp P) as Hg.
  (* Hg : prob(f a1) <= exp(INR n·ε) * prob(f a2) + δ * grp ε (INR n)
     Goal : prob(f a1) <= exp(c·ε) * prob(f a2) + δ * grp ε c *)
  assert (Hexple : exp (INR n * ε) <= exp (c * ε)).
  { apply exp_mono. apply Rmult_le_compat_r; lra. }
  assert (Hp2 : 0 <= prob (f a2) (λ x, bool_decide (P x))) by apply prob_ge_0.
  assert (Hterm1 : exp (INR n * ε) * prob (f a2) (λ x, bool_decide (P x))
                   <= exp (c * ε) * prob (f a2) (λ x, bool_decide (P x))).
  { apply Rmult_le_compat_r; [exact Hp2 | exact Hexple]. }
  assert (Hterm2 : δ * grp ε (INR n) <= δ * grp ε c).
  { apply Rmult_le_compat_l; [exact Hδ | apply grp_mono_c; lra]. }
  lra.
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
