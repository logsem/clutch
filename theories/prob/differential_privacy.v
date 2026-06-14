From Stdlib Require Import Reals Psatz.
From Stdlib.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Lim_seq Rbar.
From stdpp Require Export countable.
From clutch.prelude Require Export base Coquelicot_ext Reals_ext stdpp_ext.
From clutch.prob Require Import couplings_exp couplings_dp.

(* TODO define some of the standard metric spaces used as input for diffpriv *)

(* Meta-level (ε,δ)-DP is, textbook-faithfully, quantified over an adjacency
   RELATION [Adj : A → A → Prop] ("for all adjacent inputs a1 a2, ..."). The
   metric forms [diffpriv_pure]/[diffpriv_approx] below are the standard
   metrization at the unit ball [d a1 a2 ≤ 1] — they are DEFINITIONALLY the
   relation forms instantiated at [λ a1 a2, d a1 a2 ≤ 1], so every existing
   client (which passes a metric [d]) is unchanged. Use the [_rel] forms when
   the adjacency assumption is something other than a unit metric ball, and make
   that assumption explicit at the use site. *)
Definition diffpriv_pure_rel {A B : Type} `{Countable B}
  (Adj : A → A → Prop) (f : A → distr B) (ε : R) :=
  ∀ a1 a2,
    Adj a1 a2 →
    ∀ (P : B → Prop),
      prob (f a1) (λ b, bool_decide (P b))
      <=
        exp ε * prob (f a2) (λ b, bool_decide (P b)).

Definition diffpriv_approx_rel {A B : Type} `{Countable B}
  (Adj : A → A → Prop) (f : A → distr B) (ε δ : R) :=
  ∀ a1 a2,
    Adj a1 a2 →
    ∀ (P : B → Prop),
      prob (f a1) (λ b, bool_decide (P b))
      <=
        exp ε * prob (f a2) (λ b, bool_decide (P b)) + δ.

Definition diffpriv_pure {A B : Type} `{Countable B}
  (d : A → A → R) (f : A → distr B) (ε : R) :=
  diffpriv_pure_rel (λ a1 a2, d a1 a2 <= 1) f ε.

Definition diffpriv_approx {A B : Type} `{Countable B}
  (d : A → A → R) (f : A → distr B) (ε δ : R) :=
  diffpriv_approx_rel (λ a1 a2, d a1 a2 <= 1) f ε δ.

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

(** Forward, textbook form: metric ADP over [d] gives textbook approximate DP
    over ANY adjacency relation [Adj] contained in the unit [d]-ball. This is the
    statement against the relation form [diffpriv_approx_rel], of which
    [diffpriv_metric_approx] (adjacency = the unit ball itself) is the instance. *)
Fact diffpriv_metric_approx_rel {A B : Type} `{Countable B}
  (Adj : A → A → Prop) (d : A → A → R) (f : A → distr B) (ε δ : R) :
  0 < ε → (∀ a b, Adj a b → d a b <= 1) →
  diffpriv_metric d f ε δ → diffpriv_approx_rel Adj f ε δ.
Proof.
  intros Hε Hsub h a1 a2 Hadj P. specialize (h a1 a2 1 (Hsub _ _ Hadj) P).
  rewrite Rmult_1_l (grp_1 _ Hε) Rmult_1_r in h. exact h.
Qed.

(** Forward, pure: at [δ=0]. *)
Fact diffpriv_metric_pure_rel {A B : Type} `{Countable B}
  (Adj : A → A → Prop) (d : A → A → R) (f : A → distr B) (ε : R) :
  0 < ε → (∀ a b, Adj a b → d a b <= 1) →
  diffpriv_metric d f ε 0 → diffpriv_pure_rel Adj f ε.
Proof.
  intros Hε Hsub h a1 a2 Hadj P.
  pose proof (diffpriv_metric_approx_rel Adj d f ε 0 Hε Hsub h a1 a2 Hadj P) as H'. lra.
Qed.

(** ** Converse: metric DP from textbook ADP via group-privacy chaining *)

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

(** Append recurrence: [grp ε (c+1) = grp ε c + e^{cε}] (the "add a step at the
    end" form, dual to [grp_rec]). For integer [c=n] this unfolds [grp ε n] into
    the geometric sum [Σ_{j<n} e^{jε}]. *)
Lemma grp_succ eps c : 0 < eps -> grp eps (c + 1) = grp eps c + exp (c * eps).
Proof.
  intros Heps.
  assert (He : exp eps - 1 <> 0).
  { cut (1 < exp eps); [lra|]. rewrite -exp_0. apply exp_increasing. lra. }
  rewrite /grp. replace ((c + 1) * eps) with (c * eps + eps) by ring.
  rewrite exp_plus. field. exact He.
Qed.

(** [grp ε n] is monotone in the BUDGET [ε] at integer distance [n] — because it
    is the geometric sum [Σ_{j<n} e^{jε}], each term non-decreasing in [ε]. This is
    exactly what makes SEQUENTIAL/k-fold composition sound for the metric def: at an
    integer distance, summing budgets [ε ↦ ε+ε'] only grows [grp], so the chained
    additive credit [δ·grp ε n + δ'·grp ε' n ≤ (δ+δ')·grp (ε+ε') n] telescopes.
    (The [c<1] non-monotonicity of [grp ε c] in [ε] is irrelevant: integer-valued
    metrics never realise a fractional distance.) *)
Lemma grp_mono_eps n eps eps' : 0 < eps -> eps <= eps' -> grp eps (INR n) <= grp eps' (INR n).
Proof.
  intros Heps Hle. assert (Heps' : 0 < eps') by lra.
  assert (Hg0 : forall e, grp e 0 = 0).
  { intros e. rewrite /grp Rmult_0_l exp_0. replace (1 - 1) with 0 by lra. apply Rdiv_0_l. }
  induction n as [|n IH].
  - rewrite INR_0 !Hg0. lra.
  - rewrite S_INR (grp_succ eps (INR n) Heps) (grp_succ eps' (INR n) Heps').
    apply Rplus_le_compat; [exact IH |].
    apply exp_mono. apply Rmult_le_compat_l; [apply pos_INR | lra].
Qed.

(** Unit-step interpolation path of length [n] from [a] to [b] over an adjacency
    relation [Adj]: a chain of [n] adjacent steps. The metric enters only through
    the path-metric hypothesis below, which says how [d]-distance is realized by
    [Adj]-paths — keeping the textbook relation [Adj] and the metric [d] separate. *)
Inductive adj_path {A} (Adj : A → A → Prop) : nat → A → A → Prop :=
| adj_path_O a : adj_path Adj 0 a a
| adj_path_S n a b c : Adj a b → adj_path Adj n b c → adj_path Adj (S n) a c.

(** Group privacy (approximate), textbook form: chaining [n] [Adj]-adjacent steps
    multiplies the privacy budget to [(n·ε, δ·grp ε n)]. *)
Lemma diffpriv_approx_rel_group {A B : Type} `{Countable B}
  (Adj : A → A → Prop) (f : A → distr B) (ε δ : R) :
  0 < ε → 0 <= δ → diffpriv_approx_rel Adj f ε δ →
  ∀ n a b, adj_path Adj n a b →
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

(** Converse of [diffpriv_metric_approx_rel], textbook form: under a path-metric
    hypothesis joining the metric [d] to the adjacency relation [Adj] (any pair at
    [d]-distance [≤c] is [Adj]-connected by a path of integer length [≤c]), textbook
    approximate DP over [Adj] implies metric ADP over [d]. [d] is then a path metric
    for [Adj]; for integer-valued metrics (all examples here) the canonical choice
    [Adj := λ a b, d a b <= 1] satisfies the hypothesis. *)
Lemma diffpriv_metric_of_approx_rel {A B : Type} `{Countable B}
  (Adj : A → A → Prop) (d : A → A → R) (f : A → distr B) (ε δ : R)
  (Hpath : ∀ a b c, d a b <= c → ∃ n, INR n <= c ∧ adj_path Adj n a b) :
  0 < ε → 0 <= δ → diffpriv_approx_rel Adj f ε δ → diffpriv_metric d f ε δ.
Proof.
  intros Hε Hδ Happ a1 a2 c d12 P.
  destruct (Hpath a1 a2 c d12) as (n & Hn & Hp).
  pose proof (diffpriv_approx_rel_group Adj f ε δ Hε Hδ Happ n a1 a2 Hp P) as Hg.
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

(** Converse, pure: at [δ=0], textbook pure DP over [Adj] implies metric pure DP. *)
Lemma diffpriv_metric_of_pure_rel {A B : Type} `{Countable B}
  (Adj : A → A → Prop) (d : A → A → R) (f : A → distr B) (ε : R)
  (Hpath : ∀ a b c, d a b <= c → ∃ n, INR n <= c ∧ adj_path Adj n a b) :
  0 < ε → diffpriv_pure_rel Adj f ε → diffpriv_metric d f ε 0.
Proof.
  intros Hε Happ.
  apply (diffpriv_metric_of_approx_rel Adj d f ε 0 Hpath Hε (Rle_refl 0)).
  intros a1 a2 Hadj P. specialize (Happ a1 a2 Hadj P). lra.
Qed.

(** [d≤1] corollary: the metrization [Adj := λ a b, d a b <= 1] (the unit ball)
    recovers the metric-only converse. *)
Corollary diffpriv_metric_of_approx {A B : Type} `{Countable B}
  (d : A → A → R) (f : A → distr B) (ε δ : R)
  (Hpath : ∀ a b c, d a b <= c → ∃ n, INR n <= c ∧ adj_path (λ x y, d x y <= 1) n a b) :
  0 < ε → 0 <= δ → diffpriv_approx d f ε δ → diffpriv_metric d f ε δ.
Proof.
  intros Hε Hδ Happ.
  exact (diffpriv_metric_of_approx_rel (λ x y, d x y <= 1) d f ε δ Hpath Hε Hδ Happ).
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
