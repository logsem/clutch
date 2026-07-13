From Stdlib Require Import Reals Psatz.
From Stdlib.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Lim_seq Rbar.
From stdpp Require Export countable.
From clutch.prelude Require Export base Coquelicot_ext Reals_ext stdpp_ext fiber_bounds.
From clutch.prob Require Export countable_sum distribution couplings graded_predicate_lifting couplings_app couplings_exp.

Open Scope R.

(** [rpow x y] is the real power [x ^ y] for [0 < x], and [0] for [x <= 0].
    Unlike [Rpower] (which returns [1] at [x = 0]), [rpow] is monotone in its
    base on [0, ∞) for [0 <= y], so tests valued in [[0,1]] can express loss
    of mass. *)
Definition rpow (x y : R) : R :=
  if bool_decide (x <= 0) then 0 else exp (y * ln x).

Lemma rpow_nonneg (x y : R) : 0 <= rpow x y.
Proof.
  rewrite /rpow.
  case_bool_decide; [lra|].
  left; apply exp_pos.
Qed.

Lemma rpow_1_l (y : R) : rpow 1 y = 1.
Proof.
  rewrite /rpow.
  case_bool_decide; [lra|].
  by rewrite ln_1 Rmult_0_r exp_0.
Qed.

Lemma rpow_exp (t y : R) : rpow (exp t) y = exp (y * t).
Proof.
  rewrite /rpow.
  case_bool_decide as Hc.
  - pose proof (exp_pos t); lra.
  - by rewrite ln_exp.
Qed.

Lemma rpow_le_compat_l (x1 x2 y : R) :
  0 <= y → x1 <= x2 → rpow x1 y <= rpow x2 y.
Proof.
  intros Hy Hx.
  rewrite /rpow.
  do 2 case_bool_decide; try lra.
  - left; apply exp_pos.
  - apply exp_mono, Rmult_le_compat_l; [lra|].
    apply ln_le; lra.
Qed.

Lemma rpow_le_1 (x y : R) : 0 <= y → x <= 1 → rpow x y <= 1.
Proof.
  intros Hy Hx.
  rewrite /rpow.
  case_bool_decide; [lra|].
  rewrite -exp_0.
  apply exp_mono.
  assert (ln x <= 0) by (rewrite -ln_1; apply ln_le; lra).
  nra.
Qed.

Lemma rpow_mult_distr (c x y : R) :
  0 < c → rpow (c * x) y = rpow c y * rpow x y.
Proof.
  intros Hc.
  rewrite /rpow.
  do 3 case_bool_decide; try lra; try (exfalso; nra).
  rewrite ln_mult; [|lra|lra].
  by rewrite Rmult_plus_distr_l exp_plus.
Qed.

Lemma rpow_0_l (y : R) : rpow 0 y = 0.
Proof.
  rewrite /rpow.
  case_bool_decide; [done|lra].
Qed.

Lemma rpow_pos (x y : R) : 0 < x → 0 < rpow x y.
Proof.
  intros Hx.
  rewrite /rpow.
  case_bool_decide; [lra|apply exp_pos].
Qed.

Lemma rpow_pos_eq (x y : R) : 0 < x → rpow x y = exp (y * ln x).
Proof.
  intros Hx.
  rewrite /rpow.
  case_bool_decide; [lra|done].
Qed.

Lemma rpow_1_r (x : R) : 0 < x → rpow x 1 = x.
Proof.
  intros Hx.
  rewrite rpow_pos_eq // Rmult_1_l exp_ln //.
Qed.

Lemma rpow_lt_compat_l (x1 x2 y : R) :
  0 < y → 0 < x1 → x1 < x2 → rpow x1 y < rpow x2 y.
Proof.
  intros Hy Hx1 Hx.
  rewrite (rpow_pos_eq x1) // (rpow_pos_eq x2); [|lra].
  apply exp_increasing, Rmult_lt_compat_l; [lra|].
  apply ln_increasing; lra.
Qed.

Lemma rpow_plus (x y z : R) : 0 < x → rpow x (y + z) = rpow x y * rpow x z.
Proof.
  intros Hx.
  rewrite !rpow_pos_eq // Rmult_plus_distr_r exp_plus //.
Qed.

Lemma rpow_split1 (x y : R) : 0 < x → rpow x y = x * rpow x (y - 1).
Proof.
  intros Hx.
  replace y with (1 + (y - 1)) at 1 by ring.
  rewrite rpow_plus // rpow_1_r //.
Qed.

Lemma rpow_inv (x y : R) : 0 < x → rpow (/ x) y = / rpow x y.
Proof.
  intros Hx.
  assert (0 < / x) by (by apply Rinv_0_lt_compat).
  rewrite !rpow_pos_eq //.
  rewrite ln_Rinv // -exp_Ropp.
  f_equal; ring.
Qed.

Lemma rpow_rpow (x y z : R) : rpow (rpow x y) z = rpow x (y * z).
Proof.
  destruct (Rle_dec x 0) as [Hx|Hx%Rnot_le_lt].
  - assert (rpow x y = 0) as ->.
    { rewrite /rpow; case_bool_decide; [done|lra]. }
    assert (rpow x (y * z) = 0) as ->.
    { rewrite /rpow; case_bool_decide; [done|lra]. }
    apply rpow_0_l.
  - rewrite (rpow_pos_eq x y) // rpow_exp rpow_pos_eq //.
    f_equal; ring.
Qed.

Lemma rpow_1_r' (x : R) : 0 <= x → rpow x 1 = x.
Proof.
  intros [Hx| <-]; [by apply rpow_1_r|apply rpow_0_l].
Qed.

Lemma rpow_eq_0 (x y : R) : 0 <= x → 0 < y → rpow x y = 0 → x = 0.
Proof.
  intros Hx Hy Hz.
  destruct (decide (x <= 0)) as [?|Hx'%Rnot_le_lt]; [lra|].
  pose proof (rpow_pos x y Hx'); lra.
Qed.

(** For [1 <= α], the map [x ↦ rpow x α] commutes with suprema of monotone
    bounded nonnegative sequences (it is continuous and monotone). *)
Lemma rpow_Sup_seq (h : nat → R) (α : R) :
  1 <= α →
  (∀ n, 0 <= h n) →
  (∀ n, h n <= h (S n)) →
  (∃ r, ∀ n, h n <= r) →
  rpow (real (Sup_seq (λ n, Rbar.Finite (h n)))) α =
  real (Sup_seq (λ n, Rbar.Finite (rpow (h n) α))).
Proof.
  intros Hα Hpos Hmono [r Hr].
  set (S := Sup_seq (λ n, Rbar.Finite (h n))).
  assert (Hfin : Rbar.is_finite S).
  { apply (is_finite_bounded 0 r).
    - apply (Sup_seq_minor_le _ _ 0%nat) => /=. apply Hpos.
    - apply upper_bound_ge_sup => n /=. apply Hr. }
  set (L := Rbar.real S).
  assert (HSL : S = Rbar.Finite L) by (rewrite /L -Hfin //).
  assert (Hub : ∀ n, h n <= L).
  { intro n.
    assert (Rbar.Rbar_le (Rbar.Finite (h n)) S) as HH.
    { apply (Sup_seq_minor_le _ _ n); simpl; lra. }
    rewrite HSL in HH; done. }
  assert (HL0 : 0 <= L) by (etrans; [apply (Hpos 0%nat)|apply Hub]).
  assert (Hαpos : 0 < / α) by (apply Rinv_0_lt_compat; lra).
  assert (Hgoal : Sup_seq (λ n, Rbar.Finite (rpow (h n) α)) =
                  Rbar.Finite (rpow L α)).
  { apply is_sup_seq_unique. intro eps. split.
    - intro n. simpl.
      pose proof (rpow_le_compat_l (h n) L α ltac:(lra) (Hub n)).
      pose proof (cond_pos eps). lra.
    - simpl.
      destruct (Rle_or_lt (rpow L α - eps) 0) as [Hc|Hc].
      + destruct (Rle_lt_or_eq_dec 0 L HL0) as [HLpos | HLz].
        * assert (Rbar.Rbar_lt 0 S) as Hs by (rewrite HSL; simpl; lra).
          apply Sup_seq_minor_lt in Hs as [n Hn]. simpl in Hn.
          exists n. pose proof (rpow_pos (h n) α Hn). lra.
        * exists 0%nat. rewrite -HLz rpow_0_l.
          pose proof (rpow_nonneg (h 0%nat) α). pose proof (cond_pos eps). lra.
      + assert (HrpowL : 0 < rpow L α) by (pose proof (cond_pos eps); lra).
        assert (HLpos : 0 < L).
        { destruct (Rle_lt_or_eq_dec 0 L HL0) as [|He]; [done|].
          rewrite -He rpow_0_l in HrpowL. lra. }
        set (c := rpow L α - eps).
        set (β := rpow c (/ α)).
        assert (Hcpos : 0 < c) by (rewrite /c; lra).
        assert (Hβpos : 0 < β) by (rewrite /β; by apply rpow_pos).
        assert (Hrpow_inv : rpow (rpow L α) (/ α) = L).
        { rewrite rpow_rpow. replace (α * / α) with 1 by (field; lra).
          by apply rpow_1_r. }
        assert (Hβ : β < L).
        { rewrite /β -Hrpow_inv.
          apply rpow_lt_compat_l;
            [exact Hαpos|exact Hcpos|rewrite /c; pose proof (cond_pos eps); lra]. }
        assert (Rbar.Rbar_lt β S) as Hs by (rewrite HSL; simpl; lra).
        apply Sup_seq_minor_lt in Hs as [n Hn]. simpl in Hn.
        exists n. rewrite -/c.
        apply (Rle_lt_trans _ (rpow β α)); last first.
        { apply rpow_lt_compat_l; [lra|exact Hβpos|exact Hn]. }
        right. rewrite /β rpow_rpow. replace (/ α * α) with 1 by (field; lra).
        rewrite rpow_1_r; [done|exact Hcpos]. }
  rewrite Hgoal /=. done.
Qed.

(** Young's inequality for products. *)
Lemma Rmult_young (x y p q : R) :
  1 < p → 1 < q → / p + / q = 1 →
  0 <= x → 0 <= y →
  x * y <= rpow x p / p + rpow y q / q.
Proof.
  intros Hp Hq Hpq Hx Hy.
  destruct Hx as [Hx| <-]; last first.
  { rewrite Rmult_0_l.
    apply Rplus_le_le_0_compat;
      apply Rdiv_le_0_compat; try apply rpow_nonneg; lra. }
  destruct Hy as [Hy| <-]; last first.
  { rewrite Rmult_0_r.
    apply Rplus_le_le_0_compat;
      apply Rdiv_le_0_compat; try apply rpow_nonneg; lra. }
  rewrite (rpow_pos_eq x p) // (rpow_pos_eq y q) //.
  set (a := p * ln x).
  set (b := q * ln y).
  set (c := / p * a + / q * b).
  assert (∀ u, exp c * (1 + (u - c)) <= exp u) as Htang.
  { intro u.
    assert (exp u = exp c * exp (u - c)) as ->.
    { rewrite -exp_plus. f_equal. ring. }
    apply Rmult_le_compat_l; [left; apply exp_pos|].
    apply exp_ineq1_le. }
  assert (x * y = exp c) as ->.
  { assert (x * y = exp (ln x + ln y)) as ->.
    { rewrite exp_plus !exp_ln //. }
    f_equal. rewrite /c /a /b. field; split; lra. }
  trans (exp c * (/ p * (1 + (a - c)) + / q * (1 + (b - c)))).
  { replace (/ p * (1 + (a - c)) + / q * (1 + (b - c))) with 1.
    { rewrite Rmult_1_r. lra. }
    rewrite /c.
    assert (/ q = 1 - / p) as -> by lra.
    field; lra. }
  rewrite Rmult_plus_distr_l.
  apply Rplus_le_compat.
  - trans (/ p * (exp c * (1 + (a - c)))); [apply Req_le; ring|].
    trans (/ p * exp a); [|apply Req_le; rewrite /Rdiv; ring].
    apply Rmult_le_compat_l; [left; apply Rinv_0_lt_compat; lra|].
    apply Htang.
  - trans (/ q * (exp c * (1 + (b - c)))); [apply Req_le; ring|].
    trans (/ q * exp b); [|apply Req_le; rewrite /Rdiv; ring].
    apply Rmult_le_compat_l; [left; apply Rinv_0_lt_compat; lra|].
    apply Htang.
Qed.

(** Hölder's inequality for countable series of non-negative functions. *)
Lemma SeriesC_rpow_Hoelder `{Countable A} (f g : A → R) (p q : R) :
  1 < p → 1 < q → / p + / q = 1 →
  (∀ a, 0 <= f a) → (∀ a, 0 <= g a) →
  ex_seriesC (λ a, rpow (f a) p) →
  ex_seriesC (λ a, rpow (g a) q) →
  SeriesC (λ a, f a * g a) <=
  rpow (SeriesC (λ a, rpow (f a) p)) (/ p) *
  rpow (SeriesC (λ a, rpow (g a) q)) (/ q).
Proof.
  intros Hp Hq Hpq Hf Hg Hexf Hexg.
  set (Sf := SeriesC (λ a, rpow (f a) p)).
  set (Sg := SeriesC (λ a, rpow (g a) q)).
  assert (0 <= Sf) as HSf by (apply SeriesC_ge_0'; intro; apply rpow_nonneg).
  assert (0 <= Sg) as HSg by (apply SeriesC_ge_0'; intro; apply rpow_nonneg).
  destruct HSf as [HSf|HSf]; last first.
  { assert (∀ a, f a = 0) as Hf0.
    { intro a.
      apply (rpow_eq_0 _ p); [done|lra|].
      pose proof (rpow_nonneg (f a) p).
      assert (rpow (f a) p <= Sf); [|lra].
      apply (SeriesC_ge_elem (λ a, rpow (f a) p));
        [intro; apply rpow_nonneg|done]. }
    rewrite (SeriesC_ext _ (λ _, 0)); [|intro a'; rewrite Hf0; ring].
    rewrite SeriesC_0 //.
    apply Rmult_le_pos; apply rpow_nonneg. }
  destruct HSg as [HSg|HSg]; last first.
  { assert (∀ a, g a = 0) as Hg0.
    { intro a.
      apply (rpow_eq_0 _ q); [done|lra|].
      pose proof (rpow_nonneg (g a) q).
      assert (rpow (g a) q <= Sg); [|lra].
      apply (SeriesC_ge_elem (λ a, rpow (g a) q));
        [intro; apply rpow_nonneg|done]. }
    rewrite (SeriesC_ext _ (λ _, 0)); [|intro a'; rewrite Hg0; ring].
    rewrite SeriesC_0 //.
    apply Rmult_le_pos; apply rpow_nonneg. }
  set (cf := rpow Sf (/ p)).
  set (cg := rpow Sg (/ q)).
  assert (0 < cf) as Hcf by (by apply rpow_pos).
  assert (0 < cg) as Hcg by (by apply rpow_pos).
  assert (∀ a, rpow (f a / cf) p = rpow (f a) p / Sf) as Hfn.
  { intro a.
    rewrite /Rdiv Rmult_comm.
    rewrite rpow_mult_distr; [|by apply Rinv_0_lt_compat].
    rewrite rpow_inv // /cf rpow_rpow.
    replace (/ p * p) with 1 by (field; lra).
    rewrite rpow_1_r //. ring. }
  assert (∀ a, rpow (g a / cg) q = rpow (g a) q / Sg) as Hgn.
  { intro a.
    rewrite /Rdiv Rmult_comm.
    rewrite rpow_mult_distr; [|by apply Rinv_0_lt_compat].
    rewrite rpow_inv // /cg rpow_rpow.
    replace (/ q * q) with 1 by (field; lra).
    rewrite rpow_1_r //. ring. }
  trans (SeriesC (λ a, cf * cg *
           (rpow (f a) p / (p * Sf) + rpow (g a) q / (q * Sg)))).
  { apply SeriesC_le; last first.
    { apply ex_seriesC_scal_l.
      apply ex_seriesC_plus.
      - apply (ex_seriesC_ext (λ a, / (p * Sf) * rpow (f a) p)).
        { intro; rewrite /Rdiv; ring. }
        by apply ex_seriesC_scal_l.
      - apply (ex_seriesC_ext (λ a, / (q * Sg) * rpow (g a) q)).
        { intro; rewrite /Rdiv; ring. }
        by apply ex_seriesC_scal_l. }
    intro a; split.
    { apply Rmult_le_pos; [apply Hf|apply Hg]. }
    trans (cf * cg * ((f a / cf) * (g a / cg))).
    { apply Req_le. field. split; lra. }
    trans (cf * cg * (rpow (f a / cf) p / p + rpow (g a / cg) q / q)).
    { apply Rmult_le_compat_l; [nra|].
      apply Rmult_young => //.
      - apply Rdiv_le_0_compat; [apply Hf|lra].
      - apply Rdiv_le_0_compat; [apply Hg|lra]. }
    apply Req_le.
    rewrite Hfn Hgn.
    field; repeat split; lra. }
  rewrite SeriesC_scal_l.
  rewrite SeriesC_plus; last first.
  { apply (ex_seriesC_ext (λ a, / (q * Sg) * rpow (g a) q)).
    { intro; rewrite /Rdiv; ring. }
    by apply ex_seriesC_scal_l. }
  { apply (ex_seriesC_ext (λ a, / (p * Sf) * rpow (f a) p)).
    { intro; rewrite /Rdiv; ring. }
    by apply ex_seriesC_scal_l. }
  rewrite (SeriesC_ext (λ a, rpow (f a) p / (p * Sf))
             (λ a, / (p * Sf) * rpow (f a) p));
    [|intro; rewrite /Rdiv; ring].
  rewrite (SeriesC_ext (λ a, rpow (g a) q / (q * Sg))
             (λ a, / (q * Sg) * rpow (g a) q));
    [|intro; rewrite /Rdiv; ring].
  rewrite !SeriesC_scal_l -/Sf -/Sg.
  apply Req_le.
  replace (/ (p * Sf) * Sf + / (q * Sg) * Sg) with (/ p + / q);
    [rewrite Hpq; ring|].
  field; repeat split; lra.
Qed.

Lemma Rinv_nonneg (x : R) : 0 <= x → 0 <= / x.
Proof.
  intros [Hx| <-]; [left; by apply Rinv_0_lt_compat|].
  rewrite Rinv_0; lra.
Qed.

Lemma foldr_Rmax_init {A : Type} (h : A → R) (l : list A) :
  1 <= foldr (λ x r, Rmax (h x) r) 1 l.
Proof.
  induction l as [|x l IH]; simpl; [lra|].
  etrans; [apply IH|apply Rmax_r].
Qed.

Lemma foldr_Rmax_in {A : Type} (h : A → R) (l : list A) (a : A) :
  a ∈ l → h a <= foldr (λ x r, Rmax (h x) r) 1 l.
Proof.
  induction l as [|x l IH]; [by intros ?%elem_of_nil|].
  intros [->|Ha]%elem_of_cons; simpl.
  - apply Rmax_l.
  - etrans; [by apply IH|apply Rmax_r].
Qed.

(** A non-negative countable series is bounded by [r] as soon as all its
    finite restrictions are. *)
Lemma SeriesC_le_from_lists `{Countable A} (f : A → R) (r : R) :
  (∀ a, 0 <= f a) →
  (∀ l : list A, NoDup l →
     SeriesC (λ a, if bool_decide (a ∈ l) then f a else 0) <= r) →
  SeriesC f <= r.
Proof.
  intros Hpos Hl.
  assert (∀ n, 0 <= countable_sum f n) as Hcpos.
  { intro n. rewrite /countable_sum.
    destruct (encode_inv_nat n); simpl; [done|lra]. }
  assert (∀ n, ∃ l : list A, NoDup l ∧
            (∀ a, a ∈ l → ∃ k, (k <= n)%nat ∧ encode_inv_nat k = Some a) ∧
            sumC_n f n =
              SeriesC (λ a, if bool_decide (a ∈ l) then f a else 0))
    as Hpart.
  { induction n as [|n IH].
    - rewrite /sumC_n Hierarchy.sum_O /countable_sum.
      destruct (encode_inv_nat 0%nat) as [a|] eqn:Ha; simpl.
      + exists [a].
        split; [apply NoDup_singleton|].
        split; [intros a' ->%list_elem_of_singleton; eauto|].
        rewrite (SeriesC_ext _ (λ a', if bool_decide (a' = a) then f a' else 0)).
        { rewrite SeriesC_singleton_dependent //. }
        intros a'; do 2 case_bool_decide; try done; set_solver.
      + exists [].
        split; [constructor|].
        split; [by intros ? ?%elem_of_nil|].
        rewrite SeriesC_0 //.
    - destruct IH as (l & Hnd & Hmem & Heq).
      rewrite /sumC_n in Heq.
      rewrite /sumC_n Hierarchy.sum_Sn {2}/countable_sum.
      destruct (encode_inv_nat (S n)) as [a|] eqn:Ha; simpl.
      + assert (a ∉ l) as Hal.
        { intros Hin.
          destruct (Hmem a Hin) as (k & Hk & Hk').
          assert (k = S n); [|lia].
          eapply encode_inv_nat_some_inj; [done|congruence]. }
        exists (a :: l).
        split; [by constructor|].
        split.
        { intros a' [->|Ha']%elem_of_cons.
          - exists (S n); auto.
          - destruct (Hmem a' Ha') as (k & ? & ?).
            exists k; split; [lia|done]. }
        rewrite Heq /Hierarchy.plus /=.
        rewrite (SeriesC_ext (λ a', if bool_decide (a' ∈ a :: l) then f a' else 0)
                  (λ a', (if bool_decide (a' = a) then f a' else 0) +
                         (if bool_decide (a' ∈ l) then f a' else 0))).
        { rewrite SeriesC_plus;
            [|apply ex_seriesC_singleton_dependent|apply ex_seriesC_list].
          rewrite SeriesC_singleton_dependent. lra. }
        intros a'; repeat case_bool_decide; try done; try lra; set_solver.
      + exists l.
        split; [done|].
        split.
        { intros a' Ha'.
          destruct (Hmem a' Ha') as (k & ? & ?).
          exists k; split; [lia|done]. }
        rewrite Heq /Hierarchy.plus /= Rplus_0_r //.
  }
  rewrite /SeriesC.
  apply series_bounded; [done| |].
  - intro n.
    destruct (Hpart n) as (l & Hnd & _ & Heq).
    rewrite /sumC_n in Heq.
    rewrite Heq.
    by apply Hl.
  - apply ex_pos_bounded_series; [done|].
    exists r; intro n.
    destruct (Hpart n) as (l & Hnd & _ & Heq).
    rewrite /sumC_n in Heq.
    rewrite Heq.
    by apply Hl.
Qed.


Section couplings.
  Context `{Countable A, Countable B, Countable A', Countable B'}.
  Context (μ1 : distr A) (μ2 : distr B) (S : A -> B -> Prop).

  (** Rényi-DP coupling with tests in the exponential scale: for strictly
      positive [F], [G], taking logarithms gives
        α * ln (Σ_a μ1 a * F a) <=
        (α-1) * ln (Σ_b μ2 b * G b) + α * (α-1) * ρ,
      and tests may additionally reach [0], expressing loss of mass, which
      makes the coupling compose through [dbind] for subdistributions. *)
  Definition RDPcoupl (α: R) (ρ : R):=
    ∀ (F : A → R) (G : B -> R)
      (HF : ∀ a, 0 <= F a <= 1)
      (HG : ∀ b, 0 <= G b <= 1)
      (HFG : ∀ a b, S a b -> rpow (F a) α <= rpow (G b) (α-1)),
      rpow (SeriesC (λ a, μ1 a * F a)) α <=
      exp (α * (α-1) * ρ) * rpow (SeriesC (λ b, μ2 b * G b)) (α-1).

End couplings.


Section couplings_theory.
  (* Context `{Countable A, Countable B, Countable A', Countable B'}. *)


  Lemma RDPcoupl_dzero `{Countable A, Countable B} (μ : distr B) φ α ρ :
    ( 1 <= α ) ->
    RDPcoupl (dzero (A:=A)) μ φ α ρ.
  Proof.
    intros Hleq ?????. rewrite SeriesC_scal_l.
    rewrite Rmult_0_l rpow_0_l.
    apply Rmult_le_pos; [left; apply exp_pos|].
    apply rpow_nonneg.
  Qed.


  Lemma RDPcoupl_mono `{Countable A', Countable B'} (μ1 μ1': distr A') (μ2 μ2': distr B') R R' α ρ ρ' :
    (∀ a, μ1 a = μ1' a) ->
    (∀ b, μ2 b = μ2' b) ->
    (∀ x y, R x y -> R' x y) ->
    ( 1 <= α ) ->
    ( ρ <= ρ') ->
    RDPcoupl μ1 μ2 R α ρ ->
    RDPcoupl μ1' μ2' R' α ρ'.
  Proof.
    intros Hμ1 Hμ2 HR Hα Hρ Hcpl F G HF HG HFG.
    setoid_rewrite <-Hμ1.
    setoid_rewrite <-Hμ2.
    etrans; [apply Hcpl; eauto|].
    apply Rmult_le_compat_r; [apply rpow_nonneg|].
    apply exp_mono.
    assert (0 <= α * (α - 1)) by nra.
    nra.
  Qed.


  Lemma RDPcoupl_dret `{Countable A, Countable B} (a : A) (b : B) (R : A → B → Prop) α ρ :
    1 <= α →
    0 <= ρ →
    R a b → RDPcoupl (dret a) (dret b) R α ρ.
  Proof.
    intros Hα Hρ HR F G HF HG HFG.
    assert (SeriesC (λ a', dret a a' * F a') = F a) as ->.
    { rewrite -(SeriesC_singleton a (F a)).
      apply SeriesC_ext => a'.
      rewrite dret_pmf_unfold; case_bool_decide; simplify_eq; lra. }
    assert (SeriesC (λ b', dret b b' * G b') = G b) as ->.
    { rewrite -(SeriesC_singleton b (G b)).
      apply SeriesC_ext => b'.
      rewrite dret_pmf_unfold; case_bool_decide; simplify_eq; lra. }
    rewrite -[X in X <= _]Rmult_1_l.
    apply Rmult_le_compat;
      [lra|apply rpow_nonneg| |by apply HFG].
    apply exp_pos_ge_1.
    assert (0 <= α * (α - 1)) by nra.
    nra.
  Qed.


  (** Variant of [RDPcoupl_dret] whose side condition covers the case
      [ρ = 0] at an arbitrary order [α]. *)
  Lemma RDPcoupl_dret' `{Countable A, Countable B} (a : A) (b : B)
    (R : A → B → Prop) α ρ :
    0 <= α * (α - 1) * ρ →
    R a b → RDPcoupl (dret a) (dret b) R α ρ.
  Proof.
    intros Hρ HR F G HF HG HFG.
    assert (SeriesC (λ a', dret a a' * F a') = F a) as ->.
    { rewrite -(SeriesC_singleton a (F a)).
      apply SeriesC_ext => a'.
      rewrite dret_pmf_unfold; case_bool_decide; simplify_eq; lra. }
    assert (SeriesC (λ b', dret b b' * G b') = G b) as ->.
    { rewrite -(SeriesC_singleton b (G b)).
      apply SeriesC_ext => b'.
      rewrite dret_pmf_unfold; case_bool_decide; simplify_eq; lra. }
    rewrite -[X in X <= _]Rmult_1_l.
    apply Rmult_le_compat;
      [lra|apply rpow_nonneg| |by apply HFG].
    by apply exp_pos_ge_1.
  Qed.


  (** [RDPcoupl] is preserved by mapping the right-hand side. *)
  Lemma RDPcoupl_dmap_r `{Countable A, Countable B, Countable B'}
    (f : B → B') (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) α ρ :
    RDPcoupl μ1 μ2 R α ρ →
    RDPcoupl μ1 (dmap f μ2) (λ a b', ∃ b, R a b ∧ b' = f b) α ρ.
  Proof.
    intros Hcpl F G HF HG HFG.
    assert (SeriesC (λ b', dmap f μ2 b' * G b') =
            SeriesC (λ b, μ2 b * G (f b))) as ->.
    { assert (Expval (dmap f μ2) G = Expval μ2 (G ∘ f)) as He.
      { apply Expval_dmap; [intro; apply HG|].
        apply (ex_expval_bounded _ _ 1); intro; apply HG. }
      rewrite /Expval /= in He. done. }
    apply Hcpl; [done|intro b; apply HG|].
    intros a b HR. apply HFG. eauto.
  Qed.


  (** [RDPcoupl] can be strengthened to relate only support points. *)
  Lemma RDPcoupl_pos_R `{Countable A, Countable B}
    (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) α ρ :
    0 <= α →
    RDPcoupl μ1 μ2 R α ρ →
    RDPcoupl μ1 μ2 (λ a b, R a b ∧ 0 < μ1 a ∧ 0 < μ2 b) α ρ.
  Proof.
    intros Hα Hcpl F G HF HG HFG.
    assert (SeriesC (λ a, μ1 a * F a) =
            SeriesC (λ a, μ1 a * (if bool_decide (0 < μ1 a)
                                  then F a else 0))) as ->.
    { apply SeriesC_ext => a.
      case_bool_decide; [done|].
      assert (μ1 a = 0) as ->; [pose proof (pmf_pos μ1 a); lra|ring]. }
    assert (SeriesC (λ b, μ2 b * G b) =
            SeriesC (λ b, μ2 b * (if bool_decide (0 < μ2 b)
                                  then G b else 1))) as ->.
    { apply SeriesC_ext => b.
      case_bool_decide; [done|].
      assert (μ2 b = 0) as ->; [pose proof (pmf_pos μ2 b); lra|ring]. }
    apply Hcpl.
    - intro a; case_bool_decide; [apply HF|lra].
    - intro b; case_bool_decide; [apply HG|lra].
    - intros a b HR.
      do 2 case_bool_decide.
      + apply HFG. done.
      + rewrite rpow_1_l.
        apply rpow_le_1; [done|apply HF].
      + rewrite rpow_0_l. apply rpow_nonneg.
      + rewrite rpow_0_l. apply rpow_nonneg.
  Qed.


  (** [RDPcoupl] is preserved by mapping the left-hand side. *)
  Lemma RDPcoupl_dmap_l `{Countable A, Countable A', Countable B}
    (f : A → A') (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) α ρ :
    RDPcoupl μ1 μ2 R α ρ →
    RDPcoupl (dmap f μ1) μ2 (λ a' b, ∃ a, R a b ∧ a' = f a) α ρ.
  Proof.
    intros Hcpl F G HF HG HFG.
    assert (SeriesC (λ a', dmap f μ1 a' * F a') =
            SeriesC (λ a, μ1 a * F (f a))) as ->.
    { assert (Expval (dmap f μ1) F = Expval μ1 (F ∘ f)) as He.
      { apply Expval_dmap; [intro; apply HF|].
        apply (ex_expval_bounded _ _ 1); intro; apply HF. }
      rewrite /Expval /= in He. done. }
    apply Hcpl; [intro; apply HF|done|].
    intros a b HR. apply HFG. eauto.
  Qed.


  (** The trivial coupling of any full-mass distribution against a point
      mass, relating the support to the point. *)
  Lemma RDPcoupl_trivial_dret_r `{Countable A, Countable B}
    (μ1 : distr A) (b : B) α :
    0 <= α →
    SeriesC μ1 = 1 →
    RDPcoupl μ1 (dret b) (λ a b', 0 < μ1 a ∧ b' = b) α 0.
  Proof.
    intros Hα Hmass F G HF HG HFG.
    assert (SeriesC (λ b', dret b b' * G b') = G b) as ->.
    { rewrite -(SeriesC_singleton b (G b)).
      apply SeriesC_ext => b'.
      rewrite dret_pmf_unfold; case_bool_decide; simplify_eq; lra. }
    replace (α * (α - 1) * 0) with 0 by ring.
    rewrite exp_0 Rmult_1_l.
    assert (∀ a, 0 < μ1 a → rpow (F a) α <= rpow (G b) (α - 1)) as Hpt.
    { intros a Ha. apply HFG. done. }
    destruct Hα as [Hα|Hα]; last first.
    { (* α = 0 *)
      rewrite -Hα.
      destruct (decide (G b <= 0)) as [Hg|Hg%Rnot_le_lt].
      + assert (rpow (G b) (0 - 1) = 0) as Hc0.
        { rewrite /rpow; case_bool_decide; [done|lra]. }
        rewrite Hc0.
        assert (SeriesC (λ a, μ1 a * F a) = 0) as ->.
        { apply SeriesC_0 => a.
          destruct (decide (0 < μ1 a)) as [Ha|Ha%Rnot_lt_le]; last first.
          { assert (μ1 a = 0) as ->; [pose proof (pmf_pos μ1 a); lra|ring]. }
          specialize (Hpt a Ha).
          rewrite -Hα Hc0 /rpow in Hpt.
          case_bool_decide as HFa;
            [|pose proof (exp_pos (0 * ln (F a))); lra].
          assert (F a = 0) as ->; [pose proof (HF a); lra|ring]. }
        rewrite rpow_0_l; lra.
      + rewrite (rpow_pos_eq (G b)) //.
        trans 1.
        * apply rpow_le_1; [lra|].
          trans (SeriesC μ1); [|lra].
          apply SeriesC_le; auto.
          intro a; split; [apply Rmult_le_pos; auto; apply HF|].
          rewrite -{2}(Rmult_1_r (μ1 a)).
          apply Rmult_le_compat_l; auto.
          apply HF.
        * apply exp_pos_ge_1.
          assert (ln (G b) <= 0)
            by (rewrite -ln_1; apply ln_le; [done|apply HG]).
          lra. }
    (* 0 < α *)
    destruct (decide (rpow (G b) (α - 1) <= 0)) as [Hc|Hc%Rnot_le_lt].
    { pose proof (rpow_nonneg (G b) (α - 1)).
      assert (rpow (G b) (α - 1) = 0) as Hc0 by lra.
      assert (SeriesC (λ a, μ1 a * F a) = 0) as ->.
      { apply SeriesC_0 => a.
        destruct (decide (0 < μ1 a)) as [Ha|Ha%Rnot_lt_le]; last first.
        { assert (μ1 a = 0) as ->; [pose proof (pmf_pos μ1 a); lra|ring]. }
        specialize (Hpt a Ha).
        rewrite Hc0 in Hpt.
        pose proof (rpow_nonneg (F a) α).
        destruct (decide (F a <= 0)) as [HFa|HFa%Rnot_le_lt].
        - assert (F a = 0) as ->; [pose proof (HF a); lra|ring].
        - pose proof (rpow_pos (F a) α HFa); lra. }
      rewrite rpow_0_l; lra. }
    set (t := rpow (rpow (G b) (α - 1)) (/ α)).
    assert (0 < t) as Ht by (by apply rpow_pos).
    assert (∀ a, 0 < μ1 a → F a <= t) as HFt.
    { intros a Ha.
      specialize (Hpt a Ha).
      destruct (decide (F a <= 0)) as [HFa|HFa%Rnot_le_lt].
      { trans 0; [done|lra]. }
      rewrite -(rpow_1_r (F a)) //.
      replace 1 with (α * / α) by (field; lra).
      rewrite -rpow_rpow /t.
      apply rpow_le_compat_l; [|done].
      left; by apply Rinv_0_lt_compat. }
    trans (rpow t α); last first.
    { rewrite /t rpow_rpow.
      replace (/ α * α) with 1 by (field; lra).
      rewrite rpow_1_r; [lra|done]. }
    apply rpow_le_compat_l; [lra|].
    trans (SeriesC (λ a, μ1 a * t)); last first.
    { rewrite SeriesC_scal_r Hmass; lra. }
    apply SeriesC_le.
    - intro a; split; [apply Rmult_le_pos; auto; apply HF|].
      destruct (decide (0 < μ1 a)) as [Ha|Ha%Rnot_lt_le].
      + apply Rmult_le_compat_l; auto.
      + assert (μ1 a = 0) as ->; [pose proof (pmf_pos μ1 a); lra|lra].
    - apply ex_seriesC_scal_r.
      apply pmf_ex_seriesC.
  Qed.


  (** The trivial coupling of a point mass against any full-mass
      distribution, relating the point to the support. *)
  Lemma RDPcoupl_dret_trivial `{Countable A, Countable B}
    (a : A) (μ2 : distr B) α ρ :
    1 <= α →
    0 <= ρ →
    SeriesC μ2 = 1 →
    RDPcoupl (dret a) μ2 (λ a' b, a' = a ∧ 0 < μ2 b) α ρ.
  Proof.
    intros Hα Hρ Hmass F G HF HG HFG.
    assert (SeriesC (λ a', dret a a' * F a') = F a) as ->.
    { rewrite -(SeriesC_singleton a (F a)).
      apply SeriesC_ext => a'.
      rewrite dret_pmf_unfold; case_bool_decide; simplify_eq; lra. }
    rewrite -[X in X <= _]Rmult_1_l.
    apply Rmult_le_compat; [lra|apply rpow_nonneg| |].
    { apply exp_pos_ge_1.
      assert (0 <= α * (α - 1)) by nra.
      nra. }
    destruct (decide (F a <= 0)) as [Hle|Hpos%Rnot_le_lt].
    { assert (rpow (F a) α = 0) as ->.
      { rewrite /rpow; case_bool_decide; [done|lra]. }
      apply rpow_nonneg. }
    assert (0 < rpow (F a) α) as Hc by (by apply rpow_pos).
    assert (ex_seriesC (λ b, μ2 b * G b)) as Hex.
    { apply (ex_seriesC_le _ μ2); auto.
      intro b; split; [apply Rmult_le_pos; auto; apply HG|].
      rewrite -{2}(Rmult_1_r (μ2 b)).
      apply Rmult_le_compat_l; auto.
      apply HG. }
    destruct Hα as [Hα|Hα]; last first.
    { (* α = 1 *)
      rewrite -Hα.
      replace (1 - 1) with 0 by ring.
      assert (0 < SeriesC (λ b, μ2 b * G b)) as Hpos2.
      { destruct (SeriesC_gtz_ex μ2 (pmf_pos μ2)) as (b & Hb); [lra|].
        specialize (HFG a b (conj eq_refl Hb)).
        rewrite -Hα in HFG.
        rewrite rpow_1_r // in HFG.
        assert (0 < G b) as HGb.
        { destruct (decide (G b <= 0)) as [HGb|HGb%Rnot_le_lt]; [|done].
          assert (rpow (G b) 0 = 0) as Hz.
          { rewrite /rpow; case_bool_decide; [done|lra]. }
          replace (1 - 1) with 0 in HFG by ring.
          rewrite Hz in HFG. lra. }
        apply (Rlt_le_trans _ (μ2 b * G b)).
        - by apply Rmult_lt_0_compat.
        - apply (SeriesC_ge_elem (λ b0, μ2 b0 * G b0) b); [|done].
          intro b'; apply Rmult_le_pos; auto; apply HG. }
      rewrite (rpow_pos_eq _ 0 Hpos2) Rmult_0_l exp_0.
      rewrite rpow_1_r //.
      apply HF. }
    (* 1 < α *)
    set (T := rpow (rpow (F a) α) (/ (α - 1))).
    assert (0 < T) as HT by (by apply rpow_pos).
    assert (∀ b, 0 < μ2 b → T <= G b) as HTb.
    { intros b Hb.
      specialize (HFG a b (conj eq_refl Hb)).
      assert (0 < G b) as HGb.
      { destruct (decide (G b <= 0)) as [HGb|HGb%Rnot_le_lt]; [|done].
        assert (rpow (G b) (α - 1) = 0) as Hz.
        { rewrite /rpow; case_bool_decide; [done|lra]. }
        rewrite Hz in HFG. lra. }
      rewrite -(rpow_1_r (G b)) //.
      replace 1 with ((α - 1) * / (α - 1)) by (field; lra).
      rewrite -rpow_rpow.
      rewrite /T.
      apply rpow_le_compat_l; [|done].
      left; apply Rinv_0_lt_compat; lra. }
    trans (rpow T (α - 1)); last first.
    { apply rpow_le_compat_l; [lra|].
      trans (SeriesC (λ b, μ2 b * T)).
      { rewrite SeriesC_scal_r Hmass; lra. }
      apply SeriesC_le; [|done].
      intro b; split.
      - apply Rmult_le_pos; auto; lra.
      - destruct (decide (0 < μ2 b)) as [Hb|Hb%Rnot_lt_le].
        + apply Rmult_le_compat_l; auto.
        + assert (μ2 b = 0) as ->; [pose proof (pmf_pos μ2 b); lra|lra]. }
    rewrite /T rpow_rpow.
    replace (/ (α - 1) * (α - 1)) with 1 by (field; lra).
    rewrite rpow_1_r; [lra|done].
  Qed.


  Lemma RDPcoupl_dbind `{Countable A, Countable B, Countable A', Countable B'} (f : A → distr A') (g : B → distr B')
    (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A' → B' → Prop) α ρ1 ρ2:
    ( 1 <= α ) ->
    (0 <= ρ1) ->
    (0 <= ρ2) ->
    (∀ a b, R a b → RDPcoupl (f a) (g b) S α ρ2) → RDPcoupl μ1 μ2 R α ρ1 → RDPcoupl (dbind f μ1) (dbind g μ2) S α (ρ1 + ρ2).
  Proof.
    intros Hα Hρ1 Hρ2 Hcoup_fg Hcoup_R h1 h2 Hh1 Hh2 Hh12.
    rewrite /pmf/=/dbind_pmf.
    setoid_rewrite <-SeriesC_scal_r.
    (* LHS: Fubini, then pull μ1 a out of the inner sum. *)
    rewrite <-(fubini_pos_seriesC (λ '(a,x), μ1 x * f x a * h1 a)).
    2: { real_solver. }
    2: { intro a'.
         apply (ex_seriesC_le _ μ1); auto.
         intro a; split.
         + apply Rmult_le_pos; [real_solver|real_solver].
         + rewrite <- Rmult_1_r.
           rewrite Rmult_assoc.
           apply Rmult_le_compat_l; auto.
           rewrite <- Rmult_1_r.
           apply Rmult_le_compat; real_solver. }
    2: { setoid_rewrite SeriesC_scal_r.
         apply (ex_seriesC_le _ (λ a : A', SeriesC (λ x : A, μ1 x * f x a)));
           auto.
         + series.
         + apply (pmf_ex_seriesC (dbind f μ1)). }
    assert (SeriesC (λ b : A, SeriesC (λ a : A', μ1 b * f b a * h1 a)) =
            SeriesC (λ b : A, μ1 b * SeriesC (λ a : A', f b a * h1 a))) as ->.
    { setoid_rewrite <- SeriesC_scal_l. series. }
    (* RHS: Fubini, then pull μ2 b out of the inner sum. *)
    rewrite <-(fubini_pos_seriesC (λ '(b,x), μ2 x * g x b * h2 b)).
    2: by series.
    2: { intro b'.
         specialize (Hh2 b').
         apply (ex_seriesC_le _ μ2); auto.
         intro b; split.
         - series.
         - do 2 rewrite <- Rmult_1_r. series. }
    2: { setoid_rewrite SeriesC_scal_r.
         apply (ex_seriesC_le _ (λ a : B', SeriesC (λ b : B, μ2 b * g b a)));
           auto.
         - intros b'; specialize (Hh2 b'); split.
           + apply Rmult_le_pos; [ | lra].
             apply (pmf_pos ((dbind g μ2)) b').
           + rewrite <- Rmult_1_r.
             apply Rmult_le_compat_l; auto.
             * apply SeriesC_ge_0'. real_solver.
             * real_solver.
         - apply (pmf_ex_seriesC (dbind g μ2)). }
    assert (SeriesC (λ b : B, SeriesC (λ a : B', μ2 b * g b a * h2 a)) =
            SeriesC (λ b : B, μ2 b * SeriesC (λ a : B', g b a * h2 a))) as ->.
    { apply SeriesC_ext; intro.
      rewrite <- SeriesC_scal_l.
      apply SeriesC_ext; real_solver. }
    (* Cut at the outer coupling applied to the mid-tests
         X a = Σ_{a'} f a a' * h1 a'   and
         V b = min(1, exp(α ρ2) * Σ_{b'} g b b' * h2 b');
       the clipping keeps V within [0,1] while exp(α ρ2) absorbs the
       grading of the inner couplings. *)
    trans (exp (α * (α - 1) * ρ1) *
           rpow (SeriesC (λ b : B, μ2 b *
             Rmin 1 (exp (α * ρ2) * SeriesC (λ a : B', g b a * h2 a))))
             (α - 1)).
    - apply (Hcoup_R (λ a, SeriesC (λ a', f a a' * h1 a'))
               (λ b, Rmin 1 (exp (α * ρ2) *
                             SeriesC (λ b', g b b' * h2 b')))).
      + intro a; split.
        * apply SeriesC_ge_0'; intro a'; specialize (Hh1 a'); real_solver.
        * apply (Rle_trans _ (SeriesC (f a))); auto.
          apply SeriesC_le; auto.
          intro a'; specialize (Hh1 a'); real_solver.
      + intro b; split.
        * apply Rmin_glb; [lra|].
          apply Rmult_le_pos; [left; apply exp_pos|].
          apply SeriesC_ge_0'; intro b'; specialize (Hh2 b'); real_solver.
        * apply Rmin_l.
      + intros a b Rab.
        destruct (Rle_dec 1 (exp (α * ρ2) *
                             SeriesC (λ b', g b b' * h2 b')))
          as [Hclip|Hclip].
        * rewrite Rmin_left; [|done].
          rewrite rpow_1_l.
          apply rpow_le_1; [lra|].
          apply (Rle_trans _ (SeriesC (f a))); auto.
          apply SeriesC_le; auto.
          intro a'; specialize (Hh1 a'); real_solver.
        * rewrite Rmin_right; [|lra].
          rewrite rpow_mult_distr; [|apply exp_pos].
          rewrite rpow_exp.
          replace ((α - 1) * (α * ρ2)) with (α * (α - 1) * ρ2) by ring.
          apply Hcoup_fg; auto.
    - trans (exp (α * (α - 1) * ρ1) *
             rpow (exp (α * ρ2) *
               SeriesC (λ b : B, μ2 b * SeriesC (λ a : B', g b a * h2 a)))
               (α - 1)).
      + apply Rmult_le_compat_l; [left; apply exp_pos|].
        apply rpow_le_compat_l; [lra|].
        rewrite -SeriesC_scal_l.
        apply SeriesC_le.
        * intro b; split.
          -- apply Rmult_le_pos; auto.
             apply Rmin_glb; [lra|].
             apply Rmult_le_pos; [left; apply exp_pos|].
             apply SeriesC_ge_0'; intro b'; specialize (Hh2 b');
               real_solver.
          -- apply (Rle_trans _ (μ2 b * (exp (α * ρ2) *
                                 SeriesC (λ a : B', g b a * h2 a)))).
             ++ apply Rmult_le_compat_l; auto.
                apply Rmin_r.
             ++ apply Req_le; ring.
        * apply ex_seriesC_scal_l.
          apply (ex_seriesC_le _ μ2); auto.
          intro b; split.
          -- apply Rmult_le_pos; auto.
             apply SeriesC_ge_0'; intro b'; specialize (Hh2 b');
               real_solver.
          -- rewrite <- Rmult_1_r.
             apply Rmult_le_compat_l; auto.
             apply (Rle_trans _ (SeriesC (g b))); auto.
             apply SeriesC_le; auto.
             intro b'; specialize (Hh2 b'); real_solver.
      + rewrite rpow_mult_distr; [|apply exp_pos].
        rewrite rpow_exp.
        rewrite -Rmult_assoc -exp_plus.
        apply Rmult_le_compat_r; [apply rpow_nonneg|].
        apply Req_le; f_equal; ring.
  Qed.


  Lemma RDPcoupl_eq_elim_rdp `{Countable A} (μ1 μ2 : distr A) α ρ:
    ( 1 <= α ) ->
    (0 <= ρ) ->
    RDPcoupl μ1 μ2 (=) α ρ →
    SeriesC (λ a : A, μ1(a) * (rpow (μ1(a)) (α-1))/(rpow (μ2(a)) (α-1))) <= exp (α * (α-1) * ρ).
  Proof.
    intros Hα Hρ Hcpl.
    assert (∀ a, 0 <= μ1 a * rpow (μ1 a) (α - 1) / rpow (μ2 a) (α - 1))
      as Htpos.
    { intro a.
      apply Rmult_le_pos; [|apply Rinv_nonneg, rpow_nonneg].
      apply Rmult_le_pos; [auto|apply rpow_nonneg]. }
    destruct Hα as [Hα| <-]; last first.
    { (* α = 1: the series is bounded by the mass of μ1. *)
      replace (1 * (1 - 1) * ρ) with 0 by ring.
      rewrite exp_0.
      trans (SeriesC μ1); [|apply pmf_SeriesC].
      apply SeriesC_le; [|apply pmf_ex_seriesC].
      intro a; split; [apply Htpos|].
      replace (1 - 1) with 0 by ring.
      rewrite /Rdiv.
      rewrite -{3}(Rmult_1_r (μ1 a)) Rmult_assoc.
      apply Rmult_le_compat_l; [auto|].
      assert (rpow (μ1 a) 0 <= 1) by (apply rpow_le_1; [lra|auto]).
      assert (/ rpow (μ2 a) 0 <= 1);
        [|assert (0 <= rpow (μ1 a) 0) by apply rpow_nonneg;
          assert (0 <= / rpow (μ2 a) 0)
            by (apply Rinv_nonneg, rpow_nonneg);
          nra].
      rewrite /rpow.
      case_bool_decide; [rewrite Rinv_0; lra|].
      rewrite Rmult_0_l exp_0 Rinv_1; lra. }
    (* α > 1: it suffices to bound every finite restriction, using the
       coupling with tests d^(α-1) * (μ1/μ2)^(α-1) and d^α * (μ1/μ2)^α
       supported on the finite set, where d normalizes them into [0,1]. *)
    apply SeriesC_le_from_lists; [done|].
    intros l Hnd.
    set (t := λ a : A, μ1 a * rpow (μ1 a) (α - 1) / rpow (μ2 a) (α - 1)).
    set (ratio := λ a : A, rpow (μ1 a) (α - 1) * / rpow (μ2 a) (α - 1)).
    set (ratio' := λ a : A, rpow (μ1 a) α * / rpow (μ2 a) α).
    set (B := foldr (λ x r, Rmax (ratio x) r) 1 l).
    set (B' := foldr (λ x r, Rmax (ratio' x) r) 1 l).
    set (d := Rmin (rpow (/ B) (/ (α - 1))) (rpow (/ B') (/ α))).
    assert (1 <= B) as HB by apply foldr_Rmax_init.
    assert (1 <= B') as HB' by apply foldr_Rmax_init.
    assert (0 < d) as Hd.
    { apply Rmin_glb_lt; apply rpow_pos, Rinv_0_lt_compat; lra. }
    assert (rpow d (α - 1) <= / B) as HdB.
    { trans (rpow (rpow (/ B) (/ (α - 1))) (α - 1)).
      - apply rpow_le_compat_l; [lra|apply Rmin_l].
      - rewrite rpow_rpow.
        replace (/ (α - 1) * (α - 1)) with 1 by (field; lra).
        rewrite rpow_1_r //.
        apply Rinv_0_lt_compat; lra. }
    assert (rpow d α <= / B') as HdB'.
    { trans (rpow (rpow (/ B') (/ α)) α).
      - apply rpow_le_compat_l; [lra|apply Rmin_r].
      - rewrite rpow_rpow.
        replace (/ α * α) with 1 by (field; lra).
        rewrite rpow_1_r //.
        apply Rinv_0_lt_compat; lra. }
    assert (∀ a, 0 <= ratio a) as Hrpos.
    { intro; apply Rmult_le_pos;
        [apply rpow_nonneg|apply Rinv_nonneg, rpow_nonneg]. }
    assert (∀ a, 0 <= ratio' a) as Hr'pos.
    { intro; apply Rmult_le_pos;
        [apply rpow_nonneg|apply Rinv_nonneg, rpow_nonneg]. }
    assert (∀ a, μ2 a * ratio' a = t a) as Hkey.
    { intro a.
      rewrite /ratio' /t /Rdiv.
      destruct (decide (μ2 a <= 0)) as [Hm2|Hm2%Rnot_le_lt].
      - assert (μ2 a = 0) as ->.
        { pose proof (pmf_pos μ2 a); lra. }
        rewrite !rpow_0_l !Rinv_0.
        ring.
      - destruct (decide (μ1 a <= 0)) as [Hm1|Hm1%Rnot_le_lt].
        + assert (μ1 a = 0) as ->.
          { pose proof (pmf_pos μ1 a); lra. }
          rewrite !rpow_0_l.
          ring.
        + rewrite (rpow_split1 (μ1 a) α) // (rpow_split1 (μ2 a) α) //.
          rewrite Rinv_mult.
          pose proof (rpow_pos (μ2 a) (α - 1) Hm2).
          field.
          split; apply Rgt_not_eq; lra. }
    set (Z := SeriesC (λ a : A, if bool_decide (a ∈ l)
              then μ1 a * rpow (μ1 a) (α - 1) / rpow (μ2 a) (α - 1)
              else 0)).
    assert (SeriesC (λ a, μ1 a * (if bool_decide (a ∈ l)
              then rpow d (α - 1) * ratio a else 0)) =
            rpow d (α - 1) * Z) as HS1.
    { rewrite /Z -SeriesC_scal_l.
      apply SeriesC_ext; intro a.
      case_bool_decide; [rewrite /ratio /Rdiv; ring|ring]. }
    assert (SeriesC (λ a, μ2 a * (if bool_decide (a ∈ l)
              then rpow d α * ratio' a else 0)) =
            rpow d α * Z) as HS2.
    { rewrite /Z -SeriesC_scal_l.
      apply SeriesC_ext; intro a.
      case_bool_decide; [|ring].
      trans (rpow d α * (μ2 a * ratio' a)); [ring|].
      rewrite Hkey /t /Rdiv //. }
    assert (rpow (rpow d (α - 1) * Z) α <=
            exp (α * (α - 1) * ρ) * rpow (rpow d α * Z) (α - 1)) as Hfinal.
    { rewrite -HS1 -HS2.
      apply Hcpl.
      - intro a.
        case_bool_decide; [|lra].
        split.
        + apply Rmult_le_pos; [apply rpow_nonneg|auto].
        + trans (/ B * B); last first.
          { rewrite Rinv_l; lra. }
          apply Rmult_le_compat; [apply rpow_nonneg|auto|exact HdB|].
          by apply (foldr_Rmax_in ratio).
      - intro a.
        case_bool_decide; [|lra].
        split.
        + apply Rmult_le_pos; [apply rpow_nonneg|auto].
        + trans (/ B' * B'); last first.
          { rewrite Rinv_l; lra. }
          apply Rmult_le_compat; [apply rpow_nonneg|auto|exact HdB'|].
          by apply (foldr_Rmax_in ratio').
      - intros a b <-.
        case_bool_decide as Hin; last first.
        { rewrite rpow_0_l. apply rpow_nonneg. }
        destruct (decide (μ1 a <= 0)) as [Hm1|Hm1%Rnot_le_lt].
        { assert (μ1 a = 0) as Hz by (pose proof (pmf_pos μ1 a); lra).
          rewrite /ratio Hz rpow_0_l.
          replace (rpow d (α - 1) * (0 * / rpow (μ2 a) (α - 1))) with 0
            by ring.
          rewrite rpow_0_l. apply rpow_nonneg. }
        destruct (decide (μ2 a <= 0)) as [Hm2|Hm2%Rnot_le_lt].
        { assert (μ2 a = 0) as Hz by (pose proof (pmf_pos μ2 a); lra).
          rewrite /ratio Hz rpow_0_l Rinv_0.
          replace (rpow d (α - 1) * (rpow (μ1 a) (α - 1) * 0)) with 0
            by ring.
          rewrite rpow_0_l. apply rpow_nonneg. }
        rewrite /ratio /ratio'.
        rewrite -(rpow_inv (μ2 a) (α - 1)) // -(rpow_inv (μ2 a) α) //.
        rewrite -(rpow_mult_distr (μ1 a)) // -(rpow_mult_distr (μ1 a)) //.
        rewrite -(rpow_mult_distr d) // -(rpow_mult_distr d) //.
        rewrite !rpow_rpow.
        apply Req_le; f_equal; ring. }
    assert (0 <= Z) as HZ.
    { rewrite /Z. apply SeriesC_ge_0'.
      intro a; case_bool_decide; [apply Htpos|lra]. }
    destruct HZ as [HZ|HZ]; last first.
    { rewrite -HZ. pose proof (exp_pos (α * (α - 1) * ρ)); lra. }
    rewrite (rpow_mult_distr (rpow d (α - 1)) Z α) in Hfinal;
      [|by apply rpow_pos].
    rewrite (rpow_mult_distr (rpow d α) Z (α - 1)) in Hfinal;
      [|by apply rpow_pos].
    rewrite !rpow_rpow in Hfinal.
    replace (rpow d (α * (α - 1))) with (rpow d ((α - 1) * α)) in Hfinal
      by (f_equal; ring).
    assert (0 < rpow d ((α - 1) * α)) as Hc2 by (by apply rpow_pos).
    assert (rpow Z α <= exp (α * (α - 1) * ρ) * rpow Z (α - 1)) as Hred.
    { apply (Rmult_le_reg_l (rpow d ((α - 1) * α))); [done|].
      etrans; [exact Hfinal|].
      apply Req_le; ring. }
    rewrite (rpow_pos_eq Z α) // (rpow_pos_eq Z (α - 1)) // in Hred.
    rewrite -exp_plus in Hred.
    pose proof (ln_le _ _ (exp_pos (α * ln Z)) Hred) as Hlnle.
    rewrite !ln_exp in Hlnle.
    rewrite -(exp_ln Z) //.
    apply exp_mono; lra.
  Qed.


  (** Logarithmic characterization of [RDPcoupl]: for tests whose μ1-side
      expectation is positive, the coupling is the familiar Rényi-style
      inequality on logarithms, and it additionally forces the μ2-side
      expectation to be positive. *)
  Lemma RDPcoupl_ln_iff `{Countable A, Countable B} (μ1 : distr A)
    (μ2 : distr B) (S : A → B → Prop) α ρ :
    RDPcoupl μ1 μ2 S α ρ ↔
    (∀ (F : A → R) (G : B → R)
       (HF : ∀ a, 0 <= F a <= 1)
       (HG : ∀ b, 0 <= G b <= 1)
       (HFG : ∀ a b, S a b → rpow (F a) α <= rpow (G b) (α-1)),
       0 < SeriesC (λ a, μ1 a * F a) →
       0 < SeriesC (λ b, μ2 b * G b) ∧
       α * ln (SeriesC (λ a, μ1 a * F a)) <=
       (α-1) * ln (SeriesC (λ b, μ2 b * G b)) + α * (α-1) * ρ).
  Proof.
    split.
    - intros Hcpl F G HF HG HFG Hpos1.
      specialize (Hcpl F G HF HG HFG).
      assert (0 < SeriesC (λ b, μ2 b * G b)) as Hpos2.
      { destruct (Rle_or_lt (SeriesC (λ b, μ2 b * G b)) 0) as [Hle|];
          [|done].
        exfalso.
        rewrite (rpow_pos_eq _ α Hpos1) in Hcpl.
        assert (rpow (SeriesC (λ b, μ2 b * G b)) (α-1) = 0) as Hz.
        { rewrite /rpow. case_bool_decide; [done|lra]. }
        rewrite Hz Rmult_0_r in Hcpl.
        pose proof (exp_pos (α * ln (SeriesC (λ a, μ1 a * F a)))); lra. }
      split; [done|].
      rewrite (rpow_pos_eq _ α Hpos1) (rpow_pos_eq _ (α-1) Hpos2) in Hcpl.
      rewrite -exp_plus in Hcpl.
      pose proof (ln_le _ _ (exp_pos _) Hcpl) as Hln.
      rewrite !ln_exp in Hln.
      lra.
    - intros Hlog F G HF HG HFG.
      assert (0 <= SeriesC (λ a, μ1 a * F a)) as Hge1.
      { apply SeriesC_ge_0'; intro a.
        apply Rmult_le_pos; [auto|apply HF]. }
      destruct Hge1 as [Hpos1|Hz1]; last first.
      { rewrite -Hz1 rpow_0_l.
        apply Rmult_le_pos; [left; apply exp_pos|apply rpow_nonneg]. }
      destruct (Hlog F G HF HG HFG Hpos1) as [Hpos2 Hln].
      rewrite (rpow_pos_eq _ α Hpos1) (rpow_pos_eq _ (α-1) Hpos2).
      rewrite -exp_plus.
      apply exp_mono; lra.
  Qed.


  (** Introduction rule for [RDPcoupl] at the equality relation: a bound on
      the α-th moment of the likelihood ratio yields a coupling.  Converse of
      [RDPcoupl_eq_elim_rdp], by Hölder's inequality. *)
  Lemma RDPcoupl_eq_intro `{Countable A} (μ1 μ2 : distr A) α ρ :
    1 <= α →
    (∀ a, 0 < μ2 a) →
    ex_seriesC (λ a, rpow (μ1 a) α * rpow (μ2 a) (1 - α)) →
    SeriesC (λ a, rpow (μ1 a) α * rpow (μ2 a) (1 - α)) <=
      exp (α * (α - 1) * ρ) →
    RDPcoupl μ1 μ2 (=) α ρ.
  Proof.
    intros Hα Hpos Hex HZ F G HF HG HFG.
    destruct (Rle_lt_or_eq_dec 1 α Hα) as [Hlt | Heq]; last first.
    { (* Limit case: α = 1 *)
      subst α.
      assert (0 <= SeriesC (λ a, μ1 a * F a)) as HSF0.
      { apply SeriesC_ge_0'; intro a; apply Rmult_le_pos; [auto|apply HF]. }
      assert (0 <= SeriesC (λ b, μ2 b * G b)) as HSG0.
      { apply SeriesC_ge_0'; intro b; apply Rmult_le_pos; [auto|apply HG]. }
      replace (1 * (1 - 1) * ρ) with 0 by ring. rewrite exp_0 Rmult_1_l.
      replace (1 - 1) with 0 by ring.
      rewrite (rpow_1_r' (SeriesC (λ a, μ1 a * F a))) //.
      assert (ex_seriesC (λ b, μ2 b * G b)) as HexG.
      { apply (ex_seriesC_le _ μ2); [|apply pmf_ex_seriesC].
        intro b; split; [apply Rmult_le_pos; [auto|apply HG]|].
        rewrite -{2}(Rmult_1_r (μ2 b)). apply Rmult_le_compat_l; [auto|apply HG]. }
      destruct (Rle_lt_or_eq_dec 0 (SeriesC (λ b, μ2 b * G b)) HSG0)
        as [HSGpos | HSGz].
      - rewrite (rpow_pos_eq _ 0 HSGpos) Rmult_0_l exp_0.
        trans (SeriesC μ1); [|apply pmf_SeriesC].
        apply SeriesC_le; [|apply pmf_ex_seriesC].
        intro a; split; [apply Rmult_le_pos; [auto|apply HF]|].
        rewrite -{2}(Rmult_1_r (μ1 a)). apply Rmult_le_compat_l; [auto|apply HF].
      - rewrite -HSGz rpow_0_l.
        assert (SeriesC (λ a, μ1 a * F a) = 0) as ->; [|lra].
        apply SeriesC_0. intro a.
        assert (G a = 0) as HGa0.
        { assert (μ2 a * G a <= 0).
          { rewrite HSGz. apply (SeriesC_ge_elem (λ b, μ2 b * G b) a); [|done].
            intro b; apply Rmult_le_pos; [auto|apply HG]. }
          pose proof (Hpos a). pose proof (HG a). nra. }
        specialize (HFG a a eq_refl).
        rewrite (rpow_1_r' (F a) ltac:(apply HF)) HGa0 (rpow_0_l (1 - 1)) in HFG.
        pose proof (HF a). assert (F a = 0) as -> by lra. ring. }
    (* α > 1: Hölder splitting of μ1 F at conjugate exponents (α, α/(α-1)) *)
    set (u := λ a, rpow (rpow (μ1 a) α * rpow (μ2 a) (1 - α) *
                        (rpow (F a) α * rpow (G a) (1 - α))) (/ α)).
    set (v := λ a, rpow (μ2 a * G a) ((α - 1) / α)).
    assert (∀ a, F a = 0 → μ1 a * F a = u a * v a) as Hcase0.
    { intros a HFa.
      rewrite /u /v.
      cbv beta.
      rewrite HFa.
      rewrite (rpow_0_l α).
      rewrite Rmult_0_l.
      rewrite !Rmult_0_r (rpow_0_l (/ α)).
      ring. }
    assert (∀ a, μ1 a * F a = u a * v a) as Huv.
    { intro a.
      destruct (decide (G a <= 0)) as [HGa|HGa%Rnot_le_lt].
      { assert (G a = 0) as HG0; [pose proof (HG a); lra|].
        apply Hcase0.
        specialize (HFG a a eq_refl).
        rewrite HG0 (rpow_0_l (α - 1)) in HFG.
        pose proof (rpow_nonneg (F a) α).
        apply (rpow_eq_0 _ α); [apply HF|lra|lra]. }
      destruct (decide (F a <= 0)) as [HFa|HFa%Rnot_le_lt].
      { apply Hcase0. pose proof (HF a); lra. }
      destruct (decide (μ1 a <= 0)) as [Hm1|Hm1%Rnot_le_lt].
      { assert (μ1 a = 0) as Hm0; [pose proof (pmf_pos μ1 a); lra|].
        rewrite /u /v.
        cbv beta.
        rewrite Hm0 (rpow_0_l α) !Rmult_0_l (rpow_0_l (/ α)).
        ring. }
      pose proof (Hpos a) as Hm2.
      rewrite /u /v.
      cbv beta.
      rewrite !(rpow_pos_eq (μ1 a)) // !(rpow_pos_eq (μ2 a)) //
        !(rpow_pos_eq (F a)) // !(rpow_pos_eq (G a)) //.
      rewrite -!exp_plus rpow_exp.
      assert (μ2 a * G a = exp (ln (μ2 a) + ln (G a))) as ->.
      { rewrite exp_plus !exp_ln //. }
      rewrite rpow_exp -exp_plus.
      assert (μ1 a * F a = exp (ln (μ1 a) + ln (F a))) as ->.
      { rewrite exp_plus !exp_ln //. }
      f_equal.
      field; lra. }
    assert (∀ a, 0 <= u a) as Hu by (intro; apply rpow_nonneg).
    assert (∀ a, 0 <= v a) as Hv by (intro; apply rpow_nonneg).
    assert (1 < α / (α - 1)) as Hq.
    { apply (Rmult_lt_reg_r (α - 1)); [lra|].
      rewrite Rmult_1_l /Rdiv Rmult_assoc Rinv_l; lra. }
    assert (/ α + / (α / (α - 1)) = 1) as Hpq.
    { rewrite Rinv_div. field; lra. }
    assert (∀ a, rpow (u a) α =
            rpow (μ1 a) α * rpow (μ2 a) (1 - α) *
            (rpow (F a) α * rpow (G a) (1 - α))) as Huα.
    { intro a.
      rewrite /u; cbv beta.
      rewrite rpow_rpow.
      replace (/ α * α) with 1 by (field; lra).
      apply rpow_1_r'.
      apply Rmult_le_pos; apply Rmult_le_pos; apply rpow_nonneg. }
    assert (∀ a, rpow (v a) (α / (α - 1)) = μ2 a * G a) as Hvq.
    { intro a.
      rewrite /v; cbv beta.
      rewrite rpow_rpow.
      replace ((α - 1) / α * (α / (α - 1))) with 1 by (field; lra).
      apply rpow_1_r'.
      apply Rmult_le_pos; [auto|apply HG]. }
    assert (∀ a, rpow (F a) α * rpow (G a) (1 - α) <= 1) as HFG1.
    { intro a.
      destruct (decide (G a <= 0)) as [HGa|HGa%Rnot_le_lt].
      { assert (G a = 0) as ->; [pose proof (HG a); lra|].
        rewrite (rpow_0_l (1 - α)) Rmult_0_r. lra. }
      trans (rpow (G a) (α - 1) * rpow (G a) (1 - α)).
      { apply Rmult_le_compat_r; [apply rpow_nonneg|].
        by apply HFG. }
      rewrite -rpow_plus //.
      replace (α - 1 + (1 - α)) with 0 by ring.
      rewrite rpow_pos_eq // Rmult_0_l exp_0. lra. }
    assert (∀ a, rpow (u a) α <=
            rpow (μ1 a) α * rpow (μ2 a) (1 - α)) as Hub.
    { intro a.
      rewrite Huα.
      rewrite -{2}(Rmult_1_r (rpow (μ1 a) α * rpow (μ2 a) (1 - α))).
      apply Rmult_le_compat_l; [apply Rmult_le_pos; apply rpow_nonneg|].
      apply HFG1. }
    assert (ex_seriesC (λ a, rpow (u a) α)) as Hexu.
    { apply (ex_seriesC_le _ (λ a, rpow (μ1 a) α * rpow (μ2 a) (1 - α)));
        [|done].
      intro a; split; [apply rpow_nonneg|apply Hub]. }
    assert (ex_seriesC (λ a, rpow (v a) (α / (α - 1)))) as Hexv.
    { apply (ex_seriesC_le _ μ2); [|apply pmf_ex_seriesC].
      intro a; split; [apply rpow_nonneg|].
      rewrite Hvq.
      rewrite -{2}(Rmult_1_r (μ2 a)).
      apply Rmult_le_compat_l; [auto|apply HG]. }
    assert (SeriesC (λ a, μ1 a * F a) <=
            rpow (SeriesC (λ a, rpow (u a) α)) (/ α) *
            rpow (SeriesC (λ a, rpow (v a) (α / (α - 1))))
              (/ (α / (α - 1)))) as Hhold.
    { rewrite (SeriesC_ext _ (λ a, u a * v a)); [|intro; apply Huv].
      apply SeriesC_rpow_Hoelder; auto. }
    rewrite (SeriesC_ext (λ a, rpow (v a) (α / (α - 1)))
              (λ b, μ2 b * G b)) in Hhold; [|intro; apply Hvq].
    assert (SeriesC (λ a, rpow (u a) α) <= exp (α * (α - 1) * ρ)) as HSU.
    { etrans; [|exact HZ].
      apply SeriesC_le; [|done].
      intro a; split; [apply rpow_nonneg|apply Hub]. }
    assert (0 <= SeriesC (λ a, rpow (u a) α)) as HSU0.
    { apply SeriesC_ge_0'; intro; apply rpow_nonneg. }
    assert (0 <= SeriesC (λ a, μ1 a * F a)) as HSF0.
    { apply SeriesC_ge_0'; intro a; apply Rmult_le_pos; [auto|apply HF]. }
    assert (0 <= SeriesC (λ b, μ2 b * G b)) as HSG0.
    { apply SeriesC_ge_0'; intro b; apply Rmult_le_pos; [auto|apply HG]. }
    destruct HSU0 as [HSU0|HSU0]; last first.
    { rewrite -HSU0 (rpow_0_l (/ α)) Rmult_0_l in Hhold.
      assert (SeriesC (λ a, μ1 a * F a) = 0) as ->; [lra|].
      rewrite (rpow_0_l α).
      apply Rmult_le_pos; [left; apply exp_pos|apply rpow_nonneg]. }
    trans (rpow (rpow (SeriesC (λ a, rpow (u a) α)) (/ α) *
                 rpow (SeriesC (λ b, μ2 b * G b)) (/ (α / (α - 1)))) α).
    { apply rpow_le_compat_l; [lra|done]. }
    rewrite rpow_mult_distr; [|by apply rpow_pos].
    rewrite !rpow_rpow.
    replace (/ α * α) with 1 by (field; lra).
    rewrite (rpow_1_r' (SeriesC (λ a, rpow (u a) α))); [|lra].
    replace (/ (α / (α - 1)) * α) with (α - 1).
    2:{ rewrite Rinv_div. field; lra. }
    apply Rmult_le_compat_r; [apply rpow_nonneg|done].
  Qed.


  Lemma RDPcoupl_eq_refl `{Countable A} (μ : distr A) α ρ :
    1 <= α → 0 <= ρ → (∀ a, 0 < μ a) →
    RDPcoupl μ μ (=) α ρ.
  Proof.
    intros Hα Hρ Hpos.
    assert (∀ a, rpow (μ a) α * rpow (μ a) (1 - α) = μ a) as Heq.
    { intro a.
      rewrite -rpow_plus //.
      replace (α + (1 - α)) with 1 by ring.
      rewrite rpow_1_r //. }
    apply RDPcoupl_eq_intro => //.
    - eapply ex_seriesC_ext; [|apply (pmf_ex_seriesC μ)].
      intro a. rewrite Heq //.
    - rewrite (SeriesC_ext _ μ); [|intro a; rewrite Heq //].
      trans 1; [apply pmf_SeriesC|].
      apply exp_pos_ge_1.
      assert (0 <= α * (α - 1)) by nra.
      nra.
  Qed.


End couplings_theory.
