(** * The paper's entropy upper bound, mechanized.

    This file proves the paper's headline theorem, building on
    [entropy_cost.v]'s [flip_cost] and [entropy_entry.v]'s ERT bounds on the
    FLDR entry points.

    Target (paper Thm. [thm:rejection-dyadic-ddg-entropy], upper half only;
    the lower half [0 <= E[L_T] - H(p)] is out of scope by design):

      [flip_cost ws < shannon_entropy ws + 6]

    given [admissible ws] and [nondegenerate ws], with [shannon_entropy ws :=
    Sum_{w in ws} (w/m) * log2(m/w)], [m := weight_sum ws].

    Scope discipline: Tachis + Eris only.

    Proof plan (mirrors the paper's proof of the theorem): rather than
    following the [Nat.testbit]-based exposition literally, we exploit that
    [model.v] already gives us row occupancy ([occ]/[msum]) as the natural
    "table carries the label's binary digits" fact
    ([ddg_table_occupancy_exact]), so steps (C)+(D) of the plan are done
    over [occ]-indicator sequences instead of explicit bit positions.  This
    also lets the dyadic Knuth-Yao per-weight lemma (step D) be proved by a
    two-case structural induction on the indicator sequence, rather than by
    locating a "leading one" position -- see [bits_KY_bound] in Section 1
    below for the resulting simplification (only ONE genuine analytic fact
    is needed, [ln_y_le_2_ln2_y1], exactly the paper's own substitution),
    and its proof comment for the one place this deviates from the paper's
    literal exposition. *)

From Coq Require Import Arith.PeanoNat Lists.List Reals Psatz Lia.
From clutch.tachis Require Import expected_time_credits ert_weakestpre
  problang_wp proofmode derived_laws ert_rules cost_models adequacy.
From clutch.prob_lang Require Import notation tactics metatheory lang.
From clutch.common Require Import inject.
From clutch.eris.lib Require Import list.
From clutch.eris.lib.sampling.fldr Require Import model implementation walk pure
  distribution entropy_cost entropy_entry interface.
From Coquelicot Require Import Rbar.
Import ListNotations.

Set Default Proof Using "Type*".
#[local] Open Scope R.

(** * 0. Finite real sums over an index range, mirroring [walk.v]'s [nsum]
    machinery but valued in [R].  [Rsum f n = f 0 + f 1 + ... + f (n-1)],
    defined by peeling the LAST index so that induction on [n] is
    structural (this is what makes the per-row "aggregate" unfolding in
    Section 5 a two-line computation). *)

Fixpoint Rsum (f : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S n' => Rsum f n' + f n'
  end.

Lemma Rsum_ext (f g : nat -> R) (n : nat) :
  (forall i, (i < n)%nat -> f i = g i) -> Rsum f n = Rsum g n.
Proof.
  induction n as [|n IH]; intros Hfg; simpl; [reflexivity|].
  assert (Hn : f n = g n) by (apply Hfg; lia).
  assert (Heqrest : Rsum f n = Rsum g n) by (apply IH; intros i Hi; apply Hfg; lia).
  rewrite Hn. rewrite Heqrest. reflexivity.
Qed.

Lemma Rsum_plus (f g : nat -> R) (n : nat) :
  Rsum (fun i => f i + g i) n = Rsum f n + Rsum g n.
Proof. induction n as [|n IH]; simpl; [lra|rewrite IH; lra]. Qed.

Lemma Rsum_scal (c : R) (f : nat -> R) (n : nat) :
  Rsum (fun i => c * f i) n = c * Rsum f n.
Proof. induction n as [|n IH]; simpl; [lra|rewrite IH; lra]. Qed.

Lemma Rsum_scal_r (f : nat -> R) (c : R) (n : nat) :
  Rsum (fun i => f i * c) n = Rsum f n * c.
Proof. induction n as [|n IH]; simpl; [lra|rewrite IH; lra]. Qed.

Lemma Rsum_div_r (f : nat -> R) (c : R) (n : nat) :
  Rsum (fun i => f i / c) n = Rsum f n / c.
Proof. induction n as [|n IH]; simpl; [lra|rewrite IH; lra]. Qed.

Lemma Rsum_div_mul_r (f : nat -> R) (c d : R) (n : nat) :
  Rsum (fun i => f i / d * c) n = Rsum f n / d * c.
Proof. induction n as [|n IH]; simpl; [lra | rewrite IH; lra]. Qed.

Lemma INR_two : INR 2 = 2.
Proof. simpl. lra. Qed.

Lemma Rsum_le (f g : nat -> R) (n : nat) :
  (forall i, (i < n)%nat -> f i <= g i) -> Rsum f n <= Rsum g n.
Proof.
  induction n as [|n IH]; intros Hfg; simpl; [lra|].
  assert (Hfg' : forall i, (i < n)%nat -> f i <= g i) by (intros; apply Hfg; lia).
  specialize (IH Hfg'). specialize (Hfg n ltac:(lia)). lra.
Qed.

Lemma Rsum_const0 (n : nat) : Rsum (fun _ : nat => 0) n = 0.
Proof. induction n as [|n IH]; simpl; lra. Qed.

Lemma Rsum_const1 (n : nat) : Rsum (fun _ : nat => 1) n = INR n.
Proof.
  induction n as [|n IH]; cbn [Rsum]; [reflexivity|].
  rewrite IH. rewrite S_INR. reflexivity.
Qed.

Lemma Rsum_nonneg (f : nat -> R) (n : nat) :
  (forall i, (i < n)%nat -> 0 <= f i) -> 0 <= Rsum f n.
Proof.
  intros Hf. rewrite <- (Rsum_const0 n). apply Rsum_le. intros i Hi. apply Hf, Hi.
Qed.

(** Split the range [0..2A) into paired even/odd indices, mirroring
    [walk.v]'s [nsum_seq_pair]. *)
Lemma Rsum_seq_pair (g : nat -> R) (A : nat) :
  Rsum (fun c => g (2 * c)%nat + g (2 * c + 1)%nat) A = Rsum g (2 * A)%nat.
Proof.
  induction A as [|A IH]; [reflexivity|].
  replace (2 * S A)%nat with (S (S (2 * A)))%nat by lia.
  cbn [Rsum]. rewrite IH.
  replace (2 * A + 1)%nat with (S (2 * A))%nat by lia.
  lra.
Qed.

(** Split [Rsum g (n+m)] into a head part and a shifted tail part,
    mirroring [walk.v]'s [nsum_seq_split]. *)
Lemma Rsum_seq_split (g : nat -> R) (n m : nat) :
  Rsum g (n + m)%nat = Rsum g n + Rsum (fun c => g (n + c)%nat) m.
Proof.
  induction m as [|m IH].
  - replace (n + 0)%nat with n by lia. simpl. lra.
  - replace (n + S m)%nat with (S (n + m))%nat by lia.
    simpl. rewrite IH. lra.
Qed.

(** Two small linearity helpers, tailored to the [qsum]/[nusum] recursive
    shape used in Section 2-3 below (a per-index [/2]-scaled sum of two, or
    three, real-valued sequences).  Direct induction on [N] rather than a
    rewrite chain through [Rsum_scal]/[Rsum_plus], to sidestep the
    [Rdiv]-vs-[Rmult] argument-order mismatches such a chain runs into. *)
Lemma Rsum_half_plus_half (a b : nat -> R) (N : nat) :
  Rsum (fun i => a i / 2 + b i / 2) N = Rsum a N / 2 + Rsum b N / 2.
Proof. induction N as [|N IH]; simpl; [lra | rewrite IH; lra]. Qed.

Lemma Rsum_half_plus_half3 (a b c : nat -> R) (N : nat) :
  Rsum (fun i => a i / 2 + (b i + c i) / 2) N =
  Rsum a N / 2 + (Rsum b N + Rsum c N) / 2.
Proof. induction N as [|N IH]; simpl; [lra | rewrite IH; lra]. Qed.

(** Bridge to [model.v]'s nat-valued [nsum]/[seq]/[map] machinery, so that
    combinatorial facts proved there (e.g. [sum_nth_seq]) cast directly. *)
Lemma Rsum_INR_nsum_seq (f : nat -> nat) (n : nat) :
  Rsum (fun i => INR (f i)) n = INR (nsum (map f (seq 0 n))).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl Rsum. rewrite IH.
    assert (Hnat : nsum (map f (seq 0 (S n))) = (nsum (map f (seq 0 n)) + f n)%nat).
    { rewrite seq_S. rewrite map_app. rewrite nsum_app.
      replace (0 + n)%nat with n by lia. simpl. lia. }
    rewrite Hnat. rewrite plus_INR. reflexivity.
Qed.

Lemma Rsum_INR_nth_weight_sum (l : list nat) :
  Rsum (fun i => INR (nth i l 0%nat)) (length l) = INR (weight_sum l).
Proof. rewrite Rsum_INR_nsum_seq. f_equal. apply sum_nth_seq. Qed.

(** * 1. Abstract 0/1-indicator sequences: the running "capacity value" and
    "depth-weighted" quantities, and the dyadic Knuth-Yao per-weight bound
    (paper step D).  [qsum bs = Sum_t bs_t/2^t], [nusum bs = Sum_t t*bs_t/2^t]
    (1-indexed from the head of [bs]). *)

Fixpoint qsum (bs : list R) : R :=
  match bs with
  | [] => 0
  | b :: bs' => b / 2 + qsum bs' / 2
  end.

Fixpoint nusum (bs : list R) : R :=
  match bs with
  | [] => 0
  | b :: bs' => b / 2 + (nusum bs' + qsum bs') / 2
  end.

Definition is_bit (b : R) : Prop := b = 0 \/ b = 1.
Definition is_bits (bs : list R) : Prop := Forall is_bit bs.

Lemma qsum_nonneg (bs : list R) : is_bits bs -> 0 <= qsum bs.
Proof.
  induction bs as [|b bs IH]; intros Hbs; simpl; [lra|].
  apply Forall_cons_iff in Hbs as [Hb Hbs'].
  specialize (IH Hbs'). destruct Hb as [-> | ->]; lra.
Qed.

Lemma nusum_nonneg (bs : list R) : is_bits bs -> 0 <= nusum bs.
Proof.
  induction bs as [|b bs IH]; intros Hbs; simpl; [lra|].
  apply Forall_cons_iff in Hbs as [Hb Hbs'].
  pose proof (qsum_nonneg bs Hbs') as Hq.
  specialize (IH Hbs'). destruct Hb as [-> | ->]; lra.
Qed.

Lemma qsum_le1 (bs : list R) : is_bits bs -> qsum bs <= 1.
Proof.
  induction bs as [|b bs IH]; intros Hbs; simpl; [lra|].
  apply Forall_cons_iff in Hbs as [Hb Hbs'].
  specialize (IH Hbs'). destruct Hb as [-> | ->]; lra.
Qed.

Lemma nusum_le2 (bs : list R) : is_bits bs -> nusum bs <= 2.
Proof.
  induction bs as [|b bs IH]; intros Hbs; simpl; [lra|].
  apply Forall_cons_iff in Hbs as [Hb Hbs'].
  pose proof (qsum_le1 bs Hbs') as Hq.
  specialize (IH Hbs'). destruct Hb as [-> | ->]; lra.
Qed.

(** The coarse bound behind the paper's "[Sum (s-1)/2^s <= 1]" fact. *)
Lemma nu_le_1_plus_q (bs : list R) : is_bits bs -> nusum bs <= 1 + qsum bs.
Proof.
  intros Hbs. destruct bs as [|b bs]; simpl; [lra|].
  apply Forall_cons_iff in Hbs as [Hb Hbs'].
  pose proof (nusum_le2 bs Hbs') as Hn. destruct Hb as [-> | ->]; lra.
Qed.

Lemma nusum_zero_of_qsum_zero (bs : list R) :
  is_bits bs -> qsum bs = 0 -> nusum bs = 0.
Proof.
  induction bs as [|b bs IH]; intros Hbs Hq; simpl in *; [reflexivity|].
  apply Forall_cons_iff in Hbs as [Hb Hbs'].
  pose proof (qsum_nonneg bs Hbs') as Hqnn.
  destruct Hb as [-> | ->].
  - assert (Hq' : qsum bs = 0) by lra.
    rewrite (IH Hbs' Hq'). lra.
  - lra.
Qed.

(** [1/a] has a nonnegative dyadic log whenever [0 < a <= 1]. *)
Lemma ln2_pos : 0 < ln 2.
Proof. pose proof ln_lt_2. lra. Qed.

Lemma Rlog2_inv_nonneg (a : R) : 0 < a -> a <= 1 -> 0 <= Rlog 2 (1 / a).
Proof.
  intros Ha0 Ha1.
  assert (Hinv : 1 <= 1 / a).
  { apply (Rmult_le_reg_r a); [exact Ha0|].
    unfold Rdiv. rewrite Rmult_assoc; rewrite Rinv_l; lra. }
  destruct (Rle_lt_or_eq_dec 1 (1 / a) Hinv) as [Hlt | Heq].
  - assert (Hln : 0 < ln (1 / a)) by (rewrite <- ln_1; apply ln_increasing; lra).
    unfold Rlog. apply Rcomplements.Rdiv_le_0_compat; [lra | apply ln2_pos].
  - unfold Rlog. rewrite <- Heq; rewrite ln_1. unfold Rdiv. rewrite Rmult_0_l. lra.
Qed.

(** The "double the argument" additivity of [Rlog 2] used in the [0]-bit
    step of the Knuth-Yao induction below. *)
Lemma Rlog2_double_inv (a : R) : 0 < a -> Rlog 2 (2 / a) = 1 + Rlog 2 (1 / a).
Proof.
  intros Ha0.
  assert (H2a : (2 / a) = 2 * (1 / a)) by (field; lra).
  unfold Rlog. rewrite H2a; rewrite ln_mult; [|lra|apply Rlt_mult_inv_pos; lra].
  pose proof ln2_pos. field. lra.
Qed.

(** The one analytic fact behind the Knuth-Yao per-weight bound: the
    paper's substitution [y := 1/(2x)], reduced to [ln y <= y - 1] (from
    [exp_ineq1_le]/[exp_ln]) and [ln 2 >= 1/2] (Stdlib's [ln_lt_2]). *)
Lemma ln_y_le_2_ln2_y1 (y : R) : 1 <= y -> ln y <= 2 * ln 2 * (y - 1).
Proof.
  intros Hy.
  assert (Hy0 : 0 < y) by lra.
  assert (H1 : ln y <= y - 1).
  { pose proof (exp_ineq1_le (ln y)) as H. rewrite (exp_ln y Hy0) in H. lra. }
  assert (H2 : 1 <= 2 * ln 2) by (pose proof ln_lt_2; lra).
  nra.
Qed.

(** [x * ln(2/x) <= ln 2] for [0 < x < 1/2] (paper's "mushroomlike" term-2
    core inequality, and also the crux of the abstract Knuth-Yao lemma's
    "leading bit" case below). *)
Lemma x_ln2x_bound (x : R) : 0 < x -> x < 1 / 2 -> x * ln (2 / x) <= ln 2.
Proof.
  intros Hx0 Hx1.
  set (y := 1 / (2 * x)).
  assert (Hy1 : 1 <= y).
  { unfold y. apply (Rmult_le_reg_r (2 * x)); [lra|].
    unfold Rdiv. rewrite Rmult_assoc; rewrite Rinv_l; lra. }
  assert (Hxy : x = 1 / (2 * y)).
  { unfold y. field. lra. }
  assert (Hln4 : ln 4 = 2 * ln 2).
  { replace 4 with (2 * 2) by lra. rewrite ln_mult; lra. }
  assert (H2x : 2 / x = 4 * y).
  { unfold y. field. lra. }
  rewrite H2x; rewrite ln_mult; [|lra|lra].
  rewrite Hln4.
  pose proof (ln_y_le_2_ln2_y1 y Hy1) as Hbound.
  assert (Hy0 : 0 < y) by lra.
  (* Goal: x * (ln 4 + ln y) <= ln 2, i.e. x * (2 ln 2 + ln y) <= ln 2. *)
  rewrite Hxy.
  apply (Rmult_le_reg_r (2 * y)); [lra|].
  assert (Hcancel : 1 / (2 * y) * (2 * ln 2 + ln y) * (2 * y) = 2 * ln 2 + ln y)
    by (field; lra).
  rewrite Hcancel. lra.
Qed.

(** The dyadic Knuth-Yao per-weight bound (paper step D), over an abstract
    0/1-indicator sequence.  Structural induction on [bs]: the [0]-bit case
    is an EXACT identity from the induction hypothesis plus
    [Rlog2_double_inv] (no slack); the [1]-bit case uses [nu_le_1_plus_q]
    plus nonnegativity of the log term ([Rlog2_inv_nonneg]) -- neither case
    needs to track "the position of the leading bit" explicitly, which is
    the one place this proof deviates from the paper's literal
    exposition. *)
Lemma bits_KY_bound (bs : list R) :
  is_bits bs -> nusum bs <= qsum bs * Rlog 2 (1 / qsum bs) + 2 * qsum bs.
Proof.
  induction bs as [|b bs IH]; intros Hbs; simpl.
  - lra.
  - apply Forall_cons_iff in Hbs as [Hb Hbs'].
    pose proof (qsum_nonneg bs Hbs') as Hqnn.
    pose proof (qsum_le1 bs Hbs') as Hqle1.
    specialize (IH Hbs').
    destruct Hb as [-> | ->].
    + (* bit 0 *)
      destruct (Req_dec (qsum bs) 0) as [Hq0 | Hq0].
      * rewrite Hq0.
        rewrite (nusum_zero_of_qsum_zero bs Hbs' Hq0).
        lra.
      * assert (Hqpos : 0 < qsum bs) by lra.
        assert (Hrw : 1 / (qsum bs / 2) = 2 / qsum bs) by (field; lra).
        replace (0 / 2 + qsum bs / 2) with (qsum bs / 2) by lra.
        rewrite Hrw. rewrite (Rlog2_double_inv (qsum bs) Hqpos).
        lra.
    + (* bit 1 *)
      pose proof (nu_le_1_plus_q bs Hbs') as Hnu1.
      set (q := 1 / 2 + qsum bs / 2).
      assert (Hq0 : 0 < q) by (unfold q; lra).
      assert (Hq1 : q <= 1) by (unfold q; lra).
      pose proof (Rlog2_inv_nonneg q Hq0 Hq1) as Hlognn.
      assert (Hqpos : 0 <= q * Rlog 2 (1 / q)) by (apply Rmult_le_pos; lra).
      assert (Hqeq : 2 * q = 1 + qsum bs) by (unfold q; lra).
      lra.
Qed.

(** * 2. Row occupancy ([occ]/[msum], from [model.v]) as a 0/1-indicator
    sequence: [occ]-values are bits, [qsum] of the per-label occupancy
    sequence recovers the label's weight mod the denominator (dividing
    [msum]'s own recursive equation through by [2 ^ length rows], the same
    trick [entropy_cost.v]'s [reject_mass_cons] uses), and the
    row-occupancy sum [Sum_i occ i row = length row] (a standard
    double-counting fact over [seq 0 N], proved via [NoDup_incl_length]
    both ways). *)

Lemma ind_is_bit (P : Prop) (d : {P} + {~ P}) : ind P d = 0%nat \/ ind P d = 1%nat.
Proof. unfold ind. destruct d; [right | left]; reflexivity. Qed.

Lemma occ_is_bit (i : nat) (row : list nat) : is_bit (INR (occ i row)).
Proof.
  unfold occ, is_bit.
  destruct (ind_is_bit (In i row) (in_dec Nat.eq_dec i row)) as [H0 | H1].
  - left. rewrite H0. reflexivity.
  - right. rewrite H1. reflexivity.
Qed.

Lemma occbits_is_bits (rows : list (list nat)) (i : nat) :
  is_bits (map (fun row => INR (occ i row)) rows).
Proof.
  induction rows as [|row rest IH]; simpl; constructor; [apply occ_is_bit | apply IH].
Qed.

(** NOTE: [filter]/[in_dec] are qualified as [List.filter]/[List.in_dec]
    throughout this lemma and the next: the ambient Iris/std++ imports
    shadow the unqualified names with a [Decision]-typeclass-based [filter],
    which does not accept a plain [bool]-valued predicate. *)
Lemma ind_sum_eq_filter_length {A : Type} (P : A -> Prop)
    (d : forall x, {P x} + {~ P x}) (l : list A) :
  nsum (map (fun x => ind (P x) (d x)) l) =
  length (List.filter (fun x => if d x then true else false) l).
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (d a) as [Hp | Hp]; simpl; lia.
Qed.

Lemma occ_sum_row (row : list nat) (N : nat) :
  List.NoDup row -> (forall x, In x row -> (x < N)%nat) ->
  nsum (map (fun i => occ i row) (seq 0 N)) = length row.
Proof.
  intros Hnd Hbound.
  unfold occ.
  rewrite (ind_sum_eq_filter_length (fun i => In i row)
    (fun i => in_dec Nat.eq_dec i row) (seq 0 N)).
  set (filt := List.filter (fun i => if in_dec Nat.eq_dec i row then true else false) (seq 0 N)).
  assert (Hincl1 : incl row filt).
  { intros x Hx. unfold filt. apply filter_In. split.
    - apply in_seq. split; [lia|]. simpl. apply Hbound. exact Hx.
    - destruct (in_dec Nat.eq_dec x row) as [_|Hno]; [reflexivity|contradiction]. }
  assert (Hincl2 : incl filt row).
  { intros x Hx. unfold filt in Hx. apply filter_In in Hx as [_ Hx'].
    destruct (in_dec Nat.eq_dec x row) as [Hyes|_]; [exact Hyes|discriminate]. }
  assert (Hnd_filt : List.NoDup filt).
  { unfold filt. apply List.NoDup_filter, seq_NoDup. }
  pose proof (NoDup_incl_length Hnd Hincl1) as Hle1.
  pose proof (NoDup_incl_length Hnd_filt Hincl2) as Hle2.
  lia.
Qed.

Lemma Rsum_INR_occ_row (row : list nat) (N : nat) :
  List.NoDup row -> (forall x, In x row -> (x < N)%nat) ->
  Rsum (fun i => INR (occ i row)) N = INR (length row).
Proof. intros. rewrite Rsum_INR_nsum_seq. f_equal. apply occ_sum_row; assumption. Qed.

Lemma qsum_occ_eq_msum (rows : list (list nat)) (i : nat) :
  qsum (map (fun row => INR (occ i row)) rows) =
  INR (msum i rows) / 2 ^ (length rows).
Proof.
  induction rows as [|row rest IH]; simpl.
  - lra.
  - rewrite IH.
    rewrite plus_INR. rewrite mult_INR. rewrite pow_INR. rewrite INR_two.
    assert (Hpow : (0:R) < 2 ^ length rest) by (apply pow_lt; lra).
    field. lra.
Qed.

(** * 3. Rows-to-bits: exchanging the order of summation between rows and
    labels (paper step C).  [nusum]/[qsum] of the row-length sequence
    decompose as the sum, over labels [i < N], of [nusum]/[qsum] of the
    per-label occupancy sequence -- a finite-Fubini argument, proved by
    induction on [rows] jointly for [qsum] and [nusum] (the [nusum] case
    needs the [qsum] case of the smaller list in its own recursive
    equation). *)
Lemma nusum_qsum_row_decomp (rows : list (list nat)) (N : nat) :
  (forall row, In row rows -> List.NoDup row) ->
  (forall row, In row rows -> forall x, In x row -> (x < N)%nat) ->
  qsum (map (fun row => INR (length row)) rows) =
    Rsum (fun i => qsum (map (fun row => INR (occ i row)) rows)) N /\
  nusum (map (fun row => INR (length row)) rows) =
    Rsum (fun i => nusum (map (fun row => INR (occ i row)) rows)) N.
Proof.
  induction rows as [|row rest IH]; intros Hnd Hbnd.
  - simpl. split; rewrite Rsum_const0; reflexivity.
  - assert (Hnd_row : List.NoDup row) by (apply Hnd; left; reflexivity).
    assert (Hbnd_row : forall x, In x row -> (x < N)%nat)
      by (intros x Hx; apply (Hbnd row); [left; reflexivity | exact Hx]).
    assert (Hnd_rest : forall row0, In row0 rest -> List.NoDup row0)
      by (intros r0 Hr0; apply Hnd; right; exact Hr0).
    assert (Hbnd_rest : forall row0, In row0 rest -> forall x, In x row0 -> (x < N)%nat)
      by (intros r0 Hr0 x Hx; apply (Hbnd r0); [right; exact Hr0 | exact Hx]).
    destruct (IH Hnd_rest Hbnd_rest) as [IHq IHn].
    pose proof (Rsum_INR_occ_row row N Hnd_row Hbnd_row) as Hrow.
    split.
    + simpl qsum. rewrite IHq; rewrite <- Hrow; rewrite <- Rsum_half_plus_half.
      apply Rsum_ext. intros i _. reflexivity.
    + simpl nusum. rewrite IHn; rewrite IHq; rewrite <- Hrow; rewrite <- Rsum_half_plus_half3.
      apply Rsum_ext. intros i _. reflexivity.
Qed.

Lemma qsum_row_decomp (rows : list (list nat)) (N : nat) :
  (forall row, In row rows -> List.NoDup row) ->
  (forall row, In row rows -> forall x, In x row -> (x < N)%nat) ->
  qsum (map (fun row => INR (length row)) rows) =
    Rsum (fun i => qsum (map (fun row => INR (occ i row)) rows)) N.
Proof. intros. apply (nusum_qsum_row_decomp rows N); assumption. Qed.

Lemma nusum_row_decomp (rows : list (list nat)) (N : nat) :
  (forall row, In row rows -> List.NoDup row) ->
  (forall row, In row rows -> forall x, In x row -> (x < N)%nat) ->
  nusum (map (fun row => INR (length row)) rows) =
    Rsum (fun i => nusum (map (fun row => INR (occ i row)) rows)) N.
Proof. intros. apply (nusum_qsum_row_decomp rows N); assumption. Qed.

(** * 4. The capacity-driven closed form for [step_mass] (paper steps A+B):
    aggregating [step_mass rows -] over the [A] live counters entering a
    row (step A) and telescoping down to the leaf ("depth-weighted row
    length") form (step B), exactly mirroring the two-lemma shape of
    [walk.v]'s [walk_count] (itself built from [nsum_seq_pair]/
    [nsum_seq_split]) but for the real-valued, "+1 per step" [step_mass]
    recursion instead of [cnt]. *)

(** Step (A): one row's worth of the aggregate identity. *)
Lemma step_mass_Rsum_step (row : list nat) (rest : list (list nat)) (A : nat) :
  (length row <= 2 * A)%nat ->
  Rsum (fun c => step_mass (row :: rest) c) A =
    INR A + (1 / 2) * Rsum (fun c => step_mass rest c) (2 * A - length row)%nat.
Proof.
  intros Hh.
  set (g := fun v => if (v <? length row)%nat then 0 else step_mass rest (v - length row)%nat).
  assert (Hstep : forall c,
    step_mass (row :: rest) c = 1 + (1/2) * (g (2*c)%nat + g (2*c+1)%nat)).
  { intros c. simpl. unfold g. lra. }
  assert (Heq : Rsum (fun c => step_mass (row :: rest) c) A =
                Rsum (fun _ : nat => 1) A +
                (1/2) * Rsum (fun c => g (2*c)%nat + g (2*c+1)%nat) A).
  { rewrite <- Rsum_scal; rewrite <- Rsum_plus. apply Rsum_ext. intros c _. rewrite Hstep. lra. }
  rewrite Heq; rewrite Rsum_const1; rewrite Rsum_seq_pair.
  pose proof (Rsum_seq_split g (length row) (2 * A - length row)%nat) as Hsplit.
  replace (length row + (2 * A - length row))%nat with (2 * A)%nat in Hsplit by lia.
  rewrite Hsplit.
  assert (Hzero : Rsum g (length row) = 0).
  { rewrite <- (Rsum_const0 (length row)). apply Rsum_ext. intros v Hv. unfold g.
    assert (Hlt : (v <? length row)%nat = true) by (apply Nat.ltb_lt; lia). rewrite Hlt.
    reflexivity. }
  assert (Htail : Rsum (fun c => g (length row + c)%nat) (2 * A - length row)%nat =
                   Rsum (fun c => step_mass rest c) (2 * A - length row)%nat).
  { apply Rsum_ext. intros c _. unfold g.
    assert (Hge : (length row + c <? length row)%nat = false) by (apply Nat.ltb_ge; lia).
    rewrite Hge. f_equal. lia. }
  rewrite Hzero; rewrite Htail. lra.
Qed.

(** Step (B), phrased as "potential conservation": the total capacity
    entering the table, discounted by [2^-position], equals the initial
    capacity minus the (correspondingly discounted) final leftover
    capacity. *)
Lemma capacity_qsum_conservation (rows : list (list nat)) (A : nat) :
  capacity_ok rows A ->
  qsum (map (fun row => INR (length row)) rows) =
    INR A - INR (cap_final rows A) / 2 ^ (length rows).
Proof.
  induction rows as [|row rest IH] in A |- *; intros Hcap.
  - simpl. lra.
  - destruct Hcap as [Hh Hcap'].
    simpl qsum. rewrite (IH (2 * A - length row)%nat Hcap').
    change (cap_final (row :: rest) A) with (cap_final rest (2 * A - length row)%nat).
    change (length (row :: rest)) with (S (length rest)).
    assert (Hpow2 : (2:R) ^ (S (length rest)) = 2 * 2 ^ (length rest)) by reflexivity.
    rewrite Hpow2.
    assert (HA' : INR (2 * A - length row)%nat = 2 * INR A - INR (length row)).
    { rewrite minus_INR; [|lia]. rewrite mult_INR. simpl. lra. }
    rewrite HA'.
    assert (Hpow : (0:R) < 2 ^ length rest) by (apply pow_lt; lra).
    field. lra.
Qed.

(** The combined (A)+(B) closed form. *)
Lemma step_mass_leaf_form (rows : list (list nat)) (A : nat) :
  capacity_ok rows A ->
  Rsum (fun c => step_mass rows c) A =
    nusum (map (fun row => INR (length row)) rows) +
    INR (length rows) * INR (cap_final rows A) / 2 ^ (length rows).
Proof.
  induction rows as [|row rest IH] in A |- *; intros Hcap.
  - simpl. rewrite Rsum_const0. lra.
  - destruct Hcap as [Hh Hcap'].
    rewrite (step_mass_Rsum_step row rest A Hh).
    rewrite (IH (2 * A - length row)%nat Hcap').
    change (cap_final (row :: rest) A) with (cap_final rest (2 * A - length row)%nat).
    change (length (row :: rest)) with (S (length rest)).
    simpl nusum.
    pose proof (capacity_qsum_conservation rest (2 * A - length row)%nat Hcap') as Hcons.
    assert (HA' : INR (2 * A - length row)%nat = 2 * INR A - INR (length row)).
    { rewrite minus_INR; [|lia]. rewrite mult_INR. simpl. lra. }
    rewrite HA' in Hcons.
    rewrite Hcons.
    assert (Hpow : (0:R) < 2 ^ length rest) by (apply pow_lt; lra).
    assert (HSlen : INR (S (length rest)) = INR (length rest) + 1) by (rewrite S_INR; lra).
    rewrite HSlen.
    assert (Hpow2 : (2:R) ^ (S (length rest)) = 2 * 2 ^ (length rest)) by reflexivity.
    rewrite Hpow2.
    field. lra.
Qed.

(** * 5. Specializing Sections 3-4 to the real DDG table at [A := 1]: the
    root identity [step_mass (ddg_table ws) 0 = Sum_i nu(e_i)]. *)
Lemma step_mass_ddg_eq_label_sum (ws : list nat) :
  admissible ws -> nondegenerate ws ->
  step_mass (ddg_table ws) 0 =
    Rsum (fun i => nusum (map (fun row => INR (occ i row)) (ddg_table ws)))
      (length (extended_weights ws)).
Proof.
  intros Hadm Hnd.
  pose proof (ddg_table_capacity ws Hadm) as Hcap.
  pose proof (ddg_table_cap_final ws Hadm Hnd) as Hfin.
  pose proof (step_mass_leaf_form (ddg_table ws) 1 Hcap) as Hleaf.
  rewrite Hfin in Hleaf.
  assert (H1 : Rsum (fun c => step_mass (ddg_table ws) c) 1 = step_mass (ddg_table ws) 0)
    by (simpl; lra).
  rewrite H1 in Hleaf.
  rewrite INR_0 in Hleaf.
  replace (INR (length (ddg_table ws)) * 0 / 2 ^ length (ddg_table ws)) with 0 in Hleaf by lra.
  rewrite Rplus_0_r in Hleaf.
  rewrite Hleaf.
  apply nusum_row_decomp.
  - intros row Hrow. eapply ddg_table_rows_nodup. exact Hrow.
  - intros row Hrow x Hx. eapply ddg_table_index_bound; eauto.
Qed.

(** * 6. Shannon entropy (the theorem's target quantity, [H(p)]) and the
    extended-weight entropy [entropy_ext] (the paper's [H(q)]), both built
    from a shared per-weight term. *)

Definition shannon_weight_term (D w : nat) : R :=
  if (w =? 0)%nat then 0 else (INR w / INR D) * Rlog 2 (INR D / INR w).

Definition shannon_entropy (ws : list nat) : R :=
  Rsum (fun i => shannon_weight_term (weight_sum ws) (nth i ws 0%nat)) (length ws).

Definition entropy_ext (ws : list nat) : R :=
  Rsum (fun i => shannon_weight_term (denominator ws) (nth i (extended_weights ws) 0%nat))
    (length (extended_weights ws)).

Lemma shannon_weight_term_eq_qlog (D w : nat) :
  (0 < D)%nat ->
  shannon_weight_term D w = (INR w / INR D) * Rlog 2 (1 / (INR w / INR D)).
Proof.
  intros HD.
  unfold shannon_weight_term.
  destruct (Nat.eqb_spec w 0) as [-> | Hw].
  - simpl. lra.
  - assert (HwR : ~ (INR w = 0)) by (apply not_0_INR; exact Hw).
    assert (HDR : ~ (INR D = 0)) by (apply not_0_INR; lia).
    assert (Hrw : 1 / (INR w / INR D) = INR D / INR w) by (field; split; assumption).
    rewrite Hrw. reflexivity.
Qed.

(** Splitting off the rejection term of [entropy_ext] (reused by both the
    [m = D] and [m < D] cases below). *)
Lemma entropy_ext_split (ws : list nat) :
  entropy_ext ws =
    Rsum (fun i => shannon_weight_term (denominator ws) (nth i ws 0%nat)) (length ws) +
    shannon_weight_term (denominator ws) (rejection_weight ws).
Proof.
  unfold entropy_ext.
  assert (Hlen : length (extended_weights ws) = S (length ws)).
  { unfold extended_weights. rewrite length_app. simpl. lia. }
  rewrite Hlen. simpl Rsum.
  assert (Hnth : forall i, (i < length ws)%nat ->
    nth i (extended_weights ws) 0%nat = nth i ws 0%nat).
  { intros i Hi. unfold extended_weights. apply app_nth1. exact Hi. }
  assert (Hlast : nth (length ws) (extended_weights ws) 0%nat = rejection_weight ws).
  { unfold extended_weights. apply nth_middle. }
  rewrite Hlast. f_equal. apply Rsum_ext. intros i Hi. rewrite (Hnth i Hi). reflexivity.
Qed.

(** * 7. The per-label Knuth-Yao bound, instantiated at the DDG table, and
    its sum over labels (paper steps D+E): [step_mass (ddg_table ws) 0 <=
    entropy_ext ws + 2]. *)

Lemma label_KY_bound (ws : list nat) (i : nat) :
  nondegenerate ws -> (i < length (extended_weights ws))%nat ->
  nusum (map (fun row => INR (occ i row)) (ddg_table ws)) <=
    shannon_weight_term (denominator ws) (nth i (extended_weights ws) 0%nat) +
    2 * (INR (nth i (extended_weights ws) 0%nat) / INR (denominator ws)).
Proof.
  intros Hnd Hi.
  pose proof (Hnd i Hi) as Hlt.
  pose proof (occbits_is_bits (ddg_table ws) i) as Hbits.
  pose proof (bits_KY_bound (map (fun row => INR (occ i row)) (ddg_table ws)) Hbits) as HKY.
  pose proof (qsum_occ_eq_msum (ddg_table ws) i) as Hqm.
  rewrite (ddg_table_depth ws) in Hqm.
  assert (Hocc : msum i (ddg_table ws) = nth i (extended_weights ws) 0%nat).
  { apply ddg_table_occupancy_exact; [exact Hi | exact Hlt]. }
  rewrite Hocc in Hqm.
  assert (Hpow : INR (denominator ws) = (2:R) ^ dyadic_width ws).
  { unfold denominator. rewrite pow_INR; rewrite INR_two. reflexivity. }
  rewrite <- Hpow in Hqm.
  rewrite Hqm in HKY.
  rewrite (shannon_weight_term_eq_qlog (denominator ws) (nth i (extended_weights ws) 0%nat)
    (denominator_pos ws)).
  lra.
Qed.

Lemma step_mass_le_entropy_ext_plus2 (ws : list nat) :
  admissible ws -> nondegenerate ws ->
  step_mass (ddg_table ws) 0 <= entropy_ext ws + 2.
Proof.
  intros Hadm Hnd.
  rewrite (step_mass_ddg_eq_label_sum ws Hadm Hnd).
  unfold entropy_ext.
  eapply Rle_trans.
  - apply Rsum_le. intros i Hi. apply label_KY_bound; [exact Hnd | exact Hi].
  - rewrite Rsum_plus.
    assert (Hscal :
      Rsum (fun i => 2 * (INR (nth i (extended_weights ws) 0%nat) / INR (denominator ws)))
        (length (extended_weights ws)) =
      2 * (Rsum (fun i => INR (nth i (extended_weights ws) 0%nat))
             (length (extended_weights ws)) / INR (denominator ws))).
    { rewrite Rsum_scal. f_equal. rewrite Rsum_div_r. reflexivity. }
    rewrite Hscal; rewrite (Rsum_INR_nth_weight_sum (extended_weights ws)); rewrite (extended_weight_sum ws Hadm).
    assert (HDpos : ~ (INR (denominator ws) = 0))
      by (apply not_0_INR; pose proof (denominator_pos ws); lia).
    assert (Hone : INR (denominator ws) / INR (denominator ws) = 1) by (field; exact HDpos).
    lra.
Qed.

(** * 8. Case (F): the paper's [m = D] (exact) case. *)

Lemma entropy_ext_eq_shannon_of_exact (ws : list nat) :
  weight_sum ws = denominator ws ->
  entropy_ext ws = shannon_entropy ws.
Proof.
  intros Heq.
  rewrite entropy_ext_split.
  assert (Hr0 : rejection_weight ws = 0%nat) by (unfold rejection_weight; lia).
  assert (Hzero : shannon_weight_term (denominator ws) (rejection_weight ws) = 0).
  { rewrite Hr0. reflexivity. }
  rewrite Hzero.
  unfold shannon_entropy.
  rewrite <- Heq.
  lra.
Qed.

Lemma flip_cost_entropy_bound_exact (ws : list nat) :
  admissible ws -> nondegenerate ws -> weight_sum ws = denominator ws ->
  flip_cost ws < shannon_entropy ws + 6.
Proof.
  intros Hadm Hnd Heq.
  pose proof (reject_mass_ddg_table ws Hadm Hnd) as Hrm.
  assert (Hr0 : rejection_weight ws = 0%nat) by (unfold rejection_weight; lia).
  rewrite Hr0 in Hrm. rewrite INR_0 in Hrm.
  assert (Hrm0 : reject_mass (ddg_table ws) 0 (length ws) = 0) by (rewrite Hrm; lra).
  unfold flip_cost. rewrite Hrm0.
  replace (1 - 0) with 1 by lra. rewrite Rdiv_1_r.
  pose proof (step_mass_le_entropy_ext_plus2 ws Hadm Hnd) as Hle.
  rewrite (entropy_ext_eq_shannon_of_exact ws Heq) in Hle.
  lra.
Qed.

(** * 9. Case (G): the paper's [m < D] (reject) case: the "mushroomlike"
    algebraic identity and its three term bounds. *)

Lemma log_diff_const (D m w : R) : 0 < D -> 0 < m -> 0 < w ->
  Rlog 2 (D / w) - Rlog 2 (m / w) = Rlog 2 (D / m).
Proof.
  intros HD Hm Hw.
  pose proof ln2_pos as Hln2.
  unfold Rlog.
  assert (H1 : ln (D / w) = ln D - ln w).
  { unfold Rdiv. rewrite ln_mult; [|lra|apply Rinv_0_lt_compat; lra]. rewrite ln_Rinv; lra. }
  assert (H2 : ln (m / w) = ln m - ln w).
  { unfold Rdiv. rewrite ln_mult; [|lra|apply Rinv_0_lt_compat; lra]. rewrite ln_Rinv; lra. }
  assert (H3 : ln (D / m) = ln D - ln m).
  { unfold Rdiv. rewrite ln_mult; [|lra|apply Rinv_0_lt_compat; lra]. rewrite ln_Rinv; lra. }
  rewrite H1; rewrite H2; rewrite H3. field. lra.
Qed.

Lemma per_term_identity (D m w : nat) : (0 < D)%nat -> (0 < m)%nat -> (0 < w)%nat ->
  shannon_weight_term D w * (INR D / INR m) - shannon_weight_term m w =
    (INR w / INR m) * Rlog 2 (INR D / INR m).
Proof.
  intros HD Hm Hw.
  assert (HDR : 0 < INR D) by (apply lt_0_INR; lia).
  assert (HmR : 0 < INR m) by (apply lt_0_INR; lia).
  assert (HwR : 0 < INR w) by (apply lt_0_INR; lia).
  unfold shannon_weight_term.
  assert (Hw0 : (w =? 0)%nat = false) by (apply Nat.eqb_neq; lia).
  rewrite Hw0.
  assert (Hcancel : INR w / INR D * Rlog 2 (INR D / INR w) * (INR D / INR m) =
                     INR w / INR m * Rlog 2 (INR D / INR w)) by (field; lra).
  rewrite Hcancel.
  rewrite <- (log_diff_const (INR D) (INR m) (INR w) HDR HmR HwR).
  ring.
Qed.

Lemma flip_cost_minus_shannon_eq (ws : list nat) :
  admissible ws -> (weight_sum ws < denominator ws)%nat ->
  entropy_ext ws * (INR (denominator ws) / INR (weight_sum ws)) - shannon_entropy ws =
    Rlog 2 (INR (denominator ws) / INR (weight_sum ws)) +
    (INR (rejection_weight ws) / INR (weight_sum ws)) *
      Rlog 2 (INR (denominator ws) / INR (rejection_weight ws)).
Proof.
  intros Hadm Hlt.
  pose proof (admissible_weight_sum_pos ws Hadm) as Hmpos.
  pose proof (denominator_pos ws) as HDpos.
  assert (Hr0 : (0 < rejection_weight ws)%nat) by (unfold rejection_weight; lia).
  assert (Hallpos : forall i, (i < length ws)%nat -> (0 < nth i ws 0%nat)%nat).
  { intros i Hi. destruct Hadm as [_ Hforall]. eapply Forall_nth in Hforall; eauto. }
  rewrite entropy_ext_split; rewrite Rmult_plus_distr_r.
  assert (Hmain :
    Rsum (fun i => shannon_weight_term (denominator ws) (nth i ws 0%nat)) (length ws) *
      (INR (denominator ws) / INR (weight_sum ws)) =
    shannon_entropy ws + Rlog 2 (INR (denominator ws) / INR (weight_sum ws))).
  { unfold shannon_entropy.
    assert (Hpt :
      Rsum (fun i => shannon_weight_term (denominator ws) (nth i ws 0%nat)) (length ws) *
        (INR (denominator ws) / INR (weight_sum ws)) =
      Rsum (fun i => shannon_weight_term (weight_sum ws) (nth i ws 0%nat) +
                     INR (nth i ws 0%nat) / INR (weight_sum ws) *
                       Rlog 2 (INR (denominator ws) / INR (weight_sum ws)))
        (length ws)).
    { rewrite <- Rsum_scal_r.
      apply Rsum_ext. intros i Hi.
      pose proof (per_term_identity (denominator ws) (weight_sum ws) (nth i ws 0%nat)
                    HDpos Hmpos (Hallpos i Hi)) as Hi'.
      lra. }
    rewrite Hpt. rewrite Rsum_plus. f_equal.
    rewrite Rsum_div_mul_r.
    rewrite (Rsum_INR_nth_weight_sum ws).
    assert (HmR : ~ (INR (weight_sum ws) = 0)) by (apply not_0_INR; lia).
    assert (Hone : INR (weight_sum ws) / INR (weight_sum ws) = 1) by (field; exact HmR).
    rewrite Hone. lra. }
  rewrite Hmain.
  assert (Hrej :
    shannon_weight_term (denominator ws) (rejection_weight ws) *
      (INR (denominator ws) / INR (weight_sum ws)) =
    INR (rejection_weight ws) / INR (weight_sum ws) *
      Rlog 2 (INR (denominator ws) / INR (rejection_weight ws))).
  { unfold shannon_weight_term.
    assert (Hr0' : (rejection_weight ws =? 0)%nat = false) by (apply Nat.eqb_neq; lia).
    rewrite Hr0'.
    assert (HrR : 0 < INR (rejection_weight ws)) by (apply lt_0_INR; exact Hr0).
    assert (HDR : 0 < INR (denominator ws)) by (apply lt_0_INR; exact HDpos).
    field. split; apply not_0_INR; lia. }
  rewrite Hrej. lra.
Qed.

Lemma term1_bound (D m : R) : 0 < m -> D < 2 * m -> 0 < D -> Rlog 2 (D / m) < 1.
Proof.
  intros Hm HD2 HD.
  assert (HDm : D / m < 2)
    by (apply (Rmult_lt_reg_r m); [lra|]; unfold Rdiv; rewrite Rmult_assoc; rewrite Rinv_l; lra).
  assert (HDm0 : 0 < D / m) by (apply Rlt_mult_inv_pos; lra).
  unfold Rlog.
  assert (Hln : ln (D / m) < ln 2) by (apply ln_increasing; lra).
  pose proof ln2_pos.
  apply (Rmult_lt_reg_r (ln 2)); [lra|].
  unfold Rdiv. rewrite Rmult_assoc; rewrite Rinv_l; lra.
Qed.

Lemma term2_bound (D m r : R) : 0 < r -> r < D / 2 -> D = m + r ->
  (r / m) * Rlog 2 (D / r) <= 1.
Proof.
  intros Hr0 HrD Hdecomp.
  assert (HD0 : 0 < D) by lra.
  assert (Hm0 : 0 < m) by lra.
  set (x := r / D).
  assert (Hx0 : 0 < x) by (unfold x; apply Rlt_mult_inv_pos; lra).
  assert (Hx1 : x < 1 / 2)
    by (unfold x; apply (Rmult_lt_reg_r D); [lra|];
        unfold Rdiv; rewrite Rmult_assoc; rewrite Rinv_l; lra).
  pose proof (x_ln2x_bound x Hx0 Hx1) as Hxln.
  assert (Hrx : r = x * D) by (unfold x; field; lra).
  assert (Hmx : m = (1 - x) * D) by nra.
  assert (Hr_m : r / m = x / (1 - x)) by (rewrite Hrx; rewrite Hmx; field; lra).
  assert (HDr : D / r = 1 / x) by (rewrite Hrx; field; lra).
  rewrite Hr_m; rewrite HDr.
  assert (Hln2x : ln (2 / x) = ln 2 + ln (1 / x)).
  { replace (2 / x) with (2 * (1 / x)) by (field; lra).
    apply ln_mult; [lra | apply Rlt_mult_inv_pos; lra]. }
  pose proof ln2_pos as Hln2.
  unfold Rlog.
  apply (Rmult_le_reg_r (ln 2 * (1 - x))); [nra|].
  assert (Hgoal_eq :
    x / (1 - x) * (ln (1 / x) / ln 2) * (ln 2 * (1 - x)) = x * ln (1 / x)).
  { field. split; lra. }
  rewrite Rmult_1_l; rewrite Hgoal_eq. nra.
Qed.

Lemma term3_bound (D m t : R) : 0 < D -> 0 < m -> D < 2 * m -> t <= 2 -> (D / m) * t < 4.
Proof.
  intros HD Hm HD2 Ht.
  assert (HDm0 : 0 < D / m) by (apply Rlt_mult_inv_pos; lra).
  assert (HDm2 : D / m < 2)
    by (apply (Rmult_lt_reg_r m); [lra|]; unfold Rdiv; rewrite Rmult_assoc; rewrite Rinv_l; lra).
  destruct (Rle_dec t 0) as [Ht0 | Ht0].
  - nra.
  - assert (Ht0' : 0 < t) by lra. nra.
Qed.

Lemma flip_cost_entropy_bound_reject (ws : list nat) :
  admissible ws -> nondegenerate ws -> (weight_sum ws < denominator ws)%nat ->
  flip_cost ws < shannon_entropy ws + 6.
Proof.
  intros Hadm Hnd Hlt.
  pose proof (admissible_weight_sum_pos ws Hadm) as Hmpos.
  pose proof (denominator_pos ws) as HDpos.
  pose proof (denominator_bounds ws Hadm) as [_ HD2m].
  assert (Hr0 : (0 < rejection_weight ws)%nat) by (unfold rejection_weight; lia).
  pose proof (reject_mass_ddg_table ws Hadm Hnd) as Hrm.
  set (D := INR (denominator ws)). set (m := INR (weight_sum ws)).
  set (r := INR (rejection_weight ws)).
  assert (HD0 : 0 < D) by (unfold D; apply lt_0_INR; exact HDpos).
  assert (Hm0 : 0 < m) by (unfold m; apply lt_0_INR; exact Hmpos).
  assert (Hr0' : 0 < r) by (unfold r; apply lt_0_INR; exact Hr0).
  assert (HD2m' : D < 2 * m).
  { unfold D, m.
    pose proof (lt_INR (denominator ws) (2 * weight_sum ws) HD2m) as H.
    rewrite mult_INR in H. rewrite INR_two in H. exact H. }
  assert (Hdecomp : D = m + r).
  { unfold D, m, r. rewrite <- plus_INR. f_equal.
    pose proof (rejection_weight_nonnegative ws Hadm) as Hsum. lia. }
  assert (Hrmeq : reject_mass (ddg_table ws) 0 (length ws) = r / D) by (unfold r, D; exact Hrm).
  assert (H1r : 1 - reject_mass (ddg_table ws) 0 (length ws) = m / D).
  { rewrite Hrmeq. rewrite Hdecomp. field. lra. }
  unfold flip_cost. rewrite H1r.
  assert (HmD0 : ~ (m / D = 0)).
  { intros Hcontra. assert (Hpos : 0 < m / D) by (apply Rlt_mult_inv_pos; lra). lra. }
  assert (Hflip : step_mass (ddg_table ws) 0 / (m / D) = step_mass (ddg_table ws) 0 * (D / m)).
  { field. lra. }
  rewrite Hflip.
  pose proof (step_mass_le_entropy_ext_plus2 ws Hadm Hnd) as Hle.
  set (S := step_mass (ddg_table ws) 0) in *.
  set (Hqv := entropy_ext ws) in *.
  set (t := S - Hqv).
  assert (HSt : S = Hqv + t) by (unfold t; lra).
  assert (Ht2 : t <= 2) by (unfold t; lra).
  pose proof (flip_cost_minus_shannon_eq ws Hadm Hlt) as Hident.
  fold D m r in Hident.
  assert (Hterm1 : Rlog 2 (D / m) < 1) by (apply term1_bound; lra).
  assert (Hterm2 : (r / m) * Rlog 2 (D / r) <= 1) by (apply term2_bound; lra).
  assert (Hterm3 : (D / m) * t < 4) by (apply term3_bound; lra).
  rewrite HSt.
  replace ((Hqv + t) * (D / m)) with (Hqv * (D / m) + (D / m) * t) by ring.
  assert (Hgoal : Hqv * (D / m) - shannon_entropy ws =
    Rlog 2 (D / m) + (r / m) * Rlog 2 (D / r)) by (unfold Hqv; exact Hident).
  lra.
Qed.

(** * 10. The main theorem and its ERT entry-point corollaries. *)

Theorem flip_cost_entropy_bound (ws : list nat) :
  admissible ws -> nondegenerate ws -> flip_cost ws < shannon_entropy ws + 6.
Proof.
  intros Hadm Hnd.
  pose proof (denominator_bounds ws Hadm) as [Hle _].
  destruct (Nat.eq_dec (weight_sum ws) (denominator ws)) as [Heq | Hneq].
  - apply flip_cost_entropy_bound_exact; assumption.
  - assert (Hlt : (weight_sum ws < denominator ws)%nat) by lia.
    apply flip_cost_entropy_bound_reject; assumption.
Qed.

Corollary fldr_ERT_entropy_bound Σ `{!tachisGpreS Σ} (ws : list nat) (σ : state) (k : nat) :
  admissible ws -> nondegenerate ws ->
  ERT (costfun := CostEntropy_2) k (fldr (inject ws), σ) < shannon_entropy ws + 6.
Proof.
  intros Hadm Hnd.
  eapply Rle_lt_trans;
    [apply (fldr_ERT_bound Σ ws σ k Hadm Hnd) | apply flip_cost_entropy_bound; assumption].
Qed.

Corollary fldr_ERT_entropy_bound_lim Σ `{!tachisGpreS Σ} (ws : list nat) (σ : state) :
  admissible ws -> nondegenerate ws ->
  lim_ERT (costfun := CostEntropy_2) (fldr (inject ws), σ) < shannon_entropy ws + 6.
Proof.
  intros Hadm Hnd.
  eapply Rle_lt_trans;
    [apply (fldr_ERT_bound_lim Σ ws σ Hadm Hnd) | apply flip_cost_entropy_bound; assumption].
Qed.

Corollary fldr_sample_ERT_entropy_bound Σ `{!tachisGpreS Σ} (ws : list nat) (σ : state) (k : nat) :
  admissible ws -> nondegenerate ws ->
  ERT (costfun := CostEntropy_2) k (fldr_sample ws fldr_unit_loc, σ) < shannon_entropy ws + 6.
Proof.
  intros Hadm Hnd.
  eapply Rle_lt_trans;
    [apply (fldr_sample_ERT_bound Σ ws σ k Hadm Hnd) | apply flip_cost_entropy_bound; assumption].
Qed.

Corollary fldr_sample_ERT_entropy_bound_lim Σ `{!tachisGpreS Σ} (ws : list nat) (σ : state) :
  admissible ws -> nondegenerate ws ->
  lim_ERT (costfun := CostEntropy_2) (fldr_sample ws fldr_unit_loc, σ) < shannon_entropy ws + 6.
Proof.
  intros Hadm Hnd.
  eapply Rle_lt_trans;
    [apply (fldr_sample_ERT_bound_lim Σ ws σ Hadm Hnd) | apply flip_cost_entropy_bound; assumption].
Qed.
