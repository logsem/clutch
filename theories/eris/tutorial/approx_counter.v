From clutch.eris Require Import eris tutorial.eris_rules.
From clutch.eris.tutorial Require Import eris_rules.

(* ###################################################################### *)
(** * Morris's Approximate Counter *)

Section counter.
  Context `{!erisGS Σ}.

  (** [bits] models the number of bits we have available to store the counter. *)
  Context (bits : nat).

  (** Morris's approximate counter maintains an estimate of how many times the
      counter has been incremented, using exponentially less memory than a
      deterministic counter (O(log log n) bits instead of O(log n)).

      The trick is to store the (base 2) logarithm of the count rather than the
      count itself. On every call to [incr], we flip a biased coin: if the
      currently stored exponent is [k], we increment it only with probability
      [1 / 2^k]. 

      The estimated count is then [2^k - 1]. This estimator is unbiased,
      (in the statistical sense), i.e. if we do k increments the expected
      value of the stimator is in fact k.  *)

  (** A helper that computes [2^k] at run time using a left shift. *)
  Definition pow2 : val := λ: "k", #1 ≪ "k".

  Definition new_counter : val := λ: <>, ref #0.

  (** On increment we sample [rand (2^k - 1)] and on outcome [0] we increment
      the stored value by one.

      Our little language does not have bounded integers, so we simulate
      the behavior by having an assert that checks whether the new 
      value would still fit — if it does not, the assert fails and the
      program errors *)
  Definition incr : val :=
    λ: "c",
      let: "k" := !"c" in
      let: "n" := pow2 "k" in
      if: rand ("n" - #1) = #0 then
        assert ("k" + #1 < #(2^bits)) ;;; ("c" <- "k" + #1)
      else SOMEV #().


  (** Read just returns the unbiased estimate of the current count *)
  Definition read : val :=
    λ: "c", pow2 (!"c") - #1.

  (** ** Representation predicates

      [is_counter_val c k] is the precise representation: [c] holds the
      exponent [k]. It's useful for "weak" specs that need to talk about
      the concrete state. *)
  Definition is_counter_val (c : loc) (k : nat) : iProp Σ := c ↦ #k.

  (** ** Numerical helper lemmas

      Small facts about [2^k] that we use to keep the program proofs free
      of arithmetic bookkeeping. *)

  Lemma pow2_pos (k : nat) : (1 <= 2^k)%nat.
  Proof. induction k; simpl; lia. Qed.

  Lemma INR_pow2_pos (k : nat) : (0 < INR (2^k))%R.
  Proof. apply lt_0_INR. apply pow2_pos. Qed.

  (** [Z]-level identities used to bridge the program's [Z] arithmetic
      back to [nat] arithmetic over [2^k]. *)
  Lemma Z_pow2_pred (k : nat) :
    (Z.of_nat (2^k) - Z.of_nat 1)%Z = Z.of_nat (2^k - 1).
  Proof. pose proof (pow2_pos k). lia. Qed.

  Lemma Z_succ_nat (k : nat) :
    (Z.of_nat k + Z.of_nat 1)%Z = Z.of_nat (S k).
  Proof. lia. Qed.

  (** Bridge: [(2^k - 1) + 1 = 2^k] as a real-number equality. *)
  Lemma INR_pow2_pred_S (k : nat) :
    (INR (2^k - 1) + 1)%R = INR (2^k).
  Proof.
    rewrite -INR_1 -plus_INR. f_equal. pose proof (pow2_pos k). lia.
  Qed.

  (** Inverse-of-[2^] is monotone in the exponent. *)
  Lemma inv_INR_pow2_mono (m n : nat) :
    (m <= n)%nat → (/ INR (2^n) <= / INR (2^m))%R.
  Proof.
    intros Hmn. apply Rinv_le_contravar; [apply INR_pow2_pos|].
    apply le_INR. by apply Nat.pow_le_mono_r.
  Qed.

  (** Packaging the boundary-case credit weakening into one step:
      from a budget of [1 / 2^(2^bits - 1)] we can extract the credit
      [1 / (2^k - 1 + 1)] required by [wp_rand_err] at any state
      [k ≥ 2^bits - 1]. *)
  Lemma ec_pow2_weaken (k : nat) :
    (2^bits - 1 <= k)%nat →
    ↯ (/ INR (2 ^ (2 ^ bits - 1)))%R ⊢ ↯ (1 / (INR (2^k - 1) + 1))%R.
  Proof.
    intros Hk. iIntros "Herr". iApply (ec_weaken with "Herr").
    rewrite INR_pow2_pred_S Rdiv_1_l.
    split.
    - left. apply Rinv_0_lt_compat. apply INR_pow2_pos.
    - by apply inv_INR_pow2_mono.
  Qed.

  #[local] Hint Resolve pow2_pos INR_pow2_pos : core.

  (** ** Specification for the [pow2] helper *)
  Lemma wp_pow2 (k : nat) :
    {{{ True }}} pow2 #k {{{ RET #(2^k); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam. wp_pures.
    replace (Z.shiftl (Z.of_nat 1) (Z.of_nat k)) with (Z.of_nat (2^k))
      by (rewrite Z.shiftl_1_l Nat2Z.inj_pow //).
    by iApply "HΦ".
  Qed.

  (** ** Basic specifications *)

  Lemma wp_new_counter :
    {{{ True }}} new_counter #() {{{ c, RET #c; is_counter_val c 0 }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /new_counter.
    wp_pures.
    wp_alloc c as "Hc".
    iApply "HΦ".
    by rewrite /is_counter_val.
  Qed.

  (** ** A weak, k-tracking spec for [incr]

      If the current state [k] is small enough that another increment
      fits, then [incr] returns [SOMEV #()] and the new state is either
      [k] or [S k]. No error credit is required because the [assert]
      is guaranteed to succeed.

      This spec is weak because it requires a precondition that forces us
      to consider only the worst-case behavior in which we run out of
      headroom after [2^bits - 1] increments, ignoring the O(log log n)
      benefit the approximate counter is supposed to provide. *)
  Lemma wp_incr_weak c k :
    (k + 1 < 2^bits)%nat →
    {{{ is_counter_val c k }}}
      incr #c
    {{{ RET SOMEV #(); is_counter_val c k ∨ is_counter_val c (S k) }}}.
  Proof.
    iIntros (Hk Φ) "Hc HΦ".
    rewrite /incr /is_counter_val.
    wp_pures.
    wp_load.
    wp_pures.
    wp_apply wp_pow2; [done|].
    iIntros "_".
    wp_pures.
    rewrite Z_pow2_pred.
    wp_apply wp_rand.
    iIntros (x) "%Hx".
    wp_pures.
    case_bool_decide as Hxz.
    - (** [x = 0]: increment branch, must discharge the assert *)
      wp_pures.
      rewrite bool_decide_eq_true_2; last by lia.
      wp_pures.
      wp_bind (_ <- _)%E.
      wp_store.
      wp_pures.
      iApply "HΦ".
      iRight.
      rewrite Z_succ_nat.
      iFrame.
      auto.
    - (** [x ≠ 0]: leave the counter unchanged, return [SOMEV #()] *)
      wp_pures.
      iApply "HΦ".
      iLeft. iFrame.
      auto.
  Qed.

  (** ** Coarse, k-independent spec for [incr] *)

  (** [is_counter c] hides [k] inside an existential. It's the right
      representation for the coarse spec, which is uniform in [k]. *)

  Definition is_counter (c : loc) : iProp Σ := ∃ k : nat, is_counter_val c k.

  (** Each call to [incr] is charged a flat error budget of
      [1 / 2^(2^bits - 1)], which is enough to cover the worst case — being
      at the boundary state [k = 2^bits - 1], where any successful coin
      causes an overflow. The spec returns [is_counter c] with the new
      state hidden behind the existential. *)
  Lemma wp_incr c :
    {{{ is_counter c ∗ ↯ (/ INR (2 ^ (2 ^ bits - 1)))%R }}}
      incr #c
    {{{ RET SOMEV #(); is_counter c }}}.
  Proof.
    iIntros (Φ) "[Hc Herr] HΦ".
    rewrite /is_counter /is_counter_val.
    iDestruct "Hc" as (k) "Hc".
    rewrite /incr.
    wp_pures.
    wp_load.
    wp_pures.
    wp_apply wp_pow2; [done|].
    iIntros "_".
    wp_pures.
    rewrite Z_pow2_pred.
    destruct (Nat.ltb (k + 1) (2 ^ bits)) eqn:Hkb.
    - (** Non-boundary case: [k + 1 < 2^bits]. The assert always succeeds,
          so we don't need the error credit at all. *)
      apply Nat.ltb_lt in Hkb.
      wp_apply wp_rand.
      iIntros (x) "%Hx".
      wp_pures.
      case_bool_decide as Hxz.
      + (** [x = 0]: increment. *)
        wp_pures.
        rewrite bool_decide_eq_true_2; last by lia.
        wp_pures.
        wp_bind (_ <- _)%E.
        wp_store.
        wp_pures.
        iApply "HΦ".
        iExists (S k).
        rewrite Z_succ_nat.
        iFrame.
        done.
      + (** [x ≠ 0]: state unchanged. *)
        wp_pures.
        iApply "HΦ".
        iExists k.
        iFrame; auto.
    - (** Boundary case: [k + 1 ≥ 2^bits], so [k ≥ 2^bits - 1]. Incrementing
          would overflow, so we must force [rand (2^k - 1)] to a nonzero
          outcome. We use [wp_rand_err] to rule out [x = 0], which costs
          [1 / 2^k]. Since [k ≥ 2^bits - 1] we have [1 / 2^k ≤ 1 / 2^(2^bits - 1)],
          so our budget suffices. *)
      apply Nat.ltb_ge in Hkb.
      wp_apply (wp_rand_err 0 (2^k - 1) with "[Herr]").
      { iApply (ec_pow2_weaken with "Herr"). lia. }
      iIntros (x) "[%Hx %Hxne]".
      wp_pures.
      rewrite bool_decide_eq_false_2; last first.
      { intros Heq. apply Hxne. injection Heq. lia. }
      wp_pures.
      iApply "HΦ".
      iExists k.
      iFrame; auto.
  Qed.

  (** ** A bounded-call spec for [incr]

      We define an "overflow probability" [err_overflow n k] as a closed
      Gallina function: this is exactly the failure probability under
      [n] calls to [incr] starting from state [k]. We then pay this
      amount up front and stash it inside a fresh representation
      predicate. Each call to [incr] uses up part of the stash and
      returns the predicate at [n - 1]; the user never has to inject new
      credits beyond the initial payment. *)

  Fixpoint err_overflow (n k : nat) : R :=
    match n with
    | O => 0%R
    | S n' =>
        let p : R := (/ INR (2^k))%R in
        let e_inc : R :=
          if Nat.ltb (k + 1) (2^bits) then err_overflow n' (S k) else 1%R in
        (p * e_inc + (1 - p) * err_overflow n' k)%R
    end.

  Lemma err_overflow_nonneg (n k : nat) : (0 <= err_overflow n k)%R.
  Proof.
    revert k. induction n as [|n IH]; intros k; simpl; [lra|].
    apply Rplus_le_le_0_compat.
    - apply Rmult_le_pos.
      + left. apply Rinv_0_lt_compat. apply INR_pow2_pos.
      + destruct (Nat.ltb (k+1) (2^bits)); [apply IH | lra].
    - apply Rmult_le_pos; [|apply IH].
      assert (/ INR (2^k) <= 1)%R; [|lra].
      rewrite -Rinv_1. apply Rinv_le_contravar; [lra|].
      rewrite -INR_1. apply le_INR. apply pow2_pos.
  Qed.

  (** Generic fact about [foldr Rplus] over a fmap of a constant function. *)
  Lemma foldr_const_seq (b : R) (start M : nat) :
    foldr Rplus 0%R ((fun _ : nat => b) <$> seq start M) = (INR M * b)%R.
  Proof.
    revert start. induction M as [|M IH]; intros start.
    - simpl. lra.
    - rewrite S_INR. simpl. rewrite IH. lra.
  Qed.

  (** The expectation of a "dirac" function [F(x) = if x = 0 then a else b]
      over the uniform distribution on [{0, ..., M}] is [a + M·b]. *)
  Lemma foldr_dirac_seq_aux (a b : R) (start M : nat) :
    (0 < start)%nat →
    foldr Rplus 0%R
      ((fun x : nat => if bool_decide (x = 0%nat) then a else b) <$> seq start M)
    = (INR M * b)%R.
  Proof.
    revert start. induction M as [|M IH]; intros start Hstart.
    - simpl. lra.
    - rewrite S_INR. simpl. rewrite bool_decide_false; [|lia].
      rewrite IH; [lra|lia].
  Qed.

  Lemma foldr_dirac_seq (a b : R) (M : nat) :
    foldr Rplus 0%R
      ((fun x : nat => if bool_decide (x = 0%nat) then a else b) <$> seq 0 (S M))
    = (a + INR M * b)%R.
  Proof.
    simpl. f_equal. apply foldr_dirac_seq_aux. lia.
  Qed.

  Definition is_counter_budget (c : loc) (n : nat) : iProp Σ :=
    ∃ k : nat, is_counter_val c k ∗ ↯ (err_overflow n k).

  Lemma is_counter_budget_intro c n :
    is_counter_val c 0 ∗ ↯ (err_overflow n 0) ⊢ is_counter_budget c n.
  Proof. iIntros "[Hc Herr]". iExists 0%nat. iFrame. Qed.

  Lemma wp_incr_budget c n :
    {{{ is_counter_budget c (S n) }}}
      incr #c
    {{{ RET SOMEV #(); is_counter_budget c n }}}.
  Proof.
    iIntros (Φ) "Hcb HΦ".
    iDestruct "Hcb" as (k) "(Hc & Herr)".
    rewrite /is_counter_val /incr.
    wp_pures.
    wp_load.
    wp_pures.
    wp_apply wp_pow2; [done|].
    iIntros "_".
    wp_pures.
    rewrite Z_pow2_pred.
    (** Distribute the up-front budget across the [2^k] outcomes of
        [rand (2^k - 1)]. Outcome [0] gets the credit appropriate for the
        increment branch ([err_overflow n (S k)] or [1] at the boundary);
        all other outcomes carry [err_overflow n k]. *)
    set (e_inc :=
      if Nat.ltb (k + 1) (2^bits) then err_overflow n (S k) else 1%R).
    set (F := fun x : nat => if bool_decide (x = 0%nat) then e_inc else err_overflow n k).
    wp_apply (wp_rand_exp F (2^k - 1)%nat with "Herr").
    { intros m. unfold F.
      case_bool_decide.
      - unfold e_inc.
        destruct (Nat.ltb (k+1) (2^bits)); [apply err_overflow_nonneg | lra].
      - apply err_overflow_nonneg. }
    { (** The sum [∑_x F(x)] is [e_inc + (2^k - 1) · err_overflow n k],
          which by the recurrence equals [2^k · err_overflow (S n) k]. *)
      pose proof (pow2_pos k) as Hpk.
      destruct (2^k) as [|M] eqn:Hpkeq; [lia|].
      replace (S (S M - 1))%nat with (S M) by lia.
      rewrite (foldr_dirac_seq e_inc (err_overflow n k) M).
      simpl err_overflow.
      change (if Nat.ltb (k + 1) (2 ^ bits) then err_overflow n (S k) else 1%R)
        with e_inc.
      rewrite Hpkeq S_INR.
      pose proof (pos_INR M) as HM.
      right. field. lra. }
    iIntros (x) "(%Hxle & Herr)".
    wp_pures.
    case_bool_decide as Hxz.
    - (** [x = 0]: enter the increment branch. *)
      assert (x = 0%nat) as -> by (injection Hxz; lia).
      iEval (rewrite /F bool_decide_true; [|done]) in "Herr".
      iEval (rewrite /e_inc) in "Herr".
      destruct (Nat.ltb (k + 1) (2^bits)) eqn:Hkb.
      + apply Nat.ltb_lt in Hkb.
        wp_pures.
        rewrite bool_decide_eq_true_2; last by lia.
        wp_pures.
        wp_bind (_ <- _)%E.
        wp_store.
        wp_pures.
        iApply "HΦ".
        iExists (S k).
        rewrite Z_succ_nat. iFrame. done.
      + (** Boundary: [Herr : ↯ 1], which is a contradiction. *)
        iExFalso. iApply (ec_contradict with "Herr"). lra.
    - (** [x ≠ 0]: [Herr] still carries [err_overflow n k] for state [k]. *)
      wp_pures.
      iApply "HΦ".
      iExists k.
      iEval (rewrite /F bool_decide_false;
             [|intros Heq; apply Hxz; subst x; reflexivity]) in "Herr".
      iFrame. done.
  Qed.

End counter.
