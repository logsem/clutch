(** Recurrence relation and Markov-style upper bound for the failure
    probability of Papadimitriou's randomized 2-SAT algorithm.

    Fix a satisfying assignment [w] (the "witness") of the formula and let [k]
    denote the Hamming distance between the current assignment and [w].

    The classical analysis observes the following: when the algorithm flips a
    uniformly random literal of an unsatisfied clause [(l1, l2)], at least
    one of the two underlying variables must disagree with [w] (otherwise
    both literals would evaluate to [w]'s value, making the clause satisfied
    in [w]). Consequently:

      - in the *interior* [0 < k < nvars], the flip moves the assignment one
        step closer to [w] with probability at least [1/2] and one step
        further with probability at most [1/2];
      - at the *upper boundary* [k = nvars], every variable disagrees with
        [w], so both variables of any unsatisfied clause disagree with [w]
        and the flip *always* decreases [k] (probability [1]).

    The standard Papadimitriou analysis takes the pessimistic interior case
    (an exactly [1/2]–[1/2] step) and uses the deterministic boundary case
    above. This gives the recurrence [err nvars n k] below.

    The main result of this file, [err_bound], is the standard
    Markov-inequality bound

        err nvars n k <= k * (2 * nvars - k) / n     (for [k <= nvars])

    obtained by exhibiting [k * (2 * nvars - k)] as a supersolution of the
    expected-hitting-time recurrence of the random walk.
*)

From Stdlib Require Import Reals Arith Lia Lra Psatz.

Section err.

  Local Open Scope R_scope.

  Variable nvars : nat.

  Fixpoint err (n k : nat) : R :=
    match k with
    | 0%nat => 0
    | S k' =>
        match n with
        | 0%nat => 1
        | S n' =>
            if Nat.eqb k nvars
            then err n' k'
            else (1 / 2) * err n' k' + (1 / 2) * err n' (S (S k'))
        end
    end.

  (** Pinpoint unfolding of one step of [err] (avoids [simpl]'s eager
      reduction of [Nat.eqb] into a match on [nvars]). *)

  Lemma err_O_O : err 0 0 = 0.
  Proof. reflexivity. Qed.

  Lemma err_O_S : forall k, err 0 (S k) = 1.
  Proof. reflexivity. Qed.

  Lemma err_S_O : forall n, err n 0 = 0.
  Proof. destruct n; reflexivity. Qed.

  Lemma err_S_S : forall n k,
    err (S n) (S k) =
      if Nat.eqb (S k) nvars
      then err n k
      else (1 / 2) * err n k + (1 / 2) * err n (S (S k)).
  Proof. reflexivity. Qed.

  Lemma err_step_boundary : forall n k,
    S k = nvars ->
    err (S n) (S k) = err n k.
  Proof.
    intros n k Heq. rewrite err_S_S.
    destruct (Nat.eqb_spec (S k) nvars); [reflexivity | lia].
  Qed.

  Lemma err_step_neq : forall n k,
    S k <> nvars ->
    err (S n) (S k) = (1 / 2) * err n k + (1 / 2) * err n (S (S k)).
  Proof.
    intros n k Hneq. rewrite err_S_S.
    destruct (Nat.eqb_spec (S k) nvars); [lia | reflexivity].
  Qed.

  (** Caller-friendly forms of the two recurrence steps, with the index
      arithmetic precomputed. *)

  Lemma err_at_max iter :
    (1 <= nvars)%nat ->
    err (S iter) nvars = err iter (nvars - 1).
  Proof.
    intros.
    transitivity (err (S iter) (S (nvars - 1))); [f_equal; lia|].
    apply err_step_boundary; lia.
  Qed.

  Lemma err_step_interior iter k :
    (1 <= k)%nat -> (k < nvars)%nat ->
    err (S iter) k = (err iter (k - 1) + err iter (k + 1)) / 2.
  Proof.
    destruct k as [|k']; [lia|]. intros.
    rewrite (err_step_neq iter k' ltac:(lia)).
    replace (S k' - 1)%nat with k' by lia.
    replace (S k' + 1)%nat with (S (S k')) by lia.
    lra.
  Qed.

  (** [err] is always a probability: [0 <= err n k <= 1]. *)

  Lemma err_nonneg : forall n k, 0 <= err n k.
  Proof.
    induction n as [|n IHn]; intros [|k].
    - rewrite err_O_O. lra.
    - rewrite err_O_S. lra.
    - rewrite err_S_O. lra.
    - destruct (Nat.eq_dec (S k) nvars) as [Heq | Hneq].
      + rewrite (err_step_boundary _ _ Heq). apply IHn.
      + rewrite (err_step_neq _ _ Hneq).
        pose proof (IHn k). pose proof (IHn (S (S k))). lra.
  Qed.

  Lemma err_le_1 : forall n k, err n k <= 1.
  Proof.
    induction n as [|n IHn]; intros [|k].
    - rewrite err_O_O. lra.
    - rewrite err_O_S. lra.
    - rewrite err_S_O. lra.
    - destruct (Nat.eq_dec (S k) nvars) as [Heq | Hneq].
      + rewrite (err_step_boundary _ _ Heq). apply IHn.
      + rewrite (err_step_neq _ _ Hneq).
        pose proof (IHn k). pose proof (IHn (S (S k))). lra.
  Qed.

  (** [err] is monotone non-decreasing AND concave in [k].  These two
      properties have to be proved together because at the upper boundary
      [S k = nvars] the recurrence collapses to [err (S n) (S k) = err n k];
      propagating monotonicity past that boundary requires concavity at the
      previous level, and vice versa. *)

  (* Local automation: unfold one [err] step, with a case split on
     [boundary vs interior].  Infeasible branches are closed by [lia]. *)
  Local Ltac expand_err :=
    repeat first
      [ rewrite err_S_O | rewrite err_O_O | rewrite err_O_S
      | match goal with
        | |- context [err (S ?n) (S ?k)] =>
          let H := fresh in
          destruct (Nat.eq_dec (S k) nvars) as [H|H];
            [ try (exfalso; lia); rewrite (err_step_boundary n k H)
            | try (exfalso; lia); rewrite (err_step_neq n k H) ]
        end ].

  Lemma err_mono_concave : forall n,
    (forall k, (S k <= nvars)%nat -> err n k <= err n (S k)) /\
    (forall k, (S (S k) <= nvars)%nat ->
               err n k + err n (S (S k)) <= 2 * err n (S k)).
  Proof.
    induction n as [|n [IHm IHc]]; split; intros [|k] Hk.
    1-4: rewrite ?err_O_O, ?err_O_S; lra.
    - rewrite err_S_O. apply err_nonneg.
    - expand_err;
        [ pose proof (IHc k ltac:(lia))
        | pose proof (IHm k ltac:(lia)); pose proof (IHm (S (S k)) ltac:(lia)) ];
        lra.
    - expand_err;
        [ pose proof (IHm 1%nat ltac:(lia)) | pose proof (IHc 1%nat ltac:(lia)) ];
        lra.
    - expand_err;
        [ pose proof (IHc k ltac:(lia)); pose proof (IHm (S (S k)) ltac:(lia))
        | pose proof (IHc k ltac:(lia)); pose proof (IHc (S (S k)) ltac:(lia)) ];
        lra.
  Qed.

  Lemma err_mono_k : forall n k1 k2,
    (k1 <= k2 <= nvars)%nat ->
    (err n k1 <= err n k2)%R.
  Proof.
    intros n k1 k2 [Hk1 Hk2]. destruct (err_mono_concave n) as [Hmono _].
    revert Hk2. induction Hk1; intros Hk2;
      [lra | etransitivity; [apply IHHk1 | apply Hmono]; lia].
  Qed.

  (** The Lyapunov / expected-hitting-time function:
      [f k = k * (2 * nvars - k)] (computed over the reals). *)

  Definition f (k : nat) : R := INR k * (2 * INR nvars - INR k).

  Lemma f_nonneg : forall k, (k <= nvars)%nat -> 0 <= f k.
  Proof.
    intros k Hk. unfold f.
    apply Rmult_le_pos; [apply pos_INR|].
    apply le_INR in Hk.
    pose proof (pos_INR k). lra.
  Qed.

  (** Key algebraic identity: [f] is a solution of the interior random-walk
      step with drift exactly [1]. *)
  Lemma f_avg_interior : forall k,
    f k + f (S (S k)) = 2 * f (S k) - 2.
  Proof.
    intros k. unfold f. rewrite !S_INR. nra.
  Qed.

  (** Boundary identity: at [k = nvars] the deterministic down-step
      decreases [f] by exactly [1]. *)
  Lemma f_boundary : (1 <= nvars)%nat -> f (nvars - 1) = f nvars - 1.
  Proof.
    intros Hn. unfold f.
    rewrite minus_INR by lia. simpl. nra.
  Qed.

  (** Main theorem in multiplicative form (avoids dividing by [0] at [n = 0]). *)

  Theorem err_bound_mul : forall n k,
    (k <= nvars)%nat ->
    err n k * INR n <= f k.
  Proof.
    induction n as [|n IHn]; intros k Hk.
    - simpl. rewrite Rmult_0_r. apply f_nonneg; auto.
    - destruct (Rle_or_lt (INR (S n)) (f k)) as [Hloose | Htight].
      + (* Loose case: INR (S n) <= f k.  Bound follows from [err <= 1]. *)
        eapply Rle_trans; [|exact Hloose].
        rewrite <- (Rmult_1_l (INR (S n))) at 2.
        apply Rmult_le_compat_r; [apply pos_INR | apply err_le_1].
      + (* Tight case: f k < INR (S n).  Use the recurrence and IH. *)
        destruct k as [|k'].
        * rewrite err_S_O, Rmult_0_l. apply f_nonneg; lia.
        * assert (Hk' : (k' <= nvars)%nat) by lia.
          (* In this branch [n > 0] because [INR (S n) > f (S k') >= 0] is
             too weak on its own, but at [n = 0] we have [INR (S n) = 1] and
             [f (S k') = 0] would force [2 * nvars = S k'] contradicting
             [S k' <= nvars] (with [k' >= 0, nvars >= 1]). *)
          assert (Hn_pos : (0 < n)%nat).
          { destruct n as [|n']; [|lia]. exfalso.
            assert (Hfp : 0 <= f (S k')) by (apply f_nonneg; lia).
            (* INR 1 = 1, so 1 > f (S k') means f (S k') < 1 *)
            simpl in Htight.
            (* f (S k') = (k'+1)(2 nvars - (k'+1)) *)
            (* For S k' = nvars: f = nvars * nvars >= 1. *)
            (* For S k' < nvars: f >= (k'+1)(k'+1) >= 1. *)
            unfold f in Htight. rewrite S_INR in Htight.
            assert (HnvarsR : INR (S k') <= INR nvars) by (apply le_INR; lia).
            rewrite S_INR in HnvarsR.
            assert (Hknn : 0 <= INR k') by apply pos_INR.
            nra. }
          assert (HnR : 1 <= INR n) by (rewrite <- INR_1; apply le_INR; lia).
          destruct (Nat.eq_dec (S k') nvars) as [Hbdy | Hneq].
          -- (* Boundary: S k' = nvars *)
             rewrite (err_step_boundary _ _ Hbdy).
             pose proof (IHn k' Hk') as IH.
             pose proof (err_nonneg n k') as Hnn.
             pose proof (err_le_1 n k') as Hle.
             assert (Hk'_eq : (k' = nvars - 1)%nat) by lia.
             assert (Hfb : f k' = f (S k') - 1).
             { rewrite Hbdy, Hk'_eq. apply f_boundary; lia. }
             rewrite Hfb in IH.
             rewrite S_INR. nra.
          -- (* Interior: S k' < nvars (since S k' <= nvars and <> nvars) *)
             rewrite (err_step_neq _ _ Hneq).
             assert (HSSk_le : (S (S k') <= nvars)%nat) by lia.
             pose proof (IHn k' Hk') as IH1.
             pose proof (IHn (S (S k')) HSSk_le) as IH2.
             pose proof (err_nonneg n k') as Hnn1.
             pose proof (err_nonneg n (S (S k'))) as Hnn2.
             pose proof (err_le_1 n k') as Hle1.
             pose proof (err_le_1 n (S (S k'))) as Hle2.
             pose proof (f_avg_interior k') as Havg.
             rewrite S_INR. nra.
  Qed.

  (** The headline corollary in division form. *)

  Theorem err_bound : forall n k,
    (1 <= n)%nat ->
    (k <= nvars)%nat ->
    err n k <= INR k * (2 * INR nvars - INR k) / INR n.
  Proof.
    intros n k Hn Hk.
    pose proof (err_bound_mul n k Hk) as Hmul.
    unfold f in Hmul.
    assert (HnR : 0 < INR n) by (apply lt_0_INR; lia).
    apply (Rmult_le_reg_r (INR n)); [exact HnR|].
    unfold Rdiv.
    rewrite Rmult_assoc, Rinv_l by lra.
    rewrite Rmult_1_r.
    exact Hmul.
  Qed.

  (** [f] is maximized at [k = nvars]: [f k <= nvars^2] for [k <= nvars].
      This is [(nvars - k)^2 >= 0] rearranged. *)

  Lemma f_max : forall k, (k <= nvars)%nat -> f k <= INR nvars * INR nvars.
  Proof.
    intros k Hk. unfold f.
    apply le_INR in Hk.
    pose proof (pos_INR k).
    pose proof (pos_INR nvars).
    nra.
  Qed.

  (** Uniform quadratic upper bound:
      [err n k <= nvars^2 / n] for [n >= 1] and [k <= nvars]. *)

  Lemma err_le_quadratic : forall n k,
    (1 <= n)%nat ->
    (k <= nvars)%nat ->
    err n k <= INR nvars * INR nvars / INR n.
  Proof.
    intros n k Hn Hk.
    eapply Rle_trans.
    { apply err_bound; assumption. }
    unfold Rdiv.
    apply Rmult_le_compat_r.
    - apply Rlt_le, Rinv_0_lt_compat, lt_0_INR; lia.
    - pose proof (f_max k Hk) as Hfm. unfold f in Hfm. exact Hfm.
  Qed.

  (** Papadimitriou's bound: after [2 * nvars^2] iterations, the failure
      probability is at most [1/2], regardless of the starting Hamming
      distance [k <= nvars]. *)

  Theorem err_papa : forall k,
    (k <= nvars)%nat ->
    err (2 * nvars * nvars) k <= 1 / 2.
  Proof.
    intros k Hk.
    destruct k as [|k'].
    - (* [k = 0]: [err _ 0 = 0]. *)
      rewrite err_S_O. lra.
    - (* [k >= 1], hence [nvars >= 1] and [2 * nvars * nvars >= 2 >= 1]. *)
      assert (Hnv1 : (1 <= nvars)%nat) by lia.
      assert (Hn1 : (1 <= 2 * nvars * nvars)%nat) by nia.
      eapply Rle_trans.
      { apply err_le_quadratic; [exact Hn1 | exact Hk]. }
      (* Goal: [nvars^2 / (2 * nvars^2) <= 1/2]. *)
      assert (HnvR : 0 < INR nvars) by (apply lt_0_INR; lia).
      rewrite !mult_INR.
      assert (HINR2 : INR 2 = 2) by (simpl; lra).
      rewrite HINR2.
      apply Rmult_le_reg_r with (2 * INR nvars * INR nvars); [nra|].
      unfold Rdiv.
      rewrite Rmult_assoc, Rinv_l by nra.
      rewrite Rmult_1_r. nra.
  Qed.

End err.
