From clutch.eris Require Export adequacy.
From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt.

Set Default Proof Using "Type*".


Section infinite_tape.

  Context `{!erisGS Σ}.

  Definition infinite_tape α (f: nat → (fin 2)) : iProp Σ :=
    ∃ k ns, α ↪ (1; ns) ∗ steps_left k ∗ ⌜ k < length ns ⌝ ∗ ⌜ ∀ i b, ns !! i = Some b → f i = b ⌝.

End infinite_tape.


Section R_approx.

  Import Hierarchy.

  Local Open Scope R_scope.

  Definition seq_bin_to_R (f : nat → (fin 2)) : R :=
    SeriesC (λ n : nat, f n * (1 / 2 ^ (S n))).

  Definition list_bin_to_seq_bin (l : list (fin 2)) : nat → (fin 2) :=
    λ n, match l !! n with
         | None => Fin.F1
         | Some x => x
         end.

  Notation list_fixed_len A k := { ls : list A | length ls = k}.

  (* Or you could just do this as a fold over the list? *)
  Definition list_bin_to_R (l : list (fin 2)) : R :=
    seq_bin_to_R (list_bin_to_seq_bin l).

  Definition discrete_approx k f :=
    SeriesC (λ ns : list_fixed_len (fin 2) k,
          (1 / 2 ^ k) * f (list_bin_to_R (proj1_sig ns))).

  Lemma Rle_0_discrete_approx k f :
    (∀ r, 0 <= f r) →
    0 <= discrete_approx k f.
  Proof.
    rewrite /discrete_approx.
    intros Hle. 
    apply SeriesC_ge_0' => ?.
    apply Rmult_le_pos; auto.
    apply Rcomplements.Rdiv_le_0_compat; first by lra.
    apply pow_lt. nra.
  Qed.

  (* I would not be shocked if this has an off by one error. *)
  Lemma discrete_approx_equiv k (f : R → R) :
    discrete_approx k f =
    SF_seq.Riemann_sum f (SF_seq.SF_seq_f2 (λ x y, x) (SF_seq.unif_part 0 1 (2 ^ k - 1))).
  Admitted.

  Lemma RInt_discrete_approx (f : R → R) ε :
    0 < ε →
    ex_RInt f 0 1 →
    ∃ (N : nat), ∀ (k : nat),
      (N <= k)%nat →
      Rabs (RInt f 0 1 - discrete_approx k f) <= ε.
  Proof.
    intros Hpos Hex.
    destruct Hex as (v&His).
    rewrite (is_RInt_unique _ _ _ v) //.
    specialize (His _ (locally_ball v {| pos := ε; cond_pos := Hpos |})).
    destruct His as (δ&His).
    assert (∃ N, ∀ k, N ≤ k → 1 / 2 ^ k < δ) as (N&HN).
    { specialize (cv_pow_half 1). rewrite /Un_cv => Hin.
      edestruct (Hin δ) as (N&Hk).
      { destruct δ; auto. }
      exists N. intros k Hle.
      assert (Hge: k ≥ N) by lia.
      specialize (Hk _ Hge).
      rewrite /Rdist in Hk.
      rewrite Rminus_0_r in Hk.
      apply Rabs_def2; auto.
    }
    exists N. intros k Hle.
    specialize (HN k Hle).
    set (y := (SF_seq.SF_seq_f2 (λ x y, x) (SF_seq.unif_part 0 1 (2 ^ k - 1)))).
    left.
    edestruct (SF_seq.Riemann_fine_unif_part (λ x y, x) 0 1 (2 ^ k - 1)) as (Hstep&Hptd&Hbegin&Hlast).
    { intros; nra. }
    { intros; nra. }
    eapply Rle_lt_trans; last eapply (His y); last first.
    { split_and!; auto.
      - rewrite Rmin_left; auto. nra.
      - rewrite Rmax_right; auto. nra.
    }
    * eapply Rle_lt_trans; first eauto.
      eapply Rle_lt_trans; last apply HN.
      right.
      f_equal; first nra.
      rewrite minus_INR ?INR_1 ?pow_INR; try nra.
      { replace (INR 2) with 2 by auto. nra. }
      { apply fin.pow_ge_1; lia. }
    * rewrite Rcomplements.sign_eq_1; last by nra.
      rewrite /abs/minus/scal/plus/mult/Rcomplements.sign//=/mult//=/opp//=.
      rewrite Rabs_minus_sym.
      rewrite Rminus_def.
      right. f_equal.
      rewrite discrete_approx_equiv.
      rewrite /y.  rewrite Rmult_1_l //.
  Qed.

End R_approx.

Section unif_tape.

  Context `{!erisGS Σ}.

  Definition unif_tape α (mr : option R) : iProp Σ :=
    match mr with
    | None => α ↪ (1; [])
    | Some r =>
        ∃ f, infinite_tape α f ∗ ⌜ seq_bin_to_R f = r ⌝
  end.

  Import Hierarchy.

  Lemma wp_presample_unif_adv_comp E e α Φ (ε1 : R) (ε2 : R -> R) :
    to_val e = None →
    (forall r, (0 <= ε2 r)%R) ->
    is_RInt ε2 0 1 ε1 →
    unif_tape α None ∗
      ↯ ε1 ∗
      (∀ r : R, ↯ (ε2 r) ∗ unif_tape α (Some r) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hnonval Hle HRint) "(Htape&Hε&Hwp)".
    wp_apply (wp_rand_err_incr); auto.
    iFrame "Hε".
    iIntros (ε1' Hmore) "Hε".
    set (εdiff := ε1' - ε1). 
    edestruct (RInt_discrete_approx ε2 εdiff) as (N1&HN1).
    { rewrite /εdiff; nra. }
    { eexists; eauto. }
    erewrite (is_RInt_unique) in HN1; eauto.
    wp_apply steps_left_intro; first done.
    iIntros (N2) "HN2".
    set (N := (N1 + N2 + 1)%nat).
    assert (Hle1: N1 ≤ N) by lia.
    assert (Hle2: (N2 < N)%nat) by lia.
    specialize (HN1 _ Hle1).
    iAssert (↯ (discrete_approx N ε2)) with "[Hε]" as "Hε".
    {
      iApply (ec_weaken with "Hε").
      split.
      - apply Rle_0_discrete_approx; auto. 
      - destruct (decide (discrete_approx N ε2 <= ε1)) as [Hle'|Hnle'].
        * nra.
        * rewrite Rabs_left in HN1; last by nra.
          rewrite /εdiff in HN1. nra.
    }
    wp_apply (wp_presample_many_adv_comp 1 1 _ _ _ _ [] N _
             (λ ls, ε2 (list_bin_to_R (proj1_sig ls)))); eauto.
    iFrame.
    iIntros (ns') "(Hε2&Hα)". 
    iApply "Hwp".
    iFrame.
    iExists (list_bin_to_seq_bin (proj1_sig ns')).
    iPureIntro.
    rewrite //=.
    split_and!.
    - destruct ns'; simpl; lia.
    - intros i b Hlook.
      rewrite /list_bin_to_seq_bin Hlook //=.
    - rewrite /list_bin_to_R //=.
  Qed.

End unif_tape.
