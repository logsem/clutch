From clutch.eris Require Export adequacy.
From clutch.eris Require Export eris error_rules receipt_rules.
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
    { (* There are already lemmas about geom sequence, I think this follows from those. Search "geom". *)
      admit. }
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
  Admitted.

End R_approx.
