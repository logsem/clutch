From clutch.eris Require Export eris error_rules.
From clutch Require Export examples.approximate_samplers.approx_sampler_lib.
From Coquelicot Require Import Series.
Require Import Lra.

Set Default Proof Using "Type*".

Section uniform_random_walk.

  (** * 1D Random walk with equal probability of stepping left or right *)

  Local Open Scope R.
  Context `{!erisGS Σ}.


  Definition unif_rw_1d_rec : val :=
    (rec: "f" "n" "α" :=
      if: "n" < #1
      then #()
      else let: "x" := (rand ("α") #1) in
           if: ("x" < #1)
           then "f" ("n" - #1) "α"
           else "f" ("n" + #1) "α")%V.

  Definition unif_rw_1d : expr :=
    ( let: "α" := (alloc #1) in
      unif_rw_1d_rec #1 "α" )%E.

  Fixpoint final_pos_rev (p0 : nat) (li : list (fin 2)) : nat :=
    match li with
      | [] => p0
      | (x::xs) =>
          match (final_pos_rev p0 xs) with
          | 0 => 0
          | S n => if (bool_decide (x = 0%fin))
                     then n
                     else (S (S n))
          end
    end.

  Definition final_pos (p0 : nat) (li : list (fin 2)) : nat :=
    final_pos_rev p0 (reverse li).

  Definition final_pos_rsm (p0 : nat) (li : list (fin 2)) : R :=
    final_pos_rev p0 (reverse li).

  Definition term_cond (p0 : nat) (li : list (fin 2)) := (final_pos p0 li = 0%nat).

  Lemma final_pos_rsm_pos (li : list (fin 2)) :
    0 <= final_pos_rsm 1 li.
  Proof.
    apply pos_INR.
  Qed.

  Lemma final_pos_dec (li : list (fin 2)):
        ¬ term_cond 1 li → ∃ c : fin 2, final_pos 1 (li ++ [c]) < final_pos 1 li.
  Proof.
    rewrite /term_cond.
    intros Hli.
    exists 0%fin.
    rewrite /final_pos.
    rewrite /final_pos in Hli.
    rewrite reverse_app reverse_singleton //.
    simpl.
    destruct (final_pos_rev 1 (reverse li)); [done|].
    apply lt_INR.
    lia.
  Qed.

  Lemma final_pos_bounded_rsm (r : R):
    ∃ n : nat, ∀ l : list (fin 2),
      final_pos_rsm 1 l <= r → final_pos 1 l ≤ n.
  Proof.
    assert (r < 0 \/ 0 <= r)%R as [Hr | Hr] by lra.
    {
      exists 0%nat.
      intros l Hl.
      pose proof (final_pos_rsm_pos l).
      lra.
    }
    destruct (Rcomplements.nfloor_ex r Hr) as [n Hn].
    exists (S n).
    rewrite /final_pos_rsm /final_pos.
    intros l Hl.
    apply INR_le.
    rewrite S_INR.
    lra.
  Qed.

  Lemma final_pos_rsm_rsm (l : list (fin 2)):
    SeriesC (λ i : fin 2, 1 / 2 * final_pos_rsm 1 (l ++ [i])) <= final_pos_rsm 1 l.
  Proof.
    rewrite SeriesC_fin2.
    rewrite /final_pos_rsm.
    do 2 rewrite reverse_app reverse_singleton //.
    simpl.
    destruct (final_pos_rev 1 (reverse l)); [lra|].
    do 2 rewrite S_INR.
    lra.
  Qed.

  Theorem rw_final_pos (n : nat) (li : list (fin 2)) (α : loc) E :
    term_cond n li ->
    α ↪ (1%nat; li) -∗
    WP unif_rw_1d_rec #n (#lbl:α) @ E {{ v, True }}.
  Proof.
    iIntros (Hterm) "Hα".
    iInduction li as [|i lr] "IH".
    - rewrite /term_cond /final_pos /= in Hterm.
      rewrite Hterm.
      rewrite /unif_rw_1d_rec.
      wp_pures.
      done.
    - rewrite /unif_rw_1d_rec.
      wp_pures.
      case_bool_decide.
      + wp_pures. done.
      + wp_pures.
        wp_bind (rand _)%E.
        (* TODO : Fix rand_tape tactic *)
        iPoseProof (wp_rand_tape 1 α i lr 1 E with "[$Hα]") as "Hklj".
  Admitted.

  Theorem unif_rw_1d_AST (n : nat) (ε : nonnegreal) E :
    (0 < ε)%R ->
    ↯ ε -∗
           WP unif_rw_1d @ E {{ v, True }}.
  Proof.
    iIntros (Hpos) "Herr".
    rewrite /unif_rw_1d.
    (* TODO: fix wp_alloctape tactic *)
    wp_apply (wp_alloc_tape); auto.
    iIntros (α) "Hα".
    do 2 wp_pure.
    wp_apply (presample_rsm 1 1 _ _ _ _ (term_cond 1) _ _ (final_pos_rsm 1) (final_pos 1)); eauto.
    - apply final_pos_rsm_pos.
    - intros l.
      rewrite /term_cond /final_pos_rsm /final_pos //.
      split; intros.
      + rewrite H //.
      + by apply INR_eq.
    - intro r.
      apply final_pos_bounded_rsm.
    - apply final_pos_dec.
    - apply final_pos_rsm_rsm.
    - iFrame.
      iIntros (lf) "(%Hlf & Hα)".
      wp_apply (rw_final_pos 1 with "[Hα]"); eauto.
  Qed.

End uniform_random_walk.
