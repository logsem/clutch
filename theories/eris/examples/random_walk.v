From clutch.eris Require Export adequacy total_adequacy.
From clutch.eris Require Export eris error_rules.
From Coquelicot Require Import Series.

Set Default Proof Using "Type*".



Section uniform_random_walk.

  (** * 1D Random walk with equal probability of stepping left or right *)

  Local Open Scope R.
  Context `{!erisGS Σ}.


  Definition unif_rw_1d_rec : val :=
    (rec: "f" "n" "α" :=
      if: "n" < #1
      then #()
      else let: "x" := (rand("α") #1) in
           if: ("x" < #1)
           then "f" ("n" - #1) "α"
           else "f" ("n" + #1) "α")%V.

  Definition unif_rw_1d : expr :=
    ( let: "α" := (alloc #1) in
      unif_rw_1d_rec #1 "α" )%E.

  Fixpoint final_pos (p0 : nat) (li : list (fin 2)) : nat :=
    match li with
      | [] => p0
      | (x::xs) =>
          match p0 with
          | 0 => 0
          | S n => if (bool_decide (x = 0%fin))
                     then final_pos n xs
                     else final_pos (S (S n)) xs
          end
    end.

  Lemma final_pos_app (p0 : nat) (li : list (fin 2)) (i : fin 2) :
    final_pos p0 (li ++ [i]) =
      match final_pos p0 li with
        | 0 => 0%nat
        | S n =>
            if (bool_decide (i = 0%fin))
                then n
                else (S (S n))
       end.
  Proof.
    revert p0.
    induction li; intro p0.
    - simpl. done.
    - rewrite -app_comm_cons.
      simpl.
      destruct p0; auto.
      destruct (decide (a = 0%fin)).
      + rewrite (bool_decide_eq_true_2 (a = 0%fin)); auto.
      + rewrite (bool_decide_eq_false_2 (a = 0%fin)); auto.
  Qed.



  Definition final_pos_rsm (p0 : nat) (li : list (fin 2)) : R :=
    final_pos p0 li.

  Definition term_cond (p0 : nat) (li : list (fin 2)) := (final_pos p0 li = 0%nat).

  Lemma term_cond_0 (p0 : nat) (li : list (fin 2)) :
    term_cond (S p0) (0%fin :: li) <-> term_cond p0 li.
  Proof.
    rewrite /term_cond; simpl; auto.
  Qed.

  Lemma term_cond_1 (p0 : nat) (li : list (fin 2)) :
    term_cond (S p0) (1%fin :: li) <-> term_cond (S (S p0)) li.
  Proof.
    rewrite /term_cond; simpl; auto.
  Qed.

  Lemma final_pos_rsm_pos (li : list (fin 2)) :
    0 <= final_pos_rsm 1 li.
  Proof.
    apply pos_INR.
  Qed.

  Lemma final_pos_dec_aux (p0 : nat) (li : list (fin 2)):
    ¬ term_cond p0 li → final_pos p0 (li ++ [0%fin]) < final_pos p0 li.
  Proof.
    revert p0.
    induction li; intro p0.
    - rewrite /term_cond.
      intros Hterm.
      simpl.
      destruct p0.
      + rewrite /final_pos // in Hterm.
      + apply lt_INR.
        lia.
    - intros Hterm.
      rewrite -app_comm_cons.
      simpl.
      destruct p0.
      + rewrite /term_cond /final_pos // in Hterm.
      + case_bool_decide.
        * apply IHli.
          intros Htc.
          apply Hterm.
          simplify_eq.
          rewrite term_cond_0 //.
        * apply IHli.
          intros Htc.
          apply Hterm.
          simplify_eq.
          assert (a = 1%fin) as ->.
          {
            inv_fin a; auto.
            - intros ? ?. done.
            - intros i ? ?.
              inv_fin i.
              + intros ??. done.
              + done. }
          rewrite term_cond_1 //.
  Qed.


  Lemma final_pos_dec (li : list (fin 2)):
        ¬ term_cond 1 li → ∃ c : fin 2, final_pos 1 (li ++ [c]) < final_pos 1 li.
  Proof.
    intros H.
    exists 0%fin.
    by apply final_pos_dec_aux.
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
    do 2 rewrite final_pos_app.
    destruct (final_pos 1 l); [lra|].
    case_bool_decide; [|done].
    case_bool_decide; [done|].
    do 2 rewrite S_INR.
    lra.
  Qed.

  Theorem rw_final_pos (n : nat) (li : list (fin 2)) (α : loc) E :
    term_cond n li ->
    α ↪ (S (Z.to_nat 0); li) -∗
    WP unif_rw_1d_rec #n (#lbl:α) @ E [{ v, True }].
  Proof.
    iIntros (Hterm) "Hα".
    iInduction li as [|i lr] "IH" forall (n Hterm).
    - rewrite /term_cond /final_pos /= in Hterm.
      rewrite Hterm.
      rewrite /unif_rw_1d_rec.
      wp_pures.
      done.
    - rewrite /unif_rw_1d_rec.
      destruct n as [|m].
      (* Corner case: n = 0 *)
      {
        wp_pures. done.
      }
      wp_pures.
      rewrite bool_decide_eq_false_2 ; [|lia].
      wp_pures.
      wp_bind (Rand _ _)%I.
      (* TODO : Fix rand_tape tactic *)
      wp_apply (twp_rand_tape with "Hα").
      iIntros "Hα".
      wp_pures.
      case_bool_decide as Hi.
      * do 2 wp_pure.
        assert (term_cond m lr).
        {
          assert (i = 0%fin) as ->.
          {
            inv_fin i.
            - intros ??. done.
            - intros i ??.
              inv_fin i.
              + intros ??. done.
              + intros ???.
                simpl in Hi. lia.
          }
          rewrite -term_cond_0 //.
        }
        replace #(S m - 1) with #m; last first.
        { do 2 f_equal. lia. }
        iApply "IH"; auto.
      * do 2 wp_pure.
        assert (term_cond (S (S m)) lr).
        {
          assert (i = 1%fin) as ->.
          {
            inv_fin i.
            - intros ??. done.
            - intros i ??.
              simpl in Hi.
              inv_fin i.
              + intros ??. done.
              + intros i ??.
                inv_fin i.
          }
          rewrite -term_cond_0 //.
        }
        replace #(S m + 1) with #(S (S m)); last first.
        { do 2 f_equal. lia. }
        iApply "IH"; auto.
  Qed.

  Theorem unif_rw_1d_AST  E :
     ⊢ WP unif_rw_1d @ E [{ v, ⌜ True ⌝ }].
  Proof.
    iApply twp_rand_err_pos; auto.
    iIntros (ε Hpos) "Herr".
    assert (0 <= ε) as Hge0 by lra.
    rewrite /unif_rw_1d.
    (* TODO: fix wp_alloctape tactic *)
    wp_apply (twp_alloc_tape); auto.
    iIntros (α) "Hα".
    do 2 wp_pure.
    wp_apply (twp_presample_rsm 1 1 _ _ _ _ (term_cond 1) (mknonnegreal ε Hge0) _ (final_pos_rsm 1) (final_pos 1)); eauto.
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

Theorem unif_rw_1d_AST_external Σ `{erisGpreS Σ} (σ : state) :
  (SeriesC (lim_exec (unif_rw_1d, σ)) = 1)%R.
Proof.
  assert (1 - 0 <= SeriesC (lim_exec (unif_rw_1d, σ)))%R as Haux; last first.
  {
    rewrite Rminus_0_r in Haux.
    apply Rle_antisym; auto.
  }
  eapply (twp_mass_lim_exec _ _ _ _ (fun _ => True)); [lra|].
  iStartProof.
  iIntros (?) "_".
  iApply unif_rw_1d_AST.
Qed.

