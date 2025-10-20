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

  Definition cons_bin_seq (z : fin 2) (f : nat → (fin 2)) : nat → (fin 2) :=
    λ n,
      match n with
      | O => z
      | S n' => f n'
      end.

  Fixpoint append_bin_seq (zs : list (fin 2)) (f : nat → (fin 2)) : nat → (fin 2) :=
    λ n, match zs with
         | nil => f n
         | z :: zs' =>
             match n with
             | O => z
             | S n' => append_bin_seq zs' f n'
             end
         end.


  Lemma cons_bin_seq_inv z1 f1 z2 f2 :
    cons_bin_seq z1 f1 = cons_bin_seq z2 f2 →
    z1 = z2 ∧ f1 = f2.
  Proof.
    intros Heq.
    split.
    - cut (cons_bin_seq z1 f1 O = cons_bin_seq z2 f2 O); first by done.
      rewrite Heq //=.
    - apply functional_extensionality => x.
      cut (cons_bin_seq z1 f1 (S x) = cons_bin_seq z2 f2 (S x)); first by done.
      rewrite Heq //=.
  Qed.

  Lemma bin_seq_hd f :
    ∃ hd f', f = cons_bin_seq hd f'.
  Proof.
    exists (f O), (λ n, f (S n)).
    apply functional_extensionality => x.
    destruct x => //=.
  Qed.

  Lemma append_bin_seq_cons z1 zs f :
    append_bin_seq (z1 :: zs) f = cons_bin_seq z1 (append_bin_seq zs f).
  Proof. rewrite //=. Qed.

  Lemma wp_rand_infinite_tape α f E s :
    {{{ infinite_tape α f }}}
      rand(#lbl:α) #1 @ s; E
    {{{ RET #(LitInt (fin_to_nat (f O))); infinite_tape α (λ n, f (S n)) }}}.
  Proof.
    iIntros (Φ) "Htape HΦ".
    iDestruct "Htape" as (k ns) "(Hα&Hsteps&%Hlt&%Hlookup)".
    destruct ns as [| n ns].
    {
      (* This is the case that we would not be able to handle without
         receipts, i.e. the case when the tape is empty. In that case
         the illusion that we are working with an infinite tape would
         be over. But that cannot happen, because the receipts
         ensure that we stop having to execute steps before the tape
         runs out *)
      simpl in Hlt. lia.
    }
    destruct k as [| k].
    { iApply steps_left_0; auto. }

    iApply (steps_left_decr with "[$] [-]"); first auto.
    wp_apply (wp_rand_tape with "[$]").
    rewrite (Hlookup 0 n) //=.
    iIntros "Htape Hsteps".
    iApply "HΦ".
    iExists k, ns.
    iFrame.
    iPureIntro; split_and!.
    * simpl in Hlt. lia.
    * intros i b Hlookup'.
      apply Hlookup. rewrite lookup_cons //.
  Qed.

  Lemma wp_rand_infinite_tape_cons α z f E s :
    {{{ infinite_tape α (cons_bin_seq z f) }}}
      rand(#lbl:α) #1 @ s; E
    {{{ RET #(LitInt z); infinite_tape α f }}}.
  Proof.
    iIntros (Φ) "Htape HΦ".
    wp_apply (wp_rand_infinite_tape with "[$]").
    iIntros "Htape".
    iApply "HΦ". iApply "Htape".
  Qed.

End infinite_tape.


Section R_approx.

  Import Hierarchy.

  Local Open Scope R_scope.

  Definition seq_bin_to_R (f : nat → (fin 2)) : R :=
    SeriesC (λ n : nat, f n * (1 / 2 ^ (S n))).

  Lemma bin_fin_to_nat_cases (n : fin 2) :
    (fin_to_nat n = 0 ∨ fin_to_nat n = 1)%nat.
  Proof. specialize (fin_to_nat_lt n). lia. Qed.

  Lemma ex_seriesC_seq_bin_to_R_ub :
    ex_seriesC (λ n : nat, 1 / 2 ^ S n).
  Proof.
    eapply (ex_seriesC_ext (λ n, / 2 * (/ 2) ^ n)).
    { intros n. rewrite //=. rewrite /Rdiv Rmult_1_l. rewrite pow_inv. rewrite Rinv_mult. f_equal. }
    eapply (ex_seriesC_scal_l).
    rewrite -ex_seriesC_nat.
    eapply (Series.ex_series_geom (/ 2)).
    rewrite Rabs_right; try nra.
  Qed.

  Lemma ex_seriesC_seq_bin_to_R_ub_shift :
    ex_seriesC (λ n : nat, 1 / 2 ^ (S (S n))).
  Proof.
    rewrite -ex_seriesC_nat -(Series.ex_series_incr_1 (λ n, 1 / 2 ^ S n)) ex_seriesC_nat.
    apply ex_seriesC_seq_bin_to_R_ub.
  Qed.

  Lemma seq_bin_to_R_elem_range (f : nat → fin 2) :
    ∀ n : nat, 0 <= f n * (1 / 2 ^ S n) <= 1 / 2 ^ S n.
  Proof.
    intros n.
      destruct (bin_fin_to_nat_cases (f n)) as [Hzero|Hone].
      * rewrite ?Hzero.
        rewrite Rmult_0_l. split; first nra.
        apply Rcomplements.Rdiv_le_0_compat; first by lra.
        apply pow_lt. nra.
      * rewrite Hone.
        rewrite Rmult_1_l. split; last nra.
        apply Rcomplements.Rdiv_le_0_compat; first by lra.
        apply pow_lt. nra.
  Qed.

  Lemma seq_bin_to_R_elem_nonneg (f : nat → (fin 2)) :
    ∀ n k : nat, 0 <= f n * (1 / 2 ^ k).
  Proof.
    intros n k.
    destruct (bin_fin_to_nat_cases (f n)) as [Hzero|Hone].
    * rewrite ?Hzero Rmult_0_l. nra.
    * rewrite Hone Rmult_1_l.
      apply Rcomplements.Rdiv_le_0_compat; first by lra.
      apply pow_lt. nra.
  Qed.

  Lemma ex_seriesC_seq_bin_to_R (f : nat → (fin 2)) :
    ex_seriesC (λ n : nat, f n * (1 / 2 ^ (S n))).
  Proof.
    eapply (ex_seriesC_le _ (λ n : nat, (1 / 2 ^ (S n)))).
    { apply seq_bin_to_R_elem_range. }
    eapply ex_seriesC_seq_bin_to_R_ub.
  Qed.

  Lemma seq_bin_to_R_range f :
    0 <= seq_bin_to_R f <= 1.
  Proof.
    split.
    - apply SeriesC_ge_0; last eapply ex_seriesC_seq_bin_to_R.
      intros; apply seq_bin_to_R_elem_nonneg.
    - transitivity (SeriesC (λ n : nat, (1 / 2 ^ (S n)))).
      { apply SeriesC_le; first apply seq_bin_to_R_elem_range.
        apply ex_seriesC_seq_bin_to_R_ub. }
      rewrite SeriesC_nat.
      rewrite -(Series.Series_ext (λ n: nat, (1 / 2) * (/ 2) ^ n)); last first.
      { intros n => //=. rewrite pow_inv. field. apply pow_nonzero. nra. }
      rewrite Series.Series_scal_l Series.Series_geom; first nra.
      rewrite Rabs_right; nra.
  Qed.

  Lemma seq_bin_to_R_cons z f :
    seq_bin_to_R (cons_bin_seq z f) = z / 2 + seq_bin_to_R f / 2.
  Proof.
    rewrite /seq_bin_to_R.
    rewrite SeriesC_nat Series.Series_incr_1; last first.
    { rewrite ex_seriesC_nat. apply ex_seriesC_seq_bin_to_R. }
    rewrite /=. f_equal.
    { nra. }
    rewrite /Rdiv.
    rewrite SeriesC_nat.
    rewrite -Series.Series_scal_r.
    eapply Series.Series_ext.
    intros n. field. apply pow_nonzero; nra.
  Qed.

  Lemma seq_bin_to_R_generic_nonneg (f : nat → (fin 2)) g h :
    0 <= Series.Series (λ k : nat, f (g k) * (1 / 2 ^ h k)).
  Proof. eapply series_ge_0 => ?. eapply seq_bin_to_R_elem_nonneg. Qed.

  Lemma seq_bin_to_R_leading0 (f : nat → (fin 2)) :
    fin_to_nat (f O) = O%nat →
    seq_bin_to_R f <= 0.5.
  Proof.
    intros Hleading.
    rewrite /seq_bin_to_R.
    rewrite ?SeriesC_nat Series.Series_incr_1; last first.
    { rewrite ex_seriesC_nat. apply ex_seriesC_seq_bin_to_R. }
    rewrite Hleading ?Rmult_0_l Rplus_0_l.
    transitivity (Series.Series (λ k, (1 / 2 ^ (S (S k))))).
    { eapply Series.Series_le.
      * intros n. eapply (seq_bin_to_R_elem_range).
      * rewrite ex_seriesC_nat; apply ex_seriesC_seq_bin_to_R_ub_shift.
    }
    rewrite //=.
    rewrite -(Series.Series_ext (λ n : nat, (1 / 4) * ( / 2) ^ n)); last first.
    { intros n. rewrite pow_inv. field.
      apply pow_nonzero; nra. }
    rewrite Series.Series_scal_l.
    rewrite Series.Series_geom; last first.
    { rewrite Rabs_right; try nra. }
    nra.
  Qed.

  Lemma seq_bin_to_R_leading1 (f : nat → (fin 2)) :
    fin_to_nat (f O) = 1%nat →
    0.5 <= seq_bin_to_R f.
  Proof.
    intros Hleading.
    rewrite /seq_bin_to_R.
    rewrite ?SeriesC_nat Series.Series_incr_1; last first.
    { rewrite ex_seriesC_nat. apply ex_seriesC_seq_bin_to_R. }
    rewrite Hleading.
    rewrite -(Rplus_0_r 0.5).
    apply Rplus_le_compat.
    { rewrite Rmult_1_l //= Rmult_1_r. nra. }
    eapply seq_bin_to_R_generic_nonneg.
  Qed.

  Definition list_bin_to_seq_bin (l : list (fin 2)) : nat → (fin 2) :=
    λ n, match l !! n with
         | None => Fin.F1
         | Some x => x
         end.

  Notation list_fixed_len A k := { ls : list A | length ls = k}.

  (* Or you could just do this as a fold over the list? *)
  Definition list_bin_to_R (l : list (fin 2)) : R :=
    seq_bin_to_R (list_bin_to_seq_bin l).

  Lemma list_bin_to_R_emp : list_bin_to_R [] = 0.
  Proof.
    rewrite /list_bin_to_R /list_bin_to_seq_bin //= /seq_bin_to_R.
    rewrite SeriesC_scal_l //=. real_solver.
  Qed.

  Definition discrete_approx k f :=
    SeriesC (λ ns : list_fixed_len (fin 2) k,
          (1 / 2 ^ k) * f (list_bin_to_R (proj1_sig ns))).

  Fixpoint list_bin_to_nat' (l : list (fin 2)) : nat :=
    match l with
    | [] => 0
    | a :: l' => a + 2%nat * list_bin_to_nat' l'
    end.
  
  Definition list_bin_to_nat (l : list (fin 2)) : nat := list_bin_to_nat' $ rev l.

  Lemma Rle_0_discrete_approx k f :
    (∀ r, 0 <= r <= 1 → 0 <= f r) →
    0 <= discrete_approx k f.
  Proof.
    rewrite /discrete_approx.
    intros Hle.
    apply SeriesC_ge_0' => ?.
    apply Rmult_le_pos; auto; last first.
    { apply Hle. apply seq_bin_to_R_range. }
    apply Rcomplements.Rdiv_le_0_compat; first by lra.
    apply pow_lt. nra.
  Qed.

  Import SF_seq.

  Lemma foldr_rplus r l : 
    seq.foldr Rplus r l = r + seq.foldr Rplus 0 l.
  Proof.
    induction l => //=; real_solver.
  Qed.

  Definition axxx := enum (list_fixed_len (fin 2) 3%nat).

  Lemma aaxxx : axxx = [].
  Proof.
    rewrite /axxx //=.
  Admitted.

  Lemma discrete_approx_fold k (f : R -> R) : 
    discrete_approx k f = seq.foldr Rplus 0 ((seq.map (λ i : nat, f (i / (2 ^ k)) / 2 ^ k) $ seq.iota 0 (2 ^ k))).
  Proof.
    rewrite /discrete_approx SeriesC_finite_foldr.
    rewrite -(foldr_fmap (λ a, Rplus (1 / 2 ^ k * f(a))) 0 (enum (list_fixed_len (fin 2) k)) (λ v, list_bin_to_R (`v))). 
    rewrite seq.foldr_map -(seq.foldr_map (λ x : nat, x / 2 ^ k) (λ a : R, Rplus (f a / 2 ^ k)) 0 _).
    f_equal; first by apply functional_extensionality => a; f_equal; real_solver.
    replace (λ v : list_fixed_len (fin 2) k, list_bin_to_R (`v)) with ((λ x : nat, x / 2^k) ∘ (λ v : list_fixed_len (fin 2) k, list_bin_to_nat (`v))). 2 : {
      (* rewrite  *)
      apply functional_extensionality => x //=.
      clear. rewrite /list_bin_to_nat /list_bin_to_R /seq_bin_to_R /list_bin_to_seq_bin. 
      destruct k.
      {
        destruct x. destruct x; try inversion e. simpl.
        rewrite SeriesC_0; real_solver.
      }
      destruct x; simpl.

      erewrite (SeriesC_ext _ (λ n, if bool_decide (n ≤ k) then (Rmult (INR (@fin_to_nat (S (S O)) match @lookup nat (Fin.t (S (S O))) (list (Fin.t (S (S O)))) (@list_lookup (Fin.t (S (S O)))) n x return (Fin.t (S (S O))) with | @Some _ x0 => x0 | @None _ => @Fin.F1 (S O) end)) (Rdiv (IZR (Zpos xH)) (Rmult (IZR (Zpos (xO xH))) (pow (IZR (Zpos (xO xH))) n)))) else 0)). 2 : {
        intros. case_bool_decide; auto.
        rewrite lookup_ge_None_2; real_solver.
      }
      rewrite SeriesC_nat_bounded'.
      rewrite -foldr_fmap.
      replace ((2 * 2 ^ k)) with (2 ^ (S k)); try real_solver.
      revert e.
      set k' := S k.
      generalize dependent k'. clear k. revert x.
      induction k'; intros.
      { destruct x; simpl; real_solver. }
      intros. simpl.

      admit.
    }
    rewrite list_fmap_compose. f_equal.
    clear. induction k; auto.
    simpl.
    rewrite seq.iotaD app_nil_r Nat.add_0_r ssrnat.add0n -list_fmap_compose fmap_app -!list_fmap_compose.
    eassert ((λ v : vec (fin 2) (k), _) = list_bin_to_nat) as ->. {
      apply functional_extensionality => x //=.
      rewrite /list_bin_to_nat.
      set l : list (fin 2) := x.
      assert (length l = k). 
      { by rewrite /l vec_to_list_length. }
      generalize dependent l.
      clear. induction k => //=; first by intros; destruct l; auto.
      intros.
      destruct (rev l) eqn : Hrx; auto.
      simpl. f_equal.
      replace (l ++ (cons 0%fin nil)) with (rev (0%fin :: (rev l))). 
      2 : { simpl. by rewrite rev_involutive. }
      rewrite -(rev_involutive l0) IHk; auto.
      rewrite -(rev_involutive l) Hrx //= app_length //= in H.
      lia. 
    }
    eassert ((_ ∘ _ ∘ vcons 1%fin) = (λ x, (2 ^ k) + x)%nat ∘ list_bin_to_nat) as ->. {
      apply functional_extensionality => x //=.
      rewrite /list_bin_to_nat. simpl.
      set l : list (fin 2) := x.
      assert (length l = k). 
      { by rewrite /l vec_to_list_length. }
      generalize dependent l.
      clear. induction k; intros; auto; first by destruct l; auto.
      destruct (rev l) eqn : Hrx; first by rewrite -(rev_involutive l) rev_length Hrx in H. 
      simpl.
      rewrite -(rev_involutive l0) IHk; try lia.
      rewrite -(rev_involutive l) Hrx //= app_length //= in H.
      lia. 
    }
    simpl in IHk. 
    rewrite -IHk. f_equal.
    - rewrite -list_fmap_compose. f_equal. 
    - rewrite list_fmap_compose list_fmap_compose.
      assert (2 ^ k = ssrnat.addn (2^k) 0)%nat; first by rewrite -ssrnat.plusE; lia.  
      rewrite {2}H seq.iotaDl.
      f_equal. rewrite -IHk -!list_fmap_compose. 
      f_equal.
  Admitted.

  Lemma pairmap_intv_pairs (f : nat -> R) n a:
    seq.pairmap (λ x y : nat, (f y, f x)) a%nat (seq.iota (S a) n) = seq.map (λ x, (f x, f (Nat.pred x)))(seq.iota (S a) n).
  Proof.
    revert a.
    induction n; intros; auto. 
    simpl. by rewrite IHn.
  Qed.

  Lemma pairmap_intv_dist_map (f : R -> nat -> R) n a: seq.pairmap (λ x y : nat, f (y - x) (Nat.pred y)) a%nat (seq.iota (S a) n) = seq.map (λ x, f 1 x) (seq.iota a n).
  Proof.
    revert a. induction n; intros; auto.
    simpl. rewrite IHn. do 2 f_equal. 
    destruct a; real_solver.
  Qed.
  
  Lemma discrete_approx_equiv k (f : R → R) :
    discrete_approx k f =
    SF_seq.Riemann_sum f (SF_seq.SF_seq_f2 (λ x y, x) (SF_seq.unif_part 0 1 (2 ^ k - 1))).
  Proof.
    rewrite discrete_approx_fold.
    rewrite /unif_part /Riemann_sum.  
    f_equal. 
    Locate pow_ge_1.
    assert ((seq.mkseq (λ i : nat, 0 + i * (1 - 0) / ((2 ^ k - 1)%nat + 1)) (S (S (2 ^ k - 1)))) = seq.map (λ i : nat, i / 2 ^ k) (seq.iota 0 (S (2 ^ k)))). {
      assert (1 ≤ 2 ^ k); first by apply fin.pow_ge_1; real_solver.
      rewrite /seq.mkseq.
      f_equal; last rewrite Nat.sub_1_r (Nat.lt_succ_pred 0) //=. 
      apply functional_extensionality => x //=. 
      field_simplify; try real_solver.
      f_equal. 
      rewrite minus_INR; auto.
      rewrite pow_INR //=. by field_simplify.
    } 
    rewrite !H.
    rewrite /SF_seq_f2 //=.
    specialize (Rcomplements.pairmap_map (λ x y : R, (y, x)) (λ i : nat, i / 2 ^ k) (seq.iota 1 (2 ^ k)) 0%nat) as Hr.
    simpl in Hr. rewrite Hr.
    clear H Hr.
    rewrite (pairmap_intv_pairs (λ x : nat, x / 2 ^ k) (2 ^ k)). 
    assert (0 = zero) as <-; auto.
    specialize (Rcomplements.pairmap_map (λ x y : R * R, scal (y.1 - x.1) (f y.2)) (λ x : nat, (x / 2 ^ k, Nat.pred x / 2 ^ k)) (seq.iota 1 (2 ^ k)) 0%nat) as Hr.
    simpl in Hr.
    assert (0 / 2 ^ k = 0); try real_solver.
    rewrite H in Hr. rewrite H.
    rewrite Hr /scal //= /mult //=.
    specialize (pairmap_intv_dist_map (λ a b, a * f (b / 2 ^ k) / 2 ^ k) (2 ^ k) 0) as Hl.
    simpl in Hl. 
    replace (λ i : nat, f (i / 2 ^ k) / 2 ^ k) with (λ i : nat, 1 * f (i / 2 ^ k) / 2 ^ k); last by apply functional_extensionality; real_solver.
    rewrite -Hl.
    f_equal.
    apply functional_extensionality => x. apply functional_extensionality => y.
    field_simplify; real_solver.
  Qed.

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

  (* Probably one would not want to use this predicate, but rather
     work with a predicate for a version that memoizes the bits that
     have been sampled so far *)
  Definition unif_tape α (mr : option R) : iProp Σ :=
    match mr with
    | None => α ↪ (1; [])
    | Some r =>
        ∃ f, infinite_tape α f ∗ ⌜ seq_bin_to_R f = r ⌝
  end.

  Import Hierarchy.

  Lemma wp_presample_unif_adv_comp E e α Φ (ε1 : R) (ε2 : R -> R) :
    to_val e = None →
    (forall r, 0 <= r <= 1 → (0 <= ε2 r)%R) ->
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
    { intros. apply Hle. apply seq_bin_to_R_range. }
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

  Lemma wp_rand_unif_tape_lt_half α r E s :
    r < 0.5 →
    {{{ unif_tape α (Some r) }}}
      rand(#lbl:α) #1 @ s; E
    {{{ RET #(LitInt 0); unif_tape α (Some (2 * r)) }}}.
  Proof.
    iIntros (Hr Φ) "Htape HΦ".
    rewrite /unif_tape.
    iDestruct "Htape" as (f) "(Htape&%Hf)".
    wp_apply (wp_rand_infinite_tape with "[$]").
    iIntros "Htape".
    rewrite /seq_bin_to_R in Hf.
    destruct (bin_fin_to_nat_cases (f O)) as [Hzero|Hone].
    - rewrite Hzero. iApply "HΦ".
      iExists _. iFrame "Htape".
      iPureIntro.
      rewrite /seq_bin_to_R -Hf.
      rewrite ?SeriesC_nat.
      symmetry. rewrite Series.Series_incr_1_aux; last first.
      { rewrite Hzero. rewrite Rmult_0_l //. }
      rewrite -Series.Series_scal_l.
      eapply Series.Series_ext.
      intros n.
      rewrite //=. field.
      apply pow_nonzero; nra.
    - exfalso.
      specialize (seq_bin_to_R_leading1 f Hone).
      rewrite /seq_bin_to_R.
      intros. nra.
  Qed.

  Lemma wp_rand_unif_tape_gt_half α r E s :
    0.5 < r →
    {{{ unif_tape α (Some r) }}}
      rand(#lbl:α) #1 @ s; E
    {{{ RET #(LitInt 1); unif_tape α (Some (2 * r - 1)) }}}.
  Proof.
    iIntros (Hr Φ) "Htape HΦ".
    rewrite /unif_tape.
    iDestruct "Htape" as (f) "(Htape&%Hf)".
    wp_apply (wp_rand_infinite_tape with "[$]").
    iIntros "Htape".
    rewrite /seq_bin_to_R in Hf.
    destruct (bin_fin_to_nat_cases (f O)) as [Hzero|Hone].
    - exfalso.
      specialize (seq_bin_to_R_leading0 f Hzero).
      rewrite /seq_bin_to_R.
      intros. nra.
    - rewrite Hone. iApply "HΦ".
      iExists _. iFrame "Htape".
      iPureIntro.
      rewrite /seq_bin_to_R -Hf.
      rewrite ?SeriesC_nat.
      symmetry. rewrite Series.Series_incr_1; last first.
      { rewrite ex_seriesC_nat. apply ex_seriesC_seq_bin_to_R. }
      rewrite Hone.
      ring_simplify.
      replace (2 * 1%nat * (1 / 2 ^ 1)) with 1; last first.
      { rewrite //=. nra.  }
      ring_simplify.
      rewrite -Series.Series_scal_l.
      eapply Series.Series_ext.
      intros n.
      rewrite //=. field.
      apply pow_nonzero; nra.
  Qed.

  (* This is probably not so useful?, also tremendous redundancy
     between two previous proofs. probably better to do things in
     terms of 1 lemma that says if returned was 0, then r was <= .5
     and now you have 2 r, otherwise >= .5 and now you have 2 r - 1.
     *)
  Lemma wp_rand_unif_tape_eq_half α r E s :
    r = 0.5 →
    {{{ unif_tape α (Some r) }}}
      rand(#lbl:α) #1 @ s; E
    {{{ z, RET #(LitInt z); (⌜ z = O ⌝ ∗ unif_tape α (Some 1)) ∨ (⌜ z = 1 ⌝%nat ∗ unif_tape α (Some 0)) }}}.
  Proof.
    iIntros (Hr Φ) "Htape HΦ".
    rewrite /unif_tape.
    iDestruct "Htape" as (f) "(Htape&%Hf)".
    wp_apply (wp_rand_infinite_tape with "[$]").
    iIntros "Htape".
    rewrite /seq_bin_to_R in Hf.
    destruct (bin_fin_to_nat_cases (f O)) as [Hzero|Hone].
    - rewrite Hzero. iApply "HΦ".
      iLeft. iSplit; first done. iExists _. iFrame "Htape".
      iPureIntro.
      replace 1 with (2 * r); last first.
      { nra. }
      rewrite /seq_bin_to_R -Hf.
      rewrite ?SeriesC_nat.
      symmetry. rewrite Series.Series_incr_1_aux; last first.
      { rewrite Hzero. rewrite Rmult_0_l //. }
      rewrite -Series.Series_scal_l.
      eapply Series.Series_ext.
      intros n.
      rewrite //=. field.
      apply pow_nonzero; nra.
    - rewrite Hone. iApply "HΦ".
      iRight. iSplit; first by auto.
      iExists _. iFrame "Htape".
      iPureIntro.
      replace 0 with (2 * r - 1); last first.
      { nra. }
      rewrite /seq_bin_to_R -Hf.
      rewrite ?SeriesC_nat.
      symmetry. rewrite Series.Series_incr_1; last first.
      { rewrite ex_seriesC_nat. apply ex_seriesC_seq_bin_to_R. }
      rewrite Hone.
      ring_simplify.
      replace (2 * 1%nat * (1 / 2 ^ 1)) with 1; last first.
      { rewrite //=. nra.  }
      rewrite -Series.Series_scal_l.
      ring_simplify.
      eapply Series.Series_ext.
      intros n.
      rewrite //=. field.
      apply pow_nonzero; nra.
  Qed.

End unif_tape.
