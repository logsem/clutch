From clutch.eris Require Export eris.
Import Hierarchy.

From mathcomp Require ssrnat.
From mathcomp Require Import div prime zmodp finset fintype ssrbool fingroup.fingroup solvable.cyclic.



Section miller_rabin_code.


  Context `{!erisGS Σ}.

  (*
    The Miller-Rabin test is a probabilistic test for primality, that
    always returns true for prime numbers, and it returns false for
    composite numbers with probability at least 1/2.

    It relies on two properties:
    - Fermat's little theorem: for every prime p, and every (0 < x < p),
      x ^ (p - 1) = 1 mod p

    - For every prime p, the equation
       x ^ 2 = 1 mod p
      only has solutions {1, p-1} in (0 < x < p)

    The algorithm receives an input m to test for primality, we assume
    w.l.o.g that m is odd. Therefore, m - 1 = 2^t * u for some t, u
    with u odd. Miller-Rabin's test samples x s.t. (0 < x < p), and
    computes the sequence (modulo m):

     x ^ u , x ^ (2 * u), x ^ (2^2 * u), ..., x ^ (2^(t-1) * u)

    checking if any of the two conditions above is violated. For this
    it is enough to check that x ^ u ≠ 1 mod m, and that, for all 0 ≤ k < t,
    x ^ (2^k * u) ≠ m - 1 (mod m). In that case, we say x is a Miller-Rabin witness,
    and m must be composite. Conversely, if m is prime, we know that
    x ^ (2^t * u) = 1 mod m, so either the entire sequence is constantly 1,
    including x ^ u, or one of the elemets is m - 1.

    A known result states that, for every composite m, at least half of
    the elements in (0 < x < m-1) are Miller-Rabin witnesses. This is due to
    the fact that there is a proper subgroup G of the group of multiplicative
    inverses (Z_m)^* containing all Miller-Rabin non-witnesses, so their
    cardinality is at most |(Z_m)^*|/2.

  *)



  Notation "e1 || e2" := (BinOp OrOp e1%E e2%E) : expr_scope.

  (*
     Takes an integer n and returns a pair
     u, t with n = (2^t) u, and u odd
  *)

  Definition power_two_decomp :=
    (rec: "g" "n" :=
      if: "n" `rem` #2 = #1 then
          ("n", #0)
      else
        let, ("u", "t") := "g" ("n" `quot` #2) in
        ("u", "t" + #1))%V.


 (*
     Computes b^e mod m using repeated squaring
 *)


  Definition fast_mod_exp :=
    (rec: "g" "b" "e" "m" :=
      if: "e" = #0 then #1
      else
        let: "r" := "g" ( ("b" * "b") `rem` "m") ("e" `quot` #2) "m" in
        if: "e" `rem` #2 = #0
        then "r"
        else ("b" * "r") `rem` "m")%V.


  (*
      Auxiliary function for a Miller-Rabin round.
      Computes the sequence (modulo m):
      y , y^2, ..., y^(t-1)

      and returns true iff any element is m-1
  *)

  Definition MR_round_aux : val :=
    (rec: "g" "y" "m" "t" :=
       if: "t" = #0 then #false
       else
         if: "y" = "m" - #1 then #true
         else "g" (("y" * "y") `rem` "m") "m" ("t" - #1))%V.


  (*
    Testing a potential witness 1 < x < m
    where m-1 can be decomposed as 2^t u
  *)

  Definition MR_round : val :=
    (λ: "m" "t" "u",
      let: "x" := #1 + rand ("m" - #2) in
      let: "y" := (fast_mod_exp "x" "u" "m") in
      if: "y" = #1 then #true
      else
        MR_round_aux "y" "m" "t")%V.


  (*
    The main function for the Miller-Rabin
    test where only 1 iteration is performed
  *)

  Definition MR_main : val :=
    (λ: "m",
      if: "m" ≤ #1 then #false
      else
        let, ("u", "t") := power_two_decomp ("m" - #1) in
        MR_round "m" "t" "u")%V.




  Definition is_MR_nonwitness (t u x : Z) : bool :=
    ( x^u `mod` (2^t * u + 1) =? 1 `mod` (2^t * u + 1))%Z ||
      (List.existsb (λ i:nat,
           (x^((2^i * u)) `mod` (2^t * u + 1) =? (2^t * u) `mod` (2^t * u + 1))%Z) (seq 0 (Z.to_nat t))).

  Definition MR_nonwitness (m t u x : Z) : Prop :=
    (m = 2^t * u + 1)%Z /\
    (Z.Odd u) /\
    (1 <= x < m )%Z /\
    ( x^u `mod` m = 1 `mod` m)%Z \/
      (exists (i : Z), 0 <= i < t /\
                    x^(2^i * u) `mod` m = (m-1) `mod` m )%Z.


  Definition MR_witness (m t u x : Z) : Prop :=
    (m = 2^t * u + 1)%Z /\
    (Z.Odd u) /\
    (1 <= x < m )%Z /\
      ( x^u `mod` m ≠ 1 `mod` m)%Z /\
      (forall (i : Z), 0 <= i < t ->
                  x^(2^i * u) `mod` m ≠ (m-1) `mod` m )%Z.


  (* These two lemmas need some group theory, but should
     be available in standard textbooks, e.g Cormen et al *)

  Lemma MR_witness_card (m t u : Z) :
    ¬ Znumtheory.prime m ->
    (m = 2^t * u + 1)%Z ->
    Z.Odd u ->
    length (List.filter (λ x : nat, is_MR_nonwitness t u (1 + x)) (seq 0 (Z.to_nat (m - 1)))) <= (IZR(m-1)) / 2.
  Admitted.

  Lemma fermat_little (p t u x : Z) :
    Znumtheory.prime p ->
    (p = 2^t * u + 1)%Z ->
    Z.Odd u ->
    (0 <= x < p)%Z ->
    MR_nonwitness p t u x.
  Admitted.

  Lemma is_MR_nonwitness_false (m t u x : Z) :
    (0 <= t)%Z ->
    (1 <= u)%Z ->
    (m = 2^t * u + 1)%Z ->
    (Z.Odd u) ->
    (1 <= x < m )%Z ->
    (is_MR_nonwitness t u x = false) ->
    MR_witness m t u x.
  Proof.
    rewrite /is_MR_nonwitness.
    intros Ht Hu Heq Hodd Hm Hwit.
    apply orb_false_elim in Hwit as [Hwit1 Hwit2].
    apply Z.eqb_neq in Hwit1.
    rewrite /MR_witness.
    split; auto.
    split; auto.
    split; auto.
    split.
    - rewrite Heq //.
    - intros i Hi1 Hi2.
      eapply (@existsb_nth _ _ _ (Z.to_nat i) 0%nat ) in Hwit2.
      * apply Z.eqb_neq in Hwit2.
        apply Hwit2.
        assert (nth (Z.to_nat i) (seq 0 (Z.to_nat t)) 0%nat = (Z.to_nat i)) as ->; auto.
        { simpl.
          rewrite seq_nth; auto.
          lia.
        }
        rewrite Heq in Hi2.
        rewrite Z2Nat.id; last by lia.
        rewrite Hi2.
        f_equal. lia.
      * rewrite seq_length. lia.
  Qed.


  Lemma is_MR_nonwitness_true (m t u x : Z) :
    (0 <= t)%Z ->
    (1 <= u)%Z ->
    (m = 2^t * u + 1)%Z ->
    (Z.Odd u) ->
    (1 <= x < m )%Z ->
    (is_MR_nonwitness t u x = true) ->
    MR_nonwitness m t u x.
  Proof.
    rewrite /is_MR_nonwitness.
    rewrite /MR_nonwitness.
    intros Ht Hu Heq Hodd Hm Hwit.
    apply orb_true_elim in Hwit as [Hwit1 | Hwit2].
    - left.
      apply Z.eqb_eq in Hwit1.
      rewrite /MR_witness.
      split; auto.
      split; auto.
      split; auto.
      rewrite Heq //.
    - right.
      apply existsb_exists in Hwit2 as [i [Hi1 Hi2]].
      exists i; split.
      + apply in_seq in Hi1. lia.
      + rewrite Heq.
        apply Z.eqb_eq in Hi2.
        rewrite Hi2.
        f_equal.
        lia.
  Qed.



  Lemma power_two_decomp_correct (n : Z) E :
    {{{ ⌜ (0 < n)%Z ⌝ }}}
      power_two_decomp #n @ E
    {{{ (u : Z) (t : Z), RET (#u, #t)%V;
        ⌜ (n = 2^t * u)%Z  /\ (0 <= t)%Z /\ Z.Odd u⌝ }}}.
  Proof.
    iLöb as "IH" forall (n).
    iIntros (Φ Hpos) "HΦ".
    wp_rec.
    wp_pures.
    case_bool_decide.
    - wp_pures.
      iModIntro.
      iApply "HΦ".
      iPureIntro.
      split; try lia.
      split; try lia.
      unfold Z.Odd.
      eexists.
      rewrite Z.rem_mod_nonneg in H; try lia.
      inversion H.
      rewrite {1}(Z_div_mod_eq_full n 2); auto.
    - wp_pures.
      wp_bind (power_two_decomp _).
      iApply ("IH" $! _ _ _ ).
      Unshelve.
      2:{
        apply Z.quot_str_pos.
        assert (n ≠ 1)%Z; [| try lia].
        intros ->.
        apply H.
        do 2 f_equal.
      }
      iIntros "!>" (u t') "[%Ht'1 [%Ht'2 %Ht'3]]".
      wp_pures.
      iApply "HΦ".
      iModIntro.
      iPureIntro.
      split; [ | split; auto; lia].
      rewrite Zpower_exp; try lia.
      rewrite -Z.mul_assoc (Z.mul_comm _ u) Z.mul_assoc -Ht'1.
      rewrite Z.quot_div_nonneg; try lia.
      rewrite Z.pow_1_r Z.mul_comm.
      rewrite {1}(Z_div_mod_eq_full n 2).
      assert (n `mod` 2 = 0)%Z; [|lia].
      rewrite Z.rem_mod_nonneg in H; try lia.
      epose proof (Z.mod_pos_bound n 2) as [? ?]; try lia.
      assert ((n `mod` 2)%Z ≠ 1%Z); try lia.
      intro. apply H.
      do 2 f_equal.
      done.
  Qed.


  Lemma fast_mod_exp_correct (b e m : Z) E :
    {{{ ⌜ (0 <= b /\ 0 <= e /\ 1 < m)%Z ⌝ }}}
      fast_mod_exp #b #e #m @ E
      {{{ (r : Z) , RET #r;
          ⌜  (0 <= r < m)%Z /\ (b^e `mod` m = r)%Z ⌝ }}}.
  Proof.
    iLöb as "IH" forall (b e m).
    iIntros (Φ Hpos) "HΦ".
    wp_rec.
    wp_pures.
    case_bool_decide.
    - wp_pures.
      iModIntro.
      iApply "HΦ".
      iPureIntro.
      split; try lia.
      replace e with 0%Z; last first.
      { by inversion H. }
      simpl.
      rewrite Z.pow_0_r Z.mod_1_l; lia.
    - wp_pures.
      wp_bind (fast_mod_exp _ _ _).
      iApply ("IH" $! _ _ _).
      + iPureIntro.
        split.
        * apply Z.rem_nonneg; lia.
        * split; [|lia].
          apply Z.quot_pos; lia.
      + iIntros "!>" (r) "[%Hr1 %Hr2]".
        wp_pures.
        case_bool_decide as H0.
        * wp_pures.
          iModIntro.
          iApply "HΦ".
          iPureIntro.
          split; auto.
          rewrite <- Hr2.
          rewrite Z.quot_div_nonneg; try lia.
          rewrite Z.rem_mod_nonneg; try lia.
          rewrite -Zpow_facts.Zpower_mod; [ | lia].
          rewrite -Z.pow_2_r.
          rewrite -Z.pow_mul_r; try lia; [ | apply Z.div_pos; lia].
          assert (2 * e `div` 2 = e)%Z as ->; auto.
          rewrite {2}(Z_div_mod_eq_full e 2).
          rewrite -Z.rem_mod_nonneg; try lia.
          inversion H0. lia.
        * wp_pures.
          iModIntro.
          iApply "HΦ".
          iPureIntro.
          split; [apply Z.rem_bound_pos_pos; lia | ].
          rewrite <- Hr2.
          rewrite Z.quot_div_nonneg; try lia.
          rewrite Z.rem_mod_nonneg; try lia; last first.
          {
            apply Z.mul_nonneg_nonneg; [lia | ].
            apply Z_mod_nonneg_nonneg; [|lia].
            apply Z.pow_nonneg.
            apply Z.rem_nonneg; lia.
          }
          rewrite Z.rem_mod_nonneg; try lia.
          rewrite -Zpow_facts.Zpower_mod; [ | lia].
          rewrite -Z.pow_2_r.
          rewrite -Z.pow_mul_r; try lia; [ | apply Z.div_pos; lia].
          rewrite Zmult_mod.
          rewrite Zmult_mod_idemp_r.
          rewrite -Zmult_mod.
          rewrite <- (Z.pow_1_r b) at 2.
          rewrite -Zpower_exp; try lia.
          ** rewrite Z.add_comm.
             rewrite {1}(Z_div_mod_eq_full e 2).
             do 3 f_equal.
             rewrite Z.rem_mod_nonneg in H0; try lia.
             epose proof (Z.mod_pos_bound e 2) as [? ?]; try lia.
             assert ((e `mod` 2)%Z ≠ 0%Z); try lia.
             intro. apply H0.
             do 2 f_equal; auto.
         ** apply Z.le_ge.
            apply Z.mul_nonneg_nonneg; [lia |].
            apply Z_div_pos; lia.
  Qed.




  Lemma MR_round_aux_correct_aux (y m t : Z) E :
      {{{ ⌜ (0 <= y < m /\ 1 < m /\ 0 <= t)%Z ⌝ }}}
        MR_round_aux #y #m #t @ E
        {{{ (b : bool) , RET #b;
            ⌜ b  <-> exists i: Z, (0 <= i < t /\ y ^ (2^i) `mod` m = (m - 1) `mod` m)%Z  ⌝ }}}.
  Proof.
    iIntros (Φ (Hym & Hm & Ht)) "HΦ".
    rewrite -(Z2Nat.id t); auto.
    iInduction (Z.to_nat t) as [|t'] "IH" forall (y m Φ Hym Hm Ht).
    - wp_rec.
      wp_pures.
      iModIntro.
      iApply "HΦ".
      iPureIntro.
      split; auto.
      + intro. done.
      + simpl.
        intros (i & Hi). lia.
    - wp_rec.
      wp_pures.
      case_bool_decide.
      + wp_pures.
        iApply "HΦ".
        iModIntro.
        iPureIntro.
        split; auto.
        intro.
        exists 0%nat.
        simpl.
        split.
        * lia.
        * inversion H as [H2].
          rewrite -H2.
          f_equal.
          lia.
      + wp_pures.
        replace #(S t' - 1) with #t'; last first.
        { do 2 f_equal. lia. }
        iApply ("IH" $! _ _ _).
        * iPureIntro.
          apply Z.rem_bound_pos; lia.
        * iPureIntro. done.
        * iPureIntro. done.
        * iIntros "!>" (b) "%H1".
          iApply "HΦ".
          iPureIntro.
          etransitivity; [apply H1 | ].
          split; intros (x & Hx1 & Hx2).
          ** exists (x + 1)%Z.
             split.
             *** lia.
             *** rewrite -Hx2.
                 rewrite Z.rem_mod_nonneg; try lia.
                 rewrite -Zpow_facts.Zpower_mod; [ | lia].
                 f_equal.
                 rewrite -Z.pow_2_r -Z.pow_mul_r; try lia.
                 f_equal.
                 rewrite Z.pow_add_r; lia.
          **
             assert (x ≠ 0)%Z as Hx3.
             {
               intros ->.
               rewrite Z.pow_0_r Z.pow_1_r in Hx2.
               rewrite Z.mod_small in Hx2; [ |lia].
               rewrite Z.mod_small in Hx2; [ |lia].
               simplify_eq.
             }
             exists (x-1)%Z.
             split; [lia |].
             rewrite -Hx2.
                 rewrite Z.rem_mod_nonneg; try lia.
                 rewrite -Zpow_facts.Zpower_mod; [ | lia].
                 f_equal.
                 rewrite -Z.pow_2_r -Z.pow_mul_r; try lia.
                 f_equal.
                 rewrite -{1}(Z.pow_1_r 2).
                 rewrite -Z.pow_add_r; try lia.
                 f_equal. lia.
  Qed.



  Lemma MR_round_aux_correct_nonwit (x m t u: Z) E :
    {{{ ⌜ (1 < m)%Z /\ (0 <= t)%Z /\ (0 <= u)%Z /\ (x ^ u `mod` m ≠ 1)%Z /\ MR_nonwitness m t u x ⌝ }}}
      MR_round_aux #(x ^ u `mod` m) #m #t @ E
      {{{ (b : bool) , RET #b;
          ⌜  b = true  ⌝ }}}.
  Proof.
    rewrite /MR_nonwitness.
    iIntros (Φ (Hm & Ht & Hu & Hneq & H2)) "HΦ".
    destruct H2 as [H3 | [i [Hi1 Hi2]]] .
    {
      exfalso.
      apply Hneq.
      destruct H3 as (?&?&?&->).
      rewrite Z.mod_1_l; lia.
    }
    wp_apply MR_round_aux_correct_aux; auto.
    { iPureIntro.
      split; try lia.
      apply Z.mod_pos_bound; lia.
    }
    iIntros (b) "%Hb".
    iApply "HΦ".
    iPureIntro.
    apply Is_true_true, Hb.
    exists i.
    split; auto.
    rewrite -Hi2.
    rewrite -Zpow_facts.Zpower_mod; [|lia].
    f_equal.
    rewrite -Z.pow_mul_r; try lia.
    f_equal. lia.
  Qed.


  Lemma MR_round_aux_correct_wit (x m t u: Z) E :
    {{{ ⌜ (1 < m)%Z /\ (0 <= t)%Z /\ (0 <= u)%Z /\ (x ^ u `mod` m ≠ 1)%Z /\ MR_witness m t u x ⌝ }}}
      MR_round_aux #(x ^ u `mod` m) #m #t @ E
      {{{ (b : bool) , RET #b;
          ⌜  b = false  ⌝ }}}.
  Proof.
    rewrite /MR_witness.
    iIntros (Φ (Hm & Ht & Hu & Hneq & H2)) "HΦ".
    wp_apply MR_round_aux_correct_aux; auto.
    { iPureIntro.
      split; try lia.
      apply Z.mod_pos_bound; lia.
    }
    iIntros (b) "%Hb".
    iApply "HΦ".
    iPureIntro.
    apply Is_true_false.
    apply neg_false.
    etrans; eauto.
    split; [|done].
    intros (i & Hi1 & Hi2).
    destruct H2 as (?&?&?&?&Hi3).
    apply (Hi3 i); auto.
    rewrite -Hi2.
    rewrite -Zpow_facts.Zpower_mod; [|lia].
    f_equal.
    rewrite -Z.pow_mul_r; try lia.
    f_equal. lia.
  Qed.

  Lemma MR_round_correct_prime (m t u : Z) E :
    {{{ ⌜(1 < m)%Z /\ (0 <= t)%Z /\
          (m = 2^t * u + 1 /\ 0 <= u /\ Z.Odd u )%Z /\ Znumtheory.prime m ⌝ }}}
      MR_round #m #t #u @ E
      {{{ (b : bool) , RET #b;
          ⌜ (b = true) ⌝ }}}.
  Proof.
    iIntros (Φ (Hm & Ht & (Heq & (Hpos & Hodd)) & Hprime)) "HΦ".
    wp_rec.
    wp_pures.
    wp_bind (rand _)%E.
    wp_apply wp_rand; auto.
    iIntros (x) "?".
    wp_pures.
    wp_bind (fast_mod_exp _ _ _).
    wp_apply (fast_mod_exp_correct); auto.
    {
      iPureIntro.
      split; lia.
    }
    iIntros (y) "[% <-]".
    wp_pures.
    case_bool_decide.
    - wp_pures.
      iApply "HΦ". done.
    - wp_pures.
      assert (0 ≤ 1 + x < m)%Z as Haux.
      { split; try lia.
        pose proof (fin_to_nat_lt x).
        lia.
      }
      simpl.
      wp_apply MR_round_aux_correct_nonwit; auto.
      iPureIntro.
      split; [lia |].
      split; [lia |].
      split; [lia |].
      split.
      + intro.
        apply H0.
        do 2 f_equal. done.
      + apply fermat_little; auto.
  Qed.


  Lemma MR_round_composite_error (m t u : Z) E :
    {{{ ⌜(1 < m)%Z /\ (0 <= t)%Z /\
          (m = 2^t * u + 1 /\ 0 <= u /\ Z.Odd u )%Z /\ ¬ Znumtheory.prime m ⌝ ∗
       € (nnreal_div (nnreal_nat 1) (nnreal_nat 2))}}}
      MR_round #m #t #u @ E
      {{{ (b : bool) , RET #b;
          ⌜ (b = false) ⌝ }}}.
  Proof.
    iIntros (Φ) "((%Hm & %Ht & (%Heq & (%Hpos & %Hodd)) & %Hcomp )& Herr) HΦ".
    wp_rec.
    wp_pures.
    wp_bind (rand _)%E.
    wp_apply (wp_rand_err_filter _ _ ((λ x, is_MR_nonwitness t u (1 + x)))) ; auto.
    iSplitL "Herr".
    {
      iApply ec_weaken; last by iFrame.
      replace (S (Z.to_nat (m - 2))) with (Z.to_nat (m-1)); last first.
      {
        rewrite -Z2Nat.inj_succ; last by lia.
        f_equal. lia.
      }
      simpl.
      apply (Rcomplements.Rle_div_l).
      - rewrite plus_INR.
        rewrite Z2Nat.inj_sub; last by lia.
        rewrite minus_INR; last by lia.
        simpl.
        replace (Z.to_nat m - (1 + 1) + 1) with (Z.to_nat m - 1) by lra.
        rewrite INR_IZR_INZ.
        rewrite Z2Nat.id; last by lia.
        apply Rlt_gt.
        apply IZR_lt in Hm. lra.
      - pose proof (MR_witness_card m) as Haux.
        etrans; eauto.
        rewrite Z2Nat.inj_sub; last by lia.
        replace (1+1) with 2 by lra.
        rewrite Rmult_1_l.
        rewrite Rmult_comm.
        rewrite Rdiv_def.
        apply Rmult_le_compat_r.
        {
          left. apply Rinv_0_lt_compat; lra.
        }
        rewrite plus_INR minus_INR.
        + rewrite minus_IZR.
          simpl.
          replace (Z.to_nat m - (1 + 1) + 1) with (Z.to_nat m - 1) by lra.
          rewrite INR_IZR_INZ.
          rewrite Z2Nat.id; last by lia.
          done.
        + lia.
     }
    iIntros (x) "%Hwit".
    wp_pures.
    wp_bind (fast_mod_exp _ _ _).
    wp_apply (fast_mod_exp_correct); auto.
    {
      iPureIntro.
      split; lia.
    }
    iIntros (y) "[% <-]".
    wp_pures.
    apply (is_MR_nonwitness_false m t u) in Hwit; auto; try lia.
    2:{
      pose proof (fin_to_nat_lt x).
      split; lia.
    }
    case_bool_decide.
    - wp_pures.
      iApply "HΦ". exfalso.
      rewrite /MR_witness in Hwit.
      destruct Hwit as (?&?&?&Hx1&Hx2).
      apply Hx1.
      assert ((1 + x)^u `mod` m = 1)%Z as ->.
      {
        inversion H0.
        rewrite H5. auto.
      }
      rewrite Zmod_1_l; auto.
    - wp_pures.
      wp_apply MR_round_aux_correct_wit; auto.
      iPureIntro.
      split; [lia |].
      split; [lia |].
      split; [lia |].
      split; auto.
      intro.
      apply H0.
      do 2 f_equal. done.
  Qed.


  Lemma MR_round_composite_error_amplify (m t u : Z) (ε : nonnegreal) E :
    {{{ ⌜(1 < m)%Z /\ (0 <= t)%Z /\
          (m = 2^t * u + 1 /\ 0 <= u /\ Z.Odd u )%Z /\ ¬ Znumtheory.prime m ⌝ ∗
       € ε }}}
      MR_round #m #t #u @ E
      {{{ (b : bool) , RET #b;
          ⌜ (b = false) ⌝ ∨ ( € (nnreal_mult (nnreal_nat 2) ε) ) }}}.
  Proof.
    iIntros (Φ) "((%Hm & %Ht & (%Heq & (%Hpos & %Hodd)) & %Hcomp )& Herr) HΦ".
    wp_rec.
    wp_pures.
    wp_bind (rand _)%E.
    wp_apply (wp_rand_err_filter_adv _ _ (λ x, is_MR_nonwitness t u (1 + x)) ε (nnreal_mult (nnreal_nat 2) ε)); eauto.
    {
      replace (S (Z.to_nat (m - 2))) with (Z.to_nat (m-1)); last first.
      {
        rewrite -Z2Nat.inj_succ; last by lia.
        f_equal. lia.
      }
      simpl.
      rewrite Rmult_assoc Rmult_comm Rmult_assoc.
      apply Rmult_le_compat_l; [apply cond_nonneg| ].
      pose proof (MR_witness_card m) as Haux.
      apply Rcomplements.Rle_div_r; [lra |].
      etrans; eauto.
      rewrite Z2Nat.inj_sub; last by lia.
      replace (1+1) with 2 by lra.
      rewrite /Rdiv.
      apply Rmult_le_compat_r; [lra |].
      replace ((Z.to_nat m - Z.to_nat 2)%nat + 1) with (IZR m - 1); [rewrite minus_IZR; lra |].
      rewrite INR_IZR_INZ.
      rewrite -plus_IZR.
      rewrite -minus_IZR.
      f_equal. lia.
    }
    iFrame.
    iIntros (x) "[%Hcont1 | Hcont2]".
    - wp_pures.
      wp_bind (fast_mod_exp _ _ _).
    wp_apply (fast_mod_exp_correct); auto.
    {
      iPureIntro.
      split; lia.
    }
    iIntros (y) "[% <-]".
    wp_pures.
    apply (is_MR_nonwitness_false m t u) in Hcont1; auto; try lia.
    2:{
      pose proof (fin_to_nat_lt x).
      split; lia.
    }
    case_bool_decide.
    + wp_pures.
      iApply "HΦ". exfalso.
      rewrite /MR_witness in Hcont1.
      destruct Hcont1 as (?&?&?&Hx1&Hx2).
      apply Hx1.
      assert ((1 + x)^u `mod` m = 1)%Z as ->.
      {
        inversion H0.
        rewrite H5. auto.
      }
      rewrite Zmod_1_l; auto.
    + wp_pures.
      wp_apply MR_round_aux_correct_wit.
      2:{ iIntros. iApply "HΦ". iLeft. done. }
      iPureIntro.
      split; [lia |].
      split; [lia |].
      split; [lia |].
      split; auto.
      intro.
      apply H0.
      do 2 f_equal. done.

    - iAssert (∀ b:bool, Φ #b)%I with "[HΦ Hcont2]" as "HΦ".
      {
        iIntros (b).
        iApply "HΦ".
        iRight.
      iApply ec_weaken; last by iFrame.

      replace (S (Z.to_nat (m - 2))) with (Z.to_nat (m-1)); last first.
      {
        rewrite -Z2Nat.inj_succ; last by lia.
        f_equal. lia.
      }
      simpl. lra.
     }
      wp_pures.
      wp_bind (fast_mod_exp _ _ _).
      wp_apply (fast_mod_exp_correct); auto.
      {
        iPureIntro.
        split; lia.
      }
      iIntros (y) "[% <-]".
      wp_pures.
      case_bool_decide.
      + wp_pures. auto.
      + wp_pures.
        destruct (is_MR_nonwitness t u (1 + x)) eqn:Hwit.
        * wp_apply MR_round_aux_correct_nonwit; auto.
          iPureIntro.
          split; [lia |].
          split; [lia |].
          split; [lia |].
          split.
          ** intro. apply H0. do 2 f_equal. done.
          ** apply is_MR_nonwitness_true; auto; try lia.
             pose proof (fin_to_nat_lt x).
             split; lia.
        * wp_apply MR_round_aux_correct_wit; auto.
          iPureIntro.
          split; [lia |].
          split; [lia |].
          split; [lia |].
          split.
          ** intro. apply H0. do 2 f_equal. done.
          ** apply is_MR_nonwitness_false; auto; try lia.
             pose proof (fin_to_nat_lt x).
             split; lia.
  Qed.


  Lemma MR_main_correct_prime (m : Z) E :
    {{{ ⌜ Znumtheory.prime m ⌝ }}}
      MR_main #m @ E
      {{{ (b : bool) , RET #b;
          ⌜ (b = true) ⌝ }}}.
  Proof.
    iIntros (Φ Hprime) "HΦ".
    assert (1 < m)%Z as Hm.
    {
      destruct Hprime; auto.
    }
    wp_rec.
    wp_pures.
    case_bool_decide; first by lia.
    wp_pures.
    wp_bind (power_two_decomp _).
    wp_apply (power_two_decomp_correct).
    { iPureIntro; lia. }
    iIntros (u t) "(%Heq & %Ht & %Hodd)".
    wp_pures.
    wp_apply MR_round_correct_prime; auto.
    iPureIntro.
    split; auto.
    split; auto.
    split; auto.
    split; first by lia.
    split; auto; lia.
  Qed.


  Lemma MR_main_composite_error (m : Z) E :
    {{{ ⌜ ¬ Znumtheory.prime m ⌝ ∗
          € (nnreal_div (nnreal_nat 1) (nnreal_nat 2))
    }}}
      MR_main #m @ E
      {{{ (b : bool) , RET #b;
          ⌜ (b = false) ⌝ }}}.
  Proof.
    iIntros (Φ) "[%Hcomp Herr] HΦ".
    wp_rec.
    wp_pures.
    case_bool_decide.
    {
      wp_pures.
      by iApply "HΦ".
    }
    wp_pures.
    wp_bind (power_two_decomp _).
    wp_apply (power_two_decomp_correct).
    { iPureIntro; lia. }
    iIntros (u t) "(%Heq & %Ht & %Hodd)".
    wp_pures.
    wp_apply (MR_round_composite_error with "[$Herr]"); auto.
    iPureIntro.
    split; first by lia.
    split; auto.
    split; auto.
    split; first by lia.
    split; auto.
    lia.
  Qed.


  Variable (num_iter : nat).


  (*
    The main function for the Miller-Rabin test,
    where num_iter iterations are performed
  *)

  Definition MR_main_looped : val :=
    (λ: "m",
      if: "m" ≤ #1 then #false
      else
        let, ("u", "t") := power_two_decomp ("m" - #1) in
        letrec: "g" "k" := (
          if: "k" = #0 then #true
          else
            let: "r" := MR_round "m" "t" "u" in
            if: "r" then "g" ("k" - #1) else #false) in
       "g" #num_iter )%V.

Lemma MR_main_looped_correct_prime (m : Z) E :
    {{{ ⌜ Znumtheory.prime m ⌝ }}}
      MR_main_looped #m @ E
      {{{ (b : bool) , RET #b;
          ⌜ (b = true) ⌝ }}}.
  Proof.
    iIntros (Φ Hprime) "HΦ".
    assert (1 < m)%Z as Hm.
    {
      destruct Hprime; auto.
    }
    wp_rec.
    wp_pures.
    case_bool_decide; first by lia.
    wp_pures.
    wp_bind (power_two_decomp _).
    wp_apply (power_two_decomp_correct).
    { iPureIntro; lia. }
    iIntros (u t) "(%Heq & %Ht & %Hodd)".
    do 11 wp_pure.
    iInduction num_iter as [|k] "IH".
    - wp_pures.
      iApply "HΦ"; done.
    - wp_pures.
      wp_bind (MR_round _ _ _).
      wp_apply MR_round_correct_prime; auto.
      * iPureIntro.
        split; auto.
        split; auto.
        split; auto.
        split; first by lia.
        split; auto; lia.
      * iIntros (b) "->".
        do 4 wp_pure.
        replace #(S k - 1) with #k; last first.
        {
          do 2 f_equal. lia.
        }
        by iApply "IH".
  Qed.


  Lemma MR_main_looped_composite_error (m : Z) E :
    {{{ ⌜ ¬ Znumtheory.prime m ⌝ ∗
          € (nnreal_div (nnreal_nat 1) (nnreal_nat (2^num_iter)))
    }}}
      MR_main_looped #m @ E
      {{{ (b : bool) , RET #b;
          ⌜ (b = false) ⌝ }}}.
  Proof.
    iIntros (Φ) "[%Hcomp Herr] HΦ".
    wp_rec.
    wp_pures.
    case_bool_decide.
    {
      wp_pures.
      by iApply "HΦ".
    }
    wp_pures.
    wp_bind (power_two_decomp _).
    wp_apply (power_two_decomp_correct).
    { iPureIntro; lia. }
    iIntros (u t) "(%Heq & %Ht & %Hodd)".
    do 11 wp_pure.
    iInduction num_iter as [|k] "IH".
    - iExFalso.
      iApply ec_spend; auto.
      simpl. lra.
    - wp_pures.
      wp_bind (MR_round _ _ _).
      wp_apply (MR_round_composite_error_amplify with "[$Herr]"); auto.
      + iPureIntro.
        split; first by lia.
        split; auto.
        split; auto.
        split; first by lia.
        split; auto.
        lia.
      + iIntros ([]) "Hpost".
        * do 4 wp_pure.
          replace #(S k - 1) with #k; last first.
          {
            do 2 f_equal; lia.
          }
          iApply ("IH" with "[Hpost]"); auto.
          iDestruct "Hpost" as "[% |Herr]"; [done |].
          iApply (ec_spend_irrel with "[$Herr]").
          simpl.
          rewrite Nat.add_0_r.
          replace (2 ^ k + 2 ^ k)%nat with (2 * 2^k)%nat by lia.
          do 2 rewrite Rmult_1_l.
          rewrite mult_INR pow_INR /=.
          rewrite Rinv_mult. lra.
        * wp_pures. iApply "HΦ"; auto.
  Qed.



End miller_rabin_code.






