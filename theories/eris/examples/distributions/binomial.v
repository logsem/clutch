From clutch.eris Require Export eris.

Section binomial.

  Context `{!erisGS Σ}.

  Parameter (B : val).

  Parameter (B_spec : ∀ (N M : nat) (ε ε1 ε2 : R), N ≤ (M + 1) → 
  ((ε1 * (1 - (N / (M + 1)))) + (ε2 * (N / (M + 1))) = ε)%R ->
  [[{↯ ε}]]
    B #N #M
  [[{
      (k : nat), RET #k; 
      (⌜k = 0⌝ ∗ ↯ ε1) ∨
      (⌜k = 1⌝ ∗ ↯ ε2)
  }]]).

  Definition binom : val :=
    λ: "m" "n",
      rec: "binom" "k" :=
        if: "k" ≤ #0
        then #0
        else "binom" ("k" - #1) + B "m" "n".

  Definition choose (n k : nat) : R :=
    if bool_decide (k ≤ n)%nat then
      C n k
    else 0%R.

  Lemma pascal' : ∀ (n i : nat), (choose n i + choose n (S i))%R = choose (S n) (S i).
  Proof.
    intros n i.
    rewrite /choose.
    repeat case_bool_decide; try lia; last lra; first by rewrite pascal.
    assert (i = n) as ->; first lia.
    rewrite !Rcomplements.C_n_n.
    lra.
  Qed.
  
  Definition binom_prob (p q n k : nat) : R := (choose n k * (p / (q + 1))^k * (1 - p / (q + 1))^(n - k))%R.


   Lemma binom_prob_split (p q n k : nat) : ((1 - (p / (q + 1))) * binom_prob p q n (k+1)  + (p / (q + 1)) * binom_prob p q n k = binom_prob p q (n+1) (k+1))%R.
  Proof.
    rewrite /binom_prob.
    set (r := (p / (q + 1))%R).
    set (s := (1 - r)%R).
    destruct (Nat.lt_ge_cases k n).
    - replace (n + 1 - (k + 1))%nat with (n - k)%nat; last lia.
      rewrite !Nat.add_1_r -pascal'.
      set (A := choose n k).
      set (B := choose n (S k)).
      rewrite -(Rmult_assoc s).
      setoid_rewrite (Rmult_comm s).
      rewrite (Rmult_assoc _ s).
      replace (s * s ^ (n - S k))%R with (s ^ (n - k))%R; last first.
      {
        rewrite -{2}(pow_1 s) -pow_add.
        f_equal.
        lia.
      }
      rewrite (Rmult_comm A) -!(Rmult_assoc r).
      replace (r * r ^ k)%R with (r ^ (S k))%R; last rewrite -{2}(pow_1 r) -pow_add //.
      unfold s.
      lra.
    - rewrite /choose.
      replace (n - (k + 1))%nat with 0%nat; last lia.
      replace (n - k)%nat with 0%nat; last lia.
      replace (n + 1 - (k + 1))%nat with 0%nat; last lia.
      repeat case_bool_decide; try lia.
      + assert (k = n) as ->; first lia.
        rewrite !Rcomplements.C_n_n.
        rewrite !Rmult_0_l !Rmult_0_r Rplus_0_l !Rmult_1_l !Rmult_1_r.
        rewrite pow_add. lra.
      + rewrite !Rmult_0_l !Rmult_0_r.
        lra.
  Qed.

  Lemma binom_prob_eq : ∀ p q n, (binom_prob p q n n = (p / (q + 1))^n)%R.
  Proof.
    intros p q n.
    rewrite /binom_prob /choose.
    case_bool_decide; last lia.
    replace (n - n)%nat with 0%nat; last lia.
    rewrite Rcomplements.C_n_n Rmult_1_r Rmult_1_l //.
  Qed.

  Lemma binom_prob_0 : ∀ p q n, (binom_prob p q n 0 = (1 - p / (q + 1))^n)%R.
  Proof.
    intros p q n.
    rewrite /binom_prob /choose.
    case_bool_decide; last lia.
    replace (n - 0)%nat with n%nat; last lia.
    rewrite Rcomplements.C_n_0 Rmult_1_r Rmult_1_l //.
  Qed.
  
  Lemma binom_prob_gt : ∀ p q n k, n < k → binom_prob p q n k = 0%R.
  Proof.
    intros p q n k Hnk.
    rewrite /binom_prob /choose.
    case_bool_decide; first lia.
    rewrite !Rmult_0_l //.
  Qed.

  Fixpoint fin_S_inj {n : nat} (m : fin n) : fin (S n) :=
    match m with
    | Fin.F1 _ => Fin.F1
    | Fin.FS _ k=> Fin.FS (fin_S_inj k)
    end.

  Lemma fin_S_inj_to_nat : ∀ (m : nat) (n : fin m), fin_to_nat n = fin_to_nat (fin_S_inj n).
  Proof.
    intros m n.
    induction n; first done.
    simpl.
    by f_equal.
  Qed.

  Lemma fin_to_nat_FS : ∀ (m : nat) (n : fin m), fin_to_nat (FS n) = S (fin_to_nat n).
  Proof.
    intros m n.
    reflexivity.
  Qed.

  Lemma Series_fin_first : ∀ (n : nat) (D : fin (S n) → R), SeriesC D = (D 0%fin + SeriesC (λ (k : fin n), D (FS k)))%R.
  Proof.
    intros n D.
    rewrite !SeriesC_finite_foldr /= foldr_fmap //.
  Qed.

  Lemma foldr_last {A : Set} : ∀ (l : list A) (x y : A) (f : A → A → A),
    (∀ x y z, f x (f y z) = f (f x y) z) →
    (∀ x y, f x y = f y x) →
    foldr f x (l ++ [y]) = f y (foldr f x l).
  Proof.
    intros l.
    induction l as [|h t IH]; intros x y f Ha Hc; first done.
    rewrite /= (IH x y f Ha Hc) Hc -Ha (Hc _ h) //.
  Qed.

  Lemma nat_to_fin_proof_ext : ∀ (k n : nat) (H1 H2 : k < n), nat_to_fin H1 = nat_to_fin H2.
  Proof.
    intros k.
    induction k.
    - intros n H1 H2. destruct n; last done. inversion H1.
    - intros n H1 H2.
      destruct n; first inversion H1.
      simpl.
      f_equal.
      apply IHk.
  Qed.
  
  Lemma enum_fin_last : ∀ (n : nat) (H : n < S n), last (enum (fin (S n))) = Some (nat_to_fin H).
  Proof.
    intros n.
    induction n; first done.
    intros H.
    replace (last (enum (fin (S (S n))))) with (last (FS <$> enum (fin (S n)))); last done.
    rewrite fmap_last (IHn (Nat.lt_succ_diag_r n)).
    simpl.
    do 2 f_equal.
    apply nat_to_fin_proof_ext.
  Qed.

  Lemma enum_fin_split : ∀ (n : nat) (H : n < S n), enum (fin (S n)) = (fin_S_inj <$> enum (fin n)) ++ [nat_to_fin H].
  Proof.
    intros n.
    induction n; first done.
    intros H.
    replace (enum (fin (S (S n)))) with (0%fin::(FS <$> enum (fin (S n)))); last done.
    rewrite {1}IHn /=.
    f_equal.
    rewrite fmap_app /=.
    f_equal; last first.
    { do 2 f_equal.
      apply nat_to_fin_proof_ext.
    }
    fold (@fmap _ list_fmap).
    rewrite -!list_fmap_compose.
    apply list_fmap_ext.
    done.
  Qed.
    
  Lemma Series_fin_last : ∀ (n : nat) (D : fin (S n) → R), SeriesC D = (SeriesC (λ (k : fin n), D (fin_S_inj k)) + D (@nat_to_fin n (S n) (Nat.lt_succ_diag_r n)))%R.
  Proof.
    intros n D.
    rewrite !SeriesC_finite_foldr -foldr_fmap enum_fin_split fmap_app /= foldr_last; try (intros; lra).
    rewrite Rplus_comm.
    f_equal.
    rewrite !foldr_fmap //.
  Qed.
    
  Lemma ec_binom_split :
    ∀ (p q n : nat) (D : fin (S (S n)) → R),
    let D0 (k : fin (S n)) := D (fin_S_inj k) in
    let D1 (k : fin (S n)) := D (FS k) in
    let ε := SeriesC (λ (k : fin (S (S n))), binom_prob p q (n+1) k * D k)%R in
    let ε0 := SeriesC (λ (k : fin (S n)), binom_prob p q n k * D0 k)%R in
    let ε1 := SeriesC (λ (k : fin (S n)), binom_prob p q n k * D1 k)%R in
    (ε = (1 - (p / (q + 1))) * ε0 + (p / (q + 1))* ε1)%R.
  Proof.
    intros p q n.
    intros D D0 D1 ε ε0 ε1.
    rewrite /ε /ε0 /ε1 /D0 /D1.
    set (r := (p / (q + 1))%R).
    set (s := (1 - r)%R).
    rewrite Series_fin_first.
    rewrite binom_prob_0 pow_add -binom_prob_0 pow_1 /=.
    fold r s.
    erewrite SeriesC_ext; last first.
    {
      intros k.
      replace (S k)%nat with (k + 1)%nat; last lia.
      replace (S (S n))%nat with ((n + 1) + 1)%nat at 1; last lia.
      rewrite -binom_prob_split Rmult_plus_distr_r.
      fold r s.
      replace (k + 1)%nat with (FS k : nat); last (simpl; lia).
      rewrite (Rmult_assoc r) (Rmult_assoc s) //.
    }
    rewrite SeriesC_plus; try apply ex_seriesC_finite.
    rewrite !SeriesC_scal_l -Rplus_assoc.
    f_equal.
    rewrite (Rmult_comm _ s) Rmult_assoc -Rmult_plus_distr_l.
    f_equal.
    rewrite -(Series_fin_first (S n) (λ k : fin (S (S n)), binom_prob p q n k * D k))%R Series_fin_last binom_prob_gt; last first.
    { rewrite fin_to_nat_to_fin. lia. }
    rewrite Rmult_0_l Rplus_0_r.
    apply SeriesC_ext.
    intros k.
    rewrite -fin_S_inj_to_nat //.
  Qed.
  
  Lemma twp_binom_split : ∀ (p q : nat), 
    p ≤ (q + 1) →
    ∀ (n : nat) (D : fin (S n) → R) (ε : R),
    SeriesC (λ k : fin (S n), (binom_prob p q n k * D k)%R) = ε →
    ([[{ ↯ ε }]] binom #p #q #n [[{ (k : fin (S n)), RET #k ; ↯ (D k) }]]).
  Proof.
    iIntros (p q Hpq n).
    iIntros (D ε HD Φ) "Herr HΦ".
    rewrite /binom.
    do 4 wp_pure.
    iRevert (D ε HD Φ) "Herr HΦ".
    iInduction (n) as [|n] "IH";
      iIntros (D ε HD Φ) "Herr HΦ";
      wp_pures.
    - iModIntro.
      replace #0 with #(0%fin : fin 1); last reflexivity.
      iApply ("HΦ" with "[Herr]").
      rewrite SeriesC_finite_foldr /= binom_prob_eq Rmult_1_l Rplus_0_r in HD.
      rewrite HD //.
    - erewrite SeriesC_ext in HD; last first.
      { intros k.
        by replace (S n) with (n + 1) at 1; last lia.
      } 
      rewrite ec_binom_split in HD.
      match type of HD with
      | ( _ * ?A +  _ * ?B)%R = _ =>
          set (ε0 := A);
          set (ε1 := B)
      end.
      fold ε0 ε1 in HD.
      wp_apply (B_spec _ _ _ ε0 ε1%R with "Herr"); first lia; first (rewrite -HD; lra).
      iIntros (?) "[[-> Herr] | [-> Herr]]".
      { wp_pure.
        replace (S n - 1)%Z with (n : Z); last lia.
        wp_apply ("IH" with "[] Herr [HΦ]").
        {
          iPureIntro.
          unfold ε0.
          reflexivity.          
        }
        {
          iIntros (k) "Herr".
          rewrite fin_S_inj_to_nat.
          wp_pures.
          rewrite Z.add_0_r.
          iApply ("HΦ" with "Herr").
        }
      }
      { wp_pure.
        replace (S n - 1)%Z with (n : Z); last lia.
        wp_apply ("IH" with "[] Herr [HΦ]").
        {
          iPureIntro.
          unfold ε0.
          reflexivity.          
        }
        {
          iIntros (k) "Herr".
          rewrite fin_S_inj_to_nat.
          wp_pures.
          rewrite Z.add_1_r -Nat2Z.inj_succ -fin_S_inj_to_nat.
          iApply ("HΦ" with "Herr").
        }
      }
  Qed.
      

  Definition binom_cred (p q n k : nat) := (1 - binom_prob p q n k)%R.

  Lemma sum_binom_prob : ∀ (p q n : nat), SeriesC (λ (k : fin (S n)), binom_prob p q n k)%R = 1%R.
  Proof.
    intros p q n.
    induction n.
    - rewrite SeriesC_finite_foldr /=.
      rewrite binom_prob_eq.
      lra.
    - rewrite Series_fin_first.
      rewrite binom_prob_0.
      set (r := (p / (q + 1))%R).
      set (s := (1 - r)%R).
      erewrite SeriesC_ext; last first.
      { intros k.
        replace (S n) with (n + 1)%nat at 1; last lia.
        replace (S k) with (k + 1)%nat at 1; last lia.
        rewrite -binom_prob_split.
        fold r s.
        replace (k + 1)%nat with (S k); last lia.
        reflexivity.
      }
      rewrite SeriesC_plus; try apply ex_seriesC_finite.
      rewrite !SeriesC_scal_l IHn Rmult_1_r Series_fin_last fin_to_nat_to_fin binom_prob_gt; last lia.
      rewrite Rplus_0_r.
      pose proof (Series_fin_first n (binom_prob p q n)) as H.
      rewrite binom_prob_0 IHn Rplus_comm in H.
      fold r s in H.
      apply (Rminus_eq_compat_r (s^n)) in H.
      rewrite Rplus_minus_r in H.
      erewrite SeriesC_ext; last first.
      { intros k.
        rewrite -fin_S_inj_to_nat //.
      }
      rewrite -H.
      rewrite Rmult_minus_distr_l /=.
      unfold s.
      lra.
  Qed.
  
  Lemma twp_binom_k :
    ∀ (p q n : nat),
    p ≤ (q + 1) →
    ∀ (k : nat),
    k ≤ n →
    ([[{ ↯ (binom_cred p q n k) }]] binom #p #q #n [[{ RET #k ; True }]]).
  Proof.
    intros p q n Hpq k Hkn.
    set (fk := nat_to_fin (le_n_S _ _ Hkn)).
    set (D1 (m : fin (S n)) := binom_prob p q n m).
    set (D2 (m : fin (S n)) := if bool_decide (m = fk)
                               then binom_prob p q n k%R
                               else 0%R).
    set (D3 (m : fin (S n)) := if bool_decide (m = fk)
                               then 0%R
                               else binom_prob p q n m%R).
    set (D4 (m : fin (S n)) :=  if bool_decide (m = fk)
                               then 0%R
                                else 1%R).
    set (D5 (m : fin (S n)) := (binom_prob p q n m * D4 m)%R).

    assert (SeriesC D1 = 1%R) as HD1; first apply sum_binom_prob.
    assert (SeriesC D2 = binom_prob p q n k) as HD2; first apply SeriesC_singleton.
    assert (SeriesC D3 = SeriesC (λ k, D1 k - D2 k)%R) as HD3.
    { apply SeriesC_ext.
      intros m.
      unfold D1, D2, D3.
      case_bool_decide as H; last lra.
      rewrite H /fk fin_to_nat_to_fin.
      lra.
    }
    assert (SeriesC D3 = SeriesC D5) as HD5.
    {
      apply SeriesC_ext.
      intros m.
      unfold D3, D5, D4.
      case_bool_decide; lra.
    } 
    rewrite SeriesC_minus in HD3; try apply ex_seriesC_finite.
    rewrite HD1 HD2 in HD3.
    fold (binom_cred p q n k) in HD3.
    rewrite -HD3 HD5.
    iIntros (Φ) "Herr HΦ".
    wp_apply (twp_binom_split with "Herr"); first done.
    { unfold D5. reflexivity. }
    iIntros (m).
    unfold D4.
    case_bool_decide as Hk.
    { rewrite Hk fin_to_nat_to_fin.
      iIntros "?".
      by iApply "HΦ".
    }
    {
      iIntros "Herr".
      iExFalso.
      iApply (ec_contradict with "Herr").
      lra.
    }
  Qed.
