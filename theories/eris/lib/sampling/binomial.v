From clutch.eris Require Export eris.

From clutch.eris.lib.sampling.utils Require Import fintools.

Section binomial.

  Context `{!erisGS Σ}.

  Parameter (B_lbl : val).
  Definition B : expr := B_lbl #().

  Parameter B_spec : ∀ (N M : nat) (ε ε1 ε2 : R), N ≤ (M + 1) → 
  ((ε1 * (1 - (N / (M + 1)))) + (ε2 * (N / (M + 1))) = ε)%R ->
  [[{↯ ε}]]
    B #N #M
  [[{
      (k : nat), RET #k; 
      (⌜k = 0⌝ ∗ ↯ ε1) ∨
      (⌜k = 1⌝ ∗ ↯ ε2)
  }]].

  Parameter B_tape : ∀ (N M : nat), loc → list (fin 2) → iProp Σ.
  
  Parameter B_tape_presample :
    ∀ (e : expr) (α : loc) (Φ : val → iProp Σ)
      (N M : nat) (ns : list (fin 2)),
    to_val e = None
    → B_tape N M α ns ∗
    (∀ (i : fin 2),B_tape N M α (ns ++ [i%fin]) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }]
  .

  Parameter (twp_B_tape :
    ∀ (N M : nat) (α : loc) (ns : list (fin 2)) (n : fin 2),
    [[{ B_tape N M α (n::ns) }]]
      B (#lbl:α) #N #M
    [[{ RET #n ; B_tape N M α ns }]]).

  Parameter (B_tape_planner :
              ∀ (N M : nat) (e : expr) (ε : nonnegreal)
                (L : nat) (α : loc) (Φ : val → iProp Σ)
                (prefix : list (fin 2)) (suffix : list (fin 2) → list (fin 2)),
               (0 < N)%nat →
               (N < S M)%nat →
               to_val e = None →
               (∀ junk : list (fin 2),
                  (0 < length (suffix (prefix ++ junk)) <= L)%nat) →
               (0 < ε)%R →
               ↯ ε ∗ B_tape N M α prefix ∗
               ( (∃ (junk : list (fin 2)), B_tape N M α (prefix ++ junk ++ suffix (prefix ++ junk))) -∗ WP e [{ Φ }]
               ) ⊢ WP e [{ Φ }]).
  
  Definition binom_tape : val :=
    λ: "α" "m" "n",
      rec: "binom" "k" :=
        if: "k" ≤ #0
        then #0
        else "binom" ("k" - #1) + B_lbl "α" "m" "n".

  Definition binom : expr := binom_tape #().
  
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

  Lemma choose_pos : ∀ (n i : nat), (0 <= choose n i)%R.
  Proof.
    intros n i.
    rewrite /choose /C.
    case_bool_decide; last done.
    apply Rcomplements.Rdiv_le_0_compat; first apply pos_INR.
    apply Rmult_lt_0_compat;
      rewrite -INR_0;
      apply lt_INR, lt_O_fact.
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
    rewrite /binom /binom_tape.
    do 6 wp_pure.
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
  
  Definition binomial_to_bernoulli (k : nat) (v : list (fin (S k))) : list (fin 2) :=  
    x ← v ;
  (repeat (1%fin : fin 2) (fin_to_nat x) ++ repeat (0%fin : fin 2) (k - fin_to_nat x)).
       
  Fixpoint bernoulli_to_binomial_aux (k c : nat) (l : list (fin 2)) (acc : fin (S k)) : list (fin (S k)) :=
    match l,c with
    | [], _ => []
    | h::t, 0 => [fin_hsum h acc] ++ bernoulli_to_binomial_aux k (k - 1) t 0%fin
    | h::t, S m => bernoulli_to_binomial_aux k m t (fin_hsum h acc)
    end.

  Definition bernoulli_to_binomial (k : nat) (l : list (fin 2)) : list (fin (S k)) :=
    bernoulli_to_binomial_aux k (k - 1) l 0%fin.
  
  Lemma bernoulli_to_binomial_aux_app :
    ∀ (k ct : nat) (l1 l2: list (fin 2)) (acc : fin (S k)),
    length l1 = S ct → bernoulli_to_binomial_aux k ct (l1 ++ l2) acc = [fin_hsum acc $ fin_sum_list 2 k l1] ++ bernoulli_to_binomial_aux k (k - 1) l2 0%fin.
  Proof.
    move=>k ct l1 l2.
    elim: l1 l2 k ct =>[|h t IH] l2 k ct acc len_ct_eq_k /=.
    - simpl in len_ct_eq_k. lia.
    - destruct ct.
      + simpl in *.
        destruct t; last (simpl in len_ct_eq_k; lia).
        simpl.
        f_equal.
        rewrite fin_hsum_comm fin_hsum_assoc; last done.
        fold (@fin_sum (S k)).
        rewrite fin_sum_0.
        reflexivity.
      + simpl in *.
        rewrite IH; last lia.
        rewrite fin_hsum_comm fin_hsum_assoc //.
  Qed.

  Lemma bernoulli_to_binomial_app_1 :
    ∀ (k : nat) (l1 l2: list (fin 2)), k ≠ 0 →
    length l1 = k → bernoulli_to_binomial k (l1 ++ l2) = [fin_sum_list 2 k l1] ++ bernoulli_to_binomial k l2.
  Proof.
    unfold bernoulli_to_binomial.
    move=>k l1 l2 k_not_0 len_k.
    rewrite bernoulli_to_binomial_aux_app //; last lia.
  Qed.

  Lemma bernoulli_to_binomial_app_n :
    ∀ (k n : nat) (l1 l2: list (fin 2)), k ≠ 0 →
    length l1 = n * k → bernoulli_to_binomial k (l1 ++ l2) = bernoulli_to_binomial k l1 ++ bernoulli_to_binomial k l2.
  Proof.
    move=>k.
    elim=>[|n IH].
    - move=>[|??] l2 k_pos len_l1; last (simpl in len_l1; lia).
      reflexivity.
    - move=>l1 l2 k_pos len_l1.
      rewrite -{1}(take_drop k l1) -app_assoc
             bernoulli_to_binomial_app_1; try done; last first.
      { rewrite take_length Nat.min_l /=; lia. }
      rewrite IH; try done; last first.
      { rewrite drop_length len_l1. lia. }
      rewrite app_assoc -bernoulli_to_binomial_app_1; try lia; last first.
      { rewrite take_length Nat.min_l /=; lia. }
      rewrite (take_drop k l1) //.
  Qed.

  Lemma binomial_to_bernoulli_to_binomial (k : nat) : (k ≠ 0)%nat → ∀ (l : list (fin (S k))), bernoulli_to_binomial k (binomial_to_bernoulli k l) = l.
  Proof.
    move=>k_pos.
    elim=>[|h t IHt].
    - unfold binomial_to_bernoulli.
      unfold bernoulli_to_binomial.
      unfold bernoulli_to_binomial_aux.
      reflexivity.
    - simpl.
      rewrite bernoulli_to_binomial_app_1; try done.
      + rewrite IHt /=.
        f_equal.
        unfold fin_sum_list.
        rewrite foldr_app.
        fold (fin_sum_list 2 k (repeat 0%fin (k - h))).
        rewrite fin_sum_repeat_0.
        fold (fin_sum_list 2 k (repeat 1%fin h)).
        rewrite fin_sum_repeat_1 //.
      + rewrite app_length !repeat_length.
        assert (h < S k) by apply fin_to_nat_lt.
        lia.
  Qed.

  
  Fixpoint is_binomial_translation (k : nat) (v : list (fin (S k))) (l : list (fin 2)) :=
    match v with
    | [] => l = []
    | vh ::vt => ∃ (pre suf : list (fin 2)), fin_sum_list 2 k pre = vh ∧
                                             length pre = k ∧
                                             l = pre ++ suf ∧
                                             is_binomial_translation k vt suf
  end.

  Lemma bernoulli_to_binomial_translation :
    ∀ (k : nat) (l : list (fin 2)) (v : list (fin (S k))),
    (0 < k)%nat →
    is_binomial_translation k v l ↔ ∃ n, length l = n * k ∧ v = bernoulli_to_binomial k l.
  Proof.
    move=>k l v.
    elim:v l =>[|hv tv IH] [|hl tl] k_pos.
    - split; last done.
      move=>_.
      by exists 0.
    - split; first done.
      move=>[[|n] [len tsl]]; simpl in len; first lia.
      contradict tsl.
      rewrite -{1}(take_drop k (hl::tl)).
      rewrite bernoulli_to_binomial_app_1; [done|lia|..].
      rewrite take_length Nat.min_l /=; lia.
    - split.
      + intros (pre & suf & sum_eq & len_pre & pre_suf & tls).
        destruct pre;
          simpl in len_pre, pre_suf; [lia | discriminate].
      + intros (? & ? & ?).
        discriminate.
    - split.
      + intros (pre & suf & sum_eq & len_pre & pre_suf & tls).
        rewrite pre_suf app_length len_pre bernoulli_to_binomial_app_1; [|lia|done].
        apply IH in tls as (n & -> & ->); last lia.
        exists (S n).
        split; first lia.
        simpl.
        by f_equal.
      + move=>[[|n] [len tsl]]; simpl in len; first lia.
        rewrite -{1}(take_drop k (hl::tl)) bernoulli_to_binomial_app_1 /= in tsl;
          [..|lia|]; last first.
        { rewrite take_length Nat.min_l /=; lia. }
        injection tsl as hv_eq tv_eq.
        simpl.
        eexists _, _.
        split; first done.
        split.
        { rewrite take_length Nat.min_l /=; lia. }
        rewrite -{1}(take_drop k (hl::tl)).
        split; first done.
        apply IH; first done.
        exists n.
        split; last done.
        rewrite drop_length /= len.
        lia.
  Qed.
    
  Definition own_binomial_tape α m n k v := (∃ l, B_tape m n α l ∗ ⌜is_binomial_translation k v l⌝)%I.

  Lemma B_tape_multiple_presample : 
    ∀ (e : expr) (α : loc) (Φ : val → iProp Σ)
      (N M k : nat) (ns : list (fin 2)),
    to_val e = None
    → B_tape N M α ns ∗
    (∀ (l : list (fin 2)), ⌜length l = k⌝ -∗ B_tape N M α (ns ++ l) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }]
  .
  Proof.
    iIntros (e α Φ N M k).
    iRevert (Φ).
    iInduction (k) as [|k] "IH";
       iIntros (Φ ns e_not_val) "[Htape Hlists]".
    - wp_apply ("Hlists" $! []); first done.
      rewrite app_nil_r //.
    - wp_apply B_tape_presample; first done.
      iFrame.
      iIntros (i) "Htape".
      wp_apply "IH"; first done.
      iFrame.
      iIntros (l length_l_k) "Htape".
      wp_apply ("Hlists" $! i::l); first rewrite /= length_l_k //.
      rewrite -app_assoc //.
  Qed.

  Lemma binomial_tape_presample :
    ∀ (e : expr) (α : loc) (Φ : val → iProp Σ)
      (N M k : nat) (ns : list (fin (S k))),
    to_val e = None
    → (0 < k)%nat
    → own_binomial_tape α N M k ns ∗
    (∀ (i : fin (S k)), own_binomial_tape α N M k (ns ++ [i%fin]) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }]
  .
  Proof.
    unfold own_binomial_tape.
    iIntros (e α Φ N M k ns e_not_val k_pos) "[(%l & Hα & %Hl) Hwp]".
    wp_apply (B_tape_multiple_presample _ α _ N M k); first done.
    iFrame.
    iIntros (l' length_l'_k) "Hα".
    set (i := fin_sum_list 2 k l').
    wp_apply ("Hwp" $! i).
    iExists (l ++ l').
    iFrame.
    iPureIntro.
    rewrite bernoulli_to_binomial_translation in Hl; last done.
    destruct Hl as (n & len & ->).
    rewrite bernoulli_to_binomial_translation; last done.
    rewrite (bernoulli_to_binomial_app_n _ n); [..|lia|done].
    exists (S n).
    rewrite app_length len length_l'_k.
    split; first lia.
    f_equal.
    rewrite -(app_nil_r l') bernoulli_to_binomial_app_1; [done|lia|done].
  Qed.
(*
  TODO : Make similar lemmas to these     
  Parameter (twp_B_tape :
    ∀ (N M : nat) (α : loc) (ns : list (fin 2)) (n : fin 2),
    [[{ B_tape N M α (n::ns) }]]
      B (#lbl:α) #N #M
    [[{ RET #n ; B_tape N M α ns }]]).

  Parameter (B_tape_planner :
              ∀ (N M : nat) (e : expr) (ε : nonnegreal)
                (L : nat) (α : loc) (Φ : val → iProp Σ)
                (prefix : list (fin 2)) (suffix : list (fin 2) → list (fin 2)),
               (0 < N)%nat →
               (N < S M)%nat →
               to_val e = None →
               (∀ junk : list (fin 2),
                  (0 < length (suffix (prefix ++ junk)) <= L)%nat) →
               (0 < ε)%R →
               ↯ ε ∗ B_tape N M α prefix ∗
               ( (∃ (junk : list (fin 2)), B_tape N M α (prefix ++ junk ++ suffix (prefix ++ junk))) -∗ WP e [{ Φ }]
               ) ⊢ WP e [{ Φ }]).
 
  *)
End binomial.
#[global] Opaque binomial.
