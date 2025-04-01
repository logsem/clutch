From clutch.eris Require Export eris.

From clutch.eris.lib.sampling Require Import utils.

Section binomial.
  Context `{!erisGS Σ}.

  Parameter (B_lbl : val).
  Definition B : expr := B_lbl #().

  Parameter B_spec :
    ∀ (N M : nat) (ε ε1 ε2 : R) (p := (N / (M + 1))%R),
    N ≤ (M + 1) → 
    ((ε1 * (1 - p)) + (ε2 * p) = ε)%R ->
    [[{↯ ε}]]
      B #N #M
    [[{
        (k : nat), RET #k; 
        (⌜k = 0⌝ ∗ ↯ ε1) ∨
        (⌜k = 1⌝ ∗ ↯ ε2)
    }]]
  .

  Parameter B_tape : loc → nat → nat → list (fin 2) → iProp Σ.
  
  Parameter B_tape_presample :
    ∀ (e : expr) (α : loc) (Φ : val → iProp Σ)
      (N M : nat) (ns : list (fin 2)),
    to_val e = None →
    B_tape α N M ns ∗
    (∀ (i : fin 2), B_tape α N M (ns ++ [i%fin]) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }]
  .

  Parameter twp_B_tape  :
   ∀ (α : loc) (N M : nat) (ns : list (fin 2)) (n : fin 2),
    [[{ B_tape α N M (n::ns) }]]
      B_lbl (#lbl:α) #N #M
    [[{ RET #n ; B_tape α N M ns }]]
  .

  Parameter B_tape_planner :
    ∀ (N M : nat) (e : expr) (ε : nonnegreal)
      (L : nat) (α : loc) (Φ : val → iProp Σ)
      (prefix : list (fin 2)) (suffix : list (fin 2) → list (fin 2)),
    (0 < N < S M)%nat →
    to_val e = None →
    (∀ junk : list (fin 2), (0 < length (suffix (prefix ++ junk)) <= L)%nat) →
    (0 < ε)%R →
    ↯ ε ∗ B_tape α N M prefix ∗
    ( (∃ (junk : list (fin 2)), B_tape α N M (prefix ++ junk ++ suffix (prefix ++ junk))) -∗ WP e [{ Φ }]) 
    ⊢ WP e [{ Φ }]
    .

  Parameter B_tape_adv_comp :
      ∀ (e : expr) (α : loc) (Φ : val → iProp Σ)
      (N M : nat) (ns : list (fin 2)) (ε : R)
      (D : fin 2 → R),
    (N ≤ M + 1)%nat →
    (∀ (i : fin 2), 0 <= D i)%R →
    (D 0%fin * (1 - (N / (M + 1))) + D 1%fin * (N / (M + 1)) = ε)%R
    →  to_val e = None
    → B_tape α N M ns ∗ ↯ ε ∗
    (∀ (i : fin 2), ↯ (D i) ∗ B_tape α N M (ns ++ [i]) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }]
  .
 
    
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

  Lemma pascal' (n i : nat) : (choose n i + choose n (S i))%R = choose (S n) (S i).
  Proof.
    rewrite /choose.
    repeat case_bool_decide; try lia; [by rewrite pascal | | lra].
    assert (i = n) as -> by lia.
    rewrite !Rcomplements.C_n_n.
    lra.
  Qed.

  Lemma choose_pos (n i : nat) : (0 <= choose n i)%R.
  Proof.
    rewrite /choose /C.
    case_bool_decide; last done.
    apply Rcomplements.Rdiv_le_0_compat; first apply pos_INR.
    apply Rmult_lt_0_compat;
      rewrite -INR_0;
      apply lt_INR, lt_O_fact.
  Qed.
  
  Definition binom_prob (p q n k : nat) : R := (choose n k * (p / (q + 1))^k * (1 - p / (q + 1))^(n - k))%R.


  Lemma binom_prob_split (p q n k : nat) : 
    ((1 - (p / (q + 1))) * binom_prob p q n (k+1) + (p / (q + 1)) * binom_prob p q n k 
      = 
    binom_prob p q (n+1) (k+1))%R.
  Proof.
    rewrite /binom_prob.
    set (r := (p / (q + 1))%R).
    set (s := (1 - r)%R).
    destruct (Nat.lt_ge_cases k n).
    - replace (n + 1 - (k + 1))%nat with (n - k)%nat by lia.
      rewrite !Nat.add_1_r -pascal'.
      set (A := choose n k).
      set (B := choose n (S k)).
      rewrite -(Rmult_assoc s) (Rmult_comm s) (Rmult_assoc _ s).
      replace (s * s ^ (n - S k))%R with (s ^ (n - k))%R; last first.
      {
        rewrite !tech_pow_Rmult.
        f_equal.
        lia.
      }
      rewrite (Rmult_comm A) -!(Rmult_assoc r) !tech_pow_Rmult.
      lra.
    - rewrite /choose.
      replace (n - (k + 1))%nat with 0%nat by lia.
      replace (n - k)%nat with 0%nat by lia.
      replace (n + 1 - (k + 1))%nat with 0%nat by lia.
      repeat case_bool_decide; try (lia || lra).
      assert (k = n) as -> by lia.
      rewrite !Rcomplements.C_n_n pow_add.
      simpl_expr.
  Qed.

  Lemma binom_prob_eq (p q n : nat) : (binom_prob p q n n = (p / (q + 1))^n)%R.
  Proof.
    rewrite /binom_prob /choose.
    case_bool_decide; last lia.
    rewrite !Nat.sub_diag Rcomplements.C_n_n.
    lra.
  Qed.

  Lemma binom_prob_0 (p q n : nat) : (binom_prob p q n 0 = (1 - p / (q + 1))^n)%R.
  Proof.
    rewrite /binom_prob /choose.
    case_bool_decide; last lia.
    rewrite Nat.sub_0_r Rcomplements.C_n_0.
    lra.
  Qed.
  
  Lemma binom_prob_gt (p q n k : nat) : n < k → binom_prob p q n k = 0%R.
  Proof.
    intros Hnk.
    rewrite /binom_prob /choose.
    case_bool_decide;
    [lia | simpl_expr].
  Qed.

  Lemma Series_fin_first (n : nat) (D : fin (S n) → R) : 
    SeriesC D = (D 0%fin + SeriesC (λ (k : fin n), D (FS k)))%R.
  Proof.
    rewrite !SeriesC_finite_foldr /= foldr_fmap //.
  Qed.

  Lemma foldr_last {A : Type} (l : list A) (x y : A) (f : A → A → A) :
    (∀ x y z, f x (f y z) = f (f x y) z) →
    (∀ x y, f x y = f y x) →
    foldr f x (l ++ [y]) = f y (foldr f x l).
  Proof.
    move => Ha Hc.
    elim: l => [|h t IH] //.
    rewrite /= IH Hc -Ha (Hc _ h) //.
  Qed.
   
  
  Lemma Series_fin_last (n : nat) (D : fin (S n) → R) : 
    SeriesC D = (SeriesC (λ (k : fin n), D (fin_S_inj k)) + D (@nat_to_fin n (S n) (Nat.lt_succ_diag_r n)))%R.
  Proof.
    rewrite !SeriesC_finite_foldr -foldr_fmap enum_fin_split fmap_app /= foldr_last; try (intros; lra).
    rewrite Rplus_comm.
    f_equal.
    rewrite !foldr_fmap //.
  Qed.
    
  Lemma ec_binom_split (p q n : nat) (D : fin (S (S n)) → R):
    let D0 (k : fin (S n)) := D (fin_S_inj k) in
    let D1 (k : fin (S n)) := D (FS k) in
    let ε := SeriesC (λ (k : fin (S (S n))), binom_prob p q (n+1) k * D k)%R in
    let ε0 := SeriesC (λ (k : fin (S n)), binom_prob p q n k * D0 k)%R in
    let ε1 := SeriesC (λ (k : fin (S n)), binom_prob p q n k * D1 k)%R in
    (ε = (1 - (p / (q + 1))) * ε0 + (p / (q + 1))* ε1)%R.
  Proof.
    move=> D0 D1 ε ε0 ε1.   
    unfold ε, ε0, ε1, D0, D1 in *.
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
  
  Lemma twp_binom_adv_comp (p q : nat) (n : nat) (D : fin (S n) → R) (ε : R) :
    p ≤ (q + 1) →
    SeriesC (λ k : fin (S n), (binom_prob p q n k * D k)%R) = ε →
    ([[{ ↯ ε }]] binom #p #q #n [[{ (k : fin (S n)), RET #k ; ↯ (D k) }]]).
  Proof.
    iIntros (Hpq HD Φ) "Herr HΦ".
    rewrite /binom /binom_tape.
    do 6 wp_pure.
    iRevert (D ε HD Φ) "Herr HΦ".
    iInduction (n) as [|n] "IH";
      iIntros (D ε HD Φ) "Herr HΦ";
      wp_pures.
    - iModIntro.
      iApply ("HΦ"$! 0%fin with "[Herr]").
      iApply (ec_eq with "Herr").
      rewrite -HD SeriesC_finite_foldr /= binom_prob_eq Rmult_1_l Rplus_0_r //.
    - erewrite SeriesC_ext in HD; last first.
      { intros k.
        replace (S n) with (n + 1) at 1 by lia.
        reflexivity. } 
      rewrite ec_binom_split in HD.
      match type of HD with
      | ( _ * ?A +  _ * ?B)%R = _ =>
          set (ε0 := A);
          set (ε1 := B)
      end.
      fold ε0 ε1 in HD.
      wp_apply (B_spec _ _ _ ε0 ε1%R with "Herr"); [lia | rewrite -HD; lra | ].
      iIntros (?) "[[-> Herr] | [-> Herr]]".
      + wp_pure.
        replace (S n - 1)%Z with (n : Z) by lia.
        wp_apply ("IH" with "[] Herr [HΦ]") as (k) "Herr"; first done.
        wp_pures.
        rewrite fin_S_inj_to_nat Z.add_0_r.
        iApply ("HΦ" with "Herr").
      + wp_pure.
        replace (S n - 1)%Z with (n : Z); last lia.
        wp_apply ("IH" with "[] Herr [HΦ]") as (k) "Herr"; first done.
        wp_pures.
        rewrite fin_S_inj_to_nat Z.add_1_r -Nat2Z.inj_succ -fin_S_inj_to_nat.
        iApply ("HΦ" with "Herr").
  Qed.
      

  Definition binom_cred (p q n k : nat) := (1 - binom_prob p q n k)%R.

  Lemma sum_binom_prob (p q n : nat) :
    SeriesC (λ (k : fin (S n)), binom_prob p q n k)%R = 1%R.
  Proof.
    elim: n => [|n IHn].
    - rewrite SeriesC_finite_foldr /= binom_prob_eq.
      lra.
    - rewrite Series_fin_first binom_prob_0.
      set (r := (p / (q + 1))%R).
      set (s := (1 - r)%R).
      erewrite SeriesC_ext; last first.
      { intros k.
        replace (S n) with (n + 1)%nat at 1 by lia.
        replace (S k) with (k + 1)%nat at 1 by lia.
        rewrite -binom_prob_split.
        fold r s.
        replace (k + 1)%nat with (S k) by lia.
        reflexivity.
      }
      rewrite SeriesC_plus; [| apply ex_seriesC_finite..].
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
  
  Lemma twp_binom_k (p q n k : nat) :
    p ≤ (q + 1) →
    k ≤ n →
    [[{ ↯ (binom_cred p q n k) }]] 
      binom #p #q #n
    [[{ RET #k ; True }]].
  Proof.
    intros Hpq Hkn.
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

    assert (SeriesC D1 = 1%R) as HD1 by apply sum_binom_prob.
    assert (SeriesC D2 = binom_prob p q n k) as HD2 by apply SeriesC_singleton.
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
    rewrite SeriesC_minus in HD3;[| apply ex_seriesC_finite..].
    rewrite HD1 HD2 in HD3.
    fold (binom_cred p q n k) in HD3.
    rewrite -HD3 HD5.
    iIntros (Φ) "Herr HΦ".
    wp_apply (twp_binom_adv_comp with "Herr"); [done..|].
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
    (repeat (1 : fin 2) (fin_to_nat x) ++ repeat (0 : fin 2) (k - fin_to_nat x))%fin.

  Lemma binomial_to_bernoulli_length : ∀ (k : nat) (v : list (fin (S k))),
    length (binomial_to_bernoulli k v) = k * length v.
  Proof.
    induction v as [|h t]; simpl; first lia.
    rewrite !app_length IHt !repeat_length.
    assert (h < S k) by apply fin_to_nat_lt.
    lia.
  Qed.
  
  Fixpoint bernoulli_to_binomial_aux (k c : nat) (l : list (fin 2)) (acc : fin (S k)) : list (fin (S k)) :=
    match l,c with
    | [], _ => []
    | h::t, 0 => [fin_hsum h acc] ++ bernoulli_to_binomial_aux k (k - 1) t 0%fin
    | h::t, S m => bernoulli_to_binomial_aux k m t (fin_hsum h acc)
    end.

  Definition bernoulli_to_binomial (k : nat) (l : list (fin 2)) : list (fin (S k)) :=
    bernoulli_to_binomial_aux k (k - 1) l 0%fin.
  
  Lemma bernoulli_to_binomial_aux_app (k ct : nat) (l1 l2: list (fin 2)) (acc : fin (S k)) :
    length l1 = S ct → 
    bernoulli_to_binomial_aux k ct (l1 ++ l2) acc 
      = 
    [fin_hsum acc $ fin_sum_list 2 k l1] ++ bernoulli_to_binomial_aux k (k - 1) l2 0%fin.
  Proof.
    elim: l1 l2 k ct acc => /= [|h t IH] l2 k ct acc len_ct_eq_k; first lia.
    case: ct len_ct_eq_k => /= [len_ct_eq_k | ct len_ct_eq_k].
    - case: t IH len_ct_eq_k => // IH _ /=.
      f_equal.
      rewrite fin_hsum_comm fin_hsum_assoc; last done.
      fold (@fin_sum (S k)).
      rewrite fin_sum_0 //.
    - rewrite IH; last lia.
      rewrite fin_hsum_comm fin_hsum_assoc //.
  Qed.

  Lemma bernoulli_to_binomial_app_1 (k : nat) (l1 l2: list (fin 2)) :
    k ≠ 0 →
    length l1 = k → 
    bernoulli_to_binomial k (l1 ++ l2) = [fin_sum_list 2 k l1] ++ bernoulli_to_binomial k l2.
  Proof.
    move=> k_not_0 len_k.
    rewrite /bernoulli_to_binomial bernoulli_to_binomial_aux_app //; last lia.
  Qed.

  Lemma bernoulli_to_binomial_app_n (k n : nat) (l1 l2: list (fin 2)) :
    k ≠ 0 →
    length l1 = n * k →
    bernoulli_to_binomial k (l1 ++ l2) = bernoulli_to_binomial k l1 ++ bernoulli_to_binomial k l2.
  Proof.
    elim:n l1 l2 =>[|n IH l1 l2].
    - by case.
    - move=> k_pos len_l1.
      rewrite -{1}(take_drop k l1) -app_assoc
             bernoulli_to_binomial_app_1; try done; last first.
      { rewrite take_length Nat.min_l /=; lia. }
      rewrite IH; try done; last first.
      { rewrite drop_length len_l1; lia. }
      rewrite app_assoc -bernoulli_to_binomial_app_1; try lia; last first.
      { rewrite take_length Nat.min_l /=; lia. }
      rewrite (take_drop k l1) //.
  Qed.

  Lemma binomial_to_bernoulli_to_binomial (k : nat) (l : list (fin (S k))) : 
    (k ≠ 0)%nat → bernoulli_to_binomial k (binomial_to_bernoulli k l) = l.
  Proof.
    move=>k_pos.
    elim:l =>[|h t IHt].
    - rewrite /binomial_to_bernoulli /bernoulli_to_binomial /bernoulli_to_binomial_aux //.
    - rewrite (bernoulli_to_binomial_app_1 _ _ _ k_pos).
      + rewrite IHt /=.
        f_equal.
        rewrite /fin_sum_list foldr_app.
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
    | vh ::vt => 
        ∃ (pre suf : list (fin 2)), 
        fin_sum_list 2 k pre = vh ∧
        length pre = k ∧
        l = pre ++ suf ∧
        is_binomial_translation k vt suf
  end.

  Lemma is_binomial_translation_0 : ∀ (v : list (fin 1)) (l : list (fin 2)), is_binomial_translation 0 v l ↔ l = [].
  Proof.
    elim=>[|h t IH] l /=; first done.
    split.
    - intros ([|??] & suf & _ & len_pre & -> & is_tl_suf); last (simpl in len_pre; lia).
      simpl.
      apply IH, is_tl_suf.
    - move=> ->.
      exists [], [].
      split.
      { inv_fin h; first reflexivity.
        move=>h. inv_fin h.
      }
      split; first reflexivity.
      split; first reflexivity.
      apply IH.
      reflexivity.
  Qed.

  Lemma bernoulli_to_binomial_translation (k : nat) (l : list (fin 2)) (v : list (fin (S k))) :
    (0 < k)%nat →
    is_binomial_translation k v l ↔ ∃ n, length l = n * k ∧ v = bernoulli_to_binomial k l.
  Proof.
    elim: v l =>[|hv tv IH] [|hl tl] k_pos.
    - split; last done.
      move=>_.
      by exists 0.
    - split; first done.
      move=>/=[[|n] [len tsl]]; first lia.
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
    
  Definition own_binomial_tape (α : loc) (m n k : nat) (v : list (fin (S k))) : iProp Σ :=
    ∃ l, B_tape α m n l ∗ ⌜is_binomial_translation k v l⌝.

  Lemma B_tape_multiple_presample (e : expr) (α : loc) (Φ : val → iProp Σ)
      (N M k : nat) (ns : list (fin 2)) : 
    to_val e = None → 
    B_tape α N M ns ∗
    (∀ (l : list (fin 2)), ⌜length l = k⌝ -∗ B_tape α N M (ns ++ l) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }]
  .
  Proof.
    iRevert (Φ ns).
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

  Lemma binomial_tape_presample  (e : expr) (α : loc) (Φ : val → iProp Σ)
      (N M k : nat) (ns : list (fin (S k))) :
    to_val e = None
    → (0 < k)%nat
    → own_binomial_tape α N M k ns ∗
    (∀ (i : fin (S k)), own_binomial_tape α N M k (ns ++ [i%fin]) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }]
  .
  Proof.
    iIntros (e_not_val k_pos) "[(%l & Hα & %Hl) Hwp]".
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

  Lemma twp_binomial_tape (N M k : nat) (α : loc) (ns : list (fin (S k))) (n : fin (S k)) :
    [[{ own_binomial_tape α N M k (n::ns) }]]
      binom_tape (#lbl:α) #N #M #k
    [[{ RET #n ; own_binomial_tape α N M k ns }]].
  Proof.
    iIntros (Φ) "(%l & Htape & is_tl) HΦ".
    rewrite /binom_tape.
    unfold is_binomial_translation.
    fold is_binomial_translation.
    do 6 wp_pure.
    iAssert (⌜k ≤ k⌝)%I as "Hk"; first done.
    generalize k at 1 5 9.
    iIntros (k').
    iRevert (l α ns n Φ) "Hk Htape HΦ is_tl".
    iInduction k' as [|k'] "IH".
    - iIntros (l α ns n Φ) "%Hk Htape HΦ (%pre & %suf & <- & %len_pre & -> & %is_tl)".
      wp_pures.
      iModIntro.
      replace 0%Z with ((0%fin : fin (S k)) : Z); last done.
      destruct pre; last (simpl in len_pre; lia).
      simpl.
      iApply "HΦ".
      iExists suf.
      by iFrame.
    - iIntros (l α ns n Φ) "%Hk Htape HΦ (%pre & %suf & %sum & %len_pre & -> & %is_tl)".
      wp_pures.
      destruct pre as [|hpre tpre]; first (simpl in len_pre; lia).
      simpl in sum.
      inv_fin hpre.
      + move=>/= sum len_pre.
        wp_apply (twp_B_tape α N M _ _ _ with "Htape").
        iIntros "Htape".
        wp_pure.
        replace (S k' - 1)%Z with (k' : Z); last lia.
        wp_apply ("IH" $! _ _ ns with "[] Htape [HΦ]"); last first; last (iPureIntro; lia).
        { iPureIntro.
          exists tpre, suf.
          auto.
        }
        iIntros "Htape".
        wp_pures.
        rewrite Z.add_0_r sum.
        iModIntro.
        by iApply "HΦ".
      + move=>/= i.
        inv_fin i; last (move=>i; inv_fin i).
        move=>/= sum len_pre.
        wp_apply (twp_B_tape α N M _ _ _ with "Htape").
        iIntros "Htape".
        wp_pure.
        replace (S k' - 1)%Z with (k' : Z); last lia.
        wp_apply ("IH" $! _ _ ns with "[] Htape [HΦ]"); last first; last (iPureIntro; lia).
        { iPureIntro.
          exists tpre, suf.
          auto.
        }
        iIntros "Htape".
        wp_pures.
        rewrite -sum fin_succ_to_nat.
        replace (S k - 1)%nat with k; last lia.
        rewrite Nat.min_l; last first.
        { transitivity (S k'); last lia.
          rewrite -len_pre -Nat.succ_le_mono.
          etrans; first apply fin_sum_list_le; first done.
          lia.
        }
        rewrite -Nat2Z.inj_add Nat.add_1_r.
        iModIntro.
        iApply ("HΦ" with "Htape").
  Qed.

  Lemma twp_binomial_tape_planner 
      (N M k : nat) (e : expr) (ε : nonnegreal)
      (L : nat) (α : loc) (Φ : val → iProp Σ)
      (prefix : list (fin (S k))) (suffix : list (fin (S k)) → list (fin (S k))) :
    (0 < N)%nat →
    (N < S M)%nat →
    (0 < k)%nat → 
    to_val e = None →
    (∀ junk : list (fin (S k)),
       (0 < length (suffix (prefix ++ junk)) <= L)%nat) →
    (0 < ε)%R →
    ↯ ε ∗ own_binomial_tape α N M k prefix ∗
    ( (∃ (junk : list (fin (S k))), own_binomial_tape α N M k (prefix ++ junk ++ suffix (prefix ++ junk))) -∗ WP e [{ Φ }]
    ) ⊢ WP e [{ Φ }].
  Proof.
    iIntros (N_pos N_lt_SM k_pos e_not_val suf_bound ε_pos)
      "(Herr & (%l & Hα & %is_tl) & Hnext)".
    set (suf_tl (lst : list (fin 2)) :=
           let r := (k - (length lst) `mod` k) `mod` k in
           let padding := repeat 0%fin r in
           padding ++ binomial_to_bernoulli k (suffix (bernoulli_to_binomial k (lst ++ padding)))
        ).
    apply bernoulli_to_binomial_translation in is_tl as (n & len_l & pref_eq); last done.
    wp_apply (B_tape_planner _ _ _ _ ((1 + L) * k) _ _ _ suf_tl); last iFrame; try done.
    { move=>junk.
      unfold suf_tl.
      rewrite app_length binomial_to_bernoulli_length.
      rewrite -app_assoc (bernoulli_to_binomial_app_n _ n); [|lia|done].
      rewrite -pref_eq.
      rewrite repeat_length app_length.
      match goal with
      | |- (_ < ?X + k * ?Y ≤ _)%nat =>
          set (A := X);
          set (B := Y);
          assert (A < k) by (apply Nat.mod_upper_bound; lia);
          assert (0 < B ≤ L) as [bound_left bound_right]by apply suf_bound
      end.
      fold A in B.
      fold B.
      split; first lia.
      rewrite Nat.mul_comm Nat.mul_add_distr_r.
      apply Nat.add_le_mono; first lia.
      by apply Nat.mul_le_mono_r.
    }
    iIntros "(%junk & Hα)".
    wp_apply "Hnext".
    set (junk' := junk ++ repeat 0%fin ((k - length junk `mod` k) `mod` k)).
    iExists (bernoulli_to_binomial k junk').
    unfold own_binomial_tape.
    iExists _.
    iFrame.
    iPureIntro.
    rewrite bernoulli_to_binomial_translation; last done.
    set (s :=
           suffix
             (bernoulli_to_binomial k
                ((l ++ junk) ++
                   repeat 0%fin
                   ((k - (n * k + length junk) `mod` k)
                      `mod` k)))).
    set (n0 := n + length junk `div` k + (if bool_decide (length junk `mod` k = 0) then 0 else 1) + length s).
     
    eexists n0.
    split.
    {
      rewrite /suf_tl /= !app_length len_l binomial_to_bernoulli_length.
      fold s.
      rewrite (Nat.add_comm (n * k) (length junk)) Nat.Div0.mod_add repeat_length.
      rewrite {1}(Nat.Div0.div_mod (length junk) k).
      unfold n0.
      case_bool_decide as H.
      {
        rewrite H Nat.sub_0_r Nat.Div0.mod_same Nat.add_0_r /=.
        lia.
      }
      { 
        assert (0 < length junk `mod` k) by lia.
        rewrite (Nat.mod_small (_ - _)); last lia.
        rewrite (Nat.add_assoc _ (k - (_ `mod` _))) Nat.add_sub_assoc; last first.
        {  assert (length junk `mod` k < k) by (apply Nat.mod_upper_bound; lia).
           lia.
        }
        lia.
      }
    }
    unfold suf_tl.
    rewrite app_length len_l.
    fold s.
    rewrite pref_eq (bernoulli_to_binomial_app_n k n); try lia.
    f_equal.
    set (n1 := length junk `div` k  +
                 if bool_decide (length junk `mod` k = 0)
                 then 0
                 else 1).
    rewrite app_assoc (bernoulli_to_binomial_app_n k n1); try lia; last first.
    {
      rewrite  app_length repeat_length (Nat.add_comm (n * k) (length junk)) Nat.Div0.mod_add {1}(Nat.Div0.div_mod (length junk) k).
      unfold n1.
      case_bool_decide as H.
      {
        rewrite H !Nat.add_0_r Nat.sub_0_r Nat.Div0.mod_same.
        lia.
      }
      {
        assert (0 < length junk `mod` k < k ) by (split; last apply Nat.mod_upper_bound; lia).
        rewrite (Nat.mod_small (_ - _)); last lia.
        rewrite Nat.add_sub_assoc; lia.
      }
    }
    unfold junk', s.
    rewrite !(Nat.add_comm (n * k) _) Nat.Div0.mod_add.
    f_equal.
    rewrite binomial_to_bernoulli_to_binomial; last lia.
    rewrite -app_assoc (bernoulli_to_binomial_app_n k n l) //.
    lia.
  Qed.
   
  Lemma B_tape_multiple_adv_comp :
    ∀ (e : expr) (α : loc) (Φ : val → iProp Σ)
      (p q n : nat) (ns : list (fin 2)) (ε : R)
      (D : fin (S n) → R),
    (∀ (i : fin (S n)), 0 <= D i)%R →
    SeriesC (λ k : fin (S n), (binom_prob p q n k * D k)%R) = ε →
    (p ≤ q + 1)%nat →
    to_val e = None →
    B_tape α p q ns ∗ ↯ ε ∗
    (∀ (ts : list (fin 2)), ⌜length ts = n⌝ →  ↯ (D (fin_sum_list _ _ ts)) ∗ B_tape α p q (ns ++ ts) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }]
  .
  Proof.
    iIntros (e α Φ p q n).
    iRevert (Φ).
    iInduction (n) as [|n] "IH";
      iIntros (Φ l ε D D_pos D_sum p_q_prob e_not_val) "(Hα & Herr & Hnext)".
    - wp_apply ("Hnext" $! []); first done.
      simpl.
      rewrite -D_sum SeriesC_finite_foldr /= Rplus_0_r binom_prob_0 Rmult_1_l app_nil_r.
      iFrame.
    - rewrite -{7}(Nat.add_1_r n) ec_binom_split in D_sum.
      match type of D_sum with
      | (_ * ?S0 + _ * ?S1 = _)%R => set (s0 := S0);
                                 set (s1 := S1)
      end.
      set (D' (i : fin 2) := match i with Fin.F1 _ => s0 | _ => s1 end). 
      wp_apply (B_tape_adv_comp _ _ _ p q _ ε D'); try done.
      { move=>i.
        unfold D', s0, s1.
        assert (0 <= p)%R by apply pos_INR.
        assert (0 <= q)%R by apply pos_INR.
        assert (0 <= p / (q + 1))%R.
        {
          apply Rcomplements.Rdiv_le_0_compat; lra.
        }
        assert (0 <= 1 - p / (q + 1))%R.
        {
          apply Rle_0_le_minus.
          apply Rcomplements.Rle_div_l; first lra.
          rewrite Rmult_1_l -INR_1 -plus_INR.
          by apply le_INR.
        } 
        full_inv_fin; apply: SeriesC_ge_0;
          [|apply ex_seriesC_finite|..|apply ex_seriesC_finite];
          move=>k;
                apply Rmult_le_pos;
                [|apply D_pos|..|apply D_pos];
                rewrite /binom_prob;
                repeat apply Rmult_le_pos;
                try apply choose_pos; by apply pow_le.
      }
      { rewrite -D_sum.
        fold s0 s1 (D' 0%fin) (D' 1%fin).
        lra.
      }
      iFrame.
      iIntros (i) "[Herr Hα]".
      full_inv_fin.
      { wp_apply ("IH" $! _ _ s0 (D ∘ fin_S_inj)); try done.
        { iPureIntro.
          move=>i.
          apply D_pos.
        }
        iFrame.
        iIntros (ts len_ts) "[Herr Hα]".
        wp_apply ("Hnext" $! 0%fin::ts); first rewrite /= len_ts //.
        rewrite -app_assoc /=.
        iFrame.
        rewrite fin_inj_sum //.
        lia.
      }
      { wp_apply ("IH" $! _ _ s1 (D ∘ FS)); try done.
        { iPureIntro.
          move=>i.
          apply D_pos.
        }
        iFrame.
        iIntros (ts len_ts) "[Herr Hα]".
        wp_apply ("Hnext" $! 1%fin::ts); first rewrite /= len_ts //.
        rewrite -app_assoc /=.
        iFrame.
        rewrite fin_inj_sum; last lia.
        rewrite fin_succ_inj //.
      }
  Qed.
        
  Lemma twp_binomial_tape_adv_comp :
    ∀ (e : expr) (α : loc) (Φ : val → iProp Σ)
      (p q n : nat) (ns : list (fin (S n))) (ε : R)
      (D : fin (S n) → R),
    (∀ (i : fin (S n)), 0 <= D i)%R →
    SeriesC (λ k : fin (S n), (binom_prob p q n k * D k)%R) = ε →
    (p ≤ q + 1)%nat →
    to_val e = None →
    own_binomial_tape α p q n ns ∗ ↯ ε ∗
    (∀ (i : fin (S n)), ↯ (D i) ∗ own_binomial_tape α p q n (ns ++ [i]) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }]
  .
  Proof.
    iIntros (e α Φ p q n ns ε D D_pos D_sum is_prob e_not_val) "((%l & Htape & %is_tl) & Herr & Hnext)".
    destruct n as [|n].
    {
      rewrite SeriesC_finite_foldr /= binom_prob_0 /= Rplus_0_r Rmult_1_l in D_sum.
      iApply "Hnext".
      rewrite -D_sum.
      iFrame.
      iPureIntro.
      apply is_binomial_translation_0 in is_tl.
      by apply is_binomial_translation_0.
    } 
    wp_apply (B_tape_multiple_adv_comp _ _ _ _ _ (S n) _ _ D D_pos D_sum is_prob e_not_val).
    iFrame.
    iIntros (ts len_ts) "[Herr Hα]".
    wp_apply "Hnext".
    iFrame.
    iPureIntro.
    rewrite bernoulli_to_binomial_translation in is_tl; last lia.
    destruct is_tl as (k & len_l & ns_eq_tl). 
    rewrite bernoulli_to_binomial_translation; last lia.
    exists (S k).
    split.
    { rewrite app_length.
      lia.
    }
    rewrite ns_eq_tl (bernoulli_to_binomial_app_n _ k); try lia.
    f_equal.
    rewrite -{2}(app_nil_r ts) bernoulli_to_binomial_app_1; try lia.
    reflexivity.
  Qed.

End binomial.
#[global] Opaque binomial.
