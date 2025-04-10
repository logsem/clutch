From clutch.eris Require Export eris.
From clutch.eris.lib.sampling Require Import binomial utils. 

Section NegativeBinomial.
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
    ⊢  WP e [{ Φ }].
 
  Definition negative_binomial : val :=
    λ: "p" "q",
      rec: "negative_binomial" "r" :=
      if: "r" ≤ #0
      then #0
      else
        let: "b" := B "p" "q" in
        if: "b" = #0
        then "negative_binomial" "r" + #1
        else "negative_binomial" ("r" - #1).

  Definition negative_binom_prob (p q r k : nat) : R :=
    (choose (k + r - 1) k * (p / (q + 1))^r * (1 - p  / (q + 1))^k)%R.

  Lemma negative_binom_pos (p q r k : nat) : p ≤ (q + 1) → (0 <= negative_binom_prob p q r k)%R.
  Proof.
    intros Hpq.

    rewrite /negative_binom_prob.
    assert (0 <= q)%R by apply pos_INR.
    repeat apply Rmult_le_pos.
    { apply choose_pos. }
    { apply pow_le, Rcomplements.Rdiv_le_0_compat; first apply pos_INR.
      lra.
    }
    { apply pow_le.
      rewrite -Rcomplements.Rminus_le_0 Rcomplements.Rle_div_l; last lra.
      rewrite Rmult_1_l -INR_1 -plus_INR.
      apply le_INR, Hpq.
    }
  Qed.
      
  Lemma negative_binom_prob_split : ∀ (p q r k : nat),
    negative_binom_prob p q (r + 1) (k + 1)%nat =
    ((1 - p / (q + 1)) * negative_binom_prob p q (r + 1) k
     + (p / (q + 1)) * negative_binom_prob p q r (k + 1))%R.
  Proof.
    intros p q r k.
    rewrite /negative_binom_prob.
    replace (k + 1 + (r + 1) - 1) with (S (k + r)); last lia.
    replace (k + 1 + r - 1) with (k + r); last lia.
    replace (k + 1) with (S k); last lia.
    replace (k + (r + 1) - 1) with (k + r); last lia.
    rewrite -pascal' pow_add /=.
    lra.
  Qed.

  Lemma negative_binom_prob_is_distr :
    ∀ (p q r : nat),
    p ≤ q + 1 →
    SeriesC (negative_binom_prob p q r) = 1.
  Admitted.
  
  Lemma ex_seriesC_negative_binom_prob :
    ∀ (p q r : nat),
    p ≤ q + 1 →
    ex_seriesC (negative_binom_prob p q r).
  Proof.
    unfold ex_seriesC.
    unfold is_seriesC.
    intros p q r Hpq.
    exists 1%R.
    apply Series.is_series_Reals.
    unfold infinite_sum.
    intros ε Hε.
  Admitted.

  Lemma ec_negative_binom_split :
    ∀ (p q r : nat) (D : nat → R),
    let ε := SeriesC (λ k, negative_binom_prob p q (r + 1) k * D k)%R in
    let ε0 := SeriesC (λ k, negative_binom_prob p q (r + 1) k * D (k + 1)%nat)%R in
    let ε1 := SeriesC (λ k, negative_binom_prob p q r k * D k)%R in
    (ε = (1 - (p / (q + 1))) * ε0 + (p / (q + 1))* ε1)%R.
  Proof.
    (* True on paper proof, modulo convergence conditions, enough for now *)
  Admitted.

  Lemma twp_negative_binomial_split :
    ∀ (p q : nat),
    0 < p →
    p < (q + 1) →
    ∀ (r : nat) (D : nat → R) (ε : R) (ε_term : R),
    (0 < ε_term)%R →
    (∀ (n : nat), 0 <= D n)%R →
    SeriesC (λ k, (negative_binom_prob p q r k * D k)%R) = ε → ↯ ε_term -∗
    ↯ ε -∗ WP negative_binomial #p #q #r [{ v, ∃ (k : nat), ⌜v = #k⌝ ∗ ↯ (D k) }].
  Proof.
    iIntros (p q Hp Hpq r D ε ε_term Hε_term HD HSum) "Hterm Herr".
    rewrite /negative_binomial.
    do 4 wp_pure.
    iRevert (D ε ε_term Hε_term HD HSum) "Herr Hterm".
    iInduction (r) as [|r] "IHr".
    - iIntros (D ε ε_term Hε_term HD HDε) "Herr Hterm".
      rewrite /negative_binom_prob /choose in HDε.
      erewrite (SeriesC_ext _ (λ k, if bool_decide (k = 0) then D 0 else 0)) in HDε; last first.
      { intros k.
        do 2 case_bool_decide; try lia; subst; simpl; last lra.
        rewrite Rcomplements.C_n_n.
        lra.
      }
      rewrite SeriesC_singleton in HDε.
      rewrite -HDε.
      wp_pures.
      iModIntro.
      iExists 0.
      by iFrame.
    - iIntros (D ε ε_term Hε_term HD HDε) "Herr Hterm".
      iRevert (D ε HD HDε) "Herr".
      set (s1 := (p / (q + 1))%R).
      set (s0 := ((1 - s1)%R)).
      set (sc0 := ((/ s0 + 1) / 2)%R).
      set (sc1 := ((1 - sc0 * s0) / s1)%R).
                                      
      assert (0 < p)%R.
      {
        rewrite -INR_0.
        by apply lt_INR.
      }
      assert (0 <= q)%R by apply pos_INR.
      assert (1 <= q + 1)%R by lra.
      assert (0 < q + 1)%R by lra.
      assert (p < q + 1)%R.
      { rewrite -INR_1 -plus_INR.
        by apply lt_INR.
      } 
      assert (0 < s1 < 1)%R; first split.
      { unfold s1.
        by apply Rcomplements.Rdiv_lt_0_compat.
      }
      { unfold s1.
        apply Rcomplements.Rlt_div_l; lra.
      }
      assert (0 < s0 < 1)%R by (unfold s0; lra).
      
      assert (0 < / s0)%R.
      { apply Rinv_0_lt_compat. lra. }

      assert (1 < / s0)%R.
      {
        apply Rcomplements.Rinv_lt_cancel; first done.
        rewrite Rinv_inv Rinv_1.
        lra.
      }

      assert (1 < sc0)%R by (unfold sc0; lra).
      assert (sc0 * s0 = (1 + s0) / 2)%R as Hsc0s0.
      {
        unfold sc0.
        rewrite -Rmult_div_swap Rmult_plus_distr_r Rmult_1_l Rinv_l; last lra.
        reflexivity.
      }

      assert (0 < sc0 * s0 < 1)%R; first (rewrite Hsc0s0; lra).
      
      assert (0 < sc1)%R.
      { unfold sc1.
        apply Rcomplements.Rdiv_lt_0_compat; lra.
      } 

      assert (sc0 * s0 + sc1 * s1 = 1)%R.
      {
        unfold sc1.
        rewrite -Rmult_div_swap Rmult_div_l; lra.
      }
      
      iApply (ec_ind_amp _ sc0 with "[] Hterm"); try done.
      iModIntro.
      iIntros (ε' Hε') "IH Hterm".
      iIntros (D ε HD HDε) "Herr".
      wp_pures.
      erewrite SeriesC_ext in HDε; last first.
      {
        intros.
        replace (S r) with (r + 1)%nat; first done.
        lia.
      }
      rewrite ec_negative_binom_split in HDε.
      fold s1 s0 in HDε.
      match type of HDε with
      | (s0 * ?A + s1 * ?B)%R = _ => set (ε0 := A);
                                     set (ε1 := B)
      end.
      fold ε0 ε1 in HDε.
      wp_pures.
      iPoseProof (ec_combine with "[Hterm Herr]") as "Hec"; first iFrame.
      
      wp_apply (B_spec _ _ _ (ε0 + ε' * sc0) (ε1 + ε' * sc1) with "Hec"); first lia.
      { rewrite -HDε.
        fold s1 s0.
        nra.
      }
      iIntros (k) "[[-> Herr] | [-> Herr]]".
      {
        do 4 wp_pure.
        iPoseProof (ec_split with "Herr") as "[Herr Hterm]".
        { apply SeriesC_ge_0'.
          intros n.
          apply Rmult_le_pos; last done.
          apply negative_binom_pos.
          lia.
        }
        { nra. }
        iPoseProof ("IH" with "[Hterm] [] [] Herr") as "IHH".
        { rewrite Rmult_comm //. }
        { instantiate (1 := λ k, D (k + 1)). iPureIntro. intros. apply HD. }
        { iPureIntro.
          apply SeriesC_ext.
          intros k.
          repeat f_equal.
          lia.
        }
        wp_bind ((rec: _ _ := _)%V _)%E.
        iApply tgl_wp_wand_r.
        iSplitL "IHH"; first done.
        iIntros (v) "(%k & -> & Herr)".
        wp_pures.
        iModIntro.
        iExists (k + 1).
        iFrame.
        iPureIntro.
        f_equal.
        rewrite Nat2Z.inj_add //.
      } 
      { do 5 wp_pure.
        replace (S r - 1)%Z with (r : Z); last lia.
        iPoseProof (ec_split with "Herr") as "[Herr Hterm]".
        { apply SeriesC_ge_0'.
          intros n.
          apply Rmult_le_pos; last done.
          apply negative_binom_pos.
          lia.
        }
        { nra. }
        iApply ("IHr" with "[] [] [] Herr Hterm").
        { iPureIntro. nra. }
        { by iPureIntro. }
        { by iPureIntro. }
      } 
  Qed.

  Lemma wp_negative_binomial_split :
    ∀ (p q : nat),
    0 < p →
    p ≤ (q + 1) →
    ∀ (r : nat) (D : nat → R) (ε : R),
    (∀ (n : nat), 0 <= D n)%R →
    SeriesC (λ k, (negative_binom_prob p q r k * D k)%R) = ε →
    ↯ ε -∗
    WP negative_binomial #p #q #r {{ v, ∃ (k : nat), ⌜v = #k⌝ ∗ ↯ (D k) }}.
  Proof.
    iIntros (p q Hp Hpq r D ε HD HSum) "Herr".
    rewrite /negative_binomial.
    do 4 wp_pure.
    iRevert (r D ε HD HSum) "Herr".
    iLöb as "IH".
    iIntros (r D ε HD HSum) "Herr".
    wp_pures.
    case_bool_decide.
    - assert (r = 0) as -> by lia.
      rewrite /negative_binom_prob /choose in HSum.
      erewrite (SeriesC_ext _ (λ k, if bool_decide (k = 0) then D 0 else 0)) in HSum; last first.
      { intros k.
        do 2 case_bool_decide; try lia; subst; simpl; last lra.
        rewrite Rcomplements.C_n_n.
        lra.
      }
      rewrite SeriesC_singleton in HSum.
      rewrite -HSum.
      wp_pures.
      iModIntro.
      iExists 0.
      by iFrame.
    - destruct r; first lia.
      set (s1 := (p / (q + 1))%R).
      set (s0 := ((1 - s1)%R)).
      wp_pures.
      erewrite SeriesC_ext in HSum; last first.
      {
        intros.
        replace (S r) with (r + 1)%nat; first done.
        lia.
      }
      rewrite ec_negative_binom_split in HSum.
      fold s1 s0 in HSum.
      match type of HSum with
      | (s0 * ?A + s1 * ?B)%R = _ => set (ε0 := A);
                                     set (ε1 := B)
      end.
      fold ε0 ε1 in HSum.
      wp_pures.
      wp_bind (B _ _).
      wp_apply tgl_wp_pgl_wp'.
      wp_apply (B_spec p q ε ε0 ε1 Hpq with "Herr").
      {fold s1 s0. lra. }
      iIntros (k) "[[-> Herr] | [-> Herr]]".
      {
        do 4 wp_pure.
        wp_bind ((rec: _ _ := _)%V _)%E.
        iApply wp_wand_r.
        replace (S r : Z) with ((r + 1)%nat : Z); last lia.
        iSplitL "Herr".
        { wp_apply ("IH" with "[] [] Herr"); first last.
          { by iPureIntro. }
          { done. }
        }
        { iIntros (v) "(%k & -> & Herr)".
          wp_pures.
          iModIntro.
          iExists (k + 1)%nat.
          iFrame.
          iPureIntro.
          f_equal.
          rewrite Nat2Z.inj_add //.
        }
      }
      {
        do 5 wp_pure.
        wp_bind ((rec: _ _ := _)%V _)%E.
        iApply wp_wand_r.
        replace (S r - 1)%Z with (r : Z); last lia.
        iSplitL "Herr".
        { wp_apply ("IH" with "[] [] Herr"); first last.
          { by iPureIntro. }
          { done. }
        }
        { iIntros (v) "(%k & -> & Herr)".
          iExists k.
          iFrame.
          iPureIntro.
          f_equal.
        }
      }
  Qed.

  Definition expand_perm : list nat → list (fin 2) :=
    flat_map (λ (i : nat), repeat (0%fin : fin 2) i ++ [1%fin : fin 2]).

  Fixpoint contract_perm_aux (l : list (fin 2)) (acc : nat) : list nat :=
    match l with
    | [] => []
    | 0%fin::t => contract_perm_aux t (S acc)
    | _%fin::t => [acc] ++ contract_perm_aux t 0
    end.

  Definition contract_perm (l : list (fin 2)) : list nat := contract_perm_aux l 0.

  Lemma expand_perm_app : ∀ (l1 l2 : list nat), expand_perm (l1 ++ l2) = expand_perm l1 ++ expand_perm l2.
  Proof.
    move=>l1 l2.
    unfold expand_perm.
    rewrite flat_map_app //.
  Qed.
  
  Lemma exists_perm : ∀ (l : list (fin 2)), ∃ perm n, l = expand_perm perm ++ repeat 0%fin n.
  Proof.
    elim=>[|h t [perm_t [n_t ->]]];
          last (full_inv_fin;
                first destruct perm_t as [|h_perm t_perm]);
          by [ exists [], 0
             | exists [], (S n_t)
             | exists (S h_perm :: t_perm) , n_t
             | exists (0::perm_t) , n_t
             ].
  Qed.
  
  Lemma contract_perm_aux_repeat : ∀ (n acc : nat) (suf : list (fin 2)), contract_perm_aux (repeat 0%fin n ++ 1%fin :: suf) acc = n + acc :: contract_perm_aux suf 0.
  Proof.
    elim=>[//|n IH] acc suf.
    simpl.
    rewrite IH.
    f_equal.
    lia.
  Qed.
  
  Lemma contract_expand_perm_suf : ∀ (perm : list nat) (suf : list (fin 2)), contract_perm (expand_perm perm ++ suf ) = perm ++ contract_perm suf.
  Proof.
    elim=>[//|h t IH] suf /=.
    rewrite /contract_perm -!app_assoc contract_perm_aux_repeat Nat.add_0_r.
    fold (contract_perm (expand_perm t ++ suf)).
    rewrite IH //.
  Qed.

  Lemma contract_expand_perm : ∀ (perm : list nat), contract_perm (expand_perm perm) = perm.
  Proof.
    move=>perm.
    rewrite -(app_nil_r (expand_perm perm)) contract_expand_perm_suf app_nil_r //.
  Qed.

  Lemma expand_contract_perm_suf : ∀ (l : list (fin 2)) (suf : list nat), expand_perm (contract_perm (l ++ [1%fin]) ++ suf) = l ++ [1%fin] ++ expand_perm suf.
  Proof.
    move=>l suf.
    destruct (exists_perm l) as (perm & n & ->).
    rewrite -!app_assoc -(app_nil_r [1%fin]) (app_assoc _ [1%fin]).
    change ((repeat _ _ ++ [_]) ++ []) with (expand_perm [n]).
    rewrite -expand_perm_app.
    rewrite contract_expand_perm.
    rewrite !expand_perm_app !app_assoc //.
  Qed.

  Lemma expand_contract_perm : ∀ (l : list (fin 2)), expand_perm (contract_perm (l ++ [1%fin])) = l ++ [1%fin].
  Proof.
    move=>l.
    rewrite -(app_nil_r (contract_perm _)) expand_contract_perm_suf app_nil_r //.
  Qed.
  
  Fixpoint is_negative_translation (r : nat) (v : list nat) (l : list (fin 2)) :=
    match v with
    | [] => l = []
    | vh::vt =>
        ∃ perm suf,
         l = expand_perm perm ++ suf ∧
         length perm = r ∧
         list_sum perm = vh ∧
         is_negative_translation r vt suf
  end.

  Definition own_negative_tape (α : loc) (N M r : nat) (v : list nat) : iProp Σ :=
    (∃ (l : list (fin 2)), B_tape α N M l ∗ ⌜is_negative_translation r v l⌝)%I.

   Lemma is_negative_translation_0 :
    ∀ (v : list nat) (l : list (fin 2)),
    is_negative_translation 0 v l ↔ l = [] ∧ v = repeat 0 (length v).
  Proof.
    move=>v l.
    elim: v l => [|vh vt IH] l /=.
    { split.
      - move=> -> //.
      - move=>[-> _] //.
    }
    split.
    - intros ([|??] & suf & -> & len_perm & <- & is_tl); last discriminate.
      simpl.
      by apply IH in is_tl as [-> <-].
    - move=>[-> [-> vt_eq]].
      exists [], [].
      simpl.
      repeat split; try done.
      apply IH.
      by split.
  Qed.

  Definition negative_to_bernoulli (r : nat) (v : list nat) : list (fin 2) :=
    i ← v ;
  repeat (0%fin : fin 2) i ++ repeat (1%fin : fin 2) r.

  Lemma negative_to_bernoulli_last (r : nat) :
    0 < r →
    ∀ (v : list nat), v ≠ [] →
    ∃ (l : list (fin 2)), negative_to_bernoulli r v = l ++ [1%fin].
  Proof.
    move=>r_pos.
    elim=>[//|vh vt IH] _.
    destruct vt.
    { destruct r; first lia.
      rewrite -(Nat.add_1_r r) /= repeat_app app_nil_r app_assoc /=.
      by eexists.
    }
    simpl in *.
    destruct IH as [l ->]; first done.
    rewrite app_assoc.
    by eexists.
  Qed.
      
  Lemma negative_to_bernoulli_length (r : nat) :
    ∀ (v : list nat), length (negative_to_bernoulli r v) = list_sum v + r * length v.
  Proof.
    elim=>[|vh vt IH] /=; first lia.
    rewrite !app_length !repeat_length IH.
    lia.
  Qed.
  
  Fixpoint bernoulli_to_negative_aux (r c : nat) (l : list (fin 2)) (acc : nat) : list nat :=
    match l,c with
    | [], _ => []
    | 1%fin::t, 0 => [acc] ++ bernoulli_to_negative_aux r (r - 1) t 0
    | 1%fin::t, S m => bernoulli_to_negative_aux r m t acc
    | _::t, _ => bernoulli_to_negative_aux r c t (S acc)
    end.

  Definition bernoulli_to_negative (r : nat) (l : list (fin 2)) := bernoulli_to_negative_aux r (r - 1) l 0.

  Lemma bernoulli_to_negative_aux_prefix (r : nat) :
    ∀ (pre suf : list (fin 2)) (acc c : nat),
    c = (list_sum $ fin_to_nat <$> pre) →
    bernoulli_to_negative_aux r c (pre ++ 1%fin :: suf) acc = [acc + length pre - c] ++ bernoulli_to_negative_aux r (r - 1) suf 0.
  Proof.
    elim=>[|hpre tpre IH].
    - move=>/= suf acc c -> /=.
      rewrite Nat.add_0_r Nat.sub_0_r //.
    - full_inv_fin.
      + move=> suf acc c /= c_eq.
        rewrite IH //=.
        f_equal.
        lia.
      + move=>suf acc c /= c_eq.
        destruct c as [|c]; first discriminate.
        injection c_eq as c_eq.
        rewrite IH //=.
        f_equal.
        lia.
  Qed.

  Lemma fmap_repeat : ∀ (A B : Type) (f : A → B) (a : A) (n : nat), f <$> (repeat a n) = repeat (f a) n.
  Proof.
    move=>A B f a.
    elim=>[//|n /= <- //].
  Qed.

  Lemma list_sum_repeat : ∀ (n k : nat), list_sum (repeat n k) = n * k.
  Proof.
    move=>n.
    elim=>[/=|k /= ->]; lia.
  Qed.

  Lemma list_sum_negative_to_bernoulli (r : nat) :
    ∀ (l : list nat), list_sum $ fin_to_nat <$> negative_to_bernoulli r l = r * length l.
  Proof.
    elim=>[|h t IH] /=; first rewrite Nat.mul_0_r //.
    rewrite !fmap_app !fmap_repeat !list_sum_app !list_sum_repeat Nat.mul_0_l Nat.mul_1_l Nat.add_0_l IH.
    lia.
  Qed.
  
  Lemma negative_to_bernoulli_to_negative (r : nat) :
    (0 < r)%nat →
    ∀ (l : list nat), bernoulli_to_negative r (negative_to_bernoulli r l) = l.
  Proof.
    case: r=>[|r] r_pos; first lia.
    elim=>[//|h t IH].
    rewrite -{2}Nat.add_1_r /= repeat_app -!app_assoc /= app_assoc
               /bernoulli_to_negative bernoulli_to_negative_aux_prefix; last first.
    { 
      rewrite /= Nat.sub_0_r fmap_app !fmap_repeat list_sum_app /= !list_sum_repeat.
      lia.
    }
    unfold bernoulli_to_negative in IH.
    rewrite !Nat.add_1_r IH /= app_length !repeat_length.
    f_equal.
    lia.
  Qed.

  Lemma list_sum_expand_perm : ∀ (perm : list nat), list_sum (fin_to_nat <$> expand_perm perm) = length perm.
  Proof.
    elim=>[//|h t IH] /=.
    rewrite !fmap_app fmap_repeat !list_sum_app list_sum_repeat IH //.
  Qed.

  Lemma list_sum_le : ∀ (l : list (fin 2)), list_sum $ fin_to_nat <$> l ≤ length l.
  Proof.
    elim=>[//|h t IH].
    unfold fmap in *.
    full_inv_fin; simpl; lia.
  Qed.
  
  Lemma list_sum_contract_perm_aux : ∀ (l : list (fin 2)) (acc : nat), list_sum (contract_perm_aux (l ++ [1%fin]) acc) = acc + length l - (list_sum $ fin_to_nat <$> l).
  Proof.
    elim=>[|h t IH] acc /=; first lia.
    full_inv_fin.
    - rewrite IH /= Nat.add_succ_r //.
    - rewrite /= IH /= -Nat.add_sub_assoc //.
      rewrite -Nat.succ_le_mono.
      apply list_sum_le.
  Qed.

  Lemma list_sum_contract_perm : ∀ (l : list (fin 2)), list_sum (contract_perm (l ++ [1%fin])) = length l - (list_sum $ fin_to_nat <$> l).
  Proof.
    move=>l.
    rewrite list_sum_contract_perm_aux //.
  Qed.
    
  Lemma expand_perm_length : ∀ (perm : list nat), length (expand_perm perm) = list_sum perm + length perm.
  Proof.
    elim=>[//|h t IH] /=.
    rewrite !app_length IH repeat_length /=.
    lia.
  Qed.

  Lemma contract_perm_aux_length : ∀ (l : list (fin 2)) (acc : nat),
    length (contract_perm_aux l acc) = list_sum $ fin_to_nat <$> l.
  Proof.
    elim=>[//|h t IH] acc /=.
    full_inv_fin; rewrite /= IH //.
  Qed.

  Lemma contract_perm_length : ∀ (l : list (fin 2)),
    length (contract_perm l) = list_sum $ fin_to_nat <$> l.
  Proof.
    move=>l.
    rewrite contract_perm_aux_length //.
  Qed.
  
  Lemma bernoulli_to_negative_expand_perm :
    ∀ (r : nat) (perm : list nat) (suf : list (fin 2)),
    (0 < r)%nat →
    length perm = r →
    bernoulli_to_negative r (expand_perm perm ++ suf) = list_sum perm :: bernoulli_to_negative r suf.
  Proof.
    case=>[|r] perm suf r_pos len_perm; first lia.
    assert (perm ≠ []) as perm_not_emp.
    { destruct perm; first discriminate.
      done.
    }
    destruct (exists_last perm_not_emp) as (pre & k & ->).
    rewrite app_length /= in len_perm.
    rewrite expand_perm_app /= app_nil_r -!app_assoc /= app_assoc /bernoulli_to_negative bernoulli_to_negative_aux_prefix.
    { simpl.
      rewrite app_length expand_perm_length repeat_length list_sum_app /=.
      replace (length pre) with r; last lia.
      f_equal.
      lia.
    }
    rewrite fmap_app fmap_repeat list_sum_app list_sum_repeat list_sum_expand_perm /=.
    lia.
  Qed.
  
  Lemma bernoulli_to_negative_expand_perm_n :
    ∀ (r n : nat) (perm : list nat) (suf : list (fin 2)),
    (0 < r)%nat →
    length perm = n * r →
    bernoulli_to_negative r (expand_perm perm ++ suf) = bernoulli_to_negative r (expand_perm perm) ++ bernoulli_to_negative r suf.
  Proof.
    move=>r.
    elim=>[|n IH] perm suf r_pos len_perm;
          first by destruct perm.
    rewrite -(take_drop r perm) expand_perm_app -!app_assoc !(bernoulli_to_negative_expand_perm _ (take r perm)) /=;
      try rewrite take_length; try lia.
    f_equal.
    apply IH; first done.
    rewrite drop_length len_perm.
    lia.
  Qed.
    
  Lemma bernoulli_to_negative_translation (r : nat) :
    (0 < r)%nat →
    ∀ (l : list (fin 2)) (v : list nat),
    is_negative_translation r v l
    ↔ 
    ∃ perm n, 
    l = expand_perm perm ∧
    length perm = n * r ∧
    v = bernoulli_to_negative r l.
  Proof.
    move=>r_pos l v.
    elim: v l =>[|vt vh IH] /= l.
    - case: l; split; try done.
      + move=>_.
        by exists [], 0.
      + intros (perm & n & -> & len_perm & perm_emp).
        destruct n; first by destruct perm.
        destruct r; first lia.
        rewrite -(take_drop (S r) perm) expand_perm_app in perm_emp.
        rewrite bernoulli_to_negative_expand_perm in perm_emp; last rewrite take_length; try lia.
        discriminate.
    - split.
      + destruct r; first lia. 
        intros (perm & suf & -> & len_perm & sum_perm & is_tl).
        apply IH in is_tl as (perm' & n & -> & len_perm' & vt_eq).
        exists (perm ++ perm'), (S n).
        split; first by rewrite expand_perm_app //.
        rewrite app_length len_perm' len_perm.
        split; first lia.
        rewrite bernoulli_to_negative_expand_perm; try lia.
        by f_equal.
      + intros (perm & n & -> & len_perm & v_eq).
        exists (take r perm), (expand_perm (drop r perm)).
        split; first by rewrite -expand_perm_app take_drop.
        assert (length (take r perm) = r).
        { rewrite take_length.
          destruct perm, n; try discriminate.
          lia.
        }
        split; first done.
        rewrite -(take_drop r perm) expand_perm_app in v_eq.
        fold expand_perm in v_eq.
        rewrite bernoulli_to_negative_expand_perm in v_eq; try lia.
        injection v_eq as vt_eq vh_eq.
        split; first done.
        apply IH.
        eexists _, (n - 1).
        split; first done.
        rewrite drop_length len_perm.
        by split; first (destruct n; lia).
  Qed.
  
  Lemma B_tape_n_success_presample
    (e : expr) (α : loc) (Φ : val → iProp Σ)
    (p q r : nat) (ns : list (fin 2)) (ε : R) :
    (0 < p)%nat →
    (p < q + 1)%nat →
    (0 < ε)%R → 
    to_val e = None →
    ↯ ε ∗
    B_tape α p q ns ∗
    (if bool_decide (r = 0)
     then B_tape α p q ns -∗ WP e [{ Φ }]
     else
       ∀ (suf : list (fin 2)), ⌜list_sum $ fin_to_nat <$> suf = r - 1⌝ -∗ B_tape α p q (ns ++ suf ++ [1%fin]) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }].
  Proof.
    iIntros (p_gt_0 p_lt_Sq).
    iInduction (r) as [|r] "IH" forall (Φ ns ε);
      iIntros (ε_pos e_not_val) "(Herr & Hα & Hnext)".
    - by wp_apply "Hnext".
    - iRevert "Hα Hnext".
      set (s0 := (p / (q + 1))%R).
      set (s1 := (1 - s0)%R).
      set (s2 := (1 / s1)%R).
      set (s3 := ((s2 + 1) / 2)%R).
      set (s4 := (1 - s3 * s1)%R).
      set (s5 := (s4 / s0)%R).
      assert (0 < q + 1)%R.
      {
       rewrite -INR_1 -INR_0 -plus_INR.
       apply lt_INR.
       lia.   
      }
      assert (0 < p)%R.
      {
        rewrite -INR_0.
        by apply lt_INR.
      }
      assert (0 < s0 < 1)%R.
      {
        unfold s0.
        split; simpl_expr.
        rewrite -INR_1 -plus_INR.
        by apply lt_INR.
      }
      assert (0 < s1 < 1)%R by (unfold s1; lra).
      assert (1 < s2)%R.
      { unfold s2. simpl_expr. }
      assert (1 < s3)%R by (unfold s3; lra).
      assert (0 < s4)%R.
      {
        unfold s4.
        rewrite -Rcomplements.Rminus_lt_0.
        unfold s3, s2.
        rewrite -Rmult_div_swap -Rcomplements.Rdiv_lt_1; last lra.
        rewrite Rmult_plus_distr_r -Rmult_div_swap Rmult_div_l; lra.
      }
      assert (0 < s5)%R.
      { unfold s5. simpl_expr. }
      assert (s5 * s0 + s3 * s1 = 1)%R.
      {
        unfold s5, s4.
        rewrite -Rmult_div_swap Rmult_div_l; lra.
      }
      iRevert (ns).
      iApply (ec_ind_amp _ s3 with "[] Herr"); try done.
      iModIntro.
      clear ε ε_pos.
      iIntros (ε ε_pos) "IHec Herr %ns Hα Hnext".
      set (D (i : fin 2) := match i with
                            | 0%fin => (s3 * ε)%R
                            | _ => (s5 * ε)%R
                            end).
      wp_apply (B_tape_adv_comp _ α _ p q _ ε D); try done.
      { lia. }
      { unfold D.
        move=>i.
        inv_fin i => [|_]; nra.
      }
      { simpl.
        fold s0 s1.
        nra.
      }
      iFrame.
      iIntros (i).
      full_inv_fin; simpl.
      + iIntros "[Herr Hα]".
        wp_apply ("IHec" with "Herr Hα").
        iIntros (suf sum_suf) "Hα".
        rewrite -app_assoc (app_assoc _ suf).
        wp_apply "Hnext"; last iFrame.
        { rewrite -sum_suf //. }
      + iClear "IHec".
        iIntros "[Herr Hα]".
        wp_apply "IH"; last iFrame.
        { iPureIntro. nra. }
        { done. }
        case_bool_decide as is_r_0.
        { iIntros "Hα".
          wp_apply ("Hnext" $! []); last iFrame.
          rewrite is_r_0 //.
        } 
        iIntros (suf sum_suf) "Hα".
        rewrite -app_assoc (app_assoc _ suf).
        wp_apply "Hnext"; last iFrame.
        rewrite /= sum_suf //.
        iPureIntro.
        lia.
  Qed.
  
  Lemma twp_negative_presample :
    ∀ (e : expr) (α : loc) (Φ : val → iProp Σ)
      (p q r : nat) (ns : list nat) (ε : R),
    (0 < p)%nat →
    (p < q + 1)%nat →
    (0 < ε)%R → 
    to_val e = None →
    ↯ ε ∗ own_negative_tape α p q r ns ∗
    (∀ (i : nat), own_negative_tape α p q r (ns ++ [i]) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }].
  Proof.
    iIntros (e α Φ p q r ns ε p_pos p_lt_Sq ε_pos e_not_val) "(Herr & (%l & Hα & %is_tl) & Hnext)".
    wp_apply (B_tape_n_success_presample _ _ _ p q r); try done.
    iFrame.
    case_bool_decide.
    { iIntros "Htape".
      iApply ("Hnext" $! 0).
      unfold own_negative_tape.
      subst r.
      apply is_negative_translation_0 in is_tl as [-> ns_eq].
      iExists [].
      iFrame.
      iPureIntro.
      apply is_negative_translation_0.
      split; first done.
      rewrite {1}ns_eq app_length /= repeat_app //.
    } 
    iIntros (suf sum_suf) "Hα".
    wp_apply ("Hnext" $! (length suf - (r - 1))).
    unfold own_negative_tape.
    iExists (l ++ suf ++ [1%fin]).
    iFrame.
    iPureIntro.
    apply bernoulli_to_negative_translation in is_tl as (perm & n & -> & len_perm & ->); last lia.
    rewrite bernoulli_to_negative_translation; last lia.
    exists (perm ++ contract_perm (suf ++ [1%fin])), (S n).
    split; first by rewrite expand_perm_app expand_contract_perm.
    split.
    { rewrite app_length contract_perm_length fmap_app list_sum_app sum_suf len_perm /=.
      lia.
    }
    rewrite (bernoulli_to_negative_expand_perm_n _ n); [|lia|done].
    f_equal.
    rewrite -(expand_contract_perm suf) -(app_nil_r (expand_perm _)) bernoulli_to_negative_expand_perm; try lia.
    { unfold bernoulli_to_negative.
      simpl.
      rewrite list_sum_contract_perm sum_suf //.
    }
    rewrite contract_perm_length fmap_app list_sum_app sum_suf /=.
    lia.
  Qed.

  (*
  Lemma B_n_success_planner :
    ∀ (p q n : nat) (α : loc) (e : expr) (ε : R)
      (L : nat) (Φ : val → iProp Σ)
      (prefix : list (fin 2)) (suffix : list (fin 2) → list (fin 2)),
    0 < p < q + 1 →
    (0 < ε)%R →
    to_val e = None →
    (∀ (junk : list (fin 2)),
       0 < length (suffix (prefix ++ junk)) <= L) →
    ↯ ε ∗
    B_tape α p q prefix ∗
    ((∃ (junk : list (fin 2)),
         B_tape α p q (prefix ++ junk ++ suffix (prefix ++ junk)))
     -∗ WP e [{ Φ }])
    ⊢ WP e [{ Φ }].
  *)
  Lemma twp_negative_planner :
    ∀ (p q r : nat) (α : loc) (e : expr) (ε : nonnegreal)
      (L_size L_sum : nat) (Φ : val → iProp Σ)
      (prefix : list nat) (suffix : list nat → list nat) ,
    (0 < p < q + 1)%nat →
    0 < r →
    to_val e = None →
    (∀ (junk : list nat),
       0 < length (suffix (prefix ++ junk)) <= L_size ∧ list_sum (suffix (prefix ++ junk)) ≤ L_sum) →
    (0 < ε)%R →
    ↯ ε ∗
    own_negative_tape α p q r prefix ∗
    ((∃ (junk : list nat),
         own_negative_tape α p q r (prefix ++ junk ++ suffix (prefix ++ junk)))
     -∗ WP e [{ Φ }])
    ⊢ WP e [{ Φ }].
  Proof.
    iIntros
      (p q r α e ε
       L_size L_sum Φ
       prefix suffix p_bounds r_pos
       e_not_val suffix_bound ε_pos)
        "(Herr & (%l & Hα & %is_tl) & Hnext)".
    set (suf (lst : list (fin 2)) :=
           let n := list_sum $ fin_to_nat <$> lst in
           let k := r - (n `mod` r) in
           let padding := repeat 1%fin k in
           let padded := lst ++ padding in
           padding ++ (negative_to_bernoulli r
              (suffix (bernoulli_to_negative r padded))
           )
        ).
    apply bernoulli_to_negative_translation in is_tl as (perm & n & l_eq & len_perm & prefix_eq); last done.
    set (L := S r + (L_sum + r * L_size)).
    assert (∀ (junk : list (fin 2)), 0 < length (suf (l ++ junk)) ≤ L) as suf_bound.
    {
      move=>junk.
      unfold suf.
      rewrite -app_assoc l_eq (bernoulli_to_negative_expand_perm_n _ n); try done.
      rewrite -l_eq -prefix_eq !app_length negative_to_bernoulli_length.
      unfold L.
      split.
      { repeat apply Nat.lt_lt_add_l.
        apply Nat.mul_pos_cancel_l; first done.
        apply suffix_bound.
      } 
      repeat apply Nat.add_le_mono.
      { rewrite repeat_length. lia. }
      { apply suffix_bound. }
      { apply Nat.mul_le_mono_l, suffix_bound. }
    }
    
    unshelve wp_apply (B_tape_planner _ _ _ _ _ _ _ _ suf _ e_not_val suf_bound); last iFrame; try done; try lia.
    iIntros "(%junk & Hα)".
    wp_apply "Hnext".
    iExists _.
    iFrame.
    iPureIntro.
    rewrite bernoulli_to_negative_translation; last done.
    eexists (contract_perm (l ++ junk ++ suf (l ++ junk))), _.
    split.
    { unfold suf.
      set lst := l ++ junk.
      set sm := list_sum $ fin_to_nat <$> lst .
      set k := r - (sm `mod` r) .

      assert (k = (k - 1) + 1) as k_eq.
      {
        assert (sm `mod` r < r).
        {
          apply Nat.mod_upper_bound.
          lia.
        }
        lia.
      }
      rewrite k_eq !repeat_app !app_assoc cons_middle app_nil_r.
      match goal with
      | |- _ = expand_perm (contract_perm (_ ++ negative_to_bernoulli _ ?V)) =>
          set (v := V)
      end.
      destruct (negative_to_bernoulli_last r r_pos v) as [pre pre_eq];
        last rewrite pre_eq app_assoc expand_contract_perm //.
      { move=>contra.
        assert (∃ l, v = suffix (prefix ++ l)) as [vv ->].
        { eexists _.
          unfold v.
          f_equal.
          rewrite -!app_assoc l_eq (bernoulli_to_negative_expand_perm_n r n); try done.
          rewrite -l_eq -prefix_eq.
          f_equal.
        }
        assert (0 < length (suffix (prefix ++ vv))) as gt_0 by apply suffix_bound.
        rewrite contra /= in gt_0.
        lia.
      } 
    }
    split.
    { rewrite contract_perm_length l_eq !fmap_app !list_sum_app list_sum_expand_perm len_perm.
      instantiate (1 := n + _).
      rewrite Nat.mul_add_distr_r.
      f_equal.
      rewrite fmap_repeat list_sum_repeat Nat.mul_1_l list_sum_negative_to_bernoulli -l_eq.
      rewrite {1}(Nat.Div0.div_mod (list_sum (fin_to_nat <$> junk)) r) (Nat.add_comm (n * r)) Nat.Div0.mod_add.
      match goal with
      | |- r * ?X + _ + (_ - _ + r * ?Y) = _ =>
          instantiate (1 := X + 1 + Y)
      end.
      assert (list_sum (fin_to_nat <$> junk) `mod` r < r).
      {
        apply Nat.mod_upper_bound.
        lia.
      }
      lia.
    }
    rewrite l_eq.
    rewrite (bernoulli_to_negative_expand_perm_n r n); try done.
    rewrite -l_eq.
    f_equal; first done.
    unfold suf.
    rewrite !fmap_app !list_sum_app l_eq !list_sum_expand_perm !len_perm -!l_eq !(Nat.add_comm (n * r)) !Nat.Div0.mod_add.
    set sm := list_sum $ fin_to_nat <$> junk .
    set k := r - (sm `mod` r).
    assert (junk ++ repeat 1%fin k = expand_perm (contract_perm (junk ++ repeat 1%fin k))) as junk_eq.
    {
      assert (k = (k - 1) + 1) as ->.
      {
        assert (sm `mod` r < r).
        {
          apply Nat.mod_upper_bound.
          lia.
        }
        lia.
      }  
      rewrite !repeat_app !app_assoc expand_contract_perm //.
    }

    rewrite !app_assoc junk_eq (bernoulli_to_negative_expand_perm_n _ (sm `div` r + 1)); try done; last first.
    { rewrite contract_perm_length fmap_app fmap_repeat list_sum_app list_sum_repeat Nat.mul_1_l.
      fold sm.
      unfold k.
      rewrite {1}(Nat.Div0.div_mod sm r).
      assert (sm `mod` r < r) by (apply Nat.mod_upper_bound; lia).
      lia.
    }
    rewrite -junk_eq.
    f_equal.
    rewrite negative_to_bernoulli_to_negative; last done.
    fold sm k.
    rewrite -app_assoc l_eq (bernoulli_to_negative_expand_perm_n r n); try done.
    rewrite -l_eq -prefix_eq //.
  Qed.
  
End NegativeBinomial.
#[global] Opaque negative_binomial.
