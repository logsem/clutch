From clutch.eris Require Export eris.

From clutch.eris.lib.sampling Require Import utils.
From clutch.eris.lib.sampling.bernoulli Require Import interface.
From clutch.eris.lib.sampling.binomial Require Import interface.

Section binomial.

  Set Default Proof Using "Type*".
  
  Context `{!erisGS Σ}.
  Context `{!bernoulli_spec bernoulli balloc}.

  Definition binom_tape : val :=
    λ: "α" "m" "n",
      rec: "binom" "k" :=
        if: "k" ≤ #0
        then #0
        else "binom" ("k" - #1) + bernoulli "α" "m" "n".

  Definition binalloc : val :=
    λ: "m" "n" "k", balloc "m" "n".
  
  Definition binom : expr := binom_tape #().
 
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
    apply SeriesC_ext =>>.
    rewrite -fin_S_inj_to_nat //.
  Qed.
  
  Lemma twp_binom_adv_comp (p q : nat) (n : nat) (D : fin (S n) → R) (ε : R) :
    (p ≤ (q + 1))%nat →
    (∀ (k : fin (S n)), 0 <= D k)%R → 
    SeriesC (λ k : fin (S n), (binom_prob p q n k * D k)%R) = ε →
    [[{ ↯ ε }]] 
      binom #p #q #n 
    [[{ (k : fin (S n)), RET #k ; ↯ (D k) }]].
  Proof.
    iIntros (Hpq HD Hpos Φ) "Herr HΦ".
    rewrite /binom /binom_tape.
    do 6 wp_pure.
    iRevert (D ε HD Hpos Φ) "Herr HΦ".
    iInduction (n) as [|n] "IH";
      iIntros (D ε Hpos HD Φ) "Herr HΦ";
      wp_pures.
    - iApply ("HΦ"$! 0%fin with "[Herr]").
      iApply (ec_eq with "Herr").
      rewrite -HD SeriesC_finite_foldr /= binom_prob_eq Rmult_1_l Rplus_0_r //.
    - erewrite SeriesC_ext in HD; last first.
      { move=>>. 
        replace (S n) with (n + 1) at 1 by lia.
        reflexivity. } 
      rewrite ec_binom_split in HD.
      match type of HD with
      | ( _ * ?A +  _ * ?B)%R = _ =>
          set (ε0 := A);
          set (ε1 := B)
      end.
      fold ε0 ε1 in HD.
      wp_apply (twp_bernoulli_scale _ _ _ ε0 ε1%R with "Herr"); first lia.
      { apply SeriesC_ge_0'.
        move=>k.
        apply Rmult_le_pos; last done.
        by apply binom_prob_pos.
      }
      { apply SeriesC_ge_0'.
        move=>k.
        apply Rmult_le_pos; last done.
        by apply binom_prob_pos.
      }
      {
        rewrite -HD -Nat.add_1_r plus_INR INR_1.
        lra.
      }
      iIntros (?) "[[-> Herr] | [-> Herr]]".
      + wp_pure.
        replace (S n - 1)%Z with (n : Z) by lia.
        wp_apply ("IH" $! (D ∘ fin_S_inj) with "[] [] Herr [HΦ]") as (k) "Herr"; [by simpl | done |].
        wp_pures.
        rewrite fin_S_inj_to_nat Z.add_0_r.
        iApply ("HΦ" with "Herr").
      + wp_pure.
        replace (S n - 1)%Z with (n : Z); last lia.
        wp_apply ("IH" $! (D ∘ FS) with "[] [] Herr [HΦ]") as (k) "Herr"; [by simpl | done |].
        wp_pures.
        rewrite fin_S_inj_to_nat Z.add_1_r -Nat2Z.inj_succ -fin_S_inj_to_nat.
        iApply ("HΦ" with "Herr").
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

  Lemma is_binomial_translation_0 (v : list (fin 1)) (l : list (fin 2)) :
    is_binomial_translation 0 v l ↔ l = [].
  Proof.
    elim: v l =>[|h t IH] /=; first done.
    split.
    - intros ([|??] & suf & _ & len_pre & -> & is_tl_suf); last (simpl in len_pre; lia).
      simpl.
      apply IH, is_tl_suf.
    - move=> ->.
      exists [], [].
      rewrite IH.
      by full_inv_fin.
  Qed.
   
  Definition own_binomial_tape (α : loc) (m n k : nat) (v : list (fin (S k))) : iProp Σ :=
    ∃ l, own_bernoulli_tape α m n l ∗ ⌜is_binomial_translation k v l⌝.

  Lemma twp_binom_alloc (m n k : nat) :
    [[{ True }]]
      binalloc #m #n #k
      [[{ (α : loc), RET #lbl:α ; own_binomial_tape α m n k [] }]].
  Proof.
    iIntros (Φ) "_ HΦ".
    unfold binalloc.
    wp_pures.
    wp_apply (twp_bernoulli_alloc with "[$]") as (α) "Hα".
    iApply "HΦ".
    iExists [].
    by iFrame.
  Qed.
  
  Lemma twp_bernoulli_multiple_presample (e : expr) (α : loc) (Φ : val → iProp Σ)
      (N M k : nat) (ns : list (fin 2)) : 
    to_val e = None → 
    own_bernoulli_tape α N M ns ∗
    (∀ (l : list (fin 2)), ⌜length l = k⌝ -∗ own_bernoulli_tape α N M (ns ++ l) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }]
  .
  Proof.
    iRevert (Φ ns).
    iInduction (k) as [|k] "IH";
       iIntros (Φ ns e_not_val) "[Htape Hlists]".
    - wp_apply ("Hlists" $! []); first done.
      rewrite app_nil_r //.
    - wp_apply (twp_presample_bernoulli with "[$Htape Hlists IH]") as (i) "Htape"; first done.
      wp_apply "IH"; first done.
      iFrame.
      iIntros (l length_l_k) "Htape".
      wp_apply ("Hlists" $! i::l with "[] [Htape]"); first rewrite /= length_l_k //.
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
    wp_apply (twp_bernoulli_multiple_presample _ α _ N M k); first done.
    iFrame.
    iIntros (l' length_l'_k) "Hα".
    set (i := fin_sum_list 2 k l').
    wp_apply ("Hwp" $! i).
    iExists (l ++ l').
    iFrame.
    iPureIntro.
    generalize dependent l.
    induction ns as [|n ns IH]; move=>/= l is_tl.
    { subst; simpl.
      exists l', [].
      rewrite app_nil_r //.
    } 
    destruct is_tl as (pre & suf & sum_pre & len_pre & -> & is_tl).
    simpl.
    exists pre, (suf ++ l').
    rewrite -app_assoc.
    repeat split; try done.
    by apply IH.
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
        wp_apply (twp_bernoulli_tape N M α _ _ _ with "Htape") as "Htape".
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
        wp_apply (twp_bernoulli_tape N M α _ _ _ with "Htape") as "Htape".
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
          etrans; [by apply fin_sum_list_le | lia].
        }
        rewrite -Nat2Z.inj_add Nat.add_1_r.
        iApply ("HΦ" with "Htape").
  Qed.
  
  Lemma twp_bernoulli_multiple_presample_adv_comp :
    ∀ (e : expr) (α : loc) (Φ : val → iProp Σ)
      (p q n : nat) (ns : list (fin 2)) (ε : R)
      (D : fin (S n) → R),
    (∀ (i : fin (S n)), 0 <= D i)%R →
    SeriesC (λ k : fin (S n), (binom_prob p q n k * D k)%R) = ε →
    (p ≤ q + 1)%nat →
    to_val e = None →
    own_bernoulli_tape α p q ns ∗ ↯ ε ∗
    (∀ (ts : list (fin 2)), ⌜length ts = n⌝ →  ↯ (D (fin_sum_list _ _ ts)) ∗ own_bernoulli_tape α p q (ns ++ ts) -∗ WP e [{ Φ }])
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
      wp_apply (twp_presample_bernoulli_adv_comp _ _ _ p q _ ε D' with "[$Hα $Herr Hnext]") as (i) "[Herr Hα]"; try done.
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
      full_inv_fin.
      + wp_apply ("IH" $! _ _ s0 (D ∘ fin_S_inj)); try done.
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
      + wp_apply ("IH" $! _ _ s1 (D ∘ FS)); try done.
        { iPureIntro.
          move=>i.
          apply D_pos.
        }
        iFrame.
        iIntros (ts len_ts) "[Herr Hα]".
        wp_apply ("Hnext" $! 1%fin::ts); first rewrite /= len_ts //.
        rewrite -app_assoc /= fin_inj_sum; last lia.
        rewrite fin_succ_inj.
        iFrame.
  Qed.
        
  Lemma twp_binomial_tape_adv_comp 
      (e : expr) (α : loc) (Φ : val → iProp Σ)
      (p q n : nat) (ns : list (fin (S n))) (ε : R)
      (D : fin (S n) → R) :
    (∀ (i : fin (S n)), 0 <= D i)%R →
    SeriesC (λ k : fin (S n), (binom_prob p q n k * D k)%R) = ε →
    (p ≤ q + 1)%nat →
    to_val e = None →
    own_binomial_tape α p q n ns ∗ ↯ ε ∗
    (∀ (i : fin (S n)), ↯ (D i) ∗ own_binomial_tape α p q n (ns ++ [i]) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }]
  .
  Proof.
    iIntros (D_pos D_sum is_prob e_not_val) "((%l & Htape & %is_tl) & Herr & Hnext)".
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
    wp_apply (twp_bernoulli_multiple_presample_adv_comp _ _ _ _ _ (S n) _ _ D D_pos D_sum is_prob e_not_val).
    iFrame.
    iIntros (ts len_ts) "[Herr Hα]".
    wp_apply "Hnext".
    iFrame.
    iPureIntro.
    rewrite bernoulli_to_binomial_translation in is_tl; last lia.
    destruct is_tl as (k & len_l & ns_eq_tl). 
    rewrite bernoulli_to_binomial_translation; last lia.
    exists (S k).
    split; first (rewrite app_length; lia).
    rewrite ns_eq_tl (bernoulli_to_binomial_app_n _ k) // -{2}(app_nil_r ts) bernoulli_to_binomial_app_1 //.
  Qed.

  #[global] Instance BinomialOfBernoulli : binomial_spec binom_tape binalloc :=
    BinomialSpec _ _ binom_tape binalloc
      twp_binom_adv_comp
      own_binomial_tape
      twp_binom_alloc
      twp_binomial_tape
      binomial_tape_presample
      twp_binomial_tape_adv_comp.
  
End binomial.
#[global] Opaque binomial.
