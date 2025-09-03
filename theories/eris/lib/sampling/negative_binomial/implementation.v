From clutch.eris Require Export eris.
From clutch.eris.lib.sampling Require Import utils. 
From clutch.eris.lib.sampling.bernoulli Require Import interface.
From clutch.eris.lib.sampling.binomial Require Import interface.
From clutch.eris.lib.sampling.negative_binomial Require Import interface.

Section NegativeBinomial.
  Context `{!bernoulli_spec bernoulli balloc}.

  Section NegativeBinomialImpl.

    Definition negative_binomial : val :=
      λ: "α" "p" "q",
        rec: "negative_binomial" "r" :=
        if: "r" ≤ #0
        then #0
        else
          let: "b" := bernoulli "α" "p" "q" in
          if: "b" = #0
          then "negative_binomial" "r" + #1
          else "negative_binomial" ("r" - #1).

    Definition nalloc : val :=
      λ: "p" "q" "r", balloc "p" "q".
    
    Lemma SeriesC_first_nat :
      ∀ (D : nat → R),
      ex_seriesC D → SeriesC D = (D 0%nat + SeriesC (D ∘ S))%R.
    Proof.
      move=>D ex_D.
      rewrite !SeriesC_nat Series.Series_incr_1 //.
      by apply ex_seriesC_nat.
    Qed.
    
  End NegativeBinomialImpl.

  Section NegativeBinomialInst.

    Context `{!erisGS Σ}.

    Set Default Proof Using "Type*".

    Lemma ec_negative_binom_split :
      ∀ (p q r : nat) (D : nat → R) (L : R),
      (0 < p ≤ q + 1)%nat →
      (∀ k, 0 <= D k <= L)%R →
      let ε := SeriesC (λ k, negative_binom_prob p q (r + 1) k * D k)%R in
      let ε0 := SeriesC (λ k, negative_binom_prob p q (r + 1) k * D (k + 1)%nat)%R in
      let ε1 := SeriesC (λ k, negative_binom_prob p q r k * D k)%R in
      (ε = (1 - (p / (q + 1))) * ε0 + (p / (q + 1))* ε1)%R.
    Proof.
      move=>p q r D L p_bounds D_bounds ε ε0 ε1.
      unfold ε, ε0, ε1.
      set (s := (p / (q + 1))%R).
      set (t := (1 - s)%R).
      move=>[:ex_series_neg_D].
      rewrite SeriesC_first_nat; last first.
      { generalize (r + 1).
        set (id := λ (n : nat), n).
        replace D with (D ∘ id); last done.
        generalize id.
        abstract: ex_series_neg_D.
        move=>f r'.
        apply (ex_seriesC_le _ (λ k, negative_binom_prob p q r' k * L)%R).
        { move=>k.
          split.
          - apply Rmult_le_pos.
            + apply negative_binom_pos.
              lia.
            + apply D_bounds.
          - apply Rmult_le_compat_l.
            + apply negative_binom_pos.
              lia.
            + apply D_bounds.
        }
        apply ex_seriesC_scal_r.
        exists 1%R.
        by apply is_seriesC_negative_binomial.
      }
      
      setoid_rewrite SeriesC_first_nat at 3; last apply (ex_series_neg_D (λ n, n)).
      unfold negative_binom_prob at 1.
      rewrite Nat.add_0_l Nat.add_sub.
      fold s t.
      rewrite interface.choose_n_0 -(interface.choose_n_0 (r - 1)) pow_add -Rmult_assoc (Rmult_assoc _ (s^1)) (Rmult_comm (s^1)) -Rmult_assoc -{1}(Nat.add_0_l r).
      unfold t ,s.
      fold (negative_binom_prob p q r 0).
      fold s t.
      rewrite pow_1 (Rmult_comm _ s) (Rmult_assoc s).
      erewrite SeriesC_ext; last first.
      {
        move=>k /=.
        rewrite -{1}(Nat.add_1_r k) negative_binom_prob_split.
        fold s t.
        rewrite Rmult_plus_distr_r Rplus_comm -{2}(Nat.add_1_r k) {1}(Nat.add_1_r k) //.
      }
      rewrite SeriesC_plus; last first.
      { eapply ex_seriesC_ext; first (move=>k; rewrite Rmult_assoc //).
        apply ex_seriesC_scal_l, ex_series_neg_D.
      }
      { eapply ex_seriesC_ext; first (move=>k; rewrite Rmult_assoc //).
        apply ex_seriesC_scal_l.
        rewrite -ex_seriesC_nat.
        rewrite -(@Series.ex_series_incr_1 _ Hierarchy.R_NormedModule (λ k, negative_binom_prob p q r k * D k)%R).
        rewrite ex_seriesC_nat.
        apply ex_series_neg_D.
      }
      setoid_rewrite SeriesC_ext at 1 2; [..| (move=>k; rewrite Rmult_assoc //) | (move=>k; rewrite Rmult_assoc //)].
      rewrite !SeriesC_scal_l Rmult_plus_distr_l -Rplus_assoc Rplus_comm //.
    Qed.

    Lemma twp_negative_binomial_split_p_eq_q_plus_1 :
      ∀ (p q r : nat),
      (0 < p)%nat →
      (p = q + 1)%nat →
      ⊢ WP negative_binomial #() #p #q #r [{ v, ⌜v = #0⌝ }].
    Proof.
      move=>p q r p_pos ->.
      rewrite /negative_binomial.
      do 6 wp_pure.
      iInduction (r) as [|r] "IH"; first by wp_pures.
      wp_pures.
      iMod ec_zero as "ε0".
      wp_apply (bernoulli_success_spec_simple with "[ε0]") as "_".
      { 
        replace (1 - (q + 1)%nat / S q)%R with 0%R; last first.
        { rewrite S_INR plus_INR INR_1 Rdiv_diag; first lra.
          pose proof (pos_INR q).
          lra.
        }
        iFrame.
      }
      do 5 wp_pure.
      replace (S r - 1)%Z with (r : Z) by lia.
      wp_apply "IH".
    Qed.
    
    Lemma twp_negative_binomial_split :
      ∀ (p q : nat),
      (0 < p)%nat →
      (p ≤ q + 1)%nat →
      ∀ (r : nat) (D : nat → R) (L : R) (ε : R),
      (∀ (n : nat), 0 <= D n <= L)%R →
      SeriesC (λ k, (negative_binom_prob p q r k * D k)%R) = ε →
      ↯ ε -∗ WP negative_binomial #() #p #q #r [{ v, ∃ (k : nat), ⌜v = #k⌝ ∗ ↯ (D k) }].
    Proof.
      iIntros (p q Hp Hpq r D L ε HD HSum) "Herr".
      iApply twp_rand_err_pos; auto.
      iIntros (ε_term Hε_term) "Hterm".
      destruct (Nat.eq_dec p (q + 1)) as [-> | p_ne_q_add_1].
      { rewrite (SeriesC_ext _ (λ k, if bool_decide (k = 0) then D 0 else 0%R)) in HSum; last first.
        { move=>n.
          unfold negative_binom_prob.
          rewrite plus_INR Rdiv_diag /=; last first.
          { pose proof (pos_INR q).
            lra.
          }
          rewrite pow1 Rminus_diag.
          case_bool_decide.
          { subst.
            rewrite interface.choose_n_0 pow_O /=.
            lra.
          }
          {
            rewrite pow_i; last lia.
            lra.
          }
        }
        rewrite SeriesC_singleton in HSum.
        subst.
        iApply tgl_wp_wand_r.
        iSplitR;
          first by wp_apply twp_negative_binomial_split_p_eq_q_plus_1.
        iIntros (?) "->".
        iExists 0.
        by iFrame.
      }
      assert (p < q + 1)%nat by lia.
      rewrite /negative_binomial.
      do 6 wp_pure.
      iRevert (D L ε ε_term Hε_term HD HSum) "Herr Hterm".
      iInduction (r) as [|r] "IHr".
      - iIntros (D L ε ε_term Hε_term HD HDε) "Herr Hterm".
        rewrite /negative_binom_prob /choose in HDε.
        erewrite (SeriesC_ext _ (λ k, if bool_decide (k = 0) then D 0 else 0)) in HDε; last first.
        { intros k.
          unfold interface.choose.
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
      - iIntros (D L ε ε_term Hε_term HD HDε) "Herr Hterm".
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
        rewrite (ec_negative_binom_split _ _ _ _ L) // in HDε.
        fold s1 s0 in HDε.
        match type of HDε with
        | (s0 * ?A + s1 * ?B)%R = _ => set (ε0 := A);
                                       set (ε1 := B)
        end.

        fold ε0 ε1 in HDε.

        assert (0 <= ε0)%R.
        { apply SeriesC_ge_0'.
          intros n.
          apply Rmult_le_pos; last apply HD.
          apply negative_binom_pos.
          lia.
        }
        assert (0 <= ε1)%R.
        { apply SeriesC_ge_0'.
          intros n.
          apply Rmult_le_pos; last apply HD.
          apply negative_binom_pos.
          lia.
        }

        assert (0 <= ε' * sc0)%R by (apply Rmult_le_pos; lra).
        assert (0 <= ε' * sc1)%R by (apply Rmult_le_pos; lra).
        
        wp_pures.
        iPoseProof (ec_combine with "[Hterm Herr]") as "Hec"; first iFrame.
        
        wp_apply (twp_bernoulli_scale _ _ _ (ε0 + ε' * sc0) (ε1 + ε' * sc1) with "Hec"); first lia; try lra.
        { rewrite -HDε -Nat.add_1_r plus_INR INR_1.
          fold s1 s0.
          nra.
        }
        iIntros (k) "[[-> Herr] | [-> Herr]]".
        {
          do 4 wp_pure.
          iPoseProof (ec_split with "Herr") as "[Herr Hterm]"; try assumption.
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
            apply Rmult_le_pos; last apply HD.
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
      ∀ (r : nat) (D : nat → R) (L : R) (ε : R),
      (∀ (n : nat), 0 <= D n <= L)%R →
      SeriesC (λ k, (negative_binom_prob p q r k * D k)%R) = ε →
      ↯ ε -∗
      WP negative_binomial #() #p #q #r {{ v, ∃ (k : nat), ⌜v = #k⌝ ∗ ↯ (D k) }}.
    Proof.
      iIntros (p q Hp Hpq r D L ε HD HSum) "Herr".
      rewrite /negative_binomial.
      do 6 wp_pure.
      iRevert (r D L ε HD HSum) "Herr".
      iLöb as "IH".
      iIntros (r D L ε HD HSum) "Herr".
      wp_pures.
      case_bool_decide.
      - assert (r = 0) as -> by lia.
        rewrite /negative_binom_prob /choose in HSum.
        erewrite (SeriesC_ext _ (λ k, if bool_decide (k = 0) then D 0 else 0)) in HSum; last first.
        { intros k.
          unfold interface.choose.
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
        rewrite (ec_negative_binom_split _ _ _ _ L) // in HSum.
        fold s1 s0 in HSum.
        match type of HSum with
        | (s0 * ?A + s1 * ?B)%R = _ => set (ε0 := A);
                                       set (ε1 := B)
        end.
        fold ε0 ε1 in HSum.
        assert (0 <= ε0)%R.
        { apply SeriesC_ge_0'.
          intros n.
          apply Rmult_le_pos; last apply HD.
          apply negative_binom_pos.
          lia.
        }
        assert (0 <= ε1)%R.
        { apply SeriesC_ge_0'.
          intros n.
          apply Rmult_le_pos; last apply HD.
          apply negative_binom_pos.
          lia.
        }
        
        wp_pures.
        wp_bind (bernoulli _ _ _).
        wp_apply tgl_wp_pgl_wp'.
        wp_apply (twp_bernoulli_scale p q ε ε0 ε1 ltac:(lia) with "Herr"); try assumption.
        { rewrite -Nat.add_1_r plus_INR INR_1. fold s1 s0. lra. }
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
    
    Lemma expand_perm_repeat_0 :
      ∀ (r : nat), expand_perm (repeat 0 r) = repeat 1%fin r.
    Proof.
      elim=>[|/= ? ->] //.
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
      (∃ (l : list (fin 2)), own_bernoulli_tape α N M l ∗ ⌜is_negative_translation r v l⌝)%I.

    Lemma twp_negative_alloc (p q r : nat) :
      [[{ True }]]
        nalloc #p #q #r
        [[{ (α : loc), RET #lbl:α; own_negative_tape α p q r [] }]].
    Proof.
      iIntros (Φ) "_ HΦ".
      unfold nalloc.
      wp_pures.
      wp_apply (twp_bernoulli_alloc with "[$]") as (α) "Hα".
      iApply "HΦ".
      iExists [].
      by iFrame.
    Qed.
    
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
    
    Lemma is_negative_translation_snoc :
      ∀ (r : nat) (v : list (fin 2)) (l : list nat) (perm : list nat),
      length perm = r → 
      is_negative_translation r l v →
      is_negative_translation r (l ++ [list_sum perm])
        (v ++ expand_perm perm).
    Proof.
      move=>r v l.
      elim:l v =>[|hl tl IH] v perm len_perm /= is_tl.
      - rewrite is_tl /=.
        exists perm, [].
        rewrite app_nil_r len_perm //.
      - destruct is_tl as (pre & suf & -> & len_pre & sum_pre & is_tl).
        exists pre, (suf ++ expand_perm perm).
        rewrite app_assoc len_pre sum_pre.
        split; first reflexivity.
        split; first reflexivity.
        split; first reflexivity.
        by apply IH.
    Qed.
    
    Lemma twp_negative_tape :
      ∀ (p q r : nat) (α : loc) (n : nat) (ns : list nat) (Φ : val → iProp Σ),
      own_negative_tape α p q r (n::ns) -∗
      (own_negative_tape α p q r ns -∗ Φ #n) -∗
      WP negative_binomial #lbl:α #p #q #r [{ Φ }].
    Proof.
      iIntros (p q r α n ns Φ) "(%l & Hα & %is_tl) Hnext".
      unfold negative_binomial.
      do 6 wp_pure.
      simpl in is_tl.
      iRevert (α l n ns is_tl Φ) "Hα Hnext".
      remember r as r' eqn:r_is_r'.
      rewrite {2 3}r_is_r'.
      clear r_is_r'.
      iInduction r' as [| r'] "IH".
      - iIntros (α l n ns (perm & suf & -> & len_perm & sum_perm & is_tl) Φ) "Hα Hnext".
        destruct perm; last discriminate.
        rewrite -sum_perm /=.
        wp_pures.
        iModIntro.
        iApply "Hnext".
        by iFrame.
      - iIntros (α l n ns (perm & suf & -> & len_perm & sum_perm & is_tl) Φ) "Hα Hnext".
        destruct perm as [|h t]; first discriminate.
        simpl.
        iRevert (Φ n sum_perm) "Hα Hnext IH".
        iInduction (h) as [|h] "IHh"; simpl.
        + iIntros (Φ n sum_perm) "Hα Hnext IH".
          wp_pures.
          wp_apply (twp_bernoulli_tape with "Hα") as "Hα".
          do 5 wp_pure.
          replace (S r' - 1)%Z with (r' : Z); last lia.
          wp_apply ("IH" with "[] Hα Hnext").
          iPureIntro.
          exists t, suf.
          split; first done.
          simpl in len_perm, sum_perm.
          by split; first lia.
        + iIntros (Φ n sum_perm) "Hα Hnext IH".
          wp_pures.
          wp_apply (twp_bernoulli_tape with "Hα") as "Hα".
          do 4 wp_pure.
          simpl in len_perm, sum_perm.
          destruct n as [| n]; first discriminate.
          injection sum_perm as sum_perm.
          unshelve wp_apply ("IHh" $! _ _ n with "[] Hα [Hnext]"); try done.
          { iIntros "Htape".
            wp_pures.
            iModIntro.
            replace (n + 1)%Z with (S n : Z); last lia.
            by iApply "Hnext".
          }
    Qed.
    
    Lemma twp_bernoulli_presample_adv_comp_n_success :
      ∀ (p q r : nat) (α : loc) (l : list (fin 2)) (e : expr)
        (D : nat → R) (L : R) (ε : R) (Φ : val → iProp Σ),
      0 < p →
      p ≤ (q + 1) →
      to_val e = None →
      (∀ (n : nat), 0 <= D n <= L)%R →
      SeriesC (λ k, (negative_binom_prob p q r k * D k)%R) = ε →
      ↯ ε ∗
      own_bernoulli_tape α p q l ∗
      (∀ (perm : list nat),
         ⌜length perm = r⌝ -∗
         ↯ (D (list_sum perm)%nat) -∗
         own_bernoulli_tape α p q (l ++ expand_perm perm) -∗ WP e [{ Φ }]) ⊢
      WP e [{ Φ }].
    Proof.
      iIntros (p q r α l e D L ε Φ Hp Hpq e_not_val HD HSum) "(Herr & Hα & Hnext)".
      iApply twp_rand_err_pos; auto.
      iIntros (ε_term Hε_term) "Hterm".
      destruct (decide (p = q + 1)) as [-> | p_ne_Sq].
      {
        rewrite (SeriesC_ext _ (λ k, if bool_decide (k = 0)%nat then D 0 else 0%R)) in HSum; last first.
        {
          move=>k.
          rewrite /negative_binom_prob plus_INR INR_1 Rdiv_diag; last (pose proof (pos_INR q); lra).
          case_bool_decide as is_k_0.
          - rewrite is_k_0 choose_n_0 pow1 pow_O /=.
            lra.
          - rewrite Rminus_diag pow_i; [lra | lia].
        }
        rewrite SeriesC_singleton in HSum.
        subst.
        wp_apply (twp_bernoulli_n_success_presample_1 _ _ _ _ _ r with "[$Hα Hnext Herr]") as "Hα"; try done.
        wp_apply ("Hnext" $! (repeat 0 r) with "[] [Herr] [Hα]").
        { rewrite repeat_length //. }
        { rewrite list_sum_repeat Nat.mul_0_l //. }
        rewrite expand_perm_repeat_0 //.
      }
      iRevert (D L ε ε_term Hε_term HD HSum l Φ) "Herr Hterm Hα Hnext".
      iInduction (r) as [|r] "IHr".
      - iIntros (D L ε ε_term Hε_term HD HSum l Φ) "Herr Hterm Hα Hnext".
        rewrite /negative_binom_prob /choose in HSum.
        erewrite (SeriesC_ext _ (λ k, if bool_decide (k = 0) then D 0 else 0)) in HSum; last first.
        { intros k.
          unfold interface.choose. 
          do 2 case_bool_decide; try lia; subst; simpl; last lra.
          rewrite Rcomplements.C_n_n.
          lra.
        }
        rewrite SeriesC_singleton in HSum.
        rewrite -HSum.
        wp_apply ("Hnext" $! [] with "[] Herr"); first done.
        rewrite app_nil_r //.
      - iIntros (D L ε ε_term Hε_term HD HSum l Φ) "Herr Hterm Hα Hnext".
        iRevert (D L ε HD HSum l) "Herr Hα Hnext".
        set (s1 := (p / (q + 1))%R).
        set (s0 := ((1 - s1)%R)).
        set (sc0 := ((/ s0 + 1) / 2)%R).
        set (sc1 := ((1 - sc0 * s0) / s1)%R).
        
        assert (0 < p)%R.
        {
          rewrite -INR_0.
          by apply lt_INR.
        }
        assert (p < q + 1)%nat by lia.
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
        iIntros (D L ε HD HDε l) "Herr Hα Hnext".
        erewrite SeriesC_ext in HDε; last first.
        {
          intros.
          replace (S r) with (r + 1)%nat; first done.
          lia.
        }
        rewrite (ec_negative_binom_split _ _ _ _ L) in HDε; try done.
        fold s1 s0 in HDε.
        match type of HDε with
        | (s0 * ?A + s1 * ?B)%R = _ => set (ε0 := A);
                                       set (ε1 := B)
        end.
        fold ε0 ε1 in HDε.
        assert (0 <= ε0)%R.
        { apply SeriesC_ge_0'.
          intros n.
          apply Rmult_le_pos; last apply HD.
          apply negative_binom_pos.
          lia.
        }
        assert (0 <= ε1)%R.
        { apply SeriesC_ge_0'.
          intros n.
          apply Rmult_le_pos; last apply HD.
          apply negative_binom_pos.
          lia.
        }
        
        iPoseProof (ec_combine with "[Hterm Herr]") as "Hec"; first iFrame.
        set (D' (k : fin 2) := match k with
                               | 0%fin => (ε0 + ε' * sc0)%R
                               | _ => (ε1 + ε' * sc1)%R
                               end).
        
        wp_apply (twp_presample_bernoulli_adv_comp _ α _ p q _ _ D' with "[$Hec Hnext $Hα IH]"); first lia; try done.
        { move=>i.
          full_inv_fin; simpl; nra.
        } 
        { rewrite -HDε /=.
          fold s1 s0.
          nra.
        }
        {
          iIntros (k) "[Herr Hα]".
          full_inv_fin.
          { 
            iPoseProof (ec_split with "Herr") as "[Herr Hterm]"; try done.
            
            { nra. }
            wp_apply ("IH" with "[Hterm] [] [] Herr Hα [Hnext]").
            { rewrite Rmult_comm //. }
            { instantiate (2 := λ k, D (k + 1)). iPureIntro. intros. apply HD. }
            { iPureIntro.
              apply SeriesC_ext.
              intros k.
              repeat f_equal.
              lia.
            }
            {
              iIntros (perm len_perm) "Herr Hα".
              rewrite -app_assoc.
              destruct perm as [|n perm]; first discriminate.
              set (perm' := (S n :: perm)).
              wp_apply ("Hnext" $! perm' with "[] [Herr]"); try done.
              rewrite Nat.add_1_r //.
            }
          } 
          { iPoseProof (ec_split with "Herr") as "[Herr Hterm]"; try done.
            { nra. }
            iApply ("IHr" with "[] [] [] Herr Hterm Hα [Hnext]").
            { iPureIntro. nra. }
            { by iPureIntro. }
            { by iPureIntro. }
            iIntros (perm len_perm) "Herr Hα".
            rewrite -app_assoc.
            wp_apply ("Hnext" $! (0::perm) with "[] Herr Hα"); first rewrite /= len_perm //.
          }
        } 
    Qed.
    
    Lemma twp_negative_presample_adv_comp :
      ∀ (p q r : nat) (α : loc) (l : list nat) (e : expr)
        (D : nat → R) (L : R) (ε : R) (Φ : val → iProp Σ),
      0 < p →
      p ≤ (q + 1) →
      to_val e = None →
      (∀ (n : nat), 0 <= D n <= L)%R →
      SeriesC (λ k, (negative_binom_prob p q r k * D k)%R) = ε →
      ↯ ε ∗
      own_negative_tape α p q r l ∗
      (∀ (n : nat),
         ↯ (D n) -∗
         own_negative_tape α p q r (l ++ [n]) -∗ WP e [{ Φ }]) ⊢
      WP e [{ Φ }].
    Proof.
      iIntros (p q r α l e D L ε Φ p_pos p_lt_Sq e_not_val D_pos D_sum) "(Herr & (%v & Hα & %is_tl) & Hnext)".
      unshelve wp_apply (twp_bernoulli_presample_adv_comp_n_success p q r _ _ _ D L ε); last iFrame; try done.
      iIntros (perm len_perm) "Herr Hα".
      wp_apply ("Hnext" with "Herr").
      iFrame.
      iPureIntro.
      by apply is_negative_translation_snoc.
    Qed.

  End NegativeBinomialInst.

  #[global] Instance NegativeOfBernoulli : negative_binomial_spec negative_binomial nalloc :=
    NegativeSpec _ _
      (@twp_negative_binomial_split)
      (@own_negative_tape)
      (@twp_negative_alloc)
      (@twp_negative_tape)
      (@twp_negative_presample_adv_comp).

End NegativeBinomial.

#[global] Opaque negative_binomial nalloc.
