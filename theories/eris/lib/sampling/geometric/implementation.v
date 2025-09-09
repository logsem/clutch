From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils.
From clutch.eris.lib.sampling.bernoulli Require Import interface.
From clutch.eris.lib.sampling.geometric Require Import interface.

Section Tape.
  
  #[local] Open Scope fin.

  Fixpoint is_geometric_translation (b : list (fin 2)) (g : list nat) := 
    match g with
    | [] => b = []
    | n::g =>
        ∃ suf, 
        b = (repeat 0 n ++ [1]) ++ suf ∧
        is_geometric_translation suf g
    end.

  Lemma is_geometric_translation_nil : is_geometric_translation [] [].
  Proof. reflexivity. Qed.
    
  Lemma is_geometric_translation_snoc (b : list (fin 2)) (g : list nat) (n : nat) :
    is_geometric_translation b g → is_geometric_translation (b ++ repeat 0%fin n ++ [1%fin]) (g ++ [n]).
  Proof.
    elim:g b n =>[|hg tg IH] b n /= is_tl.
    - subst. eexists. split; last reflexivity. rewrite app_nil_r //.
    - destruct is_tl as (suf & -> & is_tl).
      eexists.
      rewrite -!app_assoc.
      split; first reflexivity.
      by apply IH.
  Qed.
  
End Tape.
#[local] Open Scope R.

Section Geometric.

  Set Default Proof Using "Type*".
  
  Context `{!bernoulli_spec bernoulli balloc}.

  Definition own_geometric_tape `{!erisGS Σ} (α : loc) (N M : nat) (t : list nat) : iProp Σ :=
    ∃ l, 
    own_bernoulli_tape α N M l ∗ 
    ⌜is_geometric_translation l t⌝.

  #[local] Ltac done ::= solve[
    lia |
    lra |
    nra |
    tactics.done |
    auto
  ].
  
  Definition geometric_tape : val :=
    rec: "geometric_tape" "α" "N" "M" :=
    if: bernoulli "α" "N" "M" = #1 then #0 else 
    #1 + "geometric_tape" "α" "N" "M"
  .
  Definition geometric : expr := geometric_tape #().

  Definition geometric_alloc : val := balloc.
  
  Lemma ec_geometric_split :
   ∀ (p q : nat) (D : nat → R) (L : R),
    (0 < p ≤ q + 1)%nat →
    (∀ k, 0 <= D k <= L)%R →
    let ε := SeriesC (λ k, geometric_prob p q k * D k)%R in
    let ε' := SeriesC (λ k, geometric_prob p q k * D (S k))%R in
    (ε = (p / (q + 1) * D 0%nat + (1 - (p / (q + 1))) * ε'))%R.
  Proof.
    move=>p q D L p_bounds D_bounds ε ε'.
    unfold ε, ε'.
    set (s := (p / (q + 1))%R).
    set (t := (1 - s)%R).
    move=>[:ex_series_geom_D].
    rewrite SeriesC_first_nat; last first.
    { abstract: ex_series_geom_D.
      apply (ex_seriesC_le _ (λ k, geometric_prob p q k * L)).
      { move=>k.
        split.
        { apply Rmult_le_pos; last apply D_bounds.
          apply geometric_prob_pos.
          lia.
        }
        { apply Rmult_le_compat_l; last apply D_bounds.
          apply geometric_prob_pos.
          lia.
        }
      }
      apply ex_seriesC_scal_r.
      eexists.
      apply is_seriesC_geometric_prob.
      lia.
    }
    unfold geometric_prob at 1.
    rewrite pow_O Rmult_1_r.
    fold s.
    f_equal.
    rewrite -SeriesC_scal_l.
    apply SeriesC_ext.
    move=>k /=.
    rewrite geometric_prob_S.
    fold s t.
    lra.
  Qed.

  Lemma twp_geometric_split `{!erisGS Σ} :
      ∀ (p q : nat),
      (0 < p)%nat →
      (p ≤ q + 1)%nat →
      ∀ (D : nat → R) (L : R) (ε : R),
      (∀ (n : nat), 0 <= D n <= L)%R →
      SeriesC (λ k, (geometric_prob p q k * D k)%R) = ε →
      ↯ ε -∗ WP geometric #p #q [{ v, ∃ (k : nat), ⌜v = #k⌝ ∗ ↯ (D k) }].
    Proof.
      iIntros (p q Hp Hpq D L ε HD HSum) "Herr".
      iApply twp_rand_err_pos; auto.
      iIntros (ε_term Hε_term) "Hterm".
      destruct (Nat.eq_dec p (q + 1)%nat) as [-> | p_ne_q_add_1].
      { rewrite (ec_geometric_split _ _ _ _ _ HD) in HSum; last done.
        pose proof (pos_INR q).
        rewrite plus_INR Rdiv_diag in HSum; last (simpl; lra).
        rewrite Rminus_diag Rmult_1_l Rmult_0_l Rplus_0_r in HSum.
        subst.
        unfold geometric, geometric_tape.
        wp_pures.
        iMod ec_zero as "Herr0".
        wp_apply (bernoulli_success_spec_simple with "[Herr0]") as "_".
        { iApply (ec_eq with "Herr0").
          rewrite S_INR plus_INR Rdiv_diag; last simpl; lra.
        }
        wp_pures.
        iModIntro.
        by iFrame.
      } 
      assert (p < q + 1)%nat as p_lt_Sq by lia.
      apply lt_INR in p_lt_Sq as p_lt_Sq'.
      apply lt_INR in Hp as Hp'.
      rewrite plus_INR /= in p_lt_Sq'.
      simpl in Hp'.
      rewrite /geometric /geometric_tape.
      
      iRevert (D ε HD HSum) "Herr".
      set (s := (p / (q + 1))%R).
      set (t := ((1 - s)%R)).

      assert (0 < s).
      { apply Rdiv_lt_0_compat; lra. }
      
      assert (0 < t).
      { rewrite Rlt_0_minus -Rcomplements.Rdiv_lt_1; lra. }
      
      assert (1 < / t).
      { unfold t, s.
        rewrite -{1}Rinv_1.
        apply Rinv_0_lt_contravar; first done.
        rewrite Rcomplements.Rlt_minus_l -{1}(Rplus_0_r 1).
        apply Rplus_le_lt_compat; first reflexivity.
        apply Rdiv_lt_0_compat; lra.
      }

      assert (1 < / s).
      { unfold s.
        rewrite -{1}Rinv_1.
        apply Rinv_0_lt_contravar.
        { apply Rdiv_lt_0_compat; lra. }
        { rewrite -Rcomplements.Rdiv_lt_1; lra. }
      }

      iApply (ec_ind_amp _ (/ t) with "[] Hterm"); try done.
      iModIntro.
      iIntros (ε' Hε') "IH Hterm".
      iIntros (D ε HD HDε) "Herr".

      set (ε0 := SeriesC (λ k : nat, geometric_prob p q k * D (S k))).
      
      assert (0 <= ε0).
      { unfold ε0.
        apply SeriesC_ge_0'.
        move=>k.
        apply Rmult_le_pos; last apply HD.
        apply geometric_prob_pos.
        lia.
      }
      
      wp_pures.
      iPoseProof (ec_combine with "[Hterm Herr]") as "Hec"; first iFrame.
      
      wp_apply (twp_bernoulli_scale _ _ _ (ε0 + ε' / t) (D 0%nat) with "Hec")
                 as (?) "[[-> Herr] | [-> Herr]]"; first lia.
      { by apply Rplus_le_le_0_compat; last nra. }
      { apply HD. }
      { rewrite -HDε SeriesC_first_nat; last first.
        { apply (ex_seriesC_le _ (λ k, geometric_prob p q k * L)).
          { move=>k.
            split.
            { apply Rmult_le_pos; last apply HD.
              apply geometric_prob_pos.
              lia.
            }
            { apply Rmult_le_compat_l; last apply HD.
              apply geometric_prob_pos.
              lia.
            }
          }
          apply ex_seriesC_scal_r.
          eexists.
          apply is_seriesC_geometric_prob.
          lia.
        }
        unfold geometric_prob at 1.
        rewrite pow_O.
        erewrite SeriesC_ext; last first.
        { move=>k /=.
          rewrite geometric_prob_S Rmult_assoc.
          fold s t.
          reflexivity.
        }
        rewrite SeriesC_scal_l S_INR /=.
        fold ε0 s t.
        rewrite (Rmult_plus_distr_r _ _ t) Rdiv_def Rmult_assoc Rinv_l; lra.
      }
      {
        do 2 wp_pure.
        iPoseProof (ec_split with "Herr") as "[Herr Hterm]"; first assumption.
        { apply Rmult_le_pos; lra. }
        rewrite (Rdiv_def ε' t) (Rmult_comm ε' (/ t)).
        iSpecialize ("IH" with "Hterm").
        iPoseProof ("IH" $! (D ∘ S) with "[] [] Herr") as "IHH"; try done.
        { iPureIntro. move=>k. apply HD. }
        wp_bind (((rec: _ _ := _) _ _)%V _)%E.
        iApply tgl_wp_wand_r.
        iSplitL "IHH"; first done.
        iIntros (v) "(%k & -> & Herr)".
        wp_pures.
        iModIntro.
        iExists (S k).
        iFrame.
        iPureIntro.
        f_equal.
        rewrite (Nat2Z.inj_add 1 k) //.
      } 
      { wp_pures.
        iModIntro.
        by iFrame.
      } 
    Qed.

    Lemma twp_geometric_alloc `{!erisGS Σ} (p q : nat) :
      [[{ True }]]
        geometric_alloc #p #q
      [[{ (α : loc), RET #lbl:α; own_geometric_tape α p q [] }]].
    Proof.
      iIntros (Φ) "_ HΦ".
      unfold geometric_alloc.
      wp_apply (twp_bernoulli_alloc with "[$]") as (α) "Hα".
      iApply ("HΦ" with "[$Hα]").
      by iPureIntro.
    Qed.
    
    Lemma twp_geometric_presample_adv_comp `{!erisGS Σ} :
      ∀ (p q : nat) (α : loc) (ns : list nat)
        (e : expr) 
        (D : nat → R) (L : R) (ε : R)
        (Φ : val → iProp Σ),
        (0 < p)%nat →
      (p ≤ q + 1)%nat →
      to_val e = None → 
      (∀ (n : nat), 0 <= D n <= L)%R →
      SeriesC (λ k, (geometric_prob p q k * D k)%R) = ε →
      own_geometric_tape α p q ns ∗
      ↯ ε ∗ 
      (∀ (i : nat), ↯ (D i) ∗ own_geometric_tape α p q (ns ++ [i]) -∗ WP e [{ Φ }])
      ⊢  WP e [{ Φ }].
    Proof.
      iIntros (p q α ns e D L ε Φ Hp Hpq He HD HSum)
        "((%l & Htape & %is_tl) & Herr & Hnext)".
      iApply twp_rand_err_pos; auto.
      iIntros (ε_term Hε_term) "Hterm".
      destruct (Nat.eq_dec p (q + 1)%nat) as [-> | p_ne_q_add_1].
      { rewrite (ec_geometric_split _ _ _ _ _ HD) in HSum; last done.
        pose proof (pos_INR q).
        rewrite plus_INR Rdiv_diag in HSum; last (simpl; lra).
        rewrite Rminus_diag Rmult_1_l Rmult_0_l Rplus_0_r in HSum.
        subst.
        unfold geometric, geometric_tape.
        wp_pures.
        set (D' (k : fin 2) := match k with
                               | Fin.F1 _ => 1%R
                               | FS _ _ => D 0%nat
                               end).
        wp_apply (twp_presample_bernoulli_adv_comp _ _ _ (q + 1)%nat q _ _ D' with "[$Herr $Htape Hnext]") as (k) "[Herr Htape]"; try done.
        { move=>k.
          inv_fin k=>[|?] /=; first lra.
          apply HD.
        }
        { rewrite plus_INR /= Rdiv_diag; lra. }
        inv_fin k=>[|k]/=.
        { iDestruct (ec_contradict with "Herr") as "[]". reflexivity. }
        inv_fin k=>[|k]/=; last inv_fin k.
        wp_apply "Hnext".
        iFrame.
        iPureIntro.
        by apply (is_geometric_translation_snoc _ _ 0).
      } 
      assert (p < q + 1)%nat as p_lt_Sq by lia.
      apply lt_INR in p_lt_Sq as p_lt_Sq'.
      apply lt_INR in Hp as Hp'.
      rewrite plus_INR /= in p_lt_Sq'.
      simpl in Hp'.
      rewrite /geometric /geometric_tape -(app_nil_r l).
      
      replace [] with (repeat (0%fin : fin 2) 0) by reflexivity.
      iAssert (∀ i : nat,
              ↯ (D i) ∗
              own_geometric_tape α p q (ns ++ [0 + i]%nat) -∗
              WP e [{ v, Φ v }])%I with "Hnext" as "Hnext".

      
      generalize 0%nat at 4 5 as n.
      
      iIntros (n).
      iRevert (n D ε HD HSum) "Htape Herr Hnext".
      set (s := (p / (q + 1))%R).
      set (t := ((1 - s)%R)).

      assert (0 < s).
      { apply Rdiv_lt_0_compat; lra. }
      
      assert (0 < t).
      { rewrite Rlt_0_minus -Rcomplements.Rdiv_lt_1; lra. }
      
      assert (1 < / t).
      { unfold t, s.
        rewrite -{1}Rinv_1.
        apply Rinv_0_lt_contravar; first done.
        rewrite Rcomplements.Rlt_minus_l -{1}(Rplus_0_r 1).
        apply Rplus_le_lt_compat; first reflexivity.
        apply Rdiv_lt_0_compat; lra.
      }

      assert (1 < / s).
      { unfold s.
        rewrite -{1}Rinv_1.
        apply Rinv_0_lt_contravar.
        { apply Rdiv_lt_0_compat; lra. }
        { rewrite -Rcomplements.Rdiv_lt_1; lra. }
      }

      iApply (ec_ind_amp _ (/ t) with "[] Hterm"); try done.
      iModIntro.
      iIntros (ε' Hε') "IH Hterm".
      iIntros (n D ε HD HDε) "Htape Herr Hnext".

      set (ε0 := SeriesC (λ k : nat, geometric_prob p q k * D (S k))).
      
      assert (0 <= ε0).
      { unfold ε0.
        apply SeriesC_ge_0'.
        move=>k.
        apply Rmult_le_pos; last apply HD.
        apply geometric_prob_pos.
        lia.
      }
      
      wp_pures.
      iPoseProof (ec_combine with "[$Hterm $Herr]") as "Hec".

      set (D' (k : fin 2) := match k with
                               | Fin.F1 _ => (ε0 + ε' / t)%R
                               | FS _ _ => D 0%nat
                               end).
      
      wp_apply (twp_presample_bernoulli_adv_comp _ _ _ _ _ _ _ D' with "[$Hec $Htape Hnext IH]") as (k) "[Herr Htape]"; try done.
      { move=>k.
        inv_fin k=>[|?] /=; last apply HD.
        by apply Rplus_le_le_0_compat; last nra.
      } 
      { rewrite -HDε SeriesC_first_nat; last first.
        { apply (ex_seriesC_le _ (λ k, geometric_prob p q k * L)).
          { move=>k.
            split.
            { apply Rmult_le_pos; last apply HD.
              apply geometric_prob_pos.
              lia.
            }
            { apply Rmult_le_compat_l; last apply HD.
              apply geometric_prob_pos.
              lia.
            }
          }
          apply ex_seriesC_scal_r.
          eexists.
          apply is_seriesC_geometric_prob.
          lia.
        }
        unfold geometric_prob at 1.
        rewrite pow_O.
        erewrite SeriesC_ext; last first.
        { move=>k /=.
          rewrite geometric_prob_S Rmult_assoc.
          fold s t.
          reflexivity.
        }
        rewrite SeriesC_scal_l /=.
        fold ε0 s t.
        rewrite (Rmult_plus_distr_r _ _ t) Rdiv_def Rmult_assoc Rinv_l; lra.
      }
      inv_fin k=>[|k] /=; last (inv_fin k=>[|k]; last inv_fin k).
      {
        iPoseProof (ec_split with "Herr") as "[Herr Hterm]"; first assumption.
        { apply Rmult_le_pos; lra. }
        rewrite (Rdiv_def ε' t) (Rmult_comm ε' (/ t)) -app_assoc -repeat_cons.
        iSpecialize ("IH" with "Hterm").
        wp_apply ("IH" $! (S n) (D ∘ S) with "[] [] Htape Herr") as (k) "[Herr Htape]"; try done.
        { iPureIntro. move=>k. apply HD. }
        wp_apply "Hnext".
        iFrame.
        rewrite Nat.add_succ_r //.
      } 
      { wp_apply "Hnext".
        iFrame.
        iPureIntro.
        rewrite Nat.add_0_r -app_assoc.
        by apply is_geometric_translation_snoc.
      } 
    Qed.

    Lemma twp_geometric_tape `{!erisGS Σ} :
      ∀ (p q : nat) (α : loc) (n : nat)
        (ns : list nat) (Φ : val → iProp Σ),
        own_geometric_tape α p q (n::ns) -∗
        (own_geometric_tape α p q ns -∗ Φ #n) -∗
        WP geometric_tape #lbl:α #p #q [{ Φ }].
  Proof.
    iIntros (p q α n).
    iInduction (n) as [|n] "IH".
    - iIntros (ns Φ) "(%l & Htape & %is_tl) HΦ".
      destruct is_tl as (suf & -> & is_tl).
      simpl.
      unfold geometric_tape.
      wp_pures.
      wp_apply (twp_bernoulli_tape with "Htape") as "Htape".
      wp_pures.
      iModIntro.
      by iApply ("HΦ" with "[$Htape]").
    - iIntros (ns Φ) "(%l & Htape & %is_tl) HΦ".
      destruct is_tl as (suf & -> & is_tl).
      simpl.
      unfold geometric_tape.
      wp_pures.
      wp_apply (twp_bernoulli_tape with "Htape") as "Htape".
      do 2 wp_pure.
      fold geometric_tape.
      wp_apply ("IH" with "[$Htape]") as "Htape".
      { iPureIntro.
        by eexists.
      }
      wp_pures.
      rewrite -(Nat2Z.inj_add 1 n) /=.
      iModIntro.
      iApply ("HΦ" with "Htape").
  Qed.

  #[global] Instance geometric_of_bernoulli : geometric_spec geometric_tape geometric_alloc :=
    GeometricSpec _ _
      (@twp_geometric_split)
      (@own_geometric_tape)
      (@twp_geometric_alloc)
      (@twp_geometric_tape)
      (@twp_geometric_presample_adv_comp)
  .
  
End Geometric.
