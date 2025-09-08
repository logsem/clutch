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
  
  Fixpoint bernoulli_to_geometric_aux (l : list (fin 2)) (acc : nat) : list nat := 
    match l with 
    | 0::l => bernoulli_to_geometric_aux l (S acc)
    | 1::l => acc :: bernoulli_to_geometric_aux l 0
    | _ => []
    end.

  Definition bernoulli_to_geometric v := bernoulli_to_geometric_aux v 0.

  Definition geometric_to_bernoulli : list nat -> list (fin 2) :=
    List.flat_map (fun h => repeat 0 h ++ [1]).

  Lemma bernoulli_to_geometric_aux_repeat_0 (n acc : nat) :
    bernoulli_to_geometric_aux (repeat 0 n) acc = [].
  Proof.
    elim: n acc => /= [|n IH] acc //.
  Qed. 
  Lemma bernoulli_to_geometric_repeat_0 (n : nat) :
    bernoulli_to_geometric (repeat 0 n) = [].
  Proof.
    apply bernoulli_to_geometric_aux_repeat_0.
  Qed.
  
  Lemma bernoulli_to_geometric_aux_repeat (n acc : nat) :
    bernoulli_to_geometric_aux (repeat 0 n ++ [1]) acc = [n + acc].
  Proof.
    elim: n acc => /= [|n IH] acc //.
    rewrite /bernoulli_to_geometric /= IH.
    f_equal; lia.
  Qed. 
  Lemma bernoulli_to_geometric_repeat (n : nat) :
    bernoulli_to_geometric (repeat 0 n ++ [1]) = [n].
  Proof.
    rewrite /bernoulli_to_geometric bernoulli_to_geometric_aux_repeat.
    f_equal; lia.
  Qed.

  Lemma bernoulli_to_geometric_aux_app (l1 l2 : list (fin 2)) (acc : nat) :
    bernoulli_to_geometric_aux (l1 ++ [1] ++ l2) acc 
      = 
    bernoulli_to_geometric_aux (l1 ++ [1]) acc ++ bernoulli_to_geometric l2.
  Proof.
    elim: l1 acc => /= [|h1 t1 IH] acc //.
    rewrite !IH //.
    by full_inv_fin.
  Qed.

  Lemma bernoulli_to_geometric_app (l1 l2 : list (fin 2)) :
    bernoulli_to_geometric (l1 ++ [1] ++ l2) 
      = 
    bernoulli_to_geometric (l1 ++ [1]) ++ bernoulli_to_geometric l2.
  Proof.
    apply bernoulli_to_geometric_aux_app.
  Qed.

  Lemma geometric_to_bernoulli_to_geometric (g : list nat) :
    bernoulli_to_geometric (geometric_to_bernoulli g) = g.
  Proof.
    elim: g => /= [|h g IH] //.
    rewrite -app_assoc bernoulli_to_geometric_app IH bernoulli_to_geometric_repeat.
    reflexivity.
  Qed.

  Lemma list_decomposition (l : list (fin 2)) :
    { 
      '(ns, n) 
    | l = (flat_map (fun v => repeat 0 v ++ [1]) ns) ++ repeat 0 n 
    }.
  Proof.
    elim: l => [|h t [[ns n] ->]]; first (by exists ([], 0%nat));
    full_inv_fin; first case ns => [|hns tns];
    by 
      [ exists ([], (S n))
      | exists ((S hns :: tns), n)
      | exists ((0%nat :: ns), n) ].
  Qed.

  Lemma bernoulli_to_geometric_to_bernoulli (b : list (fin 2)) :
    (geometric_to_bernoulli ∘ bernoulli_to_geometric) (b ++ [1])
      = 
    b ++ [1].
  Proof.

    case: (list_decomposition b) => [[ns n] ->].
    elim: ns => [|hns tns IHns] /=; first rewrite bernoulli_to_geometric_repeat //; first rewrite /= app_nil_r //.
    rewrite -!app_assoc bernoulli_to_geometric_app bernoulli_to_geometric_repeat /=.
    simpl in IHns.
    rewrite !app_assoc IHns -!app_assoc //.
  Qed.
  
  Lemma bernoulli_to_geometric_translation
    (v : list (fin 2)) (l : list nat) :
    is_geometric_translation v l 
      ↔ 
    (l = bernoulli_to_geometric v ∧ ∀ l' k, v = l' ++ [k] -> k = 1).
  Proof.
    elim: l v => [|h l IH] v //=; split.
    - move=> ->. split=>[|[|??] ? ?] //.
    - destruct v as [| e v ] using rev_ind.
      + split=>[|[|??] ? ?] //.
      + move=>[H1 H2].
        rewrite (H2 v e eq_refl) in H1.
        case: (list_decomposition v) => [[ns n] Heq].
        rewrite Heq in H1.
        destruct ns; simpl in H1.
        * rewrite bernoulli_to_geometric_repeat // in H1.
        * rewrite -!app_assoc bernoulli_to_geometric_app bernoulli_to_geometric_repeat // in H1.
    - intros (suf & Hv_eq & Htranslation_suf).
      subst v.
      split.
      + rewrite -app_assoc bernoulli_to_geometric_app bernoulli_to_geometric_repeat.
        f_equal.
        by apply IH.
      + move=> l' k Heq.
        destruct suf as [| e suf _] using rev_ind.
        * rewrite app_nil_r in Heq.
          by apply list_snoc_singleton_inv in Heq as [_ ->].
        * apply IH in Htranslation_suf as [_ Heqsuf].
          apply (Heqsuf suf). 
          rewrite app_assoc in Heq.
          by apply list_snoc_singleton_inv in Heq as [_ ->].
  - move => [Heq Hend1].
    case: (list_decomposition v) => [[ns n] Heqv]. subst v.
    assert (n = 0%nat) as ->.
    { destruct n as [|n]; first done.
      specialize Hend1 with (flat_map (λ v : nat, repeat 0 v ++ [1]) ns ++ repeat 0 (n)) 0.
      exfalso.
      assert ((0 : fin 2) ≠ 1) as contra by by intro.
      apply contra, Hend1.
      replace (S n) with (n + 1)%nat by lia.
      rewrite repeat_app app_assoc //. }
    simpl in *.
    rewrite ->app_nil_r in *.
    destruct ns as [|n ns]; first done.
    simpl.
    rewrite /= -app_assoc bernoulli_to_geometric_app bernoulli_to_geometric_repeat in Heq.
    injection Heq as -> ->.
    eexists.
    split; first done.
    apply IH. split; first done.
    intros l' k Heq.
    apply Hend1 with (l' := (repeat 0 n ++ [1]) ++ l').
    rewrite /= Heq app_assoc //.
  Qed.

  Lemma geometric_to_bernoulli_ends_with_1 (g_tape : list nat) :
    g_tape = [] ∨ ∃ b_tape, b_tape ++ [1%fin] = geometric_to_bernoulli g_tape.
  Proof.
    destruct g_tape as [|g_end g_tape _] using rev_ind; first by left.
    right.
    rewrite /geometric_to_bernoulli flat_map_app /= app_nil_r app_assoc.
    eauto.
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

  Lemma geometric_spec `{!erisGS Σ} 
    (N M k : nat) (Hlt : (N <= M)%nat) (p := N / (S M)) :
  [[{↯ (1 - (((1 - p)^k) * p))%R }]]
    geometric #N #M
  [[{RET #k; True}]].
  Proof.
    assert (0 <= p <= 1)%R as Hp. {
      split; subst p; simpl_expr.
    }
    induction k.
    - iIntros "%Φ Herr HΦ".
      rewrite /geometric /geometric_tape Rmult_1_l.
      wp_pures.
      wp_apply (bernoulli_success_spec_simple with "Herr") as "_".
      wp_pures.
      by iApply "HΦ".
    - iIntros "%Φ Herr HΦ".
      rewrite /geometric /geometric_tape.
      wp_pures.
      fold geometric_tape geometric.
      replace (1 - (1 - p)^(S k) * p) with ((1 - p) * (1 - (1 - p)^k * p) + p) by rewrite //=.
      wp_apply (twp_bernoulli_scale _ _ _ (1 - (1 - p) ^ k * p) 1 with "Herr") as "%n [[-> Herr] | [-> Herr]]";
      fold p; try done; last solve[cred_contra].
      { apply Rle_0_le_minus.
        assert (0 <= ((1 - p) ^ k) <= 1)%R by (apply Rpow_le_1; lra).
        by apply Rmult_le_1. }
      wp_pures.
      wp_apply (IHk with "Herr") as "_".
      wp_pures.
      rewrite Z.add_1_l -Nat2Z.inj_succ.
      by iApply "HΦ".
  Qed.

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

    Lemma twp_geometric_presample `{!erisGS Σ} :
      ∀ (e : expr) (α : loc) (p q : nat)
        (D : nat → R) (L : R) (ε : R)
        (ns : list nat)
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
         iIntros (e α p q D L ε ns Φ Hp Hpq He HD HSum)
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
       
End Geometric.
