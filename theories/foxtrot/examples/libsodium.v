(** randombytes_uniform implementation from libsodium
    https://github.com/jedisct1/libsodium/blob/85ddc5c2c6c7b8f7c99f9af6039e18f1f2ca0daa/src/libsodium/randombytes/randombytes.c#L146
    Code is simplified (we assume randombytes_random distributes uniformly), 

    We also do a check that the input is a number smaller than 2^32
*)
From clutch.foxtrot Require Import foxtrot.
Set Default Proof Using "Type*".

Section proof.
  Context (MAX: nat). (** Usually 2^32*)
  
  Definition randombytes_uniform : val :=
    λ: "upper_bound",
      if: #MAX ≤ "upper_bound" then #0 else
        if: "upper_bound" < #2 then #0 else
          let: "min" := (#MAX `rem` ("upper_bound")) in
          let: "r" := ref #0 in 
          (rec: "f" "x" := "r" <- rand #(MAX-1)%nat;;
                           if: !"r"< "min"
                           then  "f" #()
                           else (!"r") `rem` "upper_bound"
          ) #()
  .

  Definition ideal_uniform: val :=
    λ: "upper_bound",
      if: ((#MAX ≤ "upper_bound") || ("upper_bound"= #0)) then #0 else
          rand ("upper_bound"-#1).

  Local Ltac start K j:=
    apply (refines_sound (#[foxtrotRΣ])); iIntros;
    unfold_rel;
    iIntros (K j);
    iIntros "Hspec";
    wp_pures;
    iModIntro;
    iFrame "Hspec";
    iModIntro;
    simpl;
    iIntros (??) "[%n [->->]]";
    unfold_rel;
    clear K j;
    iIntros (K j) "Hspec".

  Lemma randombytes_uniform_refines_ideal :
    ∅ ⊨ randombytes_uniform ≤ctx≤ ideal_uniform : TNat → TNat.
  Proof.
    rewrite /ideal_uniform/randombytes_uniform.
    eapply (ctx_refines_transitive) with
      (λ: "upper_bound",
         if: #MAX ≤ "upper_bound" then #0 else
           if: "upper_bound" = #0 then #0 else
             Fork (rand (#MAX `quot` "upper_bound" - #1));; rand ("upper_bound"-#1)
      )%V; last first.
    { start K j. 
      wp_pures.
      tp_pures j.
      case_bool_decide; tp_pures j; try wp_pures.
      - iFrame. by iExists 0%nat. 
      - solve_vals_compare_safe.
      - case_bool_decide; tp_pures j; wp_pures.
        + iFrame. by iExists 0%nat.
        + wp_apply (wp_fork).
          * wp_pures. by wp_apply wp_rand.
          * wp_pures.
            wp_apply (wp_couple_rand_rand with "[$]").
            -- simpl. lia.
            -- simpl.
               iIntros (?) "[% ?]".
               iFrame.
               by iExists _. 
    }
    eapply (ctx_refines_transitive) with
      (λ: "upper_bound",
         if: #MAX ≤ "upper_bound" then #0 else
           if: "upper_bound" = #0 then #0 else
             (rand (#MAX - (#MAX `rem` "upper_bound") -#1)) `rem` "upper_bound"
      )%V; last first.
    { start K j.
      wp_pures.
      tp_pures j.
      case_bool_decide; tp_pures j; try wp_pures.
      - iFrame. by iExists 0%nat. 
      - solve_vals_compare_safe.
      - case_bool_decide; tp_pures j; wp_pures.
        + iFrame. by iExists 0%nat.
        + tp_bind j (Fork _)%E.
          iMod (pupd_fork with "[$Hspec]") as "[Hspec [%j' Hspec']]".
          wp_pures.
          simpl. tp_pures j.
          assert (0<n)%nat.
          { destruct n; [done|lia]. }
          assert (MAX `mod` n< MAX)%Z as H'.
          { apply Z.lt_le_trans with n; last lia.
            apply Z.mod_pos_bound. lia. }
          assert (0< MAX `div` n)%nat.
          { apply Nat.div_str_pos. lia. }
          tp_pures j'.
          wp_apply (wp_couple_rand_two_rands (n-1)%nat (MAX `div` n -1 )%nat (λ x y, x+y*n)%nat with "[Hspec Hspec']").
          * by erewrite Nat2Z.id. 
          * by erewrite Nat2Z.id.
          * rewrite !Z.rem_mod_nonneg; try lia.
            rewrite -!Nat2Z.inj_mod.
            rewrite -Nat2Z.inj_mod in H'.
            rewrite -Nat2Z.inj_sub; last lia.
            replace 1%Z with (Z.of_nat 1) by lia.
            rewrite -Nat2Z.inj_sub; last lia.
            f_equal.
            f_equal.
            replace (S (n-1)) with n by lia.
            replace (S _) with (MAX `div` n)%nat; last lia.
            rewrite {1}(Nat.div_mod_eq MAX n).
            lia.
          * simpl.
            intros x y.
            replace (S _) with n by lia.
            replace (S _) with (MAX `div` n)%nat; last lia.
            replace (S _) with ((MAX `div` n  + (n - 1) * MAX `div` n))%nat by lia.
            intros. simpl.
            apply Nat.lt_le_trans with (n + y * n)%nat; first lia.
            trans (1*(MAX / n) + (n-1) * (MAX / n))%nat; last lia.
            rewrite -Nat.mul_add_distr_r.
            replace (1+_) with n by lia.
            trans (n*(y+1)); first lia.
            apply Nat.mul_le_mono; lia.
          * intros ????.
            simpl. 
            replace (S _) with n by lia.
            replace (S _) with (MAX `div` n)%nat; last lia.
            intros ???? H''.
            apply Logic.and_comm.
            eapply Nat.mul_split_l; [done..|lia].
          * intros ?.
            replace (S _) with n by lia.
            replace (S _) with (MAX `div` n)%nat; last lia.
            intros.
            exists (x `mod` n).
            eexists (x/n).
            repeat split.
            -- apply Nat.mod_upper_bound; lia.
            -- apply Nat.Div0.div_lt_upper_bound. lia.
            -- rewrite {3}(Nat.div_mod_eq x n). lia.
          * rewrite Nat2Z.inj_sub; last lia.
            iFrame "Hspec".
            rewrite Nat2Z.inj_sub; last lia.
            rewrite Z.quot_div_nonneg; [|lia..].
            rewrite Nat2Z.inj_div. replace (Z.of_nat 1) with 1%Z by lia.
            rewrite -(fill_empty (rand _)%E).
            iFrame. 
          * iIntros (x) "(%n'&%m'&%&%&->&Hspec&_)".
            wp_pures.
            iFrame.
            iExists _. iPureIntro.
            split; last done.
            f_equal.
            rewrite Nat2Z.inj_add Nat2Z.inj_mul.
            rewrite Z.rem_add; try lia.
            rewrite Z.rem_small; [done|lia].
    }
    start K j.
    wp_pures.
    tp_pures j.
    case_bool_decide; tp_pures j; try wp_pures.
    - iFrame. by iExists 0%nat. 
    - solve_vals_compare_safe.
    - case_bool_decide as H1; tp_pures j; wp_pures.
      + inversion H1. subst. rewrite bool_decide_eq_true_2; last lia.
        wp_pures. iFrame. by iExists 0%nat.
      + destruct (decide (n=1)).
        { subst. rewrite bool_decide_eq_true_2; last lia.
          replace (Z.of_nat 1) with 1%Z by lia.
          tp_bind j (rand _)%E.
          iMod (pupd_rand with "[$]") as "(%&Hspec&%)".
          simpl.
          tp_pures j.
          rewrite !Z.rem_1_r.
          wp_pures.
          iFrame.
          iModIntro. by iExists 0.
        } 
        rewrite bool_decide_eq_false_2; last first.
        { destruct n; [done|lia]. }
        wp_pures.
        wp_alloc l as "Hl".
        do 3 wp_pure.
        assert (0<n)%nat.
        { destruct n; [done|lia]. }
        assert (MAX `mod` n< MAX)%Z as H'.
        { apply Z.lt_le_trans with n; last lia.
          apply Z.mod_pos_bound. lia. }
        assert (0< MAX `div` n)%nat.
        { apply Nat.div_str_pos. lia. }
        pose (λ x, if bool_decide (MAX -MAX `mod` n <= x)%nat then x+MAX else
                     if bool_decide (x < MAX `mod` n)
                     then x + MAX - MAX `mod` n else x) as f.
        assert (Inj (=) (=) f).
        { intros x y.
          rewrite /f.
          intros. rewrite -Nat2Z.inj_mod in H'. 
          repeat case_bool_decide; lia.
        }
        rewrite !Z.rem_mod_nonneg; try lia.
        rewrite -!Nat2Z.inj_mod.
        rewrite -Nat2Z.inj_mod in H'.
        rewrite -Nat2Z.inj_sub; last lia.
        replace 1%Z with (Z.of_nat 1) by lia.
        rewrite -Nat2Z.inj_sub; last lia.
        remember 0%Z as z eqn:Heqz.
        rewrite Heqz in H1.
        clear Heqz.
        iLöb as "IH" forall (z).
        tp_bind j (rand _)%E.
        wp_pures.
        wp_apply (wp_couple_fragmented_rand_rand_inj f with "[$]"); first lia.
        { intros x.
          replace (S _) with (MAX - MAX `mod` n) by lia.
          rewrite /f.
          intros. 
          rewrite bool_decide_eq_false_2; last lia.
          case_bool_decide; lia. 
        }
        iIntros (x) "(%&[H|H])".
        * (* accepted *)
          iDestruct "H" as "(%&%&<-&Hspec)".
          simpl.
          wp_store.
          wp_load.
          wp_pures.
          rewrite bool_decide_eq_false_2; last first.
          { rewrite /f.
            rewrite bool_decide_eq_false_2; last lia.
            rewrite -Z.le_ngt.
            case_bool_decide; last lia.
            rewrite {2}(Nat.div_mod_eq MAX n).
            trans (m+n*(MAX / n)); last lia.
            trans n.
            - apply Z.lt_le_incl.
              rewrite Nat2Z.inj_mod.
              apply Z_mod_lt. lia.
            - assert (0<MAX/n); first lia.
              trans (n*1)%Z; first lia.
              trans (n*MAX`div`n); last lia.
              rewrite Nat2Z.inj_mul.
              apply Zmult_le_compat; lia. 
          }
          tp_pures j.
          wp_pures.
          wp_load.
          wp_pures.
          iFrame.
          iExists (m `mod` n). iPureIntro.
          rewrite !Z.rem_mod_nonneg; try lia.
          rewrite -!Nat2Z.inj_mod.
          split; last done.
          f_equal.
          rewrite /f.
          rewrite bool_decide_eq_false_2; last lia.
          case_bool_decide; last done.
          rewrite -Nat.add_sub_assoc; last lia.
          rewrite -Nat.Div0.add_mod_idemp_r.
          replace ((_-_)`mod`_) with 0; first (repeat f_equal; lia).
          symmetry.
          rewrite -Nat.Div0.div_exact.
          rewrite {1}(Nat.div_mod_eq MAX n).
          trans (n*MAX`div`n); first lia.
          f_equal. 
          rewrite {2}(Nat.div_mod_eq MAX n).
          replace (_+_-_) with (n*MAX`div`n) by lia.
          rewrite Nat.mul_comm.
          rewrite Nat.div_mul; lia.
        * (* rejected *)
          simpl.
          iDestruct "H" as "(%Hcontra&Hspec)".
          tp_pures j.
          wp_store.
          wp_load.
          wp_pures.
          rewrite bool_decide_eq_true_2; last first.
          { apply Z.nle_gt.
            intros Hineq.
            apply Hcontra.
            rewrite /f.
            destruct (decide (MAX-MAX`mod`n<=x)).
            - exists (x- (MAX-MAX`mod`n)).
              split.
              + trans (MAX -1 - (MAX- MAX`mod`n)); first lia.
                trans (MAX`mod` n - 1); first lia.
                rewrite {2}(Nat.div_mod_eq MAX n).
                trans (n*MAX`div` n - 1); last lia.
                assert (MAX `mod` n < n).
                { apply Nat.mod_upper_bound; lia. }
                assert (0< MAX `div` n)%nat.
                { apply Nat.div_str_pos. lia. }
                apply Nat.sub_le_mono_r.
                trans (n*1); first lia.
                apply Nat.mul_le_mono; lia.
              + rewrite bool_decide_eq_false_2; first (rewrite bool_decide_eq_true_2; lia).
                apply Nat.lt_nge.
                apply Nat.lt_le_trans with (MAX `mod` n); first lia.
                rewrite {2}(Nat.div_mod_eq MAX n).
                trans (n*MAX`div` n ); last lia.
                assert (MAX `mod` n < n).
                { apply Nat.mod_upper_bound; lia. }
                assert (0< MAX `div` n)%nat.
                { apply Nat.div_str_pos. lia. }
                trans (n*1); first lia.
                apply Nat.mul_le_mono; lia.
            - exists x.
              split; first lia.
              rewrite bool_decide_eq_false_2; last lia.
              rewrite bool_decide_eq_false_2; lia. }
          wp_pure.
          iApply ("IH" with "[$][$]").
  Qed. 

  Lemma ideal_refines_randombytes_uniform :
    ∅ ⊨ ideal_uniform ≤ctx≤ randombytes_uniform  : TNat → TNat.
  Proof.
    rewrite /ideal_uniform/randombytes_uniform.
    eapply (ctx_refines_transitive) with
      (λ: "upper_bound",
         if: #MAX ≤ "upper_bound" then #0 else
           if: "upper_bound" = #0 then #0 else
             let: "α" := alloc ("upper_bound"-#1) in
             let: "β" := alloc (#MAX `quot` "upper_bound" - #1) in
             rand("α") ("upper_bound"-#1)
      )%V.
    { start K j. 
      wp_pures.
      tp_pures j.
      case_bool_decide; tp_pures j; try wp_pures.
      - iFrame. by iExists 0%nat. 
      - solve_vals_compare_safe.
      - case_bool_decide; tp_pures j; wp_pures.
        + iFrame. by iExists 0%nat.
        + tp_allocnattape j α as "Hα".
          tp_pures j.
          tp_allocnattape j β as "Hβ".
          tp_pures j.
          wp_apply (wp_couple_rand_rand_lbl with "[$Hspec $Hα]"); first (simpl; lia).
          iIntros (?) "(_&Hspec&%)".
          simpl. iFrame. by iExists _.
    }
    eapply (ctx_refines_transitive) with
      (λ: "upper_bound",
         if: #MAX ≤ "upper_bound" then #0 else
           if: "upper_bound" = #0 then #0 else
             (rand (#MAX - (#MAX `rem` "upper_bound") -#1)) `rem` "upper_bound"
      )%V.
    { start K j.
      wp_pures.
      tp_pures j.
      case_bool_decide; tp_pures j; try wp_pures.
      - iFrame. by iExists 0%nat. 
      - solve_vals_compare_safe.
      - case_bool_decide; tp_pures j; wp_pures.
        + iFrame. by iExists 0%nat.
        + wp_alloctape α as "Hα".
          wp_pures. 
          wp_alloctape β as "Hβ".
          wp_pures.
          assert (0<n)%nat.
          { destruct n; [done|lia]. }
          assert (MAX `mod` n< MAX)%Z as H'.
          { apply Z.lt_le_trans with n; last lia.
            apply Z.mod_pos_bound. lia. }
          assert (0< MAX `div` n)%nat.
          { apply Nat.div_str_pos. lia. }
          tp_bind j (rand _)%E.
          iMod (pupd_couple_two_tapes_rand (n-1)%nat (MAX `div` n -1 )%nat (λ x y, x+y*n) with "[Hα][Hβ][$]") as "H".
          * by erewrite Nat2Z.id. 
          * by erewrite Nat2Z.id.
          * rewrite !Z.rem_mod_nonneg; try lia.
            rewrite -!Nat2Z.inj_mod.
            rewrite -Nat2Z.inj_mod in H'.
            rewrite -Nat2Z.inj_sub; last lia.
            replace 1%Z with (Z.of_nat 1) by lia.
            rewrite -Nat2Z.inj_sub; last lia.
            f_equal.
            f_equal.
            replace (S (n-1)) with n by lia.
            replace (S _) with (MAX `div` n)%nat; last lia.
            rewrite {1}(Nat.div_mod_eq MAX n).
            lia.
          * simpl.
            intros x y.
            replace (S _) with n by lia.
            replace (S _) with (MAX `div` n)%nat; last lia.
            replace (S _) with ((MAX `div` n  + (n - 1) * MAX `div` n))%nat by lia.
            intros. simpl.
            apply Nat.lt_le_trans with (n + y * n)%nat; first lia.
            trans (1*(MAX / n) + (n-1) * (MAX / n))%nat; last lia.
            rewrite -Nat.mul_add_distr_r.
            replace (1+_) with n by lia.
            trans (n*(y+1)); first lia.
            apply Nat.mul_le_mono; lia.
          * intros ????.
            simpl. 
            replace (S _) with n by lia.
            replace (S _) with (MAX `div` n)%nat; last lia.
            intros ???? H''.
            apply Logic.and_comm.
            eapply Nat.mul_split_l; [done..|lia].
          * intros ?.
            replace (S _) with n by lia.
            replace (S _) with (MAX `div` n)%nat; last lia.
            intros.
            exists (x `mod` n).
            eexists (x/n).
            repeat split.
            -- apply Nat.mod_upper_bound; lia.
            -- apply Nat.Div0.div_lt_upper_bound. lia.
            -- rewrite {3}(Nat.div_mod_eq x n). lia.
          * replace (Z.to_nat (n-1)%Z) with (n-1); last lia.
            iFrame.
          * rewrite Z.quot_div_nonneg; try lia.
            rewrite Z2Nat.inj_sub; last lia.
            rewrite -Nat2Z.inj_div.
            rewrite Nat2Z.id.
            replace (Z.to_nat 1) with 1 by lia.
            iFrame.
          * iDestruct "H" as "(%&%&Hα&Hβ &Hspec&%&%)".
            simpl.
            tp_pures j.
            wp_randtape.
            { replace (Z.to_nat (n-1)) with (n-1); [done|lia]. }
            iFrame. 
            iExists _. iPureIntro.
            split; first done.
            f_equal.
            rewrite Nat2Z.inj_add Nat2Z.inj_mul.
            rewrite Z.rem_add; try lia.
            rewrite Z.rem_small; [done|lia].
    }eapply (ctx_refines_transitive) with
      (λ: "upper_bound",
         if: #MAX ≤ "upper_bound" then #0 else
           if: "upper_bound" = #0 then #0 else
             (rand(alloc (#MAX - (#MAX `rem` "upper_bound") -#1) ) (#MAX - (#MAX `rem` "upper_bound") -#1)) `rem` "upper_bound"
      )%V.
    { start K j.
      wp_pures.
      tp_pures j.
      case_bool_decide; tp_pures j; try wp_pures.
      - iFrame. by iExists 0%nat. 
      - solve_vals_compare_safe.
      - case_bool_decide; tp_pures j; wp_pures.
        + iFrame. by iExists 0%nat.
        + tp_allocnattape j α as "Hα".
          tp_pures j.
          tp_bind j (rand(_) _)%E.
          wp_apply (wp_couple_rand_rand_lbl with "[$Hspec $Hα]"); first (simpl; lia).
          iIntros (?) "(_&Hspec&%)".
          simpl.
          tp_pures j.
          wp_pures.
          iFrame.
          iExists _. iPureIntro.
          destruct n; first done.
          rewrite !Z.rem_mod_nonneg; try lia.
          by rewrite -Nat2Z.inj_mod. 
    }
    start K j.
    wp_pures.
    tp_pures j.
    case_bool_decide; tp_pures j; try wp_pures.
    - iFrame. by iExists 0%nat. 
    - case_bool_decide as H1; tp_pures j; wp_pures.
      + destruct (decide (n=1)).
        * subst. rewrite bool_decide_eq_false_2; last done.
          wp_pures.
          wp_alloctape α as "Hα".
          wp_pures.
          wp_apply (wp_rand_tape_empty with "[$]").
          iIntros (?) "[Hα %]".
          wp_pures.
          replace (Z.of_nat 1) with 1%Z by lia.
          rewrite !Z.rem_1_r.
          iFrame.
          by iExists 0.
        * destruct n; last lia.
          rewrite bool_decide_eq_true_2; last done.
          wp_pures.
          iFrame.
          by iExists 0.
      + rewrite bool_decide_eq_false_2; last first.
        { destruct n; [lia|done]. }
        wp_pures.
        tp_alloc j  as l "Hl".
        do 3 tp_pure j.
        assert (0<n)%nat.
        { destruct n; [done|lia]. }
        assert (MAX `mod` n< MAX)%Z as H'.
        { apply Z.lt_le_trans with n; last lia.
          apply Z.mod_pos_bound. lia. }
        assert (0< MAX `div` n)%nat.
        { apply Nat.div_str_pos. lia. }
        pose (λ x, if bool_decide (MAX -MAX `mod` n <= x)%nat then x+MAX else
                     if bool_decide (x < MAX `mod` n)
                     then x + MAX - MAX `mod` n else x) as f.
        assert (Inj (=) (=) f).
        { intros x y.
          rewrite /f.
          intros. rewrite -Nat2Z.inj_mod in H'. 
          repeat case_bool_decide; lia.
        }
        rewrite !Z.rem_mod_nonneg; try lia.
        rewrite -!Nat2Z.inj_mod.
        rewrite -Nat2Z.inj_mod in H'.
        rewrite -Nat2Z.inj_sub; last lia.
        replace 1%Z with (Z.of_nat 1) by lia.
        rewrite -Nat2Z.inj_sub; last lia.
        remember 0%Z as z eqn:Heqz.
        clear Heqz.
        wp_alloctape α as "Hα".
        destruct (MAX `mod` n) eqn :Heqn.
        { wp_pures.
          rewrite !Z.rem_mod_nonneg; try lia.
          rewrite -!Nat2Z.inj_mod.
          rewrite Heqn.
          replace (_-_-_)%Z with (Z.of_nat (MAX - 1)) by lia.
          tp_pures j.
          tp_bind j (rand _)%E.
          iMod (pupd_couple_tape_rand with "[$][$]") as "(%&?&?&%)"; [|simpl;lia|].
          - rewrite TCEq_eq. lia.
          - simpl.
            tp_store j.
            tp_pures j.
            tp_load j.
            tp_pures j.
            rewrite bool_decide_eq_false_2; last lia.
            tp_pures j.
            wp_randtape.
            { rewrite TCEq_eq; lia. }
            tp_load j.
            tp_pures j.
            wp_pures. 
            iFrame.
            iExists _.
            iPureIntro.
            rewrite Z.rem_mod_nonneg; try lia.
            by rewrite -Nat2Z.inj_mod. }
        iMod (pupd_epsilon_err) as "(%ε&%&Hε)".
        iRevert (z) "Hl Hspec Hα".
        iApply (ec_ind_simpl _ (MAX / (MAX - (MAX - MAX `mod` n)%nat))%R with "[][$]"); first done.
        { rewrite -Rcomplements.Rlt_div_r.
          - rewrite Rmult_1_l.
            rewrite -minus_INR; last lia.
            apply lt_INR. lia.
          - rewrite -minus_INR; last lia.
            apply Rlt_gt.
            replace 0%R with (INR 0) by done.
            apply lt_INR. lia. }
        iModIntro.
        iIntros  "[IH Hε] % Hl Hspec Ha".
        tp_pures j.
        tp_bind j (rand _)%E.
        iMod (pupd_couple_fragmented_tape_rand_inj_rev' f with "[$][$][$]") as "(%x&%&Hspec&H)"; first lra.
        { lia. }
        { intros x.
          replace (S _) with (MAX - MAX `mod` n) by lia.
          rewrite /f.
          intros. 
          rewrite bool_decide_eq_false_2; last lia.
          case_bool_decide; lia. 
        }
        iDestruct "H" as "[H|H]".
        * (* accepted *)
          iDestruct "H" as "(%m&%&<-&Hα)".
          simpl.
          tp_store j.
          tp_pures j.
          tp_load j.
          tp_pures j.
          rewrite bool_decide_eq_false_2; last first.
          { rewrite /f.
            rewrite bool_decide_eq_false_2; last lia.
            rewrite -Z.le_ngt.
            case_bool_decide; last lia.
            rewrite -Heqn.
            rewrite {2}(Nat.div_mod_eq MAX n).
            trans (m+n*(MAX / n)); last lia.
            trans n.
            - apply Z.lt_le_incl.
              rewrite Nat2Z.inj_mod.
              apply Z_mod_lt. lia.
            - assert (0<MAX/n); first lia.
              trans (n*1)%Z; first lia.
              trans (n*MAX`div`n); last lia.
              rewrite Nat2Z.inj_mul.
              apply Zmult_le_compat; lia. 
          }
          tp_pures j.
          wp_randtape.
          { rewrite -Heqn.
            rewrite TCEq_eq.
            rewrite Z.rem_mod_nonneg; try lia.
            rewrite -Nat2Z.inj_mod. lia.
          }
          tp_load j.
          tp_pures j.
          wp_pures.
          iFrame. 
          iExists (m `mod` n). iPureIntro.
          rewrite !Z.rem_mod_nonneg; try lia.
          rewrite -!Nat2Z.inj_mod.
          split; first done.
          f_equal.
          rewrite /f.
          rewrite bool_decide_eq_false_2; last lia.
          case_bool_decide; last done.
          rewrite -Nat.add_sub_assoc; last lia.
          rewrite -Nat.Div0.add_mod_idemp_r.
          replace ((_-_)`mod`_) with 0; first (repeat f_equal; lia).
          symmetry.
          rewrite -Nat.Div0.div_exact.
          rewrite {1}(Nat.div_mod_eq MAX n).
          trans (n*MAX`div`n); first lia.
          f_equal. 
          rewrite {2}(Nat.div_mod_eq MAX n).
          replace (_+_-_) with (n*MAX`div`n) by lia.
          rewrite Nat.mul_comm.
          rewrite Nat.div_mul; lia.
        * (* rejected *)
          replace (S (_-_)) with MAX by lia.
          rewrite -Heqn.
          replace (S (_-_)) with (MAX - MAX `mod` n) by lia.
          simpl.
          iDestruct "H" as "(%Hcontra&Hα&Hε)".
          tp_store j.
          tp_pures j.
          tp_load j.
          tp_pures j.
          rewrite bool_decide_eq_true_2; last first.
          { apply Z.nle_gt.
            intros Hineq.
            apply Hcontra.
            rewrite /f.
            destruct (decide (MAX-MAX`mod`n<=x)).
            - exists (x- (MAX-MAX`mod`n)).
              split.
              + trans (MAX -1 - (MAX- MAX`mod`n)); first lia.
                trans (MAX`mod` n - 1); first lia.
                rewrite {2}(Nat.div_mod_eq MAX n).
                trans (n*MAX`div` n - 1); last lia.
                assert (MAX `mod` n < n).
                { apply Nat.mod_upper_bound; lia. }
                assert (0< MAX `div` n)%nat.
                { apply Nat.div_str_pos. lia. }
                apply Nat.sub_le_mono_r.
                trans (n*1); first lia.
                apply Nat.mul_le_mono; lia.
              + rewrite bool_decide_eq_false_2; first (rewrite bool_decide_eq_true_2; lia).
                apply Nat.lt_nge.
                apply Nat.lt_le_trans with (MAX `mod` n); first lia.
                rewrite {2}(Nat.div_mod_eq MAX n).
                trans (n*MAX`div` n ); last lia.
                assert (MAX `mod` n < n).
                { apply Nat.mod_upper_bound; lia. }
                assert (0< MAX `div` n)%nat.
                { apply Nat.div_str_pos. lia. }
                trans (n*1); first lia.
                apply Nat.mul_le_mono; lia.
            - exists x.
              split; first lia.
              rewrite bool_decide_eq_false_2; last lia.
              rewrite bool_decide_eq_false_2; lia. }
          tp_pure j.
          iApply ("IH" with "[$][$][$][$]").
  Qed. 
  

  Lemma randombytes_uniform_equivalent_ideal :
    ∅ ⊨ randombytes_uniform =ctx= ideal_uniform : TNat → TNat.
  Proof.
    split.
    - apply randombytes_uniform_refines_ideal.
    - apply ideal_refines_randombytes_uniform.
  Qed. 

  
End proof.
