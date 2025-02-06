From iris.algebra Require Import excl_auth.
From clutch.coneris Require Import coneris par spawn lazy_rand_interface.
  
Set Default Proof Using "Type*".
Section lemmas.
  Context `{!inG Σ (excl_authR boolO)}.

  (* Helpful lemmas *)
  Lemma ghost_var_alloc b :
    ⊢ |==> ∃ γ, own γ (●E b) ∗ own γ (◯E b).
  Proof.
    iMod (own_alloc (●E b ⋅ ◯E b)) as (γ) "[??]".
    - by apply excl_auth_valid.
    - by eauto with iFrame.
  Qed.

  Lemma ghost_var_agree γ b c :
    own γ (●E b) -∗ own γ (◯E c) -∗ ⌜ b = c ⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    by iCombine "Hγ● Hγ◯" gives %->%excl_auth_agree_L.
  Qed.

  Lemma ghost_var_update γ b' b c :
    own γ (●E b) -∗ own γ (◯E c) ==∗ own γ (●E b') ∗ own γ (◯E b').
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E b' ⋅ ◯E b') with "Hγ● Hγ◯") as "[$$]".
    { by apply excl_auth_update. }
    done.
  Qed.
End lemmas.


Section race.
  Context `{!conerisGS Σ, !spawnG Σ, c:!lazy_rand 1, !inG Σ (excl_authR boolO) }.

  
  Definition race_prog : expr :=
  let: "r" := init_lazy_rand #() in
  ( lazy_read_rand "r" (allocate_tape #()) #0)
  |||
  ( lazy_read_rand "r" (allocate_tape #()) #1).

  Lemma race_prog_spec:
  {{{ ↯ (1/2) }}}
    race_prog
    {{{ (n:nat), RET ((#n,#n),(#n,#n))%Z; ⌜n<=1⌝ }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    rewrite /race_prog.
    iMod (ghost_var_alloc false) as (γ) "[Hauth Hfrag]".
    wp_apply (lazy_rand_init (nroot.@"1") (λ x,  ⌜x = None⌝ ∗ own γ (◯E false) ∨
                                                ∃ x1, ⌜x=Some (x1, x1)⌝ ∗ (own γ (◯E true)))%I
                                                
               with "[Hfrag]").
    { iLeft. iFrame. done. }
    iIntros (?) "(%&%&%&#Hinv)".
    iMod (inv_alloc (nroot.@"inv") _ (own γ (●E false) ∗ ↯ (1/2)∨ own γ (●E true))%I with "[Herr Hauth ]") as "#Hinv2".
    { iLeft. iFrame. }
    wp_pures.
    wp_apply (wp_par (λ res, ∃ (n:nat), ⌜(#n, #n)%V = res⌝ ∗ rand_frag n n _)%I
                (λ res, ∃ (n:nat), ⌜(#n, #n)%V = res⌝ ∗ rand_frag n n _)%I with "[][]").
    - wp_apply (lazy_rand_alloc_tape _ _ ).
      { iSplit; last by iIntros. done. }
      iIntros (α) "[Ht _]".
      replace #0 with (# (Z.of_nat 0)) by done.
      wp_apply (lazy_rand_spec _ _ _ _ _ _ (λ x y, ⌜x=y⌝ ∗ rand_frag x x _)%I (λ x y, ⌜x=y⌝ ∗ rand_frag x x _)%I with "[-]").
      + iSplit; first done.
        simpl. iIntros (n m) "H1 Hauth Htauth".
        iApply (state_update_inv_acc with "Hinv2").
        { apply subseteq_difference_r; last done.
          by apply ndot_preserve_disjoint_r, ndot_ne_disjoint.
        }
        iIntros ">[[H2 Herr]|H2]"; iDestruct "H1" as "[(->&?)|(%&->&?)]"; iDestruct (ghost_var_agree with "[$][$]") as "%"; simplify_eq.
        * iMod (rand_tape_presample _ _ _ _ _ _ _ _ _ _ (λ x, if bool_decide (fin_to_nat x = 0%nat) then 0 else 1) with "[$][$][$][$]") as "(%n&?&?&?)".
          { apply subseteq_difference_r.
            - by apply ndot_preserve_disjoint_l, ndot_ne_disjoint.
            - apply subseteq_difference_r; last done.
              by apply ndot_ne_disjoint.
          }
          { intros. case_bool_decide; simpl; lra. }
          { rewrite SeriesC_finite_foldr/=. lra. }
          iAssert (⌜fin_to_nat n=0%nat⌝)%I as "%Heq".
          { case_bool_decide; first done. iDestruct (ec_contradict with "[$]") as "[]".
            simpl. lra. }
          rewrite bool_decide_eq_true_2; last done.
          iFrame.
          iMod (ghost_var_update with "[$][$]") as "[H1 H2]".
          iFrame.
          iModIntro.
          iIntros. iSplitR "H1"; last first.
          { by iRight. }
          iMod (rand_auth_update (0,_) with "[$]") as "?".
          { simpl. lia. }
          iDestruct (rand_auth_duplicate with "[$]") as "#?".
          rewrite Heq. iFrame. iIntros. 
          iModIntro. simpl. repeat iSplit; try done.
          iRight. iFrame. iExists _. done. 
        * iDestruct (rand_auth_duplicate with "[$]") as "#?".
          iFrame. iModIntro.
          repeat iSplit; try done.
          iRight. iFrame. by iExists _.
      + by iIntros (??) "[(->&#$)|(->&#$)]".
    - wp_apply (lazy_rand_alloc_tape _ _ ).
      { iSplit; last by iIntros. done. }
      iIntros (α) "[Ht _]".
      replace #1 with (# (Z.of_nat 1)) by done.
      wp_apply (lazy_rand_spec _ _ _ _ _ _ (λ x y, ⌜x=y⌝ ∗ rand_frag x x _)%I (λ x y, ⌜x=y⌝ ∗ rand_frag x x _)%I with "[-]").
      + iSplit; first done.
        simpl. iIntros (n m) "H1 Hauth Htauth".
        iApply (state_update_inv_acc with "Hinv2").
        { apply subseteq_difference_r; last done.
          by apply ndot_preserve_disjoint_r, ndot_ne_disjoint.
        }
        iIntros ">[[H2 Herr]|H2]"; iDestruct "H1" as "[(->&?)|(%&->&?)]"; iDestruct (ghost_var_agree with "[$][$]") as "%"; simplify_eq.
        * iMod (rand_tape_presample _ _ _ _ _ _ _ _ _ _ (λ x, if bool_decide (fin_to_nat x = 1%nat) then 0 else 1) with "[$][$][$][$]") as "(%n&?&?&?)".
          { apply subseteq_difference_r.
            - by apply ndot_preserve_disjoint_l, ndot_ne_disjoint.
            - apply subseteq_difference_r; last done.
              by apply ndot_ne_disjoint.
          }
          { intros. case_bool_decide; simpl; lra. }
          { rewrite SeriesC_finite_foldr/=. lra. }
          iAssert (⌜fin_to_nat n=1%nat⌝)%I as "%Heq".
          { case_bool_decide; first done. iDestruct (ec_contradict with "[$]") as "[]".
            simpl. lra. }
          rewrite bool_decide_eq_true_2; last done.
          iFrame.
          iMod (ghost_var_update with "[$][$]") as "[H1 H2]".
          iFrame.
          iModIntro.
          iIntros. iSplitR "H1"; last first.
          { by iRight. }
          iMod (rand_auth_update (1,_) with "[$]") as "?".
          { simpl. lia. }
          iDestruct (rand_auth_duplicate with "[$]") as "#?".
          rewrite Heq. iFrame. iIntros. 
          iModIntro. simpl. repeat iSplit; try done.
          iRight. iFrame. iExists _. done. 
        * iDestruct (rand_auth_duplicate with "[$]") as "#?".
          iFrame. iModIntro.
          repeat iSplit; try done.
          iRight. iFrame. by iExists _.
      + by iIntros (??) "[(->&#$)|(->&#$)]". 
    - iIntros (??) "[(%&<-&?) (%&<-&?)]".
      iDestruct (rand_frag_frag_agree with "[$][$]") as "[% %]".
      simplify_eq.
      iApply "HΦ".
      iNext.
      iDestruct (rand_frag_valid with "[$]") as "%".
      done.
  Qed.
      
  
End race.
