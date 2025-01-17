From iris.algebra Require Import excl_auth cmra.
From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris par spawn.
From clutch.coneris.examples Require Import random_counter2.random_counter.

Local Open Scope Z.

Set Default Proof Using "Type*".

Inductive T : Type :=
| S0 :T
| S1: forall (n:nat), T.

Definition sampled s :=
  match s with
  | S0 => None
  | S1 n => Some n
  end.

Definition one_positive n1 n2:=
  bool_decide (∃ (n:nat), (n > 0)%nat /\ (sampled n1 = Some n \/ sampled n2 = Some n)).

Canonical Structure TO := leibnizO T.

Section lemmas.
  Context `{!inG Σ (excl_authR TO)}.

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

Section client.
  Context `{rc:random_counter} {L: counterG Σ}.
  Definition con_prog : expr :=
    let: "c" := new_counter #() in
    ((incr_counter "c") |||
    incr_counter "c" 
    ) ;;
    read_counter "c"
  .

  Definition counter_nroot:=nroot.@"counter".
  Definition inv_nroot:=nroot.@"inv".
  
  Context `{!spawnG Σ, !inG Σ (excl_authR TO)}.

  Definition con_prog_inv (γ1 γ2: gname): iProp Σ :=
    ∃ (n1 n2 : T) ,
      let p:= one_positive n1 n2 in
      own γ1 (●E n1) ∗ own γ2 (●E n2) ∗
      if p
      then ↯ 0%R
      else
        ∃ (flip_num:nat),
          ↯ (Rpower 4%R (INR flip_num-2))%R ∗
          ⌜(flip_num = bool_to_nat (bool_decide (sampled n1=Some 0%nat)) +bool_to_nat (bool_decide (sampled n2=Some 0%nat)))%nat⌝.

  Lemma Rpower_4_2: (Rpower 4 2 = 16)%R.
  Proof.
    replace 2%R with (1+1)%R by lra.
    rewrite Rpower_plus Rpower_1; lra.
  Qed.
  
  Lemma con_prog_spec:
    {{{ ↯ (1/16) }}}
      con_prog
      {{{ (n:nat), RET #n; ⌜(0<n)%nat⌝ }}}.
  Proof.
    iIntros (Φ) "Hε HΦ".
    rewrite /con_prog.
    wp_apply (new_counter_spec (L:=L) _ counter_nroot with "[//]") as (c) "(%γ & #Hcounter & Hfrag)".
    replace (1)%Qp with (1/2+1/2)%Qp; last compute_done.
    replace 0%nat with (0+0)%nat by lia.
    rewrite -(counter_content_frag_combine).
    iDestruct "Hfrag" as "[Hc1 Hc2]".
    wp_pures.
    iMod (ghost_var_alloc S0) as (γ1) "[Hauth1 Hfrag1]".
    iMod (ghost_var_alloc S0) as (γ2) "[Hauth2 Hfrag2]".
    iMod (inv_alloc inv_nroot _ (con_prog_inv γ1 γ2) with "[Hauth1 Hauth2 Hε]") as "#Hinv".
    { iModIntro. iFrame.
      rewrite /one_positive. rewrite bool_decide_eq_false_2.
      - iExists _. iSplit; last done.
        simpl. replace (0-2)%R with (-2)%R by lra.
        rewrite Rpower_Ropp Rpower_4_2.
        iApply (ec_eq with "[$]").
        lra.
      - intros (?&?&[|]); simpl in *; simplify_eq; lia.
    }
    wp_apply (wp_par (λ _, ∃ (n:nat), own γ1 (◯E (S1 n)) ∗ counter_content_frag γ (1/2) n)%I
                (λ _, ∃ (n:nat), own γ2 (◯E (S1 n)) ∗ counter_content_frag γ (1/2) n)%I with "[Hfrag1 Hc1][Hfrag2 Hc2]").
    - wp_apply (incr_counter_spec _ _ _ _ (λ _ _, ∃ n : nat, own γ1 (◯E (S1 n)) ∗ counter_content_frag γ (1 / 2) n )%I with "[$Hcounter Hfrag1 Hc1]"); [done| |by iIntros].
      iIntros (α) "Htape".
      iApply (state_update_inv_acc with "[$]"); first done.
      iIntros ">(%n1 & %n2 & Hauth1 & Hauth2 & Herr)".
      iDestruct (ghost_var_agree with "[$Hauth1][$]") as "->".
      case_match eqn:H.
      + iMod (counter_tapes_presample _ _ _ _ _ _  (λ _, 0%R) with "[$][$][$]") as "(%n & Herr & Htape)".
        *  apply namespaces.coPset_subseteq_difference_r; last done.
           by apply ndot_ne_disjoint.
        * done.
        *  rewrite SeriesC_0; intros; lra.
        * iMod (ghost_var_update _ (S1 (fin_to_nat n)) with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
          simpl. iFrame.
          iModIntro.
          iSplitR "Herr"; last first.
          -- case_match eqn:H1; first done.
             rewrite /one_positive in H H1.
             apply bool_decide_eq_true_1 in H.
             apply bool_decide_eq_false_1 in H1.
             exfalso. apply H1. naive_solver.
          -- iIntros (z) "Hauth1".
             iMod (counter_content_update with "[$][$]") as "[$ ?]".
             by iFrame.
      + iDestruct "Herr" as "(%&Herr&->)/=".
        iMod (counter_tapes_presample _ _ _ _ _ _ (λ x, if 0<? fin_to_nat x then 0%R else (Rpower 4 (1+(bool_to_nat (bool_decide (sampled n2 = Some 0%nat)) - 2))))%R with "[$][$][$]") as "(%n & Herr & Htape)".
        * apply namespaces.coPset_subseteq_difference_r; last done.
          by apply ndot_ne_disjoint.
        * intros. case_match; first done. rewrite /Rpower. left. apply exp_pos.
        * rewrite SeriesC_finite_foldr/=.
          rewrite Rpower_plus Rpower_1; lra.
        * iMod (ghost_var_update _ (S1 (fin_to_nat n)) with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
          simpl. iFrame.
          iModIntro.
          iSplitR "Herr"; last first.
          -- case_match eqn:H0.
             ++ case_match eqn:H1; first done.
                rewrite /one_positive in H1.
                apply bool_decide_eq_false_1 in H1.
                exfalso.
                apply H1. eexists _; split; last by left.
                lia.
             ++ case_match eqn:H1.
                { rewrite /one_positive in H H1.
                  apply bool_decide_eq_false_1 in H.
                  apply bool_decide_eq_true_1 in H1.
                  exfalso. apply H.
                  destruct H1 as (?&?&[|]); last naive_solver.
                  simpl in *. simplify_eq. lia. }
                iExists _. iSplit; last done.
                iApply (ec_eq with "[$]").
                f_equal.
                rewrite plus_INR. 
                assert (fin_to_nat n = 0)%nat as ->; simpl; last lra.
                apply Z.ltb_ge in H0. lia.
          -- iIntros (z) "Hauth".
             iMod (counter_content_update with "[$][$]") as "[$ ?]".
             by iFrame.
    - wp_apply (incr_counter_spec _ _ _ _ (λ _ _, ∃ n : nat, own γ2 (◯E (S1 n)) ∗ counter_content_frag γ (1 / 2) n )%I with "[$Hcounter Hfrag2 Hc2]"); [done| |by iIntros].
      iIntros (α) "Htape".
      iApply (state_update_inv_acc with "[$]"); first done.
      iIntros ">(%n1 & %n2 & Hauth1 & Hauth2 & Herr)".
      iDestruct (ghost_var_agree with "[$Hauth2][$]") as "->".
      case_match eqn:H.
      + iMod (counter_tapes_presample _ _ _ _ _ _  (λ _, 0%R) with "[$][$][$]") as "(%n & Herr & Htape)".
        *  apply namespaces.coPset_subseteq_difference_r; last done.
           by apply ndot_ne_disjoint.
        * done.
        *  rewrite SeriesC_0; intros; lra.
        * iMod (ghost_var_update _ (S1 (fin_to_nat n)) with "[$Hauth2][$]") as "[Hauth2 Hfrag2]".
          simpl. iFrame.
          iModIntro.
          iSplitR "Herr"; last first.
          -- case_match eqn:H1; first done.
             rewrite /one_positive in H H1.
             apply bool_decide_eq_true_1 in H.
             apply bool_decide_eq_false_1 in H1.
             exfalso. naive_solver.
          -- iIntros (z) "Hauth1".
             iMod (counter_content_update with "[$][$]") as "[$ ?]".
             by iFrame.
      + iDestruct "Herr" as "(%&Herr&->)/=".
        iMod (counter_tapes_presample _ _ _ _ _ _ (λ x, if 0<? fin_to_nat x then 0%R else (Rpower 4 (1+((bool_to_nat (bool_decide (sampled n1 = Some 0)) + 0)%nat - 2))))%R with "[$][$][$]") as "(%n & Herr & Htape)".
        * apply namespaces.coPset_subseteq_difference_r; last done.
          by apply ndot_ne_disjoint.
        * intros. case_match; first done. rewrite /Rpower. left. apply exp_pos.
        * rewrite SeriesC_finite_foldr/=.
          rewrite Rpower_plus Rpower_1/=; lra.
        * iMod (ghost_var_update _ (S1 (fin_to_nat n)) with "[$Hauth2][$]") as "[Hauth2 Hfrag2]".
          simpl. iFrame.
          iModIntro.
          iSplitR "Herr"; last first.
          -- case_match eqn:H0.
             ++ case_match eqn:H1; first done.
                rewrite /one_positive in H1.
                apply bool_decide_eq_false_1 in H1.
                exfalso.
                apply H1. eexists _. split; last by right. lia.
             ++ case_match.
                { rewrite /one_positive in H H1.
                  apply bool_decide_eq_false_1 in H.
                  apply bool_decide_eq_true_1 in H1.
                  exfalso. apply H.
                  destruct H1 as (?&?&[|]); first naive_solver.
                  simpl in *. simplify_eq. lia. }
                iExists _. iSplit; last done.
                iApply (ec_eq with "[$]").
                f_equal.
                rewrite !plus_INR. 
                assert (fin_to_nat n = 0)%nat as ->; simpl; last lra.
                apply Z.ltb_ge in H0. lia. 
          -- iIntros (z) "Hauth".
             iMod (counter_content_update with "[$][$]") as "[$ ?]".
             by iFrame.
    - iIntros (??) "[(%n1 & Hfrag1 & Hc1)(%n2 & Hfrag2 & Hc2)]".
      iNext. wp_pures.
      iCombine "Hc1 Hc2" as "Hc".
      rewrite counter_content_frag_combine.
      replace (1/2+1/2)%Qp with 1%Qp; last compute_done.
      iAssert (|={⊤}=> ⌜(n1+n2>0)%nat⌝)%I with "[Hfrag1 Hfrag2]" as ">%".
      { iInv "Hinv" as ">(%&%&Hauth1&Hauth2&Herr)".
        iDestruct (ghost_var_agree with "[$Hauth1][$]") as "->".
        iDestruct (ghost_var_agree with "[$Hauth2][$]") as "->".
        rewrite /con_prog_inv.
        destruct n1, n2 as [|]; [simpl|simpl; iModIntro; iFrame; iSplitL "Herr"; iModIntro; try (iPureIntro; lia); done..]; last first.
        rewrite /one_positive. rewrite bool_decide_eq_false_2; last first.
        { intros (?&?&[|]); simpl in *; simplify_eq; lia. }
        iDestruct "Herr" as "(%&Herr&->)".
        simpl. replace (_+_-_)%R with 0%R by lra.
        rewrite Rpower_O; last lra.
        by iDestruct (ec_contradict with "[$]") as "[]".
      }
      wp_apply (read_counter_spec _ _ _ _ (λ n, ⌜(n>0)%nat⌝)%I with "[$Hcounter Hc]"); first done.
      { iIntros.
        iDestruct (counter_content_agree with "[$][$]") as "<-".
        iFrame. iModIntro. iPureIntro. lia.
      }
      iIntros.
      iApply "HΦ".
      iPureIntro; lia.
  Qed.
  
End client.
