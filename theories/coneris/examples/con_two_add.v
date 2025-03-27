From iris.algebra Require Import excl_auth cmra.
From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris par spawn.

Local Open Scope Z.

Set Default Proof Using "Type*".

Section lemmas'.
  Context `{!inG Σ (excl_authR (boolO))}.

  (* Helpful lemmas *)
  Lemma ghost_var_alloc' b :
    ⊢ |==> ∃ γ, own γ (●E b) ∗ own γ (◯E b).
  Proof.
    iMod (own_alloc (●E b ⋅ ◯E b)) as (γ) "[??]".
    - by apply excl_auth_valid.
    - by eauto with iFrame.
  Qed.

  Lemma ghost_var_agree' γ b c :
    own γ (●E b) -∗ own γ (◯E c) -∗ ⌜ b = c ⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    by iCombine "Hγ● Hγ◯" gives %->%excl_auth_agree_L.
  Qed.

  Lemma ghost_var_update' γ b' b c :
    own γ (●E b) -∗ own γ (◯E c) ==∗ own γ (●E b') ∗ own γ (◯E b').
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E b' ⋅ ◯E b') with "Hγ● Hγ◯") as "[$$]".
    { by apply excl_auth_update. }
    done.
  Qed.
End lemmas'.


(** * This is the con_two_add example in the paper of Coneris*)
Definition two_add_prog' : expr :=
  let: "l" := ref #0 in
  ((FAA "l" (rand #3))
   |||
   (FAA "l" (rand #3)));;
  !"l".


(** * This is the proof sketched for the example con_two_add in the paper of Coneris.

   This is **not** the most idiomatic/direct way to encode this proof, but it is structured to match
   the simplified layout of the text to avoid pulling in too many high level Iris ideas *)

(* Each thread moves through a state machine with 3 states:

   S0 --> initial state
   S1 n --> sampled n
   S2 n --> sampled and added n

*)

Inductive T : Type :=
| S0 : T
| S1 (n : nat) : T
| S2 (n : nat) : T.

Definition no_thread_added t1 t2 :=
  match t1, t2 with
  | S2 _, _ => False
  | _, S2 _ => False
  | _, _ => True
  end.

Definition one_thread_added t1 t2 n :=
  match t1, t2 with
  | S2 _, S2 _ => False
  | S2 n', _ => n = n'
  | _, S2 n' => n = n'
  | _, _ => False
  end.

Definition both_threads_added t1 t2 n :=
  match t1, t2 with
  | S2 n1, S2 n2 => n = n1 + n2
  | _, _ => False
  end.

Definition no_thread_sampled t1 t2 :=
  match t1, t2 with
  | S0, S0 => True
  | _, _ => False
  end.
  
Definition one_thread_sampled_zero t1 t2 :=
  match t1, t2 with
  | S1 0, S0 => True
  | S2 0, S0 => True
  | S0, S1 0 => True
  | S0, S2 0 => True
  | _, _ => False
  end.

Definition at_least_one_thread_sampled_non_zero t1 t2 :=
  (match t1 with
   | S0 => False
   | S1 n => n > 0 
   | S2 n => n > 0
   end) ∨
  (match t2 with
   | S0 => False
   | S1 n => n > 0 
   | S2 n => n > 0
  end).
    
Canonical Structure TO := leibnizO T.

Section lemmasT.
  Context `{!inG Σ (excl_authR TO)}.

  Lemma ghost_var_allocT b :
    ⊢ |==> ∃ γ, own γ (●E b) ∗ own γ (◯E b).
  Proof.
    iMod (own_alloc (●E b ⋅ ◯E b)) as (γ) "[??]".
    - by apply excl_auth_valid.
    - by eauto with iFrame.
  Qed.

  Lemma ghost_var_agreeT γ b c :
    own γ (●E b) -∗ own γ (◯E c) -∗ ⌜ b = c ⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    by iCombine "Hγ● Hγ◯" gives %->%excl_auth_agree_L.
  Qed.

  Lemma ghost_var_updateT γ b' b c :
    own γ (●E b) -∗ own γ (◯E c) ==∗ own γ (●E b') ∗ own γ (◯E b').
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E b' ⋅ ◯E b') with "Hγ● Hγ◯") as "[$$]".
    { by apply excl_auth_update. }
    done.
  Qed.
End lemmasT.

Section complex'.
  Context `{!conerisGS Σ, !spawnG Σ, !inG Σ (excl_authR TO)}.

  Definition parallel_add_inv' (γ1 γ2: gname) l: iProp Σ :=
    (* The first line is ghost state omitted from the paper discussion *)
    ∃ (s1 s2 : T), own γ1 (●E s1) ∗ own γ2 (●E s2) ∗
      (((l ↦ #0 ∗ ⌜ no_thread_added s1 s2 ⌝) ∨
         (∃ n : nat, l ↦ #n ∗ ⌜ one_thread_added s1 s2 n ⌝) ∨
         (∃ n : nat, l ↦ #n ∗ ⌜ n > 0 ⌝ ∗ ⌜ both_threads_added s1 s2 n ⌝)) ∗
       ((↯(1/16) ∗ ⌜ no_thread_sampled s1 s2 ⌝) ∨
         (↯(1/4) ∗ ⌜ one_thread_sampled_zero s1 s2 ⌝) ∨
         (↯(1) (* both_thread_sampled_zero *)) ∨
         (↯(0) ∗ ⌜ at_least_one_thread_sampled_non_zero s1 s2 ⌝))).

  Lemma parallel_add_inv'_symmetric γ1 γ2 l :
    parallel_add_inv' γ1 γ2 l -∗
    parallel_add_inv' γ2 γ1 l.
  Proof.
    rewrite /parallel_add_inv'.
    iDestruct 1 as "(%s1&%s2&Hauth1&Hauth2&Hstate&Hsamp)".
    iExists s2, s1.
    iFrame.
    iSplitL "Hstate".
    { 
      iDestruct "Hstate" as "[H1|[H2|H3]]".
      { iLeft.  destruct s1, s2; naive_solver. }
      { iRight. iLeft. destruct s1, s2; naive_solver. }
      { iRight. iRight. rewrite /both_threads_added.
        iDestruct "H3" as "(%n&$&$&%Hp)"; iPureIntro; destruct s1, s2; try naive_solver; lia. }
    }
    { 
      iDestruct "Hsamp" as "[H1|[H2|[H3|H4]]]".
      { iLeft.  destruct s1, s2; naive_solver. }
      { iRight. iLeft. destruct s1 as [|n1|n1]; destruct s2 as [|n2|n2]; try destruct n1, n2; naive_solver. }
      { by iFrame. }
      { iRight. iRight. iRight.
        rewrite /at_least_one_thread_sampled_non_zero.
        iDestruct "H4" as "($&[H1|H2])".
        * iRight; auto.
        * iLeft; auto.
      }
    }
  Qed.
  
  Lemma rand_step γ1 γ2 l:
    {{{ inv nroot (parallel_add_inv' γ1 γ2 l) ∗ own γ1 (◯E S0) }}}
      rand #3
      {{{ (n: nat), RET #n; own γ1 (◯E (S1 n)) }}}.
  Proof.
    iIntros (Φ) "(#I&Hfrag1) HΦ".
    iInv "I" as ">(%s1&%s2&Hauth1&Hauth2&Hstate&Hsamp)".
    iDestruct (ghost_var_agreeT with "[$Hauth1][$]") as "->".
    iDestruct "Hsamp" as "[Hnosamp|[Hone0|[Hbogus|Honenonzero]]]".
    + iDestruct "Hnosamp" as "(Herr&%Hpure)".
      destruct s2; try inv Hpure; [].
      wp_apply (wp_couple_rand_adv_comp1' _ _ _ _
                  (λ x, if bool_decide(fin_to_nat x = 0)%nat
                        then 1/4
                        else 0)%R with "[$]") as (x) "Herr".
      { intros. case_match; last done. lra. }
      { rewrite SeriesC_finite_foldr. simpl. lra. }
      iMod (ghost_var_updateT _ (S1 (fin_to_nat x)) with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
      iModIntro.
      iSplitL "Hauth1 Hauth2 Hstate Herr".
      { iNext. iExists _, _.  iFrame "Hauth1 Hauth2 Hstate". 
        case_bool_decide as Hcase.
        * iRight. iLeft; iFrame. rewrite Hcase. by eauto.
        * iRight. iRight. iRight. iFrame. iPureIntro. rewrite /at_least_one_thread_sampled_non_zero. lia.
      }
      by iApply "HΦ".
    + iDestruct "Hone0" as "(Herr&%Hpure)".
      wp_apply (wp_couple_rand_adv_comp1' _ _ _ _
                  (λ x, if bool_decide(fin_to_nat x = 0)%nat
                        then 1
                        else 0)%R with "[$]") as (x) "Herr".
      { intros. case_match; last done. lra. }
      { rewrite SeriesC_finite_foldr. simpl. lra. }
      iMod (ghost_var_updateT _ (S1 (fin_to_nat x)) with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
      iModIntro.
      iSplitL "Hauth1 Hauth2 Hstate Herr".
      { iNext. iExists _, _.  iFrame "Hauth1 Hauth2 Hstate". 
        case_bool_decide as Hcase.
        * iFrame. 
        * iRight. iRight. iRight. iFrame. iPureIntro. rewrite /at_least_one_thread_sampled_non_zero. lia.
      }
      by iApply "HΦ".
    + iDestruct (ec_contradict with "Hbogus") as "[]". lra. 
    + wp_apply (wp_rand with "[//]") as (x) "_".
      iMod (ghost_var_updateT _ (S1 (fin_to_nat x)) with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
      iModIntro.
      iSplitL "Hauth1 Hauth2 Hstate Honenonzero".
      { iNext. iExists _, _.  iFrame "Hauth1 Hauth2 Hstate".
        iDestruct "Honenonzero" as "(Hz&%Hp)".
        iRight. iRight. iRight. iFrame. iPureIntro.
        rewrite /at_least_one_thread_sampled_non_zero in Hp *.
        destruct s2; try lia.
      }
      by iApply "HΦ".
  Qed.
  
  Lemma faa_step γ1 γ2 l (n: nat) :
    {{{ inv nroot (parallel_add_inv' γ1 γ2 l) ∗ own γ1 (◯E (S1 n)) }}}
      FAA #l #n
    {{{ (v : val), RET v; own γ1 (◯E (S2 n)) }}}.
  Proof.
    iIntros (Φ) "(#I&Hfrag1) HΦ".
    iInv "I" as ">(%s1&%s2&Hauth1&Hauth2&Hstate&Hsamp)".
    iDestruct (ghost_var_agreeT with "[$Hauth1][$]") as "->".
    iDestruct "Hstate" as "[Hnone|[Hone|Htwo]]".
    * iDestruct "Hnone" as "(Hl&%Hcase)".
      wp_faa.
      iEval (simpl) in "Hl".
      iMod (ghost_var_updateT _ (S2 n) with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
      iModIntro.
      iSplitL "Hauth1 Hauth2 Hsamp Hl".
      { iNext. iExists _, _.  iFrame "Hauth1 Hauth2".
        iSplitL "Hl".
        { iRight. iLeft. iExists _. iFrame. iPureIntro. rewrite /one_thread_added. destruct s2;
            try inv Hcase; lia. }
        { iDestruct "Hsamp" as "[(Hnosamp&%Hp)|[(Hone0&%Hp)|[Hbogus|(Honenonzero&%Hp)]]]".
          + inversion Hp.
          + iRight. iLeft. iFrame. iPureIntro.
            destruct s2; simpl in Hp; simpl; try lia; auto.
          + iFrame; by eauto.
          + iFrame; by eauto.
        }
      }
      by iApply "HΦ".
    * iDestruct "Hone" as (n') "(Hl&%Hcase)".
      wp_faa.
      iEval (simpl) in "Hl".
      iMod (ghost_var_updateT _ (S2 n) with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
      destruct s2 as [| |n0]; try inversion Hcase.
      subst.
      iAssert (⌜at_least_one_thread_sampled_non_zero (S2 n) (S2 n0)⌝)%I as %Hatleast.
      { iDestruct "Hsamp" as "[(?&%Hp)|[(?&%Hp)|[H1|(?&%Hp)]]]".
        * inversion Hp.
        * rewrite //= in Hp; destruct n; auto.
        * iDestruct (ec_contradict with "[$]") as %[]. lra.
        * eauto.
      }
      iMod (ec_zero) as "Hzero".
      iMod (ghost_var_updateT _ (S2 n) with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
      iModIntro.
      iSplitL "Hauth1 Hauth2 Hsamp Hl Hzero".
      { iNext. iExists _, _.  iFrame "Hauth1 Hauth2".
        iSplitL "Hl".
        { iRight. iRight.
          rewrite -Nat2Z.inj_add.
          iExists _. iFrame. iPureIntro.
          rewrite /at_least_one_thread_sampled_non_zero in Hatleast. split; rewrite //=; lia.
        }
        iRight. iRight. iRight.
        iFrame. eauto.
      }
      by iApply "HΦ".
    * iDestruct "Htwo" as (?) "(?&?&%Hp)".
      inversion Hp.
  Qed.
  
  Lemma complex_parallel_add_spec':
    {{{ ↯ (1/16) }}}
      two_add_prog'
      {{{ (n:nat), RET #n; ⌜(0<n)%nat⌝ }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    iMod (ghost_var_allocT S0) as (γ1) "[Hauth1 Hfrag1]".
    iMod (ghost_var_allocT S0) as (γ2) "[Hauth2 Hfrag2]".
    rewrite /two_add_prog'.
    wp_alloc l as "Hl".
    wp_pures.
    iMod (inv_alloc nroot _ (parallel_add_inv' γ1 γ2 l) with "[Hauth1 Hauth2 Herr Hl]") as "#I".
    { iNext.
      replace #0 with #(Z.of_nat 0) by eauto.
      iFrame.
      iSplit.
      { iPureIntro. left. by eauto. }
      { iLeft. iFrame. }
    }
    wp_apply (wp_par (λ _, ∃ (n:nat), own γ1 (◯E (S2 n)))%I
                (λ _, ∃ (n:nat), own γ2 (◯E (S2 n)))%I with "[Hfrag1][Hfrag2]").
    - wp_apply (rand_step with "[$]"). 
      iIntros (n) "Hfrag1".
      wp_apply (faa_step with "[$]").
      iIntros (?) "Hfrag1".
      iExists _; iFrame.
    - iAssert (inv nroot (parallel_add_inv' γ2 γ1 l))%I as "I'".
      { iApply inv_iff; first by iApply "I".
        iNext. iModIntro. iSplit; iIntros "H"; by iApply parallel_add_inv'_symmetric.
      }
      iClear "I".
      wp_apply (rand_step with "[$]"). 
      iIntros (n) "Hfrag1".
      wp_apply (faa_step with "[$]").
      iIntros (?) "Hfrag1".
      iExists _; iFrame.
    - iIntros (??) "((%n1&H1)&(%n2&H2))".
      iNext. wp_pures.
      iInv "I" as ">(%s1&%s2&Hauth1&Hauth2&Hstate&Hsamp)".
      iDestruct (ghost_var_agreeT with "[$Hauth1][$]") as "->".
      iDestruct (ghost_var_agreeT with "[$Hauth2][$]") as "->".
      iDestruct "Hstate" as "[(?&%Hp)|[(%n&?&%Hp)|Htwo]]".
      { naive_solver. }
      { naive_solver. }
      iDestruct "Htwo" as "(%n&Hl&%Hgt0&%Hp)".
      wp_load.
      iModIntro. iSplitL "Hauth1 Hauth2 Hl Hsamp".
      { iNext. iExists _, _; iFrame. iRight; iRight. iExists _; by iFrame. }
      iApply "HΦ". iPureIntro. lia.
  Qed.
  
End complex'.
