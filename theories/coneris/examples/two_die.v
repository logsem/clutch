From iris.algebra Require Import excl_auth cmra.
From iris.base_logic.lib Require Import invariants.
From coneris.coneris Require Import coneris par spawn.

Local Open Scope Z.

Set Default Proof Using "Type*".

Section lemmas.
  Context `{!inG Σ (excl_authR (option natO))}.

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

Definition two_die_prog : expr :=
  let, ("v1", "v2") := ((rand #5) ||| rand #5) in
  "v1" + "v2".

Section simple.
  Context `{!conerisGS Σ, !spawnG Σ}.
  Lemma simple_parallel_add_spec:
    {{{ ↯ (1/6) }}}
      two_die_prog
      {{{ (n:nat), RET #n; ⌜(0<n)%nat⌝ }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    rewrite /two_die_prog.
    wp_pures.
    wp_apply (wp_par (λ x, ∃ (n:nat), ⌜x=#n⌝ ∗ ⌜(0<n)%nat⌝)%I
                (λ x, ∃ (n:nat), ⌜x=#n⌝ ∗ ⌜(0<=n)%nat⌝)%I with "[Herr][]").
    - wp_apply (wp_rand_err_nat _ _ 0%nat).
      iSplitL.
      { iApply (ec_eq with "[$]"). simpl. lra. }
      iIntros (??).
      iPureIntro. simpl. eexists _; split; first done.
      lia.
    - wp_apply (wp_rand); first done.
      iIntros (??).
      iPureIntro. simpl. eexists _; split; first done.
      lia.
    - iIntros (??) "[(%&->&%)(%&->&%)]".
      iNext.
      wp_pures.
      iModIntro.
      rewrite -Nat2Z.inj_add. iApply "HΦ".
      iPureIntro. lia.
  Qed.
End simple.

Section complex.
  Context `{!conerisGS Σ, !spawnG Σ, !inG Σ (excl_authR (option natO))}.
  
  Definition parallel_add_inv (γ1 γ2 : gname) : iProp Σ :=
    ∃ (n1 n2 : option nat) ,
      own γ1 (●E n1) ∗ own γ2 (●E n2) ∗
      if bool_decide ((∃ x, n1 = Some x /\ (0<x)%nat)\/ (∃ x, n2 = Some x /\ (0<x)%nat))
      then ↯ 0%R
      else
        ∃ (flip_num:nat),
          ↯ (Rpower 6%R (INR flip_num-2))%R ∗
                                             ⌜(flip_num = bool_to_nat (bool_decide (n1=Some 0%nat)) +bool_to_nat (bool_decide (n2=Some 0%nat)))%nat⌝.
  
  Lemma complex_parallel_add_spec:
    {{{ ↯ (1/36) }}}
      two_die_prog
      {{{ (n:nat), RET #n; ⌜(0<n)%nat⌝ }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    iMod (ghost_var_alloc None) as (γ1) "[Hauth1 Hfrag1]".
    iMod (ghost_var_alloc None) as (γ2) "[Hauth2 Hfrag2]".
    iMod (inv_alloc nroot _ (parallel_add_inv γ1 γ2) with "[Hauth1 Hauth2 Herr]") as "#I".
    - iNext.
      iFrame.
      rewrite bool_decide_eq_false_2.
      + iExists _. iSplit; last done. simpl.
        iApply (ec_eq with "[$]").
        replace (0-2)%R with (-2)%R by lra.
        rewrite Rpower_Ropp.
        rewrite Rdiv_1_l; f_equal.
        rewrite /Rpower.
        erewrite <-(exp_ln _); last lra.
        f_equal.
        replace (IPR 2) with (INR 2); last first.
        { by rewrite -INR_IPR. }
        erewrite <-ln_pow; [|lra].
        f_equal. lra.
      + intros [(?&?&?)|(?&?&?)]; simplify_eq.
    - rewrite /two_die_prog.
      wp_pures.
      wp_apply (wp_par (λ x, ∃ (n:nat), ⌜x = #n ⌝ ∗ own γ1 (◯E (Some n)))%I
                  (λ x, ∃ (n:nat), ⌜x = #n ⌝ ∗ own γ2 (◯E (Some n)))%I with "[Hfrag1][Hfrag2]").
      + iInv "I" as ">(%&%&Hauth1&Hauth2&Herr)" "Hclose".
        iDestruct (ghost_var_agree with "[$Hauth1][$]") as "->".
        case_bool_decide as H.
        * wp_apply wp_rand; first done.
          iIntros (n) "_".
          iMod (ghost_var_update _ (Some (fin_to_nat n)) with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
          iMod ("Hclose" with "[$Hauth1 $Hauth2 Herr ]"); last by iFrame.
          iNext. rewrite bool_decide_eq_true_2; first done.
          right.
          by destruct H as [(?&?&?)|].
        * iDestruct "Herr" as "(%&Herr&->)".
          rewrite bool_decide_eq_false_2; last done.
          simpl.
          wp_apply (wp_couple_rand_adv_comp1' _ _ _ _
                      (λ x, if bool_decide (fin_to_nat x = 0)%nat
                            then (Rpower 6 (bool_to_nat (bool_decide (n2 = Some 0%nat)) - 2 + 1))%R
                            else 0%R
                      ) with "[$]") as (n) "Herr".
          -- intros. case_match; last done.
             rewrite /Rpower.
             apply Rlt_le, exp_pos.
          -- rewrite SeriesC_finite_foldr. simpl.
             rewrite Rpower_plus Rpower_1; last lra.
             lra.
          -- iMod (ghost_var_update _ (Some (fin_to_nat n)) with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
             iMod ("Hclose" with "[$Hauth1 $Hauth2 Herr ]"); last by iFrame.
             iNext.
             case_bool_decide as H1; subst.
             ++ rewrite (bool_decide_eq_false_2 (_\/_)); last first.
                { intros [(?&?&?)|(?&?&?)].
                  - simplify_eq. lia.
                  - simplify_eq.
                    apply H.
                    naive_solver.
                }
                iExists _. iSplit; last done.
                rewrite (bool_decide_eq_true_2 (Some _ = Some _)); last by f_equal.
                iApply (ec_eq with "[$]").
                f_equal.
                rewrite plus_INR.
                simpl. lra.
             ++ rewrite (bool_decide_eq_true_2 (_\/_)); first done.
                left. eexists _. split; first done.
                lia.
      + iInv "I" as ">(%&%&Hauth1&Hauth2&Herr)" "Hclose".
        iDestruct (ghost_var_agree with "[$Hauth2][$]") as "->".
        case_bool_decide as H.
        * wp_apply wp_rand; first done.
          iIntros (n) "_".
          iMod (ghost_var_update _ (Some (fin_to_nat n)) with "[$Hauth2][$]") as "[Hauth2 Hfrag2]".
          iMod ("Hclose" with "[$Hauth1 $Hauth2 Herr ]"); last by iFrame.
          iNext. rewrite bool_decide_eq_true_2; first done.
          left.
          by destruct H as [|(?&?&?)].
        * iDestruct "Herr" as "(%&Herr&->)".
          rewrite (bool_decide_eq_false_2 (None = _)); last done.
          rewrite Nat.add_0_r.
          simpl.
          wp_apply (wp_couple_rand_adv_comp1' _ _ _ _
                      (λ x, if bool_decide (fin_to_nat x = 0)%nat
                            then (Rpower 6 (bool_to_nat (bool_decide (n1 = Some 0%nat)) - 2 + 1))%R
                            else 0%R
                      ) with "[$]") as (n) "Herr".
          -- intros. case_match; last done.
             rewrite /Rpower.
             apply Rlt_le, exp_pos.
          -- rewrite SeriesC_finite_foldr. simpl.
             rewrite Rpower_plus Rpower_1; last lra.
             lra.
          -- iMod (ghost_var_update _ (Some (fin_to_nat n)) with "[$Hauth2][$]") as "[Hauth2 Hfrag2]".
             iMod ("Hclose" with "[$Hauth1 $Hauth2 Herr ]"); last by iFrame.
             iNext.
             case_bool_decide as H1; subst.
             ++ rewrite (bool_decide_eq_false_2 (_\/_)); last first.
                { intros [(?&?&?)|(?&?&?)].
                  - simplify_eq.
                    apply H.
                    naive_solver.
                  - simplify_eq. lia.
                }
                iExists _. iSplit; last done.
                rewrite (bool_decide_eq_true_2 (Some _ = Some _)); last by f_equal.
                iApply (ec_eq with "[$]").
                f_equal.
                rewrite plus_INR.
                simpl. lra.
             ++ rewrite (bool_decide_eq_true_2 (_\/_)); first done.
                right. eexists _. split; first done.
                lia.
      + iIntros (??) "[(%n&->&Hfrag1) (%n'&->&Hfrag2)]".
        iNext.
        wp_pures.
        iInv "I" as ">(%&%&Hauth1&Hauth2&Herr)" "Hclose".
        iDestruct (ghost_var_agree with "[$Hauth1][$]") as "->".
        iDestruct (ghost_var_agree with "[$Hauth2][$]") as "->".
        iAssert (⌜0<n+n'⌝)%I as "%".
        { destruct n; destruct n'.
          { rewrite bool_decide_eq_false_2.
            - iDestruct "Herr" as "(%&Herr&->)".
              rewrite !bool_decide_eq_true_2; last done.
              simpl.
              replace (_+_-_)%R with 0%R; last lra.
              rewrite Rpower_O; last lra.
              iDestruct (ec_contradict with "[$]") as "[]".
              simpl. lra.
            - intros [(?&?&?)|(?&?&?)]; simplify_eq; lia.
          }
          all: iPureIntro; lia.
        }
        iMod ("Hclose" with "[$Herr $Hauth1 $Hauth2]").
        rewrite -Nat2Z.inj_add. iApply "HΦ".
        iPureIntro. lia.
  Qed.
End complex.

(** * This is the con_prog example in the paper of Coneris*)
Definition two_die_prog' : expr :=
  let: "l" := ref #0 in
  ((if: #0 < rand #5
    then FAA "l" #1
    else #()
   ) |||
     (if: #0 < rand #5
    then FAA "l" #1
    else #()));;
  !"l".

Section simple'.
  Context `{!conerisGS Σ, !spawnG Σ, !inG Σ (excl_authR boolO)}.

  Definition simple_parallel_add_inv' l γ :=
    (∃ (n:nat), l ↦#n ∗ (own γ (●E false) ∨ own γ (●E true) ∗ ⌜(0<n)%nat⌝))%I.
    
  Lemma simple_parallel_add_spec':
    {{{ ↯ (1/6) }}}
      two_die_prog'
      {{{ (n:nat), RET #n; ⌜(0<n)%nat⌝ }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    rewrite /two_die_prog'.
    wp_pures.
    wp_alloc l as "Hl".
    wp_pures.
    iMod (ghost_var_alloc' false) as "(%γ & Hauth & Hfrag)".
    iMod (inv_alloc nroot _ (simple_parallel_add_inv' _ _) with "[Hauth Hl]") as "#I".
    { iExists 0%nat. iFrame. }
    wp_apply (wp_par (λ _, own γ (◯E true) )%I
                (λ x, True)%I with "[Herr Hfrag][]").
    - wp_apply (wp_rand_err_nat _ _ 0%nat).
      iSplitL "Herr".
      { iApply (ec_eq with "[$]"). simpl. lra. }
      iIntros (??).
      wp_pures.
      rewrite bool_decide_eq_true_2; last lia.
      wp_pures.
      iInv "I" as ">(%&Hl&H)" "Hclose".
      wp_faa.
      iDestruct "H" as "[H|H]".
      + iMod (ghost_var_update' _ true with "[$][$]") as "[Hauth Hfrag]".
        iMod ("Hclose" with "[Hl Hauth]"); last done.
        iExists (n+1)%nat. iNext.
        rewrite Nat2Z.inj_add. iFrame.
        iRight. iSplit; first done.
        iPureIntro. lia.
      + iDestruct "H" as "[H %]".
        by iDestruct (ghost_var_agree' with "[$][$]") as "%".
    - wp_apply (wp_rand); first done.
      iIntros (??).
      wp_pures.
      case_bool_decide.
      + wp_pures.
        iInv "I" as ">(%&Hl&H)" "Hclose".
        wp_faa.
        iMod ("Hclose" with "[Hl H]"); last done. 
        iExists (_+1)%nat. iNext.
        rewrite Nat2Z.inj_add. iFrame.
        iDestruct "H" as "[H|[H %]]"; iFrame.
        iRight. iFrame. iPureIntro. lia.
      + by wp_pures.
    - iIntros (??) "[H _]".
      iNext.
      wp_pures.
      iInv "I" as ">(%n&Hl&[H'|[H' %]])" "Hclose";
        first by iDestruct (ghost_var_agree' with "[$][$]") as "%".
      wp_load.
      iMod ("Hclose" with "[H' Hl]") as "_".
      + iFrame. iRight. iFrame. by iPureIntro.
      + iApply "HΦ". by iPureIntro.
  Qed.
End simple'.


(** * This is the proof presented for the example con_prog in the paper of Coneris *)

Inductive T : Type :=
| S0 :T
| S1: forall (n:nat), (n>0)%nat -> T
| S2: forall (n:nat), T.

Definition sampled s :=
  match s with
  | S0 => None
  | S1 n _ => Some n
  | S2 n => Some n
  end.

Definition one_positive n1 n2:=
  bool_decide (∃ (n:nat), (n > 0)%nat /\ (sampled n1 = Some n \/ sampled n2 = Some n)).

Definition added_1 s:=
  bool_decide (∃ (n:nat), (n > 0)%nat /\ s=S2 n).

Canonical Structure TO := leibnizO T.

Section lemmasT.
  Context `{!inG Σ (excl_authR TO)}.

  (* Helpful lemmas *)
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
    ∃ (s1 s2 : T) (n:nat),
      let p:= one_positive s1 s2 in
      own γ1 (●E s1) ∗ own γ2 (●E s2) ∗
      l↦#n ∗
      (if (added_1 s1 || added_1 s2) then ⌜(0<n)%nat⌝ else True) ∗
      if p
      then ↯ 0%R
      else
        ∃ (flip_num:nat),
          ↯ (Rpower 6%R (INR flip_num-2))%R ∗
          ⌜(flip_num = bool_to_nat (bool_decide (sampled s1=Some 0%nat)) +bool_to_nat (bool_decide (sampled s2=Some 0%nat)))%nat⌝.
  
  Lemma complex_parallel_add_spec':
    {{{ ↯ (1/36) }}}
      two_die_prog'
      {{{ (n:nat), RET #n; ⌜(0<n)%nat⌝ }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    iMod (ghost_var_allocT S0) as (γ1) "[Hauth1 Hfrag1]".
    iMod (ghost_var_allocT S0) as (γ2) "[Hauth2 Hfrag2]".
    rewrite /two_die_prog'.
    wp_alloc l as "Hl".
    wp_pures.
    iMod (inv_alloc nroot _ (parallel_add_inv' γ1 γ2 l) with "[Hauth1 Hauth2 Herr Hl]") as "#I".
    { iNext.
      iFrame.
      simpl.
      iExists 0%nat. iFrame.
      replace (added_1 _) with false; last first.
      - rewrite /added_1. rewrite bool_decide_eq_false_2; first done.
        naive_solver.
      - iSplit; first done.
        rewrite /one_positive.
        rewrite bool_decide_eq_false_2; last naive_solver.
        iExists _; iSplit; last done.
        iApply (ec_eq with "[$]").
        simpl.
        replace (0-2)%R with (-2)%R by lra.
        rewrite Rpower_Ropp.
        rewrite Rdiv_1_l; f_equal.
        rewrite /Rpower.
        erewrite <-(exp_ln _); last lra.
        f_equal.
        replace (IPR 2) with (INR 2); last first.
        { by rewrite -INR_IPR. }
        erewrite <-ln_pow; [|lra].
        f_equal. lra.
    }
    wp_apply (wp_par (λ _, ∃ (n:nat), own γ1 (◯E (S2 n)))%I
                (λ _, ∃ (n:nat), own γ2 (◯E (S2 n)))%I with "[Hfrag1][Hfrag2]").
    - wp_bind (rand _)%E.
      iInv "I" as ">(%s1&%s2&%n&Hauth1&Hauth2&Hl&H&Herr)" "Hclose".
      iDestruct (ghost_var_agreeT with "[$Hauth1][$]") as "->".
      destruct (one_positive _ _) eqn:H1.
      + wp_apply (wp_rand with "[//]") as (x) "_".
        destruct (fin_to_nat x) as [|x'] eqn:Hx.
        * iMod (ghost_var_updateT _ (S2 0%nat) with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
          iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hl H Herr]") as "_".
          { iNext.
            replace (added_1 S0) with false; last first.
            { rewrite /added_1 bool_decide_eq_false_2; naive_solver. }
            replace (added_1 (S2 0)) with false; last first.
            { rewrite /added_1 bool_decide_eq_false_2; first done.
              intros (?&?&?). simplify_eq. lia. }
            rewrite !orb_false_l.
            iFrame.
            case_match eqn:H2; first done.
            rewrite /one_positive in H1 H2.
            apply bool_decide_eq_true_1 in H1.
            apply bool_decide_eq_false_1 in H2.
            exfalso.
            apply H2. naive_solver.
          }
          iModIntro. wp_pures. by iFrame.
        * iMod (ghost_var_updateT _ (S1 (S x') _) with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
          iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hl H Herr]") as "_".
          { iNext.
            replace (added_1 S0) with false; last first.
            { rewrite /added_1 bool_decide_eq_false_2; naive_solver. }
            replace (added_1 (S1 (S _) _)) with false; last first.
            { rewrite /added_1 bool_decide_eq_false_2; naive_solver. }
            rewrite !orb_false_l. iFrame.
            case_match eqn:H2; first done.
            rewrite /one_positive in H1 H2.
            apply bool_decide_eq_true_1 in H1.
            apply bool_decide_eq_false_1 in H2.
            exfalso.
            apply H2. naive_solver.
          }
          iModIntro. wp_pures.
          clear s2 H1 n.
          iInv "I" as ">(%s1&%s2&%n&Hauth1&Hauth2&Hl&H&Herr)" "Hclose".
          iDestruct (ghost_var_agreeT with "[$Hauth1][$]") as "->".
          wp_faa.
          iMod (ghost_var_updateT _ (S2 (S x')) with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
          replace (_+_)%Z with (Z.of_nat (n+1)); last lia.
          iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hl H Herr]") as "_"; last by iFrame.
          iNext.
          replace (added_1 (S2 _)) with true; last first.
          { rewrite /added_1. rewrite bool_decide_eq_true_2; first done.
            eexists _; split; last done. lia.
          }
          rewrite orb_true_l; iSplit; first (iPureIntro; lia).
          rewrite /one_positive.
          rewrite bool_decide_eq_true_2; first done.
          eexists _; split; last by left. lia.
      + iDestruct "Herr" as "(%&Herr&->)".
        simpl.
        wp_apply (wp_couple_rand_adv_comp1' _ _ _ _
                    (λ x, if bool_decide(fin_to_nat x = 0)%nat
                          then (Rpower 6 (bool_to_nat (bool_decide (sampled s2 = Some 0%nat)) - 2 +1))
                          else 0)%R with "[$]") as (x) "Herr".
        { intros. case_match; last done.
          rewrite /Rpower.
          apply Rlt_le, exp_pos.
        }
        { rewrite SeriesC_finite_foldr. simpl.
          rewrite Rpower_plus Rpower_1; lra.
        }
        case_bool_decide as H2.
        * iMod (ghost_var_updateT _ (S2 0%nat) with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
          iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hl H Herr]") as "_".
          { iNext.
            replace (added_1 S0) with false; last first.
            { rewrite /added_1 bool_decide_eq_false_2; naive_solver. }
            replace (added_1 (S2 0)) with false; last first.
            { rewrite /added_1 bool_decide_eq_false_2; first done.
              intros (?&?&?). simplify_eq. lia. }
            rewrite !orb_false_l.
            iFrame.
            case_match eqn:H3.
            - rewrite /one_positive in H1 H3.
              apply bool_decide_eq_false_1 in H1.
              apply bool_decide_eq_true in H3.
              exfalso. apply H1.
              destruct H3 as (?&[?[?|?]]); last naive_solver.
              simpl in *. simplify_eq. lia.
            - simpl. iExists _; iSplit; last done.
              iApply ec_eq; last done.
              f_equal. rewrite S_INR. lra.
          }
          iModIntro. rewrite H2. wp_pures. by iFrame.
        * unshelve iMod (ghost_var_updateT _ (S1 (x) _) with "[$Hauth1][$]") as "[Hauth1 Hfrag1]"; first lia.
          iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hl H Herr]") as "_".
          { iNext.
            replace (added_1 S0) with false; last first.
            { rewrite /added_1 bool_decide_eq_false_2; naive_solver. }
            replace (added_1 (S1 _ _)) with false; last first.
            { rewrite /added_1 bool_decide_eq_false_2; naive_solver. }
            rewrite !orb_false_l. iFrame.
            case_match eqn:H3; first done.
            rewrite /one_positive in H3.
            apply bool_decide_eq_false_1 in H3.
            exfalso.
            apply H3. eexists _. split; last by left. lia. 
          }
          iModIntro. wp_pures.
          clear s2 H1 n.
          rewrite bool_decide_eq_true_2; last lia.
          wp_pures.
          iInv "I" as ">(%s1&%s2&%n&Hauth1&Hauth2&Hl&H&Herr)" "Hclose".
          iDestruct (ghost_var_agreeT with "[$Hauth1][$]") as "->".
          wp_faa.
          iMod (ghost_var_updateT _ (S2 (x)) with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
          replace (_+_)%Z with (Z.of_nat (n+1)); last lia.
          iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hl H Herr]") as "_"; last by iFrame.
          iNext.
          replace (added_1 (S2 _)) with true; last first.
          { rewrite /added_1. rewrite bool_decide_eq_true_2; first done.
            eexists _; split; last done. lia.
          }
          rewrite orb_true_l; iSplit; first (iPureIntro; lia).
          rewrite /one_positive.
          rewrite bool_decide_eq_true_2; first done.
          eexists _; split; last by left. lia.
    - wp_bind (rand _)%E.
      iInv "I" as ">(%s1&%s2&%n&Hauth1&Hauth2&Hl&H&Herr)" "Hclose".
      iDestruct (ghost_var_agreeT with "[$Hauth2][$]") as "->".
      destruct (one_positive _ _) eqn:H1.
      + wp_apply (wp_rand with "[//]") as (x) "_".
        destruct (fin_to_nat x) as [|x'] eqn:Hx.
        * iMod (ghost_var_updateT _ (S2 0%nat) with "[$Hauth2][$]") as "[Hauth2 Hfrag2]".
          iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hl H Herr]") as "_".
          { iNext.
            replace (added_1 S0) with false; last first.
            { rewrite /added_1 bool_decide_eq_false_2; naive_solver. }
            replace (added_1 (S2 0)) with false; last first.
            { rewrite /added_1 bool_decide_eq_false_2; first done.
              intros (?&?&?). simplify_eq. lia. }
            rewrite !orb_false_r.
            iFrame.
            case_match eqn:H2; first done.
            rewrite /one_positive in H1 H2.
            apply bool_decide_eq_true_1 in H1.
            apply bool_decide_eq_false_1 in H2.
            exfalso.
            apply H2. naive_solver.
          }
          iModIntro. wp_pures. by iFrame.
        * unshelve iMod (ghost_var_updateT _ (S1 (S x') _) with "[$Hauth2][$]") as "[Hauth2 Hfrag2]"; first lia.
          iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hl H Herr]") as "_".
          { iNext.
            replace (added_1 S0) with false; last first.
            { rewrite /added_1 bool_decide_eq_false_2; naive_solver. }
            replace (added_1 (S1 (S _) _)) with false; last first.
            { rewrite /added_1 bool_decide_eq_false_2; naive_solver. }
            rewrite !orb_false_r. iFrame.
            case_match eqn:H2; first done.
            rewrite /one_positive in H1 H2.
            apply bool_decide_eq_true_1 in H1.
            apply bool_decide_eq_false_1 in H2.
            exfalso.
            apply H2. naive_solver.
          }
          iModIntro. wp_pures.
          clear s1 H1 n.
          iInv "I" as ">(%s1&%s2&%n&Hauth1&Hauth2&Hl&H&Herr)" "Hclose".
          iDestruct (ghost_var_agreeT with "[$Hauth2][$]") as "->".
          wp_faa.
          iMod (ghost_var_updateT _ (S2 (S x')) with "[$Hauth2][$]") as "[Hauth2 Hfrag2]".
          replace (_+_)%Z with (Z.of_nat (n+1)); last lia.
          iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hl H Herr]") as "_"; last by iFrame.
          iNext.
          replace (added_1 (S2 _)) with true; last first.
          { rewrite /added_1. rewrite bool_decide_eq_true_2; first done.
            eexists _; split; last done. lia.
          }
          rewrite orb_true_r; iSplit; first (iPureIntro; lia).
          rewrite /one_positive.
          rewrite bool_decide_eq_true_2; first done.
          eexists _; split; last by right. lia.
      + iDestruct "Herr" as "(%&Herr&->)".
        simpl.
        wp_apply (wp_couple_rand_adv_comp1' _ _ _ _
                    (λ x, if bool_decide(fin_to_nat x = 0)%nat
                          then (Rpower 6 (bool_to_nat (bool_decide (sampled s1 = Some 0%nat)) - 2 +1))
                          else 0)%R with "[$]") as (x) "Herr".
        { intros. case_match; last done.
          rewrite /Rpower.
          apply Rlt_le, exp_pos.
        }
        { rewrite SeriesC_finite_foldr. simpl.
          rewrite -plus_n_O Rpower_plus Rpower_1; lra. 
        }
        case_bool_decide as H2.
        * iMod (ghost_var_updateT _ (S2 0%nat) with "[$Hauth2][$]") as "[Hauth2 Hfrag2]".
          iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hl H Herr]") as "_".
          { iNext.
            replace (added_1 S0) with false; last first.
            { rewrite /added_1 bool_decide_eq_false_2; naive_solver. }
            replace (added_1 (S2 0)) with false; last first.
            { rewrite /added_1 bool_decide_eq_false_2; first done.
              intros (?&?&?). simplify_eq. lia. }
            rewrite !orb_false_r.
            iFrame.
            case_match eqn:H3.
            - rewrite /one_positive in H1 H3.
              apply bool_decide_eq_false_1 in H1.
              apply bool_decide_eq_true in H3.
              exfalso. apply H1.
              destruct H3 as (?&[?[?|?]]); first naive_solver.
              simpl in *. simplify_eq. lia.
            - simpl. iExists _; iSplit; last done.
              iApply ec_eq; last done.
              f_equal. rewrite plus_INR. simpl. lra. 
          }
          iModIntro. rewrite H2. wp_pures. by iFrame.
        * unshelve iMod (ghost_var_updateT _ (S1 (x) _) with "[$Hauth2][$]") as "[Hauth2 Hfrag2]"; first lia.
          iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hl H Herr]") as "_".
          { iNext.
            replace (added_1 S0) with false; last first.
            { rewrite /added_1 bool_decide_eq_false_2; naive_solver. }
            replace (added_1 (S1 _ _)) with false; last first.
            { rewrite /added_1 bool_decide_eq_false_2; naive_solver. }
            rewrite !orb_false_r. iFrame.
            case_match eqn:H3; first done.
            rewrite /one_positive in H3.
            apply bool_decide_eq_false_1 in H3.
            exfalso.
            apply H3. eexists _. split; last by right. lia. 
          }
          iModIntro. wp_pures.
          clear s1 H1 n.
          rewrite bool_decide_eq_true_2; last lia.
          wp_pures.
          iInv "I" as ">(%s1&%s2&%n&Hauth1&Hauth2&Hl&H&Herr)" "Hclose".
          iDestruct (ghost_var_agreeT with "[$Hauth2][$]") as "->".
          wp_faa.
          iMod (ghost_var_updateT _ (S2 (x)) with "[$Hauth2][$]") as "[Hauth2 Hfrag2]".
          replace (_+_)%Z with (Z.of_nat (n+1)); last lia.
          iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hl H Herr]") as "_"; last by iFrame.
          iNext.
          replace (added_1 (S2 _)) with true; last first.
          { rewrite /added_1. rewrite bool_decide_eq_true_2; first done.
            eexists _; split; last done. lia.
          }
          rewrite orb_true_r; iSplit; first (iPureIntro; lia).
          rewrite /one_positive.
          rewrite bool_decide_eq_true_2; first done.
          eexists _; split; last by right. lia.
    - iIntros (??) "[(%n1&Hfrag1) (%n2&Hfrag2)]".
      iNext.
      wp_pures.
      iInv "I" as ">(%s1&%s2&%n&Hauth1&Hauth2&Hl&H&Herr)" "Hclose".
      iDestruct (ghost_var_agreeT with "[$Hauth1][$]") as "->".
      iDestruct (ghost_var_agreeT with "[$Hauth2][$]") as "->".
      wp_load.
      iAssert (⌜(0<n)%nat⌝)%I as "%".
      + case_match eqn:H; first done.
        case_match eqn:H1.
        * rewrite orb_false_iff in H. destruct H as [Ha Hb].
          rewrite /added_1 in Ha Hb. apply bool_decide_eq_false_1 in Ha, Hb.
          rewrite /one_positive in H1. apply bool_decide_eq_true_1 in H1.
          exfalso. naive_solver.
        * iDestruct "Herr" as "(%&Herr&->)".
          iDestruct (ec_contradict with "[$]") as "[]".
          rewrite !bool_decide_eq_true_2/=; last first.
          -- destruct n1; first done.
             rewrite orb_false_iff in H. destruct H as [Ha Hb].
             rewrite /added_1 in Ha Hb. apply bool_decide_eq_false_1 in Ha, Hb.
             exfalso. apply Ha. eexists _. split; last done. lia.
          -- destruct n2; first done.
             rewrite orb_false_iff in H. destruct H as [Ha Hb].
             rewrite /added_1 in Ha Hb. apply bool_decide_eq_false_1 in Ha, Hb.
             exfalso. apply Hb. eexists _. split; last done. lia.
          -- replace (_+_-_)%R with 0%R; last lra.
             rewrite Rpower_O; lra.
      + iMod ("Hclose" with "[$]") as "_".
        iApply "HΦ".
        by iPureIntro.
        Unshelve.
        all: lia.
  Qed.
End complex'.
