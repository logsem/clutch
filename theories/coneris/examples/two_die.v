From iris.algebra Require Import excl_auth.
From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris par spawn.

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

Definition two_die_prog : expr :=
  let, ("v1", "v2") := ((rand #5) ||| rand #5) in
  "v1" + "v2".

Section simple.
  Context `{!conerisGS Σ, !spawnG Σ}.
  Lemma simple_parallel_add_spec:
    {{{ ↯ (1/3) }}}
      two_die_prog
      {{{ (n:nat), RET #n; ⌜(0<n)%nat⌝ }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    replace (1/3)%R with (1/6+1/6)%R by lra.
    iDestruct (ec_split with "[$]") as "[Herr Herr']"; [lra..|].
    rewrite /two_die_prog.
    wp_pures.
    wp_apply (wp_par (λ x, ∃ (n:nat), ⌜x=#n⌝ ∗ ⌜(0<n)%nat⌝)%I
                (λ x, ∃ (n:nat), ⌜x=#n⌝ ∗ ⌜(0<n)%nat⌝)%I with "[Herr][Herr']").
    - wp_apply (wp_rand_err_nat _ _ 0%nat).
      iSplitL.
      { iApply (ec_eq with "[$]"). simpl. lra. }
      iIntros (??).
      iPureIntro. simpl. eexists _; split; first done.
      lia.
    - wp_apply (wp_rand_err_nat _ _ 0%nat).
      iSplitL.
      { iApply (ec_eq with "[$]"). simpl. lra. }
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
        admit.
      + admit.
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
  Admitted.
End complex.




           
