From iris.algebra Require Import excl_auth frac_auth.
From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris par spawn atomic lib.flip hocap.

Local Open Scope Z.

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
    by iCombine "Hγ● Hγ◯" gives %<-%excl_auth_agree_L.
  Qed.

  Lemma ghost_var_update γ b' b c :
    own γ (●E b) -∗ own γ (◯E c) ==∗ own γ (●E b') ∗ own γ (◯E b').
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E b' ⋅ ◯E b') with "Hγ● Hγ◯") as "[$$]".
    { by apply excl_auth_update. }
    done.
  Qed.

  Local Lemma resource_nonneg (b:bool): (0 <= 1 - Rpower 2 (bool_to_nat b - 1))%R.
  Proof.
    destruct b as [|]; simpl.
    - replace (1-1)%R with 0%R by lra.
      rewrite Rpower_O; lra.
    - replace (1-1)%R with 0%R by lra.
      replace (0-1)%R with (-1)%R by lra.
      rewrite Rpower_Ropp. rewrite Rpower_1; lra.
  Qed. 
End lemmas.


Section lemmas.
  Context `{!inG Σ (excl_authR (optionO boolO))}.

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
    by iCombine "Hγ● Hγ◯" gives %<-%excl_auth_agree_L.
  Qed.

  Lemma ghost_var_update' γ b' b c :
    own γ (●E b) -∗ own γ (◯E c) ==∗ own γ (●E b') ∗ own γ (◯E b').
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E b' ⋅ ◯E b') with "Hγ● Hγ◯") as "[$$]".
    { by apply excl_auth_update. }
    done.
  Qed.
End lemmas.


Section lemmasZ.
  Context `{!inG Σ (excl_authR ZR)}.

  (* Helpful lemmas *)
  Lemma ghost_var_allocZ b :
    ⊢ |==> ∃ γ, own γ (●E b) ∗ own γ (◯E b).
  Proof.
    iMod (own_alloc (●E b ⋅ ◯E b)) as (γ) "[??]".
    - by apply excl_auth_valid.
    - by eauto with iFrame.
  Qed.

  Lemma ghost_var_agreeZ γ b c :
    own γ (●E b) -∗ own γ (◯E c) -∗ ⌜ b = c ⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    by iCombine "Hγ● Hγ◯" gives %<-%excl_auth_agree_L.
  Qed.

  Lemma ghost_var_updateZ γ b' b c :
    own γ (●E b) -∗ own γ (◯E c) ==∗ own γ (●E b') ∗ own γ (◯E b').
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E b' ⋅ ◯E b') with "Hγ● Hγ◯") as "[$$]".
    { by apply excl_auth_update. }
    done.
  Qed.
End lemmasZ.




Section simple_parallel_add.
Definition simple_parallel_add : expr :=
  let: "r" := ref #0 in
  ( if: #0 < rand #2 then FAA "r" #1 else #())
  |||
  (if: #0 < rand #2 then FAA "r" #1 else #())
  ;;
  !"r".

(* Simple spec, where the error is directly distributed *)
Context `{!conerisGS Σ, !spawnG Σ, !inG Σ (excl_authR boolO)}.

Definition simple_parallel_add_inv (l:loc) (γ1 γ2 : gname) : iProp Σ :=
  ∃ (b1 b2 : bool) (z : Z),
      own γ1 (●E b1) ∗ own γ2 (●E b2) ∗ l ↦ #z ∗
      ⌜(z = bool_to_Z b1 + bool_to_Z b2)%Z⌝.

Lemma simple_parallel_add_spec:
  {{{ ↯ (2/3) }}}
    simple_parallel_add
    {{{ (z:Z), RET #z; ⌜(z=2)⌝ }}}.
Proof.
  iIntros (Φ) "Herr HΦ".
  rewrite /simple_parallel_add.
  wp_alloc l as "Hl".
  wp_pures.
  iMod (ghost_var_alloc false) as (γ1) "[Hγ1● Hγ1◯]".
  iMod (ghost_var_alloc false) as (γ2) "[Hγ2● Hγ2◯]".
  iMod (inv_alloc nroot _ (simple_parallel_add_inv l γ1 γ2) with "[Hl Hγ1● Hγ2●]") as "#I".
  { iModIntro. iExists _, _, _. iFrame. iPureIntro. simpl. lia. }
  replace (2/3)%R with (/3 + /3)%R by lra.
  iDestruct (ec_split with "[$]") as "[Herr1 Herr2]"; [lra|lra|].
  wp_apply (wp_par (λ _, own γ1 (◯E true))%I (λ _, own γ2 (◯E true))%I
             with "[Herr1 Hγ1◯][Herr2 Hγ2◯]").
  { wp_apply (wp_rand_err_nat _ _ 0%nat).
    replace (INR (Z.to_nat 2) + 1)%R with 3%R; [iFrame|simpl; lra].
    iIntros (??).
    wp_pures.
    rewrite bool_decide_eq_true_2; last lia.
    wp_pures.
    iInv "I" as (???) ">(Hγ1● & Hγ2● & Hl & %)" "Hclose".
    iDestruct (ghost_var_agree with "[$Hγ1●][$]") as "->".
    wp_faa.
    iMod (ghost_var_update _ true with "[$Hγ1●][$]") as "[Hγ1● Hγ1◯]".
    iMod ("Hclose" with "[Hγ1● Hγ2● Hl]"); last done.
    iModIntro. iExists _, _, _. iFrame.
    iPureIntro. simpl in *. lia.
  }
  { wp_apply (wp_rand_err_nat _ _ 0%nat).
    replace (INR (Z.to_nat 2) + 1)%R with 3%R; [iFrame|simpl; lra].
    iIntros (??).
    wp_pures.
    rewrite bool_decide_eq_true_2; last lia.
    wp_pures.
    iInv "I" as (???) ">(Hγ1● & Hγ2● & Hl & %)" "Hclose".
    iDestruct (ghost_var_agree with "[$Hγ2●][$]") as "->".
    wp_faa.
    iMod (ghost_var_update _ true with "[$Hγ2●][$]") as "[Hγ2● Hγ2◯]".
    iMod ("Hclose" with "[Hγ1● Hγ2● Hl]"); last done.
    iModIntro. iExists _, _, _. iFrame.
    iPureIntro. simpl in *. lia.
  }
  iIntros (??) "[??]".
  iNext. wp_pures.
  iInv "I" as (???) ">(Hγ1● & Hγ2● & Hl & %)" "Hclose".
  iDestruct (ghost_var_agree with "[$Hγ1●][$]") as "->".
  iDestruct (ghost_var_agree with "[$Hγ2●][$]") as "->".
  simpl in *. subst. wp_load.
  iMod ("Hclose" with "[Hγ1● Hγ2● Hl]").
  - iNext. by iFrame.
  - iApply "HΦ". iPureIntro. lia.
Qed. 

End simple_parallel_add.

Section parallel_add.

Definition half_FAA (l:loc):=
  (if: flip then FAA #l #1 else #())%E.
  
Definition parallel_add : expr :=
  let: "r" := ref #0 in
  ( if: flip then FAA "r" #1 else #())
  |||
  (if: flip then FAA "r" #1 else #())
  ;;
  !"r".

Definition is_Some_true x:=
  match x with
  | Some true => true
  | _ => false
  end.

(* More complicated spec, where the error is stored in the invariant for adv comp *)
Context `{!conerisGS Σ, !spawnG Σ, !inG Σ (excl_authR (optionO boolO))}.

Definition parallel_add_inv (l:loc) (γ1 γ2 : gname) : iProp Σ :=
  ∃ (b1 b2 : option bool) (flip_num:nat) (err:nonnegreal) (z : Z),
    own γ1 (●E b1) ∗ own γ2 (●E b2) ∗ l ↦ #z ∗
    ↯ err ∗
    ⌜ (nonneg err = 1- Rpower 2%R (INR flip_num-2))%R⌝ ∗
    ⌜(flip_num = bool_to_nat (ssrbool.isSome b1) +bool_to_nat (ssrbool.isSome b2))%nat⌝∗ 
    ⌜(z = bool_to_Z (is_Some_true b1) + bool_to_Z (is_Some_true b2))%Z⌝
.

Lemma parallel_add_spec:
  {{{ ↯ (3/4) }}}
    parallel_add
    {{{ (z:Z), RET #z; ⌜(z=2)⌝ }}}.
Proof.
  iIntros (Φ) "Herr HΦ".
  rewrite /parallel_add.
  wp_alloc l as "Hl".
  wp_pures.
  iMod (ghost_var_alloc' None) as (γ1) "[Hγ1● Hγ1◯]".
  iMod (ghost_var_alloc' None) as (γ2) "[Hγ2● Hγ2◯]".
  iMod (inv_alloc nroot _ (parallel_add_inv l γ1 γ2) with "[Hl Hγ1● Hγ2● Herr]") as "#I".
  { iModIntro. iExists _, _, _,  (mknonnegreal _ _), _. iFrame.
    simpl.
    repeat iSplit; [|done|iPureIntro; lia].
    iPureIntro. simpl.
    replace (0-2)%R with (-2)%R by lra.
    assert (Rpower 2 (-2) = 1/4)%R; last lra.
    rewrite Rpower_Ropp.
    rewrite Rdiv_1_l; f_equal.
    rewrite /Rpower.
    rewrite -(exp_ln 4%R); last lra.
    f_equal.
    replace (IPR 2) with (INR 2); last first.
    { by rewrite -INR_IPR. }
    erewrite <-ln_pow; [|lra].
    f_equal. lra.
  }
  wp_apply (wp_par (λ _, own γ1 (◯E (Some true)))%I (λ _, own γ2 (◯E (Some true)))%I
             with "[Hγ1◯][Hγ2◯]").
  { rewrite /flipL.
    wp_pures.
    wp_bind (rand _)%E.
    iInv "I" as (?????) ">( Hγ1● & Hγ2● & Hl & Herr & %H & -> & ->)" "Hclose".
    iDestruct (ghost_var_agree' with "[$Hγ1●][$]") as "->".
    simpl in *.
    wp_apply (wp_couple_rand_adv_comp1 _ _ _ _
                (λ x, if fin_to_nat x =? 0 then nnreal_one else mknonnegreal (1 - Rpower 2 (bool_to_nat (ssrbool.isSome b2) - 1))%R _) with "[$Herr]").
    - rewrite SeriesC_finite_foldr; simpl.
      rewrite H.
      trans ((1 / (1 + 1) * (2 - Rpower 2 (bool_to_nat (ssrbool.isSome b2) - 1)) + 0))%R; first lra.
      trans (1 / (1 + 1) *  (2 - 2*Rpower 2 (bool_to_nat (ssrbool.isSome b2) - 2)))%R; last lra.
      assert (((Rpower 2 (bool_to_nat (ssrbool.isSome b2) - 1)) + 0)%R =
              (( 2 * Rpower 2 (bool_to_nat (ssrbool.isSome b2) - 2)))%R); last lra.
      assert (((INR (bool_to_nat (ssrbool.isSome b2)) - 1))%R = (1+(bool_to_nat (ssrbool.isSome b2) - 2)))%R as -> by lra.
      rewrite Rpower_plus. rewrite Rpower_1; lra.
    - iIntros (n) "Herr".
      inv_fin n; simpl; first (iExFalso; by iApply (ec_contradict with "[$]")).
      intros n. inv_fin n; last (intros n; inv_fin n).
      iMod (ghost_var_update' _ (Some false) with "[$Hγ1●][$]") as "[Hγ1● Hγ1◯]".
      iMod ("Hclose" with "[Hγ1● Hγ2● Hl Herr]") as "_".
      { iNext. iExists _, _, _, (mknonnegreal _ _ ), _. iFrame.
        repeat iSplit; iPureIntro; [|done|done].
        rewrite S_INR.
        simpl.
        replace (INR (bool_to_nat (ssrbool.isSome b2)) + 1 - 2)%R with
          (INR (bool_to_nat (ssrbool.isSome b2)) - 1)%R by lra.
        lra.
      }
      iModIntro. wp_pures.
      wp_apply conversion.wp_int_to_bool as "_"; first done.
      wp_pures.
      clear err H.
      iInv "I" as (?????) ">( Hγ1● & Hγ2● & Hl & Herr & %H & -> & ->)" "Hclose".
      iDestruct (ghost_var_agree' with "[$Hγ1●][$]") as "->".
      wp_faa.
      iMod (ghost_var_update' _ (Some true) with "[$Hγ1●][$]") as "[Hγ1● Hγ1◯]".
      iMod ("Hclose" with "[Hγ1● Hγ2● Hl Herr]") as "_"; last done.
      iNext. iExists _, _, _, (mknonnegreal _ _ ), _. iFrame; simpl.
      repeat iSplit; iPureIntro; [done|done|lia]. 
  }
  { rewrite /flipL.
    wp_pures.
    wp_bind (rand _)%E.
    iInv "I" as (?????) ">( Hγ1● & Hγ2● & Hl & Herr & %H & -> & ->)" "Hclose".
    iDestruct (ghost_var_agree' with "[$Hγ2●][$]") as "->".
    simpl in *.
    wp_apply (wp_couple_rand_adv_comp1 _ _ _ _
                (λ x, if fin_to_nat x =? 0 then nnreal_one else mknonnegreal (1 - Rpower 2 (bool_to_nat (ssrbool.isSome b1) - 1))%R _) with "[$Herr]").
    - rewrite SeriesC_finite_foldr; simpl.
      rewrite H.
      trans ((1 / (1 + 1) * (2 - Rpower 2 (bool_to_nat (ssrbool.isSome b1) - 1)) + 0))%R; first lra.
      rewrite Nat.add_0_r.
      trans (1 / (1 + 1) *  (2 - 2*Rpower 2 (bool_to_nat (ssrbool.isSome b1) - 2)))%R; last lra.
      assert (((Rpower 2 (bool_to_nat (ssrbool.isSome b1) - 1)) + 0)%R =
              (( 2 * Rpower 2 (bool_to_nat (ssrbool.isSome b1) - 2)))%R); last lra.
      assert (((INR (bool_to_nat (ssrbool.isSome b1)) - 1))%R = (1+(bool_to_nat (ssrbool.isSome b1) - 2)))%R as -> by lra.
      rewrite Rpower_plus. rewrite Rpower_1; lra.
    - iIntros (n) "Herr".
      inv_fin n; simpl; first (iExFalso; by iApply (ec_contradict with "[$]")).
      intros n. inv_fin n; last (intros n; inv_fin n).
      iMod (ghost_var_update' _ (Some false) with "[$Hγ2●][$]") as "[Hγ2● Hγ2◯]".
      iMod ("Hclose" with "[Hγ1● Hγ2● Hl Herr]") as "_".
      { iNext. iExists _, _, _, (mknonnegreal _ _ ), _. iFrame.
        repeat iSplit; iPureIntro; [|done|done].
        rewrite plus_INR.
        simpl.
        replace (INR (bool_to_nat (ssrbool.isSome b1))+1 - 2)%R with
          (INR (bool_to_nat (ssrbool.isSome b1)) - 1)%R; lra.
      }
      iModIntro. wp_pures.
      wp_apply conversion.wp_int_to_bool as "_"; first done.
      wp_pures.
      clear err H.
      iInv "I" as (?????) ">( Hγ1● & Hγ2● & Hl & Herr & %H & -> & ->)" "Hclose".
      iDestruct (ghost_var_agree' with "[$Hγ2●][$]") as "->".
      wp_faa.
      iMod (ghost_var_update' _ (Some true) with "[$Hγ2●][$]") as "[Hγ2● Hγ2◯]".
      iMod ("Hclose" with "[Hγ1● Hγ2● Hl Herr]") as "_"; last done.
      iNext. iExists _, _, _, (mknonnegreal _ _ ), _. iFrame; simpl.
      repeat iSplit; iPureIntro; [done|done|lia]. 
  }
  iIntros (??) "[Hγ1◯ Hγ2◯]".
  iNext. wp_pures.
  iInv "I" as (?????) ">( Hγ1● & Hγ2● & Hl & Herr & %H & -> & ->)" "Hclose".
  wp_load.
  iDestruct (ghost_var_agree' with "[$Hγ1●][$]") as "->".
  iDestruct (ghost_var_agree' with "[$Hγ2●][$]") as "->".
  iMod ("Hclose" with "[Hγ1● Hγ2● Hl Herr]") as "_".
  - iNext. iFrame. iPureIntro. simpl. eexists _. repeat split; naive_solver.
  - simpl. iApply "HΦ". iPureIntro. lia.
    Unshelve.
    all: try lra.
    all: try apply cond_nonneg.
    all: apply resource_nonneg. 
Qed.

(** This time we use the property of flip being logically atomic *)
Lemma parallel_add_spec':
  {{{ ↯ (3/4) }}}
    parallel_add
    {{{ (z:Z), RET #z; ⌜(z=2)⌝ }}}.
Proof.
  iIntros (Φ) "Herr HΦ".
  rewrite /parallel_add.
  wp_alloc l as "Hl".
  wp_pures.
  iMod (ghost_var_alloc' None) as (γ1) "[Hγ1● Hγ1◯]".
  iMod (ghost_var_alloc' None) as (γ2) "[Hγ2● Hγ2◯]".
  iMod (inv_alloc nroot _ (parallel_add_inv l γ1 γ2) with "[Hl Hγ1● Hγ2● Herr]") as "#I".
  { iModIntro. iExists _, _, _,  (mknonnegreal _ _), _. iFrame.
    simpl.
    repeat iSplit; [|done|iPureIntro; lia].
    iPureIntro. simpl.
    replace (0-2)%R with (-2)%R by lra.
    assert (Rpower 2 (-2) = 1/4)%R; last lra.
    rewrite Rpower_Ropp.
    rewrite Rdiv_1_l; f_equal.
    rewrite /Rpower.
    rewrite -(exp_ln 4%R); last lra.
    f_equal.
    replace (IPR 2) with (INR 2); last first.
    { by rewrite -INR_IPR. }
    erewrite <-ln_pow; [|lra].
    f_equal. lra.
  }
  wp_apply (wp_par (λ _, own γ1 (◯E (Some true)))%I (λ _, own γ2 (◯E (Some true)))%I
             with "[Hγ1◯][Hγ2◯]").
  { wp_bind (flipL _).
    (* need to change with using epsilon *)
    awp_apply
      (awp_flip_adv _
         (λ x b,
            match ClassicalEpsilon.excluded_middle_informative (1/2<=nonneg x)%R
            with
            | left P => if b then  mknonnegreal (2*x - 1)%R _ else nnreal_one
            | _ => x
            end )).
    - intros; case_match; simpl; lra.
    - iInv "I" as (?????) ">( Hγ1● & Hγ2● & Hl & Herr & %H & -> & ->)".
      iDestruct (ghost_var_agree' with "[$Hγ1●][$]") as "->".
      iAaccIntro with "Herr".
      + iIntros. iFrame. eauto.
      + iIntros (b).
        case_match eqn:Heqn; last first.
        { exfalso. apply n. rewrite H. simpl.
          rewrite Rpower_plus Rpower_Ropp.
          replace (Rpower 2 2)%R with 4%R; last first.
          { replace (2)%R with (1+1)%R at 2 by lra.
            rewrite Rpower_plus Rpower_1; lra.
          }
          assert (Rpower 2 (bool_to_nat (ssrbool.isSome b2))<=2)%R; last lra.
          replace 2%R with (Rpower 2 1)%R at 2; last (rewrite Rpower_1; lra).
          apply Rle_Rpower; first lra.
          replace 1%R with (INR 1) by done.
          apply le_INR.
          rewrite /bool_to_nat; case_match; lia.
        } 
        destruct b; last first.
        { iIntros. iExFalso. iApply ec_contradict; last done. simpl. lra. }
        simpl.
        iIntros "Herr".
        iMod (ghost_var_update' _ (Some false) with "[$Hγ1●][$]") as "[Hγ1● Hγ1◯]".
        iModIntro.
        iSplitL "Herr Hl Hγ1● Hγ2●".
        * iNext. iFrame. iExists _, (mknonnegreal _ _). simpl; iFrame.
          repeat iSplit; iPureIntro; [|done..].
          rewrite H. rewrite S_INR. simpl.
          replace (1 - Rpower 2 (bool_to_nat (ssrbool.isSome b2) + 1 - 2))%R with
            (1 - Rpower 2 (bool_to_nat (ssrbool.isSome b2) -1 ))%R; last (do 2 f_equal; lra).
          rewrite !Rpower_plus !Rpower_Ropp.
          replace (Rpower 2 2)%R with 4%R; last first.
          { replace (2)%R with (1+1)%R at 2 by lra.
            rewrite Rpower_plus Rpower_1; lra.
          }
          rewrite Rpower_1; lra.
        * wp_pures.
          clear err H r Heqn.
          iInv "I" as (?????) ">( Hγ1● & Hγ2● & Hl & Herr & %H & -> & ->)" "Hclose".
          iDestruct (ghost_var_agree' with "[$Hγ1●][$]") as "->".
          wp_faa.
          iMod (ghost_var_update' _ (Some true) with "[$Hγ1●][$]") as "[Hγ1● Hγ1◯]".
          iMod ("Hclose" with "[Hγ1● Hγ2● Hl Herr]") as "_"; last done.
          iNext. iExists _, _, _, (mknonnegreal _ _ ), _. iFrame; simpl.
          repeat iSplit; iPureIntro; [done|done|lia].
          Unshelve.
          all: simpl; try lra; apply cond_nonneg.
  }

  { wp_bind (flipL _).
    (* need to change with using epsilon *)
    awp_apply
      (awp_flip_adv _
         (λ x b,
            match ClassicalEpsilon.excluded_middle_informative (1/2<=nonneg x)%R
            with
            | left P => if b then  mknonnegreal (2*x - 1)%R _ else nnreal_one
            | _ => x
            end )).
    - intros; case_match; simpl; lra.
    - iInv "I" as (?????) ">( Hγ1● & Hγ2● & Hl & Herr & %H & -> & ->)".
      iDestruct (ghost_var_agree' with "[$Hγ2●][$]") as "->".
      iAaccIntro with "Herr".
      + iIntros. iFrame. eauto.
      + iIntros (b).
        case_match eqn:Heqn; last first.
        { exfalso. apply n. rewrite H. simpl.
          rewrite Rpower_plus Rpower_Ropp.
          replace (Rpower 2 2)%R with 4%R; last first.
          { replace (2)%R with (1+1)%R at 2 by lra.
            rewrite Rpower_plus Rpower_1; lra.
          }
          rewrite -plus_n_O.
          assert (Rpower 2 (bool_to_nat (ssrbool.isSome b1))<=2)%R; last lra.
          replace 2%R with (Rpower 2 1)%R at 2; last (rewrite Rpower_1; lra).
          apply Rle_Rpower; first lra.
          replace 1%R with (INR 1) by done.
          apply le_INR.
          rewrite /bool_to_nat; case_match; lia.
        } 
        destruct b; last first.
        { iIntros. iExFalso. iApply ec_contradict; last done. simpl. lra. }
        simpl.
        iIntros "Herr".
        iMod (ghost_var_update' _ (Some false) with "[$Hγ2●][$]") as "[Hγ2● Hγ2◯]".
        iModIntro.
        iSplitL "Herr Hl Hγ1● Hγ2●".
        * iNext. iFrame. iExists _, (mknonnegreal _ _). simpl; iFrame.
          repeat iSplit; iPureIntro; [|done..].
          rewrite H. simpl. rewrite !plus_INR.
          replace (1 - Rpower 2 (bool_to_nat (ssrbool.isSome b1) + 1 - 2))%R with
            (1 - Rpower 2 (bool_to_nat (ssrbool.isSome b1) -1 ))%R; last (do 2 f_equal; lra).
          rewrite !Rpower_plus !Rpower_Ropp.
          replace (Rpower 2 2)%R with 4%R; last first.
          { replace (2)%R with (1+1)%R at 2 by lra.
            rewrite Rpower_plus Rpower_1; lra.
          }
          simpl.
          rewrite Rpower_O; first rewrite Rpower_1; lra.
        * wp_pures.
          clear err H r Heqn.
          iInv "I" as (?????) ">( Hγ1● & Hγ2● & Hl & Herr & %H & -> & ->)" "Hclose".
          iDestruct (ghost_var_agree' with "[$Hγ2●][$]") as "->".
          wp_faa.
          iMod (ghost_var_update' _ (Some true) with "[$Hγ2●][$]") as "[Hγ2● Hγ2◯]".
          iMod ("Hclose" with "[Hγ1● Hγ2● Hl Herr]") as "_"; last done.
          iNext. iExists _, _, _, (mknonnegreal _ _ ), _. iFrame; simpl.
          repeat iSplit; iPureIntro; [done|done|lia].
          Unshelve.
          all: simpl; try lra; apply cond_nonneg.
  }
  
  iIntros (??) "[Hγ1◯ Hγ2◯]".
  iNext. wp_pures.
  iInv "I" as (?????) ">( Hγ1● & Hγ2● & Hl & Herr & %H & -> & ->)" "Hclose".
  wp_load.
  iDestruct (ghost_var_agree' with "[$Hγ1●][$]") as "->".
  iDestruct (ghost_var_agree' with "[$Hγ2●][$]") as "->".
  iMod ("Hclose" with "[Hγ1● Hγ2● Hl Herr]") as "_".
  - iNext. iFrame. iPureIntro. simpl. eexists _. repeat split; naive_solver.
  - simpl. iApply "HΦ". iPureIntro. lia.
Qed.

Context `{!hocap_errorGS Σ, !inG Σ (excl_authR ZR), !inG Σ (excl_authR (optionO boolO))}.
(* A hocap style spec for half_FAA*)
Definition loc_nroot:=nroot.@"loc".
Definition both_nroot:=nroot.@"both".
Definition loc_inv (l:loc) γ:= 
  inv loc_nroot (∃ (z:Z), l↦#z ∗ own γ (●E z)).

Lemma wp_half_FAA E
  (ε2 : nonnegreal -> bool -> nonnegreal)
  (P Q : iProp Σ) (R : bool -> iProp Σ) γ1 γ2 (l:loc):
  ↑hocap_error_nroot ⊆ E ->
  ↑loc_nroot ⊆ E ->
  (∀ (ε:nonnegreal),  ((nonneg (ε2 ε true) + nonneg (ε2 ε false))/2 <= (nonneg ε))%R) →
  {{{ error_inv γ1 ∗ loc_inv l γ2 ∗
      □(∀ (ε:nonnegreal) (b : bool), P ∗ ●↯ ε @ γ1 ={E∖↑hocap_error_nroot}=∗ (⌜(1<=ε2 ε b)%R⌝∨●↯ (ε2 ε b) @ γ1 ∗ R b) ) ∗
      □ (∀ (b:bool) (z:Z), R b ∗ own γ2 (●E z) ={E∖↑loc_nroot}=∗
                                       if b then own γ2 (●E(z+1)%Z)∗ Q else own γ2 (●E(z))∗ Q ) ∗
      P }}} half_FAA l @ E {{{ (v: val), RET v; Q }}}.
Proof.
  iIntros (Hsubset1 Hsubset2 Hineq Φ) "(#Hinv1 & #Hinv2 & #Hchange1 & #Hchange2 & HP) HΦ".
  rewrite /half_FAA.
  wp_apply (wp_hocap_flip_adv_comp _ _ P with "[-HΦ]"); [done|done|..].
  - by repeat iSplit.
  - iIntros. destruct b.
    + wp_pures. iInv "Hinv2" as "(%&?&?)" "Hclose".
      wp_faa.
      iMod ("Hchange2" with "[$]") as "[??]".
      iMod ("Hclose" with "[$]").
      by iApply "HΦ".
    + iInv "Hinv2" as "(%&?&?)" "Hclose".
      wp_pure.
      iMod ("Hchange2" with "[$]") as "[??]".
      iMod ("Hclose" with "[$]").
      by iApply "HΦ".
Qed.

Lemma parallel_add_spec''':
  {{{ ↯ (3/4) }}}
    parallel_add
    {{{ (z:Z), RET #z; ⌜(z=2)⌝ }}}.
Proof.
  iIntros (Φ) "Herr HΦ".
  rewrite /parallel_add.
  wp_alloc l as "Hl".
  wp_pures.
  rewrite -/(half_FAA l).
  (** Allocate hocap error*)
  unshelve iMod (hocap_error_alloc (mknonnegreal (3/4) _)) as "(%γ1 & Hεauth & Hεfrag)".
  { lra. }
  simpl.
  (** Allocate hocap heap *)
  iMod (own_alloc ((●E 0) ⋅ (◯E 0))) as "[%γ2 [Hauth_loc Hfrag_loc]]".
  { by apply excl_auth_valid. }
  (** Allocate hocap for tracking contributions *)
  iMod (own_alloc ((●E None) ⋅ (◯E None))) as "[%γ3 [Hauth_a Hfrag_a]]".
  { by apply excl_auth_valid. }
  iMod (own_alloc ((●E None) ⋅ (◯E None))) as "[%γ4 [Hauth_b Hfrag_b]]".
  { by apply excl_auth_valid. }
  (** Allocate error invariants *)
  iMod (inv_alloc hocap_error_nroot _ ((∃ (ε:nonnegreal), ↯ ε ∗ ●↯ ε @ γ1)) with "[Herr Hεauth]") as "#Hεinv".
  { iExists (mknonnegreal (3/4) _); iFrame.
    Unshelve. lra. }
  (** Allocate location inv *)
  iMod (inv_alloc loc_nroot _ (∃ (z:Z), l↦#z ∗ own γ2 (●E z)
          ) with "[Hl Hauth_loc]") as "#Hlocinv".
  { iFrame. }
  iMod (inv_alloc both_nroot _
          (∃ (z:Z) (a b:option bool), own γ2 (◯E z) ∗
                                   own γ3 (●E a) ∗
                                   own γ4 (●E b) ∗
                                   ⌜(z=bool_to_Z (is_Some_true a) + bool_to_Z (is_Some_true b))%Z⌝ ∗
                                   ◯↯ (1-Rpower 2 (IZR (bool_to_Z (bool_decide (is_Some a)))+IZR (bool_to_Z (bool_decide (is_Some b)))-2))%R@ γ1)
         with "[Hfrag_loc Hεfrag Hauth_a Hauth_b]") as "#Hinvboth".
  { iFrame. simpl. iModIntro. iSplitR; first by iPureIntro.
    replace (1-_)%R with (3/4)%R; first done.
    replace (Rpower _ _) with (1/4)%R; try lra.
    replace (0+0-2)%R with (-2)%R by lra.
    rewrite Rpower_Ropp/ Rpower. replace (IPR 2) with (INR 2); last done.
    rewrite -ln_pow; last lra.
    rewrite exp_ln; lra.
  }
  wp_apply (wp_par (λ _, own γ3 (◯E (Some true)))(λ _, own γ4 (◯E (Some true))) with "[Hfrag_a][Hfrag_b]").
  - (* first branch *)
    wp_apply (wp_half_FAA _ (λ x b,
            match ClassicalEpsilon.excluded_middle_informative (1/2<=nonneg x)%R
            with
            | left P => if b then  mknonnegreal (2*x - 1)%R _ else nnreal_one
            | _ => x
            end ) (own γ3 (◯E None))
                (own γ3 (◯E (Some true)))
                (λ b, ⌜b=true⌝ ∗ (own γ3 (◯E (Some false))))%I γ1 γ2 l with "[$Hfrag_a]"); [done|done|..].
    + intros. case_match; simpl; lra.
    + repeat iSplit.
      * done.
      * done.
      * iModIntro. iIntros (ε res) "[Hfrag_a Hεauth]".
        iInv both_nroot as ">(%z & %a & %b & Hloc_frag & Hauth_a & Hauth_b & -> & Hεfrag)" "Hclose".
        iDestruct (hocap_error_agree with "[$][$]") as "%K".
        iDestruct (ghost_var_agree' with "[$Hauth_a][$]") as "->".
        simpl in *.
        case_match; last first.
        { exfalso. apply n.
          simpl in *.
          rewrite K.
          assert (Rpower 2 (0+IZR (bool_to_Z (bool_decide (is_Some b))) - 2) <= 1/2)%R; try lra.
          replace (_/_)%R with (/2) by lra.
          rewrite -{3}(Rpower_1 2); last lra.
          rewrite -Rpower_Ropp.
          apply Rle_Rpower; first lra.
          case_bool_decide; simpl; lra.
        }
        iMod (ghost_var_update' _ (Some false) with "[$Hauth_a][$]") as "[Hauth_a Hfrag_a]".
        iMod (hocap_error_update _ (mknonnegreal _ _)with "[$][$]") as "[Hεauth Hεfrag]".
        simpl.
        iMod ("Hclose" with "[Hloc_frag Hauth_a Hauth_b Hεfrag]"); iFrame; first done.
        simpl. case_match; last first.
        { iLeft. done. }
        iRight. iFrame. iModIntro; iSplitL; last done.
        simpl. rewrite K.
        iApply (hocap_error_irrel with "[$]").
        rewrite !Rpower_plus Rpower_O; last lra.
        rewrite Rpower_1; lra.
      * iModIntro.
        iIntros (??) "[[-> Hfrag_a] Hauth_loc]".
        iInv both_nroot as ">(% & %a & %b & Hloc_frag & Hauth_a & Hauth_b & -> & Hεfrag)" "Hclose".
        iDestruct (ghost_var_agreeZ with "[$][$]") as "->". 
        iDestruct (ghost_var_agree'  with "[$Hauth_a][$]") as "->".
        iMod (ghost_var_updateZ  with "[$][$]") as "[Hauth_loc Hfrag_loc]".
        iMod (ghost_var_update' _ (Some true) with "[$Hauth_a][$]") as "[Hauth_a Hfrag_a]".
        simpl.
        iMod ("Hclose" with "[$Hfrag_loc $Hauth_a $Hauth_b $Hεfrag]") as "_"; first done.
        iFrame. simpl.
        iModIntro.
        replace (0+_+1)%Z with (1+bool_to_Z (is_Some_true b)); [done|lia].
    + iIntros. done. 
  - (* first branch *)
    wp_apply (wp_half_FAA _ (λ x b,
            match ClassicalEpsilon.excluded_middle_informative (1/2<=nonneg x)%R
            with
            | left P => if b then  mknonnegreal (2*x - 1)%R _ else nnreal_one
            | _ => x
            end ) (own γ4 (◯E None))
                (own γ4 (◯E (Some true)))
                (λ b, ⌜b=true⌝ ∗ (own γ4 (◯E (Some false))))%I γ1 γ2 l with "[$Hfrag_b]"); [done|done|..].
    + intros. case_match; simpl; lra.
    + repeat iSplit.
      * done.
      * done.
      * iModIntro. iIntros (ε res) "[Hfrag_b Hεauth]".
        iInv both_nroot as ">(%z & %a & %b & Hloc_frag & Hauth_a & Hauth_b & -> & Hεfrag)" "Hclose".
        iDestruct (hocap_error_agree with "[$][$]") as "%K".
        iDestruct (ghost_var_agree' with "[$Hauth_b][$]") as "->".
        simpl in *.
        case_match; last first.
        { exfalso. apply n.
          simpl in *.
          rewrite K.
          assert (Rpower 2 (IZR (bool_to_Z (bool_decide (is_Some a)))+0 - 2) <= 1/2)%R; try lra.
          replace (_/_)%R with (/2) by lra.
          rewrite -{3}(Rpower_1 2); last lra.
          rewrite -Rpower_Ropp.
          apply Rle_Rpower; first lra.
          case_bool_decide; simpl; lra.
        }
        iMod (ghost_var_update' _ (Some false) with "[$Hauth_b][$]") as "[Hauth_b Hfrag_b]".
        iMod (hocap_error_update _ (mknonnegreal _ _)with "[$][$]") as "[Hεauth Hεfrag]".
        simpl.
        iMod ("Hclose" with "[Hloc_frag Hauth_a Hauth_b Hεfrag]"); iFrame; first done.
        simpl. case_match; last first.
        { iLeft. done. }
        iRight. iFrame. iModIntro; iSplitL; last done.
        simpl. rewrite K.
        iApply (hocap_error_irrel with "[$]").
        rewrite !Rpower_plus Rpower_O; last lra.
        rewrite Rpower_1; lra.
      * iModIntro.
        iIntros (??) "[[-> Hfrag_a] Hauth_loc]".
        iInv both_nroot as ">(% & %a & %b & Hloc_frag & Hauth_a & Hauth_b & -> & Hεfrag)" "Hclose".
        iDestruct (ghost_var_agreeZ with "[$][$]") as "->". 
        iDestruct (ghost_var_agree'  with "[$Hauth_b][$]") as "->".
        iMod (ghost_var_updateZ  with "[$][$]") as "[Hauth_loc Hfrag_loc]".
        iMod (ghost_var_update' _ (Some true) with "[$Hauth_b][$]") as "[Hauth_b Hfrag_b]".
        simpl.
        iMod ("Hclose" with "[$Hfrag_loc $Hauth_a $Hauth_b $Hεfrag]") as "_"; first done.
        iFrame. simpl.
        iModIntro.
        replace (_+0+1)%Z with (bool_to_Z (is_Some_true a)+1); [done|lia].
    + iIntros. done. 
  - iIntros (??) "[Hfrag_a Hfrag_b]". iModIntro. wp_pures.
    iInv loc_nroot as ">(%&Hl&Hloc_auth)" "Hclose".
    iInv both_nroot as ">(%&%&%&Hloc_frag&Hauth_a & Hauth_b & -> & Hεfrag)" "Hclose'".
    iDestruct (ghost_var_agreeZ with "[$][$]") as "->". 
    iDestruct (ghost_var_agree' with "[$Hauth_a][$]") as "->".
    iDestruct (ghost_var_agree' with "[$Hauth_b][$]") as "->".
    simpl.
    wp_load.
    iMod ("Hclose'" with "[$Hloc_frag $Hauth_a $Hauth_b $Hεfrag]"); first done.
    iModIntro.
    iMod ("Hclose" with "[Hl Hloc_auth]"); first by iFrame.
    by iApply "HΦ".
    Unshelve.
    all: simpl; try lra.
    + replace (1+_-2)%R with (INR (bool_to_nat (bool_decide (is_Some b)))-1)%R; first apply resource_nonneg.
      case_bool_decide; simpl; lra.
    + replace (_+1-2)%R with (INR (bool_to_nat (bool_decide (is_Some a)))-1)%R; first apply resource_nonneg.
      case_bool_decide; simpl; lra.
Qed.
  
  

End parallel_add.

