From iris.algebra Require Import excl_auth frac_auth.
From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris par spawn atomic lib.flip.

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

Section lemmasfrac.
  Context `{!inG Σ (frac_authR ZR)}.

  (* Helpful lemmas *)
  Lemma ghost_var_alloc_frac b :
    ⊢ |==> ∃ γ, own γ (●F b) ∗ own γ (◯F b).
  Proof.
    iMod (own_alloc (●F b ⋅ ◯F b)) as (γ) "[??]".
    - by apply frac_auth_valid.
    - by eauto with iFrame.
  Qed.

  Lemma ghost_var_agree_frac γ b c :
    own γ (●F b) -∗ own γ (◯F c) -∗ ⌜ b = c ⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    by iCombine "Hγ● Hγ◯" gives %<-%frac_auth_agree_L.
  Qed.

  Lemma ghost_var_update_frac γ b' b c q:
    own γ (●F b) -∗ own γ (◯F{q} c) ==∗ own γ (●F (b+b')) ∗ own γ (◯F{q} (c+ b')).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●F _ ⋅ ◯F{q} _) with "Hγ● Hγ◯") as "[$$]".
    { apply frac_auth_update. apply Z_local_update; lia. }
    done.
  Qed.
End lemmasfrac.

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

Section attempt1.
  (* More complicated spec, where the error is stored in the invariant for adv comp *)
  Context `{!conerisGS Σ, !spawnG Σ, !inG Σ (excl_authR (optionO boolO))}.

  (** Ideally err should be a R*)
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
                  (λ x, if fin_to_nat x =? 0 then 1%R else (1 - Rpower 2 (bool_to_nat (ssrbool.isSome b2) - 1))%R) with "[$Herr]").
      - intros; case_match; first lra.
        apply resource_nonneg.
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
                  (λ x, if fin_to_nat x =? 0 then 1%R else (1 - Rpower 2 (bool_to_nat (ssrbool.isSome b1) - 1))%R) with "[$Herr]").
      - intros; case_match; first lra. apply resource_nonneg.
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
      all: simpl; try apply cond_nonneg.
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
              match ClassicalEpsilon.excluded_middle_informative (1/2<=x)%R
              with
              | left P => if b then(2*x - 1)%R else 1%R
              | _ => x
              end )).
      - intros. repeat case_match; lra.
      - intros; case_match; simpl; lra.
      - iInv "I" as (?????) ">( Hγ1● & Hγ2● & Hl & Herr & %H & -> & ->)".
        iDestruct (ghost_var_agree' with "[$Hγ1●][$]") as "->".
        iAaccIntro with "Herr".
        + iIntros. iFrame. eauto.
        + iIntros (b).
          case_match eqn:Heqn; last first.
          { exfalso. apply n. simpl. rewrite H.
            rewrite Rpower_plus Rpower_Ropp.
            replace (Rpower 2 2)%R with 4%R; last first.
            { replace (2)%R with (1+1)%R at 2 by lra.
              rewrite Rpower_plus Rpower_1; lra.
            }
            simpl.
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
            all: simpl; simpl in *; try lra; apply cond_nonneg.
    }
    { wp_bind (flipL _).
      (* need to change with using epsilon *)
      awp_apply
        (awp_flip_adv _
           (λ x b,
              match ClassicalEpsilon.excluded_middle_informative (1/2<=x)%R
              with
              | left P => if b then  (2*x - 1)%R else 1%R
              | _ => x
              end )).
      - intros; repeat case_match; simpl; lra.
      - intros; case_match; simpl; lra.
      - iInv "I" as (?????) ">( Hγ1● & Hγ2● & Hl & Herr & %H & -> & ->)".
        iDestruct (ghost_var_agree' with "[$Hγ2●][$]") as "->".
        iAaccIntro with "Herr".
        + iIntros. iFrame. eauto.
        + iIntros (b).
          case_match eqn:Heqn; last first.
          { exfalso. apply n. simpl. rewrite H. simpl.
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
            all: simpl; simpl in *; try lra; apply cond_nonneg.
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
End attempt1.

Definition loc_nroot:=nroot.@"loc".
Definition both_nroot:=nroot.@"both".

Definition half_FAA' (l:loc) α:=
  (if: flipL #lbl:α then FAA #l #1 else #())%E.
  
Definition parallel_add' : expr :=
  let: "r" := ref #0 in
  let: "α" := allocB in
  let: "α'" := allocB in
  ( if: flipL "α" then FAA "r" #1 else #())
  |||
  (if: flipL "α'" then FAA "r" #1 else #())
  ;;
  !"r".

Section attempt3.
  Context `{!conerisGS Σ, !spawnG Σ, !inG Σ (frac_authR ZR)}.
  (* A hocap style spec for half_FAA'*)
  
  Lemma wp_half_FAA' E
    (P Q : iProp Σ)  γ (l:loc) α bs:
    ↑loc_nroot ⊆ E ->
    {{{ inv loc_nroot (∃ (z:Z), l↦#z ∗ own γ (●F z)) ∗
        □ (∀ (z:Z), P ∗ own γ (●F z) ={E∖↑loc_nroot}=∗
                          own γ (●F(z+1)%Z)∗ Q) ∗
        P ∗ α ↪B (true::bs) }}} half_FAA' l α @ E {{{ (v: val), RET v; α ↪B (bs) ∗ Q }}}.
  Proof.
    iIntros (Hsubset Φ) "(#Hinv & #Hchange & HP & Hα) HΦ".
    rewrite /half_FAA'.
    wp_apply (wp_flipL with "[$]").
    iIntros "Hα".
    wp_pures.
    iInv "Hinv" as "(%&?&?)" "Hclose".
    wp_faa.
    iMod ("Hchange" with "[$]") as "[??]".
    iMod ("Hclose" with "[$]").
    iApply "HΦ". by iFrame.
  Qed.

  
  Lemma parallel_add_spec''':
    {{{ ↯ (3/4) }}}
      parallel_add'
      {{{ (z:Z), RET #z; ⌜(z=2)⌝ }}}.
  Proof with wp_pures.
    iIntros (Φ) "Herr HΦ".
    rewrite /parallel_add'.
    wp_alloc l as "Hl".
    wp_pures.
    wp_apply (wp_allocB_tape with "[//]") as (α) "Hα"...
    wp_apply (wp_allocB_tape with "[//]") as (α') "Hα'"...
    rewrite -/(half_FAA' l α) -/(half_FAA' l α').
    (** Create location RA *)
    iMod (own_alloc ((●F 0) ⋅ (◯F 0))) as "[%γ [Hauth_loc Hfrag_loc]]".
    { by apply frac_auth_valid. }
    (** Allocate location inv *)
    iMod (inv_alloc loc_nroot _ (∃ (z:Z), l↦#z ∗ own γ (●F z)
            ) with "[Hl Hauth_loc]") as "#Hlocinv".
    { iFrame. }
    iDestruct "Hfrag_loc" as "[Hfrac_a Hfrac_b]".
    (** presample *)
    wp_apply (wp_presample_bool_adv_comp _ _ _ _ _ _ (λ b, if b then nnreal_half else nnreal_one)); last iFrame "Hα Herr".
    { intros; case_match; simpl; lra. }
    { simpl; lra. }
    iIntros ([|]) "[Herr Hα]"; last first.
    { iExFalso. by iApply ec_contradict. }
    wp_apply (wp_presample_bool_adv_comp _ _ _ _ _ _ (λ b, if b then nnreal_zero else nnreal_one)); last iFrame "Hα' Herr".
    { intros; case_match; simpl; lra. }
    { simpl; lra. }
    iIntros ([|]) "[? Hα']"; last first.
    { iExFalso. by iApply ec_contradict. }
    wp_apply (wp_par (λ _, own γ (◯F{1/2} 1))%I (λ _, own γ (◯F{1/2} 1))%I
               with "[Hfrac_a Hα][Hfrac_b Hα']").
    - wp_apply (wp_half_FAA' _ (own γ (◯F{1/2} 0)) (own γ (◯F{1/2} 1)) with "[$Hfrac_a $Hα]"); [done| | by iIntros (?) "[??]"].
      iSplit; first done.
      iModIntro.
      iIntros (?) "[Hfrac Hauth]".
      iMod (ghost_var_update_frac with "[$][$]") as "[??]".
      by iFrame.
    - wp_apply (wp_half_FAA' _ (own γ (◯F{1/2} 0)) (own γ (◯F{1/2} 1)) with "[$Hfrac_b $Hα']"); [done| | by iIntros (?) "[??]"].
      iSplit; first done.
      iModIntro.
      iIntros (?) "[Hfrac Hauth]".
      iMod (ghost_var_update_frac with "[$][$]") as "[??]".
      by iFrame.
    - iIntros (??) "[Hfrac_a Hfrac_b]".
      iCombine "Hfrac_a Hfrac_b" as "Hfrac".
      iNext. wp_pures.
      iInv "Hlocinv" as ">(%z & Hl & Hauth)" "Hclose".
      iDestruct (ghost_var_agree_frac with "[$][$]") as "->".
      wp_load.
      iMod ("Hclose" with "[$]").
      by iApply "HΦ".
  Qed. 
  
End attempt3.


End parallel_add.

