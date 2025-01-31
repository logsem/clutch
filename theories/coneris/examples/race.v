From iris.algebra Require Import excl_auth.
From clutch.coneris Require Import coneris par spawn lib.hocap_rand_atomic.

Local Open Scope Z.

Set Default Proof Using "Type*".

Inductive T : Type :=
| S1 |S2 |S3|S4|S5 :T.
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


Section race.
  Context `{!conerisGS Σ, !spawnG Σ, !rand_atomic_spec 1, !inG Σ (excl_authR TO)}.

  Definition race_prog : expr :=
  let: "r" := ref #false in
  let: "res" := ref #(-1) in
  let: "α":= rand_allocate_tape #() in
  ( if: CAS "r" #false #true then "res" <- (rand_tape "α") else #())
  |||
  (if: CAS "r" #false #true then "res" <- (rand_tape "α") else #())
  ;;
  !"res".


  Definition winning s :=
    match s with
    | S2 |S3 |S4 => Some true
    | S5 => Some false
    |_ => None
    end. 
  
  Definition check_invalid s1 s2 : Prop :=
    match (winning s1, winning s2) with
    | (Some true, Some true) | (Some false, None) | (None, Some false)| (Some false, Some false)=> False
    | _ => True
    end.

  Definition value_of_r s1 s2:=
    match (winning s1, winning s2) with
    | (Some true, _) |(_, Some true) => true
    | _ => false
    end.

  Definition value_of_res s1 s2:=
    match (s1, s2) with
    | (S4, _) | (_, S4)  => 1%Z
    | _ => -1%Z
    end.

  Definition tape_elem s1 s2:=
    match (s1, s2) with
    | (S3, _) | (_, S3) | (S4, _) |(_, S4)  => []
    | _ => [1%nat]
    end.

  Definition inv_pred r res α γ1 γ2:=
    (∃ s1 s2,
      own γ1 (●E s1) ∗ own γ2 (●E s2) ∗
      ⌜check_invalid s1 s2⌝ ∗
      r ↦ #(value_of_r s1 s2) ∗
      res ↦ #(value_of_res s1 s2) ∗
      rand_tapes α (tape_elem s1 s2)
    )%I.
    
  (* We want to upper bound the probability we get a 0 (error).
     If we use two tapes, we need to pay 3/4 to ensure both tapes dont have a 0
     If we use one tape, we only need 1/2
   *)
  Lemma race_prog_spec:
  {{{ ↯ (1/2) }}}
    race_prog
    {{{ (z:Z), RET #z; ⌜(z=1)⌝ }}}.
  Proof with wp_pures. 
  iIntros (Φ) "Herr HΦ".
  rewrite /race_prog.
  wp_alloc r as "Hr"...
  wp_alloc res as "Hres"...
  wp_apply (rand_allocate_tape_spec with "[//]") as (α) "Hα".
  wp_pures.
  iMod (ghost_var_alloc S1) as "(%γ1 & Hauth1 & Hfrag1)".
  iMod (ghost_var_alloc S1) as "(%γ2 & Hauth2 & Hfrag2)".
  iMod (rand_tapes_presample _ _ _ _ (λ x, if bool_decide (fin_to_nat x=0)%nat then nnreal_one else nnreal_zero) with "[$][$]") as "(%n&Herr&Hα)".
  { intros. case_bool_decide; simpl; lra. }
  { rewrite SeriesC_finite_foldr/=. lra. }
  case_bool_decide.
  { iDestruct (ec_contradict with "[$]") as "[]". by simpl. }
  rewrite app_nil_l.
  assert (fin_to_nat n=1)%nat as ->.
  { pose proof fin_to_nat_lt n. lia. }
  iMod (inv_alloc nroot _ (inv_pred _ _ _ _ _) with "[$Hauth1 $Hauth2 $Hr $Hres $Hα]") as "#Hinv"; simpl.
  wp_apply (wp_par (λ _, own γ1 (◯E (S4)) ∨ own γ1 (◯E (S5)))%I
                (λ _, own γ2 (◯E (S4)) ∨ own γ2 (◯E (S5)))%I with "[Hfrag1][Hfrag2]").
  - wp_bind (CmpXchg _ _ _)%E.
    iInv "Hinv" as ">(%s1&%s2&Hauth1&Hauth2&%Hc1&Hr&Hres&Hα)" "Hclose".
    iDestruct (ghost_var_agree with "[$Hauth1][$]") as "->".
    wp_cmpxchg as Hr | Hr; simplify_eq.
    + (* success *)
      iMod (ghost_var_update _ S2 with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
      iMod ("Hclose" with "[$Hauth1 $Hauth2 Hr Hres Hα]") as "_".
      { destruct s2; by iFrame. }
      iModIntro. wp_pures.
      clear.
      awp_apply (rand_tape_spec_some).
      iInv "Hinv" as ">(%s1&%s2&Hauth1&Hauth2&%Hc1&Hr&Hres&Hα)".
      iDestruct (ghost_var_agree with "[$Hauth1][$]") as "->".
      replace (tape_elem _ _) with [1%nat]; last first.
      { by destruct s2. }
      iAaccIntro with "Hα".
      { iFrame.
        iIntros. iModIntro.
        iNext. iFrame. iSplit; first done.
        by destruct s2.
      }
      iIntros "Hα".
      iMod (ghost_var_update _ S3 with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
      iFrame. iModIntro.  iSplit.
      { iPureIntro. by destruct s2. }
      clear.
      iInv "Hinv" as ">(%s1&%s2&Hauth1&Hauth2&%Hc1&Hr&Hres&Hα)" "Hclose".
      iDestruct (ghost_var_agree with "[$Hauth1][$]") as "->".
      wp_store.
      iMod (ghost_var_update _ S4 with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
      iMod ("Hclose" with "[$Hauth1 $Hauth2 Hr Hres Hα]") as "_".
      { iFrame. destruct s2; by iFrame. }
      by iFrame.
    + iMod (ghost_var_update _ S5 with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
      iMod ("Hclose" with "[$Hauth1 $Hauth2 Hr Hres Hα]") as "_".
      { destruct s2; by iFrame. }
      iModIntro.
      wp_pures.
      by iFrame.
  - wp_bind (CmpXchg _ _ _)%E.
    iInv "Hinv" as ">(%s1&%s2&Hauth1&Hauth2&%Hc1&Hr&Hres&Hα)" "Hclose".
    iDestruct (ghost_var_agree with "[$Hauth2][$]") as "->".
    wp_cmpxchg as Hr | Hr; simplify_eq.
    + (* success *)
      iMod (ghost_var_update _ S2 with "[$Hauth2][$]") as "[Hauth2 Hfrag2]".
      iMod ("Hclose" with "[$Hauth1 $Hauth2 Hr Hres Hα]") as "_".
      { destruct s1; by iFrame. }
      iModIntro. wp_pures.
      clear.
      awp_apply (rand_tape_spec_some).
      iInv "Hinv" as ">(%s1&%s2&Hauth1&Hauth2&%Hc1&Hr&Hres&Hα)".
      iDestruct (ghost_var_agree with "[$Hauth2][$]") as "->".
      replace (tape_elem _ _) with [1%nat]; last first.
      { by destruct s1. }
      iAaccIntro with "Hα".
      { iFrame.
        iIntros. iModIntro.
        iNext. iFrame. iSplit; first done.
        by destruct s1.
      }
      iIntros "Hα".
      iMod (ghost_var_update _ S3 with "[$Hauth2][$]") as "[Hauth2 Hfrag2]".
      iFrame. iModIntro. iSplitL "Hα".
      { destruct s1; by iFrame. }
      clear.
      iInv "Hinv" as ">(%s1&%s2&Hauth1&Hauth2&%Hc1&Hr&Hres&Hα)" "Hclose".
      iDestruct (ghost_var_agree with "[$Hauth2][$]") as "->".
      wp_store.
      iMod (ghost_var_update _ S4 with "[$Hauth2][$]") as "[Hauth2 Hfrag2]".
      iMod ("Hclose" with "[$Hauth1 $Hauth2 Hr Hres Hα]") as "_".
      { iFrame. destruct s1; by iFrame. }
      by iFrame.
    + iMod (ghost_var_update _ S5 with "[$Hauth2][$]") as "[Hauth2 Hfrag2]".
      iMod ("Hclose" with "[$Hauth1 $Hauth2 Hr Hres Hα]") as "_".
      { destruct s1; by iFrame. }
      iModIntro.
      wp_pures.
      by iFrame.
  - iIntros (??)  "[Hfrag1 Hfrag2]".
    iNext.
    wp_pures.
    iInv "Hinv" as ">(%s1&%s2&Hauth1&Hauth2&%Hc1&Hr&Hres&Hα)" "Hclose".
    iDestruct "Hfrag1" as "[Hfrag1|Hfrag1]";
        iDestruct "Hfrag2" as "[Hfrag2|Hfrag2]";
        iDestruct (ghost_var_agree with "[$Hauth1][$]") as "->";
      iDestruct (ghost_var_agree with "[$Hauth2][$]") as "->"; try done;
      wp_load; iMod ("Hclose" with "[$]") as "_"; by iApply "HΦ".
  Qed.
End race.
