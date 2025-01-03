From iris.algebra Require Import excl_auth cmra.
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

(* Inductive ra_state:= *)
(* |Start *)
(* |Final *)
(* |Invalid. *)

(* Section ra_state. *)
(*   Global Instance ra_state_equiv_instance: Equiv ra_state :=eq. *)
(*   Global Instance ra_state_equiv_equivalence : Equivalence (≡@{ra_state}) := _. *)
(*   Global Instance ra_state_leibniz_equiv : LeibnizEquiv ra_state := _. *)
(*   Canonical ra_stateO := Ofe ra_state (discrete_ofe_mixin _). *)
(*   Local Instance ra_state_op_instance : Op ra_state := λ s1 s2, *)
(*                                                    match s1, s2 with *)
(*                                                    | Final, Final => Final *)
(*                                                    | _, _ => Invalid *)
(*                                                    end. *)

(*   Local Instance ra_state_pcore_instance : PCore ra_state := λ s, *)
(*                                                          match s with *)
(*                                                          | Start => None *)
(*                                                          | _ => Some s *)
(*                                                          end. *)

(*   Local Instance ra_state_valid_instance : Valid ra_state := λ s, *)
(*                                                          match s with *)
(*                                                          | Start | Final => True *)
(*                                                          | Invalid => False *)
(*                                                          end. *)
  
(*   Lemma ra_state_ra_mixin : RAMixin ra_state. *)
(*   Proof. *)
(*     split. *)
(*     - solve_proper. *)
(*     - naive_solver. *)
(*     - solve_proper. *)
(*     - by intros [] [] []. *)
(*     - by intros [] []. *)
(*     - by intros [] []. *)
(*     - by intros [] []. *)
(*     - intros [] _ [] [[] ->] e; try done. *)
(*       all: eexists; split; first done. *)
(*       all: try by exists Invalid. *)
(*                     by exists Final. *)
(*                          - by intros [] []. *)
(*   Qed. *)
(*   Canonical Structure ra_stateR := discreteR ra_state ra_state_ra_mixin. *)

(*   Global Instance ra_state_cmra_discrete : CmraDiscrete ra_state. *)
(*   Proof. apply discrete_cmra_discrete. Qed. *)

(* End ra_state. *)

(* Global Instance Start_exclusive : Exclusive Start. *)
(* Proof. by intros []. Qed. *)

(* Global Instance Final_core_id : CoreId Final. *)
(* Proof. red. done. Qed. *)

(* Lemma ra_state_update s : s ~~> Final. *)
(* Proof. *)
(*   rewrite cmra_discrete_update. *)
(*   intros mz H. *)
(*   by destruct s, mz as [[| |]|]. *)
(* Qed. *)

(* Section properties. *)
(*   Context `{!inG Σ ra_stateR}. *)
  
(* Lemma alloc_Start : ⊢ |==> ∃ γ, own γ Start. *)
(* Proof. *)
(*   iApply own_alloc. *)
(*   done. *)
(* Qed. *)

(* Lemma ra_state_valid γ (s : ra_state) : own γ s ⊢ ⌜✓ s⌝. *)
(* Proof. *)
(*   iIntros "H". *)
(*   iPoseProof (own_valid with "H") as "%H". *)
(*   done. *)
(* Qed. *)

(* Lemma ra_state_bupd γ (s : ra_state) : own γ s ==∗ own γ Final. *)
(* Proof. *)
(*   iApply own_update. *)
(*   apply ra_state_update. *)
(* Qed. *)

(* Lemma ra_state_contradict γ : own γ Start -∗ own γ Final -∗ False. *)
(* Proof. *)
(*   iIntros "H1 H2". *)
(*   iCombine "H1 H2" gives "%K"; by cbv in K. *)
(* Qed. *)

(* Lemma ra_state_final γ s: own γ Final -∗ own γ s -∗ ⌜s=Final⌝. *)
(* Proof. *)
(*   iIntros "H1 H2". *)
(*   destruct s; [|done|]. *)
(*   all: iCombine "H1 H2" gives "%K"; by cbv in K. *)
(* Qed. *)
  
(* End properties. *)

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

Section complex'.
  Context `{!conerisGS Σ, !spawnG Σ, !inG Σ (excl_authR (option natO)), !inG Σ (excl_authR (boolO))}.

  Definition one_positive n1 n2:=
    match (n1, n2) with
    | (Some (S _), _) | (_, Some (S _)) => true
    | _ => false
    end.

  Definition added_1 s n:=
    match (s, n) with
    | (true, Some (S _)) | (true, None)=> true
    | _ => false
    end.

  Definition parallel_add_inv' (γ1 γ2 γ3 γ4: gname) l: iProp Σ :=
    ∃ (n1 n2 : option nat) (n:nat) s1 s2,
      let p:= one_positive n1 n2 in
      own γ1 (●E n1) ∗ own γ2 (●E n2) ∗
      l↦#n ∗
      own γ3 (●E s1) ∗ own γ4 (●E s2) ∗
      (if (added_1 s1 n1 || added_1 s2 n2) then ⌜(0<n)%nat⌝ else True) ∗
      if p
      then ↯ 0%R
      else
        ∃ (flip_num:nat),
          ↯ (Rpower 6%R (INR flip_num-2))%R ∗
          ⌜(flip_num = bool_to_nat (bool_decide (n1=Some 0%nat)) +bool_to_nat (bool_decide (n2=Some 0%nat)))%nat⌝.
  
  Lemma complex_parallel_add_spec':
    {{{ ↯ (1/36) }}}
      two_die_prog'
      {{{ (n:nat), RET #n; ⌜(0<n)%nat⌝ }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    iMod (ghost_var_alloc None) as (γ1) "[Hauth1 Hfrag1]".
    iMod (ghost_var_alloc None) as (γ2) "[Hauth2 Hfrag2]".
    iMod (ghost_var_alloc' false) as (γ1') "[Hauth1' Hfrag1']".
    iMod (ghost_var_alloc' false) as (γ2') "[Hauth2' Hfrag2']".
    rewrite /two_die_prog'.
    wp_alloc l as "Hl".
    wp_pures.
    iMod (inv_alloc nroot _ (parallel_add_inv' γ1 γ2 γ1' γ2' l) with "[Hauth1 Hauth2 Herr Hauth1' Hauth2' Hl]") as "#I".
    { iNext.
      iFrame.
      simpl.
      iExists 0%nat. iFrame.
      iSplit; first done.
      iExists _. iSplit; last done.
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
    wp_apply (wp_par (λ _, ∃ (n:nat), own γ1 (◯E (Some n)) ∗ own γ1' (◯E true))%I
                (λ _, ∃ (n:nat), own γ2 (◯E (Some n)) ∗ own γ2' (◯E true))%I with "[Hfrag1 Hfrag1'][Hfrag2 Hfrag2']").
    - wp_bind (rand _)%E.
      iInv "I" as ">(%&%&%n&%s1&%s2&Hauth1&Hauth2&Hl&Hra1&Hra2&H&Herr)" "Hclose".
      iDestruct (ghost_var_agree with "[$Hauth1][$]") as "->".
      destruct (one_positive _ _) eqn:H1.
      + wp_apply (wp_rand with "[//]") as (x) "_".
        iMod (ghost_var_update _ (Some (fin_to_nat x)) with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
        destruct n2 as [[|n2]|]; simplify_eq.
        iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hra1 $Hra2 $Hl H Herr]") as "_".
        { iNext.
          case_match eqn:H2.
          - rewrite orb_true_iff in H2. destruct H2 as [H2|H2].
            + destruct s1; simplify_eq.
              case_match; (iSplit; first done); by destruct x.
            + rewrite H2. rewrite orb_true_r. iSplit; first done.
              by destruct x.
          - rewrite orb_false_iff in H2. destruct H2 as [H2 ->].
            rewrite orb_false_r.
            case_match; last (iSplit; first done); first destruct s1; simplify_eq.
            by destruct x.
        }
        iModIntro.
        wp_pures.
        clear n n2 H1 s1 s2.
        case_bool_decide as H2; wp_pures.
        * iInv "I" as ">(%&%&%n&%s1&%s2&Hauth1&Hauth2&Hl&Hra1&Hra2&H&Herr)" "Hclose".
          iDestruct (ghost_var_agree with "[$Hauth1][$]") as "->".
          wp_faa.
          iMod (ghost_var_update' _ true with "[$Hra1][$]") as "[Hra1 Hfrag1']".
          iMod ("Hclose" with "[$Hauth1 $Hauth2 Hl Hra1 $Hra2 H Herr]") as "_".
          { iExists (n+1)%nat. iFrame. rewrite Nat2Z.inj_add. iFrame.
            iNext. destruct (added_1 true _||_); last done.
            iPureIntro. lia.
          }
          by iFrame.
        * iInv "I" as ">(%&%&%n&%s1&%s2&Hauth1&Hauth2&Hl&Hra1&Hra2&H&Herr)" "Hclose".
          iDestruct (ghost_var_agree with "[$Hauth1][$]") as "->".
          iMod (ghost_var_update' _ true with "[$Hra1][$]") as "[Hra1 Hfrag1']".
          iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hl $Hra1 $Hra2 H $Herr]") as "_".
          { iNext.
            case_match eqn :H1; first by case_match.
            case_match eqn:H3; last done.
            assert (fin_to_nat x=0)%nat as K by lia.
            rewrite K in H1 H3.
            destruct s1, s2, n2 as [[|]|]; simplify_eq. 
          }
          by iFrame.
      + iDestruct "Herr" as "(%&Herr&->)".
        simpl.
        wp_apply (wp_couple_rand_adv_comp1' _ _ _ _
                    (λ x, if bool_decide(fin_to_nat x = 0)%nat
                          then (Rpower 6 (bool_to_nat (bool_decide (n2 = Some 0%nat)) - 2 +1))
                          else 0)%R with "[$]") as (x) "Herr".
        { intros. case_match; last done.
          rewrite /Rpower.
          apply Rlt_le, exp_pos.
        }
        { rewrite SeriesC_finite_foldr. simpl.
          rewrite Rpower_plus Rpower_1; lra.
        }
        iMod (ghost_var_update _ (Some (fin_to_nat x)) with "[$Hauth1][$]") as "[Hauth1 Hfrag1]".
        iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hra1 $Hra2 $Hl H Herr]") as "_".
        { iNext.
          iSplitL "H".
          - case_match eqn:H2; first by case_match.
            case_match eqn:H3; last done.
            destruct s1, s2, (fin_to_nat x), n2 as [[|]|]; simplify_eq.
          - case_bool_decide as K.
            + case_match.
              * iApply (ec_weaken with "[$]").
                split; first done.
                rewrite /Rpower.
                apply Rlt_le, exp_pos.
              * rewrite K. simpl.
                iExists _; iSplit; last done. rewrite S_INR.
                iApply (ec_eq with "[$]"). f_equal. lra.
            + case_match; first done.
              destruct (fin_to_nat x); simplify_eq.
        }
        iModIntro.
        wp_pures.
        clear n n2 H1 s1 s2.
        case_bool_decide as H2; wp_pures.
        * iInv "I" as ">(%&%&%n&%s1&%s2&Hauth1&Hauth2&Hl&Hra1&Hra2&H&Herr)" "Hclose".
          iDestruct (ghost_var_agree with "[$Hauth1][$]") as "->".
          wp_faa.
          iMod (ghost_var_update' _ true with "[$Hra1][$]") as "[Hra1 Hfrag1']".
          iMod ("Hclose" with "[$Hauth1 $Hauth2 Hl $Hra1 $Hra2 H Herr]") as "_".
          { iExists (n+1)%nat. iFrame. rewrite Nat2Z.inj_add. iFrame.
            iNext. destruct (added_1 true _||_); last done.
            iPureIntro. lia.
          }
          by iFrame.
        * iInv "I" as ">(%&%&%n&%s1&%s2&Hauth1&Hauth2&Hl&Hra1&Hra2&H&Herr)" "Hclose".
          iDestruct (ghost_var_agree with "[$Hauth1][$]") as "->".
          iMod (ghost_var_update' _ true with "[$Hra1][$]") as "[Hra1 Hfrag1']".
          iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hl $Hra1 $Hra2 H $Herr]") as "_".
          { iNext.
            case_match eqn :H1; first by case_match.
            case_match eqn:H3; last done.
            assert (fin_to_nat x=0)%nat as K by lia.
            rewrite K in H1 H3.
            destruct s1, s2, n2 as [[|]|]; simplify_eq. 
          }
          by iFrame.
    - wp_bind (rand _)%E.
      iInv "I" as ">(%&%&%n&%s1&%s2&Hauth1&Hauth2&Hl&Hra1&Hra2&H&Herr)" "Hclose".
      iDestruct (ghost_var_agree with "[$Hauth2][$]") as "->".
      destruct (one_positive _ _) eqn:H1.
      + wp_apply (wp_rand with "[//]") as (x) "_".
        iMod (ghost_var_update _ (Some (fin_to_nat x)) with "[$Hauth2][$]") as "[Hauth2 Hfrag2]".
        destruct n1 as [[|n1]|]; simplify_eq.
        iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hra1 $Hra2 $Hl H Herr]") as "_".
        { iNext.
          case_match eqn:H2.
          - rewrite orb_true_iff in H2. destruct H2 as [H2|H2].
            + destruct s1; simplify_eq.
              case_match; (iSplit; first done); by destruct x.
            + iSplitL "H"; first by case_match.
              by simpl.
          - rewrite orb_false_iff in H2. destruct H2 as [-> H2].
            rewrite orb_false_l.
            case_match; last (iSplit; first done); first destruct s2; simplify_eq.
            by destruct x.
        }
        iModIntro.
        wp_pures.
        clear n n1 H1 s1 s2.
        case_bool_decide as H2; wp_pures.
        * iInv "I" as ">(%&%&%n&%s1&%s2&Hauth1&Hauth2&Hl&Hra1&Hra2&H&Herr)" "Hclose".
          iDestruct (ghost_var_agree with "[$Hauth2][$]") as "->".
          wp_faa.
          iMod (ghost_var_update' _ true with "[$Hra2][$]") as "[Hra2 Hfrag2']".
          iMod ("Hclose" with "[$Hauth1 $Hauth2 Hl $Hra2 $Hra1 H Herr]") as "_".
          { iExists (n+1)%nat. iFrame. rewrite Nat2Z.inj_add. iFrame.
            iNext. destruct (_||added_1 true _); last done.
            iPureIntro. lia.
          }
          by iFrame.
        * iInv "I" as ">(%&%&%n&%s1&%s2&Hauth1&Hauth2&Hl&Hra1&Hra2&H&Herr)" "Hclose".
          iDestruct (ghost_var_agree with "[$Hauth2][$]") as "->".
          iMod (ghost_var_update' _ true with "[$Hra2][$]") as "[Hra2 Hfrag2']".
          iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hl $Hra2 $Hra1 H $Herr]") as "_".
          { iNext.
            case_match eqn :H1; first by case_match.
            case_match eqn:H3; last done.
            assert (fin_to_nat x=0)%nat as K by lia.
            rewrite K in H1 H3.
            destruct s1, s2, n1 as [[|]|]; simplify_eq. 
          }
          by iFrame.
      + iDestruct "Herr" as "(%&Herr&->)".
        simpl.
        wp_apply (wp_couple_rand_adv_comp1' _ _ _ _
                    (λ x, if bool_decide(fin_to_nat x = 0)%nat
                          then (Rpower 6 (bool_to_nat (bool_decide (n1 = Some 0%nat)) - 2 +1))
                          else 0)%R with "[$]") as (x) "Herr".
        { intros. case_match; last done.
          rewrite /Rpower.
          apply Rlt_le, exp_pos.
        }
        { rewrite SeriesC_finite_foldr. simpl.
          rewrite -plus_n_O Rpower_plus Rpower_1; lra. 
        }
        iMod (ghost_var_update _ (Some (fin_to_nat x)) with "[$Hauth2][$]") as "[Hauth2 Hfrag2]".
        iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hra1 $Hra2 $Hl H Herr]") as "_".
        { iNext.
          iSplitL "H".
          - case_match eqn:H2; first by case_match.
            case_match eqn:H3; last done.
            destruct s1, s2, (fin_to_nat x), n1 as [[|]|]; simplify_eq.
          - case_bool_decide as K.
            + case_match.
              * iApply (ec_weaken with "[$]").
                split; first done.
                rewrite /Rpower.
                apply Rlt_le, exp_pos.
              * rewrite K. simpl.
                iExists _; iSplit; last done. rewrite plus_INR. 
                iApply (ec_eq with "[$]"). f_equal. simpl. lra.
            + case_match; first done.
              destruct n1 as [[|]|], (fin_to_nat x); simplify_eq.
        }
        iModIntro.
        wp_pures.
        clear n n1 H1 s1 s2.
        case_bool_decide as H2; wp_pures.
        * iInv "I" as ">(%&%&%n&%s1&%s2&Hauth1&Hauth2&Hl&Hra1&Hra2&H&Herr)" "Hclose".
          iDestruct (ghost_var_agree with "[$Hauth2][$]") as "->".
          wp_faa.
          iMod (ghost_var_update' _ true with "[$Hra2][$]") as "[Hra2 Hfrag2']".
          iMod ("Hclose" with "[$Hauth1 $Hauth2 Hl $Hra1 $Hra2 H Herr]") as "_".
          { iExists (n+1)%nat. iFrame. rewrite Nat2Z.inj_add. iFrame.
            iNext. destruct (_||added_1 true _); last done.
            iPureIntro. lia.
          }
          by iFrame.
        * iInv "I" as ">(%&%&%n&%s1&%s2&Hauth1&Hauth2&Hl&Hra1&Hra2&H&Herr)" "Hclose".
          iDestruct (ghost_var_agree with "[$Hauth2][$]") as "->".
          iMod (ghost_var_update' _ true with "[$Hra2][$]") as "[Hra2 Hfrag2']".
          iMod ("Hclose" with "[$Hauth1 $Hauth2 $Hl $Hra1 $Hra2 H $Herr]") as "_".
          { iNext.
            case_match eqn :H1; first by case_match.
            case_match eqn:H3; last done.
            assert (fin_to_nat x=0)%nat as K by lia.
            rewrite K in H1 H3.
            destruct s1, s2, n1 as [[|]|]; simplify_eq. 
          }
          by iFrame.
    - iIntros (??) "[(%n1&Hfrag1&Hfrag1') (%n2&Hfrag2&Hfrag2')]".
      iNext.
      wp_pures.
      iInv "I" as ">(%&%&%n&%s1&%s2&Hauth1&Hauth2&Hl&Hra1&Hra2&H&Herr)" "Hclose".
      iDestruct (ghost_var_agree with "[$Hauth1][$]") as "->".
      iDestruct (ghost_var_agree with "[$Hauth2][$]") as "->".
      iDestruct (ghost_var_agree' with "[$Hra1][$]") as "->".
      iDestruct (ghost_var_agree' with "[$Hra2][$]") as "->".
      wp_load.
      iAssert (⌜(0<n)%nat⌝)%I as "%".
      + destruct n1, n2; simpl; try done.
        iDestruct "Herr" as "(%&Herr&->)".
        iDestruct (ec_contradict with "[$]") as "[]".
        simpl.
        replace (_-_)%R with 0%R by lra.
        rewrite Rpower_O; lra.
      + iMod ("Hclose" with "[$]") as "_".
        iApply "HΦ".
        by iPureIntro.
  Qed.
End complex'.
