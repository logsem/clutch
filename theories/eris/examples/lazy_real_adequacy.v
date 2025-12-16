From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen Continuity.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real real_decr_trial.
From clutch.eris.examples Require Import math.
Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(* We prove the simple adequacy statement of samplers e that returns a distribution of lazy reals *)
(* we compare to see whether the lazy real <= (x)/(2^y) *)
(* We have the inequality (x)<2^y *)
Definition pow2 : val :=
  rec: "pow2" "y":=
    if: "y"≤#0%nat then #(1%nat) else #2 * ("pow2" ("y"-#1)).

Definition is_zero : val :=
  (rec: "f" "α" "l" :=
     let, ("z", "l'") := get_chunk "α" "l" in
     if: "z" = #0 then "f" "α" "l'" else #false)%V.

Definition is_smaller_prog_aux : val :=
  (rec: "f" "α" "l" "x" "y" :=
     if: "y"=#0 then is_zero "α" "l"
     else
       let, ("z", "l'") := get_chunk "α" "l" in
       let: "y'" := "y" - #1 in 
       let: "p" := pow2 "y'" in
       if: "x"<"p"
       then (* first digit of (x)/(2^y) is 0*)
         if: "z"=#1 then #false
         else "f" "α" "l'" "x" "y'"
       else (* first digit of (x)/(2^y) is 1*)
         if: "z"=#0 then #true
         else "f" "α" "l'" ("x"-"p") "y'"
  )%V.

Definition is_smaller_prog : val :=
  λ: "p" "n" "x" "y",
    let, ("l","k") := "p" in
    if: "k"< "n" then #true
    else if: "n"<"k" then #false 
         else let, ("α", "l'") := "l" in
              is_smaller_prog_aux "α" "l'" "x" "y" 
.

Local Lemma ineq_lemma (x y:nat): (x<2^y)%nat -> 0<=x/2^y <1.
Proof.
  split.
  - apply Rcomplements.Rdiv_le_0_compat.
    + apply pos_INR.
    + apply pow_lt. lra. 
  - rewrite -Rcomplements.Rdiv_lt_1; last (apply pow_lt; lra).
    replace 2 with (INR 2) by done.
    rewrite -pow_INR.
    apply lt_INR. lia.
Qed.

(* move this lemma? *)
Lemma seq_bin_to_R_0 f :
  seq_bin_to_R f = 0 ->
  ∀ x : nat, f x = 0%fin.
Proof.
  intros H.
  apply Classical_Pred_Type.not_ex_not_all.
  intros [n Hcontra].
  assert (f n =1%fin) as H0. 
  { inv_fin (f n); first done.
    intros i; inv_fin i; first done. intros i; inv_fin i.
  }
  assert (0<seq_bin_to_R f); last lra.
  rewrite /seq_bin_to_R.
  apply Rlt_le_trans with (SeriesC (λ n0 : nat, if bool_decide (n0 = n) then f n0 * (1 / 2 ^ S n0) else 0)).
  - rewrite SeriesC_singleton_dependent.
    rewrite H0.
    simpl.
    rewrite Rmult_1_l.
    apply Rdiv_lt_0_compat; first lra.
    apply Rmult_lt_0_compat; first lra.
    apply pow_lt. lra.
  - apply SeriesC_filter_leq.
    + intros n'.
      apply Rmult_le_pos.
      * inv_fin (f n'); first done.
        (intros i; inv_fin i); first (simpl; lra).
        intros i; inv_fin i.
      * apply Rcomplements.Rdiv_le_0_compat; first lra.
        apply pow_lt. lra.
    + eapply ex_seriesC_le; last apply ex_seriesC_seq_bin_to_R_ub.
      intros n'.
      split.
      * apply Rmult_le_pos.
        -- inv_fin (f n'); first done.
           (intros i; inv_fin i); first (simpl; lra).
           intros i; inv_fin i.
        -- apply Rcomplements.Rdiv_le_0_compat; first lra.
           apply pow_lt. lra.
      * assert (f n'<=1); last real_solver.
        inv_fin (f n'); first (simpl; lra).
        intros i; inv_fin i; first done.
        intros i; inv_fin i.
Qed. 

Section adequacy.
  Context `{!erisGS Σ}.
  
  Lemma wp_pow2 (n:nat):
    {{{ True }}}
      pow2 #n
      {{{(x:nat), RET (#x); ⌜x = (2^n)%nat⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iLöb as "IH" forall (Φ n).
    rewrite /pow2.
    wp_pures. rewrite -/pow2.
    case_bool_decide; wp_pures.
    - iModIntro. iApply "HΦ".
      assert (n = 0)%nat by lia.
      simplify_eq. done.
    - replace (Z.of_nat n - 1)%Z with (Z.of_nat (n-1)); last first.
      + rewrite Nat2Z.inj_sub; first lia.
        destruct n; last lia. done.
      + wp_apply ("IH").
        iIntros (x) "%".
        wp_pures.
        iModIntro.
        replace (_*_)%Z with (Z.of_nat (2*x)); last first.
        * rewrite Nat2Z.inj_mul. f_equal.
        * iApply "HΦ". iPureIntro. subst.
          rewrite -PeanoNat.Nat.pow_succ_r'. f_equal.
          destruct n; try done. lia.
  Qed.

  Lemma wp_e1 x y μ e (n:nat):
    (∀ x, 0<=μ x)->
    (∀ r, 0<=r -> ex_RInt μ (0) r) →
    ex_RInt_gen μ (at_point 0) (Rbar_locally Rbar.p_infty) →
    (x<2^y)%nat ->
    (∀ (F : R -> R), (⌜∃ M, ∀ x , 0 <= F x <= M⌝) -∗
                    (⌜(IPCts F)⌝) -∗
       ↯ (RInt_gen (fun (x:R) => μ x * F x) (at_point 0) (Rbar_locally Rbar.p_infty) )%R -∗
       WP e {{ vp, ∃ (r : R) (k:nat) (l:val),  ⌜vp=(l, #k)%V⌝ ∗ lazy_real l r ∗ ↯(F (r+k)%R) }}) -∗
    ↯ (RInt_gen μ (at_point (x / 2 ^ y + INR n)) (Rbar_locally Rbar.p_infty)) -∗
    WP e {{ vp, ∃ (r : R) (k:nat) (l:val),  ⌜vp=(l, #k)%V⌝ ∗ lazy_real l r ∗
                                          ↯(Iverson (λ r', (x/2^y)+n<r') (r+k)%R) }}.
  Proof.
    iIntros (Hpos Hex Hex' Hineq) "Hwp Herr".
    iApply "Hwp".
    - iPureIntro.
      exists 1. intros; rewrite /Iverson; case_match; lra.
    - iPureIntro.
      rewrite /IPCts.
      remember (x/2^y+n) as k.
      exists (λ r, if bool_decide (k<r) then 1 else
                if bool_decide (k-1<r) then (r-(k-1)) else 0
        ).
      exists (((λ r, k-1-r), k-1, k)::nil).
      repeat split.
      + simpl. rewrite /Icc/Iverson/Rmin/Rmax.
        intros. repeat (case_bool_decide||case_match); lra.
      + apply Forall_singleton.
        intros ??.
        apply: continuous_minus; last apply continuous_id.
        apply continuous_const.
      + intros ??[eps Heps].
        exists eps.
        intros.
        apply Heps.
        clear -H.
        revert H.
        rewrite /ball//=/AbsRing_ball/abs/=.
        intros H%Rabs_def2.
        rewrite /minus/plus/opp/= in H *.
        apply Rabs_def1; repeat case_bool_decide; lra.
    - iApply (ec_eq with "[$]").
      (* erewrite RInt_sep. *)
      erewrite <-(RInt_gen_Chasles _ (x/2^y+n)(Fa := (at_point 0))); last first.
      + eapply (ex_RInt_gen_ext_eq_Ioi (f:=μ)).
        * intros. rewrite Iverson_True; [lra|done].
        * eapply ex_RInt_gen_Chasles_exists; first done.
          rewrite ex_RInt_gen_at_point.
          apply Hex.
          apply Rplus_le_le_0_compat; last apply pos_INR.
          apply Rcomplements.Rdiv_le_0_compat; first apply pos_INR.
          apply pow_lt. lra.
      + apply ex_RInt_gen_at_point.
        eapply (ex_RInt_ext (λ _, 0)).
        * intros ? [H' H].
          rewrite Iverson_False; first lra.
          apply Rlt_asym.
          rewrite /Rmax in H.
          rewrite /Rmin in H'.
          case_match; first lra.
          exfalso.
          assert (0<=x/2^y+n); last lra.
          apply Rplus_le_le_0_compat; last apply pos_INR.
          apply ineq_lemma. lia.
        * apply ex_RInt_const.
      + rewrite RInt_gen_at_point.
        * erewrite (RInt_gen_ext_eq_Ioi (g:= μ) (f:=λ x, μ x*_)%R ).
          -- replace (RInt _ _ _) with 0; first by rewrite plus_zero_l.
             symmetry.
             erewrite (RInt_ext _ (λ _, 0)).
             ++ rewrite RInt_const. by rewrite scal_zero_r.
             ++ intros ? H.
                rewrite Iverson_False; first lra.
                rewrite /Rmin/Rmax in H.
                case_match; try lra.
                assert (0<=x/2^y+n); last lra.
                apply Rplus_le_le_0_compat; last apply pos_INR.
                apply Rcomplements.Rdiv_le_0_compat; last apply pow_lt; last lra.
                apply pos_INR.
          -- intros. rewrite Iverson_True; [lra|done].
          -- eapply (ex_RInt_gen_ext_eq_Ioi (f:=μ)).
             ++ intros. rewrite Iverson_True; [lra|done].
             ++ eapply ex_RInt_gen_Chasles_exists; first done.
                rewrite ex_RInt_gen_at_point.
                apply Hex.
                apply Rplus_le_le_0_compat; last apply pos_INR.
                apply Rcomplements.Rdiv_le_0_compat; first apply pos_INR.
                apply pow_lt. lra.
        * eapply ex_RInt_ext; last apply ex_RInt_const.
          simpl.
          intros.
          rewrite Iverson_False; first by rewrite Rmult_0_r.
          rewrite /Rmax in H.
          rewrite /Rmin in H.
          repeat case_match; try lra.
          exfalso.
          assert (0<=x/2^y+n); last lra.
          apply Rplus_le_le_0_compat; last apply pos_INR.
          apply Rcomplements.Rdiv_le_0_compat; first apply pos_INR.
          apply pow_lt. lra.
  Qed.

  Lemma wp_e2 x y μ e (n:nat):
    (∀ x, 0<=μ x)->
    (∀ r, 0<=r -> ex_RInt μ (0) r) →
    ex_RInt_gen μ (at_point 0) (Rbar_locally Rbar.p_infty) →
    (x<2^y)%nat ->
    (∀ (F : R -> R), (⌜∃ M, ∀ x , 0 <= F x <= M⌝) -∗
                    (⌜(IPCts F)⌝) -∗
       ↯ (RInt_gen (fun (x:R) => μ x * F x) (at_point 0) (Rbar_locally Rbar.p_infty) )%R -∗
       WP e {{ vp, ∃ (r : R) (k:nat) (l:val),  ⌜vp=(l, #k)%V⌝ ∗ lazy_real l r ∗ ↯(F (r+k)%R) }}) -∗
    ↯ (RInt μ 0 (x / 2 ^ y + INR n)) -∗
    WP e {{ vp, ∃ (r : R) (k:nat) (l:val),  ⌜vp=(l, #k)%V⌝ ∗ lazy_real l r ∗
                                          ↯(Iverson (λ r', r'<= (x/2^y)+n) (r+k)%R) }}.
  Proof.
    iIntros (Hpos Hex Hex' Hineq) "Hwp Herr".
    iApply "Hwp".
    - iPureIntro.
      exists 1. intros; rewrite /Iverson; case_match; lra.
    - iPureIntro.
      rewrite /IPCts.
      remember (x/2^y+n) as k.
      exists (λ r, if bool_decide (r<=k-1) then 1 else
                if bool_decide (r<=k) then (1-(r-k+1)) else 0
        ).
      exists (((λ r, r-(k-1)), k-1, k)::nil).
      repeat split.
      + simpl. rewrite /Icc/Iverson/Rmin/Rmax.
        intros. repeat (case_bool_decide||case_match); lra.
      + apply Forall_singleton.
        intros ??.
        apply: continuous_minus; first apply continuous_id.
        apply continuous_const.
      + intros ??[eps Heps].
        exists eps.
        intros.
        apply Heps.
        clear -H.
        revert H.
        rewrite /ball//=/AbsRing_ball/abs/=.
        intros H%Rabs_def2.
        rewrite /minus/plus/opp/= in H *.
        apply Rabs_def1; repeat case_bool_decide; lra.
    - iApply (ec_eq with "[$]").
      (* erewrite RInt_sep. *)
      erewrite <-(RInt_gen_Chasles _ (x/2^y+n)(Fa := (at_point 0))); last first.
      + eapply (ex_RInt_gen_ext_eq_Ioi (f:=(λ _, 0))).
        * intros. rewrite Iverson_False; lra. 
        * admit.
      + apply ex_RInt_gen_at_point.
        eapply (ex_RInt_ext μ).
        * intros ? [H' H].
          rewrite Iverson_True; first lra.
          unfold Rmax in *.
          case_match; try lra.
          trans 0; first lra.
          apply Rplus_le_le_0_compat; last apply pos_INR.
          apply ineq_lemma. lia.
        * apply Hex.
          apply Rplus_le_le_0_compat; last apply pos_INR.
          apply ineq_lemma. lia.
      + rewrite RInt_gen_at_point; last first.
        * apply ex_RInt_ext with μ; last apply Hex; last first.
          -- apply Rplus_le_le_0_compat; last apply pos_INR.
             apply ineq_lemma. lia.
          -- rewrite /Rmin/Rmax.
             intros. rewrite Iverson_True; first lra.
             assert (0<=x / 2 ^ y + n); last (case_match; lra).
             apply Rplus_le_le_0_compat; last apply pos_INR.
             apply ineq_lemma. lia.
        * erewrite (RInt_gen_ext_eq_Ioi (g:= λ _, 0) (f:=λ x, μ x*_)%R ); last first.
          -- eapply (ex_RInt_gen_ext_eq_Ioi (f:=(λ _, 0))).
             ++ intros. rewrite Iverson_False; lra. 
             ++ admit.
          -- intros. rewrite Iverson_False; lra.
          -- erewrite (RInt_ext (λ _,_*_) μ); last first.
             ++ rewrite /Rmin/Rmax.
                intros.
                rewrite Iverson_True; first lra.
                case_match; try lra.
                assert (0<=x / 2 ^ y + n); last (lra).
                apply Rplus_le_le_0_compat; last apply pos_INR.
                apply ineq_lemma. lia.
             ++ admit.
  Admitted. 

  Lemma wp_is_zero1 α l f:
    seq_bin_to_R f = 0 ->
    chunk_and_tape_seq α l f -∗
    WP is_zero #lbl:α #l {{ v, ⌜v = #true⌝ }}.
  Proof.
    iLöb as "IH" forall (f α l).
    iIntros (Hzero) "H".
    rewrite /is_zero.
    wp_pures.
    pose proof seq_bin_to_R_0 _ Hzero as H.
    destruct (bin_seq_hd f) as [hd [f' ->]].
    wp_apply (wp_get_chunk_cons with "[$]").
    iIntros (?) "[??]".
    rewrite -/is_zero.
    wp_pures.
    rewrite bool_decide_eq_true_2; last first.
    { specialize (H 0%nat).
      simpl in *. by subst. 
    }
    wp_pures.
    iApply "IH"; last done.
    iPureIntro.
    rewrite seq_bin_to_R_cons in Hzero.
    specialize (H 0%nat).
    simpl in *. subst.
    replace (_/_) with 0 in Hzero; last (simpl; lra).
    rewrite Rplus_0_l in Hzero.
    lra.
  Qed.
  
  Lemma wp_is_zero2 α l f:
    seq_bin_to_R f ≠ 0 ->
    chunk_and_tape_seq α l f -∗
    WP is_zero #lbl:α #l {{ v, ⌜v = #false⌝ }}.
  Proof.
    iLöb as "IH" forall (f α l).
    iIntros (Hzero) "H".
    rewrite /is_zero.
    wp_pures.
    destruct (bin_seq_hd f) as [hd [f' ->]].
    wp_apply (wp_get_chunk_cons with "[$]").
    iIntros (?) "[??]".
    rewrite -/is_zero.
    wp_pures.
    case_bool_decide; last by wp_pures.
    wp_pures.
    iApply ("IH" with "[][$]").
    iPureIntro.
    intros Hcontra.
    assert (hd = 0%fin) as ->.
    { simplify_eq. apply fin_to_nat_inj. simpl. lia. }
    rewrite seq_bin_to_R_cons in Hzero.
    rewrite Hcontra in Hzero. simpl in *. lra.
  Qed.
  
  Lemma wp_is_smaller_prog_aux1 (x y:nat) f α l:
    (x<2^y)%nat -> 
    seq_bin_to_R f <= x/2^y ->
    chunk_and_tape_seq α l f -∗
    WP is_smaller_prog_aux #lbl:α #l #x #y  {{ v, ⌜v = #true⌝ }}.
  Proof.
    iLöb as "IH" forall (x y f α l).
    iIntros (Hineq Hineq') "H".
    rewrite /is_smaller_prog_aux.
    wp_pures.
    case_bool_decide.
    { simplify_eq.
      wp_pures.
      assert (y = 0)%nat as -> by lia.
      simpl in *.
      assert (x=0)%nat as -> by lia.
      simpl in *.
      pose proof seq_bin_to_R_range f as Hrange.
      assert (seq_bin_to_R f=0) by lra.
      by wp_apply wp_is_zero1.
    }
    wp_pure.
    destruct (bin_seq_hd f) as [hd [f' ->]].
    wp_apply (wp_get_chunk_cons with "[$]").
    iIntros (?) "[H1 H2]".
    wp_pures.
    destruct y as [|y']; first done.
    replace (Z.of_nat (S y') - 1)%Z with (Z.of_nat (y')); last lia.
    wp_apply (wp_pow2 with "[//][-]").
    iNext.
    iIntros (? ->).
    wp_pures.
    rewrite -/is_smaller_prog_aux.
    rewrite seq_bin_to_R_cons in Hineq'.
    case_bool_decide.
    - (* First digit of RHS is a 0*)
      assert (hd = 0%fin) as ->.
      { inv_fin hd; first done.
        intros i; inv_fin i; last (intros i; inv_fin i).
        pose proof seq_bin_to_R_range f'.
        intros Hcontra.
        simpl in *.
        assert (1 / 2   <= x / (2 * 2 ^ y')) as H2; first lra.
        rewrite Rcomplements.Rle_div_l in H2; last lra.
        rewrite -Rmult_div_swap in H2.
        rewrite -Rcomplements.Rle_div_r in H2; last first.
        - apply Rlt_gt.
          apply Rmult_lt_0_compat; first lra.
          apply pow_lt. lra.
        - rewrite Rmult_1_l in H2.
          replace 2 with (INR 2) in H2 by done.
          rewrite -pow_INR -!mult_INR in H2.
          apply INR_le in H2.
          lia. }
      wp_pures.
      wp_pures.
      iApply "IH"; last done.
      + iPureIntro. simpl in Hineq.
        lia.
      + iPureIntro.
        assert (seq_bin_to_R f' / 2 * 2 <= (x / 2 ^ S y')*2) as H'.
        { apply Rmult_le_compat_r; first lra. simpl in *; lra. }
        rewrite -Rmult_div_swap in H'.
        rewrite Rmult_div_l in H'; last done.
        etrans; first exact.
        right.
        simpl.
        rewrite Rdiv_mult_distr.
        replace (x / 2 / 2 ^ y' * 2 ) with (x / 2 ^ y' * 2/2 ) by lra.
        by rewrite Rmult_div_l.
    - (* Second digit of RHS is a 1*)
      wp_pures.
      case_bool_decide; first by wp_pures.
      assert (hd = 1%fin) as ->.
      { inv_fin hd; first done.
        intros i; inv_fin i; first done.
        intros i; inv_fin i.
      }
      wp_pures.
      rewrite -Nat2Z.inj_sub; last lia.
      iApply ("IH" with "[][][$]").
      + iPureIntro.
        simpl in *. lia.
      + iPureIntro. simpl in *.
        assert (seq_bin_to_R f'  <= 2*(x / (2 * 2 ^ y') - 1/2)) by lra.
        etrans; first exact.
        rewrite -Rcomplements.Rle_div_r; last (apply pow_lt; lra).
        replace 2 with (INR 2) by done.
        rewrite (Rmult_comm (INR 2) (_^_)).
        rewrite Rdiv_mult_distr.
        rewrite Rmult_minus_distr_l.
        rewrite !Rmult_div_assoc.
        rewrite !Rmult_div_r; last (simpl; lra).
        replace (INR 2 * INR x / INR 2 ^ y' / INR 2) with ((INR 2 / INR 2)*INR x / INR 2 ^ y') by lra.
        rewrite Rdiv_diag; last (simpl; lra).
        rewrite Rmult_1_l.
        rewrite Rmult_minus_distr_r.
        rewrite Rmult_1_l.
        rewrite -Rmult_div_swap.
        rewrite Rmult_div_l; last first.
        { unshelve epose proof pow_lt (INR 2) y' _; simpl in *; lra. }
        rewrite -pow_INR.
        rewrite -minus_INR; last lia.
        apply le_INR. lia.
  Qed.

  Lemma wp_is_smaller_prog_aux2 (x y:nat) f α l:
    (x<2^y)%nat -> 
    x/2^y < seq_bin_to_R f ->
    chunk_and_tape_seq α l f -∗
    WP is_smaller_prog_aux #lbl:α #l #x #y  {{ v, ⌜v = #false⌝ }}.
  Proof.
    iLöb as "IH" forall (x y f α l).
    iIntros (Hineq Hineq') "H".
    rewrite /is_smaller_prog_aux.
    wp_pures.
    case_bool_decide.
    { wp_pures.
      wp_apply wp_is_zero2; last done.
      pose proof ineq_lemma _ _ Hineq. lra.
    }
    wp_pure.
    destruct (bin_seq_hd f) as [hd [f' ->]].
    wp_apply (wp_get_chunk_cons with "[$]").
    iIntros (?) "[H1 H2]".
    wp_pures.
    destruct y as [|y']; first done.
    replace (Z.of_nat (S y') - 1)%Z with (Z.of_nat (y')); last lia.
    wp_apply (wp_pow2 with "[//][-]").
    iNext.
    iIntros (? ->).
    wp_pures.
    rewrite -/is_smaller_prog_aux.
    rewrite seq_bin_to_R_cons in Hineq'.
    case_bool_decide.
    - (* First digit of RHS is a 0*)
      wp_pures.
      case_bool_decide; first by wp_pures.
      assert (hd = 0%fin) as ->.
      { inv_fin hd; first done.
        intros i; inv_fin i; first done.
        intros i; inv_fin i.
      }
      wp_pures.
      iApply ("IH" with "[][][$]"); iPureIntro; first lia.
      simpl in *.
      assert (x / (2* 2 ^ y') < seq_bin_to_R f' / 2) as K; first lra.
      rewrite Rdiv_mult_distr in K.
      rewrite (Rdiv_def x) (Rdiv_def (seq_bin_to_R _)) in K.
      assert (x / (2 ^ y')*/2 < seq_bin_to_R f'* / 2) as K'; first lra.
      apply Rmult_lt_reg_r in K'; first done.
      apply pos_half_prf.
    - (* Second digit of RHS is a 1*)
      wp_pures.
      pose proof ineq_lemma _ _ Hineq as Hineq''.
      case_bool_decide.
      + assert (hd = 0%fin) as ->.
        { inv_fin hd; first done.
          intros i; inv_fin i; first done.
          intros i; inv_fin i.
        }
        wp_pures.
        exfalso.
        simpl in *.
        assert (seq_bin_to_R f' / 2 <= x / (2 * 2 ^ y')); last lra.
        rewrite Rdiv_mult_distr.
        rewrite (Rdiv_def) (Rdiv_def x).
        assert (seq_bin_to_R f' * / 2 <= (x / 2 ^ y') * / 2 ); last lra.
        apply Rmult_le_compat_r; first (left; apply pos_half_prf).
        pose proof seq_bin_to_R_range f'.
        assert (1<=x/2^y'); last lra.
        apply Rcomplements.Rle_div_r; first (apply pow_lt; lra).
        rewrite Rmult_1_l.
        replace 2 with (INR 2) by done.
        rewrite -pow_INR. apply le_INR.
        lia.
      + wp_pures.
        rewrite -Nat2Z.inj_sub; last lia.
        iApply ("IH" with "[][][$]"); iPureIntro.
        * simpl in *. lia.
        * assert (hd=1%fin) as ->.
          { inv_fin hd; first done.
            intros i; inv_fin i; first done.
            intros i; inv_fin i.
          }
          simpl in *.
          rewrite Rplus_comm in Hineq'.
          apply Rcomplements.Rlt_minus_l in Hineq'.
          apply Rcomplements.Rlt_div_r in Hineq'; last lra.
          eapply Rle_lt_trans; last exact.
          replace ((x / (2 * 2 ^ y') - 1 / 2) * 2) with (x/(2*2^y')*2-1) by lra.
          rewrite Rdiv_mult_distr.
          replace (_/_/_*_) with (x/2^y'*2/2) by lra.
          rewrite Rmult_div_l; last done.
          rewrite minus_INR; last lia.
          rewrite Rdiv_minus_distr.
          rewrite pow_INR. replace (INR 2) with 2 by done.
          rewrite Rdiv_diag; first done.
          by apply pow_nonzero.
  Qed. 
  
  Lemma wp_is_smaller_prog1 n x y μ e:
    (∀ x, 0<=μ x)->
    (∀ r, 0<=r -> ex_RInt μ (0) r) →
    ex_RInt_gen μ (at_point 0) (Rbar_locally Rbar.p_infty) →
    (x<2^y)%nat ->
    (∀ (F : R -> R), (⌜∃ M, ∀ x , 0 <= F x <= M⌝) -∗(⌜IPCts F⌝) -∗
       ↯ (RInt_gen (fun (x:R) => μ x * F x) (at_point 0) (Rbar_locally Rbar.p_infty) )%R -∗
       WP e {{ vp, ∃ (r : R) (k:nat) (l:val),  ⌜vp=(l, #k)%V⌝ ∗ lazy_real l r ∗ ↯(F (r+k)%R) }}) -∗
    ↯ (RInt_gen μ (at_point (x / 2 ^ y + INR n)) (Rbar_locally Rbar.p_infty)) -∗
    WP is_smaller_prog e #n #x #y {{ v, ⌜v = #true⌝ }}.
  Proof.
    iIntros (Hpos Hex Hex' Hineq) "Hwp Herr".
    rewrite /is_smaller_prog.
    wp_bind e.
    wp_apply (pgl_wp_wand with "[-]"); first by iApply (wp_e1 with "[Hwp][$]").
    simpl.
    iIntros (?) "(%r&%k&%&->&Hl&Herr)".
    rewrite /lazy_real.
    iDestruct "Hl" as "(%&%&%f&->&->&H)".
    wp_pures.
    pose proof seq_bin_to_R_range f.
    case_bool_decide; first by wp_pures.
    wp_pures.
    case_bool_decide.
    { iDestruct (ec_contradict with "[$]") as "[]".
      rewrite Iverson_True; first done.
      assert ( x / 2 ^ y + n <  k); last lra.
      rewrite -Rcomplements.Rlt_minus_r.
      rewrite -minus_INR; last lia.
      apply Rlt_le_trans with (1).
      - by apply ineq_lemma.
      - replace 1 with (INR 1) by done.
        apply le_INR. lia.
    }
    wp_pures.
    rewrite /Iverson.
    case_match; first by iDestruct (ec_contradict with "[$]") as "[]".
    wp_apply wp_is_smaller_prog_aux1; try done.
    assert (n=k)%nat as -> by lia.
    lra.
  Qed.

  Lemma wp_is_smaller_prog2 n x y μ e:
    (∀ x, 0<=μ x)->
    (∀ r, 0<=r -> ex_RInt μ (0) r) →
    ex_RInt_gen μ (at_point 0) (Rbar_locally Rbar.p_infty) →
    (x<2^y)%nat ->
    (∀ (F : R -> R), (⌜∃ M, ∀ x , 0 <= F x <= M⌝) -∗(⌜IPCts F⌝) -∗
       ↯ (RInt_gen (fun (x:R) => μ x * F x) (at_point 0) (Rbar_locally Rbar.p_infty) )%R -∗
       WP e {{ vp, ∃ (r : R) (k:nat) (l:val),  ⌜vp=(l, #k)%V⌝ ∗ lazy_real l r ∗ ↯(F (r+k)%R) }}) -∗
    ↯ (RInt μ 0 (x / 2 ^ y + INR n)) -∗
    WP is_smaller_prog e #n #x #y {{ v, ⌜v = #false⌝ }}.
  Proof.
    iIntros (Hpos Hex Hex' Hineq) "Hwp Herr".
    rewrite /is_smaller_prog.
    wp_bind e.
    wp_apply (pgl_wp_wand with "[-]"); first by iApply (wp_e2 with "[Hwp][$]").
    simpl.
    iIntros (?) "(%r&%k&%&->&Hl&Herr)".
    rewrite /lazy_real.
    iDestruct "Hl" as "(%&%&%f&->&->&H)".
    wp_pures.
    pose proof seq_bin_to_R_range f.
    pose proof ineq_lemma _ _ Hineq.
    case_bool_decide.
    { rewrite Iverson_True; first by iDestruct (ec_contradict with "[$]") as "[]".
      assert (seq_bin_to_R f + k <=  n); last lra.
      assert (1+k<=n); last lra.
      replace (1) with (INR 1) by done.
      rewrite -plus_INR.
      apply le_INR. lia.
    }
    wp_pures.
    case_bool_decide; first by wp_pures.
    wp_pures.
    assert (k=n) as -> by lia.
    wp_pures.
    rewrite /Iverson.
    case_match; first by iDestruct (ec_contradict with "[$]") as "[]".
    wp_apply wp_is_smaller_prog_aux2; try done.
    lra.
  Qed.
End adequacy.

Theorem lazy_real_adeqaucy1 Σ `{erisGpreS Σ} (e : expr) (σ : state) (μ : R -> R):
  (∀ x, 0<=μ x)->
    (∀ r, 0<=r -> ex_RInt μ (0) r) →
    ex_RInt_gen μ (at_point 0) (Rbar_locally Rbar.p_infty) →
  (∀ `{erisGS Σ} (F : R -> R) (Hnn : ∃ M, ∀ x , 0 <= F x <= M) (HPCts: IPCts F),
      ↯ (RInt_gen (fun (x:R) => μ x * F x) (at_point 0) (Rbar_locally Rbar.p_infty) )%R -∗
       WP e {{ vp, ∃ (r : R) (k:nat) (l:val),  ⌜vp=(l, #k)%V⌝ ∗ lazy_real l r ∗ ↯(F (r+k)%R) }}) →
  ∀ (x y n:nat), (x<2^y)%nat ->
  pgl (lim_exec (is_smaller_prog e #n #x #y, σ)) (λ x, x=#true) (RInt_gen μ (at_point (x / 2 ^ y + INR n)) (Rbar_locally Rbar.p_infty)).
Proof.
  intros Hpos Hbound Hbound' Hwp x y n Hineq.
  apply ineq_lemma in Hineq as Hineq'.
  eapply (wp_pgl_lim Σ).
  { 
    apply RInt_gen_pos_ex'.
    - done.
    - intros.
      eapply ex_RInt_Chasles; last apply Hbound.
      + apply ex_RInt_swap. apply Hbound.
        apply Rplus_le_le_0_compat; first naive_solver.
        apply pos_INR.
      + etrans; destruct Hineq'; first exact.
        etrans; last by left.
        apply Rplus_le_0_compat.
        apply pos_INR.
    - intros.
      apply RInt_ge_0; try done; first lra.
      eapply ex_RInt_Chasles; last apply Hbound.
      + apply ex_RInt_swap. apply Hbound.
        apply Rplus_le_le_0_compat; first naive_solver.
        apply pos_INR.
      + etrans; destruct Hineq'; first exact.
        etrans; last by left.
        apply Rplus_le_0_compat.
        apply pos_INR.
    - eapply ex_RInt_gen_Chasles_exists; first done.
      rewrite ex_RInt_gen_at_point.
      apply Hbound.
      apply Rplus_le_le_0_compat; first naive_solver.
      apply pos_INR.
  } 
  iIntros (?) "Herr".
  iPoseProof (wp_is_smaller_prog1 with "[][$]") as "$"; [done..|].
  iIntros (? H2 H3) "Herr".
  by iApply Hwp.
Qed. 

Theorem lazy_real_adeqaucy2 Σ `{erisGpreS Σ} (e : expr) (σ : state) (μ : R -> R):
  (∀ x, 0<=μ x)->
    (∀ r, 0<=r -> ex_RInt μ (0) r) →
    ex_RInt_gen μ (at_point 0) (Rbar_locally Rbar.p_infty) →
  (∀ `{erisGS Σ} (F : R -> R) (Hnn : ∃ M, ∀ x , 0 <= F x <= M) (HPCts: IPCts F),
      ↯ (RInt_gen (fun (x:R) => μ x * F x) (at_point 0) (Rbar_locally Rbar.p_infty) )%R -∗
       WP e {{ vp, ∃ (r : R) (k:nat) (l:val),  ⌜vp=(l, #k)%V⌝ ∗ lazy_real l r ∗ ↯(F (r+k)%R) }}) →
  ∀ (x y n:nat), (x<2^y)%nat ->
  pgl (lim_exec (is_smaller_prog e #n #x #y, σ)) (λ x, x=#false) (RInt μ 0 (x / 2 ^ y + INR n)).
Proof.
  intros Hpos Hbound Hbound' Hwp x y n Hineq.
  apply ineq_lemma in Hineq as Hineq'.
  eapply (wp_pgl_lim Σ).
  {
    apply RInt_ge_0.
    - apply Rplus_le_le_0_compat; first naive_solver.
      apply pos_INR.
    - apply Hbound.
      apply Rplus_le_le_0_compat; first naive_solver.
      apply pos_INR.
    - naive_solver.
  } 
  iIntros (?) "Herr".
  iPoseProof (wp_is_smaller_prog2 with "[][$]") as "$"; [done..|].
  iIntros (? H2 H3) "Herr".
  by iApply Hwp.
Qed. 
