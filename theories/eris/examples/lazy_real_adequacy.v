From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen Continuity.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real real_decr_trial lazy_real_expr.
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
    assert (0<=x / 2 ^ y + n) as K1.
    { apply Rplus_le_le_0_compat; last apply pos_INR.
      apply ineq_lemma. lia. }
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
        * apply ex_RInt_gen_0. 
      + apply ex_RInt_gen_at_point.
        eapply (ex_RInt_ext μ).
        * intros ? [H' H].
          rewrite Iverson_True; first lra.
          unfold Rmax in *.
          case_match; lra.
        * by apply Hex.
      + rewrite RInt_gen_at_point; last first.
        * apply ex_RInt_ext with μ; last by apply Hex; last first.
          -- rewrite /Rmin/Rmax.
             intros. rewrite Iverson_True; first lra. case_match; lra.
        * erewrite (RInt_gen_ext_eq_Ioi (g:= λ _, 0) (f:=λ x, μ x*_)%R ); last first.
          -- eapply (ex_RInt_gen_ext_eq_Ioi (f:=(λ _, 0))).
             ++ intros. rewrite Iverson_False; lra. 
             ++ apply ex_RInt_gen_0. 
          -- intros. rewrite Iverson_False; lra.
          -- erewrite (RInt_ext (λ _,_*_) μ); last first.
             ++ rewrite /Rmin/Rmax.
                intros.
                rewrite Iverson_True; first lra.
                case_match; lra.
             ++ rewrite RInt_gen_0.
                by rewrite plus_zero_r.
  Qed. 

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

Theorem lazy_real_adequacy1 Σ `{erisGpreS Σ} (e : expr) (σ : state) (μ : R -> R):
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

(**  For applying Gauss *)
Theorem lazy_real_adequacy1' Σ `{erisGpreS Σ} (e : expr) (σ : state) (μ : R -> R):
  IPCts μ ->
  (∀ x, 0<=μ x)->
    (∀ r, 0<=r -> ex_RInt μ (0) r) →
    ex_RInt_gen μ (at_point 0) (Rbar_locally Rbar.p_infty) →
  (∀ `{erisGS Σ} (F : nat -> R -> R) (Hnn : ∃ M, ∀ x k , 0 <= F k x <= M) (HPCts: ∀ k, PCts (F k) 0 1),
      ↯ (RInt_gen (fun (x:R) => μ x * F (Z.to_nat (Int_part x)) (frac_part x)) (at_point 0) (Rbar_locally Rbar.p_infty) )%R -∗
       WP e {{ vp, ∃ (r : R) (k:nat) (l:val),  ⌜vp=(l, #k)%V⌝ ∗ lazy_real l r ∗ ↯(F k (r)%R) }}) →
  ∀ (x y n:nat), (x<2^y)%nat ->
  pgl (lim_exec (is_smaller_prog e #n #x #y, σ)) (λ x, x=#true) (RInt_gen μ (at_point (x / 2 ^ y + INR n)) (Rbar_locally Rbar.p_infty)).
Proof.
  intros Hcts Hpos Hbound Hbound' Hwp x y n Hineq.
  apply: lazy_real_adequacy1; try done.
  iIntros (??[M ]?) "Herr".
  set (F':= (λ (k:nat) r, F (k+r))).
  iApply (pgl_wp_wand with "[-]").
  - iApply (Hwp _ F').
    + rewrite /F'.
      naive_solver.
    + intros k. by apply IPCts_PCts, IPCts_shift.
    + iApply (ec_eq with "[$]").
      apply RInt_gen_ext_eq_Ioi.
      * intros x0 ?. f_equal.
        rewrite /F'.
        f_equal.
        rewrite {1}(Rplus_Int_part_frac_part x0).
        f_equal.
        rewrite INR_IZR_INZ.
        rewrite Z2Nat.id; first done.
        pose proof base_Int_part x0 as [].
        assert (-1< IZR (Int_part x0)) as K by lra.
        assert (-1<Int_part x0)%Z; last lia.
        by apply lt_IZR.
      * eapply (@ex_RInt_gen_Ici_compare_IPCts 0 (λ x0 : R, M * μ x0)).
        -- by apply IPCts_scal_mult.
        -- by apply IPCts_mult.
        -- intros.
           split; first real_solver.
           rewrite Rmult_comm. real_solver.
        -- destruct Hbound' as [x0 Hbound'].
           apply (is_RInt_gen_scal _ M) in Hbound'.
           rewrite /scal/=/mult/= in Hbound'.
           by eexists _.
  - simpl. rewrite /F'. setoid_rewrite (Rplus_comm (INR _)).
    by iIntros.
Qed. 

Theorem lazy_real_adequacy2 Σ `{erisGpreS Σ} (e : expr) (σ : state) (μ : R -> R):
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

(**  For applying Gauss *)
Theorem lazy_real_adequacy2' Σ `{erisGpreS Σ} (e : expr) (σ : state) (μ : R -> R):
  IPCts μ ->
  (∀ x, 0<=μ x)->
    (∀ r, 0<=r -> ex_RInt μ (0) r) →
    ex_RInt_gen μ (at_point 0) (Rbar_locally Rbar.p_infty) →
  (∀ `{erisGS Σ} (F : nat -> R -> R) (Hnn : ∃ M, ∀ x k , 0 <= F k x <= M) (HPCts: ∀ k, PCts (F k) 0 1),
      ↯ (RInt_gen (fun (x:R) => μ x * F (Z.to_nat $ Int_part x) (frac_part x)) (at_point 0) (Rbar_locally Rbar.p_infty) )%R -∗
       WP e {{ vp, ∃ (r : R) (k:nat) (l:val),  ⌜vp=(l, #k)%V⌝ ∗ lazy_real l r ∗ ↯(F k (r)%R) }}) →
  ∀ (x y n:nat), (x<2^y)%nat ->
  pgl (lim_exec (is_smaller_prog e #n #x #y, σ)) (λ x, x=#false) (RInt μ 0 (x / 2 ^ y + INR n)).
Proof.
  intros Hcts Hpos Hbound Hbound' Hwp x y n Hineq.
  apply: lazy_real_adequacy2; try done.
  iIntros (??[M ]?) "Herr".
  set (F':= (λ (k:nat) r, F (k+r))).
  iApply (pgl_wp_wand with "[-]").
  - iApply (Hwp _ F').
    + rewrite /F'.
      naive_solver.
    + intros k. by apply IPCts_PCts, IPCts_shift.
    + iApply (ec_eq with "[$]").
      apply RInt_gen_ext_eq_Ioi.
      * intros x0 ?. f_equal.
        rewrite /F'.
        f_equal.
        rewrite {1}(Rplus_Int_part_frac_part x0).
        f_equal.
        rewrite INR_IZR_INZ.
        rewrite Z2Nat.id; first done.
        pose proof base_Int_part x0 as [].
        assert (-1< IZR (Int_part x0)) as K by lra.
        assert (-1<Int_part x0)%Z; last lia.
        by apply lt_IZR.
      * eapply (@ex_RInt_gen_Ici_compare_IPCts 0 (λ x0 : R, M * μ x0)).
        -- by apply IPCts_scal_mult.
        -- by apply IPCts_mult.
        -- intros.
           split; first real_solver.
           rewrite Rmult_comm. real_solver.
        -- destruct Hbound' as [x0 Hbound'].
           apply (is_RInt_gen_scal _ M) in Hbound'.
           rewrite /scal/=/mult/= in Hbound'.
           by eexists _.
  - simpl. rewrite /F'. setoid_rewrite (Rplus_comm (INR _)).
    by iIntros.
Qed. 

Section CReal.

Definition lazy_real_cdf_checker (sampler : expr) (B C : Z) : expr :=
  let: "sample" := sampler in
  let: "num" := R_ofZ #B in
  let: "bound" := R_mulPow "num" #C in
  R_cmp "sample" "bound" #0%nat.


Theorem RInt_gen_ex_pos {μ X} (HC : IPCts μ)
    (Hhi : ex_RInt_gen μ (at_point 0) (Rbar_locally Rbar.p_infty)) :
    ex_RInt_gen μ (at_point X) (Rbar_locally Rbar.p_infty).
Proof.
  apply (@ex_RInt_gen_Chasles_exists _ 0); OK.
  rewrite ex_RInt_gen_at_point.
  by apply IPCts_RInt.
Qed.

Theorem RInt_gen_ex_neg {μ X}
    (HC : IPCts μ)
    (Hlo : ex_RInt_gen μ (Rbar_locally Rbar.m_infty) (at_point 0)) :
    ex_RInt_gen μ (Rbar_locally Rbar.m_infty) (at_point X).
Proof.
  apply (@ex_RInt_gen_Chasles_exists_neg _ _ 0); OK.
  rewrite ex_RInt_gen_at_point.
  by apply IPCts_RInt.
Qed.

Theorem IPCts_Ici {X} : IPCts (Iverson (Ici X)).
Proof.
  destruct (IPCts_Ioi X) as [F [L [H1 [H2 H3]]]].
  exists F.
  exists (((fun _ : R => 1), X, X) :: L).
  split; [|split].
  { intros x.
    rewrite fmap_cons fsum_cons.
    rewrite (Rplus_comm _ (fsum _ _)) -Rplus_assoc.
    rewrite -H1.
    rewrite /IntervalFun_R.
    rewrite /Iverson.
    rewrite /Ici/Ioi/Icc//=.
    rewrite Rmin_left; OK.
    rewrite Rmax_right; OK.
    case_decide; case_decide; case_decide; OK.
  }
  { apply Forall_cons.
    split; OK.
    rewrite /IntervalFun_continuity.
    intros ??.
    apply continuous_const.
  }
  { done. }
Qed.


Theorem IPCts_Iic {X} : IPCts (Iverson (Iic X)).
Proof.
  destruct (IPCts_Iio X) as [F [L [H1 [H2 H3]]]].
  exists F.
  exists (((fun _ : R => 1), X, X) :: L).
  split; [|split].
  { intros x.
    rewrite fmap_cons fsum_cons.
    rewrite (Rplus_comm _ (fsum _ _)) -Rplus_assoc.
    rewrite -H1.
    rewrite /IntervalFun_R.
    rewrite /Iverson.
    rewrite /Iic/Iio/Icc//=.
    rewrite Rmin_left; OK.
    rewrite Rmax_right; OK.
    case_decide; case_decide; case_decide; OK.
  }
  { apply Forall_cons.
    split; OK.
    rewrite /IntervalFun_continuity.
    intros ??.
    apply continuous_const.
  }
  { done. }
Qed.

Theorem RInt_gen_split_pos {μ X}
    (HC : IPCts μ)
    (Hlo : ex_RInt_gen μ (Rbar_locally Rbar.m_infty) (at_point 0))
    (Hhi : ex_RInt_gen μ (at_point 0) (Rbar_locally Rbar.p_infty)) :
  RInt_gen μ (at_point X) (Rbar_locally Rbar.p_infty) =
  RInt_gen (λ x : R, μ x * Iverson (Ici X) x) (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty).
Proof.
  rewrite
    -(@RInt_gen_Chasles R_CompleteNormedModule (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty) _ _
        (λ x : R, μ x * Iverson (Ici X) x) X); first last.
  { apply (@ex_RInt_gen_ext_eq_Ioi μ).
    { intros ??.
      rewrite Iverson_True; OK.
      rewrite /Ici//=. OK.
    }
    apply RInt_gen_ex_pos; OK.
  }
  { apply (@ex_RInt_gen_ext_eq_Iio (fun _ => 0)).
    { intros ??.
      rewrite Iverson_False; OK.
      rewrite /Ici//=. OK.
    }
    apply RInt_gen_ex_neg.
    { apply IPCts_cts. intros ?. apply continuous_const. }
    apply (@ex_RInt_gen_neg_change_of_var_rev (λ _ : R, 0)).
    { intros ??.
      apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
      intros ??.
      apply continuous_const.
    }
    apply ex_RInt_gen_0.
  }
  rewrite /plus//=.
  replace (RInt_gen (λ x : R, μ x * Iverson (Ici X) x) (at_point X) (Rbar_locally Rbar.p_infty))
     with (RInt_gen μ (at_point X) (Rbar_locally Rbar.p_infty)).
  2: {
   apply (@RInt_gen_ext_eq_Ioi μ).
   { intros ??.
     rewrite Iverson_True; OK.
     rewrite /Ici//=. OK.
   }
   apply RInt_gen_ex_pos; OK.
  }
  replace (RInt_gen (λ x : R, μ x * Iverson (Ici X) x) (Rbar_locally Rbar.m_infty) (at_point X))
     with (0).
  2: {
    rewrite (@RInt_gen_ext_eq_Iio _ (fun _ => 0)).
    { symmetry.
      replace X with (- -X) by OK.
      rewrite -(@RInt_gen_shift_neg (fun _ => 0) (-X)); first last.
      { apply RInt_gen_ex_neg.
        { apply IPCts_cts. intros ?. apply continuous_const. }
        apply (@ex_RInt_gen_neg_change_of_var_rev (λ _ : R, 0)).
        { intros ??.
          apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
          intros ??.
          apply continuous_const.
        }
        apply ex_RInt_gen_0.
      }
      { intros ?.
        apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros ??.
        apply continuous_const.
      }
      rewrite -RInt_gen_neg_change_of_var.
      { by rewrite RInt_gen_0. }
      { intros ??.
        apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros ??.
        apply continuous_const.
      }
      { intros ??.
        apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros ??.
        apply continuous_const.
      }
      { apply RInt_gen_ex_neg.
        { apply IPCts_cts. intros ?. apply continuous_const. }
        apply (@ex_RInt_gen_neg_change_of_var_rev (λ _ : R, 0)).
        { intros ??.
          apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
          intros ??.
          apply continuous_const.
        }
        apply ex_RInt_gen_0.
      }
    }
    { intros ??.
      rewrite Iverson_False; OK.
      rewrite /Ici//=. OK.
    }
    apply (@ex_RInt_gen_ext_eq_Iio (fun _ => 0)).
    { intros ??.
      rewrite Iverson_False; OK.
      rewrite /Ici//=. OK.
    }
    apply RInt_gen_ex_neg.
    { apply IPCts_cts. intros ?. apply continuous_const. }
    apply (@ex_RInt_gen_neg_change_of_var_rev (λ _ : R, 0)).
    { intros ??.
      apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
      intros ??.
      apply continuous_const.
    }
    apply ex_RInt_gen_0.
  }
  OK.
Qed.

Theorem RInt_gen_split_neg {μ X}
    (HC : IPCts μ)
    (Hlo : ex_RInt_gen μ (Rbar_locally Rbar.m_infty) (at_point 0))
    (Hhi : ex_RInt_gen μ (at_point 0) (Rbar_locally Rbar.p_infty)) :
  RInt_gen μ (Rbar_locally Rbar.m_infty) (at_point X) =
  RInt_gen (λ x : R, μ x * Iverson (Iic X) x) (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty).
Proof.
  rewrite
    -(@RInt_gen_Chasles R_CompleteNormedModule (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty) _ _
        (λ x : R, μ x * Iverson (Iic X) x) X); first last.
  { apply (@ex_RInt_gen_ext_eq_Ioi (fun _ => 0)).
    { intros ??.
      rewrite Iverson_False; OK.
      rewrite /Iic//=. OK.
    }
    apply ex_RInt_gen_0.
  }
  { apply (@ex_RInt_gen_ext_eq_Iio μ).
    { intros ??.
      rewrite Iverson_True; OK.
      rewrite /Iic//=. OK.
    }
    apply RInt_gen_ex_neg; OK.
  }
  rewrite /plus//=.
  replace (RInt_gen (λ x : R, μ x * Iverson (Iic X) x) (at_point X) (Rbar_locally Rbar.p_infty))
     with (0).
  2: {
    rewrite (@RInt_gen_ext_eq_Ioi _ (fun _ => 0)).
    { by rewrite RInt_gen_0. }
    { intros ??.
      rewrite Iverson_False; OK.
      rewrite /Iic//=; OK.
    }
    apply (@ex_RInt_gen_ext_eq_Ioi (fun _ => 0)).
    { intros ??.
      rewrite Iverson_False; OK.
      rewrite /Iic//=; OK.
    }
    apply ex_RInt_gen_0.
  }
  replace (RInt_gen (λ x : R, μ x * Iverson (Iic X) x) (Rbar_locally Rbar.m_infty) (at_point X))
     with (RInt_gen μ (Rbar_locally Rbar.m_infty) (at_point X)).
  2: {
   apply (@RInt_gen_ext_eq_Iio μ).
   { intros ??.
     rewrite Iverson_True; OK.
     rewrite /Iic//=. OK.
   }
   apply RInt_gen_ex_neg; OK.
  }
  OK.
Qed.




(* The checker program will observe that a sample is less than B*2^C, with error ∫_(B*2^C)^∞ μ(x) dx *)
Theorem lazy_real_expr_adequacy_below Σ `{erisGpreS Σ} {M} (e : expr) (σ : state) (μ : R -> R)
    (Hnn : ∀ x, 0 <= μ x <= M) (HC : IPCts μ)
    (Hlo : ex_RInt_gen μ (Rbar_locally Rbar.m_infty) (at_point 0))
    (Hhi : ex_RInt_gen μ (at_point 0) (Rbar_locally Rbar.p_infty))
    (Hspec :
      ∀ `{erisGS Σ} E (F : R -> R) (Hnn : ∃ M, ∀ x , 0 <= F x <= M) (HPC : IPCts F),
      ↯ (RInt_gen (fun (x : R) => μ x * F x) (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty))%R -∗
       WP e @ E {{ cont, ∃ r, IsApprox cont r E ∗ ↯(F r) }}) :
    ∀ B C : Z,
      pgl
        (lim_exec (lazy_real_cdf_checker e B C, σ))
        (fun x => x = #(-1)%Z)
        (RInt_gen μ (at_point (IZR B / powerRZ 2 C)) (Rbar_locally Rbar.p_infty)).
Proof.
  intros B C.
  apply (wp_pgl_lim Σ).
  { apply RInt_gen_pos_strong.
    { apply Hnn. }
    { intros ?. by apply IPCts_RInt. }
    { intros ??.
      apply RInt_ge_0; OK.
      { by apply IPCts_RInt. }
      intros ??.
      apply Hnn.
    }
    { by apply RInt_gen_ex_pos. }
  }
  iIntros (?) "He".
  rewrite /lazy_real_cdf_checker.
  wp_pures.
  wp_bind e.
  iApply pgl_wp_mono.
  2: {
    iApply (@Hspec _ _ (Iverson (Ici (IZR B / powerRZ 2 C)))).
    { exists 1. intros ?. split; [apply Iverson_nonneg|apply Iverson_le_1]. }
    { apply IPCts_Ici. }
    { iApply (ec_eq with "He").
      rewrite //=.
      by apply RInt_gen_split_pos.
    }
  }
  rewrite //=.
  iIntros (sample) "[%r HI]".
  remember (IsApprox sample r ⊤ ∗ ↯ (Iverson (Ici (IZR B / powerRZ 2 C)) r))%I as Hcrs.
  wp_pures.
  wp_bind (R_ofZ _).
  iApply (pgl_wp_mono_frame Hcrs with "[] HI").
  2: { wp_apply wp_R_ofZ. }
  rewrite //=.
  iIntros (num) "[HI Hnum]".
  wp_pures.
  wp_bind (R_mulPow _ _).
  iApply (pgl_wp_mono_frame Hcrs with "[Hnum] HI").
  2: { wp_apply (wp_R_mulPow with "Hnum"). }
  rewrite //=.
  iIntros (bound) "[HI Hbound]".
  rewrite HeqHcrs.
  iDestruct "HI" as "[Hsample He]".
  rewrite /Iverson//=.
  case_decide.
  { iExFalso. by iApply (ec_contradict with "He"). }
  wp_pures.
  iApply pgl_wp_mono.
  2: {
    iApply (@wp_R_cmp_lt _ _ sample bound r (IZR B / powerRZ 2 C)).
    2:{ iFrame. }
    rewrite /Ici in H1.
    OK.
  }
  rewrite //=.
  iIntros (?) "(?&?)".
  iFrame.
Qed.

(* The checker program will observe that a sample is above B*2^C, with error ∫_(-∞)^(B*2^C) μ(x) dx *)
(* TODO: Is this necessary? *)
Theorem lazy_real_expr_adequacy_above Σ `{erisGpreS Σ} {M} (e : expr) (σ : state) (μ : R -> R)
    (Hnn : ∀ x, 0 <= μ x <= M) (HC : IPCts μ)
    (Hlo : ex_RInt_gen μ (Rbar_locally Rbar.m_infty) (at_point 0))
    (Hhi : ex_RInt_gen μ (at_point 0) (Rbar_locally Rbar.p_infty))
    (Hspec :
      ∀ `{erisGS Σ} E (F : R -> R) (Hnn : ∃ M, ∀ x , 0 <= F x <= M) (HPC : IPCts F),
      ↯ (RInt_gen (fun (x : R) => μ x * F x) (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty))%R -∗
       WP e @ E {{ cont, ∃ r, IsApprox cont r E ∗ ↯(F r) }}) :
    ∀ B C : Z,
      pgl
        (lim_exec (lazy_real_cdf_checker e B C, σ))
        (fun x => x = #(1)%Z)
        (RInt_gen μ (Rbar_locally Rbar.m_infty) (at_point (IZR B / powerRZ 2 C))).
Proof.
  intros B C.
  apply (wp_pgl_lim Σ).
  { apply RInt_gen_pos_strong_neg.
    { apply Hnn. }
    { intros ?. by apply IPCts_RInt. }
    { intros ??.
      apply RInt_ge_0; OK.
      { by apply IPCts_RInt. }
      intros ??.
      apply Hnn.
    }
    { by apply RInt_gen_ex_neg. }
  }
  iIntros (?) "He".
  rewrite /lazy_real_cdf_checker.
  wp_pures.
  wp_bind e.
  iApply pgl_wp_mono.
  2: {
    iApply (@Hspec _ _ (Iverson (Iic (IZR B / powerRZ 2 C)))).
    { exists 1. intros ?. split; [apply Iverson_nonneg|apply Iverson_le_1]. }
    { apply IPCts_Iic. }
    { iApply (ec_eq with "He").
      rewrite //=.
      by apply RInt_gen_split_neg.
    }
  }
  rewrite //=.
  iIntros (sample) "[%r HI]".
  remember (IsApprox sample r ⊤ ∗ ↯ (Iverson (Iic (IZR B / powerRZ 2 C)) r))%I as Hcrs.
  wp_pures.
  wp_bind (R_ofZ _).
  iApply (pgl_wp_mono_frame Hcrs with "[] HI").
  2: { wp_apply wp_R_ofZ. }
  rewrite //=.
  iIntros (num) "[HI Hnum]".
  wp_pures.
  wp_bind (R_mulPow _ _).
  iApply (pgl_wp_mono_frame Hcrs with "[Hnum] HI").
  2: { wp_apply (wp_R_mulPow with "Hnum"). }
  rewrite //=.
  iIntros (bound) "[HI Hbound]".
  rewrite HeqHcrs.
  iDestruct "HI" as "[Hsample He]".
  rewrite /Iverson//=.
  case_decide.
  { iExFalso. by iApply (ec_contradict with "He"). }
  wp_pures.
  iApply pgl_wp_mono.
  2: {
    iApply (@wp_R_cmp_gt _ _ sample bound r (IZR B / powerRZ 2 C)).
    2:{ iFrame. }
    rewrite /Iic in H1.
    OK.
  }
  rewrite //=.
  iIntros (?) "(?&?)".
  iFrame.
Qed.

Lemma IPCts_poke1 {A B C} : IPCts (poke (fun _ => A) B C).
Proof.
  exists (fun _ => A), (List.cons ((fun _ => C - A), B, B) List.nil).
  split; [|split].
  { intros ?.
    rewrite /poke/fsum//=/Iverson/Icc//=.
    rewrite Rmin_left; OK.
    rewrite Rmax_right; OK.
    case_decide.
    { rewrite decide_True; OK. }
    { rewrite decide_False; OK. }
  }
  { rewrite Forall_singleton.
    intros ??.
    apply continuous_const.
  }
  { intros ?.
    apply continuous_const.
  }
Qed.

Theorem lazy_real_expr_adequacy_mass Σ `{erisGpreS Σ} {M} (e : expr) (σ : state) (μ : R -> R)
    (Hnn : ∀ x, 0 <= μ x <= M) (HC : IPCts μ)
    (Hlo : ex_RInt_gen μ (Rbar_locally Rbar.m_infty) (at_point 0))
    (Hhi : ex_RInt_gen μ (at_point 0) (Rbar_locally Rbar.p_infty))
    (Hspec :
      ∀ `{erisGS Σ} E (F : R -> R) (Hnn : ∃ M, ∀ x , 0 <= F x <= M) (HPC : IPCts F),
      ↯ (RInt_gen (fun (x : R) => μ x * F x) (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty))%R -∗
       WP e @ E {{ cont, ∃ r, IsApprox cont r E ∗ ↯(F r) }})
    (Hmass : RInt_gen μ (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty) <= 1) :
    ∀ B C : Z,
     prob (lim_exec (lazy_real_cdf_checker e B C, σ)) (fun x => negb (bool_decide (x = #(1)%Z \/ x = #(-1)%Z))) <=
       1 - RInt_gen μ (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty).
Proof.
  intros ??.
  suffices HS :
      pgl
        (lim_exec (lazy_real_cdf_checker e B C, σ))
        (fun x => x = #(1)%Z \/ x = #(-1)%Z)
        (1 - RInt_gen μ (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty)).
  { rewrite /pgl in HS.
    etrans; last eapply HS.
    right.
    f_equal.
    funexti.
    f_equal.
    case_bool_decide.
    { rewrite bool_decide_true; OK. }
    { rewrite bool_decide_false; OK. }
  }
  apply (wp_pgl_lim Σ).
  { lra. }
  iIntros (?) "He".
  rewrite /lazy_real_cdf_checker.
  wp_pures.
  wp_bind e.
  iApply pgl_wp_mono.
  2: {
    iApply (@Hspec _ _ (poke (fun _ => 0) (IZR B / powerRZ 2 C) 1)).
    { exists 1. intros ?. rewrite /poke. case_decide; OK. }
    { apply IPCts_poke1. }
    { (* The integral is zero *)
      replace (RInt_gen (λ x0 : R, μ x0 * poke (λ _ : R, 0) (IZR B / powerRZ 2 C) 1 x0) (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty))
          with 0.
      { iApply (ec_weaken with "He"). split; OK. }
      erewrite <-(RInt_gen_Chasles _ (IZR B / powerRZ 2 C) (Fa := (Rbar_locally Rbar.m_infty))); last first.
      { apply (@ex_RInt_gen_ext_eq_Ioi (fun _ => 0)).
        { intros ??. rewrite /poke. rewrite decide_False; OK. }
        apply ex_RInt_gen_0.
      }
      { apply (@ex_RInt_gen_ext_eq_Iio (fun _ => 0)).
        { intros ??. rewrite /poke. rewrite decide_False; OK. }
        replace (IZR B / powerRZ 2 C) with (- (- (IZR B / powerRZ 2 C))) by OK.
        apply (ex_RInt_gen_shift_neg (F := fun _ => 0)).
        { intros ?. apply @ex_RInt_const. }
        apply (ex_RInt_gen_neg_change_of_var_rev (F := fun _ => 0)).
        { intros ??. apply @ex_RInt_const. }
        apply ex_RInt_gen_0.
      }
      rewrite /plus//=.
      rewrite (RInt_gen_ext_eq_Ioi (g := fun _ => 0)); first last.
      { apply (@ex_RInt_gen_ext_eq_Ioi (fun _ => 0)).
        { intros ??. rewrite /poke. rewrite decide_False; OK. }
        apply ex_RInt_gen_0.
      }
      { intros ??. rewrite /poke. rewrite decide_False; OK. }
      rewrite (RInt_gen_ext_eq_Iio (g := fun _ => 0)); first last.
      { apply (@ex_RInt_gen_ext_eq_Iio (fun _ => 0)).
        { intros ??. rewrite /poke. rewrite decide_False; OK. }
        replace (IZR B / powerRZ 2 C) with (- (- (IZR B / powerRZ 2 C))) by OK.
        apply (ex_RInt_gen_shift_neg (F := fun _ => 0)).
        { intros ?. apply @ex_RInt_const. }
        apply (ex_RInt_gen_neg_change_of_var_rev (F := fun _ => 0)).
        { intros ??. apply @ex_RInt_const. }
        apply ex_RInt_gen_0.
      }
      { intros ??. rewrite /poke. rewrite decide_False; OK. }
      rewrite RInt_gen_0.
      replace (IZR B / powerRZ 2 C) with (- (- (IZR B / powerRZ 2 C))) by OK.
      rewrite -(RInt_gen_shift_neg (F := fun _ => 0)); first last.
      { apply (ex_RInt_gen_neg_change_of_var_rev (F := fun _ => 0)).
        { intros ??. apply @ex_RInt_const. }
        apply ex_RInt_gen_0.
      }
      { intros ?. apply @ex_RInt_const. }
      rewrite -(RInt_gen_neg_change_of_var (F := (fun _ => 0))).
      2: { intros ??. apply @ex_RInt_const. }
      2: { intros ??. apply @ex_RInt_const. }
      2: { apply (ex_RInt_gen_neg_change_of_var_rev (F := fun _ => 0)).
          { intros ??. apply @ex_RInt_const. }
          apply ex_RInt_gen_0.
      }
      rewrite RInt_gen_0.
      OK.
    }
  }
  rewrite //=.
  iIntros (sample) "[%r HI]".
  remember (IsApprox sample r ⊤ ∗ ↯ (poke (λ _ : R, 0) (IZR B / powerRZ 2 C) 1 r))%I as Hcrs.
  wp_pures.
  wp_bind (R_ofZ _).
  iApply (pgl_wp_mono_frame Hcrs with "[] HI").
  2: { wp_apply wp_R_ofZ. }
  rewrite //=.
  iIntros (num) "[HI Hnum]".
  wp_pures.
  wp_bind (R_mulPow _ _).
  iApply (pgl_wp_mono_frame Hcrs with "[Hnum] HI").
  2: { wp_apply (wp_R_mulPow with "Hnum"). }
  rewrite //=.
  iIntros (bound) "[HI Hbound]".
  rewrite HeqHcrs.
  iDestruct "HI" as "[Hsample He]".
  rewrite /poke.
  case_decide.
  { iExFalso. by iApply (ec_contradict with "He"). }
  apply Rdichotomy in H1.
  destruct H1.
  { wp_pures.
    iApply pgl_wp_mono.
    2: {
      iApply (@wp_R_cmp_lt _ _ sample bound r (IZR B / powerRZ 2 C)).
      2:{ iFrame. }
      OK.
    }
    rewrite //=.
    iIntros (?) "(%&?)".
    iPureIntro; OK.
  }
  { wp_pures.
    iApply pgl_wp_mono.
    2: {
      iApply (@wp_R_cmp_gt _ _ sample bound r (IZR B / powerRZ 2 C)).
      2:{ iFrame. }
      OK.
    }
    rewrite //=.
    iIntros (?) "(%&?)".
    iPureIntro; OK.
  }
Qed.


Theorem lazy_real_expr_adequacy_mass_prob Σ `{erisGpreS Σ} {M} (e : expr) (σ : state) (μ : R -> R)
    (Hnn : ∀ x, 0 <= μ x <= M) (HC : IPCts μ)
    (Hlo : ex_RInt_gen μ (Rbar_locally Rbar.m_infty) (at_point 0))
    (Hhi : ex_RInt_gen μ (at_point 0) (Rbar_locally Rbar.p_infty))
    (Hspec :
      ∀ `{erisGS Σ} E (F : R -> R) (Hnn : ∃ M, ∀ x , 0 <= F x <= M) (HPC : IPCts F),
      ↯ (RInt_gen (fun (x : R) => μ x * F x) (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty))%R -∗
       WP e @ E {{ cont, ∃ r, IsApprox cont r E ∗ ↯(F r) }})
    (Hmass : RInt_gen μ (Rbar_locally Rbar.m_infty) (Rbar_locally Rbar.p_infty) = 1) :
    ∀ B C : Z,
     prob (lim_exec (lazy_real_cdf_checker e B C, σ)) (fun x => negb (bool_decide (x = #(1)%Z \/ x = #(-1)%Z))) = 0.
Proof.
  intros ??.
  have Lem1 : ∀ X : R, 0 <= X → X <= 0 → X = 0 by OK.
  apply Lem1; clear Lem1.
  { apply prob_ge_0. }
  etrans.
  { eapply lazy_real_expr_adequacy_mass; OK. }
  rewrite Hmass. OK.
Qed.

End CReal.
