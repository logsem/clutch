(** * Batch Sampling *)
From clutch.ert_logic Require Export expected_time_credits ert_weakestpre problang_wp proofmode
  derived_laws cost_models ert_rules.
From clutch.prob_lang Require Import notation tactics metatheory lang.
From iris.proofmode Require Export proofmode.
From Coq Require Export Reals Psatz.
From Coquelicot Require Export Hierarchy.
Require Import Lra.

Set Default Proof Using "Type*".

Definition sample
  := (rec: "g" "_" :=
        let: "result" := (rand #1) + #2 * (rand #1) in
        if: ("result" < #3)%E
          then "result"
        else ("g" #()))%V.

Section proof1.
  Context `{!ert_clutchGS Σ CostRand}.
  Lemma wp_geo E:
    {{{ ⧖ (8/3) }}}
      sample #()@E
      {{{(n:Z), RET #n; ⌜(0<=n<3)%Z⌝ }}}.
  Proof.
    iIntros (Φ) "Hx HΦ".
    iLöb as "IH" forall (Φ) "Hx HΦ".
    rewrite /sample.
    (* iAssert (⧖ (2/3) ∗ ⧖ 2)%I with "[Hx]"as "[Hx1 Hx2]". *)
    (* { iApply etc_split; try lra. iApply etc_irrel; last done. lra. } *)
    wp_pures. simpl.
    wp_apply (wp_couple_rand_adv_comp _ _ _ _ _ (λ x, if (fin_to_nat x =? 0)%nat then 1 else 7/3) with "[$]").
    - intros. case_match; lra.
    - exists (7/3). intros. case_match; lra.
    - simpl. rewrite SeriesC_finite_foldr. simpl. lra.
    - iIntros (n1) "Hx". case_match eqn: H1.
      + (* zero for first flip *)
        wp_pures.
        rewrite -(Rplus_0_r 1).
        wp_apply (wp_couple_rand_constant _ 0 with "[$]").
        { simpl. lra. }
        iIntros (n2) "Hx".
        wp_pures.
        case_bool_decide as H2; last first.
        { exfalso. apply H2. pose proof fin_to_nat_lt n2.
          rewrite Nat.eqb_eq in H1. lia. }
        wp_pures.
        iModIntro. iApply "HΦ".
        iPureIntro. lia.
      + wp_pures.
        wp_apply (wp_couple_rand_adv_comp _ _ _ _ _ (λ x, if (fin_to_nat x =? 0)%nat then 0 else 8/3) with "[$]").
        * intros. case_match; simpl; lra.
        * exists (8/3). intros; case_match; simpl; lra.
        * simpl. rewrite SeriesC_finite_foldr. simpl. lra.
        * iIntros (n2) "Hx". case_match eqn:K.
          { wp_pures. case_bool_decide as K'.
            - wp_pures. iModIntro. iApply "HΦ".
              iPureIntro; lia.
            - exfalso. pose proof fin_to_nat_lt n1. apply K'.
              rewrite Nat.eqb_eq in K. lia.
          }
          wp_pures. case_bool_decide as K'.
          { exfalso. rewrite Nat.eqb_neq in H1. rewrite Nat.eqb_neq in K. lia. }
          wp_pure. iApply ("IH" with "[Hx]").
          -- iApply etc_irrel; last done. simpl. lra.
          -- done.        
  Qed.  
End proof1.

Local Hint Resolve pos_INR : core.
Local Hint Resolve pos_INR_S: core.

Definition coin_tosser :=
  (rec: "g" "current" "rem" :=
     if: "rem" = #0 then "current"
     else "g" ("current"*#2 + (rand #1)) ("rem"-#1))%V.

Definition amortized_sample_helper :=
  (rec: "g" "_" :=
     let: "v" := coin_tosser #(0%nat) #(8%nat) in
     if: "v" < #243 then "v"
     else ("g" #()))%V.

Definition amortized_sample:=
  (λ: "lcnt" "lmem" "_",
     let: "num" := !"lcnt" in
     (if: "num" = #0
      then
        "lmem" <- amortized_sample_helper #();;
        "lcnt" <- #5
        (** sample 5*)
      else #()) ;;
     let: "mem" :=!"lmem" in
     let: "rem" := "mem" `rem` #3 in
     let: "quot" := "mem" `quot` #3 in
     "lcnt" <- !"lcnt" - #1;;
     "lmem" <- "quot";;
     "rem"
  )%V.

Definition amortized_sample_specialized (cnt mem:loc):=
  (λ: "_",
     let: "num" := !#cnt in
     (if: "num" = #0
      then
        #mem <- amortized_sample_helper #();;
        #cnt <- #5
        (** sample 5*)
      else #()) ;;
     let: "mem" :=!#mem in
     let: "rem" := "mem" `rem` #3 in
     let: "quot" := "mem" `quot` #3 in
     #cnt <- !#cnt - #1;;
     #mem <- "quot";;
     "rem"
  )%V.

Definition amortized_sample_creator :=
  (λ: "_",
     amortized_sample (ref #0) (ref #0)
  )%V.

Notation tc_total := (8*256/243).
Notation tc_each := (tc_total/5).

Local Lemma tc_each_better: tc_each < 8/3.
Proof. lra. Qed.

Section proof2.
  Context `{!ert_clutchGS Σ CostRand}.
  
  Definition amortized_sample_inv (f:val):=
    (∃ lcnt lmem (cnt mem:nat),
        ⌜f = amortized_sample_specialized lcnt lmem⌝ ∗
        lcnt ↦ #cnt ∗ ⌜(cnt < 5)%nat⌝ ∗
        lmem ↦ #mem ∗ ⌜(mem < 3 ^ cnt)%nat⌝ ∗
        ⧖ ((4-cnt) * tc_each)
    )%I.

  Local Definition compute_num (l:nat) (r:nat) (bound:nat):nat :=
    if (bound <=? l)%nat then (r-l)%nat
    else if (r<=? bound)%nat then (0)%nat
         else (r-bound)%nat.

  Local Lemma compute_num_split_lemma (current remaining:nat) current' f:
  current' =(λ x:fin (2%nat), (current*2+fin_to_nat x)*(2^remaining))%nat ->
           f = (λ x : fin 2,
                  tc_total * compute_num (current' x) (current' x + 2 ^ remaining) 243 /
                               2 ^ remaining ) ->
           1 / (1 + 1) * f 0%fin + (1 / (1 + 1) * f 1%fin + 0) =
           tc_total *
             compute_num (current * (2 ^ remaining + (2 ^ remaining + 0))) ((current * (2 ^ remaining + (2 ^ remaining + 0))) + (2 ^ remaining + (2 ^ remaining + 0))) 243 /
               (2 * 2 ^ remaining).
  Proof.
    Admitted.
    (* intros Hcurrent' Hf. *)
  (*   rewrite Hf. *)
  (*   cut (1 / (1 + 1) * *)
  (* (compute_num (current' 0%fin) (current' 0%fin + 2 ^ remaining) 243 / 2 ^ remaining) + *)
  (* (1 / (1 + 1) * *)
  (*  (compute_num (current' 1%fin) (current' 1%fin + 2 ^ remaining) 243 / 2 ^ remaining) + 0) = *)
  
  (* compute_num (current * (2 ^ remaining + (2 ^ remaining + 0))) *)
  (*   (current * (2 ^ remaining + (2 ^ remaining + 0)) + (2 ^ remaining + (2 ^ remaining + 0))) 243 / *)
  (* (2 * 2 ^ remaining)); first lra. *)
  (*   rewrite /compute_num. *)
  (*   destruct (243 <=? current * (2 ^ remaining + (2 ^ remaining + 0)))%nat eqn:H1. *)
  (*   - assert ((243 <=? current' 0%fin)%nat = true) as K1. *)
  (*     { rewrite Nat.leb_le. rewrite Nat.leb_le in H1. *)
  (*       subst. lia. *)
  (*     } *)
  (*     assert ((243 <=? current' 1%fin)%nat = true) as K2. *)
  (*     { rewrite Nat.leb_le. rewrite Nat.leb_le in H1. *)
  (*       subst. lia. } *)
  (*     rewrite K1 K2. subst. simpl. *)
  (*     trans (1%R). *)
  (*     + replace (_+_) with (1/2 + 1/2); try lra. *)
  (*       replace ((current * 2 + 0 + 2 ^ remaining - (current * 2 + 0))%nat / 2 ^ remaining) with 1; last first. *)
  (*       { symmetry. apply Rdiv_diag_eq. *)
  (*         - apply pow_nonzero. lra. *)
  (*         - replace (current * 2 + 0 + 2 ^ remaining - (current * 2 + 0))%nat with *)
  (*             (2^remaining)%nat; last lia. *)
  (*           rewrite pow_INR. done. *)
  (*       } *)
  (*       replace ((current * 2 + 1 + 2 ^ remaining - (current * 2 + 1))%nat / 2 ^ remaining) with 1; first lra. *)
  (*       symmetry. apply Rdiv_diag_eq. *)
  (*         * apply pow_nonzero. lra. *)
  (*         * replace (current * 2 + 1 + 2 ^ remaining - (current * 2 + 1))%nat with *)
  (*             (2^remaining)%nat; last lia. *)
  (*           rewrite pow_INR. done. *)
  (*     + symmetry. apply Rdiv_diag_eq. *)
  (*         * apply Rmult_integral_contrapositive; split; try lra. apply pow_nonzero. lra. *)
  (*         * replace (current + (2 ^ remaining + (2 ^ remaining + 0)) - current)%nat with *)
  (*             (2 * 2 ^ remaining)%nat; last lia. *)
  (*           rewrite mult_INR. *)
  (*           rewrite pow_INR. done. *)
  (*   - rewrite Nat.leb_gt in H1. *)
  (*     destruct (current + (2 ^ remaining + (2 ^ remaining + 0)) <=? 243)%nat eqn:H2. *)
  (*     + rewrite Nat.leb_le in H2. *)
  (*       assert ((243 <=? current' 0%fin)%nat = false) as K1. *)
  (*       { rewrite Nat.leb_gt. admit. } *)
  (*       assert ((243 <=? current' 1%fin)%nat = false) as K2. *)
  (*       { admit. } *)
  (*       rewrite K1 K2. *)
  (*       assert (current' 0%fin + 2 ^ remaining <=? 243 = true)%nat as K3. *)
  (*       { admit. } *)
  (*       assert (current' 1%fin + 2 ^ remaining <=? 243 = true)%nat as K4. *)
  (*       { admit. } *)
  (*       rewrite K3 K4. simpl. lra. *)
  (*     + rewrite Nat.leb_gt in H2. *)
  (*       assert ((243 <=? current' 0%fin)%nat = false) as K1. *)
  (*       { admit. } *)
  (*       rewrite K1. *)
  (* Admitted. *)

           
  Lemma wp_coin_tosser (current remaining:nat) E:
    (current*2^remaining + 2^remaining <= 256)%nat -> (remaining <= 8)%nat -> 
    {{{ ⧖ ((remaining) + (tc_total*(compute_num (current*2^remaining) (current*2^remaining + 2^remaining) (243)%nat)/2^remaining)) }}}
      coin_tosser #current #remaining@E
      {{{ (n:nat), RET #n;
          ⌜(current*2^remaining <= n < current*2^remaining + 2^ remaining)%nat⌝ ∗
          (if (n<?243)%nat then True else ⧖ tc_total) }}}.
  Proof.
    iIntros (Hineq1 Hineq2 Φ) "Hx HΦ".
    rewrite /coin_tosser. iLöb as "IH" forall (current remaining Hineq1 Hineq2 Φ) "Hx HΦ".
    wp_pures.
    case_bool_decide.
    - wp_pures. iModIntro. iApply "HΦ". replace remaining with 0%nat; last first.
      { destruct remaining; done. }
      iSplit.
      + iPureIntro. simpl. lia.
      + case_match eqn: H0; first done.
        iApply (etc_irrel with "[$Hx]").
        simpl. replace (_ / _) with tc_total; first lra.
        rewrite -Rmult_div_assoc. replace (compute_num _ _ _)%nat with 1%nat; first (simpl; lra).
        rewrite /compute_num. rewrite Nat.leb_antisym. rewrite Nat.mul_1_r. rewrite H0. simpl. lia.
    - wp_pures. wp_bind (rand _)%E.
      destruct remaining as [|remaining]; first done.
      replace (Z.of_nat (S remaining) - 1%Z)%Z with (Z.of_nat remaining); last lia.
      rewrite S_INR.
      rewrite Rplus_assoc.
      iDestruct (etc_split with "[$Hx]") as "[Hx1 Hx2]".
      { auto. }
      { apply Rplus_le_le_0_compat; try lra.
        repeat apply Rmult_le_pos; try real_solver.
        apply Rlt_le, Rinv_0_lt_compat.
        apply pow_lt. lra.
      }
      set (current' := (λ x:fin (2%nat), (current*2+fin_to_nat x)*(2^remaining))%nat).
      set (f:= λ x: fin (2%nat), tc_total * (compute_num (current' x) (current' x + (2^remaining)) 243)%nat/(2^remaining)).
      wp_apply (wp_couple_rand_adv_comp' _ _ _ _ _ f with "[$Hx2]").
      * intros n. rewrite /f.
        repeat apply Rmult_le_pos; try real_solver.
        apply Rlt_le, Rinv_0_lt_compat.
        apply pow_lt. lra.
      * simpl. f_equal. rewrite SeriesC_finite_foldr. simpl.
        eapply compute_num_split_lemma; done.
      * iIntros (n) "Hx".
        do 2 wp_pure.
        replace 2%Z with (Z.of_nat 2) by lia.
        rewrite <-Nat2Z.inj_mul.
        rewrite <-Nat2Z.inj_add.
        wp_apply ("IH" with "[][][Hx1 Hx]").
        -- iPureIntro. pose proof fin_to_nat_lt n.
           trans ((current * 2 + 1) * 2 ^ remaining + 2 ^ remaining)%nat.
           ++ apply Plus.plus_le_compat_r_stt, Nat.mul_le_mono_r.
              lia.
           ++ etrans; last exact. simpl. lia.
        -- iPureIntro. lia.
        -- iApply etc_combine; iFrame.
        -- iIntros (n') "[[%Ha %Hb] H]". iApply "HΦ". iFrame. iPureIntro.
           pose proof fin_to_nat_lt n.
           split.
           ++ etrans; last exact. simpl. lia.
           ++ eapply NPeano.Nat.lt_le_trans; first exact. simpl.
              assert ((current * 2 + fin_to_nat n) * 2 ^ remaining + 2 ^ remaining<=
                        (current * 2 * 2 ^ remaining + 2^remaining + 2 ^ remaining))%nat; simpl; try lia.
              assert ((current * 2 + fin_to_nat n) * 2 ^ remaining + 2 ^ remaining<=
                        (current * 2 + 1) * 2 ^ remaining + 2 ^ remaining)%nat; simpl; try lia.
              apply Plus.plus_le_compat_r_stt. apply Nat.mul_le_mono_r. lia.
  Admitted.

  Lemma wp_amortized_sample_helper E:
    {{{ ⧖ tc_total }}}
      amortized_sample_helper #()@E
      {{{ (n:nat), RET #n; ⌜(n<243)%nat⌝ }}}.
  Proof.
    iIntros (Φ) "Hx HΦ".
    rewrite /amortized_sample_helper.
    iLöb as "IH" forall (Φ) "Hx HΦ".
    wp_pures. simpl.
    wp_apply (wp_coin_tosser with "[Hx]").
    - simpl. lia.
    - lia.
    - iApply etc_irrel; last done. simpl. lra.
    - iIntros (n) "(%&Hx)".
      wp_pures. case_match.
      + case_bool_decide; last first.
        { exfalso. rewrite Nat.ltb_lt in H0. lia. }
        wp_pures. iModIntro. iApply "HΦ". iPureIntro; lia.
      + case_bool_decide.
        { exfalso. rewrite Nat.ltb_ge in H0. lia. }
        wp_pure. iApply ("IH" with "[$]").
        done.
  Qed.
  
  
  Lemma wp_amortized_sample_continuation cnt mem (lmem lcnt:loc) E:
    (0<cnt<=5)%nat -> (mem<3^cnt)%nat ->
    {{{ ⧖ ((5 - cnt) * tc_each) ∗ lcnt ↦ #cnt ∗ lmem ↦ #mem }}}
    (let: "mem" := ! #lmem in
     let: "rem" := "mem" `rem` #3 in
     let: "quot" := "mem" `quot` #3 in #lcnt <- ! #lcnt - #1;; #lmem <- "quot";; "rem") @ E
    {{{ (n:Z), RET #n; ⌜(0<=n<3)%Z⌝ ∗ amortized_sample_inv (amortized_sample_specialized lcnt lmem) }}}.
  Proof.
    iIntros (Hineq1 Hineq2 Φ) "(Hx & Hcnt & Hmem) HΦ".
    wp_apply (wp_load with "[$Hmem]").
    { rewrite bool_decide_eq_true_2 //. }
    iIntros "Hmem".
    wp_pures. 
    wp_apply (wp_load with "[$Hcnt]").
    { rewrite bool_decide_eq_true_2 //. }
    iIntros "Hcnt". wp_pures.
    wp_apply (wp_store with "[$Hcnt]").
    { rewrite bool_decide_eq_true_2 //. }
    iIntros "Hcnt".
    wp_pures.    
    wp_apply (wp_store with "[$Hmem]").
    { rewrite bool_decide_eq_true_2 //. }
    iIntros "Hmem". wp_pures.
    iModIntro. iApply "HΦ".
    repeat iSplit.
    + iPureIntro. apply Z.rem_nonneg; lia.
    + iPureIntro. apply Z.rem_bound_pos; lia.
    + iExists lcnt, lmem, _, _. iSplit; first done.
      replace (Z.of_nat cnt - 1)%Z with (Z.of_nat (cnt - 1)); last first.
      { destruct cnt; lia. }
      iFrame. iSplit.
      { iPureIntro; lia. }
      replace (Z.of_nat mem ÷ 3)%Z with (Z.of_nat (mem / 3)%nat); last first.
      { rewrite Nat2Z.inj_div. rewrite Z.quot_div_nonneg; lia. }
      iFrame. iSplit. 
      { iPureIntro. apply Nat.Div0.div_lt_upper_bound. replace (_*_)%nat with (3^cnt)%nat; first done.
        destruct cnt; first lia.
        simpl. replace (cnt - 0)%nat with cnt; lia.
      }
      iApply (etc_irrel with "[$Hx]").
      destruct cnt; first lia.
      replace (S cnt - 1)%nat with cnt; last lia.
      rewrite S_INR. simpl. lra.
  Qed.
  
  Lemma wp_amortized_sample f E:
    {{{ ⧖ tc_each ∗ amortized_sample_inv f}}}
      f #()@E
      {{{ (n:Z), RET #n; ⌜(0<=n<3)%Z⌝ ∗ amortized_sample_inv f }}}.
  Proof.
    iIntros (Φ) "[Hx Hinv] HΦ".
    iDestruct "Hinv" as "(%lcnt & %lmem & %cnt & %mem & -> & Hcnt & % & Hmem & % & Hx')".
    rewrite /amortized_sample_specialized.
    wp_pures.
    wp_apply (wp_load with "[$Hcnt]").
    { rewrite bool_decide_eq_true_2 //. }
    iIntros "Hcnt".
    wp_pures.
    simpl.
    case_bool_decide.
    - (** The complicated case where we have to do the batch sampling*)
      wp_pures. wp_apply (wp_amortized_sample_helper with "[Hx Hx']").
      + iDestruct (etc_combine with "[$]") as "Hx". iApply etc_irrel; last done.
        replace cnt with 0%nat; simpl; try lra.
        by destruct cnt.
      + iIntros (v) "%Hv".
        wp_apply (wp_store with "[$Hmem]").
        { rewrite bool_decide_eq_true_2 //. }
        iIntros "Hmem".
        wp_pures.
        wp_apply (wp_store with "[$Hcnt]").
        { rewrite bool_decide_eq_true_2 //. }
        iIntros "Hcnt".
        wp_pures.
        iMod etc_zero as "Hz".
        replace 5%Z with (Z.of_nat 5)%nat; last done.
        wp_apply (wp_amortized_sample_continuation with "[$Hcnt $Hmem Hz]").
        { lia. }
        { simpl. lia. }
        { simpl. iApply etc_irrel; last done. simpl. lra. }
        iIntros (x) "[%?]". iApply "HΦ". iSplit; first done. done.
    - wp_pures.
      iApply (wp_amortized_sample_continuation with "[$Hcnt $Hmem Hx Hx']").
      + destruct cnt; try lia. done.
      + done.
      + iDestruct (etc_combine with "[$]") as "Hx". iApply etc_irrel; last done.
        lra.
      + iModIntro. iIntros (n) "[% H]". iApply "HΦ". iSplit; done.
  Qed.


  Lemma wp_amortized_sample_creator E:
    {{{ ⧖ (4*tc_each) }}}
      amortized_sample_creator #()@E
      {{{ v, RET v; amortized_sample_inv v }}}.
  Proof.
    iIntros (Φ) "Hx HΦ".
    rewrite /amortized_sample_creator.
    wp_pures. rewrite /amortized_sample.
    wp_alloc lmem as "Hlmem".
    wp_alloc lcnt as "Hlcnt".
    wp_pures. iModIntro. iApply "HΦ".
    rewrite /amortized_sample_inv.
    iExists lcnt, lmem, 0%nat, 0%nat.
    iFrame. iSplit; first done.
    repeat iSplit.
    - iPureIntro; lia.
    - iPureIntro. simpl. lia.
    - iApply etc_irrel; last done. simpl. lra.
  Qed.
    
End proof2. 
  

