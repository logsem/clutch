(** * Exact time credit accounting for Coupon collecting *)
From clutch.tachis Require Export expected_time_credits ert_weakestpre problang_wp proofmode
  derived_laws cost_models ert_rules.
From clutch.prob_lang Require Import notation tactics metatheory lang.
From iris.proofmode Require Export proofmode.
From Stdlib Require Export Reals Psatz.
From Coquelicot Require Export Hierarchy.
From Stdlib Require Import Lra.


Set Default Proof Using "Type*".

Section Coupon.
  Variables coupon':nat.
  Notation coupon:= (S coupon').

  Definition coupon_helper : val :=
    rec: "coupon_helper" "a" "cnt" :=
      if: "cnt" = #0 then #() else
        let: "k" := rand (#coupon') in
        (if: ! ("a" +ₗ "k") 
        then "coupon_helper" "a" "cnt"
         else ("a" +ₗ "k") <- #true ;;
             "coupon_helper" "a" ("cnt"-#1)).

  Definition coupon_collection : expr :=
    λ: "x", 
      let: "a" := AllocN #coupon #false in
      coupon_helper "a" #coupon.
End Coupon.

Definition harmonic_sum:= sum_n_m (λ x, /INR x) 1.

Lemma harmonic_sum_pos (n:nat): 0<= harmonic_sum n.
Proof.
  rewrite /harmonic_sum.
  induction n.
  - rewrite sum_n_m_zero; try done. lia.
  - rewrite sum_n_Sm; last lia.
    replace (plus _ _) with (sum_n_m (λ x, /INR x) 1 n + /(S n))by done.
    apply Rplus_le_le_0_compat; try done.
    rewrite -Rdiv_1_l. apply Rcomplements.Rdiv_le_0_compat; try lra.
    apply pos_INR_S.
Qed.

Local Hint Resolve harmonic_sum_pos : core.
Local Hint Resolve pos_INR : core.
Local Hint Resolve pos_INR_S: core.


Lemma harmonic_sum_S (n:nat): harmonic_sum (S n) = (harmonic_sum n + / (S n)).
Proof.
  rewrite {1}/harmonic_sum. rewrite sum_n_Sm; last lia.
  apply Rplus_eq_compat_l. done.
Qed.
                          

Local Lemma coupon_etc_credit_split p coupon:
  (p≠0)%nat -> (coupon ≠ 0)%nat -> (p<coupon)%nat -> p/coupon + (coupon-p)/coupon * (1 + (coupon/p)) = (coupon/p).
Proof.
  intros H1 H2. 
  rewrite Rmult_plus_distr_l -Rplus_assoc Rmult_1_r.
  replace (_/_+_) with 1.
  - replace (_*_) with ((coupon-p)/p).
    + replace 1 with (p/p).
      * rewrite -Rdiv_plus_distr.
        by replace (_+_) with (INR coupon) by lra.
      * apply Rdiv_diag. replace 0 with (INR 0) by done. by move => /INR_eq.
    + rewrite Rmult_div_assoc -Rmult_div_swap -Rmult_div_assoc.
      rewrite Rdiv_diag; first lra.
      replace 0 with (INR 0) by done.
      by apply not_INR.
  - rewrite -Rdiv_plus_distr.
    replace (p+_) with (INR coupon) by lra.
    rewrite Rdiv_diag; first lra.
    replace 0 with (INR 0) by done.
    by apply not_INR.
Qed.



Local Lemma etc_coupon_split  (n c:nat)(true_set:gset (fin c))(lis:list val):
  (0 < S n <= c)%nat ->
  size true_set = (c - S n)%nat ->
  (∀ n, lis !! fin_to_nat n = Some #true ↔ n ∈ true_set ) ->
  (∀ n, lis !! fin_to_nat n = Some #false ↔ n ∉ true_set) ->
  SeriesC
    (λ n0 : fin (c),
       1 / c * (if bool_decide (n0 ∈ true_set) then c / S n else 0)) +
    1 = c * / S n.
Proof.
  intros Hleq Hs H1 H2.
  erewrite (SeriesC_ext _ (λ x, /(S n) * if bool_decide (x ∈ true_set) then 1 else 0)); last first.
  { intros. case_bool_decide; try lra. rewrite -Rmult_div_swap Rmult_1_l.
    rewrite !Rdiv_def. rewrite Rmult_comm -Rmult_assoc (Rmult_comm (/c)) Rinv_r; first apply Rmult_comm.
    replace 0 with (INR 0); last by simpl.
    apply not_INR. lia.
  }
  replace (SeriesC _) with ((c- S n)/S n).
  { replace 1 with (S n/(S n)).
    - rewrite -Rdiv_plus_distr -Rdiv_def.
      f_equal. lra.
    - apply Rdiv_diag. replace 0 with (INR 0); last by simpl. apply not_INR.
      lia.
  }
  rewrite SeriesC_scal_l.
  rewrite Rdiv_def Rmult_comm. f_equal.
  rewrite -minus_INR; last lia.
  rewrite -Hs.
  erewrite (SeriesC_ext _ (λ x, if bool_decide (x∈elements true_set) then 1 else 0)); last first.
  { intros n'. case_bool_decide as H3; case_bool_decide as H4; try lra; exfalso.
    - rewrite elem_of_elements in H4. naive_solver.
    - rewrite elem_of_elements in H4. naive_solver. }
  rewrite SeriesC_list_1; first done.
  apply NoDup_elements.
Qed.

  
Section proofs.
  Context `{!tachisGS Σ CostRand}.


  Local Lemma wp_coupon_helper_end (coupon':nat) (l:loc) E: 
    {{{ True }}} coupon_helper coupon' #l #(0) @ E {{{ RET #(); True}}}.
  Proof.
    iIntros (Φ) "Hx HΦ".
    rewrite /coupon_helper.
    wp_pures.
    iApply "HΦ".
    done.
  Qed.

  Local Lemma wp_coupon_helper_ind (coupon':nat) (l:loc) (lis:list val) (true_set: gset (fin (S coupon'))) (n:nat) E:
    (0<n<= S coupon')%nat ->
    (length lis = S coupon')%nat ->
    (size true_set = S coupon' - n)%nat ->
    (∀ n,  lis !! (fin_to_nat n) = Some (#true) <-> n∈true_set) ->
    (∀ n,  lis !!(fin_to_nat n) = Some (#false) <-> n∉true_set) -> 
    {{{ ⧖ ((S coupon') * harmonic_sum n) ∗
          l ↦∗ lis
    }}}
      coupon_helper coupon' #l #(n) @ E
      {{{RET #(); True}}}.
  Proof.
    iIntros (Hn Hlis Hset Hrel Hrel' Φ) "[Hx Hl] HΦ".
    iLöb as "IH" forall (true_set n lis Hn Hlis Hset Hrel Hrel' Φ) "Hx Hl HΦ".
    destruct n as [| n]; first lia.
    rewrite /coupon_helper.
    wp_pures. simpl.
    rewrite -/(INR (S _)).
    rewrite harmonic_sum_S Rmult_plus_distr_l.
    iDestruct (etc_split with "Hx") as "[Hx1 Hx2]".
    { apply Rmult_le_pos; auto. }
    { apply Rle_mult_inv_pos; auto.  }
    wp_apply (wp_couple_rand_adv_comp' _ _ _ _ _
                (λ x:(fin (S coupon')), if (bool_decide (x∈true_set))
                          then (S coupon') / (S n)
                          else 0) with "[$Hx2]").
    - intros; case_bool_decide; last lra. apply Rcomplements.Rdiv_le_0_compat; auto.
    - rewrite Rplus_comm. replace (cost _) with 1; last by simpl.
      erewrite etc_coupon_split; done.
    - iIntros (c). case_bool_decide.
      + (** got an old coupon*)
        iIntros "Hx".
        wp_pures.
        wp_apply (wp_load_offset with "[$Hl]"); subst.        
        * erewrite Hrel; first done.
        * rewrite bool_decide_eq_true_2 //.
        * iIntros "Hl".
          simpl. wp_pure. 
          wp_apply ("IH" with "[][][][][][Hx1 Hx][Hl]"); try done.
          rewrite harmonic_sum_S Rmult_plus_distr_l.
          iApply etc_combine; iFrame. 
      + (** Got a new coupon*)
        iIntros "_".
        wp_pures.
        wp_apply (wp_load_offset with "[$Hl]").
        * erewrite Hrel'; auto.
        * rewrite bool_decide_eq_true_2 //.
        * iIntros "Hl".
          wp_pures.
          wp_apply (wp_store_offset with "[$Hl]").
          { replace (lis!!_) with (Some #false); first done.
            symmetry. erewrite Hrel'; auto.
          }
          { rewrite bool_decide_eq_true_2 //. }
          iIntros "Hl".
          do 3 wp_pure.
          replace (Z.of_nat (S n) - 1)%Z with (Z.of_nat n); last lia.
          destruct n.
          -- (** collected all coupons *)
            wp_apply (wp_coupon_helper_end); auto.
          -- iApply ("IH" with "[][][][][][$Hx1][$Hl]").
             ++ iPureIntro; lia.
             ++ iPureIntro. by rewrite length_insert.
             ++ iPureIntro. instantiate (1:= true_set ∪ {[c]}).
                rewrite size_union.
                { rewrite size_singleton. lia. }
                set_solver.
             ++ iPureIntro. intros x.
                rewrite list_lookup_insert_Some. split.
                ** intros [[H'[??]]|].
                   --- apply fin_to_nat_inj in H'. set_solver.
                   --- apply elem_of_union_l.
                       naive_solver.
                ** rewrite elem_of_union.
                   intros [?|?].
                   --- right. split; last naive_solver.
                       intro. subst. naive_solver.
                   --- left. split; first set_solver. 
                       split; first done.
                       pose proof fin_to_nat_lt x. lia.
             ++ iPureIntro. intros x.
                rewrite list_lookup_insert_Some. split.
                ** intros [[?[??]]|[H1 H2]]; first done.
                   erewrite Hrel' in H2; first set_solver. 
                ** intros. right. split; first set_solver.
                   erewrite Hrel'; first set_solver.
             ++ done.
  Qed.

  
  Lemma wp_coupon_collection (coupon':nat) E:
    {{{ ⧖ (S coupon' * harmonic_sum (S coupon')) }}}
      coupon_collection coupon' #()@E
      {{{RET #(); True}}}.
  Proof.
    iIntros (Φ) "Hx HΦ".
    rewrite /coupon_collection.
    (* pose proof (cond_nonneg (nnreal_harmonic_sum (S coupon'))). *)
    (* assert (0 <= S coupon') by eapply pos_INR. *)
    (* rewrite Rplus_assoc.  *)
    (* rewrite etc_split; [|lra|]; last first. *)
    (* { eapply Rplus_le_le_0_compat; real_solver. } *)
    (* iDestruct "Hx" as "[Hx1 Hx2]".     *)
    wp_pures.
    wp_apply (wp_allocN ); [lia| |].
    { rewrite bool_decide_eq_true_2 //. }
    iIntros (l) "Hl".
    wp_pure. wp_pure.
    rewrite -/(coupon_helper _). 
    rewrite -/(INR (S coupon')).
    wp_apply (wp_coupon_helper_ind with "[$Hx $Hl][$]").
    - lia.
    - rewrite length_replicate. by rewrite Nat2Z.id. 
    - replace (_-_)%nat with 0%nat by lia. instantiate (1:= ∅).
      done.
    - intros. split; last set_solver.
      move => /lookup_replicate [??]. done.
    - intros. split; first set_solver.
      intros _.
      rewrite lookup_replicate_2; auto.
      pose proof fin_to_nat_lt n. lia.
  Qed.
  
End proofs.
