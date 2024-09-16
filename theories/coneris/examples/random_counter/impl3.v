From iris.algebra Require Import frac_auth.
From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris hocap random_counter.

Set Default Proof Using "Type*".

Section filter.
  Definition filter_f (n:nat):= bool_decide (n<4)%nat.
  Definition filtered_list (l:list _) := filter filter_f l.
End filter.

Section lemmas.
  Context `{!conerisGS Σ}.
  Lemma hocap_tapes_notin3 α N ns (m:gmap loc (nat*list nat)) :
    α ↪N (N; ns) -∗ ([∗ map] α↦t ∈ m,∃ (ls:list nat), ⌜ (filter filter_f ls) = t.2⌝ ∗ α ↪N ( 4%nat ; ls)) -∗ ⌜m!!α=None ⌝.
  Proof.
    destruct (m!!α) eqn:Heqn; last by iIntros.
    iIntros "Hα Hmap".
    iDestruct (big_sepM_lookup with "[$]") as "(%&%&?)"; first done.
    iExFalso.
    iApply (tapeN_tapeN_contradict with "[$][$]").
  Qed. 
End lemmas.

Section impl3.

  Definition new_counter3 : val:= λ: "_", ref #0.
  Definition allocate_tape3 : val := λ: "_", AllocTape #4.
  Definition incr_counter_tape3 :val := rec: "f" "l" "α":=
                                          let: "n" := rand("α") #4 in
                                          if: "n" < #4
                                          then (FAA "l" "n", "n")
                                          else "f" "l" "α".
  Definition read_counter3 : val := λ: "l", !"l".
  Class counterG3 Σ := CounterG3 { counterG2_error::hocap_errorGS Σ;
                                   counterG2_tapes:: hocap_tapesGS Σ;
                                   counterG2_frac_authR:: inG Σ (frac_authR natR) }.

  Context `{!conerisGS Σ, !hocap_errorGS Σ, !hocap_tapesGS Σ, !inG Σ (frac_authR natR)}.
  Definition counter_inv_pred3 (c:val) γ1 γ2 γ3:=
    (∃ (ε:R) (m:gmap loc (nat * list nat)) (l:loc) (z:nat),
        ↯ ε ∗ ●↯ ε @ γ1 ∗
        ([∗ map] α ↦ t ∈ m, ∃ (ls:list nat), ⌜ (filter filter_f ls) = t.2⌝ ∗ α ↪N ( 4%nat ; ls) )
        ∗ ●m@γ2 ∗  
        ⌜c=#l⌝ ∗ l ↦ #z ∗ own γ3 (●F z)
    )%I.

  Lemma new_counter_spec3 E ε N:
    {{{ ↯ ε }}}
      new_counter3 #() @ E
      {{{ (c:val), RET c;
          ∃ γ1 γ2 γ3, inv N (counter_inv_pred3 c γ1 γ2 γ3) ∗
                      ◯↯ε @ γ1 ∗ own γ3 (◯F 0%nat)
      }}}.
  Proof.
    rewrite /new_counter3.
    iIntros (Φ) "Hε HΦ".
    wp_pures.
    wp_alloc l as "Hl".
    iDestruct (ec_valid with "[$]") as "%".
    unshelve iMod (hocap_error_alloc (mknonnegreal ε _)) as "[%γ1 [H1 H2]]".
    { lra. }
    simpl.
    iMod (hocap_tapes_alloc (∅:gmap _ _)) as "[%γ2 [H3 H4]]".
    iMod (own_alloc (●F 0%nat ⋅ ◯F 0%nat)) as "[%γ3[H5 H6]]".
    { by apply frac_auth_valid. }
    replace (#0) with (#0%nat) by done.
    iMod (inv_alloc N _ (counter_inv_pred3 (#l) γ1 γ2 γ3) with "[$Hε $Hl $H1 $H3 $H5]") as "#Hinv".
    { iSplit; last done. by iApply big_sepM_empty. }
    iApply "HΦ".
    iExists _, _, _. by iFrame.
  Qed.

  Lemma allocate_tape_spec3 N E c γ1 γ2 γ3:
    ↑N ⊆ E->
    {{{ inv N (counter_inv_pred3 c γ1 γ2 γ3) }}}
      allocate_tape3 #() @ E
      {{{ (v:val), RET v;
          ∃ (α:loc), ⌜v=#lbl:α⌝ ∗ α ◯↪N (3%nat; []) @ γ2
      }}}.
  Proof.
    iIntros (Hsubset Φ) "#Hinv HΦ".
    rewrite /allocate_tape3.
    wp_pures.
    wp_alloctape α as "Hα".
    iInv N as ">(%ε & %m & %l & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    iDestruct (hocap_tapes_notin3 with "[$][$]") as "%".
    iMod (hocap_tapes_new with "[$]") as "[H4 H7]"; first done.
    iMod ("Hclose" with "[$H1 $H2 H3 $H4 $H5 $H6 Hα]") as "_".
    { iNext. iSplitL; last done.
      rewrite big_sepM_insert; [simpl; iFrame|done].
      by rewrite filter_nil.
    }
    iApply "HΦ".
    by iFrame.
  Qed.

  Lemma incr_counter_tape_spec_some3 N E c γ1 γ2 γ3 (P: iProp Σ) (Q:nat->iProp Σ) (α:loc) (n:nat) ns:
    ↑N⊆E -> 
    {{{ inv N (counter_inv_pred3 c γ1 γ2 γ3) ∗
        □ (∀ (z:nat), P ∗ own γ3 (●F z) ={E∖↑N}=∗
                          own γ3 (●F(z+n)%nat)∗ Q z) ∗
        P ∗ α ◯↪N (3%nat; n::ns) @ γ2
    }}}
      incr_counter_tape3 c #lbl:α @ E
      {{{ (z:nat), RET (#z, #n); Q z ∗ α ◯↪N (3%nat; ns) @ γ2}}}.
  Proof.
    iIntros (Hsubset Φ) "(#Hinv & #Hvs & HP & Hα) HΦ".
  Admitted.
  (*   rewrite /incr_counter_tape3. *)
  (*   wp_pures. *)
  (*   wp_bind (rand(_) _)%E. *)
  (*   iInv N as ">(%ε & %m & %l & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose". *)
  (*   iDestruct (hocap_tapes_agree with "[$][$]") as "%". *)
  (*   erewrite <-(insert_delete m) at 1; last done. *)
  (*   rewrite big_sepM_insert; last apply lookup_delete. *)
  (*   simpl. *)
  (*   iDestruct "H3" as "[Htape H3]". *)
  (*   wp_apply (wp_rand_tape with "[$]"). *)
  (*   iIntros "[Htape %]". *)
  (*   iMod (hocap_tapes_pop with "[$][$]") as "[H4 Hα]". *)
  (*   iMod ("Hclose" with "[$H1 $H2 H3 $H4 $H5 $H6 Htape]") as "_". *)
  (*   { iSplitL; last done. *)
  (*     erewrite <-(insert_delete m) at 2; last done. *)
  (*     iNext. *)
  (*     rewrite insert_insert. *)
  (*     rewrite big_sepM_insert; last apply lookup_delete. iFrame. *)
  (*   } *)
  (*   iModIntro. *)
  (*   wp_pures. *)
  (*   clear -Hsubset. *)
  (*   wp_bind (FAA _ _). *)
  (*   iInv N as ">(%ε & %m & % & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose". *)
  (*   wp_faa. *)
  (*   iMod ("Hvs" with "[$]") as "[H6 HQ]". *)
  (*   replace (#(z+n)) with (#(z+n)%nat); last first. *)
  (*   { by rewrite Nat2Z.inj_add. } *)
  (*   iMod ("Hclose" with "[$H1 $H2 $H3 $H4 $H5 $H6]") as "_"; first done. *)
  (*   iModIntro. wp_pures. *)
  (*   iApply "HΦ". *)
  (*   by iFrame. *)
  (* Qed.  *)

  Lemma counter_presample_spec3 NS E ns α
     (ε2 : R -> nat -> R)
    (P : iProp Σ) T γ1 γ2 γ3 c:
    ↑NS ⊆ E ->
    (∀ ε n, 0<= ε -> 0<=ε2 ε n)%R ->
    (∀ (ε:R), 0<= ε ->SeriesC (λ n, if (bool_decide (n≤3%nat)) then 1 / (S 3%nat) * ε2 ε n else 0%R)%R <= ε)%R->
    inv NS (counter_inv_pred3 c γ1 γ2 γ3) -∗
    (□∀ (ε:R) n, (P ∗ ●↯ ε@ γ1) ={E∖↑NS}=∗
        (⌜(1<=ε2 ε n)%R⌝ ∨(●↯ (ε2 ε n) @ γ1 ∗ T (n)))) 
        -∗
    P -∗ α ◯↪N (3%nat; ns) @ γ2 -∗
        wp_update E (∃ n, T (n) ∗ α◯↪N (3%nat; ns++[n]) @ γ2).
  Proof.
    iIntros (Hsubset Hpos Hineq) "#Hinv #Hvs HP Hfrag".
  Admitted.
  (*   iApply wp_update_state_step_coupl. *)
  (*   iIntros (σ ε) "((Hheap&Htapes)&Hε)". *)
  (*   iMod (inv_acc with "Hinv") as "[>(% & % & % & % & H1 & H2 & H3 & H4 & -> & H5 & H6) Hclose]"; [done|]. *)
  (*   iDestruct (hocap_tapes_agree with "[$][$]") as "%". *)
  (*   erewrite <-(insert_delete m) at 1; last done. *)
  (*   rewrite big_sepM_insert; last apply lookup_delete. *)
  (*   simpl. *)
  (*   iDestruct "H3" as "[Htape H3]". *)
  (*   iDestruct (tapeN_lookup with "[$][$]") as "(%&%&%)". *)
  (*   iDestruct (ec_supply_bound with "[$][$]") as "%". *)
  (*   iMod (ec_supply_decrease with "[$][$]") as (ε1' ε_rem -> Hε1') "Hε_supply". subst. *)
  (*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'". *)
  (*   iApply state_step_coupl_state_adv_comp_con_prob_lang; first done. *)
  (*   unshelve iExists (λ x, mknonnegreal (ε2 ε1' x) _). *)
  (*   { apply Hpos. apply cond_nonneg. } *)
  (*   iSplit. *)
  (*   { iPureIntro.  *)
  (*     unshelve epose proof (Hineq ε1' _) as H1; first apply cond_nonneg. *)
  (*     by rewrite SeriesC_nat_bounded_fin in H1. } *)
  (*   iIntros (sample). *)
    
  (*   destruct (Rlt_decision (nonneg ε_rem + (ε2 ε1' sample))%R 1%R) as [Hdec|Hdec]; last first. *)
  (*   { apply Rnot_lt_ge, Rge_le in Hdec. *)
  (*     iApply state_step_coupl_ret_err_ge_1. *)
  (*     simpl. simpl in *. lra. *)
  (*   } *)
  (*   iApply state_step_coupl_ret. *)
  (*   unshelve iMod (ec_supply_increase _ (mknonnegreal (ε2 ε1' sample) _) with "Hε_supply") as "[Hε_supply Hε]". *)
  (*   { apply Hpos. apply cond_nonneg. } *)
  (*   { simpl. done. } *)
  (*   iMod (tapeN_update_append _ _ _ _ sample with "[$][$]") as "[Htapes Htape]". *)
  (*   iMod (hocap_tapes_presample _ _ _ _ _ (fin_to_nat sample) with "[$][$]") as "[H4 Hfrag]". *)
  (*   iMod "Hclose'" as "_". *)
  (*   iMod ("Hvs" with "[$]") as "[%|[H2 HT]]". *)
  (*   { iExFalso. iApply (ec_contradict with "[$]"). exact. } *)
  (*   iMod ("Hclose" with "[$Hε $H2 Htape H3 $H4 $H5 $H6]") as "_". *)
  (*   { iNext. iSplit; last done. *)
  (*     rewrite big_sepM_insert_delete; iFrame. *)
  (*   } *)
  (*   iApply fupd_mask_intro_subseteq; first set_solver. *)
  (*   iFrame. *)
  (* Qed.  *)

  Lemma read_counter_spec3 N E c γ1 γ2 γ3 P Q:
    ↑N ⊆ E ->
    {{{  inv N (counter_inv_pred3 c γ1 γ2 γ3) ∗
        □ (∀ (z:nat), P ∗ own γ3 (●F z) ={E∖↑N}=∗
                    own γ3 (●F z)∗ Q z)
         ∗ P
    }}}
      read_counter3 c @ E
      {{{ (n':nat), RET #n'; Q n'
      }}}.
  Proof.
    iIntros (Hsubset Φ) "(#Hinv & #Hvs & HP) HΦ".
    rewrite /read_counter3.
    wp_pure.
    iInv N as ">(%ε & %m & %l & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    wp_load.
    iMod ("Hvs" with "[$]") as "[H6 HQ]".
    iMod ("Hclose" with "[$H1 $H2 $H3 $H4 $H5 $H6]"); first done.
    iApply ("HΦ" with "[$]").
  Qed. 
    
End impl3. 
