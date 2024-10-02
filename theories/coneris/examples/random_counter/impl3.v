From iris.algebra Require Import frac_auth.
From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris hocap hocap_rand random_counter.

Set Default Proof Using "Type*".

Section filter.
  Definition filter_f (n:nat):= (n<4)%nat.
  Definition filtered_list (l:list _) := filter filter_f l.

  Lemma Forall_filter_f ns:
    Forall (λ x : nat, x ≤ 3) ns -> filter filter_f ns = ns.
  Proof.
    induction ns; first done.
    intros H.
    rewrite Forall_cons in H. destruct H.
    rewrite filter_cons_True; first f_equal; first naive_solver.
    rewrite /filter_f. lia.
  Qed.
End filter.

Section impl3.
  Context `{H:conerisGS Σ, r1:@rand_spec Σ H, L:randG Σ, !inG Σ (frac_authR natR)}.

  Definition new_counter3 : val:= λ: "_", ref #0.
  Definition allocate_tape3 : val := λ: "_", rand_allocate_tape #4%nat.
  Definition incr_counter_tape3 :val := rec: "f" "l" "α":=
                                          let: "n" := rand_tape "α" #4%nat in
                                          if: "n" < #4
                                          then (FAA "l" "n", "n")
                                          else "f" "l" "α".
  Definition read_counter3 : val := λ: "l", !"l".
  Class counterG3 Σ := CounterG3 { counterG3_randG:randG Σ;
                                   counterG3_frac_authR:: inG Σ (frac_authR natR) }.

  Definition counter_inv_pred3 (c:val) γ2:= (∃ (l:loc) (z:nat), ⌜c=#l⌝ ∗ l ↦ #z ∗ own γ2 (●F z) )%I.

  Definition is_counter3 N (c:val) γ1 γ2:=
    ((is_rand (L:=L) (N.@"rand") γ1) ∗
     inv (N.@"counter") (counter_inv_pred3 c γ2))%I.

  Lemma new_counter_spec3 E N:
    {{{ True }}}
      new_counter3 #() @ E
      {{{ (c:val), RET c;
          ∃ γ1 γ2, is_counter3 N c γ1 γ2 ∗ own γ2 (◯F 0%nat)
      }}}.
  Proof.
    rewrite /new_counter3.
    iIntros (Φ) "_ HΦ".
    wp_pures.
    iMod (rand_inv_create_spec) as "(%γ1 & #Hinv)".
    wp_alloc l as "Hl".
    iMod (own_alloc (●F 0%nat ⋅ ◯F 0%nat)) as "[%γ2[H5 H6]]".
    { by apply frac_auth_valid. }
    replace (#0) with (#0%nat) by done.
    iMod (inv_alloc _ _ (counter_inv_pred3 (#l) γ2) with "[$Hl $H5]") as "#Hinv'"; first done.
    iApply "HΦ".
    iFrame.
    iModIntro.
    iExists _. by iSplit.
  Qed.

  Lemma allocate_tape_spec3 N E c γ1 γ2:
    ↑N ⊆ E->
    {{{ is_counter3 N c γ1 γ2 }}}
      allocate_tape3 #() @ E
      {{{ (v:val), RET v;
          ∃ (α:loc), ⌜v=#lbl:α⌝ ∗ (∃ ls, ⌜filter filter_f ls = []⌝ ∗ rand_tapes_frag (L:=L) γ1 α (4, ls))
      }}}.
  Proof.
    iIntros (Hsubset Φ) "[#Hinv #Hinv'] HΦ".
    rewrite /allocate_tape3.
    wp_pures.
    wp_apply rand_allocate_tape_spec as (v) "(%α & -> & Hfrag)"; [by eapply nclose_subseteq'|done|].
    iApply "HΦ".
    by iFrame.
  Qed.

  Lemma incr_counter_tape_spec_some3  N E c γ1 γ2 (Q:nat->iProp Σ) (α:loc) n ns:
    ↑N⊆E ->
    {{{ is_counter3 N c γ1 γ2 ∗
        (∃ ls, ⌜filter filter_f ls = n::ns⌝ ∗ rand_tapes_frag (L:=L) γ1 α (4, ls)) ∗
        (  ∀ (z:nat), own γ2 (●F z) ={E∖↑N}=∗
                    own γ2 (●F (z+n)) ∗ Q z)
           
    }}}
      incr_counter_tape3 c #lbl:α @ E
                                  {{{ (z:nat), RET (#z, #n);
                                      (∃ ls, ⌜filter filter_f ls = ns⌝ ∗ rand_tapes_frag (L:=L) γ1 α (4, ls)) ∗
                                                          Q z }}}.
  Proof.
    iIntros (Hsubset Φ) "([#Hinv #Hinv'] & (%ls & %Hfilter & Hfrag) & Hvs) HΦ".
    rewrite /incr_counter_tape3.
    iLöb as "IH" forall (ls Hfilter Φ) "Hfrag".
    wp_pures.
    destruct ls as [|hd ls]; first simplify_eq.
    wp_apply (rand_tape_spec_some with "[$]") as "Hfrag"; first by eapply nclose_subseteq'.
    wp_pures.
    case_bool_decide as K.
    - wp_pures.
      wp_bind (FAA _ _).
      iInv "Hinv'" as ">(%&%&-> & ?&?)" "Hclose".
      wp_faa.
      iMod (fupd_mask_subseteq (E ∖ ↑N)) as "Hclose'".
      + apply difference_mono_l.
        by apply nclose_subseteq'.
      + iMod ("Hvs" with "[$]") as "[? HQ]".
        iMod "Hclose'" as "_".
        rewrite -Nat2Z.inj_add.
        rewrite filter_cons_True in Hfilter; last (rewrite /filter_f; lia).
        simplify_eq.
        iMod ("Hclose" with "[-HQ Hfrag HΦ]") as "_"; first by iFrame.
        iModIntro.
        wp_pures.
        iApply "HΦ". by iFrame.
    - wp_pure.
      iApply ("IH" with "[][$][$][$]").
      iPureIntro.
      rewrite filter_cons_False in Hfilter; first done.
      rewrite /filter_f. lia.
  Qed.

  
  Lemma counter_presample_spec3  NS E T γ1 γ2 c α ns:
    ↑NS ⊆ E ->
    is_counter3 NS c γ1 γ2 -∗
    (∃ ls, ⌜filter filter_f ls = ns⌝ ∗ rand_tapes_frag (L:=L) γ1 α (4, ls)) -∗
    ( |={E∖↑NS,∅}=>
        ∃ ε ε2 num,
        ↯ ε ∗ 
        ⌜(∀ n, 0<=ε2 n)%R⌝ ∗
        ⌜(SeriesC (λ l, if bool_decide (l∈fmap (λ x, fmap (FMap:=list_fmap) fin_to_nat x) (enum_uniform_fin_list 3%nat num)) then ε2 l else 0%R) / (4^num) <= ε)%R⌝ ∗
      (∀ ns', ↯ (ε2 ns') ={∅,E∖↑NS}=∗
              T ε ε2 num ns'
      ))-∗ 
        wp_update E (∃ ε ε2 num ns', (∃ ls, ⌜filter filter_f ls = ns++ns'⌝ ∗ rand_tapes_frag (L:=L) γ1 α (4, ls)) ∗ T ε ε2 num ns').
  Proof.
    iIntros (Hsubset) "[#Hinv #Hinv'] Hfrag Hvs".
    iMod wp_update_epsilon_err as "(%eps&%Heps&Heps)".
    iRevert "Hfrag Hvs".
    iApply (ec_ind_amp _ 5%R with "[][$]"); [done|lra|].
    clear eps Heps.
    iModIntro.
    iIntros (eps Heps) "#IH Heps (%ls & %Hfilter & Hfrag) Hvs".
    iMod (rand_presample_spec _ _ _ _ _ _ (λ ε num ε2 ns',
         _                                    
            )%I with "[//][$][Heps Hvs]") as "H"; first by apply nclose_subseteq'.
    - iMod (fupd_mask_subseteq (E ∖ ↑NS)) as "Hclose".
      { apply difference_mono_l.
        by apply nclose_subseteq'. }
      iMod "Hvs" as "(%ε & %ε2 & %num & Herr &%Hpos & %Hineq & Hrest)".
      iFrame.
      admit.
    - iDestruct "H" as "(%ε & %num & %ε2 & %ns' & Hfrag & HT)".
      iModIntro.
      iFrame.
      rewrite filter_app.
      admit.
  Admitted.
  (*   iIntros (Hsubset Hpos Hineq) "#Hinv #Hvs HP Hfrag". *)
  (*   iMod wp_update_epsilon_err as "(%epsilon_err&%H&?)". *)
  (*   iApply wp_update_state_step_coupl. *)
  (*   iRevert "HP Hfrag". *)
  (*   iApply (ec_ind_amp _ 5%R with "[][$]"); [done|lra|]. *)
  (*   iModIntro. *)
  (*   clear epsilon_err H. *)
  (*   iIntros (epsilon_err ?) "#IH Hepsilon_err HP Hfrag". *)
  (*   iIntros (σ ε) "((Hheap&Htapes)&Hε)". *)
  (*   iMod (inv_acc with "Hinv") as "[>(%ε0 & % & % & % & H1 & H2 & H3 & H4 & -> & H5 & H6) Hclose]"; [done|]. *)
  (*   iDestruct (hocap_tapes_agree with "[$][$]") as "%". *)
  (*   erewrite <-(insert_delete m) at 1; last done. *)
  (*   rewrite big_sepM_insert; last apply lookup_delete. *)
  (*   simpl. *)
  (*   iDestruct "H3" as "[(%ls & %Hls & Htape) H3]". *)
  (*   iDestruct (tapeN_lookup with "[$][$]") as "(%&%&%)". *)
  (*   iDestruct (ec_valid with "H1") as "%". *)
  (*   iDestruct (ec_combine with "[$]") as "Htotal". *)
  (*   iDestruct (ec_supply_bound with "[$][$]") as "%". *)
  (*   iMod (ec_supply_decrease with "[$][$]") as (ε1' ε_rem -> Hε1') "Hε_supply". subst. *)
  (*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'". *)
  (*   pose (ε2' := λ (x:nat), (if bool_decide (x<=3)%nat then ε2 ε0 x else *)
  (*                           if bool_decide (x=4)%nat then ε0 + 5 * epsilon_err *)
  (*                           else 0)%R *)
  (*        ). *)
  (*   iApply state_step_coupl_state_adv_comp_con_prob_lang; first done. *)
  (*   assert (forall x, 0<=ε2' x)%R. *)
  (*   { intros. rewrite /ε2'. repeat case_bool_decide; try done; first naive_solver. *)
  (*     apply Rplus_le_le_0_compat; simpl; [naive_solver|lra]. } *)
  (*   unshelve iExists (λ x, mknonnegreal (ε2' x) _); auto. *)
  (*   iSplit. *)
  (*   { iPureIntro. *)
  (*     unshelve epose proof (Hineq ε0 _) as H'; first (by naive_solver). *)
  (*     rewrite SeriesC_nat_bounded_fin in H'. *)
  (*     replace (INR 5%nat) with 5%R by (simpl; lra). *)
  (*     replace (INR 4%nat) with 4%R in H' by (simpl; lra). *)
  (*     rewrite /=/ε2' Hε1'. *)
  (*     rewrite SeriesC_finite_foldr/=. *)
  (*     rewrite SeriesC_finite_foldr/= in H'. *)
  (*     lra. *)
  (*   } *)
  (*   iIntros (sample). *)
  (*   simpl. *)
  (*   destruct (Rlt_decision (nonneg ε_rem + (ε2' sample))%R 1%R) as [Hdec|Hdec]; last first. *)
  (*   { apply Rnot_lt_ge, Rge_le in Hdec. *)
  (*     iApply state_step_coupl_ret_err_ge_1. *)
  (*     simpl. simpl in *. lra. *)
  (*   } *)
  (*   destruct (Nat.lt_total (fin_to_nat sample) 4%nat) as [|[|]]. *)
  (*   - (* we sample a value less than 4*) *)
  (*     iApply state_step_coupl_ret. *)
  (*     unshelve iMod (ec_supply_increase _ (mknonnegreal (ε2' sample) _) with "Hε_supply") as "[Hε_supply Hε]"; auto. *)
  (*     iMod (tapeN_update_append _ _ _ _ sample with "[$][$]") as "[Htapes Htape]". *)
  (*     iMod (hocap_tapes_presample _ _ _ _ _ (fin_to_nat sample) with "[$][$]") as "[H4 Hfrag]". *)
  (*     iMod "Hclose'" as "_". *)
  (*     iMod ("Hvs" $! _ (fin_to_nat sample)%nat with "[$]") as "[%|[H2 HT]]". *)
  (*     { iExFalso. iApply (ec_contradict with "[$]"). *)
  (*       simpl. *)
  (*       rewrite /ε2'. *)
  (*       by rewrite bool_decide_eq_true_2; last lia. *)
  (*     } *)
  (*     simpl. *)
  (*     iMod ("Hclose" with "[$Hε H2 Htape H3 $H4 $H5 $H6]") as "_". *)
  (*     { iNext. *)
  (*       rewrite /ε2'. rewrite bool_decide_eq_true_2; last lia. *)
  (*       iFrame. *)
  (*       rewrite big_sepM_insert_delete; iFrame. simpl. iPureIntro. *)
  (*       split; last done. *)
  (*       rewrite filter_app. f_equal. *)
  (*       rewrite filter_cons. *)
  (*       rewrite decide_True; first done. *)
  (*       rewrite /filter_f. by apply bool_decide_pack. *)
  (*     } *)
  (*     iApply fupd_mask_intro_subseteq; first set_solver. *)
  (*     iFrame. *)
  (*   - (* we sampled a 4, and hence löb *) *)
  (*     unshelve iMod (ec_supply_increase _ (mknonnegreal (ε2' sample) _) with "Hε_supply") as "[Hε_supply Hε]"; auto. *)
  (*     iMod (tapeN_update_append _ _ _ _ sample with "[$][$]") as "[Htapes Htape]". *)
  (*     iMod "Hclose'" as "_". *)
  (*     simpl. *)
  (*     rewrite {2}/ε2'. *)
  (*     rewrite bool_decide_eq_false_2; last lia. *)
  (*     rewrite bool_decide_eq_true_2; last lia. *)
  (*     iDestruct (ec_split with "[$]") as "[Hε Hampl]"; simpl; [naive_solver|lra|]. *)
  (*     simpl. *)
  (*     iMod ("Hclose" with "[$Hε $H2 Htape H3 $H4 $H5 $H6]") as "_". *)
  (*     { iNext. *)
  (*       rewrite (big_sepM_delete _ m); [iFrame|done]. *)
  (*       simpl. iPureIntro; split; last done. *)
  (*       rewrite filter_app filter_cons decide_False; simpl. *)
  (*       - by rewrite filter_nil app_nil_r. *)
  (*       - rewrite /filter_f. case_bool_decide; [lia|auto]. *)
  (*     } *)
  (*     iDestruct ("IH" with "[$][$][$]") as "IH'". *)
  (*     by iMod ("IH'" $! (state_upd_tapes <[_:=_]> _) with "[$]") as "IH'". *)
  (*   - pose proof fin_to_nat_lt sample; lia. *)
  (* Qed. *)

  Lemma read_counter_spec3 N E c γ1 γ2 Q:
    ↑N ⊆ E ->
    {{{  is_counter3 N c γ1 γ2  ∗
         (∀ (z:nat), own γ2 (●F z) ={E∖↑N}=∗
                     own γ2 (●F z) ∗ Q z)
        
    }}}
      read_counter3 c @ E
      {{{ (n':nat), RET #n'; Q n'
      }}}.
  Proof.
    iIntros (Hsubset Φ) "([#Hinv #Hinv'] & Hvs) HΦ".
    rewrite /read_counter3.
    wp_pure.
    iInv "Hinv'" as ">( %l & %z & -> & H5 & H6)" "Hclose".
    wp_load.
    iMod (fupd_mask_subseteq (E ∖ ↑N)) as "Hclose'".
    { apply difference_mono_l.
      by apply nclose_subseteq'. }
    iMod ("Hvs" with "[$]") as "[? HQ]".
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[-HQ HΦ]"); first by iFrame.
    iApply ("HΦ" with "[$]").
  Qed.
    
End impl3.

Program Definition random_counter3 `{F:rand_spec}: random_counter :=
  {| new_counter := new_counter3;
    allocate_tape:= allocate_tape3;
    incr_counter_tape := incr_counter_tape3;
    read_counter:=read_counter3;
    counterG := counterG3;
    tape_name := rand_tape_name;
    counter_name :=gname;
    is_counter _ N c γ1 γ2 := is_counter3 N c γ1 γ2;
    counter_tapes_auth _ γ m := (∃ (m':gmap loc (nat*list nat)),
                                    ⌜(dom m = dom m')⌝ ∗
                                    ⌜∀ l xs' tb, m'!!l=Some (tb, xs') → tb = 4 ∧ m!!l=Some (filter filter_f xs')⌝ ∗
                                                 rand_tapes_auth (L:=counterG3_randG) γ m')%I;
    counter_tapes_frag _ γ α ns :=
      (∃ ls, ⌜filter filter_f ls = ns⌝ ∗ rand_tapes_frag (L:=counterG3_randG) γ α (4, ls))%I;
    counter_content_auth _ γ z := own γ (●F z);
    counter_content_frag _ γ f z := own γ (◯F{f} z);
    new_counter_spec _ := new_counter_spec3;
    allocate_tape_spec _ :=allocate_tape_spec3;
    incr_counter_tape_spec_some _ :=incr_counter_tape_spec_some3;
    counter_presample_spec _ :=counter_presample_spec3;
    read_counter_spec _ :=read_counter_spec3
  |}.

Next Obligation.
  simpl.
  iIntros (???????) "(%&%&%&?) (%&%&%&?)".
  iApply (rand_tapes_auth_exclusive with "[$][$]").
Qed.
Next Obligation.
  simpl.
  iIntros (????????) "(%&%&?) (%&%&?)".
  iApply (rand_tapes_frag_exclusive with "[$][$]").
Qed.
Next Obligation.
  simpl.
  iIntros (????????) "(%&%&%K&?) (%&%&?)".
  iDestruct (rand_tapes_agree γ α with "[$][$]") as "%K'".
  iPureIntro.
  apply K in K'. subst. naive_solver.
Qed.
Next Obligation.
  simpl.
  iIntros (???????) "(%&%&?)".
  iPureIntro.
  subst.
  induction ls; first done.
  rewrite filter_cons.
  case_decide as H; last done.
  rewrite Forall_cons_iff; split; last done.
  rewrite /filter_f in H. lia.
Qed.
Next Obligation.
  simpl.
  iIntros (??????????) "(%&%&%&?) (%&%&?)".
  iMod (rand_tapes_update _ _ _ _ (_,ns') with "[$][$]") as "[??]"; last iFrame.
  - eapply Forall_impl; first done. simpl; lia.
  - iPureIntro. split; [split; first (rewrite !dom_insert_L; set_solver)|].
    + intros ? xs' ? K.
      rewrite lookup_insert_Some in K.
      destruct K as [[??]|[??]]; simplify_eq.
      * split; first done.
        rewrite lookup_insert_Some; left.
        split; first done.
        by erewrite Forall_filter_f.
      * rewrite lookup_insert_ne; last done.
        naive_solver.
    + by apply Forall_filter_f.
Qed.
Next Obligation.
  simpl.
  iIntros (???????) "H1 H2".
  iCombine "H1 H2" gives "%K". by rewrite auth_auth_op_valid in K.
Qed.
Next Obligation.
  simpl. iIntros (????? z z' ?) "H1 H2".
  iCombine "H1 H2" gives "%K".
  apply frac_auth_included_total in K. iPureIntro.
  by apply nat_included.
Qed.
Next Obligation.
  simpl.
  iIntros (?????????).
  rewrite frac_auth_frag_op. by rewrite own_op.
Qed.
Next Obligation.
  simpl. iIntros (???????) "H1 H2".
  iCombine "H1 H2" gives "%K".
  iPureIntro.
  by apply frac_auth_agree_L in K.
Qed.
Next Obligation.
  simpl. iIntros (?????????) "H1 H2".
  iMod (own_update_2 _ _ _ (_ ⋅ _) with "[$][$]") as "[$$]"; last done.
  apply frac_auth_update.
  apply nat_local_update. lia.
Qed.
