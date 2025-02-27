From iris.algebra Require Import frac_auth.
From iris.base_logic.lib Require Import invariants.
From coneris.coneris Require Import coneris hocap_rand random_counter3.random_counter.

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
  Definition incr_counter3 :val := λ: "l",
                                     let: "α" :=  (rand_allocate_tape #4%nat) in
                                     (rec: "f" "α " :=
                                          let: "n" := rand_tape "α" #4%nat in
                                          if: "n" < #4
                                          then (FAA "l" "n", "n")
                                          else "f" "α") "α".
  Definition read_counter3 : val := λ: "l", !"l".
  Class counterG3 Σ := CounterG3 { counterG3_randG:randG Σ;
                                   counterG3_frac_authR:: inG Σ (frac_authR natR) }.

  Definition counter_inv_pred3 (c:val) γ2:= (∃ (l:loc) (z:nat), ⌜c=#l⌝ ∗ l ↦ #z ∗ own γ2 (●F z) )%I.

  Definition is_counter3 N (c:val) γ1:=
    (inv N (counter_inv_pred3 c γ1))%I.

  Lemma new_counter_spec3 E N:
    {{{ True }}}
      new_counter3 #() @ E
      {{{ (c:val), RET c;
          ∃ γ1, is_counter3 N c γ1 ∗ own γ1 (◯F 0%nat)
      }}}.
  Proof.
    rewrite /new_counter3.
    iIntros (Φ) "_ HΦ".
    wp_pures.
    (* iMod (rand_inv_create_spec) as "(%γ1 & #Hinv)". *)
    wp_alloc l as "Hl".
    iMod (own_alloc (●F 0%nat ⋅ ◯F 0%nat)) as "[%γ1[H5 H6]]".
    { by apply frac_auth_valid. }
    replace (#0) with (#0%nat) by done.
    iMod (inv_alloc _ _ (counter_inv_pred3 (#l) γ1) with "[$Hl $H5]") as "#Hinv'"; first done.
    iApply "HΦ".
    iFrame.
    by iModIntro.
  Qed.
  

  Lemma counter_tapes_presample3 N E γ1 c α ε (ε2 : fin 4%nat -> R):
    (∀ x, 0<=ε2 x)%R ->
    (SeriesC (λ n, 1 / 4 * ε2 n)%R <= ε)%R ->
    is_counter3 N c γ1 -∗
    (∃ ls, ⌜filter filter_f ls = []⌝ ∗ rand_tapes (L:=L) α (4, ls)) -∗
    ↯ ε  -∗
    state_update E E (∃ n, ↯ (ε2 n) ∗
                         (∃ ls, ⌜filter filter_f ls = ([fin_to_nat n])⌝ ∗ rand_tapes (L:=L) α (4, ls))).
  Proof.
    iIntros (Hpos Hineq) "#Hinv Hfrag Herr".
    iMod (state_update_epsilon_err) as "(%ep & %Heps & Heps)".
    iRevert "Hfrag Herr".
    iApply (ec_ind_amp _ (5)%R with "[][$]"); try lra.
    clear ep Heps.
    iModIntro.
    iIntros (eps Heps) "#IH Heps (%ls & %Hfilter & Hfrag) Herr".
    iDestruct (ec_valid with "[$]") as "%".
    iCombine "Heps Herr" as "Herr'".
    iMod (rand_tapes_presample _ _ _ _ _ 
            (λ x, match decide (fin_to_nat x < 4)%nat with
                  | left p => ε2 (nat_to_fin p)
                  | _ => ε + 5*eps
                                  end
            )%R with "[$][$]") as "(%n & Herr & Hfrag)". 
    { intros. case_match; first done.
      apply Rplus_le_le_0_compat; first naive_solver.
      apply Rmult_le_pos; lra.
    }
    { rewrite SeriesC_finite_foldr/=.
      rewrite SeriesC_finite_foldr/= in Hineq.
      lra.
    }
    case_match eqn :K.
    - (* accept *)
      iFrame.
      iPureIntro.
      rewrite filter_app Hfilter. 
      rewrite filter_cons /filter_f filter_nil K.
      f_equal. by rewrite fin_to_nat_to_fin.
    - iDestruct (ec_split with "[$]") as "[Hε Heps]"; first lra.
      { apply Rmult_le_pos; lra. }
      iApply ("IH" with "[$][Hfrag][$]").
      iFrame.
      iPureIntro.
      rewrite filter_app.
      rewrite filter_cons_False; first by rewrite filter_nil app_nil_r.
      rewrite /filter_f. lia.
  Qed.
  
  Lemma incr_counter_spec3 N E c γ1 (Q:_->_->nat->nat->iProp Σ)  :
    ↑N⊆E ->
    {{{ is_counter3 N c γ1 ∗
        |={E,∅}=>
          (∃ ε (ε2 : fin 4%nat -> R),
              ↯ ε ∗ ⌜(∀ x, 0<=ε2 x)%R⌝∗
              ⌜(SeriesC (λ n, 1 / 4 * ε2 n)%R <= ε)%R ⌝ ∗
              (∀ n, ↯ (ε2 n) ={∅, E}=∗
          (∀ (z:nat), own γ1 (●F z) ={E∖↑N}=∗
                    own γ1 (●F (z+n)%nat) ∗ Q ε ε2 z n)))
           
    }}}
      incr_counter3 c @ E
      {{{ (z n:nat), RET (#z, #n); ∃ ε ε2, Q ε ε2 z n }}}.
  Proof.
    iIntros (Hsubset Φ) "(#Hinv & Hvs) HΦ".
    rewrite /incr_counter3.
    wp_pures.
    wp_apply rand_allocate_tape_spec as (α) "Htape"; first done.
    do 3 wp_pure.
    iAssert (state_update E E (∃ n,
                   (∃ ls, ⌜filter filter_f ls = ([fin_to_nat n])⌝ ∗ rand_tapes (L:=L) α (4, ls)) ∗
                                 ∃ ε ε2,  (∀ z : nat, own γ1 (●F z) ={E ∖ ↑N}=∗ own γ1 (●F (z + n)) ∗ Q ε ε2 z n)
            ))%I with "[Hvs Htape]" as ">(%n & Htape &%&%&Hvs)".
    { iMod "Hvs" as "(%&%&?&%&%&Hvs)".
      iMod (counter_tapes_presample3 with "[$][$Htape][$]") as "(%&?&?)"; [try done..|].
      iMod ("Hvs" with "[$]").
      iModIntro.
      iFrame.
    }
    iDestruct "Htape" as "(%ls & %Hfilter &Hfrag)".
    iLöb as "IH" forall (ls Hfilter Φ) "Hfrag".
    wp_pures.
    destruct ls as [|hd ls]; first simplify_eq.
    wp_apply (rand_tape_spec_some with "[$]") as "Hfrag". 
    wp_pures.
    case_bool_decide as K.
    - wp_pures.
      wp_bind (FAA _ _).
      iInv "Hinv" as ">(%&%&-> & ?&?)" "Hclose".
      wp_faa.
      iMod ("Hvs" with "[$]") as "[? HQ]".
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
  
  Lemma read_counter_spec3 N E c γ1 Q:
    ↑N ⊆ E ->
    {{{  is_counter3 N c γ1 ∗
         (∀ (z:nat), own γ1 (●F z) ={E∖↑N}=∗
                     own γ1 (●F z) ∗ Q z)
        
    }}}
      read_counter3 c @ E
      {{{ (n':nat), RET #n'; Q n'
      }}}.
  Proof.
    iIntros (Hsubset Φ) "(#Hinv & Hvs) HΦ".
    rewrite /read_counter3.
    wp_pure.
    iInv "Hinv" as ">( %l & %z & -> & H5 & H6)" "Hclose".
    wp_load.
    (* iMod (fupd_mask_subseteq (E ∖ ↑N)) as "Hclose'". *)
    (* { apply difference_mono_l. *)
    (*   by apply nclose_subseteq'. } *)
    iMod ("Hvs" with "[$]") as "[? HQ]".
    (* iMod "Hclose'" as "_". *)
    iMod ("Hclose" with "[-HQ HΦ]"); first by iFrame.
    iApply ("HΦ" with "[$]").
  Qed.
    
End impl3.

Program Definition random_counter3 `{F:rand_spec}: random_counter :=
  {| new_counter := new_counter3;
    incr_counter := incr_counter3;
    read_counter:=read_counter3;
    counterG := counterG3;
    counter_name :=gname;
    is_counter _ N c γ1 := is_counter3 N c γ1;
    counter_content_auth _ γ z := own γ (●F z);
    counter_content_frag _ γ f z := own γ (◯F{f} z);
    new_counter_spec _ := new_counter_spec3 (L:=counterG3_randG) ;
    incr_counter_spec _ :=incr_counter_spec3 (L:=counterG3_randG);
    read_counter_spec _ :=read_counter_spec3 (L:=counterG3_randG) 
  |}.
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
