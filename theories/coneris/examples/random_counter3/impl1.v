From iris.algebra Require Import frac_auth.
From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris hocap_rand random_counter3.random_counter.

Set Default Proof Using "Type*".

Section impl1.
  Context `{H:conerisGS Σ, r1:@rand_spec Σ H, L:randG Σ, !inG Σ (frac_authR natR)}.

  Definition new_counter1 : val:= λ: "_", ref #0.
  Definition incr_counter1 :val := λ: "l", let: "n" := rand #3%nat in (FAA "l" "n", "n").
  Definition read_counter1 : val := λ: "l", !"l".
  Class counterG1 Σ := CounterG1 { counterG1_randG : randG Σ;
                                   counterG1_frac_authR:: inG Σ (frac_authR natR) }.

  Definition counter_inv_pred1 c γ2 := (∃ (l:loc) (z:nat), ⌜c=#l⌝ ∗ l ↦ #z ∗ own γ2 (●F z) )%I.
  Definition is_counter1 N (c:val) γ1:=
    (
    inv (N) (counter_inv_pred1 c γ1)
    )%I.

  Lemma new_counter_spec1 E N:
    {{{ True }}}
      new_counter1 #() @ E
      {{{ (c:val), RET c;
          ∃ γ1, is_counter1 N c γ1 ∗ own γ1 (◯F 0%nat)
      }}}.
  Proof.
    rewrite /new_counter1.
    iIntros (Φ) "_ HΦ".
    wp_pures.
    (* iMod (rand_inv_create_spec) as "(%γ1 & #Hinv)". *)
    wp_alloc l as "Hl".
    iMod (own_alloc (●F 0%nat ⋅ ◯F 0%nat)) as "[%γ1[H5 H6]]".
    { by apply frac_auth_valid. }
    replace (#0) with (#0%nat) by done.
    iMod (inv_alloc _ _ (counter_inv_pred1 (#l) γ1) with "[$Hl $H5]") as "#Hinv'"; first done.
    iApply "HΦ".
    iFrame.
    by iModIntro.
  Qed.


  Lemma incr_counter_spec1 N E c γ1 (Q:_->_->nat->nat->iProp Σ)  :
    ↑N⊆E ->
    {{{ is_counter1 N c γ1 ∗
        |={E∖↑N, ∅}=>
          (∃ ε (ε2 : fin 4%nat -> R),
              ↯ ε ∗ ⌜(∀ x, 0<=ε2 x)%R⌝∗
              ⌜(SeriesC (λ n, 1 / 4 * ε2 n)%R <= ε)%R ⌝ ∗
              (∀ n, ↯ (ε2 n) ={∅, E∖↑N}=∗
          (∀ (z:nat), own γ1 (●F z) ={E∖↑N}=∗
                      own γ1 (●F (z+n)%nat) ∗ Q ε ε2 z n)))
    }}}
      incr_counter1 c @ E
                                 {{{ (z n:nat), RET (#z, #n); ∃ ε ε2, Q ε ε2 z n }}}.
  Proof.
    iIntros (Hineq Φ) "[#Hinv Hvs] HΦ".
    rewrite /incr_counter1.
    wp_pures.
    wp_bind (rand _)%E.
    iApply pgl_wp_mask_mono; last iMod "Hvs" as "(%&%&?&%&%&Hvs)".
    { by apply namespaces.coPset_subseteq_difference_l. }
    wp_apply (wp_couple_rand_adv_comp1' with "[$]"); [done|simpl|].
    { replace (_+_+_+_)%R with 4%R; [done|lra]. }
    iIntros.
    iMod ("Hvs" with "[$]") as "Hvs".
    iModIntro. 
    wp_pures.
    wp_bind (FAA _ _)%E.
    iInv "Hinv" as ">( %l & %z & -> & H5 & H6)" "Hclose".
    wp_faa.
    iMod ("Hvs" with "[$]") as "[? HQ]".
    rewrite -Nat2Z.inj_add.
    iMod ("Hclose" with "[-HQ HΦ]"); first by iFrame.
    iModIntro. wp_pures.
    iApply ("HΦ" with "[$]").
  Qed.
  
  
  Lemma read_counter_spec1 N E c γ1 Q:
    ↑N ⊆ E ->
    {{{  is_counter1 N c γ1 ∗
         (∀ (z:nat), own γ1 (●F z) ={E∖↑N}=∗
                     own γ1 (●F z) ∗ Q z)
        
    }}}
      read_counter1 c @ E
      {{{ (n':nat), RET #n'; Q n'
      }}}.
  Proof.
    iIntros (Hsubset Φ) "(#Hinv & Hvs) HΦ".
    rewrite /read_counter1.
    wp_pure.
    iInv "Hinv" as ">( %l & %z & -> & H5 & H6)" "Hclose".
    wp_load.
    iMod ("Hvs" with "[$]") as "[? HQ]".
    (* iMod "Hclose'" as "_". *)
    iMod ("Hclose" with "[-HQ HΦ]"); first by iFrame.
    iApply ("HΦ" with "[$]").
  Qed.
  
End impl1.

Program Definition random_counter1 `{!conerisGS Σ, F:rand_spec}: random_counter :=
  {| new_counter := new_counter1;
    incr_counter := incr_counter1;
    read_counter:=read_counter1;
    counterG := counterG1;
    counter_name :=gname;
    is_counter _ N c γ1 := is_counter1 N c γ1;
    counter_content_auth _ γ z := own γ (●F z);
    counter_content_frag _ γ f z := own γ (◯F{f} z);
    new_counter_spec _ := new_counter_spec1 (L:=counterG1_randG);
    incr_counter_spec _ :=incr_counter_spec1 (L:=counterG1_randG);
    read_counter_spec _ :=read_counter_spec1 (L:=counterG1_randG)
  |}.
Next Obligation.
  iIntros (?????????) "H1 H2".
  iCombine "H1 H2" gives "%H". by rewrite auth_auth_op_valid in H.
Qed.
Next Obligation.
  simpl. iIntros (??????? z z' ?) "H1 H2".
  iCombine "H1 H2" gives "%H".
  apply frac_auth_included_total in H. iPureIntro.
  by apply nat_included.
Qed.
Next Obligation.
  simpl.
  iIntros.
  rewrite frac_auth_frag_op. rewrite own_op.
  iSplit; iIntros; iFrame.
Qed.
Next Obligation.
  simpl. iIntros (?????????) "H1 H2".
  iCombine "H1 H2" gives "%H".
  iPureIntro.
  by apply frac_auth_agree_L in H.
Qed.
Next Obligation.
  simpl. iIntros (???????????) "H1 H2".
  iMod (own_update_2 _ _ _ (_ ⋅ _) with "[$][$]") as "[$$]"; last done.
  apply frac_auth_update.
  apply nat_local_update. lia.
Qed.
  
