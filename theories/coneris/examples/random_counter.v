From iris.algebra Require Import frac_auth.
From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris hocap.

Set Default Proof Using "Type*".

Section impl1.

  Definition new_counter : val:= λ: "_", ref #0.
  Definition incr_counter : val := λ: "l", let: "n" := rand #3 in FAA "l" "n";; "n".
  Definition allocate_tape : val := λ: "_", AllocTape #3.
  Definition incr_counter_tape :val := λ: "l" "α", let: "n" := rand("α") #3 in FAA "l" "n";; "n".

  Context `{!conerisGS Σ, !hocap_errorGS Σ, !hocap_tapesGS Σ, !inG Σ (frac_authR ZR)}.
  Definition counter_inv_pred (c:val) γ1 γ2 γ3:=
    (∃ (ε:R) m (l:loc) (z:Z),
        ↯ ε ∗ ●↯ ε @ γ1 ∗
        ([∗ map] α ↦ t ∈ m, α ↪N ( t.1 ; t.2 )) ∗ ●m@γ2 ∗  
        ⌜c=#l⌝ ∗ l ↦ #z ∗ own γ3 (●F z)
    )%I.

  Definition counter_nroot := nroot.@"counter".

  Lemma new_counter_spec ε:
    {{{ ↯ ε }}}
      new_counter #()
      {{{ (c:val), RET c;
          ∃ γ1 γ2 γ3, inv counter_nroot (counter_inv_pred c γ1 γ2 γ3) ∗
                      ◯↯ε @ γ1 ∗ own γ3 (◯F 0%Z)
      }}}.
  Proof.
    rewrite /new_counter.
    iIntros (Φ) "Hε HΦ".
    wp_pures.
    wp_alloc l as "Hl".
    iDestruct (ec_valid with "[$]") as "%".
    unshelve iMod (hocap_error_alloc (mknonnegreal ε _)) as "[%γ1 [H1 H2]]".
    { lra. }
    simpl.
    iMod (hocap_tapes_alloc (∅:gmap _ _)) as "[%γ2 [H3 H4]]".
    iMod (own_alloc (●F 0%Z ⋅ ◯F 0%Z)) as "[%γ3[H5 H6]]".
    { by apply frac_auth_valid. }
    iMod (inv_alloc counter_nroot _ (counter_inv_pred (#l) γ1 γ2 γ3) with "[$Hε $Hl $H1 $H3 $H5]") as "#Hinv".
    { iSplit; last done. by iApply big_sepM_empty. }
    iApply "HΦ".
    iExists _, _, _. by iFrame.
  Qed. 

  Lemma incr_counter_spec c γ1 γ2 γ3 (ε2:R -> nat -> R) (P: iProp Σ) (T Q: nat -> iProp Σ):
    (∀ ε n, 0<= ε -> 0<= ε2 ε n)%R->
    (∀ (ε:R), 0<=ε -> ((ε2 ε 0%nat) + (ε2 ε 1%nat)+ (ε2 ε 2%nat)+ (ε2 ε 3%nat))/4 <= ε)%R →
    {{{ inv counter_nroot (counter_inv_pred c γ1 γ2 γ3) ∗
        □(∀ (ε:R) (n : nat), P ∗ ●↯ ε @ γ1 ={⊤∖↑counter_nroot}=∗ (⌜(1<=ε2 ε n)%R⌝∨●↯ (ε2 ε n) @ γ1 ∗ T n) ) ∗
        □ (∀ (n:nat) (z:Z), T n ∗ own γ3 (●F z) ={⊤∖↑counter_nroot}=∗
                          own γ3 (●F(z+n)%Z)∗ Q n) ∗
        P
    }}}
      incr_counter c
      {{{ (n:nat), RET #n; Q n }}}.
  Proof.
    iIntros (Hpos Hineq Φ) "(#Hinv & #Hvs1 & #Hvs2 & HP) HΦ".
    rewrite /incr_counter.
    wp_pures.
    wp_bind (rand _)%E.
    iInv counter_nroot as ">(%ε & %m & %l & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    iDestruct (ec_valid with "[$]") as "[%K1 %K2]".
    wp_apply (wp_couple_rand_adv_comp1' _ _ _ _ (λ x, ε2 ε (fin_to_nat x)) with "[$]").
    { intros. naive_solver. }
    { rewrite SeriesC_finite_foldr; specialize (Hineq ε K1). simpl; lra. }
    iIntros (n) "H1".
    iMod ("Hvs1" with "[$]") as "[%|[H2 HT]]".
    { iExFalso. iApply ec_contradict; last done. done. }
    iMod ("Hclose" with "[$H1 $H2 $H3 $H4 $H5 $H6]") as "_"; first done.
    iModIntro. wp_pures.
    clear.
    wp_bind (FAA _ _).
    iInv counter_nroot as ">(%ε & %m & % & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    wp_faa.
    iMod ("Hvs2" with "[$]") as "[H6 HQ]".
    iMod ("Hclose" with "[$H1 $H2 $H3 $H4 $H5 $H6]") as "_"; first done.
    iModIntro.
    wp_pures.
    by iApply "HΦ".
  Qed.

  Lemma allocate_tape_spec c γ1 γ2 γ3:
    {{{ inv counter_nroot (counter_inv_pred c γ1 γ2 γ3) }}}
      allocate_tape #()
      {{{ (v:val), RET v;
          ∃ (α:loc), ⌜v=#lbl:α⌝ ∗ α ◯↪N (3%nat; []) @ γ2
      }}}.
  Proof.
    iIntros (Φ) "#Hinv HΦ".
    rewrite /allocate_tape.
    wp_pures.
    wp_alloctape α as "Hα".
    iInv counter_nroot as ">(%ε & %m & %l & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    iDestruct (hocap_tapes_notin with "[$][$]") as "%".
    iMod (hocap_tapes_new with "[$]") as "[H4 H7]"; first done.
    iMod ("Hclose" with "[$H1 $H2 H3 $H4 $H5 $H6 Hα]") as "_".
    { iNext. iSplitL; last done.
      rewrite big_sepM_insert; [simpl; iFrame|done].
    }
    iApply "HΦ".
    by iFrame.
  Qed.

  Lemma incr_counter_tape_spec c γ1 γ2 γ3 (ε2:R -> nat -> R) (P Q: iProp Σ) (α:loc) (n:nat) ns:
    {{{ inv counter_nroot (counter_inv_pred c γ1 γ2 γ3) ∗
        □ (∀ (z:Z), P ∗ own γ3 (●F z) ={⊤∖↑counter_nroot}=∗
                          own γ3 (●F(z+n)%Z)∗ Q) ∗
        P ∗ α ◯↪N (3%nat; n::ns) @ γ2
    }}}
      incr_counter_tape c #lbl:α
      {{{ RET #n; Q ∗ α ◯↪N (3%nat; ns) @ γ2}}}.
  Proof.
    iIntros (Φ) "(#Hinv & #Hvs & HP & Hα) HΦ".
    rewrite /incr_counter_tape.
    wp_pures.
    wp_bind (rand(_) _)%E.
    iInv counter_nroot as ">(%ε & %m & %l & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    iDestruct (hocap_tapes_agree with "[$][$]") as "%".
    erewrite <-(insert_delete m) at 1; last done.
    rewrite big_sepM_insert; last apply lookup_delete.
    simpl.
    iDestruct "H3" as "[Htape H3]".
    wp_apply (wp_rand_tape with "[$]").
    iIntros "[Htape %]".
    iMod (hocap_tapes_pop with "[$][$]") as "[H4 Hα]".
    iMod ("Hclose" with "[$H1 $H2 H3 $H4 $H5 $H6 Htape]") as "_".
    { iSplitL; last done.
      erewrite <-(insert_delete m) at 2; last done.
      iNext.
      rewrite insert_insert.
      rewrite big_sepM_insert; last apply lookup_delete. iFrame.
    }
    iModIntro.
    wp_pures.
    clear.
    wp_bind (FAA _ _).
    iInv counter_nroot as ">(%ε & %m & % & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    wp_faa.
    iMod ("Hvs" with "[$]") as "[H6 HQ]".
    iMod ("Hclose" with "[$H1 $H2 $H3 $H4 $H5 $H6]") as "_"; first done.
    iModIntro. wp_pures.
    iApply "HΦ".
    by iFrame.
  Qed. 
    
    
    
End impl1.
