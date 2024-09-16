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
    
End impl3. 
