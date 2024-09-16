From iris.algebra Require Import frac_auth.
From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris hocap random_counter.

Set Default Proof Using "Type*".

Section filter.
  Definition filter_f (n:nat):= bool_decide (n<4)%nat.
  Definition filtered_list (l:list _) := filter filter_f l.
End filter.

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
    
End impl3. 
