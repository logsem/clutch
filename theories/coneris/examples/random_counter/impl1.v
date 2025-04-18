From iris.algebra Require Import frac_auth.
From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris hocap_rand random_counter.random_counter.

Set Default Proof Using "Type*".

Section impl1.
  Context `{H:conerisGS Σ, r1:@rand_spec Σ H, L:randG Σ, !inG Σ (frac_authR natR)}.

  Definition new_counter1 : val:= λ: "_", ref #0.
  Definition allocate_tape1 : val := λ: "_", rand_allocate_tape #3%nat.
  Definition incr_counter_tape1 :val := λ: "l" "α", let: "n" := rand_tape "α" #3%nat in (FAA "l" "n", "n").
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

  Lemma allocate_tape_spec1 N E c γ1:
    ↑N ⊆ E->
    {{{ is_counter1 N c γ1 }}}
      allocate_tape1 #() @ E
      {{{ (v:val), RET v; rand_tapes (L:=L) v (3%nat, [])
      }}}.
  Proof.
    iIntros (Hsubset Φ) "#Hinv HΦ".
    rewrite /allocate_tape1.
    wp_pures.
    by wp_apply rand_allocate_tape_spec. 
  Qed.

  Lemma incr_counter_tape_spec_some1 N E c γ1 (Q:nat->iProp Σ) α n ns:
    ↑N⊆E ->
    {{{ is_counter1 N c γ1 ∗
        rand_tapes (L:=L) α (3, n::ns) ∗
        (  ∀ (z:nat), own γ1 (●F z) ={E∖↑N}=∗
                    own γ1 (●F (z+n)) ∗ Q z)
           
    }}}
      incr_counter_tape1 c α @ E
                                 {{{ (z:nat), RET (#z, #n); rand_tapes (L:=L) α (3, ns) ∗
                                                          Q z }}}.
  Proof.
    iIntros (Hsubset Φ) "(#Hinv & Hfrag & Hvs) HΦ".
    rewrite /incr_counter_tape1.
    wp_pures.
    wp_apply (rand_tape_spec_some with "[$]") as "Hfrag". 
    wp_pures.
    wp_bind (FAA _ _).
    iInv "Hinv" as ">(%&%&-> & ?&?)" "Hclose".
    wp_faa.
    (* iMod (fupd_mask_subseteq (E ∖ ↑N)) as "Hclose'". *)
    (* + apply difference_mono_l. *)
    (*   by apply nclose_subseteq'. *)
    (* +  *)
    iMod ("Hvs" with "[$]") as "[? HQ]".
    (* iMod "Hclose'" as "_". *)
    rewrite -Nat2Z.inj_add.
    iMod ("Hclose" with "[-HQ Hfrag HΦ]") as "_"; first by iFrame.
    iModIntro.
    wp_pures.
    iApply "HΦ". by iFrame.
  Qed.

  Lemma counter_tapes_presample1 N E γ1 c α ns ε (ε2 : fin 4%nat -> R):
    ↑N ⊆ E ->
    (∀ x, 0<=ε2 x)%R ->
    (SeriesC (λ n, 1 / 4 * ε2 n)%R <= ε)%R ->
    is_counter1 N c γ1 -∗
    rand_tapes (L:=L) α (3%nat, ns) -∗
    ↯ ε  -∗
    state_update E E (∃ n, ↯ (ε2 n) ∗ rand_tapes (L:=L) α (3%nat, ns++[fin_to_nat n])).
  Proof.
    iIntros (Hsubset Hpos Hineq) "#Hinv Hfrag Herr".
    iMod (rand_tapes_presample with "[$][$]") as "(%&$&$)"; try done.
    etrans; last exact.
    apply Req_le.
    apply SeriesC_ext; intros. simpl. lra.
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
    (* iMod (fupd_mask_subseteq (E ∖ ↑N)) as "Hclose'". *)
    (* { apply difference_mono_l. *)
    (*   by apply nclose_subseteq'. } *)
    iMod ("Hvs" with "[$]") as "[? HQ]".
    (* iMod "Hclose'" as "_". *)
    iMod ("Hclose" with "[-HQ HΦ]"); first by iFrame.
    iApply ("HΦ" with "[$]").
  Qed.
  
End impl1.

Program Definition random_counter1 `{!conerisGS Σ, F:rand_spec}: random_counter :=
  {| new_counter := new_counter1;
    allocate_tape:= allocate_tape1;
    incr_counter_tape := incr_counter_tape1;
    read_counter:=read_counter1;
    counterG := counterG1;
    (* tape_name := rand_tape_name; *)
    counter_name :=gname;
    is_counter _ N c γ1 := is_counter1 N c γ1;
    (* counter_tapes_auth _ γ m :=  rand_tapes_auth (L:=counterG1_randG) γ ((λ ns, (3, ns))<$>m); *)
    counter_tapes _  α ns := rand_tapes (L:= counterG1_randG) α (3%nat, ns);
    counter_content_auth _ γ z := own γ (●F z);
    counter_content_frag _ γ f z := own γ (◯F{f} z);
    counter_tapes_presample _ := counter_tapes_presample1;
    new_counter_spec _ := new_counter_spec1 (L:=counterG1_randG);
    allocate_tape_spec _ :=allocate_tape_spec1;
    incr_counter_tape_spec_some _ :=incr_counter_tape_spec_some1;
    read_counter_spec _ :=read_counter_spec1 (L:=counterG1_randG)
  |}.
(* Next Obligation. *)
(*   simpl. *)
(*   iIntros (?????????) "H1 H2". *)
(*   iDestruct (rand_tapes_auth_exclusive with "[$][$]") as "[]". *)
(* Qed. *)
Next Obligation.
  simpl.
  iIntros.
  iDestruct (rand_tapes_exclusive with "[$][$]") as "[]".
Qed.
(* Next Obligation. *)
(*   simpl. *)
(*   iIntros. *)
(*   iDestruct (rand_tapes_agree with "[$][$]") as "%H". *)
(*   iPureIntro. *)
(*   apply lookup_fmap_Some in H as (?&?&?). *)
(*   by simplify_eq. *)
(* Qed. *)
Next Obligation.
  iIntros.
  iDestruct (rand_tapes_valid with "[$]") as "$".
Qed.
(* Next Obligation. *)
(*   simpl. *)
(*   iIntros. *)
(*   iMod (rand_tapes_update with "[$][$]") as "[??]"; last iFrame; first done. *)
(*   by rewrite fmap_insert. *)
(* Qed. *)
Next Obligation.
  simpl.
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
  
