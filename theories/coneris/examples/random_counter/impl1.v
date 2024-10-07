From iris.algebra Require Import frac_auth.
From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris hocap hocap_rand random_counter.

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
  Definition is_counter1 N (c:val) γ1 γ2:=
    (is_rand (L:=L) (N.@"rand") γ1 ∗
    inv (N.@"counter") (counter_inv_pred1 c γ2)
    )%I.

  Lemma new_counter_spec1 E N:
    {{{ True }}}
      new_counter1 #() @ E
      {{{ (c:val), RET c;
          ∃ γ1 γ2, is_counter1 N c γ1 γ2 ∗ own γ2 (◯F 0%nat)
      }}}.
  Proof.
    rewrite /new_counter1.
    iIntros (Φ) "_ HΦ".
    wp_pures.
    iMod (rand_inv_create_spec) as "(%γ1 & #Hinv)".
    wp_alloc l as "Hl".
    iMod (own_alloc (●F 0%nat ⋅ ◯F 0%nat)) as "[%γ2[H5 H6]]".
    { by apply frac_auth_valid. }
    replace (#0) with (#0%nat) by done.
    iMod (inv_alloc _ _ (counter_inv_pred1 (#l) γ2) with "[$Hl $H5]") as "#Hinv'"; first done.
    iApply "HΦ".
    iFrame.
    iModIntro.
    iExists _. by iSplit.
  Qed.

  (* (** Not used in instantiating type class*) *)
  (* Lemma incr_counter_spec1 E N c γ1 γ2 γ3 (ε2:R -> nat -> R) (P: iProp Σ) (T: nat -> iProp Σ) (Q: nat->nat->iProp Σ): *)
  (*   ↑N ⊆ E-> *)
  (*   (∀ ε n, 0<= ε -> 0<= ε2 ε n)%R-> *)
  (*   (∀ (ε:R), 0<=ε -> ((ε2 ε 0%nat) + (ε2 ε 1%nat)+ (ε2 ε 2%nat)+ (ε2 ε 3%nat))/4 <= ε)%R → *)
  (*   {{{ inv N (counter_inv_pred1 c γ1 γ2 γ3) ∗ *)
  (*       □(∀ (ε:R) (n : nat), P ∗ ●↯ ε @ γ1 ={E∖↑N}=∗ (⌜(1<=ε2 ε n)%R⌝∨●↯ (ε2 ε n) @ γ1 ∗ T n) ) ∗ *)
  (*       □ (∀ (n z:nat), T n ∗ own γ3 (●F z) ={E∖↑N}=∗ *)
  (*                         own γ3 (●F(z+n)%nat)∗ Q z n) ∗ *)
  (*       P *)
  (*   }}} *)
  (*     incr_counter1 c @ E *)
  (*     {{{ (n:nat) (z:nat), RET (#z, #n); Q z n }}}. *)
  (* Proof. *)
  (*   iIntros (Hsubset Hpos Hineq Φ) "(#Hinv & #Hvs1 & #Hvs2 & HP) HΦ". *)
  (*   rewrite /incr_counter1. *)
  (*   wp_pures. *)
  (*   wp_bind (rand _)%E. *)
  (*   iInv N as ">(%ε & %m & %l & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose". *)
  (*   iDestruct (ec_valid with "[$]") as "[%K1 %K2]". *)
  (*   wp_apply (wp_couple_rand_adv_comp1' _ _ _ _ (λ x, ε2 ε (fin_to_nat x)) with "[$]"). *)
  (*   { intros. naive_solver. } *)
  (*   { rewrite SeriesC_finite_foldr; specialize (Hineq ε K1). simpl; lra. } *)
  (*   iIntros (n) "H1". *)
  (*   iMod ("Hvs1" with "[$]") as "[%|[H2 HT]]". *)
  (*   { iExFalso. iApply ec_contradict; last done. done. } *)
  (*   iMod ("Hclose" with "[$H1 $H2 $H3 $H4 $H5 $H6]") as "_"; first done. *)
  (*   iModIntro. wp_pures. *)
  (*   clear -Hsubset. *)
  (*   wp_bind (FAA _ _). *)
  (*   iInv N as ">(%ε & %m & % & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose". *)
  (*   wp_faa. *)
  (*   iMod ("Hvs2" with "[$]") as "[H6 HQ]". *)
  (*   replace (#(z+n)) with (#(z+n)%nat); last first. *)
  (*   { by rewrite Nat2Z.inj_add. } *)
  (*   iMod ("Hclose" with "[$H1 $H2 $H3 $H4 $H5 $H6]") as "_"; first done. *)
  (*   iModIntro. *)
  (*   wp_pures. *)
  (*   by iApply "HΦ". *)
  (* Qed. *)

  Lemma allocate_tape_spec1 N E c γ1 γ2:
    ↑N ⊆ E->
    {{{ is_counter1 N c γ1 γ2 }}}
      allocate_tape1 #() @ E
      {{{ (v:val), RET v;
          ∃ (α:loc), ⌜v=#lbl:α⌝ ∗ rand_tapes_frag (L:=L) γ1 α (3%nat, [])
      }}}.
  Proof.
    iIntros (Hsubset Φ) "[#Hinv #Hinv'] HΦ".
    rewrite /allocate_tape1.
    wp_pures.
    wp_apply rand_allocate_tape_spec; [by eapply nclose_subseteq'|done..].
  Qed.

  Lemma incr_counter_tape_spec_some1 N E c γ1 γ2 (Q:nat->iProp Σ) (α:loc) n ns:
    ↑N⊆E ->
    {{{ is_counter1 N c γ1 γ2 ∗
        rand_tapes_frag (L:=L) γ1 α (3, n::ns) ∗
        (  ∀ (z:nat), own γ2 (●F z) ={E∖↑N}=∗
                    own γ2 (●F (z+n)) ∗ Q z)
           
    }}}
      incr_counter_tape1 c #lbl:α @ E
                                 {{{ (z:nat), RET (#z, #n); rand_tapes_frag (L:=L) γ1 α (3, ns) ∗
                                                          Q z }}}.
  Proof.
    iIntros (Hsubset Φ) "([#Hinv #Hinv'] & Hfrag & Hvs) HΦ".
    rewrite /incr_counter_tape1.
    wp_pures.
    wp_apply (rand_tape_spec_some with "[$]") as "Hfrag"; first by eapply nclose_subseteq'. 
    wp_pures.
    wp_bind (FAA _ _).
    iInv "Hinv'" as ">(%&%&-> & ?&?)" "Hclose".
    wp_faa.
    iMod (fupd_mask_subseteq (E ∖ ↑N)) as "Hclose'".
    + apply difference_mono_l.
      by apply nclose_subseteq'.
    + iMod ("Hvs" with "[$]") as "[? HQ]".
      iMod "Hclose'" as "_".
      rewrite -Nat2Z.inj_add.
      iMod ("Hclose" with "[-HQ Hfrag HΦ]") as "_"; first by iFrame.
      iModIntro.
      wp_pures.
      iApply "HΦ". by iFrame.
  Qed.

  Lemma counter_tapes_presample1 N E γ1 γ2 c α ns ε (ε2 : fin 4%nat -> R):
    ↑N ⊆ E ->
    (∀ x, 0<=ε2 x)%R ->
    (SeriesC (λ n, 1 / 4 * ε2 n)%R <= ε)%R ->
    is_counter1 N c γ1 γ2  -∗
    rand_tapes_frag (L:=L) γ1 α (3%nat, ns) -∗
    ↯ ε  -∗
    state_update E (∃ n, ↯ (ε2 n) ∗ rand_tapes_frag (L:=L) γ1 α (3%nat, ns++[fin_to_nat n])).
  Proof.
    iIntros (Hsubset Hpos Hineq) "[#Hinv #Hinv'] Hfrag Herr".
    iMod (rand_tapes_presample with "[//][$][$]") as "(%&$&$)"; try done; first by apply nclose_subseteq'.
    etrans; last exact.
    apply Req_le.
    apply SeriesC_ext; intros. simpl. lra.
  Qed.
  
  Lemma read_counter_spec1 N E c γ1 γ2 Q:
    ↑N ⊆ E ->
    {{{  is_counter1 N c γ1 γ2  ∗
         (∀ (z:nat), own γ2 (●F z) ={E∖↑N}=∗
                     own γ2 (●F z) ∗ Q z)
        
    }}}
      read_counter1 c @ E
      {{{ (n':nat), RET #n'; Q n'
      }}}.
  Proof.
    iIntros (Hsubset Φ) "([#Hinv #Hinv'] & Hvs) HΦ".
    rewrite /read_counter1.
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
  
End impl1.

Program Definition random_counter1 `{!conerisGS Σ, F:rand_spec}: random_counter :=
  {| new_counter := new_counter1;
    allocate_tape:= allocate_tape1;
    incr_counter_tape := incr_counter_tape1;
    read_counter:=read_counter1;
    counterG := counterG1;
    tape_name := rand_tape_name;
    counter_name :=gname;
    is_counter _ N c γ1 γ2 := is_counter1 (L:=counterG1_randG) N c γ1 γ2;
    counter_tapes_auth _ γ m :=  rand_tapes_auth (L:=counterG1_randG) γ ((λ ns, (3, ns))<$>m);
    counter_tapes_frag _ γ α ns := rand_tapes_frag (L:= counterG1_randG)γ α (3%nat, ns);
    counter_content_auth _ γ z := own γ (●F z);
    counter_content_frag _ γ f z := own γ (◯F{f} z);
    counter_tapes_presample _ := counter_tapes_presample1;
    new_counter_spec _ := new_counter_spec1;
    allocate_tape_spec _ :=allocate_tape_spec1;
    incr_counter_tape_spec_some _ :=incr_counter_tape_spec_some1;
    read_counter_spec _ :=read_counter_spec1
  |}.
Next Obligation.
  simpl.
  iIntros (?????????) "H1 H2".
  iDestruct (rand_tapes_auth_exclusive with "[$][$]") as "[]".
Qed.
Next Obligation.
  simpl.
  iIntros.
  iDestruct (rand_tapes_frag_exclusive with "[$][$]") as "[]".
Qed.
Next Obligation.
  simpl.
  iIntros.
  iDestruct (rand_tapes_agree with "[$][$]") as "%H".
  iPureIntro.
  apply lookup_fmap_Some in H as (?&?&?).
  by simplify_eq.
Qed.
Next Obligation.
  iIntros.
  iDestruct (rand_tapes_valid with "[$]") as "$".
Qed.
Next Obligation.
  simpl.
  iIntros.
  iMod (rand_tapes_update with "[$][$]") as "[??]"; last iFrame; first done.
  by rewrite fmap_insert.
Qed.
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
  
