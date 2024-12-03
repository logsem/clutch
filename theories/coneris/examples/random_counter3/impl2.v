From iris.algebra Require Import frac_auth.
From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris random_counter3.random_counter hocap_flip.

Set Default Proof Using "Type*".

Local Definition expander (l:list nat):=
  l ≫= (λ x, [2<=?x; (Nat.odd x)]).
Local Lemma expander_eta x: x<4->(Z.of_nat x=  Z.of_nat 2*Z.b2z (2<=? x)%nat +  Z.b2z (Nat.odd x))%Z.
Proof.
  destruct x as [|[|[|[|]]]]; last lia; intros; simpl; lia.
Qed.

Local Lemma expander_inj l1 l2: Forall (λ x, x<4) l1 ->
                                   Forall (λ y, y<4) l2 ->
                                   expander l1 = expander l2 ->
                                   l1 = l2. 
Proof.
  rewrite /expander.
  revert l2.
  induction l1 as [|x xs IH].
  - simpl.
    by intros [] ???.
  - simpl.
    intros [|y ys]; simpl; first done.
    rewrite !Forall_cons.
    rewrite /Nat.odd.
    intros [K1 H1] [K2 H2] H.
    simplify_eq.
    f_equal; last naive_solver.
    repeat (destruct x as [|x]; try lia);
      repeat (destruct y as [|y]; try lia);
      simpl in *; simplify_eq.
Qed.

Local Fixpoint decoder (l:list bool) :=
  match l with
  |[] => Some []
  | b::b'::ls =>
      res← decoder ls;
      Some (((bool_to_nat b)*2+(bool_to_nat b'))::res)
  | _ => None
end.

(* Lemma decoder_unfold l: *)
(*   decoder l =  *)
(*   match l with *)
(*   |[] => Some [] *)
(*   | b::b'::ls => *)
(*       res← decoder ls; *)
(*       Some (((bool_to_nat b)*2+(bool_to_nat b'))::res) *)
(* | _ => None end. *)
(* Proof. *)
(*   induction l; by rewrite {1}/decoder. *)
(* Qed. *)

Local Lemma decoder_correct bs ns: decoder bs = Some ns -> expander ns = bs.
Proof.
  revert bs.
  induction ns.
  - intros bs H. simpl. destruct bs as [|?[|??]]; try done.
    simpl in *.
    rewrite bind_Some in H.
    destruct H as (?&?&?).
    simplify_eq.
  - intros [|b[|b' ?]]; simpl; try done.
    intros H.
    rewrite bind_Some in H.
    destruct H as (?&?&?).
    simplify_eq.
    repeat f_equal; last naive_solver; destruct b; destruct b'; done.
Qed.
      
    
Local Lemma decoder_inj x y z: decoder x = Some z -> decoder y = Some z -> x= y.
Proof.
  intros H1 H2.
  apply decoder_correct in H1, H2.
  by subst.
Qed.

Local Lemma decoder_ineq bs xs: decoder bs = Some xs -> Forall (λ x : nat, x < 4) xs.
Proof.
  revert bs.
  induction xs; first by (intros; apply Forall_nil).
  intros [|b[|b'?]] H; try simplify_eq.
  rewrite bind_Some in H.
  destruct H as (?&?&?).
  simplify_eq.
  rewrite Forall_cons.
  split; last naive_solver.
  destruct b, b'; simpl; lia.
Qed.

Local Lemma decoder_None p bs : length bs = p -> decoder bs = None -> ¬ ∃ num, length bs = 2 * num.
Proof.
  revert bs.
  induction (lt_wf p) as [x ? IH].
  destruct x.
  - intros []??; simplify_eq.
  - intros [|?[|??]]; intros Hlen H'; simplify_eq.
    + simpl in *. simplify_eq.
      intros (num&?).
      destruct num; lia.
    + simpl in *.
      simplify_eq.
      rewrite bind_None in H'.
      destruct H' as [|(?&?&?)]; last done.
      unshelve epose proof IH (length l) _ l _ _ as H1; try lia; try done.
      intros (num & ?). apply H1.
      exists (num-1). lia.
Qed.

Local Lemma decoder_Some_length bs xs: decoder bs = Some xs -> length bs = 2 * length xs.
Proof.
  revert bs.
  induction xs as [|x xs IH]; intros [|?[|??]] H; simpl in *; simplify_eq; try done.
  - rewrite bind_Some in H.
    destruct H as (?&?&?).
    simplify_eq.
  - rewrite bind_Some in H.
    destruct H as (?&?&?).
    simplify_eq.
    f_equal. rewrite IH; [lia|done].
Qed.


Section impl2.
  Context `{F: flip_spec Σ}.
  Definition new_counter2 : val:= λ: "_", ref #0.
  Definition incr_counter2 :val := λ: "l", let: "α" := (flip_allocate_tape #()) in
                                           let: "n" :=
                                             conversion.bool_to_int (flip_tape "α")
                                           in
                                           let: "n'" :=
                                             conversion.bool_to_int (flip_tape "α")
                                           in
                                           let: "x" := #2 * "n" + "n'" in
                                           (FAA "l" "x", "x").
  Definition read_counter2 : val := λ: "l", !"l".
  Class counterG2 Σ := CounterG2 { (* counterG2_tapes:: hocap_tapesGS' Σ; *)
                                   counterG2_frac_authR:: inG Σ (frac_authR natR);
                                   counterG2_flipG: flipG Σ
                         }.
  
  Context `{L:!flipG Σ, !inG Σ (frac_authR natR)}.
  
  
  Definition counter_inv_pred2 (c:val) γ :=
    (∃ (l:loc) (z:nat),
        ⌜c=#l⌝ ∗ l ↦ #z ∗ own γ (●F z)
    )%I.

  Definition is_counter2 N (c:val) γ1:=
    ((* is_flip (L:=L) (N.@"flip") γ1 ∗ *)
    inv (N) (counter_inv_pred2 c γ1)
    )%I.

  Lemma new_counter_spec2 E N:
    {{{ True }}}
      new_counter2 #() @ E
      {{{ (c:val), RET c;
          ∃ γ1, is_counter2 N c γ1 ∗ own γ1 (◯F 0%nat)
      }}}.
  Proof.
    rewrite /new_counter2.
    iIntros (Φ) "_ HΦ".
    wp_pures.
    (* iMod (flip_inv_create_spec) as "(%γ1 & #Hinv)". *)
    wp_alloc l as "Hl".
    iMod (own_alloc (●F 0%nat ⋅ ◯F 0%nat)) as "[%γ1[H5 H6]]".
    { by apply frac_auth_valid. }
    replace (#0) with (#0%nat) by done.
    iMod (inv_alloc _ _ (counter_inv_pred2 (#l) γ1) with "[$Hl $H5]") as "#Hinv'"; first done.
    iApply "HΦ".
    iFrame.
    by iModIntro.
  Qed.


  (** This lemma is not possible as only one view shift*)
  (* Lemma incr_counter_spec2 E N c γ1 γ2 γ3 (ε2:R -> nat -> R) (P: iProp Σ) (T: nat -> iProp Σ) (Q: nat->nat->iProp Σ): *)
  (*   ↑N ⊆ E-> *)
  (*   (∀ ε n, 0<= ε -> 0<= ε2 ε n)%R-> *)
  (*   (∀ (ε:R), 0<=ε -> ((ε2 ε 0%nat) + (ε2 ε 1%nat)+ (ε2 ε 2%nat)+ (ε2 ε 3%nat))/4 <= ε)%R → *)
  (*   {{{ inv N (counter_inv_pred2 c γ1 γ2 γ3) ∗ *)
  (*       □(∀ (ε:R) (n : nat), P ∗ ●↯ ε @ γ1 ={E∖↑N}=∗ (⌜(1<=ε2 ε n)%R⌝∨●↯ (ε2 ε n) @ γ1 ∗ T n) ) ∗ *)
  (*       □ (∀ (n z:nat), T n ∗ own γ3 (●F z) ={E∖↑N}=∗ *)
  (*                         own γ3 (●F(z+n)%nat)∗ Q z n) ∗ *)
  (*       P *)
  (*   }}} *)
  (*     incr_counter2 c @ E *)
  (*     {{{ (n:nat) (z:nat), RET (#z, #n); Q z n }}}. *)
  (* Proof. *)
  (*   iIntros (Hsubset Hpos Hineq Φ) "(#Hinv & #Hvs1 & #Hvs2 & HP) HΦ". *)
  (*   rewrite /incr_counter2. *)
  (*   wp_pures. *)
  (*   wp_bind (rand _)%E. *)
  (*   iInv N as ">(%ε & %m & %l & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose". *)
  (*   (** cant do two view shifts! *) *)
  (* Abort. *)

  (* Lemma allocate_tape_spec2 N E c γ1: *)
  (*   ↑N ⊆ E-> *)
  (*   {{{ is_counter2 N c γ1 }}} *)
  (*     allocate_tape2 #() @ E *)
  (*     {{{ (v:val), RET v; (flip_tapes (L:=L) v (expander []) ∗ ⌜Forall (λ x, x<4) []⌝) *)
  (*     }}}. *)
  (* Proof. *)
  (*   iIntros (Hsubset Φ) "#Hinv HΦ".     *)
  (*   rewrite /allocate_tape2. *)
  (*   wp_pures. *)
  (*   wp_apply flip_allocate_tape_spec; first done. *)
  (*   iIntros (?) "?". *)
  (*   iApply "HΦ". *)
  (*   iFrame. *)
  (*   iPureIntro.  *)
  (*   by apply Forall_nil. *)
  (* Qed. *)

  
  Lemma counter_tapes_presample2 N E γ1 c α ε (ε2 : fin 4%nat -> R):
    (∀ x, 0<=ε2 x)%R ->
    (SeriesC (λ n, 1 / 4 * ε2 n)%R <= ε)%R ->
    is_counter2 N c γ1  -∗
    (flip_tapes (L:=L) α (expander []) ∗ ⌜Forall (λ x, x<4) []⌝) -∗
    ↯ ε  -∗
    state_update E E (∃ n, ↯ (ε2 n) ∗
                         (flip_tapes (L:=L) α (expander ([fin_to_nat n])) ∗ ⌜Forall (λ x, x<4) ([fin_to_nat n])⌝)).
  Proof.
    iIntros (Hpos Hineq) "#Hinv' [Hfrag %Hforall] Herr".
    iMod (flip_tapes_presample _ _ _ _ (λ b, 1/2 *if b then (ε2 2%fin + ε2 3%fin) else (ε2 0%fin + ε2 1%fin))%R with "[$][$]") as "(%b & Herr & Hfrag)".
    { intros []; apply Rmult_le_pos; try lra.
      all: by apply Rplus_le_le_0_compat. } 
    { etrans; last exact.
      rewrite SeriesC_finite_foldr/=. lra. }
    destruct b.
    - iMod (flip_tapes_presample _ _ _ _ (λ b, if b then ε2 3%fin else ε2 2%fin)%R with "[$][$]") as "(%b & Herr & Hfrag)".
      { intros []; by try lra. }
      { simpl. lra. }
      destruct b.
      + iFrame. rewrite /expander  -!app_assoc/=.
        rewrite Nat.OddT_odd; last (constructor 1 with (x:=1); lia). iFrame.
        iPureIntro. naive_solver.
      + iFrame. rewrite /expander -!app_assoc/=.
        rewrite Nat.odd_2. iFrame.
        iPureIntro. naive_solver.
    - iMod (flip_tapes_presample _ _ _ _  (λ b, if b then ε2 1%fin else ε2 0%fin)%R with "[$][$]") as "(%b & Herr & Hfrag)".
      { intros []; by try lra. }
      { simpl. lra. }
      destruct b.
      + iFrame. rewrite /expander -!app_assoc/=.
        rewrite Nat.OddT_odd; last (constructor 1 with (x:=0); lia). iFrame.
        iPureIntro. naive_solver.
      + iFrame. rewrite /expander -!app_assoc/=.
        rewrite Nat.odd_0. iFrame.
        iPureIntro. constructor; [lia|constructor]. 
  Qed.
    
Lemma incr_counter_spec2 N E c γ1 (Q:nat->nat->iProp Σ)  :
    ↑N⊆E ->
    {{{ is_counter2 N c γ1 ∗
        state_update E ∅
          (∃ ε (ε2 : fin 4%nat -> R),
              ↯ ε ∗ ⌜(∀ x, 0<=ε2 x)%R⌝∗
              ⌜(SeriesC (λ n, 1 / 4 * ε2 n)%R <= ε)%R ⌝ ∗
              (∀ n, ↯ (ε2 n) -∗ state_update ∅ E
          (∀ (z:nat), own γ1 (●F z) ={E∖↑N}=∗
                    own γ1 (●F (z+n)%nat) ∗ Q z n)))
    }}}
      incr_counter2 c @ E
      {{{ (z n:nat), RET (#z, #n); Q z n }}}.
  Proof.
    iIntros (Hsubset Φ) "(#Hinv & Hvs) HΦ".
    rewrite /incr_counter2.
    wp_pures.
    wp_apply flip_allocate_tape_spec as (α) "Htape"; first done.
    wp_pures.
    iAssert (state_update E E (∃ n, (flip_tapes (L:=L) α (expander ([fin_to_nat n])) ∗ ⌜Forall (λ x, x<4) ([fin_to_nat n])⌝) ∗
                                    (∀ z : nat, own γ1 (●F z) ={E ∖ ↑N}=∗ own γ1 (●F (z + n)) ∗ Q z n)
            ))%I with "[Hvs Htape]" as ">(%n & (Htape&%) &Hvs)".
    { iMod "Hvs" as "(%&%&?&%&%&Hvs)".
      iMod (counter_tapes_presample2 with "[$][Htape][$]") as "(%&?&(?&%))"; [try done..|].
      - simpl. iFrame. iPureIntro. by rewrite Forall_nil.
      - iMod ("Hvs" with "[$]").
        iModIntro.
        by iFrame.
    }
    wp_apply (flip_tape_spec_some with "[$]") as "Hα".
    wp_apply (conversion.wp_bool_to_int) as "_"; first done.
    wp_pures.
    wp_apply (flip_tape_spec_some with "[$]") as "Hα".
    wp_apply (conversion.wp_bool_to_int) as "_"; first done.
    wp_pures.
    wp_bind (FAA _ _).
    iInv "Hinv" as ">(%&%&->&?&?)" "Hclose".
    wp_faa. simpl.
    (* iMod (fupd_mask_subseteq (E ∖ ↑N)) as "Hclose'". *)
    (* { apply difference_mono; [done|by apply nclose_subseteq']. } *)
    iMod ("Hvs" with "[$]") as "[H6 HQ]".
    replace 2%Z with (Z.of_nat 2%nat) by done.
    replace (_*_+_)%Z with (Z.of_nat n); last first.
    { assert (n<4).
      - by eapply (@Forall_inv _ (λ x, x<4)).
      - by apply expander_eta.
    }
    replace (#(z+n)) with (#(z+n)%nat); last first.
    { by rewrite Nat2Z.inj_add. }
    (* iMod "Hclose'" as "_". *)
    iMod ("Hclose" with "[-HΦ HQ Hα]") as "_"; first by iFrame.
    iModIntro.
    wp_pures.
    iApply "HΦ".
    iFrame.
    by iPureIntro.
  Qed.

  
  Lemma read_counter_spec2 N E c γ1 Q:
    ↑N ⊆ E ->
    {{{  is_counter2 N c γ1 ∗
         (∀ (z:nat), own γ1 (●F z) ={E∖↑N}=∗
                    own γ1 (●F z) ∗ Q z)
        
    }}}
      read_counter2 c @ E
      {{{ (n':nat), RET #n'; Q n'
      }}}.
  Proof.
    iIntros (Hsubset Φ) "(#Hinv & Hvs) HΦ".
    rewrite /read_counter2.
    wp_pure.
    iInv "Hinv" as ">(%l&%z  & -> & Hloc & Hcont)" "Hclose".
    wp_load.
    (* iMod (fupd_mask_subseteq (E ∖ ↑N)) as "Hclose'". *)
    (* { apply difference_mono_l. by apply nclose_subseteq'. } *)
    iMod ("Hvs" with "[$]") as "[Hcont HQ]".
    (* iMod "Hclose'". *)
    iMod ("Hclose" with "[ $Hloc $Hcont]"); first done.
    iApply "HΦ". by iFrame.
  Qed.
  
End impl2.

Program Definition counterG2_to_flipG `{conerisGS Σ, !flip_spec, !counterG2 Σ} : flipG Σ.
Proof.
  eapply counterG2_flipG.
Qed.
  
Program Definition random_counter2 `{flip_spec Σ}: random_counter :=
  {| new_counter := new_counter2;
    incr_counter := incr_counter2;
    read_counter:=read_counter2;
    counterG := counterG2;
    (* tape_name := flip_tape_name; *)
    counter_name :=gname;
    is_counter _ N c γ1 := is_counter2 N c γ1;
    (* counter_tapes_auth K γ m := (flip_tapes_auth (L:=counterG2_to_flipG) γ ((λ ns, expander ns)<$>m) ∗ ⌜map_Forall (λ _ ns, Forall (λ x, x<4) ns) m⌝)%I; *)
    (* counter_tapes K α n := (flip_tapes (L:=counterG2_to_flipG) α (expander (match n with |Some x => [x] |None => [] end)) ∗ ⌜Forall (λ x, x<4) (match n with |Some x => [x] |None => [] end)⌝)%I; *)
    counter_content_auth _ γ z := own γ (●F z);
    counter_content_frag _ γ f z := own γ (◯F{f} z);
    (* counter_tapes_presample _ := counter_tapes_presample2; *)
    new_counter_spec _ := new_counter_spec2 (L:=counterG2_to_flipG);
    incr_counter_spec _ :=incr_counter_spec2 (L:=counterG2_to_flipG);
    read_counter_spec _ :=read_counter_spec2 (L:=counterG2_to_flipG)
  |}.
(* Next Obligation. *)
(*   simpl. *)
(*   iIntros (???????) "[H1 ?] [H2 ?]". *)
(*   iApply (flip_tapes_auth_exclusive with "[$][$]"). *)
(* Qed. *)
(* Next Obligation. *)
(*   simpl. *)
(*   iIntros (???????) "[??] [??]". *)
(*   iApply (flip_tapes_exclusive with "[$][$]"). *)
(* Qed. *)
(* Next Obligation. *)
(*   simpl. *)
(*   iIntros (????????) "[Hauth %H0] [Hfrag %]". *)
(*   iDestruct (flip_tapes_agree γ α ((λ ns0 : list nat, expander ns0) <$> m) (expander ns) with "[$][$]") as "%K". *)
(*   iPureIntro. *)
(*   rewrite lookup_fmap_Some in K. destruct K as (?&K1&?). *)
(*   replace ns with x; first done. *)
(*   apply expander_inj; try done. *)
(*   by eapply map_Forall_lookup_1 in H0. *)
(* Qed. *)
(* Next Obligation. *)
(*   simpl. *)
(*   iIntros (??????) "[? %]". *)
(*   iPureIntro. *)
(*   eapply Forall_impl; first done. *)
(*   simpl. lia. *)
(* Qed. *)
(* Next Obligation. *)
(*   simpl. *)
(*   iIntros (??????????) "[H1 %] [H2 %]". *)
(*   iMod (flip_tapes_update with "[$][$]") as "[??]". *)
(*   iFrame. *)
(*   iModIntro. *)
(*   rewrite fmap_insert. iFrame. *)
(*   iPureIntro. split. *)
(*   - apply map_Forall_insert_2; last done. *)
(*     eapply Forall_impl; first done. simpl; lia. *)
(*   - eapply Forall_impl; first done. *)
(*     simpl; lia. *)
(* Qed. *)
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
       
