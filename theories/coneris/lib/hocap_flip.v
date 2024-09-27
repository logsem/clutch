From clutch.coneris Require Import coneris.
From clutch.coneris Require Import flip hocap hocap_rand.

Set Default Proof Using "Type*".

Class flip_spec `{!conerisGS Σ} := FlipSpec
{
  (** * Operations *)
  flip_allocate_tape : val;
  flip_tape : val;
  (** * Ghost state *)
  (** The assumptions about [Σ] *)
  flipG : gFunctors → Type;
  (** [name] is used to associate [locked] with [is_lock] *)
  flip_tape_name: Type;
  (** * Predicates *)
  is_flip {L : flipG Σ} (N:namespace) (γ2: flip_tape_name): iProp Σ;
  flip_tapes_auth {L : flipG Σ} (γ: flip_tape_name) (m:gmap loc (list bool)): iProp Σ;
  flip_tapes_frag {L : flipG Σ} (γ: flip_tape_name) (α:loc) (ns:list bool): iProp Σ;
  (** * General properties of the predicates *)
  #[global] is_flip_persistent {L : flipG Σ} N γ1 ::
    Persistent (is_flip (L:=L) N γ1);
  #[global] flip_tapes_auth_timeless {L : flipG Σ} γ m ::
    Timeless (flip_tapes_auth (L:=L) γ m);
  #[global] flip_tapes_frag_timeless {L : flipG Σ} γ α ns ::
    Timeless (flip_tapes_frag (L:=L) γ α ns);
  #[global] flip_tape_name_inhabited::
    Inhabited flip_tape_name;

  flip_tapes_auth_exclusive {L : flipG Σ} γ m m':
  flip_tapes_auth (L:=L) γ m -∗ flip_tapes_auth (L:=L) γ m' -∗ False;
  flip_tapes_frag_exclusive {L : flipG Σ} γ α ns ns':
  flip_tapes_frag (L:=L) γ α ns -∗ flip_tapes_frag (L:=L) γ α ns' -∗ False;
  flip_tapes_agree {L : flipG Σ} γ α m ns:
    flip_tapes_auth (L:=L) γ m -∗ flip_tapes_frag (L:=L) γ α ns -∗ ⌜ m!! α = Some (ns) ⌝;
  flip_tapes_update {L : flipG Σ} γ α m ns ns':
    flip_tapes_auth (L:=L) γ m -∗ flip_tapes_frag (L:=L) γ α ns ==∗
    flip_tapes_auth (L:=L) γ (<[α := ns']> m) ∗ flip_tapes_frag (L:=L) γ α ns';

  (** * Program specs *)
  flip_inv_create_spec {L : flipG Σ} N E:
  ⊢ wp_update E (∃ γ1, is_flip (L:=L) N γ1);
  
  flip_allocate_tape_spec {L: flipG Σ} N E γ1:
    ↑N ⊆ E->
    {{{ is_flip (L:=L) N γ1 }}}
      flip_allocate_tape #() @ E
      {{{ (v:val), RET v;
          ∃ (α:loc), ⌜v=#lbl:α⌝ ∗ flip_tapes_frag (L:=L) γ1 α []
      }}};
  
  flip_tape_spec_some {L: flipG Σ} N E γ1 (Q:bool -> list bool -> iProp Σ) (α:loc) n ns:
    ↑N⊆E ->
    {{{ is_flip (L:=L) N γ1 ∗ flip_tapes_frag (L:=L) γ1 α (n::ns)
    }}}
      flip_tape #lbl:α @ E
                       {{{ RET #n; flip_tapes_frag (L:=L) γ1 α ns }}};
  
  flip_presample_spec {L: flipG Σ} NS E γ1 α ns T:
    ↑NS ⊆ E ->
    is_flip (L:=L) NS γ1 -∗
    flip_tapes_frag (L:=L) γ1 α ns -∗
    (|={E∖↑NS, ∅}=>
        ∃ ε num ε2, ↯ ε ∗ 
                    ⌜(∀ l, length l = num ->  0<=ε2 l)%R⌝ ∗
                    ⌜(SeriesC (λ l, if length l =? num then ε2 l else 0) /(2^num) <= ε)%R⌝∗
                      (∀ ns', ↯ (ε2 ns') 
                ={∅, E∖↑NS}=∗ T ε num ε2 ns'))
        -∗
          wp_update E (∃ ε num ε2 ns', T ε num ε2 ns' ∗
                                            flip_tapes_frag (L:=L) γ1 α (ns ++ ns'))
}.


(** Instantiate flip *)
Section instantiate_flip.
  Context `{H: conerisGS Σ, r1:@rand_spec Σ H}.
  (* Class flipG1 Σ := FlipG1 { flipG1_tapes:: hocap_tapesGS Σ}. *)
  (* Local Definition flip_inv_pred1 `{!hocap_tapesGS Σ} γ1:= *)
  (*   (∃ (m:gmap loc (list bool)) , *)
  (*       ([∗ map] α ↦ t ∈ ((λ (ns:list bool), (1%nat, bool_to_nat<$>ns))<$>m), rand_tapes_auth γ1 α ( t.1 ; t.2 )) ∗ *)
  (*       ●(((λ (ns:list bool), (1, bool_to_nat<$>ns))<$>m):gmap _ _)@γ2 *)
  (*   )%I. *)

  #[local] Program Definition flip_spec1 : flip_spec :=
    {| flip_allocate_tape:= (λ: <>, rand_allocate_tape #1%nat); 
      flip_tape:= (λ: "α", conversion.int_to_bool (rand_tape "α" #1%nat));
      flipG := randG;
      flip_tape_name := rand_tape_name;
      is_flip L N γ1 := is_rand (L:=L) N γ1;
      flip_tapes_auth L γ m := rand_tapes_auth (L:=L) γ ((λ ns, (1, bool_to_nat<$>ns))<$>m);
      flip_tapes_frag L γ α ns := rand_tapes_frag (L:=L) γ α (1, (fmap (FMap:=list_fmap) bool_to_nat ns));
    |}.
  Next Obligation.
    simpl.
    iIntros (????) "H1 H2".
    by iDestruct (rand_tapes_auth_exclusive with "[$][$]") as "?".
  Qed.
  Next Obligation.
    simpl.
    iIntros (?????) "H1 H2".
    by iDestruct (rand_tapes_frag_exclusive with "[$][$]") as "?".
  Qed.
  Next Obligation.
    simpl.
    iIntros.
    iDestruct (rand_tapes_agree with "[$][$]") as "%H'".
    rewrite lookup_fmap_Some in H'. destruct H' as (?&?&K).
    simplify_eq.
    rewrite K.
    iPureIntro.
    f_equal.
    eapply fmap_inj; last done.
    intros [][]?; by simplify_eq.
  Qed.
  Next Obligation.
    iIntros.
    iMod (rand_tapes_update with "[$][$]") as "[??]"; last iFrame.
    - simpl.
      rewrite Forall_fmap.
      apply Forall_true.
      simpl.
      intros []; simpl; lia.
    - iModIntro. 
      rewrite fmap_insert; iFrame.
  Qed.
  Next Obligation.
    simpl.
    iIntros (???).
    iApply rand_inv_create_spec.
  Qed.
  Next Obligation.
    simpl.
    iIntros. 
    wp_pures.
    wp_apply rand_allocate_tape_spec; [exact|done..].
  Qed.
  Next Obligation.
    simpl.
    iIntros (???? Q ???? Φ) "(#Hinv & Hfrag) HΦ".
    wp_pures.
    wp_apply (rand_tape_spec_some  with "[-HΦ]"); [done|..].
    - by iFrame. 
    - iIntros "Hfrag". 
      wp_apply conversion.wp_int_to_bool as "_"; first done.
      replace (Z_to_bool _) with n; first by iApply "HΦ".
      destruct n; simpl.
      + rewrite Z_to_bool_neq_0; lia.
      + rewrite Z_to_bool_eq_0; lia.
  Qed.
  Next Obligation.
    simpl.
    iIntros (?????? T ?) "#Hinv Hfrag Hvs".
    iMod (rand_presample_spec _ _ _ _ _ _
            (λ ε num ε2 ns',
               ∃ bs' ε2',  ⌜fmap (FMap:= list_fmap) bool_to_nat bs'=fin_to_nat <$> ns'⌝ ∗
                             ⌜∀ xs ys, fmap (FMap:= list_fmap) bool_to_nat xs = fmap (FMap:= list_fmap)fin_to_nat ys -> ε2' xs = ε2 ys⌝ ∗
               T ε num ε2' bs'
            )%I
           with "[//][$][-]") as "(%&%&%&%&[(%&%&%K&%&?)?])"; [exact| |iModIntro; iFrame]; last first.
    { by rewrite fmap_app K. }
    iMod "Hvs" as "(%&%&%&Herr &%Hpos&%Hineq &Hrest)".
    iFrame.
    iExists num, (λ ls, ε2 (nat_to_bool<$>(fin_to_nat <$> ls))).
    iModIntro.
    repeat iSplit; try iPureIntro.
    - intros. apply Hpos.
      by rewrite !fmap_length.
    - etrans; last exact.
      replace 2%R with (INR 2); last (simpl; lra).
      rewrite !Rdiv_def.
      apply Rmult_le_compat_r.
      { rewrite -Rdiv_1_l -pow_INR. apply Rdiv_INR_ge_0. }
      etrans; last eapply (SeriesC_le_inj _ (λ l, Some ((λ x, nat_to_bool (fin_to_nat x)) <$> l))).
      + apply Req_le_sym.
        apply SeriesC_ext.
        intros. simpl. rewrite fmap_length.
        rewrite elem_of_enum_uniform_fin_list'. case_match; last lra.
        rewrite -list_fmap_compose.
        f_equal.
      + intros. case_match; last lra.
        apply Hpos.
        by rewrite -Nat.eqb_eq.
      + intros ??? H1 H2.
        simplify_eq.
        apply fmap_inj in H1; first done.
        intros x y ?.
        repeat (inv_fin x; simpl; try intros x);
          by repeat (inv_fin y; simpl; try intros y).
      + eapply ex_seriesC_list_length. intros.
        case_match; last done.
        by rewrite -Nat.eqb_eq.
    - iIntros (ls) "H2".
      iMod ("Hrest" with "[$H2 ]") as "?".
      iFrame.
      iModIntro.
      iSplit; iPureIntro.
      + rewrite -!list_fmap_compose.
      erewrite (Forall_fmap_ext_1 (_∘_)); first done.
      apply Forall_true.
      intros x; by repeat (inv_fin x; simpl; try intros x).
      + intros ?? <-.
        f_equal.
        rewrite -!list_fmap_compose.
        rewrite -{1}(list_fmap_id xs).
        erewrite (Forall_fmap_ext_1 (_∘_)); first done.
        apply Forall_true.
        intros []; simpl.
        ** by rewrite nat_to_bool_neq_0.
        ** by rewrite nat_to_bool_eq_0.
  Qed.
End instantiate_flip.

(* Section test. *)
(*   Context `{F:flip_spec}. *)
(*   Lemma flip_presample_spec_simple {L: flipG Σ} NS E ns α *)
(*      (ε2 : R -> bool -> R) *)
(*     (P : iProp Σ) T γ1 γ2: *)
(*     ↑NS ⊆ E -> *)
(*     (∀ ε n, 0<= ε -> 0<=ε2 ε n)%R -> *)
(*     (∀ (ε:R), 0<= ε -> (ε2 ε true + ε2 ε false)/2 <= ε)%R-> *)
(*     is_flip (L:=L) NS γ1 γ2 -∗ *)
(*     (□∀ (ε:R) n, (P ∗ flip_error_auth (L:=L) γ1 ε) ={E∖↑NS}=∗ *)
(*         (⌜(1<=ε2 ε n)%R⌝ ∨ (flip_error_auth (L:=L) γ1 (ε2 ε n)  ∗ T (n)))) *)
(*         -∗ *)
(*     P -∗ flip_tapes_frag (L:=L) γ2 α ns-∗ *)
(*         wp_update E (∃ n, T (n) ∗ flip_tapes_frag (L:=L) γ2 α (ns++[n])). *)
(*   Proof. *)
(*     iIntros (Hsubset Hpos Hineq) "#Hinv #Hvs HP Hfrag". *)
(*     pose (ε2' ε l:= match l with *)
(*                     | [b]=> ε2 ε b *)
(*                     | _ => 1%R *)
(*                     end *)
(*          ). *)
(*     iMod (flip_presample_spec _ _ _ _ ε2' P 1%nat (λ l, match l with | [b] => T b | _ => False end )%I with "[//][][$][$]") as "(%l & [??])"; first done. *)
(*     - rewrite /ε2'. *)
(*       intros. repeat case_match; try done. naive_solver. *)
(*     - intros. *)
(*       etrans; last apply Hineq; try done. *)
(*       erewrite (SeriesC_subset (λ x, x ∈ [[true]; [false]])); last first. *)
(*       + intros ? H'. *)
(*         case_match eqn:K; last done. *)
(*         rewrite Nat.eqb_eq in K. *)
(*         exfalso. *)
(*         apply H'. *)
(*         destruct a as [|[|] [|]]; try (simpl in *; done). *)
(*         all: set_solver. *)
(*       + rewrite SeriesC_list; last first. *)
(*         { rewrite !NoDup_cons; repeat split; last apply NoDup_nil; set_solver. } *)
(*         simpl. lra. *)
(*     - iModIntro. iIntros (ε n) "?". *)
(*       destruct n as [|b [|]]. *)
(*       + iLeft. iPureIntro. *)
(*         by rewrite /ε2'. *)
(*       + iMod ("Hvs" $! ε b with "[$]") as "[% | ?]". *)
(*         * iLeft. iPureIntro. by rewrite /ε2'. *)
(*         * iRight. by rewrite /ε2'. *)
(*       + iLeft. iPureIntro. *)
(*         by rewrite /ε2'. *)
(*     - repeat case_match; try done. *)
(*       iModIntro. *)
(*       iFrame. *)
(*   Qed. *)
(* End test. *)
