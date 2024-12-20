From clutch.coneris Require Import coneris.
From clutch.coneris Require Import flip hocap_rand.

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
  (** * Predicates *)
  (* is_flip {L : flipG Σ} (N:namespace) (γ2: flip_tape_name): iProp Σ; *)
  (* flip_tapes_auth {L : flipG Σ} (γ: flip_tape_name) (m:gmap loc (list bool)): iProp Σ; *)
  flip_tapes {L : flipG Σ} (α:val) (ns:list bool): iProp Σ;
  (** * General properties of the predicates *)
  (* #[global] is_flip_persistent {L : flipG Σ} N γ1 :: *)
  (*   Persistent (is_flip (L:=L) N γ1); *)
  (* #[global] flip_tapes_auth_timeless {L : flipG Σ} γ m :: *)
  (*   Timeless (flip_tapes_auth (L:=L) γ m); *)
  #[global] flip_tapes_timeless {L : flipG Σ} α ns ::
    Timeless (flip_tapes (L:=L) α ns);
  (* #[global] flip_tape_name_inhabited:: *)
  (*   Inhabited flip_tape_name; *)

  (* flip_tapes_auth_exclusive {L : flipG Σ} γ m m': *)
  (* flip_tapes_auth (L:=L) γ m -∗ flip_tapes_auth (L:=L) γ m' -∗ False; *)
  flip_tapes_exclusive {L : flipG Σ} α ns ns':
  flip_tapes (L:=L) α ns -∗ flip_tapes (L:=L) α ns' -∗ False;
  (* flip_tapes_agree {L : flipG Σ} γ α m ns: *)
  (*   flip_tapes_auth (L:=L) γ m -∗ flip_tapes (L:=L) γ α ns -∗ ⌜ m!! α = Some (ns) ⌝; *)
  (* flip_tapes_update {L : flipG Σ} γ α m ns ns': *)
  (*   flip_tapes_auth (L:=L) γ m -∗ flip_tapes (L:=L) γ α ns ==∗ *)
  (*   flip_tapes_auth (L:=L) γ (<[α := ns']> m) ∗ flip_tapes (L:=L) γ α ns'; *)
  flip_tapes_presample {L:flipG Σ} E α ns ε (ε2 : bool -> R):
    (∀ x, 0<=ε2 x)%R ->
    ((ε2 true + ε2 false)/2 <= ε)%R ->
    (* is_flip (L:=L) N γ -∗ *)
    flip_tapes (L:=L) α (ns) -∗
    ↯ ε  -∗
    state_update E E (∃ n, ↯ (ε2 n) ∗ flip_tapes (L:=L) α (ns ++ [n]));

  (** * Program specs *)
  (* flip_inv_create_spec {L : flipG Σ} N E: *)
  (* ⊢ wp_update E (∃ γ1, is_flip (L:=L) N γ1); *)
  
  flip_allocate_tape_spec {L: flipG Σ} E:
    {{{ True }}}
      flip_allocate_tape #() @ E
      {{{ (v:val), RET v; flip_tapes (L:=L) v []
      }}};
  
  flip_tape_spec_some {L: flipG Σ} E α n ns:
    {{{ flip_tapes (L:=L) α (n::ns)
    }}}
      flip_tape α @ E
                       {{{ RET #n; flip_tapes (L:=L) α ns }}};
  
  (* flip_presample_spec {L: flipG Σ} NS E γ1 α ns T: *)
  (*   ↑NS ⊆ E -> *)
  (*   is_flip (L:=L) NS γ1 -∗ *)
  (*   flip_tapes (L:=L) γ1 α ns -∗ *)
  (*   (|={E∖↑NS, ∅}=> *)
  (*       ∃ ε num ε2, ↯ ε ∗  *)
  (*                   ⌜(∀ l, length l = num ->  0<=ε2 l)%R⌝ ∗ *)
  (*                   ⌜(SeriesC (λ l, if length l =? num then ε2 l else 0) /(2^num) <= ε)%R⌝∗ *)
  (*                     (∀ ns', ↯ (ε2 ns')  *)
  (*               ={∅, E∖↑NS}=∗ T ε num ε2 ns')) *)
  (*       -∗ *)
  (*         wp_update E (∃ ε num ε2 ns', flip_tapes (L:=L) γ1 α (ns ++ ns') ∗ T ε num ε2 ns') *)
}.


(** Instantiate flip *)
Section instantiate_flip.
  Context `{H: conerisGS Σ, r1:@rand_spec Σ H}.

  #[local] Program Definition flip_spec1 : flip_spec :=
    {| flip_allocate_tape:= (λ: <>, rand_allocate_tape #1%nat); 
      flip_tape:= (λ: "α", conversion.int_to_bool (rand_tape "α" #1%nat));
      flipG := randG;
      (* flip_tape_name := rand_tape_name; *)
      (* is_flip L N γ1 := is_rand (L:=L) N γ1; *)
      (* flip_tapes_auth L γ m := rand_tapes_auth (L:=L) γ ((λ ns, (1, bool_to_nat<$>ns))<$>m); *)
      flip_tapes L α ns := rand_tapes (L:=L) α (1, (fmap (FMap:=list_fmap) bool_to_nat ns));
    |}.
  (* Next Obligation. *)
  (*   simpl. *)
  (*   iIntros (????) "H1 H2". *)
  (*   by iDestruct (rand_tapes_auth_exclusive with "[$][$]") as "?". *)
  (* Qed. *)
  Next Obligation.
    simpl.
    iIntros (????) "H1 H2".
    by iDestruct (rand_tapes_exclusive with "[$][$]") as "?".
  Qed.
  (* Next Obligation. *)
  (*   simpl. *)
  (*   iIntros. *)
  (*   iDestruct (rand_tapes_agree with "[$][$]") as "%H'". *)
  (*   rewrite lookup_fmap_Some in H'. destruct H' as (?&?&K). *)
  (*   simplify_eq. *)
  (*   rewrite K. *)
  (*   iPureIntro. *)
  (*   f_equal. *)
  (*   eapply fmap_inj; last done. *)
  (*   intros [][]?; by simplify_eq. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   iIntros. *)
  (*   iMod (rand_tapes_update with "[$][$]") as "[??]"; last iFrame. *)
  (*   - simpl. *)
  (*     rewrite Forall_fmap. *)
  (*     apply Forall_true. *)
  (*     simpl. *)
  (*     intros []; simpl; lia. *)
  (*   - iModIntro.  *)
  (*     rewrite fmap_insert; iFrame. *)
  (* Qed. *)
  Next Obligation.
    simpl.
    iIntros (????????) "Hfrag Hε".
    iMod (rand_tapes_presample _ _ _ _ _ (λ x, ε2 (nat_to_bool (fin_to_nat x)))with "[$][$]") as "(%n&?&?)"; try done.
    - rewrite SeriesC_finite_foldr/=.
      rewrite nat_to_bool_eq_0 nat_to_bool_neq_0; last lia.
      lra.
    - iFrame.
      iModIntro.
      rewrite fmap_app.
      by repeat (inv_fin n; try (intros n)); simpl.
  Qed.
  (* Next Obligation. *)
  (*   simpl. *)
  (*   iIntros (???). *)
  (*   iApply rand_inv_create_spec. *)
  (* Qed. *)
  Next Obligation.
    simpl.
    iIntros. 
    wp_pures.
    wp_apply rand_allocate_tape_spec; [exact|done..].
  Qed.
  Next Obligation.
    simpl.
    iIntros (??? ?? Φ) "Hfrag HΦ".
    wp_pures.
    wp_apply (rand_tape_spec_some  with "[-HΦ]"); first done.
    iIntros "Hfrag". 
    wp_apply conversion.wp_int_to_bool as "_"; first done.
    replace (Z_to_bool _) with n; first by iApply "HΦ".
    destruct n; simpl.
    - rewrite Z_to_bool_neq_0; lia.
    - rewrite Z_to_bool_eq_0; lia.
  Qed.
  (* Next Obligation. *)
  (*   simpl. *)
  (*   iIntros (?????? T ?) "#Hinv Hfrag Hvs". *)
  (*   iMod (rand_presample_spec _ _ _ _ _ _ *)
  (*           (λ ε num ε2 ns', *)
  (*              ∃ bs' ε2',  ⌜fmap (FMap:= list_fmap) bool_to_nat bs'=fin_to_nat <$> ns'⌝ ∗ *)
  (*                            ⌜∀ xs ys, fmap (FMap:= list_fmap) bool_to_nat xs = fmap (FMap:= list_fmap)fin_to_nat ys -> ε2' xs = ε2 ys⌝ ∗ *)
  (*              T ε num ε2' bs' *)
  (*           )%I *)
  (*          with "[//][$][-]") as "(%&%&%&%&?&%&%&%K&%&?)"; [exact| |iModIntro; iFrame]; last first. *)
  (*   { by rewrite fmap_app K. } *)
  (*   iMod "Hvs" as "(%&%&%&Herr &%Hpos&%Hineq &Hrest)". *)
  (*   iFrame. *)
  (*   iExists num, (λ ls, ε2 (nat_to_bool<$>(fin_to_nat <$> ls))). *)
  (*   iModIntro. *)
  (*   repeat iSplit; try iPureIntro. *)
  (*   - intros. apply Hpos. *)
  (*     by rewrite !fmap_length. *)
  (*   - etrans; last exact. *)
  (*     replace 2%R with (INR 2); last (simpl; lra). *)
  (*     rewrite !Rdiv_def. *)
  (*     apply Rmult_le_compat_r. *)
  (*     { rewrite -Rdiv_1_l -pow_INR. apply Rdiv_INR_ge_0. } *)
  (*     etrans; last eapply (SeriesC_le_inj _ (λ l, Some ((λ x, nat_to_bool (fin_to_nat x)) <$> l))). *)
  (*     + apply Req_le_sym. *)
  (*       apply SeriesC_ext. *)
  (*       intros. simpl. rewrite fmap_length. *)
  (*       rewrite elem_of_enum_uniform_fin_list'. case_match; last lra. *)
  (*       rewrite -list_fmap_compose. *)
  (*       f_equal. *)
  (*     + intros. case_match; last lra. *)
  (*       apply Hpos. *)
  (*       by rewrite -Nat.eqb_eq. *)
  (*     + intros ??? H1 H2. *)
  (*       simplify_eq. *)
  (*       apply fmap_inj in H1; first done. *)
  (*       intros x y ?. *)
  (*       repeat (inv_fin x; simpl; try intros x); *)
  (*         by repeat (inv_fin y; simpl; try intros y). *)
  (*     + eapply ex_seriesC_list_length. intros. *)
  (*       case_match; last done. *)
  (*       by rewrite -Nat.eqb_eq. *)
  (*   - iIntros (ls) "H2". *)
  (*     iMod ("Hrest" with "[$H2 ]") as "?". *)
  (*     iFrame. *)
  (*     iModIntro. *)
  (*     iSplit; iPureIntro. *)
  (*     + rewrite -!list_fmap_compose. *)
  (*     erewrite (Forall_fmap_ext_1 (_∘_)); first done. *)
  (*     apply Forall_true. *)
  (*     intros x; by repeat (inv_fin x; simpl; try intros x). *)
  (*     + intros ?? <-. *)
  (*       f_equal. *)
  (*       rewrite -!list_fmap_compose. *)
  (*       rewrite -{1}(list_fmap_id xs). *)
  (*       erewrite (Forall_fmap_ext_1 (_∘_)); first done. *)
  (*       apply Forall_true. *)
  (*       intros []; simpl. *)
  (*       ** by rewrite nat_to_bool_neq_0. *)
  (*       ** by rewrite nat_to_bool_eq_0. *)
  (* Qed. *)
End instantiate_flip.

Section test.
  Context `{F:flip_spec}.
  Lemma flip_presample_spec_simple {L: flipG Σ} E α ns ε ε2:
    (∀ n, 0<=ε2 n)%R ->
    ((ε2 true + ε2 false)/2<=ε)%R ->
    (* is_flip (L:=L) NS γ1 -∗ *)
    flip_tapes (L:=L) α ns -∗
    ↯ ε -∗
          wp_update E (∃ b, flip_tapes (L:=L) α (ns ++ [b]) ∗ ↯ (ε2 b)).
  Proof.
    iIntros (Hpos Hineq) "Hfrag Herr".
    iApply wp_update_state_update.
    iMod (flip_tapes_presample with "[$][$]") as "(%&?&?)"; try done.
    by iFrame.
  Qed.
End test.
