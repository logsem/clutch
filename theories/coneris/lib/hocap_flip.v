From clutch.coneris Require Import coneris.
From clutch.coneris Require Import flip hocap_rand.

(* An abstract spec for a flip module that allows presampling tapes *)

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
  flip_tapes {L : flipG Σ} (α:val) (ns:list bool): iProp Σ;
  (** * General properties of the predicates *)
  #[global] flip_tapes_timeless {L : flipG Σ} α ns ::
    Timeless (flip_tapes (L:=L) α ns);
  flip_tapes_exclusive {L : flipG Σ} α ns ns':
  flip_tapes (L:=L) α ns -∗ flip_tapes (L:=L) α ns' -∗ False;
  flip_tapes_presample {L:flipG Σ} E α ns ε (ε2 : bool -> R):
    (∀ x, 0<=ε2 x)%R ->
    ((ε2 true + ε2 false)/2 <= ε)%R ->
    (* is_flip (L:=L) N γ -∗ *)
    flip_tapes (L:=L) α (ns) -∗
    ↯ ε  -∗
    state_update E E (∃ n, ↯ (ε2 n) ∗ flip_tapes (L:=L) α (ns ++ [n]));

  (** * Program specs *)
  
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

}.


(** Instantiate flip *)
Section instantiate_flip.
  Context `{H: conerisGS Σ, r1:@rand_spec Σ H}.

  #[local] Program Definition flip_spec1 : flip_spec :=
    {| flip_allocate_tape:= (λ: <>, rand_allocate_tape #1%nat); 
      flip_tape:= (λ: "α", conversion.int_to_bool (rand_tape "α" #1%nat));
      flipG := randG;
      flip_tapes L α ns := rand_tapes (L:=L) α (1, (fmap (FMap:=list_fmap) bool_to_nat ns));
    |}.
  Next Obligation.
    simpl.
    iIntros (????) "H1 H2".
    by iDestruct (rand_tapes_exclusive with "[$][$]") as "?".
  Qed.
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
