(** * Hocap atomic rand specs
    The sampling operation is atomic. This allows tapes to be placed within invariants
 *)
From clutch.coneris Require Import coneris atomic.

Set Default Proof Using "Type*".

Class rand_atomic_spec (tb:nat) `{!conerisGS Σ} := RandAtomicSpec
{
  (** * Operations *)
  rand_allocate_tape : val;
  rand_tape : val;
  (** * Ghost state *)

  
  (** * Predicates *)
  rand_tapes (α:val) (ns: (list nat)): iProp Σ;
  (** * General properties of the predicates *)
  (* #[global] rand_tapes_auth_timeless {L : randG Σ} γ m :: *)
  (*   Timeless (rand_tapes_auth (L:=L) γ m); *)
  #[global] rand_tapes_timeless α ns::
    Timeless (rand_tapes α ns);  
  (* #[global] rand_tape_name_inhabited :: *)
  (*   Inhabited rand_tape_name; *)

  (* rand_tapes_auth_exclusive {L : randG Σ} γ m m': *)
  (* rand_tapes_auth (L:=L) γ m -∗ rand_tapes_auth (L:=L) γ m' -∗ False; *)
  rand_tapes_exclusive α ns ns':
  rand_tapes α ns-∗ rand_tapes α ns'-∗ False;
  (* rand_tapes_agree {L : randG Σ} γ α m ns: *)
  (* rand_tapes_auth (L:=L) γ m -∗ rand_tapes (L:=L) γ α ns -∗ ⌜ m!! α = Some (ns) ⌝; *)
  rand_tapes_valid α ns:
    rand_tapes α ns -∗ ⌜Forall (λ n, n<=tb)%nat ns⌝ ; 
  (* rand_tapes_update {L : randG Σ} γ α m ns ns': *)
  (* Forall (λ x, x<=ns'.1) ns'.2 -> *)
  (*   rand_tapes_auth (L:=L) γ m -∗ rand_tapes (L:=L) γ α ns ==∗ *)
  (*   rand_tapes_auth (L:=L) γ (<[α := ns']> m) ∗ rand_tapes (L:=L) γ α ns'; *)
  rand_tapes_presample E α ns ε (ε2 : fin (S tb) -> R):
  (∀ x, 0<=ε2 x)%R ->
  (SeriesC (λ n, 1 / (S tb) * ε2 n)%R <= ε)%R ->
  rand_tapes α ns-∗
  ↯ ε  -∗
  state_update E E (∃ n, ↯ (ε2 n) ∗ rand_tapes α (ns ++ [fin_to_nat n])); 
    

  (** * Program specs *)
  
  rand_allocate_tape_spec E :
    {{{ True }}}
      rand_allocate_tape #() @ E
      {{{ (v:val), RET v;
           rand_tapes v []
      }}}; 
  
  rand_tape_spec_some E (α:val):
    ⊢(<<{∀∀ n ns, rand_tapes α (n::ns) }>>
      rand_tape α @ E
             <<{  rand_tapes α ns |RET #n }>>)%I
}.


Section checks.
  Context `{H: conerisGS Σ, r1:!rand_atomic_spec tb}.
  Lemma wp_atomic_rand_tape_1 n ns α :
     rand_tapes α (n :: ns) -∗
      WP (rand_tape α)%E 
             {{ λ n', ⌜#n=n'⌝∗  rand_tapes α (ns) ∗ ⌜ (n<=tb)%nat⌝ }}.
  Proof.
    iIntros "Hfrag".
    iDestruct (rand_tapes_valid with "[$]") as "%H'".
    awp_apply (rand_tape_spec_some ∅ with "[-]").
    iAaccIntro with "Hfrag".
    - iIntros "?". by iFrame.
    -  iIntros. iFrame. iModIntro. iSplit; first done.
       iPureIntro.
       rewrite Forall_cons in H'. naive_solver.
  Qed.

End checks.


Section impl.
  Local Opaque INR.
  Variable tb:nat.
  Context `{!conerisGS Σ}.

  Definition rand_tapes1 α ns := (∃ α', ⌜α = #lbl:α'⌝ ∗ (α' ↪N (tb; ns) ))%I.

  #[local] Program Definition rand_atomic_spec1 : rand_atomic_spec tb :=
    {| rand_allocate_tape:= (λ: "_", alloc #tb);
      rand_tape:= (λ: "α", rand("α") #tb); 
      rand_tapes := rand_tapes1;
    |}.
  Next Obligation.
    simpl.
    iIntros (???) "(%&%&H1) (%&%&H2)".
    simplify_eq.
    iDestruct (tapeN_tapeN_contradict with "[$][$]") as "[]".
  Qed.
  Next Obligation.
    simpl.
    iIntros (??) "(%&?&H1)".
    iApply (tapeN_ineq with "[$]").
  Qed.
  Next Obligation.
    simpl.
    iIntros (???????) "(%&%&?)?".
    by iMod (state_update_presample_exp with "[$][$]") as "(%&$&$)". 
  Qed.
  Next Obligation.
    simpl.
    iIntros (? Φ) "_ HΦ".
    wp_pures.
    wp_apply (wp_alloc_tape); first done.
    iIntros (α) "Hα".
    iApply "HΦ".
    by iFrame.
  Qed.
  Next Obligation.
    iIntros (?? Φ) "AU".
    wp_pures.
    iApply fupd_pgl_wp.
    iMod "AU" as "(%&%&(%&%&Ht)&[AU _])".
    simplify_eq.
    iMod ("AU" with "[$Ht//]") as "AU".
    iModIntro.
    iMod ("AU") as "(%&%&(%&%&Ht)&[_ AU])".
    simplify_eq.
    wp_apply (wp_rand_tape with "[$]") as "[Htape %]".
    by iMod ("AU" with "[$Htape//]").
  Qed.
End impl.
