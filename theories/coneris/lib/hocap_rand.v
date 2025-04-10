(** * Hocap rand specs *)
From clutch.coneris Require Import coneris.

(** An abstract spec for a rand module that allows presampling tapes *)

Set Default Proof Using "Type*".

Class rand_spec `{!conerisGS Σ} := RandSpec
{
  (** * Operations *)
  rand_allocate_tape : val;
  rand_tape : val;
  (** * Ghost state *)
  (** The assumptions about [Σ] *)
  randG : gFunctors → Type;
  
  (** * Predicates *)
  rand_tapes {L : randG Σ} (* (γ: rand_tape_name) *) (α:val) (ns: (nat * list nat)): iProp Σ;
  (** * General properties of the predicates *)
  #[global] rand_tapes_timeless {L : randG Σ} α ns ::
    Timeless (rand_tapes (L:=L) α ns);
  rand_tapes_exclusive {L : randG Σ} α ns ns':
  rand_tapes (L:=L) α ns -∗ rand_tapes (L:=L) α ns' -∗ False;
  rand_tapes_valid {L : randG Σ} α tb ns:
  rand_tapes (L:=L) α (tb, ns) -∗ ⌜Forall (λ n, n<=tb)%nat ns⌝ ;
  rand_tapes_presample {L:randG Σ} E α tb ns ε (ε2 : fin (S tb) -> R):
  (∀ x, 0<=ε2 x)%R ->
  (SeriesC (λ n, 1 / (S tb) * ε2 n)%R <= ε)%R ->
  (* is_rand(L:=L) N γ -∗ *)
  rand_tapes (L:=L) α (tb, ns) -∗
  ↯ ε  -∗
  state_update E E (∃ n, ↯ (ε2 n) ∗ rand_tapes (L:=L) α (tb, ns ++ [fin_to_nat n]));
    

  (** * Program specs *)
  rand_allocate_tape_spec {L: randG Σ} E (tb:nat) :
    {{{ True }}}
      rand_allocate_tape #tb @ E
      {{{ (v:val), RET v;
           rand_tapes (L:=L) v (tb, [])
      }}}; 
  rand_tape_spec_some {L: randG Σ} E α (tb:nat) n ns:
    {{{ rand_tapes (L:=L) α (tb, n::ns) }}}
      rand_tape α #tb @ E
                       {{{ RET #n; rand_tapes (L:=L) α (tb, ns) }}}; 
}.

Section impl.
  Local Opaque INR.
  (* (** Instantiate rand *) *)
  Class randG1 (Σ: gFunctors) := RandG1 { 
                             (* flipG1_tapes:: hocap_tapesGS Σ; *)
                      }.
  (* Local Definition rand_inv_pred1 `{!conerisGS Σ} (γ2:gname) : iProp Σ:= *)
  (*   (True)%I. *)

  #[local] Program Definition rand_spec1 `{!conerisGS Σ}: rand_spec :=
    {| rand_allocate_tape:= (λ: "N", alloc "N");
      rand_tape:= (λ: "α" "N", rand("α") "N"); 
      randG := randG1;
      rand_tapes _ α ns := (∃ α', ⌜α = #lbl:α'⌝ ∗ (α' ↪N (ns.1; ns.2) ))%I;
    |}.
  Next Obligation.
    simpl.
    iIntros (??????) "(%&%&H1) (%&%&H2)".
    simplify_eq.
    iDestruct (tapeN_tapeN_contradict with "[$][$]") as "[]".
  Qed.
  Next Obligation.
    simpl.
    iIntros (??????) "(%&?&H1)".
    iApply (tapeN_ineq with "[$]").
  Qed.
  Next Obligation.
    simpl.
    iIntros (???????????) "(%&%&?)?".
    by iMod (state_update_presample_exp with "[$][$]") as "(%&$&$)". 
  Qed.
  Next Obligation.
    simpl.
    iIntros (????? Φ) "_ HΦ".
    wp_pures.
    wp_apply (wp_alloc_tape); first done.
    iIntros (α) "Hα".
    iApply "HΦ".
    by iFrame.
  Qed.
  Next Obligation.
    simpl.
    iIntros (???????? Φ) "(%&%&?) HΦ".
    wp_pures.
    simpl. subst.
    wp_apply (wp_rand_tape with "[$]") as "[Htape %]".
    iApply "HΦ". by iFrame.
    (* iPureIntro. by eapply Forall_inv_tail. *)
  Qed.
End impl.

Section checks.
  Context `{H: conerisGS Σ, r1:@rand_spec Σ H, L:randG Σ}.
  
  Lemma wp_rand_tape_1 (N:nat) E n ns α:
    {{{ ▷ rand_tapes (L:=L) α (N, n :: ns) }}}
      rand_tape α #N@ E
                       {{{ RET #(LitInt n); rand_tapes (L:=L) α (N, ns) ∗ ⌜n <= N⌝ }}}.
  Proof.
    iIntros (Φ) ">Hfrag HΦ".
    iDestruct (rand_tapes_valid with "[$]") as "%H'". 
    wp_apply (rand_tape_spec_some with "[Hfrag]"); first exact.
    iIntros.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    rewrite Forall_cons in H'. naive_solver.
  Qed.

  Local Opaque enum_uniform_fin_list.

              
  Lemma wp_presample_adv_comp_rand_tape (N : nat) E α ns (ε1 : R) (ε2 : fin (S N) -> R) :
    (∀ n, 0<=ε2 n)%R ->
    (SeriesC (λ n, (1 / (S N)) * ε2 n)%R <= ε1)%R →
    ▷ rand_tapes (L:=L) α (N, ns) -∗
    ↯ ε1 -∗
    wp_update E (∃ n, ↯ (ε2 n) ∗ rand_tapes (L:=L) α (N, ns ++[fin_to_nat n]))%I.
  Proof.
    iIntros (Hpos Hineq) ">Htape Herr".
    iDestruct (ec_valid with "[$]") as "%Hpos'".
    destruct Hpos' as [Hpos' ?].
    iApply wp_update_state_update.
    by iApply (rand_tapes_presample with "[$][$]").
  Qed.
      

End checks.
