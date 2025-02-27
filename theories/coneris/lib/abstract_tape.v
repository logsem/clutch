(** * Abstract tapes *)
From stdpp Require Import namespaces.
From iris Require Import excl_auth invariants list.
From coneris.coneris Require Import coneris.

Set Default Proof Using "Type*".

Class abstract_tapesGS (Σ : gFunctors) := Abstract_tapesGS {
  abstract_tapesGS_inG :: ghost_mapG Σ val (nat*list nat)
                                         }.
Definition abstract_tapesΣ := ghost_mapΣ val (nat*list nat).

Notation "α ◯↪N ( M ; ns ) @ γ":= (α ↪[ γ ] (M,ns))%I
                                    (at level 20, format "α ◯↪N ( M ; ns ) @ γ") : bi_scope.

Notation "● m @ γ" := (ghost_map_auth γ 1 m) (at level 20) : bi_scope.

Section tapes_lemmas.
  Context `{!conerisGS Σ, !abstract_tapesGS Σ}.

  Lemma abstract_tapes_alloc m:
    ⊢ |==>∃ γ, (● m @ γ) ∗ [∗ map] k↦v ∈ m, (k ◯↪N (v.1; v.2) @ γ).
  Proof.
    iMod ghost_map_alloc as (γ) "[??]".
    iFrame. iModIntro.
    iApply big_sepM_mono; last done.
    by iIntros (?[??]).
  Qed.

  Lemma abstract_tapes_agree m γ k N ns:
    (● m @ γ) -∗ (k ◯↪N (N; ns) @ γ) -∗ ⌜ m!!k = Some (N, ns) ⌝.
  Proof.
    iIntros "H1 H2".
    by iCombine "H1 H2" gives "%".
  Qed.

  Lemma abstract_tapes_new γ m k N ns :
    m!!k=None -> ⊢ (● m @ γ) ==∗ (● (<[k:=(N,ns)]>m) @ γ) ∗ (k ◯↪N (N; ns) @ γ).
  Proof.
    iIntros (Hlookup) "H".
    by iApply ghost_map_insert.
  Qed.

  Lemma abstract_tapes_presample γ m k N ns n:
    (● m @ γ) -∗ (k ◯↪N (N; ns) @ γ) ==∗ (● (<[k:=(N,ns++[n])]>m) @ γ) ∗ (k ◯↪N (N; ns++[n]) @ γ).
  Proof.
    iIntros "H1 H2".
    iApply (ghost_map_update with "[$][$]"). 
  Qed.

  Lemma abstract_tapes_pop γ m k N ns n:
    (● m @ γ) -∗ (k ◯↪N (N; n::ns) @ γ) ==∗ (● (<[k:=(N,ns)]>m) @ γ) ∗ (k ◯↪N (N; ns) @ γ).
  Proof.
    iIntros "H1 H2".
    iApply (ghost_map_update with "[$][$]"). 
  Qed.

  Lemma abstract_tapes_notin α N ns m (f:(nat*list nat)-> nat) g:
    α ↪N (N; ns) -∗ ([∗ map] α0↦t ∈ m, α0 ↪N (f t; g t)) -∗ ⌜m!!α=None ⌝.
  Proof.
    destruct (m!!α) eqn:Heqn; last by iIntros.
    iIntros "Hα Hmap".
    iDestruct (big_sepM_lookup with "[$]") as "?"; first done.
    iExFalso.
    iApply (tapeN_tapeN_contradict with "[$][$]").
  Qed. 

  Lemma abstract_tapes_auth_exclusive m m' γ:
    (● m @ γ) -∗ (● m' @ γ)-∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_auth_valid_2 with "[$][$]") as "%".
    cbv in H.
    destruct H. done.
  Qed.
  
  Lemma abstract_tapes_frag_exclusive k N N' ns ns' γ:
    (k ◯↪N (N; ns) @ γ) -∗ (k ◯↪N (N'; ns') @ γ)-∗ False.
  Proof.
    iIntros "H1 H2".
    iCombine "H1 H2" gives "%".
    cbv in H.
    destruct H. done.
  Qed.
  (** * TODO add*)
End tapes_lemmas.
