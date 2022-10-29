(** Rules for updating the specification program. *)
From stdpp Require Import namespaces.
From iris.algebra Require Import auth excl frac agree gmap list.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import proofmode.
From self.prob_lang Require Export lang notation tactics primitive_laws spec_ra.

Section rules.
  Context `{!prelocGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

  (** Pure reductions *)
  Lemma step_pure E K e e' (P : Prop) n :
    P →
    PureExec P n e e' →
    nclose specN ⊆ E →
    spec_ctx ∗ ⤇ fill K e ={E}=∗ spec_ctx ∗ ⤇ fill K e'.
  Proof.
    iIntros (HP Hex ?) "[#Hspec Hj]". iFrame "Hspec".
    iInv specN as (ξ ρ e0 σ0) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    iMod (spec_prog_update (fill K e') with "Hauth Hj") as "[Hauth Hj]".
    iFrame "Hj". iApply "Hclose". iNext.
    edestruct (exec_PureExec_ctx_snoc (fill K) P) as [ξ' Hexec']; [done|done|].
    iExists (ξ ++ ξ'), _, _, _.
    iFrame. by erewrite Hexec'.
  Qed.

  (* (** Alloc, load, and store *) *)
  (* Lemma step_alloc E j K e v : *)
  (*   IntoVal e v → *)
  (*   nclose specN ⊆ E → *)
  (*   spec_ctx ∗ j ⤇ fill K (ref e) ={E}=∗ ∃ l, spec_ctx ∗ j ⤇ fill K (#l) ∗ l ↦ₛ v. *)
  (* Proof. *)
  (*   iIntros (<-?) "[#Hinv Hj]". iFrame "Hinv". *)
  (*   rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def /=. *)
  (*   iDestruct "Hinv" as (ρ) "Hinv". *)
  (*   iInv specN as (tp σ) ">[Hown %]" "Hclose". *)
  (*   destruct (exist_fresh (dom (heap σ))) as [l Hl%not_elem_of_dom]. *)
  (*   iDestruct (own_valid_2 with "Hown Hj") *)
  (*     as %[[?%tpool_singleton_included' _]%prod_included ?]%auth_both_valid_discrete. *)
  (*   iMod (own_update_2 with "Hown Hj") as "[Hown Hj]". *)
  (*   { by eapply auth_update, prod_local_update_1, *)
  (*       singleton_local_update, (exclusive_local_update _ (Excl (fill K (#l)%E))). } *)
  (*   iMod (own_update with "Hown") as "[Hown Hl]". *)
  (*   { eapply auth_update_alloc, prod_local_update_2, *)
  (*       (alloc_singleton_local_update _ l (1%Qp,to_agree (Some v : leibnizO _))); last done. *)
  (*     by apply lookup_to_heap_None. } *)
  (*   rewrite heapS_mapsto_eq /heapS_mapsto_def /=. *)
  (*   iExists l. iFrame "Hj Hl". iApply "Hclose". iNext. *)
  (*   iExists (<[j:=fill K (# l)]> tp), (state_upd_heap <[l:=Some v]> σ). *)
  (*   rewrite to_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro. *)
  (*   eapply rtc_r, step_insert_no_fork; eauto. *)
  (*   rewrite -state_init_heap_singleton. eapply AllocNS; first by lia. *)
  (*   intros. assert (i = 0) as -> by lia. by rewrite loc_add_0. *)
  (* Qed. *)

  (* Lemma step_load E j K l q v: *)
  (*   nclose specN ⊆ E → *)
  (*   spec_ctx ∗ j ⤇ fill K (!#l) ∗ l ↦ₛ{q} v *)
  (*   ={E}=∗ spec_ctx ∗ j ⤇ fill K (of_val v) ∗ l ↦ₛ{q} v. *)
  (* Proof. *)
  (*   iIntros (?) "(#Hinv & Hj & Hl)". iFrame "Hinv". *)
  (*   rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def. *)
  (*   iDestruct "Hinv" as (ρ) "Hinv". *)
  (*   rewrite heapS_mapsto_eq /heapS_mapsto_def /=. *)
  (*   iInv specN as (tp σ) ">[Hown %]" "Hclose". *)
  (*   iDestruct (own_valid_2 with "Hown Hj") *)
  (*     as %[[?%tpool_singleton_included' _]%prod_included ?]%auth_both_valid_discrete. *)
  (*   iDestruct (own_valid_2 with "Hown Hl") *)
  (*     as %[[? ?%heap_singleton_included]%prod_included ?]%auth_both_valid_discrete. *)
  (*   iMod (own_update_2 with "Hown Hj") as "[Hown Hj]". *)
  (*   { by eapply auth_update, prod_local_update_1, singleton_local_update, *)
  (*       (exclusive_local_update _ (Excl (fill K (of_val v)))). } *)
  (*   iFrame "Hj Hl". iApply "Hclose". iNext. *)
  (*   iExists (<[j:=fill K (of_val v)]> tp), σ. *)
  (*   rewrite to_tpool_insert'; last eauto. iFrame. iPureIntro. *)
  (*   eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto. *)
  (* Qed. *)

  (* Lemma step_store E j K l v' e v: *)
  (*   IntoVal e v → *)
  (*   nclose specN ⊆ E → *)
  (*   spec_ctx ∗ j ⤇ fill K (#l <- e) ∗ l ↦ₛ v' *)
  (*   ={E}=∗ spec_ctx ∗ j ⤇ fill K #() ∗ l ↦ₛ v. *)
  (* Proof. *)
  (*   iIntros (<-?) "(#Hinv & Hj & Hl)". iFrame "Hinv". *)
  (*   rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def. *)
  (*   iDestruct "Hinv" as (ρ) "Hinv". *)
  (*   rewrite heapS_mapsto_eq /heapS_mapsto_def /=. *)
  (*   iInv specN as (tp σ) ">[Hown %]" "Hclose". *)
  (*   iDestruct (own_valid_2 with "Hown Hj") *)
  (*     as %[[?%tpool_singleton_included' _]%prod_included _]%auth_both_valid_discrete. *)
  (*   iDestruct (own_valid_2 with "Hown Hl") *)
  (*     as %[[_ Hl%heap_singleton_included]%prod_included _]%auth_both_valid_discrete. *)
  (*   iMod (own_update_2 with "Hown Hj") as "[Hown Hj]". *)
  (*   { by eapply auth_update, prod_local_update_1, singleton_local_update, *)
  (*       (exclusive_local_update _ (Excl (fill K #()))). } *)
  (*   iMod (own_update_2 with "Hown Hl") as "[Hown Hl]". *)
  (*   { eapply auth_update, prod_local_update_2. *)
  (*     apply: singleton_local_update. *)
  (*     { by rewrite /to_heap lookup_fmap Hl. } *)
  (*     apply: (exclusive_local_update _ *)
  (*       (1%Qp, to_agree (Some v : leibnizO (option val)))). *)
  (*     apply: pair_exclusive_l. done. } *)
  (*   iFrame "Hj Hl". iApply "Hclose". iNext. *)
  (*   iExists (<[j:=fill K #()]> tp), (state_upd_heap <[l:=Some v]> σ). *)
  (*   rewrite to_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro. *)
  (*   eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto. *)
  (* Qed. *)


End rules.
