(** This file proves the basic laws of the ProbLang weakest precondition by
    applying the lifting lemmas. *)
From iris.proofmode       Require Import base tactics classes proofmode.
From iris.base_logic.lib Require Export ghost_map.
From clutch.approxis Require Import  app_weakestpre.
From clutch.base_logic Require Export error_credits.
From clutch.common Require Import locations.
From clutch.prob_eff_lang.hazel_prob Require Import  weakestpre lang spec_ra lifting notation iEff class_instances spec_tactics.

Class probeffGS Σ := HeapG {
  probeffGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state *)
  probeffGS_heap : ghost_mapG Σ loc val;
  probeffGS_tapes : ghost_mapG Σ loc tape;
  (* ghost names for the state *)
  probeffGS_heap_name : gname;
  probeffGS_tapes_name : gname;
  (* CMRA and ghost name for the spec *)
  probeffGS_spec :: specG_prob_eff_lang Σ;
  (* CMRA and ghost name for the error *)
  probeffGS_error :: ecGS Σ;
}.

Class probeffGpreS Σ := ProbeffGpreS {
  probeffGpreS_iris  :: invGpreS Σ;
  probeffGpreS_heap  :: ghost_mapG Σ loc val;
  probeffGpreS_tapes :: ghost_mapG Σ loc tape;
  probeffGpreS_spec :: specGpreS Σ;
  probeffGpreS_err   :: ecGpreS Σ;
                          }.

Definition heap_auth `{probeffGS Σ} :=
  @ghost_map_auth _ _ _ _ _ probeffGS_heap probeffGS_heap_name.
Definition tapes_auth `{probeffGS Σ} :=
  @ghost_map_auth _ _ _ _ _ probeffGS_tapes probeffGS_tapes_name.

Global Instance probeffGS_irisGS `{!probeffGS Σ} : approxisWpGS eff_prob_lang Σ := {
  approxisWpGS_invGS := probeffGS_invG;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes))%I;
  err_interp := ec_supply;
}.


(** Heap *)
Notation "l ↦{ dq } v" := (@ghost_map_elem _ _ _ _ _ probeffGS_heap probeffGS_heap_name l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (l ↦{ DfracDiscarded } v)%I
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (l ↦{ DfracOwn q } v)%I
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (l ↦{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↦  v") : bi_scope.

(** Tapes *)
Notation "l ↪{ dq } v" := (@ghost_map_elem _ _ tape _ _ probeffGS_tapes probeffGS_tapes_name l dq v)
  (at level 20, format "l  ↪{ dq }  v") : bi_scope.
Notation "l ↪□ v" := (l ↪{ DfracDiscarded } v)%I
  (at level 20, format "l  ↪□  v") : bi_scope.
Notation "l ↪{# q } v" := (l ↪{ DfracOwn q } v)%I
  (at level 20, format "l  ↪{# q }  v") : bi_scope.
Notation "l ↪ v" := (l ↪{ DfracOwn 1 } v)%I
  (at level 20, format "l  ↪  v") : bi_scope.

(** User-level tapes *)
Definition nat_tape `{probeffGS Σ} l (N : nat) (ns : list nat) : iProp Σ :=
  ∃ (fs : list (fin (S N))), ⌜fin_to_nat <$> fs = ns⌝ ∗ l ↪ (N; fs).

Notation "l ↪N ( M ; ns )" := (nat_tape l M ns)%I
  (at level 20, format "l  ↪N  ( M ;  ns )") : bi_scope.

Section tape_interface.
  Context `{!probeffGS Σ}.

  (** Helper lemmas to go back and forth between the user-level representation
      of tapes (using nat) and the backend (using fin) *)

  Lemma tapeN_to_empty l M :
    (l ↪N ( M ; [] ) -∗ l ↪ ( M ; [] )).
  Proof.
    iIntros "Hl".
    iDestruct "Hl" as (?) "(%Hmap & Hl')".
    by destruct (fmap_nil_inv _ _ Hmap).
  Qed.


  Lemma empty_to_tapeN l M :
    (l ↪ ( M ; [] ) -∗ l ↪N ( M ; [] )).
  Proof.
    iIntros "Hl".
    iExists []. auto.
  Qed.

  Lemma read_tape_head l M n ns :
    (l ↪N ( M ; n :: ns ) -∗
      ∃ x xs, l ↪ ( M ; x :: xs ) ∗ ⌜ fin_to_nat x = n ⌝ ∗
        ( l ↪ ( M ; xs ) -∗l ↪N ( M ; ns ) )).
  Proof.
    iIntros "Hl".
    iDestruct "Hl" as (xss) "(%Hmap & Hl')".
    destruct (fmap_cons_inv _ _ _ _ Hmap) as (x&xs&->&Hxs&->).
    iExists x, xs.
    iFrame.
    iSplit; auto.
    iIntros.
    iExists xs; auto.
  Qed.

 
  Lemma spec_tapeN_to_empty l M :
    (l ↪ₛN ( M ; [] ) -∗ l ↪ₛ ( M ; [] )).
  Proof.
    iIntros "Hl".
    iDestruct "Hl" as (?) "(%Hmap & Hl')".
    by destruct (fmap_nil_inv _ _ Hmap).
  Qed.

  Lemma empty_to_spec_tapeN l M :
    (l ↪ₛ ( M ; [] ) -∗ l ↪ₛN ( M ; [] )).
  Proof.
    iIntros "Hl".
    iExists []. auto.
  Qed.

  Lemma read_spec_tape_head l M n ns :
    (l ↪ₛN ( M ; n :: ns ) -∗
      ∃ x xs, l ↪ₛ ( M ; x :: xs ) ∗ ⌜ fin_to_nat x = n ⌝ ∗
              ( l ↪ₛ ( M ; xs ) -∗l ↪ₛN ( M ; ns ) )).
  Proof.
    iIntros "Hl".
    iDestruct "Hl" as (xss) "(%Hmap & Hl')".
    destruct (fmap_cons_inv _ _ _ _ Hmap) as (x&xs&->&Hxs&->).
    iExists x, xs.
    iFrame.
    iSplit; auto.
    iIntros.
    iExists xs; auto.
  Qed.


End tape_interface.


Section lifting.
Context `{!probeffGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

(** Recursive functions: we do not use this lemma as it is easier to use Löb
    induction directly, but this demonstrates that we can state the expected
    reasoning principle for recursive functions, without any visible ▷. *)

Lemma ewp_rec_löb E f x e Φ Ψ Ψ':
  □ ( □ (∀ v, Ψ v -∗ EWP (rec: f x := e)%V v @ E <| Ψ' |> {{ Φ }}) -∗
     ∀ v, Ψ v -∗ EWP (subst' x v (subst' f (rec: f x := e) e)) @ E <| Ψ' |> {{ Φ }}) -∗
  ∀ v, Ψ v -∗ EWP (rec: f x := e)%V v @ E <| Ψ' |> {{ Φ }}.
Proof.
  iIntros "#Hrec". iLöb as "IH". iIntros (v) "HΨ".
  iApply ewp_pure_step_later; first done.
  iNext. iApply ("Hrec" with "[] HΨ"). iIntros "!>" (w) "HΨ".
  iApply ("IH" with "HΨ").
Qed.

(** Heap *)
Lemma ewp_alloc E Φ Ψ v :
    ⊢ ▷( ∀ l, l ↦ v -∗ Φ #l) -∗
          EWP Alloc (Val v) @ E <| Ψ |> {{ v, Φ v }}.
Proof.
  iIntros "HΦ". 
  iApply ewp_lift_atomic_head_step; [done|done|].
  iIntros (σ1) "[Hh Ht] !#".
  iSplit. {iPureIntro. eexists. apply head_step_support_equiv_rel. constructor; eauto. }
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iMod ((ghost_map_insert (fresh_loc σ1.(heap)) v) with "Hh") as "[? Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iFrame.
  rewrite map_union_empty -insert_union_singleton_l.
  iFrame.
  iIntros "!>". by iApply "HΦ".
Qed.

(* Lemma ewp_allocN_seq (N : nat) (z : Z) E v Φ Ψ :
     TCEq N (Z.to_nat z) →
     (0 < N)%Z →
      (▷ ∀ l, ([∗ list] i ∈ seq 0 N, (l +ₗ i) ↦ v) -∗ Φ #l) -∗
     EWP
       AllocN (Val $ LitV $ LitInt $ z) (Val v) @ E <| Ψ |>
     {{v, Φ v}}.
   Proof.
     iIntros (He Hn Φ) "_ HΦ".
     iApply wp_lift_atomic_head_step; [done|].
     iIntros (σ1) "[Hh Ht] !#".
     iSplit.
     { iPureIntro.
       rewrite /head_reducible.
       eexists.
       apply head_step_support_equiv_rel.
       econstructor; eauto.
       lia.
     }
     iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
     iMod ((ghost_map_insert_big _ _ with "Hh")) as "[$ Hl]".
     iIntros "!>". iFrame.
     iApply "HΦ".
     iInduction (H) as [ | ?] "IH" forall (σ1).
     - simpl.
       iSplit; auto.
       rewrite map_union_empty.
       rewrite loc_add_0.
       by rewrite big_sepM_singleton.
     - rewrite seq_S.
       rewrite heap_array_replicate_S_end.
       iPoseProof (big_sepM_union _ _ _ _ with "Hl") as "[H1 H2]".
       iApply big_sepL_app.
       iSplitL "H1".
       + iApply "IH".
         { iPureIntro. lia. }
         iApply "H1".
       + simpl. iSplit; auto.
         by rewrite big_sepM_singleton.
         Unshelve.
         {
           apply heap_array_map_disjoint.
           intros.
           apply not_elem_of_dom_1.
           by apply fresh_loc_offset_is_fresh.
         }
         apply heap_array_map_disjoint.
         intros.
         apply not_elem_of_dom_1.
         rewrite dom_singleton.
         apply not_elem_of_singleton_2.
         intros H2.
         apply loc_add_inj in H2.
         rewrite length_replicate in H1.
         lia.
   Qed. *)

Lemma ewp_load E l dq v Φ Ψ :
  ▷ l ↦{dq} v -∗                (* should add a ▷ here *)
  ▷ (l ↦{dq} v -∗ Φ v) -∗
  EWP Load (Val $ LitV $ LitLoc l) @ E <| Ψ |> {{ v, Φ v }}.
Proof.
  iIntros ">Hl HΦ". 
  iApply ewp_lift_atomic_head_step; [done|done|].
  iIntros (σ1) "[Hh Ht] !#". 
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  iSplit. { iPureIntro. eexists. apply head_step_support_equiv_rel. constructor; eauto. }
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iFrame. iModIntro. by iApply "HΦ".
Qed.

  
Lemma ewp_store E l v' v Φ Ψ :
  ▷ l ↦ v' -∗                     
  ▷ (l ↦ v -∗ Φ #()) -∗
  EWP #l <- v @ E <| Ψ |> {{ v, Φ v }}.
Proof.
  iIntros ">Hl HΦ".
  iApply ewp_lift_atomic_head_step; [done|done|].
  iIntros (σ1) "[Hh Ht] !#".
  iDestruct (ghost_map_lookup with "Hh Hl") as %?.
  iSplit. { iPureIntro. eexists. apply head_step_support_equiv_rel. econstructor; eauto. }
  iIntros "!> /=" (e2 σ2 Hs); inv_head_step.
  iMod (ghost_map_update with "Hh Hl") as "[$ Hl]".
  iFrame. iModIntro. by iApply "HΦ".
Qed.

  
Lemma ewp_rand (N : nat) (z : Z) E Φ Ψ :
  TCEq N (Z.to_nat z) →
  ▷ (∀ n : nat, ⌜n ≤ N⌝ -∗ Φ #n) -∗
               EWP rand #z @ E <| Ψ |> {{ v, Φ v }}.
Proof.
  iIntros (->) "HΦ".
  iApply ewp_lift_atomic_head_step; [done|done|].
  iIntros (σ1) "Hσ !#".
  iSplit. { iPureIntro. eexists. apply head_step_support_equiv_rel. econstructor; eauto. }
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iApply ("HΦ" $! x).
  iPureIntro.
  pose proof (fin_to_nat_lt x); lia.
  Unshelve. apply Fin.F1. 
Qed.

(** Tapes  *)
Lemma ewp_alloc_tape N z E Φ Ψ :
  TCEq N (Z.to_nat z) →
  ▷ (∀ α : loc, α ↪N (N; []) -∗ Φ #lbl:α) -∗
  EWP alloc #z @ E <| Ψ |> {{ v, Φ v }}.
Proof.
  iIntros (->) "HΦ".
  iApply ewp_lift_atomic_head_step; [done|done|].
  iIntros (σ1) "(Hh & Ht) !# /=".
  iSplit. { iPureIntro. eexists. apply head_step_support_equiv_rel. econstructor; eauto. }
  iIntros "!>" (e2 σ2 Hs); inv_head_step.
  iMod (ghost_map_insert (fresh_loc σ1.(tapes)) with "Ht") as "[$ Hl]".
  { apply not_elem_of_dom, fresh_loc_is_fresh. }
  iFrame. iModIntro.
  iApply "HΦ".
  iExists []; auto.
Qed.

Lemma ewp_rand_tape N α n ns z E Φ Ψ :
  TCEq N (Z.to_nat z) →
  ▷ α ↪N (N; n :: ns) -∗          
  ▷ (α ↪N (N; ns) ∗ ⌜n ≤ N⌝ -∗ Φ #n) -∗
  EWP rand(#lbl:α) #z @ E <| Ψ |> {{ v, Φ v }}.
Proof.
  iIntros (->) ">Hl HΦ". 
  iApply ewp_lift_atomic_head_step; [done|done|].
  iIntros (σ1) "(Hh & Ht) !#".
  iDestruct (read_tape_head with "Hl") as (x xs) "(Hl&<-&Hret)".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  iSplit. { iPureIntro. eexists. apply head_step_support_equiv_rel. econstructor; eauto. }
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iMod (ghost_map_update with "Ht Hl") as "[$ Hl]".
  iFrame. iModIntro.
  iApply "HΦ".  iSplit; first by iApply "Hret".
  iPureIntro.
  pose proof (fin_to_nat_lt x); lia.
Qed.

Lemma ewp_rand_tape_empty N z α E Φ Ψ:
  TCEq N (Z.to_nat z) →
  ▷ α ↪N (N; []) -∗              
  ▷ (∀ n : nat, α ↪N (N; []) ∗ ⌜n ≤ N⌝ -∗ Φ #n) -∗
  EWP rand(#lbl:α) #z @ E <| Ψ |> {{ v, Φ v }}.
Proof.
  iIntros (->) ">Hl HΦ".
  iPoseProof (tapeN_to_empty with "Hl") as "Hl".
  iApply ewp_lift_atomic_head_step; [done|done|].
  iIntros (σ1) "(Hh & Ht) !#".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  iSplit. { iPureIntro. eexists. apply head_step_support_equiv_rel. apply RandTapeEmptyS; eauto. }
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iModIntro. iApply ("HΦ" with "[$Hl]").
  iSplit; auto.
  iPureIntro.
  pose proof (fin_to_nat_lt x); lia.
  Unshelve. apply Fin.F1.
Qed.

Lemma ewp_rand_tape_wrong_bound N M z α E ns Φ Ψ :
  TCEq N (Z.to_nat z) →
  N ≠ M →
  ▷ α ↪N (M; ns) -∗              
  ▷ (∀ n : nat, α ↪N (M; ns) ∗ ⌜n ≤ N⌝ -∗ Φ #n) -∗
  EWP rand(#lbl:α) #z @ E <| Ψ |> {{ v, Φ v }}.
Proof.
  iIntros (-> ?) ">Hl HΦ".
  iApply ewp_lift_atomic_head_step; [done|done|].
  iIntros (σ1) "(Hh & Ht) !#".
  iDestruct "Hl" as (?) "(?&Hl)".
  iDestruct (ghost_map_lookup with "Ht Hl") as %?.
  iSplit. { iPureIntro. eexists. apply head_step_support_equiv_rel. eapply RandTapeOtherS; eauto. }
  iIntros "!>" (e2 σ2 Hs).
  inv_head_step.
  iFrame.
  iModIntro.
  iApply ("HΦ").
  iFrame.
  iPureIntro.
  pose proof (fin_to_nat_lt x); lia.
  Unshelve. apply Fin.F1.
Qed.

(** spec [rand] *)
Lemma ewp_rand_r N z E e K Φ Ψ :
  TCEq N (Z.to_nat z) →
  ⤇ fill K (rand #z) ∗
  (∀ n : nat, ⤇ fill K #n -∗ ⌜ n ≤ N ⌝ -∗ EWP e @ E <| Ψ |> {{v, Φ v }})
  ⊢ EWP e @ E <| Ψ |> {{v, Φ v }}.
Proof.
  iIntros (->) "(Hj & Hwp)".
  iApply ewp_lift_step_spec_couple.
  iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)".
  iDestruct (spec_auth_prog_agree with "Hs Hj") as %->.
  iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
  iApply spec_coupl_step.
  { apply reducible_fill. eexists. simpl. apply head_step_prim_step. apply head_step_support_equiv_rel. econstructor; eauto. }
  simpl.
  rewrite fill_dmap //=.
  iIntros (e2' σ2' ([? ? ]&?&Hs)%dmap_pos).
  simplify_eq/=.
(*   rewrite head_prim_step_eq in Hs.
     inv_head_step.
     iApply spec_coupl_ret. iFrame.
     iMod (spec_update_prog (fill K #_) with "Hs Hj") as "[hs Hj]".
     iFrame. iModIntro.
     iMod "Hclose" as "_"; iModIntro.
     iApply ("Hwp" with "Hj").
     iPureIntro.
     pose proof (fin_to_nat_lt x); lia.
   Qed. *)
Admitted.                       (* type classes fail *)

(** This is just a wrapper for tp_alloctape that works with nats
    TODO : Make into tactic *)
Lemma ewp_alloc_tape_r N z E e K Φ Ψ :
  TCEq N (Z.to_nat z) →
  ⤇ fill K (alloc #z) ∗
    (∀ α, ⤇ fill K #lbl:α -∗ α ↪ₛN (N; []) -∗ EWP e @ E <| Ψ |> {{ Φ }})
    ⊢ EWP e @ E <| Ψ |> {{v, Φ v }}.
Proof.
  iIntros (->) "(Hj & Hwp)".
  tp_alloctape as α "Hα".
  iApply ("Hwp" with "[$Hj] [$Hα]").
  iPureIntro.
  auto.
Qed.


  
(** spec [rand(α)] with empty tape  *)
Lemma ewp_rand_empty_r N z E e K α Φ Ψ :
  TCEq N (Z.to_nat z) →
  ⤇ fill K (rand(#lbl:α) #z) ∗ α ↪ₛN (N; []) ∗
  (∀ n : nat, (α ↪ₛN (N; []) ∗ ⤇ fill K #n) -∗ ⌜ n ≤ N ⌝ -∗ EWP e @ E <| Ψ |> {{ Φ }})
  ⊢ EWP e @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros (->) "(Hj & Hα & Hwp)".
  iApply ewp_lift_step_spec_couple.
  iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)".
  iPoseProof (spec_tapeN_to_empty with "Hα") as "Hα".
  iDestruct (spec_auth_prog_agree with "Hs Hj") as %->.
  iDestruct (spec_auth_lookup_tape with "Hs Hα") as %?.
  iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
  iApply spec_coupl_step.
  { apply reducible_fill. eexists. simpl. apply head_step_prim_step. apply head_step_support_equiv_rel. apply RandTapeEmptyS; eauto. }
  simpl.
  rewrite fill_dmap //=.
  iIntros (e2' σ2' ([? ? ]&?&Hs)%dmap_pos).
  simplify_eq/=.
(*   rewrite head_prim_step_eq // in Hs.
     inv_head_step.
     iApply spec_coupl_ret.
     iMod (spec_update_prog (fill K #_) with "Hs Hj") as "[$ Hj]".
     iFrame. iModIntro.
     iMod "Hclose" as "_"; iModIntro.
     iApply ("Hwp" with "[Hα Hj]");
      first by iFrame; auto.
     iPureIntro.
     pose proof (fin_to_nat_lt x); lia.
   Qed. *)
Admitted.                       (* type classes fail *)

(** This is just a wrapper for tp_rand that works with nats
    TODO: Make into tactic *)
Lemma ewp_rand_tape_r N z E e K α Φ Ψ n ns :
  TCEq N (Z.to_nat z) →
  ⤇ fill K (rand(#lbl:α) #z) ∗ α ↪ₛN (N; n::ns) ∗
    ((α ↪ₛN (N; ns) ∗ ⤇ fill K #n) -∗ ⌜ n ≤ N ⌝ -∗ EWP e @ E <| Ψ |> {{ Φ }})
    ⊢ EWP e @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros (Heq) "(Hj & Hα & Hwp)".
  iDestruct (read_spec_tape_head with "Hα") as (x xs) "(Hl&<-&Hret)".
  tp_rand.
  iDestruct ("Hret" with "Hl") as "Hret".
  iApply ("Hwp" with "[$]").
  iPureIntro.
  pose proof (fin_to_nat_lt x);lia.
Qed.

(** spec [rand(α)] with wrong tape  *)
Lemma ewp_rand_wrong_tape_r N M z E e K α Φ Ψ ns :
  TCEq N (Z.to_nat z) →
  N ≠ M →
  ⤇ fill K (rand(#lbl:α) #z) ∗ α ↪ₛN (M; ns) ∗
  (∀ (n : nat), (α ↪ₛN (M; ns) ∗ ⤇ fill K #n) -∗ ⌜ n ≤ N ⌝ -∗ EWP e @ E <| Ψ |> {{ Φ }})
  ⊢ EWP e @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros (-> ?) "(Hj & Hα & Hwp)".
  iApply ewp_lift_step_spec_couple.
  iIntros (σ1 e1' σ1' ε1) "(Hσ & Hs & Hε)".
  iDestruct "Hα" as (?) "(%&Hα)".
  iDestruct (spec_auth_prog_agree with "Hs Hj") as %->.
  iDestruct (spec_auth_lookup_tape with "Hs Hα") as %?.
  iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
  iApply spec_coupl_step.
  { apply reducible_fill. eexists. simpl. apply head_step_prim_step. apply head_step_support_equiv_rel. eapply RandTapeOtherS; eauto. }
  simpl.
  rewrite fill_dmap //=.
  iIntros (e2' σ2' ([? ? ]&?&Hs)%dmap_pos).
  simplify_eq/=.
(*   rewrite head_prim_step_eq // in Hs.
     inv_head_step.
     iApply spec_coupl_ret.
     iMod (spec_update_prog (fill K #_) with "Hs Hj") as "[$ Hj]".
     iFrame. iModIntro.
     iMod "Hclose" as "_"; iModIntro.
     iApply ("Hwp" with "[-]"); first by iFrame.
     iPureIntro.
     pose proof (fin_to_nat_lt x); lia.
   Qed. *)
Admitted.                       (* type classes fail *)

End lifting.

Global Hint Extern 0 (TCEq _ (Z.to_nat _ )) => rewrite Nat2Z.id : typeclass_instances.
