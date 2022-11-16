(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Compataibility rules *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list.
From iris.program_logic Require Import ectx_lifting.
From self.prob_lang Require Import spec_rules.
From self.prob_logrel Require Import model.
From self.proofmode Require Import rel_tactics.

Section compatibility.
  Context `{!prelocGS Σ}.
  Implicit Types e : expr.

  Local Ltac value_case :=
    try rel_pure_l; try rel_pure_r; rel_values.

  Local Tactic Notation "rel_bind_ap" uconstr(e1) uconstr(e2) constr(IH) ident(v) ident(w) constr(Hvs) :=
    rel_bind_l e1;
    rel_bind_r e2;
    iApply (refines_bind with IH);
    iIntros (v w) (Hvs); simpl.

  Lemma refines_pair e1 e2 e1' e2' A B :
    (REL e1 << e1' : A) -∗
    (REL e2 << e2' : B) -∗
    REL (e1, e2) << (e1', e2') : A * B.
  Proof.
    iIntros "IH1 IH2".
    rel_bind_ap e2 e2' "IH2" v2 v2' "Hvv2".
    rel_bind_ap e1 e1' "IH1" v1 v1' "Hvv1".
    value_case.
    iExists _, _, _, _; eauto.
  Qed.

  Lemma refines_app e1 e2 e1' e2' A B :
    (REL e1 << e1' : A → B) -∗
    (REL e2 << e2' : A) -∗
    REL App e1 e2 << App e1' e2' : B.
  Proof.
    iIntros "IH1 IH2".
    rel_bind_ap e2 e2' "IH2" v v' "Hvv".
    rel_bind_ap e1 e1' "IH1" f f' "Hff".
    by iApply "Hff".
  Qed.

  Lemma refines_seq A e1 e2 e1' e2' B :
    (REL e1 << e1' : A) -∗
    (REL e2 << e2' : B) -∗
    REL (e1;; e2) << (e1';; e2') : B.
  Proof.
    iIntros "IH1 IH2".
    rel_bind_ap e1 e1' "IH1" v v' "#Hvv".
    repeat rel_pure_l. repeat rel_pure_r.
    done.
  Qed.

  Lemma refines_pack (A : lrel Σ) e e' (C : lrel Σ → lrel Σ) :
    (REL e << e' : C A) -∗
    REL e << e' : ∃ A, C A.
  Proof.
    iIntros "H".
    rel_bind_ap e e' "H" v v' "Hvv".
    value_case.
    iModIntro. iExists A. done.
  Qed.

  Lemma refines_forall e e' (C : lrel Σ → lrel Σ) :
    □ (∀ A, REL e << e' : C A) -∗
    REL (λ: <>, e)%V << (λ: <>, e')%V : ∀ A, C A.
  Proof.
    iIntros "#H".
    rel_values. iModIntro.
    iIntros (A ? ?) "_ !#".
    rel_rec_l. rel_rec_r. iApply "H".
  Qed.

  Lemma refines_store e1 e2 e1' e2' A :
    (REL e1 << e1' : ref A) -∗
    (REL e2 << e2' : A) -∗
    REL e1 <- e2 << e1' <- e2' : ().
  Proof.
    iIntros "IH1 IH2".
    rel_bind_ap e2 e2' "IH2" w w' "IH2".
    rel_bind_ap e1 e1' "IH1" v v' "IH1".
    iDestruct "IH1" as (l l') "(% & % & Hinv)"; simplify_eq/=.
    rel_store_l_atomic.
    iInv (logN .@ (l,l')) as (v v') "[Hv1 [>Hv2 #Hv]]" "Hclose".
    iModIntro. iExists _; iFrame "Hv1".
    iNext. iIntros "Hw1".
    rel_store_r.
    iMod ("Hclose" with "[Hw1 Hv2 IH2]").
    { iNext; iExists _, _; simpl; iFrame. }
    value_case.
  Qed.

  Lemma refines_load e e' A :
    (REL e << e' : ref A) -∗
    REL !e << !e' : A.
  Proof.
    iIntros "H".
    rel_bind_ap e e' "H" v v' "H".
    iDestruct "H" as (l l' -> ->) "#H".
    rel_load_l_atomic.
    iInv (logN .@ (l,l')) as (w w') "[Hw1 [>Hw2 #Hw]]" "Hclose"; simpl.
    iModIntro. iExists _; iFrame "Hw1".
    iNext. iIntros "Hw1".
    rel_load_r.
    iMod ("Hclose" with "[Hw1 Hw2]").
    { iNext. iExists w,w'; by iFrame. }
    value_case.
  Qed.

Notation "🖭" := lrel_tape : lrel_scope.
(* ▥⛁🛢⛓🔗🪙🎲 *)

  Lemma refines_flip e e' :
    (REL e << e' : 🖭) -∗
    REL flip e << flip e' : lrel_bool.
  Proof.
    iIntros "H".
    (* rewrite {1} refines_eq /refines_def. *)
    (* rewrite /refines_right. *)
From self Require Import spec_tactics.
    eapply (tac_rel_bind_l e); [ tp_bind_helper |].
    eapply (tac_rel_bind_r e'); [ tp_bind_helper |].
    iApply (refines_bind with "H").
    iIntros (v v') "Hv"; simpl.

    (* rel_bind_ap uconstr(e1) uconstr(e2)
                   constr(IH) ident(v) ident(w) constr(Hv) = *)
    (* rel_bind_l (metatheory.subst_map _ e); *)
    (* rel_bind_r (metatheory.subst_map _ e'). *)
    (* try iSpecialize (IH with "Hvs"); *)
    (* iApply (refines_bind with IH); *)
    (* iIntros (v w) Hv; simpl. *)

    (* rel_bind_ap e e' "H" v v' "H". *)

    iDestruct "Hv" as (α α' -> ->) "#Hv".
    rewrite refines_eq /refines_def.
    iIntros (K) "[#Hss Hr] !#".

    rewrite /refines_right.

    iApply lifting.wp_lift_step_fupd_couple; [done|].
    iIntros (σ [eₛ σₛ]) "[[Hh1 Ht1] Hρ]".
    iInv specN as (ξₛ ρ' e2 σ2) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hρ Hspec0") as %<-.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplit.
    { iPureIntro.
      rewrite /reducible.
      (* flip is certainly reducible. *)
      admit.
    }
    iExists _, _, _. iSplit.
    { iPureIntro. apply state_prim_step_sch_wf.
      (* flip is not a value, okay. *)
      admit. }
    iSplit.
    { iPureIntro.
      (* need to pick a relation... *)
      eapply Rcoupl_exec_det_prefix_r; [done|].
      (* well, why do we have a coupling? *)
      (* eapply (state_prim_state_coupl α α'). *)
      admit.
    }

    iIntros (e3 σ3 [e4 σ4] R2); simplify_eq.
    iIntros "!> !>". rewrite /state_interp /spec_interp /=.
    iMod (spec_interp_update (e2, _) with "Hρ Hspec0") as "[Hρ Hspec0]".

    (* do this...earlier? *)
    iInv (logN .@ (α,α')) as (bs) "[>Hα >Hα']" "Hclose''"; simpl.
    1:admit.


    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Htapes Hα'") as %?%lookup_total_correct.
    simplify_map_eq.
    iMod (ghost_map_update (tapes σ !!! α ++ [b]) with "Ht1 Hα") as "[Ht1 Hα]".
    iFrame.
    iMod (ghost_map_update (tapes σ2 !!! αₛ ++ [b]) with "Htapes Hαs") as "[Htapes Hαs]".
    iMod "Hclose'". iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_"; last first.
    { iModIntro. iApply "Hwp". iExists b. iFrame. }
    iModIntro. rewrite /spec_inv.
    iExists [], _, _, (state_upd_tapes _ _). simpl.
    iFrame. rewrite exec_nil dret_1 //.

    iInv (logN .@ (α,α')) as (bs) "[>Hα >Hα']" "Hclose"; simpl.


    iInv specN as (ξₛ ρ' e2 σ2) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose'".
    iDestruct (spec_interp_auth_frag_agree with "Hρ Hspec0") as %<-.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplit.
    { iPureIntro; eapply Hpstep. }

    iApply wp_couple_tapes.

    2: solve_ndisj.

    rel_load_l_atomic.
    iInv (logN .@ (l,l')) as (w w') "[Hw1 [>Hw2 #Hw]]" "Hclose"; simpl.
    iModIntro. iExists _; iFrame "Hw1".
    iNext. iIntros "Hw1".
    rel_load_r.
    iMod ("Hclose" with "[Hw1 Hw2]").
    { iNext. iExists w,w'; by iFrame. }
    value_case.
  Qed.

End compatibility.
