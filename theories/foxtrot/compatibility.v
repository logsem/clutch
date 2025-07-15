(** Compataibility rules *)
From stdpp Require Import namespaces.
From clutch.con_prob_lang Require Import lang notation.
From clutch.foxtrot Require Import primitive_laws proofmode model coupling_rules.

Section compatibility.
  Context `{!foxtrotRGS Σ}.
  Implicit Types e : expr.

  (* Local Ltac value_case := *)
  (*   try rel_pure_l; try rel_pure_r; rel_values. *)

  (* Local Tactic Notation "rel_bind_ap" uconstr(e1) uconstr(e2) constr(IH) ident(v) ident(w) constr(Hvs) := *)
  (*   rel_bind_l e1; *)
  (*   rel_bind_r e2; *)
  (*   iApply (refines_bind with IH); *)
  (*   iIntros (v w) (Hvs); simpl. *)

  Local Ltac unfold_rel := rewrite refines_eq /refines_def.

  Lemma refines_pair e1 e2 e1' e2' A B:
    (REL e1 << e1' : A) -∗
    (REL e2 << e2' : B) -∗
    REL (e1, e2) << (e1', e2') : A * B.
  Proof.
    unfold_rel.
    iIntros "IH1 IH2" (K j) "Hspec".
    tp_bind j (e2')%E.
    iSpecialize ("IH2" $! _ j with "[$]").
    (* iMod "IH2". *)
    (* iModIntro. *)
    wp_bind e2.
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&?)".
    wp_bind e1.
    simpl.
    tp_bind j e1'.
    iSpecialize ("IH1" with "[$]").
    (* iMod ("IH1"). *)
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&?)".
    simpl.
    tp_pures j.
    wp_pures.
    by iFrame.
  Qed.
  
  Lemma refines_injl e e' τ1 τ2 :
    (REL e << e' : τ1) -∗
    REL InjL e << InjL e' : τ1 + τ2.
  Proof.
    unfold_rel.
    iIntros "IH".
    iIntros (??) "?".
    tp_bind j e'.
    iDestruct ("IH" with "[$]") as "IH".
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&?)".
    simpl. tp_pures j.
    wp_pures.
    iFrame.
    iExists _, _. eauto. 
  Qed.

  Lemma refines_injr e e' τ1 τ2 :
    (REL e << e' : τ2) -∗
    REL InjR e << InjR e' : τ1 + τ2.
  Proof.
    unfold_rel.
    iIntros "IH".
    iIntros (??) "?".
    tp_bind j e'.
    iDestruct ("IH" with "[$]") as "IH".
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&?)".
    simpl. tp_pures j.
    wp_pures.
    iFrame.
    iExists _, _. eauto. 
  Qed.

  Lemma refines_app e1 e2 e1' e2' A B :
    (REL e1 << e1' : A → B) -∗
    (REL e2 << e2' : A) -∗
    REL App e1 e2 << App e1' e2' : B.
  Proof.
    unfold_rel.
    iIntros "IH1 IH2" (K j) "Hspec".
    tp_bind j (e2')%E.
    iSpecialize ("IH2" $! _ j with "[$]").
    wp_bind e2.
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&?)".
    wp_bind e1.
    simpl.
    tp_bind j e1'.
    iSpecialize ("IH1" with "[$]").
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&Hiff)".
    simpl.
    tp_pures j.
    wp_pures.
    iDestruct ("Hiff" with "[$]") as "Hiff".
    unfold_rel.
    by iApply ("Hiff" with "[$]").
  Qed.
  
  Lemma refines_seq A e1 e2 e1' e2' B :
    (REL e1 << e1' : A) -∗
    (REL e2 << e2' : B) -∗
    REL (e1;; e2) << (e1';; e2') : B.
  Proof.
    unfold_rel.
    iIntros "IH1 IH2".
    iIntros.
    wp_bind e1.
    tp_bind j e1'.
    iDestruct ("IH1" with "[$]") as "?".
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&?)".
    wp_pures.
    simpl.
    tp_pures j.
    by iApply ("IH2" with "[$]").
  Qed.
  
  Lemma refines_pack (A : lrel Σ) e e' (C : lrel Σ → lrel Σ) :
    (REL e << e' : C A) -∗
    REL e << e' : ∃ A, C A.
  Proof.
    unfold_rel.
    iIntros "H".
    iIntros.
    iDestruct ("H" with "[$]") as "?".
    wp_apply (wp_mono with "[$]").
    iIntros (?) "(%&?&?)".
    iFrame.
  Qed. 

  Lemma refines_forall e e' (C : lrel Σ → lrel Σ) :
    □ (∀ A, REL e << e' : C A) -∗
    REL (λ: <>, e)%V << (λ: <>, e')%V : ∀ A, C A.
  Proof.
    unfold_rel.
    iIntros "#H".
    iIntros.
    wp_pures.
    iFrame.
    iModIntro.
    iIntros (??).
    iIntros "!>" (??).
    unfold_rel.
    iIntros (? j').
    iIntros.
    wp_pures.
    tp_pures j'.
    iDestruct ("H" with "[$]") as "H'".
    by iApply "H'".
  Qed.
  
(* Tactic Notation "rel_store_l_atomic" := rel_apply_l refines_store_l. *)

  Lemma refines_store e1 e2 e1' e2' A :
    (REL e1 << e1' : ref A) -∗
    (REL e2 << e2' : A) -∗
    REL e1 <- e2 << e1' <- e2' : ().
  Proof.
    unfold_rel.
    iIntros "IH1 IH2" (K j) "Hspec".
    tp_bind j (e2')%E.
    iSpecialize ("IH2" $! _ j with "[$]").
    wp_bind e2.
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&HA)".
    wp_bind e1.
    simpl.
    tp_bind j e1'.
    iSpecialize ("IH1" with "[$]").
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&#H)".
    iDestruct ("H") as "(%&%&%&%&H)".
    subst.
    iInv "H" as "(%&%&>l1&>l2&H')" "Hclose".
    simpl.
    tp_store j.
    wp_store.
    iMod ("Hclose" with "[$HA $l1 $l2]") as "_".
    by iFrame.
  Qed.
  
  Lemma refines_load e e' A :
    (REL e << e' : ref A) -∗
    REL !e << !e' : A.
  Proof.
    iIntros "H".
    unfold_rel.
    iIntros.
    tp_bind j e'.
    iDestruct ("H" with "[$]") as "H".
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&#H)".
    simpl.
    iDestruct ("H") as "(%&%&%&%&H)".
    subst.
    iInv "H" as "(%&%&>l1&>l2&#H')" "Hclose".
    simpl.
    tp_load j.
    wp_load.
    iMod ("Hclose" with "[$H' $l1 $l2]") as "_".
    by iFrame.
  Qed.
  
  Lemma refines_rand_tape e1 e1' e2 e2' :
    (REL e1 << e1' : lrel_nat) -∗
    (REL e2 << e2' : lrel_tape) -∗
    REL rand(e2) e1  << rand(e2') e1' : lrel_nat.
  Proof.
    unfold_rel.
    iIntros "IH1 IH2".
    iIntros.
    tp_bind j e2'.
    iDestruct ("IH2" with "[$]") as "H".
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&HA)".
    simpl.
    tp_bind j e1'.
    iDestruct ("IH1" with "[$]") as "H".
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&HA')".
    simpl.
    iDestruct "HA'" as (M) "[-> ->]".
    iDestruct "HA" as (α α' N -> ->) "#H".
    iInv (logN.@ (α, α')) as ">[Hα Hα']" "Hclose".
    iPoseProof (empty_to_spec_tapeN with "Hα'") as "Hα'".
    iPoseProof (empty_to_tapeN with "Hα") as "Hα".
    destruct (decide (N = M)); simplify_eq.
    - iApply (wp_couple_rand_lbl_rand_lbl with "[$]"); auto.
      iNext. iIntros (?) "(?&?&?&%)".
      iPoseProof (spec_tapeN_to_empty with "[$]") as "Hαs".
      iPoseProof (tapeN_to_empty with "[$]") as "Hα".
      iMod ("Hclose" with "[$]").
      iModIntro.
      iExists _. simpl. iFrame. by iExists _. 
    - iApply (wp_couple_rand_lbl_rand_lbl_wrong
               with "[$]"); [done|done|].
      iNext. iIntros (?) "(?&?&?&%)".
      iPoseProof (spec_tapeN_to_empty with "[$]") as "Hαs".
      iPoseProof (tapeN_to_empty with "[$]") as "Hα".
      iMod ("Hclose" with "[$]").
      iModIntro.
      iExists _. simpl. iFrame. by iExists _.
  Qed.

  Lemma refines_rand_unit e e' :
    (REL e << e' : lrel_nat) -∗
    REL rand e << rand e' : lrel_nat.
  Proof.
    unfold_rel.
    iIntros "H".
    iIntros.
    tp_bind j e'.
    iDestruct ("H" with "[$]") as "H".
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&HA)".
    iDestruct "HA" as "(%&->&->)".
    simpl.
    wp_apply (wp_couple_rand_rand with "[$]"); first done.
    iIntros (?) "[% ?]". iFrame.
    by iExists _.
  Qed.
  
End compatibility.
