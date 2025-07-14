(** Compataibility rules *)
From stdpp Require Import namespaces.
From clutch.con_prob_lang Require Import lang notation.
From clutch.foxtrot Require Import primitive_laws proofmode model .

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
    iIntros "IH1 IH2" (K j) "Hspec Hna".
    tp_bind j (e2')%E.
    iSpecialize ("IH2" $! _ j with "[$][$]").
    wp_bind e2.
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&?&?)".
    wp_bind e1.
    simpl.
    tp_bind j e1'.
    iSpecialize ("IH1" with "[$][$]").
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&?&?)".
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
    iIntros (??) "??".
    tp_bind j e'.
    iDestruct ("IH" with "[$][$]") as "IH".
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&?&?)".
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
    iIntros (??) "??".
    tp_bind j e'.
    iDestruct ("IH" with "[$][$]") as "IH".
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&?&?)".
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
    iIntros "IH1 IH2" (K j) "Hspec Hna".
    tp_bind j (e2')%E.
    iSpecialize ("IH2" $! _ j with "[$][$]").
    wp_bind e2.
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&?&?)".
    wp_bind e1.
    simpl.
    tp_bind j e1'.
    iSpecialize ("IH1" with "[$][$]").
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&?&Hiff)".
    simpl.
    tp_pures j.
    wp_pures.
    iDestruct ("Hiff" with "[$]") as "Hiff".
    unfold_rel.
    iApply ("Hiff" with "[$][$]").
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
    iDestruct ("IH1" with "[$][$]") as "?".
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&?&?)".
    wp_pures.
    simpl.
    tp_pures j.
    iApply ("IH2" with "[$][$]").
  Qed.
  
  Lemma refines_pack (A : lrel Σ) e e' (C : lrel Σ → lrel Σ) :
    (REL e << e' : C A) -∗
    REL e << e' : ∃ A, C A.
  Proof.
    unfold_rel.
    iIntros "H".
    iIntros.
    iDestruct ("H" with "[$][$]") as "?".
    wp_apply (wp_mono with "[$]").
    iIntros (?) "(%&?&?&?)".
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
    iDestruct ("H" with "[$][$]") as "H'".
    iApply "H'".
  Qed.
  
(* Tactic Notation "rel_store_l_atomic" := rel_apply_l refines_store_l. *)

  Lemma refines_store e1 e2 e1' e2' A :
    (REL e1 << e1' : ref A) -∗
    (REL e2 << e2' : A) -∗
    REL e1 <- e2 << e1' <- e2' : ().
  Proof.
    unfold_rel.
    iIntros "IH1 IH2" (K j) "Hspec Hna".
    tp_bind j (e2')%E.
    iSpecialize ("IH2" $! _ j with "[$][$]").
    wp_bind e2.
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&?&HA)".
    wp_bind e1.
    simpl.
    tp_bind j e1'.
    iSpecialize ("IH1" with "[$][$]").
    wp_apply (wp_wand with "[$]").
    iIntros (?) "(%&?&?&#H)".
    iDestruct ("H") as "(%&%&%&%&H)".
    subst.
    iInv "H" as "(%&%&>l1&>l2&H')" "Hclose".
    simpl.
    tp_store j.
    wp_store.
    iMod ("Hclose" with "[$HA $l1 $l2]") as "_".
    by iFrame.
  Qed.
  
  (* Lemma refines_load e e' A : *)
  (*   (REL e << e' : ref A) -∗ *)
  (*   REL !e << !e' : A. *)
  (* Proof. *)
  (*   iIntros "H". *)
  (*   rel_bind_ap e e' "H" v v' "H". *)
  (*   iDestruct "H" as (l l' -> ->) "#H". *)
  (*   (* TODO: maybe fix tactic? *) *)
  (*   (* rel_load_l_atomic. *) *)
  (*   iApply (refines_atomic_l _ _ []); simpl. *)
  (*   iIntros (K') "Hr". *)
  (*   iInv (logN .@ (l,l')) as (w w') "[Hw1 [>Hw2 #Hw]]" "Hclose"; simpl. *)
  (*   iModIntro. *)
  (*   tp_load. *)
  (*   wp_load. *)
  (*   iMod ("Hclose" with "[Hw1 Hw2]") as "_". *)
  (*   { iNext. iExists w,w'; by iFrame. } *)
  (*   iModIntro. iExists _. iFrame. *)
  (*   value_case. *)
  (* Qed. *)

  (* Lemma refines_rand_tape e1 e1' e2 e2' : *)
  (*   (REL e1 << e1' : lrel_nat) -∗ *)
  (*   (REL e2 << e2' : lrel_tape) -∗ *)
  (*   REL rand(e2) e1  << rand(e2') e1' : lrel_nat. *)
  (* Proof. *)
  (*   iIntros "IH1 IH2". *)
  (*   rel_bind_ap e2 e2' "IH2" w w' "IH2". *)
  (*   rel_bind_ap e1 e1' "IH1" v v' "IH1". *)
  (*   iDestruct "IH1" as (M) "[-> ->]". *)
  (*   iDestruct "IH2" as (α α' N -> ->) "#H". *)
  (*   iApply (refines_atomic_l _ _ []); simpl. *)
  (*   iIntros (K') "Hr". *)
  (*   iInv (logN.@ (α, α')) as ">[Hα Hα']" "Hclose". *)
  (*   iModIntro. *)
  (*   iPoseProof (empty_to_spec_tapeN with "Hα'") as "Hα'". *)
  (*   iPoseProof (empty_to_tapeN with "Hα") as "Hα". *)
  (*   destruct (decide (N = M)); simplify_eq. *)
  (*   - iApply (wp_couple_rand_lbl_rand_lbl with "[$Hα $Hα' $Hr]"); auto. *)
  (*     iIntros "!>" (N) "(Hα & Hαs & Hr & %)". *)
  (*     iPoseProof (spec_tapeN_to_empty with "Hαs") as "Hαs". *)
  (*     iPoseProof (tapeN_to_empty with "Hα") as "Hα". *)
  (*     iMod ("Hclose" with "[$Hα $Hαs]") as "_". *)
  (*     iModIntro. *)
  (*     iExists _. simpl. iFrame "Hr". *)
  (*     rel_values. *)
  (*   - iApply (wp_couple_rand_lbl_rand_lbl_wrong *)
  (*              with "[$Hα $Hα' $Hr]"); [done|done|]. *)
  (*     iIntros "!>" (m) "(Hα & Hα' & Hr & %)". *)
  (*     iPoseProof (spec_tapeN_to_empty with "Hα'") as "Hα'". *)
  (*     iPoseProof (tapeN_to_empty with "Hα") as "Hα". *)
  (*     iMod ("Hclose" with "[$Hα $Hα']") as "_". *)
  (*     iModIntro. *)
  (*     iExists _. iFrame "Hr". *)
  (*     rel_values. *)
  (* Qed. *)

  (* Lemma refines_rand_unit e e' : *)
  (*   (REL e << e' : lrel_nat) -∗ *)
  (*   REL rand e << rand e' : lrel_nat. *)
  (* Proof. *)
  (*   iIntros "H". *)
  (*   rel_bind_ap e e' "H" v v' "H". *)
  (*   iDestruct "H" as (n) "%H". *)
  (*   destruct H as [-> ->]. *)
  (*   rel_bind_l (rand(_) _)%E. *)
  (*   rel_bind_r (rand(_) _)%E. *)
  (*   iApply (refines_couple_rands_lr); auto. *)
  (*   iIntros (b). *)
  (*   iModIntro. *)
  (*   iIntros "%". *)
  (*   value_case. *)
  (* Qed. *)

End compatibility.
