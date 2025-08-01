(** Compataibility rules *)
From stdpp Require Import namespaces.
From clutch.con_prob_lang Require Import lang notation.
From clutch.foxtrot Require Import primitive_laws proofmode coupling_rules.
From clutch.foxtrot.binary_rel Require Import binary_model binary_rel_tactics binary_app_rel_rules.

Section compatibility.
  Context `{!foxtrotRGS Σ}.
  Implicit Types e : expr.

  (* Local Ltac value_case := *)
  (*   try rel_pure_l; try rel_pure_r; rel_values. *)

  Local Tactic Notation "rel_bind_ap" uconstr(e1) uconstr(e2) constr(IH) ident(v) ident(w) constr(Hvs) :=
    rel_bind_l e1;
    rel_bind_r e2;
    iApply (refines_bind with IH);
    iIntros (v w) (Hvs); simpl.

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

  Lemma refines_cmpxchg_ref A e1 e2 e3 e1' e2' e3' :
    (REL e1 << e1' : lrel_ref (lrel_ref A)) -∗
    (REL e2 << e2' : lrel_ref A) -∗
    (REL e3 << e3' : lrel_ref A) -∗
    REL (CmpXchg e1 e2 e3) << (CmpXchg e1' e2' e3') : lrel_prod (lrel_ref A) lrel_bool.
  Proof.
    iIntros "IH1 IH2 IH3".
    rel_bind_l e3; rel_bind_r e3'.
    iApply (refines_bind with "IH3").
    iIntros (v3 v3') "#IH3".
    rel_bind_l e2; rel_bind_r e2'.
    iApply (refines_bind with "IH2").
    iIntros (v2 v2') "#IH2".
    rel_bind_l e1; rel_bind_r e1'.
    iApply (refines_bind with "IH1").
    iIntros (v1 v1') "#IH1 /=".
    iPoseProof "IH1" as "IH1'".
    iDestruct "IH1" as (l1 l2) "(% & % & Hinv)"; simplify_eq/=.
    rewrite {2}/lrel_car /=.
    iDestruct "IH2" as (r1 r2 -> ->) "Hr".
    (* iDestruct "IH3" as (n1 n2 -> ->) "Hn". *)
    rewrite -(fill_empty (CmpXchg #l1 _ _)).
    iApply refines_atomic_l.
    iIntros (? j) "Hspec".
    iInv (logN .@ (l1,l2)) as (v1 v2) "[Hl1 [>Hl2 #Hv]]" "Hclose".
    iModIntro.
    destruct (decide ((v1, v2) = (#r1, #r2))); simplify_eq/=.
    - iApply wp_pupd.
      wp_cmpxchg_suc.
      iModIntro.
      tp_cmpxchg_suc j.
      iModIntro.
      iMod ("Hclose" with "[-Hspec]").
      { iNext; iExists _, _; by iFrame. }
      iModIntro.
      iFrame. 
      rel_values. subst.
      iExists _, _, _, _. do 2 (iSplitL; first done).
      iFrame "Hv". iExists _. done.
    - iApply wp_pupd.
      destruct (decide (v1=#r1)); simplify_eq; last first.
      + destruct (decide (v2 = #r2)); simplify_eq/=.
        * wp_cmpxchg_fail.
          iDestruct "Hv" as (r1' r2' ? ?) "#Hv". simplify_eq/=.
          destruct (decide ((l1, l2) = (r1, r2'))); simplify_eq/=.
          { iInv (logN.@(r1', r2')) as (? ?) "(Hr1 & >Hr2 & Hrr)" "Hcl".
            iExFalso. by iCombine "Hr2 Hl2" gives %[]. }
          destruct (decide ((l1, l2) = (r1', r2'))); simplify_eq/=.
          ++ assert (r1' ≠ r1) by naive_solver.
             iInv (logN.@(r1, r2')) as (? ?) "(Hr1 & >Hr2 & Hrr)" "Hcl".
             iExFalso. by iCombine "Hr2 Hl2" gives %[].
          ++ iInv (logN.@(r1, r2')) as (? ?) "(Hr1 & >Hr2 & Hrr)" "Hcl".
             iInv (logN.@(r1', r2')) as (? ?) "(Hr1' & >Hr2' & Hrr')" "Hcl'".
             iExFalso. by iCombine "Hr2 Hr2'" gives %[].
        * wp_cmpxchg_fail.
          iModIntro.
          tp_cmpxchg_fail j.
          iModIntro. 
          iMod ("Hclose" with "[-Hspec]").
          { iNext; iExists _, _; by iFrame. }
          iModIntro. iFrame. 
          rel_values. iModIntro. iExists _,_,_,_.
          repeat iSplit; eauto.
      + assert (v2 ≠ #r2) by naive_solver.
        wp_cmpxchg_suc.
        iDestruct "Hv" as (r1' r2' ? ?) "#Hv". simplify_eq/=.
        destruct (decide ((l1, l2) = (r1', r2'))); simplify_eq/=.
        { iInv (logN.@(r1', r2)) as (? ?) "(>Hr1 & >Hr2 & Hrr)" "Hcl".
          iExFalso. by iCombine "Hr1 Hl1" gives %[]. }
        destruct (decide ((l1, l2) = (r1', r2))); simplify_eq/=.
        { iInv (logN.@(r1', r2')) as (? ?) "(>Hr1 & >Hr2 & Hrr)" "Hcl".
          iExFalso. by iCombine "Hr1 Hl1" gives %[]. }
        iInv (logN.@(r1', r2)) as (? ?) "(>Hr1 & >Hr2 & Hrr)" "Hcl".
        iInv (logN.@(r1', r2')) as (? ?) "(>Hr1' & >Hr2' & Hrr')" "Hcl'".
        iExFalso. by iCombine "Hr1 Hr1'" gives %[].
  Qed.

  Lemma refines_xchg e1 e2 e1' e2' A :
    (REL e1 << e1' : ref A) -∗
    (REL e2 << e2' : A) -∗
    REL Xchg e1 e2 << Xchg e1' e2' : A.
  Proof.
    iIntros "IH1 IH2".
    rel_bind_ap e2 e2' "IH2" w w' "IH2".
    rel_bind_ap e1 e1' "IH1" v v' "IH1".
    iDestruct "IH1" as (l l') "(% & % & Hinv)"; simplify_eq/=.
    rewrite -(fill_empty (Xchg #l _)).
    iApply refines_atomic_l.
    iIntros (? j) "Hspec".
    iInv (logN.@ (l,l')) as (v v') "[Hv1 [>Hv2 #Hv]]" "Hclose".
    iModIntro.
    iApply wp_pupd.
    wp_xchg.
    iModIntro.
    tp_xchg j.
    iModIntro.
    iMod ("Hclose" with "[Hv1 Hv2 IH2]").
    { iNext; iExists _, _; simpl; iFrame. }
    iModIntro. iFrame. simpl.
    rel_values.
  Qed.
  
End compatibility.
