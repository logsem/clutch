(** Compataibility rules *)
From stdpp Require Import namespaces.
From clutch.delay_prob_lang Require Import lang notation.
From clutch.elton Require Import primitive_laws proofmode.
From clutch.elton.unary_rel Require Import unary_model unary_rel_tactics unary_app_rel_rules.

Section compatibility.
  Context `{!eltonGS Σ}.
  Implicit Types e : expr.

  (* Local Ltac value_case := *)
  (*   try rel_pure_l; try rel_pure_r; rel_values. *)

  Local Tactic Notation "rel_bind_ap" uconstr(e1)  constr(IH) ident(v)  constr(Hvs) :=
    rel_bind_l e1;
    (* rel_bind_r e2; *)
    iApply (refines_bind with IH);
    iIntros (v) (Hvs); simpl.

  Local Ltac unfold_rel := rewrite refines_eq /refines_def.

  Lemma refines_pair e1 e2 A B:
    (REL e1 : A) -∗
    (REL e2 : B) -∗
    REL (e1, e2)  : A * B.
  Proof.
    unfold_rel.
    iIntros "H1 H2".
    wp_bind e2.
    wp_apply (pgl_wp_wand with "[$]").
    iIntros (?) "H2".
    wp_bind e1.
    wp_apply (pgl_wp_wand with "[$]").
    iIntros (?) "H1".
    wp_pures.
    iModIntro. by iFrame "H2 H1".
  Qed.
  
  Lemma refines_injl e τ1 τ2 :
    (REL e  : τ1) -∗
    REL InjL e : τ1 + τ2.
  Proof.
    unfold_rel.
    iIntros "IH".
    (* iIntros (??) "?". *)
    (* tp_bind j e'. *)
    (* iDestruct ("IH" with "[$]") as "IH". *)
    wp_apply (pgl_wp_wand with "[$]").
    iIntros. wp_pures.
    iExists _. eauto.
  Qed.
  
  Lemma refines_injr e τ1 τ2 :
    (REL e : τ2) -∗
    REL InjR e : τ1 + τ2.
  Proof.
    unfold_rel.
    iIntros "IH".
    (* iIntros (??) "?". *)
    (* tp_bind j e'. *)
    (* iDestruct ("IH" with "[$]") as "IH". *)
    wp_apply (pgl_wp_wand with "[$]").
    iIntros. 
    wp_pures.
    iExists _. eauto.
  Qed.
  
  Lemma refines_app e1 e2 A B :
    (REL e1 : A → B) -∗
    (REL e2 : A) -∗
    REL App e1 e2  : B.
  Proof.
    unfold_rel.
    iIntros "IH1 IH2".
    (* tp_bind j (e2')%E. *)
    (* iSpecialize ("IH2" $! _ j with "[$]"). *)
    wp_bind e2.
    wp_apply (pgl_wp_wand with "[$]").
    iIntros. 
    (* iIntros (?) "(%&?&?)". *)
    (* wp_bind e1. *)
    (* simpl. *)
    (* tp_bind j e1'. *)
    (* iSpecialize ("IH1" with "[$]"). *)
    wp_apply (pgl_wp_wand with "[$]").
    iIntros (?) "H".
    simpl in *.
    iDestruct ("H" with "[$]") as "Hiff".
    by unfold_rel.
  Qed.
  
  Lemma refines_seq A e1 e2 B :
    (REL e1 : A) -∗
    (REL e2 : B) -∗
    REL (e1;; e2) : B.
  Proof.
    unfold_rel.
    iIntros "IH1 IH2".
    iIntros.
    wp_bind e1.
    (* iDestruct ("IH1" with "[$]") as "?". *)
    wp_apply (pgl_wp_wand with "[$IH1]").
    iIntros (?) "?".
    by wp_pures.
  Qed.
  
  Lemma refines_pack (A : lrel Σ) e (C : lrel Σ → lrel Σ) :
    (REL e : C A) -∗
    REL e : ∃ A, C A.
  Proof.
    unfold_rel.
    iIntros "H".
    iIntros.
    (* iDestruct ("H" with "[$]") as "?". *)
    wp_apply (pgl_wp_mono with "[$]").
    iIntros (?) "?".
    iFrame.
  Qed. 

  Lemma refines_forall e (C : lrel Σ → lrel Σ) :
    □ (∀ A, REL e : C A) -∗
    REL (λ: <>, e)%V  : ∀ A, C A.
  Proof.
    unfold_rel.
    iIntros "#H".
    iIntros.
    wp_pures.
    iFrame.
    iModIntro.
    iIntros (??).
    iIntros "!>" (?).
    subst.
    unfold_rel.
    wp_pures.
    iApply "H".
  Qed.
  
(* Tactic Notation "rel_store_l_atomic" := rel_apply_l refines_store_l. *)

  Lemma refines_store e1 e2 A :
    (REL e1 : ref A) -∗
    (REL e2 : A) -∗
    REL e1 <- e2 : ().
  Proof.
    unfold_rel.
    iIntros "IH1 IH2". (*  (K j) "Hspec". *)
    (* tp_bind j (e2')%E. *)
    (* iSpecialize ("IH2" $! _ j with "[$]"). *)
    wp_bind e2.
    wp_apply (pgl_wp_wand with "[$]").
    iIntros (?) "HA".
    wp_bind e1.
    (* simpl. *)
    (* tp_bind j e1'. *)
    (* iSpecialize ("IH1" with "[$]"). *)
    wp_apply (pgl_wp_wand with "[$]").
    iIntros (?) "#H".
    iDestruct ("H") as "(%&%&H)".
    subst.
    iInv "H" as "(%&>l1&H')" "Hclose".
    simpl.
    (* tp_store j. *)
    wp_store.
    iMod ("Hclose" with "[$HA $l1]") as "_".
    by iFrame.
  Qed.
  
  Lemma refines_load e A :
    (REL e : ref A) -∗
    REL !e : A.
  Proof.
    iIntros "H".
    unfold_rel.
    iIntros.
    (* tp_bind j e'. *)
    (* iDestruct ("H" with "[$]") as "H". *)
    wp_apply (pgl_wp_wand with "[$]").
    iIntros (?) "#H".
    simpl.
    iDestruct ("H") as "(%&%&H)".
    subst.
    iInv "H" as "(%&>l1&#H')" "Hclose".
    simpl.
    wp_load.
    iMod ("Hclose" with "[$H' $l1]") as "_".
    by iFrame.
  Qed.
  
  (* Lemma refines_rand_tape e1 e2  : *)
  (*   (REL e1 : lrel_nat) -∗ *)
  (*   (REL e2 : lrel_tape) -∗ *)
  (*   REL rand(e2) e1  : lrel_nat. *)
  (* Proof. *)
  (*   unfold_rel. *)
  (*   iIntros "IH1 IH2". *)
  (*   iIntros. *)
  (*   (* tp_bind j e2'. *) *)
  (*   (* iDestruct ("IH2" with "[$]") as "H". *) *)
  (*   wp_apply (wp_wand with "[$]"). *)
  (*   iIntros (?) "HA". *)
  (*   simpl. *)
  (*   (* tp_bind j e1'. *) *)
  (*   (* iDestruct ("IH1" with "[$]") as "H". *) *)
  (*   wp_apply (wp_wand with "[$]"). *)
  (*   iIntros (?) "HA'". *)
  (*   simpl. *)
  (*   iDestruct "HA'" as (M) "->". *)
  (*   iDestruct "HA" as (α N ->) "#H". *)
  (*   iInv (logN.@ (α)) as ">Hα" "Hclose". *)
  (*   (* iPoseProof (empty_to_spec_tapeN with "Hα'") as "Hα'". *) *)
  (*   iPoseProof (empty_to_tapeN with "Hα") as "Hα". *)
  (*   destruct (decide (N = M)); simplify_eq. *)
  (*   - wp_apply (wp_rand_tape_empty with "[$]"). *)
  (*     iIntros (?) "[Ht %]". *)
  (*     iMod ("Hclose" with "[Ht]"). *)
  (*     { iPoseProof (tapeN_to_empty with "[$]") as "$". } *)
  (*     by iExists _. *)
  (*   - wp_apply (wp_rand_tape_wrong_bound with "[$]"); first done. *)
  (*     iIntros (?) "[Ht %]". *)
  (*     iMod ("Hclose" with "[Ht]"). *)
  (*     { iPoseProof (tapeN_to_empty with "[$]") as "$". } *)
  (*     by iExists _. *)
  (* Qed. *)

  Lemma refines_rand e :
    (REL e : lrel_nat) -∗
    REL rand e  : lrel_nat.
  Proof.
    unfold_rel.
    iIntros "H".
    iIntros.
    (* tp_bind j e'. *)
    (* iDestruct ("H" with "[$]") as "H". *)
    wp_apply (pgl_wp_wand with "[$]").
    iIntros (?) "HA".
    iDestruct "HA" as "(%&->)".
    simpl.
    wp_apply (wp_rand); first done.
    iIntros. 
    by iExists _.
  Qed.

  (* Lemma refines_cmpxchg_ref A e1 e2 e3 : *)
  (*   (REL e1 : lrel_ref (lrel_ref A)) -∗ *)
  (*   (REL e2 : lrel_ref A) -∗ *)
  (*   (REL e3 : lrel_ref A) -∗ *)
  (*   REL (CmpXchg e1 e2 e3)  : lrel_prod (lrel_ref A) lrel_bool. *)
  (* Proof. *)
  (*   iIntros "IH1 IH2 IH3". *)
  (*   rel_bind_l e3(* ; rel_bind_r e3' *). *)
  (*   iApply (refines_bind with "IH3"). *)
  (*   iIntros (v3) "#IH3". *)
  (*   rel_bind_l e2(* ; rel_bind_r e2' *). *)
  (*   iApply (refines_bind with "IH2"). *)
  (*   iIntros (v2) "#IH2". *)
  (*   rel_bind_l e1(* ; rel_bind_r e1' *). *)
  (*   iApply (refines_bind with "IH1"). *)
  (*   iIntros (v1) "#IH1 /=". *)
  (*   iPoseProof "IH1" as "IH1'". *)
  (*   iDestruct "IH1" as (l1) "[-> Hinv]"; simplify_eq/=. *)
  (*   rewrite {2}/lrel_car /=. *)
  (*   iDestruct "IH2" as (r1 ->) "Hr". *)
  (*   (* iDestruct "IH3" as (n1 n2 -> ->) "Hn". *) *)
  (*   rewrite -(fill_empty (CmpXchg #l1 _ _)). *)
  (*   iApply refines_atomic_l. *)
  (*   (* iIntros (? j) "Hspec". *) *)
  (*   iInv (logN .@ (l1)) as (v1) "[Hl1 #Hv]" "Hclose". *)
  (*   iModIntro. *)
  (*   destruct (decide (v1 = #r1)); simplify_eq/=. *)
  (*   - iApply wp_pupd. *)
  (*     wp_cmpxchg_suc. *)
  (*     iModIntro. *)
  (*     (* tp_cmpxchg_suc j. *) *)
  (*     iModIntro. *)
  (*     iMod ("Hclose" with "[-]"). *)
  (*     { iNext; iExists _; by iFrame. } *)
  (*     iModIntro. *)
  (*     rel_values. subst. *)
  (*     iExists _, _. *)
  (*     iModIntro. *)
  (*     iSplit; first done. *)
  (*     iSplit; first done. *)
  (*     by iExists _.  *)
  (*   - iApply wp_pupd. *)
  (*     wp_cmpxchg_fail. *)
  (*     iModIntro. *)
  (*     iModIntro.  *)
  (*     iMod ("Hclose" with "[-]"). *)
  (*     { iNext; iExists _; by iFrame. } *)
  (*     iModIntro.  *)
  (*     rel_values. iModIntro. iExists _, _. *)
  (*     repeat iSplit; try done. *)
  (*     by iExists _. *)
  (* Qed. *)

  (* Lemma refines_xchg e1 e2 A : *)
  (*   (REL e1 : ref A) -∗ *)
  (*   (REL e2 : A) -∗ *)
  (*   REL Xchg e1 e2 : A. *)
  (* Proof. *)
  (*   iIntros "IH1 IH2". *)
  (*   rel_bind_ap e2 "IH2" w "IH2". *)
  (*   rel_bind_ap e1 "IH1" v "IH1". *)
  (*   iDestruct "IH1" as (l ) "(% & Hinv)"; simplify_eq/=. *)
  (*   rewrite -(fill_empty (Xchg #l _)). *)
  (*   iApply refines_atomic_l. *)
  (*   (* iIntros (? j) "Hspec". *) *)
  (*   iInv (logN.@ (l)) as (v) "[Hv1 #Hv]" "Hclose". *)
  (*   iModIntro. *)
  (*   iApply wp_pupd. *)
  (*   wp_xchg. *)
  (*   iModIntro. *)
  (*   (* tp_xchg j. *) *)
  (*   iModIntro. *)
  (*   iMod ("Hclose" with "[Hv1 IH2]"). *)
  (*   { iNext; iExists _; simpl; iFrame. } *)
  (*   iModIntro. iFrame. simpl. *)
  (*   rel_values. *)
  (* Qed. *)
  
End compatibility.
