(** Compataibility rules *)
From stdpp Require Import namespaces.
From clutch.prob_lang Require Import notation lang.
From clutch.rel_logic Require Import
  primitive_laws  proofmode spec_rules spec_tactics model rel_tactics rel_rules.

Section compatibility.
  Context `{!clutchRGS Σ}.
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

  Lemma refines_injl e e' τ1 τ2 :
    (REL e << e' : τ1) -∗
    REL InjL e << InjL e' : τ1 + τ2.
  Proof.
    iIntros "IH".
    rel_bind_ap e e' "IH" v v' "Hvv".
    value_case.
    iExists _,_ ; eauto.
  Qed.

  Lemma refines_injr e e' τ1 τ2 :
    (REL e << e' : τ2) -∗
    REL InjR e << InjR e' : τ1 + τ2.
  Proof.
    iIntros "IH".
    rel_bind_ap e e' "IH" v v' "Hvv".
    value_case.
    iExists _,_ ; eauto.
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
    (* TODO: maybe fix tactic? *)
    (* rel_store_l_atomic. *)
    iApply (refines_atomic_l _ _ []); simpl.
    iIntros (K') "Hr".
    iInv (logN .@ (l,l')) as (v v') "[Hv1 [>Hv2 #Hv]]" "Hclose".
    iModIntro.
    wp_store.
    tp_store.
    iMod ("Hclose" with "[Hv1 Hv2 IH2]") as "_".
    { iNext; iExists _, _; simpl; iFrame. }
    iModIntro. iExists _. iFrame.
    value_case.
  Qed.

  Lemma refines_load e e' A :
    (REL e << e' : ref A) -∗
    REL !e << !e' : A.
  Proof.
    iIntros "H".
    rel_bind_ap e e' "H" v v' "H".
    iDestruct "H" as (l l' -> ->) "#H".
    (* TODO: maybe fix tactic? *)
    (* rel_load_l_atomic. *)
    iApply (refines_atomic_l _ _ []); simpl.
    iIntros (K') "Hr".
    iInv (logN .@ (l,l')) as (w w') "[Hw1 [>Hw2 #Hw]]" "Hclose"; simpl.
    iModIntro.
    wp_load.
    tp_load.
    iMod ("Hclose" with "[Hw1 Hw2]") as "_".
    { iNext. iExists w,w'; by iFrame. }
    iModIntro. iExists _. iFrame.
    value_case.
  Qed.

  Lemma refines_rand_tape e1 e1' e2 e2' :
    (REL e1 << e1' : lrel_nat) -∗
    (REL e2 << e2' : lrel_tape) -∗
    REL rand e1 from e2 << rand e1' from e2' : lrel_nat.
  Proof.
    iIntros "IH1 IH2".
    rel_bind_ap e2 e2' "IH2" w w' "IH2".
    rel_bind_ap e1 e1' "IH1" v v' "IH1".
    iDestruct "IH1" as (M) "[-> ->]".
    iDestruct "IH2" as (α α' N -> ->) "#H".
    iApply (refines_atomic_l _ _ []); simpl.
    iIntros (K') "Hr".
    iInv (logN.@ (α, α')) as ">[Hα Hα']" "Hclose".
    iModIntro.
    destruct (decide (N = M)); simplify_eq.
    - iApply (wp_couple_rand_lbl_rand_lbl with "[$Hα $Hα' $Hr Hclose]"); [solve_ndisj|].
      iIntros "!>" (N) "(Hα & Hαs & Hr)".
      iMod ("Hclose" with "[$Hα $Hαs]") as "_".
      iModIntro.
      iExists _. iFrame "Hr".
      rel_values.
    - iApply (wp_couple_rand_lbl_rand_lbl_wrong
               with "[$Hα $Hα' $Hr Hclose]"); [done|solve_ndisj|].
      iIntros "!>" (m) "(Hα & Hα' & Hr)".
      iMod ("Hclose" with "[$Hα $Hα']") as "_".
      iModIntro.
      iExists _. iFrame "Hr".
      rel_values.
  Qed.

  Lemma refines_rand_unit e e' :
    (REL e << e' : lrel_nat) -∗
    REL rand e from #() << rand e' from #() : lrel_nat.
  Proof.
    iIntros "H".
    rel_bind_ap e e' "H" v v' "H".
    iDestruct "H" as (n) "%H".
    destruct H as [-> ->].
    rel_bind_l (rand _ from _)%E.
    rel_bind_r (rand _ from _)%E.
    iApply (refines_couple_rands_lr).
    iIntros (b).
    value_case.
  Qed.

End compatibility.
