From clutch.prob_eff_lang.probblaze Require Import logic notation.
From iris.proofmode Require Import base proofmode classes.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import valgroup.

Import valgroup_tactics.

Section proof.
Context {s t : label}.
Context `{probblazeRGS Σ}.
Context {V1 H1 V2 H2 : (val → val → iProp Σ)}.


Definition handler s h r f: expr :=
  handle: f with
  | effect s "x", "k" as multi => h
  | return "y" => r
end. 

Program Definition T : iThy Σ := (λ e1 e2, λne Q,
                                    ∃ v1 v2 : val, V1 v1 v2 ∗ 
                                             (⌜ e1 = do: s v1 ⌝%E ∗
                                             ⌜ e2 = do: s v2 ⌝%E ∗
                                             □ (∀ w1 w2, H1 w1 w2 -∗ Q w1 w2)))%I.
Next Obligation. solve_proper. Qed.

Program Definition S : iThy Σ :=  (λ e1 e2, λne Q,
                                     ∃ v1 v2 : val, V2 v1 v2 ∗ 
                                  (⌜ e1 = do: t v1 ⌝%E ∗
                                  ⌜ e2 = do: t v2 ⌝%E ∗
                                  □ (∀ w1 w2, H2 w1 w2 -∗ Q w1 w2)))%I.
Next Obligation. solve_proper. Qed.


(* Proving that two handlers can commute if they have disjoint effects *)
(* Only works for a trivial return branch -- imagine h1, h2, r1, r2 to be different constants, then this would not commute *)
Lemma commuting_handlers (h1 h2 r1 r2 f1 f2 : expr) L R: 
  s ≠ t →
  □ (∀ v1 v2 k1 k2, V1 v1 v2 -∗ BREL val_subst "k" (KontV k1) (val_subst "x" v1 h1) ≤ val_subst "k" (KontV k2) (val_subst "x" v2 h1) <| L |> {{ R }}) -∗
  □ (∀ v1 v2 k1 k2, V2 v1 v2 -∗ BREL val_subst "k" (KontV k1) (val_subst "x" v1 h2) ≤ val_subst "k" (KontV k2) (val_subst "x" v2 h2) <| L |> {{ R }}) -∗
  BREL f1 ≤ f2 <| ([s;t], [s;t], iThySum T S) :: L |> {{ R }} -∗
       BREL handler s h1 "y" (handler t h2 "y" f1) ≤ handler t h2 "y" (handler s h1 "y" f2) <| ([s;t], [s;t], ⊥) :: L |> {{ R }}.
Proof.
  iIntros (Hneq) "#Hh1 #Hh2 Hff". unfold handler.
  iApply (brel_exhaustion _ _ [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _] [HandleCtx _ _ _ _ _; HandleCtx _ _ _ _ _]with "Hff").
  1,2 : set_solver.
  iSplit; iModIntro.
  - iIntros (??) "HR". by brel_pures. 
  - iIntros (???????) "[(%&%&HV&->&->&#HQ) | (%&%&HV&->&->&#HQ)] #Hkont". 
    + simpl. brel_pures.
      * eapply @neutral_ectx in H0; last constructor. simpl. by apply not_elem_of_cons.  
      * apply neutral_ectx; constructor.
      * simpl. iApply brel_learn. iIntros "%Hdistinct _".
        iApply (brel_introduction_mono L); first (iApply to_iThy_le_intro'; by apply submseteq_cons).
        iApply (brel_bind [] [HandleCtx _ _ _ _ _]); [ |(iApply to_iThy_le_refl)| ].
        -- iApply traversable_ectx_labels; last done; try set_solver.
        -- iDestruct ("Hh1" with "HV") as "Hh". 
           iApply (brel_wand with "Hh"). 
           iIntros (??) "!# H1". simpl.
           by brel_pures.
    + simpl. brel_pures.
      * apply neutral_ectx; repeat constructor.
      * eapply @neutral_ectx in H3; last (apply list_elem_of_further; constructor). simpl. by apply not_elem_of_cons.
      * iApply brel_learn. iIntros "%Hdistinct _".
        iApply (brel_introduction_mono L); first (iApply to_iThy_le_intro'; by apply submseteq_cons).
        iApply (brel_bind [HandleCtx _ _ _ _ _] []); [ |(iApply to_iThy_le_refl)| ].
        -- iApply traversable_ectx_labels; last done; try set_solver.
        -- iDestruct ("Hh2" with "HV") as "Hh". 
           iApply (brel_wand with "Hh"). 
           iIntros (??) "!# H1". simpl.
           by brel_pures.
Qed. 


End proof.
