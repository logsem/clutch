From iris.proofmode Require Import base.
From iris.base_logic.lib Require Import  na_invariants.
From iris.algebra Require Export agree excl auth frac excl_auth.
From iris.algebra.lib Require Export dfrac_agree.
From clutch.prob_eff_lang.probblaze Require Import logic.

Ltac label_not_in_singleton Hdl := 
  apply NoDup_cons_1_1;
  eapply submseteq_NoDup; last exact Hdl;
  solve_submseteq. 

Section lemmas.
  Context `{!probblazeRGS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.

  Definition token γ := own γ (Excl ()).

  Lemma send_upd P n γtok γfrac :
    P ∗
    invariants.inv n (token γtok ∨ own γfrac DfracDiscarded) ⊢
    (|={⊤,⊤ ∖ ↑n}=>
       (own γfrac DfracDiscarded ={⊤ ∖ ↑n,⊤}=∗ token γtok ∗ P)
        ∨ (|={⊤ ∖ ↑n,⊤}=> own γfrac DfracDiscarded)).
  Proof. 
    iIntros "(HP&#Hinv)".
    iMod (inv_acc with "Hinv") as "([>Htok | >#Hfrac] & Hclose)"; try done.
    - iModIntro. iLeft.
      iIntros. iFrame. iMod ("Hclose" with "[$]") as "_". 
      by iModIntro. 
    - iModIntro. iRight. iFrame "#".
      iApply "Hclose". iNext.
      by iRight.
  Qed. 

End lemmas.

