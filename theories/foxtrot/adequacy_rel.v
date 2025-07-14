From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import na_invariants.
From Coquelicot Require Import Rbar Lub.
From clutch.foxtrot Require Import primitive_laws.
From clutch.foxtrot Require Import weakestpre model adequacy.
From clutch.con_prob_lang Require Import lang lub_termination.

Class foxtrotRGpreS Σ := FoxtrotRGPreS {
  foxtrotRGpreS_foxtrot :: foxtrotGpreS Σ;
  prelorelGpreS_na_inv :: na_invG Σ;
}.

Definition foxtrotRΣ : gFunctors := #[foxtrotΣ; na_invΣ].
Global Instance subG_foxtrotRGPreS {Σ} : subG foxtrotRΣ Σ → foxtrotRGpreS Σ.
Proof. solve_inG. Qed.

Theorem foxtrot_rel_adequacy Σ `{foxtrotRGpreS Σ}
  (A : ∀ `{foxtrotRGS Σ}, lrel Σ) (ϕ : val → val → Prop) e e' σ σ' ε :
  (0 <= ε)%R →
  (∀ `{foxtrotRGS Σ}, ∀ v v', A v v' -∗ ⌜ϕ v v'⌝) →
  (∀ `{foxtrotRGS Σ}, ↯ ε ⊢ REL e << e' : A) →
  ∀ sch_int_σ `(Countable sch_int_σ) sch ζ `{!TapeOblivious sch_int_σ sch} ε' n,
  (ε'>0)%R ->
  ∃ `(Countable sch_int_σ') sch' ζ' `(!TapeOblivious sch_int_σ' sch'),
     ARcoupl (sch_exec sch n (ζ, ([e], σ))) (sch_lim_exec sch' (ζ', ([e'], σ'))) ϕ (ε + ε').
Proof.
  intros Hε HA Hlog ?????????.
  eapply (foxtrot_adequacy_intermediate Σ); try done. 
  intros H'.
  iIntros "Herr Hspec".
  iMod na_alloc as "[%γ Htok]".
  set (HclutchR := FoxtrotRGS Σ _ _ γ).
  iPoseProof (Hlog _) as "Hlog".
  (* iDestruct ((ec_split_le ε ε') with "Herr") as "[ε ε']" ; [real_solver|]. *)
  iSpecialize ("Hlog" with "Herr").
  rewrite refines_eq /refines_def.
  rewrite -(fill_empty e').
  iDestruct ("Hlog" with "[$][$]") as "Hlog".
  iApply (wp_mono with "Hlog").
  iIntros (?) "(% &?&?&?) /=".
  iFrame.
  by iApply HA.
Qed.

Theorem foxtrot_rel_adequacy' Σ `{foxtrotRGpreS Σ}
  (A : ∀ `{foxtrotRGS Σ}, lrel Σ) (ϕ : val → val → Prop) e e' σ σ' ε :
  (0 <= ε)%R →
  (∀ `{foxtrotRGS Σ}, ∀ v v', A v v' -∗ ⌜ϕ v v'⌝) →
  (∀ `{foxtrotRGS Σ}, ↯ ε ⊢ REL e << e' : A) →
  Rbar_le (lub_termination_prob e σ) (Rbar_plus (lub_termination_prob e' σ') ε).
Proof.
  intros.
  eapply ARcoupl_lub.
  intros.
  by eapply foxtrot_rel_adequacy.
Qed. 
