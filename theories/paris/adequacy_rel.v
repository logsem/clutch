From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import na_invariants.
From clutch.paris Require Import primitive_laws.
From clutch.paris Require Import app_weakestpre model adequacy.
From clutch.prob_lang Require Import lang.

Class parisRGpreS Σ := ParisRGPreS {
  parisRGpreS_paris :: parisGpreS Σ;
  prelorelGpreS_na_inv :: na_invG Σ;
}.

Definition parisRΣ : gFunctors := #[parisΣ; na_invΣ].
Global Instance subG_parisRGPreS {Σ} : subG parisRΣ Σ → parisRGpreS Σ.
Proof. solve_inG. Qed.

Theorem refines_coupling Σ `{parisRGpreS Σ}
  (A : ∀ `{parisRGS Σ}, lrel Σ) (φ : val → val → Prop) e e' σ σ' :
  (∀ `{parisRGS Σ}, ∀ v v', A v v' -∗ ⌜φ v v'⌝) →
  (∀ `{parisRGS Σ}, ⊢ REL e << e' : A) →
  ARcoupl (lim_exec (e, σ)) (lim_exec (e', σ')) φ 0%NNR.
Proof.
  intros HA Hlog.
  eapply (wp_adequacy_error_lim Σ).
  intros H0 ε Hpos.
  iIntros "He' Herr".
  iMod na_alloc as "[%γ Htok]".
  set (HclutchR := ParisRGS Σ _ _ γ).
  iPoseProof (Hlog _) as "Hlog".
  rewrite refines_eq /refines_def.
  iSpecialize ("Hlog" $! [] ε with "He' Htok Herr [//]").
  iApply (wp_mono with "Hlog").
  iIntros (?) "H /=".
  iDestruct "H" as (??) "(? & ? & ? & ? & ?) /=".
  iExists _. iFrame. by iApply HA.
Qed.
