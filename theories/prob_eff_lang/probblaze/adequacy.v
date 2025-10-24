From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import na_invariants.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws logic.
From clutch.approxis Require Import app_weakestpre.
From clutch.prob_eff_lang.probblaze Require Import syntax semantics wp_adequacy.

Class probblazeRGpreS Σ := ProbblazeRGPreS {
  probblazeRGpreS_probblaze :: probblazeGpreS Σ;
  prelorelGpreS_na_inv :: na_invG Σ;
}.

Definition probblazeRΣ : gFunctors := #[probblazeΣ; na_invΣ].
Global Instance subG_probblazeRGPreS {Σ} : subG probblazeRΣ Σ → probblazeRGpreS Σ.
Proof. solve_inG. Qed.

Theorem approximates_coupling Σ `{probblazeRGpreS Σ}
  (R : ∀ `{probblazeRGS Σ}, (val -d> val -d> iProp Σ)) (φ : val → val → Prop) e e' σ σ' ε :
  (0 <= ε)%R →
  (∀ `{probblazeRGS Σ}, ∀ v v', R v v' -∗ ⌜φ v v'⌝) →
  (∀ `{probblazeRGS Σ}, ↯ ε ⊢ REL e ≤ e' <|iThyBot|> {{R}}) →
  ARcoupl (lim_exec (e, σ)) (lim_exec (e', σ')) φ ε.
Proof.
  intros Hε HA Hlog.
  eapply (wp_adequacy_error_lim Σ); [done|].
  intros H0 ε' Hpos.
  iIntros "He' Herr".
  iMod na_alloc as "[%γ Htok]".
  set (HclutchR := ProbblazeRGS Σ _ _ γ).
  iPoseProof (Hlog _) as "Hlog".
  iDestruct ((ec_split_le ε ε') with "Herr") as "[ε ε']" ; [real_solver|].
  iSpecialize ("Hlog" with "ε"). simpl.
  rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
  assert (0 < ε' - ε)%R by real_solver.
  iPoseProof (kwp_empty (R HclutchR)) as "Hkwp".
  iSpecialize ("Hlog" $! [] [] (R HclutchR) with "Hkwp"). 
  iSpecialize ("Hlog" $! [] (ε' - ε)%R with "He' Htok ε' [//]").
  iApply (wp_mono with "Hlog").
  iIntros (?) "H /=".
  iDestruct "H" as (??) "(? & ? & ? & ? & ?) /=".
  iExists _. iFrame. by iApply HA.
Qed.

Corollary refines_coupling Σ `{probblazeRGpreS Σ}
  (R : ∀ `{probblazeRGS Σ}, (val -d> val -d> iProp Σ)) (φ : val → val → Prop) e e' σ σ' :
  (∀ `{probblazeRGS Σ}, ∀ v v', R v v' -∗ ⌜φ v v'⌝) →
  (∀ `{probblazeRGS Σ}, ⊢ REL e ≤ e' <|iThyBot|> {{R}}) →
  ARcoupl (lim_exec (e, σ)) (lim_exec (e', σ')) φ 0.
Proof.
  intros ? Hlog. intros. eapply approximates_coupling ; eauto. 1: lra.
  iIntros.
  iApply Hlog.
Qed.
