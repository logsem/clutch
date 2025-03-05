From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import na_invariants.
From clutch.micrometer Require Import primitive_laws.
From clutch.micrometer Require Import app_weakestpre model adequacy.
(*  From clutch.prob_lang Require Import lang. *)

(*
Class approxisRGpreS Σ := ApproxisRGPreS {
  approxisRGpreS_approxis :: approxisGpreS Σ;
  prelorelGpreS_na_inv :: na_invG Σ;
}.

Definition approxisRΣ : gFunctors := #[approxisΣ; na_invΣ].
Global Instance subG_approxisRGPreS {Σ} : subG approxisRΣ Σ → approxisRGpreS Σ.
Proof. solve_inG. Qed.

Theorem approximates_coupling Σ `{approxisRGpreS Σ}
  (A : ∀ `{approxisRGS Σ}, lrel Σ) (φ : val → val → Prop) e e' σ σ' ε :
  (0 <= ε)%R →
  (∀ `{approxisRGS Σ}, ∀ v v', A v v' -∗ ⌜φ v v'⌝) →
  (∀ `{approxisRGS Σ}, ↯ ε ⊢ REL e << e' : A) →
  ARcoupl (lim_exec (e, σ)) (lim_exec (e', σ')) φ ε.
Proof.
  intros Hε HA Hlog.
  eapply (wp_adequacy_error_lim Σ); [done|].
  intros H0 ε' Hpos.
  iIntros "He' Herr".
  iMod na_alloc as "[%γ Htok]".
  set (HclutchR := ApproxisRGS Σ _ _ γ).
  iPoseProof (Hlog _) as "Hlog".
  iDestruct ((ec_split_le ε ε') with "Herr") as "[ε ε']" ; [real_solver|].
  iSpecialize ("Hlog" with "ε").
  rewrite refines_eq /refines_def.
  assert (0 < ε' - ε)%R by real_solver.
  iSpecialize ("Hlog" $! [] (ε' - ε)%R with "He' Htok ε' [//]").
  iApply (wp_mono with "Hlog").
  iIntros (?) "H /=".
  iDestruct "H" as (??) "(? & ? & ? & ? & ?) /=".
  iExists _. iFrame. by iApply HA.
Qed.

Corollary refines_coupling Σ `{approxisRGpreS Σ}
  (A : ∀ `{approxisRGS Σ}, lrel Σ) (φ : val → val → Prop) e e' σ σ' :
  (∀ `{approxisRGS Σ}, ∀ v v', A v v' -∗ ⌜φ v v'⌝) →
  (∀ `{approxisRGS Σ}, ⊢ REL e << e' : A) →
  ARcoupl (lim_exec (e, σ)) (lim_exec (e', σ')) φ 0.
Proof.
  intros ? Hlog. intros. eapply approximates_coupling ; eauto. 1: lra.
  iIntros.
  iApply Hlog.
Qed.
*)
