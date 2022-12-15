From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import na_invariants.
From self.logrel Require Import model.
From self.prob_lang Require Import adequacy primitive_laws lang.

Class prelogrelGpreS Σ := PrelogrelGPreS {
  prelogrelGpreS_preloc :> prelocGpreS Σ;
  prelorelGpreS_na_inv  :> na_invG Σ;
}.

Definition prelogrelΣ : gFunctors := #[prelocΣ; na_invΣ].
Global Instance subG_prelogrelGPreS {Σ} : subG prelogrelΣ Σ → prelogrelGpreS Σ.
Proof. solve_inG. Qed.

Theorem refines_coupling Σ `{prelogrelGpreS Σ}
  (A : ∀ `{prelogrelGS Σ}, lrel Σ) (φ : val → val → Prop) e e' σ σ' n :
  (∀ `{prelogrelGS Σ}, ∀ v v', A v v' -∗ ⌜φ v v'⌝) →
  (∀ `{prelogrelGS Σ}, ⊢ REL e << e' : A) →
  refRcoupl (prim_exec n (e, σ)) (lim_prim_exec (e', σ')) (coupl_rel φ).
Proof.
  intros HA Hlog.
  apply (wp_adequacy Σ).
  intros ?.
  iIntros "#Hctx He'".
  iMod na_alloc as "[%γ Htok]".
  set (Hprelogrel := PrelogrelGS Σ _ _ γ).
  iPoseProof (Hlog _) as "Hlog".
  rewrite refines_eq /refines_def.
  iSpecialize ("Hlog" $! []  with "[$Hctx $He'] Htok").
  iApply (wp_mono with "Hlog").
  iIntros (?) "H /=".
  iDestruct "H" as (?) "([? ? ] & ? & ?) /=".
  iExists _. iFrame. by iApply HA.
Qed.
