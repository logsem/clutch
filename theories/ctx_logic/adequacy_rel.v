From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import na_invariants.
From clutch.ctx_logic Require Import weakestpre model adequacy.
From clutch.prob_lang Require Import lang.

Class clutchRGpreS Σ := ClutchRGPreS {
  clutchRGpreS_clutch :: clutchGpreS Σ;
  prelorelGpreS_na_inv  :: na_invG Σ;
}.

Definition clutchRΣ : gFunctors := #[clutchΣ; na_invΣ].
Global Instance subG_clutchRGPreS {Σ} : subG clutchRΣ Σ → clutchRGpreS Σ.
Proof. solve_inG. Qed.

Theorem refines_coupling Σ `{clutchRGpreS Σ}
  (A : ∀ `{clutchRGS Σ}, lrel Σ) (φ : val → val → Prop) e e' σ σ' n :
  (∀ `{clutchRGS Σ}, ∀ v v', A v v' -∗ ⌜φ v v'⌝) →
  (∀ `{clutchRGS Σ}, ⊢ REL e << e' : A) →
  refRcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ.
Proof.
  intros HA Hlog.
  apply (wp_refRcoupl Σ); auto.
  intros ?.
  iIntros "#Hctx He'".
  iMod na_alloc as "[%γ Htok]".
  set (HclutchR := ClutchRGS Σ _ _ γ).
  iPoseProof (Hlog _) as "Hlog".
  rewrite refines_eq /refines_def.
  iSpecialize ("Hlog" $! []  with "[$Hctx $He'] Htok").
  iApply (wp_mono with "Hlog").
  iIntros (?) "H /=".
  iDestruct "H" as (?) "([? ? ] & ? & ?) /=".
  iExists _. iFrame. by iApply HA.
Qed.
