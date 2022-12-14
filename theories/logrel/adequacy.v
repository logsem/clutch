From iris.proofmode Require Import proofmode.
From self.logrel Require Import model.
From self.prob_lang Require Import adequacy primitive_laws lang.

Theorem refines_coupling Σ `{prelocGpreS Σ}
  (A : ∀ `{prelocGS Σ}, lrel Σ) (φ : val → val → Prop) e e' σ σ' n :
  (∀ `{prelocGS Σ}, ∀ v v', A v v' -∗ ⌜φ v v'⌝) →
  (∀ `{prelocGS Σ}, ⊢ REL e << e' : A) →
  refRcoupl (prim_exec n (e, σ)) (lim_prim_exec (e', σ')) (coupl_rel φ).
Proof.
  intros HA Hlog.
  apply (wp_adequacy Σ).
  intros ?.
  iIntros "#Hctx He'".
  iPoseProof (Hlog _) as "Hlog".
  rewrite refines_eq /refines_def.
  iMod ("Hlog" $! []  with "[$Hctx $He']") as "Hwp".
  iApply (wp_mono with "Hwp").
  iIntros (?) "H /=".
  iDestruct "H" as (?) "[[? ?] ?] /=".
  iExists _. iFrame. by iApply HA.
Qed.
