From iris.base_logic.lib Require Export fancy_updates invariants.
From clutch.prelude Require Import iris_ext.
From iris.proofmode Require Import base tactics classes.
From clutch.delay_prob_lang Require Import lang urn_subst.
From clutch.elton Require Import weakestpre primitive_laws.

Section rupd.
  Context `{H:!eltonGS Σ}.
  (* Do we need to open invariants? *)
  Definition rupd_def (P:val -> Prop) v : iProp Σ:=
    (∀ σ1, state_interp σ1 -∗
           ⌜∀ f, urns_f_valid (urns σ1) f ->
                ∃ v', urn_subst_val f v = Some v' /\ P v'⌝).
  
  Local Definition rupd_aux : seal (@rupd_def). Proof. by eexists. Qed.
  Definition rupd := rupd_aux.(unseal).
  Lemma rupd_unseal : rupd = rupd_def.
  Proof. rewrite -rupd_aux.(seal_eq) //. Qed.

  
End rupd. 
