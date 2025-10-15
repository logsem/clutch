(** Rules for updating the specification program. *)
From Coq Require Export Reals Psatz.
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.common Require Import locations.
From clutch.prob_eff_lang.probblaze Require Import semantics notation.
From clutch.prob_eff_lang.probblaze Require Export spec_ra.

Section rules.
  Context `{!specG_blaze_prob_lang Σ, invGS_gen hasLc Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.
  Implicit Types ℓ : label.

  (* Move the following to exec_lang *)
  Lemma stepN_det_step_ctx K n ρ (e1 e2 : expr) σ1 σ2 :
    prim_step e1 σ1 (e2, σ2) = 1%R →
    stepN n ρ (fill K e1, σ1) = 1%R →
    stepN (S n) ρ (fill K e2, σ2) = 1%R.
  Proof.
    intros.
    rewrite -Nat.add_1_r.
    erewrite (stepN_det_trans n 1); [done|done|].
    rewrite stepN_Sn /=.
    rewrite dret_id_right.
    rewrite -semantics.fill_step_prob; [done| |].
    - eapply (val_stuck _ σ1 (e2, σ2)).
      rewrite H0. lra.
    - eapply (prim_step_uncaught_eff _ σ1 e2 σ2). rewrite H0. lra.
  Qed.
  
  Lemma stepN_PureExec_ctx K (P : Prop) m n ρ (e e' : expr) σ :
    P →
    PureExec P n e e' →
    stepN m ρ (fill K e, σ) = 1 →
    stepN (m + n) ρ (fill K e', σ) = 1.
  Proof.
    move=> HP /(_ HP).
    destruct ρ as [e0 σ0].
    revert e e' m. induction n=> e e' m.
    { rewrite -plus_n_O. by inversion 1. }
    intros (e'' & Hsteps & Hpstep)%nsteps_inv_r Hdet.
    specialize (IHn _ _ m Hsteps Hdet).
    rewrite -plus_n_Sm. simpl in *.
    eapply stepN_det_step_ctx; [by apply pure_step_det|done].
  Qed.
  
  (** Pure reductions *)
  Lemma step_pure E K e e' (P : Prop) n:
    P →
    PureExec P n e e' →
    ⤇ fill K e ⊢ spec_update E (⤇ fill K e').
  Proof.
    iIntros (HP Hex) "HK". rewrite spec_update_unseal.
    iIntros ([??]) "Hs".
    iDestruct (spec_auth_prog_agree with "[$] [$]") as "->".
    iMod (spec_update_prog (fill K e') with "[$][$]") as "[HK Hs]".
    iModIntro. iExists _, n. iFrame. iPureIntro.
    eapply (stepN_PureExec_ctx K P 0); [done|done|].
    rewrite dret_1_1 //.
  Qed.
