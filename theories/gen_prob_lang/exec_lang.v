(* Generic LanguageCtx step lemmas for [gen_prob_lang], ported from
   [prob_lang/exec_lang.v].  Unlike [prob_lang] there is no canonical
   [language] structure (the operational semantics is parametric in a
   distribution signature [S : Sig], giving [gen_lang S]), so the lemmas are
   stated over the [language] [gen_lang S] explicitly.  They are otherwise
   language-generic: each is proven over an arbitrary [LanguageCtx K]. *)

From Stdlib Require Export Reals Psatz.
From clutch.common Require Import language.
From clutch.gen_prob_lang Require Import lang.

Section gen_exec_lang.
Context (Sg : Sig).
Notation Λ := (gen_lang Sg).
Implicit Types e : language.expr Λ.
Implicit Types σ : language.state Λ.

Lemma exec_det_step_ctx (K : language.expr Λ → language.expr Λ) `{!LanguageCtx K}
    n ρ e1 e2 σ1 σ2 :
  language.prim_step e1 σ1 (e2, σ2) = 1%R →
  pexec n ρ (K e1, σ1) = 1%R →
  pexec (S n) ρ (K e2, σ2) = 1%R.
Proof.
  intros. eapply pexec_det_step; [|done].
  rewrite -fill_step_prob //.
  eapply (language.val_stuck _ σ1 (e2, σ2)).
  rewrite H. lra.
Qed.

Lemma exec_PureExec_ctx (K : language.expr Λ → language.expr Λ) `{!LanguageCtx K}
    (P : Prop) m n ρ e e' σ :
  P →
  PureExec P n e e' →
  pexec m ρ (K e, σ) = 1 →
  pexec (m + n) ρ (K e', σ) = 1.
Proof.
  move=> HP /(_ HP).
  destruct ρ as [e0 σ0].
  revert e e' m. induction n=> e e' m.
  { rewrite -plus_n_O. by inversion 1. }
  intros (e'' & Hsteps & Hpstep)%nsteps_inv_r Hdet.
  specialize (IHn _ _ m Hsteps Hdet).
  rewrite -plus_n_Sm.
  eapply exec_det_step_ctx; [done| |done].
  apply Hpstep.
Qed.

Lemma stepN_det_step_ctx (K : language.expr Λ → language.expr Λ) `{!LanguageCtx K}
    n ρ e1 e2 σ1 σ2 :
  language.prim_step e1 σ1 (e2, σ2) = 1%R →
  stepN n ρ (K e1, σ1) = 1%R →
  stepN (S n) ρ (K e2, σ2) = 1%R.
Proof.
  intros.
  rewrite -Nat.add_1_r.
  erewrite (stepN_det_trans n 1); [done|done|].
  rewrite stepN_Sn /=.
  rewrite dret_id_right.
  rewrite -fill_step_prob //.
  eapply (language.val_stuck _ σ1 (e2, σ2)).
  rewrite H. lra.
Qed.

Lemma stepN_PureExec_ctx (K : language.expr Λ → language.expr Λ) `{!LanguageCtx K}
    (P : Prop) m n ρ e e' σ :
  P →
  PureExec P n e e' →
  stepN m ρ (K e, σ) = 1 →
  stepN (m + n) ρ (K e', σ) = 1.
Proof.
  move=> HP /(_ HP).
  destruct ρ as [e0 σ0].
  revert e e' m. induction n=> e e' m.
  { rewrite -plus_n_O. by inversion 1. }
  intros (e'' & Hsteps & Hpstep)%nsteps_inv_r Hdet.
  specialize (IHn _ _ m Hsteps Hdet).
  rewrite -plus_n_Sm.
  eapply stepN_det_step_ctx; [done| |done].
  apply Hpstep.
Qed.

End gen_exec_lang.
