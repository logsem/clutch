From Stdlib Require Export Reals Psatz.

From iris.base_logic.lib Require Export fancy_updates own.
From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl auth.
From iris.prelude Require Import options.

From clutch.prob Require Import couplings distribution markov.
From clutch.base_logic Require Export spec_update.

(** The authoritative spec tracking algebra  *)
Definition specUR (δ : markov) : ucmra := optionUR (exclR (leibnizO (mstate δ))).
Definition authUR_spec (δ : markov) : ucmra := authUR (specUR δ).

Class specPreG (δ : markov) (Σ : gFunctors) := SpecPreG {
  specG_pre_authUR :: inG Σ (authUR_spec δ);
}.
Definition specΣ (δ : markov) : gFunctors := GFunctor (authUR_spec δ).
Global Instance subG_caliperGPreS {δ Σ} : subG (specΣ δ) Σ → specPreG δ Σ.
Proof. solve_inG. Qed.

Class specG (δ : markov) (Σ : gFunctors) := SpecG {
  specG_authUR :: inG Σ (authUR_spec δ);
  specG_gname : gname;
}.

Section spec_auth.
  Context `{specG δ Σ}.
  Implicit Types a : mstate δ.

  Definition specA a : iProp Σ :=
    own specG_gname (● (Excl' a : specUR _)).
  Definition specF a : iProp Σ :=
    own specG_gname (◯ (Excl' a : specUR _)).

  Lemma spec_auth_agree a a' :
    specA a -∗ specF a' -∗ ⌜a = a'⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as
      %[Hexcl ?]%auth_both_valid_discrete.
    rewrite Excl_included in Hexcl.
    by apply leibniz_equiv in Hexcl.
  Qed.

  Lemma spec_auth_update a'' a a' :
    specA a -∗ specF a' ==∗ specA a'' ∗ specF a''.
  Proof.
    iIntros "Ha Hf".
    iDestruct (spec_auth_agree with "Ha Hf") as %->.
    iMod (own_update_2 with "Ha Hf") as "[Ha Hf]".
    { eapply auth_update .
      eapply (@option_local_update _ _ _ (Excl a'' : exclR (leibnizO (mstate δ)))).
      by eapply exclusive_local_update. }
    by iFrame.
  Qed.

End spec_auth.

Lemma spec_auth_alloc {δ Σ} a `{!specPreG δ Σ} :
  ⊢ |==> ∃ (_ : specG δ Σ), specA a ∗ specF a.
Proof.
  iMod (own_alloc ((● (Excl' a : specUR _)) ⋅ (◯ (Excl' a : specUR _))))
    as "(%γspec & Hauth & Hfrag)".
  { by apply auth_both_valid_discrete. }
  set (HspecG := SpecG δ Σ _ γspec).
  iModIntro. iExists HspecG. iFrame.
Qed.

#[global] Instance spec_auth_spec_update {δ Σ} `{specG δ Σ} : spec_updateGS δ Σ := Spec_updateGS specA.
