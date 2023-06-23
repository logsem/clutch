From Coq Require Export Reals Psatz.

From iris.base_logic.lib Require Export fancy_updates own.
From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl auth.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob Require Export couplings distribution markov.

Set Default Proof Using "Type".

(** A [spec] is a Markov chain together with an interpretation in the logic  *)
Class spec (A B : Type) `{markov A B} (Σ : gFunctors) := Spec {
  spec_interp : A → iProp Σ;
}.
Global Arguments Spec {_ _ _ _ _}.

(** An "update"-modality for deterministic spec steps  *)
Section spec_update.
  Context `{spec A B Σ} `{invGS_gen hlc Σ}.

  Definition spec_update E (P : iProp Σ) : iProp Σ :=
    (∀ a : A, spec_interp a -∗ |={E}=> ∃ (n : nat) (b : A), ⌜stepN n a b = 1⌝ ∗ spec_interp b ∗ P)%I.

  Lemma spec_update_bind E P Q : spec_update E P ∗ (P -∗ spec_update E Q) ⊢ spec_update E Q.
  Proof.
    rewrite /spec_update. iIntros "[P PQ]" (a) "Ha".
    iMod ("P" $! a with "Ha") as (n b Hab) "[Hb P]".
    iSpecialize ("PQ" with "P").
    iMod ("PQ" $! b with "Hb") as (m c Hbc) "[Hc Q]".
    iModIntro. iExists (n + m)%nat, _. iFrame. iPureIntro.
    rewrite stepN_plus. 
    by erewrite stepN_det_steps.
  Qed.

  Lemma spec_update_mono_fupd E P Q : spec_update E P ∗ (P ={E}=∗ Q) ⊢ spec_update E Q.
  Proof.
    iIntros "[HP PQ]". iIntros (a) "Hsrc".
    iMod ("HP" with "Hsrc") as (n b Hstep) "[Hsrc P]".
    iMod ("PQ" with "P"). iFrame. iModIntro.
    iExists n, b. by iFrame.
  Qed.

  Lemma spec_update_mono E P Q : spec_update E P ∗ (P -∗ Q) ⊢ spec_update E Q.
  Proof.
    iIntros "[Hupd HPQ]". iApply (spec_update_mono_fupd with "[$Hupd HPQ]").
    iIntros "P". iModIntro. by iApply "HPQ".
  Qed.

  Lemma fupd_spec_update E P : (|={E}=> spec_update E P) ⊢ spec_update E P.
  Proof.
    iIntros "H". rewrite /spec_update. iIntros (e) "Hsrc".
    iMod "H". by iApply "H".
  Qed.

End spec_update.

(** The authoritative spec tracking algebra  *)
Definition specUR (A : Type) : ucmra := optionUR (exclR (leibnizO A)).
Definition authUR_spec (A : Type) : ucmra := authUR (specUR A).

Class specPreG (A : Type) (Σ : gFunctors) := SpecPreG {
  specG_pre_authUR :> inG Σ (authUR_spec A);
}.
Definition specΣ (A : Type) : gFunctors := GFunctor (authUR_spec A).
Global Instance subG_tprGPreS {A Σ} : subG (specΣ A) Σ → specPreG A Σ.
Proof. solve_inG. Qed.

Class specG (A : Type) (Σ : gFunctors) := SpecG {
  specG_authUR :> inG Σ (authUR_spec A);
  specG_gname : gname;
}.

Section spec_auth.
  Context `{specG A Σ}.

  Definition specA (a : A) : iProp Σ :=
    own specG_gname (● (Excl' a : specUR _)).
  Definition specF (a : A) : iProp Σ :=
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
      eapply (@option_local_update _ _ _ (Excl a'' : exclR (leibnizO A))).
      by eapply exclusive_local_update. }
    by iFrame.
  Qed.

End spec_auth.

Lemma spec_auth_alloc {A} (a : A) `{specPreG A Σ} :
  ⊢ |==> ∃ `{_ : specG A Σ}, specA a ∗ specF a.
Proof.
  iMod (own_alloc ((● (Excl' a : specUR _)) ⋅ (◯ (Excl' a : specUR _))))
    as "(%γspec & Hauth & Hfrag)".
  { by apply auth_both_valid_discrete. }
  set (HspecG := SpecG _ Σ _ γspec).
  iModIntro. iExists HspecG. iFrame.
Qed.

(** A Markov chain gives us an instance *)
#[global]
Instance spec_auth_spec {A B Σ} `{Countable A} `{!markov A B, !specG A Σ} : spec A B Σ :=
 Spec _ specA.
