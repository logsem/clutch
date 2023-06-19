From iris.proofmode Require Import base proofmode.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Import own.
From iris.prelude Require Import options.

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

  Lemma specA_frag_agree a a' :
    specA a -∗ specF a' -∗ ⌜a = a'⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as
      %[Hexcl ?]%auth_both_valid_discrete.
    rewrite Excl_included in Hexcl.
    by apply leibniz_equiv in Hexcl.
  Qed.

  Lemma spec_update a'' a a' :
    specA a -∗ specF a' ==∗ specA a'' ∗ specF a''.
  Proof.
    iIntros "Ha Hf".
    iDestruct (specA_frag_agree with "Ha Hf") as %->.
    iMod (own_update_2 with "Ha Hf") as "[Ha Hf]".
    { eapply auth_update .
      eapply (@option_local_update _ _ _ (Excl a'' : exclR (leibnizO A))).
      by eapply exclusive_local_update. }
    by iFrame.
  Qed.

End spec_auth.

Lemma spec_alloc {A} (a : A) `{specPreG A Σ} :
  ⊢ |==> ∃ `{_ : specG A Σ}, specA a ∗ specF a.
Proof.
  iMod (own_alloc ((● (Excl' a : specUR _)) ⋅ (◯ (Excl' a : specUR _))))
    as "(%γspec & Hauth & Hfrag)".
  { by apply auth_both_valid_discrete. }
  set (HspecG := SpecG _ Σ _ γspec).
  iModIntro. iExists HspecG. iFrame.
Qed.
