From Coq Require Export Reals Psatz.

From iris.base_logic.lib Require Export fancy_updates own.
From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl auth.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob Require Export couplings distribution markov.

Set Default Proof Using "Type".

(** A [spec] is a Markov chain together with an interpretation in the logic  *)
Class spec (δ : markov) (Σ : gFunctors) := Spec {
  spec_interp : mstate δ → iProp Σ;
}.
Global Arguments Spec {_ _}.

Canonical Structure mstateO δ := leibnizO (mstate δ).

(** An "update"-modality for deterministic spec steps  *)
Section spec_update.
  Context `{spec δ Σ} `{invGS_gen hlc Σ}.
  Implicit Types a : mstate δ.

  Definition spec_updateN (n : nat) (E : coPset) (P : iProp Σ) : iProp Σ :=
    (∀ a, spec_interp a -∗ |={E}=> ∃ a', ⌜stepN n a a' = 1⌝ ∗ spec_interp a' ∗ P)%I.

  Definition spec_update (E : coPset) (P : iProp Σ) : iProp Σ :=
    (∀ a, spec_interp a -∗ |={E}=> ∃ a' n, ⌜stepN n a a' = 1⌝ ∗ spec_interp a' ∗ P)%I.

  Lemma spec_updateN_implies_spec_update n E P:
    spec_updateN n E P -∗ spec_update E P.
  Proof.
    rewrite /spec_updateN/spec_update.
    iIntros "H % Ha".
    iMod ("H" with "[$]") as "(%&%&?&?)". iModIntro.
    iExists _, _. iFrame. by iPureIntro.
  Qed.

  Lemma spec_updateN_ret E P :
    P ⊢ spec_updateN 0 E P.
  Proof.
    iIntros "HP" (a) "Ha !#".
    iExists _.
    rewrite stepN_O dret_1_1 //.
    by iFrame.
  Qed.

  Lemma spec_update_ret E P :
    P ⊢ spec_update E P.
  Proof.
    iIntros "HP" (a) "Ha !#".
    iExists a, O.
    rewrite stepN_O dret_1_1 //.
    by iFrame.
  Qed.

  Lemma spec_updateN_bind n m E P Q :
    spec_updateN n E P ∗ (P -∗ spec_updateN m E Q) ⊢ spec_updateN (n + m) E Q.
  Proof.
    rewrite /spec_updateN. iIntros "[P PQ]" (a) "Ha".
    iMod ("P" $! a with "Ha") as (b Hab) "[Hb P]".
    iSpecialize ("PQ" with "P").
    iMod ("PQ" $! b with "Hb") as (c Hbc) "[Hc Q]".
    iModIntro. iExists _.
    erewrite stepN_det_trans; [|done|done].
    by iFrame.
  Qed.

  Lemma spec_update_bind E P Q :
    spec_update E P ∗ (P -∗ spec_update E Q) ⊢ spec_update E Q.
  Proof.
    rewrite /spec_update. iIntros "[P PQ]" (a) "Ha".
    iMod ("P" $! a with "Ha") as (b n Hab) "[Hb P]".
    iSpecialize ("PQ" with "P").
    iMod ("PQ" $! b with "Hb") as (c m Hbc) "[Hc Q]".
    iModIntro. iExists _, (n + m)%nat. iFrame.
    by erewrite stepN_det_trans.
  Qed.

  Lemma spec_updateN_mono_fupd n E P Q :
    spec_updateN n E P ∗ (P ={E}=∗ Q) ⊢ spec_updateN n E Q.
  Proof.
    iIntros "[HP PQ]". iIntros (a) "Hsrc".
    iMod ("HP" with "Hsrc") as (b Hstep) "[Hsrc P]".
    iMod ("PQ" with "P"). iFrame. iModIntro.
    iExists b. by iFrame.
  Qed.

  Lemma spec_update_mono_fupd E P Q :
    spec_update E P ∗ (P ={E}=∗ Q) ⊢ spec_update E Q.
  Proof.
    rewrite /spec_update.
    iIntros "[HP PQ]". iIntros (a) "Hsrc".
    iMod ("HP" with "Hsrc") as (b n Hstep) "[Hsrc P]".
    iMod ("PQ" with "P"). iFrame. iModIntro.
    iExists b, _. by iFrame.
  Qed.

  Lemma spec_updateN_mono n E P Q :
    spec_updateN n E P ∗ (P -∗ Q) ⊢ spec_updateN n E Q.
  Proof.
    iIntros "[Hupd HPQ]". iApply (spec_updateN_mono_fupd with "[$Hupd HPQ]").
    iIntros "P". iModIntro. by iApply "HPQ".
  Qed.

  Lemma spec_update_mono E P Q :
    spec_update E P ∗ (P -∗ Q) ⊢ spec_update E Q.
  Proof.
    rewrite /spec_update.
    iIntros "[Hupd HPQ]". iApply (spec_update_mono_fupd with "[$Hupd HPQ]").
    iIntros "P". iModIntro. by iApply "HPQ".
  Qed.

  Lemma fupd_spec_updateN n E P :
    (|={E}=> spec_updateN n E P) ⊢ spec_updateN n E P.
  Proof.
    iIntros "H". rewrite /spec_updateN. iIntros (e) "Hsrc".
    iMod "H". by iApply "H".
  Qed.

  Lemma fupd_spec_update E P :
    (|={E}=> spec_update E P) ⊢ spec_update E P.
  Proof.
    rewrite /spec_update.
    iIntros "H". rewrite /spec_updateN. iIntros (e) "Hsrc".
    iMod "H". by iApply "H".
  Qed.

  Global Instance from_modal_spec_update P E :
    FromModal True modality_id (spec_update E P) (spec_update E P) P.
  Proof. iIntros (_) "HP /=". by iApply spec_update_ret. Qed.

  Global Instance elim_modal_spec_update P Q E :
    ElimModal True false false (spec_update E P) P (spec_update E Q) (spec_update E Q).
  Proof. iIntros (?) "[HP Hcnt]". iApply (spec_update_bind with "[$]"). Qed.

  Global Instance from_modal_spec_updateN P E :
    FromModal True modality_id (spec_update E P) (spec_updateN 0 E P) P.
  Proof. iIntros (_) "HP /=". by iApply spec_updateN_ret. Qed.

  Global Instance elim_modal_spec_updateN n m P Q E :
    ElimModal True false false (spec_updateN n E P) P (spec_updateN (n + m) E Q) (spec_updateN m E Q).
  Proof. iIntros (?) "[HP Hcnt]". iApply (spec_updateN_bind with "[$]"). Qed.

End spec_update.

(** The authoritative spec tracking algebra  *)
Definition specUR (δ : markov) : ucmra := optionUR (exclR (leibnizO (mstate δ))).
Definition authUR_spec (δ : markov) : ucmra := authUR (specUR δ).

Class specPreG (δ : markov) (Σ : gFunctors) := SpecPreG {
  specG_pre_authUR :: inG Σ (authUR_spec δ);
}.
Definition specΣ (δ : markov) : gFunctors := GFunctor (authUR_spec δ).
Global Instance subG_tprGPreS {δ Σ} : subG (specΣ δ) Σ → specPreG δ Σ.
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

(** A Markov chain gives us an instance *)
Definition spec_auth_spec {δ Σ} `{specG δ Σ} : spec δ Σ := Spec specA.