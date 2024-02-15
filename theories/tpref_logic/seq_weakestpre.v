From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export na_invariants.
From clutch.tpref_logic Require Export weakestpre spec.

Class seqG (Σ: gFunctors) := {
  seqG_na_invG :: na_invG Σ;
  seqG_name: gname;
}.

Definition seq `{!tprwpG Λ Σ} `{!spec δ Σ} `{!seqG Σ} E (e : expr Λ) (Φ : val Λ → iProp Σ) : iProp Σ :=
  (na_own seqG_name E -∗ WP e {{ v, na_own seqG_name E ∗ Φ v }})%I.

Definition seq_inv `{!invGS_gen HasNoLc Σ} `{!seqG Σ} (N : namespace) (P : iProp Σ) := na_inv seqG_name N P.

Notation "'SEQ' e @ E {{ Φ } }" := (seq E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'SEQ' e @ E {{ Φ } }" := (seq E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'SEQ' e {{ Φ } }" := (seq ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

Notation "'SEQ' e @ E {{ v , Q } }" := (seq E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'SEQ'  e  '/' @  '['  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'SEQ' e {{ v , Q } }" := (seq ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'SEQ'  e  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

Lemma seq_value `{!tprwpG Λ Σ} `{!spec δ Σ} `{!seqG Σ} Φ E (v : val Λ) e `{!IntoVal e v} :
  Φ v ⊢ SEQ e @ E {{ v, Φ v }}.
Proof. iIntros "Hv Hna". iApply rwp_value. iFrame. Qed.

