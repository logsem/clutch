From clutch.foxtrot Require Import foxtrot.

Definition diverge : val :=
  (rec: "f" "_" :=
             "f" #()).        
Section proof.
Local Set Default Proof Using "Type*".
Context `{!foxtrotGS Σ}.

Lemma wp_diverge:
  {{{ True }}}
    diverge #()
    {{{ v, RET (v); False }}}.
Proof.
  iIntros (Φ) "_ _".
  rewrite /diverge.
  iLöb as "IH".
  by wp_pure.
Qed.

End proof.
