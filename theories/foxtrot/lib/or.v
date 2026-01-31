From clutch.foxtrot Require Import foxtrot nodet.

Definition or (e1 e2:expr) :expr :=
    if: nodet #()= #0
    then e1
    else e2.
        
Section proof.
Local Set Default Proof Using "Type*".
Context `{!foxtrotGS Σ}.

Lemma wp_or e1 e2 Φ:
  {{{ WP e1 {{ Φ }} ∧ WP e2 {{ Φ }} }}}
    or e1 e2
    {{{ (v:val), RET (v); Φ v}}}.
Proof.
  rewrite /or.
  iIntros (ψ) "H Hψ".
  wp_pures.
  wp_apply (wp_nodet); first done.
  iIntros (?) "_".
  wp_pures.
  case_bool_decide; wp_pure.
  - iDestruct "H" as "[H _]".
    by wp_apply (wp_wand with "[$]").
  - iDestruct "H" as "[_ H]".
    by wp_apply (wp_wand with "[$]").
Qed.
End proof.

Section proof'.
  Context `{!foxtrotGS Σ}.
  Lemma tp_or j K E (b:bool) e1 e2:
    j ⤇ fill K (or e1 e2) -∗
    pupd E E
      (if b then j ⤇ fill K e1 else j ⤇ fill K e2
      ).
  Proof.
    rewrite /or.
    iIntros "Hspec".
    tp_bind j (nodet #())%E.
    destruct b.
    - iMod (tp_nodet _ _ _ 0 with "[$]").
      simpl.
      tp_pures j; last done.
      solve_vals_compare_safe.
    - iMod (tp_nodet _ _ _ 1 with "[$]").
      simpl.
      tp_pures j; last done.
      solve_vals_compare_safe.
  Qed. 
End proof'.
