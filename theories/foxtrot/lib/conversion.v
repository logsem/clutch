From clutch.foxtrot Require Import foxtrot.

Definition bool_to_int : val :=
  λ: "b",
    if: "b" = #false then
      #0
    else #1.

Definition int_to_bool : val :=
  λ: "z",
    if: "z" = #0 then #false      
    else #true.

Section specs.
  Context `{!foxtrotGS Σ}.
  
  Lemma wp_bool_to_int (b: bool) E :
    {{{ True }}}
      bool_to_int #b @ E
    {{{ RET #(Z.b2z b); True%I}}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /bool_to_int.
    wp_pures. destruct b; case_bool_decide as Heq; try congruence; wp_pures; by iApply "HΦ".
  Qed.

  Lemma spec_bool_to_int E j K (b : bool) :
    j ⤇ fill K (bool_to_int #b) -∗ pupd E E (j ⤇ fill K (of_val #(Z.b2z b))).
  Proof.
    rewrite /bool_to_int.
    iIntros "HK".
    tp_pures j; [solve_vals_compare_safe|].
    destruct b; case_bool_decide as Heq; try congruence; tp_pures j; by iModIntro.
  Qed.

  Lemma wp_int_to_bool (z : Z) E :    
    {{{ True }}}
      int_to_bool #z @ E
    {{{ RET #(Z_to_bool z); True%I}}}.
  Proof. 
    iIntros (Φ) "_ HΦ".
    rewrite /int_to_bool.
    wp_pures.
    case_bool_decide as Heq; simplify_eq; wp_pures. 
    - by iApply "HΦ".
    - rewrite Z_to_bool_neq_0; [|by intros ->].
      by iApply "HΦ".
  Qed.

  Lemma spec_int_to_bool E j K (z : Z) :    
    j ⤇ fill K (int_to_bool #z) -∗ pupd E E (j ⤇ fill K (of_val #(Z_to_bool z))).
  Proof. 
    rewrite /int_to_bool.
    iIntros "HK".
    tp_pures j; [solve_vals_compare_safe|].
    case_bool_decide as Heq; simplify_eq; tp_pures j. 
    - by iModIntro. 
    - iModIntro. by rewrite Z_to_bool_neq_0; [|by intros ->].
  Qed.
  
End specs.       
