From coneris.coneris Require Import coneris.

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
  Context `{!conerisGS Σ}.
  
  Lemma wp_bool_to_int (b: bool) E :
    {{{ True }}}
      bool_to_int #b @ E
    {{{ RET #(Z.b2z b); True%I}}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /bool_to_int.
    wp_pures. destruct b; case_bool_decide as Heq; try congruence; wp_pures; by iApply "HΦ".
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
  
End specs.       
