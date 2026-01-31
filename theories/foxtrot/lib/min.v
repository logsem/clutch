From clutch.foxtrot Require Import foxtrot.

Definition min_prog : val :=
  λ: "x" "y",
    if: "x" < "y" then "x" else "y".

Section specs.
  Context `{!foxtrotGS Σ}.
  
  Lemma wp_min_prog (x y:Z) E :
    {{{ True }}}
      min_prog #x #y @ E
    {{{ (z:Z), RET #z; ⌜(z= x `min` y)%Z⌝}}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /min_prog.
    wp_pures.
    case_bool_decide; wp_pures; iApply "HΦ"; iModIntro; iPureIntro.
    - rewrite Z.min_l; lia.
    - rewrite Z.min_r; lia.
  Qed. 

  Lemma spec_min_prog E j K (x y : Z) :
    j ⤇ fill K (min_prog #x #y) -∗ pupd E E (j ⤇ fill K (# (x `min` y)%Z)).
  Proof.
    rewrite /min_prog.
    iIntros "HK".
    tp_pures j.
    case_bool_decide; tp_pures j.
    - rewrite Z.min_l; [done|lia].
    - rewrite Z.min_r; [done|lia].
  Qed.
  
End specs.       
