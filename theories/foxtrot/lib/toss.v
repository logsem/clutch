From clutch.foxtrot Require Import foxtrot.

(* The bias here is p/(q+1)*)
Definition toss (p q: nat) (e1 e2 :expr): expr :=
    if: rand #q<#p
    then e1
    else e2.


Section proof.
  Local Set Default Proof Using "Type*".
  Context `{!foxtrotGS Σ}.

  Lemma wp_toss_simplify (p q k x y:nat) e1 e2 e3 e4 j K E Φ:
    k>0->
    y=((q+1)*k-1)->
    x=(k*p)->
    □ (j⤇fill K (e3)-∗
      WP e1 @E {{Φ}}) -∗
    □ (j⤇fill K (e4)-∗
      WP e2 @E {{Φ}}) -∗
    {{{ j⤇fill K (toss p q e3 e4) }}}
      toss x y e1 e2 @E
      {{{ v, RET (v); Φ v}}}.
  Proof.
    iIntros (?->->) "#H1 #H2".
    iIntros (ψ) "!> Hspec Hψ".
    rewrite /toss.
    tp_bind j (rand _)%E.
    wp_apply (wp_couple_toss with "[$]"); [done..|].
    simpl.
    iIntros (?) "Hspec".
    wp_pures.
    case_bool_decide as H0.
    - tp_pures j.
      wp_pures.
      rewrite bool_decide_eq_true_2; last first.
      { apply inj_lt. apply Nat2Z.inj_lt in H0.
        by apply Nat.Div0.div_lt_upper_bound in H0.
      }
      tp_pures j.
      wp_apply (wp_wand with "[Hspec]").
      + by iApply "H1".
      + done. 
    - tp_pures j.
      wp_pures.
      rewrite bool_decide_eq_false_2; last first.
      { apply Z.nlt_ge in H0.
        apply Z.le_ngt.
        apply inj_le. apply Nat2Z.inj_le in H0.
        apply Nat.div_le_lower_bound; lia.
      }
      tp_pures j.
      wp_apply (wp_wand with "[Hspec]").
      + by iApply "H2".
      + done. 
  Qed. 
      
End proof.
