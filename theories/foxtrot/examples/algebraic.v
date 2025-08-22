(** * Algebraic theory *)
From clutch.foxtrot Require Import foxtrot.
From clutch.foxtrot.lib Require Import toss or.

Set Default Proof Using "Type*".

Section eq1.
  Variable (e : expr).
  Variable (τ: type).
  Variable (p q:nat).
  Lemma eq1 :
      ∅ ⊢ₜ e : τ -> ∅ ⊨ toss p q e e =ctx= e : τ.
  Proof.
    intros H;
    split;
      apply (refines_sound (#[foxtrotRΣ])); iIntros;
      iPoseProof (binary_fundamental.refines_typed _ _ _ H) as "H";
    iIntros; unfold_rel;
      iIntros (K j) "Hspec"; rewrite /toss.
    - wp_apply wp_rand; first done.
      iIntros (??).
      wp_pures.
      case_bool_decide; wp_pures; iApply ("H"$!K j with "[$]").
    - tp_bind j (rand _)%E.
      iMod (pupd_rand with "[$]") as "(%&?&%)".
      simpl.
      tp_pures j.
      case_bool_decide; tp_pures j; by iApply "H".
  Qed. 
End eq1.

Section eq2.
  Variable (e1 e2 : expr).
  Variable (τ: type).
  Variable (p q:nat).
  Variable (Hineq: p<=q+1).
  Lemma eq2 :
    ∅ ⊢ₜ e1 : τ -> ∅ ⊢ₜ e2 : τ ->
              ∅ ⊨ toss p q e1 e2 =ctx= toss (q+1-p)%nat q e2 e1 : τ.
  Proof.
    assert (Bij (λ x, if bool_decide (x<=q)%nat then q-x else x)) as Hbij.
    { split.
      - intros x y.
        case_bool_decide; case_bool_decide; lia.
      - intros y. destruct (decide (y<=q)).
        + exists (q-y). rewrite bool_decide_eq_true_2; lia.
        + exists y. rewrite bool_decide_eq_false_2; lia.
    }
    intros H1 H2;
    split;
      apply (refines_sound (#[foxtrotRΣ])); iIntros;
      iPoseProof (binary_fundamental.refines_typed _ _ _ H1) as "H1";
      iPoseProof (binary_fundamental.refines_typed _ _ _ H2) as "H2";
    iIntros; unfold_rel;
      iIntros (K j) "Hspec"; rewrite /toss; tp_bind j (rand _)%E.
    - unshelve wp_apply (wp_couple_rand_rand _ (λ x, if bool_decide (x<=q)%nat then q-x else x) with "[$]").
      { intros. case_bool_decide; lia. }
      simpl.
      iIntros (?) "[% Hspec]".
      wp_pures.
      rewrite bool_decide_eq_true_2; last lia.
      tp_pures j.
      case_bool_decide; case_bool_decide; try lia; wp_pures; tp_pures j.
      + by iApply "H2". 
      + by iApply "H1".
    - unshelve wp_apply (wp_couple_rand_rand _ (λ x, if bool_decide (x<=q)%nat then q-x else x) with "[$]").
      { intros. case_bool_decide; lia. }
      simpl.
      iIntros (?) "[% Hspec]".
      wp_pures.
      rewrite bool_decide_eq_true_2; last lia.
      tp_pures j.
      case_bool_decide; case_bool_decide; try lia; wp_pures; tp_pures j.
      + by iApply "H1". 
      + by iApply "H2".
  Qed. 
End eq2.

Section eq3.
End eq3.

Section eq4.
End eq4.

Section eq5.
End eq5.

Section eq6.
End eq6.

Section eq7.
End eq7.

Section eq8.
End eq8.
