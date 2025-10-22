From clutch.eris Require Export eris error_rules.

Definition loop:val:=
  rec: "loop" "x" := "loop" "x".
 
Section proof.
Local Set Default Proof Using "Type*".
Context `{!erisGS Σ}.

  Lemma loop_lemma E (v:val) Φ:
    ⊢ WP (loop v) @ E {{Φ}}.
  Proof.
    iLöb as "IH".
    rewrite /loop.
    by wp_pures.
  Qed.

  Definition flip_loop : expr :=
    if: rand #1 = #1 then #() else loop #().

  Lemma twp_e'_two E:
    ⊢ ↯ (1/2) -∗ WP flip_loop @ E [{ _, ⌜True⌝ }].
  Proof.
    iIntros "Herr".
    rewrite /flip_loop.
    set (ε2 := λ n : fin (S 1), if (fin_to_nat n =? 1) then 0%R else 1%R).
    wp_apply (twp_couple_rand_adv_comp1 _ _ _ _ ε2 with "[$]").
    { intros; rewrite /ε2; case_match; lra. }
    { rewrite SeriesC_finite_foldr /ε2. simpl. lra. }
    iIntros (n) "Herr".
    wp_pures.
    case_bool_decide; wp_pures; first done.
    rewrite /ε2.
    iExFalso.
    iApply ec_contradict; last done.
    assert (fin_to_nat n ≠ 1).
    { intros H1. rewrite H1 in H. done.  }
    assert ((if n =? 1 then 0 else 1) = 1)%R.
    { case_match; [ | done].
      exfalso. apply H0. apply Nat.eqb_eq in H1. done.
    }
    rewrite H1.
    done.
  Qed.

End proof.
