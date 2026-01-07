From clutch.eris Require Export eris.

Section test.
  Context `{!erisGS Σ}.

  Definition φ v :iProp Σ:= (⌜v = #true⌝)%I.

  Definition loop:val:=
    rec: "loop" "x" := "loop" "x".

  Definition e' (n:expr) : expr :=
    let: "k" := rand #1 in
    if: n+"k" ≤ #2 then
      #true
    else
      if: n+"k"=#3
      then #false
      else loop #().

  Definition e :expr :=
    let: "n" := rand #3 in
    if: "n"≤#1
    then #true
    else e' "n".

  Lemma loop_lemma E (v:val) Φ:
    ⊢ WP (loop v) @ E {{Φ}}.
  Proof.
    iLöb as "IH".
    rewrite /loop.
    by wp_pures.
  Qed.

  Lemma twp_e'_two E:
    ⊢ ↯ (1/2) -∗ WP (e' #2) @ E [{ φ }].
  Proof.
    iIntros "Herr".
    rewrite /e'.
    wp_apply (twp_rand_err_int _ _ 1).
    iSplitL.
    - iApply (ec_eq with "[$]").
      simpl. lra.
    - iIntros (x) "[% %]".
      wp_pures.
      case_bool_decide; last by lia.
      by wp_pures.
  Qed.

  Lemma wp_e'_two E:
    ⊢ ↯ (1/2) -∗ WP (e' #2) @ E {{ φ }}.
  Proof.
    iIntros "Herr".
    iApply tgl_wp_pgl_wp'.
    by iApply twp_e'_two.
  Qed.

  Lemma twp_e'_three E:
    ⊢ ↯ (1%R) -∗ WP (e' #3) @ E [{ φ }].
  Proof.
    iIntros "Herr".
    iExFalso.
    iApply ec_contradict; last done.
    simpl. lra.
  Qed.

  Lemma wp_e'_three E:
    ⊢ ↯ (1/2) -∗ WP (e' #3) @ E {{ φ }}.
  Proof.
    iIntros "Herr".
    rewrite /e'.
    wp_apply (wp_rand_err_nat _ _ 0).
    iSplitL.
    - iApply (ec_eq with "[$]").
      simpl. lra.
    - iIntros (x) "% !>".      
      wp_pures.
      assert (x=1) as -> by lia.
      case_bool_decide; first lia.
      wp_pures.
      wp_apply loop_lemma.
  Qed.

  Lemma twp_e E:
    ⊢ ↯ (3 / 8) -∗
    WP e @ E [{φ}].
  Proof.
    iIntros "Herr".
    rewrite /e.
    set (ε2 := λ n : nat, if (n <? 2) then 0%R else
                      if (n =? 2) then (1/2)%R else 1%R).
    wp_apply (twp_rand_exp_nat _ _ _ ε2 with "[$]").
    { intros; rewrite /ε2.
      case_match; [lra |].
      case_match; lra.
    }
    { rewrite SeriesC_nat_bounded_to_foldr /ε2. simpl. lra. }
    iIntros (n) "[%Hn Herr]".
    wp_pures.
    case_bool_decide; wp_pures; first done.
    assert (n = 2 \/ n = 3) as [-> | ->] by lia.
    - by wp_apply twp_e'_two.
    - by wp_apply twp_e'_three.
  Qed.

  Lemma wp_e E:
    ⊢ ↯ ((1/4)%R) -∗
       WP e @ E {{φ}}.
  Proof.
    iIntros "Herr".
    rewrite /e.
    set (ε2 := λ n : nat, if (n <? 2) then 0%R else (1/2)%R).
    wp_apply (wp_rand_exp_nat _ _ _ ε2 with "[$]").
        {
          intros; rewrite /ε2.
          case_match; [lra |].
          real_solver.
        }
        { rewrite SeriesC_nat_bounded_to_foldr /ε2. simpl. lra. }
        iIntros (n) "[%Hn Herr]".
        wp_pures.
        case_bool_decide; wp_pures; first done.
        assert (n = 2 \/ n = 3) as [-> | ->] by lia.
    - rewrite /ε2/=.
      by wp_apply wp_e'_two.
    - rewrite /ε2/=.
      by wp_apply wp_e'_three.
  Qed.

  Definition e'' :expr :=
    let: "l" := ref #0 in
    "l" <- (!"l" + rand #3);;
    "l" <- (!"l" + rand #3);;
    !"l".

  Lemma wp_e'' :
    ↯ (1 / 16) ⊢ WP e'' {{ v, ∃ (n : nat), ⌜v = #n⌝ ∗ ⌜n > 0⌝ }}.
  Proof.
    iIntros "Herr". rewrite /e''.
    wp_alloc l as "Hl".
    wp_pures.
    wp_bind (rand #3)%E.
    set (ε1 := λ n : fin 4, if fin_to_nat n =? 0 then (1/4)%R else 0%R).
    wp_apply (wp_rand_exp_fin1 _ _ _ _ ε1 with "Herr").
    { intros; rewrite /ε1/=.
      real_solver.
    }
    { rewrite SeriesC_finite_foldr.
      rewrite /ε1 /=.
      lra. }
    iIntros (n) "Herr".
    wp_load. wp_pures. wp_store.
    inv_fin n; last first.
    - intros n.
      wp_apply wp_rand; [done|].
      iIntros (m) "_".
      wp_load. wp_store. wp_load.
      iModIntro. iExists _.
      iSplit; [iPureIntro|].
      { do 2 f_equal. rewrite -Nat2Z.inj_add //. }
      iPureIntro. lia.
    - replace (ε1 0%fin) with (1/4)%R; last first.
      { rewrite /ε1 /=. done. }
      set (ε2 := λ n : fin 4, if fin_to_nat n =? 0 then 1%R else 0%R).
      wp_apply (wp_rand_exp_fin1 _ _ _ _ ε2 with "Herr").
      { intros. rewrite /ε2. real_solver. }
      { rewrite SeriesC_finite_foldr.
        rewrite /ε2 /=. lra. }
      iIntros (n) "Herr".
      inv_fin n.
      { by iDestruct (ec_contradict with "Herr") as %[]. }
      intros n => /=.
      wp_load. wp_store. wp_load.
      iModIntro. iExists _.
      iSplit; [done|].
      iPureIntro. lia.
  Qed.

End test.

Local Open Scope R.

Section foo.
Context `{!erisGS Σ}.

Definition foo N (m : nat) : expr :=
  let: "n" := rand #N in
  if: "n" = #m then #false else #true.


Lemma wp_foo (N : nat) m E :
  {{{ ↯ (/ (N + 1)) }}}
  (foo N m) @ E
  {{{ v, RET v; ⌜ v = #true ⌝ }}}.
Proof.
  iIntros (Φ) "Herr HΦ".
  rewrite /foo/=.
  wp_bind (rand _)%E.
  wp_apply (wp_rand_err_nat _ _ m).
  iFrame.
  iIntros (?) "!> [% %]".
  wp_pures.
  rewrite bool_decide_eq_false_2; auto; [ | intro; simplify_eq ].
  wp_if_false.
  by iApply "HΦ".
Qed.


Definition bar N : expr :=
  let: "m" := rand #N in
  let: "n" := rand #N in
  if: "n" = "m" then #false else #true.


Definition wp_bar (N : nat) E :
  {{{ ↯ (/ (N+1)) }}}
  (bar N) @ E
  {{{ v, RET v; ⌜ v = #true ⌝ }}}.
Proof.
  iIntros (Φ) "Herr HΦ".
  rewrite /bar/=.
  wp_bind (rand _)%E.
  wp_apply (wp_rand); auto.
  iIntros "%m ?".
  wp_pures.
  wp_apply (wp_rand_err_nat _ _ m).
  iFrame.
  iIntros (?) "!> [% %]".
  wp_pures.
  rewrite bool_decide_eq_false_2; auto; [ | intro; simplify_eq ].
  wp_if_false.
  by iApply "HΦ".
Qed.


Definition baz : expr :=
  rec: "baz" "x" :=
    let: "n" := rand #2 in
    (if: "n" < #2
      then "n"
      else "baz" #() ).


Lemma wp_baz E :
  ↯ (1/2) -∗ WP baz #() @ E {{ v, ⌜v = #0⌝ }}.
Proof.
  iIntros "Herr".
  wp_pure.
  iLöb as "IH".
  wp_pures.
  set f:= (λ n : fin 3,
              if bool_decide (n = 0%fin)
                then 0%R
                else if bool_decide (n = 1%fin) then 1%R
                                            else (1/2)).
  unshelve wp_apply (wp_rand_exp_fin _ _ _ _ f with "Herr").
  {
    intros; rewrite /f.
    real_solver.
  }
  {
    rewrite SeriesC_finite_foldr.
    rewrite /f/=.
    lra.
  }
  iIntros (n) "Hεcont".
  wp_pures.
  case_bool_decide.
  - destruct (decide (n = 0%fin)) as [->|].
    + wp_pures. done.
    + assert (n = 1%fin) as ->.
      { inv_fin n; first done.
        intros i. inv_fin i; first done.
        intros i. inv_fin i; first done.
        intros i. inv_fin i.
      }
      rewrite /f/=.
      iExFalso.
      iApply (ec_contradict with "[$]"). done.
  - assert (n = 2%fin) as ->; [|].
    { inv_fin n; first done.
      repeat (intros i; inv_fin i; first done).
      intros i; inv_fin i.
    }
    wp_pure.
    iApply "IH".
    rewrite /f/=.
    done.
Qed.

Lemma wp_baz_distr E (F : nat -> R) :
  (forall n:nat, 0 <= F(n)) ->
  ↯ (1/2 * F(0%nat) + 1/2 * F(1%nat)) -∗ WP baz #() @ E {{ v, ∃ n:nat, ⌜v = #n⌝ ∗ ↯ (F(n))  }}.
Proof.
  iIntros (HF) "Herr".
  wp_pure.
  iLöb as "IH".
  wp_pures.
  set f:= (λ n : fin 3,
              if bool_decide (n = 0%fin)
                then F(0%nat)
                else if bool_decide (n = 1%fin) then F(1%nat)
                     else ((1/2 * F(0%nat) + 1/2 * F(1%nat)))).
  unshelve wp_apply (wp_rand_exp_fin _ _ _ _ f with "Herr").
  {
    intros; rewrite /f.
    case_bool_decide; auto.
    case_bool_decide; auto.
    apply Rplus_le_le_0_compat.
    - real_solver.
    - real_solver.
  }
  {
    rewrite SeriesC_finite_foldr.
    rewrite /f/=.
    lra.
  }
  iIntros (n) "Hεcont".
  wp_pures.
  case_bool_decide.
  - destruct (decide (n = 0%fin)) as [->|].
    + wp_pures.
      rewrite /f /=.
      iExists 0%nat.
      iFrame.
      iPureIntro.
      done.
    + assert (n = 1%fin) as ->.
      { inv_fin n; first done.
        intros i. inv_fin i; first done.
        intros i. inv_fin i; first done.
        intros i. inv_fin i.
      }
      rewrite /f/=.
      wp_pures.
      iExists 1%nat.
      iFrame.
      iPureIntro.
      done.
  - assert (n = 2%fin) as ->; [|].
    { inv_fin n; first done.
      repeat (intros i; inv_fin i; first done).
      intros i; inv_fin i.
    }
    wp_pure.
    iApply "IH".
    rewrite /f/=.
    done.
Qed.

End foo. 
