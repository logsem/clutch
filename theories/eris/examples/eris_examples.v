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
    ⊢ ↯ (nnreal_half) -∗ WP (e' #2) @ E [{ φ }].
  Proof.
    iIntros "Herr".
    rewrite /e'.
    wp_apply (twp_rand_err_nat _ _ 1).
    iSplitL.
    - iApply (ec_eq with "[$]").
      simpl. lra.
    - iIntros (x) "%".
      wp_pures.
      pose proof (fin_to_nat_lt x).
      destruct (fin_to_nat x); last lia.
      case_bool_decide; last lia.
      by wp_pures.
  Qed.

  Lemma wp_e'_two E:
    ⊢ ↯ (nnreal_half) -∗ WP (e' #2) @ E {{ φ }}.
  Proof.
    iIntros "Herr".
    iApply tgl_wp_pgl_wp'.
    by iApply twp_e'_two.
  Qed.

  Lemma twp_e'_three E:
    ⊢ ↯ (nnreal_one) -∗ WP (e' #3) @ E [{ φ }].
  Proof.
    iIntros "Herr".
    iExFalso.
    iApply ec_contradict; last done.
    simpl. lra.
  Qed.

  Lemma wp_e'_three E:
    ⊢ ↯ (nnreal_half) -∗ WP (e' #3) @ E {{ φ }}.
  Proof.
    iIntros "Herr".
    rewrite /e'.
    wp_apply (wp_rand_err_nat _ _ 0).
    iSplitL.
    - iApply (ec_eq with "[$]").
      simpl. lra.
    - iIntros (x) "%".
      wp_pures.
      pose proof (fin_to_nat_lt x).
      destruct (fin_to_nat x); first lia.
      assert (n=0) as -> by lia.
      case_bool_decide; first lia.
      wp_pures.
      wp_apply loop_lemma.
  Qed.
  
  Lemma twp_e E:
    ⊢ ↯ (nnreal_div (nnreal_nat 3) (nnreal_nat 8)) -∗
    WP e @ E [{φ}].
  Proof.
    iIntros "Herr".
    rewrite /e.
    set (ε2 := λ n : fin (S 3), if (fin_to_nat n <? 2) then nnreal_zero else
                      if (fin_to_nat n =? 2) then nnreal_half else nnreal_one)
        .
        wp_apply (twp_couple_rand_adv_comp1 _ _ _ _ ε2 with "[$]").
        { rewrite SeriesC_finite_foldr. simpl. lra. }
        iIntros (n) "Herr".
        wp_pures. 
        case_bool_decide; wp_pures; first done.
        pose proof (fin_to_nat_lt n).
        eassert (n=nat_to_fin (_:2<4) \/ n = nat_to_fin (_ :3<4)) as [-> | ->].
        { Unshelve.
          all: try lia.
          simpl.
          destruct (fin_to_nat n) as [|[|[|[|]]]] eqn:Hn; [lia|lia|left|right| lia].
          - by repeat (inv_fin n; [done|intros n ?]).
          - by repeat (inv_fin n; [done|intros n ?]).
        }
    - by wp_apply twp_e'_two.
    - by wp_apply twp_e'_three.
  Qed.

  Lemma wp_e E:
    ⊢ ↯ (nnreal_div (nnreal_nat 1) (nnreal_nat 4)) -∗
    WP e @ E {{φ}}.
  Proof.
    iIntros "Herr".
    rewrite /e.
    set (ε2 := λ n : fin (S 3), if (fin_to_nat n <? 2) then nnreal_zero else
                      if (fin_to_nat n =? 2) then nnreal_half else nnreal_half)
        .
        wp_apply (wp_couple_rand_adv_comp1 _ _ _ _ ε2 with "[$]").
        { rewrite SeriesC_finite_foldr. simpl. lra. }
        iIntros (n) "Herr".
        wp_pures. 
        case_bool_decide; wp_pures; first done.
        pose proof (fin_to_nat_lt n).
        eassert (n=nat_to_fin (_:2<4) \/ n = nat_to_fin (_ :3<4)) as [-> | ->].
        { Unshelve.
          all: try lia.
          simpl.
          destruct (fin_to_nat n) as [|[|[|[|]]]] eqn:Hn; [lia|lia|left|right| lia].
          - by repeat (inv_fin n; [done|intros n ?]).
          - by repeat (inv_fin n; [done|intros n ?]).
        }
    - by wp_apply wp_e'_two.
    - by wp_apply wp_e'_three.
  Qed.
    
End test.

Local Open Scope R.

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
  iIntros.
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
  iIntros.
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
  ↯ (nnreal_inv (nnreal_nat 2)) -∗ WP baz #() @ E {{ v, ⌜v = #0⌝ }}.
Proof.
  iIntros "Herr".
  wp_pure.
  iLöb as "IH".
  wp_pures.
  set f:= (λ n : fin 3,
              if bool_decide (n = 0%fin)
                then nnreal_zero
                else if bool_decide (n = 1%fin) then nnreal_one
                                            else nnreal_inv((nnreal_nat 2))).
  unshelve wp_apply (wp_couple_rand_adv_comp _ _ _ _ f with "Herr").
  {
    exists 1; intro n.
    rewrite /f.
    case_bool_decide.
    - simpl; lra.
    - case_bool_decide; simpl; lra.
  }
  {
    rewrite SeriesC_finite_foldr. simpl. lra.
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



