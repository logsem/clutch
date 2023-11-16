From clutch.ub_logic Require Export ub_clutch.


Local Open Scope R.
Context `{!ub_clutchGS Σ}.

Definition foo N (m : nat) : expr :=
  let: "n" := rand #N from #() in
  if: "n" = #m then #false else #true.


Lemma wp_foo (N : nat) m E :
  {{{ € (nnreal_inv(nnreal_nat(N+1))) }}}
  (foo N m) @ E
  {{{ v, RET v; ⌜ v = #true ⌝ }}}.
Proof.
  iIntros (Φ) "Herr HΦ".
  rewrite /foo/=.
  wp_bind (rand _ from #())%E.
  wp_apply (wp_rand_err_nat _ _ m).
  iFrame.
  iIntros.
  wp_pures.
  rewrite bool_decide_eq_false_2; auto; [ | intro; simplify_eq ].
  wp_if_false.
  by iApply "HΦ".
Qed.


Definition bar N : expr :=
  let: "m" := rand #N from #() in
  let: "n" := rand #N from #() in
  if: "n" = "m" then #false else #true.


Definition wp_bar (N : nat) E :
  {{{ € (nnreal_inv(nnreal_nat(N+1))) }}}
  (bar N) @ E
  {{{ v, RET v; ⌜ v = #true ⌝ }}}.
Proof.
  iIntros (Φ) "Herr HΦ".
  rewrite /bar/=.
  wp_bind (rand _ from #())%E.
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
    let: "n" := rand #2 from #() in
    (if: "n" < #2
      then "n"
      else "baz" #() ).


Lemma wp_baz E :
  € (nnreal_inv (nnreal_nat 2)) -∗ WP baz #() @ E {{ v, ⌜v = #0⌝ }}.
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
  unshelve wp_apply (wp_couple_rand_adv_comp _ _ _ _ _ f with "Herr").
  { intro. exact ⌜ true ⌝%I. }.
  {
    exists 1; intro n.
    rewrite /f.
    case_bool_decide.
    - simpl; lra.
    - case_bool_decide; simpl; lra.
  }
  {
    admit.
  }
  iIntros (n) "Hεcont".
  wp_pures.
  case_bool_decide.
  - destruct (decide (n = 0%fin)) as [->|].
    + wp_pures. done.
    + assert (n = 1%fin) as ->.
      {
        admit.
      }
      rewrite /f/=.
      (* Should be allowed to prove this for free with €1 *)
      admit.
  - assert (n = 2%fin) as ->; [admit|].
    wp_pure.
    iApply "IH".
    rewrite /f/=.
    done.
Admitted.


