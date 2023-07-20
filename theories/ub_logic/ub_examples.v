From clutch.ub_logic Require Export ub_clutch.


Local Open Scope R.
Context `{!clutchGS Σ}.

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
