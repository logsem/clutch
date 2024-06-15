(* From discussions with Ugo:

''' define e := let x = rand n in x = t

where x : string(n), n sec'ty param, and t arbitrary.

The program e should be equivalent up to negligible probability to false, so
long as x and t are independent. But since x is randomly sampled, they will
indeed be independent.

This law is well-known ; it may not be used in EC, but in Squirrel prover, and
shows up in their examples too.
'''

We would like to show that `e` is feasibly contextually equivalent to `false`.

We can't reason about feasible contextual equivalence yet, so we instead show
that there is an approximate coupling between the evaluation of `e` and `false`
that lifts equality with error `1/N`, i.e.,

`e ~ false { m b . m = b } 1/n`

 *)

From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prob_lang Require Import notation tactics metatheory.
From clutch.paris Require Import adequacy coupling_rules proofmode.
From clutch.prob_lang Require Import class_instances.

Section wp_refinement.
  Context `{!parisGS Σ}.

  Lemma wp_ref_no_coll_l N z (t : fin (S N)) :
    TCEq N (Z.to_nat z) →
    {{{ ↯ (1 / S N) ∗ ⤇ #false }}}
       let: "x" := rand #z in "x" = #t
    {{{ (b : bool), RET #b; ⤇ #b }}}.
  Proof.
    iIntros (Nz Ψ) "(ε & hj) HΨ".
    wp_bind (rand #z)%E.
    wp_apply (wp_rand_avoid_l t with "ε"); [done|].
    iIntros (??).
    wp_pures.
    iApply "HΨ".
    rewrite bool_decide_eq_false_2 //.
    intros ?. simplify_eq.
  Qed.

End wp_refinement.

Section opsem_refinement.

  Lemma no_coll_l N (ε : nonnegreal) z (t : fin (S N)) σ σ' :
    N = Z.to_nat z →
    ARcoupl
      (lim_exec ((let: "x" := rand #z in "x" = #t)%E, σ))
      (lim_exec (Val #false, σ'))
      (=)
      (1 / S N).
  Proof.
    intros ->.
    eapply (wp_adequacy parisΣ).
    { real_solver. }
    iIntros (?) "? ?".
    iApply (wp_ref_no_coll_l with "[$]").
    eauto.
  Qed.

End opsem_refinement.
