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
From clutch.app_rel_logic Require Import adequacy coupling_rules.
From clutch.prob_lang Require Import class_instances.


Section wp_refinement.
  Context `{!clutchGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.
  Implicit Types ε : nonnegreal.

  (* These are copied from class_instances since we're missing a proofmode for
  the approximate logic and have to do reductions according to the operational
  semantics by hand. *)
  Local Ltac solve_exec_safe := intros; subst; eexists; eapply head_step_support_equiv_rel; eauto with head_step.
  Local Ltac solve_exec_puredet :=
    intros; simpl;
    (repeat case_match); simplify_eq;
    rewrite dret_1_1 //.
  Local Ltac solve_pure_exec :=
    subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

  Fact ref_no_coll_l N ε z (t : fin (S N)) :
    (0 < S N)%R →
    (TCEq (1 / (S N)) ε)%R →
    TCEq N (Z.to_nat z) →
    (€ ε ∗
       refines_right [] (of_val #false))
      ⊢ WP
      (let: "x" := rand #z from #() in "x" = #t)
      {{ v , ∃ v', ⤇ v' ∗ ⌜v = v'⌝ }}.
  Proof.
    iIntros (? Nε Nz) "(ε & #hs & hj)".
    iApply wp_bind.
    {
      replace (App (λ: (BNamed "x"), Var "x" = Val #(LitInt (Z.of_nat (fin_to_nat t)))))
        with (fill [(AppRCtx (λ: (BNamed "x"), Var "x" = Val #(LitInt (Z.of_nat (fin_to_nat t)))))])
        by auto.
      eapply ectxi_lang_ctx_item.
    }
    iApply (wp_rand_avoid t with "hs ε") ; auto.
    { rewrite TCEq_eq. apply nnreal_ext. rewrite -Nε. real_solver. }
    iNext. iIntros (x) "%xt". simpl.

    iApply (wp_pure_step_later _ _ ((λ: "x", "x" = #t)%V #x) True) ; try easy.
    { replace (let: "x" := #x in "x" = #t)%E with (fill [AppLCtx #x] (λ:"x", "x" = #t)%E) by auto.
      replace ((λ: "x", "x" = #t)%V #x) with (fill [AppLCtx #x] (Val (λ: "x", "x" = #t)%V)) by auto.
      eapply pure_exec_fill.
      apply _. }
    iModIntro.
    iApply (wp_pure_step_later _ _ ((#x = #t)%E) True 1) ; try easy.
    1: solve_pure_exec.
    iModIntro.
    iApply (wp_pure_step_later _ _ (Val $ LitV $ LitBool $ bool_decide (#x = #t))%E).
    1: unfold bin_op_eval ; simpl ; auto.
    case_bool_decide as xt'.
    - inversion xt' as [xt''].
      apply Nat2Z.inj' in xt''.
      exfalso. apply xt.
      by apply fin_to_nat_inj.
    - iApply wp_value. iExists _. iNext. iFrame "hj". done.
  Qed.

  (* Bring the statement of the lemma into the shape that the adequacy theorem
     expects. *)
  Corollary ref_no_coll_l' N ε z (t : fin (S N)) :
    (0 < S N)%R →
    (TCEq (1 / S N) ε)%R →
    TCEq N (Z.to_nat z) →
    (⊢ spec_ctx
     -∗ ⤇ (fill [] (of_val #false))
     -∗ € ε
     -∗ WP (let: "x" := rand #z from #() in "x" = #t)
        {{ v , ∃ v', ⤇ v' ∗ ⌜v = v'⌝ }}).
  Proof.
    iIntros. iApply ref_no_coll_l ; eauto. iFrame. done.
  Qed.

End wp_refinement.

Section opsem_refinement.

  Lemma no_coll_l Σ `{clutchGpreS Σ} N (ε : nonnegreal) z (t : fin (S N)) σ σ' :
      (0 < S N)%R →
      ((1 / S N) = ε)%R →
      N = Z.to_nat z →
      ARcoupl
        (lim_exec_val ((let: "x" := rand #z from #() in "x" = #t)%E, σ))
        (lim_exec_val (Val #false, σ'))
        (λ v v' : val, v = v')
        ε.
  Proof.
    intros Npos Nε Nz.
    epose proof
      (wp_aRcoupl_lim _
         (let: "x" := rand #z from #() in "x" = #t)%E
         #false σ σ' ε (λ v v', v = v')) as adequacy.
    assert (TCEq N (Z.to_nat z)) by by rewrite Nz.
    assert (TCEq (1 / S N)%R ε) by by rewrite Nε.
    epose proof (fun H => @ref_no_coll_l' _ H N ε z t Npos _ _) as ref_wp.
    simpl in ref_wp.
    epose proof (adequacy ref_wp) as P.
    simpl in P.
    exact P.
  Qed.

End opsem_refinement.
