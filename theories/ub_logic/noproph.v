From clutch.ub_logic Require Export ub_clutch lib.map.
Set Default Proof Using "Type*".

(* Prophecy variables are unsound with up-to-bad reasoning *)

Module counter_example.
  Context `{!clutchGS Σ}.

  Axiom NewProph : val.
  Axiom ResolveProph : val.
  Axiom proph_id : Set.
  Axiom proph : proph_id → list (val * val) → iProp Σ.
  Axiom LitProphecy : proph_id → base_lit.

  Lemma wp_new_proph s E :
    {{{ True }}}
      NewProph #() @ s; E
    {{{ pvs p, RET (LitV (LitProphecy p)); proph p pvs }}}.
  Proof.
  Admitted.

  Lemma wp_resolve_proph s E (p : proph_id) (pvs : list (val * val)) v :
    {{{ proph p pvs }}}
      ResolveProph (Val $ LitV $ LitProphecy p) (Val v) @ s; E
    {{{ pvs', RET (LitV LitUnit); ⌜pvs = (LitV LitUnit, v)::pvs'⌝ ∗ proph p pvs' }}}.
  Proof.
  Admitted.

  Definition bad : expr :=
    let: "p" := NewProph #() in
    let: "x" := (rand #99 from #()) in
    (ResolveProph "p" "x").

  Lemma falso :
    € (nnreal_inv(nnreal_nat(100))) ⊢ WP bad {{ _, False%I }}.
  Proof.
    iIntros "Hcred".
    rewrite /bad.
    wp_apply (wp_new_proph with "[//]").
    iIntros (pvs p) "Hproph".
    wp_pures.
    destruct pvs as [|(?&v) ?].
    { wp_apply (wp_rand with "[//]").
      iIntros (?) "_". wp_pures.
      wp_apply (wp_resolve_proph with "[$]").
      iIntros (?) "(%Hbad&?)". congruence.
    }
    assert ((∃ z : Z, v = LitV $ LitInt $ z) ∨ (∀ z : Z, v ≠ LitV $ LitInt $ z)) as Hcases.
    { destruct v; firstorder. destruct l; firstorder. eauto. }
    destruct Hcases as [Hz|Hnz]; last first.
    {
      wp_apply (wp_rand with "[//]").
      iIntros (?) "_". wp_pures.
      wp_apply (wp_resolve_proph with "[$]").
      iIntros (?) "(%Hbad&?)". congruence.
    }

    destruct Hz as (z&->).
    wp_apply (wp_rand_err_nat 99 _ (Z.to_nat z)); iFrame "Hcred".
    iIntros (x Hneq). wp_pures.
    wp_apply (wp_resolve_proph with "[$]").
    iIntros (?) "(%Heq&Hproph)".
    inversion Heq. subst. lia.
  Qed.

End counter_example.
