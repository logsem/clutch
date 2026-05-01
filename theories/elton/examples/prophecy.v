(** * Counter example of prophecy variables *)
From clutch.elton Require Import elton.

Set Default Proof Using "Type*".

Section counterexample.
  
  (** We assume prophecy variables exist in our language with [WP] specs as
      found in [HeapLang] (see https://dl.acm.org/doi/10.1145/3371113) *)
  Class prophecies := {
      NewProph : val;
      ResolveProph : val;
      NewProph_simple : remove_drand_val (NewProph) = Some (NewProph);
      ResolveProph_simple : remove_drand_val (ResolveProph) = Some (ResolveProph);
      proph_id : Set;
      proph `{H:!eltonGS Σ} : proph_id → list (val * val) → iProp Σ;
      LitProphecy : proph_id → base_lit;

      wp_new_proph s E `{H:!eltonGS Σ}
:
        {{{ True }}}
          NewProph #() @ s; E
        {{{ pvs p, RET (LitV (LitProphecy p)); proph p pvs }}};

     wp_resolve_proph s E (p : proph_id) (pvs : list (val * val)) v `{H:!eltonGS Σ}:
       {{{ proph p pvs }}}
         ResolveProph (Val $ LitV $ LitProphecy p) (Val v) @ s; E
       {{{ pvs', RET (LitV LitUnit); ⌜pvs = (LitV LitUnit, v)::pvs'⌝ ∗ proph p pvs' }}};
    }.

  Definition prog `{prophecies} : expr :=
    let: "x" := NewProph #() in
    let: "y" := rand #1 in
    ResolveProph "x" "y";;
    #false.
  
End counterexample.

Lemma prophecy_unsound {H:prophecies}:
  pgl (lim_exec (prog (H:=H), {|heap :=∅; urns := ∅ |})) (λ v, v=#true) (1/2).
Proof.
  eapply (elton_adequacy_remove_drand eltonΣ (prog)).
  { rewrite /prog. simpl.
    rewrite ResolveProph_simple.
    simpl.
    by rewrite NewProph_simple. 
  }
  { lra. }
  iIntros (? Φ). iModIntro.
  iIntros "Herr HΦ".
  rewrite /prog.
  wp_apply wp_new_proph; first done.
  iIntros (vs ?) "?".
  wp_pures.
  destruct (vs) as [|[v1 v2]].
  - wp_apply (wp_rand); first done.
    iIntros (?) "_".
    wp_pures.
    wp_apply (wp_resolve_proph with "[$]").
    by iIntros (?) "[% ?]".
  - destruct (decide (v2 = #0)); subst.
    + wp_apply (wp_couple_rand_adv_comp' _ _ _ _ (λ x, if bool_decide (fin_to_nat x=0)%nat then 1 else 0)%R with "[$]").
      * intros n.
        case_bool_decide; lra.
      * rewrite SeriesC_finite_foldr.
        simpl.
        lra.
      * iIntros (n).
        inv_fin n; simpl; first (iIntros "?"; by iDestruct (ec_contradict with "[$]") as "[]").
        iIntros (n). inv_fin n; last (iIntros (n); inv_fin n).
        iIntros "?".
        wp_pures.
        wp_apply (wp_resolve_proph with "[$]").
        by iIntros (?) "[% _]".
    + wp_apply (wp_couple_rand_adv_comp' _ _ _ _ (λ x, if bool_decide (fin_to_nat x=1)%nat then 1 else 0)%R with "[$]").
      * intros n'.
        case_bool_decide; lra.
      * rewrite SeriesC_finite_foldr.
        simpl.
        lra.
      * iIntros (n').
        inv_fin n'; simpl.
        { iIntros "?".
        wp_pures.
        wp_apply (wp_resolve_proph with "[$]").
        iIntros (?) "[% _]".
        simplify_eq. 
        }
        iIntros (n'). inv_fin n'; last (iIntros (n'); inv_fin n').
        (iIntros "?"; by iDestruct (ec_contradict with "[$]") as "[]").
Qed.
