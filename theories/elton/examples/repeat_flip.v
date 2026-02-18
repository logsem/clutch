From iris.base_logic.lib Require Import token.
From clutch.elton Require Import elton. 
From clutch.elton.lib Require Import flip.
Set Default Proof Using "Type*".

Definition prog : expr :=
  λ: "A",
    let: "v" := flip #() in
    let: "l" := ref "v" in
    let: "f" := (λ: "_",
                   let: "v" := flip #() in
                   "l" <- "v"
                ) in
    "A" "f";;
    ! "l"
.

Definition prog' : expr :=
  λ: "A",
    let: "v" := dflip #() in
    let: "l" := ref "v" in
    let: "f" := (λ: "_",
                   let: "v" := dflip #() in
                   "l" <- "v"
                ) in
    "A" "f";;
    ! "l"
.

Definition fair_coin_val : distr val:= dmap (λ (b:bool), #(b)) fair_coin.

Section proofs.
  Lemma prog_correct A:
    ∅ ⊢ₜ A : ((TUnit → TUnit) → TUnit) ->
             ∀ v, ((lim_exec ((prog A), {|heap:=∅; urns:= ∅|})) v <= fair_coin_val v)%R.
  Proof.
    intros Htyped.
    eapply (elton_adequacy_remove_drand_distribution (#[eltonΣ; tokenΣ]) (prog' A)).
    { simpl. by erewrite typed_remove_drand_expr. }
    iIntros (? ε L D Hpos Hrange Hineq).
    iIntros (Φ).
    iModIntro.
    iIntros "Herr HΦ".
    rewrite /prog'.
    wp_pures.
    iPoseProof (typed_safe _ [] _ Htyped) as "H".
    wp_bind (A).
    iApply (pgl_wp_wand); first done.
    iIntros (?) "#Hinterp".
    do 2 wp_pure.
    rewrite -/dflip.
    wp_apply (wp_dflip with "[//]").
    iIntros (l) "Hflip".
    wp_pures.
    wp_alloc loc as "Hl".
    wp_pures.
    rewrite -/dflip.
    iMod (token_alloc) as (γ) "Htoken".
    iMod (inv_alloc nroot _ ((∃ x, loc↦ #(flip_v x) ∗ flip_urn x {[true; false]}) ∨∃ v, loc ↦ v ∗ token γ)%I with "[Hflip Hl]") as "#Hinv"; first iFrame.
    wp_bind (v _)%E.
    rewrite refines_eq /refines_def.
    simpl.
    iApply (pgl_wp_wand); first iApply "Hinterp".
    { iIntros (?).
      iModIntro.
      iIntros (?).
      subst.
      rewrite refines_eq /refines_def.
      wp_pure.
      rewrite -/(dflip _).
      wp_apply (wp_dflip with "[//]").
      iIntros (l') "Hflip'".
      wp_pures.
      iInv "Hinv" as ">[H1|H1]" "Hclose".
      - iDestruct "H1" as "(%&?&?)".
        wp_store.
        by iMod ("Hclose" with "[$]").
      - iDestruct "H1" as "(%&?&?)".
        wp_store.
        by iMod ("Hclose" with "[$]").
    }
    iIntros (?) "_".
    wp_pures.
    rewrite -(fill_empty (!_)).
    iApply pgl_wp_bind.
    iInv "Hinv" as ">[H1|H1]" "Hclose"; last first. 
    { iDestruct "H1" as "(%&?&Htoken')".
      iCombine "Htoken" "Htoken'" gives "[]". }
    iDestruct "H1" as "(%&Hl&Hflip)".
    wp_load.
    iMod ("Hclose" with "[Htoken Hl]").
    { iNext. iRight.
      iFrame. }
    iModIntro.
    simpl.
    assert (∀ b, 0<= D b)%R as Hpos' by naive_solver.
    iMod (flip_urn_resolve (λ b, mknonnegreal _ (Hpos' #b)) with "[$][$]") as "(%&Herr &Hflip)".
    - simpl.
      trans (2*(SeriesC (λ v : val, D v * fair_coin_val v)))%R; last real_solver.
      erewrite (SeriesC_ext _ (λ (b:val), if bool_decide (b∈([( #true); (#false)] : list val)) then D b * /2 else 0))%R.
      + rewrite (SeriesC_list); simpl.
        * rewrite /fair_coin_val. rewrite /dmap/dbind/pmf/dbind_pmf. lra.
        * repeat rewrite NoDup_cons.
          repeat split; try set_solver.
          by apply NoDup_nil.
      + intros.
        case_bool_decide as H'.
        * set_unfold in H'.
          destruct!/=; simpl; rewrite /fair_coin_val; f_equal.
          all: erewrite dmap_elem_eq; last done.
          all: try rewrite fair_coin_pmf; try lra.
          all: intros ???; by simplify_eq.
        * rewrite /fair_coin_val.
          erewrite dmap_elem_ne; first lra.
          -- intros ???; by simplify_eq.
          -- intros [[] ]; destruct!/=; set_solver.
    - iApply (wp_value_promotion with "[Hflip]"); first by iApply flip_v_promote.
      iIntros "_".
      wp_pures.
      iApply "HΦ".
      by iFrame.
  Qed. 

  
End proofs.
    
