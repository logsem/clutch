From iris.base_logic.lib Require Import token.
From clutch.elton Require Import elton. 
From clutch.elton.lib Require Import flip.
Set Default Proof Using "Type*".

Definition prog : expr :=
  λ: "A",
    let: "v" := flip #() in
    let: "l" := ref "v" in
    let: "f1" := (λ: "_",
                   let: "v" := flip #() in
                   "l" <- "v"
                ) in
    let: "f2" := (λ: "_",
                   let: "v" := !"l" in
                   "l" <- ~ "v"
                ) in
    "A" "f1" "f2";;
    ! "l"
.

Definition prog' : expr :=
  λ: "A",
    let: "v" := dflip #() in
    let: "l" := ref "v" in
    let: "f1" := (λ: "_",
                   let: "v" := dflip #() in
                   "l" <- "v"
                ) in
    let: "f2" := (λ: "_",
                   let: "v" := !"l" in
                   "l" <- ~ "v"
                ) in
    "A" "f1" "f2";;
    ! "l"
.

Definition fair_coin_val : distr val:= dmap (λ (b:bool), #(b)) fair_coin.

Section proofs.
  Lemma prog_correct A:
    ∅ ⊢ₜ A : ((TUnit → TUnit) → (TUnit → TUnit) → TUnit) ->
             ∀ v, ((lim_exec ((prog A), {|heap:=∅; urns:= ∅|})) v <= fair_coin_val v)%R.
  Proof.
    assert (Inhabited base_lit) by exact ({|inhabitant := LitUnit |}).
    assert (Inhabited (bool->bool)) by exact ({|inhabitant := id |}).  
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
    iMod ((inv_alloc (nroot.@"2") _ ((flip_urn l {[true; false]}) ∨ token γ))%I with "[$Hflip]") as "#Hinv'".
    iMod (inv_alloc (nroot.@"1") _
            ( ∃ (x:base_lit)(f:bool -> bool) l , ⌜Bij f⌝ ∗ loc ↦ #x ∗ ⌜base_lit_type_check x = Some BLTBool⌝ ∗
                              □(∀ b, flip_urn l {[b]} -∗ rupd (λ x, x=f b) (flip_urn l {[b]}) x) ∗
                             inv (nroot.@"2")((flip_urn l {[true; false]})
                               ∨ token γ))%I
           with "[ Hl]") as "#Hinv"; first iFrame.
    { iNext. iExists id. iFrame "Hinv'". repeat iSplit.
      - iPureIntro.
        split. 
        + intros ???. by simplify_eq.
        + intros ?. naive_solver.
      - (iPureIntro; apply flip_v_type).
      - iModIntro. 
        iIntros. 
        by iApply flip_v_promote. }
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
      iInv "Hinv" as "H1" "Hclose".
      repeat setoid_rewrite bi.later_exist.
      iDestruct "H1" as "(%&%&%&H1)".
      repeat rewrite bi.later_sep_1.
      iDestruct "H1" as "(>%&>H1&>%&H2&H3)".
      wp_store.
    iMod ((inv_alloc (nroot.@"2") _ ((flip_urn _ {[true; false]}) ∨ token γ))%I with "[$Hflip']") as "#Hinv''".
      iDestruct "H2" as "#H2".
      iDestruct "H3" as "#H3".
      iMod ("Hclose" with "[$H1 $Hinv'']"); last done.
      iExists id.
      iNext.
      repeat iSplit; try done.
      - iPureIntro; split; apply _.
      - iModIntro.
        iIntros.
        simpl.
        by iApply flip_v_promote.
    }
    iIntros (v') "#Hinterp'".
    wp_bind (v' _).
    rewrite refines_eq /refines_def.
    simpl.
    iApply (pgl_wp_wand); first iApply "Hinterp'".
    { iIntros (?).
      iModIntro.
      iIntros (?).
      subst.
      rewrite refines_eq /refines_def.
      wp_pure.
      wp_bind (! _)%E.
      iInv "Hinv" as "H1" "Hclose".
      repeat setoid_rewrite bi.later_exist.
      iDestruct "H1" as "(%x&%f&%&H1)".
      repeat rewrite bi.later_sep_1.
      iDestruct "H1" as "(>%&>H1&>%&H2&H3)".
      wp_load.
      iDestruct "H2" as "#H2".
      iDestruct "H3" as "#H3".
      iMod ("Hclose" with "[$H1 $H2 $H3]"); first done.
      iModIntro.
      wp_pures.
      destruct (decide (∃ b, x=LitBool b))as [[b]|].
      - destruct!/=. wp_pures. 
        iInv "Hinv" as "H1" "Hclose".
        repeat setoid_rewrite bi.later_exist.
        iDestruct "H1" as "(%x&%&%&H1)".
        repeat rewrite bi.later_sep_1.
        iDestruct "H1" as "(>%Hbij&>H1&>%Htype&_&_)".
        wp_store.
        iMod ("Hclose" with "[$H1]"); last done.
        iFrame "H3".
        iExists (negb ∘ f).
        repeat iSplit; try done.
        + iPureIntro.
          split.
          * apply _.
          * apply _.
        + iNext. iModIntro.
          iIntros (b0)"?".
          iDestruct ("H2" with "[$]") as "H1".
          rewrite rupd_unseal/rupd_def.
          iIntros. 
          iDestruct ("H1" with "[$]") as "(%H'&?&$)".
          iFrame. iPureIntro.
          simpl.
          intros ? H2'. apply H' in H2'.
          destruct H2' as (?&?&?).
          subst.
          naive_solver.
      - destruct!/=.
        wp_pure.
        { simpl.
          rewrite H3. repeat case_match; naive_solver. }
        iInv "Hinv" as "H1" "Hclose".
        repeat setoid_rewrite bi.later_exist.
        iDestruct "H1" as "(%&%&%&H1)".
        repeat rewrite bi.later_sep_1.
        iDestruct "H1" as "(>%Hbij&>H1&>%Htype&_&_)".
        wp_store.
        iMod ("Hclose" with "[$H1]"); last done.
        iFrame "H3".
        iExists (negb ∘ f).
        repeat iSplit; try done.
        + iPureIntro.
          split.
          * apply _.
          * apply _.
        + simpl. by rewrite H3.
        + iModIntro. iModIntro.
          iIntros (?)"?".
          iDestruct ("H2" with "[$]") as "H1".
          rewrite rupd_unseal/rupd_def.
          iIntros. 
          iDestruct ("H1" with "[$]") as "(%H'&?&$)".
          iFrame. iPureIntro.
          simpl.
          intros ? H2'. apply H' in H2'.
          destruct H2' as (?&H2'&?).
          subst.
          rewrite H2'. simpl.
          naive_solver.
    }
    iIntros (?) "_".
    wp_pures.
    rewrite -(fill_empty (!_)).
    iApply pgl_wp_bind.
    iInv "Hinv" as "H1" "Hclose".
    repeat setoid_rewrite bi.later_exist.
    iDestruct "H1" as "(%x&%f&%&H1)".
    repeat rewrite bi.later_sep_1.
    iDestruct "H1" as "(>%&>H1&>%&H2&H3)".
    wp_load.
    iDestruct "H2" as "#H2".
    iDestruct "H3" as "#H3".
    iMod ("Hclose" with "[$H1 $H2 $H3]"); first done.
    iInv "H3" as ">[H3'|H3']" "Hclose"; last first.
    { iCombine "Htoken" "H3'" gives "[]". }
    iMod ("Hclose" with "[$Htoken]").
    iModIntro.
    simpl.
    set (D' := λ (v:val), match v with
                    | #(LitBool b) => D # (LitBool (f b))
                    | _ => D v
                    end
        ).
    assert (∀ b, 0<= D' (b))%R as Hpos'.
    { rewrite /D'. intros. repeat case_match; naive_solver. }
    iMod (flip_urn_resolve (λ b, mknonnegreal _ (Hpos' #b)) with "[$][$]") as "(%&Herr &Hflip)".
    - simpl.
      trans (2*(SeriesC (λ v : val, D v * fair_coin_val v)))%R; last real_solver.
      erewrite (SeriesC_ext _ (λ (b:val), if bool_decide (b∈([( #true); (#false)] : list val)) then D b * /2 else 0))%R.
      + rewrite (SeriesC_list); simpl.
        * rewrite /fair_coin_val. rewrite /dmap/dbind/pmf/dbind_pmf.
          destruct (f true) eqn :Heqn.
          -- assert (f false = false) as ->; last lra.
             destruct (f false) eqn:Heqn'; last done.
             rewrite -Heqn in Heqn'.
             simplify_eq.
          -- assert (f false = true) as ->; last lra.
             destruct (f false) eqn:Heqn'; first done.
             rewrite -{2}Heqn in Heqn'.
             simplify_eq.
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
    - iApply (wp_value_promotion with "[Hflip]"); first by iApply "H2". 
      iIntros "_".
      wp_pures.
      iApply "HΦ". by iFrame.
  Qed. 

  
End proofs.
    
