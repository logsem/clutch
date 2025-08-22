(** * Algebraic theory *)
From clutch.foxtrot Require Import foxtrot.
From clutch.foxtrot.lib Require Import toss or diverge nodet par spawn.

Set Default Proof Using "Type*".

Section eq1.
  Variable (e : expr).
  Variable (τ: type).
  Variable (p q:nat).
  Lemma eq1 :
      ∅ ⊢ₜ e : τ -> ∅ ⊨ toss p q e e =ctx= e : τ.
  Proof.
    intros H;
    split;
      apply (refines_sound (#[foxtrotRΣ])); iIntros;
      iPoseProof (binary_fundamental.refines_typed _ _ _ H) as "H";
    iIntros; unfold_rel;
      iIntros (K j) "Hspec"; rewrite /toss.
    - wp_apply wp_rand; first done.
      iIntros (??).
      wp_pures.
      case_bool_decide; wp_pures; iApply ("H"$!K j with "[$]").
    - tp_bind j (rand _)%E.
      iMod (pupd_rand with "[$]") as "(%&?&%)".
      simpl.
      tp_pures j.
      case_bool_decide; tp_pures j; by iApply "H".
  Qed. 
End eq1.

Section eq2.
  Variable (e1 e2 : expr).
  Variable (τ: type).
  Variable (p q:nat).
  Variable (Hineq: p<=q+1).
  Lemma eq2 :
    ∅ ⊢ₜ e1 : τ -> ∅ ⊢ₜ e2 : τ ->
              ∅ ⊨ toss p q e1 e2 =ctx= toss (q+1-p)%nat q e2 e1 : τ.
  Proof.
    assert (Bij (λ x, if bool_decide (x<=q)%nat then q-x else x)) as Hbij.
    { split.
      - intros x y.
        case_bool_decide; case_bool_decide; lia.
      - intros y. destruct (decide (y<=q)).
        + exists (q-y). rewrite bool_decide_eq_true_2; lia.
        + exists y. rewrite bool_decide_eq_false_2; lia.
    }
    intros H1 H2;
    split;
      apply (refines_sound (#[foxtrotRΣ])); iIntros;
      iPoseProof (binary_fundamental.refines_typed _ _ _ H1) as "H1";
      iPoseProof (binary_fundamental.refines_typed _ _ _ H2) as "H2";
    iIntros; unfold_rel;
      iIntros (K j) "Hspec"; rewrite /toss; tp_bind j (rand _)%E.
    - unshelve wp_apply (wp_couple_rand_rand _ (λ x, if bool_decide (x<=q)%nat then q-x else x) with "[$]").
      { intros. case_bool_decide; lia. }
      simpl.
      iIntros (?) "[% Hspec]".
      wp_pures.
      rewrite bool_decide_eq_true_2; last lia.
      tp_pures j.
      case_bool_decide; case_bool_decide; try lia; wp_pures; tp_pures j.
      + by iApply "H2". 
      + by iApply "H1".
    - unshelve wp_apply (wp_couple_rand_rand _ (λ x, if bool_decide (x<=q)%nat then q-x else x) with "[$]").
      { intros. case_bool_decide; lia. }
      simpl.
      iIntros (?) "[% Hspec]".
      wp_pures.
      rewrite bool_decide_eq_true_2; last lia.
      tp_pures j.
      case_bool_decide; case_bool_decide; try lia; wp_pures; tp_pures j.
      + by iApply "H1". 
      + by iApply "H2".
  Qed. 
End eq2.

Section eq3.
  Variable (e1 e2 e3: expr).
  Variable (τ: type).
  Variable (p q r s:nat).
  Variable (Hineq: p<=q+1).
  Variable (Hineq': r<=s+1).

  Definition intermediate_prog: expr:=
      (let: "x" := rand ((#q+#1)*(#s+#1)-#1) in
      if: ("x" < #p*#r) then e1
      else
        if: ("x"-#p*#r<#p*(#s+#1-#r))
        then e2 else e3)%E.

  Ltac start H1 H2 H3:= 
        apply (refines_sound (#[foxtrotRΣ])); iIntros;
          iPoseProof (binary_fundamental.refines_typed _ _ _ H1) as "H1";
          iPoseProof (binary_fundamental.refines_typed _ _ _ H2) as "H2";
          iPoseProof (binary_fundamental.refines_typed _ _ _ H3) as "H3";
          iIntros; unfold_rel;
          iIntros (K j) "Hspec".
  Ltac start' H1 H2 H3:= 
        apply (refines_sound (#[spawnΣ; foxtrotRΣ])); iIntros;
          iPoseProof (binary_fundamental.refines_typed _ _ _ H1) as "H1";
          iPoseProof (binary_fundamental.refines_typed _ _ _ H2) as "H2";
          iPoseProof (binary_fundamental.refines_typed _ _ _ H3) as "H3";
          iIntros; unfold_rel;
        iIntros (K j) "Hspec".
  Local Lemma empty_gamma : (∅=dom (∅:stringmap type)).
  Proof.
    by rewrite dom_empty_L.
  Qed. 
  Ltac solve_subst:=
        rewrite !subst_is_closed_empty; try rewrite !empty_gamma; try by eapply typed_is_closed_expr.
  Lemma eq3_1 :
    ∅ ⊢ₜ e1 : τ -> ∅ ⊢ₜ e2 : τ -> ∅ ⊢ₜ e3 : τ ->
                                          ∅ ⊨ toss p q (toss r s e1 e2) e3 ≤ctx≤ toss (p*r) ((q+1)*(s+1)-1) e1 (toss (r*(q+1-p)) ((q+1)*(s+1)-p*r-1) e2 e3): τ.
  Proof.
    intros H1 H2 H3.
    eapply (ctx_refines_transitive) with (intermediate_prog).
    - eapply (ctx_refines_transitive) with
        (let: "α" := alloc #q in
         let: "β" := alloc #s in
         if: ((rand("α") #q) < #p)
              then if:((rand("β") #s) < #r) then e1 else e2
             else e3
        )%E.
      + (* no tape to tapes*)
        start H1 H2 H3.
        tp_allocnattape j α as "Hα".
        tp_pures j.
        tp_allocnattape j β as "Hβ".
        tp_pures j.
        rewrite /toss.
        tp_bind j (rand(_) _)%E.
        wp_apply (wp_couple_rand_rand_lbl with "[$Hα $Hspec]"); first (simpl; lia).
        iIntros (?) "[_ [Hspec %]]".
        simpl.
        tp_pures j.
        wp_pures.
        solve_subst.
        case_bool_decide; wp_pures; tp_pures j.
        * tp_bind j (rand(_) _)%E.
          wp_apply (wp_couple_rand_rand_lbl with "[$Hβ $Hspec]"); first (simpl; lia).
          iIntros (?) "[_ [Hspec %]]".
          simpl.
          tp_pures j.
          wp_pures.
          case_bool_decide; wp_pures; tp_pures j.
          -- by iApply "H1".
          -- by iApply "H2".
        * by iApply "H3".
      + (* pupd_couple_two_tapes_rand*) admit. 
    - eapply (ctx_refines_transitive) with
        (let, ("x","y") := ((rand #((q + 1) * (s + 1) - 1)) ||| (rand #(((q + 1) * (s + 1) - p * r - 1))))in 
         if: "x" < #(p*r) then e1 else if: "y"<#(r*(q+1-p))%nat then e2 else e3
        )%E.
      + (* wp_coupe_rand_two_rands *) admit.
      + eapply (ctx_refines_transitive) with
          (let, ("α", "β") := (alloc #((q + 1) * (s + 1) - 1), alloc #(((q + 1) * (s + 1) - p * r - 1)))in
            let, ("x","y") := ((rand("α") #((q + 1) * (s + 1) - 1)) ||| (rand("β") #(((q + 1) * (s + 1) - p * r - 1))))in 
         if: "x" < #(p*r) then e1 else if: "y"<#(r*(q+1-p))%nat then e2 else e3
          )%E.
        * start' H1 H2 H3.
          tp_allocnattape j β as "Hβ".
          tp_allocnattape j α as "Hα".
          do 9 tp_pure j.
          tp_bind j (_|||_)%E.
          iMod (tp_par with "[$]") as "(%j1&%j2&%K1&%K2&Hspec1&Hspec2&Hcont)".
          wp_pures.
          wp_apply (wp_par (λ v, ∃ (n:nat), ⌜v=#n⌝ ∗ j1⤇fill K1 v)%I (λ v, ∃ (n:nat), ⌜v=#n⌝ ∗ j2⤇fill K2 v)%I with "[Hspec1 Hα][Hspec2 Hβ]").
          -- wp_apply (wp_couple_rand_rand_lbl with "[$]"); first (simpl; lia).
             iIntros (?) "[?[$?]]". by iExists _.
          -- wp_apply (wp_couple_rand_rand_lbl with "[$]"); first (simpl; lia).
             iIntros (?) "[?[$?]]". by iExists _.
          -- iIntros (??) "[(%&->&Hspec1)(%&->&Hspec2)]".
             iNext. wp_pures.
             iMod ("Hcont" with "[$]"). simpl.
             tp_pures j.
             solve_subst.
             case_bool_decide; wp_pures; tp_pures j; first by iApply "H1".
             case_bool_decide; wp_pures; tp_pures j; [by iApply "H2"|by iApply "H3"].
        * start' H1 H2 H3.
          wp_alloctape β as "Hβ".
          wp_alloctape α as "Hα".
          wp_pures.
          rewrite /toss.
          tp_bind j (rand _)%E.
          iMod (pupd_couple_tape_rand with "[$][$]") as "(%n&Hα&Hspec&%)".
          { rewrite TCEq_eq. lia. }
          { simpl; lia. }
          simpl.
          tp_pures j.
          case_bool_decide; tp_pures j.
          -- wp_apply (wp_par (λ v, ⌜v=#n⌝)%I (λ _, True)%I with "[Hα][Hβ]").
             ++ by wp_randtape.
             ++ iMod (pupd_presample with "[$]") as "(%&?&?)". by wp_randtape.
             ++ iIntros (??) "[-> _]".
                iNext.
                wp_pures.
                rewrite bool_decide_eq_true_2; last lia.
                wp_pures.
                solve_subst.
                by iApply "H1".
          -- tp_bind j (rand _)%E.
             iMod (pupd_couple_tape_rand with "[$Hβ][$]") as "(%n'&Hβ&Hspec&%)".
             { rewrite TCEq_eq. lia. }
             { simpl; lia. }
             simpl.
             tp_pures j.
             wp_apply (wp_par (λ v, ⌜v=#n⌝)%I (λ v, ⌜v=#n'⌝)%I with "[Hα][Hβ]").
             ++ by wp_randtape.
             ++ by wp_randtape.
             ++ iIntros (??) "[-> ->]".
                iNext.
                wp_pures.
                case_bool_decide as H6; rewrite bool_decide_eq_false_2; try lia; solve_subst; wp_pures; tp_pures j.
                ** rewrite bool_decide_eq_true_2; last lia.
                   wp_pures.
                   by iApply "H2".
                ** rewrite bool_decide_eq_false_2; first (wp_pures; by iApply "H3").
                   lia.
  Admitted.
  
  Lemma eq3_2 :
    ∅ ⊢ₜ e1 : τ -> ∅ ⊢ₜ e2 : τ -> ∅ ⊢ₜ e3 : τ ->
                                          ∅ ⊨  toss (p*r) ((q+1)*(s+1)-1) e1 (toss (r*(q+1-p)) ((q+1)*(s+1)-p*r-1) e2 e3)≤ctx≤toss p q (toss r s e1 e2) e3 : τ.
  Proof. 
  Admitted.
  
  Lemma eq3 :
    ∅ ⊢ₜ e1 : τ -> ∅ ⊢ₜ e2 : τ -> ∅ ⊢ₜ e3 : τ ->
              ∅ ⊨ toss p q (toss r s e1 e2) e3 =ctx= toss (p*r) ((q+1)*(s+1)-1) e1 (toss (r*(q+1-p)) ((q+1)*(s+1)-p*r-1) e2 e3): τ.
  Proof.
    intros H1 H2 H3; split.
    - by apply eq3_1.
    - by apply eq3_2.
  Qed. 
End eq3.

Section eq4.
  Variable (e: expr).
  Variable (τ: type).
  Lemma eq4 :
      ∅ ⊢ₜ e : τ -> ∅ ⊨ or e e =ctx= e : τ.
  Proof.
    intros H;
    split;
      apply (refines_sound (#[foxtrotRΣ])); iIntros;
      iPoseProof (binary_fundamental.refines_typed _ _ _ H) as "H";
    iIntros; unfold_rel;
      iIntros (K j) "Hspec".
    - wp_apply (wp_or with "[-]").
      + iSplit; by iApply "H".
      + by iIntros. 
    - iMod (tp_or _ _ _ true with "[$]").
      by iApply "H".
  Qed. 
End eq4.

Section eq5.
  Variable (e1 e2 : expr).
  Variable (τ: type).
  Lemma eq5 :
    ∅ ⊢ₜ e1 : τ -> ∅ ⊢ₜ e2 : τ ->
              ∅ ⊨ or e1 e2 =ctx= or e2 e1 : τ.
  Proof.
    intros H1 H2;
    split;
      apply (refines_sound (#[foxtrotRΣ])); iIntros;
      iPoseProof (binary_fundamental.refines_typed _ _ _ H1) as "H1";
      iPoseProof (binary_fundamental.refines_typed _ _ _ H2) as "H2";
    iIntros; unfold_rel;
      iIntros (K j) "Hspec".
    - wp_apply (wp_or with "[-]").
      + iSplit.
        * iMod (tp_or _ _ _ false with "[$]").
          by iApply "H1".
        * iMod (tp_or _ _ _ true with "[$]").
          by iApply "H2".
      + simpl. by iIntros.
    - wp_apply (wp_or with "[-]").
      + iSplit.
        * iMod (tp_or _ _ _ false with "[$]").
          by iApply "H2".
        * iMod (tp_or _ _ _ true with "[$]").
          by iApply "H1".
      + simpl. by iIntros.
  Qed.     
End eq5.

Section eq6.
  Variable (e1 e2 e3: expr).
  Variable (τ: type).

  Lemma eq6 :
    ∅ ⊢ₜ e1 : τ -> ∅ ⊢ₜ e2 : τ -> ∅ ⊢ₜ e3 : τ ->
              ∅ ⊨ or e1 (or e2 e3) =ctx= or (or e1 e2) e3: τ.
  Proof.
    intros H1 H2 H3.
    split;
      apply (refines_sound (#[foxtrotRΣ])); iIntros;
      iPoseProof (binary_fundamental.refines_typed _ _ _ H1) as "H1";
      iPoseProof (binary_fundamental.refines_typed _ _ _ H2) as "H2";
      iPoseProof (binary_fundamental.refines_typed _ _ _ H3) as "H3"; unfold_rel;
      iIntros (K j) "Hspec"; wp_apply (wp_or with "[-]"); try iSplit; try wp_apply (wp_or with "[-]"); try iSplit.
    - iMod (tp_or _ _ _ true with "[$]").
      iMod (tp_or _ _ _ true with "[$]").
      by iApply "H1".
    - iMod (tp_or _ _ _ true with "[$]").
      iMod (tp_or _ _ _ false with "[$]").
      by iApply "H2".
    - iMod (tp_or _ _ _ false with "[$]").
      by iApply "H3".
    - by iIntros.
    - by iIntros.
    - iMod (tp_or _ _ _ true with "[$]").
      by iApply "H1".
    - iMod (tp_or _ _ _ false with "[$]").
      iMod (tp_or _ _ _ true with "[$]").
      by iApply "H2".
    - shelve. 
    - iMod (tp_or _ _ _ false with "[$]").
      iMod (tp_or _ _ _ false with "[$]").
      by iApply "H3".
    - by iIntros.
      Unshelve.
      2:{ by iIntros. }
  Qed. 
End eq6.

Section eq7.
  Variable (e: expr).
  Variable (τ: type).
  Lemma eq7 :
      ∅ ⊢ₜ e : τ -> ∅ ⊨ or e (diverge #()) =ctx= e : τ.
  Proof.
    intros H;
    split;
      apply (refines_sound (#[foxtrotRΣ])); iIntros;
      iPoseProof (binary_fundamental.refines_typed _ _ _ H) as "H";
    iIntros; unfold_rel;
      iIntros (K j) "Hspec".
    - wp_apply (wp_or with "[-]").
      + iSplit; first by iApply "H".
        wp_apply wp_diverge; first done.
        by iIntros. 
      + by iIntros. 
    - iMod (tp_or _ _ _ true with "[$]").
      by iApply "H".
  Qed. 
End eq7.

Section eq8.
  (** The other refinement direction is not provable in Foxtrot atm *)
  Variable (e1 e2 e3: expr).
  Variable (p q:nat).
  Variable (τ: type).
  Lemma eq8:
    ∅ ⊢ₜ e1 : τ -> ∅ ⊢ₜ e2 : τ -> ∅ ⊢ₜ e3 : τ ->
              ∅ ⊨ or (toss p q e1 e2) (toss p q e1 e3) ≤ctx≤ toss p q e1 (or e2 e3): τ.
  Proof.
    intros H1 H2 H3.
      apply (refines_sound (#[foxtrotRΣ])); iIntros;
      iPoseProof (binary_fundamental.refines_typed _ _ _ H1) as "H1";
      iPoseProof (binary_fundamental.refines_typed _ _ _ H2) as "H2";
      iPoseProof (binary_fundamental.refines_typed _ _ _ H3) as "H3"; unfold_rel;
        iIntros (K j) "Hspec".
      wp_apply (wp_or with "[-]").
    - iSplit.
      + rewrite /toss.
        tp_bind j (rand _)%E.
        wp_apply (wp_couple_rand_rand with "[$]"); first (simpl; lia).
        iIntros (?) "(%&Hpsec)".
        simpl.
        tp_pures j.
        wp_pures.
        case_bool_decide; tp_pures j; wp_pures.
        * by iApply "H1".
        * iMod (tp_or _ _ _ true with "[$]").
          by iApply "H2".
      + rewrite /toss.
        tp_bind j (rand _)%E.
        wp_apply (wp_couple_rand_rand with "[$]"); first (simpl; lia).
        iIntros (?) "(%&Hpsec)".
        simpl.
        tp_pures j.
        wp_pures.
        case_bool_decide; tp_pures j; wp_pures.
        * by iApply "H1".
        * iMod (tp_or _ _ _ false with "[$]").
          by iApply "H3".
    - by iIntros.
  Qed. 
End eq8.
