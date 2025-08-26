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
                                          ∅ ⊨ toss r s (toss p q e1 e2) e3 ≤ctx≤ toss (p*r) ((q+1)*(s+1)-1) e1 (toss (r*(q+1-p)) ((q+1)*(s+1)-p*r-1) e2 e3): τ.
  Proof.
    intros H1 H2 H3.
    eapply (ctx_refines_transitive) with
        (let: "α" := alloc #s in
         let: "β" := alloc #q in
         if: ((rand("α") #s) < #r)
              then if:((rand("β") #q) < #p) then e1 else e2
             else e3
        )%E.
    { (* no tape to tapes*)
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
      - tp_bind j (rand(_) _)%E.
        wp_apply (wp_couple_rand_rand_lbl with "[$Hβ $Hspec]"); first (simpl; lia).
        iIntros (?) "[_ [Hspec %]]".
        simpl.
        tp_pures j.
        wp_pures.
        case_bool_decide; wp_pures; tp_pures j.
        + by iApply "H1".
        + by iApply "H2".
      - by iApply "H3".
    }  
    eapply (ctx_refines_transitive) with
      (let, ("x","y") := ((rand #((q + 1) * (s + 1) - 1)%nat) ||| (rand #(((q + 1) * (s + 1) - p * r - 1))%nat))in 
       if: "x" < #(p*r) then e1 else if: "y"<#(r*(q+1-p))%nat then e2 else e3
      )%E.
    {
      start H1 H2 H3.
      wp_alloctape α as "Hα".
      wp_pures.
      wp_alloctape β as "Hβ".
      wp_pures.
      tp_bind j (_|||_)%E.
      iMod (tp_par with "[$]") as "(%j1&%j2&%K1&%K2&Hspec1&Hspec2&Hcont)".
      iMod (pupd_couple_associativity with "Hα Hβ Hspec1 Hspec2") as "(%resl&%resl'&%resr&%resr'&%&%&%&%&Hα&Hβ&Hspec1&Hspec2&%Hcond)".
      { exact. }
      { exact. }
      { lia. }
      { lia. }
      simpl.
      iMod ("Hcont" with "[$]") as "Hspec".
      tp_pures j.
      case_bool_decide.
      - rewrite bool_decide_eq_true_2; last lia.
        tp_pures j.
        solve_subst.
        wp_randtape.
        wp_pures.
        rewrite bool_decide_eq_true_2; last lia.
        wp_pures.
        wp_randtape.
        wp_pures.
        rewrite bool_decide_eq_true_2; last lia.
        wp_pures.
        by iApply "H1".
      - rewrite bool_decide_eq_false_2; last lia.
        tp_pures j.
        solve_subst.
        case_bool_decide.
        + rewrite bool_decide_eq_true_2; last lia.
          tp_pures j.
          wp_pures.
          wp_randtape. wp_pures.
          rewrite bool_decide_eq_true_2; last lia.
          wp_pures.
          wp_randtape.
          wp_pures.
          rewrite bool_decide_eq_false_2; last lia.
          wp_pures.
          by iApply "H2".
        + rewrite bool_decide_eq_false_2; last lia.
          tp_pures j.
          wp_pures.
          wp_randtape. wp_pures.
          rewrite bool_decide_eq_false_2; last lia.
          wp_pures.
          by iApply "H3". }
    eapply (ctx_refines_transitive) with
      (let, ("α", "β") := (alloc #((q + 1) * (s + 1) - 1)%nat, alloc #(((q + 1) * (s + 1) - p * r - 1))%nat)in
       let, ("x","y") := ((rand("α") #((q + 1) * (s + 1) - 1)%nat) ||| (rand("β") #(((q + 1) * (s + 1) - p * r - 1))%nat))in 
       if: "x" < #(p*r) then e1 else if: "y"<#(r*(q+1-p))%nat then e2 else e3
      )%E.
    { start' H1 H2 H3.
      tp_allocnattape j β as "Hβ".
      tp_allocnattape j α as "Hα".
      do 9 tp_pure j.
      tp_bind j (_|||_)%E.
      iMod (tp_par with "[$]") as "(%j1&%j2&%K1&%K2&Hspec1&Hspec2&Hcont)".
      wp_pures.
      wp_apply (wp_par (λ v, ∃ (n:nat), ⌜v=#n⌝ ∗ j1⤇fill K1 v)%I (λ v, ∃ (n:nat), ⌜v=#n⌝ ∗ j2⤇fill K2 v)%I with "[Hspec1 Hα][Hspec2 Hβ]").
      - wp_apply (wp_couple_rand_rand_lbl with "[$]"); first (simpl; lia).
         iIntros (?) "[?[$?]]". by iExists _.
      - wp_apply (wp_couple_rand_rand_lbl with "[$]"); first (simpl; lia).
         iIntros (?) "[?[$?]]". by iExists _.
      - iIntros (??) "[(%&->&Hspec1)(%&->&Hspec2)]".
         iNext. wp_pures.
         iMod ("Hcont" with "[$]"). simpl.
         tp_pures j.
         solve_subst.
         case_bool_decide; wp_pures; tp_pures j; first by iApply "H1".
         case_bool_decide; wp_pures; tp_pures j; [by iApply "H2"|by iApply "H3"]. }
    start' H1 H2 H3.
    wp_alloctape β as "Hβ".
    wp_alloctape α as "Hα".
    wp_pures.
    rewrite /toss.
    tp_bind j (rand _)%E.
    iMod (pupd_couple_tape_rand with "[$][$]") as "(%n&Hα&Hspec&%)".
    { simpl; lia. }
    simpl.
    tp_pures j.
    case_bool_decide; tp_pures j.
    - wp_apply (wp_par (λ v, ⌜v=#n⌝)%I (λ _, True)%I with "[Hα][Hβ]").
      + by wp_randtape.
      + iMod (pupd_presample with "[$]") as "(%&?&?)". by wp_randtape.
      + iIntros (??) "[-> _]".
        iNext.
        wp_pures.
        rewrite bool_decide_eq_true_2; last lia.
        wp_pures.
        solve_subst.
        by iApply "H1".
    - tp_bind j (rand _)%E.
      iMod (pupd_couple_tape_rand with "[$Hβ][$]") as "(%n'&Hβ&Hspec&%)".
      { simpl; lia. }
      simpl.
      tp_pures j.
      wp_apply (wp_par (λ v, ⌜v=#n⌝)%I (λ v, ⌜v=#n'⌝)%I with "[Hα][Hβ]").
      + by wp_randtape.
      + by wp_randtape.
      + iIntros (??) "[-> ->]".
        iNext.
        wp_pures.
        case_bool_decide as H6; rewrite bool_decide_eq_false_2; try lia; solve_subst; wp_pures; tp_pures j.
        * rewrite bool_decide_eq_true_2; last lia.
          wp_pures.
          by iApply "H2".
        * rewrite bool_decide_eq_false_2; first (wp_pures; by iApply "H3").
          lia.
 Qed.
  
  Lemma eq3_2 :
    ∅ ⊢ₜ e1 : τ -> ∅ ⊢ₜ e2 : τ -> ∅ ⊢ₜ e3 : τ ->
                                          ∅ ⊨  toss (p*r) ((q+1)*(s+1)-1) e1 (toss (r*(q+1-p)) ((q+1)*(s+1)-p*r-1) e2 e3)≤ctx≤toss r s (toss p q e1 e2) e3 : τ.
  Proof.
    intros H1 H2 H3.
    remember ((q+1)*(s+1)-p*r-1) as s' eqn:Hs'.
    remember (p*r) as p' eqn:Hp'.
    remember ((q+1)*(s+1)-1) as q' eqn:Hq'.
    remember (r*(q+1-p)) as r' eqn:Hr'.
    eapply (ctx_refines_transitive) with
        (toss (q'+1-p') q' (toss (s'+1-r') s' e3 e2) e1
        )%E.
    {
      start H1 H2 H3.
      rewrite /toss.
      assert (Bij (λ x, if bool_decide (x<=q')%nat then q'-x else x)) as Hbij1.
      { split.
        - intros x y.
          case_bool_decide; case_bool_decide; lia.
        - intros y. destruct (decide (y<=q')).
          + exists (q'-y). rewrite bool_decide_eq_true_2; lia.
          + exists y. rewrite bool_decide_eq_false_2; lia.
      }
      assert (Bij (λ x, if bool_decide (x<=s')%nat then s'-x else x)) as Hbij2.
      { split.
        - intros x y.
          case_bool_decide; case_bool_decide; lia.
        - intros y. destruct (decide (y<=s')).
          + exists (s'-y). rewrite bool_decide_eq_true_2; lia.
          + exists y. rewrite bool_decide_eq_false_2; lia.
      }
      tp_bind j (rand _)%E.
      unshelve wp_apply (wp_couple_rand_rand _ (λ x, if bool_decide (x<=q')%nat then q'-x else x) with "[$]").
      { intros. case_bool_decide; lia. }
      iIntros (?) "(%&Hspec)".
      simpl.
      wp_pures.
      rewrite bool_decide_eq_true_2; last lia.
      tp_pures j.
      case_bool_decide; last first.
      - rewrite bool_decide_eq_true_2; last lia.
        wp_pures.
        tp_pures j.
        by iApply "H1".
      - tp_pures j.
        rewrite bool_decide_eq_false_2; last lia.
        wp_pures.
      tp_bind j (rand _)%E.
      unshelve wp_apply (wp_couple_rand_rand _ (λ x, if bool_decide (x<=s')%nat then s'-x else x) with "[$]").
      { intros. case_bool_decide; lia. }
      iIntros (?) "(%&Hspec)".
      simpl.
      rewrite bool_decide_eq_true_2; last lia.
      wp_pures. tp_pures j.
      case_bool_decide.
        + rewrite bool_decide_eq_false_2; last lia.
          wp_pures; tp_pures j.
          by iApply "H3".
        + rewrite bool_decide_eq_true_2; last lia.
          wp_pures; tp_pures j.
          by iApply "H2".
    }
    remember (q'+1-p') as p'' eqn :Hp''.
    remember (s'+1-r') as r'' eqn :Hr''.
    eapply (ctx_refines_transitive) with
        (let: "α" := alloc #q' in
         let: "β" := alloc #s' in
         if: ((rand("α") #q') < #p'')
              then if:((rand("β") #s') < #r'') then e3 else e2
             else e1
        )%E.
    { (* no tape to tapes*)
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
      - tp_bind j (rand(_) _)%E.
        wp_apply (wp_couple_rand_rand_lbl with "[$Hβ $Hspec]"); first (simpl; lia).
        iIntros (?) "[_ [Hspec %]]".
        simpl.
        tp_pures j.
        wp_pures.
        case_bool_decide; wp_pures; tp_pures j.
        + by iApply "H3".
        + by iApply "H2".
      - by iApply "H1".
    }  
    eapply (ctx_refines_transitive) with
      (let, ("x","y") := ((rand #((q' + 1) * (s' + 1) - 1)%nat) ||| (rand #(((q' + 1) * (s' + 1) - p'' * r'' - 1))%nat))in 
       if: "x" < #(p''*r'')%nat then e3 else if: "y"<#(p''*(s'+1-r''))%nat then e2 else e1
      )%E.
    {
      start H1 H2 H3.
      wp_alloctape α as "Hα".
      wp_pures.
      wp_alloctape β as "Hβ".
      wp_pures.
      tp_bind j (_|||_)%E.
      iMod (tp_par with "[$]") as "(%j1&%j2&%K1&%K2&Hspec1&Hspec2&Hcont)".
      iMod (pupd_couple_associativity (p:=r'') (r:=p'') with "Hα Hβ Hspec1 Hspec2") as "(%resl&%resl'&%resr&%resr'&%&%&%&%&Hα&Hβ&Hspec1&Hspec2&%Hcond)"; [lia..|].
      simpl.
      iMod ("Hcont" with "[$]") as "Hspec".
      tp_pures j.
      case_bool_decide.
      - rewrite bool_decide_eq_true_2; last lia.
        tp_pures j.
        solve_subst.
        wp_randtape.
        wp_pures.
        rewrite bool_decide_eq_true_2; last lia.
        wp_pures.
        wp_randtape.
        wp_pures.
        rewrite bool_decide_eq_true_2; last lia.
        wp_pures.
        by iApply "H3".
      - rewrite bool_decide_eq_false_2; last lia.
        tp_pures j.
        solve_subst.
        case_bool_decide.
        + rewrite bool_decide_eq_true_2; last lia.
          tp_pures j.
          wp_pures.
          wp_randtape. wp_pures.
          rewrite bool_decide_eq_true_2; last lia.
          wp_pures.
          wp_randtape.
          wp_pures.
          rewrite bool_decide_eq_false_2; last lia.
          wp_pures.
          by iApply "H2".
        + rewrite bool_decide_eq_false_2; last lia.
          tp_pures j.
          wp_pures.
          wp_randtape. wp_pures.
          rewrite bool_decide_eq_false_2; last lia.
          wp_pures.
          by iApply "H1". }
    eapply (ctx_refines_transitive) with
      (let, ("α", "β") := (alloc #((q' + 1) * (s' + 1) - 1)%nat, alloc #(((q' + 1) * (s' + 1) - p'' * r'' - 1))%nat)in
       let, ("x","y") := ((rand("α") #((q' + 1) * (s' + 1) - 1)%nat) ||| (rand("β") #(((q' + 1) * (s' + 1) - p'' * r'' - 1))%nat))in 
       if: "x" < #(p''*r'')%nat then e3 else if: "y"<#(p''*(s'+1-r''))%nat then e2 else e1
      )%E.
    { start' H1 H2 H3.
      tp_allocnattape j β as "Hβ".
      tp_allocnattape j α as "Hα".
      do 9 tp_pure j.
      tp_bind j (_|||_)%E.
      iMod (tp_par with "[$]") as "(%j1&%j2&%K1&%K2&Hspec1&Hspec2&Hcont)".
      wp_pures.
      wp_apply (wp_par (λ v, ∃ (n:nat), ⌜v=#n⌝ ∗ j1⤇fill K1 v)%I (λ v, ∃ (n:nat), ⌜v=#n⌝ ∗ j2⤇fill K2 v)%I with "[Hspec1 Hα][Hspec2 Hβ]").
      - wp_apply (wp_couple_rand_rand_lbl with "[$]"); first (simpl; lia).
         iIntros (?) "[?[$?]]". by iExists _.
      - wp_apply (wp_couple_rand_rand_lbl with "[$]"); first (simpl; lia).
         iIntros (?) "[?[$?]]". by iExists _.
      - iIntros (??) "[(%&->&Hspec1)(%&->&Hspec2)]".
         iNext. wp_pures.
         iMod ("Hcont" with "[$]"). simpl.
         tp_pures j.
         solve_subst.
         case_bool_decide; wp_pures; tp_pures j; first by iApply "H3".
         case_bool_decide; wp_pures; tp_pures j; [by iApply "H2"|by iApply "H1"]. }
    remember ((q' + 1) * (s' + 1) - p'' * r'' - 1) as q1.
    remember (p'' * (s' + 1 - r'')) as p1.
    remember (p'' * r'') as r1.
    remember ((q' + 1) * (s' + 1) - 1)%nat as s1.
    eapply (ctx_refines_transitive) with
      (toss r1 s1 e3 (toss p1 q1 e2 e1) 
      )%E.
    { 
      start' H1 H2 H3.
      wp_alloctape β as "Hβ".
      wp_alloctape α as "Hα".
      wp_pures.
      rewrite /toss.
      tp_bind j (rand _)%E.
      iMod (pupd_couple_tape_rand with "[$][$]") as "(%n&Hα&Hspec&%)".
      { simpl; lia. }
      simpl.
      tp_pures j.
      case_bool_decide; tp_pures j.
      - wp_apply (wp_par (λ v, ⌜v=#n⌝)%I (λ _, True)%I with "[Hα][Hβ]").
        + by wp_randtape.
        + iMod (pupd_presample with "[$]") as "(%&?&?)". by wp_randtape.
        + iIntros (??) "[-> _]".
          iNext.
          wp_pures.
          rewrite bool_decide_eq_true_2; last lia.
          wp_pures.
          solve_subst.
          by iApply "H3".
      - tp_bind j (rand _)%E.
        iMod (pupd_couple_tape_rand with "[$Hβ][$]") as "(%n'&Hβ&Hspec&%)".
        { simpl; lia. }
        simpl.
        tp_pures j.
        wp_apply (wp_par (λ v, ⌜v=#n⌝)%I (λ v, ⌜v=#n'⌝)%I with "[Hα][Hβ]").
        + by wp_randtape.
        + by wp_randtape.
        + iIntros (??) "[-> ->]".
          iNext.
          wp_pures.
          case_bool_decide as H6; rewrite bool_decide_eq_false_2; try lia; solve_subst; wp_pures; tp_pures j.
          * rewrite bool_decide_eq_true_2; last lia.
            wp_pures.
            by iApply "H2".
          * rewrite bool_decide_eq_false_2; first (wp_pures; by iApply "H1").
            lia.
    }
    eapply (ctx_refines_transitive) with
        (toss (s1+1-r1) s1 (toss (q1+1-p1) q1 e1 e2) e3
        )%E.
    {
      start H1 H2 H3.
      rewrite /toss.
      assert (Bij (λ x, if bool_decide (x<=s1)%nat then s1-x else x)) as Hbij1.
      { clear. split.
        - intros x y.
          case_bool_decide; case_bool_decide; lia.
        - intros y. destruct (decide (y<=s1)).
          + exists (s1-y). rewrite bool_decide_eq_true_2; lia.
          + exists y. rewrite bool_decide_eq_false_2; lia.
      }
      assert (Bij (λ x, if bool_decide (x<=q1)%nat then q1-x else x)) as Hbij2.
      { clear. split.
        - intros x y.
          case_bool_decide; case_bool_decide; lia.
        - intros y. destruct (decide (y<=q1)).
          + exists (q1-y). rewrite bool_decide_eq_true_2; lia.
          + exists y. rewrite bool_decide_eq_false_2; lia.
      }
      tp_bind j (rand _)%E.
      unshelve wp_apply (wp_couple_rand_rand _ (λ x, if bool_decide (x<=s1)%nat then s1-x else x) with "[$]").
      { clear. intros. case_bool_decide; lia. }
      iIntros (?) "(%&Hspec)".
      simpl.
      wp_pures.
      rewrite bool_decide_eq_true_2; last lia.
      tp_pures j.
      case_bool_decide; last first.
      - rewrite bool_decide_eq_true_2; last (subst; lia).
        wp_pures.
        tp_pures j.
        by iApply "H3".
      - tp_pures j.
        rewrite bool_decide_eq_false_2; last (subst; lia).
        wp_pures.
      tp_bind j (rand _)%E.
      unshelve wp_apply (wp_couple_rand_rand _ (λ x, if bool_decide (x<=q1)%nat then q1-x else x) with "[$]").
      { clear. intros. case_bool_decide; lia. }
      iIntros (?) "(%H5&Hspec)".
      simpl.
      rewrite bool_decide_eq_true_2; last lia.
      wp_pures. tp_pures j.
      case_bool_decide as H6.
        + rewrite bool_decide_eq_false_2; last first.
          { clear -H6. lia. }
          wp_pures; tp_pures j.
          by iApply "H1".
        + rewrite bool_decide_eq_true_2; last first.
          { clear -H6 H5. lia. }
          wp_pures; tp_pures j.
          by iApply "H2".
    }
    subst.
    
    start H1 H2 H3.
    destruct (decide (r>0/\0<(((q+1)*(s+1))-p*r))) as [[]|Hn].
    - wp_apply (wp_toss_simplify with "[][][$]").
      2: { rewrite Nat.sub_add; last lia.
           rewrite Nat.sub_add; last lia. f_equal.
           rewrite (Nat.mul_comm (q+1)).
           by rewrite -Nat.mul_assoc. }
      { rewrite /gt.
        apply Nat.mul_pos_pos; lia. }
      { rewrite !Nat.sub_add; try lia.
        remember (q+1) as q'.
        remember(s+1) as s'.
        rewrite (Nat.mul_comm s' q').
        remember (q'*s'-p*r) as k eqn :Hk.
        rewrite {3}Hk.
        replace ((q' * s' - p * r - r * (q' - p))) with (q'*s'-r*q').
        { replace (q'*s'*k) with (k*(q'*s')) by lia.
          rewrite -Nat.mul_sub_distr_l.
          replace (q'*_*_) with (k*(q'*r)) by lia.
          f_equal.
          apply Nat.add_sub_eq_r.
          rewrite Nat.add_sub_assoc; first lia.
          rewrite Nat.mul_comm.
          apply Nat.mul_le_mono_l. lia.
        }
        apply Nat.add_sub_eq_r.
        rewrite -Nat.sub_add_distr.
        rewrite -Nat.add_sub_swap; last first. 
        - replace (p*r) with (r*p); last lia.
          rewrite -Nat.mul_add_distr_l.
          rewrite -Nat.le_add_sub; last lia.
          rewrite Nat.mul_comm.
          apply Nat.mul_le_mono_l. lia.
        - apply Nat.add_sub_eq_r.
          f_equal.
          rewrite Nat.mul_sub_distr_l.
          rewrite Nat.mul_comm.
          rewrite -Nat.le_add_sub; first lia.
          apply Nat.mul_le_mono_l. lia.
      }
      2:{ done. }
      2:{ by iIntros. }
      iModIntro.
      iIntros.
      + wp_apply (wp_toss_simplify with "[][][$]").
        2:{ f_equal.
            rewrite !Nat.sub_add; try lia.
            instantiate (1:= (r*((q+1)*(s+1)-p*r)) ).
            rewrite Nat.mul_assoc .
            rewrite (Nat.mul_comm (_*_-_)).
            rewrite -Nat.mul_sub_distr_r.
            f_equal.
            apply Nat.add_sub_eq_r.
            rewrite Nat.add_sub_assoc; last first.
            - apply Nat.le_add_le_sub_r.
              rewrite Nat.mul_comm.
              rewrite -Nat.mul_add_distr_r.
              rewrite Nat.sub_add; last lia.
              apply Nat.mul_le_mono_l.
              lia.
            - rewrite Nat.add_sub_assoc; last first.
              + apply Nat.mul_le_mono; lia.
              + rewrite Nat.add_comm.
                rewrite -Nat.sub_add_distr.
                apply Nat.add_sub_eq_r.
                f_equal.
                rewrite Nat.mul_sub_distr_l.
                rewrite Nat.mul_comm.
                rewrite -Nat.le_add_sub; first lia.
                apply Nat.mul_le_mono; lia.
        }
        { rewrite /gt.
          apply Nat.mul_pos_pos; lia.
        }
        { rewrite !(Nat.sub_add); try lia; last first.
          - assert (((q + 1) * (s + 1) - p * r) * ((q + 1) * (s + 1) - p * r - r * (q + 1 - p))<(q + 1) * (s + 1) * ((q + 1) * (s + 1) - p * r)); last lia.
            rewrite (Nat.mul_comm (_*_)) .
            apply Nat.mul_lt_mono_pos_l; first lia.
            rewrite -Nat.sub_add_distr.
            apply Nat.sub_lt.
            + rewrite Nat.mul_comm.
              rewrite -Nat.mul_add_distr_l.
              rewrite Nat.mul_comm.
              apply Nat.mul_le_mono; lia.
            + rewrite Nat.mul_comm.
              rewrite -Nat.mul_add_distr_l.
              apply Nat.mul_pos_pos; first lia.
              lia.
          - remember (q+1) as q'.
            remember (s+1) as s'.
            replace (q' * s' - p * r - r * (q' - p)) with (q'*s' - r *q'); last first.
            { rewrite -Nat.sub_add_distr. f_equal.
              rewrite (Nat.mul_comm _ r).
              rewrite -Nat.mul_add_distr_l. 
              f_equal. lia. 
            }
            rewrite Nat.mul_comm.
            rewrite -Nat.mul_sub_distr_l.
            replace ((q' * s' - (q' * s' - r * q'))) with (r*q'); last first. 
            { symmetry.
              apply Nat.add_sub_eq_r.
              rewrite Nat.add_sub_assoc; first lia.
              rewrite Nat.mul_comm.
              apply Nat.mul_le_mono_l. lia.
            }
            replace ((q' * s' - p * r - (q' * s' - r * q'))) with (r*q'-p*r); last first.
            { rewrite -Nat.sub_add_distr.
              apply Nat.add_sub_eq_r.
              rewrite Nat.add_sub_assoc; last first.
              - rewrite Nat.mul_comm.
                apply Nat.mul_le_mono; lia.
              - rewrite -Nat.add_sub_swap; last first.
                + assert (p*r <=r*q'); last lia.
                  rewrite Nat.mul_comm.
                  apply Nat.mul_le_mono; lia.
                + apply Nat.add_sub_eq_r.
                  rewrite Nat.add_sub_assoc; first lia.
                  trans (q'*s'); last lia.
                  rewrite Nat.mul_comm.
                  apply Nat.mul_le_mono; lia.
            }
            rewrite -Nat.mul_sub_distr_l.
            replace (_-(_-_)) with (p*r); first lia.
            symmetry.
            apply Nat.add_sub_eq_r.
            rewrite -Nat.le_add_sub; first done.
            rewrite Nat.mul_comm.
            apply Nat.mul_le_mono; lia.
        }
        { done. }
        { done. }
        { by iIntros. }
    - apply not_and_or_not in Hn as [|].
      + replace (r) with 0 by lia.
        replace ((((q + 1) * (s + 1) - 1 + 1) * ((q + 1) * (s + 1) - p * 0 - 1 + 1) - 1 + 1 -
                    ((q + 1) * (s + 1) - 1 + 1 - p * 0) * ((q + 1) * (s + 1) - p * 0 - 1 + 1 - 0 * (q + 1 - p)))) with 0 by lia.
        rewrite /toss.
        wp_apply wp_rand; first done.
        tp_bind j (rand _)%E.
        iIntros.
        iMod (pupd_rand with "[$]") as "(%&?&%)".
        simpl.
        tp_pures j.
        wp_pures.
        rewrite !bool_decide_eq_false_2; try lia.
        tp_pures j. wp_pures.
        by iApply "H3".
      + assert ((q + 1) * (s + 1) - p * r=0) as Heq by lia.
        rewrite Heq.
        apply Nat.sub_0_le in Heq.
        simpl.
        rewrite !Nat.mul_1_r.
        rewrite !Nat.sub_add; try lia.
        replace (((q + 1) * (s + 1) - p * r)) with 0 by lia.
        simpl.
        rewrite !Nat.sub_0_r.
        destruct (decide (r=s+1)); last first.
        { assert (r<s+1) by lia.
          exfalso.
          revert Heq.
          apply Nat.lt_nge.
          apply Nat.lt_le_trans with (p*(s+1)).
          - apply Nat.mul_lt_mono_pos_l; lia.
          - apply Nat.mul_le_mono_nonneg; lia.
        }
        subst.
        destruct (decide (p=q+1)); last first.
        { assert (p<q+1) by lia.
          exfalso.
          revert Heq.
          apply Nat.lt_nge.
          apply Nat.mul_lt_mono_pos_r; lia.
        }
        subst. 
        rewrite /toss.
        wp_apply wp_rand; first done.
        tp_bind j (rand _)%E.
        iIntros.
        iMod (pupd_rand with "[$]") as "(%&?&%)".
        simpl.
        tp_pures j.
        wp_pures.
        rewrite !bool_decide_eq_true_2; try lia.
        tp_pures j. wp_pures.
        wp_apply wp_rand; first done.
        tp_bind j (rand _)%E.
        iIntros.
        iMod (pupd_rand with "[$]") as "(%&?&%)".
        simpl.
        tp_pures j.
        wp_pures.
        rewrite !bool_decide_eq_true_2; try lia.
        tp_pures j. wp_pures.
        by iApply "H1".
  Qed. 
  
  Lemma eq3 :
    ∅ ⊢ₜ e1 : τ -> ∅ ⊢ₜ e2 : τ -> ∅ ⊢ₜ e3 : τ ->
              ∅ ⊨ toss r s (toss p q e1 e2) e3 =ctx= toss (p*r) ((q+1)*(s+1)-1) e1 (toss (r*(q+1-p)) ((q+1)*(s+1)-p*r-1) e2 e3): τ.
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
