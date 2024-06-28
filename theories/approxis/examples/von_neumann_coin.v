(* Our old friend, the Von Neumann coin, but now with approximate refinements!*)
From clutch Require Export approxis.
Set Default Proof Using "Type*".

Section proofs.

  Context `{!approxisRGS Σ}.


  (* die from 3 coins with early abort *)
  Definition vnd_tapes : expr :=
    (rec: "f" <> :=
       let: "α" := alloc #1 in
       let: "b0" := rand("α") #1 in
       let: "b1" := rand("α") #1 in
       if: (("b0" = #1) `and` ("b1" = #1))
             then "f" #()
             else (let: "b2" := rand("α") #1 in
                  let: "r" := (#4*"b2" + #2*"b1" + "b0") in
                  if: "r" < #6 then "r" else "f" #()))%V.

  Definition rej_tapes : expr :=
    (rec: "f" <> :=
       let: "β" := alloc #7 in
       let: "r" := rand("β") #7 in
       if: "r" < #6 then "r" else "f" #())%V.

  Definition die_tapes : expr :=
    (let: "γ" := alloc #5 in λ:<>, rand("γ") #5)%E.

  Lemma vnd_ref_rej :
    ⊢ (REL (vnd_tapes) << (rej_tapes) : lrel_unit → lrel_int).
  Proof.
    rewrite /vnd_tapes /rej_tapes.
    iApply (refines_arrow_val).
    iModIntro.
    iLöb as "IH".
    iIntros (v1 v2) "Hv1v2".
    rel_pures_l.
    rel_pures_r.
    rel_alloctape_l α as "Hα".
    rel_alloctape_r β as "Hβ".
    rel_pures_l.
    rel_pures_r.
    iApply (refines_couple_exp_decoder_lr 7 1 3 [] [] α β); [by simpl |].
    iFrame.
    iIntros (l m) "%Hfa %Hm %Hlen Hα Hβ /=".
    destruct l as [|a1 l]; [inversion Hlen |].
    destruct l as [|a2 l]; [inversion Hlen |].
    destruct l as [|a3 l]; [inversion Hlen |].
    destruct l as [|a4 l]; [|inversion Hlen].
    rewrite /fin.decoder_nat/=.
    rewrite !Nat.add_0_r.
    replace (a1 + (a2 + (a3 + a3) + (a2 + (a3 + a3)))) with (4*a3 + 2*a2 + a1) by lia.
    rel_rand_l. iIntros "Ha1".
    rel_rand_l. iIntros "Ha2".
    do 4 rel_pure_l.
    destruct( decide (a1 = 1 /\ a2 = 1)) as [ [-> ->] | Ha1a2].
    - do 2 rel_pure_l.
      rel_rand_r.
      iIntros "Hr".
      rel_pures_r.
      rewrite bool_decide_eq_false_2; [|lia].
      rel_pure_r.
      by rel_apply "IH".
    - rel_pures_l.
      replace (#(bool_decide (#a1 = #1) && bool_decide (#a2 = #1))%bool) with (#false); last first.
      {
        do 2 f_equal.
        apply not_and_l in Ha1a2 as [H1|H2].
        - rewrite {1}bool_decide_eq_false_2; auto.
          intro H. injection.

      Search and not.
      rewrite bool_decide_eq_false_2.
      rel_rand_l. iIntros "Ha3".
      rel_pures_l.
      rel_rand_r.
      iIntros "Hr".
    rel_pures_r.
    case_bool_decide as H1.
    - case_bool_decide as H2; [|lia].
      rel_pures_l. rel_pures_r.
      rel_values. iPureIntro.
      simpl.
      exists (4 * a3 + 2 * a2 + a1).
      split; auto.
      do 2 f_equal; simpl.
      rewrite !Nat2Z.inj_add /=. lia.
    - case_bool_decide; [lia|].
      rel_pure_l. rel_pure_r.
      by rel_apply "IH".
  Qed.

  Lemma rej_ref_vnd :
   ⊢ REL (rej_tapes) << (vnd_tapes) : lrel_unit → lrel_int.
  Proof.
    rewrite /vnd_tapes /rej_tapes.
    iApply (refines_arrow_val).
    iModIntro.
    iLöb as "IH".
    iIntros (v1 v2) "Hv1v2".
    rel_pures_l.
    rel_pures_r.
    rel_alloctape_r α as "Hα".
    rel_alloctape_l β as "Hβ".
    rel_pures_l.
    rel_pures_r.
    iApply (refines_couple_exp_decoder_rev 7 1 3 [] [] β α); [by simpl|].
    iFrame.
    iIntros (l m) "%Hfa %Hm %Hlen Hα Hβ".
    destruct l as [|b1 l]; [inversion Hlen |].
    destruct l as [|b2 l]; [inversion Hlen |].
    destruct l as [|b3 l]; [inversion Hlen |].
    destruct l as [|b4 l]; [|inversion Hlen].
    rewrite /fin.decoder_nat/=.
    rewrite !Nat.add_0_r.
    replace (b1 + (b2 + (b3 + b3) + (b2 + (b3 + b3)))) with (4*b3 + 2*b2 + b1) by lia.
    rel_rand_r. iIntros "Hb1".
    rel_rand_r. iIntros "Hb2".
    rel_rand_r. iIntros "Hb3".
    rel_pures_r.
    rel_rand_l.
    iIntros "Hr".
    rel_pures_l.
    case_bool_decide.
    - case_bool_decide; [|lia].
      rel_pures_l. rel_pures_r.
      rel_values. iPureIntro.
      simpl.
      exists (4 * b3 + 2 * b2 + b1).
      split; auto.
      do 2 f_equal; simpl.
      rewrite !Nat2Z.inj_add /=. lia.
    - case_bool_decide; [lia|].
      rel_pure_l. rel_pure_r.
      by rel_apply "IH".
  Qed.


  Lemma rej_ref_die :
    ⊢ REL (rej_tapes) << (die_tapes) : lrel_unit → lrel_int.
  Proof.
    rewrite /rej_tapes /die_tapes.
    rel_alloctape_r γ as "Hγ".
    rel_pures_r.
    iApply (refines_na_alloc (γ ↪ₛN (Z.to_nat 5; []))%I (nroot.@"coins")); iFrame.
    iIntros "#Hinv".
    rel_arrow.
    iIntros (v1 v2) "#Hv1v2".
    rel_pures_l.
    iLöb as "IH".
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "[>Hγ Hclose]".
    rel_alloctape_l β as "Hβ".
    rel_pures_l.
    replace (Z.to_nat 5) with 5 by lia.
    replace (Z.to_nat 7) with 7 by lia.
    iApply (refines_couple_TT_frag 7 5 (λ x,x)); [lia|lia|..]. iFrame.
    iIntros (n) "%Hn".
    case_bool_decide as H.
    - iIntros (m) "(Hβ & Hγ & % & %)".
      simpl.
      rel_rand_l. iIntros "%".
      rel_pures_l.
      rel_pures_r.
      rel_rand_r. iIntros "%".
      rewrite bool_decide_eq_true_2; last by lia.
      rel_pures_l.
      iApply (refines_na_close with "[-]").
      iFrame.
      iSplitL; auto.
      rel_values.
    - iIntros "[Hβ [Hγ %]]".
      simpl.
      rel_rand_l. iIntros "%".
      rel_pures_l.
      rewrite bool_decide_eq_false_2; last first.
      {
        intros ?.
        apply H.
        exists n. lia.
      }
      rel_pures_l.
      iApply (refines_na_close with "[-]").
      iFrame.
      iSplitL; auto.
  Qed.



  Lemma die_ref_rej :
    ⊢ REL (die_tapes) << (rej_tapes) : lrel_unit → lrel_int.
  Proof.
    rewrite /rej_tapes /die_tapes.
    rel_alloctape_l γ as "Hγ".
    rel_pures_l.
    iApply (refines_na_alloc (γ ↪N (Z.to_nat 5; []))%I (nroot.@"coins")); iFrame.
    iIntros "#Hinv".
    iApply (refines_arrow_val_err _ _ _ _ (8%nat / (8%nat - 6%nat)));
      first by (simpl; lra).
    iModIntro.
    iIntros (ε) "%Hpos #IH Herr".
    iIntros (v1 v2) "#Hv1v2".
    iApply (refines_na_inv with "[$Hinv Herr Hv1v2]"); [done |].
    iIntros "[>Hγ Hclose]".
    rel_alloctape_r β as "Hβ".
    rel_pures_r.
    iApply (refines_couple_TT_adv 5 7 (λ x, x));
      [| lia | lia | iFrame]; [lra |].
    iIntros (m) "%".
    case_bool_decide.
    - iIntros (n) "(Hγ & Hβ & % & %)".
      simpl.
      rel_pures_l.
      rel_rand_l; iIntros "%".
      rel_rand_r; iIntros "%".
      rel_pures_r.
      iApply (refines_na_close with "[-]").
      iFrame.
      iSplitL; auto.
      rewrite bool_decide_eq_true_2; last by lia.
      rel_pures_r.
      rel_values.
    - iIntros (ε') "(-> & Hγ & Hβ & Herr & %)".
      iApply (refines_na_close with "[-]").
      iFrame.
      iSplitL "Hγ"; auto.
      rel_rand_r; iIntros "%".
      rel_pures_r.
      rewrite bool_decide_eq_false_2; last first.
      {
        intros ?.
        apply H0.
        exists m. lia.
      }
      rel_pure_r.
      iApply ("IH" with "[$Herr]").
      iDestruct "Hv1v2" as (?) "?".
      done.
  Qed.


End proofs.

Lemma vnd_equiv_die:
  ∅ ⊨ vnd_tapes =ctx= die_tapes: TUnit → TInt.
Proof.
  assert (approxisRGpreS approxisRΣ).
  { apply subG_approxisRGPreS. apply subG_refl. }
  split.
  - eapply ctx_refines_transitive.
    + eapply refines_sound; eauto.
      iIntros. iApply vnd_ref_rej.
    + eapply refines_sound; eauto.
      iIntros. iApply rej_ref_die.
  - eapply ctx_refines_transitive.
    + eapply refines_sound; eauto.
      iIntros. iApply die_ref_rej.
    + eapply refines_sound; eauto.
      iIntros. iApply rej_ref_vnd.
Qed.
