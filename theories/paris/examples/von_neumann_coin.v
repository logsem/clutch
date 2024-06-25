(* Our old friend, the Von Neumann coin, but now with approximate refinements!*)
From clutch Require Export paris lib.flip.
Set Default Proof Using "Type*".

Section proofs.

  Context `{!parisRGS Σ}.


  (* Von Neumann die *)
  Definition vnd_tapes : expr :=
    (rec: "f" <> :=
       let: "α" := alloc #1 in
       let: "b0" := rand("α") #1 in
       let: "b1" := rand("α") #1 in
       let: "b2" := rand("α") #1 in
       let: "r" := (#4*"b0" + #2*"b1" + "b2") in
       if: "r" < #6 then "r" else "f" #())%V.

  Definition rej_tapes : expr :=
    (rec: "f" <> :=
       let: "β" := alloc #7 in
       let: "r" := rand("β") #7 in
       if: "r" < #6 then "r" else "f" #())%V.

  Definition die_tapes : expr :=
    (let: "γ" := alloc #5 in λ:<>, rand("γ") #5)%E.

  Fixpoint bin_to_oct (l : list nat) : nat :=
    match l with
    | [b0; b1; b2] => (4*b0 + 2*b1 + b2)
    | _ => 0
    end.

  Lemma destr_fin2 (x : fin 2): {x = 0%fin} + {x = 1%fin}.
  Proof.
    inv_fin x; auto.
    intros x.
    inv_fin x; auto.
    intros x.
    inv_fin x; auto.
  Qed.

  (* Shame on me *)
  Lemma destr_fin6 (x : fin 6):
    x = 0%fin \/ x = 1%fin \/ x = 2%fin \/ x = 3%fin \/ x = 4%fin \/ x = 5%fin.
  Proof.
    inv_fin x; auto; intros x.
    inv_fin x; auto; intros x.
    inv_fin x; auto; intros x.
    inv_fin x; auto; intros x.
    inv_fin x; [right;right;auto| ]; intros x.
    inv_fin x; [right;right;auto| ]; intros x.
    inv_fin x.
  Qed.

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
    iApply (refines_couple_exp 7 1 3 bin_to_oct).
    {
      intros l Hl.
      unfold bin_to_oct; simpl.
      destruct l; simpl; [lia |].
      destruct l; simpl; [lia |].
      destruct l; simpl; [lia |].
      destruct l; simpl; [ |lia].
      apply Forall_cons_1 in Hl as [? Hl].
      apply Forall_cons_1 in Hl as [? Hl].
      apply Forall_cons_1 in Hl as [? Hl].
      lia.
    }
    {
      rewrite /bin_to_oct /length.
      intros l1 l2 Hl1 Hl2 Hl1l2.
      destruct l1; simpl; [lia |].
      destruct l1; simpl; [lia |].
      destruct l1; simpl; [lia |].
      destruct l1; simpl; [|lia].
      destruct l2; simpl; [lia |].
      destruct l2; simpl; [lia |].
      destruct l2; simpl; [lia |].
      destruct l2; simpl; [|lia].
      destruct l; simpl; [lia |].
      destruct l; simpl; [lia |].
      destruct l; simpl; [ |lia].

    }
    {
      intros l1 l2 Hl1 Hl2 Heq.
      destruct l1 as [|a1 l1]; [inversion Hl1 |].
      destruct l1 as [|a2 l1]; [inversion Hl1 |].
      destruct l1 as [|a3 l1]; [inversion Hl1 |].
      destruct l1 as [|]; [|inversion Hl1].
      destruct l2 as [|b1 l2]; [inversion Hl2 |].
      destruct l2 as [|b2 l2]; [inversion Hl2 |].
      destruct l2 as [|b3 l2]; [inversion Hl2 |].
      destruct l2 as [|]; [|inversion Hl2].
      rewrite /bin_to_oct /= /fin.fin_force in Heq.
      apply (list_fmap_eq_inj fin_to_nat).
      - apply fin_to_nat_inj.
      - simpl.
      destruct ( destr_fin2 a1) ;
      destruct ( destr_fin2 a2) ;
      destruct ( destr_fin2 a3) ;
      destruct ( destr_fin2 b1) ;
      destruct ( destr_fin2 b2) ;
      destruct ( destr_fin2 b3); simplify_eq; auto.
    }
    iFrame.
    iIntros (l m) "[%Hl %Heq] Hα Hβ".
    simpl.
    destruct l as [|a1 l]; [inversion Hl |].
    destruct l as [|a2 l]; [inversion Hl |].
    destruct l as [|a3 l]; [inversion Hl |].
    destruct l as [|]; [|inversion Hl].
    rewrite /bin_to_oct /= in Heq.
    do 3 rel_rand_l.
    rel_pures_l.
    rel_rand_r.
    rel_pures_r.
    rewrite -Heq.
    rewrite /fin.fin_force.
    case_bool_decide as H1.
    - case_bool_decide as H2.
      + rel_pures_l. rel_pures_r.
        destruct ( destr_fin2 a1) ;
        destruct ( destr_fin2 a2) ;
          destruct ( destr_fin2 a3) ; simplify_eq; simpl; rel_values.
      + exfalso.
        apply H2.
        destruct ( destr_fin2 a1) ;
        destruct ( destr_fin2 a2) ;
        destruct ( destr_fin2 a3) ; simplify_eq; simpl; simpl in H1; lia.
    - case_bool_decide as H2.
      + exfalso.
        apply H1.
        destruct ( destr_fin2 a1) ;
        destruct ( destr_fin2 a2) ;
        destruct ( destr_fin2 a3) ; simplify_eq; simpl; simpl in H2; lia.
      + rel_pure_l. rel_pure_r.
        rel_apply "IH".
        auto.
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
    iApply (refines_couple_exp_rev 7 1 3 bin_to_oct); [|simpl; done|].
    {
      intros l1 l2 Hl1 Hl2 Heq.
      destruct l1 as [|a1 l1]; [inversion Hl1 |].
      destruct l1 as [|a2 l1]; [inversion Hl1 |].
      destruct l1 as [|a3 l1]; [inversion Hl1 |].
      destruct l1 as [|]; [|inversion Hl1].
      destruct l2 as [|b1 l2]; [inversion Hl2 |].
      destruct l2 as [|b2 l2]; [inversion Hl2 |].
      destruct l2 as [|b3 l2]; [inversion Hl2 |].
      destruct l2 as [|]; [|inversion Hl2].
      rewrite /bin_to_oct /= /fin.fin_force in Heq.
      apply (list_fmap_eq_inj fin_to_nat).
      - apply fin_to_nat_inj.
      - simpl.
      destruct ( destr_fin2 a1) ;
      destruct ( destr_fin2 a2) ;
      destruct ( destr_fin2 a3) ;
      destruct ( destr_fin2 b1) ;
      destruct ( destr_fin2 b2) ;
      destruct ( destr_fin2 b3); simplify_eq; auto.
    }
    iFrame.
    iIntros (l m) "[%Hl %Heq] Hα Hβ".
    simpl.
    destruct l as [|a1 l]; [inversion Hl |].
    destruct l as [|a2 l]; [inversion Hl |].
    destruct l as [|a3 l]; [inversion Hl |].
    destruct l as [|]; [|inversion Hl].
    rewrite /bin_to_oct /= in Heq.
    do 3 rel_rand_r.
    rel_pures_r.
    rel_rand_l.
    rel_pures_l.
    rewrite -Heq.
    rewrite /fin.fin_force.
    case_bool_decide as H1.
    - case_bool_decide as H2.
      + rel_pures_l. rel_pures_r.
        destruct ( destr_fin2 a1) ;
        destruct ( destr_fin2 a2) ;
          destruct ( destr_fin2 a3) ; simplify_eq; simpl; rel_values.
      + exfalso.
        apply H2.
        destruct ( destr_fin2 a1) ;
        destruct ( destr_fin2 a2) ;
        destruct ( destr_fin2 a3) ; simplify_eq; simpl; simpl in H1; lia.
    - case_bool_decide as H2.
      + exfalso.
        apply H1.
        destruct ( destr_fin2 a1) ;
        destruct ( destr_fin2 a2) ;
        destruct ( destr_fin2 a3) ; simplify_eq; simpl; simpl in H2; lia.
      + rel_pure_l. rel_pure_r.
        rel_apply "IH".
        auto.
  Qed.


  Lemma rej_ref_die :
    ⊢ REL (rej_tapes) << (die_tapes) : lrel_unit → lrel_int.
  Proof.
    rewrite /rej_tapes /die_tapes.
    rel_alloctape_r γ as "Hγ".
    rel_pures_r.
    iApply (refines_na_alloc (γ ↪ₛ (Z.to_nat 5; []))%I (nroot.@"coins")); iFrame.
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
    iApply (refines_couple_TT_frag 7 5 (λ (x : fin 6), fin.fin_force 7 (fin_to_nat x)));
      first by lia.
    iFrame.
    iIntros (n).
    case_bool_decide as H.
    - iIntros (m) "[Hβ [Hγ %Heq]]".
      simpl.
      rel_rand_l.
      rel_pures_l.
      rel_pures_r.
      rel_rand_r.
      case_bool_decide as H1.
      + rel_pures_l.
        rewrite -Heq.
        iApply (refines_na_close with "[-]").
        iFrame.
        iSplitL; auto.
        rel_values.
        iModIntro.
        iExists m.
        iPureIntro; split; auto.
        f_equal.
        rewrite /fin.fin_force.
        pose proof (fin_to_nat_lt m).
        case_match.
        * lia.
        * do 2 f_equal.
          rewrite fin_to_nat_to_fin //.
      + exfalso.
        apply H1.
        destruct H as [x <-].
        rewrite /fin.fin_force.
        pose proof (fin_to_nat_lt x).
        case_match.
        * lia.
        * rewrite fin_to_nat_to_fin //.
          lia.
    - iIntros "[Hβ Hγ]".
      simpl.
      rel_rand_l.
      rel_pures_l.
      case_bool_decide as H2.
      + exfalso.
        assert (n < 6)%nat as H3 by lia.
        apply H.
        exists (Fin.of_nat_lt H3).
        rewrite /fin.fin_force.
        (* Shame on me *)
        inv_fin n; auto; intros n.
        inv_fin n; auto; intros n.
        inv_fin n; auto; intros n.
        inv_fin n; auto; intros n.
        inv_fin n; auto; intros n.
        inv_fin n; auto; intros n.
        inv_fin n; auto; intros n.
        * intros H. simpl in H. lia.
        * intros.
          inv_fin n; auto.
          ** intros ? H. simpl in H. lia.
          ** intros n. inv_fin n.
      + rel_pures_l.
        iApply (refines_na_close with "[-]").
        iFrame.
        iSplitL; auto.
  Unshelve.
  rewrite /fin.fin_force.
  intros x y Hxy.
  pose proof (fin_to_nat_lt x).
  pose proof (fin_to_nat_lt y).
  case_match; [lia |].
  case_match; [lia |].
  (* Shame on me *)
  destruct (destr_fin6 x) as [-> | [-> | [-> | [-> | [-> | ->]]]]];
  destruct (destr_fin6 y) as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    try inversion Hxy; auto.
  Qed.



  Lemma die_ref_rej :
    ⊢ REL (die_tapes) << (rej_tapes) : lrel_unit → lrel_int.
  Proof.
    rewrite /rej_tapes /die_tapes.
    rel_alloctape_l γ as "Hγ".
    rel_pures_l.
    iApply (refines_na_alloc (γ ↪ (Z.to_nat 5; []))%I (nroot.@"coins")); iFrame.
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
    iApply (refines_couple_TT_adv 5 7 (λ (x : fin 6), fin.fin_force 7 (fin_to_nat x)));
      [| | iFrame]; [lra | lia |].
    iIntros (m).
    case_bool_decide.
    - iIntros (n) "[Hγ [Hβ %Heq]]".
      simpl.
      rel_pures_l.
      rel_rand_l.
      rel_rand_r.
      rel_pures_r.
      iApply (refines_na_close with "[-]").
      iFrame.
      iSplitL; auto.
      case_bool_decide as H2.
      + rel_pures_r.
        rel_values.
        iExists m.
        iModIntro.
        iPureIntro.
        split; auto.
        f_equal.
        rewrite /fin.fin_force in Heq.
        pose proof (fin_to_nat_lt n).
        case_match.
        * lia.
        * rewrite -Heq.
          do 2 f_equal.
          rewrite fin_to_nat_to_fin //.
      + exfalso.
        apply H2.
        destruct H as [x <-].
        rewrite /fin.fin_force.
        pose proof (fin_to_nat_lt x).
        case_match.
        * lia.
        * rewrite fin_to_nat_to_fin //.
          lia.
    - iIntros (ε') "(-> & Hγ & Hβ & Herr)".
      iApply (refines_na_close with "[-]").
      iFrame.
      iSplitL "Hγ"; auto.
      rel_rand_r.
      rel_pures_r.
      case_bool_decide as H2.
      + exfalso.
        assert (m < 6)%nat as H3.
        { inv_fin m; auto; simpl; try lia. }
        apply H.
        exists (Fin.of_nat_lt H3).
        rewrite /fin.fin_force.
        (* Shame on me *)
        inv_fin m; auto; intros m.
        inv_fin m; auto; intros m.
        inv_fin m; auto; intros m.
        inv_fin m; auto; intros m.
        inv_fin m; auto; intros m.
        inv_fin m; auto; intros m.
        inv_fin m; auto; intros m.
        * intros H. simpl in H. lia.
        * intros.
          inv_fin m; auto.
          ** intros ? H. simpl in H. lia.
          ** intros m. inv_fin m.
      + rel_pure_r.
        iApply ("IH" with "[$Herr]").
        iDestruct "Hv1v2" as (?) "?".
        done.
        Unshelve.
  rewrite /fin.fin_force.
  intros x y Hxy.
  pose proof (fin_to_nat_lt x).
  pose proof (fin_to_nat_lt y).
  case_match; [lia |].
  case_match; [lia |].
  (* Shame on me *)
  destruct (destr_fin6 x) as [-> | [-> | [-> | [-> | [-> | ->]]]]];
  destruct (destr_fin6 y) as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    try inversion Hxy; auto.
  Qed.


End proofs.
