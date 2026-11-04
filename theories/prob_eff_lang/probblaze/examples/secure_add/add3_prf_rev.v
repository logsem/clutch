From iris.proofmode Require Import base proofmode classes.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def.
From clutch.prob_eff_lang.probblaze.examples.secure_add Require Import
  add_corrupt_C_bijection add3_def add3_tbl add3_net add3_party add3_prf.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.
Import valgroup_tactics.

(** * The security proof, mirrored: the ideal world refines the real one

    The same argument as in [add3_prf], with the ideal world (F_ADD3 and the
    simulator) on the left and the real protocol on the right.  The ghost
    state still records the real world's inputs and samples. *)

Section code_rev.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  Lemma brel_prod3_l K (ℓ0 ℓ1 ℓ2 : loc) o0 o1 o2 e2 E L R :
    ℓ0 ↦ optvg o0 -∗ ℓ1 ↦ optvg o1 -∗ ℓ2 ↦ optvg o2 -∗
    (ℓ0 ↦ optvg o0 -∗ ℓ1 ↦ optvg o1 -∗ ℓ2 ↦ optvg o2 -∗
       BREL fill K (optvg (prod_opt o0 o1 o2)) ≤ e2 @ E <|L|> {{R}}) -∗
    BREL fill K (prod3 (#ℓ0, #ℓ1, #ℓ2)%V) ≤ e2 @ E <|L|> {{R}}.
  Proof using All.
    iIntros "H0 H1 H2 H". rewrite /prod3. brel_pures_l.
    brel_load_l. rewrite fill_app /=.
    destruct o0 as [a|]; rewrite /optvg; brel_pures_l; last by iApply ("H" with "H0 H1 H2").
    brel_load_l. rewrite fill_app /=.
    destruct o1 as [b|]; brel_pures_l; last by iApply ("H" with "H0 H1 H2").
    brel_load_l. rewrite fill_app /=.
    destruct o2 as [d|]; brel_pures_l; last by iApply ("H" with "H0 H1 H2").
    rewrite -(fill_app K [InjRCtx; AppLCtx (vgval d); AppRCtx vmult] (vmult (vgval a) (vgval b))).
    iApply brel_mult_l. rewrite fill_app /=.
    rewrite -(fill_app K [InjRCtx] (vmult (vgval (a * b)) (vgval d))).
    iApply brel_mult_l. rewrite fill_app /=. brel_pures_l.
    by iApply ("H" with "H0 H1 H2").
  Qed.

End code_rev.

Section prf_rev.
  Context `{!probblazeRGS Σ, !inG Σ (dfrac_agreeR valO)}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Context (c : nat) (Hc : (c < 3)%nat).
  Context (γx : Z → gname) (γr : Z → Z → gname).
  Local Open Scope Z_scope.

  Local Notation xk := (xk γx).
  Local Notation Rmsg_rev := (Rmsg_rev c γx γr).
  Local Notation Rdeliv_rev := (Rdeliv_rev c γx γr).
  Local Notation NetT l1 l2 := (NetThy Rmsg_rev Rdeliv_rev l1 l2).

  Section state_rev.
    (* F_ADD3's inputs and the simulator's δ and [x_c] (left), Π's started
       flags (right). *)
    Context (ℓs0 ℓs1 ℓs2 ℓx0 ℓx1 ℓx2 ℓδ ℓxc : loc).
    Local Notation party_toks := (party_toks γx γr).

    Definition pstate_rev (j : Z) (o : option vgG) : iProp Σ :=
      sel ℓs0 ℓs1 ℓs2 j ↦ₛ #(bool_decide (is_Some o)) ∗ sel ℓx0 ℓx1 ℓx2 j ↦ optvg o ∗
      match o with None => party_toks j | Some x => xk j x end.

    Definition start_inv_rev : iProp Σ :=
      ∃ o : Z → option vgG,
        pstate_rev 0 (o 0) ∗ pstate_rev 1 (o 1) ∗ pstate_rev 2 (o 2) ∗
        (∃ v, ℓxc ↦ v ∗ ⌜∀ x, o (cz c) = Some x → v = vgval x⌝) ∗
        (∃ v, ℓδ ↦ v ∗ ⌜∀ a b, o (hz c) = Some a → o (hz' c) = Some b →
                          is_Some (o (cz c)) → v = vgval (a * b)%g⌝).

    Global Instance pstate_rev_timeless j o : Timeless (pstate_rev j o).
    Proof. rewrite /pstate_rev. destruct o; apply _. Qed.

    Lemma pstates_take_rev o j :
      0 ≤ j < 3 →
      pstate_rev 0 (o 0) ∗ pstate_rev 1 (o 1) ∗ pstate_rev 2 (o 2) ⊢
      pstate_rev j (o j) ∗
      (∀ o', pstate_rev j o' -∗
         pstate_rev 0 (upd o j o' 0) ∗ pstate_rev 1 (upd o j o' 1) ∗ pstate_rev 2 (upd o j o' 2)).
    Proof using Hc.
      iIntros (Hj) "(H0 & H1 & H2)". rewrite /upd.
      assert (j = 0 ∨ j = 1 ∨ j = 2) as [ -> | [ -> | -> ] ] by (clear -Hj; lia);
        iFrame; iIntros (o') "H"; repeat case_bool_decide; try lia; iFrame.
    Qed.

    Lemma pstate_rev_known j o x : pstate_rev j o -∗ xk j x -∗ ⌜o = Some x⌝.
    Proof using.
      iIntros "(_ & _ & Ho) Hx". destruct o as [x'|].
      - by iDestruct (xk_agree with "Ho Hx") as %->.
      - iDestruct "Ho" as "[Ht _]". by iDestruct (slot_tok_excl with "Ht Hx") as %[].
    Qed.

    Lemma pstates_rev_known o j x :
      0 ≤ j < 3 →
      pstate_rev 0 (o 0) -∗ pstate_rev 1 (o 1) -∗ pstate_rev 2 (o 2) -∗ xk j x -∗
      ⌜o j = Some x⌝ ∗ pstate_rev 0 (o 0) ∗ pstate_rev 1 (o 1) ∗ pstate_rev 2 (o 2).
    Proof using.
      iIntros (Hj) "H0 H1 H2 #Hx".
      assert (j = 0 ∨ j = 1 ∨ j = 2) as [ -> | [ -> | -> ] ] by (clear -Hj; lia).
      - iDestruct (pstate_rev_known with "H0 Hx") as %?. by iFrame.
      - iDestruct (pstate_rev_known with "H1 Hx") as %?. by iFrame.
      - iDestruct (pstate_rev_known with "H2 Hx") as %?. by iFrame.
    Qed.

    Local Notation patch_v := (patch_v c ℓδ).

    Lemma patch_ok_rev N L :
      na_invP N start_inv_rev ⊢
      patch_spec L patch_v (λ: "s" "d" "t" "m", "m")%V Rmsg_rev Rdeliv_rev.
    Proof using All.
      iIntros "#Hinv !>" (l1s l2s k1 k2 s d t m1 m2 S Hk1 Hk2 Hhdr) "#Hm Hk".
      rewrite /patch_v. brel_pures.
      iDestruct "Hm" as (s' d' t' m m') "((%Hhdr' & %Hkey & -> & ->) & #Hl & #Hadj)".
      destruct (key_inj _ _ _ _ _ _ Hhdr Hhdr' Hkey) as (<- & <- & <-).
      destruct (roles_spec c Hc) as (Hcn & Hcn2 & Hhn & Hhn2 & Hh'n & Hh'n2 & Hhc & Hh'c & Hh'h & Hcr & Hhr & Hh'r).
      destruct (decide ((s, d, t) = (hz c, cz c, 1))) as [[= -> -> ->] | Hne].
      - (* [h]'s sum to [c]: the patch multiplies by [δ = x_h · x_{h'}] *)
        rewrite /Sum. brel_pures. rewrite !bool_decide_eq_true_2 //. brel_pures.
        rewrite !bool_decide_eq_true_2 //. brel_pures.
        rewrite /add3_party.raw_adj (bool_decide_eq_false_2 (_ = (hz' c, hz c, 0))); last by intros [=].
        rewrite bool_decide_eq_true_2 //.
        iDestruct "Hadj" as (x x') "(#Hx & #Hx' & ->)".
        iAssert (∃ xq, xk (cz c) xq)%I as (xq) "#Hxq".
        { iEval (rewrite /add3_party.lval bool_decide_eq_false_2 //) in "Hl".
          iDestruct "Hl" as (? ? xq ? ? ? ?) "(_ & _ & #H & _)". iExists xq. by rewrite -Hhn2. }
        iApply (brel_na_inv _ _ N); first set_solver. iFrame "Hinv".
        iIntros "[(%o & >H0 & >H1 & >H2 & Hxc & >(%dv & Hδ & %Hδ)) Hclose]".
        iDestruct (pstates_rev_known with "H0 H1 H2 Hx") as "(%Hsx & H0 & H1 & H2)"; first done.
        iDestruct (pstates_rev_known with "H0 H1 H2 Hx'") as "(%Hsx' & H0 & H1 & H2)"; first done.
        iDestruct (pstates_rev_known with "H0 H1 H2 Hxq") as "(%Hsxq & H0 & H1 & H2)"; first done.
        rewrite (Hδ x x' Hsx Hsx'); last by rewrite Hsxq.
        brel_load_l. rewrite fill_app /=. iApply brel_mult_l.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "H0 H1 H2 Hxc Hδ".
        { iNext. iExists o. iFrame. iPureIntro. intros a b Ha Hb _.
          rewrite Hsx in Ha. rewrite Hsx' in Hb. by simplify_eq. }
        rewrite (_ : ((x * x')^-1 * m * (x * x'))%g = m); last by rewrite -mulgA (vgG_comm m) mulKg.
        iApply "Hk". iExists _, _, _, m, m. iSplit; first done. iFrame "Hl".
        rewrite /add3_party.del_adj bool_decide_eq_true_2 //.
      - (* any other message: no patch *)
        iAssert (BREL fill k1 (vgval m') ≤ fill k2 (vgval m) <|(l1s, l2s, iThyBot) :: L|> {{S}})%I
          with "[Hk]" as "Hdone".
        { iApply "Hk". iExists s, d, t, m, m'. iSplit; first done. iFrame "Hl".
          rewrite /add3_party.del_adj bool_decide_eq_false_2 //. }
        rewrite /Sum.
        case_bool_decide as E1; brel_pures;
          [case_bool_decide as E2; brel_pures; [case_bool_decide as E3; brel_pures|]|]; try done.
        exfalso. apply Hne. by simplify_eq.
    Qed.

    Local Ltac go_tail_rev N k1 k2 :=
      brel_pures;
      iApply brel_na_close; iFrame "Hclose";
      iSplitL "Hps Hxc Hδ";
      [ iNext; iDestruct "Hps" as "(H0 & H1 & H2)"; iExists _; iFrame "H0 H1 H2 Hxc Hδ" | ];
      lazymatch goal with
      | |- environments.envs_entails _ (brel _ _ _ (_ :: ?Lr) _) =>
          iApply (brel_bind'' [AppRCtx _; AppRCtx _] [AppRCtx _; InjRCtx] Lr [([_], [_], iThyBot)])
      end;
      [ simpl; apply list_subseteq_nil | simpl; apply list_subseteq_nil
      | iApply to_iThy_le_intro'; apply Permutation_submseteq; symmetry;
        apply Permutation_cons_append | ];
      first [ iApply (run_party_spec_rev_c c Hc γx γr with "Hlk Hxk Htp Htq"); [done | done |]
            | iApply (run_party_spec_rev_h c Hc γx γr with "Hlk Hxk Htp Htq"); [done | done |] ];
      iIntros (v1 v2) "(%x0 & %x1 & %x2 & #Hy0 & #Hy1 & #Hy2 & ->)"; simpl; brel_pures;
      iApply (brel_na_inv _ _ N); [set_solver | iFrame "Hinv"];
      iIntros "[(%o2 & >H0 & >H1 & >H2 & Hxc & Hδ) Hclose]";
      iDestruct (pstates_rev_known with "H0 H1 H2 Hy0") as "(%E0 & H0 & H1 & H2)"; [done |];
      iDestruct (pstates_rev_known with "H0 H1 H2 Hy1") as "(%E1 & H0 & H1 & H2)"; [done |];
      iDestruct (pstates_rev_known with "H0 H1 H2 Hy2") as "(%E2 & H0 & H1 & H2)"; [done |];
      iDestruct "H0" as "(Hs0 & Hx0 & H0)"; iDestruct "H1" as "(Hs1 & Hx1 & H1)";
      iDestruct "H2" as "(Hs2 & Hx2 & H2)";
      iApply (brel_prod3_l [AppRCtx _] with "Hx0 Hx1 Hx2"); iIntros "Hx0 Hx1 Hx2";
      lazymatch goal with
      | H0 : ?f 0 = Some _, H1 : ?f 1 = Some _, H2 : ?f 2 = Some _ |- _ =>
          iEval (rewrite H0 H1 H2 /=)
      end;
      iApply brel_na_close; iFrame "Hclose";
      iSplitL "Hs0 Hx0 H0 Hs1 Hx1 H1 Hs2 Hx2 H2 Hxc Hδ";
      [ iNext; iExists _; iFrame "Hxc Hδ"; rewrite /pstate_rev; iFrame | ];
      brel_cont_l; brel_cont_r;
      iApply (brel_exhaustion (fill k1 _) (fill k2 _));
      [ set_unfold; tauto | set_unfold; tauto
      | iApply "Hrel";
        lazymatch goal with |- context [InjRV (vgval ?y)] => iApply ("HQ" $! (Some y)) end
      | iApply "IH" ].

    Local Opaque run_party.

    (** One session: F_ADD3 with the simulator against the protocol. *)
    Lemma go_sess_spec_rev N L l1 l2 (f1 f2 lk1 lk2 : val) R :
      na_invP N start_inv_rev -∗
      env_fun_spec L leak_ok lk1 lk2 -∗
      (∀ go1 go2, BREL f1 (ports go1) ≤ f2 (ports go2)
         <|([go1], [go2], GoThy go1 go2) :: ([l1], [l2], NetT l1 l2) :: L|> {{R}}) -∗
      BREL (λ: "r", (λ: "f" "leakIn", F_ADD3_sess c (#ℓx0, #ℓx1, #ℓx2)%V "f" "leakIn")%V f1 "r")%V
             (sim_leak c #ℓδ #ℓxc lk1 (net_eps l1))
         ≤ Π_sess c (#ℓs0, #ℓs1, #ℓs2)%V f2 (lk2, net_eps l2)%V
        <|([l1], [l2], NetT l1 l2) :: L|> {{R}}.
    Proof using All.
      iIntros "#Hinv #Hlk Hf".
      rewrite /Π_sess /F_ADD3_sess /sim_leak. brel_pures.
      brel_effect_l go1 as "Hg1". brel_effect_r go2 as "Hg2". brel_pures.
      iApply brel_new_theory.
      iApply (brel_add_label_l with "Hg1").
      iApply (brel_add_label_r with "Hg2").
      iApply (brel_exhaustion (f1 _) (f2 _) _ _ (GoThy go1 go2) with "[Hf]");
        [set_unfold; tauto | set_unfold; tauto | by iApply "Hf" |].
      iLöb as "IH".
      iSplit; [iIntros "!>" (v1 v2) "HR"; brel_pures; iModIntro; done |].
      iIntros "!>" (k1 k2 e1 e2 Q) "%Hk1 %Hk2 HXQ #Hrel".
      iDestruct "HXQ" as (j n) "(%Hj & -> & -> & #HQ)".
      brel_handle_os_l ka as "Hka". brel_handle_os_r kb as "Hkb". brel_pures.
      repeat foldkont.
      destruct (vg_of_int_sem n) as [x|] eqn:Hn; last first.
      { (* not a group element *)
        iApply brel_vg_of_int_none_l; first done.
        iApply brel_vg_of_int_none_r; first done. brel_pures.
        brel_cont_l. brel_cont_r.
        iApply (brel_exhaustion (fill k1 _) (fill k2 _));
          [set_unfold; tauto | set_unfold; tauto | iApply "Hrel"; iApply ("HQ" $! None) | iApply "IH"]. }
      iApply brel_vg_of_int_correct_l; first done.
      iApply brel_vg_of_int_correct_r; first done. brel_pures.
      iApply (brel_sel3_l [AppRCtx _]); first done.
      iApply (brel_sel3_r [AppRCtx _]); first done.
      simpl. rewrite !sel_loc. brel_pures.
      iApply (brel_na_inv _ _ N); first set_solver. iFrame "Hinv".
      iIntros "[(%o & >H0 & >H1 & >H2 & >Hxc & >Hδ) Hclose]".
      iDestruct (pstates_take_rev o j with "[$H0 $H1 $H2]") as "[(Hs & Hxj & Hst) Hback]"; first done.
      brel_load_l. brel_load_r.
      destruct (o j) as [xj|] eqn:Hoj.
      - (* party [j] has already run: both sides refuse *)
        rewrite bool_decide_eq_true_2; last by eexists. rewrite /optvg. brel_pures.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hs Hxj Hst Hback Hxc Hδ".
        { iNext.
          iDestruct ("Hback" $! (Some xj) with "[Hs Hxj Hst]") as "(H0 & H1 & H2)".
          { rewrite /pstate_rev bool_decide_eq_true_2; last by eexists. iFrame. }
          rewrite !(upd_eq_same _ _ _ _ Hoj). iExists o. iFrame. }
        rewrite /kont /kont0. brel_cont_l. brel_cont_r.
        iApply (brel_exhaustion (fill k1 _) (fill k2 _));
          [set_unfold; tauto | set_unfold; tauto | iApply "Hrel"; iApply ("HQ" $! None) | iApply "IH"].
      - (* party [j]'s first input: F_ADD3 records it, and the simulator runs party [j] *)
        rewrite bool_decide_eq_false_2; last by intros [? ?]. rewrite /optvg. brel_pures.
        brel_store_l. brel_store_r. brel_pures.
        iDestruct "Hst" as "(Htx & Htp & Htq)".
        iMod (slot_set _ (vgval x) with "Htx") as "#Hxk".
        iDestruct ("Hback" $! (Some x) with "[Hs Hxj]") as "(H0 & H1 & H2)".
        { rewrite /pstate_rev bool_decide_eq_true_2; last by eexists. iFrame "∗ #". }
        iDestruct "H0" as "(Hs0 & Hx0 & H0)".
        iDestruct "H1" as "(Hs1 & Hx1 & H1)".
        iDestruct "H2" as "(Hs2 & Hx2 & H2)".
        iApply (brel_prod3_l [AppRCtx _; AppRCtx _; PairRCtx _] with "Hx0 Hx1 Hx2").
        iIntros "Hx0 Hx1 Hx2". simpl. brel_pures.
        (* the simulator records [x_c] *)
        destruct (decide (j = cz c)) as [Hjc | Hjc].
        + rewrite (bool_decide_eq_true_2 (#j = #c)); last by rewrite Hjc. brel_pures.
          iDestruct "Hxc" as (vxc) "[Hxc _]". brel_store_l. brel_pures.
          iAssert (∃ v, ℓxc ↦ v ∗ ⌜∀ y, upd o j (Some x) (cz c) = Some y → v = vgval y⌝)%I
            with "[Hxc]" as "Hxc".
          { iExists _. iFrame. iPureIntro. intros y'. rewrite -Hjc upd_at. by intros [= <-]. }
          iDestruct "Hxc" as (vxc') "[Hxc %Hvxc']".
          destruct (prod_opt (upd o j (Some x) 0) (upd o j (Some x) 1) (upd o j (Some x) 2))
            as [y|] eqn:Hy; rewrite /optvg; brel_pures.
          * (* all inputs are in: the simulator sets [δ = y · x_c⁻¹ = x_h · x_{h'}] *)
            destruct (prod_opt_some _ _ Hy) as (a & b & d & Ha & Hb & Hd & ->).
            destruct (proj1 (roles_all c Hc (upd o j (Some x)))
                        (ex_intro _ a (ex_intro _ b (ex_intro _ d (conj Ha (conj Hb Hd))))))
              as ([xc0 Hxc0] & [xh Hxh] & [xh' Hxh']).
            iDestruct "Hδ" as (vδ) "[Hδ _]".
            brel_load_l. rewrite (Hvxc' xc0 Hxc0).
            repeat (brel_inv_l || brel_mult_l). brel_pures. brel_store_l. brel_pures.
            iAssert (∃ v, ℓxc ↦ v ∗ ⌜∀ y, upd o j (Some x) (cz c) = Some y → v = vgval y⌝)%I
              with "[Hxc]" as "Hxc".
            { iExists _. iFrame. iPureIntro. intros ? E. rewrite Hxc0 in E. by simplify_eq. }
            iAssert (∃ v, ℓδ ↦ v ∗ ⌜∀ a' b', upd o j (Some x) (hz c) = Some a' →
                        upd o j (Some x) (hz' c) = Some b' → is_Some (upd o j (Some x) (cz c)) →
                        v = vgval (a' * b')%g⌝)%I with "[Hδ]" as "Hδ".
            { iExists _. iFrame. iPureIntro. intros a' b' Ha' Hb' _.
              rewrite Hxh in Ha'. rewrite Hxh' in Hb'. simplify_eq. f_equal.
              by eapply (delta_alg c Hc). }
            iAssert (pstate_rev 0 (upd o j (Some x) 0) ∗ pstate_rev 1 (upd o j (Some x) 1) ∗
                     pstate_rev 2 (upd o j (Some x) 2))%I
              with "[Hs0 Hx0 H0 Hs1 Hx1 H1 Hs2 Hx2 H2]" as "Hps"; first by iFrame.
            go_tail_rev N k1 k2.
          * (* not all inputs are in yet: δ unchanged *)
            iAssert (∃ v, ℓxc ↦ v ∗ ⌜∀ y, upd o j (Some x) (cz c) = Some y → v = vgval y⌝)%I
              with "[Hxc]" as "Hxc".
            { iExists _. by iFrame. }
            iAssert (∃ v, ℓδ ↦ v ∗ ⌜∀ a b, upd o j (Some x) (hz c) = Some a →
                        upd o j (Some x) (hz' c) = Some b → is_Some (upd o j (Some x) (cz c)) →
                        v = vgval (a * b)%g⌝)%I with "[Hδ]" as "Hδ".
            { iDestruct "Hδ" as (vδ) "[Hδ _]". iExists vδ. iFrame. iPureIntro.
              intros a b Ha Hb Hcs. exfalso. apply (prod_opt_none _ Hy), (roles_all c Hc).
              split_and!; [done | by eexists | by eexists]. }
            iAssert (pstate_rev 0 (upd o j (Some x) 0) ∗ pstate_rev 1 (upd o j (Some x) 1) ∗
                     pstate_rev 2 (upd o j (Some x) 2))%I
              with "[Hs0 Hx0 H0 Hs1 Hx1 H1 Hs2 Hx2 H2]" as "Hps"; first by iFrame.
            go_tail_rev N k1 k2.
        + rewrite (bool_decide_eq_false_2 (#j = #c)); last by intros [= ?]. brel_pures.
          iAssert (∃ v, ℓxc ↦ v ∗ ⌜∀ y, upd o j (Some x) (cz c) = Some y → v = vgval y⌝)%I
            with "[Hxc]" as "Hxc".
          { iDestruct "Hxc" as (vxc) "[Hxc %Hvxc]". iExists vxc. iFrame. iPureIntro.
            intros y'. rewrite upd_ne; [apply Hvxc | intros ?; by apply Hjc]. }
          iDestruct "Hxc" as (vxc') "[Hxc %Hvxc']".
          destruct (prod_opt (upd o j (Some x) 0) (upd o j (Some x) 1) (upd o j (Some x) 2))
            as [y|] eqn:Hy; rewrite /optvg; brel_pures.
          * (* all inputs are in: the simulator sets [δ = y · x_c⁻¹ = x_h · x_{h'}] *)
            destruct (prod_opt_some _ _ Hy) as (a & b & d & Ha & Hb & Hd & ->).
            destruct (proj1 (roles_all c Hc (upd o j (Some x)))
                        (ex_intro _ a (ex_intro _ b (ex_intro _ d (conj Ha (conj Hb Hd))))))
              as ([xc0 Hxc0] & [xh Hxh] & [xh' Hxh']).
            iDestruct "Hδ" as (vδ) "[Hδ _]".
            brel_load_l. rewrite (Hvxc' xc0 Hxc0).
            repeat (brel_inv_l || brel_mult_l). brel_pures. brel_store_l. brel_pures.
            iAssert (∃ v, ℓxc ↦ v ∗ ⌜∀ y, upd o j (Some x) (cz c) = Some y → v = vgval y⌝)%I
              with "[Hxc]" as "Hxc".
            { iExists _. iFrame. iPureIntro. intros ? E. rewrite Hxc0 in E. by simplify_eq. }
            iAssert (∃ v, ℓδ ↦ v ∗ ⌜∀ a' b', upd o j (Some x) (hz c) = Some a' →
                        upd o j (Some x) (hz' c) = Some b' → is_Some (upd o j (Some x) (cz c)) →
                        v = vgval (a' * b')%g⌝)%I with "[Hδ]" as "Hδ".
            { iExists _. iFrame. iPureIntro. intros a' b' Ha' Hb' _.
              rewrite Hxh in Ha'. rewrite Hxh' in Hb'. simplify_eq. f_equal.
              by eapply (delta_alg c Hc). }
            iAssert (pstate_rev 0 (upd o j (Some x) 0) ∗ pstate_rev 1 (upd o j (Some x) 1) ∗
                     pstate_rev 2 (upd o j (Some x) 2))%I
              with "[Hs0 Hx0 H0 Hs1 Hx1 H1 Hs2 Hx2 H2]" as "Hps"; first by iFrame.
            go_tail_rev N k1 k2.
          * (* not all inputs are in yet: δ unchanged *)
            iAssert (∃ v, ℓxc ↦ v ∗ ⌜∀ y, upd o j (Some x) (cz c) = Some y → v = vgval y⌝)%I
              with "[Hxc]" as "Hxc".
            { iExists _. by iFrame. }
            iAssert (∃ v, ℓδ ↦ v ∗ ⌜∀ a b, upd o j (Some x) (hz c) = Some a →
                        upd o j (Some x) (hz' c) = Some b → is_Some (upd o j (Some x) (cz c)) →
                        v = vgval (a * b)%g⌝)%I with "[Hδ]" as "Hδ".
            { iDestruct "Hδ" as (vδ) "[Hδ _]". iExists vδ. iFrame. iPureIntro.
              intros a b Ha Hb Hcs. exfalso. apply (prod_opt_none _ Hy), (roles_all c Hc).
              split_and!; [done | by eexists | by eexists]. }
            iAssert (pstate_rev 0 (upd o j (Some x) 0) ∗ pstate_rev 1 (upd o j (Some x) 1) ∗
                     pstate_rev 2 (upd o j (Some x) 2))%I
              with "[Hs0 Hx0 H0 Hs1 Hx1 H1 Hs2 Hx2 H2]" as "Hps"; first by iFrame.
            go_tail_rev N k1 k2.
    Qed.

  End state_rev.

End prf_rev.

Section main_rev.
  Context `{!probblazeRGS Σ, !inG Σ (dfrac_agreeR valO)}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Context (c : nat) (Hc : (c < 3)%nat).
  Local Open Scope Z_scope.

  Lemma I_ADD3_R_ADD3 : ⊢ sem_typed [] (I_ADD3 c) (R_ADD3 c) ⊥ τ_ADD3 [].
  Proof using All.
    iIntros (vs) "!> _".
    rewrite subst_map_is_closed_empty; last is_closed.
    rewrite subst_map_is_closed_empty; last is_closed.
    Local Opaque F_NET_sess Π_sess F_ADD3_sess sim_leak.
    rewrite /R_ADD3 /I_ADD3 /F_NET /Π /S_ADD3 /F_ADD3 /F_NET_gen /functionality_composition /func_comp.
    brel_pures.
    (* the ideal world's state: F_ADD3's inputs, the simulator's δ, [x_c] and mailbox *)
    brel_alloc_l x2 as "Hx2". brel_pures_l. brel_alloc_l x1 as "Hx1". brel_pures_l.
    brel_alloc_l x0 as "Hx0". brel_pures_l.
    brel_alloc_l d as "Hd". brel_pures_l. brel_alloc_l xc as "Hxc". brel_pures_l.
    rewrite /patch. brel_pures_l. brel_alloc_l m1 as "Hm1".
    (* the real world's: Π's flags and the network's mailbox *)
    brel_alloc_r st2 as "Hst2". brel_alloc_r st1 as "Hst1". brel_alloc_r st0 as "Hst0". brel_pures_r.
    brel_alloc_r m2 as "Hm2".
    (* ghost state and invariants *)
    iMod slots_alloc as (γx γr) "(Ht0 & Ht1 & Ht2)".
    iApply (brel_na_alloc (net_inv m1 m2 (Rmsg_rev c γx γr)) netN).
    iSplitL "Hm1 Hm2".
    { iNext. iExists _, _, ∅, ∅. iFrame. iSplit; [iPureIntro; apply is_tbl_nil|].
      iSplit; [iPureIntro; apply is_tbl_nil|]. by rewrite big_sepM2_empty. }
    iIntros "#Hnet".
    iApply (brel_na_alloc (start_inv_rev c γx γr st0 st1 st2 x0 x1 x2 d xc) startN).
    iSplitL "Hst0 Hst1 Hst2 Hx0 Hx1 Hx2 Hd Hxc Ht0 Ht1 Ht2".
    { iNext. iExists (λ _, None). rewrite /pstate_rev /=. iFrame.
      iPureIntro. split; [done | by intros ?? []]. }
    iIntros "#Hstart".
    brel_pures. iModIntro. iSplit; last done.
    (* a session: the environment calls the scenario with a client [f] *)
    rewrite /τ_ADD3 /sem_ty_mbang /sem_ty_type_forall /sem_ty_row_forall /sem_ty_arr /=.
    iModIntro. iIntros (α θL f1 f2) "Hf".
    brel_pures. iModIntro. iIntros (θ1 r1 r2) "Hr".
    rewrite /τ_envops /sem_ty_prod.
    iDestruct "Hr" as (lk1 lk2 ops1 ops2) "(-> & -> & #Hlk & %nl1 & %nl2 & %w1 & %w2 & -> & -> & #Hnl & #Hw)".
    brel_pures.
    (* the network *)
    iApply (F_NET_sess_spec netN with "Hnet [] [] [] [Hf]").
    { by iApply hdr_spec_typed. }
    { by iApply hdr_spec_typed. }
    { by iApply (patch_ok_rev c Hc γx γr st0 st1 st2 x0 x1 x2 d xc startN). }
    iIntros (l1 l2). brel_pures.
    (* F_ADD3 and the simulator against the protocol *)
    iApply (go_sess_spec_rev c Hc γx γr st0 st1 st2 x0 x1 x2 d xc startN with "Hstart [] [Hf]").
    { by iApply leak_spec_typed. }
    iIntros (go1 go2).
    (* the client, at its type *)
    iApply (brel_introduction_mono with "[] [Hf]"); last first.
    { iApply ("Hf" $! (go_row go1 go2)). iApply ports_typed. }
    iApply to_iThy_le_intro'. unfold sem_row_union.
    repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app).
    simpl. solve_submseteq.
  Qed.


End main_rev.
