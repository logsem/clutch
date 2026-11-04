From iris.proofmode Require Import base proofmode classes.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def.
From clutch.prob_eff_lang.probblaze.examples.secure_add Require Import
  add_corrupt_C_bijection add3_def add3_tbl add3_net add3_party.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.
Import valgroup_tactics.

(** * The security proof: the real world refines the ideal one *)

(* The [j]-th of three things. *)
Definition sel {A} (a0 a1 a2 : A) (j : Z) : A :=
  if bool_decide (j = 0%Z) then a0 else if bool_decide (j = 1%Z) then a1 else a2.

Section code.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  Lemma brel_sel3_l K (v0 v1 v2 : val) (j : Z) e2 E L R :
    (0 ≤ j < 3)%Z →
    BREL fill K (sel v0 v1 v2 j) ≤ e2 @ E <|L|> {{R}} ⊢
    BREL fill K (sel3 (v0, v1, v2)%V #j) ≤ e2 @ E <|L|> {{R}}.
  Proof.
    intros Hj. iIntros "H". rewrite /sel3 /sel.
    assert (j = 0 ∨ j = 1 ∨ j = 2)%Z as [ -> | [ -> | -> ] ] by lia; by brel_pures_l.
  Qed.

  Lemma brel_sel3_r K (v0 v1 v2 : val) (j : Z) e1 E L R :
    (0 ≤ j < 3)%Z →
    BREL e1 ≤ fill K (sel v0 v1 v2 j) @ E <|L|> {{R}} ⊢
    BREL e1 ≤ fill K (sel3 (v0, v1, v2)%V #j) @ E <|L|> {{R}}.
  Proof.
    intros Hj. iIntros "H". rewrite /sel3 /sel.
    assert (j = 0 ∨ j = 1 ∨ j = 2)%Z as [ -> | [ -> | -> ] ] by lia; by brel_pures_r.
  Qed.

  (* An optional group element, as a value. *)
  Definition optvg (o : option vgG) : val :=
    match o with Some x => SOMEV (vgval x) | None => NONEV end.

  Definition prod_opt (o0 o1 o2 : option vgG) : option vgG :=
    match o0, o1, o2 with Some a, Some b, Some d => Some (a * b * d)%g | _, _, _ => None end.

  Lemma brel_prod3_r K (ℓ0 ℓ1 ℓ2 : loc) o0 o1 o2 e1 E L R :
    ℓ0 ↦ₛ optvg o0 -∗ ℓ1 ↦ₛ optvg o1 -∗ ℓ2 ↦ₛ optvg o2 -∗
    (ℓ0 ↦ₛ optvg o0 -∗ ℓ1 ↦ₛ optvg o1 -∗ ℓ2 ↦ₛ optvg o2 -∗
       BREL e1 ≤ fill K (optvg (prod_opt o0 o1 o2)) @ E <|L|> {{R}}) -∗
    BREL e1 ≤ fill K (prod3 (#ℓ0, #ℓ1, #ℓ2)%V) @ E <|L|> {{R}}.
  Proof using All.
    iIntros "H0 H1 H2 H". rewrite /prod3. brel_pures_r.
    brel_load_r. rewrite fill_app /=.
    destruct o0 as [a|]; rewrite /optvg; brel_pures_r; last by iApply ("H" with "H0 H1 H2").
    brel_load_r. rewrite fill_app /=.
    destruct o1 as [b|]; brel_pures_r; last by iApply ("H" with "H0 H1 H2").
    brel_load_r. rewrite fill_app /=.
    destruct o2 as [d|]; brel_pures_r; last by iApply ("H" with "H0 H1 H2").
    (* the group tactics do not see through [fill K] *)
    rewrite -(fill_app K [InjRCtx; AppLCtx (vgval d); AppRCtx vmult] (vmult (vgval a) (vgval b))).
    iApply brel_mult_r. rewrite fill_app /=.
    rewrite -(fill_app K [InjRCtx] (vmult (vgval (a * b)) (vgval d))).
    iApply brel_mult_r. rewrite fill_app /=. brel_pures_r.
    by iApply ("H" with "H0 H1 H2").
  Qed.

End code.

Section prf.
  Context `{!probblazeRGS Σ, !inG Σ (dfrac_agreeR valO)}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Context (c : nat) (Hc : (c < 3)%nat).
  Context (γx : Z → gname) (γr : Z → Z → gname).
  Local Open Scope Z_scope.

  Local Notation xk := (xk γx).
  Local Notation rk := (rk γr).
  Local Notation Rmsg := (Rmsg c γx γr).
  Local Notation Rdeliv := (Rdeliv c γx γr).
  Local Notation NetT l1 l2 := (NetThy Rmsg Rdeliv l1 l2).

  (** Facts about the roles, for each corrupt party. *)
  Lemma sel_roles {A} (a0 a1 a2 : A) :
    ∃ ac ah ah', sel a0 a1 a2 (cz c) = ac ∧ sel a0 a1 a2 (hz c) = ah ∧ sel a0 a1 a2 (hz' c) = ah' ∧
      ((ac, ah, ah') = (a0, a1, a2) ∨ (ac, ah, ah') = (a1, a2, a0) ∨ (ac, ah, ah') = (a2, a0, a1)).
  Proof using Hc.
    rewrite /sel /cz /hz /hz' /hon.
    destruct c as [|[|[|c']]]; [..|lia]; simpl; eauto 10.
  Qed.

  Lemma roles_concrete :
    (cz c, hz c, hz' c) = (0, 1, 2) ∨ (cz c, hz c, hz' c) = (1, 2, 0) ∨ (cz c, hz c, hz' c) = (2, 0, 1).
  Proof using Hc.
    rewrite /cz /hz /hz' /hon. destruct c as [|[|[|c']]]; [..|lia]; simpl; auto.
  Qed.

  Definition upd (o : Z → option vgG) (j : Z) (o' : option vgG) : Z → option vgG :=
    λ k, if bool_decide (k = j) then o' else o k.

  Lemma sel_loc (a b d : loc) j : sel #a #b #d j = #(sel a b d j).
  Proof using. rewrite /sel. by repeat case_bool_decide. Qed.

  Lemma upd_at o j o' : upd o j o' j = o'.
  Proof using. rewrite /upd. by case_bool_decide. Qed.
  Lemma upd_ne o j o' k : k ≠ j → upd o j o' k = o k.
  Proof using. intros. rewrite /upd. by case_bool_decide. Qed.
  Lemma upd_same o j k : upd o j (o j) k = o k.
  Proof using. rewrite /upd. case_bool_decide; by subst. Qed.
  Lemma upd_eq_same o j o' k : o j = o' → upd o j o' k = o k.
  Proof using. intros <-. apply upd_same. Qed.

  (* All three have given their inputs, in terms of indices or of roles. *)
  Lemma roles_all (o : Z → option vgG) :
    (∃ a b d, o 0 = Some a ∧ o 1 = Some b ∧ o 2 = Some d) ↔
    (is_Some (o (cz c)) ∧ is_Some (o (hz c)) ∧ is_Some (o (hz' c))).
  Proof using Hc.
    destruct roles_concrete as [[= -> -> ->] | [[= -> -> ->] | [= -> -> ->]]];
      (split; [intros (?&?&?&->&->&->); split_and!; by eexists
              | intros ([? ->]&[? ->]&[? ->]); by do 3 eexists]).
  Qed.

  Lemma prod_opt_some (o : Z → option vgG) y :
    prod_opt (o 0) (o 1) (o 2) = Some y →
    ∃ a b d, o 0 = Some a ∧ o 1 = Some b ∧ o 2 = Some d ∧ y = (a * b * d)%g.
  Proof using.
    rewrite /prod_opt. destruct (o 0), (o 1), (o 2); intros; simplify_eq; eauto 10.
  Qed.

  Lemma prod_opt_none (o : Z → option vgG) :
    prod_opt (o 0) (o 1) (o 2) = None → ¬ (∃ a b d, o 0 = Some a ∧ o 1 = Some b ∧ o 2 = Some d).
  Proof using.
    rewrite /prod_opt. intros H (?&?&?&E0&E1&E2). by rewrite E0 E1 E2 in H.
  Qed.

  (* [δ = y · x_c⁻¹ = x_h · x_{h'}]. *)
  Lemma delta_alg (o : Z → option vgG) a b d xc xh xh' :
    o 0 = Some a → o 1 = Some b → o 2 = Some d →
    o (cz c) = Some xc → o (hz c) = Some xh → o (hz' c) = Some xh' →
    (a * b * d * xc^-1 = xh * xh')%g.
  Proof using All.
    intros E0 E1 E2.
    destruct roles_concrete as [[= -> -> ->] | [[= -> -> ->] | [= -> -> ->]]];
      rewrite ?E0 ?E1 ?E2; intros [= <-] [= <-] [= <-].
    - by rewrite -!mulgA (vgG_comm d) (mulgCA b) mulKVg.
    - by rewrite -!mulgA (vgG_comm d b^-1) mulKVg vgG_comm.
    - by rewrite mulgK.
  Qed.

  (** The state of the three parties, and of the simulator *)
  Section state.
    (* Π's started flags (left), F_ADD3's inputs, and the simulator's δ and
       [x_c] (right). *)
    Context (ℓs0 ℓs1 ℓs2 ℓx0 ℓx1 ℓx2 ℓδ ℓxc : loc).

    Definition party_toks (j : Z) : iProp Σ :=
      slot_tok (γx j) ∗ slot_tok (γr j (nxt j)) ∗ slot_tok (γr j (nxt2 j)).

    Definition pstate (j : Z) (o : option vgG) : iProp Σ :=
      sel ℓs0 ℓs1 ℓs2 j ↦ #(bool_decide (is_Some o)) ∗ sel ℓx0 ℓx1 ℓx2 j ↦ₛ optvg o ∗
      match o with None => party_toks j | Some x => xk j x end.

    (* [x_c] once [c] gave its input, and [δ = x_h · x_{h'}] once all did. *)
    Definition start_inv : iProp Σ :=
      ∃ o : Z → option vgG,
        pstate 0 (o 0) ∗ pstate 1 (o 1) ∗ pstate 2 (o 2) ∗
        (∃ v, ℓxc ↦ₛ v ∗ ⌜∀ x, o (cz c) = Some x → v = vgval x⌝) ∗
        (∃ v, ℓδ ↦ₛ v ∗ ⌜∀ a b, o (hz c) = Some a → o (hz' c) = Some b →
                           is_Some (o (cz c)) → v = vgval (a * b)%g⌝).

    Global Instance pstate_timeless j o : Timeless (pstate j o).
    Proof. rewrite /pstate. destruct o; apply _. Qed.

    Lemma pstates_take o j :
      0 ≤ j < 3 →
      pstate 0 (o 0) ∗ pstate 1 (o 1) ∗ pstate 2 (o 2) ⊢
      pstate j (o j) ∗
      (∀ o', pstate j o' -∗
         pstate 0 (upd o j o' 0) ∗ pstate 1 (upd o j o' 1) ∗ pstate 2 (upd o j o' 2)).
    Proof using Hc.
      iIntros (Hj) "(H0 & H1 & H2)". rewrite /upd.
      assert (j = 0 ∨ j = 1 ∨ j = 2) as [ -> | [ -> | -> ] ] by (clear -Hj; lia);
        iFrame; iIntros (o') "H"; repeat case_bool_decide; try lia; iFrame.
    Qed.

    Lemma pstate_known j o x : pstate j o -∗ xk j x -∗ ⌜o = Some x⌝.
    Proof using.
      iIntros "(_ & _ & Ho) Hx". destruct o as [x'|].
      - by iDestruct (xk_agree with "Ho Hx") as %->.
      - iDestruct "Ho" as "[Ht _]". by iDestruct (slot_tok_excl with "Ht Hx") as %[].
    Qed.

    Lemma pstates_known o j x :
      0 ≤ j < 3 →
      pstate 0 (o 0) -∗ pstate 1 (o 1) -∗ pstate 2 (o 2) -∗ xk j x -∗
      ⌜o j = Some x⌝ ∗ pstate 0 (o 0) ∗ pstate 1 (o 1) ∗ pstate 2 (o 2).
    Proof using.
      iIntros (Hj) "H0 H1 H2 #Hx".
      assert (j = 0 ∨ j = 1 ∨ j = 2) as [ -> | [ -> | -> ] ] by (clear -Hj; lia).
      - iDestruct (pstate_known with "H0 Hx") as %?. by iFrame.
      - iDestruct (pstate_known with "H1 Hx") as %?. by iFrame.
      - iDestruct (pstate_known with "H2 Hx") as %?. by iFrame.
    Qed.

    (* The simulator's patch, once [δ] is allocated. *)
    Definition patch_v : val :=
      (λ: "s" "d" "t" "m",
         if: ("s" = #(hon c)) && ("d" = #c) && ("t" = Sum) then "m" · !#ℓδ else "m")%V.

    Lemma patch_ok N L :
      na_invP N start_inv ⊢
      patch_spec L (λ: "s" "d" "t" "m", "m")%V patch_v Rmsg Rdeliv.
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
        iDestruct (pstates_known with "H0 H1 H2 Hx") as "(%Hsx & H0 & H1 & H2)"; first done.
        iDestruct (pstates_known with "H0 H1 H2 Hx'") as "(%Hsx' & H0 & H1 & H2)"; first done.
        iDestruct (pstates_known with "H0 H1 H2 Hxq") as "(%Hsxq & H0 & H1 & H2)"; first done.
        rewrite (Hδ x x' Hsx Hsx'); last by rewrite Hsxq.
        brel_load_r. rewrite fill_app /=. iApply brel_mult_r.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "H0 H1 H2 Hxc Hδ".
        { iNext. iExists o. iFrame. iPureIntro. intros a b Ha Hb _.
          rewrite Hsx in Ha. rewrite Hsx' in Hb. by simplify_eq. }
        rewrite (_ : ((x * x')^-1 * m * (x * x'))%g = m); last by rewrite -mulgA (vgG_comm m) mulKg.
        iApply "Hk". iExists _, _, _, m, m. iSplit; first done. iFrame "Hl".
        rewrite /add3_party.del_adj bool_decide_eq_true_2 //.
      - (* any other message: no patch *)
        iAssert (BREL fill k1 (vgval m) ≤ fill k2 (vgval m') <|(l1s, l2s, iThyBot) :: L|> {{S}})%I
          with "[Hk]" as "Hdone".
        { iApply "Hk". iExists s, d, t, m, m'. iSplit; first done. iFrame "Hl".
          rewrite /add3_party.del_adj bool_decide_eq_false_2 //. }
        rewrite /Sum.
        case_bool_decide as E1; brel_pures;
          [case_bool_decide as E2; brel_pures; [case_bool_decide as E3; brel_pures|]|]; try done.
        exfalso. apply Hne. by simplify_eq.
    Qed.

    (** The client's ports: [port j n] asks for party [j] to run on input [n]. *)
    Definition ports (l : label) : val :=
      ((λ: "x", do: l (#0, "x")), (λ: "x", do: l (#1, "x")), (λ: "x", do: l (#2, "x")))%V.

    (* Both sides call the same port on the same input, and get the same
       output (in Option 𝔾). *)
    Program Definition GoThy (go1 go2 : label) : iThy Σ :=
      λ e1 e2, (λne Q,
        ∃ (j : Z) (n : nat), ⌜0 ≤ j < 3⌝ ∗
          ⌜e1 = (do: go1 (#j, #n)%V)%E⌝ ∗ ⌜e2 = (do: go2 (#j, #n)%V)%E⌝ ∗
          □ (∀ o : option vgG, Q (optvg o) (optvg o)))%I.
    Next Obligation. solve_proper. Qed.

    (* After the simulator's bookkeeping, in every case: close the invariant,
       run party [j] in both worlds, and resume the client with the product. *)
    Local Ltac go_tail N k1 k2 :=
      brel_pures;
      iApply brel_na_close; iFrame "Hclose";
      iSplitL "Hps Hxc Hδ";
      [ iNext; iDestruct "Hps" as "(H0 & H1 & H2)"; iExists _; iFrame "H0 H1 H2 Hxc Hδ" | ];
      lazymatch goal with
      | |- environments.envs_entails _ (brel _ _ _ (_ :: ?Lr) _) =>
          iApply (brel_bind'' [AppRCtx _; InjRCtx] [AppRCtx _; AppRCtx _] Lr [([_], [_], iThyBot)])
      end;
      [ simpl; apply list_subseteq_nil | simpl; apply list_subseteq_nil
      | iApply to_iThy_le_intro'; apply Permutation_submseteq; symmetry;
        apply Permutation_cons_append | ];
      first [ iApply (run_party_spec_c c Hc γx γr with "Hlk Hxk Htp Htq"); [done | done |]
            | iApply (run_party_spec_h c Hc γx γr with "Hlk Hxk Htp Htq"); [done | done |] ];
      iIntros (v1 v2) "(%x0 & %x1 & %x2 & #Hy0 & #Hy1 & #Hy2 & ->)"; simpl; brel_pures;
      iApply (brel_na_inv _ _ N); [set_solver | iFrame "Hinv"];
      iIntros "[(%o2 & >H0 & >H1 & >H2 & Hxc & Hδ) Hclose]";
      iDestruct (pstates_known with "H0 H1 H2 Hy0") as "(%E0 & H0 & H1 & H2)"; [done |];
      iDestruct (pstates_known with "H0 H1 H2 Hy1") as "(%E1 & H0 & H1 & H2)"; [done |];
      iDestruct (pstates_known with "H0 H1 H2 Hy2") as "(%E2 & H0 & H1 & H2)"; [done |];
      iDestruct "H0" as "(Hs0 & Hx0 & H0)"; iDestruct "H1" as "(Hs1 & Hx1 & H1)";
      iDestruct "H2" as "(Hs2 & Hx2 & H2)";
      iApply (brel_prod3_r [AppRCtx _] with "Hx0 Hx1 Hx2"); iIntros "Hx0 Hx1 Hx2";
      lazymatch goal with
      | H0 : ?f 0 = Some _, H1 : ?f 1 = Some _, H2 : ?f 2 = Some _ |- _ =>
          iEval (rewrite H0 H1 H2 /=)
      end;
      iApply brel_na_close; iFrame "Hclose";
      iSplitL "Hs0 Hx0 H0 Hs1 Hx1 H1 Hs2 Hx2 H2 Hxc Hδ";
      [ iNext; iExists _; iFrame "Hxc Hδ"; rewrite /pstate; iFrame | ];
      brel_cont_l; brel_cont_r;
      iApply (brel_exhaustion (fill k1 _) (fill k2 _));
      [ set_unfold; tauto | set_unfold; tauto
      | iApply "Hrel";
        lazymatch goal with |- context [InjRV (vgval ?y)] => iApply ("HQ" $! (Some y)) end
      | iApply "IH" ].

    (* Party runs are handled by [run_party_spec], not unfolded. *)
    Local Opaque run_party.

    (** One session: the protocol against F_ADD3 and the simulator's leak. *)
    Lemma go_sess_spec N L l1 l2 (f1 f2 lk1 lk2 : val) R :
      na_invP N start_inv -∗
      env_fun_spec L leak_ok lk1 lk2 -∗
      (∀ go1 go2, BREL f1 (ports go1) ≤ f2 (ports go2)
         <|([go1], [go2], GoThy go1 go2) :: ([l1], [l2], NetT l1 l2) :: L|> {{R}}) -∗
      BREL Π_sess c (#ℓs0, #ℓs1, #ℓs2)%V f1 (lk1, net_eps l1)%V
         ≤ (λ: "r", (λ: "f" "leakIn", F_ADD3_sess c (#ℓx0, #ℓx1, #ℓx2)%V "f" "leakIn")%V f2 "r")%V
             (sim_leak c #ℓδ #ℓxc lk2 (net_eps l2))
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
      iDestruct (pstates_take o j with "[$H0 $H1 $H2]") as "[(Hs & Hxj & Hst) Hback]"; first done.
      brel_load_l. brel_load_r.
      destruct (o j) as [xj|] eqn:Hoj.
      - (* party [j] has already run: both sides refuse *)
        rewrite bool_decide_eq_true_2; last by eexists. rewrite /optvg. brel_pures.
        iApply brel_na_close. iFrame "Hclose".
        iSplitL "Hs Hxj Hst Hback Hxc Hδ".
        { iNext.
          iDestruct ("Hback" $! (Some xj) with "[Hs Hxj Hst]") as "(H0 & H1 & H2)".
          { rewrite /pstate bool_decide_eq_true_2; last by eexists. iFrame. }
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
        { rewrite /pstate bool_decide_eq_true_2; last by eexists. iFrame "∗ #". }
        iDestruct "H0" as "(Hs0 & Hx0 & H0)".
        iDestruct "H1" as "(Hs1 & Hx1 & H1)".
        iDestruct "H2" as "(Hs2 & Hx2 & H2)".
        iApply (brel_prod3_r [AppRCtx _; AppRCtx _; PairRCtx _] with "Hx0 Hx1 Hx2").
        iIntros "Hx0 Hx1 Hx2". simpl. brel_pures.
        (* the simulator records [x_c] *)
        destruct (decide (j = cz c)) as [Hjc | Hjc].
        + rewrite (bool_decide_eq_true_2 (#j = #c)); last by rewrite Hjc. brel_pures.
          iDestruct "Hxc" as (vxc) "[Hxc _]". brel_store_r. brel_pures.
          iAssert (∃ v, ℓxc ↦ₛ v ∗ ⌜∀ y, upd o j (Some x) (cz c) = Some y → v = vgval y⌝)%I
            with "[Hxc]" as "Hxc".
          { iExists _. iFrame. iPureIntro. intros y'. rewrite -Hjc upd_at. by intros [= <-]. }
          iDestruct "Hxc" as (vxc') "[Hxc %Hvxc']".
          destruct (prod_opt (upd o j (Some x) 0) (upd o j (Some x) 1) (upd o j (Some x) 2))
            as [y|] eqn:Hy; rewrite /optvg; brel_pures.
          * (* all inputs are in: the simulator sets [δ = y · x_c⁻¹ = x_h · x_{h'}] *)
            destruct (prod_opt_some _ _ Hy) as (a & b & d & Ha & Hb & Hd & ->).
            destruct (proj1 (roles_all (upd o j (Some x)))
                        (ex_intro _ a (ex_intro _ b (ex_intro _ d (conj Ha (conj Hb Hd))))))
              as ([xc0 Hxc0] & [xh Hxh] & [xh' Hxh']).
            iDestruct "Hδ" as (vδ) "[Hδ _]".
            brel_load_r. rewrite (Hvxc' xc0 Hxc0).
            repeat (brel_inv_r || brel_mult_r). brel_pures. brel_store_r. brel_pures.
            iAssert (∃ v, ℓxc ↦ₛ v ∗ ⌜∀ y, upd o j (Some x) (cz c) = Some y → v = vgval y⌝)%I
              with "[Hxc]" as "Hxc".
            { iExists _. iFrame. iPureIntro. intros ? E. rewrite Hxc0 in E. by simplify_eq. }
            iAssert (∃ v, ℓδ ↦ₛ v ∗ ⌜∀ a' b', upd o j (Some x) (hz c) = Some a' →
                        upd o j (Some x) (hz' c) = Some b' → is_Some (upd o j (Some x) (cz c)) →
                        v = vgval (a' * b')%g⌝)%I with "[Hδ]" as "Hδ".
            { iExists _. iFrame. iPureIntro. intros a' b' Ha' Hb' _.
              rewrite Hxh in Ha'. rewrite Hxh' in Hb'. simplify_eq. f_equal.
              by eapply delta_alg. }
            iAssert (pstate 0 (upd o j (Some x) 0) ∗ pstate 1 (upd o j (Some x) 1) ∗
                     pstate 2 (upd o j (Some x) 2))%I
              with "[Hs0 Hx0 H0 Hs1 Hx1 H1 Hs2 Hx2 H2]" as "Hps"; first by iFrame.
            go_tail N k1 k2.
          * (* not all inputs are in yet: δ unchanged *)
            iAssert (∃ v, ℓxc ↦ₛ v ∗ ⌜∀ y, upd o j (Some x) (cz c) = Some y → v = vgval y⌝)%I
              with "[Hxc]" as "Hxc".
            { iExists _. by iFrame. }
            iAssert (∃ v, ℓδ ↦ₛ v ∗ ⌜∀ a b, upd o j (Some x) (hz c) = Some a →
                        upd o j (Some x) (hz' c) = Some b → is_Some (upd o j (Some x) (cz c)) →
                        v = vgval (a * b)%g⌝)%I with "[Hδ]" as "Hδ".
            { iDestruct "Hδ" as (vδ) "[Hδ _]". iExists vδ. iFrame. iPureIntro.
              intros a b Ha Hb Hcs. exfalso. apply (prod_opt_none _ Hy), roles_all.
              split_and!; [done | by eexists | by eexists]. }
            iAssert (pstate 0 (upd o j (Some x) 0) ∗ pstate 1 (upd o j (Some x) 1) ∗
                     pstate 2 (upd o j (Some x) 2))%I
              with "[Hs0 Hx0 H0 Hs1 Hx1 H1 Hs2 Hx2 H2]" as "Hps"; first by iFrame.
            go_tail N k1 k2.
        + rewrite (bool_decide_eq_false_2 (#j = #c)); last by intros [= ?]. brel_pures.
          iAssert (∃ v, ℓxc ↦ₛ v ∗ ⌜∀ y, upd o j (Some x) (cz c) = Some y → v = vgval y⌝)%I
            with "[Hxc]" as "Hxc".
          { iDestruct "Hxc" as (vxc) "[Hxc %Hvxc]". iExists vxc. iFrame. iPureIntro.
            intros y'. rewrite upd_ne; [apply Hvxc | intros ?; by apply Hjc]. }
          iDestruct "Hxc" as (vxc') "[Hxc %Hvxc']".
          destruct (prod_opt (upd o j (Some x) 0) (upd o j (Some x) 1) (upd o j (Some x) 2))
            as [y|] eqn:Hy; rewrite /optvg; brel_pures.
          * (* all inputs are in: the simulator sets [δ = y · x_c⁻¹ = x_h · x_{h'}] *)
            destruct (prod_opt_some _ _ Hy) as (a & b & d & Ha & Hb & Hd & ->).
            destruct (proj1 (roles_all (upd o j (Some x)))
                        (ex_intro _ a (ex_intro _ b (ex_intro _ d (conj Ha (conj Hb Hd))))))
              as ([xc0 Hxc0] & [xh Hxh] & [xh' Hxh']).
            iDestruct "Hδ" as (vδ) "[Hδ _]".
            brel_load_r. rewrite (Hvxc' xc0 Hxc0).
            repeat (brel_inv_r || brel_mult_r). brel_pures. brel_store_r. brel_pures.
            iAssert (∃ v, ℓxc ↦ₛ v ∗ ⌜∀ y, upd o j (Some x) (cz c) = Some y → v = vgval y⌝)%I
              with "[Hxc]" as "Hxc".
            { iExists _. iFrame. iPureIntro. intros ? E. rewrite Hxc0 in E. by simplify_eq. }
            iAssert (∃ v, ℓδ ↦ₛ v ∗ ⌜∀ a' b', upd o j (Some x) (hz c) = Some a' →
                        upd o j (Some x) (hz' c) = Some b' → is_Some (upd o j (Some x) (cz c)) →
                        v = vgval (a' * b')%g⌝)%I with "[Hδ]" as "Hδ".
            { iExists _. iFrame. iPureIntro. intros a' b' Ha' Hb' _.
              rewrite Hxh in Ha'. rewrite Hxh' in Hb'. simplify_eq. f_equal.
              by eapply delta_alg. }
            iAssert (pstate 0 (upd o j (Some x) 0) ∗ pstate 1 (upd o j (Some x) 1) ∗
                     pstate 2 (upd o j (Some x) 2))%I
              with "[Hs0 Hx0 H0 Hs1 Hx1 H1 Hs2 Hx2 H2]" as "Hps"; first by iFrame.
            go_tail N k1 k2.
          * (* not all inputs are in yet: δ unchanged *)
            iAssert (∃ v, ℓxc ↦ₛ v ∗ ⌜∀ y, upd o j (Some x) (cz c) = Some y → v = vgval y⌝)%I
              with "[Hxc]" as "Hxc".
            { iExists _. by iFrame. }
            iAssert (∃ v, ℓδ ↦ₛ v ∗ ⌜∀ a b, upd o j (Some x) (hz c) = Some a →
                        upd o j (Some x) (hz' c) = Some b → is_Some (upd o j (Some x) (cz c)) →
                        v = vgval (a * b)%g⌝)%I with "[Hδ]" as "Hδ".
            { iDestruct "Hδ" as (vδ) "[Hδ _]". iExists vδ. iFrame. iPureIntro.
              intros a b Ha Hb Hcs. exfalso. apply (prod_opt_none _ Hy), roles_all.
              split_and!; [done | by eexists | by eexists]. }
            iAssert (pstate 0 (upd o j (Some x) 0) ∗ pstate 1 (upd o j (Some x) 1) ∗
                     pstate 2 (upd o j (Some x) 2))%I
              with "[Hs0 Hx0 H0 Hs1 Hx1 H1 Hs2 Hx2 H2]" as "Hps"; first by iFrame.
            go_tail N k1 k2.
    Qed.





  End state.

End prf.

(** * Typed infrastructure: the client's row, its ports, and the environment *)

Section typed_infra.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Local Open Scope Z_scope.

  (* The row of the ports, for the client. *)
  Program Definition go_mono (go1 go2 : label) : pmono_prot Σ :=
    {| pmono_prot_car := GoThy go1 go2; pmono_prot_prop := _ |}.
  Next Obligation.
    iIntros (go1 go2 e1 e2 Φ Φ') "#HΦ (%j & %n & %Hj & -> & -> & #HQ)".
    iExists j, n. do 3 (iSplit; first done).
    iIntros "!>" (o). iApply "HΦ". iApply "HQ".
  Qed.

  Definition go_sig (go1 go2 : label) := @SemSig Σ (go_mono go1 go2) (go1, go2).

  Lemma go_pers_mono_row (go1 go2 : label) :
    ⊢ pers_mono_row (iLblSig_to_iLblThy [([go1], [go2], go_sig go1 go2)]).
  Proof.
    iIntros (????) "#HΦΦ'". iIntros (???) "(%H1 & H2)".
    iSplitR "H2"; [iPureIntro; apply H1 |].
    apply list_elem_of_singleton in H1. inversion H1. simplify_eq/=.
    iDestruct "H2" as (?e1' ?e2' ?k1 ?k2 ?S) "(%Hv1 & %HNk1 & %Hv2 & %HNk2 & He1e2 & #Hs1s2)".
    iExists e1', e2', k1, k2, S.
    repeat iSplit; try iPureIntro; try done.
    iModIntro. iIntros (??) "HS". iApply "HΦΦ'". by iApply "Hs1s2".
  Qed.

  Definition go_row (go1 go2 : label) : sem_row Σ :=
    SemRow [([go1], [go2], go_sig go1 go2)] (go_pers_mono_row go1 go2).

  (* The ports are well typed against [go_row]. *)
  Lemma ports_typed go1 go2 :
    let θ := go_row go1 go2 in
    ⊢ ((τ_port θ × τ_port θ) × τ_port θ)%T (ports go1) (ports go2).
  Proof.
    intros θ. rewrite /τ_port /ports /sem_ty_prod /sem_ty_mbang /sem_ty_arr /=.
    iExists _, _, _, _. iSplit; first done. iSplit; first done.
    iSplit; [iExists _, _, _, _; iSplit; first done; iSplit; first done; iSplit |];
      iModIntro; iIntros (w1 w2) "(%n & -> & ->)"; brel_pures;
      (iApply brel_introduction'; first by left);
      iExists _, _, [], [], _;
      do 2 (iSplit; [by iPureIntro|]; iSplit; [iPureIntro; apply NeutralEctx_nil|]);
      (iSplit; [|iIntros (??) "!# H"; iApply "H"]);
      [iExists 0, n | iExists 1, n | iExists 2, n];
      (do 3 (iSplit; first (iPureIntro; done || lia)));
      iIntros "!>" ([y|]); iApply brel_value; iIntros "$ !>"; rewrite /optvg /sem_ty_sum;
      [iExists _, _; iRight; repeat iSplit; try done; by iExists y
      |iExists _, _; iLeft; repeat iSplit; try done
      |iExists _, _; iRight; repeat iSplit; try done; by iExists y
      |iExists _, _; iLeft; repeat iSplit; try done
      |iExists _, _; iRight; repeat iSplit; try done; by iExists y
      |iExists _, _; iLeft; repeat iSplit; try done].
  Qed.

  (* Calling a typed operation of the environment (in row [θ]) from below
     any theory [X] with labels [l1s], [l2s]. *)
  Lemma brel_env_call' l1s l2s X k1 k2 (f1 f2 v1 v2 : val) (τ κ : sem_ty Σ) (θ L : sem_row Σ) R :
    ectx_labels k1 ⊆ l1s →
    ectx_labels k2 ⊆ l2s →
    (τ -{ θ }-> κ)%T f1 f2 -∗
    τ v1 v2 -∗
    (∀ w1 w2, κ w1 w2 -∗
       BREL fill k1 w1 ≤ fill k2 w2
         <|(l1s, l2s, X) :: iLblSig_to_iLblThy (sem_row_union (¡ θ)%R L)|> {{R}}) -∗
    BREL fill k1 (f1 v1) ≤ fill k2 (f2 v2)
      <|(l1s, l2s, X) :: iLblSig_to_iLblThy (sem_row_union (¡ θ)%R L)|> {{R}}.
  Proof.
    iIntros (Hk1 Hk2) "Hf Hv Hk".
    iApply (brel_bind'' _ _ (iLblSig_to_iLblThy (¡ θ)%R) [(l1s, l2s, X)]).
    { rewrite labels_l_cons /=. set_solver. }
    { rewrite labels_r_cons /=. set_solver. }
    { iApply to_iThy_le_intro'. unfold sem_row_union.
      repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app).
      solve_submseteq. }
    rewrite iThyIfMono_iLblSig_to_iThyIfMono.
    iApply (brel_mono OS with "[] [Hf Hv] Hk"); first iApply to_iThy_le_refl.
    rewrite /sem_ty_mbang /sem_ty_arr /=. by iApply "Hf".
  Qed.

  Lemma leak_spec_typed θ L lk1 lk2 :
    (τ_view -{ θ }-> 𝟙)%T lk1 lk2 -∗
    env_fun_spec (iLblSig_to_iLblThy (sem_row_union (¡ θ)%R L)) leak_ok lk1 lk2.
  Proof.
    iIntros "#Hlk !>" (l1s l2s X k1 k2 v S Hk1 Hk2 Hv) "Hk".
    iApply (brel_env_call' with "Hlk [] [Hk]"); [done | done | |].
    - rewrite /τ_view /sem_ty_sum /sem_ty_prod.
      destruct Hv as [[r ->] | (s & t & m & ->)].
      + iExists _, _. iLeft. repeat iSplit; try done. by iExists r.
      + iExists _, _. iRight. repeat iSplit; try done.
        iExists _, _, _, _. repeat iSplit; try done.
        * iExists _, _, _, _. repeat iSplit; try done; by iExists _.
        * by iExists m.
    - by iIntros (w1 w2) "[-> ->]".
  Qed.

  Lemma hdr_spec_typed θ L f1 f2 :
    (τ_hdr -{ θ }-> 𝟙)%T f1 f2 -∗
    env_op_spec (iLblSig_to_iLblThy (sem_row_union (¡ θ)%R L)) f1 f2.
  Proof.
    iIntros "#Hf !>" (l1s l2s k1 k2 s d t S Hk1 Hk2) "Hk".
    iApply (brel_env_call' with "Hf [] [Hk]"); [done | done | |].
    - rewrite /τ_hdr /sem_ty_prod.
      iExists _, _, _, _. repeat iSplit; try done; last by iExists _.
      iExists _, _, _, _. repeat iSplit; try done; by iExists _.
    - by iIntros (w1 w2) "[-> ->]".
  Qed.

End typed_infra.

(** * The real world refines the ideal one, at [τ_ADD3] *)

Lemma sel_0 {A} (a b d : A) : sel a b d 0 = a.
Proof. done. Qed.
Lemma sel_1 {A} (a b d : A) : sel a b d 1 = b.
Proof. done. Qed.
Lemma sel_2 {A} (a b d : A) : sel a b d 2 = d.
Proof. done. Qed.

Section main.
  Context `{!probblazeRGS Σ, !inG Σ (dfrac_agreeR valO)}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Context (c : nat) (Hc : (c < 3)%nat).
  Local Open Scope Z_scope.

  Definition netN : namespace := nroot .@ "add3" .@ "net".
  Definition startN : namespace := nroot .@ "add3" .@ "start".

  Lemma slots_alloc :
    ⊢ |==> ∃ (γx : Z → gname) (γr : Z → Z → gname),
        party_toks γx γr 0 ∗ party_toks γx γr 1 ∗ party_toks γx γr 2.
  Proof.
    iMod slot_alloc as (a0) "Ha0". iMod slot_alloc as (a1) "Ha1". iMod slot_alloc as (a2) "Ha2".
    iMod slot_alloc as (r01) "Hr01". iMod slot_alloc as (r02) "Hr02".
    iMod slot_alloc as (r12) "Hr12". iMod slot_alloc as (r10) "Hr10".
    iMod slot_alloc as (r20) "Hr20". iMod slot_alloc as (r21) "Hr21".
    iModIntro.
    iExists (λ j, sel a0 a1 a2 j), (λ i j, sel (sel r01 r01 r02 j) (sel r10 r12 r12 j) (sel r20 r21 r21 j) i).
    rewrite /party_toks /=. iFrame.
  Qed.

  Lemma R_ADD3_I_ADD3 : ⊢ sem_typed [] (R_ADD3 c) (I_ADD3 c) ⊥ τ_ADD3 [].
  Proof using All.
    iIntros (vs) "!> _".
    rewrite subst_map_is_closed_empty; last is_closed.
    rewrite subst_map_is_closed_empty; last is_closed.
    Local Opaque F_NET_sess Π_sess F_ADD3_sess sim_leak.
    rewrite /R_ADD3 /I_ADD3 /F_NET /Π /S_ADD3 /F_ADD3 /F_NET_gen /functionality_composition /func_comp.
    brel_pures.
    (* the real world's state: Π's flags and the network's mailbox *)
    brel_alloc_l st2 as "Hst2". brel_alloc_l st1 as "Hst1". brel_alloc_l st0 as "Hst0". brel_pures.
    brel_alloc_l m1 as "Hm1". brel_pures.
    (* the ideal world's: F_ADD3's inputs, the simulator's δ and [x_c], its mailbox *)
    brel_alloc_r x2 as "Hx2". brel_pures_r. brel_alloc_r x1 as "Hx1". brel_pures_r.
    brel_alloc_r x0 as "Hx0". brel_pures_r.
    brel_alloc_r d as "Hd". brel_pures_r. brel_alloc_r xc as "Hxc". brel_pures_r.
    rewrite /patch. brel_pures_r. brel_alloc_r m2 as "Hm2".
    (* ghost state and invariants *)
    iMod slots_alloc as (γx γr) "(Ht0 & Ht1 & Ht2)".
    iApply (brel_na_alloc (net_inv m1 m2 (Rmsg c γx γr)) netN).
    iSplitL "Hm1 Hm2".
    { iNext. iExists _, _, ∅, ∅. iFrame. iSplit; [iPureIntro; apply is_tbl_nil|].
      iSplit; [iPureIntro; apply is_tbl_nil|]. by rewrite big_sepM2_empty. }
    iIntros "#Hnet".
    iApply (brel_na_alloc (start_inv c γx γr st0 st1 st2 x0 x1 x2 d xc) startN).
    iSplitL "Hst0 Hst1 Hst2 Hx0 Hx1 Hx2 Hd Hxc Ht0 Ht1 Ht2".
    { iNext. iExists (λ _, None). rewrite /pstate /=. iFrame.
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
    { by iApply (patch_ok c Hc γx γr st0 st1 st2 x0 x1 x2 d xc startN). }
    iIntros (l1 l2). brel_pures.
    (* the protocol against F_ADD3 and the simulator *)
    iApply (go_sess_spec c Hc γx γr st0 st1 st2 x0 x1 x2 d xc startN with "Hstart [] [Hf]").
    { by iApply leak_spec_typed. }
    iIntros (go1 go2).
    (* the client, at its type *)
    iApply (brel_introduction_mono with "[] [Hf]"); last first.
    { iApply ("Hf" $! (go_row go1 go2)). iApply ports_typed. }
    iApply to_iThy_le_intro'. unfold sem_row_union.
    repeat (rewrite -> iLblSig_to_iLblThy_proj; rewrite -> iLblSig_to_iLblThy_app).
    simpl. solve_submseteq.
  Qed.



End main.
