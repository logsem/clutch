(** * Coupling rules  *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.app_rel_logic Require Import lifting ectx_lifting.
From clutch.prob_lang Require Import lang notation tactics metatheory.
From clutch.app_rel_logic Require Export primitive_laws spec_rules.
From clutch.app_rel_logic Require Export seq_amplification.
Require Import Lra.


Section rules.
  Context `{!clutchGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.
  Implicit Types ε : nonnegreal.

  Lemma wp_couple_tapes (N M : nat) E e α αₛ ns nsₛ Φ (ε : nonnegreal) :
    to_val e = None →
    (∀ σ1, reducible e σ1) →
    nclose specN ⊆ E →
    (N <= M)%R →
    (((S M - S N) / S N) = ε)%R →
    spec_ctx ∗
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗
    € ε ∗
    (∀ (n : fin (S N)) (m : fin (S M)),
        ⌜(fin_to_nat n = m)⌝ →
        α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) -∗
        WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He Hred ? NMpos NMε) "(#Hinv & >Hα & >Hαₛ & Hε & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iInv specN as (ρ' e0' σ0' n_spec_steps) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Htapes Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplitR ; [done|].
    (* Get up to speed with the spec resource (tracked in spec_ctx) *)
    iApply exec_coupl_det_r; [done|].
    (* split ε_now into ε + (ε_now - ε) *)
    iDestruct (ec_supply_bound with "Hε2 Hε") as %Hle.
    set (ε' := nnreal_minus ε_now ε Hle ).
    replace ε_now with (nnreal_plus ε ε'); last first.
    { apply nnreal_ext; simpl; lra. }
    (* Do a coupled [state_step] on both sides  *)
    iApply (exec_coupl_state_steps α αₛ).
    { rewrite /= /get_active.
      apply elem_of_list_In, in_prod;
        apply elem_of_list_In, elem_of_elements, elem_of_dom; auto. }
    iExists _.
    iSplit.
    { iPureIntro.
      eapply ARcoupl_state_state ; eauto.
    }
    iIntros (σ2 σ2' (n & m & nm & ? & ?)).
    (* Update our resources *)
    iMod (spec_interp_update (e0', (state_upd_tapes <[αₛ:=(M; nsₛ ++ [m]) : tape]> σ0'))
           with "Hauth2 Hspec0") as "[Hauth2 Hspec0]".
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Htapes Hαₛ") as %?%lookup_total_correct.
    simplify_map_eq.
    iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
    iMod (ghost_map_update ((M; nsₛ ++ [m]) : tape) with "Htapes Hαₛ") as "[Htapes Hαₛ]".
    (* Update Hε2 *)
    iMod (ec_decrease_supply with "Hε2 Hε") as "Hε2".
    (* Close the [spec_ctx] invariant again, so the assumption can access all invariants *)
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, (state_upd_tapes _ _), 0. simpl.
      iFrame. rewrite exec_O dret_1_1 //. }
    (* Our [WP] assumption with the updated resources now suffices to prove the goal *)
    iSpecialize ("Hwp" $! n m nm with "[$Hα $Hαₛ]").
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! (state_upd_tapes <[α:=(N; ns ++ [n]) : tape]> _)
           with "[$Hh1 $Hauth2 $Ht1 $Hε2]") as "[Hred Hwp]".
    iModIntro. done.
  Qed.

  Lemma wp_couple_tapes_rev (N M : nat) E e α αₛ ns nsₛ Φ (ε : nonnegreal) :
    to_val e = None →
    (∀ σ1, reducible e σ1) →
    nclose specN ⊆ E →
    (M <= N)%R →
    (((S N - S M) / S N) = ε)%R →
    spec_ctx ∗
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗
    € ε ∗
    (∀ (n : fin (S N)) (m : fin (S M)),
        ⌜(fin_to_nat n = m)⌝ →
        α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) -∗
        WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He Hred ? NMpos NMε) "(#Hinv & >Hα & >Hαₛ & Hε & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iInv specN as (ρ' e0' σ0' n_spec_steps) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Htapes Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplitR ; [done|].
    (* Get up to speed with the spec resource (tracked in spec_ctx) *)
    iApply exec_coupl_det_r; [done|].
    (* split ε_now into ε + (ε_now - ε) *)
    iDestruct (ec_supply_bound with "Hε2 Hε") as %Hle.
    set (ε' := nnreal_minus ε_now ε Hle ).
    replace ε_now with (nnreal_plus ε ε'); last first.
    { apply nnreal_ext; simpl; lra. }
    (* Do a coupled [state_step] on both sides  *)
    iApply (exec_coupl_state_steps α αₛ).
    { rewrite /= /get_active.
      apply elem_of_list_In, in_prod;
        apply elem_of_list_In, elem_of_elements, elem_of_dom; auto. }
    iExists _.
    iSplit.
    { iPureIntro.
      eapply ARcoupl_state_state_rev ; eauto.
    }
    iIntros (σ2 σ2' (n & m & nm & ? & ?)).
    (* Update our resources *)
    iMod (spec_interp_update (e0', (state_upd_tapes <[αₛ:=(M; nsₛ ++ [m]) : tape]> σ0'))
           with "Hauth2 Hspec0") as "[Hauth2 Hspec0]".
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Htapes Hαₛ") as %?%lookup_total_correct.
    simplify_map_eq.
    iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
    iMod (ghost_map_update ((M; nsₛ ++ [m]) : tape) with "Htapes Hαₛ") as "[Htapes Hαₛ]".
    (* Update Hε2 *)
    iMod (ec_decrease_supply with "Hε2 Hε") as "Hε2".
    (* Close the [spec_ctx] invariant again, so the assumption can access all invariants *)
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, (state_upd_tapes _ _), 0. simpl.
      iFrame. rewrite exec_O dret_1_1 //. }
    (* Our [WP] assumption with the updated resources now suffices to prove the goal *)
    iSpecialize ("Hwp" $! n m nm with "[$Hα $Hαₛ]").
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! (state_upd_tapes <[α:=(N; ns ++ [n]) : tape]> _)
           with "[$Hh1 $Hauth2 $Ht1 $Hε2]") as "[Hred Hwp]".
    iModIntro. done.
  Qed.

  Lemma wp_couple_no_coll_rand K N z E (x : Fin.t N) Φ ε :
    nclose specN ⊆ E →
    (0 < S N)%R →
    ((1 / S N) = ε)%R →
    N = Z.to_nat z →
    € ε ∗
    refines_right K (rand #z from #()) ∗
    (∀ (n : fin (S N)),
        ⌜(fin_to_nat n ≠ x)⌝ →
        refines_right K #n -∗
        WP (let: "x" := of_val #(fin_to_nat x) in "x") @ E {{ Φ }})
    ⊢ WP (let: "x" := of_val #(fin_to_nat x) in "x") @ E {{ Φ }}.
  Proof.
    iIntros (? Npos Nε Nz) "(Hε & [#Hinv Hj] &  Hwp)".
    iApply wp_lift_step_fupd_couple ; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iInv specN as (ρ' e0' σ0' n_spec_steps) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    (* iDestruct (ghost_map_lookup with "Htapes Hαₛ") as %?. *)
    (* iDestruct (ghost_map_lookup with "Ht1 Hα") as %?. *)
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplitR. { (* iPureIntro. *)
               (* replace (#() ;; #x)%E with (fill [AppLCtx #()] (λ:<>, #x))%E by auto. *)
               (* apply head_prim_fill_reducible. *)
               (* eexists (_, _). *)
               (* apply head_step_support_equiv_rel. *)
               (* eapply RecS. *) admit. }
    (* Get up to speed with the spec resource (tracked in spec_ctx) *)
    iApply exec_coupl_det_r; [done|].
    (* split ε_now into ε + (ε_now - ε) *)
    iDestruct (ec_supply_bound with "Hε2 Hε") as %Hle.
    set (ε' := nnreal_minus ε_now ε Hle ).
    replace ε_now with (nnreal_plus ε ε') by (apply nnreal_ext; simpl; lra).
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    From clutch.rel_logic Require Import proofmode.
    (* wp_bind #x. *)
    set (e := (let: "x" := #x in "x")%E).
    (* Unset Printing Notations. Set Printing Coercions. *)
    replace e with (fill [AppRCtx (λ:"x", "x")] (Val #x))%E by reflexivity.
    (* Do a coupled [state_step] on both sides  *)
    iApply (exec_coupl_exec_r).
  Abort.

  Lemma wp_couple_rand_no_coll K N z E (x : Fin.t N) Φ ε :
    nclose specN ⊆ E →
    (0 < S N)%R →
    ((1 / S N) = ε)%R →
    N = Z.to_nat z →
    € ε ∗
    refines_right K #x ∗
    (∀ (n : fin (S N)),
        ⌜(fin_to_nat n ≠ x)⌝ →
        refines_right K #x -∗
        WP (Val #n) @ E {{ Φ }})
    ⊢ WP (rand #z from #()) @ E {{ Φ }}.
  Proof.
    iIntros (? Npos Nε Nz) "(Hε & [#Hinv Hj] &  Hwp)".
    iApply wp_lift_step_fupd_couple ; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iInv specN as (ρ' e0' σ0' n_spec_steps) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    (* iDestruct (ghost_map_lookup with "Htapes Hαₛ") as %?. *)
    (* iDestruct (ghost_map_lookup with "Ht1 Hα") as %?. *)
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplitR. { (* iPureIntro. *)
               (* replace (#() ;; #x)%E with (fill [AppLCtx #()] (λ:<>, #x))%E by auto. *)
               (* apply head_prim_fill_reducible. *)
               (* eexists (_, _). *)
               (* apply head_step_support_equiv_rel. *)
               (* eapply RecS. *) admit. }
    (* Get up to speed with the spec resource (tracked in spec_ctx) *)
    iApply exec_coupl_det_r; [done|].
    (* split ε_now into ε + (ε_now - ε) *)
    iDestruct (ec_supply_bound with "Hε2 Hε") as %Hle.
    set (ε' := nnreal_minus ε_now ε Hle ).
    replace ε_now with (nnreal_plus ε ε') by (apply nnreal_ext; simpl; lra).
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hj") as %->.
    From clutch.rel_logic Require Import proofmode.
    (* wp_bind #x. *)
    set (e := (let: "x" := #x in "x")%E).
    (* Unset Printing Notations. Set Printing Coercions. *)
    replace e with (fill [AppRCtx (λ:"x", "x")] (Val #x))%E by reflexivity.
    (* Do a coupled [state_step] on both sides  *)
    iApply (exec_coupl_exec_r).

  Abort.

  (** * rand(unit, N) ~ rand(unit, M) coupling, N <= M *)
  Lemma wp_couple_rand_rand (N M : nat) z w K E Φ (ε : nonnegreal) :
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat w) →
    nclose specN ⊆ E →
    (N <= M)%R ->
    (((S M - S N) / S N) = ε)%R →
    refines_right K (rand #w from #()) ∗
    € ε ∗
    ▷ (∀ (n : fin (S N)) (m : fin (S M)),
        ⌜(fin_to_nat n = m)⌝ →
        refines_right K #m  -∗ WP (Val #n) @ E {{ Φ }})
    ⊢ WP rand #z from #() @ E {{ Φ }}.
  Proof.
    iIntros (-> -> ? HNM Hε) "([#Hinv Hr ] & Hε & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iInv specN as (ρ' e0' σ0' m) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_prog_auth_frag_agree with "Hauth Hr") as %->.
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplit.
    { iPureIntro. apply head_prim_reducible.
      eexists (Val #0%fin, σ1).
      apply head_step_support_equiv_rel.
      by eapply (RandNoTapeS _ _ 0%fin). }
    iDestruct (ec_supply_bound with "Hε2 Hε") as %Hle.
    set (ε' := nnreal_minus ε_now ε Hle ).
    replace ε_now with (nnreal_plus ε ε'); last first.
    { apply nnreal_ext; simpl; lra. }
    iApply exec_coupl_det_r; [done|].
    iApply exec_coupl_prim_steps.
    iExists (λ '(e2, σ2) '(e2', σ2'),
        ∃ (n : fin _) (m : fin _),
        (fin_to_nat n = m) ∧
        (e2, σ2) = (Val #n, σ1) ∧ (e2', σ2') = (fill K #m, σ0')).
    iSplit.
    { iPureIntro. apply head_prim_reducible.
      eexists (Val #0%fin, σ1).
      apply head_step_support_equiv_rel.
      by eapply (RandNoTapeS _ _ 0%fin). }
    iSplit.
    { iPureIntro. simpl.
      rewrite fill_dmap // -(dret_id_right (prim_step _ _)) /=.
      rewrite /dmap /=.
      replace ε with (nnreal_plus ε nnreal_zero); last first.
      { apply nnreal_ext; simpl; lra. }
      eapply ARcoupl_dbind.
      1,2:apply cond_nonneg.
      2:eapply ARcoupl_rand_rand; eauto.
      intros [] [] (b & ? & ? & [=] & [=])=>/=.
      apply ARcoupl_dret.
      simplify_eq. eauto. }
    iIntros ([] [] (b & b' & Hbb' & [= -> ->] & [= -> ->])).
    simplify_eq.
    iMod (spec_interp_update (fill K #b', σ0') with "Hauth2 Hspec0") as "[Hauth2 Hspec0]".
    iMod (spec_prog_update (fill K #b')  with "Hauth Hr") as "[Hauth Hr]".
    iMod (ec_decrease_supply with "Hε2 Hε") as "Hε2".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, _, 0. simpl.
      iFrame. rewrite exec_O dret_1_1 //. }
    iModIntro. iFrame.
    iApply "Hwp"; eauto.
    iSplit; done.
  Qed.

  Lemma ec_spend_irrel ε1 ε2 : (ε1.(nonneg) = ε2.(nonneg)) → € ε1 -∗ € ε2.
  Proof. Admitted.

  Lemma ec_spend_1 ε1 : (1 <= ε1.(nonneg))%R → € ε1 -∗ False.
  Proof. Admitted.

  (** advanced composition on one tape *)
  (* not really sure what this lemma will look like in the real version? *)
  Lemma presample_adv_comp (N : nat) α ns (ε : nonnegreal) (ε2 : fin (S N) -> nonnegreal) :
    SeriesC (λ n, (1 / (S N)) * ε2 n)%R = (nonneg ε) →
    (α ↪ (N; ns) ∗ € ε) -∗ (∃ s, (α ↪ (N; ns ++ [s])) ∗ €(ε2 s)).
  Proof. Admitted.

  Lemma amplification_depth N L (ε : posreal) (kwf : kwf N L) : exists n : nat, (1 <= ε * (k N L kwf) ^ n)%R.
  Proof.
    (* shouldn't be too hard, it's the log *)
  Admitted.


  Lemma lookup_ex {A} (n : nat) (L : list A) : (n < length L)%nat -> exists x, (L !! n) = Some x.
  Proof.
    (* can't figure out how to do this with existing lemmas! *)
    intros HL.
    destruct L as [|h H]; [simpl in HL; lia|].
    generalize dependent H. generalize dependent h.
    induction n as [|n' IH].
    - intros h ? ?. exists h; by simpl.
    - intros h H HL.
      rewrite cons_length in HL; apply Arith_prebase.lt_S_n in HL.
      destruct H as [|h' H']; [simpl in HL; lia|].
      replace ((h :: h' :: H') !! S n') with ((h' :: H') !! n'); last by simpl.
      by apply IH.
  Qed.


  (* whenever i is strictly less than l (ie, (S i) <= l) we can amplify *)
  (* we'll need another rule for spending?, but that should be simple *)
  Lemma presample_amplify' N L kwf prefix (suffix_total suffix_remaining : list (fin (S N))) 𝛼 (ε : posreal) :
    ⊢ ⌜ L = length suffix_total ⌝ →
      ⌜ (0 < L)%nat ⌝ →
      𝛼 ↪ (N; prefix) -∗
      (€ (pos_to_nn ε)) -∗
      ∀ (i : nat),
        (∀ (HL : (i <= L)%nat),
            (∃ junk, 𝛼 ↪ (N; prefix ++ junk) ∗ €(εAmp N L ε kwf)) ∨
            ((𝛼 ↪ (N; prefix ++ (take i suffix_total))) ∗
              € (εR N L i ε (mk_fRwf N L i kwf HL)))).
  Proof.
    iIntros (Htotal HLpos) "Htape Hcr_initial"; iIntros (i).
    iInduction i as [|i'] "IH" forall (suffix_remaining).
    - iIntros (HL).
      iRight. iSplitL "Htape".
      + rewrite take_0 -app_nil_end. iFrame.
      + iApply ec_spend_irrel; last iFrame.
        rewrite /εR /fR /pos_to_nn /=; lra.
    - iIntros "%HL".
      assert (HL' : (i' <= L)%nat) by lia.
      iSpecialize ("IH" $! _ with "Htape Hcr_initial").
      iSpecialize ("IH" $! HL').
      iDestruct "IH" as "[[%junk(Htape&Hcr)]|(Htape&Hcr)]".
      + iLeft; iExists junk; iFrame.
      +
        (* we need to do something different dependning on if (S i') is L? No. in that case we still need 1 amp*)
        assert (Hi' : (i' < length suffix_total)%nat) by lia.
        destruct (lookup_ex i' suffix_total Hi') as [target Htarget].
        rewrite (take_S_r _ _ target); [|apply Htarget].
        pose M := (εDistr_mean N L i' ε target (mk_fRwf N L (S i') kwf HL)).
        iPoseProof (presample_adv_comp N 𝛼
                     (prefix ++ take i' suffix_total)
                     (εR N L i' ε (fRwf_dec_i N L i' _)) (εDistr N L i' ε target _) M) as "PS".
        replace {| k_wf := kwf; i_ub := HL' |} with(fRwf_dec_i N L i' {| k_wf := kwf; i_ub := HL |});
          last by apply fRwf_ext.
        iSpecialize ("PS" with "[Htape Hcr]"); first iFrame.
        iDestruct "PS" as "[%s (Htape&Hcr)]".
        (* NOW we can destruct and decide if we're left or right *)
        rewrite /εDistr.
        case_bool_decide.
        * iRight. rewrite H app_assoc. iFrame.
        * iLeft. iExists (take i' suffix_total ++ [s]).
          replace (k_wf N L (S i') {| k_wf := kwf; i_ub := HL |}) with kwf; last by apply kwf_ext.
          rewrite -app_assoc; iFrame.
      Unshelve. auto.
  Qed.

  (* do one step in the amplification sequence *)
  Lemma presample_amplify N L prefix suffix 𝛼 (ε : posreal) (kwf: kwf N L) :
    L = (length suffix) ->
    € (pos_to_nn ε) -∗
    (𝛼 ↪ (N; prefix)) -∗
    (𝛼 ↪ (N; prefix ++ suffix) ∨ (∃ junk, 𝛼 ↪ (N; prefix ++ junk) ∗ €(εAmp N L ε kwf))).
  Proof.
    iIntros (Hl) "Hcr Htape".

    destruct suffix as [|s0 sr].
    - iLeft. rewrite -app_nil_end. iFrame.
    - remember (s0 :: sr) as suffix.
      assert (Hl_pos : (0 < L)%nat).
      { rewrite Hl Heqsuffix cons_length. lia. }
      iPoseProof (presample_amplify' N L _ prefix suffix suffix 𝛼 ε $! Hl Hl_pos) as "X".
      iSpecialize ("X" with "Htape Hcr").
      iSpecialize ("X" $! L (le_n L)).
      iDestruct "X" as "[H|(H&_)]".
      + iRight. iApply "H".
      + iLeft. rewrite Hl firstn_all. iFrame.
  Qed.


  Lemma seq_amplify N L d prefix suffix 𝛼 (ε : posreal) (kwf: kwf N L) :
    L = (length suffix) ->
    € (pos_to_nn ε) -∗
    (𝛼 ↪ (N; prefix)) -∗
    (∃ junk,
        𝛼 ↪ (N; prefix ++ junk ++ suffix) ∨ 𝛼 ↪ (N; prefix ++ junk) ∗ €(pos_to_nn (εAmp_iter N L d ε kwf))).
  Proof.
    iIntros (HL) "Hcr Htape".
    iInduction (d) as [|d'] "IH".
    - iExists []; rewrite app_nil_r. iRight. iFrame.
      iApply ec_spend_irrel; last auto.
      by rewrite /εAmp_iter /pos_to_nn /= Rmult_1_r.
    - iDestruct ("IH" with "Hcr Htape") as "[%junk [Hlucky|(Htape&Hcr)]]".
      + iExists junk; iLeft; iFrame.
      + rewrite -εAmp_iter_cmp.
        iPoseProof (presample_amplify N L (prefix ++ junk) suffix 𝛼 (εAmp_iter N L d' ε kwf)) as "X"; try auto.
        iDestruct ("X" with "Hcr Htape") as "[Hlucky|[%junk' (Htape&Hcr)]]".
        * iExists junk; iLeft. rewrite -app_assoc; iFrame.
        * iExists (junk ++ junk'); iRight.
          rewrite app_assoc; iFrame.
  Qed.


  Lemma presample_planner N prefix suffix 𝛼 ε (HN : (0 < N)%nat) (HL : (0 < (length suffix))%nat) (Hε : (0 < ε)%R) :
    € ε -∗
    (𝛼 ↪ (N; prefix)) -∗
    (∃ junk, 𝛼 ↪ (N; prefix ++ junk ++ suffix)).
  Proof.
    iIntros "Hcr Htape".
    (* make the interface match the other coupling rules *)
    remember (length suffix) as L.
    assert (kwf : kwf N L). { apply mk_kwf; lia. }
    pose ε' := mkposreal ε.(nonneg) Hε.
    replace ε with (pos_to_nn ε'); last first.
    { rewrite /ε' /pos_to_nn. by apply nnreal_ext. }

    destruct (amplification_depth N L ε' kwf) as [d Hdepth].
    iDestruct ((seq_amplify N L d prefix suffix 𝛼 ε' kwf) with "Hcr Htape") as "[%junk [?|(_&Hcr)]]"; auto.
    iExFalso; iApply ec_spend_1; last iFrame.
    Set Printing Coercions.
    rewrite /pos_to_nn /εAmp_iter /=.
    replace (nonneg ε) with (pos ε') by auto.
    done.
  Qed.

End rules.
