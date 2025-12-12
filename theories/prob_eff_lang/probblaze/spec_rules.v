(** Rules for updating the specification program. *)
From Coq Require Export Reals Psatz.
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.common Require Import locations.
From clutch.prob_eff_lang.probblaze Require Import  notation primitive_laws semantics syntax.
From clutch.prob_eff_lang.probblaze Require Export spec_ra.

Section rules.
  Context `{!specG_blaze_prob_lang Σ, invGS_gen hasLc Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.
  Implicit Types ℓ : label.

  (* Move the following to exec_lang *)
  Lemma stepN_det_step_ctx K n ρ (e1 e2 : expr) σ1 σ2 :
    prim_step e1 σ1 (e2, σ2) = 1%R →
    stepN n ρ (fill K e1, σ1) = 1%R →
    stepN (S n) ρ (fill K e2, σ2) = 1%R.
  Proof.
    intros.
    rewrite -Nat.add_1_r.
    erewrite (stepN_det_trans n 1); [done|done|].
    rewrite stepN_Sn /=.
    rewrite dret_id_right.
    rewrite -semantics.fill_step_prob; [done| |].
    - eapply (val_stuck _ σ1 (e2, σ2)).
      rewrite H0. lra.
    - eapply (prim_step_uncaught_eff _ σ1 e2 σ2). rewrite H0. lra.
  Qed.
  
  Lemma stepN_PureExec_ctx K (P : Prop) m n ρ (e e' : expr) σ :
    P →
    PureExec P n e e' →
    stepN m ρ (fill K e, σ) = 1 →
    stepN (m + n) ρ (fill K e', σ) = 1.
  Proof.
    move=> HP /(_ HP).
    destruct ρ as [e0 σ0].
    revert e e' m. induction n=> e e' m.
    { rewrite -plus_n_O. by inversion 1. }
    intros (e'' & Hsteps & Hpstep)%nsteps_inv_r Hdet.
    specialize (IHn _ _ m Hsteps Hdet).
    rewrite -plus_n_Sm. simpl in *.
    eapply stepN_det_step_ctx; [by apply pure_step_det|done].
  Qed.
  
  (** Pure reductions *)
  Lemma step_pure E K e e' (P : Prop) n:
    P →
    PureExec P n e e' →
    ⤇ fill K e ⊢ spec_update E (⤇ fill K e').
  Proof.
    iIntros (HP Hex) "HK". rewrite spec_update_unseal.
    iIntros ([??]) "Hs".
    iDestruct (spec_auth_prog_agree with "[$] [$]") as "->".
    iMod (spec_update_prog (fill K e') with "[$][$]") as "[HK Hs]".
    iModIntro. iExists _, n. iFrame. iPureIntro.
    eapply (stepN_PureExec_ctx K P 0); [done|done|].
    rewrite dret_1_1 //.
  Qed.

  Ltac solve_step :=
  simpl;
  match goal with
  | |- (prim_step _ _).(pmf) _ = 1%R  =>
      rewrite head_prim_step_eq /= ;
        simplify_map_eq ; solve_distr
  | |- (head_step _ _).(pmf) _ = 1%R  => simplify_map_eq; solve_distr
  | |- (head_step _ _).(pmf) _ > 0%R  => eauto with head_step
  end.


  (** Alloc, load, and store *)
  Lemma step_alloc E K e v :
    IntoVal e v →
    ⤇ fill K (ref e) ⊢ spec_update E (∃ l, ⤇ fill K (#l) ∗ l ↦ₛ v).
  Proof.
    iIntros (<-) "HK". rewrite spec_update_unseal.
    iIntros ([? σ]) "Hs".
    iDestruct (spec_auth_prog_agree with "[$] [$]") as "->".
    iMod (spec_auth_heap_alloc with "Hs") as "[Hs Hl]".
    iMod (spec_update_prog (fill K _) with "[$][$]") as "[HK Hs]".
    iModIntro. iExists (fill K _, _), 1.
    iFrame "HK".
    iSplit; last first.
    { iExists _. iFrame. }
    iPureIntro.
    apply (stepN_det_step_ctx K 0 (fill K (ref (language.of_val v)), σ) (ref (language.of_val v))  #(fresh_loc (heap σ)) σ); [|by apply dret_1_1].
    setoid_rewrite head_prim_step_eq.
    - simplify_map_eq. apply dret_1_1. rewrite state_init_heap_singleton. done.
    - eexists. apply head_step_support_equiv_rel. constructor; eauto.
  Qed.

  Lemma step_load E K l q v:
    ⤇ fill K (!#l) ∗ l ↦ₛ{q} v
    ⊢ spec_update E (⤇ fill K (of_val v) ∗ l ↦ₛ{q} v).
  Proof.
    iIntros "[HK Hl]". rewrite spec_update_unseal.
    iIntros ([? σ]) "Hs".
    iDestruct (spec_auth_prog_agree with "[$] [$]") as "->".
    iMod (spec_update_prog (fill K v) with "[$][$]") as "[Hauth Hj]".
    iDestruct (spec_auth_lookup_heap with "Hauth Hl") as %?.
    iModIntro. iExists _, 1. iFrame.
    iPureIntro.
    eapply stepN_det_step_ctx; [|by apply dret_1_1].
    setoid_rewrite head_prim_step_eq.
    - simplify_map_eq. solve_distr. 
    - eexists. apply head_step_support_equiv_rel. constructor; eauto.
  Qed.

  Lemma step_store E K l v' e v:
    IntoVal e v →
    ⤇ fill K (#l <- e) ∗ l ↦ₛ v'
    ⊢ spec_update E (⤇ fill K #(()%V) ∗ l ↦ₛ v).
  Proof.
    iIntros (<-) "[HK Hl]". rewrite spec_update_unseal.
    iIntros ([? σ]) "Hs".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "->".
    iMod (spec_update_prog  (fill K #(()%V)) with "[$][$]") as "[Hauth Hj]".
    iDestruct (spec_auth_lookup_heap with "Hauth Hl") as %?.
    iMod (spec_auth_update_heap with "Hauth Hl") as "[Hauth $]".
    iModIntro. iExists (fill K #(()%V), state_upd_heap <[l:=v]> σ), 1.
    iFrame. iPureIntro.
    eapply stepN_det_step_ctx; [|by apply dret_1_1].
    setoid_rewrite head_prim_step_eq.
    - simplify_map_eq. solve_distr. 
    - eexists. apply head_step_support_equiv_rel. econstructor; eauto.
  Qed.

  (** AllocTape and Rand (non-empty tape)  *)
  Lemma step_alloctape E K N z :
    TCEq N (Z.to_nat z) →
    ⤇ fill K (alloc #z) ⊢ spec_update E (∃ l, ⤇ fill K (#lbl:l) ∗ l ↪ₛ (N; [])).
  Proof.
    iIntros (->) "HK". rewrite spec_update_unseal.
    iIntros ([? σ]) "Hs".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "->".
    iMod (spec_update_prog (fill K #(LitLbl (fresh_loc σ.(tapes)))) with "[$] [$]") as "[Hauth Hj]".
    iMod (spec_auth_tape_alloc with "Hauth") as "[Hauth Hl]".
    iModIntro. iExists _, 1. iFrame.
    iPureIntro.
    eapply stepN_det_step_ctx; [|by apply dret_1_1].
    setoid_rewrite head_prim_step_eq.
    - simplify_map_eq. solve_distr. 
    - eexists. apply head_step_support_equiv_rel. econstructor; eauto.
  Qed.

  Lemma step_rand E K l N z n ns :
    TCEq N (Z.to_nat z) →
    ⤇ fill K (rand(#lbl:l) #z) ∗ l ↪ₛ (N; n :: ns)
      ⊢ spec_update E (⤇ fill K #n ∗ l ↪ₛ (N; ns)).
  Proof.
    iIntros (->) "[HK Hl]". rewrite spec_update_unseal.
    iIntros ([? σ]) "Hs".
    iDestruct (spec_auth_prog_agree with "[$][$]") as "->".
    iMod (spec_update_prog (fill K #n) with "[$] [$]") as "[Hauth Hj]".
    iDestruct (spec_auth_lookup_tape with "Hauth Hl") as %?.
    iMod (spec_auth_update_tape with "Hauth Hl") as "[Hauth $]".
    iModIntro. iExists (fill K #n, (state_upd_tapes <[l:=_]> σ)), 1.
    iFrame.
    iPureIntro.
    eapply stepN_det_step_ctx; [|by apply dret_1_1].
    setoid_rewrite head_prim_step_eq.
    - simplify_map_eq. rewrite bool_decide_eq_true_2; [by apply dret_1_1|done].
    - eexists. apply head_step_support_equiv_rel. econstructor; eauto.
  Qed.


  (** AllocTape and Rand (nat tape)  *)
  Lemma step_allocnattape E K N z :
    TCEq N (Z.to_nat z) →
    ⤇ fill K (alloc #z) ⊢ spec_update E (∃ l, ⤇ fill K (#lbl:l) ∗ l ↪ₛN (N; [])).
  Proof.
    iIntros (->) "HK".
    iMod (step_alloctape with "HK") as (l) "(HK & Hl)".
    rewrite spec_update_unseal.
    iIntros ([? σ]) "Hs".
    iModIntro.
    iExists _,0. iFrame.
    iPureIntro.
    split; [|done].
    rewrite stepN_O //.
    by apply dret_1.
  Qed.


  Lemma step_randnat E K l N z n ns :
    TCEq N (Z.to_nat z) →
    ⤇ fill K (rand(#lbl:l) #z) ∗ l ↪ₛN (N; n :: ns)
      ⊢ spec_update E (⤇ fill K #n ∗ ⌜ n ≤ N ⌝ ∗ l ↪ₛN (N; ns)).
  Proof.
    iIntros (->) "[HK Hl]".
    iDestruct (read_spec_tape_head with "Hl") as (x xs) "(Hl&<-&Hcont)".
    iMod (step_rand with "[$HK $Hl]") as "(HK & Hl)".
    iDestruct ("Hcont" with "Hl") as "Hl".
    rewrite spec_update_unseal.
    iIntros ([? σ]) "Hs".
    iModIntro.
    iExists _,0. iFrame.
    iPureIntro.
    split; [| pose proof (fin_to_nat_lt x); lia].
    rewrite stepN_O //.
    by apply dret_1.
  Qed.
 
  (** Effect *)
  Lemma step_alloc_label E K s e :
    ⤇ fill K (Effect s e) ⊢
    spec_update E (∃ (ℓ : label), ⤇ fill K (lbl_subst s ℓ e) ∗ spec_labels_frag ℓ (DfracOwn 1)).
  Proof.
    iIntros "HK". rewrite spec_update_unseal.
    iIntros ([? σ]) "(Hprog&Hheap&Htapes&Hlabels)".
    iDestruct (spec_auth_prog_agree with "[$] [$]") as "->".
    set (ℓ := next_label σ).
    iMod (ghost_map_insert ℓ () with "Hlabels") as "[Hlabels Hl]".
    { by apply lookup_to_labels_None. } 
    iExists (fill K (lbl_subst s ℓ e), (state_upd_next_label label_succ σ)). rewrite -to_labels_succ.
    iMod (spec_update_prog (fill K _) _ (state_upd_next_label label_succ σ) with "[$][$]") as "[HK Hs]"; last first.
    iModIntro. iExists 1.
    iFrame "HK".
    iSplit; last first.
    { iExists _. iFrame. }
    iPureIntro.
    eapply stepN_det_step_ctx ; [|by apply dret_1_1].
    setoid_rewrite head_prim_step_eq.
    - simplify_map_eq. apply dret_1_1.  done.
    - eexists. apply head_step_support_equiv_rel. constructor; eauto.
  Qed.

  Lemma step_handle_os E K K' hs (l : label) (e : expr) (v : val) (h ret : expr) :
    let C := match hs with Deep => HandleCtx hs OS l h ret :: K' | Shallow => K' end in
    IntoVal e v →
    l ∉ ectx_labels K' →
    ⤇ fill K (Handle hs OS (EffLabel l) (fill K' (Do (EffLabel l) e)) h ret) ⊢
    spec_update E ( ∃ (r : loc), ⤇ fill K (App (App h v) (ContV r C)) ∗ unshotₛ r).
  Proof.
    iIntros (? <- ?) "HK". 
    rewrite spec_update_unseal.
    iIntros ([? σ]) "Hs".
    iDestruct (spec_auth_prog_agree with "[$] [$]") as "->".
    iMod (spec_auth_heap_alloc with "Hs") as "[Hs Hl]".
    iMod (spec_update_prog (fill K _) with "[$][$]") as "[HK Hs]".
    iModIntro. iExists (fill K _, _), 1.
    iFrame "HK".
    iSplit; last first.
    { iExists _. iFrame. }
    iPureIntro. eapply stepN_det_step_ctx; [|by apply dret_1_1].
    setoid_rewrite head_prim_step_eq.
    - simplify_map_eq. rewrite to_of_eff. case_decide; [|done]. rewrite decide_True; last done.
      apply dret_1_1.  done.
    - eexists. apply head_step_support_equiv_rel. constructor; eauto.
      by rewrite to_of_eff.
  Qed.

  Lemma step_cont E K K' (e : expr) (v : val) (r : loc) :
    IntoVal e v →
    unshotₛ r -∗
    ⤇ fill K (App (ContV r K') e) -∗ spec_update E ( ⤇ fill K (fill K' v)).
  Proof.
    iIntros (<-) "Hr HK". 
    rewrite spec_update_unseal.
    iIntros ([? σ]) "Hs".
    iDestruct (spec_auth_prog_agree with "[$] [$]") as "->".
    iDestruct (spec_auth_lookup_heap with "[$][$]") as %?.
    iMod (spec_update_prog (fill K _) with "[$][$]") as "[Hs HK]".
    iMod (spec_auth_update_heap (#false)with "[$][$]") as "[Hs Hr]".
    iModIntro. iExists (fill K _, _), 1.
    iFrame "HK".
    iSplit; last iFrame.
    iPureIntro. eapply stepN_det_step_ctx; [|by apply dret_1_1].
    setoid_rewrite head_prim_step_eq.
    - simplify_map_eq. by apply dret_1_1. 
    - eexists. apply head_step_support_equiv_rel. constructor; eauto.
  Qed.

End rules.

