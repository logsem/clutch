(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Core ReLoC rules *)
From stdpp Require Import coPset namespaces.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list.
From self.program_logic Require Import ectx_lifting.
From self.prob_lang Require Import lang spec_rules spec_tactics ctx_subst proofmode.
From self.logrel Require Import model.

Section rules.
  Context `{!prelogrelGS Σ}.
  Implicit Types A : lrel Σ.
  Implicit Types e : expr.
  Implicit Types v w : val.

  Local Existing Instance pure_exec_fill.

  (** * Primitive rules *)

  (** ([fupd_refines] is defined in [logrel_binary.v]) *)

  (** ** Forward reductions on the LHS *)

  Lemma refines_pure_l n
    (K' : list ectx_item) e e' t A ϕ :
    PureExec ϕ n e e' →
    ϕ →
    ▷^n (REL fill K' e' << t : A)
    ⊢ REL fill K' e << t : A.
  Proof.
    intros Hpure Hϕ.
    rewrite refines_eq /refines_def.
    iIntros "IH" (j) "Hs Hnais".
    iModIntro. wp_pures.
    iApply fupd_wp. iApply ("IH" with "Hs Hnais").
  Qed.

  Lemma refines_masked_l E n
    (K' : list ectx_item) e e' t A ϕ :
    PureExec ϕ n e e' →
    ϕ →
    (REL fill K' e' << t @ E : A)
    ⊢ REL fill K' e << t @ E : A.
  Proof.
    intros Hpure Hϕ.
    rewrite refines_eq /refines_def.
    iIntros "IH" (j) "Hs Hnais /=".
    iMod ("IH" with "Hs Hnais") as "IH".
    iModIntro. by wp_pures.
  Qed.

  Lemma refines_wp_l K e1 t A :
    (WP e1 {{ v,
        REL fill K (of_val v) << t : A }})%I -∗
    REL fill K e1 << t : A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "He" (j) "Hs Hnais /=".
    iModIntro. iApply wp_bind.
    iApply (wp_wand with "He").
    iIntros (v) "Hv".
    by iMod ("Hv" with "Hs Hnais").
  Qed.

  Lemma refines_atomic_l (E : coPset) K e1 t A
        (Hatomic : Atomic WeaklyAtomic e1) :
   (|={⊤,E}=> WP e1 @ E {{ v,
     REL fill K (of_val v) << t @ E : A }})%I -∗
   REL fill K e1 << t : A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "Hlog" (j) "Hs Hnais /=". iModIntro.
    iApply wp_bind. iApply wp_atomic; auto.
    iMod "Hlog" as "He". iModIntro.
    iApply (wp_wand with "He").
    iIntros (v) "Hlog".
    by iApply ("Hlog" with "Hs Hnais").
  Qed.

  (** ** Forward reductions on the RHS *)

  Lemma refines_pure_r E K' e e' t A n
    (Hspec : nclose specN ⊆ E) ϕ :
    PureExec ϕ n e e' →
    ϕ →
    (REL t << fill K' e' @ E : A)
    ⊢ REL t << fill K' e @ E : A.
  Proof.
    rewrite refines_eq /refines_def => Hpure Hϕ.
    iIntros "Hlog" (j) "Hj Hnais /=".
    tp_pures j ; auto.
    iApply ("Hlog" with "Hj Hnais").
  Qed.

  Lemma refines_right_bind K' K e :
    refines_right K' (fill K e) ≡ refines_right (K ++ K') e.
  Proof. rewrite /refines_right /=. by rewrite fill_app. Qed.

  Definition refines_right_bind' := refines_right_bind.

  (* A helper lemma for proving the stateful reductions for the RHS below *)
  Lemma refines_step_r E K' e1 e2 A :
    (∀ k, refines_right k e2 ={E}=∗
         ∃ v, refines_right k (of_val v) ∗ REL e1 << fill K' (of_val v) @ E : A) -∗
    REL e1 << fill K' e2 @ E : A.
  Proof.
    rewrite refines_eq /refines_def /=.
    iIntros "He" (K'') "Hs Hnais /=".
    rewrite refines_right_bind /=.
    iMod ("He" with "Hs") as (v) "[Hs He]".
    rewrite -refines_right_bind'.
    iSpecialize ("He" with "Hs Hnais").
    by iApply "He".
  Qed.

  Lemma refines_alloc_r E K e v t A
    (Hmasked : nclose specN ⊆ E) :
    IntoVal e v →
    (∀ l : loc, l ↦ₛ v -∗ REL t << fill K (of_val #l) @ E : A)%I
    -∗ REL t << fill K (ref e) @ E : A.
  Proof.
    rewrite /IntoVal. intros <-.
    iIntros "Hlog". simpl.
    iApply refines_step_r ; simpl.
    iIntros (K') "HK'".
    tp_alloc K' as l "Hl".
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_load_r E K l q v t A
    (Hmasked : nclose specN ⊆ E) :
    l ↦ₛ{q} v -∗
    (l ↦ₛ{q} v -∗ REL t << fill K (of_val v) @ E : A)
    -∗ REL t << (fill K !#l) @ E : A.
  Proof.
    iIntros "Hl Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    tp_load k.
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_store_r E K l e e' v v' A
    (Hmasked : nclose specN ⊆ E) :
    IntoVal e' v' →
    l ↦ₛ v -∗
    (l ↦ₛ v' -∗ REL e << fill K (of_val #()) @ E : A) -∗
    REL e << fill K (#l <- e') @ E : A.
  Proof.
    rewrite /IntoVal. iIntros (<-) "Hl Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk". simpl.
    tp_store k. iModIntro. iExists _. iFrame.
    by iApply "Hlog".
  Qed.

  Lemma refines_alloctape_r E K t A
    (Hmasked : nclose specN ⊆ E) :
    (∀ α : loc, α ↪ₛ [] -∗ REL t << fill K (of_val #lbl:α) @ E : A)%I
    -∗ REL t << fill K alloc @ E : A.
  Proof.
    rewrite /IntoVal.
    iIntros "Hlog".
    iApply refines_step_r.
    iIntros (K') "HK'".
    tp_alloctape K' as α "Hα".
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_flip_r E K α b bs t A
    (Hmasked : nclose specN ⊆ E) :
    α ↪ₛ (b :: bs)
    -∗ (α ↪ₛ bs -∗ REL t << fill K (of_val #b) @ E : A)
    -∗ REL t << (fill K (flip #lbl:α)) @ E : A.
  Proof.
    iIntros "Hα Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    tp_flip k.
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  (** This rule is useful for proving that functions refine each other *)
  Lemma refines_arrow_val (v v' : val) A A' :
    □(∀ v1 v2, A v1 v2 -∗
      REL App v (of_val v1) << App v' (of_val v2) : A') -∗
    REL (of_val v) << (of_val v') : (A → A')%lrel.
  Proof.
    iIntros "#H".
    iApply refines_ret. iModIntro.
    iModIntro. iIntros (v1 v2) "HA".
    iSpecialize ("H" with "HA").
    by iApply "H".
  Qed.

  (** * Some derived (symbolic execution) rules *)

  (** ** Stateful reductions on the LHS *)

  Lemma refines_alloc_l K E e v t A :
    IntoVal e v →
    (|={⊤,E}=> ▷ (∀ l : loc, l ↦ v -∗
           REL fill K (of_val #l) << t @ E : A))%I
    -∗ REL fill K (ref e) << t : A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog". iModIntro.
    wp_alloc l. by iApply "Hlog".
  Qed.

  Lemma refines_load_l K E l q t A :
    (|={⊤,E}=> ∃ v',
      ▷(l ↦{q} v') ∗
      ▷(l ↦{q} v' -∗ (REL fill K (of_val v') << t @ E : A)))%I
    -∗ REL fill K (! #l) << t : A.
  Proof.
    iIntros "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog" as (v') "[Hl Hlog]". iModIntro.
    wp_load. by iApply "Hlog".
  Qed.

  Lemma refines_store_l K E l e v' t A :
    IntoVal e v' →
    (|={⊤,E}=> ∃ v, ▷ l ↦ v ∗
      ▷(l ↦ v' -∗ REL fill K (of_val #()) << t @ E : A))
    -∗ REL fill K (#l <- e) << t : A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog" as (v) "[Hl Hlog]". iModIntro.
    wp_store. by iApply "Hlog".
  Qed.

  Lemma refines_alloctape_l K E t A :
    (|={⊤,E}=> ▷ (∀ α : loc, α ↪ [] -∗
           REL fill K (of_val #lbl:α) << t @ E : A))%I
    -∗ REL fill K alloc << t : A.
  Proof.
    iIntros "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog". iModIntro.
    iApply (wp_alloc_tape _ _ with "[//]"). iIntros "!>" (l) "?". by iApply "Hlog".
  Qed.

  Lemma refines_flip_l E K α b bs t A :
    (|={⊤,E}=> ▷ α ↪ (b :: bs)
               ∗ ▷ (α ↪ bs -∗ REL fill K (of_val #b) << t @ E : A))
    -∗ REL fill K (flip #lbl:α) << t : A.
  Proof.
    iIntros "Hlog".
    iApply refines_atomic_l.
    iMod "Hlog" as "[Hα Hlog]". iModIntro.
    iApply (wp_flip with "Hα").
    by iApply "Hlog".
  Qed.

  Lemma refines_wand E e1 e2 A A' :
    (REL e1 << e2 @ E : A) -∗
    (∀ v1 v2, A v1 v2 ={⊤}=∗ A' v1 v2) -∗
    REL e1 << e2 @ E : A'.
  Proof.
    iIntros "He HAA".
    iApply (refines_bind [] [] with "He").
    iIntros (v v') "HA /=". iApply refines_ret.
    by iApply "HAA".
  Qed.

  Lemma refines_arrow (v v' : val) A A' :
    □ (∀ v1 v2 : val, □(REL of_val v1 << of_val v2 : A) -∗
      REL App v (of_val v1) << App v' (of_val v2) : A') -∗
    REL (of_val v) << (of_val v') : (A → A')%lrel.
  Proof.
    iIntros "#H".
    iApply refines_arrow_val; eauto.
    iModIntro. iIntros (v1 v2) "#HA".
    iApply "H". iModIntro.
    by iApply refines_ret.
  Qed.


  Lemma refines_couple_tapes e1 e2 A α αₛ bs bsₛ :
    to_val e1 = None →
    ((αₛ ↪ₛ bsₛ ∗ α ↪ bs ∗
       ((∃ b, αₛ ↪ₛ (bsₛ ++ [b]) ∗ α ↪ (bs ++ [b]))
       -∗ REL e1 << e2 : A)))
    ⊢ REL e1 << e2 : A.
  Proof.
    iIntros (e1ev) "(Hαs & Hα & Hlog)".
    rewrite refines_eq /refines_def.
    iIntros (K2) "[#Hs He2] Hnais /=".
    iApply wp_couple_tapes ; auto.
    iSplitR ; auto.
    iModIntro. rewrite -fupd_wp.
    iFrame "Hα Hαs".
    iIntros "Hb".
    iApply ("Hlog" with "Hb [Hs He2]") ; now iFrame.
  Qed.

  Lemma refines_couple_tapes_masked E e1 e2 A α αₛ bs bsₛ
    (Hmasked : nclose specN ⊆ E) :
    to_val e1 = None →
    (|={⊤,E}=>
       (αₛ ↪ₛ bsₛ ∗ α ↪ bs ∗
       ((∃ b, αₛ ↪ₛ (bsₛ ++ [b]) ∗ α ↪ (bs ++ [b]))
       -∗ REL e1 << e2 @ E : A)))
    ⊢ REL e1 << e2 : A.
  Proof.
    iIntros (e1ev) "H".
    rewrite refines_eq /refines_def.
    iIntros (K2) "[#Hs He2] Hnais /= !>".
    rewrite wp_unfold /wp_pre /= e1ev.
    iIntros (???) "([Hh1 Ht1] & Hspec)".
    iMod "H" as "(Hαs & Hα & H)".
    iInv specN as (ρ' e0' σ0' n) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hspec Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Htapes Hαs") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    (* Get up to speed with the spec resource (tracked in spec_ctx) *)
    iApply exec_coupl_det_r; [done|].
    (* Do a coupled [state_step] on both sides  *)
    iApply (exec_coupl_state_steps α αₛ).
    { rewrite /= /get_active.
      apply elem_of_list_In, in_prod;
        apply elem_of_list_In, elem_of_elements, elem_of_dom; eauto. }
    iExists _.
    iSplit.
    { iPureIntro. eapply Rcoupl_pos_R, Rcoupl_state_step; by apply elem_of_dom. }
    iIntros (σ2 σ2' ((? & ? & [b [= -> ->]]) & ? & ?)).
    (* Update our resources *)
    iMod (spec_interp_update (e0', (state_upd_tapes <[αₛ:=tapes σ0' !!! αₛ ++ [b]]> σ0'))
           with "Hspec Hspec0") as "[Hspec Hspec0]".
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Htapes Hαs") as %?%lookup_total_correct.
    simplify_map_eq.
    iMod (ghost_map_update (tapes σ1 !!! α ++ [b]) with "Ht1 Hα") as "[Ht1 Hα]".
    iMod (ghost_map_update (tapes σ0' !!! αₛ ++ [b]) with "Htapes Hαs") as "[Htapes Hαs]".
    (* Close the [spec_ctx] invariant again, so the assumption can access all invariants  *)
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, (state_upd_tapes _ _), 0. simpl.
      iFrame. rewrite exec_O dret_1_1 //. }
    (* Our [WP] assumption with the updated resources now suffices to prove the goal *)
    iSpecialize ("H" with "[Hα Hαs] [$Hs $He2] Hnais").
    { iExists _. iFrame. }
    iMod "H".
    rewrite !wp_unfold /wp_pre /= e1ev.
    iMod ("H" $! (state_upd_tapes _ _) with "[$Hh1 $Hspec Ht1]") as "Hwp"; [done|].
    iModIntro. done.
  Qed.

End rules.
