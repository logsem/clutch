From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import excl.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.prelude Require Import options.
From iris.base_logic.lib Require Export ghost_map invariants.

From self.prelude Require Import stdpp_ext.
From self.program_logic Require Export exec weakestpre.
From self.prob_lang Require Import
  primitive_laws class_instances spec_ra tactics notation lang metatheory.
From self.prob Require Export couplings distribution.
Import uPred.

Set Default Proof Using "Type*".
Local Open Scope R.

Section erasure_helpers.

  Variable (m : nat).
  Hypothesis IH :
    ∀ (e1 : expr) (σ1 : state) α bs,
    tapes σ1 !! α = Some bs →
    Rcoupl (prim_exec_val m (e1, σ1))
      (fair_conv_comb
         (prim_exec_val m (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [true]]> σ1))
         (prim_exec_val m (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [false]]> σ1))) eq.

  Local Lemma ind_case_det e σ α bs K :
    tapes σ !! α = Some bs →
    is_det_head_step e σ = true →
    Rcoupl
      (dmap (fill_lift K) (head_step e σ) ≫= prim_exec_val m)
      (fair_conv_comb
         (dmap (fill_lift K) (head_step e (state_upd_tapes <[α:=tapes σ !!! α ++ [true]]> σ)) ≫= prim_exec_val m)
         (dmap (fill_lift K) (head_step e (state_upd_tapes <[α:=tapes σ !!! α ++ [false]]> σ)) ≫= prim_exec_val m))
      eq.
  Proof using m IH.
    intros Hα (e2 & (σ2 & Hdet))%is_det_head_step_true%det_step_pred_ex_rel.
    pose proof (det_head_step_upd_tapes e σ e2 σ2 α true Hdet) as HdetT.
    pose proof (det_head_step_upd_tapes e σ e2 σ2 α false Hdet) as HdetF.
    erewrite det_step_eq_tapes in Hα; [|done].
    erewrite 3!det_head_step_singleton; [|done..].
    rewrite !dmap_dret.
    rewrite !dret_id_left.
    by eapply IH.
  Qed.

  Local Lemma ind_case_dzero e σ α bs K :
    tapes σ !! α = Some bs →
    is_det_head_step e σ = false →
    ¬ det_head_step_pred e σ →
    (∀ σ', σ.(heap) = σ'.(heap) → head_step e σ' = dzero) →
    Rcoupl
      (dmap (fill_lift K) (head_step e σ) ≫= prim_exec_val m)
      (fair_conv_comb
         (dmap (fill_lift K) (head_step e (state_upd_tapes <[α:=tapes σ !!! α ++ [true]]> σ)) ≫= prim_exec_val m)
         (dmap (fill_lift K) (head_step e (state_upd_tapes <[α:=tapes σ !!! α ++ [false]]> σ)) ≫= prim_exec_val m)) eq.
  Proof using m IH.
    intros Hα Hdet Hndet HZ.
    rewrite !HZ //.
    rewrite dmap_dzero dbind_dzero.
    exists dzero; split.
    - split.
      + rewrite /lmarg dmap_dzero; auto.
      + rewrite /rmarg dmap_dzero.
        apply distr_ext=> ?.
        rewrite fair_conv_comb_pmf.
        rewrite /pmf /dzero; lra.
    - intros []. rewrite /pmf /=. lra.
  Qed.

  Local Lemma ind_case_alloc σ α bs K :
    tapes σ !! α = Some bs →
    prob_head_step_pred alloc σ →
    ¬ det_head_step_pred alloc σ →
    is_det_head_step alloc σ = false →
    Rcoupl
      (dmap (fill_lift K) (head_step AllocTape σ) ≫= prim_exec_val m)
      (fair_conv_comb
         (dmap (fill_lift K) (head_step AllocTape (state_upd_tapes <[α:=tapes σ !!! α ++ [true]]> σ)) ≫= prim_exec_val m)
         (dmap (fill_lift K) (head_step AllocTape (state_upd_tapes <[α:=tapes σ !!! α ++ [false]]> σ)) ≫= prim_exec_val m))
      eq.
  Proof using m IH.
    intros Hα HP Hndet Hdet.
    do 3 rewrite head_step_alloc_unfold; simpl.
    rewrite !dmap_dret !dret_id_left.
    assert (fresh_loc (tapes σ) = (fresh_loc (<[α:=tapes σ !!! α ++ [true]]> (tapes σ)))) as <-.
    { eapply fresh_loc_upd_some; eauto. }
    assert (fresh_loc (tapes σ) = (fresh_loc (<[α:=tapes σ !!! α ++ [false]]> (tapes σ)))) as <-.
    { eapply fresh_loc_upd_some; eauto. }
    specialize
      (IH (fill K #lbl:(fresh_loc (tapes σ)))(state_upd_tapes <[fresh_loc (tapes σ):=[]]> σ) α bs).
    apply lookup_total_correct in Hα as Hαtot.
    simpl.
    (* TODO: fix slightly ugly hack :P *)
    revert IH; intro IHm.
    pose proof (elem_fresh_ne _ _ _ Hα) as Hne.
    assert (α ≠ fresh_loc (tapes σ)) as Hne' by auto ; clear Hne.
    rewrite -(upd_diff_tape_tot σ _ _ _ Hne') in IHm.
    specialize (IHm (fresh_loc_lookup σ α bs [] Hα)).
    do 2 (erewrite <-(fresh_loc_upd_swap σ) in IHm; [|done]).
    done.
  Qed.

  Local Lemma ind_case_flip_some σ α α' K b bs bs' :
    tapes σ !! α = Some bs →
    tapes σ !! α' = Some (b :: bs') →
    Rcoupl
      (dmap (fill_lift K) (head_step (flip #lbl:α') σ) ≫= prim_exec_val m)
      (fair_conv_comb
         (dmap (fill_lift K) (head_step (flip #lbl:α') (state_upd_tapes <[α:=tapes σ !!! α ++ [true]]> σ)) ≫= prim_exec_val m)
         (dmap (fill_lift K) (head_step (flip #lbl:α') (state_upd_tapes <[α:=tapes σ !!! α ++ [false]]> σ)) ≫= prim_exec_val m))
      eq.
  Proof using m IH.
    intros Hα Hα'.
    destruct (decide (α = α')) as [-> | Hαneql].
    - rewrite (head_step_flip_nonempty_unfold _ _ b bs') //.
      rewrite (head_step_flip_nonempty_unfold _ _ b (bs' ++ [true])); last first.
      { rewrite app_comm_cons. by apply upd_tape_some. }
      rewrite (head_step_flip_nonempty_unfold _ _ b (bs' ++ [false])); last first.
      { rewrite app_comm_cons. by apply upd_tape_some. }
      rewrite !dmap_dret !dret_id_left.
      erewrite lookup_total_correct; [|done].
      do 2 rewrite upd_tape_twice.
      rewrite (upd_tape_app _ α' bs' [true]).
      rewrite (upd_tape_app _ α' bs' [false]).
      eapply IH. rewrite lookup_insert //.
    - rewrite (head_step_flip_nonempty_unfold _ _ b bs') //.
      rewrite (head_step_flip_nonempty_unfold _ _ b bs'); last first.
      { rewrite -Hα' -upd_diff_tape //. }
      rewrite (head_step_flip_nonempty_unfold _ _ b bs'); last first.
      { rewrite -Hα' -upd_diff_tape //. }
      rewrite !dmap_dret !dret_id_left.
      assert (tapes (state_upd_tapes <[α':=bs']> σ) !! α = Some bs) as Hα''.
      { rewrite lookup_insert_ne //. }
      pose proof (IH (fill K #b) (state_upd_tapes <[α':=bs']> σ) α bs Hα'') as IHm2.
      rewrite upd_diff_tape_comm //.
      rewrite (upd_diff_tape_comm _ α α' bs' (tapes σ !!! α ++ [false])) //.
      rewrite -(upd_diff_tape_tot _ α α' ) // in IHm2.
  Qed.

  Local Lemma ind_case_flip_none σ α α' K bs :
    tapes σ !! α = Some bs →
    (tapes σ !! α' = Some [] ∨ tapes σ !! α' = None) →
    Rcoupl
      (dmap (fill_lift K) (head_step (flip #lbl:α') σ) ≫= prim_exec_val m)
      (fair_conv_comb
         (dmap (fill_lift K) (head_step (flip #lbl:α') (state_upd_tapes <[α:=tapes σ !!! α ++ [true]]> σ)) ≫= prim_exec_val m)
         (dmap (fill_lift K) (head_step (flip #lbl:α') (state_upd_tapes <[α:=tapes σ !!! α ++ [false]]> σ)) ≫= prim_exec_val m))
      eq.
  Proof using m IH.
    intros Hα [Hα' | Hα'].
    - destruct (decide (α = α')) as [-> | Hαneql].
      + rewrite head_step_flip_empty_unfold //.
        rewrite (head_step_flip_nonempty_unfold _ _ true []); last first.
        { rewrite (upd_tape_some σ α' true []) //. }
        rewrite (head_step_flip_nonempty_unfold _ _ false []); last first.
        { rewrite (upd_tape_some σ α' false []) //. }
        rewrite !dmap_dret !dret_id_left.
        rewrite /fair_conv_comb.
        rewrite -!dbind_assoc.
        eapply (Rcoupl_dbind _ _ _ _ (=)); [ | apply Rcoupl_eq].
        intros ? b ->.
        do 2 rewrite upd_tape_twice.
        rewrite -(lookup_total_correct _ _ _ Hα').
        rewrite (upd_tape_some_trivial _ _ []) //.
        destruct b; simpl; do 2 rewrite dret_id_left; apply Rcoupl_eq.
      + rewrite head_step_flip_empty_unfold //.
        rewrite head_step_flip_empty_unfold //; last first.
        { rewrite -upd_diff_tape //. }
        rewrite head_step_flip_empty_unfold; last first.
        { rewrite -upd_diff_tape //. }
        rewrite {3 4}/fair_conv_comb.
        rewrite -!dbind_assoc.
        rewrite -(dbind_fair_conv_comb _ _ fair_coin).
        rewrite /fair_conv_comb.
        eapply Rcoupl_dbind; [|apply Rcoupl_eq].
        intros ? [] ->; rewrite !dret_id_left; by eapply IH.
    - destruct (decide (α = α')) as [-> | Hαneql]; [simplify_map_eq|].
      rewrite head_step_flip_unalloc_unfold //.
      rewrite head_step_flip_unalloc_unfold //; last first.
      { rewrite -Hα' -upd_diff_tape //. }
      rewrite head_step_flip_unalloc_unfold; last first.
      { rewrite -Hα' -upd_diff_tape //. }
      rewrite {3 4}/fair_conv_comb.
      rewrite -!dbind_assoc.
      erewrite <- (dbind_fair_conv_comb _ _ fair_coin).
      rewrite /fair_conv_comb.
      eapply Rcoupl_dbind; [|apply Rcoupl_eq].
      intros ? [] ->; rewrite !dret_id_left; by eapply IH.
  Qed.

  Local Lemma ind_case_flip_no_tapes (σ : state) (α : loc) K :
    Rcoupl
      (dmap (fill_lift K) (head_step (flip #()) σ) ≫= prim_exec m)
      (fair_conv_comb
         (dmap (fill_lift K)
            (head_step (flip #())
               (state_upd_tapes <[α:=tapes σ !!! α ++ [true]]> σ)) ≫= prim_exec m)
         (dmap (fill_lift K)
            (head_step (flip #())
               (state_upd_tapes <[α:=tapes σ !!! α ++ [false]]> σ)) ≫= prim_exec m))
      pure_eq.
  Proof using m IH. Admitted.

End erasure_helpers.

Lemma prim_coupl_upd_tapes_dom m e1 σ1 α bs :
  σ1.(tapes) !! α = Some bs →
  Rcoupl
    (prim_exec_val m (e1, σ1))
    (fair_conv_comb
       (prim_exec_val m (e1, (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [true]]> σ1)))
       (prim_exec_val m (e1, (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [false]]> σ1))))
    eq.
Proof.
  revert e1 σ1 α bs; induction m; intros e1 σ1 α bs Hα.
  - rewrite /prim_exec_val/=.
    destruct (to_val e1) eqn:He1.
    + exists (dprod (dret v)
                (fair_conv_comb
                   (dret v)
                   (dret v))).
      split; [split ; [rewrite lmarg_dprod //|rewrite rmarg_dprod //] |].
      { erewrite SeriesC_ext; [ | intro; rewrite fair_conv_comb_pmf; done].
        rewrite SeriesC_plus;
          [rewrite SeriesC_scal_l; rewrite dret_mass; lra | | ];
          apply ex_seriesC_scal_l; apply pmf_ex_seriesC. }
      { apply dret_mass. }
      intros (v2 & v2') Hpos. simpl.
      rewrite /pmf/= in Hpos.
      rewrite fair_conv_comb_pmf in Hpos.
      assert (dret v v2 > 0 ∧ dret v v2' > 0) as (Hpos1 & Hpos2).
      { (* This is a fact about the reals, maybe it can be done easier *)
        apply Rgt_lt in Hpos.
        assert (0.5+0.5 = 1) as Hhalf; [lra | ].
        rewrite -Rmult_plus_distr_r Hhalf Rmult_1_l in Hpos.
        apply pos_prod_nn_real in Hpos; try lra; auto. }
      { apply dret_pos in Hpos1, Hpos2. by simplify_eq. }
    + exists dzero. repeat split_and!.
      * rewrite /lmarg dmap_dzero //.
      * apply distr_ext=>?.
        rewrite rmarg_pmf fair_conv_comb_pmf /pmf /=.
        rewrite SeriesC_0 //. lra.
      * intros ?. rewrite /pmf /=. lra.
  - simpl. destruct (to_val e1) eqn:He1.
    + specialize (IHm e1 σ1 α bs Hα).
      destruct m; simpl in *; by rewrite He1 in IHm.
    + rewrite /prim_step /=.
      destruct (decomp e1) as [K ered] eqn:decomp_e1.
      rewrite decomp_e1.
      destruct (is_det_head_step ered σ1) eqn:Hdet.
      * by eapply ind_case_det.
      * assert (¬ det_head_step_pred ered σ1) as Hndet.
        { intros ?%is_det_head_step_true. rewrite H // in Hdet. }
        destruct (det_or_prob_or_dzero ered σ1) as [ HD | [HP | HZ]].
        { by destruct Hndet. }
        { inversion HP; simplify_eq.
          - by eapply ind_case_alloc.
          - by eapply ind_case_flip_some.
          - by eapply ind_case_flip_none.
          - by eapply ind_case_flip_no_tapes. }
        { by eapply ind_case_dzero. }
Qed.

Lemma prim_coupl_step_prim m e1 σ1 α bs :
  σ1.(tapes) !! α = Some bs →
  Rcoupl
    (prim_exec_val m (e1, σ1))
    (state_step σ1 α ≫= (λ σ2, prim_exec_val m (e1, σ2)))
    eq.
Proof.
  intros Hα.
  rewrite state_step_fair_conv_comb; last first.
  { apply elem_of_dom. eauto. }
  rewrite fair_conv_comb_dbind.
  do 2 rewrite dret_id_left.
  by eapply prim_coupl_upd_tapes_dom.
Qed.

Lemma limprim_coupl_step_limprim e1 σ1 α bs :
  σ1.(tapes) !! α = Some bs →
  Rcoupl
    (lim_prim_exec_val (e1, σ1))
    (state_step σ1 α ≫= (λ σ2, lim_prim_exec_val (e1, σ2)))
    eq.
Proof.
  (* Hopefully there is some continuity argument using the previous lemma *)
  (* intros; rewrite state_step_fair_conv_comb fair_conv_comb_dbind. *)
  (* do 2 rewrite dret_id_left. *)
Admitted.

Lemma refRcoupl_erasure e1 σ1 e1' σ1' α α' R Φ m bs bs':
  σ1.(tapes) !! α = Some bs →
  σ1'.(tapes) !! α' = Some bs' →
  Rcoupl (state_step σ1 α) (state_step σ1' α') R →
  (∀ σ2 σ2', R σ2 σ2' →
             refRcoupl (prim_exec_val m (e1, σ2))
               (lim_prim_exec_val (e1', σ2')) Φ ) →
  refRcoupl (prim_exec_val m (e1, σ1))
    (lim_prim_exec_val (e1', σ1')) Φ.
Proof.
  intros Hα Hα' HR Hcont.
  eapply refRcoupl_eq_refRcoupl_unfoldl ;
    [eapply prim_coupl_step_prim; eauto |].
  eapply refRcoupl_eq_refRcoupl_unfoldr;
    [| eapply Rcoupl_eq_sym, limprim_coupl_step_limprim; eauto].
  apply (refRcoupl_dbind _ _ _ _ R); auto.
  by eapply Rcoupl_refRcoupl.
Qed.

(* TODO: upstream? *)
Section fupd_plainly_derived.
  Context {PROP : bi}.
  Context `{!BiFUpd PROP, !BiPlainly PROP, !BiFUpdPlainly PROP}.

  Lemma step_fupd_mono Eo Ei (P Q : PROP) :
    (P ⊢ Q) → (|={Eo}[Ei]▷=> P) ⊢ (|={Eo}[Ei]▷=> Q).
  Proof. intros HPQ. by apply fupd_mono, later_mono, fupd_mono. Qed.

  Lemma step_fupd_except_0 E1 E2 (P : PROP) : (|={E1}[E2]▷=> ◇ P) ={E1}[E2]▷=∗ P.
  Proof. rewrite fupd_except_0 //. Qed.

  Lemma step_fupdN_except_0 E1 E2 (P : PROP) n : (|={E1}[E2]▷=>^(S n) ◇ P) ={E1}[E2]▷=∗^(S n) P.
  Proof.
    induction n as [|n IH]; [apply step_fupd_except_0|].
    replace (S (S n)) with (1 + S n)%nat by lia.
    rewrite 2!step_fupdN_add. by apply step_fupd_mono.
  Qed.

  Lemma step_fupdN_plain_forall E {A} (Φ : A → PROP) `{!∀ x, Plain (Φ x)} n :
    (|={E}▷=>^n ∀ x, Φ x) ⊣⊢ (∀ x, |={E}▷=>^n Φ x).
  Proof .
    intros. apply (anti_symm _).
    { apply forall_intro=> x. apply step_fupdN_mono. eauto. }
    destruct n; [done|].
    trans (∀ x, |={E}=> ▷^(S n) ◇ Φ x)%I.
    { apply forall_mono=> x. by rewrite step_fupdN_plain. }
    rewrite -fupd_plain_forall'.
    rewrite -step_fupdN_except_0 /= -step_fupdN_intro //.
    apply fupd_elim.
    rewrite -later_forall -laterN_forall -except_0_forall.
    apply step_fupd_intro. done.
  Qed.

End fupd_plainly_derived.

Section class_instance_updates.
  Context {PROP : bi}.

  Global Instance from_forall_step_fupdN
    `{!BiFUpd PROP, !BiPlainly PROP, !BiFUpdPlainly PROP} E {A} P (Φ : A → PROP) name n :
    FromForall P Φ name → (∀ x, Plain (Φ x)) →
    FromForall (|={E}▷=>^n P) (λ a, |={E}▷=>^n (Φ a))%I name.
  Proof.
    rewrite /FromForall=>? ?.
    rewrite -step_fupdN_plain_forall. by apply step_fupdN_mono.
  Qed.
End class_instance_updates.

Section adequacy.
  Context `{!prelocGS Σ}.

  Lemma refRcoupl_dbind' `{Countable A, Countable A', Countable B, Countable B'}
    (f : A → distr A') (g : B → distr B') (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (T : A' → B' → Prop) n :
    ⌜refRcoupl μ1 μ2 R⌝ -∗
    (∀ a b, ⌜R a b⌝ ={∅}▷=∗^(S n) ⌜refRcoupl (f a) (g b) T⌝) -∗
    |={∅}▷=>^(S n) ⌜refRcoupl (dbind f μ1) (dbind g μ2) T⌝ : iProp Σ.
  Proof.
    iIntros (HR) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a b, R a b → refRcoupl (f a) (g b) T)⌝)).
    { iIntros (?). iPureIntro. by eapply refRcoupl_dbind. }
    iIntros (???) "/=".
    iMod ("H" with "[//]"); auto.
  Qed.

  Lemma exec_coupl_erasure (e1 : expr) (σ1 : state) (e1' : expr) (σ1' : state) (n : nat) φ :
    to_val e1 = None →
    exec_coupl e1 σ1 e1' σ1' (λ '(e2, σ2) '(e2', σ2'),
        |={∅}▷=>^(S n) ⌜refRcoupl (prim_exec_val n (e2, σ2)) (lim_prim_exec_val (e2', σ2')) φ⌝)
    ⊢ |={∅}▷=>^(S n) ⌜refRcoupl (prim_exec_val (S n) (e1, σ1)) (lim_prim_exec_val (e1', σ1')) φ⌝.
  Proof.
    iIntros (Hv) "Hexec".
    iAssert (⌜to_val e1 = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /exec_coupl /exec_coupl'.
    set (Φ := (λ '((e1, σ1), (e1', σ1')),
                (⌜to_val e1 = None⌝ ={∅}▷=∗^(S n)
                 ⌜refRcoupl (prim_exec_val (S n) (e1, σ1))
                            (lim_prim_exec_val (e1', σ1')) φ⌝)%I) :
           prodO cfgO cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros m ((?&?)&(?&?)) ((?&?)&(?&?)) [[[=] [=]] [[=] [=]]]. by simplify_eq. }
    set (F := (exec_coupl_pre (λ '(e2, σ2) '(e2', σ2'),
                   |={∅}▷=>^(S n) ⌜refRcoupl (prim_exec_val n (e2, σ2))
                     (lim_prim_exec_val (e2', σ2')) φ⌝)%I)).
    iPoseProof (least_fixpoint_iter F Φ with "[]") as "H"; last first.
    { iIntros "Hfix %". by iMod ("H" $! ((_, _), (_, _)) with "Hfix [//]"). }
    clear.
    iIntros "!#" ([[e1 σ1] [e1' σ1']]). rewrite /exec_coupl_pre.
    iIntros "[(%R & % & %Hcpl & H) | [(%R & % & %Hcpl & H) | [(%R & %m & %Hcpl & H) | H]]] %Hv".
    - rewrite prim_exec_val_Sn_not_val; [|done].
      rewrite -bind_lim_prim_exec.
      destruct (to_val e1') eqn:Hv'.
      + destruct (decide (prim_step e1 σ1 = dzero)) as [Hs|].
        * rewrite /= Hs dbind_dzero.
          do 3 iModIntro. iApply step_fupdN_intro; [done|].
          iModIntro. iPureIntro.
          apply refRcoupl_dzero.
        * assert (prim_step e1' σ1' = dzero) as Hz by by apply val_stuck_dzero.
          rewrite /= (val_stuck_dzero e1') in Hcpl; [|eauto].
          by apply Rcoupl_dzero_r_inv in Hcpl.
      + rewrite prim_step_or_val_no_val; [|done].
        iApply (refRcoupl_dbind' _ _ _ _ R).
        { iPureIntro. by apply Rcoupl_refRcoupl. }
        iIntros ([] [] HR). by iMod ("H" with "[//]").
    - rewrite prim_exec_val_Sn_not_val; [|done].
      rewrite -(dret_id_left (lim_prim_exec_val)).
      iApply refRcoupl_dbind'.
      { iPureIntro. apply Rcoupl_pos_R in Hcpl. by apply Rcoupl_refRcoupl. }
      iIntros ([] [] (?&?& [= -> ->]%dret_pos)).
      by iMod ("H"  with "[//]").
    - rewrite -(dret_id_left (prim_exec_val _)).
      rewrite (lim_prim_exec_exec m).
      iApply refRcoupl_dbind'.
      { iPureIntro. apply Rcoupl_pos_R in Hcpl. by apply Rcoupl_refRcoupl. }
      iIntros ([] [] (?& [= -> ->]%dret_pos &?)).
      by iMod ("H"  with "[//] [//]").
    - rewrite prim_exec_val_Sn_not_val; [|done].
      iDestruct (big_orL_mono _ (λ _ _,
                     |={∅}▷=>^(S n)
                       ⌜refRcoupl (prim_step e1 σ1 ≫= prim_exec_val n)
                                  (lim_prim_exec_val (e1', σ1')) φ⌝)%I
                  with "H") as "H".
      { iIntros (i [α1 α2] [Hα1 Hα2]%elem_of_list_lookup_2%elem_of_list_prod_1) "(% & %Hcpl & H)".
        rewrite -prim_exec_val_Sn_not_val; [|done].
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ σ2 σ2', R2 σ2 σ2' → refRcoupl (prim_exec_val (S n) (e1, σ2))
                                                    (lim_prim_exec_val (e1', σ2')) φ⌝)%I).
        - iIntros (?). iPureIntro.
          rewrite /= /get_active in Hα1, Hα2.
          apply elem_of_elements, elem_of_dom in Hα1 as [], Hα2 as [].
          eapply refRcoupl_erasure; eauto.
        - iIntros (???). by iMod ("H" with "[//] [//]"). }
      iInduction (list_prod (language.get_active σ1) (language.get_active σ1'))
        as [| [α α']] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[H | Ht]"; [done|].
      by iApply "IH".
  Qed.

  Theorem wp_coupling (e e' : expr) (σ σ' : state) n φ :
    state_interp σ ∗ spec_interp (e', σ') ∗ spec_ctx ∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜refRcoupl (prim_exec_val n (e, σ)) (lim_prim_exec_val (e', σ')) φ⌝.
  Proof.
    iInduction n as [|n] "IH" forall (e σ e' σ'); iIntros "([Hh Ht] & HspecI_auth & #Hctx & Hwp)".
    - rewrite /prim_exec /=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite wp_value_fupd.
        iMod "Hwp" as (v') "[Hspec_frag %]".
        iInv specN as (ρ e0 σ0 n) ">(HspecI_frag & %Hexec & Hspec_auth & Hstate)" "_".
        iDestruct (spec_interp_auth_frag_agree with "HspecI_auth HspecI_frag") as %<-.
        iDestruct (spec_prog_auth_frag_agree with "Hspec_auth Hspec_frag") as %->.
        iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        erewrite lim_prim_exec_exec_val; [|done].
        iPureIntro.
        rewrite /dmap.
        by apply refRcoupl_dret.
      + iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iPureIntro.
        apply refRcoupl_dzero.
    - rewrite prim_exec_val_Sn /prim_step_or_val /=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite wp_value_fupd.
        iMod "Hwp" as (v') "[Hspec_frag %]".
        iInv specN as (ξ ρ e0 σ0) ">(HspecI_frag & %Hexec & Hspec_auth & Hstate)" "_".
        iDestruct (spec_interp_auth_frag_agree with "HspecI_auth HspecI_frag") as %<-.
        iDestruct (spec_prog_auth_frag_agree with "Hspec_auth Hspec_frag") as %->.
        iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iApply step_fupdN_intro; [done|]. do 4 iModIntro.
        iPureIntro.
        rewrite prim_exec_val_unfold dret_id_left /=.
        erewrite lim_prim_exec_exec_val; [|done].
        by apply refRcoupl_dret.
      + rewrite wp_unfold /wp_pre /= Heq.
        iMod ("Hwp" with "[$]") as "Hcpl".
        iModIntro.
        iPoseProof
          (exec_coupl_mono _ (λ '(e2, σ2) '(e2', σ2'), |={∅}▷=>^(S n)
             ⌜refRcoupl (prim_exec_val n (e2, σ2)) (lim_prim_exec_val (e2', σ2')) φ⌝)%I
            with "[] Hcpl") as "H".
        { iIntros ([] []) "H !> !>".
          iMod "H" as "(Hstate & HspecI_auth & Hwp)".
          iMod ("IH" with "[$]") as "H".
          iModIntro. done. }
        rewrite -prim_exec_val_Sn_not_val; [|done].
        by iApply (exec_coupl_erasure with "H").
  Qed.

End adequacy.

Class prelocGpreS Σ := PrelocGpreS {
  prelocGpreS_iris  :> invGpreS Σ;
  prelocGpreS_heap  :> ghost_mapG Σ loc val;
  prelocGpreS_tapes :> ghost_mapG Σ loc (list bool);
  prelocGpreS_cfg   :> inG Σ (authUR cfgUR);
  prelocGpreS_prog  :> inG Σ (authR progUR);
}.

Definition prelocΣ : gFunctors :=
  #[invΣ; ghost_mapΣ loc val; ghost_mapΣ loc (list bool);
    GFunctor (authUR cfgUR); GFunctor (authUR progUR)].
Global Instance subG_prelocGPreS {Σ} : subG prelocΣ Σ → prelocGpreS Σ.
Proof. solve_inG. Qed.


Theorem wp_adequacy Σ `{prelocGpreS Σ} (e e' : expr) (σ σ' : state) n φ :
  (∀ `{prelocGS Σ}, ⊢ spec_ctx -∗ ⤇ e' -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }}) →
  refRcoupl (prim_exec_val n (e, σ)) (lim_prim_exec_val (e', σ')) φ.
Proof.
  intros Hwp.
  eapply (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod (ghost_map_alloc σ'.(heap)) as "[%γHs [Hh_spec _]]".
  iMod (ghost_map_alloc σ'.(tapes)) as "[%γTs [Ht_spec _]]".
  iMod (own_alloc ((● (Excl' (e', σ'))) ⋅ (◯ (Excl' (e', σ'))))) as "(%γsi & Hsi_auth & Hsi_frag)".
  { by apply auth_both_valid_discrete. }
  iMod (own_alloc ((● (Excl' e')) ⋅ (◯ (Excl' e')))) as "(%γp & Hprog_auth & Hprog_frag)".
  { by apply auth_both_valid_discrete. }
  set (HspecGS := CfgSG Σ _ γsi _ γp _ _ γHs γTs).
  set (HprelocGS := HeapG Σ _ _ _ γH γT HspecGS).
  iMod (inv_alloc specN ⊤ spec_inv with "[Hsi_frag Hprog_auth Hh_spec Ht_spec]") as "#Hctx".
  { iModIntro. iExists _, _, _, O. iFrame. rewrite exec_O dret_1_1 //. }
  iApply wp_coupling.
  iFrame. iFrame "Hctx".
  by iApply (Hwp with "[Hctx] [Hprog_frag]").
Qed.
