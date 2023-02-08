From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Lim_seq.
From stdpp Require Import fin_maps fin_map_dom.
From self.program_logic Require Import language ectx_language exec.
From self.prob_lang Require Import locations notation lang metatheory.
From self.prob Require Import couplings.

Set Default Proof Using "Type*".
Local Open Scope R.

Section erasure_helpers.

  Variable (m : nat).
  Hypothesis IH :
    ∀ (e1 : expr) (σ1 : state) α bs,
    tapes σ1 !! α = Some bs →
    Rcoupl (exec_val m (e1, σ1))
      (fair_conv_comb
         (exec_val m (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [true]]> σ1))
         (exec_val m (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [false]]> σ1))) eq.

  Local Lemma ind_case_det e σ α bs K :
    tapes σ !! α = Some bs →
    is_det_head_step e σ = true →
    Rcoupl
      (dmap (fill_lift K) (head_step e σ) ≫= exec_val m)
      (fair_conv_comb
         (dmap (fill_lift K) (head_step e (state_upd_tapes <[α:=tapes σ !!! α ++ [true]]> σ)) ≫= exec_val m)
         (dmap (fill_lift K) (head_step e (state_upd_tapes <[α:=tapes σ !!! α ++ [false]]> σ)) ≫= exec_val m))
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
      (dmap (fill_lift K) (head_step e σ) ≫= exec_val m)
      (fair_conv_comb
         (dmap (fill_lift K) (head_step e (state_upd_tapes <[α:=tapes σ !!! α ++ [true]]> σ)) ≫= exec_val m)
         (dmap (fill_lift K) (head_step e (state_upd_tapes <[α:=tapes σ !!! α ++ [false]]> σ)) ≫= exec_val m)) eq.
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
      (dmap (fill_lift K) (head_step AllocTape σ) ≫= exec_val m)
      (fair_conv_comb
         (dmap (fill_lift K) (head_step AllocTape (state_upd_tapes <[α:=tapes σ !!! α ++ [true]]> σ)) ≫= exec_val m)
         (dmap (fill_lift K) (head_step AllocTape (state_upd_tapes <[α:=tapes σ !!! α ++ [false]]> σ)) ≫= exec_val m))
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
      (dmap (fill_lift K) (head_step (flip #lbl:α') σ) ≫= exec_val m)
      (fair_conv_comb
         (dmap (fill_lift K) (head_step (flip #lbl:α') (state_upd_tapes <[α:=tapes σ !!! α ++ [true]]> σ)) ≫= exec_val m)
         (dmap (fill_lift K) (head_step (flip #lbl:α') (state_upd_tapes <[α:=tapes σ !!! α ++ [false]]> σ)) ≫= exec_val m))
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
      (dmap (fill_lift K) (head_step (flip #lbl:α') σ) ≫= exec_val m)
      (fair_conv_comb
         (dmap (fill_lift K) (head_step (flip #lbl:α') (state_upd_tapes <[α:=tapes σ !!! α ++ [true]]> σ)) ≫= exec_val m)
         (dmap (fill_lift K) (head_step (flip #lbl:α') (state_upd_tapes <[α:=tapes σ !!! α ++ [false]]> σ)) ≫= exec_val m))
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

  Local Lemma ind_case_flip_no_tapes (σ : state) (α : loc) K bs :
    tapes σ !! α = Some bs →
    Rcoupl
      (dmap (fill_lift K) (head_step (flip #()) σ) ≫= exec_val m)
      (fair_conv_comb
         (dmap (fill_lift K)
            (head_step (flip #())
               (state_upd_tapes <[α:=tapes σ !!! α ++ [true]]> σ)) ≫= exec_val m)
         (dmap (fill_lift K)
            (head_step (flip #())
               (state_upd_tapes <[α:=tapes σ !!! α ++ [false]]> σ)) ≫= exec_val m))
      eq.
  Proof using m IH.
    intros Hα.
    rewrite !head_step_flip_no_tape_unfold.
    rewrite -!dbind_assoc -/exec_val.
    rewrite -(dbind_fair_conv_comb _ _ fair_coin).
    eapply Rcoupl_dbind; [|apply Rcoupl_eq].
    intros ? [] ->; rewrite !dret_id_left; by eapply IH.
  Qed.

End erasure_helpers.

Lemma prim_coupl_upd_tapes_dom m e1 σ1 α bs :
  σ1.(tapes) !! α = Some bs →
  Rcoupl
    (exec_val m (e1, σ1))
    (fair_conv_comb
       (exec_val m (e1, (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [true]]> σ1)))
       (exec_val m (e1, (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [false]]> σ1))))
    eq.
Proof.
  revert e1 σ1 α bs; induction m; intros e1 σ1 α bs Hα.
  - rewrite /exec_val/=.
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
      { apply Rgt_lt in Hpos.
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
    (exec_val m (e1, σ1))
    (state_step σ1 α ≫= (λ σ2, exec_val m (e1, σ2)))
    eq.
Proof.
  intros Hα.
  rewrite state_step_fair_conv_comb; last first.
  { apply elem_of_dom. eauto. }
  rewrite fair_conv_comb_dbind.
  do 2 rewrite dret_id_left.
  by eapply prim_coupl_upd_tapes_dom.
Qed.



Lemma limprim_coupl_step_limprim_aux e1 σ1 α bs v:
  σ1.(tapes) !! α = Some bs →
  (lim_exec_val (e1, σ1)) v =
  (state_step σ1 α ≫= (λ σ2, lim_exec_val (e1, σ2))) v.
Proof.
  intro Hsome.
   rewrite lim_exec_val_rw/=.
   rewrite {2}/pmf/=/dbind_pmf.
   setoid_rewrite lim_exec_val_rw.
   simpl in *.
   assert
     (SeriesC (λ a: state, state_step σ1 α a * Sup_seq (λ n : nat, exec_val n (e1, a) v)) =
     SeriesC (λ a: state, Sup_seq (λ n : nat, state_step σ1 α a * exec_val n (e1, a) v))) as Haux.
   { apply SeriesC_ext; intro v'.
     apply eq_rbar_finite.
     rewrite rmult_finite.
     rewrite (rbar_finite_real_eq (Sup_seq (λ n : nat, exec_val n (e1, v') v))); auto.
     - rewrite <- (Sup_seq_scal_l (state_step σ1 α v') (λ n : nat, exec_val n (e1, v') v)); auto.
     - apply (Rbar_le_sandwich 0 1).
       + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
       + apply upper_bound_ge_sup; intro; simpl; auto.
   }
   rewrite Haux.
   rewrite (MCT_seriesC _ (λ n, exec_val n (e1,σ1) v) (lim_exec_val (e1,σ1) v)); auto.
   - intros; apply Rmult_le_pos; auto.
   - intros.
     apply Rmult_le_compat; auto; [apply Rle_refl | apply exec_val_mon]; auto.
   - intro.
     exists (state_step σ1 α a); intro.
     rewrite <- Rmult_1_r.
     apply Rmult_le_compat_l; auto.
   - intro n.
     rewrite (Rcoupl_eq_elim _ _ (prim_coupl_step_prim n e1 σ1 α bs Hsome)); auto.
     rewrite {3}/pmf/=/dbind_pmf.
     apply SeriesC_correct; auto.
     apply (ex_seriesC_le _ (state_step σ1 α)); auto.
     intro; split; auto.
     + apply Rmult_le_pos; auto.
     + rewrite <- Rmult_1_r.
       apply Rmult_le_compat_l; auto.
   - rewrite lim_exec_val_rw.
     rewrite rbar_finite_real_eq; [ apply Sup_seq_correct | ].
     rewrite mon_sup_succ.
     + apply (Rbar_le_sandwich 0 1); auto.
       * apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
       * apply upper_bound_ge_sup; intro; simpl; auto.
     + intro; apply exec_val_mon.
Qed.

Lemma limprim_coupl_step_limprim e1 σ1 α bs :
  σ1.(tapes) !! α = Some bs →
  Rcoupl
    (lim_exec_val (e1, σ1))
    (state_step σ1 α ≫= (λ σ2, lim_exec_val (e1, σ2)))
    eq.
Proof.
  intro Hsome.
  erewrite (distr_ext (lim_exec_val (e1, σ1))); last first.
  - intro a.
    apply (limprim_coupl_step_limprim_aux _ _ _ _ _ Hsome).
  - apply Rcoupl_eq.
Qed.

Lemma refRcoupl_erasure e1 σ1 e1' σ1' α α' R Φ m bs bs':
  σ1.(tapes) !! α = Some bs →
  σ1'.(tapes) !! α' = Some bs' →
  Rcoupl (state_step σ1 α) (state_step σ1' α') R →
  (∀ σ2 σ2', R σ2 σ2' →
             refRcoupl (exec_val m (e1, σ2))
               (lim_exec_val (e1', σ2')) Φ ) →
  refRcoupl (exec_val m (e1, σ1))
    (lim_exec_val (e1', σ1')) Φ.
Proof.
  intros Hα Hα' HR Hcont.
  eapply refRcoupl_eq_refRcoupl_unfoldl ;
    [eapply prim_coupl_step_prim; eauto |].
  eapply refRcoupl_eq_refRcoupl_unfoldr;
    [| eapply Rcoupl_eq_sym, limprim_coupl_step_limprim; eauto].
  apply (refRcoupl_dbind _ _ _ _ R); auto.
  by eapply Rcoupl_refRcoupl.
Qed.

Lemma refRcoupl_erasure_r (e1 : expr) σ1 e1' σ1' α' R Φ m bs':
  to_val e1 = None →
  σ1'.(tapes) !! α' = Some bs' →
  Rcoupl (prim_step e1 σ1) (state_step σ1' α') R →
  (∀ e2 σ2 σ2', R (e2, σ2) σ2' → refRcoupl (exec_val m (e2, σ2)) (lim_exec_val (e1', σ2')) Φ ) →
  refRcoupl (exec_val (S m) (e1, σ1)) (lim_exec_val (e1', σ1')) Φ.
Proof.
  intros He1 Hα' HR Hcont.
  rewrite exec_val_Sn_not_val //.
  eapply (refRcoupl_eq_refRcoupl_unfoldr _ (state_step σ1' α' ≫= (λ σ2', lim_exec_val (e1', σ2')))).
  - eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl].
    intros [] ??. by apply Hcont.
  - apply Rcoupl_eq_sym. by eapply limprim_coupl_step_limprim.
Qed.

Lemma refRcoupl_erasure_l (e1 e1' : expr) σ1 σ1' α R Φ m bs :
  σ1.(tapes) !! α = Some bs →
  Rcoupl (state_step σ1 α) (prim_step e1' σ1') R →
  (∀ σ2 e2' σ2', R σ2 (e2', σ2') → refRcoupl (exec_val m (e1, σ2)) (lim_exec_val (e2', σ2')) Φ ) →
  refRcoupl (exec_val m (e1, σ1)) (lim_exec_val (e1', σ1')) Φ.
Proof.
  intros Hα HR Hcont.
  assert (to_val e1' = None).
  { apply Rcoupl_pos_R, Rcoupl_inhabited_l in HR as (?&?&?&?&?); [eauto using val_stuck|].
    rewrite state_step_mass; [lra|]. apply elem_of_dom. eauto. }
  eapply (refRcoupl_eq_refRcoupl_unfoldl _ (state_step σ1 α ≫= (λ σ2, exec_val m (e1, σ2)))).
  - by eapply prim_coupl_step_prim.
  - rewrite lim_exec_val_prim_step.
    rewrite prim_step_or_val_no_val //.
    eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl].
    intros ? [] ?. by apply Hcont.
Qed.
