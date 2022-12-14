From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import big_op.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.prelude Require Import options.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export ghost_map.

From self.prelude Require Import stdpp_ext.
From self.program_logic Require Import exec weakestpre.
From self.prob_lang Require Import
  primitive_laws class_instances spec_ra tactics notation lang metatheory.
From self.prob Require Export couplings distribution.
Import uPred.

Local Open Scope R.


Section helper_lemma.
  Context `{!irisGS prob_lang Σ}.

  Definition pure_eq (ρ1 ρ2 : cfg) := (ρ1.1 = ρ2.1) ∧ (ρ1.2.(heap) = ρ2.2.(heap)).

  (* Lemma foo_helper_1 (m : nat) (e1 : expr) (σ1 : state) (e1' : expr) (σ1' : state) (R: cfg → cfg → Prop): *)
  (*   Rcoupl (prim_step e1 σ1) (prim_step e1' σ1') R → *)
  (*   (forall ρ2 ρ2', R ρ2 ρ2' → ∃ n : nat, refRcoupl (prim_exec ρ2 m) (prim_exec ρ2' n) pure_eq) *)
  (*   → ∃ n : nat, refRcoupl (prim_exec (e1, σ1) (S m)) (prim_exec (e1', σ1') n) pure_eq. *)
  (* Proof. *)
  (*   intros (μ & ((HμL & HμR) & HμSupp)) Hcont. *)
  (*   assert (exists n, ∀ ρ2 ρ2' : cfg, μ (ρ2, ρ2') > 0 → refRcoupl (prim_exec ρ2 m) (prim_exec ρ2' n) pure_eq) as (n & Hn). *)
  (*   (* Somehow use finiteness of the support? *) *)
  (*   { admit. } *)
  (*   exists (S n). *)
  (*   rewrite /prim_exec /=. *)
  (*   case_match; case_match. *)
  (*   + specialize (Hn (e1, σ1) (e1', σ1')). *)
  (*     assert (μ (e1, σ1, (e1', σ1')) > 0) as Haux; [admit | ]. *)
  (*     specialize (Hn Haux). *)
  (*     destruct m; destruct n; *)
  (*     rewrite /prim_exec in Hn. *)
  (* Admitted. *)

  Lemma bar (ρ : cfg) :
    dbind (λ ρ', lim_prim_exec ρ') (prim_step_or_val ρ) = (lim_prim_exec ρ).
  Proof. Admitted.

  (* Definition ref_eq_coupl (ρ1 ρ2 : cfg) := *)
  (*   ∀ n, refRcoupl (prim_exec ρ1 n) (lim_prim_exec ρ2) pure_eq. *)

  Lemma qux (μ1 μ2 : distr cfg) :
    Rcoupl μ1 μ2 pure_eq ↔ (dmap (λ '(e, σ), (e, σ.(heap))) μ1) = (dmap (λ '(e, σ), (e, σ.(heap))) μ2).
  Proof. Admitted.

  Lemma quux (μ1 μ2 : distr cfg) :
    refRcoupl μ1 μ2 pure_eq ↔ refRcoupl (dmap (λ '(e, σ), (e, σ.(heap))) μ1) (dmap (λ '(e, σ), (e, σ.(heap))) μ2) eq.
  Proof. Admitted.

  Lemma quuux e1 σ1 α m :
    dmap (λ '(e, σ), (e, heap σ)) (dbind (λ σ2, prim_exec m (e1, σ2)) (state_step σ1 α)) = dmap (λ '(e, σ), (e, heap σ)) (prim_exec m (e1, σ1)).
  Proof. Admitted.

  Lemma qux_something e1 σ1 α :
    Rcoupl (dret (e1, σ1)) (dbind (λ σ2 : state, dret (e1, σ2)) (state_step σ1 α)) pure_eq.
  Proof.
    assert (dret (e1 , σ1) = dbind (λ σ, dret (e1, σ)) (dret σ1)) as Hfck.
    { rewrite dret_id_left//. }
    rewrite Hfck.
    eapply (Rcoupl_bind _ _ _ _ (λ σ σ', σ.(heap) = σ'.(heap))).
    { intros ???. apply Rcoupl_ret. done. }
    clear Hfck.
    exists (dprod (dret σ1) (state_step σ1 α)). split.
    * admit.
      (* split. *)
      (* { rewrite lmarg_dprod //. } *)
      (* { rewrite rmarg_dprod //. } *)
    * intros [] [->%dret_pos ?]%dprod_pos. simpl.
      apply state_step_support_equiv_rel in H.
      by inversion H.
  Admitted.


  Lemma pure_eq_coupl_sym μ1 μ2 :
    Rcoupl μ1 μ2 pure_eq → Rcoupl μ2 μ1 pure_eq.
  Proof.
    intros H.
    apply qux.
    apply qux in H.
    auto.
  Qed.

  Lemma pure_eq_coupl_trans μ1 μ2 μ3 :
    Rcoupl μ1 μ2 pure_eq → Rcoupl μ2 μ3 pure_eq → Rcoupl μ1 μ3 pure_eq.
  Proof.
    intros H12 H23.
    apply qux.
    apply qux in H12.
    apply qux in H23.
    rewrite H12; auto.
  Qed.

  Lemma pure_eq_ref_coupl_trans μ1 μ2 μ3 :
    refRcoupl μ1 μ2 pure_eq → refRcoupl μ2 μ3 pure_eq → refRcoupl μ1 μ3 pure_eq.
  Proof.
    intros H12 H23.
    apply quux.
    apply quux in H12.
    apply quux in H23.
    pose proof (refcoupl_elim _ _ H12) as H12'.
    pose proof (refcoupl_elim _ _ H23) as H23'.
    apply refcoupl_from_ineq.
    intro a.
    eapply Rle_trans; eauto.
  Qed.


  Lemma pure_eq_ref_coupl_unfoldl μ1 μ2 μ3 :
    Rcoupl μ1 μ2 pure_eq → refRcoupl μ2 μ3 pure_eq → refRcoupl μ1 μ3 pure_eq.
  Proof.
    intros H12 H23.
    apply quux.
    apply qux in H12.
    apply quux in H23.
    rewrite H12; auto.
  Qed.

  Lemma pure_eq_ref_coupl_unfoldr μ1 μ2 μ3 :
    refRcoupl μ1 μ2 pure_eq → Rcoupl μ2 μ3 pure_eq → refRcoupl μ1 μ3 pure_eq.
  Proof.
    intros H12 H23.
    apply quux.
    apply quux in H12.
    apply qux in H23.
    rewrite <- H23; auto.
  Qed.


  (* Lemma baar e1 σ1 α b: *)
  (*   det_head_step_pred e1 σ1 → *)
  (*   det_head_step_pred e1 (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [b]]> σ1). *)
  (* Proof. *)
  (*   intro Hdet. *)
  (*   inversion Hdet; econstructor; eauto. *)
  (* Qed. *)


  Lemma baaar e1 σ1 e2 σ2 α b:
    det_head_step_rel e1 σ1 e2 σ2 →
    det_head_step_rel
      e1 (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [b]]> σ1)
      e2 (state_upd_tapes <[α := σ2.(tapes) !!! α ++ [b]]> σ2).
  Proof. inversion 1; econstructor; eauto. Qed.

  Lemma head_step_alloc_unfold σ:
    head_step alloc σ = dret (let l := fresh_loc (tapes σ) in (Val #lbl:l, state_upd_tapes <[fresh_loc (tapes σ):=[]]> σ) ) .
  Proof.
    apply distr_ext.
    intros (e2 & σ2).
    rewrite /pmf/head_step/head_step_pmf/=/dret_pmf.
    case_bool_decide as H; simplify_eq; auto.
    + case_bool_decide; simplify_eq; auto.
      destruct H; auto.
    + do 3 (case_match; auto).
      case_bool_decide; simplify_eq; auto.
      destruct H.
      destruct_and?.
      f_equal; auto.
      rewrite H; auto.
  Qed.

  Lemma head_step_flip_nonempty_unfold σ l b bs :
    σ.(tapes) !! l = Some (b :: bs) →
    head_step (flip #lbl:l) σ = dret (Val (LitV (LitBool b)), state_upd_tapes <[l:=bs]> σ).
  Proof.
    intro Hσ.
    apply distr_ext.
    intro ρ.
    rewrite /pmf/head_step/head_step_pmf/=/dret_pmf.
    do 4 (case_match; auto); simplify_eq.
    rewrite Hσ/=.
    case_bool_decide as H.
    + case_bool_decide as H2; auto.
      destruct H2; destruct_and?; simplify_eq.
      f_equal; auto.
    + case_bool_decide; auto.
      destruct H;
      simplify_eq; auto.
  Qed.


  Lemma head_step_flip_empty_unfold σ l  :
    σ.(tapes) !! l = Some ([]) →
    head_step (flip #lbl:l) σ = fair_conv_comb (dret (Val(#true), σ)) (dret (Val(#false), σ)).
  Proof.
    intro Hσ.
    apply distr_ext.
    intro ρ.
    rewrite /pmf/head_step/head_step_pmf/=/dbind_pmf/dret_pmf/=.
  Admitted.

  Lemma head_step_flip_unalloc_unfold σ l  :
    σ.(tapes) !! l = None →
    head_step (flip #lbl:l) σ = fair_conv_comb (dret (Val(#true), σ)) (dret (Val(#false), σ)).
  Proof.
  Admitted.

  Lemma upd_tape_some σ α b bs:
    tapes σ !! α = Some bs →
      tapes (state_upd_tapes <[α:=tapes σ !!! α ++ [b]]> σ) !! α =  Some (bs++[b]).
  Proof.
    Admitted.


  Lemma upd_tape_some_trivial σ α bs:
    tapes σ !! α = Some bs →
      state_upd_tapes <[α:=tapes σ !!! α]> σ = σ.
  Proof.
    Admitted.


  Lemma upd_tape_none σ α b :
    tapes σ !! α = None →
      tapes (state_upd_tapes <[α:=tapes σ !!! α ++ [b]]> σ) !! α =  Some ([b]).
  Proof.
    Admitted.

  Lemma upd_diff_tape σ α β b:
    α ≠ β →
    tapes σ !! α = tapes (state_upd_tapes <[β:=tapes σ !!! β ++ b]> σ) !! α.
  Proof.
    Admitted.

  Lemma upd_diff_tape_comm σ α β bs bs':
    α ≠ β →
    state_upd_tapes <[β:= bs]> (state_upd_tapes <[α := bs']> σ) =
    state_upd_tapes <[α:= bs']> (state_upd_tapes <[β := bs]> σ).
  Proof.
    Admitted.

  Lemma upd_diff_tape_tot σ α β bs:
    α ≠ β →
    tapes σ !!! α = tapes (state_upd_tapes <[β:=bs]> σ) !!! α.
  Proof. symmetry ; by rewrite lookup_total_insert_ne. Qed.

  Lemma upd_tape_twice σ β bs bs' :
    state_upd_tapes <[β:= bs]> (state_upd_tapes <[β:= bs']> σ) =
      state_upd_tapes <[β:= bs]> σ.
  Proof.
    Admitted.

  Lemma upd_tape_app σ α bs bs':
    state_upd_tapes <[α:=bs ++ bs']> σ =
    state_upd_tapes <[α:=tapes (state_upd_tapes <[α:=bs]> σ) !!! α ++ bs']>
                    (state_upd_tapes <[α:=bs]> σ).
  Proof.
    Admitted.


  Lemma fresh_loc_upd_some σ α bs bs' :
    (tapes σ) !! α = Some bs →
    fresh_loc (tapes σ) = (fresh_loc (<[α:= bs']> (tapes σ))).
  Proof.
    intros Hα.
    apply fresh_loc_eq_dom.
    by rewrite dom_insert_lookup_L.
  Qed.

  Local Lemma elem_fresh_ne {V} (ls : gmap loc V) k v :
    ls !! k = Some v → fresh_loc ls ≠ k.
  Proof.
    intros; assert (is_Some (ls !! k)) as Hk by auto.
    pose proof (fresh_loc_is_fresh ls).
    rewrite -elem_of_dom in Hk.
    set_solver.
  Qed.

  Lemma fresh_loc_upd_swap σ α bs bs' bs'' :
    (tapes σ) !! α = Some bs →
    state_upd_tapes <[fresh_loc (tapes σ):=bs']> (state_upd_tapes <[α:=bs'']> σ)
    = state_upd_tapes <[α:=bs'']> (state_upd_tapes <[fresh_loc (tapes σ):=bs']> σ).
  Proof.
    intros H.
    apply elem_fresh_ne in H.
    unfold state_upd_tapes.
    by rewrite insert_commute.
  Qed.

  Lemma fresh_loc_lookup σ α bs bs' :
    (tapes σ) !! α = Some bs →
    (tapes (state_upd_tapes <[fresh_loc (tapes σ):=bs']> σ)) !! α = Some bs.
  Proof.
    intros H.
    pose proof (elem_fresh_ne _ _ _ H).
    by rewrite lookup_insert_ne.
  Qed.

  Lemma exec_coupl_eq e σ m :
    Rcoupl (prim_exec m (e, σ)) (prim_exec m (e, σ)) pure_eq.
  Proof.
    move : e σ.
    induction m; intros e σ.
    - rewrite /prim_exec.
      case_match.
      + exists (dret ((e, σ),(e, σ))).
         split ; [split; [ rewrite /lmarg dmap_dret; auto | rewrite /rmarg dmap_dret; auto ]  |  ].
         intros (ρ2 & ρ2') H2; simpl; auto.
         apply dret_pos in H2.
         simplify_eq.
         rewrite /pure_eq; auto.
      + exists dzero.
         split; [split; [ rewrite /lmarg dmap_dzero; auto | rewrite /rmarg dmap_dzero; auto ] | ].
         intros (ρ2 & ρ2') H2; simpl; auto.
         rewrite /pmf/dzero in H2; lra.
    - rewrite prim_exec_unfold /=.
      case_match.
      + exists (dret ((e, σ),(e, σ))).
         split ; [split; [ rewrite /lmarg dmap_dret; auto | rewrite /rmarg dmap_dret; auto ]  |  ].
         intros (ρ2 & ρ2') H2; simpl; auto.
         apply dret_pos in H2.
         simplify_eq.
         rewrite /pure_eq; auto.
      + apply (Rcoupl_bind _ _ _ _ (=)); [ | apply Rcoupl_eq].
         intros ? (e2 & σ2) ->.
         apply (IHm e2 σ2).
  Qed.

  (* Lemma exec_coupl_eq_irrel e σ l m : *)
  (*   tapes σ !! l = None → *)
  (*   Rcoupl (prim_exec m (e, σ)) (prim_exec m (e, (state_upd_tapes <[l:=[]]> σ))) pure_eq. *)
  (* Proof. Admitted. *)

  Lemma pos_sum_nn_real p q :
    0 <= p →
    0 <= q →
    0 < p + q →
    0 < p ∨ 0 < q.
  Proof.
    intros Hp Hq Hsum.
    destruct Hp as [ Hp | Hp ]; simplify_eq; auto.
    destruct Hq as [ Hq | Hq ]; simplify_eq; auto.
    lra.
  Qed.

  Lemma pos_prod_nn_real p q :
    0 <= p →
    0 <= q →
    0 < p * q →
    0 < p ∧ 0 < q.
  Proof.
    intros Hp Hq Hsum.
    destruct Hp as [ Hp | Hp ]; simplify_eq; split; auto; try lra.
    destruct Hq as [ Hq | Hq ]; simplify_eq ; auto; lra.
  Qed.

End helper_lemma.

(* Lemma det_head_step_rel_head_reducible e1 σ1 e2 σ2 : *)
(*   det_head_step_rel e1 σ1 e2 σ2 → head_reducible e1 σ1. *)
(* Proof. *)
(*   intros ?%det_head_step_singleton. *)
(*   exists (e2, σ2). simpl. rewrite H dret_1_1 //. lra. *)
(* Qed. *)

Section erasure_helpers.

  Variable (m : nat).
  Hypothesis IH :
    ∀ (e1 : expr) (σ1 : state) α bs,
    tapes σ1 !! α = Some bs →
    Rcoupl (prim_exec m (e1, σ1))
      (fair_conv_comb
         (prim_exec m (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [true]]> σ1))
         (prim_exec m (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [false]]> σ1))) pure_eq.

  Local Lemma ind_case_det e σ α bs K :
    tapes σ !! α = Some bs →
    is_det_head_step e σ = true →
    Rcoupl
      (dmap (fill_lift K) (head_step e σ) ≫= prim_exec m)
      (fair_conv_comb
         (dmap (fill_lift K) (head_step e (state_upd_tapes <[α:=tapes σ !!! α ++ [true]]> σ)) ≫= prim_exec m)
         (dmap (fill_lift K) (head_step e (state_upd_tapes <[α:=tapes σ !!! α ++ [false]]> σ)) ≫= prim_exec m))
      pure_eq.
  Proof using m IH.
    intros Hα (e2 & (σ2 & Hdet))%is_det_head_step_true%det_step_pred_ex_rel.
    pose proof (baaar e σ e2 σ2 α true Hdet) as HdetT.
    pose proof (baaar e σ e2 σ2 α false Hdet) as HdetF.
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
      (dmap (fill_lift K) (head_step e σ) ≫= prim_exec m)
      (fair_conv_comb
         (dmap (fill_lift K) (head_step e (state_upd_tapes <[α:=tapes σ !!! α ++ [true]]> σ)) ≫= prim_exec m)
         (dmap (fill_lift K) (head_step e (state_upd_tapes <[α:=tapes σ !!! α ++ [false]]> σ)) ≫= prim_exec m)) pure_eq.
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
      (dmap (fill_lift K) (head_step AllocTape σ) ≫= prim_exec m)
      (fair_conv_comb
         (dmap (fill_lift K) (head_step AllocTape (state_upd_tapes <[α:=tapes σ !!! α ++ [true]]> σ)) ≫= prim_exec m)
         (dmap (fill_lift K) (head_step AllocTape (state_upd_tapes <[α:=tapes σ !!! α ++ [false]]> σ)) ≫= prim_exec m))
      pure_eq.
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
      (dmap (fill_lift K) (head_step (flip #lbl:α') σ) ≫= prim_exec m)
      (fair_conv_comb
         (dmap (fill_lift K) (head_step (flip #lbl:α') (state_upd_tapes <[α:=tapes σ !!! α ++ [true]]> σ)) ≫= prim_exec m)
         (dmap (fill_lift K) (head_step (flip #lbl:α') (state_upd_tapes <[α:=tapes σ !!! α ++ [false]]> σ)) ≫= prim_exec m))
      pure_eq.
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
      (dmap (fill_lift K) (head_step (flip #lbl:α') σ) ≫= prim_exec m)
      (fair_conv_comb
         (dmap (fill_lift K) (head_step (flip #lbl:α') (state_upd_tapes <[α:=tapes σ !!! α ++ [true]]> σ)) ≫= prim_exec m)
         (dmap (fill_lift K) (head_step (flip #lbl:α') (state_upd_tapes <[α:=tapes σ !!! α ++ [false]]> σ)) ≫= prim_exec m))
      pure_eq.
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
        eapply (Rcoupl_bind _ _ _ _ (=)); [ | apply Rcoupl_eq].
        intros ? b ->.
        do 2 rewrite upd_tape_twice.
        rewrite -(lookup_total_correct _ _ _ Hα').
        rewrite (upd_tape_some_trivial _ _ []) //.
        destruct b; simpl; do 2 rewrite dret_id_left; apply exec_coupl_eq.
      + rewrite head_step_flip_empty_unfold //.
        rewrite head_step_flip_empty_unfold //; last first.
        { rewrite -upd_diff_tape //. }
        rewrite head_step_flip_empty_unfold; last first.
        { rewrite -upd_diff_tape //. }
        rewrite {3 4}/fair_conv_comb.
        rewrite -!dbind_assoc.
        rewrite -(dbind_fair_conv_comb _ _ fair_coin).
        rewrite /fair_conv_comb.
        eapply Rcoupl_bind; [|apply Rcoupl_eq].
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
      eapply Rcoupl_bind; [|apply Rcoupl_eq].
      intros ? [] ->; rewrite !dret_id_left; by eapply IH.
  Qed.
End erasure_helpers.

Section erasure.

  Lemma prim_coupl_upd_tapes_dom m e1 σ1 α bs :
    σ1.(tapes) !! α = Some bs →
    Rcoupl
      (prim_exec m (e1, σ1))
      (fair_conv_comb
         (prim_exec m (e1, (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [true]]> σ1)))
         (prim_exec m (e1, (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [false]]> σ1))))
      pure_eq.
  Proof.
    revert e1 σ1 α bs; induction m; intros e1 σ1 α bs Hα.
    - rewrite /prim_exec/=.
      destruct (to_val e1).
      + exists (dprod
                  (dret (e1, σ1))
                  (fair_conv_comb
                     (dret (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [true]]> σ1))
                     (dret (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [false]]> σ1)))).
        split; [split ; [rewrite lmarg_dprod //|rewrite rmarg_dprod //] |].
        { erewrite SeriesC_ext; [ | intro; rewrite fair_conv_comb_pmf; done].
          rewrite SeriesC_plus;
            [do 2 rewrite SeriesC_scal_l; do 2 rewrite dret_mass; lra | | ];
            apply ex_seriesC_scal_l; apply pmf_ex_seriesC. }
        { apply dret_mass. }
        intros ((e2 & σ2) & (e2' & σ2')) Hpos. simpl.
        rewrite /pmf/= in Hpos.
        rewrite fair_conv_comb_pmf in Hpos.
        assert ((dret (e1, σ1) (e2, σ2) > 0 ∧
                   dret (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [true]]> σ1) (e2', σ2') > 0) ∨
                (dret (e1, σ1) (e2, σ2) > 0 ∧
                   dret (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [false]]> σ1) (e2', σ2') > 0))
          as [(Hpos1 & Hpos2) | (Hpos3 & Hpos4)].
        { (* This is a fact about the reals, maybe it can be done easier *)
          apply Rgt_lt in Hpos.
          rewrite -Rmult_plus_distr_l
                  -Rmult_assoc
                  -{1}Rmult_comm
           -Rmult_assoc
            Rmult_plus_distr_r in Hpos.
          apply pos_prod_nn_real in Hpos; try lra.
          destruct Hpos as [Hpos ?].
          apply pos_sum_nn_real in Hpos;
            [| by apply Rmult_le_pos
            | by apply Rmult_le_pos].
          destruct Hpos; [left | right];
            apply pos_prod_nn_real; auto; rewrite Rmult_comm; auto. }
        { apply dret_pos in Hpos1, Hpos2. by simplify_eq. }
        { apply dret_pos in Hpos3, Hpos4. by simplify_eq. }
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
          - by eapply ind_case_flip_none. }
        { by eapply ind_case_dzero. }
  Qed.

  Lemma prim_coupl_step_prim m e1 σ1 α bs :
    σ1.(tapes) !! α = Some bs →
    Rcoupl
      (prim_exec m (e1, σ1))
      (state_step σ1 α ≫= (λ σ2, prim_exec m (e1, σ2)))
      pure_eq.
  Proof.
    intros Hα.
    rewrite state_step_fair_conv_comb; last first.
    { apply elem_of_dom. eauto. }
    rewrite fair_conv_comb_dbind.
    do 2 rewrite dret_id_left.
    by eapply prim_coupl_upd_tapes_dom.
  Qed.

  Lemma limprim_coupl_step_limprim : forall e1 σ1 α bs,
    σ1.(tapes) !! α = Some bs →
    Rcoupl
      (lim_prim_exec (e1, σ1))
      (state_step σ1 α ≫= (λ σ2, lim_prim_exec (e1, σ2)))
      pure_eq.
  Proof.
    (* Hopefully there is some continuity argument using the previous lemma *)
    (* intros; rewrite state_step_fair_conv_comb fair_conv_comb_dbind. *)
    (* do 2 rewrite dret_id_left. *)
  Admitted.

End erasure.


Lemma quuuux e1 σ1 α m bs :
  σ1.(tapes) !! α = Some bs →
  dmap (λ '(e, σ), (e, heap σ)) (prim_exec m (e1, σ1)) =
    dmap (λ '(e, σ), (e, heap σ)) (state_step σ1 α ≫= (λ σ2, prim_exec m (e1, σ2))).
Proof.
  intros.
  apply qux.
  assert
    ((state_step σ1 α ≫= (λ σ2 : language.state prob_lang, prim_exec m (e1, σ2)))=
       (fair_conv_comb (prim_exec m (e1, (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [true]]> σ1)) )
          (prim_exec m (e1, (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [false]]> σ1)) ))
    ) as ->; [ | eapply prim_coupl_upd_tapes_dom; eauto].
  rewrite state_step_fair_conv_comb; last first.
  { apply elem_of_dom; eauto. }
  rewrite fair_conv_comb_dbind.
  do 2 rewrite dret_id_left; auto.
Qed.

  Lemma Rcoupl_erasure e1 σ1 e1' σ1' α α' R m bs bs':
    σ1.(tapes) !! α = Some bs →
    σ1'.(tapes) !! α' = Some bs' →
    Rcoupl (state_step σ1 α) (state_step σ1' α') R →
    (∀ σ2 σ2', R σ2 σ2' → Rcoupl (prim_exec m (e1, σ2)) (prim_exec m (e1', σ2')) pure_eq) →
    Rcoupl (prim_exec m (e1, σ1)) (prim_exec m (e1', σ1')) pure_eq.
  Proof.
    intros Hα Hα' HR Hcont.
    eapply pure_eq_coupl_trans ; [eapply prim_coupl_step_prim ; eauto | ].
    apply pure_eq_coupl_sym.
    eapply pure_eq_coupl_trans ; [eapply prim_coupl_step_prim ; eauto | ].
    apply pure_eq_coupl_sym.
    apply (Rcoupl_bind _ _ _ _ R); auto.
  Qed.

  Lemma refRcoupl_erasure e1 σ1 e1' σ1' α α' R m bs bs':
    σ1.(tapes) !! α = Some bs →
    σ1'.(tapes) !! α' = Some bs' →
    Rcoupl (state_step σ1 α) (state_step σ1' α') R →
    (∀ σ2 σ2', R σ2 σ2' → refRcoupl (prim_exec m (e1, σ2)) (lim_prim_exec (e1', σ2')) pure_eq) →
    refRcoupl (prim_exec m (e1, σ1)) (lim_prim_exec (e1', σ1')) pure_eq.
  Proof.
    intros Hα Hα' HR Hcont.
    eapply pure_eq_ref_coupl_unfoldl ; [eapply prim_coupl_step_prim ; eauto | ].
    eapply pure_eq_ref_coupl_unfoldr; [ | eapply pure_eq_coupl_sym, limprim_coupl_step_limprim ; eauto ].
    apply (refRcoupl_bind _ _ _ _ R); auto.
    apply weaken_coupl; auto.
  Qed.

  Lemma lim_prim_exec_exec n (ρ : cfg) :
    lim_prim_exec ρ = exec n ρ ≫= lim_prim_exec.
  Proof. Admitted.

  Lemma lim_prim_exec_exec_val n ρ (v : val) σ :
    exec n ρ (Val v, σ) = 1 →
    lim_prim_exec ρ = dret (Val v, σ).
  Proof. Admitted.


(* TODO: upstream? *)
  Section fupd_plainly_derived.
    Context {PROP : bi}.
    Context `{!BiFUpd PROP, !BiPlainly PROP, !BiFUpdPlainly PROP}.

    Lemma step_fupd_except_0 E1 E2 (P : PROP) : (|={E1}[E2]▷=> ◇ P) ={E1}[E2]▷=∗ P.
    Proof.
      iIntros "H".
      iMod "H".
      do 2 iModIntro.
      rewrite fupd_except_0 //.
    Qed.

    Lemma step_fupdN_except_0 E1 E2 (P : PROP) n : (|={E1}[E2]▷=>^(S n) ◇ P) ={E1}[E2]▷=∗^(S n) P.
    Proof.
      iInduction n as [|n IH] "IH".
      - iIntros "H /=". by iApply step_fupd_except_0.
      - iIntros "H /=".
        iMod "H". do 2 iModIntro.
        iMod "H". iModIntro.
        iMod ("IH" with "H") as "H".
        do 2 iModIntro. done.
    Qed.

    Lemma step_fupdN_plain_forall E {A} (Φ : A → PROP) `{!∀ x, Plain (Φ x)} n :
      (|={E}▷=>^n ∀ x, Φ x) ⊣⊢ (∀ x, |={E}▷=>^n Φ x).
    Proof using BiFUpd0 BiFUpdPlainly0 BiPlainly0 PROP.
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

End  fupd_plainly_derived.

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

  Lemma refRcoupl_bind' `{Countable A, Countable B} μ1 μ2 f g (R T : A → B → Prop) n  :
    ⌜refRcoupl μ1 μ2 R⌝ -∗
    (∀ a b, ⌜R a b⌝ ={∅}▷=∗^(S n) ⌜refRcoupl (f a) (g b) T⌝) -∗
    |={∅}▷=>^(S n) ⌜refRcoupl (dbind f μ1) (dbind g μ2) T⌝ : iProp Σ.
  Proof.
    iIntros (HR) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a b, R a b → refRcoupl (f a) (g b) T)⌝)).
    { iIntros (?). iPureIntro. by eapply refRcoupl_bind. }
    iIntros (???) "/=".
    iMod ("H" with "[//]"); auto.
  Qed.

  Definition coupl_rel (φ : val → val → Prop) (ρ ρ' : cfg) : Prop :=
    match to_val ρ.1, to_val ρ'.1 with
    | Some v, Some v' => φ v v'
    | Some _, None => False
    | None,  _ => True
    end.

  Lemma exec_coupl_erasure (e1 : expr) (σ1 : state) (e1' : expr) (σ1' : state) (n : nat) φ :
    to_val e1 = None →
    exec_coupl e1 σ1 e1' σ1' (λ '(e2, σ2) '(e2', σ2'),
        |={∅}▷=>^(S n) ⌜refRcoupl (prim_exec n (e2, σ2)) (lim_prim_exec (e2', σ2')) (coupl_rel φ)⌝)
    ⊢ |={∅}▷=>^(S n) ⌜refRcoupl (prim_exec (S n) (e1, σ1)) (lim_prim_exec (e1', σ1')) (coupl_rel φ)⌝.
  Proof.
    iIntros (Hv) "Hexec".
    iAssert (⌜to_val e1 = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /exec_coupl /exec_coupl'.
    iPoseProof (least_fixpoint_iter
                  (exec_coupl_pre (λ '(e2, σ2) '(e2', σ2'),
                       |={∅}▷=>^(S n) ⌜refRcoupl (prim_exec n (e2, σ2)) (lim_prim_exec (e2', σ2')) (coupl_rel φ)⌝)%I)
                  (λ '((e1, σ1), (e1', σ1')), ⌜to_val e1 = None⌝ ={∅}▷=∗^(S n)
                      ⌜refRcoupl (prim_exec (S n) (e1, σ1)) (lim_prim_exec (e1', σ1')) (coupl_rel φ)⌝)%I
                 with "[]") as "H"; last first.
    { iIntros "Hfix %". by iMod ("H" $! ((_, _), (_, _)) with "Hfix [//]"). }
    clear.
    iIntros "!#" ([[e1 σ1] [e1' σ1']]). rewrite /exec_coupl_pre.
    iIntros "[(%R & % & %Hcpl & H) | [(%R & % & %Hcpl & H) | [(%R & %m & %Hcpl & H) | H]]] %Hv".
    - rewrite prim_exec_Sn_not_val; [|done].
      rewrite -bar.
      destruct (to_val e1') eqn:Hv'.
      + destruct (decide (prim_step e1 σ1 = dzero)) as [Hs|].
        * rewrite /= Hs dbind_dzero.
          do 3 iModIntro. iApply step_fupdN_intro; [done|].
          iModIntro. iPureIntro. apply refRcoupl_dzero.
        * assert (prim_step e1' σ1' = dzero) as Hz by by apply val_stuck_dzero.
          rewrite /= (val_stuck_dzero e1') in Hcpl; [|eauto].
          by apply Rcoupl_dzero_r_inv in Hcpl.
      + rewrite prim_step_or_val_no_val; [|done].
        iApply (refRcoupl_bind' _ _ _ _ R).
        { iPureIntro. by apply weaken_coupl. }
        iIntros ([] [] HR). by iMod ("H" with "[//]").
    - rewrite prim_exec_Sn_not_val; [|done].
      rewrite -(dret_id_left (lim_prim_exec)).
      iApply refRcoupl_bind'.
      { iPureIntro. apply Rcoupl_pos_R in Hcpl. by apply weaken_coupl. }
      iIntros ([] [] (?&?& [= -> ->]%dret_pos)).
      by iMod ("H"  with "[//]").
    - rewrite -{2}(dret_id_left (prim_exec _)).
      rewrite (lim_prim_exec_exec m).
      iApply refRcoupl_bind'.
      { iPureIntro. apply Rcoupl_pos_R in Hcpl. by apply weaken_coupl. }
      iIntros ([] [] (?& [= -> ->]%dret_pos &?)).
      by iMod ("H"  with "[//] [//]").
    - rewrite prim_exec_Sn_not_val; [|done].
      iDestruct (big_orL_mono _ (λ _ _,
                     |={∅}▷=>^(S n)
                       ⌜refRcoupl (prim_step e1 σ1 ≫= prim_exec n)
                                  (lim_prim_exec (e1', σ1')) (coupl_rel φ)⌝)%I
                  with "H") as "H".
      { iIntros (i [α1 α2] [Hα1 Hα2]%elem_of_list_lookup_2%elem_of_list_prod_1) "(% & %Hcpl & H)".
        rewrite -prim_exec_Sn_not_val; [|done].
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ σ2 σ2', R2 σ2 σ2' → refRcoupl (prim_exec (S n) (e1, σ2))
                                                    (lim_prim_exec (e1', σ2')) (coupl_rel φ)⌝)%I).
        - iIntros (?). iPureIntro.
          rewrite /= /get_active in Hα1, Hα2.
          apply elem_of_elements, elem_of_dom in Hα1 as [], Hα2 as [].
          (* TODO: generalize erasure theorem *)
          (* eapply baz; [done|done|done|].    *)
          admit.
        - iIntros (???). by iMod ("H" with "[//] [//]"). }
      iInduction (list_prod (language.get_active σ1) (language.get_active σ1'))
        as [| [α α']] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[H | Ht]"; [done|].
      by iApply "IH".
  Admitted.

  Theorem wp_coupling (e e' : expr) (σ σ' : state) n φ :
    state_interp σ ∗ spec_interp (e', σ') ∗ spec_ctx ∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜refRcoupl (prim_exec n (e, σ)) (lim_prim_exec (e', σ')) (coupl_rel φ)⌝.
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
        iPureIntro. by apply refRcoupl_ret.
      + iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iPureIntro. apply refRcoupl_dzero.
    - rewrite prim_exec_Sn /prim_step_or_val /=.
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
        rewrite prim_exec_unfold dret_id_left /=.
        erewrite lim_prim_exec_exec_val; [|done].
        by apply refRcoupl_ret.
      + rewrite wp_unfold /wp_pre /= Heq.
        iMod ("Hwp" with "[$]") as "Hcpl".
        iModIntro.
        iPoseProof
          (exec_coupl_mono _ (λ '(e2, σ2) '(e2', σ2'), |={∅}▷=>^(S n)
             ⌜refRcoupl (prim_exec n (e2, σ2)) (lim_prim_exec (e2', σ2')) (coupl_rel φ)⌝)%I
            with "[] Hcpl") as "H".
        { iIntros ([] []) "H !> !>".
          iMod "H" as "(Hstate & HspecI_auth & Hwp)".
          iMod ("IH" with "[$]") as "H".
          iModIntro. done. }
        rewrite -prim_exec_Sn_not_val; [|done].
        by iApply (exec_coupl_erasure with "H").
  Qed.

End adequacy.
