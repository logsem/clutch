From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import big_op.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.prelude Require Import options.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export ghost_map.

From self.program_logic Require Export language exec weakestpre.
From self.prob_lang Require Export lang primitive_laws.
From self.prob_lang Require Export class_instances spec_ra.
From self.prob_lang Require Import tactics notation.
From self.prob Require Export couplings distribution.
Import uPred.

Local Open Scope R.


Section helper_lemma.
  Context `{!irisGS prob_lang Σ}.

  Lemma refRcoupl_bind' `{Countable A, Countable B} μ1 μ2 f g (R S : A → B → Prop) :
    ⌜refRcoupl μ1 μ2 R⌝ -∗
    (∀ a b, ⌜R a b⌝ ={∅}=∗ ⌜refRcoupl (f a) (g b) S⌝) -∗
    |={∅}=> ⌜refRcoupl (dbind f μ1) (dbind g μ2) S⌝ : iProp Σ.
  Proof.
    iIntros (HR) "HS".
    iApply (pure_impl_1 (∀ a b, R a b → refRcoupl (f a) (g b) S)).
    { iPureIntro. by eapply refRcoupl_bind. }
    iIntros (???).
    by iMod ("HS" with "[//]").
  Qed.


  Definition pure_eq (ρ1 ρ2 : cfg) := (ρ1.1 = ρ2.1) ∧ (ρ1.2.(heap) = ρ2.2.(heap)).

  Lemma foo_helper_1 (m : nat) (e1 : expr) (σ1 : state) (e1' : expr) (σ1' : state) (R: cfg -> cfg -> Prop):
    Rcoupl (prim_step e1 σ1) (prim_step e1' σ1') R ->
    (forall ρ2 ρ2', R ρ2 ρ2' -> ∃ n : nat, refRcoupl (prim_exec ρ2 m) (prim_exec ρ2' n) pure_eq)
    -> ∃ n : nat, refRcoupl (prim_exec (e1, σ1) (S m)) (prim_exec (e1', σ1') n) pure_eq.
  Proof.
    intros (μ & ((HμL & HμR) & HμSupp)) Hcont.
    assert (exists n, ∀ ρ2 ρ2' : cfg, μ (ρ2, ρ2') > 0 → refRcoupl (prim_exec ρ2 m) (prim_exec ρ2' n) pure_eq) as (n & Hn).
    (* Somehow use finiteness of the support? *)
    { admit. }
    exists (S n).
    rewrite /prim_exec /=.
    case_match; case_match.
    + specialize (Hn (e1, σ1) (e1', σ1')).
      assert (μ (e1, σ1, (e1', σ1')) > 0) as Haux; [admit | ].
      specialize (Hn Haux).
      destruct m; destruct n;
      rewrite /prim_exec in Hn.
  Admitted.

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
    dmap (λ '(e, σ), (e, heap σ)) (dbind (λ σ2, prim_exec (e1, σ2) m) (state_step σ1 α)) = dmap (λ '(e, σ), (e, heap σ)) (prim_exec (e1, σ1) m).
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
    * split.
      { rewrite lmarg_dprod //. }
      { rewrite rmarg_dprod //. }
    * intros [] [->%dret_pos ?]%dprod_pos. simpl.
      apply state_step_support_equiv_rel in H.
      by inversion H.
  Qed.

  (* Lemma alejandro_magic σ1 α m : *)
  (*   Rcoupl (dret σ1) (state_step σ1 α) (λ σ2 σ2', ∀ e, Rcoupl (prim_exec (e, σ2) m) (prim_exec (e, σ2') m) pure_eq). *)
  (* Proof. *)

  Lemma pure_eq_coupl_sym μ1 μ2 :
    Rcoupl μ1 μ2 pure_eq
    -> Rcoupl μ2 μ1 pure_eq.
  Proof.
    intros H.
    apply qux.
    apply qux in H.
    auto.
  Qed.

  Lemma pure_eq_coupl_trans μ1 μ2 μ3 :
    Rcoupl μ1 μ2 pure_eq
    -> Rcoupl μ2 μ3 pure_eq
    -> Rcoupl μ1 μ3 pure_eq.
  Proof.
    intros H12 H23.
    apply qux.
    apply qux in H12.
    apply qux in H23.
    rewrite H12; auto.
  Qed.


  Lemma baar e1 σ1 α b:
      det_head_step_pred e1 σ1 ->
      det_head_step_pred e1 (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [b]]> σ1).
  Proof.
    intro Hdet.
    inversion Hdet; econstructor; eauto.
  Qed.


  Lemma baaar e1 σ1 e2 σ2 α b:
      det_head_step_rel e1 σ1 e2 σ2 ->
      det_head_step_rel e1 (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [b]]> σ1)
                         e2 (state_upd_tapes <[α := σ2.(tapes) !!! α ++ [b]]> σ2).
  Proof.
    intro Hdet.
    inversion Hdet; econstructor; eauto.
  Qed.

  Lemma head_step_alloc_rw σ:
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


  Lemma head_step_flip_nonempty_rw σ l b bs :
    σ.(tapes) !! l = Some (b :: bs) ->
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


  Lemma head_step_flip_empty_rw σ l  :
    σ.(tapes) !! l = Some ([]) ->
    head_step (flip #lbl:l) σ = fair_conv_comb (dret (Val(#true), σ)) (dret (Val(#false), σ)).
  Proof.
    intro Hσ.
    apply distr_ext.
    intro ρ.
    rewrite /pmf/head_step/head_step_pmf/=/dbind_pmf/dret_pmf/=.
  Admitted.

  Lemma head_step_flip_unalloc_rw σ l  :
    σ.(tapes) !! l = None ->
    head_step (flip #lbl:l) σ = fair_conv_comb (dret (Val(#true), σ)) (dret (Val(#false), σ)).
  Proof.
  Admitted.

  Lemma upd_tape_some σ α b bs:
    tapes σ !! α = Some bs ->
      tapes (state_upd_tapes <[α:=tapes σ !!! α ++ [b]]> σ) !! α =  Some (bs++[b]).
  Proof.
    Admitted.


  Lemma upd_tape_some_trivial σ α bs:
    tapes σ !! α = Some bs ->
      state_upd_tapes <[α:=tapes σ !!! α]> σ = σ.
  Proof.
    Admitted.


  Lemma upd_tape_none σ α b :
    tapes σ !! α = None ->
      tapes (state_upd_tapes <[α:=tapes σ !!! α ++ [b]]> σ) !! α =  Some ([b]).
  Proof.
    Admitted.

  Lemma upd_diff_tape σ α β b:
    α ≠ β ->
    tapes σ !! α = tapes (state_upd_tapes <[β:=tapes σ !!! β ++ b]> σ) !! α.
  Proof.
    Admitted.

  Lemma upd_diff_tape_comm σ α β bs bs':
    α ≠ β ->
    state_upd_tapes <[β:= bs]> (state_upd_tapes <[α := bs']> σ) =
    state_upd_tapes <[α:= bs']> (state_upd_tapes <[β := bs]> σ).
  Proof.
    Admitted.

  Lemma upd_diff_tape_tot σ α β bs:
    α ≠ β ->
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


  (* To prove the following, weed to add extra lemmas to locations.v *)
  Lemma fresh_loc_upd_some σ α bs bs' :
    (tapes σ) !! α = Some bs ->
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
    (tapes σ) !! α = Some bs ->
    state_upd_tapes <[fresh_loc (tapes σ):=bs']> (state_upd_tapes <[α:=bs'']> σ)
    = state_upd_tapes <[α:=bs'']> (state_upd_tapes <[fresh_loc (tapes σ):=bs']> σ).
  Proof.
    intros H.
    apply elem_fresh_ne in H.
    unfold state_upd_tapes.
    by rewrite insert_commute.
  Qed.

  Lemma fresh_loc_lookup σ α bs bs' :
    (tapes σ) !! α = Some bs ->
    (tapes (state_upd_tapes <[fresh_loc (tapes σ):=bs']> σ)) !! α = Some bs.
  Proof.
    intros H.
    pose proof (elem_fresh_ne _ _ _ H).
    by rewrite lookup_insert_ne.
  Qed.


  Lemma exec_coupl_eq e σ m :
    Rcoupl (prim_exec (e, σ) m)
    (prim_exec (e, σ) m) pure_eq.
  Proof.
    move : e σ.
    induction m; intros e σ.
    + rewrite /prim_exec.
      case_match.
      ++ exists (dret ((e, σ),(e, σ))).
        split ; [split; [ rewrite /lmarg dmap_dret; auto | rewrite /rmarg dmap_dret; auto ]  |  ].
        intros (ρ2 & ρ2') H2; simpl; auto.
        apply dret_pos in H2.
        simplify_eq.
        rewrite /pure_eq; auto.
      ++ exists dzero.
         split; [split; [ rewrite /lmarg dmap_dzero; auto | rewrite /rmarg dmap_dzero; auto ] | ].
         intros (ρ2 & ρ2') H2; simpl; auto.
         rewrite /pmf/dzero in H2; lra.
    + rewrite prim_exec_unfold /=.
      case_match.
      ++ exists (dret ((e, σ),(e, σ))).
        split ; [split; [ rewrite /lmarg dmap_dret; auto | rewrite /rmarg dmap_dret; auto ]  |  ].
        intros (ρ2 & ρ2') H2; simpl; auto.
        apply dret_pos in H2.
        simplify_eq.
        rewrite /pure_eq; auto.
      ++ apply (Rcoupl_bind _ _ _ _ (=)); [ | apply Rcoupl_eq].
         intros ? (e2 & σ2) ->.
         apply (IHm e2 σ2).
  Qed.

  (* Hopefully this is not too hard to show *)
  Lemma exec_coupl_eq_irrel e σ l m :
    tapes σ !! l = None ->
    Rcoupl (prim_exec (e, σ) m)
    (prim_exec (e, (state_upd_tapes <[l:=[]]> σ)) m) pure_eq.
  Proof. Admitted.


  Lemma pos_sum_nn_real p q :
    (0 <= p) -> (0 <= q) ->
    (0 < p + q) ->
    (0 < p \/ 0 < q).
  Proof.
    intros Hp Hq Hsum.
    destruct Hp as [ Hp | Hp ]; simplify_eq; auto.
    destruct Hq as [ Hq | Hq ]; simplify_eq; auto.
    lra.
  Qed.

  Lemma pos_prod_nn_real p q :
    (0 <= p) -> (0 <= q) ->
    (0 < p * q) ->
    (0 < p /\ 0 < q).
  Proof.
    intros Hp Hq Hsum.
    destruct Hp as [ Hp | Hp ]; simplify_eq; split; auto; try lra.
    destruct Hq as [ Hq | Hq ]; simplify_eq ; auto; lra.
  Qed.


  Lemma prim_coupl_upd_tapes : forall m e1 σ1 α,
      Rcoupl (prim_exec (e1, σ1) m)
             (fair_conv_comb (prim_exec (e1, (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [true]]> σ1)) m )
                             (prim_exec (e1, (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [false]]> σ1)) m ))
             (pure_eq).
  Proof.
    induction m; intros e1 σ1 α.
    - rewrite /prim_exec/=.
      destruct (to_val e1).
      + exists (dprod (dret (e1, σ1))
    (fair_conv_comb (dret (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [true]]> σ1))
       (dret (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [false]]> σ1)))).
        split; [split ; [ rewrite lmarg_dprod // | rewrite rmarg_dprod //] | ].
        intros ((e2 & σ2) & (e2' & σ2')) Hpos.
        simpl in *.
        rewrite /pmf/= in Hpos.
        rewrite fair_conv_comb_pmf in Hpos.
        assert ((dret (e1, σ1) (e2, σ2) > 0 /\ dret (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [true]]> σ1) (e2', σ2') > 0)
            \/ (dret (e1, σ1) (e2, σ2) > 0 /\ dret (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [false]]> σ1) (e2', σ2') > 0))
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
          apply pos_sum_nn_real in Hpos; [ | apply Rmult_le_pos; apply pmf_pos | apply Rmult_le_pos; apply pmf_pos].
          destruct Hpos; [left | right]; apply pos_prod_nn_real; auto; rewrite Rmult_comm; auto.
       }
        ++ rewrite /pmf/=/dret_pmf/= in Hpos1.
           case_bool_decide as Heq1; try lra.
           rewrite Heq1.
           rewrite /pmf/=/dret_pmf/= in Hpos2.
           case_bool_decide as Heq2; try lra.
           rewrite Heq2.
           rewrite /pure_eq/=//.
        ++ rewrite /pmf/=/dret_pmf/= in Hpos3.
           case_bool_decide as Heq3; try lra.
           rewrite Heq3.
           rewrite /pmf/=/dret_pmf/= in Hpos4.
           case_bool_decide as Heq4; try lra.
           rewrite Heq4.
           rewrite /pure_eq/=//.
    + exists dzero.
    split.
    {
      split.
      { rewrite /lmarg dmap_dzero; auto. }
      { apply distr_ext; intros.
        rewrite rmarg_pmf fair_conv_comb_pmf /pmf /=.
        rewrite SeriesC_0; auto; lra.
      }
    }
    intros ? Hpos.
    rewrite /pmf/= in Hpos.
    lra.
  - simpl.
    destruct (to_val e1) eqn:He1.
    + specialize (IHm e1 σ1 α).
      rewrite /prim_exec/= in IHm.
      destruct m; simpl in *;
      rewrite He1 in IHm; auto.
    + rewrite /prim_step /=.
      destruct (decomp e1) as [K ered] eqn:decomp_e1.
      rewrite decomp_e1.
      destruct (is_det_head_step ered σ1) eqn:Hdet.
      ++ apply is_det_head_step_true in Hdet.
         apply det_step_pred_ex_rel in Hdet.
         destruct Hdet as (e2 & (σ2 & Hdet)).
         pose proof (baaar ered σ1 e2 σ2 α true Hdet) as HdetT.
         pose proof (baaar ered σ1 e2 σ2 α false Hdet) as HdetF.
         erewrite 3 det_head_step_singleton; eauto.
         do 6 rewrite dret_id_left; auto.
         (* Woohooo! *)
      ++ assert (¬ det_head_step_pred ered σ1) as Hndet.
         {destruct (is_det_head_step_true ered σ1); auto. intro Hf.
         specialize (H0 Hf); simplify_eq. rewrite H0 in Hdet; auto. }
         destruct (det_or_prob_or_dzero ered σ1) as [[ HD | HP ] | HZ]; [destruct Hndet; auto | | ]; last first.
         +++ assert (head_step ered σ1 = dzero) as Haux1; auto.
             assert (head_step ered (state_upd_tapes <[α:=tapes σ1 !!! α ++ [true]]> σ1) = dzero) as Haux2; auto.
             assert (head_step ered (state_upd_tapes <[α:=tapes σ1 !!! α ++ [false]]> σ1) = dzero) as Haux3; auto.
             rewrite Haux1 Haux2 Haux3.
             (* Everything should be rewritable to dzero here *)
             rewrite <- dbind_assoc.
             rewrite dbind_dzero.
             exists dzero; split; [split | intros ? H'; rewrite /pmf/dzero in H'; lra].
             ++++ rewrite /lmarg dmap_dzero; auto.
             ++++ rewrite /rmarg dmap_dzero.
                  apply distr_ext.
                  intros ?.
                  rewrite fair_conv_comb_pmf.
                  rewrite /pmf/dzero; lra.
         +++ rewrite <- dbind_assoc.
           inversion HP; simplify_eq.
             ++++ do 3 rewrite head_step_alloc_rw; simpl.
                  do 3 rewrite dret_id_left.
                  do 3 rewrite dret_id_left.
                  assert (fresh_loc (tapes σ1) = (fresh_loc (<[α:=tapes σ1 !!! α ++ [true]]> (tapes σ1)))) as <-.
                  { admit. }
                  assert (fresh_loc (tapes σ1) = (fresh_loc (<[α:=tapes σ1 !!! α ++ [false]]> (tapes σ1)))) as <-.
                  { admit. }
                  (* We may need to require that α is in the domain of σ1 *)
                  admit.
             ++++
               destruct H as (b & H).
               destruct H as (bs & H).
               destruct (decide (α = l)) as [-> | Hαneql].
               +++++
               rewrite (head_step_flip_nonempty_rw _ _ b bs); auto.
               rewrite (head_step_flip_nonempty_rw _ _ b (bs++[true])); last first.
               { rewrite app_comm_cons.
                 apply upd_tape_some; auto. }
               rewrite (head_step_flip_nonempty_rw _ _ b (bs++[false])); last first.
               { rewrite app_comm_cons.
                 apply upd_tape_some; auto. }
               do 3 rewrite dret_id_left.
               do 3 rewrite dret_id_left.
               apply lookup_total_correct in H.
               rewrite H.
               do 2 rewrite upd_tape_twice.
               pose proof (IHm (fill K #b) (state_upd_tapes <[l:=bs]> σ1) l ) as IHm2.
               rewrite (upd_tape_app _ l bs [true]).
               rewrite (upd_tape_app _ l bs [false]).
               auto.
               +++++
               rewrite (head_step_flip_nonempty_rw _ _ b bs); auto.
               rewrite (head_step_flip_nonempty_rw _ _ b bs); last first.
               { rewrite <- H. symmetry. apply (upd_diff_tape); auto. }
               rewrite (head_step_flip_nonempty_rw _ _ b bs); last first.
               { rewrite <- H. symmetry. apply (upd_diff_tape); auto. }
               do 3 rewrite dret_id_left.
               do 3 rewrite dret_id_left.
               pose proof (IHm (fill K #b) (state_upd_tapes <[l:=bs]> σ1) α ) as IHm2.
               rewrite {1}upd_diff_tape_comm; auto.
               rewrite {1}(upd_diff_tape_comm _ α l bs (tapes σ1 !!! α ++ [false])); auto.
               rewrite <- (upd_diff_tape_tot _ α l ) in IHm2; auto.
             ++++ destruct H.
                  +++++ destruct (decide (α = l)) as [-> | Hαneql].
               ++++++
               rewrite (head_step_flip_empty_rw _ _); auto.
               rewrite (head_step_flip_nonempty_rw _ _ true []); last first.
               { rewrite (upd_tape_some σ1 l true []); auto. }
               rewrite (head_step_flip_nonempty_rw _ _ false []); last first.
               { rewrite (upd_tape_some σ1 l false []); auto. }
               do 3 rewrite dret_id_left.
               rewrite /fair_conv_comb.
               rewrite <- dbind_assoc.
               apply (Rcoupl_bind _ _ _ _ (=)); [ | apply Rcoupl_eq].
               intros ? b ->.
               do 2 rewrite upd_tape_twice.
               pose proof (lookup_total_correct _ _ _ H) as H'.
               rewrite <- H'.
               rewrite (upd_tape_some_trivial _ _ []); eauto.
               destruct b; simpl; do 2 rewrite dret_id_left; apply exec_coupl_eq.
               ++++++
               rewrite (head_step_flip_empty_rw _ _); auto.
               rewrite (head_step_flip_empty_rw _ _); last first.
               { rewrite <- upd_diff_tape; auto. }
               rewrite (head_step_flip_empty_rw _ _ ); last first.
               { rewrite <- upd_diff_tape; auto. }
               rewrite {3 4}/fair_conv_comb.
               do 4 rewrite <- dbind_assoc.
               erewrite <- (dbind_fair_conv_comb _ _ fair_coin).
               rewrite {2}/fair_conv_comb.
               rewrite {1}dbind_assoc.
               rewrite /fair_conv_comb.
               rewrite <-dbind_assoc.
               rewrite <-dbind_assoc.
               eapply (Rcoupl_bind _ _ _ _ (=)); [ | apply Rcoupl_eq].
               intros ? ? ->.
               destruct b.
               +++++++
                 do 6 rewrite dret_id_left.
                 specialize (IHm (fill K #true) σ1 α).
                 auto.
               +++++++
                 do 6 rewrite dret_id_left.
                 specialize (IHm (fill K #false) σ1 α).
                 auto.
            +++++ destruct (decide (α = l)) as [-> | Hαneql].
               ++++++
               rewrite (head_step_flip_unalloc_rw _ _); auto.
               rewrite (head_step_flip_nonempty_rw _ _ true []); last first.
               { apply upd_tape_none; auto. }
               rewrite (head_step_flip_nonempty_rw _ _ false []); last first.
               { apply upd_tape_none; auto. }
               do 3 rewrite dret_id_left.
               rewrite /fair_conv_comb.
               rewrite <- dbind_assoc.
               apply (Rcoupl_bind _ _ _ _ (=)); [ | apply Rcoupl_eq].
               intros ? b ->.
               do 2 rewrite upd_tape_twice.
               destruct b; simpl; [do 2 rewrite dret_id_left | do 3 rewrite dret_id_left].
               +++++++ apply exec_coupl_eq_irrel; auto.
               +++++++ apply exec_coupl_eq_irrel; auto.

               ++++++
               rewrite (head_step_flip_unalloc_rw _ _); auto.
               rewrite (head_step_flip_unalloc_rw _ _); last first.
               { rewrite <- H; symmetry; apply upd_diff_tape ; auto. }
               rewrite (head_step_flip_unalloc_rw _ _ ); last first.
               { rewrite <- H; symmetry; apply upd_diff_tape ; auto. }
               rewrite {3 4}/fair_conv_comb.
               do 4 rewrite <- dbind_assoc.
               erewrite <- (dbind_fair_conv_comb _ _ fair_coin).
               rewrite {2}/fair_conv_comb.
               rewrite {1}dbind_assoc.
               rewrite /fair_conv_comb.
               rewrite <-dbind_assoc.
               rewrite <-dbind_assoc.
               eapply (Rcoupl_bind _ _ _ _ (=)); [ | apply Rcoupl_eq ].
               intros ? ? ->.
               destruct b.
               +++++++
                 do 6 rewrite dret_id_left.
                 specialize (IHm (fill K #true) σ1 α).
                 auto.
               +++++++
                 do 6 rewrite dret_id_left.
                 specialize (IHm (fill K #false) σ1 α).
                 auto.
  Admitted.


  Lemma prim_coupl_upd_tapes_dom : forall m e1 σ1 α bs,
      σ1.(tapes) !! α = Some bs ->
      Rcoupl (prim_exec (e1, σ1) m)
             (fair_conv_comb (prim_exec (e1, (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [true]]> σ1)) m )
                             (prim_exec (e1, (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [false]]> σ1)) m ))
             (pure_eq).
  Proof.
    induction m; intros e1 σ1 α bs Hα.
    - rewrite /prim_exec/=.
      destruct (to_val e1).
      + exists (dprod (dret (e1, σ1))
    (fair_conv_comb (dret (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [true]]> σ1))
       (dret (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [false]]> σ1)))).
        split; [split ; [ rewrite lmarg_dprod // | rewrite rmarg_dprod //] | ].
        intros ((e2 & σ2) & (e2' & σ2')) Hpos.
        simpl in *.
        rewrite /pmf/= in Hpos.
        rewrite fair_conv_comb_pmf in Hpos.
        assert ((dret (e1, σ1) (e2, σ2) > 0 /\ dret (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [true]]> σ1) (e2', σ2') > 0)
            \/ (dret (e1, σ1) (e2, σ2) > 0 /\ dret (e1, state_upd_tapes <[α:=tapes σ1 !!! α ++ [false]]> σ1) (e2', σ2') > 0))
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
          apply pos_sum_nn_real in Hpos; [ | apply Rmult_le_pos; apply pmf_pos | apply Rmult_le_pos; apply pmf_pos].
          destruct Hpos; [left | right]; apply pos_prod_nn_real; auto; rewrite Rmult_comm; auto.
       }
        ++ rewrite /pmf/=/dret_pmf/= in Hpos1.
           case_bool_decide as Heq1; try lra.
           rewrite Heq1.
           rewrite /pmf/=/dret_pmf/= in Hpos2.
           case_bool_decide as Heq2; try lra.
           rewrite Heq2.
           rewrite /pure_eq/=//.
        ++ rewrite /pmf/=/dret_pmf/= in Hpos3.
           case_bool_decide as Heq3; try lra.
           rewrite Heq3.
           rewrite /pmf/=/dret_pmf/= in Hpos4.
           case_bool_decide as Heq4; try lra.
           rewrite Heq4.
           rewrite /pure_eq/=//.
    + exists dzero.
    split.
    {
      split.
      { rewrite /lmarg dmap_dzero; auto. }
      { apply distr_ext; intros.
        rewrite rmarg_pmf fair_conv_comb_pmf /pmf /=.
        rewrite SeriesC_0; auto; lra.
      }
    }
    intros ? Hpos.
    rewrite /pmf/= in Hpos.
    lra.
  - simpl.
    destruct (to_val e1) eqn:He1.
    + specialize (IHm e1 σ1 α bs Hα).
      rewrite /prim_exec/= in IHm.
      destruct m; simpl in *;
      rewrite He1 in IHm; auto.
    + rewrite /prim_step /=.
      destruct (decomp e1) as [K ered] eqn:decomp_e1.
      rewrite decomp_e1.
      destruct (is_det_head_step ered σ1) eqn:Hdet.
      ++ apply is_det_head_step_true in Hdet.
         apply det_step_pred_ex_rel in Hdet.
         destruct Hdet as (e2 & (σ2 & Hdet)).
         pose proof (baaar ered σ1 e2 σ2 α true Hdet) as HdetT.
         pose proof (baaar ered σ1 e2 σ2 α false Hdet) as HdetF.
         pose proof (det_step_eq_tapes _ _ _ _ Hdet) as Htapes.
         rewrite Htapes in Hα.
         erewrite 3 det_head_step_singleton; eauto.
         do 6 rewrite dret_id_left; auto.
         apply (IHm (fill K e2) σ2 α bs Hα).
         (* Woohooo! *)
      ++ assert (¬ det_head_step_pred ered σ1) as Hndet.
         {destruct (is_det_head_step_true ered σ1); auto. intro Hf.
         specialize (H0 Hf); simplify_eq. rewrite H0 in Hdet; auto. }
         destruct (det_or_prob_or_dzero ered σ1) as [[ HD | HP ] | HZ]; [destruct Hndet; auto | | ]; last first.
         +++ assert (head_step ered σ1 = dzero) as Haux1; auto.
             assert (head_step ered (state_upd_tapes <[α:=tapes σ1 !!! α ++ [true]]> σ1) = dzero) as Haux2; auto.
             assert (head_step ered (state_upd_tapes <[α:=tapes σ1 !!! α ++ [false]]> σ1) = dzero) as Haux3; auto.
             rewrite Haux1 Haux2 Haux3.
             (* Everything should be rewritable to dzero here *)
             rewrite <- dbind_assoc.
             rewrite dbind_dzero.
             exists dzero; split; [split | intros ? H'; rewrite /pmf/dzero in H'; lra].
             ++++ rewrite /lmarg dmap_dzero; auto.
             ++++ rewrite /rmarg dmap_dzero.
                  apply distr_ext.
                  intros ?.
                  rewrite fair_conv_comb_pmf.
                  rewrite /pmf/dzero; lra.
         +++ rewrite <- dbind_assoc.
           inversion HP; simplify_eq.
             ++++ do 3 rewrite head_step_alloc_rw; simpl.
                  do 3 rewrite dret_id_left.
                  do 3 rewrite dret_id_left.
                  assert (fresh_loc (tapes σ1) = (fresh_loc (<[α:=tapes σ1 !!! α ++ [true]]> (tapes σ1)))) as <-.
                  { eapply fresh_loc_upd_some; eauto. }
                  assert (fresh_loc (tapes σ1) = (fresh_loc (<[α:=tapes σ1 !!! α ++ [false]]> (tapes σ1)))) as <-.
                  { eapply fresh_loc_upd_some; eauto. }
                  specialize
                    (IHm (fill K #lbl:(fresh_loc (tapes σ1)))(state_upd_tapes <[fresh_loc (tapes σ1):=[]]> σ1) α bs).
                  apply lookup_total_correct in Hα as Hαtot.
                  revert IHm ; intro IHm.
                  pose proof (elem_fresh_ne _ _ _ Hα) as Hne.
                  assert (α ≠ fresh_loc (tapes σ1)) as Hne' by auto ; clear Hne.
                  rewrite -(upd_diff_tape_tot σ1 _ _ _ Hne') in IHm.
                  specialize (IHm (fresh_loc_lookup σ1 α bs [] Hα)).
                  erewrite <- (fresh_loc_upd_swap σ1) in IHm; eauto.
                  erewrite <- (fresh_loc_upd_swap σ1) in IHm; eauto.
             ++++
               destruct H as (b' & H).
               destruct H as (bs' & H).
               destruct (decide (α = l)) as [-> | Hαneql].
               +++++
               rewrite (head_step_flip_nonempty_rw _ _ b' bs'); auto.
               rewrite (head_step_flip_nonempty_rw _ _ b' (bs'++[true])); last first.
               { rewrite app_comm_cons.
                 apply upd_tape_some; auto. }
               rewrite (head_step_flip_nonempty_rw _ _ b' (bs'++[false])); last first.
               { rewrite app_comm_cons.
                 apply upd_tape_some; auto. }
               do 3 rewrite dret_id_left.
               do 3 rewrite dret_id_left.
               apply lookup_total_correct in H.
               rewrite H.
               do 2 rewrite upd_tape_twice.
               assert (tapes (state_upd_tapes <[l:=bs']> σ1) !! l = Some bs') as Hl.
               { apply lookup_insert. }
               pose proof (IHm (fill K #b') (state_upd_tapes <[l:=bs']> σ1) l bs' Hl) as IHm2.
               rewrite (upd_tape_app _ l bs' [true]).
               rewrite (upd_tape_app _ l bs' [false]).
               auto.
               +++++
               rewrite (head_step_flip_nonempty_rw _ _ b' bs'); auto.
               rewrite (head_step_flip_nonempty_rw _ _ b' bs'); last first.
               { rewrite <- H. symmetry. apply (upd_diff_tape); auto. }
               rewrite (head_step_flip_nonempty_rw _ _ b' bs'); last first.
               { rewrite <- H. symmetry. apply (upd_diff_tape); auto. }
               do 3 rewrite dret_id_left.
               do 3 rewrite dret_id_left.
               assert (tapes (state_upd_tapes <[l:=bs']> σ1) !! α = Some bs) as Hα'.
               { rewrite lookup_insert_ne; auto. }
               pose proof (IHm (fill K #b') (state_upd_tapes <[l:=bs']> σ1) α bs Hα') as IHm2.
               rewrite {1}upd_diff_tape_comm; auto.
               rewrite {1}(upd_diff_tape_comm _ α l bs' (tapes σ1 !!! α ++ [false])); auto.
               rewrite <- (upd_diff_tape_tot _ α l ) in IHm2; auto.
             ++++ destruct H.
                  +++++ destruct (decide (α = l)) as [-> | Hαneql].
               ++++++
               rewrite (head_step_flip_empty_rw _ _); auto.
               rewrite (head_step_flip_nonempty_rw _ _ true []); last first.
               { rewrite (upd_tape_some σ1 l true []); auto. }
               rewrite (head_step_flip_nonempty_rw _ _ false []); last first.
               { rewrite (upd_tape_some σ1 l false []); auto. }
               do 3 rewrite dret_id_left.
               rewrite /fair_conv_comb.
               rewrite <- dbind_assoc.
               apply (Rcoupl_bind _ _ _ _ (=)); [ | apply Rcoupl_eq].
               intros ? b ->.
               do 2 rewrite upd_tape_twice.
               pose proof (lookup_total_correct _ _ _ H) as H'.
               rewrite <- H'.
               rewrite (upd_tape_some_trivial _ _ []); eauto.
               destruct b; simpl; do 2 rewrite dret_id_left; apply exec_coupl_eq.
               ++++++
               rewrite (head_step_flip_empty_rw _ _); auto.
               rewrite (head_step_flip_empty_rw _ _); last first.
               { rewrite <- upd_diff_tape; auto. }
               rewrite (head_step_flip_empty_rw _ _ ); last first.
               { rewrite <- upd_diff_tape; auto. }
               rewrite {3 4}/fair_conv_comb.
               do 4 rewrite <- dbind_assoc.
               erewrite <- (dbind_fair_conv_comb _ _ fair_coin).
               rewrite {2}/fair_conv_comb.
               rewrite {1}dbind_assoc.
               rewrite /fair_conv_comb.
               rewrite <-dbind_assoc.
               rewrite <-dbind_assoc.
               eapply (Rcoupl_bind _ _ _ _ (=)); [ | apply Rcoupl_eq].
               intros ? ? ->.
               destruct b.
               +++++++
                 do 6 rewrite dret_id_left.
                 specialize (IHm (fill K #true) σ1 α bs).
                 auto.
               +++++++
                 do 6 rewrite dret_id_left.
                 specialize (IHm (fill K #false) σ1 α bs).
                 auto.
            +++++ destruct (decide (α = l)) as [-> | Hαneql].
               ++++++
                 rewrite H in Hα.
                 simplify_eq.

               ++++++
               rewrite (head_step_flip_unalloc_rw _ _); auto.
               rewrite (head_step_flip_unalloc_rw _ _); last first.
               { rewrite <- H; symmetry; apply upd_diff_tape ; auto. }
               rewrite (head_step_flip_unalloc_rw _ _ ); last first.
               { rewrite <- H; symmetry; apply upd_diff_tape ; auto. }
               rewrite {3 4}/fair_conv_comb.
               do 4 rewrite <- dbind_assoc.
               erewrite <- (dbind_fair_conv_comb _ _ fair_coin).
               rewrite {2}/fair_conv_comb.
               rewrite {1}dbind_assoc.
               rewrite /fair_conv_comb.
               rewrite <-dbind_assoc.
               rewrite <-dbind_assoc.
               eapply (Rcoupl_bind _ _ _ _ (=)); [ | apply Rcoupl_eq ].
               intros ? ? ->.
               destruct b.
               +++++++
                 do 6 rewrite dret_id_left.
                 specialize (IHm (fill K #true) σ1 α bs).
                 auto.
               +++++++
                 do 6 rewrite dret_id_left.
                 specialize (IHm (fill K #false) σ1 α bs).
                 auto.
  Qed.


  Lemma prim_coupl_step_prim : forall m e1 σ1 α,
      Rcoupl (prim_exec (e1, σ1) m)
             (dbind (λ σ2, prim_exec (e1, σ2) m) (state_step σ1 α))
             pure_eq.
  Proof.
    intros; rewrite state_step_fair_conv_comb fair_conv_comb_dbind.
    do 2 rewrite dret_id_left.
    apply prim_coupl_upd_tapes.
  Qed.



  Lemma quuuux e1 σ1 α m :
    dmap (λ '(e, σ), (e, heap σ)) (prim_exec (e1, σ1) m) = dmap (λ '(e, σ), (e, heap σ)) (dbind (λ σ2, (prim_exec (e1, σ2) m)) (state_step σ1 α)).
  Proof.
    apply qux.
    assert
      ((state_step σ1 α ≫= (λ σ2 : language.state prob_lang, prim_exec (e1, σ2) m))=
         (fair_conv_comb (prim_exec (e1, (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [true]]> σ1)) m )
                             (prim_exec (e1, (state_upd_tapes <[α := σ1.(tapes) !!! α ++ [false]]> σ1)) m ))
      ) as ->; [ | apply prim_coupl_upd_tapes].
    rewrite state_step_fair_conv_comb fair_conv_comb_dbind.
    do 2 rewrite dret_id_left; auto.
  Qed.



  Lemma baz e1 σ1 e1' σ1' α α' R m :
    Rcoupl (state_step σ1 α) (state_step σ1' α') R →
    (∀ σ2 σ2', R σ2 σ2' → refRcoupl (prim_exec (e1, σ2) (S m)) (lim_prim_exec (e1', σ2')) pure_eq) →
    refRcoupl (prim_exec (e1, σ1) (S m)) (lim_prim_exec (e1', σ1')) pure_eq.
  Proof.
    intros HR Hcont.
    assert (refRcoupl (dbind (λ σ2, prim_exec (e1, σ2) (S m)) (state_step σ1 α))
                      (dbind (λ σ2', lim_prim_exec (e1', σ2')) (state_step σ1' α')) pure_eq) as H.
    { eapply refRcoupl_bind; [|done]. by apply weaken_coupl. }

    (* destruct m. *)
    (* - simpl in *. destruct (prob_lang.to_val e1) eqn:Heq.  *)
    (*   +  *)

    apply quux.
    apply quux in H.
    assert ((dmap (λ '(e, σ), (e, heap σ)) (prim_exec (e1, σ1) (S m))) =
            (dmap (λ '(e, σ), (e, heap σ)) (dbind (λ σ2 : language.state prob_lang, prim_exec (e1, σ2) (S m)) (state_step σ1 α)))) as H1.
    { rewrite prim_exec_Sn.
      assert ((dbind (λ σ2, prim_exec (e1, σ2) (S m)) (state_step σ1 α)) =
              (dbind (λ σ2 , (dbind (λ ρ' : language.cfg prob_lang, prim_exec ρ' m) (prim_step_or_val (e1, σ2)))) (state_step σ1 α))) as Hfoo by admit.
      rewrite Hfoo. clear Hfoo.
      apply qux.
      rewrite dbind_assoc.
      eapply (Rcoupl_bind _ _ _ _ pure_eq).
      {


      admit. }
    assert ((dmap (λ '(e, σ), (e, heap σ)) (lim_prim_exec (e1', σ1'))) =
            (dmap (λ '(e, σ), (e, heap σ)) (dbind (λ σ2' : language.state prob_lang, lim_prim_exec (e1', σ2')) (state_step σ1' α')))) as H2.
    { admit. }
    Admitted.


  Lemma foo (e1 : expr) (σ1 : state) (e1' : expr) (σ1' : state) (m : nat) :
    to_val e1 = None ->
    exec_coupl  e1 σ1 e1' σ1'
      (λ '(e2, σ2) '(e2', σ2'), ⌜refRcoupl (prim_exec (e2, σ2) m) (lim_prim_exec (e2', σ2')) pure_eq⌝)%I ⊢@{iProp Σ}
    |={∅}=> ⌜refRcoupl (prim_exec (e1, σ1) (S m) ) (lim_prim_exec (e1', σ1')) pure_eq⌝.
  Proof.
    iIntros (Hv) "Hexec".
    iAssert (⌜to_val e1 = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /exec_coupl /exec_coupl'.
    iPoseProof (least_fixpoint_iter
                  (exec_coupl_pre
                     (λ '(e2, σ2) '(e2', σ2'), ⌜refRcoupl (prim_exec (e2, σ2) m) (lim_prim_exec (e2', σ2')) pure_eq⌝)%I)
                  (λ '((e1, σ1), (e1', σ1')), ⌜to_val e1 = None⌝ ={∅}=∗
                      ⌜refRcoupl (prim_exec (e1, σ1) (S m)) (lim_prim_exec (e1', σ1')) pure_eq⌝)%I
                 with "[]") as "H"; last first.
    { iIntros "Hfix %". by iMod ("H" $! ((_, _), (_, _)) with "Hfix [//]"). }
    clear.
    iIntros "!#" ([[e1 σ1] [e1' σ1']]). rewrite /exec_coupl_pre.
    iIntros "[(% & %Hcpl & % & H) | [? | [? | H]]] %Hv".
    - rewrite prim_exec_Sn.
      rewrite -bar.
      rewrite {1}/prim_step_or_val /= Hv.
      assert (to_val e1' = None) as Hv' by admit.
      rewrite {1}/prim_step_or_val /= Hv'.
      iApply (refRcoupl_bind' _ _ _ _ R2).
      { iPureIntro. by apply weaken_coupl. }
      iIntros ([] [] HR2). iMod ("H" with "[//]"). auto.
    - admit.
    - admit.
    - simpl. rewrite Hv.
      iInduction (list_prod (get_active σ1) (get_active σ1')) as [| [α α']] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[(% & %Hcpl & H) | Ht]"; last first.
      { by iApply "IH". }
      iClear "IH". simpl in *.

Admitted.


End helper_lemma.


Section adequacy.
  Context `{!prelocGS Σ}.

  Definition coupl_rel (φ : val → val → Prop) (ρ ρ' : cfg) : Prop :=
    match to_val ρ.1, to_val ρ'.1 with
    | Some v, Some v' => φ v v'
    | _, _ => False
    end.

  Theorem wp_coupling e σ e' σ' n φ :
    state_interp σ ∗ spec_interp (e', σ') ∗ spec_ctx ∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜refRcoupl (prim_exec (e, σ) n) (lim_prim_exec (e', σ')) (coupl_rel φ)⌝.
  Proof.
    iRevert (e σ e' σ').
    iInduction n as [|n] "IH"; iIntros (e σ e' σ') "([Hh Ht] & HspecI_auth & #Hctx & Hwp)".
    - rewrite /prim_exec /=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite wp_value_fupd.
        iMod "Hwp" as (v') "[Hspec_frag %]".
        iInv specN as (ξ ρ e0 σ0) ">(HspecI_frag & %Hexec & Hspec_auth & Hstate)" "_".
        iDestruct (spec_interp_auth_frag_agree with "HspecI_auth HspecI_frag") as %<-.
        iDestruct (spec_prog_auth_frag_agree with "Hspec_auth Hspec_frag") as %->.
        iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        (* This is doable (a pure [refRcoupl] result *)
        admit.
      + iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        (* also doable *)
        admit.
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
        (* This is doable - LHS in the goal is equal to [dret (v, σ)] *)
        admit.
      + rewrite wp_unfold /wp_pre /= Heq.
        iMod ("Hwp" with "[$]") as "Hcpl".
        iModIntro.
        iPoseProof
          (exec_coupl_mono _ (λ '(e2, σ2) '(e2', σ2'), |={∅}▷=> |={∅}▷=>^n
             ⌜refRcoupl (prim_exec (e2, σ2) n) (lim_prim_exec (e2', σ2')) (coupl_rel φ)⌝)%I
            with "[] Hcpl") as "H".
        { iIntros ([] []) "H !> !>".
          iMod "H" as "(Hstate & HspecI_auth & Hwp)".
          iMod ("IH" with "[$]") as "H".
          iModIntro. done. }

        (* Now we have something of roughly the shape of the [foo] lemma *)

  Admitted.

End adequacy.
