From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Lim_seq.
From clutch.prelude Require Import Series_ext.
From clutch.con_prob_lang Require Import lang.
From clutch.foxtrot Require Import oscheduler.
From clutch.prob Require Import distribution couplings_app.

Set Default Proof Using "Type*".

Section full_info.
  Definition cfg' : Type := (list expr * gmap loc val).
  Definition full_info_state : Type := list (cfg' * nat).
  Definition cfg_to_cfg' (ρ:cfg) := (ρ.1, heap ρ.2).

  Record full_info_oscheduler :=
    MkFullInfoOsch {
        fi_osch :> oscheduler (full_info_state);
        fi_osch_tape_oblivious :: oTapeOblivious _ fi_osch;
        fi_osch_valid:
        ∀ l ρ j l' μ, fi_osch (l, ρ) = Some μ -> (μ (l', j) > 0)%R ->
                      l' = l++[(cfg_to_cfg' ρ, j)];
        fi_osch_consistent:
        ∀ l ρ, fi_osch (l, ρ) = None -> ∀ ρ', fi_osch (l, ρ') = None
      }.

  
  
  Lemma full_info_reachable_prefix (osch:full_info_oscheduler) n l ρ l' ρ' :
    (osch_exec osch n (l, ρ) (l', ρ') > 0)%R -> prefix l l'.
  Proof.
    revert l ρ l' ρ'.
    induction n; intros l ρ l' ρ'.
    - simpl. repeat case_match; try (rewrite dzero_0; lra); intros H'; apply dret_pos in H'; by simplify_eq.
    - rewrite osch_exec_Sn.
      intros H'; apply dbind_pos in H' as [[??][H1 H2]].
      apply IHn in H1.
      rewrite /osch_step_or_none in H2.
      repeat case_match.
      + rewrite /osch_step in H2. case_match; simplify_eq.
        apply dbind_pos in H2 as [[??][H' K]].
        eapply fi_osch_valid in K; last done.
        trans f; last done.
        apply dmap_pos in H' as [?[??]].
        simplify_eq. eexists _. naive_solver.
      + apply dret_pos in H2. naive_solver.
  Qed.
  
  Lemma full_info_lim_reachable_prefix (osch:full_info_oscheduler) l ρ l' ρ' :
    (osch_lim_exec osch (l, ρ) (l', ρ') > 0)%R -> prefix l l'.
  Proof.
    intros H.
    apply osch_lim_exec_pos in H as [??].
    by apply full_info_reachable_prefix in H.
  Qed.

  
  Definition is_frontier_n l n initial_l (osch:full_info_oscheduler) :=
    ∃ ρ ρ', osch_exec osch n (initial_l, ρ) (l, ρ') > 0.
  
  Definition is_frontier l initial_l (osch:full_info_oscheduler) :=
    ∃ ρ ρ', osch_lim_exec osch (initial_l, ρ) (l, ρ') > 0.

  Lemma is_frontier_n_prefix_unique n initial_l l l' osch:
    is_frontier_n l n initial_l osch -> is_frontier_n l' n initial_l osch -> prefix l l' -> l = l'.
  Proof.
    revert l l' initial_l. rewrite /is_frontier_n.
    induction n; intros l l' initial_l.
    - simpl. intros (?&H1&H2) (?&H3&H4).
      case_match eqn : Heqn1.
      { rewrite dzero_0 in H4. lra. }
      apply dret_pos in H4. simplify_eq.
      erewrite fi_osch_consistent in H2; last done.
      apply dret_pos in H2. by simplify_eq.
    - simpl. intros (?&H1&H2) (?&H3&H4).
      case_match eqn :Heqn1.
      { apply dbind_pos in H4 as [[f ?][H4 H5]].
        apply dbind_pos in H4 as [?[??]].
        case_match eqn:Heqn2; last first.
        { by erewrite fi_osch_consistent in Heqn1. }
        apply dbind_pos in H2 as [[f' ?][H6 H7]].
        apply dbind_pos in H6 as [?[??]].
        destruct (decide (f=f')) as [|K].
        - subst.
          eapply IHn; naive_solver.
        - apply full_info_reachable_prefix in H, H2.
          destruct H2, H. simplify_eq.
          intros [??]. 
          eapply fi_osch_valid in Heqn1, Heqn2; [|done..].
          simplify_eq.
          exfalso.
          apply K. f_equal.
          rewrite -!app_assoc in H.
          simplify_eq. rewrite /cfg_to_cfg'. f_equal. f_equal. by f_equal.
      }
      erewrite fi_osch_consistent in H2; last done.
      apply dret_pos in H2, H4.
      by simplify_eq.
  Qed.
      
  
  Lemma is_frontier_prefix_unique initial_l l l' osch:
    is_frontier l initial_l osch -> is_frontier l' initial_l osch -> prefix l l' -> l = l'.
  Proof.
    rewrite /is_frontier.
    intros (?&?&H1) (?&?&H2).
    apply osch_lim_exec_pos in H1 as [n H1].
    apply osch_lim_exec_pos in H2 as [m H2].
    apply Rlt_gt in H1, H2.
    destruct (decide (n<=m)%nat).
    - eapply (is_frontier_n_prefix_unique m); last first. 
      { rewrite /is_frontier_n. eexists _, _. apply H2. }
      rewrite /is_frontier_n. eexists _, _.
      eapply Rge_gt_trans; last apply H1.
      apply Rle_ge.
      by apply osch_exec_mono'. 
    - eapply (is_frontier_n_prefix_unique n).
      { rewrite /is_frontier_n. eexists _, _. apply H1. }
      rewrite /is_frontier_n. eexists _, _.
      eapply Rge_gt_trans; last apply H2.
      apply Rle_ge.
      apply osch_exec_mono'. lia.
  Qed.

  (** Do nothing oscheduler *)

  Program Definition full_info_inhabitant: full_info_oscheduler :=
     {|
      fi_osch :={| oscheduler_f := λ _, None |}
      |}.
  Next Obligation.
    intros ?????. by simpl.
  Qed.
  Next Obligation.
    naive_solver.
  Qed.
  Next Obligation.
    naive_solver.
  Qed.

  Lemma full_info_inhabitant_lim_exec x:
    osch_lim_exec full_info_inhabitant x = dret x.
  Proof.
    by rewrite osch_lim_exec_None.
  Qed.

  (** Append a prefix list to every state *)
  Program Definition full_info_lift_osch prel (osch: full_info_oscheduler) : full_info_oscheduler :=
    {|
      fi_osch := {| oscheduler_f := λ '(l, ρ),
                                      match decide (∃ sufl, l=prel++sufl) with
                                      | left pro =>
                                          (dmap (λ '(l_res, j), (prel++l_res, j))) <$> (osch (epsilon pro, ρ)) 
                                      | _ => None
                                      end
                 |}
    |}.
  Next Obligation. done. Qed.
  Next Obligation.
    simpl. intros ?? ?[? [??]][?[??]]??. simpl in *. simplify_eq.
    case_match; last done.
    f_equal.
    by apply fi_osch_tape_oblivious.
  Qed.
  Next Obligation.
    simpl.
    intros ???????.
    case_match; last done.
    pose proof epsilon_correct _ e as Hrewrite.
    simpl in *.
    intros H' Hpos.
    apply fmap_Some_1 in H' as [?[H0 ?]]. subst.
    apply dmap_pos in Hpos as [[??][??]]. simplify_eq.
    eapply fi_osch_valid in H0; last done.
    subst. rewrite app_assoc. f_equal. by symmetry.
  Qed.
  Next Obligation.
    simpl.
    intros ????. case_match; last done.
    pose proof epsilon_correct _ e as He.
    simpl in *.
    intros Hnone.
    apply fmap_None in Hnone.
    intros.
    by eapply fi_osch_consistent in Hnone as ->.
  Qed.

  Lemma full_info_lift_osch_unfold prel osch l ρ:
    full_info_lift_osch prel osch (prel ++ l, ρ) =
    dmap (λ '(l', ρ'), (prel ++ l', ρ')) <$> (osch (l, ρ)).
  Proof.
    rewrite /full_info_lift_osch.
    simpl.
    case_match; last (exfalso; naive_solver).
    pose proof epsilon_correct _ e as H1.
    simpl in *.
    simplify_eq. rewrite -H1.
    apply option_fmap_ext.
    intros. rewrite /dmap. apply dbind_ext_right.
    by intros [??].
  Qed.
    
  
  Lemma full_info_lift_osch_exec prel osch n l ρ:
    osch_exec (full_info_lift_osch prel osch) n (prel++l, ρ) =
    dmap (λ '(l', ρ'), (prel++l', ρ')) (osch_exec osch n (l, ρ)).
  Proof.
    revert l ρ.
    induction n; intros l ρ.
    {
      rewrite /osch_exec/full_info_lift_osch/=.
      repeat case_match.
      - by rewrite dmap_dzero.
      - pose proof epsilon_correct _ e. simpl in *.
        simplify_eq.
        apply fmap_Some in H as [?[??]].
        exfalso. subst. rewrite H2 in H1. rewrite H in H1. done.
      - by rewrite dmap_dzero.
      - done.
      - rewrite fmap_None in H.
        pose proof epsilon_correct _ e. simpl in *. simplify_eq.
        rewrite H2 in H1. rewrite H1 in H. done.
      - by rewrite dmap_dret.
      - exfalso. naive_solver.
      - exfalso. naive_solver.
    }
    rewrite !osch_exec_Sn.
    rewrite dmap_dbind.
    rewrite /osch_step_or_none.
    case_match eqn:Heqn.
    - rewrite /full_info_lift_osch /= in Heqn.
      case_match; last done.
      pose proof epsilon_correct _ e as H0.
      simpl in *. simplify_eq. apply fmap_Some in Heqn as [?[H1 ->]].
      rewrite <-H0 in H1.
      rewrite H1/=.
      rewrite /osch_step/=.
      case_match eqn :Heqn1.
      + case_match; last done.
        apply fmap_Some in Heqn1 as [?[H3 ->]].
        pose proof epsilon_correct _ e0 as H'.
        simpl in *.
        simplify_eq.
        rewrite -H' in H3.
        rewrite H3.
        rewrite {1}/dmap -!dbind_assoc.
        apply dbind_ext_right.
        intros [??].
        rewrite dret_id_left. rewrite -!dbind_assoc.
        apply dbind_ext_right.
        intros. rewrite !dret_id_left.
        by rewrite -IHn.
      + rewrite dbind_dzero.
        case_match; last done.
        apply fmap_None in Heqn1.
        pose proof epsilon_correct _ e0 as H'.
        simpl in *. simplify_eq. rewrite -H' in Heqn1. rewrite Heqn1 in H1. done.
    - rewrite /full_info_lift_osch/= in Heqn.
      rewrite dret_id_left.
      erewrite IHn.
      case_match.
      + apply fmap_None in Heqn.
        pose proof epsilon_correct _ e. simpl in *. simplify_eq.
        rewrite -H0 in Heqn. rewrite Heqn. by rewrite dret_id_left.
      + exfalso. naive_solver.
  Qed.

  Lemma full_info_lift_osch_lim_exec prel osch l ρ:
    osch_lim_exec (full_info_lift_osch prel osch) (prel++l, ρ) =
    dmap (λ '(l', ρ'), (prel++l', ρ')) (osch_lim_exec osch (l, ρ)).
  Proof.
    apply distr_ext.
    intros. 
    apply Rle_antisym.
    - apply osch_lim_exec_leq.
      intros.
      rewrite full_info_lift_osch_exec.
      rewrite /dmap/dbind/dbind_pmf{1 4}/pmf.
      apply SeriesC_le; last (apply pmf_ex_seriesC_mult_fn; naive_solver).
      intros. split; first real_solver.
      apply Rmult_le_compat; try done.
      apply osch_lim_exec_is_sup.
    - apply osch_lim_exec_dmap_le.
      intros n. etrans; last apply (osch_lim_exec_is_sup _ n).
      by rewrite full_info_lift_osch_exec.
  Qed.
  (** TODO: lemmas about full_info_lift_osch *)
    
  
  Definition full_info_cons_distr (μ : distr nat) (l:full_info_state) (ρ:cfg) : distr (full_info_state * nat) :=
    dmap (λ n, (l++[(cfg_to_cfg' ρ, n)], n))%nat μ.

  Lemma full_info_cons_distr_tape_oblivious μ l ρ1 ρ2:
    cfg_to_cfg' ρ1 = cfg_to_cfg' ρ2 ->
    full_info_cons_distr μ l ρ1 = full_info_cons_distr μ l ρ2.
  Proof.
    rewrite /full_info_cons_distr.
    by intros ->.
  Qed.

  Lemma full_info_cons_distr_valid μ l ρ l' j:
    (full_info_cons_distr μ l ρ (l', j) > 0)%R → l' = l ++ [(cfg_to_cfg' ρ, j)].
  Proof.
    rewrite /full_info_cons_distr.
    intros Hpos.
    apply dmap_pos in Hpos as [?[??]].
    by simplify_eq.
  Qed.
  
  (** This is a way of building a scheduler that conss one step into many different states 
     each of which is a different kind of scheduler
   *)
  Program Definition full_info_cons_osch (μ : distr nat) (f: nat -> full_info_oscheduler) :=
    {|
      fi_osch := {| oscheduler_f := λ '(l, ρ),
                                      match decide (∃ hd, ∃ tl, l=hd::tl) with
                                      | left pro =>
                                          let hd:=(epsilon pro) in
                                          (full_info_lift_osch [hd] (f hd.2)) (l, ρ)
                                      | _ => Some (full_info_cons_distr μ [] ρ)
                                      end
                 |}
    |}.
  Next Obligation.
    done.
  Qed.
  Next Obligation.
    simpl.
    intros ???[??][??]??. simpl in *. simplify_eq.
    case_match.
    - simpl in *.
      case_match; last naive_solver.
      f_equal.
      by apply fi_osch_tape_oblivious.
    - f_equal. apply full_info_cons_distr_tape_oblivious.
      rewrite /cfg_to_cfg'. by f_equal.
  Qed.
  Next Obligation.
    simpl.
    intros ???????.
    case_match.
    - case_match; last done.
      intros Hsome.
      eapply fmap_Some_1 in Hsome as [?[H1 ->]].
      intros Hpos.
      apply dmap_pos in Hpos as [[??][? ?]].
      simplify_eq.
      eapply fi_osch_valid in H1; last done.
      rewrite H1.
      pose proof epsilon_correct _ e as [??].
      pose proof epsilon_correct _ e0 as H4.
      simpl in *.
      simplify_eq.
      rewrite app_comm_cons. by f_equal.
    - intros. simplify_eq. assert (l=[]) as ->.
      + destruct l; first done. exfalso. naive_solver.
      + by eapply full_info_cons_distr_valid.
  Qed.
  Next Obligation.
    simpl. intros ???[??].
    case_match; last done.
    case_match; last done.
    rewrite fmap_None.
    intros H'[??].
    rewrite fmap_None.
    by eapply fi_osch_consistent.
  Qed.

  (** TODO: lemmas about full_info_cons_osch *)

  Lemma full_info_cons_osch_unfold μ f x a l ρ:
    full_info_cons_osch μ f ([(x, a)] ++ l, ρ) =
    (full_info_lift_osch [(x, a)] (f a)) ([(x, a)] ++l, ρ).
  Proof.
    Local Opaque full_info_lift_osch.
    rewrite /full_info_cons_osch/=.
    case_match; last (exfalso; naive_solver).
    pose proof epsilon_correct _ e as [??].
    simplify_eq. destruct (epsilon e).
    by simplify_eq.
  Qed.
    
  Lemma full_info_cons_osch_exec_0 μ f ρ:
    osch_exec (full_info_cons_osch μ f) 0 ([], ρ) =
    dzero.
  Proof.
    rewrite /osch_exec.
    rewrite /full_info_cons_osch/=.
    case_match; first done.
    case_match; (exfalso; naive_solver).
  Qed.

  Lemma full_info_cons_osch_exec_n μ f ρ a x n l:
    osch_exec (full_info_cons_osch μ f) n ([(x, a)]++l, ρ) =
    dmap (λ '(l', ρ'), ([(x, a)]++l', ρ')) (osch_exec (f a) n (l, ρ)).
  Proof.
    revert ρ l.
    induction n; intros ρ l.
    - destruct ((f a) (l, ρ)) eqn:Heqn.
      + rewrite !osch_exec_0.
        * by rewrite dmap_dzero.
        * done.
        * rewrite full_info_cons_osch_unfold.
          rewrite full_info_lift_osch_unfold.
          rewrite Heqn. simpl. naive_solver. 
      + rewrite !osch_exec_is_none.
        * by rewrite dmap_dret.
        * done.
        * rewrite full_info_cons_osch_unfold.
          rewrite full_info_lift_osch_unfold.
          rewrite Heqn. simpl. naive_solver.  
    - rewrite !osch_exec_Sn.
      rewrite dmap_dbind.
      rewrite /osch_step_or_none.
      rewrite full_info_cons_osch_unfold.
      rewrite full_info_lift_osch_unfold.
      case_match eqn:H.
      + apply fmap_Some in H as [?[??]].
        simplify_eq. rewrite H.
        rewrite /osch_step.
        rewrite full_info_cons_osch_unfold full_info_lift_osch_unfold.
        rewrite !H.
        simpl.
        rewrite /dmap.
        rewrite -(dbind_assoc _ (osch_exec (full_info_cons_osch μ f) n)).
        rewrite -!dbind_assoc.
        apply dbind_ext_right.
        intros [??]. rewrite dret_id_left.
        rewrite -!dbind_assoc.
        apply dbind_ext_right.
        intros. rewrite !dret_id_left. rewrite IHn.
        by rewrite /dmap.
      + apply fmap_None in H. rewrite H.
        rewrite !dret_id_left. by erewrite IHn.
  Qed.
    
  Lemma full_info_cons_osch_exec_Sn μ f n ρ:
    osch_exec (full_info_cons_osch μ f) (S n) ([], ρ) =
    μ ≫= (λ x, step' x ρ ≫= (λ ρ', osch_exec (full_info_lift_osch [(cfg_to_cfg' ρ, x)] (f x)) n ([(cfg_to_cfg' ρ, x)], ρ'))) .
  Proof.
    rewrite osch_exec_Sn.
    rewrite /osch_step_or_none.
    case_match eqn:Heqn; last first.
    { rewrite /full_info_cons_osch in Heqn.
      simpl in *.
      case_match; naive_solver.
    }
    rewrite /osch_step. rewrite Heqn.
    rewrite /full_info_cons_osch in Heqn.
    simpl in Heqn. case_match; first naive_solver.
    simplify_eq. subst.
    (* rewrite /full_info_cons_distr. *)
    rewrite {1}/dmap -(dbind_assoc _ (osch_exec (full_info_cons_osch μ f) n)).
    rewrite -dbind_assoc.
    apply dbind_ext_right.
    intros.  rewrite dret_id_left.
    rewrite -!dbind_assoc.
    apply dbind_ext_right.
    intros. rewrite dret_id_left.
    rewrite app_nil_l.
    rewrite full_info_cons_osch_exec_n.
    by rewrite full_info_lift_osch_exec.
  Qed.

  Lemma full_info_cons_osch_lim_exec μ f ρ:
    osch_lim_exec (full_info_cons_osch μ f) ([], ρ) =
    μ ≫= (λ x, step' x ρ ≫= (λ ρ', osch_lim_exec (full_info_lift_osch [(cfg_to_cfg' ρ, x)] (f x)) ([(cfg_to_cfg' ρ, x)], ρ'))) .
  Proof.
    apply distr_ext.
    intros.
    apply Rle_antisym.
    - apply osch_lim_exec_leq.
      intros [].
      + rewrite full_info_cons_osch_exec_0. rewrite dzero_0. done.
      + rewrite full_info_cons_osch_exec_Sn.
        rewrite {1}/dbind{1}/dbind_pmf{1}/pmf.
        rewrite {2}/dbind{1}/dbind_pmf{3}/pmf.
        apply SeriesC_le; last first.
        { apply pmf_ex_seriesC_mult_fn. naive_solver. }
        intros. split; first real_solver.
        apply Rmult_le_compat; try done.
        rewrite /dbind/dbind_pmf{1 4}/pmf.
        apply SeriesC_le; last first.
        { apply pmf_ex_seriesC_mult_fn. naive_solver. }
        intros. split; first real_solver.
        apply Rmult_le_compat; try done.
        apply osch_lim_exec_is_sup.
    - rewrite {1 2}/dbind{1 2}/dbind_pmf{1 3}/pmf.
      setoid_rewrite <- SeriesC_scal_l.
      setoid_rewrite osch_lim_exec_unfold.
      assert (SeriesC(λ a0 : nat, SeriesC  (λ x , μ a0 *
                                                  (step' a0 ρ x *
                                                     Sup_seq
                                                       (λ n : nat,
                                                          osch_exec (full_info_lift_osch [(cfg_to_cfg' ρ, a0)] (f a0)) n
                                                            ([(cfg_to_cfg' ρ, a0)], x) a))))=
              Sup_seq (λ n : nat, SeriesC
                                  (λ a0 : nat,
                                     SeriesC
                                       (λ x : mdpstate (con_lang_mdp con_prob_lang),
                                          μ a0 *
                                            (step' a0 ρ x *
                                               osch_exec (full_info_lift_osch [(cfg_to_cfg' ρ, a0)] (f a0)) n
                                                 ([(cfg_to_cfg' ρ, a0)], x) a))))
             ) as ->; last first.
      { apply Rbar_le_fin.
        - apply Rbar_0_le_to_Rle. apply Sup_seq_minor_le with 0%nat. apply pmf_pos.
        - apply upper_bound_ge_sup.
          intros n.
          rewrite rbar_finite_real_eq; last apply is_finite_Sup_seq_osch_exec.
          etrans; last apply (sup_is_upper_bound _ (S n)).
          Local Opaque osch_exec full_info_cons_osch. simpl.
          rewrite full_info_cons_osch_exec_Sn.
          Local Transparent osch_exec full_info_cons_osch.
          rewrite {1}/dbind{1}/dbind_pmf{4}/pmf.
          right.
          apply SeriesC_ext.
          intros. rewrite SeriesC_scal_l.
          f_equal.
      }
      erewrite <-SeriesC_Sup_seq_swap.
      + apply SeriesC_ext.
        intros.
        erewrite <-SeriesC_Sup_seq_swap.
        * apply SeriesC_ext. intros.
          destruct (pmf_pos μ n) as [|<-]; last first.
          { trans 0; first lra.
            erewrite Sup_seq_ext; first by erewrite sup_seq_const.
            simpl. intros. rewrite Rmult_0_l. done. 
          }
          destruct (pmf_pos (step' n ρ) n0) as [|<-]; last first.
          { trans 0; first lra.
            erewrite Sup_seq_ext; first by erewrite sup_seq_const.
            simpl. intros. rewrite Rmult_0_l. rewrite Rmult_0_r. done.  }
          rewrite -Rmult_assoc -Sup_seq_scal_l'; last first.
          { apply is_finite_Sup_seq_osch_exec. }
          { real_solver. }
          f_equal. 
          apply Sup_seq_ext. intros. rewrite Rmult_assoc. done. 
        * intros. real_solver.
        * intros. apply Rmult_le_compat; try done; try real_solver.
          apply Rmult_le_compat; try done.
          apply osch_exec_mono.
        * intros. exists (1*(1*1)).
          intros. apply Rmult_le_compat; try done; real_solver.
        * intros. apply SeriesC_correct.
          apply ex_seriesC_scal_l.
          apply pmf_ex_seriesC_mult_fn. naive_solver.
        * simpl. instantiate (1:=μ n*1).
          intros.
          rewrite SeriesC_scal_l.
          apply Rmult_le_compat; try done.
          -- apply SeriesC_ge_0'. intros. real_solver.
          -- trans (SeriesC (step' n ρ )); last done.
             apply SeriesC_le; last done.
             intros. split; first real_solver.
             rewrite <-Rmult_1_r .
             by apply Rmult_le_compat.
      + intros.
        apply SeriesC_ge_0'.
        intros. real_solver.
      + intros. apply SeriesC_le; last (apply ex_seriesC_scal_l; apply pmf_ex_seriesC_mult_fn; naive_solver).
        intros; split; first real_solver.
        apply Rmult_le_compat; try done; first real_solver.
        apply Rmult_le_compat; try done.
        apply osch_exec_mono.
      + intros. exists (μ a0 * 1).
        intros. rewrite SeriesC_scal_l.
        apply Rmult_le_compat; try done.
        * apply SeriesC_ge_0'; intros; real_solver.
        * trans (SeriesC (step' a0 ρ )); last done.
          apply SeriesC_le; last done.
          intros. split; first real_solver.
          rewrite <-Rmult_1_r .
          apply Rmult_le_compat; try done.
      + intros n.
        apply SeriesC_correct.
        setoid_rewrite SeriesC_scal_l.
        apply pmf_ex_seriesC_mult_fn.
        exists 1.
        intros. split.
        * apply SeriesC_ge_0'; real_solver.
        * trans (SeriesC (step' a0 ρ )); last done.
          apply SeriesC_le; last done.
          intros. split; first real_solver.
          rewrite <-Rmult_1_r .
          apply Rmult_le_compat; try done.
      + simpl. instantiate (1:=1).
        intros.
        setoid_rewrite SeriesC_scal_l.
        trans (SeriesC μ); last done. 
        apply SeriesC_le; last done.
        intros.
        split; first apply Rmult_le_pos; try done.
        * apply SeriesC_ge_0'. real_solver.
        * rewrite <-Rmult_1_r. apply Rmult_le_compat; try done.
          -- apply SeriesC_ge_0'. real_solver.
          -- trans (SeriesC (step' n0 ρ)); last done.
             apply SeriesC_le; last done.
             intros; split; first real_solver.
             rewrite <-Rmult_1_r. apply Rmult_le_compat; try done.
  Qed.
      


  (** This oscheduler performs a stutter step *)
  Definition full_info_stutter_osch (ρ:cfg) (osch:full_info_oscheduler) :=
    full_info_cons_osch (dret (length ρ.1)) (λ _, osch).

  Lemma full_info_stutter_osch_lim_exec ρ osch :
    osch_lim_exec (full_info_stutter_osch ρ osch) ([], ρ) =
    dmap (λ '(l, ρ'), (([(cfg_to_cfg' ρ, (length ρ.1))]++l), ρ')) (osch_lim_exec osch ([], ρ)).
  Proof.
    rewrite /full_info_stutter_osch.
    rewrite full_info_cons_osch_lim_exec.
    rewrite dret_id_left.
    rewrite /step'.
    destruct ρ.
    case_match eqn:H.
    { apply lookup_lt_Some in H.
      simpl in *. lia.
    }
    rewrite dret_id_left.
    by rewrite full_info_lift_osch_lim_exec.
  Qed.

  (** This is a way of building a scheduler by appending schedulers at the frontier of another
   *)
  Program Definition full_info_append_osch
    (osch:full_info_oscheduler) (f: full_info_state -> full_info_oscheduler) :=
    {|
      fi_osch := {| oscheduler_f := λ '(l, ρ),
                                      match
                                        decide (∃ prel, prefix prel l /\ is_frontier prel [] osch) with
                                      | left pro =>
                                          let prel:=(epsilon pro) in
                                          (full_info_lift_osch prel (f prel)) (l, ρ)
                                      | _ => osch (l, ρ)
                                      end
                 |}
    |}.
  Next Obligation.
    done.
  Qed.
  Next Obligation.
    simpl. intros ???????.
    simpl. case_match; by apply fi_osch_tape_oblivious.
  Qed.
  Next Obligation.
    simpl.
    intros ???????. case_match; apply fi_osch_valid.
  Qed.
  Next Obligation.
    simpl. intros ????. case_match; apply fi_osch_consistent.
  Qed.

  Lemma is_frontier_prefix_lemma prel prel' osch l:
    prefix prel l -> is_frontier prel [] osch -> prefix prel' l -> is_frontier prel' [] osch -> prel = prel'.
  Proof.
    intros.
    epose proof prefix_weak_total _ _ l _ _  as [|].
    - by eapply is_frontier_prefix_unique.
    - symmetry; by eapply is_frontier_prefix_unique.
      Unshelve.
      all: done.
  Qed.
  
  Lemma full_info_append_osch_prefix prel osch f l ρ:
    is_frontier prel [] osch ->
    full_info_append_osch osch f (prel ++ l, ρ) = full_info_lift_osch prel (f prel) (prel ++ l, ρ).
  Proof.
    rewrite /full_info_append_osch.
    intros. simpl. case_match; last first.
    { exfalso. apply n. eexists _; split; last done.
      by eexists _.
    }
    pose proof epsilon_correct _ e as H'. simpl in *.
    assert (epsilon e = prel) as Hrewrite.
    { eapply is_frontier_prefix_lemma; [apply H'|naive_solver|by eexists _|done]. }
    by rewrite Hrewrite in H' *.
  Qed.
    
  Lemma full_info_append_osch_exec_prefix prel l osch f n ρ:
    is_frontier prel [] osch ->
    osch_exec (full_info_append_osch osch f) n (prel++l, ρ) =
    osch_exec (full_info_lift_osch prel (f prel)) n (prel++l, ρ).
  Proof.
    revert l ρ.
    induction n; intros l ρ Hfront.
    - simpl. case_match eqn :H1; case_match eqn :H2.
      + pose proof epsilon_correct _ e as H. simpl in *.
        assert (epsilon e = prel) as Hrewrite.
        { eapply is_frontier_prefix_lemma; [apply H|naive_solver|by eexists _|done]. }
        rewrite Hrewrite in H1 *.
        by rewrite H1.
      + exfalso.
        apply n. exists prel. split; last done.
        by eexists _.
      + pose proof epsilon_correct _ e. simpl in *.
        assert (epsilon e = prel) as Hrewrite.
        { eapply is_frontier_prefix_lemma; [apply H|naive_solver|by eexists _|done]. }
        rewrite Hrewrite in H1 *. by rewrite H1.
      + exfalso.
        apply n.
        exists prel. split; last done. by eexists _.
    - rewrite !osch_exec_Sn.
      rewrite /osch_step_or_none.
      rewrite full_info_append_osch_prefix; last done.
      case_match.
      + rewrite /osch_step. rewrite full_info_append_osch_prefix; last done.
        case_match; last by rewrite !dbind_dzero.
        simplify_eq. 
  Admitted.

    
   
End full_info.
