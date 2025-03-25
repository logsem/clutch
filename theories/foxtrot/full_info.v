From Coq Require Import Reals Psatz.
From clutch.prob Require Import distribution couplings_app oscheduler.
From clutch.con_prob_lang Require Import lang.
Set Default Proof Using "Type*".

Section full_info.
  Definition full_info_state : Type := list (cfg * nat).

  Record full_info_oscheduler :=
    MkFullInfoOsch {
        fi_osch :> oscheduler (con_lang_mdp con_prob_lang) (full_info_state);
        fi_osch_tape_oblivious :: oTapeOblivious _ fi_osch;
        fi_osch_valid:
        ∀ l ρ j l' μ, fi_osch (l, ρ) = Some μ -> (μ (l', j) > 0)%R ->
                      l' = l++[(ρ, j)];
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
      rewrite /osch_step_or_final_or_none in H2.
      repeat case_match.
      + apply dret_pos in H2. naive_solver.
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

  Lemma osch_lim_exec_full_info_inhabitant x:
    osch_lim_exec full_info_inhabitant x = dret x.
  Proof.
    by rewrite osch_lim_exec_None.
  Qed.

  Program Definition full_info_append_oscheduler prel (osch: full_info_oscheduler) : full_info_oscheduler :=
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
    
  
  Definition full_info_stutter_distr (μ : distr nat) (l:list (cfg * nat)) (ρ:cfg) : distr (full_info_state * nat) :=
    dmap (λ n, (l++[(ρ, n)], n))%nat μ.
  
  (* This is a way of building a scheduler that stutters one step into many different states 
     each of which is a different kind of scheduler
   *)
  (* Program Definition full_info_stutter_osch (μ : distr nat) (f: nat -> full_info_scheduler) *)
  
  (* TODO add more lemmas *)
  
End full_info.
