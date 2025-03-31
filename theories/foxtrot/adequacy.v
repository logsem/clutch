From Coquelicot Require Import Lub Rbar Lim_seq.
From iris.proofmode Require Import base proofmode.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.base_logic Require Import error_credits.
From clutch.con_prob_lang Require Import erasure notation.
From clutch.foxtrot Require Import weakestpre primitive_laws oscheduler full_info.
From clutch.prob Require Import distribution couplings_app.
Import uPred.

Section iris_lemmas.
  Context `{!foxtrotGS Σ}.
  Lemma step_fupd_fupdN_S n (P : iProp Σ) :  ((|={∅}▷=>^(S n) P) ⊣⊢ (|={∅}=> |={∅}▷=>^(S n) P))%I.
  Proof. iSplit; iIntros; simpl; iApply fupd_idemp; iFrame. Qed.

  Lemma fupdN_S n (P : iProp Σ) :  ((|={∅}▷=>^(S n) P) ⊣⊢ (|={∅}▷=> |={∅}▷=>^(n) P))%I.
  Proof. done. Qed.

  Lemma fupd_later_mono n (P Q : iProp Σ) :
    (P ⊢ Q) ->
    (|={⊤,∅}=> |={∅}▷=> |={∅}▷=>^n P) -∗
    (|={⊤,∅}=> |={∅}▷=> |={∅}▷=>^n Q).
  Proof.
    iIntros. 
    by iApply (step_fupdN_mono).
  Qed.

End iris_lemmas.

Section adequacy.
  Context `{!foxtrotGS Σ}.

  Lemma wp_adequacy_val_fupd `{Countable sch_int_σ} sch ζ `{!TapeOblivious sch_int_σ sch} σ (ε:nonnegreal) e es ρ n v ϕ:
    ∀ ε', ε'>0 -> 
    to_val e = Some v ->
    state_interp σ ∗ err_interp ε ∗ spec_interp ρ ∗
    WP e {{ v, ∃ v' : val, 0 ⤇ Val v' ∗ ⌜ϕ v v'⌝ }} ⊢
    |={⊤,∅}=>  ⌜∃ (osch:full_info_oscheduler),
                   ARcoupl (sch_exec sch n (ζ, (e::es, σ))) (osch_lim_exec osch ([], ρ))
                     (λ v '(l, ρ), ∃ v', ρ.1!!0%nat = Some (Val v') /\ ϕ v v') (ε + ε') ⌝.
  Proof.
    iIntros (ε' Hε' Hval) "(?&?&?&Hwp)".
    rewrite wp_unfold/wp_pre.
    iMod ("Hwp" with "[$]") as "H".
    simpl; rewrite Hval.
    iRevert (ε' Hε').
    iRevert (σ ρ ε) "H".
    iApply spec_coupl_ind.
    iModIntro.
    iIntros (σ ρ ε) "[%|[>(?&?&?&(%&?&%))|[H|H]]]"; iIntros (ε' Hε').
    - iPureIntro. intros.
      exists full_info_inhabitant.
      apply ARcoupl_1; lra.
    - iApply fupd_mask_intro; first done.
      iDestruct (spec_auth_prog_agree with "[$][$]") as "%".
      iIntros. iPureIntro.
      intros. exists full_info_inhabitant.
      erewrite sch_exec_is_final; last done.
      rewrite full_info_inhabitant_lim_exec.
      apply ARcoupl_dret; first apply Rplus_le_le_0_compat.
      { done. }
      { lra. }
      destruct ρ. naive_solver.
    - unshelve eset (ε_new := mknonnegreal (ε+ε'/2)%R _).
      { apply Rplus_le_le_0_compat; first apply cond_nonneg.
        apply Rcomplements.Rdiv_le_0_compat; lra. }
      simpl in *.
      iDestruct ("H" $! ε_new with "[]") as "[H _]".
      { rewrite /ε_new. simpl. iPureIntro.
        rewrite Rplus_comm. apply Rcomplements.Rlt_minus_l.
        rewrite Rminus_diag.
        apply Rcomplements.Rdiv_lt_0_compat; lra.
      }
      iDestruct ("H" $! (ε'/2) with "[]") as ">[%osch %Hcoupl]".
      { iPureIntro.
        apply Rlt_gt.
        apply Rcomplements.Rdiv_lt_0_compat; lra. }
      iPureIntro.
      exists osch.
      rewrite /ε_new/= in Hcoupl.
      rewrite Rplus_assoc in Hcoupl.
      by rewrite Rplus_half_diag in Hcoupl.
    - iDestruct "H" as "(%S&%μ&%osch&%ε1 & %X2 & %r &%Herasable&%&%&%Hcoupl&%Hinj&H)".
      apply sch_erasable_sch_erasable_val in Herasable. rewrite -Herasable.
      set (S' := (λ '(σ2, l, ρ'), S σ2 (l, ρ'))).
      eset (P:=(λ (p: sigT S') (fp:full_info_oscheduler),
                  let '(σ2, l,  ρ') := projT1 p in 
                     ⌜
                     ARcoupl (sch_exec sch n (ζ, (e :: es, σ2))) (osch_lim_exec fp ([], ρ'))
                       (λ (v0 : val) '(_, ρ0), ∃ v' : val, ρ0.1 !! 0%nat = Some (Val v') ∧ ϕ v0 v')
                       (X2 (l, ρ') + ε')⌝)%I : _-> _-> iProp Σ).
      iAssert (|={∅}=> ∀ p, ∃ fp, P p (fp))%I with "[H]" as "H".
      {
        rewrite /P.
        iApply fupd_plain_forall; [|done|].
        - intros x. apply exist_plain.
          intros.
          destruct  (projT1 x). case_match.
          apply pure_plain.
        - iIntros ([([??]&?&?)?]).
          iMod ("H" with "[//]") as "[H _]".
          iMod ("H" with "[//]") as "[%osch' %Hcoupl']".
          iExists osch'. done.
      }
      iMod "H".
      iDestruct (iris_choice with "[$]") as "[%f H]".
      pose (f' := λ x,
              match (decide (∃ Hx, (projT1 Hx).1.2 = x)) with
              | left pro => f (epsilon pro)
              | _ => full_info_inhabitant
              end     
           ).
      iExists (full_info_append_osch osch f').
      iApply (fupd_mono _ _ ⌜_⌝).
      { iPureIntro. intros K.
        replace (_+_)%R with ((ε+ε')+0) by (simpl; lra).
        eapply ARcoupl_eq_trans_r; last first.
        - apply ARcoupl_eq_0. intros. apply full_info_append_osch_lim_exec.
        - apply K.
        - done.
        - apply Rplus_le_le_0_compat; [apply cond_nonneg|lra].   
      }
      rewrite /P.
      iModIntro.
      iApply (pure_mono (∀ a, let
         '(σ2, l, ρ') := projT1 a in
          ARcoupl (sch_exec sch n (ζ, (e :: es, σ2))) (osch_lim_exec (f a) ([], ρ'))
             (λ (v0 : val) '(_, ρ0), ∃ v' : val, ρ0.1 !! 0%nat = Some (Val v') ∧ ϕ v0 v') 
             (X2 (l, ρ') + ε'))); last first.
      { iIntros (a).
        case_match eqn :Heqn. case_match.
        iDestruct ("H"$! a) as "H".
        by rewrite Heqn.
      }
      intros H'.
      eapply (ARcoupl_mon_grading _ _ _ (ε1 + (Expval (osch_lim_exec _ _) _ + ε'))).
      { rewrite -Rplus_assoc. apply Rplus_le_compat_r.
      done. }
      eapply ARcoupl_dbind_adv_rhs'; last first.
      + apply ARcoupl_pos_R. done.
      + Local Opaque osch_lim_exec full_info_lift_osch. simpl.
        intros ?[l ?] (H3&?&?).
        case_match eqn:Heqn; last first.
        { exfalso. apply n0. exists l; split; first done.
          rewrite /is_frontier. naive_solver.
        }
        pose proof epsilon_correct _ e0 as Hcorrect.
        simpl in *.
        assert (epsilon e0=l) as ->.
        { symmetry. eapply is_frontier_prefix_lemma.
          - done. 
          - rewrite /is_frontier. naive_solver.
          - naive_solver.
          - naive_solver.
        }
        epose proof (H' ((a, l, c); H3)) as H'.
        do 2 case_match. rewrite /f'.
        case_match; last first.
        { exfalso.
          apply n0.
          by exists ((a, l, c); H3).
        }
        assert (epsilon e1 =  ((a, l, c); H3)) as ->.
        { pose proof epsilon_correct _ e1 as H9.
          simpl in H9.
          destruct (epsilon e1) as [x y]. simpl in *. simplify_eq.
          eapply classic_proof_irrel.PIT.subsetT_eq_compat.
          rewrite /S' in y.
          do 2 case_match.
          simpl in *.
          simplify_eq.
          destruct (Hinj _ _ _ _ _ y H3). by simplify_eq.
        }
        rewrite -{3}(app_nil_r l).
        rewrite full_info_lift_osch_lim_exec.
        rewrite <-(dmap_id (sch_exec _ _ _)).
        simpl in *; simplify_eq.
        apply ARcoupl_map; last first.
        { eapply ARcoupl_mono; last apply H'; try done.
          - intros ? [??]. naive_solver.
          - instantiate (1 := λ _, _ + ε'). simpl. done.
        }
        simpl. apply Rplus_le_le_0_compat; last lra. apply cond_nonneg.
      + simpl. rewrite /Expval.
        setoid_rewrite (Rmult_plus_distr_l).
        rewrite SeriesC_plus; last first.
        { apply ex_seriesC_scal_r. done. }
        { apply pmf_ex_seriesC_mult_fn; naive_solver. }
        apply Rplus_le_compat; first done.
        rewrite SeriesC_scal_r.
        trans (1*ε'); last lra.
        apply Rmult_le_compat_r; first lra.
        done.
      + exists( r+ε').
        intros.
        split; first apply Rplus_le_le_0_compat; try done; try lra.
        apply Rplus_le_compat_r. done.
      + apply cond_nonneg.
  Qed.


  Lemma spec_coupl_erasure `{Countable sch_int_σ} sch ζ `{!TapeOblivious sch_int_σ sch} σ ρ ε Z ϕ n e es:
    ∀ ε', ε'>0 -> 
    spec_coupl σ ρ ε Z -∗
    (∀ σ2 ρ2 ε2, Z σ2 ρ2 ε2 ={∅}=∗ |={∅}▷=>^(n)∀ ε'', ⌜ε''>0⌝-∗ 
                                                 ⌜∃ (osch:full_info_oscheduler),
       ARcoupl (sch_exec sch n (ζ, (e::es, σ2))) (osch_lim_exec osch ([], ρ2))
         (λ v '(l, ρ), ∃ v', ρ.1!!0%nat = Some (Val v') /\ ϕ v v') (ε2 + ε'')⌝
    ) -∗
    |={∅}=> |={∅}▷=>^(n)
             ⌜∃ (osch:full_info_oscheduler),
       ARcoupl (sch_exec sch n (ζ, (e::es, σ))) (osch_lim_exec osch ([], ρ))
         (λ v '(l, ρ), ∃ v', ρ.1!!0%nat = Some (Val v') /\ ϕ v v') (ε + ε')⌝.
  Proof.
  Admitted.

  Lemma spec_coupl_erasure' `{Countable sch_int_σ} sch ζ `{!TapeOblivious sch_int_σ sch} σ ρ ε Z ϕ n e es e' num:
    ∀ ε', ε'>0 -> 
    ((e::es)!!num = Some e') ->
    to_val e = None ->
    to_val e' = None ->
    spec_coupl σ ρ ε Z -∗
    (∀ σ2 ρ2 ε2, Z σ2 ρ2 ε2 ={∅}=∗ |={∅}▷=>^(S n) ∀ ε'', ⌜ε''>0⌝-∗ 
                                                 ⌜∃ (osch:full_info_oscheduler),
       ARcoupl (prim_step e' σ2 ≫= λ '(e3, σ3, efs), sch_exec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3))) (osch_lim_exec osch ([], ρ2))
         (λ v '(l, ρ), ∃ v', ρ.1!!0%nat = Some (Val v') /\ ϕ v v') (ε2 + ε'')⌝
    ) -∗
    |={∅}=> |={∅}▷=>^(S n)
             ⌜∃ (osch:full_info_oscheduler),
       ARcoupl (prim_step e' σ ≫= λ '(e3, σ3, efs), sch_exec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3))) (osch_lim_exec osch ([], ρ))
         (λ v '(l, ρ), ∃ v', ρ.1!!0%nat = Some (Val v') /\ ϕ v v') (ε + ε')⌝.
  Proof.
  Admitted.

  Lemma prog_coupl_erasure `{Countable sch_int_σ} sch ζ `{!TapeOblivious sch_int_σ sch} σ ρ ε Z ϕ n e es e' num:
    ∀ ε', ε'>0 -> 
    ((e::es)!!num = Some e') ->
    to_val e = None ->
    to_val e' = None ->
    prog_coupl e' σ ρ ε Z -∗
    (∀ e2 σ2 efs ρ2 ε2, Z e2 σ2 efs ρ2 ε2 ={∅}=∗  |={∅}▷=>^(S n)∀ ε'', ⌜ε''>0⌝-∗
                                                 ⌜∃ (osch:full_info_oscheduler),
       ARcoupl (sch_exec sch n (ζ, (<[num:=e2]> (e :: es) ++ efs, σ2))) (osch_lim_exec osch ([], ρ2))
         (λ v '(l, ρ), ∃ v', ρ.1!!0%nat = Some (Val v') /\ ϕ v v') (ε2 + ε'')⌝
    ) -∗
    |={∅}=> |={∅}▷=>^(S n)
             ⌜∃ (osch:full_info_oscheduler),
       ARcoupl (prim_step e' σ ≫= λ '(e3, σ3, efs), sch_exec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3))) (osch_lim_exec osch ([], ρ))
         (λ v '(l, ρ), ∃ v', ρ.1!!0%nat = Some (Val v') /\ ϕ v v') (ε + ε')⌝.
  Proof.
  Admitted.
  
  Lemma wp_adequacy_step_fupdN `{Countable sch_int_σ} sch ζ `{!TapeOblivious sch_int_σ sch} σ σ' (ε:nonnegreal) e es es' ϕ n:
    ∀ ε', ε'>0 -> 
    state_interp σ ∗ err_interp ε ∗ spec_interp (es', σ') ∗
    WP e {{ v, ∃ v' : val, 0 ⤇ Val v' ∗ ⌜ϕ v v'⌝ }} ∗ ([∗ list] e' ∈ es, WP e' {{ _, True }})
    ⊢ |={⊤,∅}=> |={∅}▷=>^n
                 ⌜∃ (osch:full_info_oscheduler),
                   ARcoupl (sch_exec sch n (ζ, (e::es, σ))) (osch_lim_exec osch ([], (es', σ')))
                     (λ v '(l, ρ), ∃ v', ρ.1!!0%nat = Some (Val v') /\ ϕ v v') (ε + ε') ⌝.
  Proof.
    iInduction n as [|n] "IH" forall (ζ σ σ' ε e es es');
      iIntros (ε' Hε') "(Hσauth & Herrauth & Hspecauth & Hwp & Hwps)".
    {
      destruct (to_val e) eqn : Heqn.
      - apply of_to_val in Heqn as <-.
        iApply wp_adequacy_val_fupd; try done.
        iFrame.
      - iApply fupd_mask_intro; [set_solver|]. iIntros. simpl. iPureIntro.
        intros. exists full_info_inhabitant. rewrite Heqn.
        apply ARcoupl_dzero. apply Rplus_le_le_0_compat; [apply cond_nonneg|lra].   
    }
    rewrite sch_exec_Sn/sch_step_or_final/=.
    case_match eqn :Heqn.
    { iMod (wp_adequacy_val_fupd with "[$]") as "H"; [done..|].
      iModIntro. repeat iModIntro.
      rewrite dret_id_left.
      by iApply step_fupdN_intro. 
    }
    rewrite /sch_step. rewrite <-!dbind_assoc.
    iAssert (
        |={⊤,∅}=>
          |={∅}▷=>
            |={∅}▷=>^n
              ⌜∃ (f : _ -> full_info_oscheduler),
              ∀ ζ' ac, sch (ζ, (e::es, σ)) (ζ', ac) > 0 -> 
              ARcoupl
                   ((let '(sch_σ', mdp_a) := (ζ', ac) in
                     dmap (λ mdp_σ' : mdpstate (con_lang_mdp con_prob_lang), (sch_σ', mdp_σ'))
                       (step mdp_a (ζ, (e :: es, σ)).2))
                     ≫= λ b : sch_int_σ * con_language.cfg con_prob_lang, sch_exec sch n b)
                (osch_lim_exec (f (ζ', ac)) ([], (es', σ')))
                (λ (v : val) '(_, ρ), ∃ v' : val, ρ.1 !! 0%nat = Some (Val v') ∧ ϕ v v') 
                (ε + ε')⌝
      )%I with "[-]" as "H"; last first.
    { iApply fupd_later_mono; last done.
      iPureIntro.
      intros [f Hcoupl].
      exists (full_info_cons_osch (dmap (λ ac, (length es'+encode_nat ac)%nat) (sch (ζ, (e::es, σ))))
           (λ x, f (match decode_nat (x - length es')%nat
                    with |Some ac => ac
                    | None => (ζ, inhabitant)
                    end
           ))
        ).
      rewrite full_info_cons_osch_lim_exec/dmap -!dbind_assoc.
      replace (_+_) with (0+(ε+ε')); last (simpl; lra).
      eapply ARcoupl_dbind; [done|apply Rplus_le_le_0_compat; [apply cond_nonneg|lra]| |apply ARcoupl_pos_R, ARcoupl_eq].
      Local Opaque full_info_lift_osch step' step.
      simpl.
      intros [s ac][s' ac'](?&?&?). simplify_eq.
      rewrite dret_id_left.
      rewrite out_of_bounds_step'; last (simpl; lia).
      rewrite dret_id_left.
      replace (_+_-_)%nat with (encode_nat (s', ac')); last lia.
      rewrite decode_encode_nat.
      rewrite full_info_lift_osch_lim_exec.
      rewrite -(dmap_id ((_≫=_)≫=_)).
      eapply ARcoupl_map.
      { apply Rplus_le_le_0_compat; [apply cond_nonneg|lra]. }
      simpl.
      eapply ARcoupl_mono; last apply Hcoupl; try done.
      simpl. intros ? [??]. naive_solver.
    }
    set (S' := (λ '(ζ', ac), sch (ζ, (e::es, σ)) (ζ', ac) > 0)).
   eset (P:=(λ (p: sigT S') (fp:full_info_oscheduler),
               let '(ζ', ac) := projT1 p in ARcoupl
                   (dmap (λ mdp_σ' : mdpstate (con_lang_mdp con_prob_lang), (ζ', mdp_σ'))
                      (step ac (ζ, (e :: es, σ)).2)
                      ≫= λ b : sch_int_σ * con_language.cfg con_prob_lang, sch_exec sch n b)
                   (osch_lim_exec fp ([], (es', σ')))
                   (λ (v : val) '(_, ρ), ∃ v' : val, ρ.1 !! 0%nat = Some (Val v') ∧ ϕ v v') 
                   (ε + ε'))).
    iApply (fupd_later_mono _ (⌜∀ p, ∃ fp, P p (fp)⌝)%I).
    { rewrite pure_exist.
      iIntros "H".
      iAssert (∀ p, ∃ fp, ⌜P p (fp)⌝)%I with "[H]" as "H".
      { rewrite pure_forall.
        iIntros (p).
        iDestruct ("H" $! p) as "[%%]".
        iPureIntro.
        naive_solver.
      }
      iDestruct (iris_choice with "[$]") as "H".
      rewrite /P.
      iDestruct "H" as "(%f & H)".
      pose (f' := λ x,
              match (decide (∃ Hx, projT1 Hx = x)) with
              | left pro => f (epsilon pro)
              | _ => full_info_inhabitant
              end
           ).
      iExists f'.
      iIntros (ζ' ac Hpos).
      assert (S' (ζ', ac)) as HS'.
      { by rewrite /S'. }
      iDestruct ("H" $! ((ζ', ac); HS')) as "%Hcoupl".
      iPureIntro.
      simpl in *.
      rewrite /f'.
      case_match; last first.
      { exfalso. apply n0. by exists ((ζ',ac); HS'). }
      assert (epsilon e0=((ζ', ac); HS')) as ->; last done.
      pose proof epsilon_correct _ e0 as H9.
      simpl in H9.
      destruct (epsilon e0) as [x y]. simpl in *. simplify_eq.
      eapply classic_proof_irrel.PIT.subsetT_eq_compat.
      by rewrite /S' in y.
    }
    iApply fupd_mask_intro; first done.
    iIntros "Hclose". simpl.
    rewrite /P -fupdN_S.
    iIntros ([[ζ' td]HS]).
    rewrite step_fupd_fupdN_S.
    iMod "Hclose" as "_".
    destruct ((e::es)!!td) as [chosen_e|] eqn:Hlookup; last first.
    {     (* step a thread out of bounds*)
      Local Transparent step.
      rewrite /step/= Heqn Hlookup.
      rewrite dmap_dret dret_id_left'.
      iApply fupd_mask_intro; first done.
      iIntros "Hclose".
      do 2 iModIntro. iMod "Hclose" as "_".
      iApply "IH"; first done; iFrame.
    }
    rewrite {1}/step/= Heqn Hlookup.
    case_match eqn:Hcheckval.
    {
      (* step a thread thats a value *)
      rewrite dmap_dret dret_id_left'.
      iApply fupd_mask_intro; first done.
      iIntros "Hclose".
      do 2 iModIntro. iMod "Hclose" as "_".
      iApply "IH"; first done. iFrame.
    }
    rewrite dmap_comp/dmap-dbind_assoc.
    erewrite (distr_ext _ _); last first.
    { intros x. erewrite (dbind_ext_right _ _ (λ '(_,_,_), _)); last first.
      - intros [[??]?].
        by rewrite dret_id_left/=.
      - done.
    }
    destruct td as [|td].
    - (* step main thread*)
      rewrite wp_unfold/wp_pre. iSimpl in "Hwp". rewrite Heqn.
      iMod ("Hwp" with "[$]") as "H".
      iApply (spec_coupl_erasure' with "[$]"); [done..|]. 
      iIntros (???) "H".
      iIntros (ε'' Hε'').
      simpl in Hlookup; simplify_eq.
      iApply (prog_coupl_erasure with "[$]"); [done..|].
      iIntros (?????) "H".
      iModIntro. simpl. iModIntro. iNext.
      iIntros (ε''' Hε''').
      iApply (spec_coupl_erasure with "[$]"); [done..|].
      iIntros (?[??]?) "H".
      iIntros (ε'''' Hε'''').
      iMod "H" as "(?&?&?&?&H)".
      iMod ("IH" with "[][-]") as "H"; last first.
      { iModIntro. iApply (step_fupdN_mono with "[$]").
        iPureIntro.
        naive_solver.
      }
      { iFrame. }
      done.
    - simpl in Hlookup.
      apply elem_of_list_split_length in Hlookup as (l1 & l2 & -> & ->).
      iDestruct "Hwps" as "[Hl1 [Hwp' Hl2]]".
      rewrite (wp_unfold _ chosen_e)/wp_pre.
      iSimpl in "Hwp'".
      iMod ("Hwp'" with "[$]") as "Hlift".
      iApply (spec_coupl_erasure' with "[$]"); [done| |done|done|].
      { simpl.
        rewrite lookup_app_r//.
        by replace (_-_)%nat with 0%nat by lia. }
      rewrite Hcheckval.
      iIntros (???) "Hlift".
      iIntros (ε'' Hε'').
      iApply (prog_coupl_erasure with "[$]"); try done.
      { simpl. rewrite lookup_app_r//.
        by replace (_-_)%nat with 0%nat by lia. }
      iIntros (?????) "H".
      iModIntro. simpl. iModIntro. iNext.
      iIntros (ε''' Hε''').
      iApply (spec_coupl_erasure with "[$]"); [done..|].
      iIntros (?[??]?) "H".
      iIntros (ε'''' Hε'''').
      iMod "H" as "(?&?&?&?&?)".
      iMod ("IH" with "[][-]") as "H"; last first. 
      { iModIntro.
        iApply (step_fupdN_mono with "[$]").
        iPureIntro.
        naive_solver.
      }
      { iFrame.
        rewrite insert_app_r_alt; last lia.
        replace (_-_)%nat with 0%nat by lia.
        simpl. iFrame. 
      } done.
  Qed.
  

  
                                                           
End adequacy.


Lemma foxtrot_adequacy_full_info_intermediate_multi Σ `{foxtrotGpreS Σ} (ε:R) ϕ n e es es' :
  (0 <= ε)%R -> 
  (∀ `{foxtrotGS Σ}, ⊢ ↯ ε -∗
                     ([∗ map] n↦e ∈ (to_tpool es'), n ⤇ e) -∗
                     WP e {{ v, ∃ v', 0%nat ⤇ Val v' ∗ ⌜ ϕ v v' ⌝ }} ∗
                     [∗ list] e'∈ es, WP e' {{ _, True%I }}
  ) ->
  ∀ sch_int_σ `(Countable sch_int_σ) sch ζ `{!TapeOblivious sch_int_σ sch} σ σ' ε',
  ε'>0 ->
  ∃ (osch:full_info_oscheduler),
    ARcoupl (sch_exec sch n (ζ, (e::es, σ))) (osch_lim_exec osch ([], (es', σ')))
      (λ v '(l, ρ), ∃ v', ρ.1!!0%nat = Some (Val v') /\ ϕ v v') (ε + ε').
Proof.
  intros Heps Hwp.
  intros ??????????. 
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod (spec_ra_init es' σ') as (HspecGS) "(Hs & Hj & ?)".
  destruct (decide (ε < 1)) as [? | K%Rnot_lt_le].
  - set ε_nonneg := mknonnegreal _ Heps.
    iMod (ec_alloc ε_nonneg) as (?) "[HE He]"; [done|].
    set (HfoxtrotGS := HeapG Σ _ _ _ γH γT HspecGS _).
    iApply (wp_adequacy_step_fupdN _ _ _ _ ε_nonneg); first lra.
    iFrame.
    simpl.
    iApply (Hwp with "[He][-]").
    + iApply ec_eq; last done.
      done.
    + iFrame.
  - iApply fupd_mask_intro; [done|]; iIntros "_".
    iApply step_fupdN_intro; [done|]; iModIntro.
    iPureIntro. eexists full_info_inhabitant.
    apply ARcoupl_1.
    simpl in *. lra.
Qed.


Lemma foxtrot_adequacy_full_info_intermediate Σ `{foxtrotGpreS Σ} (ε:R) ϕ n e e' :
  (0 <= ε)%R -> 
  (∀ `{foxtrotGS Σ}, ⊢ ↯ ε -∗ 0%nat ⤇ e' -∗ WP e {{ v, ∃ v', 0%nat ⤇ Val v' ∗ ⌜ ϕ v v' ⌝ }}) ->
  ∀ sch_int_σ `(Countable sch_int_σ) sch ζ `{!TapeOblivious sch_int_σ sch} σ σ' ε',
  ε'>0 ->
  ∃ (osch:full_info_oscheduler),
    ARcoupl (sch_exec sch n (ζ, ([e], σ))) (osch_lim_exec osch ([], ([e'], σ')))
      (λ v '(l, ρ), ∃ v', ρ.1!!0%nat = Some (Val v') /\ ϕ v v') (ε + ε').
Proof.
  intros ? Hwp ??????????.
  by epose proof foxtrot_adequacy_full_info_intermediate_multi _ _ _ _ e [] [e'] _ _ _ _ _ _ _ _ _ _.
  Unshelve.
  all: try done.
  iIntros (?) "? H". simpl. rewrite /to_tpool.
  iSplit; last done.
  iApply (Hwp with "[$]").
  iApply big_sepM_lookup; last iFrame.
  simpl. apply lookup_insert.
Qed.

Lemma foxtrot_adequacy_intermediate Σ `{foxtrotGpreS Σ} (ε:R) ϕ n e e' :
  (0 <= ε)%R -> 
  (∀ `{foxtrotGS Σ}, ⊢ ↯ ε -∗ 0%nat ⤇ e' -∗ WP e {{ v, ∃ v', 0%nat ⤇ Val v' ∗ ⌜ ϕ v v' ⌝ }}) ->
  ∀ sch_int_σ `(Countable sch_int_σ) sch ζ `{!TapeOblivious sch_int_σ sch} σ σ' ε',
  ε'>0 ->
  ∃ `(Countable sch_int_σ') sch' ζ' `(!TapeOblivious sch_int_σ' sch'),
     ARcoupl (sch_exec sch n (ζ, ([e], σ))) (sch_lim_exec sch' (ζ', ([e'], σ'))) ϕ (ε + ε').
Proof.
  intros Heps Hwp.
  intros ??? sch ζ ? ? ? ε' ?.
  epose proof foxtrot_adequacy_full_info_intermediate _ _ _ _ _ _ Heps Hwp _ _ sch ζ _ _ _ _ as [osch Hcoupl].
  epose proof osch_to_sch osch as [sch'[Htape ?]].
  eexists _, _, _, sch', [], Htape.
  replace (_+_)%R with ((ε+ε')+0)%R; last lra.
  eapply (ARcoupl_eq_trans_r _ ((osch_lim_exec_val osch ([], ([e'], _))))) ; [lra|done| |by apply ARcoupl_eq_0].
  rewrite osch_lim_exec_exec_val.
  replace (_+_)%R with ((ε+ε')+0)%R; last lra.
  rewrite -(dret_id_right (sch_exec _ _ _)).
  eapply ARcoupl_dbind; try done.
  { real_solver. }
  simpl. intros ? [?[??]][? [Hsome ?]].
  simpl. simpl in *. rewrite Hsome.
  simpl. by apply ARcoupl_dret.
  Unshelve. done.
Qed.

Definition termination_prob cfg sch_int_σ ζ `{Countable sch_int_σ} sch `{!TapeOblivious sch_int_σ sch} :=
  SeriesC (sch_lim_exec sch (ζ, cfg)).

Definition termination_prob_type:Type :=
  (sigT (λ sch_int_σ:Type,
                    sch_int_σ * 
                    sigT (λ Heqdecision:EqDecision sch_int_σ,
                            sigT (λ Hcountable : @Countable sch_int_σ Heqdecision,
                                    sigT (λ sch : @scheduler (con_lang_mdp con_prob_lang) sch_int_σ Heqdecision Hcountable,
                                            
                                                    @TapeOblivious sch_int_σ Heqdecision Hcountable sch
                                            
                                      )
                              )
  )))%type.

Definition termination_n_prob n cfg sch_int_σ ζ `{Countable sch_int_σ} sch `{!TapeOblivious sch_int_σ sch} :=
  SeriesC (sch_exec sch n (ζ, cfg)).

Definition termination_prob' e σ (r:R):=
  ∃ (p:termination_prob_type), 
    @termination_prob
      ([e], σ)
      (projT1 p)
      ((projT2 p).1)
      (projT1 $ (projT2 p).2)
      (projT1 $ projT2 $ (projT2 p).2)
      (projT1 $ projT2 $ projT2 $ (projT2 p).2)
      (projT2 $ projT2 $ projT2 $ (projT2 p).2) = r.

Definition termination_n_prob' n e σ (r:R) :=
  ∃ (p:termination_prob_type), 
    @termination_n_prob
      n
      ([e], σ)
      (projT1 p)
      ((projT2 p).1)
      (projT1 $ (projT2 p).2)
      (projT1 $ projT2 $ (projT2 p).2)
      (projT1 $ projT2 $ projT2 $ (projT2 p).2)
      (projT2 $ projT2 $ projT2 $ (projT2 p).2) = r.

Definition lub_termination_prob e σ:= (Lub_Rbar (termination_prob' e σ)).
Definition lub_termination_n_prob n e σ:= (Lub_Rbar (termination_n_prob' n e σ)).

Lemma lub_termination_sup_seq_termination_n e σ:
  lub_termination_prob e σ = Sup_seq (λ n, lub_termination_n_prob n e σ).
Proof.
  apply Rbar_le_antisym; rewrite /lub_termination_prob.
  - pose proof Lub_Rbar_correct (termination_prob' e σ) as H.
    apply H.
    rewrite /termination_prob'.
    rewrite /is_ub_Rbar.
    rewrite /termination_prob.
    intros r [? <-].
    rewrite sch_lim_exec_Sup_seq.
    rewrite rbar_finite_real_eq; last first.
    { eapply (is_finite_bounded 0 1).
      - eapply Sup_seq_minor_le. apply pmf_SeriesC_ge_0.
      - apply upper_bound_ge_sup. intros. apply pmf_SeriesC.
    }
    apply Sup_seq_le.
    rewrite /lub_termination_n_prob.
    intros n.
    pose proof Lub_Rbar_correct (termination_n_prob' n e σ) as H'.
    apply H'.
    rewrite /termination_n_prob'.
    eexists _.
    by instantiate (1:= (_;(_,(_;(_;(_;_)))))).
  - apply upper_bound_ge_sup.
    intros n.
    rewrite /lub_termination_n_prob.
    pose proof Lub_Rbar_correct (termination_n_prob' n e σ) as H. apply H.
    rewrite /is_ub_Rbar.
    intros r [x <-].
    etrans.
    + instantiate (1:= termination_prob ([e], σ) _ _ _).
      rewrite /termination_n_prob/termination_prob.
      apply SeriesC_le; last done.
      intros; split; first done.
      rewrite sch_lim_exec_unfold.
      apply Coquelicot_ext.rbar_le_finite.
      { eapply (is_finite_bounded 0 1).
      - eapply Sup_seq_minor_le. apply pmf_pos.
      - apply upper_bound_ge_sup. intros. apply pmf_le_1. }
      etrans; last apply sup_is_upper_bound. done.
    + 
    pose proof Lub_Rbar_correct (termination_prob' e σ) as H'.
    rewrite /is_lub_Rbar in H'.
    rewrite /is_ub_Rbar in H'.
    destruct H' as [H' _].
    apply H'.
    rewrite /termination_prob'.
    by exists x.
         Unshelve.
         { exact 0%nat. }
         { simpl.
           by destruct x as (?&?&?&?&?&?). 
         }
         exact 0%nat.
Qed.

Lemma Rbar_le_lub R S : (∀ r, R r -> ∀ ε, (ε > 0)%R -> ∃ r', r-ε<= r' /\ S r') ->
                        Rbar_le (Lub_Rbar R) (Lub_Rbar S).
Proof.
  intros H.
  apply Lub_Rbar_correct.
  rewrite /is_ub_Rbar.
  intros r Hr.
  apply Rbar_le_plus_epsilon.
  intros eps Heps.
  replace eps with (- - eps) by lra.
  apply Rbar_le_opp.
  pose proof (H _ Hr eps Heps) as (r' & Hr' & Hs).
  trans r'.
  { simpl. lra. }
  by apply Lub_Rbar_correct.
Qed.

Lemma foxtrot_adequacy Σ `{foxtrotGpreS Σ} ϕ e e' σ σ' : 
  (∀ `{foxtrotGS Σ}, ⊢ 0%nat ⤇ e' -∗ WP e {{ v, ∃ v', 0%nat ⤇ Val v' ∗ ⌜ ϕ v v' ⌝ }}) ->
  Rbar_le (lub_termination_prob e σ) (lub_termination_prob e' σ').
Proof.
  intros Hwp.
  rewrite lub_termination_sup_seq_termination_n.
  apply upper_bound_ge_sup.
  intros n.
  apply Rbar_le_lub.
  rewrite /termination_prob'.
  intros r [(sch_int_σ&ζ&Heqdecision&Hcountable&sch&Htape) <-].
  simpl.
  intros ε Hε.
  epose proof foxtrot_adequacy_intermediate Σ 0 ϕ n e e' _ _ as Hwp'. Unshelve.
  2: { done. }
  2: { iIntros. by iApply Hwp. }
  epose proof Hwp' sch_int_σ Heqdecision Hcountable sch ζ Htape σ σ' ε Hε as
    (sch_int_σ'&Heqdeicision'&Hcountable'&sch'&ζ'&Htape'&Hcoupl).
  apply ARcoupl_mass_leq in Hcoupl.
  replace (0+_) with ε in Hcoupl by lra.
  exists (SeriesC (sch_lim_exec sch' (ζ', ([e'], σ')))). split.
  - rewrite /termination_n_prob. rewrite Rcomplements.Rle_minus_l.
    apply Hcoupl.
  - rewrite /termination_prob_type.
    eexists (sch_int_σ'; _); simpl.
    instantiate (1:=(ζ', (_;(_;(_;Htape'))))).
    by rewrite /termination_prob.
Qed.
