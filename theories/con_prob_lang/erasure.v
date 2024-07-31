From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Lim_seq.
From stdpp Require Import fin_maps fin_map_dom.
From clutch.prelude Require Import stdpp_ext.
From clutch.common Require Import con_language con_ectx_language sch_erasable.
From clutch.con_prob_lang Require Import notation lang metatheory.
From clutch.prob Require Import couplings couplings_app mdp.

Set Default Proof Using "Type*".
Local Open Scope R.
Local Opaque state_upd_tapes.

Section erasure_helpers.

  Variable (m : nat).
  Context {sch_int_σ: Type}.
  Context `{TapeOblivious sch_int_σ sch}.
  Hypothesis IH :
    ∀ (es1 : list expr) (σ1 : state) α N zs ζ,
    tapes σ1 !! α = Some (N; zs) →
    Rcoupl
      (dmap (λ x, x.2.1) (sch_pexec sch m (ζ, (es1, σ1))))
      (dmap (λ x, x.2.1) (dunifP N ≫= (λ z, sch_pexec sch m (ζ, (es1, state_upd_tapes <[α:= (N; zs ++ [z])]> σ1))))) eq.

  Local Lemma ind_case_det e σ α N zs K (n:nat) s es:
    tapes σ !! α = Some (N; zs) →
    is_det_head_step e σ = true ->
    Rcoupl
    (dmap (pair s ∘ ((λ '(expr', σ', efs), (<[n:=expr']> es ++ efs, σ')) ∘ fill_lift' K))
       (head_step e σ)
     ≫= λ a,
          dmap (λ x, x.2.1) (sch_pexec sch m a))
    ((dunifP N
      ≫= λ a0 : fin (S N),
           dmap (pair s ∘ ((λ '(expr', σ', efs), (<[n:=expr']> es ++ efs, σ')) ∘ fill_lift' K))
             (head_step e (state_upd_tapes <[α:=(N; zs ++ [a0])]> σ)))
     ≫= λ b,
       dmap (λ x, x.2.1) (sch_pexec sch m b)) eq.
  Proof using m IH.
    intros Hα (e2 & (σ2 & (efs & Hdet)))%is_det_head_step_true%det_step_pred_ex_rel.
    erewrite 1!det_head_step_singleton; [|done..].
    setoid_rewrite (det_head_step_singleton ); eauto; last first.
    - eapply det_head_step_upd_tapes; eauto.
    - erewrite det_step_eq_tapes in Hα; [|done].
      rewrite !dmap_dret.
      rewrite !dret_id_left /=.
      rewrite -!dbind_assoc.
      erewrite (distr_ext (dunifP _ ≫= _) _); last first.
      { intros. apply dbind_pmf_ext; [|done..]. intros.
        rewrite dmap_dret dret_id_left. simpl. done. }
      rewrite -dmap_dbind. apply IH. done.
  Qed.

  Local Lemma ind_case_dzero e σ α N zs K (n:nat) s es:
    tapes σ !! α = Some (N; zs) →
    head_step e σ = dzero ->
    Rcoupl
    (dmap (pair s ∘ ((λ '(expr', σ', efs), (<[n:=expr']> es ++ efs, σ')) ∘ fill_lift' K))
       (head_step e σ)
     ≫= λ a,
          dmap (λ x, x.2.1) (sch_pexec sch m a))
    ((dunifP N
      ≫= λ a0 : fin (S N),
           dmap (pair s ∘ ((λ '(expr', σ', efs), (<[n:=expr']> es ++ efs, σ')) ∘ fill_lift' K))
             (head_step e (state_upd_tapes <[α:=(N; zs ++ [a0])]> σ)))
     ≫= λ b,
       dmap (λ x, x.2.1) (sch_pexec sch m b)) eq.
  Proof using m IH.
    intros Hα Hz.
    rewrite Hz.
    setoid_rewrite head_step_dzero_upd_tapes; [|by eapply elem_of_dom_2|done].
    rewrite dmap_dzero dbind_dzero dzero_dbind.
    rewrite dbind_dzero.
    apply Rcoupl_dzero_dzero.
  Qed.

  Local Lemma ind_case_alloc (z:Z) σ α N zs K (n:nat) s es:
    tapes σ !! α = Some (N; zs) →
    Rcoupl
    (dmap (pair s ∘ ((λ '(expr', σ', efs), (<[n:=expr']> es ++ efs, σ')) ∘ fill_lift' K))
       (head_step (alloc #z) σ)
     ≫= λ a,
          dmap (λ x, x.2.1) (sch_pexec sch m a))
    ((dunifP N
      ≫= λ a0 : fin (S N),
           dmap (pair s ∘ ((λ '(expr', σ', efs), (<[n:=expr']> es ++ efs, σ')) ∘ fill_lift' K))
             (head_step (alloc #z) (state_upd_tapes <[α:=(N; zs ++ [a0])]> σ)))
     ≫= λ b,
       dmap (λ x, x.2.1) (sch_pexec sch m b)) eq.
  Proof using m IH.
    intros Hα.
    rewrite dmap_dret dret_id_left.
    rewrite {3}/dmap.
    erewrite dbind_ext_right'; [|done|]; last first.
    { rewrite dbind_assoc dmap_fold.
      rewrite /dmap -dbind_assoc.
      erewrite dbind_ext_right; last first.
      - intros. rewrite dret_id_left. done.
      - done.
    }
    rewrite -dmap_dbind.
    rewrite -dbind_assoc.
    erewrite dbind_ext_right; last first.
    { intros.
      rewrite dret_id_left'.
      rewrite sch_pexec_fold.
      done.
    }
    apply lookup_total_correct in Hα as Hαtot.
    pose proof (elem_fresh_ne _ _ _ Hα) as Hne.
    erewrite dbind_ext_right; last first.
    { intros ?.
      rewrite -(fresh_loc_upd_some _ _ (N; zs)); [|done].
      rewrite (fresh_loc_upd_swap σ α (N; zs) (_; [])) //. }
    apply IH.
    by apply fresh_loc_lookup.
  Qed.

  Local Lemma ind_case_rand_some (z:Z) σ α α' (N M:nat) n ns ns' K (id:nat) s es:
    N=Z.to_nat z ->
    tapes σ!!α = Some (M;ns') ->
    tapes σ !! α' = Some (N; n::ns) →
    Rcoupl
    (dmap (pair s ∘ ((λ '(expr', σ', efs), (<[id:=expr']> es ++ efs, σ')) ∘ fill_lift' K))
       (head_step (rand(#lbl:α') #z) σ)
     ≫= λ a,
          dmap (λ x, x.2.1) (sch_pexec sch m a))
    ((dunifP M
      ≫= λ a0 ,
           dmap (pair s ∘ ((λ '(expr', σ', efs), (<[id:=expr']> es ++ efs, σ')) ∘ fill_lift' K))
             (head_step (rand(#lbl:α') #z) (state_upd_tapes <[α:=(M; ns' ++ [a0])]> σ)))
     ≫= λ b,
       dmap (λ x, x.2.1) (sch_pexec sch m b)) eq.
  Proof using m IH.
    intros Hz Hα Hα'.
    apply lookup_total_correct in Hα as Hαtot.
    apply lookup_total_correct in Hα' as Hα'tot.
    destruct (decide (α = α')) as [-> | Hαneql].
    - simplify_eq. rewrite /head_step Hα.
      setoid_rewrite lookup_insert.
      rewrite bool_decide_eq_true_2 //.
      rewrite dmap_dret dret_id_left.
      rewrite -dmap_dbind.
      erewrite dbind_ext_right'; [|done|]; last first.
      { apply dbind_ext_right.
        intros.
        simpl. rewrite dmap_dret. done.
      }
      assert (Haux : ∀ n,
                 state_upd_tapes <[α':=(Z.to_nat z; ns ++ [n])]> σ =
                 state_upd_tapes <[α':=(Z.to_nat z; ns ++ [n])]> (state_upd_tapes <[α':=(Z.to_nat z; ns)]> σ)).
      { intros. by rewrite state_upd_tapes_twice. }
      rewrite -!dbind_assoc.
      erewrite dbind_ext_right; last first.
      { intros. by rewrite dret_id_left sch_pexec_fold state_upd_tapes_twice Haux. }
      apply IH.
      apply lookup_insert.
    - rewrite /head_step Hα'.
      rewrite bool_decide_eq_true_2 //.
      setoid_rewrite lookup_insert_ne; [|done].
      rewrite Hα' bool_decide_eq_true_2 //.
      rewrite !dmap_dret !dret_id_left.
      rewrite -dmap_dbind.
      rewrite -dbind_assoc.
      erewrite dbind_ext_right; last first.
      { intros.
        rewrite upd_diff_tape_comm; [|done].
        rewrite dmap_dret dret_id_left sch_pexec_fold //. }
      eapply IH.
      rewrite lookup_insert_ne //.
  Qed.

  Local Lemma ind_case_rand_empty (z:Z) σ α α' (N M:nat) ns K (id:nat) s es:
    M=Z.to_nat z ->
    tapes σ!!α = Some (N;ns) ->
    tapes σ !! α' = Some (M; []) →
    Rcoupl
    (dmap (pair s ∘ ((λ '(expr', σ', efs), (<[id:=expr']> es ++ efs, σ')) ∘ fill_lift' K))
       (head_step (rand(#lbl:α') #z) σ)
     ≫= λ a,
          dmap (λ x, x.2.1) (sch_pexec sch m a))
    ((dunifP N
      ≫= λ a0 ,
           dmap (pair s ∘ ((λ '(expr', σ', efs), (<[id:=expr']> es ++ efs, σ')) ∘ fill_lift' K))
             (head_step (rand(#lbl:α') #z) (state_upd_tapes <[α:=(N; ns ++ [a0])]> σ)))
     ≫= λ b,
       dmap (λ x, x.2.1) (sch_pexec sch m b)) eq.
  Proof using m IH.
    intros Hz Hα Hα'.
    destruct (decide (α = α')) as [-> | Hαneql].
    + simplify_eq.  rewrite /head_step Hα.
      rewrite bool_decide_eq_true_2 //.
      rewrite {1 2}/dmap.
      rewrite -!dbind_assoc.
      eapply (Rcoupl_dbind _ _ _ _ (=)); [ |apply Rcoupl_eq].
      intros ? b ->.
      do 2 rewrite dret_id_left.
      rewrite lookup_insert.
      rewrite bool_decide_eq_true_2 //.
      rewrite dmap_dret dret_id_left.
      rewrite upd_tape_twice.
      rewrite dmap_fold.
      rewrite state_upd_tapes_no_change; [|done].
      apply Rcoupl_eq.
    + rewrite /head_step /=.
      setoid_rewrite lookup_insert_ne; [|done].
      rewrite Hα'.
      rewrite bool_decide_eq_true_2 //.
      rewrite !dbind_assoc.
      rewrite -!dbind_assoc.
      erewrite (dbind_ext_right (dunifP N)); last first.
      { intro.
        rewrite /dmap.
        rewrite -!dbind_assoc.
        apply dbind_ext_right.
        intros.
        rewrite !dret_id_left. done.
      }
      rewrite dbind_comm.
      eapply Rcoupl_dbind; [|apply Rcoupl_eq].
      intros; simplify_eq.
      do 2 rewrite dret_id_left /=.
      rewrite !dbind_assoc.
      rewrite !dmap_fold.
      by apply IH.
  Qed.

  Local Lemma ind_case_rand_some_neq (z:Z) σ α α' (N M:nat) ns ns' K (id:nat) s es:
    N≠Z.to_nat z ->
    tapes σ!!α = Some (M;ns') ->
    tapes σ !! α' = Some (N; ns) →
    Rcoupl
    (dmap (pair s ∘ ((λ '(expr', σ', efs), (<[id:=expr']> es ++ efs, σ')) ∘ fill_lift' K))
       (head_step (rand(#lbl:α') #z) σ)
     ≫= λ a,
          dmap (λ x, x.2.1) (sch_pexec sch m a))
    ((dunifP M
      ≫= λ a0 ,
           dmap (pair s ∘ ((λ '(expr', σ', efs), (<[id:=expr']> es ++ efs, σ')) ∘ fill_lift' K))
             (head_step (rand(#lbl:α') #z) (state_upd_tapes <[α:=(M; ns' ++ [a0])]> σ)))
     ≫= λ b,
       dmap (λ x, x.2.1) (sch_pexec sch m b)) eq.
  Proof using m IH.
    intros Hz Hα Hα'.
    rewrite /head_step Hα'.
    rewrite bool_decide_eq_false_2 //.
    destruct (decide (α = α')) as [-> | Heq].
    - simplify_eq.
      setoid_rewrite lookup_insert.
      rewrite bool_decide_eq_false_2 //.
      rewrite /dmap /=.
      rewrite -!dbind_assoc.
      erewrite (dbind_ext_right (dunifP M)); last first.
      { intros. rewrite -!dbind_assoc.
        apply dbind_ext_right.
        intros.
        rewrite !dret_id_left'//.
      } 
      rewrite dbind_comm.
      eapply Rcoupl_dbind; [|apply Rcoupl_eq].
      intros; simplify_eq.
      rewrite 2!dret_id_left.
      rewrite -!dmap_dbind.
      by apply IH.
    - setoid_rewrite lookup_insert_ne; [|done].
      rewrite Hα' bool_decide_eq_false_2 //.
      rewrite /dmap.
      rewrite -!dbind_assoc. 
      erewrite (dbind_ext_right (dunifP M)); last first.
      { intros. rewrite -!dbind_assoc.
        apply dbind_ext_right.
        intros.
        rewrite !dret_id_left//.
      } 
      rewrite dbind_comm.
      eapply Rcoupl_dbind; [|apply Rcoupl_eq].
      intros; simplify_eq.
      rewrite 2!dret_id_left.
      rewrite -dmap_dbind.
      by apply IH.
  Qed.

  Local Lemma ind_case_rand (z:Z) σ α (N M:nat) ns K (id:nat) s es:
    N=Z.to_nat z ->
    tapes σ!!α = Some (M;ns) ->
    Rcoupl
    (dmap (pair s ∘ ((λ '(expr', σ', efs), (<[id:=expr']> es ++ efs, σ')) ∘ fill_lift' K))
       (head_step (rand #z) σ)
     ≫= λ a,
          dmap (λ x, x.2.1) (sch_pexec sch m a))
    ((dunifP M
      ≫= λ a0 ,
           dmap (pair s ∘ ((λ '(expr', σ', efs), (<[id:=expr']> es ++ efs, σ')) ∘ fill_lift' K))
             (head_step (rand #z) (state_upd_tapes <[α:=(M; ns ++ [a0])]> σ)))
     ≫= λ b,
       dmap (λ x, x.2.1) (sch_pexec sch m b)) eq.
  Proof using m IH.
    intros Hz Hα.
    rewrite /head_step.
    erewrite (dbind_ext_right (dunifP M)); last first.
    { intro.
      rewrite {1 2}/dmap.
      rewrite -dbind_assoc.
      apply dbind_ext_right.
      intros. rewrite !dret_id_left. done.
    }
    rewrite {2 3}/dmap.
    rewrite -!dbind_assoc.
    erewrite (dbind_ext_right (dunifP M)); last first.
    { intros n. rewrite -!dbind_assoc. done. }
    rewrite dbind_comm.
    eapply Rcoupl_dbind; [|apply Rcoupl_eq].
    intros; simplify_eq.
    do 2 rewrite dret_id_left.
    erewrite (distr_ext (dunifP M ≫=_ )); last first.
    { intros. apply dbind_pmf_ext; [|done..].
      intros. rewrite !dret_id_left. done.
    }
    rewrite -dmap_dbind.
    apply IH; auto.
  Qed.

End erasure_helpers.


Lemma prim_coupl_upd_tapes_dom `{Countable sch_int_σ} m (es1: list expr) σ1 α N ns ζ `{TapeOblivious sch_int_σ sch}:
  σ1.(tapes) !! α = Some (N; ns) →
  Rcoupl
    (dmap (λ x, x.2.1) (sch_pexec sch m (ζ, (es1, σ1))))
    (dunifP N ≫=
       (λ n, dmap (λ x, x.2.1) (sch_pexec sch m (ζ, (es1, state_upd_tapes <[α := (N; ns ++ [n])]> σ1)))))
    (=).
Proof.
  rewrite -dmap_dbind.
  revert es1 σ1 α N ns ζ; induction m; intros es1 σ1 α N ns ζ Hα.
  - rewrite /sch_pexec /=.
    rewrite dmap_dret.
    rewrite dmap_dbind.
    erewrite (distr_ext (dunifP N≫=_)); last first.
    { intros. apply dbind_pmf_ext; [|done..].
      intros. rewrite dmap_dret. done.
    }
    rewrite (dret_const (dunifP N)); [apply Rcoupl_eq | apply dunif_mass; lia].
  - rewrite sch_pexec_Sn /sch_step_or_final.
    case_match eqn:He1; simpl in He1.
    + rewrite dret_id_left.
      rewrite -/(sch_pexec sch m (ζ, (es1, σ1))).
      rewrite sch_pexec_is_final; last by rewrite /is_final.
      rewrite dmap_dret. simpl.
      rewrite dmap_dbind.
      erewrite (distr_ext (dunifP N ≫=_)); last first.
      { intros. apply dbind_pmf_ext; [|done..].
        intros. rewrite sch_pexec_is_final; last by rewrite /is_final.
        rewrite dmap_dret. simpl. done.
      }
      rewrite dret_const; [|solve_distr_mass].
      apply Rcoupl_eq.
    + rewrite !dmap_dbind.
      erewrite (distr_ext (dunifP N ≫= _)); last first.
      { intros. apply dbind_pmf_ext; [|done..].
        intros. setoid_rewrite sch_pexec_Sn.
        rewrite /sch_step_or_final/=He1/sch_step/=.
        rewrite !dmap_dbind/=.
        apply dbind_pmf_ext; [done| |done].
        apply dbind_ext_right.
        intros [sch_int_σ' thread_id].
        rewrite /mbind/option_bind He1.
        instantiate (1 := λ '(sch_int_σ', thread_id),
                       dmap (λ mdp_σ' : con_language.cfg con_prob_lang, (sch_int_σ', mdp_σ'))
                         match es1 !! thread_id with
                         | Some expr0 =>
                             match to_val expr0 with
                             | Some _ => dret (es1, state_upd_tapes <[α:=(N; ns ++ [a0])]> σ1)
                             | None =>
                                 dmap (λ '(expr', σ', efs), (<[thread_id:=expr']> es1 ++ efs, σ'))
                                   (prim_step expr0 (state_upd_tapes <[α:=(N; ns ++ [a0])]> σ1))
                             end
                         | None => dret (es1, state_upd_tapes <[α:=(N; ns ++ [a0])]> σ1)
                         end ).
        done.
      }
      rewrite /sch_step/prim_step/=.
      rewrite /mbind/option_bind He1.
      setoid_rewrite sch_tape_oblivious_state_upd_tapes.
      rewrite dbind_assoc dbind_comm -!dbind_assoc'.
      eapply Rcoupl_dbind; last apply Rcoupl_eq.
      intros ?[] ->.
      rewrite /dmap.
      destruct (es1 !! n)  as [e1|]eqn:He2; last first.
      { (* we step a thread id that is out of bound *)
        rewrite !dret_id_left. rewrite -/dmap.
        rewrite dmap_fold.
        erewrite (distr_ext(_≫=_)); last first.
        - intros.
          rewrite dbind_assoc. rewrite dmap_fold.
          erewrite dmap_eq; first done; last first.
          + intros [?[??]].
            apply dbind_pmf_ext; [done| |done].
            etrans.
            * apply dbind_ext_right.
              intros. rewrite dret_id_left. done.
            * rewrite dmap_fold. done.
          + done.
        - rewrite {3}/dmap. rewrite -dbind_assoc.
          eapply Rcoupl_eq_trans; first apply IHm; last first.
          + apply Rcoupl_dmap.
            eapply Rcoupl_dbind; last apply Rcoupl_eq.
            intros ?? ->.
            rewrite dret_id_left. eapply Rcoupl_mono; first apply Rcoupl_eq.
            naive_solver.
          + done.
      }
      destruct (to_val e1) eqn:He3.
      { (* the thread we chose is already a value *)
        rewrite !dret_id_left. rewrite -/dmap.
        rewrite dmap_fold.
        erewrite (distr_ext(_≫=_)); last first.
        - intros.
          rewrite dbind_assoc. rewrite dmap_fold.
          erewrite dmap_eq; first done; last first.
          + intros [?[??]].
            apply dbind_pmf_ext; [done| |done].
            etrans.
            * apply dbind_ext_right.
              intros. rewrite dret_id_left. done.
            * rewrite dmap_fold. done.
          + done.
        - rewrite {3}/dmap. rewrite -dbind_assoc.
          eapply Rcoupl_eq_trans; first apply IHm; last first.
          + apply Rcoupl_dmap.
            eapply Rcoupl_dbind; last apply Rcoupl_eq.
            intros ?? ->.
            rewrite dret_id_left. eapply Rcoupl_mono; first apply Rcoupl_eq.
            naive_solver.
          + done.
      }
      rewrite /prim_step/=.
      destruct (decomp e1) as [K ered] eqn:Hdecomp_e1.
      rewrite Hdecomp_e1.
      rewrite !dmap_fold !dmap_comp /=.
      erewrite (distr_ext (dunifP N≫=_)); last first.
      { intros. apply dbind_pmf_ext; [|done..].
      intros. rewrite !dmap_fold !dmap_comp. done. }
      destruct (det_or_prob_or_dzero ered σ1) as [ HD | [HP | HZ]].
      * eapply ind_case_det; [done|done|by apply is_det_head_step_true].
      * inversion HP; simplify_eq.
        -- by eapply ind_case_alloc. 
        -- by eapply ind_case_rand_some.
        -- by eapply ind_case_rand_empty.
        -- by eapply ind_case_rand_some_neq.
        -- by eapply ind_case_rand.
      * by eapply ind_case_dzero.
Qed.

Lemma pexec_coupl_step_pexec `{Countable sch_int_σ} m es1 σ1 α bs ζ `{TapeOblivious sch_int_σ sch} :
  σ1.(tapes) !! α = Some bs →
   Rcoupl
    (dmap (λ ρ, ρ.2.1) (sch_pexec sch m (ζ, (es1, σ1))))
    (dmap (λ ρ, ρ.2.1) (state_step σ1 α ≫= (λ σ2, sch_pexec sch m (ζ, (es1, σ2)))))
    eq.
Proof.
  intros.
  destruct bs.
  eapply Rcoupl_eq_trans; first eapply prim_coupl_upd_tapes_dom; try done.
  rewrite <-dmap_dbind.
  apply Rcoupl_dmap.
  erewrite state_step_unfold; last done.
  rewrite /dmap.
  rewrite -dbind_assoc.
  eapply Rcoupl_dbind; last apply Rcoupl_eq.
  intros ??->.
  rewrite dret_id_left.
  eapply Rcoupl_mono; first apply Rcoupl_eq.
  intros. naive_solver.
Qed.

Lemma prim_coupl_step_prim `{Hcountable:Countable sch_int_σ} m es1 σ1 α bs ζ `{HTO: TapeOblivious sch_int_σ sch} :
  σ1.(tapes) !! α = Some bs →
  Rcoupl
    (sch_exec sch m (ζ, (es1, σ1)))
    (state_step σ1 α ≫= (λ σ2, sch_exec sch m (ζ, (es1, σ2))))
    eq.
Proof.
  intros Hα.
  epose proof pexec_coupl_step_pexec _ _ _ _ _ _ Hα as H'.
  setoid_rewrite sch_exec_pexec_relate.
  simpl.
  set (g:= λ es2: list expr, match option_bind _ _ to_val ((es2!!(0%nat)): option expr) with | Some b => dret b | None => dzero end).
  erewrite (distr_ext _ (dmap (λ ρ, ρ.2.1) (sch_pexec sch m (ζ, (es1, σ1))) ≫= g )); last first.
  { intros. rewrite /dmap.
    rewrite -dbind_assoc. simpl.
    apply dbind_pmf_ext; try done.
    intros [? []]. rewrite dret_id_left.
    rewrite /con_lang_mdp_to_final. intros.
    simpl. rewrite /option_bind. done.
  }
  erewrite (distr_ext (state_step _ _ ≫= _) _).
  - eapply Rcoupl_dbind; last exact.
    intros. subst. apply Rcoupl_eq.
  - intros. rewrite /dmap.
    rewrite -!dbind_assoc. simpl.
    apply dbind_pmf_ext; [|done|done].
    intros. apply dbind_pmf_ext; try done.
    intros [?[]]?.
    rewrite dret_id_left. simpl.
    rewrite /option_bind. done.
Qed.

Lemma state_step_sch_erasable `{Hcountable:Countable sch_int_σ} σ1 α bs `{TapeOblivious sch_int_σ sch}:
  σ1.(tapes) !! α = Some bs →
  sch_erasable sch (state_step σ1 α) σ1.
Proof.
  intros. rewrite /sch_erasable.
  intros.
  symmetry.
  apply Rcoupl_eq_elim.
  by eapply prim_coupl_step_prim.
Qed.

Lemma iterM_state_step_sch_erasable
  `{Hcountable:Countable sch_int_σ} σ1 α bs n `{TapeOblivious sch_int_σ sch}:
  σ1.(tapes) !! α = Some bs →
  sch_erasable sch (iterM n (λ σ, state_step σ α) σ1) σ1.
Proof.
  revert σ1 bs.
  induction n; intros σ1 bs K.
  - simpl. apply dret_sch_erasable.
  - simpl. apply sch_erasable_dbind; first by eapply state_step_sch_erasable.
    intros ? K'.
    destruct bs.
    erewrite state_step_unfold in K'; last done.
    rewrite dmap_pos in K'. destruct K' as (?&->&?).
    eapply IHn. simpl. apply lookup_insert.
Qed.

Lemma limprim_coupl_step_limprim_aux
  `{Hcountable:Countable sch_int_σ} e1 σ1 α bs v ζ `{TapeOblivious sch_int_σ sch}:
  σ1.(tapes) !! α = Some bs →
  (sch_lim_exec sch (ζ, (e1, σ1))) v =
  (state_step σ1 α ≫= (λ σ2, sch_lim_exec sch (ζ, (e1, σ2)))) v.
Proof.
  intro Hsome.
   rewrite sch_lim_exec_unfold/=.
   rewrite {2}/pmf/=/dbind_pmf.
   setoid_rewrite sch_lim_exec_unfold.
   simpl in *.
   assert
     (SeriesC (λ a: state, state_step σ1 α a * Sup_seq (λ n : nat, sch_exec sch n (ζ, (e1, a)) v)) =
     SeriesC (λ a: state, Sup_seq (λ n : nat, state_step σ1 α a * sch_exec sch n (ζ, (e1, a)) v))) as Haux.
   { apply SeriesC_ext; intro v'.
     apply eq_rbar_finite.
     rewrite rmult_finite.
     rewrite (rbar_finite_real_eq (Sup_seq (λ n : nat, sch_exec sch n (ζ, (e1, v')) v))); auto.
     - rewrite <- (Sup_seq_scal_l (state_step σ1 α v') (λ n : nat, sch_exec sch n (ζ, (e1, v')) v)); auto.
     - apply (Rbar_le_sandwich 0 1).
       + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
       + apply upper_bound_ge_sup; intro; simpl; auto.
   }
   rewrite Haux.
   rewrite (MCT_seriesC _ (λ n, sch_exec sch n (ζ, (e1,σ1)) v) (sch_lim_exec sch (ζ, (e1,σ1)) v)); auto.
   - real_solver.
   - intros. apply Rmult_le_compat; auto; [done|apply sch_exec_mono].
   - intro. exists (state_step σ1 α a)=>?. real_solver.
   - intro n.
     rewrite (Rcoupl_eq_elim _ _ (prim_coupl_step_prim n e1 σ1 α bs _ Hsome)); auto.
     rewrite {3}/pmf/=/dbind_pmf.
     apply SeriesC_correct; auto.
     apply (ex_seriesC_le _ (state_step σ1 α)); auto.
     real_solver.
   - rewrite sch_lim_exec_unfold.
     rewrite rbar_finite_real_eq; [apply Sup_seq_correct |].
     rewrite mon_sup_succ.
     + apply (Rbar_le_sandwich 0 1); auto.
       * apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
       * apply upper_bound_ge_sup; intro; simpl; auto.
     + intros. eapply sch_exec_mono.
Qed.

Lemma sch_limprim_coupl_step_sch_limprim
  `{Hcountable:Countable sch_int_σ} (e1 : list expr) σ1 α bs ζ`{TapeOblivious sch_int_σ sch} :
  σ1.(tapes) !! α = Some bs →
  Rcoupl
    (sch_lim_exec sch (ζ, (e1, σ1)))
    (state_step σ1 α ≫= (λ σ2, sch_lim_exec sch (ζ, (e1, σ2))))
    eq.
Proof.
  intro Hsome.
  erewrite (distr_ext (sch_lim_exec sch (ζ, (e1, σ1)))); last first.
  - intro a.
    apply (limprim_coupl_step_limprim_aux _ _ _ _ _ _ Hsome).
  - apply Rcoupl_eq.
Qed.

Lemma sch_lim_exec_eq_erasure `{Hcountable:Countable sch_int_σ} αs e σ ζ `{TapeOblivious sch_int_σ sch}:
  αs ⊆ get_active σ →
  sch_lim_exec sch (ζ, (e, σ)) = foldlM state_step σ αs ≫= (λ σ', sch_lim_exec sch (ζ, (e, σ'))).
Proof.
  induction αs as [|α αs IH] in σ |-*.
  { rewrite /= dret_id_left //. }
  intros Hα.
  eapply Rcoupl_eq_elim.
  assert (sch_lim_exec sch (ζ, (e, σ)) = state_step σ α ≫= (λ σ2, sch_lim_exec sch (ζ, (e, σ2)))) as ->.
  { apply distr_ext => v.
    assert (α ∈ get_active σ) as Hel; [apply Hα; left|].
    rewrite /get_active in Hel.
    apply elem_of_elements, elem_of_dom in Hel as [? ?].
    by eapply limprim_coupl_step_limprim_aux. }
  rewrite foldlM_cons -dbind_assoc.
  eapply Rcoupl_dbind; [|eapply Rcoupl_pos_R, Rcoupl_eq].
  intros ?? (-> & Hs%state_step_support_equiv_rel & _).
  inversion_clear Hs.
  rewrite IH; [eapply Rcoupl_eq|].
  intros α' ?. rewrite /get_active /=.
  apply elem_of_elements.
  apply elem_of_dom.
  destruct (decide (α = α')); subst.
  + eexists. rewrite lookup_insert //.
  + rewrite lookup_insert_ne //.
    apply elem_of_dom. eapply elem_of_elements, Hα. by right.
Qed.
