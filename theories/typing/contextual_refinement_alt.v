From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Lim_seq.
From clutch.common Require Import language ectx_language.
From clutch.prob_lang Require Import lang notation metatheory.
From clutch.typing Require Import types contextual_refinement.
From clutch.prob Require Import distribution.

(** Alternative formulation of contextual refinement without restricting to
    contexts of the ground type but only observing termination through their
    masses. *)
Definition ctx_refines_alt (Γ : stringmap type)
    (e e' : expr) (τ : type) : Prop := ∀ K σ₀ τ',
  typed_ctx K Γ τ ∅ τ' →
  (SeriesC (lim_exec (fill_ctx K e, σ₀)) <= SeriesC (lim_exec (fill_ctx K e', σ₀)))%R.

Notation SeqV e1 e2 := (LamV BAnon e2%E e1%E).

Lemma prim_step_true_no_final e σ n :
  to_val e = None →
  step_or_final ((SeqV e #true)%E, σ) ≫= exec n =
    (prim_step e σ) ≫= (λ '(e', σ'), exec n ((SeqV e' #true)%E, σ')).
Proof.
  intros He.
  rewrite 1!step_or_final_no_final /=; [|eauto].
  replace (SeqV e #true)%E with (fill [(AppRCtx (LamV <> #true)%E)] e); [|done].
  rewrite fill_dmap //=.
  rewrite /dmap.
  rewrite -dbind_assoc -/exec.
  eapply dbind_eq; [|done].
  intros [e' σ'] Hs.
  rewrite dret_id_left //.
Qed.

Lemma prim_step_true_val e σ n v :
  to_val e = Some v →
  step_or_final ((SeqV e #true)%E, σ) ≫= exec n =
    exec n ((of_val #true)%E, σ).
Proof.
  intros He.
  rewrite 1!step_or_final_no_final /=; [|eauto].
  apply of_to_val in He. rewrite -He.
  rewrite head_prim_step_eq; last first.
  { eexists (_, _).
    eapply head_step_support_equiv_rel.
    by econstructor. }
  erewrite det_head_step_singleton; [|by econstructor]; simpl.
  rewrite dret_id_left -/exec //.
Qed.

Lemma exec_SeriesC_SeqV_true e σ n :
  exec (S n) (SeqV e #true, σ) #true = SeriesC (exec n (e, σ)).
Proof.
  move: e σ; induction n; intros e σ.
  - rewrite exec_Sn.
    destruct (to_val e) eqn:Heq.
    + setoid_rewrite prim_step_true_val; eauto; simpl.
      rewrite Heq dret_mass dret_1_1; auto.
    + setoid_rewrite prim_step_true_no_final; eauto; simpl.
      rewrite Heq.
      rewrite SeriesC_0; auto.
      rewrite /pmf/=/dbind_pmf.
      setoid_rewrite SeriesC_0; auto.
      intros (? & ?).
      rewrite Rmult_0_r; auto.
  - setoid_rewrite exec_Sn.
    destruct (to_val e) eqn:Heq.
    + rewrite (prim_step_true_val _ _ _ v); auto.
      rewrite {1}/step_or_final/= Heq.
      assert (SeriesC (exec n (e, σ)) = SeriesC (dret (e, σ) ≫= exec n)) as Haux.
      { apply SeriesC_ext; intro. rewrite dret_id_left. auto. }
      rewrite -Haux.
      rewrite exec_unfold /= Heq.
      rewrite dret_mass.
      rewrite dret_1_1; auto.
    + rewrite prim_step_true_no_final; auto.
      rewrite step_or_final_no_final; auto.
      rewrite /pmf/=/dbind_pmf.
      rewrite distr_double_swap.
      apply SeriesC_ext; intro.
      rewrite SeriesC_scal_l.
      rewrite (Rmult_eq_compat_l (prim_step e σ n0)
                 ((let '(e', σ') := n0 in prim_step (SeqV e' #true) σ' ≫= exec n) #true)
                 (SeriesC (exec n n0))); auto.
      destruct n0. rewrite -IHn.
      rewrite exec_Sn.
      rewrite step_or_final_no_final //; auto. 
Qed.

Lemma lim_exec_SeriesC_SeqV_true e σ :
  SeriesC (lim_exec (e, σ)) = (lim_exec (SeqV e #true, σ)) #true.
Proof.
  rewrite lim_exec_unfold.
  erewrite SeriesC_ext; [|intro; apply lim_exec_unfold].
  simpl.
  rewrite (MCT_seriesC _ (λ n, SeriesC (exec n (e,σ)))
             (Sup_seq (λ n0 : nat, SeriesC (λ n : val, exec n0 (e, σ) n)))) .
  - rewrite (mon_sup_succ (λ n : nat, exec n ((SeqV e #true)%E, σ) #true)).
    + f_equal. apply Sup_seq_ext; intro n.
      rewrite (exec_SeriesC_SeqV_true e σ n); auto.
    + intro; apply exec_mono.
  - intros; auto.
  - intros. apply: (exec_mono (_,_)).
  - intros; exists 1; intros; auto.
  - intros. apply SeriesC_correct; auto.
  - rewrite (Rbar_le_sandwich 0 1); auto.
    + apply Sup_seq_correct.
    + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
    + apply upper_bound_ge_sup; intro; simpl; auto.
Qed.

Lemma ctx_refines_impl_alt Γ e1 e2 τ :
  (Γ ⊨ e1 ≤ctx≤ e2 : τ) → ctx_refines_alt Γ e1 e2 τ.
Proof.
  intros H K σ0 τ' Hty.
  pose (K' := (CTX_AppR (LamV BAnon #true)%E):: K).
  cut (∀ e, lim_exec (SeqV e #true, σ0) #true = SeriesC (lim_exec (e, σ0))).
  - intros Heq. rewrite -2!Heq.
    eapply (H K' σ0 true).
    repeat econstructor; eauto.
  - intros e.
    rewrite lim_exec_SeriesC_SeqV_true //.
Qed.



(*Other direction*)
Lemma ssd_is_value_lim_exec_cfg_same e σ :
  (ssd (λ '(e', _), bool_decide (is_Some (to_val e'))) (lim_exec_cfg (e, σ))) =
  lim_exec_cfg (e, σ).
Proof.
  apply distr_ext. intros [e' σ'].
  rewrite /ssd{1}/pmf/ssd_pmf.
  case_bool_decide; eauto; simpl.
  rewrite -eq_None_not_Some in H.
  rewrite /lim_exec_cfg lim_distr_pmf.
  symmetry. 
  rewrite <-sup_seq_const. do 2 f_equal. apply functional_extensionality_dep.
  intros. revert e σ. induction x; intros; simpl; destruct (to_val e) eqn:H1; eauto.
  - assert (e ≠ e').
    { intro. rewrite H0 in H1. by rewrite H in H1. }
    rewrite /dret/pmf/dret_pmf; case_bool_decide; [|done].
    by inversion H2.  
  - assert (e ≠ e').
    { intro. rewrite H0 in H1. by rewrite H in H1. }
    rewrite /dret/pmf/dret_pmf; case_bool_decide; [|done].
    by inversion H2.
  - rewrite /dbind/pmf/dbind_pmf.
    erewrite <-dzero_mass. do 2 f_equal.
    apply functional_extensionality_dep.
    intros [??].
    replace (dzero _) with 0; last done.
    erewrite <-Rbar_finite_eq. rewrite rmult_finite.
    rewrite IHx. apply Rbar_mult_0_r.
Qed. 
                                                                               

Lemma ssd_not_value_lim_exec_cfg_dzero e σ :
  ssd (λ a : expr * state, negb (let '(e', _) := a in bool_decide (is_Some (to_val e'))))
    (lim_exec_cfg (e, σ)) = dzero.
Proof.
  apply distr_ext. intros [e' σ'].
  rewrite /dzero/ssd/pmf/ssd_pmf.
  case_bool_decide; eauto; simpl.
  rewrite -eq_None_not_Some in H.
  rewrite /lim_exec_cfg lim_distr_pmf.
  rewrite <-sup_seq_const. do 2 f_equal. apply functional_extensionality_dep.
  intros. revert e σ. induction x; intros; simpl; destruct (to_val e) eqn:H1; eauto.
  - assert (e ≠ e').
    { intro. rewrite H0 in H1. by rewrite H in H1. }
    rewrite /dret/pmf/dret_pmf; case_bool_decide; [|done].
    by inversion H2.  
  - assert (e ≠ e').
    { intro. rewrite H0 in H1. by rewrite H in H1. }
    rewrite /dret/pmf/dret_pmf; case_bool_decide; [|done].
    by inversion H2.
  - rewrite /dbind/pmf/dbind_pmf.
    erewrite <-dzero_mass. do 2 f_equal.
    apply functional_extensionality_dep.
    intros [??].
    replace (dzero _) with 0; last done.
    erewrite <-Rbar_finite_eq. rewrite rmult_finite.
    rewrite IHx. apply Rbar_mult_0_r.
Qed. 

(* first part *)
Lemma lim_exec_val_of_val_b_one e b σ: e = of_val #b -> lim_exec_val ((e = #b)%E, σ) #true = 1.
Proof.
  intros ->.
  rewrite lim_exec_val_rw.
  rewrite mon_sup_succ.
  - erewrite <-sup_seq_const. do 2 f_equal. apply functional_extensionality_dep.
    intros n. simpl. rewrite head_prim_step_eq => /=.
    2: { eexists (_, _). destruct b;
        eapply head_step_support_equiv_rel;
        by econstructor.
    }
    destruct b => /=; try case_bool_decide; try done.
    all: rewrite dret_id_left; destruct n => /=; by rewrite dret_1_1.
  - intro. apply exec_val_mon.
Qed.

Lemma lim_exec_val_of_val_not_b_zero e b σ: (is_Some (to_val e)) -> e ≠ of_val #b -> lim_exec_val ((e = #b)%E, σ) #true = 0.
Proof.
  intros H H0.
  rewrite lim_exec_val_rw.
  erewrite <-sup_seq_const. do 2 f_equal.
  apply functional_extensionality_dep.
  intros [].
  - by rewrite /pmf /=.
  - simpl. destruct H.
    apply of_to_val in H as H1. rewrite -H1. rewrite -H1 in H0.
    clear H H1. 
    destruct x eqn:H2; rewrite head_prim_step_eq.
    -- destruct b, l => /=; try (rewrite dret_id_left; destruct n => /=; done).
       all: rewrite bool_decide_eq_false_2;[rewrite dret_id_left; by destruct n|].
       all: intro; apply H0; by rewrite H.
    -- eexists (_,_).
       eapply head_step_support_equiv_rel.
       destruct l, b; by econstructor.
    -- destruct b => /=; try (rewrite dret_id_left; destruct n => /=; done).
    -- eexists (_,_).
       eapply head_step_support_equiv_rel.
       destruct b; by econstructor.
    -- destruct b => /=; try (rewrite dret_id_left; destruct n => /=; done).
    -- eexists (_,_).
       eapply head_step_support_equiv_rel.
       destruct b; by econstructor.
    -- destruct v, b => /=; try (rewrite dret_id_left; destruct n => /=; done).
       all: destruct l => /=; try (rewrite dret_id_left; destruct n => /=; done).
    -- eexists (_,_).
       eapply head_step_support_equiv_rel.
       destruct v, b; try by econstructor.
       all: destruct l; by econstructor.
    -- destruct v, b => /=; try (rewrite dret_id_left; destruct n => /=; done).
       all: destruct l => /=; try (rewrite dret_id_left; destruct n => /=; done).
    -- eexists (_,_).
       eapply head_step_support_equiv_rel.
       destruct v, b; try by econstructor.
       all: destruct l; by econstructor.
Qed.         


Lemma lim_exec_val_is_b_test e σ (b:bool) : lim_exec_val (e, σ) #b = lim_exec_val ((e = #b)%E, σ) #true.
Proof.
  replace ((e=#b)%E) with (fill_item (BinOpLCtx EqOp (#b)) e); last first.
  { done. }
  rewrite lim_exec_val_context_bind => /=.
  pose (ν := λ '(e', σ'), lim_exec_val ((e' = #b)%E, σ')).
  assert ((λ '(e', σ'), lim_exec_val ((e' = #b)%E, σ'))=(λ c, ν c)) as K.
  { by apply functional_extensionality_dep. }
  rewrite K.
  erewrite (ssd_bind_split_sum _ _ (λ '(e', σ'), bool_decide (is_Some (to_val e')))).
  rewrite ssd_not_value_lim_exec_cfg_dzero.
  rewrite dbind_dzero /dzero {3}/pmf. rewrite Rplus_0_r.
  erewrite (ssd_bind_split_sum _ _ (λ '(e', σ'), bool_decide (to_val e' = Some #b))).
  erewrite (ssd_bind_constant _ _ _ _ 1); last first.
  { intros [e' s] H. rewrite /ν.
    apply lim_exec_val_of_val_b_one.
    rewrite bool_decide_eq_true in H.
    by apply of_to_val in H.
  }
  rewrite Rmult_1_l.
  rewrite {1}ssd_is_value_lim_exec_cfg_same.
  rewrite ssd_chain.
  rewrite (ssd_bind_constant _ _ _ _ 0); last first.
  { intros [??] H.
    rewrite /ν.
    rewrite andb_true_iff in H. destruct H as [H1 H2].
    rewrite negb_true_iff in H1.
    rewrite bool_decide_eq_false in H1.
    rewrite bool_decide_eq_true in H2.
    apply lim_exec_val_of_val_not_b_zero; eauto.
    intro. rewrite H in H1. simpl in H1. by apply H1. 
  }
  rewrite Rmult_0_l Rplus_0_r.
  rewrite ssd_fix_value_lim_exec_val_lim_exec_cfg.
  by rewrite ssd_fix_value.
Qed. 


(* second part *)

Definition loop := App (RecV "f" "x" (App (Var "f") (Var "x"))) (#()).

Lemma loop_zero_mass n σ x: exec_val n (loop, σ) x = 0.
Proof.
  induction n as [n Hn] using (well_founded_induction lt_wf).
  destruct n.
  - simpl. destruct x; auto.
  -  rewrite /loop. simpl. rewrite head_prim_step_eq; last first.
     -- eexists _. erewrite det_head_step_singleton; [|by econstructor]. simpl.
        rewrite dret_1_1; [|done]. lra.
     -- simpl. rewrite dret_id_left -/exec_val. apply Hn. lia.
Qed. 

Lemma lim_exec_val_of_val_true_one (e : expr) σ: e = #true -> lim_exec_val ((if: e then #() else loop)%E, σ) (#()) = 1.
Proof.
intros ->.
  rewrite lim_exec_val_rw.
  rewrite mon_sup_succ.
  - erewrite <-sup_seq_const. do 2 f_equal. apply functional_extensionality_dep.
    intros n. simpl. rewrite head_prim_step_eq => /=.
    2: { eexists (_, _). 
        eapply head_step_support_equiv_rel;
        by econstructor.
    }
    rewrite dret_id_left; destruct n => /=; by rewrite dret_1_1.
  - intro. apply exec_val_mon.
Qed.

Lemma lim_exec_val_of_val_not_true_zero (e : expr) σ: (∃ v, e = of_val v) -> e ≠ #true -> lim_exec_val ((if: e then #() else loop)%E, σ) (#()) = 0.
Proof.
  intros H H0.
  rewrite lim_exec_val_rw.
  erewrite <-sup_seq_const. do 2 f_equal.
  apply functional_extensionality_dep.
  intros [].
  - by rewrite /pmf /=.
  - simpl. destruct H.
    rewrite H. rewrite H in H0.
    clear H. 
    destruct x eqn:H2.
    { destruct l.
      2: { destruct b; [exfalso; by apply H0|].
           rewrite head_prim_step_eq => /=; last first.
           + eexists (_, _). 
             eapply head_step_support_equiv_rel;
               by econstructor.
           + rewrite dret_id_left -/ exec_val. rewrite loop_zero_mass. f_equal.
      } 
      all: replace (_≫=_) with (dzero ≫= exec_val n); [by rewrite dbind_dzero|f_equal].
      all: apply distr_ext => s; replace (dzero s) with 0 by done.
      all: rewrite /prim_step => /=; rewrite decomp_unfold => /=.
      all: by rewrite dmap_dzero.
    }
    all: replace (_≫=_) with (dzero ≫= exec_val n); [by rewrite dbind_dzero|f_equal].
    all: apply distr_ext => s; replace (dzero s) with 0 by done.
    all: rewrite /prim_step => /=; rewrite decomp_unfold => /=.
    all: by rewrite dmap_dzero.
Qed. 

Lemma lim_exec_val_is_true_test e σ: 
  lim_exec_val ((if: e then #() else loop)%E, σ) #() = lim_exec_val (e,σ) (#true).
Proof.
  replace (if: e then #() else loop)%E with (fill_item (IfCtx #() loop) e); last first.
  { done. }
  rewrite lim_exec_val_context_bind => /=.
  pose (ν := λ '(e', σ'), lim_exec_val ((if: e' then #() else loop)%E, σ')).
  assert ((λ '(e', σ'), lim_exec_val ((if: e' then #() else loop)%E, σ'))=(λ c, ν c)) as K.
  { by apply functional_extensionality_dep. }
  rewrite K.
  erewrite (ssd_bind_split_sum _ _ (λ '(e', σ'), bool_decide (is_Some (to_val e')))).
  rewrite ssd_not_value_lim_exec_cfg_dzero.
  rewrite dbind_dzero /dzero {3}/pmf. rewrite Rplus_0_r.
  erewrite (ssd_bind_split_sum _ _ (λ '(e', σ'), bool_decide (to_val e' = Some #true))).
  erewrite (ssd_bind_constant _ _ _ _ 1); last first.
  { intros [e' s] H. rewrite /ν.
    apply lim_exec_val_of_val_true_one.
    rewrite bool_decide_eq_true in H.
    by apply of_to_val in H.
  }
  rewrite Rmult_1_l.
  rewrite {1}ssd_is_value_lim_exec_cfg_same.
  rewrite ssd_chain.
  rewrite (ssd_bind_constant _ _ _ _ 0); last first.
  { intros [??] H.
    rewrite /ν.
    rewrite andb_true_iff in H. destruct H as [H1 H2].
    rewrite negb_true_iff in H1.
    rewrite bool_decide_eq_false in H1.
    rewrite bool_decide_eq_true in H2.
    apply lim_exec_val_of_val_not_true_zero.
    - destruct H2. apply of_to_val in H. eauto.
    - intro. rewrite H in H1. simpl in H1. by apply H1. 
  }
  rewrite Rmult_0_l Rplus_0_r.
  rewrite ssd_fix_value_lim_exec_val_lim_exec_cfg.
  by rewrite ssd_fix_value.
Qed. 


Lemma lim_exec_val_seriesc_return_value e σ:
  SeriesC (lim_exec_val ((if: e then #() else loop)%E, σ)) =
  lim_exec_val ((if: e then #() else loop)%E, σ) #(). 
Proof.
  rewrite -ssd_fix_value.
  f_equal. f_equal.
  apply distr_ext. intros v.
  destruct (bool_decide (v=#())) eqn:H.
  - by rewrite /ssd {2}/pmf /=/ssd_pmf H.
  - rewrite /ssd {2}/pmf /=/ssd_pmf H.
    rewrite bool_decide_eq_false in H.
    rewrite lim_exec_val_rw.
    rewrite <-sup_seq_const. do 2 f_equal. apply functional_extensionality_dep.
    intros n. revert e σ. induction n.
    + by intros.
    + intros. simpl. 
      destruct (to_val e) eqn:H'.
      -- apply of_to_val in H'; subst. destruct v0.
         { destruct l.
           2: { destruct b;
                rewrite head_prim_step_eq => /=; last first.
                + eexists (_, _). 
                  eapply head_step_support_equiv_rel;
                    by econstructor.
                + rewrite dret_id_left -/ exec_val. rewrite loop_zero_mass. f_equal.
                + eexists (_, _). 
                  eapply head_step_support_equiv_rel;
                    by econstructor.
                + rewrite dret_id_left -/ exec_val.
                  destruct n => /=; f_equal; by apply dret_0.
           }
           all: replace (_≫=_) with (dzero ≫= exec_val n); [by rewrite dbind_dzero|f_equal].
           all: apply distr_ext => s; replace (dzero s) with 0 by done.
           all: rewrite /prim_step => /=; rewrite decomp_unfold => /=.
           all: by rewrite dmap_dzero.
         }
         all: replace (_≫=_) with (dzero ≫= exec_val n); [by rewrite dbind_dzero|f_equal].
         all: apply distr_ext => s; replace (dzero s) with 0 by done.
         all: rewrite /prim_step => /=; rewrite decomp_unfold => /=.
         all: by rewrite dmap_dzero.
      -- replace (if: _ then _ else _)%E with (fill [IfCtx (#()) loop] e); last done.
         rewrite fill_prim_step_dbind; [|done].
         rewrite /dmap => /=.
         rewrite -dbind_assoc -/exec_val.
         rewrite {1}/dbind/pmf/dbind_pmf.
         f_equal. apply SeriesC_0. intros [??].
         rewrite dret_id_left => /=.
         replace (exec_val _ _ _) with 0; [lra|].
         do 2 f_equal.
         rewrite <- Rbar_finite_eq.
         by rewrite IHn.
Qed.


(*Combining both *)
Lemma alt_impl_ctx_refines_loop_lemma e (b:bool) σ:
  lim_exec_val (e, σ) #b = SeriesC (lim_exec_val ((if: e = #b then #() else loop)%E, σ)).
Proof.
  rewrite lim_exec_val_seriesc_return_value.
  rewrite lim_exec_val_is_true_test.
  apply lim_exec_val_is_b_test.
Qed. 

Lemma alt_impl_ctx_refines Γ e1 e2 τ :
  ctx_refines_alt Γ e1 e2 τ -> (Γ ⊨ e1 ≤ctx≤ e2 : τ).
Proof.
  intros H K σ0 b Hty.
  destruct (bool_decide_reflect (lim_exec_val (fill_ctx K e1, σ0) #b <= lim_exec_val (fill_ctx K e2, σ0) #b)) as [|HC]; first done.
  apply Rnot_le_gt in HC. 
  pose (K' := CTX_IfL (#()) loop :: CTX_BinOpL EqOp #b :: K).
  assert (¬ SeriesC (lim_exec_val (fill_ctx K' e1, σ0)) <= SeriesC (lim_exec_val (fill_ctx K' e2, σ0))); last first.
  - exfalso. eapply H0, H.
    rewrite /K'.
    econstructor.
    2:{ econstructor; eauto. econstructor; eauto. econstructor. econstructor. }
    rewrite /loop. econstructor; tychk.
  - apply Rlt_not_le, Rgt_lt.
    rewrite /K' /=. 
    by do 2 rewrite -alt_impl_ctx_refines_loop_lemma.
Qed. 
