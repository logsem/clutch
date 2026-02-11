From Stdlib Require Import Reals Psatz.
From clutch.delay_prob_lang Require Import tactics notation urn_subst metatheory.
From clutch.delay_prob_lang Require Export lang.
From clutch.prob Require Import distribution.
Set Default Proof Using "Type*".

Lemma list_destruct_rev {A: Type} (l:list A) :
  l= [] \/ ∃ x xs, l = xs ++ [x].
Proof.
  induction l using rev_ind; destruct!/=; first naive_solver.
  - right. eexists _, []. naive_solver.
  - right. naive_solver.
Qed.

Local Ltac smash :=
  repeat (done||subst||simpl in *||rewrite app_nil_r||rewrite app_assoc||split||eexists _).

Lemma fill_is_val K (e:expr) v:
  fill K e = (Val v) -> K=[].
Proof.
  intros H.
  eapply fill_to_val; by erewrite H.
Qed. 

Local Ltac fill_inv :=
  repeat
    match goal with
    | H : fill _ _ = (Val _)  |- _ => apply fill_is_val in H as ?; subst; simpl in *; subst
    | H : (Val _) = fill _ _  |- _ => symmetry in H; apply fill_is_val in H as ?; subst; simpl in *; subst
    | H : is_Some (to_val (fill _ _))  |- _ =>  destruct H as [? H]; apply of_to_val in H;symmetry in H
    end.

Lemma fill_equal_break K K' e1' v' σ:
  head_step_pred e1' σ ->
  fill K' e1' = fill K (Val v') ->
  (∃ K1, K= K1++K') \/ (∃ Kall K1 K1' K2, K' = K1++[K1']++ Kall /\ K = K2:: Kall /\ fill (K1++[K1']) e1' = fill_item K2 (Val v') /\ K1' ≠ K2).
Proof.
  revert K' e1' v'.
  induction K as [|K1 K2 IHK]using rev_ind.
  - intros K' e1' v' H1 H2.
    simpl in *.
    epose proof fill_to_val K' _ as ->; last by erewrite H2.
    left. exists []. naive_solver.
  - intros K' e1' v' H1 H2.
    rewrite fill_app in H2.
    simpl in *.
    destruct (list_destruct_rev K') as [|[K1' [K2']]].
    { subst. simpl in *. subst.
      setoid_rewrite app_nil_r.
      naive_solver. }
    subst. rewrite fill_app in H2.
    simpl in *.
    destruct (decide (K1=K1')).
    { subst. simplify_eq.
      apply IHK in H2; last done.
      destruct!/=.
      - setoid_rewrite app_assoc; naive_solver.
      - right. eexists _, _, _, _.
        split; last done.
        rewrite -app_assoc. f_equal.
    }
    destruct K1, K1'; simplify_eq; fill_inv; simplify_eq; try (by inversion H1); right.
    all: repeat eexists _; split; last split; [|done|]; try (by rewrite app_nil_r); try (by rewrite fill_app); try (by f_equal); by rewrite fill_app.
Qed.

Lemma value_promote_preserves_atomicity_empty_context f v v' e1' e2' σ σ' K K' :
  urn_subst_val f v = Some v' ->
  head_step_rel e1' σ e2' σ' ->
  fill K' e1' = fill K (Val v') ->
  ( ∀ (σ σ' : state) (K0 : list ectx_item) (e1' : ectxi_language.expr d_prob_ectxi_lang) (e2' : expr),
      fill K0 e1' = fill K v → head_step e1' σ (e2', σ') > 0 → is_Some (to_val (fill K0 e2'))) ->
  K' = [].
Proof.
  intros H1 H2 H3 H4.
  eapply fill_equal_break in H3 as H5; last first.
  { rewrite head_step_pred_ex_rel. naive_solver. }
  destruct H5 as [H|H].
  - destruct!/=.
    rewrite fill_app in H3.
    simplify_eq.
    admit.
  - destruct H as (Hall & K1 & K1' & K2 & -> &-> &H&Hneq).
    rewrite !fill_app//= in H3, H.
    simplify_eq. simpl in *.
    admit. 
    (* destruct (list_destruct_rev K1) as [|[K1' [K2']]]. *)
    (* + subst. simpl in *. inversion H2. *)
    (* + subst. rewrite fill_app in H2. simpl in H2. *)
    (*   destruct (list_destruct_rev K2') as [|[K1'' [K2'']]]; last first. *)
    (*   { subst. rewrite fill_app in H2. *)
    (*     simpl in *. inversion H2; destruct K1'; simplify_eq; destruct K1''; simplify_eq. *)
    (*   } *)
    (*   subst. simpl in *. *)
    (*   inversion H2; destruct K1'; simplify_eq; simpl in *; simplify_eq. *)
    (*   * unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply PairS|..]. by fill_inv. *)
    (*   * unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply PairS|..]. by fill_inv. *)
    (*   * unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply InjLS|..]; last by fill_inv. *)
    (*   * unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply InjRS|..]; last by fill_inv. *)
    (*   * destruct v; simpl in *; repeat setoid_rewrite bind_Some in H1; destruct!/=. *)
    (*     unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply BetaS|..]; last by fill_inv. *)
    (*     2:{ done. } *)
    (*   * unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply BetaS|..]; last by fill_inv. *)
    (*     2:{ done. } *)
    (*   * unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply UnOpS|..]; last by fill_inv. *)
        
    (*     admit. *)
    (*   * admit. *)
    (*   * admit. *)
    (*   * destruct v; simpl in *; repeat setoid_rewrite bind_Some in H1; destruct!/=. *)
    (*     unshelve epose proof H4 ({|heap:=inhabitant; urns :=urns_subst_f_to_urns  f|}) _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply IfTrueS|..]; last by fill_inv. *)
    (*     admit.  *)
    (*   * destruct v; simpl in *; repeat setoid_rewrite bind_Some in H1; destruct!/=. *)
    (*     unshelve epose proof H4 ({|heap:=inhabitant; urns :=urns_subst_f_to_urns  f|}) _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply IfFalseS|..]; last by fill_inv. *)
    (*     admit.  *)
    (*   * destruct v; simpl in *; repeat setoid_rewrite bind_Some in H1; destruct!/=. *)
    (*     unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply FstS|..]; last by fill_inv. *)
    (*   * destruct v; simpl in *; repeat setoid_rewrite bind_Some in H1; destruct!/=. *)
    (*     unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply SndS|..]; last by fill_inv. *)
    (*   * destruct v; simpl in *; repeat setoid_rewrite bind_Some in H1; destruct!/=. *)
    (*     unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply CaseLS|..]; last by fill_inv. *)
    (*   * destruct v; simpl in *; repeat setoid_rewrite bind_Some in H1; destruct!/=. *)
    (*     unshelve epose proof H4 σ' _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply CaseRS|..]; last by fill_inv. *)
    (*   * destruct v; simpl in *; repeat setoid_rewrite bind_Some in H1; destruct!/=. *)
    (*     unshelve epose proof H4 ({|heap:=inhabitant; urns :=urns_subst_f_to_urns  f|}) _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply AllocNS|..]; last by fill_inv. *)
    (*     all: try done. *)
    (*     admit. *)
    (*   * unshelve epose proof H4 ({|heap:=inhabitant; urns :=urns_subst_f_to_urns  f|}) _ (K') _ _ _ _; [| | |done|rewrite head_step_support_equiv_rel; eapply AllocNS|..]; last by fill_inv. *)
    (*     all: try done. *)
    (*     admit. *)
    (*   * destruct v as [l0| | | |]; simpl in *; repeat setoid_rewrite bind_Some in H1; destruct!/=. *)
    (*     destruct l0; simpl in *; repeat setoid_rewrite bind_Some in H; destruct!/=; repeat case_match; simplify_eq. *)
    (*     -- admit. *)
    (*     -- admit.  *)
    (*   * admit. *)
    (*   * admit.  *)
    (*   * admit. *)
    (*   * admit.  *)
    (*   * admit. *)
    (*   * admit.  *)
    (*   * admit. *)
    (*   * admit.  *)
    (*   * admit. *)
    (*   * admit.  *)
    (*   * admit. *)
    (*   * admit.  *)
    (*   * admit. *)
    (*   * admit.  *)
    (*   * admit. *)
    (*   * admit.  *)

Admitted. 

Lemma value_promote_preserves_atomicity K f v v':
  Atomic StronglyAtomic (fill K (Val v)) ->
  urn_subst_val f v = Some v' ->
  Atomic StronglyAtomic (fill K (Val v')).
Proof.
  rewrite /Atomic/=.
  intros H1 H2 σ e' σ' Hstep.
  rewrite prim_step_iff in Hstep.
  destruct Hstep as (K' & e1' & e2' & H3 & <- & H4).
  simpl in *.
  rewrite head_step_support_equiv_rel in H4.
  setoid_rewrite prim_step_iff in H1.
  simpl in *.
  assert (∀ (σ : state) (σ' : state) (K0 : list ectx_item) e1' e2',
      fill K0 e1' = fill K v  -> head_step e1' σ (e2', σ') > 0
      → is_Some (to_val (fill K0 e2'))) as H1' by naive_solver.
  clear H1.
  assert (K' = []) as ->; last first.
  { simpl.
    inversion H4; simpl; subst; simpl in *; try done.
    - simpl in *.
      destruct (list_destruct_rev K) as [|[K1 [K2]]]; simplify_eq.
      rewrite fill_app in H3.
      simpl in *.
      destruct K1; simplify_eq; simpl in *; simplify_eq.
      + destruct (list_destruct_rev K2) as [|[K1' [K2']]]; simplify_eq; last first. 
        * rewrite fill_app in H3. simpl in *. destruct K1'; simplify_eq.
        * simpl in *. simplify_eq.
          destruct v; simpl in *; repeat setoid_rewrite bind_Some in H2; destruct!/=.
          unshelve epose proof H1' σ' σ' [] _ _ _ _; [| |done|..].
          2:{ rewrite head_step_support_equiv_rel.
              by apply BetaS. }
          simpl in *.
          unfold is_Some in *. destruct!/=.
          rename select (to_val _ = _) into H'.
          apply of_to_val in H'. subst.
          destruct x, f0; simpl in *.
          -- simpl in *. subst. setoid_rewrite bind_Some in H. destruct!/=.
             naive_solver.
          -- induction e; simplify_eq; simpl in *; subst; simplify_eq.
             ++ setoid_rewrite bind_Some in H. destruct!/=.
                naive_solver.
             ++ case_match; subst; simplify_eq; simpl.
                case_match; last done.
                naive_solver.
          -- induction e; simpl in *; simplify_eq.
             ++ rewrite bind_Some in H. destruct!/=; naive_solver.
             ++ case_match; subst; simpl; case_match; try done.
                naive_solver.
          -- induction e; simpl in *; simplify_eq.
             ++ rewrite bind_Some in H. destruct!/=; naive_solver.
             ++ case_match; subst; simpl; case_match; try done; first naive_solver.
                simpl. case_match; subst; first naive_solver.
                simpl in *; by case_match. 
      + unshelve epose proof (fill_to_val K2 _ _) as ->; [|by erewrite <-H|].
        simpl in *. simplify_eq.
        unshelve epose proof H1' σ' σ' [] _ _ _ _; [| |done|..].
        2:{ rewrite head_step_support_equiv_rel.
            by apply BetaS.
        }
        simpl in *.
        by eapply subst_to_val_change'.
    - destruct (list_destruct_rev K) as [|[K1[K2]]]; simplify_eq.
      rewrite fill_app in H3.
      destruct K1; simplify_eq; simpl in *; simplify_eq.
      destruct (list_destruct_rev K2) as [|[K1' [K2']]]; simplify_eq; last first.
      * rewrite fill_app in H3; simpl in *; destruct K1'; simplify_eq.
      * simpl in *. simplify_eq.
        destruct v; simpl in *; repeat setoid_rewrite bind_Some in H2; destruct!/=.
        eapply urn_subst_equal_unique in H; last apply urn_subst_equal_obv; last first.
        { by eapply urn_subst_is_simple. }
        subst. 
        unshelve epose proof H1' ({|heap:=∅; urns:=urns_subst_f_to_urns f|}) ({|heap:=∅; urns:=urns_subst_f_to_urns f|}) [] _ _ _ _; [| |done|..].
        2:{ rewrite head_step_support_equiv_rel.
            eapply IfTrueS.
            intros ? H .
            simpl in *.
            apply urns_subst_f_to_urns_unique_valid in H.
            by subst. 
        }
        done. 
    - destruct (list_destruct_rev K) as [|[K1[K2]]]; simplify_eq.
      rewrite fill_app in H3.
      destruct K1; simplify_eq; simpl in *; simplify_eq.
      destruct (list_destruct_rev K2) as [|[K1' [K2']]]; simplify_eq; last first.
      * rewrite fill_app in H3; simpl in *; destruct K1'; simplify_eq.
      * simpl in *. simplify_eq.
        destruct v; simpl in *; repeat setoid_rewrite bind_Some in H2; destruct!/=.
        eapply urn_subst_equal_unique in H; last apply urn_subst_equal_obv; last first.
        { by eapply urn_subst_is_simple. }
        subst. 
        unshelve epose proof H1' ({|heap:=∅; urns:=urns_subst_f_to_urns f|}) ({|heap:=∅; urns:=urns_subst_f_to_urns f|}) [] _ _ _ _; [| |done|..].
        2:{ rewrite head_step_support_equiv_rel.
            eapply IfFalseS.
            intros ? H .
            simpl in *.
            apply urns_subst_f_to_urns_unique_valid in H.
            by subst. 
        }
        done. 
    - destruct (list_destruct_rev K) as [|[K1[K2]]]; simplify_eq.
      rewrite fill_app in H3.
      destruct K1; simplify_eq; simpl in *; simplify_eq.
      destruct (list_destruct_rev K2) as [|[K1' [K2']]]; simplify_eq; last first.
      { rewrite fill_app in H3. destruct K1'; simplify_eq. }
      simpl in *. simplify_eq.
      destruct v; repeat setoid_rewrite bind_Some in H2; destruct!/=. 
      unshelve epose proof H1' σ' σ' [] _ _ _ _ as IHv'; [| |done| |].
      2:{ rewrite head_step_support_equiv_rel. apply CaseLS. }
      done. 
    - destruct (list_destruct_rev K) as [|[K1[K2]]]; simplify_eq.
      rewrite fill_app in H3.
      destruct K1; simplify_eq; simpl in *; simplify_eq.
      destruct (list_destruct_rev K2) as [|[K1' [K2']]]; simplify_eq; last first.
      { rewrite fill_app in H3. destruct K1'; simplify_eq. }
      simpl in *. simplify_eq.
      induction v; repeat setoid_rewrite bind_Some in H2; destruct!/=. 
      unshelve epose proof H1' σ' σ' [] _ _ _ _; [| |done| |].
      2:{ rewrite head_step_support_equiv_rel. apply CaseRS. }
      done. 
  }
  by eapply value_promote_preserves_atomicity_empty_context.
Qed. 

                     
