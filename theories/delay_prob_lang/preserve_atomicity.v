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
    - admit.
    - admit.
    - admit.
    - admit.
  }
Admitted. 
