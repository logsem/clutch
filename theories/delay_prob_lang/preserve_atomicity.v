From Stdlib Require Import Reals Psatz.
From clutch.delay_prob_lang Require Import tactics notation urn_subst metatheory.
From clutch.delay_prob_lang Require Export lang.
From clutch.prob Require Import distribution.
Set Default Proof Using "Type*".

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
  inversion H4.
  - 
Admitted. 
