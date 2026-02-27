From Stdlib Require Import Reals Psatz.
From stdpp Require Import gmap countable.
From clutch.delay_prob_lang Require Import lang metatheory.
From clutch.prob Require Export couplings distribution mdp.

Section urn_erasable.
  Definition urn_erasable (μ : distr (gmap loc urn)) m:=
     (μ ≫= urns_f_distr) = urns_f_distr m.
    
  Lemma urn_erasable_dbind (μ1 : distr _) (μ2 : _ → distr (_)) σ:
    urn_erasable μ1 σ → (∀ σ', μ1 σ' > 0 → urn_erasable (μ2 σ') σ') → urn_erasable (μ1 ≫= μ2) σ.
  Proof.
    intros H1 H2.
    rewrite /urn_erasable.
    intros. rewrite -dbind_assoc'.
    erewrite <-H1. rewrite /dmap.
    apply dbind_eq; last naive_solver.
    intros. by apply H2.
  Qed.

  Lemma urn_erasable_dbind_predicate `{Countable A} (μ : distr _)  μ1 μ2 σ (f: A → bool):
    SeriesC μ = 1 →
    urn_erasable μ1 σ →
    urn_erasable μ2 σ →
    urn_erasable (dbind (λ x, if f x then μ1 else μ2) μ) σ.
  Proof.
    rewrite /urn_erasable.
    intros Hsum H1 H2. rewrite -dbind_assoc'.
    apply distr_ext. intros v.
    rewrite {1}/dbind{1}/dbind_pmf{1}/pmf/=.
    erewrite (SeriesC_ext _ (λ a : A, μ a *  urns_f_distr σ v)).
    { erewrite SeriesC_scal_r. rewrite Hsum. apply Rmult_1_l. }
    intros. rewrite /dmap in H1 H2. case_match.
    - by rewrite H1.
    - by rewrite H2.
  Qed.

  Lemma urn_erasable_same_support_set μ m:
    urn_erasable μ m ->
    ∀ m', μ m' > 0 -> urns_support_set m' = urns_support_set m.
  Proof.
    rewrite /urn_erasable.
    intros H m' Hpos.
    pose proof urns_f_distr_witness m' as Hexists.
    destruct Hexists as [f Hexists].
    assert (urns_f_distr m f > 0) as Hpos'.
    { rewrite -H. rewrite dbind_pos.
      naive_solver. }
    apply urns_f_distr_pos in Hpos', Hexists.
    apply urns_f_valid_support in Hpos', Hexists.
    set_solver.
  Qed. 

End urn_erasable.

Section urn_erasable_functions.

  Lemma dret_urn_erasable σ:
    urn_erasable (dret σ) σ.
  Proof.
    intros.
    rewrite /urn_erasable.
    intros. rewrite dret_id_left'. done.
  Qed.
 
  Lemma complete_split_urn_erasable (m:gmap loc urn) u s :
  s ≠ ∅ ->
  m!!u=Some (urn_unif s) ->
  urn_erasable (unif_set s ≫=  (λ y, dret (<[u:= urn_unif {[y]}]> m))) m.
  Proof.
    rewrite /urn_erasable.
    intros. rewrite -dbind_assoc'. by erewrite urns_f_distr_split.
  Qed.

  Lemma two_split_urn_erasable m u s1 s2 s (H:(0<=size s1/size s<=1)%R):
    s1≠ ∅ ->
    s2≠ ∅ ->
    s1 ##s2 ->
    s1∪s2 = s ->
    m!!u=Some (urn_unif s)->
    urn_erasable (dmap (λ b, if b then (<[u:= urn_unif s1]> m) else (<[u:= urn_unif s2]> m)) (biased_coin _ H)) m.
  Proof.
    intros Hnonempty1 Hnonempty2 Hdisjoint Hunion Hlookup.
    rewrite /urn_erasable.
    rewrite /dmap -dbind_assoc'.
    apply distr_ext.
    intros f.
    replace (m) with (<[u:=urn_unif s]> (delete u m)) at 1; last first. 
    { apply map_eq.
      intros u'.
      destruct (decide (u=u')); subst; by simplify_map_eq.
    }
    rewrite urns_f_distr_insert; simpl; simplify_map_eq; try done; last by apply union_positive_l_alt_L.
    rewrite dbind_comm.
    replace (urns_f_distr_compute_distr _) with (dbind (λ b, if b then urns_f_distr_compute_distr (urn_unif s1) else urns_f_distr_compute_distr (urn_unif s2)) (biased_coin (size s1/size (s1 ∪ s2)) H)); last first.
    - apply distr_ext.
      intros x.
      destruct (decide (x∈s1)).
      + rewrite {1}/dbind/dbind_pmf{1}/pmf. rewrite SeriesC_finite_foldr/=.
        rewrite Rplus_0_r.
        rewrite /biased_coin/biased_coin_pmf{1 3}/pmf.
        rewrite /urns_f_distr_compute_distr/urns_f_distr_compute/pmf.
        rewrite bool_decide_eq_true_2; last done.
        rewrite bool_decide_eq_false_2; last set_solver.
        rewrite bool_decide_eq_true_2; last set_solver.
        rewrite Rmult_0_r Rplus_0_r.
        rewrite Rdiv_def.
        rewrite Rmult_comm.
        rewrite -Rmult_assoc.
        replace (/_ * _) with 1%R; first lra.
        rewrite Rmult_comm.
        rewrite Rmult_inv_r; first lra.
        apply not_0_INR.
        intros Hcontra.
        apply size_empty_inv in Hcontra.
        rewrite leibniz_equiv_iff in Hcontra.
        naive_solver.
      + destruct (decide (x∈s2)).
        * rewrite {1}/dbind/dbind_pmf{1}/pmf. rewrite SeriesC_finite_foldr/=.
          rewrite Rplus_0_r.
          rewrite /biased_coin/biased_coin_pmf{1 3}/pmf.
          rewrite /urns_f_distr_compute_distr/urns_f_distr_compute/pmf.
          rewrite bool_decide_eq_false_2; last set_solver.
          rewrite bool_decide_eq_true_2; last done.
          rewrite bool_decide_eq_true_2; last set_solver.
          rewrite Rmult_0_r Rplus_0_l.
          rewrite Rdiv_def.
          rewrite -(Rdiv_diag (size s1 + size s2)); last first.
          -- rewrite -plus_INR.
             apply not_0_INR.
             assert (0<size s1)%nat; last lia.
             destruct (size s1) eqn:K; last lia.
             exfalso.
             apply size_empty_inv in K.
             rewrite leibniz_equiv_iff in K. naive_solver.
          -- rewrite Rdiv_def.
             rewrite Rmult_plus_distr_r.
             rewrite size_union; last done.
             rewrite -plus_INR.
             rewrite Rplus_minus_l.
             rewrite Rmult_comm.
             rewrite -Rmult_assoc.
             rewrite Rinv_l; first lra.
             apply not_0_INR.
             intros K.
             apply size_empty_inv in K.
             set_solver.
        * rewrite {1}/dbind/dbind_pmf{1}/pmf. rewrite SeriesC_finite_foldr/=.
          rewrite Rplus_0_r.
          rewrite /biased_coin/biased_coin_pmf{1 3}/pmf.
          rewrite /urns_f_distr_compute_distr/urns_f_distr_compute/pmf.
          rewrite bool_decide_eq_false_2; last set_solver.
          rewrite bool_decide_eq_false_2; last done.
          rewrite bool_decide_eq_false_2; last set_solver.
          lra. 
    - rewrite -dbind_assoc'. apply dbind_pmf_ext; last done; last by apply distr_ext.
      intros []?; rewrite dret_id_left -/(urns_f_distr _);
      rewrite -insert_delete_insert;
        rewrite urns_f_distr_insert; try rewrite Hlookup/=; simplify_map_eq; try done; by rewrite dbind_comm.
  Qed. 
End urn_erasable_functions.
