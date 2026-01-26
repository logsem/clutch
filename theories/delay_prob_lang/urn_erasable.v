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
    pose proof urns_f_valid_exists m' as Hexists.
    destruct Hexists as [f Hexists].
    assert (urns_f_distr m f > 0) as Hpos'.
    { rewrite -H. rewrite dbind_pos.
      setoid_rewrite urns_f_distr_pos.
      naive_solver. }
    rewrite urns_f_distr_pos in Hpos'.
    erewrite urns_f_valid_support; last done. 
    by erewrite urns_f_valid_support.
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

  Lemma complete_split_urn_erasable (m:gmap loc urn) u lis (N:nat):
  NoDup lis ->
  m!!u=Some (list_to_set lis) ->
  length lis = S N ->
  urn_erasable (dunifP N ≫= (λ n, (match (lis)!!(fin_to_nat n) with
                     | Some y => dret (<[u:={[y]}]> m)
                     | None => dzero
                                   end ))) m.
  Proof.
    rewrite /urn_erasable.
    intros. rewrite -dbind_assoc'. by erewrite urns_f_distr_split.
  Qed. 
End urn_erasable_functions.
