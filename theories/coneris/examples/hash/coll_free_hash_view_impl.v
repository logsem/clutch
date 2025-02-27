From iris.algebra Require Import gset_bij.
From coneris.coneris Require Export coneris coll_free_hash_view_interface.

Set Default Proof Using "Type*".

(** An implementation of a collision-free hash view*)

Section hash_view_impl.
  Context `{Hcon:conerisGS Σ, 
              HinG: inG Σ (gset_bijR nat nat)}.
  
  Definition hash_view_auth m γ := (own γ (gset_bij_auth (DfracOwn 1) (map_to_set pair m)))%I.
  Definition hash_view_frag k v γ := (own γ (gset_bij_elem k v)).

  Lemma hash_view_auth_coll_free m γ2:
    hash_view_auth m γ2 -∗ ⌜coll_free m⌝.
  Proof.
    rewrite /hash_view_auth.
    iIntros "H".
    iDestruct (own_valid with "[$]") as "%H".
    rewrite gset_bij_auth_valid in H.
    iPureIntro.
    intros k1 k2 H1 H2 H3.
    destruct H1 as [v1 K1].
    destruct H2 as [v2 H2].
    assert (v1 = v2) as ->; first by erewrite !lookup_total_correct in H3.
    unshelve epose proof (H k1 v2 _) as [_ H']; first by rewrite elem_of_map_to_set_pair.
    unshelve epose proof (H' k2 _) as ->; last done.
    by rewrite elem_of_map_to_set_pair.
  Qed.

  Lemma hash_view_auth_duplicate_frag m n b γ2:
    m!!n=Some b -> hash_view_auth m γ2 -∗ hash_view_auth m γ2 ∗ hash_view_frag n b γ2.
  Proof.
    iIntros (Hsome) "Hauth".
    rewrite /hash_view_auth/hash_view_frag.
    rewrite -own_op.
    rewrite -core_id_extract; first done.
    apply bij_view_included.
    rewrite elem_of_map_to_set.
    naive_solver.
  Qed.
  
  Lemma hash_view_auth_frag_agree m γ2 k v:
    hash_view_auth m γ2  ∗ hash_view_frag k v γ2 -∗
    ⌜m!!k=Some v⌝.
  Proof.
    rewrite /hash_view_auth/hash_view_frag.
    rewrite -own_op.
    iIntros "H".
    iDestruct (own_valid with "[$]") as "%H".
    rewrite bij_both_valid in H.
    destruct H as [? H].
    rewrite elem_of_map_to_set in H.
    iPureIntro.
    destruct H as (?&?&?&?).
    by simplify_eq.
  Qed.

  Lemma hash_view_auth_insert m n x γ:
    m!!n=None ->
    Forall (λ m : nat, x ≠ m) (map (λ p : nat * nat, p.2) (map_to_list m)) ->
    hash_view_auth m γ ==∗
    hash_view_auth (<[n:=x]> m) γ ∗ hash_view_frag n x γ.
  Proof.
    iIntros (H1 H2) "H".
    rewrite /hash_view_auth/hash_view_frag.
    rewrite -own_op.
    iApply own_update; last done.
    rewrite -core_id_extract; last first.
    { apply bij_view_included. rewrite elem_of_map_to_set.
      eexists _, _; split; last done.
      apply lookup_insert.
    }
    etrans; first apply gset_bij_auth_extend; last by rewrite map_to_set_insert_L.
    - intros b. rewrite elem_of_map_to_set; intros (?&?&?&?).
      simplify_eq.
    - intros a. rewrite elem_of_map_to_set; intros (?&?&?&?).
      simplify_eq.
      rewrite Forall_map in H2.
      rewrite Forall_forall in H2.
      unfold not in H2.
      eapply H2; [by erewrite elem_of_map_to_list|done].
  Qed.
End hash_view_impl.



Class hvG1 Σ := {hvG1_gsetbijR :: inG Σ (gset_bijR nat nat)}. 
Program Definition hv_impl `{!conerisGS Σ} : hash_view :=
  {|
    hvG := hvG1;
    hv_name := gname;
    hv_auth _ m γ := hash_view_auth m γ;
    hv_frag _ k v γ := hash_view_frag k v γ
  |}.
Next Obligation.
  rewrite /hash_view_auth.
  iIntros (??????) "H1 H2".
  iCombine "H1 H2" gives "%H".
  rewrite gset_bij_auth_dfrac_op_valid in H.
  destruct H as [? _].
  cbv in H. done.
Qed.
Next Obligation.
  rewrite /hash_view_auth.
  iIntros. iApply own_alloc.
  by rewrite gset_bij_auth_valid.
Qed.
Next Obligation.
  simpl.
  iIntros.
  by iApply hash_view_auth_coll_free.
Qed.
Next Obligation.
  simpl. iIntros.
  by iApply hash_view_auth_duplicate_frag.
Qed.
Next Obligation.
  simpl. iIntros.
  by iApply hash_view_auth_frag_agree.
Qed.
Next Obligation.
  simpl. iIntros (????????) "H1 H2".
  iCombine "H1 H2" gives "%H".
  by apply gset_bij_elem_agree in H.
Qed.
Next Obligation.
  simpl.
  iIntros.
  by iApply hash_view_auth_insert.
Qed.
