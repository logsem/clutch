(** * Exact time credit accounting for Quicksort *)
From clutch.ert_logic Require Import ert_weakestpre lifting ectx_lifting primitive_laws expected_time_credits cost_models problang_wp proofmode ert_rules.
From clutch.lib Require Import utils.
From iris.proofmode Require Export tactics.
From Coq Require Export Reals Psatz.
From stdpp Require Import sorting.
Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Set Default Proof Using "Type*".
Require Import Lra.


Section lib.
  (** Lemmas: Move or eliminate *)

  Lemma easy_fix_eq:
    ∀ (A : Type) (R : A → A → Prop) (Rwf : well_founded R) (P : A → Type)
      (F : ∀ x : A, (∀ y : A, R y x → P y) → P x),
      ∀ x : A, Fix Rwf P F x = F x (λ (y : A) (_ : R y x), Fix Rwf P F y).
  Proof.
    intros. apply Init.Wf.Fix_eq.
    intros. assert (f = g) as ->; last done.
    apply functional_extensionality_dep => ?.
    apply functional_extensionality_dep => ?. done.
  Qed.


  #[local] Definition fin_transport_lemma (A B : nat) : (0 < B)%nat -> (A < B)%nat -> (A < (S (B - 1)))%nat.
  Proof. intros. lia. Qed.

   (* Source of many deeply annoying lemmas involving fin_enum: can't directly pull off the last element *)
   Fixpoint fin_inj_incr (n : nat) (i : fin n) : (fin (S n)) :=
     match i with
       0%fin => 0%fin
     | (FS _ i) => FS (fin_inj_incr _ i)
     end.

   Lemma fin_inj_incr_to_nat (n : nat) (i : fin n) : fin_to_nat i = fin_to_nat (fin_inj_incr n i).
   Proof.
     induction i as [|i' IH]; [done|].
     simpl. f_equal. done.
   Qed.



   Lemma fmap_compat `{A: Type} `{B: Type} f : list_fmap A B f = (fmap f).
   Proof. rewrite /fmap. done. Qed.

   Lemma fin_inj_FS_comm (n : nat) (l : list (fin n)) :
     FS <$> (fin_inj_incr _ <$> l) = fin_inj_incr _ <$> (FS <$> l).
   Proof.
     (* Fmapping this over a list only matters for giving us funext *)
     rewrite -list_fmap_compose.
     rewrite -list_fmap_compose.
     apply Forall_fmap_ext, Forall_true.
     eauto.
    Qed.

   (* Allows us to pull off the last element of a fin_enum, leaving a smaller fin_enum *)
   Lemma fin_enum_snoc_rec (n : nat) :
     (fin_enum (S n)) = (fin_inj_incr n <$> fin_enum n) ++ [(nat_to_fin (Nat.lt_succ_diag_r n) : fin (S n))%fin].
   Proof.
     induction n as [|n' IH]; [done|].
     rewrite {1}/fin_enum.
     rewrite {1}/fin_enum in IH.
     rewrite IH.
     rewrite fmap_app app_comm_cons.
     f_equal; last first.
     - simpl.
       do 3 f_equal.
       apply proof_irrelevance.
     - rewrite /fin_enum /=.
       f_equal.
       rewrite fmap_compat.
       rewrite fin_inj_FS_comm.
       done.
   Qed.
End lib.



Section sorting.
  (** Definitions related to specifying a sorting function *)

  Context {A} (R : relation A) `{∀ x y, Decision (R x y)} `{!TotalOrder R} `{Inhabited A}.

  Definition rank (L : list A) (x : A) : nat := (length (List.filter (fun y => bool_decide (strict R y x)) L)).


  Lemma perm_filter `{S : Type} L1 L2 (f : S -> bool) : (L1 ≡ₚ L2) -> (List.filter f L1) ≡ₚ (List.filter f L2).
  Proof.
    generalize dependent L2.
    induction L1 as [|L' LS IH].
    - simpl; intros ? H2.
      apply Permutation_nil in H2.
      by rewrite H2 /=.
    - intros L2.
      intros HPerm.
      assert (Hex : exists (L2A L2B : list S), L2 = L2A ++ [L'] ++ L2B).
      { simpl. apply in_split.
        eapply Permutation_in; first eapply HPerm.
        apply in_eq.
      }
      destruct Hex as [Hex1 [Hex2 ->]].

      rewrite /= -Permutation_middle in HPerm.
      apply Permutation_cons_inv in HPerm.

      do 2 rewrite List.filter_app.
      simpl.
      destruct (f L'); simpl.
      + rewrite -Permutation_middle.
        apply Permutation_skip.
        rewrite -List.filter_app.
        by apply IH.
      + rewrite -List.filter_app.
        by apply IH.
  Qed.


  Lemma rank_inv_perm L1 L2 x : (L1 ≡ₚ L2) -> rank L1 x = rank L2 x.
  Proof. intros; rewrite /rank. by apply Permutation_length, perm_filter. Qed.

  Lemma rank_to_sorted L x : rank (merge_sort R L) x = rank L x.
  Proof. apply rank_inv_perm, merge_sort_Permutation. Qed.

  Definition index_to_rank (L : list A) : nat -> nat := rank L ∘ (fun i => L !!! i).




  (** Permutations over the index space *)

  (* Separate definition so it stops getting unfolded *)
  Definition index_space N : list nat := (seq 0%nat N).

  Lemma index_space_emp : (index_space 0) = [].
  Proof. by rewrite /index_space /=. Qed.

  Lemma index_space_snoc N : (index_space (S N)) = (index_space N) ++ [N].
  Proof. by rewrite /index_space seq_S /=. Qed.

  Lemma index_space_cons N : (index_space (S N)) = 0 :: (fmap S (index_space N)).
  Proof. by rewrite /index_space /= fmap_S_seq. Qed.

  Lemma index_space_unfold N : index_space N = (seq 0%nat N).
  Proof. by rewrite /index_space /=. Qed.

  Opaque index_space.







  (** List reversal permutation *)
  Lemma equal_perm `{T : Type} (L1 L2: list T) : (L1 = L2) -> (L1 ≡ₚ L2).
  Proof. intros; simplify_eq; eauto. Qed.

  Definition reverse_order `{T : Type} (L : list T) (i : nat) : nat := (length L - 1 - i)%nat.

  Lemma reverse_perm N : (index_space N) ≡ₚ (reverse_order (index_space N) <$> (index_space N)).
  Proof.
    induction N as [|N' IH].
    - simpl. constructor.
    - rewrite /reverse_order seq_length.
      rewrite /reverse_order seq_length in IH.
      rewrite {2}index_space_cons fmap_cons.
      rewrite {1}index_space_snoc.
      rewrite -Permutation_cons_append.
      replace (S N' - 1 - 0) with N' by lia.
      constructor.
      rewrite {1}IH.
      apply equal_perm.
      rewrite -list_fmap_compose.
      apply list_fmap_ext.
      intros ? ? H1.
      rewrite lookup_seq in H1.
      destruct H1 as [H1 H2].
      simpl. lia.
  Qed.



  (** Index to list permutation on index_space *)

  Lemma list_access_perm (L : list A) : (λ i : nat, L !!! i) <$> index_space (length L) ≡ₚ L.
  Proof.
    induction L as [|L' LS IH] using rev_ind.
    - by rewrite /= index_space_emp /=.
    - rewrite app_length /= Nat.add_1_r index_space_snoc.
      rewrite fmap_app /=.
      apply Permutation_app.
      + rewrite -{3}IH.
        apply equal_perm.
        apply list_fmap_ext.
        intros i x HIn.
        apply lookup_total_app_l.

        replace x with (index_space (length LS) !!! i); last by apply list_lookup_total_correct.
        rewrite index_space_unfold.
        rewrite index_space_unfold in HIn.
        apply lookup_seq in HIn; destruct HIn.
        rewrite lookup_total_seq_lt; lia.
      + rewrite list_lookup_total_middle; done.
  Qed.

  Lemma fmap_perm `{T : Type} `{S : Type} (L1 L2 : list T) (f : T -> S) : (L1 ≡ₚ L2) -> (f <$> L1 ≡ₚ f <$> L2).
  Proof. intros. rewrite H1. done. Qed.

  Lemma index_to_rank_nat_perm_sorted (L : list A) :
    List.NoDup L ->
    Sorted R L ->
    (index_space (length L)) ≡ₚ rank L <$> L.
  Proof.
    intros HU HS.
    assert (HS' : StronglySorted R L).
    { apply Sorted_StronglySorted; last apply HS. by destruct TotalOrder0 as [[[? ?] ?] ?]. }
    clear HS.

    apply equal_perm.

    induction L as [|L0 L' IH] using rev_ind.
    - rewrite /= index_space_emp. done.
    - rewrite app_length /= Nat.add_1_r index_space_snoc.
      rewrite IH; [ | eapply NoDup_app_remove_r, HU |eapply StronglySorted_app_inv_l, HS'].
      clear IH.
      rewrite fmap_app.
      f_equal.
      + apply list_fmap_ext.
        intros i x Hi.
        rewrite /rank.
        rewrite List.filter_app app_length.
        simpl.
        rewrite bool_decide_false; [rewrite /=; lia| ].
        assert (R x L0).
        { eapply elem_of_StronglySorted_app; eauto.
          - eapply elem_of_list_lookup_2. eauto.
          - by apply elem_of_list_singleton.
        }
        intros Hcont.
        apply strict_spec_alt in Hcont.
        assert (HT : Trichotomy (strict R)); first by destruct TotalOrder0.
        assert (HO : PartialOrder R); first by destruct TotalOrder0.
        destruct HO as [[HRef Htrans] Has].
        destruct Hcont as [ ? ? ].
        rewrite /AntiSymm in Has.
        auto.

      + simpl; f_equal.
        induction L' as [|L'0 L's IH].
        * rewrite /rank /=.
          rewrite bool_decide_false; [by simpl|].
          intros [ ? ? ]. auto.
        * simpl.
          rewrite IH.
          2: {
            rewrite -app_comm_cons in HU.
            apply NoDup_cons_iff in HU.
            by destruct HU.
          }
          2: {
            rewrite -app_comm_cons in HS'.
            apply StronglySorted_inv in HS'.
            by destruct HS'.
          }
          replace (L'0 :: L's ++ [L0]) with ([L'0] ++ (L's ++ [L0])); last by simpl.
          rewrite /rank.
          symmetry.
          rewrite List.filter_app app_length.
          replace ( length (List.filter (λ y : A, bool_decide (strict R y L0)) [L'0]) ) with 1; [lia|].
          simpl.
          rewrite bool_decide_true; [done|].

          apply strict_spec_alt.
          split.
          -- eapply elem_of_StronglySorted_app; first eapply HS'; apply elem_of_list_here.
          -- rewrite /not.
             intros ->.
             apply NoDup_remove in HU.
             destruct HU  as [? Hcont].
             apply Hcont, in_eq.
  Qed.


  Lemma index_to_rank_nat_perm (L : list A) :
    List.NoDup L ->
    (index_space (length L)) ≡ₚ (index_to_rank L) <$> (index_space (length L)).
  Proof.
    intros Hnodup.
    rewrite /index_to_rank.
    rewrite list_fmap_compose.
    rewrite fmap_perm; last apply list_access_perm.
    rewrite fmap_perm; last (symmetry; apply (merge_sort_Permutation R)).
    rewrite (list_fmap_ext (rank L) (rank (merge_sort R L))); last (intros; symmetry; apply rank_to_sorted).
    replace (length L) with (length (merge_sort R L)); last apply Permutation_length, merge_sort_Permutation.
    apply index_to_rank_nat_perm_sorted; last (apply Sorted_merge_sort, trichotomy_total).
    eapply (Permutation_NoDup _ Hnodup).
    Unshelve.
    symmetry.
    apply merge_sort_Permutation.
  Qed.

  Lemma fold_R_fin_perm f :
    forall (g : nat -> nat) (L : list nat),
      (L ≡ₚ (map g L) -> (foldr (Rplus ∘ f) 0%R $ L) = (foldr (Rplus ∘ f) 0%R $ map g $ L)).
  Proof.
    intros g L Hp.
    eapply (foldr_permutation (=) (Rplus ∘ f) 0%R L (map g L) _ Hp).
    Unshelve.
    intros; simpl; lra.
  Qed.

End sorting.





Section qs_time.
  (** Defines the Quicksort recurrence relation *)

  (* Tight bounding argument necessitates the pivot take time An+B *)
  Definition tc_pivot_lin (A B : R) (n : nat) : R := (A*n+B)%R.

  Definition tc_pivot_lin_nonneg A B n : (0 <= A)%R -> (0 <= B)%R -> (0 <= tc_pivot_lin A B n)%R.
  Proof.
    intros. rewrite /tc_pivot_lin.
    apply Rplus_le_le_0_compat; try lra.
    apply Rmult_pos_nat_r; done.
  Qed.


  Definition tc_base : R := 1%R.

  Lemma tc_base_nonneg : (0%R <= tc_base)%R.
  Proof. rewrite /tc_base. lra. Qed.

  Opaque tc_base.



  (* tc_quicksort(len) = (1/len) + 2 * sum(i=0 to len-1)(tc_quicksort i) *)
  Definition tc_quicksort (A B : R) (len : nat) : R.
  refine (@Fix nat _ (Wf.measure_wf lt_wf (fun x => x)) (fun _ => R)
          (fun len qf_rec =>
           match len with
               0%nat   => tc_base
             | (S n) => ((tc_pivot_lin A B len) +
                          2 * (foldr Rplus 0%R $
                                map (fun n => (qf_rec (fin_to_nat n) _)) $
                                fin_enum len) / len )%R
           end) len).
  Proof. rewrite /Wf.MR. apply fin_to_nat_lt. Defined.


  Lemma tc_quicksort_aux A B len :
    tc_quicksort A B len =
      match len with
        0%nat   => tc_base
      | (S _) => ((tc_pivot_lin A B len)
                  + 2 * (foldr Rplus 0%R $
                        map (fun n => tc_quicksort A B (fin_to_nat n)) $
                        (fin_enum len) ) / len)%R
      end.
  Proof. rewrite /tc_quicksort easy_fix_eq; done. Qed.


  (* An alternative to proving all of that fin_enum stuff might be to just define the seq version
     directly in the refine using a dependent pattern match. *)
  Lemma tc_quicksort_unfold A B len :
    tc_quicksort A B len =
      match len with
        0%nat   => tc_base
      | (S _) => ((tc_pivot_lin A B len)
                  + 2 * (foldr Rplus 0%R $
                        map (fun n => tc_quicksort A B n) $
                        seq 0%nat len) / len)%R
      end.
  Proof.
    rewrite tc_quicksort_aux.
    destruct len; [done|].
    do 3 f_equal.
    generalize (S len); intros N; clear.
    induction N as [|N' IH]; [done|].
    Opaque seq fin_enum.
    rewrite seq_S map_app foldr_snoc /=.
    rewrite fin_enum_snoc_rec map_app foldr_snoc /=.
    rewrite foldr_comm_acc; last (intros; simpl; lra).
    rewrite foldr_comm_acc; last (intros; simpl; lra).
    rewrite -IH.
    f_equal.
    + by rewrite fin_to_nat_to_fin.
    + rewrite map_map.
      do 2 f_equal.
      apply functional_extensionality; intros; simpl.
      by rewrite -fin_inj_incr_to_nat.
    Transparent seq fin_enum.
  Qed.

  Opaque tc_quicksort.





  Lemma tc_quicksort_0 A B : tc_quicksort A B 0%nat = tc_base.
  Proof. rewrite tc_quicksort_unfold. done. Qed.

  Lemma tc_quicksort_S A B n :
    (1 <= n)%nat ->
    tc_quicksort A B n = ((tc_pivot_lin A B n) + 2 * (foldr Rplus 0 $ map (fun i => ((tc_quicksort A B i))%NNR) $ seq 0%nat n)%NNR /n)%R.
  Proof. intros. rewrite tc_quicksort_unfold. destruct n; [lia|]. done. Qed.

  (* Prove this by strong induction now *)
  Lemma tc_quicksort_nonneg A B n :
    (0 <= A)%R -> (0 <= B)%R ->
    (0 <= tc_quicksort A B n)%R.
  Proof.
    intros HA HB.
    induction n as [ n' IH ] using (well_founded_induction lt_wf).
    rewrite tc_quicksort_unfold.
    destruct n' as [|n']; [apply tc_base_nonneg |].
    apply Rplus_le_le_0_compat; [apply tc_pivot_lin_nonneg; try done | ].
    apply Rmult_le_pos; [| apply Rlt_le, Rinv_0_lt_compat, pos_INR_S].
    apply Rmult_le_pos; [lra|].
    induction n' as [|n'' IH'].
    - rewrite /= tc_quicksort_0 Rplus_0_r.
      apply tc_base_nonneg.
    - rewrite seq_S.
      Opaque seq.
      rewrite map_app foldr_snoc /=.
      rewrite foldr_comm_acc; last (intros; simpl; lra).
      apply Rplus_le_le_0_compat.
      * apply IH; lia.
      * apply IH'. intros. apply IH. lia.
      Transparent seq.
  Qed.

End qs_time.


Section qs_bound.
  (** Upper bound on the tc_quicksort recurrence *)

  Lemma tc_quicksort_bound_ind n' (A B : R) (HAB : ( 0 <= B <= A)%R) :
    ((tc_quicksort A B (S n')) / (S n' + 1)%nat  <= (2* A) / (S n' + 1)%nat + (tc_quicksort A B n') / (n' + 1)%nat )%R.
  Proof.
    Opaque INR.
    remember (S n') as n.
    remember (tc_quicksort A B) as C.
    repeat rewrite Rdiv_def.
    simpl.

    etrans; last first.
    { (* Include the (B-A)/(n(n+1)) term *)
      eapply Rplus_le_compat_l.
      rewrite -(Rplus_0_l (_ * _)%R).
      eapply Rplus_le_compat_r.
      assert (Hinst: (((B - A) / (n * (n+1)) <= 0)%R)).
      { apply Rcomplements.Rle_div_l.
        - apply Rlt_gt.
          rewrite Heqn.
          pose P := (pos_INR n').
          rewrite S_INR.
          apply Rmult_lt_0_compat;lra.
        - rewrite Rmult_0_l.
          apply Rle_minus. lra.
      }
      eapply Hinst.
    }

    (* In this form, they should be equal *)
    apply Req_le.

    (* n'=0, separate proof *)
    destruct n' as [|n''].
    { simplify_eq; simpl.
      rewrite tc_quicksort_0 /=.
      rewrite Rinv_1 Rmult_1_r Rmult_1_l.
      replace (2 * A * / (INR 2))%R with A; last first.
      { repeat rewrite S_INR. rewrite INR_0. lra.  }
      rewrite Rdiv_def.
      rewrite tc_quicksort_unfold /tc_pivot_lin.
      simpl.
      rewrite INR_1 Rdiv_1_r Rplus_0_r.
      rewrite tc_quicksort_0.
      rewrite Rmult_plus_distr_r.
      repeat rewrite S_INR.
      repeat rewrite INR_0.
      lra.
    }

    (* Get rid of some n+1 denominators *)
    eapply (Rmult_eq_reg_r (INR (n + 1))); last first.
    { rewrite Nat.add_1_r S_INR. pose P:= (pos_INR n); lra. }
    rewrite Rmult_assoc Rinv_l; last first.
    { rewrite Nat.add_1_r S_INR. pose P:= (pos_INR n); lra. }
    rewrite Rmult_1_r.
    do 2 rewrite Rmult_plus_distr_r.
    rewrite Rmult_assoc Rinv_l; last first.
    { rewrite Nat.add_1_r S_INR. pose P:= (pos_INR n); lra. }
    rewrite Rmult_1_r.
    rewrite Rdiv_mult_distr.
    replace ((B - A) / INR n / (INR n + 1) * INR (n + 1))%R
       with ((B - A) / INR n)%R; last first.
    { rewrite (Rdiv_def _ (_ + _)%R).
      rewrite Rmult_assoc.
      rewrite Nat.add_1_r S_INR.
      rewrite Rinv_l; last (pose P := (pos_INR n); lra).
      lra.
    }

    (* Unfold C *)
    Opaque INR.
    rewrite HeqC Heqn.
    rewrite tc_quicksort_S; last lia.
    rewrite -Heqn -HeqC.
    Opaque seq.
    simpl.
    Transparent seq.

    (* Pull out one term from the series *)
    replace (foldr Rplus 0%R (map (λ i : nat, (C i)) (seq 0 n)))
       with (C (S n'') + (foldr Rplus 0%R (map (λ i : nat, (C i)) (seq 0 (S n'')))))%R;
      last first.
    { rewrite Heqn.
      Opaque seq.
      rewrite (seq_S (S n'')) /=.
      rewrite map_app.
      rewrite foldr_snoc.
      rewrite foldr_comm_acc; [done|].
      intros; simpl.
      lra.
      Transparent seq.
    }
    remember (foldr Rplus 0%R (map (λ i : nat, (C i)) (seq 0 (S n'')))) as SR.

    (* Remove n denominators *)
    replace (S (n'' + 1)) with n by lia.
    apply (Rmult_eq_reg_r (INR n)); last (apply not_0_INR; lia).
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_plus_distr_r.
    rewrite Rdiv_def.
    rewrite Rmult_assoc.
    rewrite Rinv_l; last (apply not_0_INR; lia).
    rewrite Rmult_1_r.
    rewrite Rmult_assoc.
    rewrite Rmult_assoc.
    rewrite (Rmult_comm (/ n)).
    rewrite -Rmult_assoc.
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_assoc.
    rewrite Rmult_assoc.
    rewrite Rmult_assoc.
    rewrite Rinv_l; last (apply not_0_INR; lia).
    rewrite Rmult_1_r.
    rewrite Rmult_assoc.
    rewrite Rinv_l; last (apply not_0_INR; lia).
    rewrite Rmult_1_r.

    (* Collect C (S n'') on the left *)
    apply (Rplus_eq_reg_l (- (tc_pivot_lin A B n * (INR n)))%R).
    rewrite -Rplus_assoc.
    rewrite Rplus_opp_l Rplus_0_l.
    rewrite -Rplus_assoc.
    apply (Rplus_eq_reg_r (- (C (S n'')) * (INR (n + 1)))%R).
    rewrite Rplus_assoc.
    rewrite Rplus_assoc.
    rewrite Rplus_assoc.
    replace (((C (S n'')) * (INR (n + 1))) + ((- (C (S n''))) * (INR (n + 1))))%R
        with (0)%R by lra.
    rewrite Rplus_0_r.
    simpl.
    rewrite Rmult_plus_distr_l.
    rewrite Rplus_comm.
    rewrite -Rplus_assoc.
    rewrite Ropp_mult_distr_l_reverse Ropp_mult_distr_r.
    rewrite Rmult_comm.
    rewrite -Rmult_plus_distr_r.
    replace ((- (INR (n + 1))) + 2)%R with (-(S n''))%R; last first.
    { rewrite S_INR.
      rewrite Nat.add_1_r S_INR.
      rewrite Heqn S_INR S_INR. lra.
    }

    (* Unfold C *)
    rewrite HeqC.
    rewrite tc_quicksort_S; last lia.
    rewrite -HeqC -HeqSR /=.

    (* Cancel the sums *)
    rewrite Rmult_plus_distr_l.

    replace ((- (INR (S n''))) * ((2 * SR) / (INR (S n''))))%R
       with ((- (INR 2) * (SR)))%R; last first.
    { rewrite -Ropp_mult_distr_l.
      rewrite -Ropp_mult_distr_l.
      f_equal.
      rewrite (Rmult_comm (INR (S n''))).
      rewrite Rmult_assoc.
      rewrite Rmult_assoc.
      rewrite Rinv_l; [|apply not_0_INR; lia].
      repeat rewrite S_INR.
      rewrite INR_0.
      lra.
    }
    rewrite Rplus_assoc.
    replace (- INR 2 * SR + 2 * SR)%R with 0%R; last first.
    { repeat rewrite S_INR. rewrite INR_0. lra. }
    rewrite Rplus_0_r.

    (* Simplify out negatives*)
    apply Ropp_eq_reg.
    rewrite Ropp_plus_distr Ropp_involutive.

    (* Expand binomial to eliminate n^2 term *)
    rewrite Heqn /=.
    rewrite /tc_pivot_lin.
    replace (((A * (INR (S (S n'')))) + B) * (INR (S (S n''))))%R
      with (((A * (INR (S (S n''))) * (INR (S (S n'')))) + B * (INR (S (S n'')))))%R; last first.
    { rewrite (S_INR (S n'')).
      rewrite Rmult_plus_distr_l.
      lra.
    }

    (* Expand the remaining (S (S n'')) terms *)
    repeat (rewrite S_INR || rewrite plus_INR || rewrite INR_0 || rewrite mult_INR).
    lra.
  Qed.


  Lemma tc_quicksort_bound_closed A B n (HAB : (0 <= B <= A)%R):
    (((tc_quicksort A B n) / (n + 1)%nat)
      <= (foldr Rplus (tc_quicksort A B 0%nat) $
          map (fun i => (2*A / (i + 1)%nat)%R) $
          seq 1%nat n))%R.
  Proof.
    Opaque seq.
    simpl.
    induction n as [|n' IH].
    { Transparent seq. simpl. rewrite INR_1. lra. Opaque seq. }
    etrans; first eapply tc_quicksort_bound_ind; first eauto.
    rewrite seq_S map_app foldr_snoc /=.
    rewrite foldr_comm_acc; last (intros; simpl; lra).
    apply Rplus_le_compat_l, IH.
    Transparent seq.
  Qed.


  (* Proof sketch for getting the classic bound without integration.

    Goal:     C(n)       <= (C(0)+ 3A) (n+1) log n
    Suffices: C(n)       <= C(0) (n+1) + 3A (n+1) log n
              C(n)/(n+1) <= C(0) + 3A log n
    Suffices:
             C(0) + sum_{i=1}^n (2A)/(i+1) <= C(0) + 3A log n
             sum_{i=1}^n (2A)/(i+1)        <= 3A log n

    By induction on n for n >= e.
    Base case:
          sum_{i=1}^i (2A)/(i+1) = 2A + A = 3A = 3A log e <= 3A log n

    Inductive case:
        Suffices:
          (sum_{i=1}^{i+1} (2A)/(i+1) - sum_{i=1}^i (2A)/(i+1)) <= (3A log (n+1)) - (3A log n)
          (2A)/(n+2) <= 3A log ((n+1)/n)
        Suffices:
          (3A)/(n+1) <= 3A log ((n+1)/n)
          1/(n+1) <= log ((n+1)/n)
          1 <= (n+1) log ((n+1)/n)
          e <= ((n+1)/n)^(n+1) = (1+1/n)^(n+1)
      The RHS decreases and has limit e.
   *)

End qs_bound.


Section qs_adv_cmp.
  (** Advanced composition for quicksort *)

  Context {A} (f : relation A) `{∀ x y, Decision (f x y)} `{!TotalOrder f} `{Inhabited A}.
  Context `[!Inject A val].


  (* Distribution, in a form which is easy to work with *)
  Definition tc_distr_def (L : list A) (CA CB : R) : nat -> R
    := fun index =>
         match L with
         | [] => tc_base
         | _ => ((tc_quicksort CA CB ∘ (index_to_rank f L)) index +
                 (tc_quicksort CA CB ∘ reverse_order (index_space (length L)) ∘ (index_to_rank f L)) index)%R
         end.

  (* Distribution, in a form which typechecks with advanced composition *)
  Definition tc_distr (L : list A) CA CB : (fin (S (Z.to_nat (length L - 1)))) -> R
    := (tc_distr_def L CA CB) ∘ fin_to_nat.


  Lemma tc_distr_nonneg L CA CB i : (0 < length L)%nat -> (0 <= CA)%R -> (0 <= CB)%R -> (0 <= tc_distr L CA CB i)%R.
  Proof.
    intros.
    rewrite /tc_distr /tc_distr_def /=.
    destruct L; first (simpl in *; lia).
    apply Rplus_le_le_0_compat; apply tc_quicksort_nonneg; done.
  Qed.


  Lemma foldr_reduction_1 (L : list A) g  :
   (List.NoDup L) ->
     (foldr (Rplus ∘ g ∘ index_to_rank f L) 0 (index_space (length L)))%R
   = (foldr (Rplus ∘ g) 0 (index_space (length L)))%R.
  Proof.
    intros.
    rewrite (fold_R_fin_perm _ (index_to_rank f L)).
    - (* generalize me? *)
      remember (index_space (length L)) as LL.
      clear HeqLL.
      remember (index_to_rank f L) as g1.
      induction LL as [|L0 L' IH].
      + simpl; lra.
      + simpl. f_equal. apply IH.
    - apply index_to_rank_nat_perm; done.
  Qed.

  Lemma foldr_reduction_2 (L : list A) g :
     (foldr (Rplus ∘ g ∘ reverse_order (index_space (length L))) 0%R (index_space (length L)))%R
   = (foldr (Rplus ∘ g) 0%R (index_space (length L)))%R.
  Proof.
    intros.
    rewrite (fold_R_fin_perm _ (reverse_order (index_space (length L)))).
    - (* generalize me *)
      remember (index_space (length L)) as LL; clear HeqLL.
      remember (reverse_order LL) as g1; clear Heqg1.
      induction LL as [|L0 L' IH].
      + simpl; done.
      + simpl. f_equal. apply IH.
    - apply reverse_perm.
  Qed.


  (* Advanced composition side condition: Turn the junk we get from the advanced composition rule back into the credit definition we have before *)
  Lemma tc_distr_equiv L CA CB :
  (0 < length L)%nat ->
  (0 <= CA)%R ->
  (0 <= CB)%R ->
  (List.NoDup L) ->
  (SeriesC (λ n : fin (S (Z.to_nat (length L - 1))), 1 / S (Z.to_nat (length L - 1)) * tc_distr L CA CB n))%R =
        (2 * foldr Rplus 0 (map (λ n : nat, tc_quicksort CA CB n) (index_space (length L))) / (length L))%R.
  Proof.
    intros Hlength ? ? Hunique.
    assert (Hlength_nz : INR (length L) ≠ 0%R).
    { symmetry. apply Rlt_not_eq. rewrite -INR_0. by apply lt_INR. }

    (* 1. Simplify everything that we can, and get rid of the / (S length xs') terms *)
    apply (Rmult_eq_reg_r (length L)); last done.

    (* Cancel on the RHS *)
    repeat rewrite Rdiv_def.
    rewrite Rmult_assoc Rinv_l; last done.
    rewrite Rmult_1_r.
    (* Cancel on the LHS *)
    rewrite Rmult_comm.
    rewrite SeriesC_scal_l.
    rewrite -Rmult_assoc Rmult_1_l.
    simpl length.

    replace ((length L) * (/ (S (Z.to_nat (Z.of_nat (length L) - 1)))))%R with 1%R; last first.
    { replace (S (Z.to_nat (Z.of_nat (length L) - 1))) with (length L) by lia.
      rewrite Rinv_r; done.
    }
    rewrite Rmult_1_l.


    (* 2. Convert the series into a foldr, simpl *)
    rewrite SeriesC_finite_foldr.
    rewrite /tc_distr.
    replace (foldr (Rplus ∘ (tc_distr_def L CA CB ∘ fin_to_nat)) 0%R (enum (fin (S (Z.to_nat (Z.of_nat (length L) - 1))))))
      with  (foldr (Rplus ∘ tc_distr_def L CA CB) 0%R (index_space (length L)));
      last first.
    { remember (tc_distr_def _ _ _) as g.
      remember (S (Z.to_nat (Z.of_nat (length L) - 1))) as l.
      replace (length L) with l; last (simplify_eq; lia).
      clear.
      induction l.
      - simpl. done.
      - rewrite index_space_snoc.
        rewrite foldr_app.
        Opaque enum. simpl. Transparent enum.
        replace (foldr (Rplus ∘ g) (g l + 0)%R (index_space l))%R with (g l + foldr (Rplus ∘ g) (0)%R (index_space l))%R; last first.
        { (* whatever *)
          remember (index_space l) as LL; clear.
          induction LL as [|LL0 LL' IH].
          - simpl. done.
          - simpl. rewrite -IH. lra.
        }
        rewrite IHl.
        rewrite /enum /fin_finite.
        rewrite fin_enum_snoc_rec.
        rewrite foldr_app.
        simpl.
        rewrite fin_to_nat_to_fin.

        replace (foldr (Rplus ∘ (λ index : fin (S l), g (fin_to_nat index))) (g l + 0)%R (fin_inj_incr l <$> fin_enum l))%R
          with (g l + foldr (Rplus ∘ (λ index : fin (S l), g (fin_to_nat index))) 0%R (fin_inj_incr l <$> fin_enum l))%R;
          last first.
        { (* whatever *)
          remember (fin_inj_incr _ <$> _ ) as LL; clear.
          induction LL as [|LL0 LL' IH].
          - simpl. done.
          - simpl. rewrite -IH. lra.
        }
        f_equal.
        replace (foldr (Rplus ∘ (λ index : fin (S l), g (fin_to_nat index))) 0%R (fin_inj_incr l <$> fin_enum l))%R
           with (foldr (Rplus ∘ (λ index : fin (S l), g (fin_to_nat index)) ∘ fin_inj_incr l ) 0%R (fin_enum l))%R;
          last first.
        { remember (fin_enum _) as LL.
          clear.
          induction LL as [|LL0 LL' IH].
          - simpl. done.
          - simpl. rewrite -IH. lra.
        }
        apply foldr_ext; eauto.
        intros; simpl.
        by rewrite fin_inj_incr_to_nat.
    }

    (* 3. Split the distr series into two sums *)
    replace (foldr (Rplus ∘ tc_distr_def L CA CB) 0%R (index_space (length L)))
       with (foldr (Rplus ∘ tc_quicksort CA CB ∘ (index_to_rank f L)) 0%R (index_space (length L)) +
             foldr (Rplus ∘ tc_quicksort CA CB ∘ (reverse_order (index_space (length L))) ∘ (index_to_rank f L)) 0%R (index_space (length L)))%R;
      last first.
    { rewrite /tc_distr_def.
      destruct L as [|L' LS]; first (simpl in *; lra).
      remember (L' :: LS) as L.
      clear HeqL L' LS.

      remember (Rplus ∘ tc_quicksort CA CB ∘ index_to_rank f L) as f1.
      remember (Rplus ∘ tc_quicksort CA CB ∘ reverse_order (index_space (length L)) ∘ index_to_rank f L) as f2.
      replace (compose Rplus _) with  (fun i => (fun r => f1 i 0 + f2 i 0 + r)%R); last first.
      { (* There's probably a better way *)
        apply functional_extensionality.
        intros; simpl.
        apply functional_extensionality.
        rewrite Heqf1 Heqf2 /=.
        intros; simpl.
        rewrite Rplus_comm.
        destruct L; first simplify_eq.
        lra.
      }

      assert (Hf1 : forall i r, (f1 i r = r + f1 i 0)%R) by (intros; rewrite Heqf1 /=; lra).
      assert (Hf2 : forall i r, (f2 i r = r + f2 i 0)%R) by (intros; rewrite Heqf2 /=; lra).
      remember (index_space (length L)) as LL.
      clear Heqf1 Heqf2 HeqLL.

      induction LL as [|LL0 LL' IH].
      - simpl; lra.
      - simpl. rewrite -IH; eauto.
        rewrite Hf1 Hf2.
        lra.
    }

    (* 4. Rewrite the reversed sum and combine to eliminate the factor of 2 *)
    rewrite (foldr_reduction_1); [|done].
    rewrite (foldr_reduction_1); [|done].
    rewrite (foldr_reduction_2).

    (* 5. Combine *)
    do 2 rewrite -foldr_fmap.
    lra.

    Transparent seq.
  Qed.


End qs_adv_cmp.


Section list.
  (** Ported list library to count comparisons *)

  Definition list_nil := NONE.

  Notation "[ ]" := (list_nil) (format "[ ]") : expr_scope.

  Definition list_cons : val := λ: "elem" "list", SOME ("elem", "list").

  Infix "::" := list_cons (at level 60, right associativity) : expr_scope.

  Notation "[ x ]" := (list_cons x list_nil) (format "[ x ]") : expr_scope.

  Notation "[ x ; y ; .. ; z ]" := (list_cons x (list_cons y .. (list_cons z list_nil) ..)) : expr_scope.

  Definition list_filter : val :=
    rec: "list_filter" "f" "l" :=
    match: "l" with
      SOME "a" =>
      let: "r" := "list_filter" "f" (Snd "a") in
      (if: "f" (Fst "a")
       then  Fst "a" :: "r"
       else  "r")
    | NONE => NONE
    end.

  Definition list_length : val :=
    rec: "list_length" "l" :=
    match: "l" with
      SOME "a" => #1 + ("list_length" (Snd "a"))
    | NONE => #0
    end.

  Definition list_remove_nth : val :=
    rec: "list_remove_nth" "l" "i" :=
      match: "l" with
      SOME "a" =>
        let: "head" := Fst "a" in
        let: "tail" := Snd "a" in
        (if: "i" = #0
           then SOME ("head", "tail")
           else
             let: "r" := "list_remove_nth" "tail" ("i" - #1) in
             match: "r" with
               SOME "b" =>
               let: "head'" := Fst "b" in
               let: "tail'" := Snd "b" in
               SOME ("head'", ("head" :: "tail'"))
             | NONE => NONE
             end)
      | NONE => list_nil
      end.

  Definition list_append : val :=
    rec: "list_append" "l" "r" :=
    match: "l" with
      NONE => "r"
    | SOME "p" =>
        let: "h" := Fst "p" in
        let: "t" := Snd "p" in
        "h" :: "list_append" "t" "r"
    end.
  Fixpoint inject_list `{!Inject A val} (xs : list A) :=
    match xs with
    | [] => NONEV
    | x :: xs' => SOMEV ((inject x), inject_list xs')
    end.

  Global Program Instance Inject_list `{!Inject A val} : Inject (list A) val :=
    {| inject := inject_list |}.
  Next Obligation.
    intros ? [] xs. induction xs as [|x xs IH]; simpl.
    - intros []; by inversion 1.
    - intros []; [by inversion 1|].
      inversion 1 as [H'].
      f_equal; [by apply (inj _)|].
      by apply IH.
  Qed.


  Context `[!Inject A val].

  Fixpoint is_list (l : list A) (v : val) :=
    match l with
      | [] => v = NONEV
      | a::l' => ∃ lv, v = SOMEV ((inject a), lv) ∧ is_list l' lv
    end.

  Lemma is_list_inject xs v :
    is_list xs v ↔ v = (inject xs).
  Proof.
    revert v.
    induction xs as [|x xs IH]; [done|]. split.
    - destruct 1 as (? & -> & ?). simpl.
      do 2 f_equal. by apply IH.
    - intros ->. eexists. split; [done|]. by apply IH.
  Qed.

  Section list_specs.
    Context `{!ert_clutchGS Σ CostTick}.

    Lemma wp_list_nil E :
      {{{ True }}}
        list_nil @ E
      {{{ v, RET v; ⌜is_list [] v⌝}}}.
    Proof. iIntros (Φ) "_ HΦ". unfold list_nil. wp_pure. by iApply "HΦ". Qed.

    Lemma wp_list_cons a l lv E :
      {{{ ⌜is_list l lv⌝ }}}
        list_cons (inject a) lv @ E
      {{{ v, RET v; ⌜is_list (a::l) v⌝}}}.
    Proof.
      iIntros (Φ) "% HΦ". wp_lam. wp_pures.
      iApply "HΦ". iPureIntro; by eexists.
    Qed.

    Lemma wp_list_length E l lv :
      {{{ ⌜is_list l lv⌝ }}}
        list_length lv @ E
      {{{ v, RET #v; ⌜v = length l⌝ }}}.
    Proof.
      iIntros (Φ) "Ha HΦ".
      iInduction l as [|a l'] "IH" forall (lv Φ);
      iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_pures.
      - wp_rec.
        wp_match. iApply ("HΦ" $! 0%nat); done.
      - wp_rec.
        simpl.
        destruct Ha as [lv' [Hlv Hlcoh]]; subst.
        wp_match; simpl.
        wp_proj. wp_bind (list_length _); simpl.
        iApply ("IH"); eauto.
        iNext.
        iIntros.
        wp_op.
        rewrite Z.add_1_l -Nat2Z.inj_succ.
        iApply "HΦ".
        eauto.
    Qed.

    Lemma wp_remove_nth E (l : list A) lv (i : nat) :
      {{{ ⌜is_list l lv /\ i < length l⌝ }}}
        list_remove_nth lv #i @ E
      {{{ v, RET v; ∃ e lv' l1 l2,
                  ⌜l = l1 ++ e :: l2 ∧
                   length l1 = i /\
                  v = SOMEV ((inject e), lv') ∧
                  is_list (l1 ++ l2) lv'⌝ }}}.
    Proof.
      iIntros (Φ) "Ha Hφ".
      iInduction l as [|a l'] "IH" forall (i lv Φ);
        iDestruct "Ha" as "(%Hl & %Hi)"; simpl in Hl; subst; wp_rec; wp_let; simpl.
      - inversion Hi.
      - destruct Hl as [lv' [Hlv Hlcoh]]; subst.
        wp_match. wp_pures. case_bool_decide; wp_pures; simpl.
        + iApply "Hφ".
          iExists a, (inject l'), [], l'.
          destruct i; auto.
          iPureIntro; split; auto.
          split; auto.
          split.
          * by apply is_list_inject in Hlcoh as ->.
          * by apply is_list_inject.
        + destruct i; first done.
          assert ((S i - 1)%Z = i) as -> by lia.
          assert (is_list l' lv' /\ i < length l') as Haux.
          { split; auto.
            inversion Hi; auto. lia.
          }
          wp_bind (list_remove_nth _ _).
          repeat rewrite Rminus_0_r.
          iApply ("IH" $! i lv' _ ); [eauto|].
          iNext. iIntros (v (e & v' & l1 & l2 & (-> & Hlen & -> & Hil))); simpl.
          wp_pures.
          wp_bind (list_cons _ _). iApply wp_list_cons; [done|].
          iIntros "!>" (v Hcons).
          wp_pures.
          iApply "Hφ".
          iExists e, (inject ((a :: l1) ++ l2)), (a :: l1), l2.
          iPureIntro.
          split; auto.
          split; [rewrite cons_length Hlen // |].
          split.
          * by apply is_list_inject in Hcons as ->.
          * by apply is_list_inject.
    Qed.

    Lemma wp_list_append E l lM r rM :
      {{{ ⌜is_list lM l⌝ ∗ ⌜is_list rM r⌝}}}
        list_append (Val l) (Val r) @ E
      {{{ v, RET v; ⌜is_list (lM ++ rM) v⌝ }}}.
    Proof.
      iIntros (Φ) "[%Hl %Hr] HΦ". rewrite /list_append.
      iInduction lM as [|a lM] "IH" forall (l r Hl Hr Φ).
      - simpl in Hl; subst. wp_pures. by iApply "HΦ".
      - destruct Hl as [l' [Hl'eq Hl']]; subst.
        do 12 wp_pure _.
        wp_bind (((rec: "list_append" _ _:= _)%V _ _)).
        iApply "IH"; [done..|].
        iIntros "!>" (v Hv).
        by wp_apply wp_list_cons.
    Qed.


    Lemma wp_list_filter (l : list A) (P : A -> bool) (f lv : val) E k (Hk : (0 <= k)%R):
      {{{ (∀ (x : A), {{{ ⧖ k }}} f (inject x) @ E {{{ w, RET w; ⌜w = inject (P x)⌝ }}} ) ∗
          ⌜is_list l lv⌝ ∗
          ⧖ (k * length l) }}}
         list_filter f lv @ E
       {{{ rv, RET rv; ⌜is_list (List.filter P l) rv⌝ }}}.
    Proof.
      iIntros (Φ) "(#Hf & %Hil & H⧖) HΦ".
      iInduction l as [ | h t] "IH" forall (lv Hil Φ); simpl in Hil.
      - subst.
        rewrite /list_filter; wp_pures.
        iApply "HΦ"; done.
      - destruct Hil as (lv' & -> & Hil).
        rewrite /list_filter.
        do 7 (wp_pure _).
        fold list_filter.
        iAssert (⧖ k ∗ ⧖ (k * length t))%I with "[H⧖]" as "(H⧖ & H⧖IH)".
        { rewrite cons_length S_INR Rmult_plus_distr_l Rmult_1_r Rplus_comm.
          iApply etc_split; eauto.
          apply Rmult_le_pos; auto.
          apply pos_INR.
        }
        wp_apply ("IH" with "[//] H⧖IH").
        iIntros (rv) "%Hilp"; wp_pures.
        wp_apply ("Hf" with "[$]").
        iIntros (w) "->".
        destruct (P h) eqn:HP; wp_pures.
        + wp_apply wp_list_cons; [by eauto |].
          iIntros (v) "%Hil'".
          iApply "HΦ"; iPureIntro.
          simpl; rewrite HP; simpl.
          simpl in Hil'; done.
        + iApply "HΦ"; iPureIntro.
          simpl. rewrite HP. done.
    Qed.

  End list_specs.
End list.



Section program.
  Context `{!ert_clutchGS Σ CostTick}.
  Context `[!Inject A val].
  Context `{Inhabited A}.
  Context (f : relation A) `{∀ x y, Decision (f x y)} `{!TotalOrder f}.


  (** Verifing the number of comparisons done by quicksort *)
  (* Proofs augmented from examples/quicksort.v *)

  Definition list_remove_nth_unsafe : val :=
    λ:"l" "n",
    match: list_remove_nth "l" "n" with
    | NONE => #()
    | SOME "v" => "v"
    end.

  (* TODO: Paramaterize by cmp *)
  Definition partition : expr :=
    λ: "cmp",
    λ:"l" "e",
      let: "f" := (λ:"x", "cmp" "e" "x") in
      (list_filter (λ:"x", ~ ("f" "x") ) "l",
        list_filter "f" "l").

  (* TODO: Paramaterize by cmp *)
  Definition qs : val :=
    λ: "cmp",
    rec: "qs" "l" :=
      let: "n" := list_length "l" in
      if: "n" < #1 then "l" else
        let: "ip" := rand ("n" - #1) in
        let, ("p", "r") := list_remove_nth_unsafe "l" "ip" in
        let, ("le", "gt") := partition "cmp" "r" "p" in
        let, ("les", "gts") := ("qs" "le", "qs" "gt") in
        list_append "les" (list_cons "p" "gts").


  Lemma wp_remove_nth_unsafe E (l : list A) (lv : val) (i : nat) :
    {{{ ⌜ is_list l lv /\ i < length l ⌝ }}}
      list_remove_nth_unsafe lv #i @ E
    {{{ v, RET v;
        ∃ e lv' l1 l2,
          ⌜ l = l1 ++ e :: l2 ∧
          length l1 = i /\
          v = ((inject e), lv')%V ∧
          is_list (l1 ++ l2) lv' ⌝ }}}.
  Proof.
    iIntros (φ) "(%llv & %Hi) hφ".
    rewrite /list_remove_nth_unsafe.
    wp_pures.
    wp_apply wp_remove_nth => //.
    iIntros (?(?&?&?&?&?&?&?&?)) ; subst. wp_pures.
    iApply "hφ". iModIntro. iExists _,_,_,_. intuition eauto.
  Qed.


  Definition part_cr k (xs : list A) : nat := (2 * k * length xs)%nat.


  Definition sorted := (StronglySorted f).

  Fact sorted_append pre post p :
    sorted pre → sorted post →
    (∀ x, In x pre → (f x p)) →
    (∀ x, In x post → (f p x)) →
    sorted (pre ++ p :: post).
  Proof.
    intros Spre Spost ppre ppost.
    induction pre => /=.
    - apply SSorted_cons, List.Forall_forall => // ; intros.
    - apply SSorted_cons, List.Forall_forall => // ; [| clear IHpre].
      { apply IHpre.
        * apply StronglySorted_inv in Spre. by destruct Spre.
        * intros. apply ppre. set_solver. }
      intros x xppp.
      destruct (in_app_or _ _ _ xppp) as [x_pre | x_post] ; clear xppp.
      + apply StronglySorted_inv in Spre. destruct Spre.
        by apply (List.Forall_forall _ pre).
      + apply in_inv in x_post.
        destruct x_post.
        { rewrite -H1. apply ppre, in_eq. }
        specialize ppre with a.
        assert (HTO : TotalOrder f) by auto.
        destruct (HTO) as [[[? Htr] ?] ? ].
        rewrite /Transitive in Htr.
        eapply Htr.
        *  eapply ppre, in_eq.
        * eapply ppost; auto.
  Qed.





  Lemma qs_time_bound :
    ∀ (xs : list A) (l : val)
      (cmp : val) (k : R) (Hcmp_nonneg : (0 <= k)%R),
    {{{ ⧖ (tc_quicksort (2 * k) 0 (length xs)) ∗
        ⌜is_list xs l⌝ ∗
        ⌜List.NoDup xs ⌝ ∗
        (∀ (x y : A), {{{ ⧖ k }}} cmp (inject x) (inject y)  {{{ w, RET w; ⌜w = inject (bool_decide (f x y))⌝  }}} ) }}}
      qs cmp l
    {{{ v, RET v; ∃ xs', ⌜ is_list xs' v ∧ xs' ≡ₚ xs ∧ sorted xs' ⌝ }}}.
  Proof with wp_pures.
    rewrite /qs.
    iIntros (xs l cmp k Hcmp_nonneg Φ) "HA1 hφ".
    do 2 wp_pure.
    iLöb as "Hqs" forall (xs l Φ).
    iDestruct "HA1" as "(H⧖ & %hl & %hnd & #Hcmp_spec)".

    wp_pure.
    wp_bind (list_length _).
    wp_apply wp_list_length; [eauto|].
    iIntros (n) "->".
    wp_pures.

    (* Base case *)
    case_bool_decide.
    { wp_pures; iModIntro. iApply "hφ". destruct xs; [ |simpl in *; lia].
      iPureIntro. exists []; split; auto.
      split; auto.
      constructor.
    }

    (* Pick a pivot index at random, using advanced composition on the (2 * ...) term*)
    wp_pures.
    rewrite tc_quicksort_unfold.
    iAssert (⧖ (tc_pivot_lin (2*k) 0 (length xs)) ∗
             ⧖ (2 * foldr Rplus 0 (map (λ n0 : nat, tc_quicksort (2 * k) 0 n0) (seq 0 (length xs))) / length xs))%I
            with "[H⧖]" as "[H⧖lin H⧖Amp]".
    { destruct xs as [|? ?]; first (simpl in *; lia).
      iApply etc_split.
      - apply tc_pivot_lin_nonneg; try lra.
      - apply Rcomplements.Rdiv_le_0_compat; last (rewrite -INR_0; apply lt_INR; simpl; lia).
        apply Rmult_le_pos; try lra.
        (* augh *)
        remember (length (a :: xs)) as W.
        clear HeqW H0 H1.
        induction W as [|W' IHW]; [simpl; lra|].
        rewrite seq_S /=.
        rewrite map_app foldr_app /=.
        rewrite foldr_comm_acc; last (intros; simpl; lra).
        apply Rplus_le_le_0_compat; [apply tc_quicksort_nonneg|]; try lra.
      - iFrame.
    }

    wp_apply (wp_couple_rand_adv_comp' _ _ _ _ _ (tc_distr _ xs (2 * k) 0%R) with "[$]").
    { intros. apply tc_distr_nonneg; try lia; try lra; eauto. }
    { rewrite /= tc_distr_equiv; try lra; try lia; try done.
      rewrite Rplus_0_l. rewrite index_space_unfold. done. }

    iIntros (ip) "H⧖"...

    (* pop the pivot from xs *)
    wp_apply (wp_remove_nth_unsafe _ xs l ip with "[]").
    { iSplit; eauto.
      iPureIntro.
      apply (Nat.lt_le_trans _ _ _ (fin_to_nat_lt ip)).
      simplify_eq; simpl length.
      destruct xs => /=; simpl in *; lia. }

    iIntros (v) "[%xp [%ap [%xsL [%xsR (%Hxs & %Hip & -> & %Hap )]]]]".
    wp_pures.
    iAssert (⧖ (tc_quicksort (2 * k) 0 (index_to_rank f xs ip)) ∗
             ⧖ (tc_quicksort (2 * k) 0 (reverse_order (index_space (length xs)) (index_to_rank f xs ip))))%I
     with "[H⧖]" as "[H⧖L H⧖R]".
    { iApply etc_split.
      - apply tc_quicksort_nonneg; try lra.
      - apply tc_quicksort_nonneg; try lra.
      - rewrite /tc_distr /tc_distr_def /=.
        destruct xs; first (simpl in *; lia).
        iFrame.
    }
    wp_pures.

    iAssert (⧖ (k * (length xs)) ∗ ⧖ (k * (length xs)))%I with "[H⧖lin]" as "[H⧖Filt1 H⧖Filt2]".
    { rewrite /tc_pivot_lin.
      iApply etc_split.
      - apply Rmult_le_pos; try lra; apply pos_INR.
      - apply Rmult_le_pos; try lra; apply pos_INR.
      - iApply etc_irrel; last iFrame.
        rewrite Rplus_0_r.
        lra.
    }

    (* x and xp might be flipped here *)
    wp_apply ((wp_list_filter (xsL ++ xsR) (fun x => bool_decide (f xp x)) _ _ _ k ) with "[H⧖Filt1]"); first lra.
    { iSplitR => //.
      - iIntros (x ψ) "!> H⧖ Hψ".
        wp_pures. by wp_apply ("Hcmp_spec" with "H⧖").
      - iSplitR; first eauto.
        iApply (etc_weaken with "[$]").
        split.
        + apply Rmult_le_pos; try lra; apply pos_INR.
        + apply Rmult_le_compat_l; try lra.
          rewrite Hxs.
          apply le_INR.
          do 2 rewrite app_length.
          simpl. lia.
    }
    iIntros (rv) "%Hrv".
    wp_pures.

    wp_apply ((wp_list_filter (xsL ++ xsR) (fun x => negb $ bool_decide (f xp x)) _ _ _ k) with "[H⧖Filt2]"); first lra.
    { iSplitR.
      - iIntros (x ψ) "!> H⧖ Hψ".
        do 2 wp_pure.
        wp_apply ("Hcmp_spec" with "H⧖").
        iIntros (?) "->".
        wp_pures.
        iModIntro; iApply "Hψ".
        iPureIntro; eauto.
      - iSplitR; first eauto.
        iApply (etc_weaken with "[$]").
        split.
        + apply Rmult_le_pos; try lra; apply pos_INR.
        + apply Rmult_le_compat_l; try lra.
          rewrite Hxs.
          apply le_INR.
          do 2 rewrite app_length.
          simpl. lia.
    }
    iIntros (lv) "%Hlv".
    do 9 wp_pure.

    wp_apply ("Hqs" $! (List.filter _ (xsL ++ xsR)) rv with "[H⧖R]").
    { iClear "Hqs".
      iSplitL; [|iSplit; [|iSplit]].
      4: { iApply "Hcmp_spec". }
      3: { iPureIntro.
           apply List.NoDup_filter.
           eapply NoDup_remove_1.
           rewrite Hxs in hnd.
           eauto.
      }
      2: { iPureIntro. eapply Hrv. }

      iApply etc_irrel; [|iFrame].
      f_equal.
      rewrite /reverse_order /index_space seq_length.
      rewrite /index_to_rank /rank /=.
      rewrite {14}Hxs.

      (* TODO Causes Coq error, report me *)
      (* rewrite -{1}(List.filter_length  (λ y : A, bool_decide (strict (cmp_rel cmp) (xs !!! ip) y))). *)

      apply Nat.add_sub_eq_l.
      replace (length (@List.filter A (fun y : A => @bool_decide (strict f y _) _) _))
         with (length (List.filter (∽ (λ x : A, (bool_decide (f xp x))))%P (xsL ++ xsR))); last first.
      { do 2 rewrite List.filter_app app_length /=.
        replace(@bool_decide _ _) with false; last first.
        { symmetry; apply bool_decide_eq_false_2.
          replace (@lookup_total _ _ _ _ _ _) with xp; last first.
          { symmetry. rewrite {2}Hxs. by apply list_lookup_total_middle. }
          intros Hcont.
          apply strict_ne in Hcont.
          auto.
        }

        assert (Htotal: TotalOrder f) by eauto.
        destruct Htotal as [[[Hrefl Htrans] Hanti] Htrich].


        do 2 f_equal.
        + apply filter_ext_in.
          intros a Ha.
          rewrite -bool_decide_not.
          apply bool_decide_ext.
          rewrite {2}Hxs.
          rewrite list_lookup_total_middle; last done.
          rewrite strict_spec_alt.

          assert (xp ≠ a).
          { rewrite Hxs in hnd.
            apply NoDup_remove_2 in hnd.
            rewrite /not; intros.
            simplify_eq.
            apply hnd.
            apply in_or_app; auto.
          }


          split.
          - intros.
            split; auto.
            destruct (Htrich a xp) as [? | [? | ?] ].
            * by apply strict_include.
            * simplify_eq.
            * exfalso; apply H3. by apply strict_include.
          - intros [ ? ? ] ?.
            apply H4, Hanti; auto.

        + apply filter_ext_in.
          intros a Ha.
          rewrite -bool_decide_not.
          apply bool_decide_ext.
          rewrite {2}Hxs.
          rewrite list_lookup_total_middle; last done.
          rewrite strict_spec_alt.

          assert (xp ≠ a).
          { rewrite Hxs in hnd.
            apply NoDup_remove_2 in hnd.
            rewrite /not; intros.
            simplify_eq.
            apply hnd.
            apply in_or_app; auto.
          }

          split.
          - intros.
            split; auto.
            destruct (Htrich a xp) as [? | [? | ?] ].
            * by apply strict_include.
            * simplify_eq.
            * exfalso; apply H3. by apply strict_include.
          - intros [ ? ? ] ?.
            apply H2, Hanti; auto.
      }

      rewrite Nat.add_comm.
      rewrite (List.filter_length (λ x : A, bool_decide (f xp x))).
      rewrite Hxs.
      repeat rewrite app_length /=.
      lia.
    }
    iIntros (lR) "(% & % & % & %)".

    wp_apply ("Hqs" $! (List.filter (fun x => negb (bool_decide (f xp x))) (xsL ++ xsR)) lv with "[H⧖L]").
    { iClear "Hqs".
      iSplitL; [|iSplit; [|iSplit]].
      4: { iApply "Hcmp_spec". }
      3: { iPureIntro.
           apply List.NoDup_filter.
           eapply NoDup_remove_1.
           rewrite Hxs in hnd.
           eauto.
      }
      2: { iPureIntro. done. }

      - iApply etc_irrel; [|iFrame].
        f_equal.
        rewrite /index_to_rank /rank /=.
        rewrite {13}Hxs.
        do 2 rewrite List.filter_app app_length /=.
        replace(@bool_decide _ _) with false; last first.
        { symmetry; apply bool_decide_eq_false_2.
          replace (@lookup_total _ _ _ _ _ _) with xp; last first.
          { symmetry. rewrite {2}Hxs. by apply list_lookup_total_middle. }
          intros Hcont.
          apply strict_ne in Hcont.
          auto.
        }


        assert (Htotal: TotalOrder f) by eauto.
        destruct Htotal as [[[Hrefl Htrans] Hanti] Htrich].

        do 2 f_equal.
        + apply filter_ext_in.
          intros a Ha.
          rewrite -bool_decide_not.

          apply bool_decide_ext.
          rewrite {2}Hxs.
          rewrite list_lookup_total_middle; last done.
          rewrite strict_spec_alt.

          assert (xp ≠ a).
          { rewrite Hxs in hnd.
            apply NoDup_remove_2 in hnd.
            rewrite /not; intros.
            simplify_eq.
            apply hnd.
            apply in_or_app; auto.
          }


          split.
          * intros [ ? ? ] ?.
            apply H5, Hanti; auto.
          * intros.
            split; auto.
            destruct (Htrich a xp) as [? | [? | ?] ].
            -- by apply strict_include.
            -- simplify_eq.
            -- exfalso. apply H6.
               by apply strict_include.


        + apply filter_ext_in.
          intros a Ha.

          rewrite -bool_decide_not.

          apply bool_decide_ext.
          rewrite {2}Hxs.
          rewrite list_lookup_total_middle; last done.
          rewrite strict_spec_alt.

          assert (xp ≠ a).
          { rewrite Hxs in hnd.
            apply NoDup_remove_2 in hnd.
            rewrite /not; intros.
            simplify_eq.
            apply hnd.
            apply in_or_app; auto.
          }


          split.
          * intros [ ? ? ] ?.
            apply H5, Hanti; auto.
          * intros.
            split; auto.
            destruct (Htrich a xp) as [? | [? | ?] ].
            -- by apply strict_include.
            -- simplify_eq.
            -- exfalso. apply H6. by apply strict_include.

    }
    iIntros (lL) "(% & % & % & %)".
    wp_pures.

    iClear "Hqs".
    wp_apply wp_list_cons => //; first eauto. iIntros (p_xs_gt_s h_p_xs_gt).
    iApply wp_list_append => //. iIntros "!>" (xs_le_p_gt_s L).
    iApply "hφ".
    iExists _.
    iPureIntro.
    split; eauto.
    split.
    - simplify_eq.
      rewrite Permutation_app_comm (Permutation_app_comm xsL).
      simpl.
      constructor.
      rewrite H3 H6.
      symmetry.
      rewrite Permutation_app_comm.
      remember (xsL ++ xsR) as LL.
      clear.
      induction LL as [|L0 LL' IH].
      + simpl. constructor.
      + simpl.
        destruct (bool_decide (f xp L0)); simpl.
        * rewrite -IH. done.
        * rewrite Permutation_app_comm /=.
          constructor.
          rewrite Permutation_app_comm.
          done.
    - apply sorted_append; eauto.
      + intros.
        rewrite H6 in H8.
        apply filter_In in H8.
        destruct H8 as [? Hdec].
        apply negb_true_iff, bool_decide_eq_false_1 in Hdec.
        assert (HT : Total f) by apply trichotomy_total.
        destruct (HT x xp); eauto.
        exfalso; by apply Hdec.
      + intros.
        rewrite H3 in H8.
        apply filter_In in H8.
        destruct H8 as [? Hdec].
        by apply bool_decide_eq_true_1 in Hdec.
  Qed.


End program.


Section log_lib.
  (** Lemmas related to log *)
  (* Taken from meldable_heaps.v; move to a common place? *)

  Lemma ln_0 : (ln 0%R = 0%R).
  Proof. compute. destruct (Rlt_dec R0 R0); auto. exfalso. lra. Qed.

  Lemma ln_pos (n : nat) : (1 < n)%nat -> (0 < ln n)%R.
  Proof.
    intros.
    apply exp_lt_inv.
    rewrite exp_0.
    pose P := (pos_INR n).
    rewrite exp_ln; [apply lt_1_INR; lia | apply lt_0_INR; lia].
  Qed.

  Lemma ln_nonneg (n : nat) : (0 <= ln n)%R.
  Proof.
    destruct n as [|n]; [ rewrite ln_0; lra | ].
    destruct n as [|n]; [ rewrite ln_1; lra | ].
    apply Rlt_le, ln_pos. lia.
  Qed.


  Lemma Rlog_pos (b : R) (v : nat) : (1 < b)%R -> (0 <= Rlog b v)%R.
  Proof.
    intros.
    rewrite /Rlog Rdiv_def.
    apply Rmult_le_pos; [apply ln_nonneg | ].
    apply Rlt_le, Rinv_0_lt_compat.
    rewrite -(ln_exp 0) exp_0.
    apply ln_increasing; lra.
  Qed.

  Lemma Rlog_nonneg_nats (b v : nat) : (0 <= Rlog b v)%R.
  Proof.
    rewrite /Rlog Rdiv_def.
    apply Rmult_le_pos; [apply ln_nonneg | ].
    destruct b; [rewrite /= ln_0 Rinv_0; lra |].
    destruct b; [rewrite /= ln_1 Rinv_0; lra |].
    apply Rlt_le, Rinv_0_lt_compat.
    apply ln_pos.
    lia.
  Qed.


  Lemma Rlog_increasing x y b : (1 < b)%R -> (0 < x < y)%R -> (Rlog b x < Rlog b y)%R.
  Proof.
    intros.
    rewrite /Rlog Rdiv_def.
    apply Rmult_lt_compat_r.
    { apply Rinv_0_lt_compat.
      rewrite -(ln_exp 0) exp_0.
      apply ln_increasing; lra.
    }
    apply ln_increasing; lra.
  Qed.
End log_lib.


Section qs_ent.
  (** Defines the recurrence relation for Quicksort entropy *)

  (* tc_quicksort(len) = (1/len) + 2 * sum(i=0 to len-1)(tc_quicksort i) *)
  Definition ec_quicksort (A : R) (len : nat) : R.
  refine (@Fix nat _ (Wf.measure_wf lt_wf (fun x => x)) (fun _ => R)
          (fun len qf_rec =>
           match len with
               0%nat   => 0%R
             | (S n) => ((Rlog 2 len) +
                          2 * (foldr Rplus 0%R $
                                map (fun n => (qf_rec (fin_to_nat n) _)) $
                                fin_enum len) / len )%R
           end) len).
  Proof. rewrite /Wf.MR. apply fin_to_nat_lt. Defined.


  Lemma ec_quicksort_aux A len :
    ec_quicksort A len =
      match len with
        0%nat   => 0%R
      | (S _) => ((Rlog 2 len)
                  + 2 * (foldr Rplus 0%R $
                        map (fun n => ec_quicksort A (fin_to_nat n)) $
                        (fin_enum len) ) / len)%R
      end.
  Proof. rewrite /ec_quicksort easy_fix_eq. done. Qed.

  Lemma ec_quicksort_unfold A len :
    ec_quicksort A len =
      match len with
        0%nat   => 0%R
      | (S _) => ((Rlog 2 len)
                  + 2 * (foldr Rplus 0%R $
                        map (fun n => ec_quicksort A n) $
                        seq 0%nat len) / len)%R
      end.
  Proof.
    rewrite ec_quicksort_aux.
    destruct len; [done|].
    do 3 f_equal.
    generalize (S len); intros N; clear.
    induction N as [|N' IH]; [done|].
    Opaque seq fin_enum.
    rewrite seq_S map_app foldr_snoc /=.
    rewrite fin_enum_snoc_rec map_app foldr_snoc /=.
    rewrite foldr_comm_acc; last (intros; simpl; lra).
    rewrite foldr_comm_acc; last (intros; simpl; lra).
    rewrite -IH.
    f_equal.
    + by rewrite fin_to_nat_to_fin.
    + rewrite map_map.
      do 2 f_equal.
      apply functional_extensionality; intros; simpl.
      by rewrite -fin_inj_incr_to_nat.
    Transparent seq fin_enum.
  Qed.

  Opaque ec_quicksort.



  Lemma ec_quicksort_0 A : ec_quicksort A 0%nat = 0%R.
  Proof. rewrite ec_quicksort_unfold. done. Qed.

  Lemma ec_quicksort_S A n :
    (1 <= n)%nat ->
    ec_quicksort A n = ((Rlog 2 n) + 2 * (foldr Rplus 0 $ map (fun i => ((ec_quicksort A i))%NNR) $ seq 0%nat n)%NNR /n)%R.
  Proof. intros. rewrite ec_quicksort_unfold. destruct n; [lia|]. done. Qed.

  Lemma ec_quicksort_nonneg A n :
    (0 <= A)%R ->
    (0 <= ec_quicksort A n)%R.
  Proof.
    intros HA.
    induction n as [ n' IH ] using (well_founded_induction lt_wf).
    rewrite ec_quicksort_unfold.
    destruct n' as [|n']; [lra|].
    apply Rplus_le_le_0_compat; [ apply Rlog_pos; lra | ].
    apply Rmult_le_pos; [| apply Rlt_le, Rinv_0_lt_compat, pos_INR_S].
    apply Rmult_le_pos; [lra|].
    induction n' as [|n'' IH'].
    - rewrite /= ec_quicksort_0 Rplus_0_r. lra.
    - rewrite seq_S.
      Opaque seq.
      rewrite map_app foldr_snoc /=.
      rewrite foldr_comm_acc; last (intros; simpl; lra).
      apply Rplus_le_le_0_compat.
      * apply IH; lia.
      * apply IH'. intros. apply IH. lia.
      Transparent seq.
  Qed.

End qs_ent.

Section ent_list.
    (** Entropy calculations for list helper functions *)
    (* None of these are interesting, they should all consume 0 entropy *)

    Program Definition CostEntropy_2 := CostEntropy 2 _.
    Next Obligation. lra. Defined.

    Context `{!ert_clutchGS Σ CostEntropy_2}.
    Context `[!Inject A val].

    Lemma wp_list_nil_ent E :
      {{{ True }}}
        list_nil @ E
      {{{ v, RET v; ⌜is_list [] v⌝}}}.
    Proof. iIntros (Φ) "_ HΦ". unfold list_nil. wp_pure. by iApply "HΦ". Qed.

    Lemma wp_list_cons_ent a l lv E :
      {{{ ⌜is_list l lv⌝ }}}
        list_cons (inject a) lv @ E
      {{{ v, RET v; ⌜is_list (a::l) v⌝}}}.
    Proof.
      iIntros (Φ) "% HΦ". wp_lam. wp_pures.
      iApply "HΦ". iPureIntro; by eexists.
    Qed.

    Lemma wp_list_length_ent E l lv :
      {{{ ⌜is_list l lv⌝ }}}
        list_length lv @ E
      {{{ v, RET #v; ⌜v = length l⌝ }}}.
    Proof.
      iIntros (Φ) "Ha HΦ".
      iInduction l as [|a l'] "IH" forall (lv Φ);
      iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_pures.
      - wp_rec.
        wp_match. iApply ("HΦ" $! 0%nat); done.
      - wp_rec.
        simpl.
        destruct Ha as [lv' [Hlv Hlcoh]]; subst.
        wp_match; simpl.
        wp_proj. wp_bind (list_length _); simpl.
        iApply ("IH"); eauto.
        iNext.
        iIntros.
        wp_op.
        rewrite Z.add_1_l -Nat2Z.inj_succ.
        iApply "HΦ".
        eauto.
    Qed.

    Lemma wp_remove_nth_ent E (l : list A) lv (i : nat) :
      {{{ ⌜is_list l lv /\ i < length l⌝ }}}
        list_remove_nth lv #i @ E
      {{{ v, RET v; ∃ e lv' l1 l2,
                  ⌜l = l1 ++ e :: l2 ∧
                   length l1 = i /\
                  v = SOMEV ((inject e), lv') ∧
                  is_list (l1 ++ l2) lv'⌝ }}}.
    Proof.
      iIntros (Φ) "Ha Hφ".
      iInduction l as [|a l'] "IH" forall (i lv Φ);
        iDestruct "Ha" as "(%Hl & %Hi)"; simpl in Hl; subst; wp_rec; wp_let; simpl.
      - inversion Hi.
      - destruct Hl as [lv' [Hlv Hlcoh]]; subst.
        wp_match. wp_pures. case_bool_decide; wp_pures; simpl.
        + iApply "Hφ".
          iExists a, (inject l'), [], l'.
          destruct i; auto.
          iPureIntro; split; auto.
          split; auto.
          split.
          * by apply is_list_inject in Hlcoh as ->.
          * by apply is_list_inject.
        + destruct i; first done.
          assert ((S i - 1)%Z = i) as -> by lia.
          assert (is_list l' lv' /\ i < length l') as Haux.
          { split; auto.
            inversion Hi; auto. lia.
          }
          wp_bind (list_remove_nth _ _).
          repeat rewrite Rminus_0_r.
          iApply ("IH" $! i lv' _ ); [eauto|].
          iNext. iIntros (v (e & v' & l1 & l2 & (-> & Hlen & -> & Hil))); simpl.
          wp_pures.
          wp_bind (list_cons _ _). iApply wp_list_cons_ent; [done|].
          iIntros "!>" (v Hcons).
          wp_pures.
          iApply "Hφ".
          iExists e, (inject ((a :: l1) ++ l2)), (a :: l1), l2.
          iPureIntro.
          split; auto.
          split; [rewrite cons_length Hlen // |].
          split.
          * by apply is_list_inject in Hcons as ->.
          * by apply is_list_inject.
    Qed.

    Lemma wp_list_append_ent E l lM r rM :
      {{{ ⌜is_list lM l⌝ ∗ ⌜is_list rM r⌝}}}
        list_append (Val l) (Val r) @ E
      {{{ v, RET v; ⌜is_list (lM ++ rM) v⌝ }}}.
    Proof.
      iIntros (Φ) "[%Hl %Hr] HΦ". rewrite /list_append.
      iInduction lM as [|a lM] "IH" forall (l r Hl Hr Φ).
      - simpl in Hl; subst. wp_pures. by iApply "HΦ".
      - destruct Hl as [l' [Hl'eq Hl']]; subst.
        do 12 wp_pure _.
        wp_bind (((rec: "list_append" _ _:= _)%V _ _)).
        iApply "IH"; [done..|].
        iIntros "!>" (v Hv).
        by wp_apply wp_list_cons_ent.
    Qed.


    (* Since we eventually want to obtain a O(n) bound, we will
       only consider comparison functions which consume zero entropy. *)
    Lemma wp_list_filter_ent (l : list A) (P : A -> bool) (f lv : val) E k (Hk : (0 <= k)%R):
      {{{ (∀ (x : A), {{{ ⌜ True ⌝  }}} f (inject x) @ E {{{ w, RET w; ⌜w = inject (P x)⌝ }}} ) ∗
          ⌜is_list l lv⌝ }}}
         list_filter f lv @ E
       {{{ rv, RET rv; ⌜is_list (List.filter P l) rv⌝ }}}.
    Proof.
      iIntros (Φ) "(#Hf & %Hil) HΦ".
      iInduction l as [ | h t] "IH" forall (lv Hil Φ); simpl in Hil.
      - subst.
        rewrite /list_filter; wp_pures.
        iApply "HΦ"; done.
      - destruct Hil as (lv' & -> & Hil).
        rewrite /list_filter.
        do 7 (wp_pure _).
        fold list_filter.
        wp_apply ("IH" with "[//]").
        iIntros (rv) "%Hilp"; wp_pures.
        wp_apply ("Hf" with "[$]").
        iIntros (w) "->".
        destruct (P h) eqn:HP; wp_pures.
        + wp_apply wp_list_cons_ent; [by eauto |].
          iIntros (v) "%Hil'".
          iApply "HΦ"; iPureIntro.
          simpl; rewrite HP; simpl.
          simpl in Hil'; done.
        + iApply "HΦ"; iPureIntro.
          simpl. rewrite HP. done.
    Qed.

End ent_list.
