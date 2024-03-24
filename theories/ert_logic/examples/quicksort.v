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

  (* Lets us use familiar relation lemmas, but still compute using f *)
  Definition computable_relation `{A : Type} (f : A -> A -> bool) : relation A
    := (fun a1 a2 => f a1 a2 = true).

  Definition strict_computable `{A : Type} (f : A -> A -> bool) : (A -> A -> bool)
    := (fun a1 a2 => (eqb (f a1 a2) true) && (eqb (f a2 a1) false)).

  (* Instead of using TotalOrder, we roll our own, so that it doesn't insert another "strict"
     We want the strictness to be baked into the function itself so that we can use it to compute,
     and so that we don't need to prove
            strict (computable_relation f) = computable_relation (strict_computable f)
     which is an equality between values of type (A -> A -> Prop).
   *)

  Record sorting_function (A : Type) (f : A -> A -> bool) :=
    { sort_order: PartialOrder (computable_relation f) ;
      sort_trich : Trichotomy (computable_relation f) ;
    }.

  (*
  Lemma computable_partial_total A f : (PartialOrder (computable_relation A f)) -> (TotalOrder (computable_relation A f)).
  Proof.
    intros [? Has].
    constructor; [constructor|]; auto.
    intros x y.
    rewrite /computable_relation /strict.
    Set Printing Parentheses.
    rewrite /AntiSymm /computable_relation in Has.
    destruct (f x y) as [|] eqn:Hf.
    - admit.
    - right.
  *)



  (* All computable relations will be total rather than partial *)


  (* Rank of an element in a list *)
  (* Element doesn't have to be in the list *)
  Definition rank `{A : Type} f (T : sorting_function A f) (L : list A) (x : A) : nat
    := (length (List.filter (fun y => (strict_computable f) x y) L)).

   Definition index_to_rank `{A : Type} `{Hinhabited : Inhabited A} (L : list A) f (Hsf : sorting_function A f) : nat -> nat
    := (rank _ Hsf L) ∘ (fun index => L !!! index).

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
  Lemma equal_perm `{T : Type} (A B : list T) : (A = B) -> (A ≡ₚ B).
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
      intros ? ? H.
      rewrite lookup_seq in H.
      destruct H as [H1 H2].
      simpl. lia.
  Qed.

   (** Index to list permutation on index_space *)

  Definition ext_id f N : nat -> nat := fun n => if (Nat.leb N n) then n else f n.

  Lemma suffices_to_prove_ext N f :
    ((index_space N) ≡ₚ ((ext_id f N) <$> (index_space N))) ->
    ((index_space N) ≡ₚ f <$> (index_space N)).
  Proof.
    intros.
    rewrite {1}H.
    apply equal_perm.
    apply list_fmap_ext.
    intros i x H1.
    rewrite /ext_id.
    replace (N <=? x) with false; [done|].
    rewrite index_space_unfold in H1.
    apply lookup_seq in H1.
    symmetry.
    apply leb_correct_conv. lia.
  Qed.



  Lemma rank_lemma `{A : Type} `{Hinhabited : Inhabited A} (L : list A) x f `{HSF : sorting_function A f} :
    (x < length L) ->
    length (List.filter (λ y : A, strict_computable f (L !!! x) y) L) < length L.
  Proof.
    intros Hlt.
    rewrite -(take_drop x L).
    rewrite List.filter_app.
    do 2 rewrite app_length.
    apply PeanoNat.Nat.add_le_lt_mono; [apply filter_length_le|].

    (* Rewrite drop *)
    destruct (drop x L) as [| l L'] eqn:HL'.
    { exfalso.
      rewrite -(take_drop x L) app_length HL' /= Nat.add_0_r in Hlt.
        pose Pcont := (firstn_le_length x L). lia. }
    rewrite list_lookup_total_middle; last (symmetry; apply firstn_length_le; lia).

    replace (l :: L') with ([l] ++ L'); last by simpl.
    rewrite List.filter_app.
    do 2 rewrite app_length.
    apply PeanoNat.Nat.add_lt_le_mono; [|apply filter_length_le].

    simpl.
    rewrite /strict_computable.
    destruct (f l l) as [|]; simpl; lia.
  Qed.



  Lemma index_to_rank_nat_perm `{A : Type} `{Hinhabited : Inhabited A} f `{HSF : sorting_function A f} (L : list A) :
    List.NoDup L ->
    (index_space (length L)) ≡ₚ ((index_to_rank L f HSF) <$> (index_space (length L))).
  Proof.
    intros.
    eapply suffices_to_prove_ext.
    rewrite index_space_unfold.
    symmetry.
    apply nat_bijection_Permutation.
    - rewrite /FinFun.bFun.
      intros.
      rewrite /ext_id.
      rewrite leb_correct_conv; [|done].
      rewrite /index_to_rank /rank /=.
      apply rank_lemma; auto.
    - rewrite /FinFun.Injective.
      rewrite /ext_id.
      intros x y Hinj.
      remember (length L <=? x) as Kx.
      remember (length L <=? y) as Ky.
      destruct Kx, Ky.
      + done.
      + exfalso.
        symmetry in HeqKy, HeqKx.
        apply -> leb_iff_conv in HeqKy.
        apply -> Nat.leb_le in HeqKx.
        rewrite Hinj /index_to_rank /rank /= in HeqKx.
        assert (Hcont : length L < length L); [|lia].
        eapply Nat.le_lt_trans; first eapply HeqKx.
        apply rank_lemma; auto.
      + exfalso.
        symmetry in HeqKy, HeqKx.
        apply -> leb_iff_conv in HeqKx.
        apply -> Nat.leb_le in HeqKy.
        rewrite -Hinj /index_to_rank /rank /= in HeqKy.
        assert (Hcont : length L < length L); [|lia].
        eapply Nat.le_lt_trans; first eapply HeqKy.
        apply rank_lemma; auto.
      + (* The actual injectivity proof *)
        symmetry in HeqKy, HeqKx.
        apply -> leb_iff_conv in HeqKx.
        apply -> leb_iff_conv in HeqKy.
        rewrite /index_to_rank /rank /= in Hinj.
        assert (Hin_x: In (L !!! x) L) by admit.
        assert (Hin_y: In (L !!! y) L) by admit.

        (* Ultimately we want to use trichotomy? *)
        destruct (Nat.eq_decidable x y) as [? | Hdec]; [done|].
        exfalso.

        (* I think all three of thse are true, but I also think I'm getting lost in the weeds *)
        destruct HSF as [? Htri].
        rewrite /Trichotomy in Htri.
        rewrite /computable_relation in Htri.
        rewrite /strict_computable /computable_relation in Hinj.
        destruct (Htri (L !!! x) (L !!! y)) as [Z | [Z | Z]].
        * admit.
        * admit.
        * admit.
  Admitted.

  Lemma filter_split_perm `{A: Type} (l : list A) f :
    l ≡ₚ List.filter f l ++ List.filter (fun x=>negb (f x)) l.
  Proof.
    induction l as [|a l IHl] => // /=.
    destruct (f a) => /= ; rewrite -?Permutation_middle -IHl //.
  Qed.

  (** Lemmas for simplifying using permutations *)

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
  Definition tc_pivot_lin (A B n : nat) : R := INR (A*n+B)%nat.

  Definition tc_base : R := 1%R.

  Lemma tc_base_nonneg : (0%R <= tc_base)%R.
  Proof. rewrite /tc_base. lra. Qed.

  Opaque tc_base.

  (* tc_quicksort(len) = (1/len) + 2 * sum(i=0 to len-1)(tc_quicksort i) *)
  Definition tc_quicksort (A B len : nat) : R.
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


  (* Non-haunted version with seq instead of fin_enum *)
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

  (* Only ever use the unfold lemma *)
  Opaque tc_quicksort.

  Lemma tc_quicksort_0 A B : tc_quicksort A B 0%nat = tc_base.
  Proof. rewrite tc_quicksort_unfold. done. Qed.

  Lemma tc_quicksort_S A B n :
    (1 <= n)%nat ->
    tc_quicksort A B n = ((tc_pivot_lin A B n) + 2 * (foldr Rplus 0 $ map (fun i => ((tc_quicksort A B i))%NNR) $ seq 0%nat n)%NNR /n)%R.
  Proof. intros. rewrite tc_quicksort_unfold. destruct n; [lia|]. done. Qed.

  (* Prove this by strong induction now *)
  Lemma tc_quicksort_nonneg A B n : (0 <= tc_quicksort A B n)%R.
  Proof.
    induction n as [ n' IH ] using (well_founded_induction lt_wf).
    rewrite tc_quicksort_unfold.
    destruct n' as [|n']; [apply tc_base_nonneg |].
    apply Rplus_le_le_0_compat; [rewrite /tc_pivot_lin; apply pos_INR | ].
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

  Lemma tc_quicksort_bound_ind n' A B (HAB : (B <= A)%nat) :
    ((tc_quicksort A B (S n')) / (S n' + 1)%nat  <= (2* A)%nat / (S n' + 1)%nat + (tc_quicksort A B n') / (n' + 1)%nat )%R.
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
          apply Rle_minus, le_INR.
          lia.
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
      replace ((A + (A + 0))%nat * / (INR 2))%R with (INR A); last first.
      { rewrite Nat.add_0_r.
        rewrite -{2}(Nat.mul_1_r A) -{3}(Nat.mul_1_r A).
        rewrite -Nat.mul_add_distr_l.
        rewrite mult_INR plus_INR INR_1.
        lra.
      }
      rewrite Rdiv_def.
      rewrite tc_quicksort_unfold /tc_pivot_lin.
      simpl.
      rewrite Nat.mul_1_r.
      rewrite INR_1 Rdiv_1_r Rplus_0_r.
      rewrite tc_quicksort_0.
      rewrite Rmult_plus_distr_r.
      rewrite plus_INR.
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
    replace (((((INR B) - (INR A)) / (INR n)) / ((INR n) + 1)) * (INR (n + 1)))%R
       with ((((INR B - INR A)) / (INR n)))%R; last first.
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
    rewrite Rmult_assoc.
    rewrite Rmult_assoc.
    rewrite Rinv_l; last (apply not_0_INR; lia).
    rewrite Rmult_1_r.
    rewrite (Rmult_comm (/ (INR n))).
    rewrite -Rmult_assoc.
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_assoc.
    rewrite Rinv_l; last (apply not_0_INR; lia).
    rewrite Rmult_1_r.
    replace (((INR B - INR A) / (INR n)) * (INR n))%R with (INR B - INR A)%R; last first.
    { rewrite Rdiv_def.
      rewrite Rmult_assoc.
      rewrite Rinv_l; last (apply not_0_INR; lia).
      lra.
    }

    (* Collect C (S n'') on the left *)
    apply (Rplus_eq_reg_l (- ((INR ((A * n) + B)) * (INR n)))%R).
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
    replace ((INR ((A * (S (S n''))) + B)) * (INR (S (S n''))))%R
      with  (((INR ((A * (S (S n''))) + B)) * INR (S n'')) + (INR ((A * (S (S n''))) + B)))%R; last first.
    { rewrite (S_INR (S n'')).
      rewrite Rmult_plus_distr_l.
      by rewrite Rmult_1_r.
    }
    replace ((INR ((A * (S (S n''))) + B)) * (INR (S n'')))%R
       with ((INR ((A * (S n'')) + B)) * (INR (S n'')) + (INR A) * (INR (S n'')))%R; last first.
    { symmetry.
      rewrite -{1}Nat.add_1_r.
      rewrite Nat.mul_add_distr_l.
      rewrite Nat.mul_1_r.
      rewrite -Nat.add_assoc (Nat.add_comm A _) Nat.add_assoc.
      rewrite plus_INR.
      rewrite Rmult_plus_distr_r.
      done.
    }
    rewrite Ropp_mult_distr_l.
    rewrite Ropp_involutive.
    rewrite Rmult_comm.
    rewrite -{1}(Rplus_0_r (_ * _)%R).
    rewrite Rplus_assoc.
    rewrite Rplus_assoc.
    apply Rplus_eq_compat_l.

    (* Expand the remaining (S (S n'')) terms *)
    repeat (rewrite S_INR || rewrite plus_INR || rewrite INR_0 || rewrite mult_INR).
    lra.
  Qed.


  Lemma tc_quicksort_bound_closed A B n (HAB : (B <= A)%nat):
    (((tc_quicksort A B n) / (n + 1)%nat)
      <= (foldr Rplus (tc_quicksort A B 0%nat) $
          map (fun i => ((2*A)%nat / (i + 1)%nat)) $
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

  Context `[!Inject A val].
  Context `{Inhabited A}.


  (* Distribution, in a form which is easy to work with *)
  Definition tc_distr_def (L : list A) f (SF : sorting_function A f) (CA CB : nat) : nat -> R
    := fun index =>
         match L with
         | [] => tc_base
         | _ => ((tc_quicksort CA CB ∘ (index_to_rank L f SF)) index +
                 (tc_quicksort CA CB ∘ reverse_order (index_space (length L)) ∘ (index_to_rank L f SF)) index)%R
         end.

  (* Distribution, in a form which typechecks with advanced composition *)
  Definition tc_distr (L : list A) f (SF : sorting_function A f) CA CB : (fin (S (Z.to_nat (length L - 1)))) -> R
    := (tc_distr_def L f SF CA CB) ∘ fin_to_nat.


  Lemma tc_distr_nonneg L f SF CA CB i : (0 < length L)%nat -> (0 <= tc_distr L f SF CA CB i)%R.
  Proof.
    intros.
    rewrite /tc_distr /tc_distr_def /=.
    destruct L; first (simpl in *; lia).
    apply Rplus_le_le_0_compat; apply tc_quicksort_nonneg.
  Qed.


  Lemma foldr_reduction_1 (L : list A) g f (SF : sorting_function A f)  :
   (List.NoDup L) ->
     (foldr (Rplus ∘ g ∘ index_to_rank L f SF) 0 (index_space (length L)))%R
   = (foldr (Rplus ∘ g) 0 (index_space (length L)))%R.
  Proof.
    intros.
    rewrite (fold_R_fin_perm _ (index_to_rank L f SF)).
    - (* generalize me *)
      remember (index_space (length L)) as LL.
      clear HeqLL.
      remember (index_to_rank L f SF) as g1.
      induction LL as [|L0 L' IH].
      + simpl; lra.
      + simpl. f_equal. apply IH.
    - apply index_to_rank_nat_perm; done.
  Qed.

  Lemma foldr_reduction_2 (L : list A) g f (SF : sorting_function A f) :
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
  Lemma tc_distr_equiv L f SF CA CB :
  (0 < length L)%nat ->
  (List.NoDup L) ->
  (SeriesC (λ n : fin (S (Z.to_nat (length L - 1))), 1 / S (Z.to_nat (length L - 1)) * tc_distr L f SF CA CB n))%R =
        (2 * foldr Rplus 0 (map (λ n : nat, tc_quicksort CA CB n) (index_space (length L))) / (length L))%R.
  Proof.
    intros Hlength Hunique.
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
    replace (foldr (Rplus ∘ (tc_distr_def L f SF CA CB ∘ fin_to_nat)) 0%R (enum (fin (S (Z.to_nat (Z.of_nat (length L) - 1))))))
      with  (foldr (Rplus ∘ tc_distr_def L f SF CA CB) 0%R (index_space (length L)));
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
        replace (foldr (Rplus ∘ g CA CB) (g CA CB l + 0)%R (index_space l))%R with (g CA CB l + foldr (Rplus ∘ g CA CB) (0)%R (index_space l))%R; last first.
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

        replace (foldr (Rplus ∘ (λ index : fin (S l), g CA CB (fin_to_nat index))) (g CA CB l + 0)%R (fin_inj_incr l <$> fin_enum l))%R
          with (g CA CB l + foldr (Rplus ∘ (λ index : fin (S l), g CA CB (fin_to_nat index))) 0%R (fin_inj_incr l <$> fin_enum l))%R;
          last first.
        { (* whatever *)
          remember (fin_inj_incr _ <$> _ ) as LL; clear.
          induction LL as [|LL0 LL' IH].
          - simpl. done.
          - simpl. rewrite -IH. lra.
        }
        f_equal.
        replace (foldr (Rplus ∘ (λ index : fin (S l), g CA CB (fin_to_nat index))) 0%R (fin_inj_incr l <$> fin_enum l))%R
           with (foldr (Rplus ∘ (λ index : fin (S l), g CA CB (fin_to_nat index)) ∘ fin_inj_incr l ) 0%R (fin_enum l))%R;
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
    replace (foldr (Rplus ∘ tc_distr_def L f SF CA CB) 0%R (index_space (length L)))
       with (foldr (Rplus ∘ tc_quicksort CA CB ∘ (index_to_rank L f SF)) 0%R (index_space (length L)) +
             foldr (Rplus ∘ tc_quicksort CA CB ∘ (reverse_order (index_space (length L))) ∘ (index_to_rank L f SF)) 0%R (index_space (length L)))%R;

      last first.
    { rewrite /tc_distr_def.
      remember (Rplus ∘ tc_quicksort CA CB ∘ index_to_rank L f SF) as f1.
      remember (Rplus ∘ tc_quicksort CA CB ∘ reverse_order (index_space (length L)) ∘ index_to_rank L f SF) as f2.
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
    rewrite (foldr_reduction_1 _ _ f); [|done].
    rewrite (foldr_reduction_1 _ _ f); [|done].
    rewrite (foldr_reduction_2 _ _ f); [|done].

    (* 5. Combine *)
    do 2 rewrite -foldr_fmap.
    lra.

    Transparent seq.
  Qed.


End qs_adv_cmp.

Section cost.
  (** Cost fucntion for Quicksort: number of comparisons *)

  Definition cmp_cost_fn (e : expr) :=
    match e with
    | BinOp LeOp _ _ => 1
    | BinOp LtOp _ _ => 1
    | _ => 0
    end.

  Program Definition CostCmp : Costfun prob_lang :=
    (Build_Costfun _ (at_redex_cost cmp_cost_fn) _).
  Next Obligation.
    intros; simpl.
    eapply at_redex_cost_nonneg.
    intros e'.
    rewrite /cmp_cost_fn.
    destruct e'; simpl; try lra.
    destruct op; simpl; try lra.
  Qed.

  Context `{!ert_clutchGS Σ CostCmp}.

  #[local] Lemma test_wp_pure :
       {{{ ⧖ 1 }}} (if: (#0 < #1) then #() else #() ) {{{ RET #(); ⧖ 0 }}}.
  Proof.
    iIntros (x) "Hx Hp".
    wp_pure.
    wp_pure.
    iModIntro.
    assert (1 - 1 = 0)%R as -> by lra.
    by iApply "Hp".
  Qed.

End cost.



Section list.
  (** Ported list library to count comparisons *)
  Context `{!ert_clutchGS Σ CostTick }.

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

  Section list_specs.
    Context `{!ert_clutchGS Σ CostTick}.
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


  Definition cmp_spec (xs : list A) (f : A -> A -> bool) (c : val) (k : nat) : iProp Σ
    := ∀ (a1 a2 : A), {{{ ⧖ k }}} (c (inject a1) (inject a2)) {{{ v, RET #v; ⌜v = (f a1 a2)⌝ }}}.


  Definition part_cr k (xs : list A) : nat := (2 * k * length xs)%nat.

  Local Notation sorted := (StronglySorted Z.le).

  (* Can I delete this lemma? We don't care about functional correctness. *)
  Fact sorted_append pre post p :
    sorted pre → sorted post →
    (∀ x, In x pre → (x <= p)%Z) → (∀ x, In x post → (p < x)%Z) →
    sorted (pre ++ p :: post).
  Proof.
    intros Spre Spost ppre ppost.
    induction pre => /=.
    - apply SSorted_cons, List.Forall_forall => // ; intros.
      by apply Z.lt_le_incl, ppost.
    - apply SSorted_cons, List.Forall_forall => // ; [| clear IHpre].
      { apply IHpre.
        * apply StronglySorted_inv in Spre. by destruct Spre.
        * intros. apply ppre. set_solver. }
      intros x xppp.
      destruct (in_app_or _ _ _ xppp) as [x_pre | x_post] ; clear xppp.
      + apply StronglySorted_inv in Spre. destruct Spre.
        by apply (List.Forall_forall _ pre).
      + assert (a ≤ p)%Z as ap by (apply ppre ; constructor => //).
        assert (∀ z, In z (p::post) -> (p ≤ z)%Z) as ppost' ; last first.
        { etrans => //. apply ppost' => //. }
        intros z hz.
        destruct (in_inv hz) as [-> | zpost] => //.
        apply Z.lt_le_incl, ppost => //.
  Qed.



  (* Remove everything but the time bound computation *)
  Lemma qs_time_bound : ∀ (xs : list A) (l : val) f (SF : sorting_function A f) cmp k,
    {{{ ⧖ (tc_quicksort (2 * k) 0 (length xs)) ∗ (cmp_spec xs f cmp k) ∗ ⌜is_list xs l⌝ ∗ ⌜List.NoDup xs ⌝}}}
      qs cmp l
    {{{ v, RET v; ∃ xs', ⌜ is_list xs' v ⌝ }}}.
  Proof with wp_pures.
    rewrite /qs.
    iIntros (xs l f SF cmp k Φ) "HA1 hφ".
    do 2 wp_pure.
    iLöb as "Hqs" forall (xs l f SF k Φ).
    iDestruct "HA1" as "(H⧖ & #Hcmp & %hl & %hnd)".

    wp_pure.
    wp_bind (list_length _).
    wp_apply wp_list_length; [eauto|].
    iIntros (n) "->".
    wp_pures.

    (* Base case *)
    case_bool_decide.
    { wp_pures; iModIntro. iApply "hφ". destruct xs; [eauto |simpl in *; lia]. }

    (* Pick a pivot index at random, using advanced composition on the (2 * ...) term*)
    wp_pures.
    rewrite tc_quicksort_unfold.
    iAssert (⧖ (tc_pivot_lin (2*k) 0 (length xs)) ∗
             ⧖ (2 * foldr Rplus 0 (map (λ n0 : nat, tc_quicksort (2 * k) 0 n0) (seq 0 (length xs))) / length xs))%I
            with "[H⧖]" as "[H⧖lin H⧖Amp]".
    { destruct xs as [|? ?]; first (simpl in *; lia).

      iApply etc_split.
      - rewrite /tc_pivot_lin Nat.add_0_r. apply pos_INR.
      - apply Rcomplements.Rdiv_le_0_compat; last (rewrite -INR_0; apply lt_INR; simpl; lia).
        apply Rmult_le_pos; try lra.
        (* augh *)
        remember (length (a :: xs)) as W.
        clear.
        induction W as [|W' IHW]; [simpl; lra|].
        rewrite seq_S /=.
        rewrite map_app foldr_app /=.
        rewrite foldr_comm_acc; last (intros; simpl; lra).
        apply Rplus_le_le_0_compat; [apply tc_quicksort_nonneg|].
        by simpl in IHW.
      - iFrame.
    }

    wp_apply (wp_couple_rand_adv_comp' _ _ _ _ _ (tc_distr xs f SF (2*k) 0) with "[$]").
    { intros. apply tc_distr_nonneg; eauto. lia. }
    { rewrite /= tc_distr_equiv; [by rewrite Rplus_0_l | lia | done ]. }

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
    iAssert (⧖ (tc_quicksort (2 * k) 0 (index_to_rank xs f SF ip)) ∗
             ⧖ (tc_quicksort (2 * k) 0 (reverse_order (index_space (length xs)) (index_to_rank xs f SF ip))))%I
     with "[H⧖]" as "[H⧖L H⧖R]".
    { iApply etc_split.
      - apply tc_quicksort_nonneg.
      - apply tc_quicksort_nonneg.
      - rewrite /tc_distr /tc_distr_def /=.
        destruct xs; first (simpl in *; lia).
        iFrame.
    }
    wp_pures.

    iAssert (⧖ (k * (length xs)) ∗ ⧖ (k * (length xs)))%I with "[H⧖lin]" as "[H⧖Filt1 H⧖Filt2]".
    { rewrite /tc_pivot_lin.
      iApply etc_split.
      - apply Rmult_le_pos; apply pos_INR.
      - apply Rmult_le_pos; apply pos_INR.
      - iApply etc_irrel; last iFrame.
        rewrite Nat.add_0_r.
        repeat rewrite mult_INR.
        repeat rewrite S_INR.
        rewrite INR_0. lra.
    }


    wp_apply ((wp_list_filter (xsL ++ xsR) _ _ _ _ k ) with "[H⧖Filt1]"); first apply pos_INR.
    { iSplitR => //.
      - iIntros (x ψ) "!> H⧖ Hψ".
        wp_pures.
        wp_apply ("Hcmp" with "H⧖").
        iIntros (v ->); iApply "Hψ"; eauto.
      - iSplitR; first eauto.
        iApply (etc_weaken with "[$]").
        split.
        + apply Rmult_le_pos; apply pos_INR.
        + apply Rmult_le_compat_l; [apply pos_INR|].
          rewrite Hxs.
          apply le_INR.
          do 2 rewrite app_length.
          simpl. lia.
    }
    iIntros (rv) "%Hrv".
    wp_pures.

    wp_apply ((wp_list_filter (xsL ++ xsR) _ _ _ _ k) with "[H⧖Filt2]"); first apply pos_INR.
    { iSplitR => //.
      - iIntros (x ψ) "!> H⧖ Hψ".
        wp_pures.
        wp_apply ("Hcmp" with "H⧖").
        iIntros (v ->). wp_pures. iApply "Hψ".
        eauto.
      - iSplitR; first eauto.
        iApply (etc_weaken with "[$]").
        split.
        + apply Rmult_le_pos; apply pos_INR.
        + apply Rmult_le_compat_l; [apply pos_INR|].
          rewrite Hxs.
          apply le_INR.
          do 2 rewrite app_length.
          simpl. lia.
    }
    iIntros (lv) "%Hlv".
    do 8 wp_pure.
    wp_pure.

    wp_apply ("Hqs" $! (List.filter (f xp) (xsL ++ xsR)) rv f SF k with "[H⧖L]").
    { iClear "Hqs".
      iSplitL; [|iSplit].
      - iApply etc_irrel; [|iFrame].
        f_equal.
        rewrite /index_to_rank /rank /=.
        rewrite {2}Hxs.
        rewrite lookup_total_app_r; last lia.
        rewrite Hip Nat.sub_diag.
        simpl.
        rewrite {1}Hxs.
        replace (xp :: xsR) with ([xp] ++ xsR); last done.
        repeat rewrite List.filter_app.
        repeat rewrite app_length.
        rewrite /=.
        replace (strict_computable f xp xp) with false; last first.
        { rewrite /strict_computable. destruct (f xp xp); by simpl. }
        simpl length.
        rewrite Nat.add_0_l.
        (* True because xp is not in xsL or xsR *)
        assert (HninL : ¬ (In xp xsL)).
        { replace xs with ((xsL ++ [xp]) ++ xsR) in hnd; last by rewrite Hxs -app_assoc /=.
          apply NoDup_app_remove_r in hnd.
          apply NoDup_cons_iff.
          eapply (Permutation_NoDup _ hnd). Unshelve.
          symmetry.
          apply Permutation_cons_append. }
        assert (HninR: ¬ (In xp xsR)).
        { rewrite Hxs in hnd.
          apply NoDup_cons_iff.
          eapply NoDup_app_remove_l; eauto. }
        f_equal; f_equal.
        + clear Hxs Hip Hap Hrv Hlv.
          induction xsL as [|x0 xsL']; [simpl; done|].
          apply not_in_cons in HninL; destruct HninL as [? ?].
          rewrite /=.
          rewrite IHxsL'; [|done].
          replace (strict_computable f xp x0) with (f xp x0); [done|].
          admit.
        + clear Hxs Hip Hap Hrv Hlv.
          induction xsR as [|x0 xsR']; [simpl; done|].
          apply not_in_cons in HninR; destruct HninR as [? ?].
          rewrite /=.
          rewrite IHxsR'; [|done].
          replace (strict_computable f xp x0) with (f xp x0); [done|].
          admit.
      - rewrite /cmp_spec.
        iIntros (? ? ?) "!> ? H".
        wp_apply ("Hcmp" with "[$]").
        iIntros (?) "->"; iApply "H"; iPureIntro.
        done.
      - iPureIntro; split; [done|].
        apply List.NoDup_filter.
        eapply NoDup_remove_1.
        rewrite Hxs in hnd.
        eauto.
    }
    iIntros (lL) "[% %]".

    wp_apply ("Hqs" $! (List.filter (∽ f xp)%P (xsL ++ xsR)) lv f SF k with "[H⧖R]").
    { iClear "Hqs".

      iSplitL; [|iSplit].
      - iApply etc_irrel; [|iFrame].
        f_equal.

        rewrite /reverse_order /index_space seq_length.
        rewrite /index_to_rank /rank /=.
        rewrite {3}Hxs.
        rewrite lookup_total_app_r; last lia.
        rewrite Hip Nat.sub_diag.
        simpl.

        replace (length (List.filter (∽ f xp)%P (xsL ++ xsR)))
            with (length (List.filter (∽ f xp)%P xs)); last first.
        { rewrite {1}Hxs.
          rewrite List.filter_app app_length /=.
          replace (f xp xp) with true; last first.
          { destruct SF as [[[Hrefl ?] ?] ?].
            symmetry.
            apply Hrefl.
          }
          simpl.
          rewrite List.filter_app app_length /=.
          done.
        }

        rewrite /strict_computable.
        rewrite -(List.filter_length (f xp)).
        rewrite Nat.add_comm.
        rewrite -Nat.sub_add_distr.
        replace (length (List.filter (f xp) xs))
          with (1 + (length (List.filter (λ y : A, ((eqb (f xp y) true) && (eqb (f y xp) false))) xs))); [lia|].

        (* True by strictness and uniqueness *)
        admit.

      - rewrite /cmp_spec.
        iIntros (? ? ?) "!> ? H".
        wp_apply ("Hcmp" with "[$]").
        iIntros (?) "->"; iApply "H"; iPureIntro.
        done.
      - iPureIntro; split; [done|].
        apply List.NoDup_filter.
        eapply NoDup_remove_1.
        rewrite Hxs in hnd.
        eauto.
    }
    iIntros (lR) "[% %]".
    wp_pures.

    iClear "Hqs".
    wp_apply wp_list_cons => //; first eauto. iIntros (p_xs_gt_s h_p_xs_gt).
    iApply wp_list_append => //. iIntros "!>" (xs_le_p_gt_s L).
    iApply "hφ".
    eauto.
  Admitted.

End program.
