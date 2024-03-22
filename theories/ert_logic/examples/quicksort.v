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

   (* Proof irrelevance for fin *)
   Lemma fin_irrel (n : nat) (x y: fin n) : (fin_to_nat x = fin_to_nat y) -> (x = y).
   Proof. Admitted.

   Lemma fmap_compat `{A: Type} `{B: Type} f : list_fmap A B f = (fmap f).
   Proof. rewrite /fmap. done. Qed.

   Lemma fin_inj_FS_comm (n : nat) (l : list (fin n)) :
     FS <$> (fin_inj_incr _ <$> l) = fin_inj_incr _ <$> (FS <$> l).
   Proof.
     induction l; [done|].
     simpl in *.
     f_equal.
     f_equal.
     - apply functional_extensionality.
       intros.
       apply fin_irrel.
       admit.
     -

   Admitted.

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

  (* sorting_function makes it easy(tm) to prove the lemmas we need *)
  Record sorting_function (A : Type) (L : list A)
    := { sort_func :> A -> A -> bool ;
         sort_reflexive : forall a, sort_func a a = true ;
         sort_trans : forall a b c, sort_func a b = true /\ sort_func b c = true -> sort_func a c = true ;
         sort_inj : Forall (fun x => (Forall (fun y => (sort_func x y = true) /\ (sort_func y x = true) -> (x = y)) L)) L
    }.

  (* TODO: Define sorting functions for restrictions (cons, snoc, app) *)
  (* TODO: Define pushforward sorting functions *)


  Definition sorting_function_retract A L1 L2 :
    (incl L1 L2) -> sorting_function A L2 -> sorting_function A L1.
  Proof.
    intros Hincl f.
    destruct f as [f H1 H2 H3].
    eapply (Build_sorting_function _ _ f); eauto.

    apply List.Forall_forall.
    intros x Hx.
    eapply List.Forall_forall in H3; last eauto.
    apply List.Forall_forall.
    intros y Hy.
    eapply List.Forall_forall in H3; last eauto.
    done.
  Defined.

  (* Definition rank_lower (l : list Z) (x : Z) (Hx : x ∈ l) (HL : (0 < length l)%nat) : fin (S (length l - 1)%nat).
    refine (nat_to_fin (fin_transport_lemma _ _ HL (filter_length_lt (fun v => (v <? x)%Z) l x Hx _))).
  Proof. apply Is_true_false_2, Z.ltb_irrefl. Defined. *)

  Definition rank `{A : Type} `{L : list A} (f : sorting_function A L) : A -> nat := fun x => (length (List.filter (fun y => f x y) L) - 1).

   Definition index_to_rank `{A : Type} `{Hinhabited : Inhabited A} `{L : list A} (f : sorting_function A L) (index : nat) : nat
    := @rank _ _ f (L !!! index).


  (** Permutations over the index space *)

  (* Separate definition so it stops getting unfolded *)
  Definition index_space N : list nat := (seq 0%nat N).

  Lemma index_space_snoc N : (index_space (S N)) = (index_space N) ++ [N].
  Proof. by rewrite /index_space seq_S /=. Qed.

  Lemma index_space_cons N : (index_space (S N)) = 0 :: (fmap S (index_space N)).
  Proof. by rewrite /index_space /= fmap_S_seq. Qed.

  Opaque index_space.



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

  Lemma index_to_rank_nat_perm `{A : Type} `{Hinhabited : Inhabited A} {L : list A} (f : sorting_function A L) :
     (index_space (length L)) ≡ₚ ((index_to_rank f) <$> (index_space (length L))).
  Proof.
    intros.
    destruct (length L) as [|L0 L1] eqn:lenl.
    { simpl. constructor. }
    symmetry.
    apply nat_bijection_Permutation.
    - rewrite /FinFun.bFun.
      intros.
      rewrite /index_to_rank /rank.
      remember (λ y : A, sort_func A L f (L !!! x) y) as f1.
      rewrite -lenl.
      rewrite <- Nat.le_succ_l.
      replace (S _) with (length (List.filter f1 L)); first apply filter_length_le.
      assert (Hpos : (0 < length (List.filter f1 L))%nat); last lia.
      (* This is true becasue x (L !!! x) ∈ L*)
      rewrite Heqf1.
      (* Bound below by the filter after dropping x elemenets *)
      rewrite -{3}(take_drop x L).
      rewrite List.filter_app app_length.
      apply PeanoNat.Nat.add_pos_r.
      (* Bound below by the first element *)
      destruct (drop x L) as [| d0 ? ] eqn:Hd.
      { assert (HK : (0 < length (drop x L))%nat) by (rewrite drop_length; lia).
        exfalso.
        rewrite Hd in HK.
        simpl in *. lia.
      }
      replace (d0 :: l) with ([d0] ++ l); last by simpl.
      rewrite List.filter_app app_length.
      apply PeanoNat.Nat.add_pos_l.
      simpl.
      rewrite -{2}(take_drop x L) Hd.
      rewrite lookup_total_app_r; last apply firstn_le_length.
      rewrite take_length_le; last (simplify_eq; lia).
      rewrite Nat.sub_diag.
      rewrite /= sort_reflexive /=.
      lia.
    - rewrite /FinFun.Injective.
      intros ? ? HRk.
      (* Uses uniqueness, probably need to prove an aux. lemma *)
      rewrite /index_to_rank /rank in HRk.
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
  Proof. Admitted.

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
  Definition tc_distr_def `{L : list A} (f : sorting_function A L) (CA CB : nat) : nat -> R
    := fun index =>
         match L with
         | [] => tc_base
         | _ => ((tc_quicksort CA CB ∘ (index_to_rank f)) index +
                 (tc_quicksort CA CB ∘ reverse_order (index_space (length L)) ∘ (index_to_rank f)) index)%R
         end.

  (* Distribution, in a form which typechecks with advanced composition *)
  Definition tc_distr (L : list A) (f : sorting_function A L) CA CB : (fin (S (Z.to_nat (length L - 1)))) -> R
    := (tc_distr_def f CA CB) ∘ fin_to_nat.


  Lemma tc_distr_nonneg L f CA CB i : (0 < length L)%nat -> (0 <= tc_distr L f CA CB i)%R.
  Proof.
    intros.
    rewrite /tc_distr /tc_distr_def /=.
    destruct L; first (simpl in *; lia).
    apply Rplus_le_le_0_compat; apply tc_quicksort_nonneg.
  Qed.


  Lemma foldr_reduction_1 (L : list A) g (f : sorting_function A L)  :
     (foldr (Rplus ∘ g ∘ index_to_rank f) 0 (index_space (length L)))%R
   = (foldr (Rplus ∘ g) 0 (index_space (length L)))%R.
  Proof.
    intros.
    rewrite (fold_R_fin_perm _ (index_to_rank f)).
    - (* generalize me *)
      remember (index_space (length L)) as LL.
      clear HeqLL.
      remember (index_to_rank f) as g1.
      induction LL as [|L0 L' IH].
      + simpl; lra.
      + simpl. f_equal. apply IH.
    - apply index_to_rank_nat_perm.
  Qed.

  Lemma foldr_reduction_2 (L : list A) g (f : sorting_function A L) :
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
  Lemma tc_distr_equiv L f CA CB :
  (0 < length L)%nat ->
  (SeriesC (λ n : fin (S (Z.to_nat (length L - 1))), 1 / S (Z.to_nat (length L - 1)) * tc_distr L f CA CB n))%R =
        (2 * foldr Rplus 0 (map (λ n : nat, tc_quicksort CA CB n) (index_space (length L))) / (length L))%R.
  Proof.
    intros Hlength.
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
    replace (foldr (Rplus ∘ (tc_distr_def f CA CB ∘ fin_to_nat)) 0%R (enum (fin (S (Z.to_nat (Z.of_nat (length L) - 1))))))
      with  (foldr (Rplus ∘ tc_distr_def f CA CB) 0%R (index_space (length L)));
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
    replace (foldr (Rplus ∘ tc_distr_def f CA CB) 0%R (index_space (length L)))
       with (foldr (Rplus ∘ tc_quicksort CA CB ∘ (index_to_rank f)) 0%R (index_space (length L)) +
             foldr (Rplus ∘ tc_quicksort CA CB ∘ (reverse_order (index_space (length L))) ∘ (index_to_rank f)) 0%R (index_space (length L)))%R;

      last first.
    { rewrite /tc_distr_def.
      remember (Rplus ∘ tc_quicksort CA CB ∘ index_to_rank f) as f1.
      remember (Rplus ∘ tc_quicksort CA CB ∘ reverse_order (index_space (length L)) ∘ index_to_rank f) as f2.
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
    do 2 rewrite (foldr_reduction_1 _ _ f).
    rewrite (foldr_reduction_2 _ _ f).

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


  Definition cmp_spec (xs : list A) (f : sorting_function A xs) (c : val) (k : nat) : iProp Σ
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
  Lemma qs_time_bound : ∀ (xs : list A) (l : val) (f : sorting_function A xs) cmp k,
    {{{ ⧖ (tc_quicksort (2 * k) 0 (length xs)) ∗ (cmp_spec xs f cmp k) ∗ ⌜is_list xs l⌝ }}}
      qs cmp l
    {{{ v, RET v; ∃ xs', ⌜ is_list xs' v ⌝ }}}.
  Proof with wp_pures.
    rewrite /qs.
    iIntros (xs l f cmp k Φ) "HA1 HA2".
    do 2 wp_pure.
    iRevert "HA1 HA2".
    iLöb as "Hqs" forall (xs l f k Φ).
    iIntros "(H⧖ & #Hcmp & %hl) hφ".

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

    wp_apply (wp_couple_rand_adv_comp' _ _ _ _ _ (tc_distr _ f (2*k) 0) with "[$]").
    { intros. apply tc_distr_nonneg; eauto. lia. }
    { rewrite /= tc_distr_equiv; [by rewrite Rplus_0_l | lia]. }

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
    iAssert (⧖ (tc_quicksort (2 * k) 0 (index_to_rank f ip)) ∗
             ⧖ (tc_quicksort (2 * k) 0 (reverse_order (index_space (length xs)) (index_to_rank f ip))))%I
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
    do 9 wp_pure.

    (* sort xs_gt *)
    wp_apply ("Hqs" with "[H⧖L]").
    { iClear "Hqs".
      iSplitL; [|iSplit]; last eauto.
      { iApply etc_irrel; [|iFrame].
        f_equal.
        rewrite /index_to_rank /rank.
        rewrite {3}Hxs.
        rewrite lookup_total_app_r; last lia.
        rewrite Hip Nat.sub_diag.
        simpl.
        rewrite {2}Hxs.
        replace (xp :: xsR) with ([xp] ++ xsR); last done.
        repeat rewrite List.filter_app.
        repeat rewrite app_length.
        rewrite /=.
        rewrite sort_reflexive.
        simpl length.
        rewrite (Nat.add_comm 1 _) Nat.add_assoc Nat.add_sub.
        f_equal.
      }

      rewrite /cmp_spec.
      iIntros (? ? ?) "!> ? H".
      wp_apply ("Hcmp" with "[$]").
      iIntros (?) "->"; iApply "H"; iPureIntro.
      Unshelve.
      2: { eapply sorting_function_retract; last eapply f.
           eapply incl_tran; first eapply incl_filter.
           rewrite Hxs.
           eapply incl_app_app; first apply incl_refl.
           apply incl_tl; apply incl_refl.
      }
      rewrite /sorting_function_retract /=.
      destruct f; simpl; done.
    }
    iIntros (lL) "[% %]".

    wp_apply ("Hqs" with "[H⧖R]").
    { iClear "Hqs".
      iSplitL; [|iSplit]; last eauto.
      { iApply etc_irrel; [|iFrame].
        f_equal.

        rewrite /reverse_order /index_space seq_length.
        rewrite /index_to_rank /rank.
        rewrite {4}Hxs.
        rewrite lookup_total_app_r; last lia.
        rewrite Hip Nat.sub_diag.
        simpl.

        rewrite -(PeanoNat.Nat.sub_succ (_ - 1) (_ - 1)).
        rewrite -Nat.add_1_l -Nat.le_add_sub; last first.
        { rewrite Hxs app_length /=; lia. }
        rewrite -Nat.add_1_l -Nat.le_add_sub; last first.
        { rewrite {2}Hxs List.filter_app app_length /=.
          rewrite sort_reflexive /=.
          lia.
        }

        replace (length (List.filter (∽ f xp)%P (xsL ++ xsR)))
            with (length (List.filter (∽ f xp)%P xs));
          last first.
        { rewrite {2}Hxs.
          rewrite List.filter_app app_length /=.
          rewrite sort_reflexive /=.
          rewrite List.filter_app app_length /=.
          done.
        }
        rewrite -(List.filter_length (f xp)).

        replace (length (List.filter (λ y : A, f xp y) xs))
          with  (length (List.filter (f xp) xs)) by f_equal.
        lia.
      }
      rewrite /cmp_spec.
      iIntros (? ? ?) "!> ? H".
      wp_apply ("Hcmp" with "[$]").
      iIntros (?) "->"; iApply "H"; iPureIntro.
      Unshelve.
      2: { eapply sorting_function_retract; last eapply f.
           eapply incl_tran; first eapply incl_filter.
           rewrite Hxs.
           eapply incl_app_app; first apply incl_refl.
           apply incl_tl; apply incl_refl.
      }
      simpl.
      rewrite /sorting_function_retract /=.
      destruct f; simpl; done.
    }
    iIntros (lR) "[% %]".
    wp_pures.

    iClear "Hqs".
    wp_apply wp_list_cons => //; first eauto. iIntros (p_xs_gt_s h_p_xs_gt).
    iApply wp_list_append => //. iIntros "!>" (xs_le_p_gt_s L).
    iApply "hφ".
    eauto.
  Qed.

End program.
