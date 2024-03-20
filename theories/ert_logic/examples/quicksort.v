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



Section accounting.
  (** Defines the Quicksort recurrence relation, an O(n log n) upper bound, and the advanced composition lemma *)

  (* Tighter bounding argument necessitates the pivot take time An+B *)
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

  (* Inline? Get something working first. *)
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


   (* Source of many deeply annoying lemmas involving fin_enum *)
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
   Proof.
    apply functional_extensionality.
    intros.
    induction x; simpl; done.
   Qed.

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


  (* Non-haunted version with seq instead of fin_enum *)
  (* An alternative to proving all of that fin_enum stuff might be to just define the seq version
     directly in the refine using a dependent pattern match. *)
  (* OTOH the fin_enum stuff comes up all of the time, so maybe we want it anyways? *)
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

  Lemma tc_quicksort_0 A B : tc_quicksort A B 0%nat = tc_base.
  Proof. rewrite tc_quicksort_unfold. done. Qed.

  Lemma tc_quicksort_S A B n :
    (1 <= n)%nat ->
    tc_quicksort A B n =
            ((tc_pivot_lin A B n) + 2 * (foldr Rplus 0 $ map (fun i => ((tc_quicksort A B i))%NNR) $ seq 0%nat n)%NNR /n)%R.
  Proof. intros. rewrite tc_quicksort_unfold. destruct n; [lia|]. done. Qed.

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
    Set Printing Coercions.
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



  (* TODO for advanded composotion *)
  (* [x] Need to define a Prop to represent unique lists*)
  (* [x] Need to define rank within a list *)
  (* [ ] Need to show that summing over __ is the same as summing over rank <$> __ *)
  (* [ ] Need to show that mean of sum (without rank) is preserved *)

  Local Notation sorted := (StronglySorted Z.le).

  Definition list_dups (l : list Z) (x : Z) : nat := length (List.filter (fun v => (v =? x)%Z) l).

  Definition list_unique (l : list Z) : Prop := Forall (fun x => list_dups l x = 1%nat) l.

  (*
    Definition pre_rank_lower (l : list Z) (x : Z) : fin (S (length l))
    := nat_to_fin (Arith_prebase.le_lt_n_Sm _ _ (filter_length_le (fun v => (v <? x)%Z) l)). *)


  #[local] Definition fin_transport_lemma (A B : nat) : (0 < B)%nat -> (A < B)%nat -> (A < (S (B - 1)))%nat.
  Proof. intros. lia. Qed.


  Definition rank_lower (l : list Z) (x : Z) (Hx : x ∈ l) (HL : (0 < length l)%nat) : fin (S (length l - 1)%nat).
    refine (nat_to_fin (fin_transport_lemma _ _ HL (filter_length_lt (fun v => (v <? x)%Z) l x Hx _))).
  Proof. apply Is_true_false_2, Z.ltb_irrefl. Defined.

  Definition index_to_rank (l : list Z) (HL : (0 < length l)%nat ) (index : fin (S (length l - 1)%nat)) : fin (S (length l - 1))%nat.
    refine (rank_lower l (l !!! fin_to_nat index) _ HL).
  Proof. apply elem_of_list_lookup_total_2.
         assert (fin_to_nat index < (S (length l - 1)%nat)) by apply fin_to_nat_lt.
         lia.
  Defined.

  Lemma index_to_rank_bij (l : list Z) HL : (list_unique l) -> Bij (index_to_rank l HL).
  Proof. Admitted.

  #[local] Lemma reverse_lemma (n m : nat) (H : (0 < n)%nat) : (n - 1 - m < n)%nat.
  Proof. intros. lia. Qed.

  Definition reverse_order N (H : (0 < N)%nat) (s : fin N) : fin N.
    refine (nat_to_fin (reverse_lemma N (fin_to_nat s) H)).
  Defined.

  Lemma reverse_order_bij N H : Bij (reverse_order N H).
  Proof.
    split.
    - rewrite /Inj; intros x y ?.
      apply fin_irrel.
      assert (HR : fin_to_nat (reverse_order N H x) = fin_to_nat (reverse_order N H y)); [f_equal; done|].
      rewrite /reverse_order in HR.
      do 2 rewrite fin_to_nat_to_fin in HR.
      pose P1 := fin_to_nat_lt x.
      pose P2 := fin_to_nat_lt y.
      lia.
    - rewrite /Surj. intros y.
      eexists (reverse_order N H y).
      rewrite /reverse_order.
      apply fin_irrel.
      do 2 rewrite fin_to_nat_to_fin.
      pose P1 := fin_to_nat_lt y.
      lia.
  Qed.

  (* The thing we're going to plug into advanced composition *)
  (* IN THEORY: this quantity of time credit should be good enough to finish the recursive calls, plus whatever extra stuff we
     have lying around from the pivot term *)
  Definition tc_distr A B xs (index : fin (S (length xs - 1)%nat)) (HL : (0 < length xs)%nat) : R
    := (tc_quicksort A B (fin_to_nat (index_to_rank xs HL index)) +
        tc_quicksort A B (reverse_order _ (fin_transport_lemma _ _ HL HL) (index_to_rank xs HL index)))%R.

  (* Advanced composition side condition: Turn the junk we get from the advanced composition rule back into the credit definition we have before *)
  (* FIXME: Change all above to be reals, and remove the map nonneg *)
  Lemma tc_distr_equiv A B (xs : list Z) (HL : (0 < length xs)%nat)
    : (SeriesC (fun s : fin (S (length xs - 1)%nat) => 1 / (S (length xs - 1)%nat) * (tc_distr A B xs s HL)))%R =
        (2 * (foldr Rplus 0%R $ map (fun i => (tc_quicksort A B i)) $ (seq 0%nat (length xs)%nat)) / (length xs))%R.
  Proof. Admitted.

  (* This will take several steps. Two of the steps involve a series (or fold) being invariant under a bijection:
      - one bijection eliminates the index_to_rank from tc_quicksort
      - another bijection

    The proof will convert through three forms:
      - A SeriesC over fin type       (form of adv comp)
      - A fold over fin_enum
      - A fold over seq               (form of tc_quicksort def)
    We can do the bijection steps at any of them.
   *)

  (* Probably easiest to use bijections over fin types? Otherwise I have to roll my own equivalent. *)

  (* Easily generalizable if useful *)
  Lemma fold_R_fin_bij N :
    ∀ f g,  Bij g ->
    (foldr Rplus 0%R $ map f $ fin_enum N) = (foldr Rplus 0%R $ map f $ map g $ fin_enum N).
  Proof.
    Set Printing Coercions.
    (* *)
    (* Idea: split off the last term of the LHS by induction. Have to show that we
          can commute out a term from the RHS (should be easy) and then redefine a
          new bijection g' so that we can apply the IH. *)

  Admitted.


End accounting.


Section cost.
  (** Cost fucntion for Quicksort: number of comparisons *)

  Definition cmp_cost_fn (e : expr) :=
    match e with
    | BinOp LeOp _ _ => nnreal_one
    | BinOp LtOp _ _ => nnreal_one
    | _ => nnreal_zero
    end.


  Program Definition CostCmp : Costfun prob_lang := (Build_Costfun _ cmp_cost_fn _ _).
  Next Obligation.
    eexists 1.
    intros; simpl.
    rewrite /cmp_cost_fn.
    destruct e; simpl; try lra.
    destruct op; simpl; try lra.
  Qed.
  Next Obligation.
    intros; simpl.
    rewrite /cmp_cost_fn.
    destruct e; simpl; try lra.
    destruct op; simpl; try lra.
  Qed.
  (* Next Obligation. Admitted. *)

  Context `{!ert_clutchGS Σ CostCmp}.

  #[local] Lemma test_wp_pure :
       {{{ ⧖ (nnreal_nat 1) }}} (if: (#0 < #1) then #() else #() ) {{{ RET #(); ⧖ (nnreal_nat 0) }}}.
  Proof.
    Set Printing Coercions.
    iIntros (x) "Hx Hp".
    wp_pure.
    wp_pure.
    iModIntro.
    iApply "Hp".
    simpl in *.
    Unset Printing Coercions.
  Abort.


End cost.

Section list.
  Context `{!ert_clutchGS Σ CostCmp }.



  Definition list_nil := NONE.

  Notation "[ ]" := (list_nil) (format "[ ]") : expr_scope.

  Definition list_cons : val := λ: "elem" "list", SOME ("elem", "list").

  Infix "::" := list_cons (at level 60, right associativity) : expr_scope.

  Notation "[ x ]" := (list_cons x list_nil) (format "[ x ]") : expr_scope.

  Notation "[ x ; y ; .. ; z ]" := (list_cons x (list_cons y .. (list_cons z list_nil) ..)) : expr_scope.


  (*
  Definition list_head : val :=
    λ: "l", match: "l" with
      SOME "a" => SOME (Fst "a")
    | NONE => NONE
    end.

  Definition list_tail : val :=
    λ: "l", match: "l" with
      SOME "a" => Snd "a"
    | NONE => NONE
    end.

  Definition list_fold : val :=
    rec: "list_fold" "handler" "acc" "l" :=
    match: "l" with
      SOME "a" =>
      let: "f" := Fst "a" in
      let: "s" := Snd "a" in
      let: "acc" := "handler" "acc" "f" in
      "list_fold" "handler" "acc" "s"
    | NONE => "acc"
    end.

  Definition list_iter : val :=
    rec: "list_iter" "handler" "l" :=
    match: "l" with
      SOME "a" =>
      let: "tail" := Snd "a" in
      "handler" (Fst "a");;
      "list_iter" "handler" "tail"
    | NONE => #()
    end.

  Definition list_iteri_loop : val :=
    rec: "list_iteri_loop" "handler" "i" "l" :=
    match: "l" with
      SOME "a" =>
      let: "tail" := Snd "a" in
      "handler" "i" (Fst "a");;
      "list_iteri_loop" "handler" ("i" + #1) "tail"
    | NONE => #()
    end.

  Definition list_iteri : val :=
    λ: "handler" "l", list_iteri_loop "handler" #0 "l".

  Definition list_mapi_loop : val :=
    rec: "list_mapi_loop" "f" "k" "l" :=
    match: "l" with
      SOME "a" =>
      "f" "k" (Fst "a") :: "list_mapi_loop" "f" ("k" + #1) (Snd "a")
    | NONE => NONE
    end.

  Definition list_mapi : val := λ: "f" "l", list_mapi_loop "f" #0 "l".

  Definition list_map : val :=
    rec: "list_map" "f" "l" :=
    match: "l" with
      SOME "a" => "f" (Fst "a") :: "list_map" "f" (Snd "a")
    | NONE => NONE
    end.
    *)

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

  (*
  Definition list_nth : val :=
    rec: "list_nth" "l" "i" :=
    match: "l" with
      SOME "a" =>
      (if: "i" = #0
       then  SOME (Fst "a")
       else  "list_nth" (Snd "a") ("i" - #1))
    | NONE => NONE
    end.

  Definition list_mem : val :=
    rec: "list_mem" "x" "l" :=
    match: "l" with
      SOME "a" =>
      let: "head" := Fst "a" in
      let: "tail" := Snd "a" in
      ("x" = "head") || ("list_mem" "x" "tail")
    | NONE => #false
    end.

*)
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

  (*
  Definition list_remove_nth_total : val :=
    rec: "list_remove_nth_total" "l" "i" :=
      match: "l" with
      SOME "a" =>
      (if: "i" = #0
       then  Snd "a"
       else  (Fst "a") :: ("list_remove_nth_total" (Snd "a") ("i" - #1)))
      | NONE => list_nil
      end.

  Definition list_find_remove : val :=
    rec: "list_find_remove" "f" "l" :=
    match: "l" with
      SOME "a" =>
      let: "head" := Fst "a" in
      let: "tail" := Snd "a" in
      (if: "f" "head"
       then  SOME ("head", "tail")
       else
         let: "r" := "list_find_remove" "f" "tail" in
         match: "r" with
           SOME "b" =>
           let: "head'" := Fst "b" in
           let: "tail'" := Snd "b" in
           SOME ("head'", ("head" :: "tail'"))
         | NONE => NONE
         end)
    | NONE => NONE
    end.

  Definition list_sub : val :=
    rec: "list_sub" "i" "l" :=
    (if: "i" ≤ #0
     then  []
     else
       match: "l" with
        SOME "a" => Fst "a" :: "list_sub" ("i" - #1) (Snd "a")
      | NONE => []
      end).

  Definition list_rev_aux : val :=
    rec: "list_rev_aux" "l" "acc" :=
    match: "l" with
      NONE => "acc"
    | SOME "p" =>
        let: "h" := Fst "p" in
        let: "t" := Snd "p" in
        let: "acc'" := "h" :: "acc" in
        "list_rev_aux" "t" "acc'"
    end.

  Definition list_rev : val := λ: "l", list_rev_aux "l" [].

  *)
  Definition list_append : val :=
    rec: "list_append" "l" "r" :=
    match: "l" with
      NONE => "r"
    | SOME "p" =>
        let: "h" := Fst "p" in
        let: "t" := Snd "p" in
        "h" :: "list_append" "t" "r"
    end.
(*
  Definition list_is_empty : val :=
    λ: "l", match: "l" with
      NONE => #true
    | SOME "_p" => #false
    end.

  Definition list_forall : val :=
    rec: "list_forall" "test" "l" :=
    match: "l" with
      NONE => #true
    | SOME "p" =>
        let: "h" := Fst "p" in
        let: "t" := Snd "p" in
        ("test" "h") && ("list_forall" "test" "t")
    end.

  Definition list_make : val :=
    rec: "list_make" "len" "init" :=
    (if: "len" = #0
     then  []
     else  "init" :: "list_make" ("len" - #1) "init").

  Definition list_init : val :=
    λ: "len" "f",
    letrec: "aux" "acc" "i" :=
      (if: "i" = "len"
       then  list_rev "acc"
       else  "aux" (("f" "i") :: "acc") ("i" + #1)) in
      "aux" [] #0.


  Definition list_seq : val :=
    rec: "list_seq" "st" "ln" :=
      (if: "ln" ≤ #0
       then  list_nil
       else  list_cons "st" ("list_seq" ("st" + #1)  ("ln" - #1))).

  Definition list_update : val :=
    rec: "list_update" "l" "i" "v" :=
    match: "l" with
      SOME "a" =>
      (if: "i" = #0
       then  "v" :: list_tail "l"
       else  Fst "a" :: "list_update" (Snd "a") ("i" - #1) "v")
    | NONE => []
    end.

  Definition list_suf : val :=
    rec: "list_suf" "i" "l" :=
    (if: "i" = #0
     then  "l"
     else
       match: "l" with
        NONE => NONE
      | SOME "p" => "list_suf" ("i" - #1) (Snd "p")
      end).

  Definition list_inf_ofs : val :=
    λ: "i" "ofs" "l",
    (if: "ofs" ≤ #0
     then  []
     else  list_sub "ofs" (list_suf "i" "l")).

  Definition list_inf : val :=
    λ: "i" "j" "l", list_inf_ofs "i" (("j" - "i") + #1) "l".

  Definition list_split : val :=
    rec: "list_split" "i" "l" :=
    (if: "i" ≤ #0
     then  ([], "l")
     else
       match: "l" with
        NONE => ([], [])
      | SOME "p" =>
          let: "x" := Fst "p" in
          let: "tl" := Snd "p" in
          let: "ps" := "list_split" ("i" - #1) "tl" in
          ("x" :: Fst "ps", Snd "ps")
      end).
  End list_code.

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
  *)

  Section list_specs.
    Context `{!ert_clutchGS Σ CostCmp }.
    Context `[!Inject A val].

    Fixpoint is_list (l : list A) (v : val) :=
      match l with
      | [] => v = NONEV
      | a::l' => ∃ lv, v = SOMEV ((inject a), lv) ∧ is_list l' lv
    end.

  (*

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

    Lemma wp_list_singleton E a :
      {{{ True }}}
        list_cons (inject a) list_nil @ E
      {{{ v, RET v; ⌜is_list [a] v⌝ }}}.
    Proof.
      iIntros (Φ) "_ HΦ". wp_pures.
      wp_apply (wp_list_cons _ []); [done|].
      iIntros (v' Hv').
      by iApply "HΦ".
    Qed.

    Lemma wp_list_head E lv l :
      {{{ ⌜is_list l lv⌝ }}}
        list_head lv @ E
      {{{ v, RET v;
          ⌜(l = [] ∧ v = NONEV) ∨ (∃ a l', l = a :: l' ∧ v = SOMEV (inject a))⌝ }}}.
    Proof.
      iIntros (Φ a) "HΦ".
      wp_lam. destruct l; simpl in *; subst.
      - wp_pures. iApply "HΦ". iPureIntro. by left.
      - destruct a as [lv' [Hhead Htail]] eqn:Heq; subst.
        wp_pures. iApply "HΦ". iPureIntro. right. eauto.
    Qed.

    Lemma wp_list_tail E lv l :
      {{{ ⌜is_list l lv⌝ }}}
        list_tail lv @ E
      {{{ v, RET v; ⌜is_list (tail l) v⌝}}}.
    Proof.
      iIntros (Φ a) "HΦ".
      wp_lam. destruct l; simpl in *; subst.
      - wp_match. wp_inj. by iApply "HΦ".
      - destruct a as [lv' [Hhead Htail]] eqn:Heq; subst.
        wp_match. wp_proj. by iApply "HΦ".
    Qed.
   *)

    (* ⧖ 0 *)
    Lemma wp_list_length E l lv :
      {{{ ⧖ 0%R ∗ ⌜is_list l lv⌝ }}}
        list_length lv @ E
      {{{ v, RET #v; ⌜v = length l⌝ }}}.
    Proof.
      iIntros (Φ) "(Htc & Ha) HΦ".
      iInduction l as [|a l'] "IH" forall (lv Φ);
      iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_pures.
      - wp_rec.
        wp_match. iApply ("HΦ" $! 0%nat); done.
      - wp_rec.
        simpl.
        destruct Ha as [lv' [Hlv Hlcoh]]; subst.
        wp_match; simpl.
        wp_proj. wp_bind (list_length _); simpl.
        iApply ("IH" $! _ _ with "[Htc]"); eauto.
        { iApply (etc_weaken with "Htc"); lra. }
        iNext. iIntros.
        (* Why can't wp_op find the binop? *)
        Fail wp_op.
        (* iSpecialize ("HΦ" $! (1 + v)%nat).
        rewrite Nat2Z.inj_add. iApply "HΦ"; by auto. *)
    Admitted.


    (*

    Lemma wp_list_iter_invariant' Φ1 Φ2 (Ψ: list A -> iProp Σ) P E l lv handler
           lrest:
      (∀ (a : A) l',
          {{{ ⌜∃ b, lrest ++ l = l' ++ a :: b⌝ ∗ P ∗ Ψ l' ∗ Φ1 a }}}
            (Val handler) (inject a) @ E
          {{{v, RET v; P ∗ Ψ (l' ++ [a]) ∗ Φ2 a }}}) -∗
      {{{ ⌜is_list l lv⌝ ∗ P ∗ Ψ lrest ∗ [∗ list] a∈l, Φ1 a}}}
        list_iter (Val handler) lv @ E
      {{{ RET #(); P ∗ Ψ (lrest++l) ∗ [∗ list] a∈l, Φ2 a }}}.
    Proof.
      rewrite /list_iter.
      iInduction l as [|a l'] "IH" forall (lv lrest);
      iIntros "#Helem"; iIntros (Φ') "!# (Ha & HP & Hl & HΦ) Hk";
      iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_pures.
      - rewrite app_nil_r. iApply "Hk"; iFrame. done.
      - assert (Helemof: a ∈ a :: l').
        { constructor. }
        destruct Ha as [lv' [Hlv Hlcoh]]; subst.
        wp_pures.
        iDestruct (big_sepL_cons with "HΦ") as "[Ha Hl']".
        wp_apply ("Helem" with "[HP Hl Ha]"); iFrame; eauto.
        iIntros (v) "(HP & Ha & HΦ)". simpl. wp_seq.
        iApply ("IH" $! lv' (lrest ++ [a]) with "[] [$HP Ha Hl']"); eauto.
        { iIntros (a' lrest' HΦ'') "!# (%Hin'&HP&Hlrest'&HΦ) Hk".
          wp_apply ("Helem" with "[HP Hlrest' HΦ]"); iFrame.
          iPureIntro. destruct Hin' as [b Hin']. exists b.
          by rewrite -app_assoc in Hin'. }
        { iSplit; eauto. iFrame. }
        iNext. iIntros "(HP & Hl)". iApply "Hk". iFrame.
          by rewrite -app_assoc /=.
    Qed.

    Lemma wp_list_iter_invariant Φ1 Φ2 (Ψ: list A -> iProp Σ) P E l lv handler :
      (∀ (a : A) l',
          {{{ ⌜∃ b, l = l' ++ a :: b⌝ ∗ P ∗ Ψ l' ∗ Φ1 a }}}
            (Val handler) (Val (inject a)) @ E
          {{{v, RET v; P ∗ Ψ (l' ++ [a]) ∗ Φ2 a }}}) -∗
      {{{ ⌜is_list l lv⌝ ∗ P ∗ Ψ [] ∗ [∗ list] a∈l, Φ1 a}}}
        list_iter (Val handler) lv @ E
      {{{ RET #(); P ∗ Ψ l ∗ [∗ list] a∈l, Φ2 a}}}.
    Proof.
      replace l with ([]++l); last by apply app_nil_l.
      iApply wp_list_iter_invariant'.
    Qed.

    Lemma wp_list_iter_idx_aux n Φ Ψ P E l lv handler :
      (∀ i (a : A),
          {{{ P ∗ Φ i a }}}
            (Val handler) (Val (inject a)) @ E
          {{{v, RET v; P ∗ Ψ i a }}}) -∗
      {{{ ⌜is_list l lv⌝ ∗ P ∗ [∗ list] i↦a ∈ l, Φ (n + i)%nat a }}}
        list_iter (Val handler) lv @ E
      {{{ RET #(); P ∗ [∗ list] i↦a ∈ l, Ψ (n + i)%nat a }}}.
    Proof.
      rewrite /list_iter.
      iIntros "#Helem"; iIntros (Φ') "!# (Ha & HP & Hl) HΦ".
      iLöb as "IH" forall (l lv n);
      destruct l as [|a l'];
      iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_pures.
      - iApply "HΦ"; eauto.
      - assert (Helemof: a ∈ a :: l').
        { constructor. }
        destruct Ha as [lv' [Hlv Hlcoh]]; subst.
        wp_pures.
        iDestruct (big_sepL_cons with "Hl") as "[Ha Hl']".
        wp_apply ("Helem" with "[HP Ha]"); iFrame; eauto.
        iIntros (v) "[HP Ha]". simpl. wp_seq.
        iApply ("IH" $! l' _ (S n) with "[] [$HP] [Hl']"); [done| |].
        { iApply (big_sepL_impl with "Hl' []").
          iIntros "!>" (k x Hlookup) "H".
          replace (n + S k)%nat with (S n + k)%nat by lia.
          done. }
        iNext. iIntros "(HP & Hl)". iApply "HΦ". iFrame.
        iApply (big_sepL_impl with "Hl []").
        iIntros "!>" (k x Hlookup) "H".
        replace (n + S k)%nat with (S n + k)%nat by lia.
        done.
    Qed.

    Lemma wp_list_iter_idx Φ Ψ P E l lv handler :
      (∀ i (a : A),
          {{{ P ∗ Φ i a }}}
            (Val handler) (Val (inject a)) @ E
          {{{v, RET v; P ∗ Ψ i a }}}) -∗
      {{{ ⌜is_list l lv⌝ ∗ P ∗ [∗ list] i↦a ∈ l, Φ i a }}}
        list_iter (Val handler) lv @ E
      {{{ RET #(); P ∗ [∗ list] i↦a ∈ l, Ψ i a }}}.
    Proof.
      iIntros "#H" (Φ') "!# (%Ha & HP & Hl) HΦ".
      iApply (wp_list_iter_idx_aux 0 Φ _ _ _ _ lv with "[H] [HP $Hl] HΦ").
      { iIntros (i a). iApply "H". }
      by iFrame.
    Qed.

    Lemma wp_list_iter Φ Ψ P E l lv handler :
      (∀ (a : A),
          {{{ P ∗ Φ a }}}
            (Val handler) (Val (inject a)) @ E
          {{{v, RET v; P ∗ Ψ a }}}) -∗
      {{{ ⌜is_list l lv⌝ ∗ P ∗ [∗ list] a ∈ l, Φ a }}}
        list_iter (Val handler) lv @ E
      {{{ RET #(); P ∗ [∗ list] a ∈ l, Ψ a }}}.
    Proof.
      rewrite /list_iter.
      iIntros "#H" (Φ') "!# (%Ha & HP & Hl) HΦ".
      iApply (wp_list_iter_idx with "[H] [HP $Hl] HΦ").
      { iIntros (i a). iApply "H". }
      by iFrame.
    Qed.

    Corollary wp_list_iter_err `{!Inject B val} (l : list A) (fv lv : val)
      (P : A -> iProp Σ) (Q : A -> iProp Σ) (err : A -> nonnegreal) E :
      {{{ (∀ (x : A),
            {{{ P x ∗ € (err x)}}}
              fv (inject x) @ E
            {{{ fr, RET fr; Q x }}}) ∗
          ⌜is_list l lv⌝ ∗
          [∗ list] x∈l, (P x ∗ € (err x))
      }}}
        list_iter fv lv @ E
        {{{ rv, RET rv; [∗ list] x ∈ l, Q x
        }}}.
    Proof.
      iIntros (Φ) "[#Hf [%Hil HP]] HΦ".
      iApply (wp_list_iter_idx (λ _ a, P a ∗ € (err a))%I (λ _ a, Q a) ⌜True⌝%I _ l
          with "[] [HP] [HΦ]") ; try iFrame.
      - iIntros (i a φ) "!> (_&P_a&err_a) Hφ".
        iApply ("Hf" with "[$P_a $err_a]"). iIntros "!>" (?) "Qa". iApply "Hφ" ; iFrame.
      - easy.
      - iIntros "!> [_ ?]". by iApply "HΦ".
    Qed.

    Corollary wp_list_iter_err_constant `{!Inject B val} (l : list A) (fv lv : val)
      (P : A -> iProp Σ) (Q : A -> iProp Σ) (err : nonnegreal) E :
      {{{ (∀ (x : A),
            {{{ P x ∗ € err}}}
              fv (inject x) @ E
            {{{ fr, RET fr; Q x }}}) ∗
          ⌜is_list l lv⌝ ∗
          ([∗ list] x∈l, (P x)) ∗
           € (err * nnreal_nat (length l))%NNR
      }}}
        list_iter fv lv @ E
        {{{ rv, RET rv; [∗ list] x ∈ l, Q x
        }}}.
    Proof.
      iIntros (Φ) "[#Hf [%Hil HP]] HΦ".
      iAssert (([∗ list] x ∈ l, P x ∗ € err))%I with "[HP]" as "HP".
      { clear Hil. iInduction (l) as [| h t] "IH"; first done.
        rewrite !big_sepL_cons. simpl.
        iDestruct "HP" as "[[HP HP'] Herr]".
        iFrame.
        iAssert (€ err ∗ € (err * nnreal_nat (length t))%NNR)%I with "[Herr]" as "[Herr Herr']".
        { iApply ec_split.
          assert (err *nnreal_nat (S(length t)) = err + err * nnreal_nat (length t))%NNR as ->.
          - apply nnreal_ext. simpl. case_match; destruct err; simpl; lra.
          - done.
        }
        iFrame. iApply "IH"; iFrame.
      }
      wp_apply (wp_list_iter_err _ _ _ _ _ (λ _, err) with "[$HP]"); try done.
      by iSplit.
    Qed.

    Lemma wp_list_iteri_loop
          (k : nat) (l : list A) (fv lv : val)
          (P : iProp Σ) (Φ Ψ : nat -> A -> iProp Σ) E :
      is_list l lv →
      (∀ (i : nat) (x : A),
        {{{ P ∗ Φ i x }}} fv #i (inject x) @ E {{{ v, RET v; P ∗ Ψ i x }}}) -∗
      {{{ P ∗ ([∗ list] i ↦ a ∈ l, Φ (k+i)%nat a) }}}
        list_iteri_loop fv #k lv @ E
      {{{ RET #(); P ∗ [∗ list] i ↦ a ∈ l, Ψ (k+i)%nat a }}}.
    Proof.
      iIntros (Hl) "#Hf".
      iIntros (Φ') "!> [HP Hl] HΦ".
      iInduction l as [ | h l] "IH" forall (lv k Hl).
      { wp_lam. rewrite Hl. wp_pures. iApply "HΦ". by iFrame. }
      wp_lam. destruct Hl as [l' [-> Hl']]. wp_pures.
      iDestruct "Hl" as "[Ha Hl']". rewrite right_id_L.
      wp_apply ("Hf" with "[$HP $Ha]"). iIntros (v) "[HP HΨ]".
      wp_pures.
      replace (Z.add (Z.of_nat k) (Zpos xH)) with (Z.of_nat (k + 1)) by lia.
      iApply ("IH" $!l' (k+1)%nat with "[//] HP [Hl'] [HΨ HΦ]").
      { iApply (big_sepL_impl with "Hl'").
        iIntros "!>" (i x HSome) "HΦ".
        replace (k + S i)%nat with (k + 1 + i)%nat by lia. done. }
      iIntros "!> [HP Hl]".
      iApply "HΦ"=> /=. rewrite right_id_L. iFrame.
      iApply (big_sepL_impl with "Hl").
      iIntros "!>" (i x HSome) "HΦ".
      by replace (k + S i)%nat with (k + 1 + i)%nat by lia.
    Qed.

    Lemma wp_list_iteri
          (l : list A) (fv lv : val)
          (P : iProp Σ) (Φ Ψ : nat -> A -> iProp Σ) E :
      is_list l lv →
      (∀ (i : nat) (x : A),
        {{{ P ∗ Φ i x }}} fv #i (inject x) @ E {{{ v, RET v; P ∗ Ψ i x }}}) -∗
      {{{ P ∗ ([∗ list] i ↦ a ∈ l, Φ i a) }}}
        list_iteri fv lv @ E
      {{{ RET #(); P ∗ [∗ list] i ↦ a ∈ l, Ψ i a }}}.
    Proof.
      iIntros (Hl) "#Hf". iIntros (Φ') "!>[HP Hown] HΦ".
      wp_lam. wp_pures.
      iAssert (⌜#0 = #(0%nat)⌝%I) as %->; [done |].
      iApply (wp_list_iteri_loop 0 l with "Hf [$HP $Hown]"); [done|].
      by iFrame.
    Qed.

    Lemma wp_list_fold P Φ Ψ E handler (l : list A) acc lv :
      (∀ (a : A) acc lacc lrem,
          {{{ ⌜l = lacc ++ a :: lrem⌝ ∗ P lacc acc ∗ Φ a }}}
            (Val handler) (Val acc) (inject a) @ E
          {{{v, RET v; P (lacc ++ [a]) v ∗ Ψ a }}}) -∗
      {{{ ⌜is_list l lv⌝ ∗ P [] acc ∗ [∗ list] a∈l, Φ a }}}
        list_fold handler acc lv @ E
      {{{v, RET v; P l v ∗ [∗ list] a∈l, Ψ a }}}.
    Proof.
      iIntros "#Hcl". iIntros (Ξ) "!# (Hl & Hacc & HΦ) HΞ".
      change l with ([] ++ l) at 1 4.
      generalize (@nil A) at 1 3 4 as lproc => lproc.
      iInduction l as [|x l] "IHl" forall (Ξ lproc acc lv) "Hacc Hl HΞ".
      - iDestruct "Hl" as %?; simpl in *; simplify_eq.
        wp_rec. wp_pures. iApply "HΞ".
        rewrite app_nil_r; iFrame; done.
      - iDestruct "Hl" as %[lw [? Hlw]]; subst.
        iDestruct "HΦ" as "[Hx HΦ]".
        wp_rec. wp_pures.
        wp_apply ("Hcl" with "[$Hacc $Hx] [-]"); auto.
        iNext. iIntros (w) "[Hacc HΨ]"; simpl. wp_pures.
        iApply ("IHl" with "[] [$HΦ] [$Hacc] [] [HΨ HΞ]"); [|auto|].
        { rewrite -app_assoc; auto. }
        iNext. iIntros (v) "[HP HΨs]".
        rewrite -app_assoc.
        iApply "HΞ"; iFrame.
    Qed.

    Lemma wp_list_fold_generalized' E handler (l lp : list A) acc lv P Φ Ψ :
      □ (∀ (a : A) acc lacc lrem, (P lacc acc None (a::lrem) -∗ P lacc acc (Some a) lrem))%I -∗
        (∀ (a : A) acc lacc lrem,
            {{{ ⌜lp ++ l = lacc ++ a :: lrem⌝ ∗ P lacc acc (Some a) lrem ∗ Φ a }}}
              (Val handler) (Val acc) (inject a) @ E
            {{{v, RET v; P (lacc ++ [a]) v None lrem ∗ Ψ a }}}) -∗
      {{{ ⌜is_list l lv⌝ ∗ P lp acc None l ∗ [∗ list] a∈l, Φ a }}}
        list_fold (Val handler) (Val acc) (Val lv) @ E
      {{{v, RET v; P (lp ++ l) v None [] ∗ [∗ list] a∈l, Ψ a }}}.
    Proof.
      iIntros "#Hvs #Hcl". iIntros (Ξ) "!# (Hl & Hacc & HΦ) HΞ".
      iInduction l as [|x l] "IHl" forall (Ξ lp acc lv) "Hacc Hl HΞ".
      - iDestruct "Hl" as %?; simpl in *; simplify_eq.
        wp_rec. wp_pures. iApply "HΞ".
        rewrite app_nil_r; iFrame. done.
      - iDestruct "Hl" as %[lw [? Hlw]]; subst.
        iDestruct "HΦ" as "[Hx HΦ]".
        wp_rec; wp_pures.
        iPoseProof ("Hvs" with "Hacc") as "Hacc".
        wp_apply ("Hcl" with "[$Hacc $Hx] [-]"); auto.
        iNext. iIntros (w) "[Hacc HΨ]"; simpl. wp_let.
        iApply ("IHl" with "[] [$HΦ] [$Hacc] [] [HΨ HΞ]"); [|auto|].
        { rewrite -app_assoc; auto. }
        iNext. iIntros (v) "[HP HΨs]".
        rewrite -app_assoc.
        iApply "HΞ"; iFrame.
    Qed.

    Lemma wp_list_fold' E handler (l : list A) acc lv P Φ Ψ :
      □ (∀ (a : A) acc lacc lrem, (P lacc acc None (a::lrem) -∗ P lacc acc (Some a) lrem))%I -∗
        (∀ (a : A) acc lacc lrem,
            {{{ ⌜l = lacc ++ a :: lrem⌝ ∗ P lacc acc (Some a) lrem ∗ Φ a }}}
              (Val handler) (Val acc) (inject a) @ E
            {{{v, RET v; P (lacc ++ [a]) v None lrem ∗ Ψ a }}}) -∗
      {{{ ⌜is_list l lv⌝ ∗ P [] acc None l ∗ [∗ list] a∈l, Φ a }}}
        list_fold (Val handler) (Val acc) lv @ E
      {{{v, RET v; P l v None [] ∗ [∗ list] a∈l, Ψ a }}}.
    Proof.
      iIntros "#Hvs #Hcl".
      iApply (wp_list_fold_generalized' _ handler l [] with "[-]"); eauto.
    Qed.

    Lemma wp_list_sub E k l lv  :
      {{{ ⌜is_list l lv⌝ }}}
        list_sub #k lv @ E
      {{{ v, RET v; ⌜is_list (take k l) v ⌝}}}.
    Proof.
     iIntros (Φ) "Hcoh HΦ".
     iInduction l as [|a l'] "IH" forall (k lv Φ);
     iDestruct "Hcoh" as %Hcoh; simpl in Hcoh; subst; wp_rec;
     wp_pures; case_bool_decide; wp_if; wp_pures.
     - iApply "HΦ"; by rewrite take_nil.
     - iApply "HΦ"; by rewrite take_nil.
     - iApply "HΦ". assert (k = O) as H1 by lia. by rewrite H1 firstn_O.
     - destruct Hcoh as [lv' [Hlv Hlcoh]]; subst.
       wp_match. wp_proj. wp_bind (list_sub _ _). wp_op.
       destruct k as [|k]; first done.
       assert (((Z.of_nat (S k)) - 1)%Z = Z.of_nat k) as -> by lia.
       iApply ("IH" $! k _ _ Hlcoh). iIntros (tl Hcoh_tl).
       iNext. wp_pures. rewrite firstn_cons. by wp_apply (wp_list_cons).
    Qed.

    Lemma wp_list_nth E (i: nat) l lv  :
     {{{ ⌜is_list l lv⌝ }}}
        list_nth (Val lv) #i @ E
      {{{ v, RET v; (⌜v = NONEV⌝ ∧ ⌜length l <= i⌝) ∨
                ⌜∃ r, v = SOMEV (inject r) ∧ nth_error l i = Some r⌝ }}}.
    Proof.
      iIntros (Φ) "Ha HΦ".
      iInduction l as [|a l'] "IH" forall (i lv Φ);
      iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_rec; wp_let.
      - wp_match. wp_pures.
        iApply ("HΦ" $! (InjLV #())). iLeft. simpl. eauto with lia.
      - destruct Ha as [lv' [Hlv Hlcoh]]; subst.
        wp_match. wp_pures. case_bool_decide; wp_pures.
        + iApply "HΦ". iRight. simpl. iExists a. by destruct i.
        + destruct i; first done.
          assert ((S i - 1)%Z = i) as -> by lia.
          iApply ("IH" $! i lv' _  Hlcoh).
          iNext. iIntros (v [ (Hv & Hs) | Hps]); simpl.
          * iApply "HΦ"; try eauto with lia.
          * iApply "HΦ"; try eauto with lia.
    Qed.

    Lemma wp_list_nth_some E (i: nat) l lv  :
      {{{  ⌜is_list l lv ∧ i < length l⌝  }}}
        list_nth (Val lv) #i @ E
      {{{ v, RET v; ⌜∃ r, v = SOMEV (inject r) ∧ nth_error l i = Some r⌝ }}}.
    Proof.
      iIntros (Φ (Hcoh & Hi)) "HΦ".
      iApply (wp_list_nth $! Hcoh).
      iIntros (v [H | H]); first eauto with lia.
      by iApply "HΦ".
    Qed.

    (*
    Lemma wp_list_mem `{!EqDecision A} E (l : list A) lv a :
      {{{ ⌜is_list l lv⌝ }}}
        list_mem (inject a) lv @ E
      {{{ (b : bool), RET #b; if b then ⌜a ∈ l⌝ else ⌜a ∉ l ∨ l = nil⌝ }}}.
    Proof.
      iIntros (Φ).
      iInduction l as [|a' l'] "IH" forall (lv Φ);
        iIntros (Hl) "HΦ"; wp_rec; wp_pures.
      - rewrite Hl. wp_pures. iApply "HΦ". auto.
      - destruct Hl as [lv' [-> Hl']]. wp_pures.
        wp_op; first apply bin_op_eval_eq_val.
        case_bool_decide as Heq; wp_if.
        { simplify_eq. iApply "HΦ". iPureIntro; set_solver. }
        iApply ("IH" with "[//]").
        iIntros "!>" ([] Ha).
        { iApply "HΦ". iPureIntro; set_solver. }
        iApply "HΦ".
        iPureIntro. left.
        simplify_eq.
        apply not_inj_fn in Heq; [|apply _].
        destruct Ha; set_solver.
    Qed.
    *)

    *)
    Lemma wp_remove_nth E (l : list A) lv (i : nat) :
      {{{ ⧖ 0%R ∗ ⌜is_list l lv /\ i < length l⌝ }}}
        list_remove_nth lv #i @ E
      {{{ v, RET v; ∃ e lv' l1 l2,
                  ⌜l = l1 ++ e :: l2 ∧
                   length l1 = i /\
                  v = SOMEV ((inject e), lv') ∧
                  is_list (l1 ++ l2) lv'⌝ }}}.
    Proof.
      iIntros (Φ) "(Hcr & Ha) Hφ".
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
          * admit. (* by apply is_list_inject in Hlcoh as ->. *)
          * admit. (* by apply is_list_inject.*)
        + destruct i; first done.
          assert ((S i - 1)%Z = i) as -> by lia.
          assert (is_list l' lv' /\ i < length l') as Haux.
          { split; auto.
            inversion Hi; auto. lia.
          }
          wp_bind (list_remove_nth _ _).
          repeat rewrite Rminus_0_r.
          iApply ("IH" $! i lv' _  with "Hcr"); [eauto|].
          iAssert (⧖ 0%R) as "Hcr"; first admit.
          iNext. iIntros (v (e & v' & l1 & l2 & (-> & Hlen & -> & Hil))); simpl.

          (* wp_pures.
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
          *)
    Admitted.

    (*

    Lemma wp_remove_nth_total E (l : list A) lv (i : nat) :
      {{{ ⌜is_list l lv /\ i < length l⌝ }}}
        list_remove_nth_total lv #i @ E
      {{{ v, RET v; ∃ e lv' l1 l2,
                  ⌜l = l1 ++ e :: l2 ∧
                   length l1 = i /\
                  v = lv' ∧
                  is_list (l1 ++ l2) lv'⌝ }}}.
    Proof.
      iIntros (Φ) "Ha Hφ".
      iInduction l as [|a l'] "IH" forall (i lv Φ);
        iDestruct "Ha" as "(%Hl & %Hi)"; simpl in Hl; subst; wp_rec; wp_let.
      - inversion Hi.
      - destruct Hl as [lv' [Hlv Hlcoh]]; subst.
        wp_match. wp_pures. case_bool_decide; wp_pures.
        + iApply "Hφ".
          iExists a, (inject l'), [], l'.
          destruct i; auto.
          iPureIntro; split; auto.
          split; auto.
          split.
          * by apply is_list_inject in Hlcoh.
          * by apply is_list_inject.
        + destruct i; first done.
          assert ((S i - 1)%Z = i) as -> by lia.
          assert (is_list l' lv' /\ i < length l') as Haux.
          { split; auto.
            inversion Hi; auto. lia.
          }
          wp_bind (list_remove_nth_total _ _).
          iApply ("IH" $! i lv' _  Haux).
          iNext. iIntros (v (e & v' & l1 & l2 & (-> & Hlen & -> & Hil))); simpl.
          wp_pures.
          iApply wp_list_cons; [done |].
          iIntros "!>" (v Hcons).
          iApply "Hφ".
          iExists e, (inject ((a :: l1) ++ l2)), (a :: l1), l2.
          iPureIntro.
          split; auto.
          split; [rewrite cons_length Hlen // |].
          split.
          * by apply is_list_inject in Hcons.
          * by apply is_list_inject.
    Qed.


    Lemma wp_find_remove E (l : list A) lv (Ψ : A → iProp Σ) (fv : val) :
      (∀ (a : A),
          {{{ True }}}
            fv (inject a) @ E
          {{{ (b : bool), RET #b; if b then Ψ a else True }}}) -∗
      {{{ ⌜is_list l lv⌝ }}}
        list_find_remove fv lv @ E
      {{{ v, RET v; ⌜v = NONEV⌝ ∨
                         ∃ e lv' l1 l2,
                           ⌜l = l1 ++ e :: l2 ∧
                           v = SOMEV ((inject e), lv') ∧
                           is_list (l1 ++ l2) lv'⌝
                           ∗ Ψ e}}}.
    Proof.
      iIntros "#Hf" (Φ).
      iInduction l as [|a l'] "IH" forall (lv Φ);
        iIntros (Hl) "!> HΦ"; wp_rec; wp_pures.
      { rewrite Hl. wp_pures. iApply "HΦ".
        iLeft; iPureIntro; split; set_solver. }
      destruct Hl as [lv' [-> Hl']]. wp_pures.
      wp_bind (fv _). iApply ("Hf" with "[//]").
      iIntros "!>" (b) "Hb /=".
      destruct b.
      { wp_pures.
        iApply "HΦ".
        iRight; iExists _, _, [], _; eauto. }
      wp_pures.
      wp_bind (list_find_remove _ _).
      iApply ("IH" with "[//]").
      iIntros "!>" (w) "[->| He] /="; wp_pures.
      { iApply "HΦ".
        iLeft; done. }
      iDestruct "He" as (e lv'' l1 l2) "[He HHΨ]".
      iDestruct "He" as %(-> & -> & Hlv'').
      wp_pures.
      wp_bind (list_cons _ _). iApply wp_list_cons; [done|].
      iIntros "!>" (v Hcoh) "/=". wp_pures.
      iApply "HΦ". iRight.
      iExists _, _, (_ :: _), _; eauto.
    Qed.

    Local Lemma wp_list_rev_aux E l lM r rM:
     {{{ ⌜is_list lM l ∧ is_list rM r⌝ }}}
       list_rev_aux (Val l) (Val r) @ E
     {{{ v, RET v; ⌜is_list (rev_append lM rM) v⌝ }}}.
    Proof.
      iIntros (? [Hl Hr]) "H".
      iInduction lM as [|a lM] "IH" forall (l r rM Hl Hr).
      - simpl in *; subst. rewrite /list_rev_aux. wp_pures. by iApply "H".
      - destruct Hl as [l' [Hl'eq Hl']]; subst.
        wp_rec; wp_pures.
        wp_apply wp_list_cons; [done|].
        iIntros (w Hw).
        wp_pures. by iApply "IH".
   Qed.

    Lemma wp_list_rev E l lM :
      {{{ ⌜is_list lM l⌝ }}}
        list_rev (Val l) @ E
      {{{ v, RET v; ⌜is_list (reverse lM) v⌝ }}}.
    Proof.
      iIntros (??) "H". rewrite /list_rev. wp_pures.
      by iApply (wp_list_rev_aux _ _ _ NONEV []).
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

    Lemma wp_list_forall Φ Ψ E (l : list A) lv (fv : val) :
      (∀ (a : A),
          {{{ True }}}
            fv (inject a) @ E
          {{{ (b : bool), RET #b; if b then Φ a else Ψ a }}}) -∗
      {{{ ⌜is_list l lv⌝ }}}
        list_forall fv lv @ E
      {{{ (b : bool), RET #b; if b then [∗ list] a ∈ l, Φ a else ∃ a, ⌜a ∈ l⌝ ∗ Ψ a }}}.
    Proof.
      rewrite /list_forall.
      iInduction l as [|a l'] "IH" forall (lv);
        iIntros "#Hfv" (Ξ) "!# %Hl HΞ".
      - simpl in Hl; subst. wp_pures. iApply "HΞ"; auto.
      - destruct Hl as [l'' [Hl'eq Hl']]; subst.
        wp_pures.
        wp_apply "Hfv"; [done|].
        iIntros ([]) "Hb".
        + wp_if. iApply ("IH"); [done..|].
          iIntros "!>" ([]).
          * iIntros "Ha". iApply "HΞ".
            rewrite big_sepL_cons. iFrame.
          * iDestruct 1 as (a') "[% ?]".
            iApply "HΞ". iExists _. iFrame.
            iPureIntro. apply elem_of_cons. by right.
        + wp_if. iApply "HΞ". iExists _. iFrame.
          iPureIntro. apply elem_of_cons. by left.
    Qed.

    Lemma wp_list_is_empty l v E :
      {{{ ⌜is_list l v⌝ }}}
        list_is_empty v @ E
      {{{ v, RET #v;
          ⌜v = match l with [] => true | _ => false end⌝ }}}.
    Proof.
      iIntros (Φ Hl) "HΦ". wp_rec. destruct l.
      - rewrite Hl. wp_pures. by iApply "HΦ".
      - destruct Hl as [? [-> _]]. wp_pures. by iApply "HΦ".
    Qed.

    Lemma is_list_eq lM :
      ∀ l1 l2, is_list lM l1 → is_list lM l2 → l1 = l2.
    Proof. induction lM; intros []; naive_solver eauto with f_equal. Qed.

    Lemma is_list_inv_l l:
      ∀ lM1 lM2, is_list lM1 l → lM1 = lM2 → is_list lM2 l.
    Proof. by intros ? ? ? <-. Qed.

    Lemma is_list_snoc lM x : ∃ lv, is_list (lM ++ [x]) lv.
    Proof. induction lM; naive_solver eauto. Qed.

    Lemma wp_list_filter (l : list A) (P : A -> bool) (f lv : val) E :
      {{{ (∀ (x : A),
              {{{ True }}}
                f (inject x) @ E
              {{{ w, RET w; ⌜w = inject (P x)⌝ }}} ) ∗
          ⌜is_list l lv⌝ }}}
         list_filter f lv @ E
       {{{ rv, RET rv; ⌜is_list (List.filter P l) rv⌝ }}}.
    Proof.
      iIntros (Φ) "[#Hf %Hil] HΦ".
      iInduction l as [ | h t] "IH" forall (lv Hil Φ); simpl in Hil.
      - subst.
        rewrite /list_filter; wp_pures.
        iApply "HΦ"; done.
      - destruct Hil as (lv' & -> & Hil).
        rewrite /list_filter.
        do 7 (wp_pure _).
        fold list_filter.
        wp_apply ("IH" $! lv'); [done |].
        iIntros (rv) "%Hilp"; wp_pures.
        wp_apply "Hf"; [done |].
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


    Lemma wp_list_split E (n:nat) (lv:val) l:
      {{{ ⌜is_list l lv⌝ ∗ ⌜n<=length l⌝ }}}
        list_split #n lv @ E
        {{{ a b, RET (a, b)%V;
            ∃ l1 l2, ⌜is_list l1 a⌝ ∗ ⌜is_list l2 b⌝ ∗ ⌜l=l1++l2⌝ ∗ ⌜length (l1) = n⌝
        }}}.
    Proof.
      revert lv l.
      induction n;
        iIntros (lv l Φ) "[%Hlist %Hlength] HΦ".
      - rewrite /list_split. wp_pures. iModIntro. iApply "HΦ".
        iExists [], l.
        repeat iSplit; by iPureIntro.
      - rewrite /list_split. wp_pures. rewrite -/list_split.
        destruct l.
        { simpl in Hlength. lia. }
        destruct Hlist as [?[-> Hlist]].
        wp_pures. replace (Z.of_nat (S n) - 1)%Z with (Z.of_nat n) by lia.
        wp_apply IHn.
        + iSplit; iPureIntro; try done. simpl in Hlength. lia.
        + iIntros (??) "(%l1 & %l2 &%&%&%&%)".
          wp_pures.
          wp_apply wp_list_cons; first done.
          iIntros. wp_pures. iApply "HΦ".
          iExists (_::l1), l2.
          iModIntro; repeat iSplit; iPureIntro; try done.
          * set_solver.
          * set_solver.
    Qed.
  End list_specs.

  Global Arguments wp_list_nil : clear implicits.
  Global Arguments wp_list_nil {_ _ _} _ {_}.

  (* Start a new section because some of the specs below (e.g. wp_list_map) need
     access to the type parameter in e.g. is_list, since they operate on more than one
     list type. *)
  Section list_specs_extra.

    Context `{!ub_clutchGS Σ}.
    Context `[!Inject A val].

    Lemma wp_list_map `{!Inject B val} (l : list A) (f : A -> B) (fv lv : val)
      (P : A -> iProp Σ) (Q : A -> val -> iProp Σ) E :
      {{{ (∀ (x : A),
            {{{ P x }}}
              fv (inject x) @ E
            {{{ fr, RET fr; ⌜fr = inject $ f x ⌝ ∗ Q x fr }}}) ∗
          ⌜is_list l lv⌝ ∗
          [∗ list] x∈l, P x
      }}}
        list_map fv lv @ E
        {{{ rv, RET rv; ⌜is_list (List.map f l) rv⌝ ∗
                        [∗ list] p ∈ zip l (List.map f l), Q (fst p) (inject $ snd p)
        }}}.
    Proof.
        iIntros (Φ) "[#Hf [%Hil HP]] HΦ".
        iInduction l as [ | h t] "IH" forall (lv Hil Φ); simpl in Hil; try subst; rewrite /list_map.
        - wp_pures.
          iApply "HΦ".
          iModIntro. iSplitR; last done.
          iPureIntro. rewrite /is_list; done.
        - wp_pures.
          destruct Hil as (lv' & -> & Hil').
          do 4 wp_pure _.
          fold list_map.
          rewrite big_sepL_cons.
          iDestruct "HP" as "[HP HP']".
          wp_apply ("IH" with "[][HP']"); [done|done|].
          iIntros (rv) "[%Hil_rv Hzip]"; wp_pures.
          wp_apply ("Hf" with "[$]").
          iIntros (fr) "[-> HQ]".
          wp_apply (wp_list_cons); [done|].
          iIntros (v) "%Hilf".
          iApply "HΦ"; auto.
          iSplitR; first done.
          rewrite map_cons. simpl. iFrame.
    Qed.

    Lemma wp_list_map_pure `{!Inject B val} (l : list A) (f : A -> B) (fv lv : val) E :
      {{{ (∀ (x : A),
            {{{ True }}}
              fv (inject x) @ E
            {{{ fr, RET fr; ⌜fr = inject (f x)⌝ }}}) ∗
            ⌜is_list l lv⌝ }}}
        list_map fv lv @ E
      {{{ rv, RET rv; ⌜is_list (List.map f l) rv⌝ }}}.
    Proof.
      iIntros (Φ) "[#H %Hl] HΦ".
      iApply wp_list_map; last first.
      - iModIntro. iIntros (?) "[% ?]". by iApply "HΦ".
      - iIntros. repeat iSplit.
        + iIntros (??) "!> _ K". wp_apply "H"; [done|].
          iIntros. iApply "K". by iSplit.
        + done.
        + by instantiate (1 := (λ _, True)%I).
    Qed.

    Lemma wp_list_map_err `{!Inject B val} (l : list A) (f : A -> B) (fv lv : val)
      (P : A -> iProp Σ) (Q : A -> val -> iProp Σ) (err : A -> nonnegreal) E :
      {{{ (∀ (x : A),
            {{{ P x ∗ € (err x)}}}
              fv (inject x) @ E
            {{{ fr, RET fr; ⌜fr = inject $ f x ⌝ ∗ Q x fr }}}) ∗
          ⌜is_list l lv⌝ ∗
          [∗ list] x∈l, (P x ∗ € (err x))
      }}}
        list_map fv lv @ E
        {{{ rv, RET rv; ⌜is_list (List.map f l) rv⌝ ∗
                        [∗ list] p ∈ zip l (List.map f l), Q (fst p) (inject $ snd p)
        }}}.
    Proof.
      iIntros (Φ) "[#Hf [%Hil HP]] HΦ".
      iApply (wp_list_map with "[HP]"); try iFrame.
      by iSplit.
    Qed.

    Lemma wp_list_map_err_constant `{!Inject B val} (l : list A) (f : A -> B) (fv lv : val)
      (P : A -> iProp Σ) (Q : A -> val -> iProp Σ) (err : nonnegreal) E :
      {{{ (∀ (x : A),
            {{{ P x ∗ € err}}}
              fv (inject x) @ E
            {{{ fr, RET fr; ⌜fr = inject $ f x ⌝ ∗ Q x fr }}}) ∗
          ⌜is_list l lv⌝ ∗
          ([∗ list] x∈l, P x) ∗
          € (err * nnreal_nat (length l))%NNR
      }}}
        list_map fv lv @ E
        {{{ rv, RET rv; ⌜is_list (List.map f l) rv⌝ ∗
                        [∗ list] p ∈ zip l (List.map f l), Q (fst p) (inject $ snd p)
        }}}.
    Proof.
      iIntros (Φ) "[#Hf [%Hil HP]] HΦ".
      iAssert (([∗ list] x ∈ l, P x ∗ € err))%I with "[HP]" as "HP".
      { clear Hil. iInduction (l) as [| h t] "IH"; first done.
        rewrite !big_sepL_cons. simpl.
        iDestruct "HP" as "[[HP HP'] Herr]".
        iFrame.
        iAssert (€ err ∗ € (err * nnreal_nat (length t))%NNR)%I with "[Herr]" as "[Herr Herr']".
        { iApply ec_split.
          assert (err *nnreal_nat (S(length t)) = err + err * nnreal_nat (length t))%NNR as ->.
          - apply nnreal_ext. simpl. case_match; destruct err; simpl; lra.
          - done.
        }
        iFrame. iApply "IH"; iFrame.
      }
      iApply (wp_list_map with "[HP]"); try iFrame.
      by iSplit.
    Qed.

    (* TODO: is this in some Coq library? *)
    Fixpoint mapi_loop {B : Type} (f : nat -> A -> B) (k : nat) (l : list A) : list B :=
      match l with
      | h :: t => (f k h) :: (mapi_loop f (S k) t)
      | [] => []
      end.

    Lemma mapi_loop_i {B : Type} (f : nat -> A -> B) (l : list A) (i k : nat) :
      (i < length l)%nat ->
      exists v w, l !! i = Some v ∧
             (mapi_loop f k l) !! i = Some w ∧
             w = f (k + i)%nat v.
    Proof.
      generalize dependent i.
      generalize dependent k.
      induction l as [ | h t IH]; intros k i Hlt; simpl in *.
      - exfalso; lia.
      - destruct i as [ | i']; simpl.
        { exists h, (f k h).
          replace (k + 0)%nat with k; auto. lia. }
        apply Nat.succ_lt_mono in Hlt.
        pose proof (IH (S k) i' Hlt) as (v & w & -> & -> & Heq).
        replace (k + S i')%nat with (S k + i')%nat by lia.
        eauto.
    Qed.

    Definition mapi {B : Type} (f : nat -> A -> B) (l : list A) : list B :=
      mapi_loop f 0 l.

    Lemma mapi_i {B : Type} (f : nat -> A -> B) (l : list A) (i : nat) :
      (i < length l)%nat ->
      exists v w, l !! i = Some v ∧
             (mapi f l) !! i = Some w ∧
             w = f i v.
    Proof.
      intros Hlt.
      pose proof (mapi_loop_i f l i O Hlt) as (v & w & H1 & H2 & H3).
      eauto.
    Qed.

    (* TODO: clean up *)
    Lemma wp_list_mapi_loop `{!Inject B val}
          (f : nat -> A -> B) (k : nat) (l : list A) (fv lv : val)
          (γ : nat -> A -> iProp Σ) (ψ : nat -> B -> iProp Σ) E :
      {{{ □ (∀ (i : nat) (x : A),
                {{{ γ (k + i)%nat x }}}
                  fv (inject (k + i)%nat) (inject x) @ E
                  {{{ fr, RET fr;
                      let r := f (k + i)%nat x in
                      ⌜fr = (inject r)⌝ ∗ ψ (k + i)%nat r }}}) ∗
          ⌜is_list l lv⌝ ∗
          ([∗ list] i ↦ a ∈ l, γ (k + i)%nat a)
      }}}
        list_mapi_loop fv #k lv @ E
      {{{ rv, RET rv;
          let l' := mapi_loop f k l in
          ⌜is_list l' rv⌝ ∗
          ([∗ list] i ↦ a ∈ l', ψ (k + i)%nat a)}}}.
    Proof.
      iInduction l as [ | h l'] "IH" forall (lv k);
        iIntros (Φ) "[#Hf [%Hil Hown]] HΦ"; simpl in Hil;
        rewrite /list_mapi_loop.
      - subst.
        wp_pures.
        iApply "HΦ".
        iSplitL ""; done.
      - destruct Hil as [lv' [-> Hil']].
        do 10 wp_pure _.
        fold list_mapi_loop.
        wp_bind (list_mapi_loop _ _ _).
        iAssert (⌜#(k + 1) = #(k + 1)%nat⌝%I) as "->".
        { iPureIntro.
          do 2 apply f_equal; lia. }
        iDestruct (big_sepL_cons with "Hown") as "[Hhead Hown]".
        iApply ("IH" with "[Hown]").
        + iSplitL "".
          * iModIntro.
            iIntros (i x).
            iPoseProof ("Hf"  $! (1 + i)%nat x) as "Hf'".
            iAssert (⌜(k + (1 + i))%nat = (k + 1 + i)%nat⌝%I) as %<-.
            {  iPureIntro; by lia. }
            iApply "Hf".
          * iSplitL ""; [done |].
            iApply (big_sepL_impl with "Hown").
            iModIntro.
            iIntros (k' x) "_ Hpre".
            iAssert (⌜(k + 1 + k')%nat = (k + S k')%nat⌝%I) as %->.
            { iPureIntro; lia. }
            done.
        + iModIntro.
          iIntros (rv) "[%Hil'' Hown]".
          wp_pures.
          iAssert (⌜#k = (inject (k + 0)%nat)⌝%I) as %->.
          { simpl.
            iPureIntro.
            do 2 f_equal.
            lia. }
          wp_apply ("Hf" with "Hhead").
          iIntros (fr) "[-> HΨ]".
          wp_apply wp_list_cons; [done | ].
          iIntros (v) "%Hil'''".
          iApply "HΦ".
          iSplitL ""; [iPureIntro |].
          { assert (f (k + 0)%nat h :: mapi_loop f (k + 1) l' = mapi_loop f k (h :: l')) as <-.
            { simpl.
              assert ((k + 0)%nat = k) as -> by lia.
              assert (k + 1 = S k)%nat as -> by lia.
              reflexivity. }
            done. }
          simpl.
          iSplitL "HΨ".
          { assert (f k h = f (k + 0)%nat h) as ->.
            { assert (k = (k + 0))%nat as <- by lia; done. }
            done. }
          iAssert (⌜(k + 1)%nat = S k⌝%I) as %->.
          { iPureIntro.
            do 2 f_equal.
            lia. }
          iApply (big_sepL_impl with "Hown").
          iModIntro.
          iIntros (k' x) "_ HΨ".
          iAssert (⌜(S k + k')%nat = (k + S k')%nat⌝%I) as %->.
          { iPureIntro.
            lia. }
          done.
    Qed.

    Lemma wp_list_mapi `{!Inject B val}
          (f : nat -> A -> B) (l : list A) (fv lv : val)
          (γ : nat -> A -> iProp Σ) (ψ : nat -> B -> iProp Σ) E :
      {{{ □ (∀ (i : nat) (x : A),
                {{{ γ i x }}}
                  fv #i (inject x) @ E
                  {{{ fr, RET fr;
                      let r := f i x in
                      ⌜fr = (inject r)⌝ ∗ ψ i r }}}) ∗
          ⌜is_list l lv⌝ ∗
          ([∗ list] i ↦ a ∈ l, γ i a)
      }}}
        list_mapi fv lv @ E
      {{{ rv, RET rv;
          let l' := mapi f l in
          ⌜is_list l' rv⌝ ∗
          ([∗ list] i ↦ a ∈ l', ψ i a)}}}.
    Proof.
      iIntros (Φ) "[#Hf [%Hil Hown]] HΦ".
      rewrite /list_mapi.
      do 3 wp_pure _.
      iAssert (⌜#0 = #(0%nat)⌝%I) as %->; [done |].
      iApply (wp_list_mapi_loop with "[Hown]").
      - iSplitL ""; last first.
        + iFrame; done.
        + iModIntro.
          iIntros (i x).
          iAssert (⌜(0 + i)%nat = i⌝%I) as %->; [done |].
          iApply "Hf".
      - iModIntro.
        assert (mapi f l = mapi_loop f 0 l) as <-; [done |].
        iFrame.
    Qed.

    (* TODO: is there a standard library lemma for this? *)
    Lemma list_lookup_succ (h : A) (l : list A) (i : nat) :
      (h :: l) !! (S i) = l !! i.
    Proof. auto. Qed.

    Lemma wp_list_seq E n m :
      {{{ True }}}
        list_seq #n #m @ E
      {{{ v, RET v; ⌜is_list (seq n m) v⌝ }}}.
    Proof.
      iIntros (Φ) "_ Hφ".
      iInduction m as [ | p] "IHm" forall (n Φ).
      - rewrite /list_seq.
        wp_pures.
        iApply "Hφ".
        iPureIntro.
        rewrite /seq.
        by apply is_list_inject.
      - rewrite /list_seq.
        wp_rec.
        do 6 wp_pure.
        assert (#(S p - 1) = #p) as ->.
        { do 3 f_equal. lia. }
        fold list_seq.
        assert (#(n + 1) = #(Z.of_nat (S n))) as ->.
        { do 3 f_equal. lia. }
        wp_apply "IHm".
        iIntros (v Hv).
        wp_apply (wp_list_cons with "[//]").
        iIntros (v' Hv').
        iApply "Hφ".
        iPureIntro.
        apply (is_list_inject) in Hv' as ->.
        by apply is_list_inject.
    Qed.
  *)
  End list_specs.
End list.



Section program.
  Context `{!ert_clutchGS Σ CostCmp }.
  (** Verifing the number of comparisons done by quicksort *)
  (* Proofs augmented from examples/quicksort.v *)

  Definition list_remove_nth_unsafe : val :=
    λ:"l" "n",
    match: list_remove_nth "l" "n" with
    | NONE => #()
    | SOME "v" => "v"
    end.

  Definition partition : expr :=
    let: "negb" := λ:"b", if: "b" then #false else #true in
    λ:"l" "e",
      let: "f" := (λ:"x", "e" < "x") in
      (list_filter (λ:"x", "negb" ("f" "x") ) "l",
        list_filter "f" "l").

  Definition qs : val :=
    rec: "qs" "l" :=
      let: "n" := list_length "l" in
      if: "n" < #1 then "l" else
        let: "ip" := rand ("n" - #1) in
        let, ("p", "r") := list_remove_nth_unsafe "l" "ip" in
        let, ("le", "gt") := partition "r" "p" in
        let, ("les", "gts") := ("qs" "le", "qs" "gt") in
        list_append "les" (list_cons "p" "gts").


  (* Necessary *)
  Lemma wp_remove_nth_unsafe {A} [_ : Inject A val] E (l : list A) (lv : val) (i : nat) :
    {{{ ⧖ 0%R ∗ ⌜ is_list l lv /\ i < length l ⌝ }}}
      list_remove_nth_unsafe lv #i @ E
    {{{ v, RET v;
        ∃ e lv' l1 l2,
          ⌜ l = l1 ++ e :: l2 ∧
          length l1 = i /\
          v = ((inject e), lv')%V ∧
          is_list (l1 ++ l2) lv' ⌝ }}}.
  Proof.
    iIntros (φ) "(Hcr & %llv & %Hi) hφ".
    rewrite /list_remove_nth_unsafe.
    wp_pures.
    wp_apply wp_remove_nth => //.
    { iSplit; first admit. eauto. }
    iIntros (?(?&?&?&?&?&?&?&?)) ; subst. wp_pures.
    iApply "hφ". iModIntro. iExists _,_,_,_. intuition eauto.
  Admitted.

  Lemma filter_split_perm {A} (l : list A) f :
    l ≡ₚ List.filter f l ++ List.filter (fun x=>negb (f x)) l.
  Proof.
    induction l as [|a l IHl] => // /=.
    destruct (f a) => /= ; rewrite -?Permutation_middle -IHl //.
  Qed.

  (* Maybe I can weaken the sorting requirement on the results *)
  Lemma Partition (xs : list Z) l (e : Z) e' :
    e' = Val #e ->
    {{{ ⌜is_list xs l⌝ }}}
      partition l e'
    {{{ le gt, RET (le, gt);
        ∃ xsle xsgt : list Z,
          ⌜is_list xsle le ∧ is_list xsgt gt
          ∧ app xsle xsgt ≡ₚ xs ⌝
          ∧ ⌜ ∀ x, In x xsle → (x ≤ e)%Z ⌝
                   ∧ ⌜ ∀ x, In x xsgt → (e < x)%Z ⌝
    }}}.
  Proof.
    iIntros (-> φ Lxs) "hφ".
    rewrite /partition.
    iAssert (⧖ 0%R) as "Hcr"; first admit.
    wp_pures. (* Not stepping anything *)
    (*
    wp_bind (list_filter _ _).
    iApply (wp_list_filter _ (λ x, bool_decide (e < x)%Z)).
    { iSplit => //. iIntros (x ψ) "_ !> hψ".
      simpl. wp_pures. iApply "hψ". eauto. }
    iIntros "!>" (gt egt). wp_pures.
    wp_bind (list_filter _ _).
    iApply (wp_list_filter _ (λ x, negb $ bool_decide (e < x)%Z)).
    { iSplit => //. iIntros (x ψ) "_ !> hψ".
      simpl. wp_pures.
      case_bool_decide ; wp_pures ; by iApply "hψ". }
    iIntros "!>" (le ele).
    wp_pures. iApply "hφ". iPureIntro.
    set (xs_gt := (List.filter (λ x : Z, bool_decide (e < x)%Z) xs)) in *.
    set (xs_le := (List.filter (λ x : Z, negb $ bool_decide (e < x)%Z) xs)) in *.
    exists xs_le, xs_gt. intuition auto.
    2:{ epose proof (filter_In _ x xs) as [h _]. destruct (h H) as [_ hle].
        destruct (bool_decide (e < x)%Z) eqn:hlt => //.
        apply bool_decide_eq_false in hlt.
        apply Z.nlt_ge. done.
    }
    2:{ epose proof (filter_In _ x xs) as [h _]. destruct (h H) as [_ hgt].
        by apply bool_decide_eq_true in hgt.
    }
    epose proof (filter_split_perm xs _) as xs_split.
    symmetry. subst xs_le xs_gt.
    rewrite Permutation_app_comm. apply xs_split.
     *)
  Admitted.

  Local Notation sorted := (StronglySorted Z.le).

  (* Can I delete this lemma? *)
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

  Definition qsA := 3%nat.
  Definition qsB := 1%nat.
  Definition qsC := tc_quicksort qsA qsB.








  (* Removed sorted requirements *)
  Lemma qs_time_bound : ∀ (xs : list Z) (l : val),
    {{{ ⧖ (qsC (length xs)) ∗ ⌜is_list xs l⌝ }}}
      qs l
    {{{ v, RET v; ∃ xs', ⌜ is_list xs' v ∧ xs' ≡ₚ xs ⌝ }}}.
  Proof with wp_pures.
    assert (Hnonneg : forall i, (0 <= qsC i)%R) by admit.
    iLöb as "Hqs". iIntros (xs l φ) "(Hcr & %hl) hφ".
    rewrite {2}/qs...
    wp_rec; first admit.
    rewrite -/qs.
    wp_bind (list_length _).
    iAssert (⧖ (qsC (length xs)) ∗ ⧖ 0%R)%I with "[Hcr]" as "(Hcr & Hfree)".
    { iApply etc_split; [admit | lra |].
      iApply (etc_weaken with "[$]").
      simpl. admit.
    }
    iApply (wp_list_length with "[Hfree]").
    { iFrame; eauto. }
    iIntros "!>" (n) "->"...
    repeat (wp_pure; eauto; rewrite Rminus_0_r).
    (* Start spending qsC *)
    rewrite /qsC.
    destruct xs as [|xs'].
    { (* Empty list *)
      rewrite tc_quicksort_unfold /= /tc_base.
      simpl. wp_pures. iApply "hφ". iExists _. iPureIntro. eauto.
    }
    simpl length.
    rewrite tc_quicksort_unfold.
    iAssert (⧖ (tc_pivot_lin qsA qsB (S (length xs))) ∗
             ⧖ (2 * (foldr Rplus 0%R (map (λ n : nat, tc_quicksort qsA qsB n) (seq 0 (S (length xs))))) / (S (length xs))))%I with "[Hcr]" as "(HcrP & Hcr)".
    { admit. }
    rewrite /tc_pivot_lin. rewrite {2}/qsA {2}/qsB.
    wp_pure with "HcrP"; first admit.
    rewrite bool_decide_false; last admit.

    (* Probably an easier way to do this *)
    remember (length xs + S (length xs + S (length xs + 0)) + 1)%nat as X; destruct X; first lia.
    rewrite HeqX; clear HeqX X.
    wp_pure with "HcrP"; first admit.
    wp_pure with "HcrP"; first admit.
    replace #(LitInt (Z.of_nat (S (length xs)) - 1)) with #(length xs); last (repeat f_equal; lia).

    (* Do advanced composotion with Hcr *)
    wp_apply (wp_couple_rand_adv_comp' _ _ _ _ _
                 (fun i => (tc_quicksort qsA qsB _ + tc_quicksort qsA qsB _)%R) with "[$]").


    (*


    (* pick a pivot index at random *)
    wp_apply wp_rand => //. iIntros (ip) "_"...
    (* pop the pivot from xs *)
    wp_apply (wp_remove_nth_unsafe _ xs l ip).
    { iPureIntro. split => //. apply (Nat.lt_le_trans _ _ _ (fin_to_nat_lt ip)).
      destruct xs => /= ; simpl in hn ; lia. }
    iIntros (pr_opt (p & r & pre & post & hpart & hpos & hpr & hr)).
    rewrite hpr. repeat (wp_pure ; unfold partition ; progress fold partition).
    (* partition xs \ p into smaller and larger elements *)
    wp_apply Partition => //.
    iIntros (le gt (xsle & xsgt & (hle & hgt & hperm) & ple & pgt))...
    (* sort xs_gt *)
    wp_apply "Hqs" => //. iIntros (gts (xs_gt_s & Lgts & Pgts & Sgts)).
    (* sort xs_le *)
    wp_apply "Hqs" => //. iIntros (les (xs_le_s & Lles & Ples & Sles))...
    (* re-assemble the sorted results *)
    replace (#p) with (inject p) by auto.
    wp_apply wp_list_cons => //. iIntros (p_xs_gt_s h_p_xs_gt).
    iApply wp_list_append => //. iIntros "!>" (xs_le_p_gt_s L).
    iApply "hφ".
    iExists (xs_le_s ++ p :: xs_gt_s). iPureIntro. repeat split => //.
    - clear -Ples Pgts hperm hpart.
      rewrite Pgts Ples. rewrite -Permutation_middle.
      rewrite hperm. rewrite Permutation_middle. rewrite -hpart. done.
    - clear -Sles Sgts ple pgt Ples Pgts. apply sorted_append => // ; intros.
      + apply ple. eapply Permutation_in => //.
      + apply pgt. eapply Permutation_in => //.
     *)
  Admitted.

End program.
