(* (* PRF based on a PRG. *)
From clutch.approxis Require Import approxis map prf prg list.
From clutch.approxis.examples Require Import option.
Import prg.bounds_check.
Set Default Proof Using "Type*".

Section defs.

    Lemma base_mult_inj : forall (n m n' m' p : nat),
      n < p -> n' < p -> m * p + n = m' * p + n' -> m = m' ∧ n = n'.
    Proof. intros * Hn Hn' Heq. Search (_ * _ + _).
      pose proof (Nat.mod_unique (m * p + n) p m n) as H1.
      pose proof (Nat.mod_unique (m * p + n) p m' n') as H2.
      pose proof (Nat.div_unique (m * p + n) p m n) as H1'.
      pose proof (Nat.div_unique (m * p + n) p m' n') as H2'.
      apply H1' in Hn as Heq1'; apply H2' in Hn' as Heq2';
      apply H1 in Hn as Heq1; apply H2 in Hn' as Heq2; try lia.
    Qed.

  (*** A PRG *)
  Context `{PRG}.

  (* to retrieve lemmas, ctrl f this : XCJQSDQSJDKL*)

  Local Opaque INR.

  Definition prg_extension : val :=
    λ: "x",
      let: "r" := prg "x" in
      (prg (Fst "r"), (Snd "r")).
  
  Let Input := 2^card_input - 1.
  Let Extension := 2^card_extension - 1.
  Let TwiceExtension := 2^(2*card_extension) - 1.

  Definition prg_extension_tape : val :=
    λ: "l" "x",
      let: "r" := prg (rand "l" #Input) in
      (prg (Fst "r"), (Snd "r")).
  
  Definition rg_extension : val :=
    λ: "x",
      let: "r1" := (rand (#1 ≪ #card_input), rand (#1 ≪ #card_extension)) in
      (prg (Fst "r"), (Snd "r")).
 
  (** RandML types of the scheme. *)
  Definition TInput := TInt.
  Definition TOutput := TInt.
  Definition THybrid := (TInput → TOutput)%ty.
  Definition THybridOpt := (TInput → TOption TOutput)%ty.

  Variable adv : val.
  Definition TAdv : type := ((TInput → (TUnit+ TOutput)) → TBool)%ty.
  Variable adv_typed : (∅ ⊢ₜ adv : TAdv).
  Definition q_calls := q_calls #card_input.

  Context (f : nat -> nonnegreal).

  Section proofs.
    Context `{!approxisRGS Σ}.

    Theorem refines_prg_l K e E A (l : expr) :
        refines E (fill K (let: "r1" := rand #Input in let: "r2" := rand(l) #Extension in ("r1", "r2"))) e A
      ⊢
        REL (fill K (prg (rand #Input)%E)) << e @ E : A.
    Admitted.

    Definition random_generator_tape : val :=
      (λ: "l" "card_input" "card_extension" "x",
        let: "r1" := rand ((#1 ≪ "card_input") - #1) in
        let: "r2" := rand "l" ((#1 ≪ "card_extension") - #1) in
        ("r1", "r2"))%V.

    Definition twice__extension (l : list nat) : nat := match l with
      | x1 :: x2 :: [] => x1 * (S Extension) + x2 
      | _ => 0
    end.

    Lemma aux ι ι' E :
        ι ↪N (Extension; [])
      ∗ ι'↪ₛN(TwiceExtension;[]) ⊢
        REL (
        let: "r2" := rand(#lbl:ι) #Extension in
        let: "r3" := prg (rand #Input) in
        (Fst "r3","r2" * #(S Extension) + Snd "r3"))
        <<
        (let: "r1" := rand #Input in
        let: "r2" := rand(#lbl:ι') (#1 ≪ #(2 * card_extension) - #1) in ("r1", "r2")) @ E : lrel_int * lrel_int.
    Proof with rel_pures_l; rel_pures_r.
      iIntros "[Hι Hι']".
      assert (eq2p : forall (p : nat), S (2 ^ p - 1) = 2 ^ p).
      {
        intro p. pose proof (fin.pow_ge_1 2 p) as H1.
        assert (H2 : 1 <= 2) by lia. apply H1 in H2.
        destruct (2 ^ p) as [|n']; first inversion H2.
        lia.
      }
      rel_apply (refines_couple_exp TwiceExtension Extension 2 twice__extension).
      - intros * G. destruct l as [|x1 l]; last destruct l as [|x2 l]; last destruct l as [|h t]; simpl; try lia.
        rewrite /TwiceExtension. inversion G. inversion H4.
        rewrite /Extension. rewrite /Extension in H7 H3.
        clear -H3 H7 eq2p. rewrite eq2p. rewrite eq2p in H3 H7.
        apply (Nat.lt_le_trans _ (x1 * 2^card_extension + 2^card_extension)).
        + rewrite -Nat.add_lt_mono_l. assumption.
        + rewrite eq2p.
          apply (Nat.le_trans _ ((2^card_extension - 1) * 2^card_extension + 2^card_extension)).
          * rewrite -Nat.add_le_mono_r. apply Nat.mul_le_mono; lia.
          * rewrite Nat.mul_sub_distr_r. rewrite Nat.mul_1_l.
            rewrite Nat.sub_add.
            { rewrite Nat.pow_add_r. replace (card_extension + 0) with card_extension by lia.
              done. }
            {
              replace (2 ^ card_extension) with (2^card_extension * 1) by lia.
              replace (2 ^ card_extension * 1 * (2 ^ card_extension * 1)) with
                (2 ^ card_extension * 2 ^ card_extension) by lia.
              apply Nat.mul_le_mono_l.
              apply (fin.pow_ge_1 2 _). lia.
            }
      - intros * H1 H2 H3 H4 H5. 
        destruct l1 as [|x1 l]; last destruct l as [|x2 l];
        last destruct l as [|h t]; simpl; try inversion H3.
        destruct l2 as [|x1' l]; last destruct l as [|x2' l];
        last destruct l as [|h t]; simpl; try inversion H4.
        inversion H1. inversion H9.
        inversion H2. inversion H17.
        simpl in H5. pose proof (base_mult_inj x2 x1 x2' x1' (S Extension)) as G.
        apply G in H12; try lia; try assumption.
        destruct H12 as [G1 G2]. subst. done.
      - rewrite /TwiceExtension. rewrite /Extension.
        rewrite eq2p.
        rewrite eq2p.
        rewrite -Nat.pow_mul_r. rewrite Nat.mul_comm. reflexivity.
      - iFrame. iIntros (l m Hlleq Hmleq [Hlengthl Hf]) "Hι Hι'". simpl.
        destruct l as [|x1 l]; last destruct l as [|x2 l]; last destruct l as [|h t]; simpl; try inversion Hlengthl.
        clear Hlengthl. simpl in Hf...
        rel_apply refines_rand_l.
        iFrame. iModIntro. iIntros "Hι %Hineqx1"...
        rel_bind_l (prg _)%E.
        rel_apply (refines_prg_l _ _ _ _  #lbl:ι).
        rel_apply (refines_couple_UU); first done.
        iModIntro. iIntros (n) "%Hn"...
        rel_apply refines_rand_l.
        iFrame. iModIntro. iIntros "Hι %Hineqx2"...
        replace (#(1 ≪ (2 * card_extension) - 1)) with (#(TwiceExtension)); first last.
        { rewrite /TwiceExtension. admit. }
        rel_apply (refines_rand_r with "Hι'").
        iIntros "Hι' %Hineqm".
        replace ((Z.of_nat x1 * Z.of_nat (S Extension) + Z.of_nat x2))%Z with
          (Z.of_nat m) by (rewrite -Hf; lia)...
          
        



    Theorem prg_ext_is_prg' (Q : nat) : ⊢
      REL (let: "ι" := alloc #Extension in (λ: <>, prg_extension_tape "ι" #()))
       << (let: "ι" := alloc #Extension in
          random_generator_tape "ι"
            #card_input #(2 * card_extension)) : () → (lrel_int * lrel_int).
    Proof with rel_pures_l; rel_pures_r. iStartProof.
      rewrite /prg; rewrite /prg_extension_tape; rewrite /random_generator_tape...
      
      rel_alloctape_l ι as "Hι".
      rel_alloctape_r ι' as "Hι'".
      set (P := (
          ι ↪N (Extension; [])
        ∗ ι'↪ₛN(Extension;[]))%I
      ). rel_apply (refines_na_alloc P (nroot.@"prg")). iFrame. iIntros "#Inv".
      rel_arrow_val; iIntros (v1 v2) "[%eq1 %eq2]"; subst.
      rel_apply refines_na_inv. iSplitL; first iApply "Inv".
      iIntros "[[Hι Hι'] Hclose]"...
      rel_bind_l (prg _). rel_apply refines_prg_l.
      replace #(Z.sub (Z.shiftl 1 (Z.of_nat card_input)) 1) with #Input.
      {
      }
      rel_bind_r (rand _ _)%E.
      About refines_rand_empty_r.

      

    Theorem prg_ext_is_prg (Q : nat) : ⊢
      REL PRG_real_rand #true  adv prg_scheme #Q
       << PRG_real_rand #false adv prg_scheme #Q : lrel_bool.
    Proof with rel_pures_l; rel_pures_r.
      rewrite /PRG_real_rand... rewrite /get_prg...
      rewrite /random_generator...
      rewrite /get_card_input; rewrite /get_card_extension...
      rel_bind_l (bounded_oracle.q_calls _ _ _).
      rel_bind_r (bounded_oracle.q_calls _ _ _).
      rel_apply (refines_bind _ _ _ (lrel_int → lrel_int)).
      2 : {
        admit.
      }
      rewrite /bounded_oracle.q_calls...
      rel_alloc_l cnt as "Hcnt";
      rel_alloc_r cnt' as "Hcnt'"...
      rel_apply (refines_na_alloc (∃ (q : nat),
          cnt  ↦  #q
        ∗ cnt' ↦ₛ #q
      ) (nroot.@"prg_ext")).
      iSplitL; first iExists 0; iFrame.
      iIntros "Inv".
      rel_arrow_val.
      iIntros (v1 v2) "[%x [%eq1 %eq2]]"; subst...
    
  End proofs.


End defs.

(* XCJQSDQSJDKL
  Lemma seq_S_len : forall (start len : nat),
    seq start (S len) = seq start len ++ [start + len].
  Proof. intros start len; generalize dependent start; induction len as [|len' IHlen];
    intro start.
    - simpl. rewrite Nat.add_0_r. reflexivity.
    - simpl. simpl in IHlen. rewrite IHlen.
      simpl. replace (start + S len') with (S (start + len')) by lia.
      reflexivity.
  Qed.

  Lemma fold_left_last : forall (last init : nat) (l : list nat),
    fold_left Nat.add (l ++ [last]) init = fold_left Nat.add l init + last.
  Proof. intros last init l. generalize dependent last.
    generalize dependent init. induction l as [|h t IHt]; intros init last.
    - simpl. reflexivity.
    - simpl. rewrite IHt. reflexivity.
  Qed. 

  Lemma lt_numR : forall (p1 p2 q : R),
    (0 < q)%R -> (p1 <= p2)%R -> (p1 / q <= p2 / q)%R.
  Proof. intros * H1 H2. apply Rcomplements.Rle_div_l; first apply H1.
    rewrite -Rmult_div_swap. rewrite -Rmult_div_assoc.
    rewrite Rdiv_diag.
    - rewrite Rmult_1_r. apply H2.
    - symmetry. apply Rlt_not_eq. apply H1.
  Qed.

  Lemma sum_seq_0_q : forall (n : nat),
    INR (fold_left Nat.add (seq 0 n) 0) = ((INR ((n - 1) * n)) / 2)%R.
  Proof. intros *. induction n as [|n' IHn].
    - simpl. real_solver.
    - rewrite seq_S_len. rewrite fold_left_last.
      rewrite plus_INR. rewrite IHn. simpl.
      replace (n' - 0) with n' by lia.
      replace (INR n') with ((2 * INR n')/2)%R by real_solver.
      rewrite -Rdiv_plus_distr.
      apply Rdiv_eq_compat_r. Set Printing Coercions.
      replace (2%R) with (INR 2) by real_solver.
      rewrite -mult_INR. rewrite -plus_INR.
      assert ((n' - 1) * n' + 2 * n' = n' * S n').
      { rewrite Nat.mul_sub_distr_r.
        rewrite Nat.mul_succ_r.
        replace (1 * n') with n' by lia.
        rewrite -Nat.add_sub_swap; last (induction n'; lia).
        rewrite -Nat.add_sub_assoc; last (induction n'; lia).
        simpl. replace (n' + 0) with n' by lia.
        rewrite -Nat.add_sub_assoc; last (induction n'; lia).
        replace (n' - n') with 0 by lia.
        replace (n' + 0) with n' by lia. reflexivity. }
      rewrite H; reflexivity.
  Qed.
*) *)