(* This file formalizes Rosulek's "Lemma 4.11 (Sampling without Replacement)",
   which should serve as a building block in a modular PRF-CPA security
   proof. *)

From clutch.prob_lang Require Import advantage typing.tychk.
From clutch.approxis Require Import approxis map list option.
From clutch.approxis.examples Require Import sum_seq bounded_oracle security_aux.
Set Default Proof Using "All".

Section sampling_without_replacement.

  Variable (card_support : nat).
  Variable (Q : nat).

  Definition sampling_with_replacement : val :=
    λ: "_", q_calls_poly #() #() #Q (λ: "_", rand #card_support).

  Definition sampling_without_replacement : val :=
    λ: "_", let: "f" :=
        let: "unused" := ref (list_seq #0 #(S card_support)) in
        λ:"_", let: "len" := list_length (! "unused") in
               let: "n" := rand ("len" - #1) in
               match: list_remove_nth (! "unused") "n" with
               | SOME "r_rest" =>
                   "unused" <- (Snd "r_rest") ;;
                   Fst "r_rest"
               | NONE => #0
               end
      in
      q_calls_poly #() #() #Q "f".

  (* TOOD: A poly time implementation that doesn't preallocate "unused". *)
  (* Definition sampling_without_replacement' : val :=
       λ: "_", let: "f" :=
           let: "seen" := ref list_nil in
           λ:"_", let: "r" := rand #card_support in
                  if: list_member "r" (! "seen") then
                    abort
                  else
                    ("seen" <- list_cons "r" (! "seen") ;;
                     "r")

                  let: "n" := rand "len" in
                  match: list_remove_nth (! "unused") "n" with
                  | SOME "r_rest" =>
                      "unused" <- (Snd "r_rest") ;;
                      Fst "r_rest"
                  | NONE => #0
                  end
         in
         q_calls_poly #() #() #Q "f". *)

  (* prf_cpa : avoid collision in the random prf input r, i.e. force r to be fresh wrt dom(irf):
     (r, irf r) vs (rand #card_input, rand #card_output)

     -> avoid dom(irf)
   *)

  (* prp_prf : avoid collision in the prf output, i.e. irf x vs irp x (for some input x) *)
  (* the interesting case is when x is fresh, otherwise no error is incurred.
     irp: pick new index i from rand |unused|, couple along list_nth i unused with
     irf: pick from rand #card_output
     error: ( card_output - |unused| ) / card_output

     -> pick from unused
    *)

  (* prp / prf is basically the "memoized" version of sampling without / with replacement. *)

  Context `{!approxisRGS Σ}.

  Local Opaque INR.

  Local Ltac smash :=
    repeat (apply Rcomplements.Rdiv_le_0_compat||apply pos_INR_S||apply pos_INR).

  Fact lemma_4_11 A :
        ↯ (ε_bday Q (S card_support))
      ⊢ REL sampling_with_replacement #() << sampling_without_replacement #() : (A → lrel_option lrel_nat)%lrel.
  Proof with (rel_pures_r ; rel_pures_l).
    iIntros "ε".
    rewrite /sampling_with_replacement/sampling_without_replacement...
    rewrite /q_calls_poly... rel_alloc_l counter_l as "counter_l".
    rel_bind_r (list_seq _ _) ; iApply refines_step_r ; iIntros (K) "spec".
    replace 0%Z with (Z.of_nat 0%nat) by lia.
    iMod (spec_list_seq with "spec") as (vunused) "(spec & %Hunused)" ; iSimpl in "spec".
    iApply spec_update_ret ; iFrame. idtac...
    rel_alloc_r ref_unused as "ref_unused"...
    rel_alloc_r counter_r as "counter_r"...
    rewrite /ε_bday Rdiv_mult_distr sum_seq.
    iApply (refines_na_alloc
              (∃ (q : nat)
                 (unused : list nat) vunused,
                  ↯ (fold_left Nat.add (seq q (Q-q)) 0%nat / S card_support)
                  ∗ counter_l ↦ #q
                  ∗ counter_r ↦ₛ #q
                  ∗ ⌜NoDup unused⌝
                  ∗ ⌜is_list unused vunused⌝
                  ∗ ⌜(S card_support - q <= length unused <= S card_support)%nat⌝
                  ∗ ref_unused ↦ₛ vunused
                  ∗ ⌜∀ x, x ∈ unused -> (x<S card_support)%nat ⌝
              )%I
              (nroot.@"cpa")) ; iFrame.
    replace (Q-0) with Q by lia; iFrame.
    iSplitL.
    { iExists _. iPureIntro. simpl.
      repeat split; try done.
      - apply NoDup_seq.
      - by rewrite length_seq.
      - by rewrite length_seq.
      - intros ?. rewrite elem_of_seq. lia. }
    clear vunused Hunused K. iIntros "#Hinv".
    rel_arrow_val ; iIntros (??) "_"...
    iApply (refines_na_inv with "[$Hinv]"); first done.
    iIntros "[>(%q&%unused&%vunused&ε&counter_l&counter_r&%HNoDup&%list_unused&%Hlen&unused&%unused_card) Hclose]".
    rel_load_l; rel_load_r...
    case_bool_decide ; last first...
    { (* we exceed query num *)
      iApply refines_na_close; iFrame.
      iSplit ; [|rel_vals].
      by iExists _. }
    rel_load_l ; rel_load_r ; rel_store_l ; rel_store_r...

    replace (Z.of_nat q+1)%Z with (Z.of_nat (S q)) by lia.
    replace (Q-q) with (S (Q-S q)) by lia.
    rewrite -cons_seq.
    rewrite fold_symmetric; try lia.
    simpl. rewrite -fold_symmetric; try lia.
    rewrite plus_INR Rdiv_plus_distr.

    rel_load_r.
    rel_apply_r refines_list_length_r => //. iIntros (?) "->"...

    set f := (λ n : nat, if (n <=? (length unused)) then (nth n unused 0) else n + (length unused)).
    rel_apply (refines_couple_UU_err_rev _ _ (mknonnegreal _ _) f); try lia.
    { intros. rewrite /f.
      rewrite leb_correct; try lia.
      destruct (lt_dec n (length unused)).
      - apply Forall_nth => //.
        1: rewrite Forall_forall ; done.
      - rewrite nth_overflow ; lia.
    }
    { rewrite /f.
      intros n1 n2 hn1 hn2.
      rewrite !leb_correct; try lia.
      destruct (zerop (length unused)) as [hlen|hlen].
      { rewrite hlen in hn1. cbv in hn1. inversion hn1 as [hn1'|_ []].
        rewrite hlen in hn2. cbv in hn2. inversion hn2 as [hn2'|_ []].
        done.
      }
      apply NoDup_nth ; try lia.
      by apply NoDup_ListNoDup.
    }
    { done. }

    iDestruct (ec_split with "[$]") as "[Hε Hε']"; try smash.
    iSplitL "Hε".
      { iApply ec_weaken; last done.
        split.
        - rewrite -Rdiv_def.
          smash. rewrite -minus_INR; last lia.
          smash.
        - rewrite Rdiv_def.
          apply Rmult_le_compat_r.
          + apply Rlt_le.
            apply RinvN_pos'.
          + rewrite -minus_INR; last lia.
            apply le_INR. lia.
      }

      iIntros (x). iModIntro. rewrite /f...
      iIntros "%Hx".
      rewrite leb_correct; last lia.
      rel_load_r.
      destruct unused as [|next_unused rest_unused] eqn:case_unused.
      {
        simpl in list_unused.
        rewrite list_unused.
        rewrite /list_remove_nth...
        iApply refines_na_close; iFrame.
        iSplitL ; [|destruct x ; rel_vals].
        iExists unused.
        iFrame.
        rewrite case_unused. iPureIntro. repeat split.
        - constructor.
        - simpl. simpl in Hlen. destruct Hlen. lia.
        - simpl. simpl in Hlen. destruct Hlen. lia.
        - intros ?. set_solver.
      }
      rewrite -case_unused.
      rewrite -case_unused in Hlen HNoDup list_unused unused_card Hx.
      rel_apply_r refines_list_remove_nth_r.
      { iPureIntro. split => //. revert Hx. rewrite case_unused => /=. lia. }
      iIntros (?) "(%&%&%&%&->&<-&->&%)"...
      rewrite nth_middle.
      rel_store_r...
      iApply (refines_na_close).
      iSplitR "Hclose"; last first.
      { iFrame.
        rel_values.
        repeat iExists _. iRight.
        iPureIntro; repeat split; try done.
        by eexists _.
      }
      iModIntro.
      iExists _, (_++_).
      iFrame.
      iPureIntro; repeat split.
      - rewrite NoDup_ListNoDup.
        eapply NoDup_remove_1.
        rewrite -NoDup_ListNoDup.
        done.
      - done.
      - rewrite length_app.
        rewrite length_app length_cons in Hlen. lia.
      - transitivity (length (l1 ++ e :: l2)) ; try lia.
        rewrite ?length_app. simpl. lia.
      - set_unfold ; naive_solver.
        Unshelve.
        rewrite -Rdiv_def.
        smash.
        rewrite -minus_INR; last lia.
        smash.
    Qed.


  Fact lemma_4_11' A :
        ↯ (ε_bday Q (S card_support))
      ⊢ REL sampling_without_replacement #() << sampling_with_replacement #() : (A → lrel_option lrel_nat)%lrel.
  Proof with (rel_pures_r ; rel_pures_l).
    iIntros "ε".
    rewrite /sampling_with_replacement/sampling_without_replacement...
    rewrite /q_calls_poly... rel_alloc_r counter_r as "counter_r".
    rel_bind_l (list_seq _ _) ; iApply refines_wp_l.
    replace 0%Z with (Z.of_nat 0%nat) by lia.
    iApply wp_list_seq => //.
    iNext. iIntros (vunused Hunused).
    idtac...
    rel_alloc_l ref_unused as "ref_unused"...
    rel_alloc_l counter_l as "counter_l"...
    rewrite /ε_bday Rdiv_mult_distr sum_seq.
    iApply (refines_na_alloc
              (∃ (q : nat)
                 (unused : list nat) vunused,
                  ↯ (fold_left Nat.add (seq q (Q-q)) 0%nat / S card_support)
                  ∗ counter_l ↦ #q
                  ∗ counter_r ↦ₛ #q
                  ∗ ⌜NoDup unused⌝
                  ∗ ⌜is_list unused vunused⌝
                  ∗ ⌜(S card_support - q <= length unused <= S card_support)%nat⌝
                  ∗ ref_unused ↦ vunused
                  ∗ ⌜∀ x, x ∈ unused -> (x<S card_support)%nat ⌝
              )%I
              (nroot.@"cpa")) ; iFrame.
    replace (Q-0) with Q by lia; iFrame.
    iSplitL.
    { iExists _. iPureIntro. simpl.
      repeat split; try done.
      - apply NoDup_seq.
      - by rewrite length_seq.
      - by rewrite length_seq.
      - intros ?. rewrite elem_of_seq. lia. }
    clear vunused Hunused. iIntros "#Hinv".
    rel_arrow_val ; iIntros (??) "_"...
    iApply (refines_na_inv with "[$Hinv]"); first done.
    iIntros "[>(%q&%unused&%vunused&ε&counter_l&counter_r&%HNoDup&%list_unused&%Hlen&unused&%unused_card) Hclose]".
    rel_load_l; rel_load_r...
    case_bool_decide ; last first...
    { (* we exceed query num *)
      iApply refines_na_close; iFrame.
      iSplit ; [|rel_vals].
      by iExists _. }
    rel_load_l ; rel_load_r ; rel_store_l ; rel_store_r...

    replace (Z.of_nat q+1)%Z with (Z.of_nat (S q)) by lia.
    replace (Q-q) with (S (Q-S q)) by lia.
    rewrite -cons_seq.
    rewrite fold_symmetric; try lia.
    simpl. rewrite -fold_symmetric; try lia.
    rewrite plus_INR Rdiv_plus_distr.

    rel_load_l.
    rel_apply_l refines_list_length_l => //. iIntros (?) "->"...

    set f := (λ n : nat, if (n <=? (length unused)) then (nth n unused 0) else n + (length unused)).
    rel_apply (refines_couple_UU_err _ _ (mknonnegreal _ _) f); try lia.
    { intros. rewrite /f.
      rewrite leb_correct; try lia.
      destruct (lt_dec n (length unused)).
      - apply Forall_nth => //.
        1: rewrite Forall_forall ; done.
      - rewrite nth_overflow ; lia.
    }
    { rewrite /f.
      intros n1 n2 hn1 hn2.
      rewrite !leb_correct; try lia.
      destruct (zerop (length unused)) as [hlen|hlen].
      { rewrite hlen in hn1. cbv in hn1. inversion hn1 as [hn1'|_ []].
        rewrite hlen in hn2. cbv in hn2. inversion hn2 as [hn2'|_ []].
        done.
      }
      apply NoDup_nth ; try lia.
      by apply NoDup_ListNoDup.
    }
    { done. }

    iDestruct (ec_split with "[$]") as "[Hε Hε']"; try smash.
    iSplitL "Hε".
      { iApply ec_weaken; last done.
        split.
        - rewrite -Rdiv_def.
          smash. rewrite -minus_INR; last lia.
          smash.
        - rewrite Rdiv_def.
          apply Rmult_le_compat_r.
          + apply Rlt_le.
            apply RinvN_pos'.
          + rewrite -minus_INR; last lia.
            apply le_INR. lia.
      }

      iIntros (x). iModIntro. rewrite /f...
      iIntros "%Hx".
      rewrite leb_correct; last lia.
      rel_load_l.
      destruct unused as [|next_unused rest_unused] eqn:case_unused.
      {
        simpl in list_unused.
        rewrite list_unused.
        rewrite /list_remove_nth...
        iApply refines_na_close; iFrame.
        iSplitL ; [|destruct x ; rel_vals].
        iExists unused.
        iFrame.
        rewrite case_unused. iPureIntro. repeat split.
        - constructor.
        - simpl. simpl in Hlen. destruct Hlen. lia.
        - simpl. simpl in Hlen. destruct Hlen. lia.
        - intros ?. set_solver.
      }
      rewrite -case_unused.
      rewrite -case_unused in Hlen HNoDup list_unused unused_card Hx.
      rel_apply_l refines_list_remove_nth_l.
      { iPureIntro. split => //. revert Hx. rewrite case_unused => /=. lia. }
      iIntros (?) "(%&%&%&%&->&<-&->&%)"...
      rewrite nth_middle.
      rel_store_l...
      iApply (refines_na_close).
      iSplitR "Hclose"; last first.
      { iFrame.
        rel_values.
        repeat iExists _. iRight.
        iPureIntro; repeat split; try done.
        by eexists _.
      }
      iModIntro.
      iExists _, (_++_).
      iFrame.
      iPureIntro; repeat split.
      - rewrite NoDup_ListNoDup.
        eapply NoDup_remove_1.
        rewrite -NoDup_ListNoDup.
        done.
      - done.
      - rewrite length_app.
        rewrite length_app length_cons in Hlen. lia.
      - transitivity (length (l1 ++ e :: l2)) ; try lia.
        rewrite ?length_app. simpl. lia.
      - set_unfold ; naive_solver.
        Unshelve.
        rewrite -Rdiv_def.
        smash.
        rewrite -minus_INR; last lia.
        smash.
    Qed.

End sampling_without_replacement.
