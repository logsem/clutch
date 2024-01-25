(** * Termination with probability 1 of the WalkSAT algorithm*)
From clutch.ub_logic Require Export ub_clutch ub_rules.
From clutch Require Export examples.approximate_samplers.approx_sampler_lib.
From Coquelicot Require Import Series.
Require Import Lra.

Set Default Proof Using "Type*".

Section higherorder_walkSAT.
  (** Demonstration of using the higher-order spec for stateful computation (WalkSAT) *)
  (** This "sampler" does not just return a value, but modifies a state *)
  Local Open Scope R.
  Context `{!ub_clutchGS Σ}.

  Context (N : nat).

  (* an assignment is a list of length N booleans *)
  (* value-level representation for assignments *)
  Inductive inv_asn' : list bool -> val -> Prop :=
    | inv_emp : inv_asn' [] NONEV
    | inv_cons (b : bool) (m' : list bool) (asn' : val) : (inv_asn' m' asn') -> inv_asn' (b :: m') (SOMEV (#b, asn')).
  Definition inv_asn m asn : Prop := length m = N /\ inv_asn' m asn.

  (* stuck expression *)
  Definition error : expr := (#42 #42)%E.

  (* set up a random assignment of n boolean variables *)
  Definition mk_init_asn': val :=
    (rec: "mk_asn'" "n" :=
       if: ("n" = #0)
       then NONE
       else
         let: "b" := (rand #1 = #1) in
         let: "r" := ("mk_asn'" ("n" - #1)) in
         SOME ("b", "r"))%V.
  Definition mk_init_asn : val := (λ: "_", mk_init_asn' #N).


  Lemma init_asn'_inv (M: nat) E : (⊢ WP (mk_init_asn' #M) @ E {{ fun v' => ∃ m, ⌜ inv_asn' m v' /\ length m = M ⌝}})%I.
  Proof.
    iInduction M as [|M'] "IH".
    - rewrite /mk_init_asn'; wp_pures.
      iModIntro; iExists []; iPureIntro; split; [constructor | by simpl].
    - rewrite /mk_init_asn'.
      do 3 wp_pure.
      wp_bind (rand _)%E; wp_apply wp_rand; eauto; iIntros (b) "%Hb".
      do 4 wp_pure.
      replace #(S M' - 1)%Z with #M'; [| do 2 f_equal; lia].
      wp_bind (RecV _ _ _ _).
      wp_apply (ub_wp_wand  with "IH").
      iIntros (asn') "[%m' (%Hm'_inv' & %Hm'_len)]".
      wp_pures.
      iModIntro; iExists ((bool_decide (#b = #1)) :: m').
      iPureIntro; split.
      + by apply inv_cons.
      + rewrite cons_length Hm'_len /=; lia.
  Qed.

  Definition eval_asn : val :=
    (rec: "eval_asn" "asn" "n" :=
       match: "asn" with
          NONE => error
        | SOME "R" => if: ("n" = #0)
                        then (Fst "R")
                        else ("eval_asn" (Snd "R") ("n" - #1))
       end)%V.


  Definition wp_eval_asn m asn E (n : nat) :
    (⊢ ⌜ (n < (length m))%nat ⌝ -∗ ⌜ inv_asn' m asn ⌝ -∗ WP (eval_asn asn #n)%E @ E {{ fun v => ⌜#(m !!! n : bool) = v⌝}})%I .
  Proof.
    iIntros "%Hn %Hinv".
    iRevert (Hn).
    iRevert (n).
    iInduction Hinv as [| b m' asn' Hinv H] "IH".
    - iIntros (? Hk). simpl in Hk; lia.
    - iIntros (n' Hlen).
      rewrite /eval_asn.
      wp_pures.
      case_bool_decide.
      + wp_pures.
        iModIntro; iPureIntro.
        inversion H as [H'].
        by rewrite -(Nat2Z.id n') H' /=.
      + do 3 wp_pure.
        replace (Z.of_nat n' - 1)%Z with (Z.of_nat (n' - 1)%nat); last first.
        { rewrite Nat2Z.inj_sub; try lia.
          pose Hc := Nat.le_0_l; apply (Nat.lt_eq_cases 0%nat n') in Hc.
          destruct Hc; try lia.
          by rewrite -H0 /= Nat2Z.inj_0 in H. }
        destruct n' as [|n''] eqn:Hn'; [by rewrite Nat2Z.inj_0 in H |].
        wp_apply (ub_wp_wand with "[IH]").
        { iApply "IH".
          iPureIntro.
          rewrite cons_length in Hlen.
          apply (Nat.le_lt_add_lt 1%nat 1%nat); try lia. }
        iIntros (v) "%Hv"; iPureIntro.
        rewrite lookup_total_cons_ne_0; try eauto.
        rewrite -Hv Nat.pred_succ.
        by replace (S n'' - 1)%nat with n'' by lia.
  Qed.


  Definition update_asn : val :=
    (rec: "update_asn'" "asn" "n" "b" :=
       match: "asn" with
         NONE => error
        | SOME "R" =>
            if: ("n" = #0)
              then SOME ("b", (Snd "R"))
              else
                let: "b0" := (Fst "R") in
                let: "r0" := ("update_asn'" (Snd "R") ("n" - #1) "b") in
                SOME ("b0", "r0")
       end)%V.

  Definition wp_update_asn m asn E n (b: bool) :
    (⊢ ⌜(n < length m)%nat ⌝ -∗ ⌜inv_asn' m asn ⌝ -∗ WP (update_asn asn #n #b)%E @ E {{ fun asn' => ⌜inv_asn' (<[n := b]> m) asn' ⌝}})%I.
  Proof.
    iIntros "%Hn %Hinv".
    iRevert (Hn).
    iRevert (n).
    iInduction Hinv as [| b' m' asn' Hinv H] "IH".
    - iIntros (? Hk). simpl in Hk; lia.
    - iIntros (n' Hlen).
      rewrite /update_asn.
      wp_pures.
      case_bool_decide.
      + wp_pures.
        iModIntro; iPureIntro.
        inversion H as [H'].
        replace (<[n':=b]> (b' :: m')) with (b :: m'); [by constructor|].
        rewrite -Nat2Z.inj_0 in H'; apply Nat2Z.inj in H'.
        by rewrite H' /=.
      + do 6 wp_pure.
        wp_bind (RecV _ _ _ _ _ _).
        replace (Z.of_nat n' - 1)%Z with (Z.of_nat (n' - 1)%nat); last first.
        { rewrite Nat2Z.inj_sub; try lia.
          pose Hc := Nat.le_0_l; apply (Nat.lt_eq_cases 0%nat n') in Hc.
          destruct Hc; try lia.
          by rewrite -H0 /= Nat2Z.inj_0 in H. }
        wp_apply (ub_wp_wand with "[IH]").
        { iApply "IH".
          iPureIntro.
          rewrite cons_length in Hlen.
          apply (Nat.le_lt_add_lt 1%nat 1%nat); try lia.
          admit. (* doable *)
        }
        iIntros (v) "%Hv".
        wp_pures.
        iModIntro; iPureIntro.
        replace (n')%nat with (S (n' - 1))%nat; last admit. (* provable *)
        simpl.
        by constructor.
  Admitted.

  (* our program will be indexed by a fixed formula to avoid manipulating value-level formulae *)
  Inductive Polarity := Pos | Neg.

  Inductive clause :=
      | ClauseV (e1 e2 e3 : fVar)
    with fVar :=
      | FvarV (p : Polarity) (n : nat) (nwf : (n < N)%nat).
  Definition formula : Type := list (clause).

  Definition fVar_index (v : fVar) : nat :=
    match v with
      | FvarV _ n _ => n
    end.

  Definition fVar_in_clause (v : fVar) (c : clause) : Prop :=
    match c with
      | ClauseV e1 e2 e3  => (v = e1) \/ (v = e2) \/ (v = e3)
    end.

  Definition index_in_clause (n : nat) (c : clause) : Prop :=
    match c with
      | ClauseV e1 e2 e3 => (n = fVar_index e1) \/ (n = fVar_index e1) \/ (n = fVar_index e1)
    end.

  Definition proj_clause_value (c : clause) (target : fin 3) : fVar :=
    match c with
      | (ClauseV e1 e2 e3) =>
          if (Fin.eqb target (0 : fin 3))%fin
            then e1
            else if (Fin.eqb target (1 : fin 3))%fin
                 then e2
                 else e3
      end.


  (* evaluation of the coq-level assignments *)

  Definition fvar_SAT (m : list bool) (v : fVar) : bool :=
    match v with
    | FvarV p n _ =>
        match p with
          | Pos => (m !!! n)
          | Neg => (negb (m !!! n))
        end
    end.

  Definition clause_SAT (m : list bool) (c : clause) : bool :=
    match c with
      | ClauseV e1 e2 e3 => (fvar_SAT m e1) || (fvar_SAT m e2) || (fvar_SAT m e3)
    end.

  Definition formula_SAT (m : list bool) (f : formula) : bool :=
    fold_left (fun acc c => acc && clause_SAT m c) f true.


  (* If there is a solution s, for any unsatisfied clause, the clause contains a variable
      which differers from the solution. *)
  Lemma progress_is_possible_clause (c : clause) (m solution : list bool) :
    (clause_SAT solution c = true) ->
    (clause_SAT m c = false) ->
    exists (v : fVar), (fVar_in_clause v c) /\ (m !!! (fVar_index v) = negb (solution !!! (fVar_index v))).
  Proof.
    intros Hsat Hunsat.
    destruct c as [e1 e2 e3].
    rewrite /clause_SAT /= in Hsat, Hunsat.
    apply orb_false_elim in Hunsat as [Hunsat' He3].
    apply orb_false_elim in Hunsat' as [He1 He2].
    apply orb_prop in Hsat as [Hsat'|Hsat]; first apply orb_prop in Hsat' as [Hsat|Hsat].
    - exists e1; simpl; split; [by left |].
      destruct e1 as [p n nwf]; simpl.
      destruct p; simpl in Hsat, He1.
      + by rewrite Hsat He1 /=.
      + apply negb_true_iff in Hsat, He1; rewrite negb_involutive in He1.
        by rewrite Hsat He1 /=.
    - exists e2; simpl; split; [right; by left|].
      destruct e2 as [p n nwf]; simpl.
      destruct p; simpl in Hsat, He2.
      + by rewrite Hsat He2 /=.
      + apply negb_true_iff in Hsat, He2; rewrite negb_involutive in He2.
        by rewrite Hsat He2 /=.
    - exists e3; simpl; split; [right; by right|].
      destruct e3 as [p n nwf]; simpl.
      destruct p; simpl in Hsat, He3.
      + by rewrite Hsat He3 /=.
      + apply negb_true_iff in Hsat, He3; rewrite negb_involutive in He3.
        by rewrite Hsat He3 /=.
  Qed.



  (* turns the existence of an fvar that can be improved into a concrete sample to amplify against *)
  Lemma reflect_progress_to_target (v : fVar) (c : clause) :
    fVar_in_clause v c -> exists s : fin 3, (proj_clause_value c s = v).
  Proof.
    intros H.
    destruct c as [e1 e2 e3].
    simpl in H; destruct H as [H|[H|H]].
    - exists 0%fin. by simpl.
    - exists 1%fin. by simpl.
    - exists 2%fin. by simpl.
  Qed.


  (* obtains the clause which simplified walkSAT will resample*)
  Lemma find_progress m f :
    (formula_SAT m f = false) ->
    exists f1 f2 c,
      f = f1 ++ [c] ++ f2 /\
      Forall (fun c' => clause_SAT m c' = true) f1 /\
      clause_SAT m c = false.
  Proof.
    intros Hunsat.
    induction f as [|c f' IH].
    - rewrite /formula_SAT /= in Hunsat. discriminate.
    - destruct (clause_SAT m c) as [|] eqn:Hc.
      + assert (Hunsat' : formula_SAT m f' = false).
        { (* true b/c clause_SAT m c is true (another fold commuting problem) *)
          rewrite /formula_SAT /= in Hunsat.
          admit.
        }
        destruct (IH Hunsat') as [f1 [f2 [c' (H & Hf1 & Hc')]]].
        exists (c :: f1), f2, c'; split; last split.
        * by rewrite /= H.
        * apply Forall_cons_2; [apply Hc | apply Hf1].
        * apply Hc'.
      + exists [], f', c; split; last split.
        * by simpl.
        * apply Forall_nil_2.
        * apply Hc.
  Admitted.




  (* this proof measues progress by the similarity to a fixed (known) solution *)
  Definition progress_measure (m solution : list bool) : nat :=
    fold_right (fun p acc => (acc + match p with | (s, t) => if (eqb s t)then 0%nat else 1%nat end)%nat) 0%nat (zip m solution).


  Lemma progress_complete m solution : (length m = length solution) -> (progress_measure m solution = 0%nat) -> m = solution.
  Proof.
    generalize dependent solution.
    induction m as [|m0 ms IH].
    - intros solution Hl _; destruct solution; eauto.
      simpl in Hl; discriminate.
    - intros solution Hl Hp.
      destruct solution as [|s0 ss].
      { simpl in Hl; discriminate. }
      rewrite /progress_measure /fold_left /= in Hp.
      apply Nat.eq_add_0 in Hp; destruct Hp as [Hp Hhp].
      f_equal.
      + apply eqb_eq. destruct (eqb m0 s0); [done|discriminate].
      + apply IH.
        * do 2 rewrite cons_length in Hl; by inversion Hl.
        * by rewrite /progress_measure.
  Qed.


  (* flipping a variable which is different to the solution brings an assignment closer to the solution *)
  Lemma flip_makes_progress (m solution : list bool) (v : fVar) :
      (m !!! (fVar_index v) = negb (solution !!! (fVar_index v))) ->
      (progress_measure (<[fVar_index v := negb (m !!! (fVar_index v))]> m ) solution < progress_measure m solution)%nat.
  Proof.
    intros Hdiff.
    (* Induct over the lists, = when not equal to fVar_index v, < when equal *)
    (* need to show we hit fVar_index... induction should keep track of location? *)
  Admitted.


  (* evaluation of the value-level assignments *)

  Definition evaluate_fvar (f: fVar) : val :=
    (λ: "asn",
       match f with
         | FvarV p n _ =>
             let: "b" := (eval_asn "asn" #n) in
             match p with
               | Pos => "b"
               | Neg => ~"b"
              end
        end).

  Lemma wp_evaluate_fvar l asn m v E :
    (⊢ ⌜ inv_asn m asn ⌝ -∗ l ↦ asn -∗ WP (evaluate_fvar v) asn @ E {{ fun v' => l ↦ asn ∗ ⌜v' = #(fvar_SAT m v)⌝ }} )%I.
  Proof.
    iIntros "%Hinv Hl".
    destruct v as [p v vwf].
    rewrite /evaluate_fvar.
    wp_pures.
    wp_bind (eval_asn _ _)%E.
    wp_apply (ub_wp_wand with "[]").
    { iApply wp_eval_asn; iPureIntro; last first.
      - rewrite /inv_asn in Hinv. by destruct Hinv.
      - destruct Hinv; lia. }
    iIntros (b) "<-".
    destruct p; wp_pures; iModIntro; eauto.
  Qed.


  Definition evaluate_clause (c : clause) : val :=
    (λ: "asn",
        match c with
         | ClauseV e1 e2 e3 => ((evaluate_fvar e1 "asn") || (evaluate_fvar e2 "asn") || (evaluate_fvar e3 "asn"))
        end)%V.

  Lemma wp_evaluate_clause l asn m c E :
    (⊢ ⌜ inv_asn m asn ⌝ -∗ l ↦ asn -∗ WP (evaluate_clause c) asn @ E {{ fun v => l ↦ asn ∗ ⌜v = #(clause_SAT m c)⌝ }} )%I.
  Proof.
    iIntros "%Hinv Hl".
    destruct c as [e1 e2 e3].
    rewrite /evaluate_clause.
    wp_pures.
    wp_bind (evaluate_fvar _ _).
    wp_apply (ub_wp_wand with "[Hl]").
    { iApply wp_evaluate_fvar; [eauto|iFrame]. }
    iIntros (s1) "(Hl&%Hs1)".
    destruct (fvar_SAT m e1) as [|] eqn:HeqS1; rewrite Hs1; wp_pures.
    { iModIntro; iFrame; iPureIntro; f_equal. simpl; by rewrite HeqS1. }
    wp_bind (evaluate_fvar _ _).
    wp_apply (ub_wp_wand with "[Hl]").
    { iApply wp_evaluate_fvar; [eauto|iFrame]. }
    iIntros (s2) "(Hl&%Hs2)".
    destruct (fvar_SAT m e2) as [|] eqn:HeqS2; rewrite Hs2; wp_pures.
    { iModIntro; iFrame; iPureIntro; f_equal. simpl; by rewrite HeqS2 orb_true_r. }
    wp_apply (ub_wp_wand with "[Hl]").
    { iApply wp_evaluate_fvar; [eauto|iFrame]. }
    iIntros (s3) "(Hl&%Hs3)".
    destruct (fvar_SAT m e3) as [|] eqn:HeqS3; rewrite Hs3.
    { iFrame; iPureIntro; f_equal. simpl; by rewrite HeqS3 orb_true_r. }
    iFrame; iPureIntro; f_equal.
    by rewrite /= HeqS1 HeqS2 HeqS3 /=.
  Qed.


  (** WALKSAT (simplified version): Find the first UNSAT clause and randomly flip a variable from it *)


  Definition clause_to_index (c : clause) : val :=
    (λ: "i",
       match c with
       | (ClauseV e1 e2 e3) =>
           (if: ("i" = #0)
            then #(fVar_index e1)
            else if: ("i" = #1)
                 then #(fVar_index e2)
                 else #(fVar_index e3))%E
       end)%V.


  Lemma wp_clause_to_index (c: clause) (target : fin 3) E :
    ⊢ (WP (clause_to_index c #target)%E @ E {{ fun i => ⌜ i = #(fVar_index (proj_clause_value c target))⌝ }})%I.
  Proof.
    iStartProof; rewrite /clause_to_index /proj_clause_value /fVar_index.
    destruct c.
    (*
    destruct target. simpl; wp_pures.
    destruct target; simpl; wp_pures; eauto.
    rewrite (bool_decide_false); first (wp_pures; eauto).
    rewrite /not; intros Hk; inversion Hk; lia.
    *)
  Admitted.

  (* selects a variable references in the clause, and flips it *)
  Definition resample_clause (c : clause) : val :=
    (λ: "l",
       let: "asn" := (! "l") in
       let: "n" := clause_to_index c (rand #2) in
       let: "b" := eval_asn "asn" "n" in
       "l" <- (update_asn "asn" "n" (~ "b")))%V.

  Definition εFac : nonnegreal := (nnreal_div (nnreal_nat 3) (nnreal_nat 2)).

  (* amplify using the 1/6 chance that the resampler flips a variable "target" *)
  (* this proof repeats itself, I think I could refactor my lemmas above to make it cleaner.
     in any case, this follows directly by symbolic execution. *)
  Lemma resample_amplify (c : clause) (target : fin 3) (m : list bool) (l: loc) ε (asn : val) E :
    inv_asn m asn ->
    ⊢ (l ↦ asn -∗
       € ε -∗
       WP (resample_clause c #l)%E @ E
         {{ fun _ => ∃ asn' m', (l ↦ asn') ∗ ⌜inv_asn m' asn' ⌝ ∗
                              ((⌜(m' !!! (fVar_index (proj_clause_value c target))) = (negb (m !!! (fVar_index (proj_clause_value c target)))) ⌝) ∨
                               (€ (ε * εFac)%NNR ))}})%I.
  Proof.
    iIntros (Hinv) "Hl Hε".
    Opaque update_asn.
    rewrite /resample_clause.
    wp_pures.
    wp_apply (wp_load with "Hl").
    iIntros "Hl".
    wp_pures.
    wp_bind (rand _)%E.
    wp_apply (wp_couple_rand_adv_comp1 _ _ _ _ ε
                (fun s => if (Fin.eqb s target)
                         then (nnreal_nat 0%nat)%NNR
                         else (ε * (nnreal_div (nnreal_nat 3%nat) (nnreal_nat 2%nat)))%NNR)
              with "Hε").
    { (* (0 + 3/2 + 3/2) / 3 = 1 *)
      admit. }
    iIntros  (i) "Hcr".
    destruct (Fin.eqb i target) eqn:Hi.
    - (* sampler chooses the target index; flips it *)
      wp_bind (clause_to_index c _)%E.
      wp_apply (ub_wp_wand); first iApply (wp_clause_to_index c i).
      iIntros (i') "->".
      wp_pures.
      wp_bind (eval_asn _ _)%E.
      wp_apply (ub_wp_wand with "[]").
      { iApply wp_eval_asn; iPureIntro; last first.
        - rewrite /inv_asn in Hinv. by destruct Hinv.
        - destruct (proj_clause_value c i) as [? ? ?].
          destruct Hinv as [? ?] .
          simpl; lia. }
      iIntros (v) "<-".
      wp_pures.
      wp_bind (update_asn _ _ _).
      wp_apply (ub_wp_wand with "[]").
      { iApply wp_update_asn; iPureIntro; last first.
        - rewrite /inv_asn in Hinv. by destruct Hinv.
        - destruct (proj_clause_value c i) as [? ? ?].
          destruct Hinv as [? ?] .
          simpl; lia. }
      iIntros (v) "%Hinv'".
      wp_pures.
      wp_store.
      iModIntro.
      iExists _, _.
      iFrame.
      iSplitR.
      { iPureIntro; split; [|eapply Hinv'].
        rewrite insert_length.
        by destruct Hinv.  }
      iLeft.
      iPureIntro.
      apply Fin.eqb_eq in Hi.
      replace i with target.
      apply list_lookup_total_insert.
      destruct (proj_clause_value c target) as [? ? ?].
      simpl; destruct Hinv; lia.
    - (* sampler chooses the wrong index, step through and conclude by the amplification  *)
      wp_bind (clause_to_index c _)%E.
      wp_apply (ub_wp_wand); first iApply (wp_clause_to_index c i).
      iIntros (i') "->".
      wp_pures.
      wp_bind (eval_asn _ _)%E.
      wp_apply (ub_wp_wand with "[]").
      { iApply wp_eval_asn; iPureIntro; last first.
        - rewrite /inv_asn in Hinv. by destruct Hinv.
        - destruct (proj_clause_value c i) as [? ? ?].
          destruct Hinv as [? ?] .
          simpl; lia. }
      iIntros (v) "<-".
      wp_pures.
      wp_bind (update_asn _ _ _).
      wp_apply (ub_wp_wand with "[]").
      { iApply wp_update_asn; iPureIntro; last first.
        - rewrite /inv_asn in Hinv. by destruct Hinv.
        - destruct (proj_clause_value c i) as [? ? ?].
          destruct Hinv as [? ?] .
          simpl; lia. }
      iIntros (v) "%Hinv'".
      wp_pures; wp_store.
      iModIntro.
      iExists _, _; iFrame.
      iPureIntro.
      split; last apply Hinv'.
      rewrite insert_length.
      by destruct Hinv.
  Admitted.


  Fixpoint sampler (f : formula) : val :=
    (λ: "asnV",
        match f with
          | [] => #()
          | (c :: cs) =>
              if: (evaluate_clause c) (! "asnV")
                then (sampler cs) "asnV"
                else (resample_clause c) "asnV"
        end)%V.

  Fixpoint checker (f : formula) : val :=
    (λ: "asnV",
       match f with
        | [] => #true
        | (c :: cs) => (evaluate_clause c (! "asnV")) && (checker cs "asnV")
        end).


  (* running the checker *)
  Lemma wp_check l asn m f E :
    (⊢ ⌜ inv_asn m asn ⌝ -∗ l ↦ asn -∗ ((WP ((Val (checker f)) #l) @ E {{ λ v', l ↦ asn ∗ ⌜v' = #(formula_SAT m f)⌝ }})))%I.
  Proof.
    iInduction f as [|c f'] "IH".
    - iIntros "%Hinv Hl".
      rewrite /checker.
      wp_pures.
      iModIntro; iFrame; iPureIntro; f_equal.
    - iIntros "%Hinv Hl".
      wp_pures.
      wp_bind (! _)%E.
      wp_load.
      wp_bind (evaluate_clause _ _)%E.
      wp_apply (ub_wp_wand with "[Hl]").
      { wp_apply wp_evaluate_clause; [|iFrame]. iPureIntro. eapply Hinv.  }
      iIntros (ev) "(Hl&->)".
      destruct (clause_SAT m c) as [|] eqn:Hcsat.
      + wp_pure.
        wp_apply (ub_wp_wand with "[Hl]").
        { iApply "IH"; [eauto|iFrame]. }
        iIntros (v) "(Hl&%Hf')".
        iFrame; iPureIntro.
        rewrite Hf'; f_equal.
        by rewrite {2}/formula_SAT /= Hcsat /formula_SAT.
      + wp_pures.
        iModIntro; iFrame; iPureIntro; f_equal.
        rewrite /formula_SAT /= Hcsat.
        induction f' as [|? ? ?]; simpl; done.
  Qed.


  (* running the sampler when the formula is SAT (equal to the solution or not) does nothing *)
  Lemma wp_sampler_done l asn m f E :
    (⊢ ⌜formula_SAT m f = true ⌝ -∗
       ⌜ inv_asn m asn ⌝ -∗
       l ↦ asn -∗
       (WP ((Val (sampler f)) #l) @ E {{ λ v', l ↦ asn }}))%I.
  Proof.
    iInduction f as [|c f'] "IHf".
    - iIntros "? ? ?".
      rewrite /sampler /=.
      wp_pures.
      iModIntro; iFrame.
    - iIntros "%Hsat %Hinv Hl".
      rewrite {2}/sampler.
      wp_pures.
      wp_bind (! _)%E.
      wp_load.
      wp_pures.
      wp_bind (evaluate_clause _ _)%E.
      wp_apply (ub_wp_wand with "[Hl]").
      { wp_apply wp_evaluate_clause; [|iFrame].
        iPureIntro. eapply Hinv.  }
      iIntros (v) "(Hl&->)".
      rewrite /formula_SAT /= in Hsat.
      assert (Hcsat: (clause_SAT m c && fold_left (λ (acc : bool) (c : clause), acc && clause_SAT m c) f' true) = true).
      { (* commuting problem (fixable, even if maybe manually) *)
        admit. }
      apply andb_prop in Hcsat; destruct Hcsat as [Hcsat Hfsat].
      rewrite Hcsat.
      wp_pures.
      iApply "IHf".
      + iPureIntro. by rewrite /formula_SAT.
      + iPureIntro; done.
      + iFrame.
  Admitted.



  Lemma wp_sampler_amplify l asn m solution f ε E :
    (⊢ ⌜formula_SAT solution f = true ⌝ -∗
       ⌜formula_SAT m f = false ⌝ -∗
       ⌜ inv_asn m asn ⌝ -∗
       l ↦ asn -∗
       € ε -∗
       (WP ((Val (sampler f)) #l) @ E
          {{ λ v', ∃ asn' m', l ↦ asn' ∗ ⌜ inv_asn m' asn' ⌝ ∗
                      (⌜(progress_measure m' solution < progress_measure m solution)%nat ⌝ ∨
                       € (ε * εFac)%NNR) }}))%I.
    Proof.
      iIntros "%Hsol %Hm %Hinv Hl Hε".
      destruct (find_progress _ _ Hm) as [f1 [f2 [c (-> & Hf1 & Hc)]]].
      (* induct over the SAT clauses doing nothing *)
      iInduction f1 as [| c' f1'] "IH"; last first.
      { assert (Hc': clause_SAT m c' = true) by admit. (* uses Hf1*)
        rewrite /sampler.
        wp_pures.
        wp_load.
        wp_bind (evaluate_clause _ _)%E.
        wp_apply (ub_wp_wand with "[Hl]").
        { wp_apply (wp_evaluate_clause with "[] Hl").
          iPureIntro; eauto. }
        iIntros (r) "(Hl&->)".
        rewrite Hc'.
        wp_pure.
        wp_apply ("IH" with "[] [] [] Hl Hε").
        - admit. (* by Hm and Hc'*)
        - admit. (* by Hsol*)
        - admit. (* by Hf1*)
      }
      simpl app.

      (* Now we start with an UNSAT clause, so do the amplification at the resample step *)
      rewrite /sampler.
      wp_pures.
      wp_load.
      wp_bind (evaluate_clause _ _)%E.
      wp_apply (ub_wp_wand with "[Hl]").
      { wp_apply (wp_evaluate_clause with "[] Hl"). iPureIntro; eapply Hinv. }
      iIntros (r) "(Hl&->)".
      rewrite Hc; wp_pures.
      wp_apply (ub_wp_wand with "[Hε Hl]").
      { wp_apply (resample_amplify with "Hl Hε").  eapply Hinv. }

      iIntros (s) "[%asn' [%m' (Hl & %Hasn' & Hs)]]".
      iExists _, _.
      iFrame.
      iSplit; [iPureIntro; eapply Hasn'|].
      iDestruct "Hs" as "[%H|Hε]".

      - (* Flip is lucky and makes progress *)
        iLeft.
        iPureIntro.
        (* the lemma I proved before seems almost usable *)


      (* Lemma flip_makes_progress (m solution : list bool) (v : fVar) :
         (m !!! (fVar_index v) = negb (solution !!! (fVar_index v))) ->
         (progress_measure (<[fVar_index v := negb (m !!! (fVar_index v))]> m ) solution
         < progress_measure m solution)%nat. *)

        admit.

      - iRight; iFrame.
  Admitted.



  (*
  Lemma walksat_sampling_scheme (f : formula) solution (l : loc) E :
    (⊢ ⌜formula_SAT solution f = true ⌝ -∗
       ⌜length solution = N ⌝ -∗
       ⌜(length f > 0)%nat ⌝ -∗
        incremental_sampling_scheme_spec
          (λ: "_", (sampler f) #l)%V
          (λ: "_", (checker f) #l)%V
          (fun n => ∃ asn m,
                      (l ↦ asn ∗
                      ⌜ inv_asn m asn ⌝ ∗
                      ⌜(progress_measure m solution <= n)%nat⌝))
          εFac
          (nnreal_nat 1%nat)
          E)%I.
  Proof.
    iIntros "%Hsolution %Hsl %Hnontrivial".
    rewrite /incremental_sampling_scheme_spec.
    iSplit.
    - iIntros (Φ) "!> [Hcr | [%asn [%m (Hl&%Hinv&%Hp)]]] HΦ".
      + (* € 1 case: spend *)
        iApply (wp_ec_spend with "Hcr"); [|auto].
        simpl; lra.
      + (* Ψ 0 case *)
        apply Nat.le_0_r in Hp.
        apply (progress_complete _) in Hp; [|destruct Hinv; lia].
        simplify_eq.
        (* using Ψ, asn now equals the solution. step the sampler... *)
        wp_pures.
        wp_apply (ub_wp_wand with "[Hl]").
        { wp_apply wp_sampler_done; try by iPureIntro. iFrame. }
        iIntros (v) "Hl".
        iApply "HΦ".
        (* then step the checker... *)
        wp_pures.
        wp_apply (ub_wp_wand with "[Hl]").
        { iApply wp_check; [|iFrame].
          iPureIntro; apply Hinv. }
        iIntros (r) "(Hl&->)"; iPureIntro; do 2 f_equal.
        done.
    - iIntros (ε p Φ) "!> (Hε&[%asn [%m (Hl&%Hinv&%Hp)]]) HΦ".
      wp_pures.
      (* step the sampler differently depending on if it is SAT *)
      destruct (formula_SAT m f) as [|] eqn:Hsat.
      + (* SAT: we can't make progress or amplify, but that is be okay, since we can pass the check *)
        wp_apply (ub_wp_wand with "[Hl]").
        { wp_apply wp_sampler_done; try by iPureIntro. iFrame. }
        iIntros (?) "Hl".
        iApply "HΦ".
        (* go directly to jail, do not pass go, do not collect € εFac *)
        iLeft.
        wp_pures.
        wp_apply (ub_wp_wand with "[Hl]").
        { iApply wp_check; [|iFrame].
          iPureIntro. eapply Hinv. }
        iIntros (?) "(Hr&->)"; iPureIntro.
        do 2 f_equal. done.
      + (* UNSAT *)

        wp_apply (ub_wp_wand with "[Hl Hε]").
        { wp_apply (wp_sampler_amplify with "[] [] [] Hl Hε"); iPureIntro.
          - apply Hsolution.
          - apply Hsat.
          - apply Hinv. }

        iIntros (s) "[%Hasn' [%Hm' (Hl & %Hinv' & [Hp | Hε])]]".
        * (* amkes progress *)
          iApply "HΦ".
          iRight. iLeft.

          (* PROBLEM: Spec needs to let credit decrease in the good cases
             so really, the invariant should connect a lower bound of credit
             and an upper bound on progress
           *)
          admit.

        * iApply "HΦ".
          iRight. iRight.
          iExists _, _.
          iFrame.
          iSplitR; [iPureIntro|].
          { (* something backwards here *) admit.  }
          iSplitL.
          -- iExists _, _.
             iFrame.
             iSplit; iPureIntro; eauto.
          -- wp_pures.
             wp_apply ub_wp_wand.
             (* Also a problem: I lose l ↦ asn' here. I guess I need to use proper invariants instead of Ψ? *)
             { iApply (wp_check with "[]"); admit. }
             iIntros (?) "(? & ->)". iPureIntro; eexists; eauto.
  Abort.
*)


  (*
  Lemma ho_spec_is_incremental (sampler checker : val) (εfactor εfinal : nonnegreal) E :
    ⊢ sampling_scheme_spec sampler checker εfactor εfinal E -∗ incremental_sampling_scheme_spec sampler checker (fun n: nat => ⌜False⌝) εfactor εfinal E.
  Proof.
    iIntros "(#Hamp&#Hspend)".
    rewrite /incremental_sampling_scheme_spec.
    iSplit.
    - iIntros (Φ) "!> [Hcr|?] HΦ"; [|iExFalso; iFrame].
      iSpecialize ("Hspend" $! #()).
      wp_apply (ub_wp_wand with "[Hcr]").
      + iApply ("Hspend" with "Hcr").
        iNext.  (* sus *)
        iIntros (?) "Hr".
        iApply "Hr".
      + iIntros (?).
        (* problem: need to strip a later here *)
        admit.
    - iIntros (ε p) "!>"; iIntros (Φ) "Hcr HΦ".
      iSpecialize ("Hamp" $! ε with "Hcr").
      iApply "Hamp".
      iNext.
      iIntros (v).
      iSpecialize ("HΦ" $! v).
      (* very sus *)
    Abort.
   *)

End higherorder_walkSAT.

  (*

  Definition incremental_sampling_scheme_spec' (sampler checker : val) Ψ εfactor εfinal E : iProp Σ
    := (* 0: we always need to be able to construct some progress measurement *)
       (  (* 1. After some amount of progress, we can ensure the checker will pass *)
          (* 2. We can always spend εfinal to obtain a sample which will surely pass *)
          {{{ € εfinal ∨ Ψ 0%nat }}}
            ((Val sampler) #())%E @ E
          {{{ (v : val), RET v; WP ((Val checker) v) @ E {{ λ v', ⌜v' = #true ⌝ }}}}} ∗
          (* 3. Given any amount of credit and progress, the sampler will either... *)
          (∀ ε p,
            {{{ € ε ∗ Ψ (S p)}}}
              ((Val sampler) #())%E @ E
            {{{ (v : val), RET v;
                (* 3.0 just get lucky and end up done *)
                (WP ((Val checker) v) @ E {{ λ v', ⌜v' = #true⌝ }}) ∨
                (* 3.1: obtain a sample which makes progress without consuming error, or *)
                (€ ε ∗ Ψ p ∗ ((WP ((Val checker) v) @ E {{ λ v', ⌜exists b: bool, v' = #b⌝ }}))) ∨
                (* 3.2: amplifies the error by a factor, possibly losing progress *)
                (∃ ε' p', € ε' ∗ ⌜(ε <= ε' * εfactor)%NNR ⌝ ∗ Ψ p' ∗ (WP ((Val checker) v) @ E {{ λ v', ⌜exists b: bool, v' = #b⌝ }}))}}}))%I.

  Lemma ho_incremental_ubdd_approx_safe (sampler checker : val) Ψ p (εfactor εfinal : nonnegreal) (depth : nat) E :
    (0 < εfactor < 1) ->
    (0 < εfinal < 1) ->
    incremental_sampling_scheme_spec' sampler checker Ψ εfactor εfinal E -∗
    ▷ € (generic_geometric_error εfactor εfinal depth) -∗
    Ψ p -∗
    (WP (ho_ubdd_rejection_sampler sampler checker) @ E {{ fun v => ∃ v', ⌜ v = SOMEV v' ⌝}})%I.
  Proof.
    iIntros ([Hfactor_lb Hfactor_ub] [Hfinal_lb Hfinal_ub]) "(#Haccept & #Hamplify) Hε HΨ".
    do 7 wp_pure.
    (* outermost induction should be on depth, generalized over p, since amplification can lose progress *)
    iInduction depth as [|depth' Hdepth'] "IH" forall (p).
    - (* depth=0, ie we have €εfinal *)
      wp_pures.
      wp_bind (sampler #())%E.
      wp_apply ("Haccept" with "[Hε]").
      { iLeft. iApply (ec_spend_irrel with "Hε"). rewrite /generic_geometric_error /=. lra. }
      iIntros (v) "Hcheck".
      wp_pures.
      wp_bind (checker v)%E.
      wp_apply (ub_wp_wand with "Hcheck").
      iIntros (r) "->".
      wp_pures.
      iModIntro; eauto.
    - (* depth > 0; either make sufficient progress or amplify. *)
      iInduction p as [|p'] "IHp". (* FIXME: this should be strong induction but iInduction isn't happy with that  *)
      + (* p = 0; progress complete *)
        wp_pures; wp_bind (sampler #())%E.
        wp_apply ("Haccept" with "[HΨ]"); [iRight; eauto|].
        iIntros (v) "Hcheck".
        wp_pures.
        wp_bind (checker v)%E.
        wp_apply (ub_wp_wand with "Hcheck").
        iIntros (r) "->".
        wp_pures.
        iModIntro; eauto.
      + (* p > 0, make progress or amplify *)
        wp_pures.
        wp_pures; wp_bind (sampler #())%E.
        wp_apply ("Hamplify" with "[$]").
        iIntros (v) "[Hluck|[(Hε&HΨ&Hcheck)|[%ε'[%p'' (Hε&%Hamp&Hp''&Hcheck)]]]]".
        * (* very lucky sample: we are done *)
          wp_pures.
          wp_apply (ub_wp_wand with "Hluck").
          iIntros (?) "->".
          wp_pures.
          iModIntro; eauto.
        * (* lucky sample: makes progress *)
          wp_pures.
          wp_bind (checker _)%E.
          wp_apply (ub_wp_wand with "Hcheck").
          iIntros (r) "[%b ->]".
          destruct b.
          -- (* lucky day, checker accepts! *)
             wp_pures; iModIntro; eauto.
          -- (* checker rejects (but we keep the progress) *)
             wp_pure. wp_apply ("IHp" with "[$] [$]").
        * (* unlucky guess, progress may get worse but we can amplify *)
          wp_pures.
          wp_bind (checker _)%E.
          wp_apply (ub_wp_wand with "Hcheck").
          iIntros (r) "[%b ->]".
          destruct b.
          -- (* really lucky day! checker accepts on bad sample *)
             wp_pures. iModIntro; eauto.
          -- (* use the amplified credit *)
             wp_pure.
             wp_apply ("IH" with "[Hε] Hp''").
             iApply (ec_spend_le_irrel with "Hε").
             simpl in Hamp.
             rewrite /generic_geometric_error /=.
             rewrite (Rmult_comm εfactor) -Rmult_assoc in Hamp.
             apply (Rmult_le_reg_r εfactor); done.
  Qed.
*)
