(** * Termination with probability 1 of the WalkSAT algorithm *)
From clutch.eris Require Export eris error_rules.
From clutch.eris Require Export eris error_rules adequacy total_adequacy.
From clutch.eris Require Export examples.approximate_samplers.approx_higherorder_incremental.
From Coquelicot Require Import Series.
Require Import Lra.

Set Default Proof Using "Type*".



Section higherorder_walkSAT.
  (** Demonstration of using the higher-order spec for stateful computation (WalkSAT) *)
  Local Open Scope R.
  Context `{!erisGS Σ}.

  Context (N : nat).
  Context (HN : (0 < N)%nat).

  (** Assignments *)

  (* Reflection of Coq- and value-level assignments *)
  Inductive inv_asn' : list bool -> val -> Prop :=
    | inv_emp : inv_asn' [] NONEV
    | inv_cons (b : bool) (m' : list bool) (asn' : val) : (inv_asn' m' asn') -> inv_asn' (b :: m') (SOMEV (#b, asn')).
  Definition inv_asn m asn : Prop := length m = N /\ inv_asn' m asn.


  (* Set up a random assignment of n boolean variables *)
  Definition mk_init_asn': val :=
    (rec: "mk_asn'" "n" :=
       if: ("n" = #0)
       then NONE
       else
         let: "b" := (rand #1 = #1) in
         let: "r" := ("mk_asn'" ("n" - #1)) in
         SOME ("b", "r"))%V.
  Definition mk_init_asn : val := (λ: "_", mk_init_asn' #N).

  (* init_asn' spec *)
  Lemma init_asn'_inv (M: nat) E :
    (⊢ WP (mk_init_asn' #M) @ E [{ fun v' => ∃ m, ⌜ inv_asn' m v' /\ length m = M ⌝}])%I.
  Proof using N HN.
    iInduction M as [|M'] "IH".
    - rewrite /mk_init_asn'; wp_pures.
      iModIntro; iExists []; iPureIntro; split; [constructor | by simpl].
    - rewrite /mk_init_asn'.
      do 3 wp_pure.
      wp_bind (rand _)%E; wp_apply twp_rand; eauto; iIntros (b) "%Hb".
      do 4 wp_pure.
      replace #(S M' - 1)%Z with #M'; [| do 2 f_equal; lia].
      wp_bind (RecV _ _ _ _).
      wp_apply (tgl_wp_wand  with "IH").
      iIntros (asn') "[%m' (%Hm'_inv' & %Hm'_len)]".
      wp_pures.
      iModIntro; iExists ((bool_decide (#b = #1)) :: m').
      iPureIntro; split.
      + by apply inv_cons.
      + rewrite cons_length Hm'_len /=; lia.
  Qed.

  (* Evaluates a value-level assignment *)
  Definition eval_asn : val :=
    (rec: "eval_asn" "asn" "n" :=
       match: "asn" with
          NONE => error
        | SOME "R" => if: ("n" = #0)
                        then (Fst "R")
                        else ("eval_asn" (Snd "R") ("n" - #1))
       end)%V.


  (* eval_asn spec *)
  Definition wp_eval_asn m asn E (n : nat) :
    (⊢ ⌜ (n < (length m))%nat ⌝ -∗ ⌜ inv_asn' m asn ⌝ -∗
       WP (eval_asn asn #n)%E @ E [{ fun v => ⌜#(m !!! n : bool) = v⌝}])%I .
  Proof using N HN.
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
        wp_apply (tgl_wp_wand with "[IH]").
        { iApply "IH".
          iPureIntro.
          rewrite cons_length in Hlen.
          apply (Nat.le_lt_add_lt 1%nat 1%nat); try lia. }
        iIntros (v) "%Hv"; iPureIntro.
        rewrite lookup_total_cons_ne_0; try eauto.
        rewrite -Hv Nat.pred_succ.
        by replace (S n'' - 1)%nat with n'' by lia.
  Qed.


  (* Updates an assignment at a given location *)
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

  (* update_asn spec *)
  Definition wp_update_asn m asn E n (b: bool) :
    (⊢ ⌜(n < length m)%nat ⌝ -∗ ⌜inv_asn' m asn ⌝ -∗
        WP (update_asn asn #n #b)%E @ E [{ fun asn' => ⌜inv_asn' (<[n := b]> m) asn' ⌝}])%I.
  Proof using N HN.
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
        wp_apply (tgl_wp_wand with "[IH]").
        { iApply "IH".
          iPureIntro.
          rewrite cons_length in Hlen.
          apply (Nat.le_lt_add_lt 1%nat 1%nat); try lia.
          rewrite Nat.sub_add; [lia|].
          destruct n'; [|lia].
          rewrite /not in H; exfalso; apply H.
          auto.
        }
        iIntros (v) "%Hv".
        wp_pures.
        iModIntro; iPureIntro.
        replace (n')%nat with (S (n' - 1))%nat; last first.
        { destruct n'; last by lia.
          exfalso; rewrite /not in H; apply H.
          f_equal. }
        simpl.
        by constructor.
  Qed.

  (** 3SAT formulas *)

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
          if (target =? (0%fin : fin 3))%nat
            then e1
            else if (target =? (1%fin : fin 3))%nat
                 then e2
                 else e3
      end.


  (** Coq-level formula evaluation *)

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
    (fun l => fold_left andb l true) $ (fun c => clause_SAT m c) <$> f.


  (** Lemmas about the existence of progress *)
  (* If there exists a solution to the clause, and an assignment is UNSAT, the assignment
     differs from the solution in at least one variable *)
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


  (* Transform a fvar into a value which the resampler can sample against *)
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


  (* Obtains the first UNSAT clause; the resampler will resample inside this clause *)
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
          rewrite /formula_SAT in Hunsat.
          rewrite (fold_symmetric _ andb_assoc) in Hunsat; [|intros; apply andb_comm].
          rewrite fmap_cons /= in Hunsat.
          rewrite /formula_SAT.
          apply andb_false_iff in Hunsat; destruct Hunsat as [H | H]; [exfalso; eauto|].
          by rewrite (fold_symmetric _ andb_assoc); [|intros; apply andb_comm].
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
  Qed.


  (** Progress measurement *)
  (* Hamming distance to some fixed solution *)
  Definition progress_measure (f : formula) (m solution : list bool) : nat :=
      fold_right Nat.add 0%nat
        ((fun p => match p with | (s, t) => if (eqb s t)then 0%nat else 1%nat end) <$> (zip m solution)).

  (* Hamming distance 0 -> assignments are equal *)
  Lemma progress_complete f m solution : (length m = length solution) -> (progress_measure f m solution = 0%nat) -> (m = solution).
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

  Lemma worst_progress_bound f m solution : (length m = length solution) -> (progress_measure f m solution <= length solution)%nat.
  Proof.
    generalize dependent solution.
    induction m as [|m0 ms IH].
    - simpl.
      intros solution H.
      rewrite (nil_length_inv solution); [|done].
      by rewrite /progress_measure /=.
    - simpl.
      intros solution H.
      destruct solution as [|s0 ss].
      {  simpl in H.  discriminate. }
      simpl in H; inversion H.
      rewrite /progress_measure /=.
      replace (S (length ss))%nat with (1 + length ss)%nat; [|by simpl].
      apply Nat.add_le_mono.
      * destruct (eqb _ _); lia.
      * by apply IH.
  Qed.


  (* Flipping a variable which is different to the solution decreases the Hamming distance *)
  Lemma flip_makes_progress f (m solution : list bool) (v : fVar) :
      (length m = length solution) ->
      (fVar_index v < length m)%nat ->
      (m !!! (fVar_index v) = negb (solution !!! (fVar_index v))) ->
      (progress_measure f (<[fVar_index v := negb (m !!! (fVar_index v))]> m ) solution < progress_measure f m solution)%nat.
  Proof.
    intros.
    assert (Hm_d : forall n, (n < length m)%nat -> exists m1 x m2, (m = m1 ++ [x] ++ m2) /\ (length m1 = n)).
    { intros.
      destruct (drop n m) as [| d0 ds] eqn:Hdrop.
      { exfalso.
        assert (HK : length (drop n m) = (length m - n)%nat) by apply drop_length.
        rewrite Hdrop /= in HK.
        lia.
      }
      eexists (take n m), d0, ds.
      split; last (apply take_length_le; lia).
      rewrite -{1}(take_drop n m).
      apply app_inv_head_iff.
      done.
    }
    edestruct  (Hm_d _ H0) as [m1 [x [m2 [-> Hm]]]].
    rewrite -Hm.
    rewrite -Hm in H1.
    rewrite list_lookup_total_middle in H1; [|auto].
    rewrite list_lookup_total_middle; [|auto].
    clear Hm.
    clear H0.
    clear Hm_d.
    generalize dependent solution.
    induction m1 as [|m1' m1's IH].
    - intros.
      rewrite /= /progress_measure.
      destruct solution as [|s0 ss]; [simpl in H; lia|].
      destruct x, s0; simpl; simpl in H1; auto; discriminate.
    - intros.
      rewrite /= /progress_measure.
      destruct solution as [|s0 ss]; [simpl in H; lia|].
      simpl.
      apply Nat.add_lt_mono_l, IH; auto.
  Qed.

  (** Value-level formula evaluation *)

  (* Evaluate a single fVar against a value-level assignment *)
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

  (* evaluate_fvar spec*)
  Lemma wp_evaluate_fvar l asn m v E :
    (⊢ ⌜ inv_asn m asn ⌝ -∗ l ↦ asn -∗
       WP (evaluate_fvar v) asn @ E [{ fun v' => l ↦ asn ∗ ⌜v' = #(fvar_SAT m v)⌝ }] )%I.
  Proof.
    iIntros "%Hinv Hl".
    destruct v as [p v vwf].
    rewrite /evaluate_fvar.
    wp_pures.
    wp_bind (eval_asn _ _)%E.
    wp_apply (tgl_wp_wand with "[]").
    { iApply wp_eval_asn; iPureIntro; last first.
      - rewrite /inv_asn in Hinv. by destruct Hinv.
      - destruct Hinv; lia. }
    iIntros (b) "<-".
    destruct p; wp_pures; iModIntro; eauto.
  Qed.

  (* Evaluate a clause against a value-level assignment *)
  Definition evaluate_clause (c : clause) : val :=
    (λ: "asn",
        match c with
         | ClauseV e1 e2 e3 => ((evaluate_fvar e1 "asn") || (evaluate_fvar e2 "asn") || (evaluate_fvar e3 "asn"))
        end)%V.

  (* evaluate_clause spec *)
  Lemma wp_evaluate_clause l asn m c E :
    (⊢ ⌜ inv_asn m asn ⌝ -∗ l ↦ asn -∗
     WP (evaluate_clause c) asn @ E [{ fun v => l ↦ asn ∗ ⌜v = #(clause_SAT m c)⌝ }])%I.
  Proof.
    iIntros "%Hinv Hl".
    destruct c as [e1 e2 e3].
    rewrite /evaluate_clause.
    wp_pures.
    wp_bind (evaluate_fvar _ _).
    wp_apply (tgl_wp_wand with "[Hl]").
    { iApply wp_evaluate_fvar; [eauto|iFrame]. }
    iIntros (s1) "(Hl&%Hs1)".
    destruct (fvar_SAT m e1) as [|] eqn:HeqS1; rewrite Hs1; wp_pures.
    { iModIntro; iFrame; iPureIntro; f_equal. simpl; by rewrite HeqS1. }
    wp_bind (evaluate_fvar _ _).
    wp_apply (tgl_wp_wand with "[Hl]").
    { iApply wp_evaluate_fvar; [eauto|iFrame]. }
    iIntros (s2) "(Hl&%Hs2)".
    destruct (fvar_SAT m e2) as [|] eqn:HeqS2; rewrite Hs2; wp_pures.
    { iModIntro; iFrame; iPureIntro; f_equal. simpl; by rewrite HeqS2 orb_true_r. }
    wp_apply (tgl_wp_wand with "[Hl]").
    { iApply wp_evaluate_fvar; [eauto|iFrame]. }
    iIntros (s3) "(Hl&%Hs3)".
    destruct (fvar_SAT m e3) as [|] eqn:HeqS3; rewrite Hs3.
    { iFrame; iPureIntro; f_equal. simpl; by rewrite HeqS3 orb_true_r. }
    iFrame; iPureIntro; f_equal.
    by rewrite /= HeqS1 HeqS2 HeqS3 /=.
  Qed.


  (** WALKSAT (simplified version): Find the first UNSAT clause and flip a random variable inside it *)

  (* Helper function: turn a sampled index within a clause (1, 2, 3) into the corresponding fVar *)
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

  (* selects a variable references in the clause, and flips it *)
  Definition resample_clause (c : clause) : val :=
    (λ: "l",
       let: "asn" := (! "l") in
       let: "n" := clause_to_index c (rand #2) in
       let: "b" := eval_asn "asn" "n" in
       "l" <- (update_asn "asn" "n" (~ "b")))%V.


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

  (* spec for helper lemma *)
  Lemma wp_clause_to_index (c: clause) (target : fin 3) E :
    ⊢ (WP (clause_to_index c #target)%E @ E [{ fun i => ⌜ i = #(fVar_index (proj_clause_value c target))⌝ }])%I.
  Proof.
    iStartProof. rewrite /proj_clause_value/clause_to_index /proj_clause_value /fVar_index.
    destruct c.
    destruct target; simpl; wp_pures; eauto.
    destruct target; simpl; wp_pures; eauto.
    rewrite (bool_decide_false); first (wp_pures; eauto).
    rewrite /not; intros Hk; inversion Hk; lia.
  Qed.

  (** Accounting specific to this example *)

  (* We need to keep some amount of credit inside the progress invariant so we always have something to amplify against *)
  Program Definition εInv ε0 : nat -> nonnegreal
    := fun p => εR 2         (* amplifying against samples of (S 2) = 3 *)
                 N         (* bound on number of correct samples we need *)
                 (N - p)   (* worst case progress is N, in which case we need ↯ε0. *)
                           (* best case progress is 0, in which case we need ↯0 *)
                 ε0        (* starting amount of credit given to the amplifier *)
                 _.
  Next Obligation. intros. constructor; try lia. constructor; lia. Qed.

  (* Amount of credit we get whenever the resampler picks wrong *)
  Program Definition εAmplified ε0 : nonnegreal
    := εAmp 2 N ε0 _.
  Next Obligation. intros. constructor; lia. Qed.

  (* Excess credit obtained each amplification *)
  Program Definition εExcess ε0 : posreal
    := Δε ε0 2 N _.
  Next Obligation. intros. constructor; lia. Qed.

  (* Accumulated credit after some number of amplifications *)
  Program Definition εProgress ε0 : nat -> nonnegreal
    := fun i => mknonnegreal (Rmax 0 (1 - i * εExcess ε0))%R _.
  Next Obligation. intros. apply Rmax_l. Qed.

  (* We can start out with some amount of progress for free *)
  (* This value is up (1/εExcess...)*)
  (* Doing this in a super annoying way because I can't find a good way to round numbers
     that works well with the INR/IZR coercions *)
  Lemma initial_progress : ⊢ ∀ ε0, ∃ i, |==> ↯ (εProgress ε0 i).
  Proof.
    iIntros (ε0).
    iExists (Z.to_nat (up _)).
    replace (εProgress _ _) with nnreal_zero; first iApply ec_zero.
    apply nnreal_ext.
    rewrite /εProgress /=.
    rewrite Rmax_left; eauto.
    apply Rle_minus.
    rewrite INR_IZR_INZ Z2Nat.id.
    - erewrite Rinv_l_sym.
      + eapply Rmult_le_compat_r.
        * rewrite -{2}(Rmult_1_r (pos _)) -Rmult_minus_distr_l.
          apply Rmult_le_pos; [apply Rlt_le, cond_pos|].
          apply Rle_0_le_minus, Rlt_le, lt_1_k.
        * eapply Rlt_le, Rgt_lt, archimed.
      + rewrite -{2}(Rmult_1_r (pos _)) -Rmult_minus_distr_l.
        apply Rgt_not_eq, Rlt_gt, Rmult_lt_0_compat; [apply cond_pos|].
        apply Rlt_0_minus, lt_1_k.
    - apply le_IZR.
      apply Rge_le, Rgt_ge.
      eapply Rgt_trans.
      + eapply archimed.
      + apply Rlt_gt, Rinv_0_lt_compat.
        rewrite -{2}(Rmult_1_r (pos _)) -Rmult_minus_distr_l.
        apply Rmult_lt_0_compat; [apply cond_pos|].
        apply Rlt_0_minus, lt_1_k.
  Qed.


  Lemma final_progress ε0 : (1 <= εProgress ε0 0%nat)%R.
  Proof. rewrite /= Rmult_0_l Rminus_0_r. apply Rmax_r. Qed.


  (* Error distribution for the resampling step *)
  Program Definition εDistr_resampler ε0 i (Hi : (S i <= N)%nat)
    := (fun v: fin 3 => εDistr 2 N i ε0 v _).
  Next Obligation. intros. do 2 (constructor; try lia). Qed.



  Lemma resample_amplify (c : clause) (target : fin 3) (m : list bool) (l: loc) ε0 p (Hp : ((S p) <= length m)%nat) (asn : val) E :
    inv_asn m asn ->
    ⊢ (l ↦ asn -∗
       ↯ (εInv ε0 (S p)) -∗
       WP (resample_clause c #l)%E @ E
         [{ fun _ =>
              ∃ asn' m', (l ↦ asn') ∗
                         ⌜inv_asn m' asn' ⌝ ∗
                         ( (* Flips the target variable and loses some credit, or... *)
                           ( ↯ (εInv ε0 p) ∗
                            ⌜m' = (<[(fVar_index (proj_clause_value c target)) := negb (m !!! (fVar_index (proj_clause_value c target)))]> m)⌝) ∨
                            (* ...obtains the amplified credit *)
                            (↯ (εAmplified ε0)))}])%I.
  Proof.
    iIntros (Hinv) "Hl Hε".
    Opaque update_asn.
    rewrite /resample_clause.
    wp_pures.
    wp_apply (twp_load with "Hl").
    iIntros "Hl".
    wp_pures.
    wp_bind (rand _)%E.
    replace (length m) with N in Hp; [|by destruct Hinv].
    wp_apply (twp_couple_rand_adv_comp1 _ _ _ _ (εDistr_resampler _ _ _ target) with "Hε").
    {
      rewrite εDistr_mean.
      rewrite /εInv.
      replace (fRwf_dec_i _ _ _ _) with (εInv_obligation_1 (S p)) by apply fRwf_ext.
      eauto. }
    iIntros  (i) "Hcr".
    destruct (Fin.eqb i target) eqn:Hi.

    - (* sampler chooses the target index and flips it *)
      wp_bind (clause_to_index c _)%E.
      wp_apply (tgl_wp_wand); first iApply (wp_clause_to_index c i).
      iIntros (i') "->".
      wp_pures.
      wp_bind (eval_asn _ _)%E.
      wp_apply (tgl_wp_wand with "[]").
      { iApply wp_eval_asn; iPureIntro; last first.
        - rewrite /inv_asn in Hinv. by destruct Hinv.
        - destruct (proj_clause_value c i) as [? ? ?].
          destruct Hinv as [? ?] .
          simpl; lia. }
      iIntros (v) "<-".
      wp_pures.
      wp_bind (update_asn _ _ _).
      wp_apply (tgl_wp_wand with "[]").
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
      iSplitL "Hcr".
      { apply Fin.eqb_eq in Hi.
        rewrite -Hi.
        rewrite /εDistr_resampler /εDistr /εInv.
        rewrite bool_decide_true; eauto.
        erewrite εR_ext.
        iApply (ec_spend_irrel with "Hcr").
        f_equal.
        (* weird unification thing I guess *)
        assert (Her : forall a b c d e f g , (a = b) -> εR c d a e f = εR c d b e g).
        { intros. simplify_eq. apply εR_ext. }
        eapply Her.
        lia.
      }
      iPureIntro.
      apply Fin.eqb_eq in Hi.
      simplify_eq.
      done.
    - (* sampler chooses the wrong index, step through and conclude by the amplification  *)
      wp_bind (clause_to_index c _)%E.
      wp_apply (tgl_wp_wand); first iApply (wp_clause_to_index c i).
      iIntros (i') "->".
      wp_pures.
      wp_bind (eval_asn _ _)%E.
      wp_apply (tgl_wp_wand with "[]").
      { iApply wp_eval_asn; iPureIntro; last first.
        - rewrite /inv_asn in Hinv. by destruct Hinv.
        - destruct (proj_clause_value c i) as [? ? ?].
          destruct Hinv as [? ?] .
          simpl; lia. }
      iIntros (v) "<-".
      wp_pures.
      wp_bind (update_asn _ _ _).
      wp_apply (tgl_wp_wand with "[]").
      { iApply wp_update_asn; iPureIntro; last first.
        - rewrite /inv_asn in Hinv. by destruct Hinv.
        - destruct (proj_clause_value c i) as [? ? ?].
          destruct Hinv as [? ?] .
          simpl; lia. }
      iIntros (v) "%Hinv'".
      wp_pures; wp_store.
      iModIntro.
      iExists _, _; iFrame.
      { assert (i ≠ target)%fin.
        { rewrite /not.
          intros.
          simplify_eq.
          replace (Fin.eqb target target) with true in Hi; [discriminate|].
          symmetry. by apply Fin.eqb_eq. }
        rewrite /εDistr_resampler /εDistr.
        rewrite bool_decide_false; eauto.
        iSplitR.
        { iPureIntro. split; last eapply Hinv'. rewrite insert_length. by destruct Hinv. }
        iRight.
        iApply (ec_spend_irrel with "Hcr").
        rewrite /εAmplified.
        f_equal.
      }
    Unshelve.
    { lia. }
    { constructor; last lia. constructor; lia. }
  Qed.


  (* running the checker *)
  Lemma wp_check l asn m f E :
    (⊢ ⌜ inv_asn m asn ⌝ -∗ l ↦ asn -∗
     ((WP ((Val (checker f)) #l) @ E [{ λ v', l ↦ asn ∗ ⌜v' = #(formula_SAT m f)⌝ }])))%I.
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
      wp_apply (tgl_wp_wand with "[Hl]").
      { wp_apply wp_evaluate_clause; [|iFrame]. iPureIntro. eapply Hinv.  }
      iIntros (ev) "(Hl&->)".
      destruct (clause_SAT m c) as [|] eqn:Hcsat.
      + wp_pure.
        wp_apply (tgl_wp_wand with "[Hl]").
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
       (WP ((Val (sampler f)) #l) @ E [{ λ v', l ↦ asn }]))%I.
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
      wp_apply (tgl_wp_wand with "[Hl]").
      { wp_apply wp_evaluate_clause; [|iFrame].
        iPureIntro. eapply Hinv.  }
      iIntros (v) "(Hl&->)".
      rewrite /formula_SAT in Hsat.
      rewrite (fold_symmetric _ andb_assoc) in Hsat; [|intros; apply andb_comm].
      rewrite fmap_cons /= in Hsat.
      apply andb_prop in Hsat; destruct Hsat as [Hcsat Hfsat].
      rewrite Hcsat.
      wp_pures.
      iApply "IHf".
      + iPureIntro.
        rewrite /formula_SAT.
        by rewrite (fold_symmetric _ andb_assoc); [|intros; apply andb_comm].
      + iPureIntro; done.
      + iFrame.
  Qed.

  (* Running the sampler when we have work to do *)
  Lemma wp_sampler_amplify l asn m solution f ε p E :
    (⊢ ⌜(S p <= N)%nat⌝ -∗
       ⌜length solution = N ⌝ -∗
       ⌜formula_SAT solution f = true ⌝ -∗
       ⌜formula_SAT m f = false ⌝ -∗
       ⌜ inv_asn m asn ⌝ -∗
       l ↦ asn -∗
       ↯ (εInv ε (S p)) -∗
       (WP ((Val (sampler f)) #l) @ E
          [{ λ v', ∃ asn' m', l ↦ asn' ∗ ⌜ inv_asn m' asn' ⌝ ∗
                      ((⌜(progress_measure f m' solution < progress_measure f m solution)%nat ⌝ ∗ ↯(εInv ε p)) ∨
                       (↯ (εAmplified ε)) )}]))%I.
    Proof.
      iIntros "%Hp %Hsol_len %Hsol %Hm %Hinv Hl Hε".
      destruct (find_progress _ _ Hm) as [f1 [f2 [c (-> & Hf1 & Hc)]]].
      (* induct over the SAT clauses doing nothing *)
      iInduction f1 as [| c' f1'] "IH"; last first.
      { assert (Hc': clause_SAT m c' = true).
        { by apply Forall_inv in Hf1. }
        rewrite /sampler.
        wp_pures.
        wp_load.
        wp_bind (evaluate_clause _ _)%E.
        wp_apply (tgl_wp_wand with "[Hl]").
        { wp_apply (wp_evaluate_clause with "[] Hl").
          iPureIntro; eauto. }
        iIntros (r) "(Hl&->)".
        rewrite Hc'.
        wp_pure.
        replace (f1' ++ [c] ++ f2) with (f1' ++ c :: f2) by auto.
        wp_apply (tgl_wp_wand with "[Hl Hε]").
        { iApply ("IH" with "[] [] [] Hl Hε").
          - iPureIntro. rewrite -Hm /formula_SAT /= /fmap. f_equal. auto.
          - iPureIntro. rewrite -Hsol /formula_SAT /= /fmap. f_equal.
            replace ((c' :: f1') ++ [c] ++ f2) with (c' :: (f1' ++ c :: f2)) in Hsol; [|by simpl].
            rewrite /formula_SAT in Hsol.
            rewrite (fold_symmetric _ andb_assoc) in Hsol; [|intros; apply andb_comm].
            rewrite /= in Hsol.
            apply andb_prop in Hsol.
            by destruct Hsol.
          - iPureIntro. by apply Forall_inv_tail in Hf1.
        }
        iIntros (v) "H". iFrame.
      }
      simpl app.

      (* Now we start with an UNSAT clause, so do the amplification at the resample step *)
      rewrite /sampler.
      wp_pures.
      wp_load.
      wp_bind (evaluate_clause _ _)%E.
      wp_apply (tgl_wp_wand with "[Hl]").
      { wp_apply (wp_evaluate_clause with "[] Hl"). iPureIntro; eapply Hinv. }
      iIntros (r) "(Hl&->)".
      rewrite Hc; wp_pures.
      (* let's explicitly find the index we're resampling against using Hm and Hsol *)
      rewrite /= /formula_SAT fmap_cons in Hm, Hsol.
      rewrite /fmap in Hm.
      rewrite (fold_symmetric _ andb_assoc) in Hm; [|intros; apply andb_comm]; simpl in Hm.
      rewrite (fold_symmetric _ andb_assoc) in Hsol; [|intros; apply andb_comm]; simpl in Hsol.
      apply andb_prop in Hsol; destruct Hsol as [Hc_solution Hf2_solution].
      destruct (progress_is_possible_clause _ _ _ Hc_solution Hc) as [targetFV [HtargetClause HtargetFV]].
      destruct (reflect_progress_to_target targetFV _ HtargetClause) as [target Htarget].
      wp_apply (tgl_wp_wand with "[Hε Hl]").
      { wp_apply ((resample_amplify _ target) with "Hl Hε"); last first.
        - eapply Hinv.
        - destruct Hinv; lia. }
      iIntros (s) "[%asn' [%m' (Hl & %Hasn' & Hs)]]".
      iExists _, _.
      iFrame.
      iSplit; [iPureIntro; eapply Hasn'|].
      iDestruct "Hs" as "[[Hε %H]|Hε]".
      - (* Flip is lucky and makes progress *)
        iLeft; iFrame.
        iPureIntro.
        rewrite H.
        apply flip_makes_progress.
        + destruct (proj_clause_value c target).
          destruct Hinv.
          simpl.
          destruct Hasn'.
          lia.
        + simplify_eq.
          destruct (proj_clause_value c target).
          destruct Hasn'.
          rewrite /= insert_length in H.
          simpl.
          lia.
        + simplify_eq.
          done.
      - iRight; iFrame.
  Qed.

  Definition iProgress ε (l : loc) solution f : nat -> iProp Σ :=
          (fun n => ∃ asn m,
                      (l ↦ asn ∗
                       ↯ (εInv ε n) ∗
                      ⌜ inv_asn m asn ⌝ ∗
                      ⌜(progress_measure f m solution <= n)%nat⌝))%I.



  (* FIXME: move or delete *)
  Lemma len_zip_eq `{T} : forall (A B : list T),  length A = length B -> length (zip A B) = length A.
  Proof.
    induction A, B.
    - intros; simpl; done.
    - intros H1; simpl in H1. discriminate.
    - intros H1; simpl in H1. discriminate.
    - intros; simpl. f_equal. apply IHA. simpl in H0. by inversion H0.
  Qed.


  Lemma walksat_sampling_scheme f solution ε (l : loc) HiL E :
    (⊢ (* ⌜forall w : nat, (w < HiL)%nat -> (0 <= 1 - w * εExcess ε)%R ⌝ -∗ (* FIXME: Define HiL in terms of ε *) *)
       ⌜formula_SAT solution f = true ⌝ -∗
       ⌜length solution = N ⌝ -∗
       ⌜(length f > 0)%nat ⌝ -∗
        incr_sampling_scheme_spec
          (λ: "_", (sampler f) #l)%V
          (λ: "_", (checker f) #l)%V
          (iProgress ε l solution f)
          (εProgress ε)
          N
          HiL
          E
          (fun _ => ∃ a asn, l ↦ asn ∗ ⌜inv_asn a asn ⌝ ∗ ⌜formula_SAT a f ⌝ ))%I.
  Proof.
    iIntros "%Hsolution %Hsl %Hnontrivial".
    rewrite /incr_sampling_scheme_spec.
    iSplit.
    - iIntros "[Hcr | [%asn [%m (Hl & Hcr & %Hinv & %Hp)]]]".
      + (* ↯ 1 case: spend *)
        iApply (twp_ec_spend with "Hcr"); [|auto].
        apply final_progress.
      + (* Ψ 0 case *)
        apply Nat.le_0_r in Hp.
        apply (progress_complete _) in Hp; [|destruct Hinv; lia].
        simplify_eq.
        (* using Ψ, asn now equals the solution. step the sampler... *)
        wp_pures.
        wp_apply (tgl_wp_wand with "[Hl]").
        { wp_apply wp_sampler_done; iFrame; iPureIntro; eauto. }
        iIntros (v) "Hl".
        (* then step the checker... *)
        wp_pures.
        wp_apply (tgl_wp_wand with "[Hl]").
        { iApply wp_check; [|iFrame].
          iPureIntro; apply Hinv. }
        iIntros (r) "(Hl&->)".
        iSplitR. { iPureIntro. do 2 f_equal. done. }
        iExists _, _.
        iFrame. eauto.
    - iIntros (i p) "!> (%Hp_bound & %Hi_bound & Hε & [%asn [%m (Hl & Hcr & %Hinv & %Hp)]])".
      wp_pures.
      (* step the sampler differently depending on if it is SAT or not *)
      destruct (formula_SAT m f) as [|] eqn:Hsat.
      + (* SAT: we can't make progress or amplify, but that is be okay, since we can pass the check *)
        wp_apply (tgl_wp_wand with "[Hl]").
        { wp_apply wp_sampler_done; try by iPureIntro. iFrame. }
        iIntros (?) "Hl".
        iLeft.
        wp_pures.
        iApply (tgl_wp_wand with "[Hε Hcr Hl]").
        { iApply wp_check; iFrame. iPureIntro. eapply Hinv. }

        iIntros (?) "[? ->]".
        iSplitR. { iPureIntro. do 2 f_equal. done. }
        iExists _, _.
        iFrame. eauto.
      + (* UNSAT *)
        (* Step to the resampling step, and amplify *)
        rewrite /sampler.
        wp_pures.
        wp_apply (tgl_wp_wand with "[Hl Hcr]").
        { wp_apply (wp_sampler_amplify with "[] [] [] [] [] Hl [Hcr]"); last iFrame; try eauto. }
        iIntros (s) "[%asn' [%m' (Hl & %Hinv' & [(%Hp' & A)|Hamp])]]".
        * (* makes progress *)
          iRight; iLeft.
          iFrame "Hε".
          wp_pures.
          iApply (tgl_wp_wand with "[Hl]").
          { iApply wp_check; iFrame. iPureIntro. eauto. }
          iIntros (?) "(Hl & ->)".
          destruct (formula_SAT m' f) as [|] eqn:Hsat'.
          { iRight. iSplitR; [eauto|].
            iExists _, _. iFrame.
            iSplit; iPureIntro; eauto. }
          { iLeft.
            iSplitR; [eauto|].
            iExists _, _.
            iFrame. iSplit; eauto.
            iPureIntro.
            apply Nat.lt_succ_r.
            eapply Nat.lt_le_trans; last eapply Hp.
            done.
          }
        * (* amplifies *)
          iRight; iRight.
          (* Revert back to iProgress N *)
          iExists N.
          iSplitR; eauto.
          (* Transfer the amplfied credits between the invariants *)
          iAssert (↯ (εInv ε N) ∗ ↯ (pos_to_nn (εExcess ε)) )%I with "[Hamp]" as "[Hinv Hexcess]".
          { iApply ec_split.
            iApply (ec_spend_le_irrel with "Hamp").
            apply εAmp_excess. }
          iAssert (↯ (εProgress ε i)) with "[Hε Hexcess]" as "Hε".
          { iAssert (↯ (εProgress ε (S i) + pos_to_nn (εExcess ε))%NNR) with "[Hε Hexcess]" as "Hε".
            { iApply ec_split; iFrame. }
            iApply ec_spend_le_irrel; [|iFrame].
            Opaque INR.
            rewrite /εProgress /=.
            rewrite {1}/Rmax.
            rewrite S_INR.
            remember (Rle_dec 0 (1 - i * (ε * k 2 N εExcess_obligation_1 - ε))) as D.
            destruct D.
            - rewrite /Rmax.
              remember (Rle_dec 0 (1 - (i + 1) * (ε * k 2 N εExcess_obligation_1 - ε))) as D2; destruct D2; lra.
            - rewrite -{1}(Rplus_0_r 0%R).
              apply Rplus_le_compat; [apply Rmax_l|].
              apply Rle_0_le_minus.
              rewrite -{1}(Rmult_1_r (pos ε)).
              apply Rlt_le.
              apply Rmult_lt_compat_l; [apply cond_pos| apply lt_1_k].
          }
          iFrame "Hε".
          wp_pures.
          wp_apply (tgl_wp_wand with "[Hl]").
          { iApply wp_check; [|iFrame]. iPureIntro; eauto. }
          iIntros (?) "[? ->]".
          destruct (formula_SAT m' f) as [|] eqn:Hast'.
          { iRight. iSplitR; [eauto|]. iFrame. eauto. }
          { iLeft.
            iSplitR; [eauto|].
            iExists _, _.
            iFrame. iSplit; eauto.
            iPureIntro.
            rewrite -Hsl.
            apply worst_progress_bound.
            destruct Hinv'.
            lia.
          }
    Qed.


  Definition WalkSAT f : expr :=
    (let: "a" := mk_init_asn #() in
     let: "l" := ref "a" in
     let: "_" := (gen_rejection_sampler (λ: "_", (sampler f) "l") (λ: "_", (checker f) "l")) in
     "l")%E.

  Lemma initial_credit (ε : nonnegreal) Hpos : ⊢ ↯ ε -∗ ↯ (εInv (mkposreal (nonneg ε) Hpos) N).
  Proof.
    iIntros.
    rewrite /εInv.
    iApply ec_spend_irrel; last iFrame.
    rewrite /= fR_closed_2 /=.
    rewrite Nat.sub_diag pow_O Rminus_diag Rdiv_0_l.
    lra.
  Qed.


  Lemma walksat_spec_fpos f solution E (ε: nonnegreal) :
    ⊢ (⌜formula_SAT solution f = true ⌝ -∗
       ⌜length solution = N ⌝ -∗
       ⌜(length f > 0)%nat ⌝ -∗
       ⌜(0 < ε)%R⌝ -∗
       ↯ ε -∗
      WP (WalkSAT f) @ E [{ fun v => ∃ (l : loc) a asn , ⌜v = #l ⌝ ∗ (l ↦ asn) ∗ ⌜inv_asn a asn ⌝ ∗ ⌜formula_SAT a f ⌝ }])%I.
  Proof.
    iIntros "%HF %Hlens %Hlenf %Hε Hcr".
    rewrite /WalkSAT /mk_init_asn.
    wp_pures.
    wp_bind (mk_init_asn' #N).
    wp_apply (tgl_wp_wand with "[]"); first wp_apply (init_asn'_inv N E).
    iIntros (v) "[%m %Hinv]".
    destruct Hinv as [Hinv Hmn].
    do 2 wp_pure.
    wp_bind (Alloc _).
    wp_apply twp_alloc; [done|].
    iIntros (l) "Hl".
    wp_pure.
    wp_pure.
    wp_bind (_ (Rec BAnon "_" (checker _ _)))%E.
    wp_apply (tgl_wp_wand with "[Hcr Hl]").
    { wp_pure.
      wp_pure.
      pose e1 := (1 / (εExcess (mkposreal (nonneg ε) Hε))).
      assert (He1 : (0 <= e1)%R).
      { rewrite /e1.
        eapply Rlt_le.
        apply Rdiv_lt_0_compat; first lra.
        rewrite /εExcess /=.
        apply -> Rcomplements.Rminus_lt_0.
        rewrite -{1}(Rmult_1_r (nonneg ε)).
        simpl in Hε.
        apply Rmult_lt_compat_l; [done|].
        apply lt_1_k.
      }
      edestruct (Rcomplements.nfloor_ex e1 He1) as [Le [HLe_lo Hle_hi]].
      assert (Hpos_exc: ((ε * k 2 N εExcess_obligation_1 - ε) > 0)%R).
      { simpl in *.
        apply Rlt_gt, Rlt_0_minus.
        rewrite /= -{1}(Rmult_1_r (nonneg ε)).
        apply Rmult_lt_compat_l; [done| apply lt_1_k].
      }
      iMod ec_zero as "He_init".
      iApply (ho_incremental_ubdd_approx_safe _ _ _ _ _ _ _ (Le + 2) with "[Hcr Hl He_init]").
      iSplit; [|iSplit; [|iSplitR; [|iSplitR "Hcr Hl"]]].
      3: { iApply walksat_sampling_scheme; eauto. }
      4: {
        rewrite /iProgress.
        iExists _, _.
        iFrame.
        iSplitL. { iApply initial_credit. iApply ec_spend_irrel; [eauto|iFrame]. }
        iSplit; iPureIntro.
        { rewrite /inv_asn; eauto. }
        { rewrite -Hlens. apply worst_progress_bound. lia. }
      }
      1: iPureIntro; lia.
      2: { iApply ec_spend_irrel; last iFrame.
           simpl; symmetry; apply Rmax_left.
           apply Rle_minus.
           rewrite (Rinv_l_sym (ε * k 2 N εExcess_obligation_1 - ε)); last lra.
           eapply Rmult_le_compat_r.
           { apply Rlt_le, Rgt_lt. done. }
           simpl in *.
           eapply Rle_trans; last first.
           { eapply Rlt_le.
             rewrite -S_INR in Hle_hi.
             eapply Hle_hi. }
           clear.
           rewrite /e1.
           simpl.
           lra.
      }
      1: { iPureIntro. lia. }
    }
    iIntros (r) "[% [% (? & % & %)]]".
    wp_pures.
    iModIntro.
    iExists _, _, _.
    iFrame.
    iPureIntro; eauto.

    Unshelve.
    - done.
  Qed.

  (* Handles f = [] separately *)
  Lemma walksat_spec f solution E (ε: nonnegreal) :
    ⊢ (⌜formula_SAT solution f = true ⌝ -∗
       ⌜length solution = N ⌝ -∗
       ⌜(0 < ε)%R⌝ -∗
       ↯ ε -∗
      WP (WalkSAT f) @ E [{ fun v => ∃ (l : loc) a asn , ⌜v = #l ⌝ ∗ (l ↦ asn) ∗ ⌜inv_asn a asn ⌝ ∗ ⌜formula_SAT a f ⌝ }])%I.
  Proof.
    iIntros "% % % ?".
    destruct (length f) as [|] eqn:Hf; last first.
    - iApply walksat_spec_fpos; eauto. iPureIntro; lia.
    - rewrite (nil_length_inv f); [|eauto].
      rewrite /WalkSAT /mk_init_asn.
      wp_pures.
      wp_bind (mk_init_asn' #N).
      wp_apply (tgl_wp_wand with "[]"); first wp_apply (init_asn'_inv N E).
      iIntros (v) "[%m [% %]]".
      wp_pures.
      wp_bind (Alloc _).
      wp_apply twp_alloc; [done|].
      iIntros (l) "Hl".
      wp_pures.
      iModIntro.
      iExists _, _, _.
      iFrame.
      iPureIntro.
      rewrite /inv_asn.
      split; [|split]; eauto.
  Qed.


End higherorder_walkSAT.

Lemma walksat_termination_limit Σ `{erisGpreS Σ} (N : nat) (HN : (0 < N)%nat) (σ : state) (f : formula N) (solution : list bool) :
  (formula_SAT N solution f = true) ->
  length solution = N ->
  (SeriesC (lim_exec (WalkSAT N f, σ)) = 1)%R.
Proof.
  intros.
  destruct (pmf_SeriesC (lim_exec (WalkSAT N f, σ))); last done.
  assert (HR : (1 - nnreal_zero <= SeriesC (lim_exec (WalkSAT N f, σ)))%R).
  { eapply (twp_mass_lim_exec_limit _ _ _ _ (fun _ => True)).
    intros.
    iStartProof.
    iIntros "Hcr".
    wp_apply (tgl_wp_wand with "[Hcr]").
    { iApply walksat_spec; eauto. }
    iIntros (?) "?"; done. }
  simpl in *.
  rewrite Rminus_0_r in HR.
  lra.
Qed.


Lemma walksat_limit Σ `{erisGpreS Σ} (N : nat) (HN : (0 < N)%nat) (σ : state) (f : formula N) (solution : list bool) :
  (formula_SAT N solution f = true) ->
  length solution = N ->
  tgl (lim_exec (WalkSAT N f, σ))
    (fun _ => True) (* Best we can do is prove it terminates? *)
    nnreal_zero.
Proof.
  intros.
  eapply twp_tgl_limit; first eapply H.
  intros.
  iStartProof.
  iIntros "Hcr".
  wp_apply (tgl_wp_wand with "[Hcr]").
  { iApply walksat_spec; eauto. }
  iIntros (v) "HR".
  (* HR is unused... is there any proposition more interesting that ⊤ we *)
  done.
Qed.
