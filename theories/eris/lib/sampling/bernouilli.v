From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils.
Local Open Scope R.

Local Ltac done ::= lia || lra || nra || real_solver || tactics.done || auto.
Ltac add_hint t := let n := fresh "hint" in have n := t.


Section Lemmas.

  Lemma foldr_plus_app (l1 l2 : list R) (acc : R) :
    foldr Rplus acc (l1 ++ l2) = foldr Rplus 0 l1 + foldr Rplus acc l2.
  Proof.
    elim: l1 =>> //=.
  Qed.


  Lemma fmap_prop {A B : Type} (l : list A) (f : A -> B) (P1 : A -> Prop) (P2 : B -> Prop) :
    (∀ a, P1 a -> P2 (f a)) ->
    (∀ a, a ∈ l -> P1 a) ->
    ∀ b, b ∈ (f <$> l) -> P2 b.
  Proof.
    move=> HPs.
    elim: l.
    - move=> _ b /= HinNil.
      by apply not_elem_of_nil in HinNil.
    - move=> a l IH Hforall /= b Hin.
      rewrite elem_of_cons in Hin.
      case: Hin.
      + move=> ->.
        apply HPs, Hforall, elem_of_list_here.
      + move=> Hin.
        apply IH => //.
        move=> a' Ha'.
        by apply Hforall, elem_of_list_further.
  Qed.

  Lemma forall_list_eq {A : Type} (l : list A) (a : A) :
    (∀ e, e ∈ l -> e = a) ->
    l = repeat a (length l).
  Proof.
    add_hint @elem_of_list_here.
    add_hint @elem_of_list_further.
    elim: l => //=.
    move=> e l IH Hl.
    rewrite (Hl e) // -IH //.
  Qed.

  Lemma map_seq_if_lt {A : Type} (e1 e2 : A) (N : nat):
    (λ x, if bool_decide (x < N)%nat then e1 else e2) <$> seq 0 N = repeat e1 N.
  Proof.
    set f := (λ x : nat, if bool_decide (x < N)%nat then e1 else e2).
    assert (Heq: ∀ e, e ∈ f <$> seq 0 N -> e = e1). {
      apply (fmap_prop _ f (λ n, n < N)%nat).
      - move=> a Ha /=.
        rewrite /f bool_decide_eq_true_2 //.
      - move=> a Ha.
        by apply elem_of_seq in Ha as [_ Ha].
    }
    replace N with (length (f <$> seq 0 N)) at 2 by rewrite fmap_length seq_length //.
    exact: forall_list_eq Heq.
  Qed.

  Lemma map_seq_if_ge {A : Type} (e1 e2 : A) (N L : nat):
    (λ x, if bool_decide (x < N)%nat then e1 else e2) <$> seq N L = repeat e2 L.
  Proof.
    set f := (λ x : nat, if bool_decide (x < N)%nat then e1 else e2).
    assert (Heq: ∀ e, e ∈ f <$> seq N L -> e = e2). {
      apply (fmap_prop _ f (λ n, n >= N)%nat) => a Ha.
      - rewrite /f bool_decide_eq_false_2 //.
      - by apply elem_of_seq in Ha as [].
    }
    replace L with (length (f <$> seq N L)) at 2 by rewrite fmap_length seq_length //.
    exact: forall_list_eq Heq.
  Qed.


  Lemma foldr_plus_repeat (ε : R) (L : nat) :
    foldr Rplus 0 (repeat ε L) = ε * L.
  Proof.
    elim: L =>> //.
    rewrite S_INR //=.
  Qed.

  Lemma SeriesC_case (N M : nat) (ε1 ε2 : R) :
    (N <= S M)%nat ->
    SeriesC (
      λ x : fin (S M), 
      if bool_decide (fin_to_nat x < N)%nat
      then ε2
      else ε1
    ) = (ε1 * (S M - N) + ε2 * N)%R.
  Proof.
    move=> HNleM.
    rewrite SeriesC_finite_foldr -foldr_fmap.
    transitivity (
      foldr Rplus 0
      ((λ x : nat, if bool_decide (x < N)%nat then ε2 else ε1) ∘ fin_to_nat <$> enum (fin (S M)))
    ).
    { reflexivity. }
    rewrite list_fmap_compose fin.enum_fin_seq.
    assert (seq 0 (S M) = seq 0 N ++ seq N (S M - N)) as ->. 
    { replace (S M)%nat with (N + (S M - N))%nat at 1 by lia.
      apply seq_app. }
    rewrite fmap_app foldr_plus_app Rplus_comm.
    rewrite map_seq_if_ge map_seq_if_lt.
    rewrite !foldr_plus_repeat minus_INR //.
  Qed.
End Lemmas.


Section Bernoulli.
  Context `{!erisGS Σ}.
  Program Definition bernoulli_distr (p : R) (p_pos : 0 <= p <= 1) : distr (fin 2) := {|
    pmf := λ x, if bool_decide (x = 1)%fin then p else (1 - p)%R
  |}.
  Next Obligation.
    move=> p Hp a /=.
    case_bool_decide=> //.
  Qed.
  Next Obligation.
    move=> N M.
    apply ex_seriesC_finite.
  Qed.
  Next Obligation.
    move=> p Hp /=.
    rewrite SeriesC_finite_foldr //=.
  Qed.
  


  Definition bernoulli : val := 
    λ: "N" "M",
      let: "x" := rand "M" in 
      if: "x" < "N" then #1 else #0.


  Lemma twp_bernoulli_scale (N M : nat) (ε ε1 ε2 : R) :
  (N <= S M)%nat ->
  0 <= ε1 ->
  0 <= ε2 ->
  ((ε1 * (1 - (N / S M))) + (ε2 * (N/S M)) = ε)%R ->
  [[{↯ ε}]]
    bernoulli #N #M
  [[{
      (k : nat), RET #k; 
      (⌜k = 0%nat⌝ ∗ ↯ ε1) ∨
      (⌜k = 1%nat⌝ ∗ ↯ ε2)
  }]].
  Proof.
    set p := (N / S M)%R.
    iIntros "%HNleM %ε1_pos %ε2_pos %Heq %Φ Herr HΦ".
    rewrite /bernoulli.
    wp_pures.
    iPoseProof (ec_valid with "Herr") as "%Hε".
    set ε' := {|nonneg := ε; cond_nonneg := proj1 Hε |}.
    set ε1' := {|nonneg := ε1; cond_nonneg := ε1_pos |}.
    set ε2' := {|nonneg := ε2; cond_nonneg := ε2_pos |}.
    set f :=
      λ (n : fin (S M)), 
        if bool_decide (fin_to_nat n < N)%nat then ε2' else ε1' 
    .
    wp_apply (twp_couple_rand_adv_comp1 _ _ _ ε' f with "Herr") as "%x Herr".
    { unfold f. move=> n.
      by case_bool_decide. }
    { unfold f. rewrite SeriesC_scal_l. rewrite Rmult_comm.
      simpl_expr.
      Opaque INR.
      rewrite /= -Heq Rmult_plus_distr_l -!Rmult_assoc.
      Transparent INR. 
      rewrite (Rmult_comm _ ε1) (Rmult_comm _ ε2) !Rmult_assoc.
      rewrite Rmult_div_assoc (Rmult_comm _ N) -Rmult_div_assoc.
      rewrite Rdiv_diag; last apply INR_S_not_0.
      rewrite Rmult_plus_distr_l Ropp_mult_distr_r_reverse.
      rewrite Rmult_div_assoc (Rmult_comm _ N) -Rmult_div_assoc.
      rewrite Rdiv_diag; last apply INR_S_not_0.
      rewrite -Rminus_def.
      simpl_expr.
      setoid_rewrite ssrbool.fun_if; cbv [nonneg ε1' ε2'].
      by apply SeriesC_case. }
    wp_pures.
    unfold f. repeat case_bool_decide; wp_pures; try lia.
    - iApply ("HΦ" $! 1)%nat; auto.
    - iApply ("HΦ" $! 0)%nat; auto.
  Qed.
    
  Lemma bernoulli_succes_spec (N M : nat) : 
    [[{↯ (1 - (N / S M))}]]
      bernoulli #N #M 
    [[{ v, RET v; ⌜v = #1⌝ }]].
  Proof.
    iIntros "%Φ Herr HΦ".
    destruct (decide (S M < N)%nat) as [Hlt |Hge%not_lt].
    { cred_contra. rewrite Rcomplements.Rlt_minus_l.
      simpl_expr. }
    wp_apply (twp_bernoulli_scale _ _ _ 1 0 with "[$Herr]")%R; [lia | lra..|].
    iIntros "%k [(_ & Herr) | (-> & Herr)]".
    - cred_contra. 
    - by iApply "HΦ".
  Qed.

  Lemma bernoulli_failure_spec (N M : nat) : 
    [[{↯ (N / S M)}]] 
      bernoulli #N #M 
    [[{ v, RET v; ⌜v = #0⌝ }]].
  Proof.
    iIntros "%Φ Herr HΦ".
    destruct (decide (S M < N)%nat) as [Hlt |Hge%not_lt].
    { cred_contra. simpl_expr. }
    wp_apply (twp_bernoulli_scale _ _ (N / S M) 0 1 with "[$Herr]")%R => //.
    iIntros "%k [(-> & Herr) | (-> & Herr)]".
    - by iApply "HΦ".
    - find_contra.
  Qed.

  Lemma bernoulli_spec (N M : nat) :
    [[{True}]] 
      bernoulli #N #M 
    [[{ v, RET v; ⌜v = #0⌝ ∨ ⌜v = #1⌝}]].
  Proof.
    iIntros "%Φ _ HΦ".
    rewrite /bernoulli; wp_pures.
    wp_apply (twp_rand with "[$]") as "%n _".
    wp_pures; case_bool_decide;
    wp_pures; iApply "HΦ"; auto. 
  Qed.

End Bernoulli.