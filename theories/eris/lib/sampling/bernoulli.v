From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils.
#[local] Open Scope R.

#[local] Ltac done ::= solve[lia || lra || nra || real_solver || tactics.done || auto].

Section Lemmas.

  Lemma foldr_plus_app (l1 l2 : list R) (acc : R) :
    foldr Rplus acc (l1 ++ l2) = foldr Rplus 0 l1 + foldr Rplus acc l2.
  Proof.
    elim: l1 =>> //=.
  Qed.


  Lemma fmap_prop {A B : Type} (l : list A) (f : A → B) (P1 : A → Prop) (P2 : B → Prop) :
    (∀ a, P1 a → P2 (f a)) →
    (∀ a, a ∈ l → P1 a) →
    ∀ b, b ∈ (f <$> l) → P2 b.
  Proof.
    move=> HPs.
    elim: l => [_ ? /= HinNil| a l IH Hforall /= b Hin].
    - by apply not_elem_of_nil in HinNil.
    - apply elem_of_cons in Hin as [-> | Hin].
      + apply HPs, Hforall, elem_of_list_here.
      + apply IH => // a' Ha'.
        apply Hforall, elem_of_list_further, Ha'.
  Qed.

  Lemma forall_list_eq {A : Type} (l : list A) (a : A) :
    (∀ e, e ∈ l → e = a) →
    l = repeat a (length l).
  Proof.
    add_hint @elem_of_list_here.
    add_hint @elem_of_list_further.
    elim: l => //= e l IH Hl.
    rewrite (Hl e) // -IH //.
  Qed.

  Lemma map_seq_if_lt {A : Type} (e1 e2 : A) (N : nat):
    (λ x, if bool_decide (x < N)%nat then e1 else e2) <$> seq 0 N = repeat e1 N.
  Proof.
    set f := (λ x : nat, if bool_decide (x < N)%nat then e1 else e2).
    assert (Heq: ∀ e, e ∈ f <$> seq 0 N → e = e1). {
      apply (fmap_prop _ f (λ n, n < N)%nat) => [a Ha | a Ha].
      - rewrite /f bool_decide_eq_true_2 //.
      - by apply elem_of_seq in Ha as [_ Ha].
    }
    replace N with (length (f <$> seq 0 N)) at 2 by rewrite fmap_length seq_length //.
    exact: forall_list_eq Heq.
  Qed.

  Lemma map_seq_if_ge {A : Type} (e1 e2 : A) (N L : nat):
    (λ x, if bool_decide (x < N)%nat then e1 else e2) <$> seq N L = repeat e2 L.
  Proof.
    set f := (λ x : nat, if bool_decide (x < N)%nat then e1 else e2).
    assert (Heq: ∀ e, e ∈ f <$> seq N L → e = e2). {
      apply (fmap_prop _ f (λ n, n >= N)%nat) => a Ha.
      - rewrite /f bool_decide_eq_false_2 //.
      - by apply elem_of_seq in Ha as [].
    }
    rewrite (forall_list_eq _ _ Heq) fmap_length seq_length //.
  Qed.


  Lemma foldr_plus_repeat (ε : R) (L : nat) :
    foldr Rplus 0 (repeat ε L) = ε * L.
  Proof.
    elim: L =>> //.
    rewrite S_INR //=.
  Qed.

  Lemma SeriesC_case (N M : nat) (ε1 ε2 : R) :
    (N <= S M)%nat →
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


Section TapeTranslation.
  Definition is_bernoulli_translation (N M : nat) : list (fin 2) → list (fin (S M)) → Prop :=
    Forall2 (
      λ v l, 
        (v = 0%fin ∧ N ≤ fin_to_nat l) ∨
        (v = 1%fin ∧ fin_to_nat l < N)%nat
    ).
  Lemma is_bernoulli_translation_def (N M : nat) (v : list (fin 2)) (l : list (fin (S M))) :
    is_bernoulli_translation N M v l =
    Forall2 (
      λ v l, 
        (v = 0%fin ∧ N ≤ fin_to_nat l) ∨
        (v = 1%fin ∧ fin_to_nat l < N)%nat
    ) v l.
  Proof.
    reflexivity.
  Qed.

  
  Lemma is_bernoulli_translation_dec (N M : nat) (v : list (fin 2)) (l : list (fin (S M))) :
    {is_bernoulli_translation N M v l} + {¬ is_bernoulli_translation N M v l}.
  Proof.
    rewrite is_bernoulli_translation_def.
    apply Forall2_dec => vh lh.
    repeat inv_fin vh =>[|vh]; destruct (decide (N ≤ lh)) as [? | ?%not_le];
    solve
      [ left; done 
      | right; move=> [[_ Hcontra] | [Hcontra _]] // ].
  Qed.

  Lemma is_bernoulli_translation_length (N M : nat) (v : list (fin 2)) (l : list (fin (S M))) :
    is_bernoulli_translation N M v l → length v = length l.
  Proof.
    rewrite is_bernoulli_translation_def.
    apply Forall2_length.
  Qed.
  
  Lemma is_bernoulli_translation_nil (N M : nat) :
    is_bernoulli_translation N M [] [].
  Proof.
    rewrite is_bernoulli_translation_def.
    apply Forall2_nil_2.
  Qed.

  Lemma is_bernoulli_translation_cons (N M : nat) (vh : fin 2) (vt : list (fin 2)) (lh : fin (S M)) (lt : list (fin (S M))):
    is_bernoulli_translation N M (vh :: vt) (lh :: lt) <->
    (vh = 0%fin ∧ (N ≤ lh)%nat ∧ is_bernoulli_translation N M vt lt) ∨
    (vh = 1%fin ∧ (lh < N)%nat ∧ is_bernoulli_translation N M vt lt)
  .
  Proof.
    rewrite is_bernoulli_translation_def.
    rewrite Forall2_cons; tauto.
  Qed.
  

  Definition tape_to_bernoulli (N M : nat) : list (fin (S M)) → list (fin 2) :=
    map (λ v, if bool_decide (N ≤ fin_to_nat v)%nat then 0%fin else 1%fin).

  Lemma tape_to_bernoulli_def (N M : nat) (l : list (fin (S M))) :
    tape_to_bernoulli N M l = map (λ v, if bool_decide (N ≤ fin_to_nat v)%nat then 0%fin else 1%fin) l.
  Proof.
    reflexivity.
  Qed.
  
  Definition bernoulli_to_tape (M : nat) : list (fin 2) → list (fin (S M)) :=
    map (λ v, if bool_decide (v = 1)%fin then 0%fin else (nat_to_fin (Nat.lt_succ_diag_r M))).
  
  Lemma bernoulli_to_tape_def (M : nat) (l : list (fin 2)) :
    bernoulli_to_tape M l = map (λ v, if bool_decide (v = 1)%fin then 0%fin else (nat_to_fin (Nat.lt_succ_diag_r M))) l.
  Proof.
    reflexivity.
  Qed.


  
  Lemma tape_to_bernoulli_translation (N M : nat) (v : list (fin 2)) (l : list (fin (S M))) :
    is_bernoulli_translation N M v l ↔ v = tape_to_bernoulli N M l.
  Proof.
    elim: l v => [[|hv tv]|h t IHt [|hv tv]] /= //; split => H //;
    [apply is_bernoulli_translation_nil | by apply Forall2_length in H..| |].
    - destruct (IHt tv) as [IHt1 IHt2]. 
      apply Forall2_cons in H as [[[-> HNleh] | [-> HhltN] ] Hforall].
      + rewrite bool_decide_eq_true_2 // -IHt1 //.
      + rewrite bool_decide_eq_false_2 // -IHt1 //.
    - case:H => -> ->.
      rewrite is_bernoulli_translation_cons;
      destruct (decide (N ≤ h))%nat as [HNleh | HhltN%not_le].
      + rewrite IHt bool_decide_eq_true_2 //.
      + rewrite IHt bool_decide_eq_false_2 //.
  Qed.

  Lemma tape_to_bernoulli_app (N M : nat) (l1 l2 : list (fin (S M))) :
    tape_to_bernoulli N M (l1 ++ l2) = tape_to_bernoulli N M l1 ++ tape_to_bernoulli N M l2.
  Proof.
    apply map_app.
  Qed.
    
  Lemma length_tape_to_bernoulli (N M : nat) (l : list (fin (S M))) :
    length (tape_to_bernoulli N M l) = length l.
  Proof.
    apply map_length.
  Qed.

  Lemma length_bernoulli_to_tape (M : nat) (l : list (fin 2)) : length (bernoulli_to_tape M l) = length l.
  Proof.
    apply map_length.
  Qed.

  Lemma bernoulli_to_tape_to_bernoulli (N M : nat) (l : list (fin 2)) :
    (0 < N ≤ M)%nat →
    tape_to_bernoulli N M (bernoulli_to_tape M l) = l.
  Proof.
    move=> [zero_lt_N N_le_M].
    elim: l =>[// |h t IHt].
    inv_fin h;
      last (move=>h; inv_fin h; last (move=>h; inv_fin h));
      simpl;
      rewrite IHt;
      first rewrite fin_to_nat_to_fin;
      case_bool_decide;
      done.
  Qed.
    
  Lemma is_bernoulli_translation_app_0 (N M : nat) (v : list (fin 2)) (l : list (fin (S M))) (k : fin (S M)) :
    N ≤ k →
    is_bernoulli_translation N M v l →
    is_bernoulli_translation N M (v ++ [0%fin]) (l ++ [k]).
  Proof.
    move=> N_le_k H.
    apply Forall2_app =>//.
  Qed.

  Lemma is_bernoulli_translation_app_1 (N M : nat) (v : list (fin 2)) (l : list (fin (S M))) (k : fin (S M)) :
    (k < N)%nat →
    is_bernoulli_translation N M v l →
    is_bernoulli_translation N M (v ++ [1%fin]) (l ++ [k]).
  Proof.
    move=> k_lt_N H.
    apply Forall2_app =>//.
  Qed.

  #[global] Opaque is_bernoulli_translation.
  #[global] Opaque tape_to_bernoulli.
  #[global] Opaque bernoulli_to_tape.

End TapeTranslation.

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
  
  
  Definition bernoulli_tape : val := 
    λ: "α" "N" "M",
      let: "x" := rand("α") "M" in 
      if: "x" < "N" then #1 else #0.

  Definition bernoulli : expr := (bernoulli_tape #())%E.

  Lemma twp_bernoulli_scale (N M : nat) (ε ε1 ε2 : R) (p := N / S M) :
    (N ≤ S M)%nat →
    0 <= ε1 →
    0 <= ε2 →
    (ε1 * (1 - p)) + (ε2 * p) = ε →
    [[{↯ ε}]]
      bernoulli #N #M
    [[{
        (k : nat), RET #k; 
        (⌜k = 0%nat⌝ ∗ ↯ ε1) ∨
        (⌜k = 1%nat⌝ ∗ ↯ ε2)
    }]].
  Proof.
    iIntros (HNleM ε1_pos ε2_pos Heq Φ) "Herr HΦ".
    rewrite /bernoulli /bernoulli_tape.
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
      setoid_rewrite ssrbool.fun_if.
      rewrite /= -Heq SeriesC_case //=.
      unfold p.
      assert (S M > 0) by apply pos_INR_S.
      rewrite !Rmult_plus_distr_l -(Rmult_assoc (S M) ε2 _) -(Rmult_comm ε2 (S M)) (Rmult_assoc ε2 (S M) _).
      simpl_expr.
      rewrite -(Rmult_assoc (S M) ε1 _) -(Rmult_comm ε1 (S M)) (Rmult_assoc ε1 (S M) _).
      simpl_expr. }
    wp_pures.
    unfold f. repeat case_bool_decide; wp_pures; try lia.
    - iApply ("HΦ" $! 1)%nat; auto.
    - iApply ("HΦ" $! 0)%nat; auto.
  Qed.

  Lemma bernoulli_success_spec (N M : nat) (ε ε' : R) (p := N / S M) :
    (0 <= ε')%R →
    ε = (ε' * (N / S M)) → 
    [[{↯ ε ∗ ↯ (1 - (N / S M))}]]
      bernoulli #N #M 
    [[{ v, RET v; ↯ ε' ∗ ⌜v = #1⌝ }]].
  Proof.
    iIntros (Hε' ->) "%Φ [Herr Hcost] HΦ".
    destruct (decide (S M < N)%nat) as [Hlt |Hge%not_lt].
    { cred_contra. rewrite Rcomplements.Rlt_minus_l.
      simpl_expr. }
    iPoseProof (ec_combine with "[$Herr $Hcost]") as "Herr".
    wp_apply (twp_bernoulli_scale _ _ _ 1 ε' with "Herr")%R; [lia| lra|lra..|].
    iIntros "%k [(_ & Herr) | (-> & Herr)]".
    - cred_contra. 
    - iApply "HΦ". by iFrame.
  Qed.

  Lemma bernoulli_failure_spec (N M : nat) (ε ε' : R) :
    (0 <= ε')%R →
    ε = (ε' * (1 - N / S M)) →
    [[{↯ ε ∗ ↯ (N / S M)}]] 
      bernoulli #N #M 
    [[{ v, RET v; ↯ ε' ∗ ⌜v = #0⌝ }]].
  Proof.
    iIntros (Hε ->) "%Φ [Herr Hcost] HΦ".
    destruct (decide (S M < N)%nat) as [Hlt |Hge%not_lt].
    { cred_contra. simpl_expr. }
    iPoseProof (ec_combine with "[$Herr $Hcost]") as "Herr".
    wp_apply (twp_bernoulli_scale _ _ _ ε' 1 with "[$Herr]")%R => //.
    iIntros "%k [(-> & Herr) | (-> & Herr)]".
    - iApply "HΦ". by iFrame.
    - find_contra.
  Qed.

  Lemma bernoulli_success_spec_simple (N M : nat) :
    [[{↯ (1 - (N / S M))}]]
      bernoulli #N #M
    [[{ v, RET v; ⌜v = #1⌝ }]].
  Proof.
    iIntros (Φ) "Herr HΦ".
    iMod ec_zero as "Hzero".
    wp_apply (bernoulli_success_spec _ _ 0%R 0%R with "[$Herr $Hzero]") => //.
    iIntros (v) "[_ Hv]".
    iApply ("HΦ" with "Hv").
  Qed.

  Lemma bernoulli_failure_spec_simple (N M : nat) :
    [[{↯ (N / S M)}]] 
      bernoulli #N #M 
    [[{ v, RET v; ⌜v = #0⌝ }]].
  Proof.
    iIntros (Φ) "Herr HΦ".
    iMod ec_zero as "Hzero".
    wp_apply (bernoulli_failure_spec _ _ 0%R 0%R with "[$Herr $Hzero]") => //.
    iIntros (v) "[_ Hv]".
    iApply ("HΦ" with "Hv").
  Qed.

  Lemma bernoulli_spec (N M : nat) :
    [[{True}]] 
      bernoulli #N #M 
    [[{ v, RET v; ⌜v = #0⌝ ∨ ⌜v = #1⌝}]].
  Proof.
    iIntros "%Φ _ HΦ".
    rewrite /bernoulli /bernoulli_tape; wp_pures.
    wp_apply (twp_rand with "[$]") as "%n _".
    wp_pures; case_bool_decide;
    wp_pures; iApply "HΦ"; auto.
  Qed.

  Example bernoulli_twice (N M : nat) (p := N / S M) (Hlt : (N <= S M)%nat) :
    [[{ ↯ (1 - p^2) }]]
      let v1 := bernoulli #N #M in 
      let v2 := bernoulli #N #M in 
      (v1, v2)
    [[{ RET (#1, #1); True }]].
  Proof.
    assert (0 <= p <= 1) as Hp. {
      split; subst p; simpl_expr.
    }
    iIntros "%Φ Herr HΦ".
    replace (1 - p ^ 2) with ((1 - p) + (p - p^2)) by lra.
    iPoseProof (ec_split with "Herr") as "[Herr1 Herr2]" => //.
    wp_apply (bernoulli_success_spec _ _ (p - p^2) (1 - p) with "[$Herr1 $Herr2]") as "%v [Herr ->]" => //;
    first (fold p; nra).
    wp_apply (bernoulli_success_spec_simple with "Herr") as (?) "->".
    wp_pures.
    by iApply "HΦ".
  Qed.

  
  Definition own_bernoulli_tape α N M v := (∃ l, α ↪ (M; l) ∗ ⌜is_bernoulli_translation N M v l⌝)%I.

  Lemma twp_presample_bernoulli 
      (e : expr) (α : loc) (Φ : val → iProp Σ)
      (N M : nat) (ns : list (fin 2)) :
    to_val e = None → 
    own_bernoulli_tape α N M ns ∗
    (∀ (i : fin 2), own_bernoulli_tape α N M (ns ++ [i]) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }]
  .
  Proof.
    iIntros (HNone) "[Hα Hnext]".
    rewrite {1}/own_bernoulli_tape.
    iDestruct "Hα" as "(%l & Hα & %Htl)".
    wp_apply twp_presample; first done.
    iFrame.
    iIntros (k) "Htape".
    destruct (decide (N ≤ k)) as [N_le_k | k_lt_N%not_le].
    - iApply "Hnext".
      rewrite /own_bernoulli_tape.
      iExists _.
      iFrame.
      iPureIntro.
      by apply is_bernoulli_translation_app_0.
    - iApply "Hnext".
      rewrite /own_bernoulli_tape.
      iExists _.
      iFrame.
      iPureIntro.
      by apply is_bernoulli_translation_app_1.
  Qed.

  Lemma twp_presample_bernoulli_adv_comp 
      (e : expr) (α : loc) (Φ : val → iProp Σ)
      (N M : nat) (ns : list (fin 2)) (ε : R)
      (D : fin 2 → R) :
    (N ≤ M + 1)%nat →
    (∀ (i : fin 2), 0 <= D i)%R →
    (D 0%fin * (1 - (N / (M + 1))) + D 1%fin * (N / (M + 1)) = ε)%R
    →  to_val e = None
    → own_bernoulli_tape α N M ns ∗ ↯ ε ∗
    (∀ (i : fin 2), ↯ (D i) ∗ own_bernoulli_tape α N M (ns ++ [i]) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }]
  .
  Proof.
    iIntros (N_le_SM D_nonneg D_expected_ε HNone) "(Hα & Herr & Hnext)".
    rewrite {1}/own_bernoulli_tape.
    iDestruct "Hα" as "(%l & Hα & %Htl)".
    set f :=
      λ (n : fin (S M)), 
        if bool_decide (fin_to_nat n < N)%nat then D 1%fin else D 0%fin.
    wp_apply (twp_presample_adv_comp _ M _ _ _ _ _ _ f); first done; last iFrame.
    { move=>n.
      unfold f.
      case_bool_decide; apply D_nonneg.
    }
    { unfold f. rewrite SeriesC_scal_l. rewrite Rmult_comm.
      simpl_expr.
      Opaque INR.
      rewrite SeriesC_case //=.
      replace (M + 1)%R with (S M : R) in D_expected_ε; last first.
      { rewrite -INR_1 -plus_INR. f_equal. lia. }
      rewrite -D_expected_ε Rmult_plus_distr_l -!Rmult_assoc
                 !(Rmult_comm _ (D _)) !Rmult_assoc.
      simpl_expr.
      rewrite Rmult_minus_distr_l.
      simpl_expr.
    }
    iIntros (n) "[Herr Hα]".
    unfold f.
    case_bool_decide;
      wp_apply "Hnext";
      iFrame;
      iPureIntro.
    - apply: is_bernoulli_translation_app_1 => //. 
    - apply: is_bernoulli_translation_app_0 => //.
  Qed.
    

  Lemma twp_bernoulli_tape (N M : nat) (α : loc) (ns : list (fin 2)) (n : fin 2) :
    [[{ own_bernoulli_tape α N M (n::ns) }]]
      bernoulli_tape (#lbl:α) #N #M
    [[{ RET #n ; own_bernoulli_tape α N M ns }]].
  Proof.
    iIntros (Φ) "Htape HΦ".
    rewrite /bernoulli_tape {1}/own_bernoulli_tape.
    iDestruct "Htape" as "(%l & Hα & %Htl)".
    case: l Htl => [Hcontra | h t Htl].
    { by apply is_bernoulli_translation_length in Hcontra. } 
    wp_pures.
    wp_apply (twp_rand_tape with "Hα").
    iIntros "Hα".
    wp_pures.
    apply is_bernoulli_translation_cons in Htl as [(-> & HNleh & Htl)| (-> & HhltN & Htl)].
    - case_bool_decide; first lia.
      wp_pures.
      iModIntro.
      iApply "HΦ".
      by iFrame.
    - case_bool_decide; last lia.
      wp_pures.
      iModIntro.
      iApply "HΦ".
      by iFrame.
  Qed.
  About twp_presample_planner_pos.

  Lemma twp_presample_bernoulli_planner 
      (N M : nat) (e : expr) (ε : nonnegreal)
      (L : nat) (α : loc) (Φ : val → iProp Σ)
      (prefix : list (fin 2)) (suffix : list (fin 2) → list (fin 2)) :
    (0 < N < S M)%nat →
    to_val e = None →
    (∀ junk : list (fin 2),
       (0 < length (suffix (prefix ++ junk)) <= L)%nat) →
    0 < ε →
    ↯ ε ∗ own_bernoulli_tape α N M prefix ∗
    ( (∃ (junk : list (fin 2)), own_bernoulli_tape α N M (prefix ++ junk ++ suffix (prefix ++ junk))) -∗ WP e [{ Φ }]
    ) ⊢ WP e [{ Φ }].
  Proof.
    iIntros ([zero_lt_N N_lt_SM] e_not_val suff_bound ε_pos)
      "(Herr & (%l & Hα & %Htl) & Hnext)".
    set suffix2 := bernoulli_to_tape M ∘ suffix ∘ tape_to_bernoulli N M.
    wp_apply (twp_presample_planner_pos _ M _ _ _ _ _ L l suffix2); try done.
    {
      move=>junk.
      rewrite /suffix2 length_bernoulli_to_tape tape_to_bernoulli_app.
      by apply tape_to_bernoulli_translation in Htl as <-.
    }
    iFrame.
    iIntros "(%junk & Hα)".
    iApply "Hnext".
    iExists (tape_to_bernoulli N M junk), _.
    iFrame.
    iPureIntro.
    apply tape_to_bernoulli_translation.
    rewrite !tape_to_bernoulli_app.
    apply tape_to_bernoulli_translation in Htl as ->.
    rewrite -tape_to_bernoulli_app /suffix2 bernoulli_to_tape_to_bernoulli //=.
  Qed.
 
End Bernoulli.
