From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils.
Local Open Scope R.

Local Ltac done ::= solve[lia || lra || nra || real_solver || tactics.done || auto].
Ltac add_hint t := let n := fresh "hint" in have n := t.


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
    (∀ e, e ∈ l → e = a) →
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
    assert (Heq: ∀ e, e ∈ f <$> seq 0 N → e = e1). {
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
    assert (Heq: ∀ e, e ∈ f <$> seq N L → e = e2). {
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

  Lemma twp_bernoulli_scale (N M : nat) (ε ε1 ε2 : R) :
  (N ≤ S M)%nat →
  0 <= ε1 →
  0 <= ε2 →
  (ε1 * (1 - (N / S M))) + (ε2 * (N / S M)) = ε →
  [[{↯ ε}]]
    bernoulli #N #M
  [[{
      (k : nat), RET #k; 
      (⌜k = 0%nat⌝ ∗ ↯ ε1) ∨
      (⌜k = 1%nat⌝ ∗ ↯ ε2)
  }]].
  Proof.
    set p := N / S M.
    iIntros "%HNleM %ε1_pos %ε2_pos %Heq %Φ Herr HΦ".
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

  Lemma bernoulli_success_spec (N M : nat) :
    ∀ (ε ε' : R),
    (0 <= ε')%R →
    ε = (ε' * (N / S M)) → 
    [[{↯ ε ∗ ↯ (1 - (N / S M))}]]
      bernoulli #N #M 
    [[{ v, RET v; ↯ ε' ∗ ⌜v = #1⌝ }]].
  Proof.
    iIntros (ε ε' Hε' ->) "%Φ [Herr Hcost] HΦ".
    destruct (decide (S M < N)%nat) as [Hlt |Hge%not_lt].
    { cred_contra. rewrite Rcomplements.Rlt_minus_l.
      simpl_expr. }
    iPoseProof (ec_combine with "[$Herr $Hcost]") as "Herr".
    wp_apply (twp_bernoulli_scale _ _ _ 1 ε' with "Herr")%R; [lia| lra|lra..|].
    iIntros "%k [(_ & Herr) | (-> & Herr)]".
    - cred_contra. 
    - iApply "HΦ". by iFrame.
  Qed.

  Lemma bernoulli_failure_spec (N M : nat) :
    ∀ (ε ε' : R),
    (0 <= ε')%R →
    ε = (ε' * (1 - N / S M)) → 
    [[{↯ ε ∗ ↯ (N / S M)}]] 
      bernoulli #N #M 
    [[{ v, RET v; ↯ ε' ∗ ⌜v = #0⌝ }]].
  Proof.
    iIntros (ε ε' Hε ->) "%Φ [Herr Hcost] HΦ".
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

  Fixpoint is_bernoulli_translation (N M : nat) (v : list (fin 2)) (l : list (fin (S M))) :=
    match v, l with
    | [], [] => True
    | 0%fin::vt, lh::lt => (N ≤ lh)%nat ∧ is_bernoulli_translation N M vt lt
    | 1%fin::vt, lh::lt => (lh < N)%nat ∧ is_bernoulli_translation N M vt lt
    | _, _ => False
    end.
  
  Theorem is_bernoulli_translation_dec (N M : nat) (v : list (fin 2)) (l : list (fin (S M))) :
    {is_bernoulli_translation N M v l} + {¬ is_bernoulli_translation N M v l}.
  Proof.
    unfold Decision.
    induction v, l as [|vh vt _ | lh lt _ | vh vt lh lt [IH | IH]] 
      using list_double_ind; simpl; auto.
    - inv_fin vh => //=.
    - repeat (inv_fin vh; try intro vh);
      [destruct (le_dec N lh) | destruct (lt_dec lh N)]; 
      tauto.
    - right; full_inv_fin; intros [_ Hcontra]; contradiction.
  Qed.

  Fixpoint tape_to_bernoulli (N M : nat) (l : list (fin (S M))) : list (fin 2):=
    match l with
    | [] => []
    | h::t => if bool_decide (N ≤ h)%nat
              then 0%fin::tape_to_bernoulli N M t
              else 1%fin::tape_to_bernoulli N M t
    end.

  Fixpoint bernoulli_to_tape (M : nat) (l : list (fin 2)) : list (fin (S M)):=
    match l with
    | [] => []
    | 0%fin::t => (nat_to_fin (Nat.lt_succ_diag_r M))::bernoulli_to_tape M t
    | _::t => 0%fin::bernoulli_to_tape M t
    end.

  Lemma tape_to_bernoulli_translation (N M : nat) :
    ∀ (v : list (fin 2)) (l : list (fin (S M))),
    is_bernoulli_translation N M v l ↔ v = tape_to_bernoulli N M l.
  Proof.
    move => v l.
    elim: l v => [[|hv tv]|h t IHt [|hv tv]] /= //.
    - inv_fin hv; last (move=>hv; inv_fin hv); done.
    - inv_fin hv;
        last (move=>hv; inv_fin hv);
        last done;
        case_bool_decide.
      + rewrite IHt.
        split.
        * move=>[_ ->] //.
        * move=> Heq. by injection Heq as ->.
      + split.
        * lia.
        * move=> Heq. discriminate.
      + split.
        * lia.
        * move=> Heq. discriminate.
      + rewrite IHt.
        split.
        * move=>[_ ->] //.
        * move=> Heq.
          injection Heq as ->.
          split; last done.
          lia.
  Qed.

  Lemma tape_to_bernoulli_app (N M : nat) :
    ∀ (l1 l2 : list (fin (S M))),
    tape_to_bernoulli N M (l1 ++ l2) = tape_to_bernoulli N M l1 ++ tape_to_bernoulli N M l2.
  Proof.
    elim=>[|h1 t1 IHt1] l2 /= //.
    rewrite IHt1 //.
  Qed.
    
  Lemma length_tape_to_bernoulli (N M : nat) :
    ∀ (l : list (fin (S M))), length (tape_to_bernoulli N M l) = length l.
  Proof.
    elim=>[// |h t /=].
    case_bool_decide;
      move=><- //.
  Qed.

  Lemma length_bernoulli_to_tape (M : nat) : ∀ (l : list (fin 2)), length (bernoulli_to_tape M l) = length l.
  Proof.
    elim=>[// |h t /=].
    inv_fin h;
      last (move=>v);
      move=><- //.
  Qed.

  Lemma bernoulli_to_tape_to_bernoulli (N M : nat) :
    (0 < N)%nat →
    (N ≤ M)%nat →
    ∀ (l : list (fin 2)), tape_to_bernoulli N M (bernoulli_to_tape M l) = l.
  Proof.
    move=> zero_lt_N N_le_M.
    elim=>[// |h t IHt].
    inv_fin h;
      last (move=>h; inv_fin h; last (move=>h; inv_fin h));
      simpl;
      rewrite IHt;
      first rewrite fin_to_nat_to_fin;
      case_bool_decide;
      done.
  Qed.
    
  Lemma is_bernoulli_translation_app_0 (N M : nat) (v : list (fin 2)) (l : list (fin (S M))) :
    ∀ (k : fin (S M)),
    N ≤ k →
    is_bernoulli_translation N M v l →
    is_bernoulli_translation N M (v ++ [0%fin]) (l ++ [k]).
  Proof.
    move=> k N_le_k.
    move: l.
    induction v as [|hv v]; move=>[|hl l];  [done | contradiction|..].
    - simpl.
      inv_fin hv; first contradiction.
      move=> hv.
      inv_fin hv; contradiction.
    - inv_fin hv; [|move=>hv; inv_fin hv]; last (move=>hv; inv_fin hv);
        simpl;
        move=>[Ht Htl] //.
  Qed.

  Lemma is_bernoulli_translation_app_1 (N M : nat) (v : list (fin 2)) (l : list (fin (S M))) :
    ∀ (k : fin (S M)),
    (k < N)%nat →
    is_bernoulli_translation N M v l →
    is_bernoulli_translation N M (v ++ [1%fin]) (l ++ [k]).
  Proof.
    move=> k N_le_k.
    move: l.
    induction v as [|hv v]; move=>[|hl l]; [done | contradiction |..].
    - inv_fin hv; first contradiction.
      move=> hv.
      inv_fin hv; contradiction.
    - inv_fin hv; [|move=>hv; inv_fin hv]; last (move=>hv; inv_fin hv);
        simpl;
        move=>[Ht Htl] //.
  Qed.
  
  
  Definition own_bernoulli_tape α N M v := (∃ l, α ↪ (M; l) ∗ ⌜is_bernoulli_translation N M v l⌝)%I.

  Lemma twp_presample_bernoulli :
    ∀ (e : expr) (α : loc) (Φ : val → iProp Σ)
      (N M : nat) (ns : list (fin 2)),
    to_val e = None
    → own_bernoulli_tape α N M ns ∗
    (own_bernoulli_tape α N M (ns ++ [0%fin]) -∗ WP e [{ Φ }]) ∗
    (own_bernoulli_tape α N M (ns ++ [1%fin]) -∗ WP e [{ Φ }])
      ⊢  WP e [{ Φ }]
  .
  Proof.
    move=> e α Φ N M ns HNone.
    iIntros "(Hα & H0 & H1)".
    rewrite {1}/own_bernoulli_tape.
    iDestruct "Hα" as "(%l & Hα & %Htl)".
    wp_apply twp_presample; first done.
    iFrame.
    iIntros (k) "Htape".
    case (decide (N ≤ k)) => [N_le_k | k_lt_N].
    - iApply "H0".
      rewrite /own_bernoulli_tape.
      iExists _.
      iFrame.
      iPureIntro.
      by apply: is_bernoulli_translation_app_0.
    - iApply "H1".
      rewrite /own_bernoulli_tape.
      iExists _.
      iFrame.
      iPureIntro.
      apply: is_bernoulli_translation_app_1;
        [lia | done].
  Qed.

  Lemma twp_bernoulli_tape :
    ∀ (N M : nat) (α : loc) (ns : list (fin 2)) (n : fin 2),
    [[{ own_bernoulli_tape α N M (n::ns) }]]
      bernoulli_tape (#lbl:α) #N #M
      [[{ RET #n ; own_bernoulli_tape α N M ns }]].
  Proof.
    iIntros (N M α ns n Φ) "Htape HΦ".
    rewrite /bernoulli_tape {1}/own_bernoulli_tape.
    iDestruct "Htape" as "(%l & Hα & %Htl)".
    case: l Htl => [Hcontra | h t Htl].
    { inv_fin n; first done.
      move => n.
      inv_fin n; first done.
      move => n.
      inv_fin n.
    } 
    wp_pures.
    wp_apply (twp_rand_tape with "Hα").
    iIntros "Hα".
    inv_fin n; simpl.
    - move=> [N_le_h Htl].
      wp_pures.
      case_bool_decide; first lia.
      wp_pures.
      iModIntro.
      iApply "HΦ".
      by iFrame.
    - intros n.
      inv_fin n; last (intros n; inv_fin n).
      move=> [k_lt_N Hlt].
      wp_pures.
      case_bool_decide; last lia.
      wp_pures.
      iModIntro.
      iApply "HΦ".
      by iFrame.
  Qed.

  Lemma twp_presample_bernoulli_planner :
    ∀ (N M : nat) (e : expr) (ε : nonnegreal)
      (L : nat) (α : loc) (Φ : val → iProp Σ)
      (prefix : list (fin 2)) (suffix : list (fin 2) → list (fin 2)),
    (0 < N)%nat →
    (N < S M)%nat →
    to_val e = None →
    (∀ junk : list (fin 2),
       (0 < length (suffix (prefix ++ junk)) <= L)%nat) →
    0 < ε →
    ↯ ε ∗ own_bernoulli_tape α N M prefix ∗
    ( (∃ (junk : list (fin 2)), own_bernoulli_tape α N M (prefix ++ junk ++ suffix (prefix ++ junk))) -∗ WP e [{ Φ }]
    ) ⊢ WP e [{ Φ }].
  Proof.
    rewrite /own_bernoulli_tape.
    iIntros (N M e ε L α Φ prefix suffix zero_lt_N N_lt_SM e_not_val suff_bound ε_pos)
      "(Herr & (%l & Hα & %Htl) & Hnext)".
    set suffix2 := bernoulli_to_tape M ∘ suffix ∘ tape_to_bernoulli N M.
    wp_apply (twp_presample_planner_pos _ M _ _ _ _ _ L l suffix2); try done.
    {
      move=>junk.
      rewrite /suffix2 length_bernoulli_to_tape tape_to_bernoulli_app.
      apply tape_to_bernoulli_translation in Htl as <-.
      apply suff_bound.
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
    do 2 f_equal.
    rewrite -tape_to_bernoulli_app /suffix2 /=.
    rewrite bernoulli_to_tape_to_bernoulli //.
  Qed.
  
End Bernoulli. 
