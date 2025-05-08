From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils.
From clutch.eris.lib.sampling.bernoulli Require Import interface.
From clutch.eris.lib.sampling.binomial Require Import interface.

Section Polya.
  
  Set Default Proof Using "Type*".
  Context `{!erisGS Σ}.
  Context `{!bernoulli_spec bernoulli}.

  #[local] Ltac done ::= solve[
    lia |
    lra |
    nra |
    real_solver  |
    tactics.done |
    auto
  ].

  Definition polya : val :=
    rec: "polya" "α" "red" "black" "n" :=
      if: "n" = #0 then #0
      else
        let: "x" := bernoulli "α" "red" ("red" + "black" - #1)  in
        if: "x" = #1 
        then #1 + "polya" "α" ("red" + #1) "black" ("n" - #1)
        else "polya" "α" "red" ("black" + #1) ("n" - #1).
  
  
  Definition Beta x y := ((fact (x - 1)) * (fact (y - 1)) / (fact (x + y - 1)))%R.
  
  Lemma Beta_0_l (y : nat) :
    Beta 0 y = 1.
  Proof.
    add_hint INR_fact_lt_0.
    rewrite /Beta /=.
    simpl_expr.
  Qed.
  Lemma Beta_0_r (x : nat) :
    Beta x 0 = 1.
  Proof.
    add_hint INR_fact_lt_0.
    rewrite /Beta /=.
    simpl_expr.
    do 2 f_equal.
    lia.
  Qed.

  Lemma Beta_pos (x y : nat) : (0 < Beta x y)%R.
  Proof.
    add_hint INR_fact_lt_0.
    unfold Beta.
    simpl_expr.
  Qed.

  Definition Beta_prob (r b n k : nat) := (choose n k * Beta (k + r) (n - k + b) / Beta r b)%R.

  Lemma Beta_prob_pos (r b n k : nat) : (0 <= Beta_prob r b n k)%R.
  Proof.
    add_hint Beta_pos.
    add_hint choose_pos.
    unfold Beta_prob.
    real_solver.
  Qed.

  #[local] Open Scope R.
  Lemma Beta_sum_split (r b n : nat) (E : fin (S (S n)) → R) :
    (0 < r)%nat → 
    (0 < b)%nat →
    SeriesC (λ k : fin (S (S n)), Beta_prob r b (S n) k * E k)%R = 
      r / (r + b) * SeriesC (λ k : fin (S n), Beta_prob (S r) b n k * E (FS k))
    + b / (r + b) * SeriesC (λ k : fin (S n), Beta_prob r (S b) n k * E (fin_S_inj k))
  .
  Proof.
    intros H_r_pos H_b_pos.
    apply lt_INR in H_r_pos as H_r_pos'.
    apply lt_INR in H_b_pos as H_b_pos'.
    assert (0 < r + b) as H_rb_pos by rewrite -plus_INR //.
    add_hint INR_fact_lt_0.
    add_hint Beta_pos.
    add_hint fact_neq_0.
    rewrite Series_fin_first Series_fin_last.
    rewrite Series_fin_last Series_fin_first.
    rewrite !fin_to_nat_FS fin_to_nat_to_fin.
    set T0 := Beta_prob r b (S n) 0%fin * E 0%fin.
    set TN := Beta_prob r b (S n) (S n) * E (FS (nat_to_fin (Nat.lt_succ_diag_r n))).
    set T0' := Beta_prob r (S b) n 0%fin * E (fin_S_inj 0).
    set TN' := Beta_prob (S r) b n n * E (FS (nat_to_fin (Nat.lt_succ_diag_r n))).
    set p1 := r / (r + b).
    set p2 := b / (r + b).
    rewrite !Rmult_plus_distr_l.
    rewrite -!SeriesC_scal_l.
    assert (TN = p1 * TN') as <-.
    {
      subst TN TN'.
      rewrite -(Rmult_assoc p1).
      simpl_expr.
      unfold Beta_prob.
      rewrite !choose_n_n !Rmult_1_l.
      subst p1.
      assert (0 < (r + b) * Beta (S r) b) by real_solver.
      trans (r * Beta (n + S r) (n - n + b) / ((r + b) * Beta (S r) b)); last first.
      {
        simpl_expr.
        rewrite (Rmult_comm _ (/(r + b))).
        rewrite Rmult_assoc.
        rewrite -(Rmult_assoc (Beta (S r) b)).
        rewrite -(Rmult_assoc (Beta (S r) b)).
        rewrite (Rmult_comm _ (/(r + b))).
        rewrite -!(Rmult_assoc (r + b)).
        rewrite Rmult_inv_r // Rmult_1_l.
        rewrite (Rmult_comm _ r).
        rewrite Rmult_assoc.
        simpl_expr.
      }
      rewrite !Nat.sub_diag !Nat.add_0_l.
      simpl_expr.
      unfold Beta.
      simpl.
      rewrite !Nat.sub_0_r.
      replace (n + S r - 1)%nat with (n + r)%nat by lia.
      replace (n + S r + b - 1)%nat with (n + r + b)%nat by lia.
      rewrite -plus_INR.
      rewrite -!(Nat.add_assoc n r b).
      remember (r + b)%nat as A.
      set B := (fact (n + A)).
      remember (fact (n + r) * fact (b - 1)) as C.
      destruct r; first lia.
      rewrite fact_simpl mult_INR S_INR /= Nat.sub_0_r -!Rmult_assoc (Rmult_comm A) !Rmult_assoc.
      simpl_expr.
      rewrite -!mult_INR.
      rewrite -(Rmult_assoc (fact r)) -mult_INR.
      set D := (fact r * fact (b - 1))%nat.
      assert (0 < D) by rewrite mult_INR //.
      rewrite Rinv_mult Rinv_inv (Rmult_comm (/D)) -!Rmult_assoc.
      simpl_expr.
      rewrite Rmult_comm -Rmult_assoc.
      simpl_expr.

      rewrite (Rmult_comm B A) !(Rmult_assoc A) -Rmult_assoc.
      replace (fact (A - 1) * A) with (fact A : R) by rewrite HeqA -mult_INR /= Nat.sub_0_r //.
      rewrite (Rmult_comm _ C) -!Rmult_assoc.
      simpl_expr.
    }
    assert (T0 = p2 * T0') as <-. {
      subst T0 p2 T0'.
      rewrite /= -!(Rmult_assoc _ _ (E 0%fin)).
      simpl_expr.
      unfold Beta_prob.
      rewrite /Beta_prob /= Nat.sub_0_r !choose_n_0 !Rmult_1_l.
      rewrite Rmult_comm Nat.add_succ_r !Rdiv_def Rmult_assoc.
      simpl_expr.
      unfold Beta.
      destruct b; first lia.
      rewrite !Nat.add_succ_r !Nat.sub_succ !Nat.sub_0_r.
      rewrite !Rinv_mult !Rinv_inv !Rmult_assoc.
      simpl_expr.
      rewrite (Rmult_comm (/fact b)) (Rmult_comm (/fact (S b))) (fact_simpl b) mult_INR Rinv_mult -Rmult_assoc.
      simpl_expr.
      rewrite (Rmult_comm (fact _)) !Rmult_assoc.
      simpl_expr.
      rewrite Rmult_comm fact_simpl.
      simpl_expr.
      rewrite -plus_INR -mult_INR Nat.add_succ_r //.
    }
    rewrite -!Rplus_assoc.
    rewrite (Rplus_comm (SeriesC _)).
    rewrite !Rplus_assoc.
    rewrite (Rplus_comm TN).
    rewrite -!Rplus_assoc.
    simpl_expr.
    rewrite (Rplus_comm (SeriesC _)).
    rewrite !Rplus_assoc.
    simpl_expr.
    rewrite -SeriesC_plus; [|apply ex_seriesC_finite..].
    apply SeriesC_ext => k.
    rewrite -(Rmult_assoc p1).
    rewrite -(Rmult_assoc p2).
    rewrite -Rmult_plus_distr_r.
    simpl_expr.
    rewrite !fin_to_nat_FS.
    rewrite -fin_S_inj_to_nat.
    unfold p1, p2, Beta_prob. 
    rewrite -pascal'.
    rewrite Rdiv_def !Rmult_plus_distr_r.
    f_equal.
    - rewrite !Rdiv_def Rmult_assoc.
      rewrite (Rmult_comm (r * / (r + b))).
      rewrite !(Rmult_assoc (choose n k)).
      simpl_expr.
      rewrite Nat.add_succ_r (Rmult_comm (Beta r b)) Rmult_assoc Rmult_assoc -{1}(Rmult_1_r (Beta _ _)).
      simpl.
      simpl_expr.
      rewrite Rmult_comm.
      simpl_expr.
      rewrite Rmult_comm -Rmult_assoc.
      simpl_expr.
      unfold Beta.
      simpl.
      rewrite !Nat.sub_0_r.
      rewrite (Rmult_comm _ r) ((Rmult_comm (r + b))).
      rewrite -!(Rmult_assoc r).
      destruct r; first lia.
      rewrite !Nat.add_succ_l !Nat.sub_succ !Nat.sub_0_r.
      rewrite (Rmult_comm _ (S r + b)) !Rdiv_def -!Rmult_assoc.
      simpl_expr.
      rewrite -!Rmult_assoc.
      simpl_expr.
      rewrite (Rmult_comm _ (S r + b)) -plus_INR -!mult_INR Nat.add_succ_l -!fact_simpl //.
    - rewrite (Rmult_comm (b / (r + b))) !Rdiv_def !(Rmult_assoc (choose n (S k))).
      simpl_expr.
      simpl.
      replace (n - S k + S b)%nat with (n - k + b)%nat; last first.
      {
        pose proof (fin_to_nat_lt k).
        lia.
      }
      unfold Beta.
      simpl.
      rewrite !Nat.sub_0_r.
      simpl_expr.
      rewrite -!Rmult_assoc.
      simpl_expr.
      rewrite (Rmult_comm _ b) -!Rmult_assoc.
      assert (0 < fact (r - 1) * fact b * / fact (r + S b - 1)). {
        simpl_expr.
      }
      simpl_expr.
      rewrite (Rmult_comm b) !Rmult_assoc.
      simpl_expr.
      rewrite (Rmult_comm b) !Rmult_assoc.
      simpl_expr.
      rewrite -!Rmult_assoc (Rmult_comm _ b) -!Rmult_assoc.
      destruct b; first lia.

      rewrite -mult_INR !S_INR /= Nat.sub_0_r.
      simpl_expr.
      rewrite (Rmult_comm _ (r + (b + 1))) -!Rmult_assoc.
      simpl_expr.
      rewrite -!Nat.add_sub_assoc //= Nat.sub_0_r -INR_1 -!plus_INR -!mult_INR Nat.add_1_r Nat.add_succ_r Nat.mul_comm //=.
  Qed.

  Lemma polya_0_b (black n : nat) :
    (black > 0)%nat →
    [[{True}]]
      polya #() #0 #black #n
    [[{RET #0; True}]].
  Proof.
    iInduction n as [|n] "IH" forall (black).
    - iIntros "%Hb %Φ _ HΦ".
      unfold polya.
      wp_pures.
      by iApply "HΦ".
    - iIntros "%Hb %Φ _ HΦ".
      unfold polya.
      wp_pures.
      fold polya.
      rewrite Z.add_0_l.
      replace (black - 1)%Z with ((black - 1)%nat : Z) by lia.
      wp_apply (bernoulli_0 with "[$]") as "_".
      wp_pures.
      replace (S n - 1)%Z with (n : Z) by lia.
      rewrite Z.add_1_r -Nat2Z.inj_succ.
      iApply "IH"; done.
  Qed.

  Lemma polya_r_0 (red n : nat) :
    (red > 0)%nat →
    [[{True}]]
      polya #() #red #0 #n
    [[{RET #n; True}]].
  Proof.
    iInduction n as [|n] "IH" forall (red).
    - iIntros "%Hr %Φ _ HΦ".
      unfold polya.
      wp_pures.
      by iApply "HΦ".
    - iIntros "%Hr %Φ _ HΦ".
      unfold polya.
      wp_pures.
      fold polya.
      destruct red; first lia.
      replace (S red + 0 - 1)%Z with (red : Z) by lia.
      wp_apply (bernoulli_1 with "[$]") as "_".
      wp_pures.
      replace (S n - 1)%Z with (n : Z) by lia.
      rewrite Z.add_1_r -Nat2Z.inj_succ.
      wp_apply "IH" as "_" => //.
      wp_pures. 
      rewrite Z.add_1_l -Nat2Z.inj_succ.
      iApply ("HΦ" with "[$]").
  Qed.
  
  Lemma polya_spec (red black n : nat) (E : fin (S n) → R) (ε : R) :
    (red + black > 0)%nat →
    (∀ k, E k >= 0) →
    ε = (SeriesC (fun k : fin (S n) => Beta_prob red black n k * E k )%R) →
    [[{
      ↯ ε
    }]]
    polya #() #red #black #n
    [[{
      (v : fin (S n)), RET #v; 
      ↯ (E v)
    }]].
  Proof.
    iIntros "%H_red_black_gt_0 %HE_nonneg %Heq %Φ Herr HΦ".
    destruct (decide (red = 0)%nat) as [-> | Hr_not_0].
    {
      rewrite Series_fin_first in Heq.
      subst.
      iPoseProof (ec_split with "Herr") as "[Herr _]".
      { add_hint Beta_prob_pos. done. }
      { add_hint Beta_prob_pos.
        apply SeriesC_ge_0' => k //. }
      rewrite /Beta_prob choose_n_0 !Beta_0_l.
      wp_apply polya_0_b as "_" => //.
      iApply ("HΦ" $! 0%fin with "[Herr]").
      iApply (ec_eq with "Herr") => //=.
    }
    destruct (decide (black = 0)%nat) as [-> | Hb_not_0].
    {
       (* !fin_to_nat_to_fin choose_n_n Nat.sub_diag !Beta_0_r Rmult_1_l Rdiv_diag // Rmult_1_l *)
      rewrite Series_fin_last in Heq.
      subst.
      iPoseProof (ec_split with "Herr") as "[_ Herr]".
      { add_hint Beta_prob_pos.
        apply SeriesC_ge_0' => k //. }
      { add_hint Beta_prob_pos.
        done. }
      wp_apply polya_r_0 as "_" => //.
      assert (n = (fin_to_nat (nat_to_fin (Nat.lt_succ_diag_r n)))) as Heqn by rewrite fin_to_nat_to_fin //.
      rewrite ->Heqn at 2.
      iApply ("HΦ" with "[Herr]").
      rewrite /Beta_prob !fin_to_nat_to_fin choose_n_n Nat.sub_diag !Beta_0_r.
      iApply (ec_eq with "Herr") => //=.
    }
    (* It is easier to prove with E : nat → R, as induction on R can mess with the types, but still requiring E : fin (S n) → R can be interesting, to discuss *)
    rename E into E', HE_nonneg into HE'_nonneg, Heq into Heq'.
    pose E k := if Nat.lt_dec k (S n) is left pf
                then E' (((Fin.of_nat_lt pf)))
                else 1%R.
    assert (HE_nonneg : ∀ k : nat, E k >= 0).
    { move=>k. unfold E. real_solver. }
    iAssert (∀ v : fin (S n), ↯ (E v) -∗ Φ #v)%I with "[HΦ]" as "HΦ".
    { iIntros "%v Herr".
      unfold E.
      iApply "HΦ".
      destruct (Nat.lt_dec v (S n)); last cred_contra.
      rewrite nat_to_fin_to_nat //. }
    assert (ε = SeriesC (λ x : fin (S n), choose n x * Beta (x + red) (n - x + black) / Beta red black * E x)) as Heq. {
      rewrite Heq'.
      apply SeriesC_ext => k.
      simpl_expr.
      pose proof (fin_to_nat_lt k).
      unfold E.
      destruct (Nat.lt_dec k (S n)); last lia.
      rewrite nat_to_fin_to_nat //. }
    clearbody E.
    clear Heq' E' HE'_nonneg.

    (* Here starts the proof *)
    iInduction n as [|n] "IH" forall (E HE_nonneg red Hr_not_0 black Hb_not_0 ε H_red_black_gt_0 Heq Φ).
    - unfold polya. wp_pures.
      rewrite SeriesC_finite_foldr /= in Heq.
      rewrite choose_n_0 Rmult_1_l in Heq.
      add_hint Beta_pos.
      rewrite Rdiv_diag // Rplus_0_r Rmult_1_l in Heq.
      rewrite Heq.
      iApply ("HΦ" $! 0%fin with "[$Herr]").
    - wp_rec. wp_pures.
      rewrite -Nat2Z.inj_add.
      rewrite Beta_sum_split in Heq; [|done..].
      match type of Heq with 
      | _ = (_ * ?A) + (_ * ?B) => 
        set ε2 := A;
        set ε1 := B;
        fold ε1 ε2 in Heq
      end.
      replace ((red + black)%nat - 1)%Z with ((red + black - 1)%nat : Z) by lia.
      wp_apply (twp_bernoulli_scale _ _ ε ε1 ε2 with "Herr") as "% [[-> Herr]| [-> Herr]]".
      { lia. }
      { unfold ε1. 
        apply SeriesC_ge_0, ex_seriesC_finite => k.
        add_hint Beta_prob_pos.
        real_solver. }
      { unfold ε2. 
        apply SeriesC_ge_0, ex_seriesC_finite => k.
        add_hint Beta_prob_pos.
        real_solver. }
      { assert (INR red + INR black ≠ 0). 
        { rewrite -plus_INR. change 0 with (INR 0).
          apply not_INR.
          lia. }
        replace (S (red + black - 1))%nat with (red + black)%nat by lia.
        rewrite Heq Rplus_comm (Rmult_comm ε2 _) (Rmult_comm ε1 _) plus_INR.
        simpl_expr.
        rewrite Rmult_plus_distr_l.
        simpl_expr. }
      + wp_pures.
        rewrite Z.add_1_r -Nat2Z.inj_succ.
        rewrite Z.sub_1_r (Nat2Z.inj_succ n) Z.pred_succ.
        wp_apply ("IH" $! E HE_nonneg with "[] [] [] [] Herr") as "%v [%Hv_le_n Herr]".
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        { iPureIntro. subst ε1.
          apply SeriesC_ext => k.
          rewrite fin_S_inj_to_nat //. }
        rewrite fin_S_inj_to_nat.
        iApply ("HΦ" with "[$Herr]").
      + wp_pures.
        rewrite Z.add_1_r -Nat2Z.inj_succ.
        rewrite Z.sub_1_r (Nat2Z.inj_succ n) Z.pred_succ.
        wp_apply ("IH" $! (E ∘ S) with "[] [] [] [] [] Herr") as "%v Herr".
        { real_solver. }
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        { iPureIntro. subst ε2.
          apply SeriesC_ext => k.
          fold (Beta_prob (S red) black n k).
          simpl_expr. }
        wp_pures.
        rewrite Z.add_1_l -Nat2Z.inj_succ.
        rewrite -fin_to_nat_FS.
        iApply ("HΦ" with "[Herr]").
        rewrite fin_to_nat_FS //.
  Qed.

  Inductive fin_list (A : Type) : nat → Type :=
  | fin_nil : fin_list A 0
  | fin_cons {n : nat} : A → fin_list A n → fin_list A (S n).

  Inductive triangle (A : Type) : nat → Type :=
  | trig_nil : triangle A 0
  | trig_snoc {n : nat} : triangle A n → fin_list A (S n) → triangle A (S n).

  Arguments fin_nil {A}.
  Arguments fin_cons {A} {n}.
  Arguments trig_nil {A}.
  Arguments trig_snoc {A} {n}.

  Definition fin_list_0_inv
    {A : Type}
    (P : fin_list A 0 → Type)
    (H : P fin_nil)
    (l : fin_list A 0) : P l :=
    match l as l0 in (fin_list _ 0) return
          ∀ (P : fin_list A 0 → Type),
            P fin_nil →
            P l0
    with
    | fin_nil => λ P H, H 
    end P H.
  
  Definition fin_list_S_inv
    {n : nat} {A : Type}
    (P : fin_list A (S n) → Type)
    (f : ∀ (a : A) (l : fin_list A n), P (fin_cons a l))
    (l : fin_list A (S n)) : P l :=
    match l as l0 in (fin_list _ (S n0)) return
          ∀ (P : fin_list A (S n0) → Type)
            (f : ∀ (a : A) (l : fin_list A n0), P (fin_cons a l)),
            P l0
    with
    | fin_cons n0 a l => λ P f, f a l
    end P f.

  Definition triangle_0_inv
    {A : Type}
    (P : triangle A 0 → Type)
    (H : P trig_nil)
    (t : triangle A 0) : P t :=
    match t as t0 in (triangle _ 0) return
          ∀ (P : triangle A 0 → Type),
            P trig_nil →
            P t0
    with
    | trig_nil => λ P H, H 
    end P H.
  
  Definition triangle_S_inv
    {n : nat} {A : Type}
    (P : triangle A (S n) → Type)
    (f : ∀ (t : triangle A n) (l : fin_list A (S n)), P (trig_snoc t l))
    (l : triangle A (S n)) : P l :=
    match l as l0 in (triangle _ (S n0)) return
          ∀ (P : triangle A (S n0) → Type)
            (f : ∀ (t : triangle A n0) (l : fin_list A (S n0)), P (trig_snoc t l)),
            P l0
    with
    | trig_snoc n0 t l => λ P f, f t l
    end P f.

  Ltac inv_fin_list l :=
  let T := type of l in
  match eval hnf in T with
  | fin_list _ ?n =>
    match eval hnf in n with
    | 0%nat =>
      generalize dependent l;
      match goal with |- ∀ l, @?P l => apply (fin_list_0_inv P) end
    | S ?n =>
      generalize dependent l;
      match goal with |- ∀ l, @?P l => apply (fin_list_S_inv P) end
    end
  end.

  Ltac inv_triangle t :=
  let T := type of t in
  match eval hnf in T with
  | triangle _ ?n =>
    match eval hnf in n with
    | 0%nat =>
      generalize dependent t;
      match goal with |- ∀ t, @?P t => apply (triangle_0_inv P) end
    | S ?n =>
      generalize dependent t;
      match goal with |- ∀ t, @?P t => apply (triangle_S_inv P) end
    end
  end.

  Definition fin_list_head {A : Type} {n : nat} : fin_list A (S n) → A :=
    fin_list_S_inv (const A) const.

  Definition fin_list_tail {A : Type} {n : nat} : fin_list A (S n) → fin_list A n :=
    fin_list_S_inv (const (fin_list A n)) (flip const).

  Lemma fin_list_cons_head_tail : ∀ {A : Type} {n : nat} (l : fin_list A (S n)),
    l = fin_cons (fin_list_head l) (fin_list_tail l).
  Proof.
    move=>A n l.
    inv_fin_list l => a l //.
  Qed.

  Lemma fin_list_head_cons : ∀ {A : Type} {n : nat} (h : A) (t : fin_list A n),
    fin_list_head (fin_cons h t) = h.
  Proof.
    trivial.
  Qed.

  Lemma fin_list_tail_cons : ∀ {A : Type} {n : nat} (h : A) (t : fin_list A n),
    fin_list_tail (fin_cons h t) = t.
  Proof.
    trivial.
  Qed.
  
  Fixpoint fin_list_snoc {A : Type} {n : nat} : fin_list A n → A → fin_list A (S n) :=
    match n as n0 return fin_list A n0 → A → fin_list A (S n0) with
    | 0 => λ l a, fin_cons a l
    | S m => λ l a, fin_list_S_inv (const (fin_list A (S (S m))))
                      (λ h t, fin_cons h (fin_list_snoc t a))
                      l

    end.
  
  Fixpoint fin_list_last {A : Type} {n : nat} : fin_list A (S n) → A :=
    match n as n0 return fin_list A (S n0) → A with
    | 0 => fin_list_head
    | S m => fin_list_last ∘ fin_list_tail
    end.

  Fixpoint fin_list_liat {A : Type} {n : nat} : fin_list A (S n) → fin_list A n :=
    match n as n0 return fin_list A (S n0) → fin_list A n0 with
    | 0 => fin_list_tail
    | S m => fin_list_S_inv (const (fin_list A (S m))) (λ h t, fin_cons h (fin_list_liat t))
    end.
  
  Lemma fin_list_snoc_liat_last :
    ∀ {A : Type} {n : nat} (l : fin_list A (S n)),
    l = fin_list_snoc (fin_list_liat l) (fin_list_last l).
  Proof.
    move=>A.
    elim=>[|n IH] l; inv_fin_list l => a l //=.
    rewrite -IH //.
  Qed.

  Lemma fin_list_last_snoc :
    ∀ {A : Type} {n : nat} (h : A) (t : fin_list A n),
    fin_list_last (fin_list_snoc t h) = h.
  Proof.
    move=>A.
    elim=>[|n IH] h t; inv_fin_list t => //=.
  Qed.

  Lemma fin_list_liat_snoc :
    ∀ {A : Type} {n : nat} (h : A) (t : fin_list A n),
    fin_list_liat (fin_list_snoc t h) = t.
  Proof.
    move=>A.
    elim=>[|n IH] h t; inv_fin_list t => //=.
    move=>a l.
    rewrite IH //.
  Qed.

  Lemma fin_list_head_snoc : ∀ {A : Type} {n : nat} (h : A) (t : fin_list A (S n)),
    fin_list_head (fin_list_snoc t h) = fin_list_head t.
  Proof.
    move=>A n h t.
    by inv_fin_list t.
  Qed.

  #[global] Opaque fin_list_snoc fin_list_last fin_list_liat.
  
  Fixpoint fin_list_get {A : Type} {n : nat} : fin_list A n → fin n → A :=
    match n as n0 return fin_list A n0 → fin n0 → A with
    | 0 => λ _, fin_0_inv _
    | S m => λ l i,
               fin_list_S_inv (const A)
                 (λ h t,
                    fin_S_inv (const A) h (λ j, fin_list_get t j) i) l
    end.
  
  Fixpoint fin_list_set {A : Type} {n : nat} : fin_list A n → fin n → A → fin_list A n :=
     match n as n0 return fin_list A n0 → fin n0 → A → fin_list A n0 with
     | 0 => λ _, fin_0_inv _
     | S m => λ l i a, fin_list_S_inv (const (fin_list A (S m)))
                         (λ h t,
                            fin_S_inv (const (fin_list A (S m)))
                              (fin_cons a t)
                              (λ j, fin_cons h (fin_list_set t j a)) i)
                         l
     end.

  Lemma fin_list_get_set :
    ∀ {A : Type} {n : nat} (l : fin_list A n) (i : fin n) (a : A),
    fin_list_get (fin_list_set l i a) i = a.
  Proof.
    move=>A.
    elim=>[|n IH] l i a; inv_fin i => [|i]; inv_fin_list l => //=.
  Qed.

  Lemma fin_list_set_get :
    ∀ {A : Type} {n : nat} (l : fin_list A n) (i : fin n),
    fin_list_set l i (fin_list_get l i) = l.
  Proof.
    move=>A.
    elim=>[|n IH] l i ; inv_fin i => [|i]; inv_fin_list l => //= a l.
    rewrite IH //.
  Qed.
  
  Fixpoint triangle_top {A : Type} {n : nat} : triangle A n → fin_list A n :=
    match n as n0 return triangle A n0 → fin_list A n0 with
    | 0 => const fin_nil
    | S m => triangle_S_inv (const (fin_list A (S m)))
               (λ t l, fin_list_snoc (triangle_top t) (fin_list_head l))
    end.

  Fixpoint triangle_bottom {A : Type} {n : nat} : triangle A n → fin_list A n :=
    match n as n0 return triangle A n0 → fin_list A n0 with
    | 0 => const fin_nil
    | S m => triangle_S_inv (const (fin_list A (S m)))
               (λ t l, fin_list_snoc (triangle_bottom t) (fin_list_last l))
    end.

  Fixpoint triangle_glue_top {A : Type} {n : nat} : triangle A n → fin_list A (S n) → triangle A (S n) :=
    match n as n0 return triangle A n0 → fin_list A (S n0) → triangle A (S n0) with
    | 0 => trig_snoc
    | S m => λ t l, triangle_S_inv (const (triangle A (S (S m))))
                      (λ t' l',
                           trig_snoc (triangle_glue_top t' (fin_list_liat l)) (fin_cons (fin_list_last l) l')
                      ) t
    end.

  Fixpoint triangle_glue_bottom {A : Type} {n : nat} : triangle A n → fin_list A (S n) → triangle A (S n) :=
    match n as n0 return triangle A n0 → fin_list A (S n0) → triangle A (S n0) with
    | 0 => trig_snoc
    | S m => λ t l, triangle_S_inv (const (triangle A (S (S m))))
                      (λ t' l',
                           trig_snoc (triangle_glue_bottom t' (fin_list_liat l)) (fin_list_snoc l' (fin_list_last l))
                      ) t
    end.

  Fixpoint triangle_remove_top {A : Type} {n : nat} : triangle A (S n) → triangle A n :=
    match n as n0 return triangle A (S n0) → triangle A n0 with
    | 0 => const trig_nil
    | S m => triangle_S_inv (const (triangle A (S m)))
               (λ t' l,
                  trig_snoc (triangle_remove_top t') (fin_list_tail l))
    end.

  Fixpoint triangle_remove_bottom {A : Type} {n : nat} : triangle A (S n) → triangle A n :=
    match n as n0 return triangle A (S n0) → triangle A n0 with
    | 0 => const trig_nil
    | S m => triangle_S_inv (const (triangle A (S m)))
               (λ t' l,
                  trig_snoc (triangle_remove_bottom t') (fin_list_liat l))
    end.

  Lemma triangle_glue_remove_top :
    ∀ {A : Type} {n : nat} (t : triangle A (S n)),
    t = triangle_glue_top (triangle_remove_top t) (triangle_top t).
  Proof.
    move=>A.
    elim=>[|n IH] t; inv_triangle t => t l.
    - inv_triangle t.
      inv_fin_list l.
      move=>a l.
      by inv_fin_list l.
    - inv_triangle t => t l'.
      simpl.
      rewrite fin_list_liat_snoc.
      rewrite -IH fin_list_last_snoc -fin_list_cons_head_tail //.
  Qed.

  Lemma triangle_glue_remove_bottom :
    ∀ {A : Type} {n : nat} (t : triangle A (S n)),
    t = triangle_glue_bottom (triangle_remove_bottom t) (triangle_bottom t).
  Proof.
    move=>A.
    elim=>[|n IH] t; inv_triangle t => t l.
    - inv_triangle t.
      inv_fin_list l.
      move=>a l.
      by inv_fin_list l.
    - inv_triangle t => t l'.
      simpl.
      rewrite fin_list_liat_snoc.
      rewrite -IH fin_list_last_snoc -fin_list_snoc_liat_last //.
  Qed.

  Lemma triangle_remove_glue_top :
    ∀ {A : Type} {n : nat} (t : triangle A n) (l : fin_list A (S n)),
    triangle_remove_top (triangle_glue_top t l) = t.
  Proof.
    move=>A.
    elim=>[|n IH] t l; inv_triangle t => //= t l'.
    rewrite IH //.
  Qed.

  Lemma triangle_remove_glue_bottom :
    ∀ {A : Type} {n : nat} (t : triangle A n) (l : fin_list A (S n)),
    triangle_remove_bottom (triangle_glue_bottom t l) = t.
  Proof.
    move=>A.
    elim=>[|n IH] t l; inv_triangle t => //= t l'.
    rewrite IH fin_list_liat_snoc //.
  Qed.

  Lemma triangle_top_glue :
    ∀ {A : Type} {n : nat} (t : triangle A n) (l : fin_list A (S n)),
    triangle_top (triangle_glue_top t l) = l.
  Proof.
    move=>A.
    elim=>[|n /= IH] t l; inv_triangle t.
    { inv_fin_list l => a l /=.
      by inv_fin_list l.
    }
    move=>t l' /=.
    rewrite IH -fin_list_snoc_liat_last //.
  Qed.

  Lemma triangle_bottom_glue :
    ∀ {A : Type} {n : nat} (t : triangle A n) (l : fin_list A (S n)),
    triangle_bottom (triangle_glue_bottom t l) = l.
  Proof.
    move=>A.
    elim=>[|n /= IH] t l; inv_triangle t.
    { inv_fin_list l => a l /=.
      by inv_fin_list l.
    }
    move=>t l' /=.
    rewrite IH fin_list_last_snoc -fin_list_snoc_liat_last //.
  Qed.

  Lemma triangle_top_bottom_first :
    ∀ {A : Type} {n : nat} (t : triangle A (S n)),
    fin_list_head (triangle_top t) = fin_list_head (triangle_bottom t).
  Proof.
    move=>A.
    elim=>[|n IH] t; inv_triangle t => t l //=.
    rewrite !fin_list_head_snoc IH //.
  Qed.
    
  #[global] Opaque
    triangle_top
    triangle_bottom
    triangle_remove_top
    triangle_remove_bottom
    triangle_glue_top
    triangle_glue_bottom.
  
  Fixpoint triangle_column {A : Type} {n : nat} : triangle A n → ∀ (i : fin n), fin_list A (FS i)%nat :=
  match n as n0 return triangle A n0 → ∀ (i : fin n0), fin_list A (FS i)%nat with
  | 0 => λ _, fin_0_inv _
  | S m => λ t i,
             fin_S_inv (fin_list A ∘ FS)
               (fin_cons
                  (fin_list_head (triangle_top t))
                  fin_nil)
               (λ j,
                  fin_cons
                    (fin_list_get
                       (triangle_top t)
                       (FS j)
                    )
                    (triangle_column (triangle_remove_top t) j)
               )
               i
  end.

  Fixpoint triangle_row {A : Type} {n : nat} : triangle A n → ∀ (i : fin n), fin_list A (n - i)%nat :=
  match n as n0 return triangle A n0 → ∀ (i : fin n0), fin_list A (n0 - i)%nat with
  | 0 => λ _, fin_0_inv _
  | S m => λ t i,
             fin_S_inv (λ i, fin_list A (S m - i))
               (triangle_top t)
               (triangle_row (triangle_remove_top t))
               i
  end.

  Definition triangle_get {A : Type} {n : nat} (t : triangle A n) (i : fin n) (j : fin (FS i)) : A :=
    fin_list_get (triangle_column t i) j.

  (** A β_tape has a list at each pair of coordinates (k,i)
      for k the number of balls drawn so far and i the number
      of red balls seen while doing so.

      So a β_tape might look something like this
      (a star represents there being a list) :

     i\k 0 1 2 3 4 5
     0   * * * * * * 
     1     * * * * *
     2       * * * *
     3         * * *
     4           * *
     5             *

   **)
  
  Definition β_tape := triangle (list (fin 2)).

  Fixpoint β_empty_list {n : nat} : fin_list (list (fin 2)) n :=
    match n as n0 return fin_list (list (fin 2)) n0 with
    | 0 => fin_nil
    | S m => fin_cons [] β_empty_list
    end.
  
  Fixpoint β_empty {n : nat} : β_tape n :=
    match n as n0 return β_tape n0 with
    | 0 => trig_nil
    | S m => trig_snoc β_empty β_empty_list
    end.

  Lemma β_empty_list_cons_snoc : ∀ {n : nat}, fin_list_snoc (@β_empty_list n) [] = fin_cons [] β_empty_list.
  Proof.
    elim=>[|n IH] //=.
    rewrite -{2}IH //.
  Qed.
    
  Lemma β_empty_top : ∀ {n : nat}, triangle_top (@β_empty n) = β_empty_list.
  Proof.
    elim=>[|n IH] //=.
    cbv [triangle_top].
    simpl.
    cbv [triangle_top] in IH.
    rewrite IH.
    apply β_empty_list_cons_snoc.
  Qed.
  
  Definition tl_error {A : Type} (l : list A) : option (list A) :=
    match l with
    | [] => None
    | _::t => Some t
    end.
   
  Definition β_list_push_first {n : nat}
    (l : fin_list (list (fin 2)) (S n)) (v : fin 2) : fin_list (list (fin 2)) (S n)
    :=
    fin_list_S_inv (const (fin_list (list (fin 2)) (S n)))
      (λ hd tl, fin_cons (v::hd) tl)
      l.

  Definition β_list_pop_first {n : nat}
    (l : fin_list (list (fin 2)) (S n))
    : option (fin_list (list (fin 2)) (S n))
    :=
    fin_list_S_inv (const (option (fin_list (list (fin 2)) (S n))))
      (λ hd tl,
         hd' ← tl_error hd ;
         Some (fin_cons hd' tl))
      l.

  Definition β_list_head_first {n : nat}
    (l : fin_list (list (fin 2)) (S n)) : option (fin 2) := 
      head (fin_list_head l)
  .
  
  Lemma β_list_push_pop_first {n : nat} :
    ∀ (l : fin_list (list (fin 2)) (S n))
      (v : fin 2),
    β_list_pop_first (β_list_push_first l v) = Some l.
  Proof.
    move=>l v.
    by inv_fin_list l.
  Qed.

  Lemma β_list_push_head_first {n : nat} :
    ∀ (l : fin_list (list (fin 2)) (S n))
      (v : fin 2),
    β_list_head_first (β_list_push_first l v) = Some v.
  Proof.
    move=>l v.
    by inv_fin_list l.
  Qed.

  Lemma β_list_head_first_top_bottom {n : nat} :
    ∀ (t : β_tape (S n)), β_list_head_first (triangle_top t) = β_list_head_first (triangle_bottom t).
  Proof.
    move=>t.
    unfold β_list_head_first.
    f_equal.
    apply triangle_top_bottom_first.
  Qed.
    
  Lemma β_list_push_first_fin_head {n : nat} :
    ∀ (l : fin_list (list (fin 2)) (S n))
      (v : fin 2),
    fin_list_head (β_list_push_first l v) = v::fin_list_head l.
  Proof.
    move=>l v.
    by inv_fin_list l.
  Qed.

  #[local] Opaque
   β_list_push_first
   β_list_pop_first
   β_list_head_first.
  
  Fixpoint β_push {n : nat} : β_tape n → fin (S n) → β_tape n :=
      match n as n0 return β_tape n0 → fin (S n0) → β_tape n0 with
      | 0 => λ _ _, trig_nil
      | S m => λ t i,
                 fin_S_inv (const (β_tape (S m)))
                   (triangle_glue_bottom
                      (β_push (triangle_remove_bottom t) 0%fin)
                      (β_list_push_first (triangle_bottom t) 0%fin)
                   )
                   (λ j,
                      triangle_glue_top
                        (β_push (triangle_remove_top t) j)
                        (β_list_push_first (triangle_top t) 1%fin)
                   )
                   i
      end.

  Lemma β_push_length_first_top {n : nat} :
    ∀ (t : β_tape (S n))
      (v : fin (S (S n))),
    length (fin_list_head (triangle_top (β_push t v))) =
    S (length (fin_list_head (triangle_top t))).
  Proof.
    move=>t v.
    inv_fin v => [|i] /=.
    - rewrite !triangle_top_bottom_first triangle_bottom_glue β_list_push_first_fin_head //.
    - rewrite triangle_top_glue β_list_push_first_fin_head //.
  Qed.
  
  Definition β_encode {n : nat} : list (fin (S n)) → β_tape n :=
    foldr (flip β_push) β_empty.

  Definition β_first {n : nat} (t : β_tape (S n)) : option (fin 2) :=
    β_list_head_first (triangle_top t).
  
  Fixpoint β_head {n : nat} : β_tape n → option (fin (S n)) :=
      match n as n0 return β_tape n0 → option (fin (S n0)) with
      | 0 => λ _, Some 0%fin
      | S m => λ t,
                 v ← β_first t ;
                 match v with
                 | 0%fin => fin_S_inj <$> β_head (triangle_remove_bottom t)
                 | _ => FS <$> β_head (triangle_remove_top t)
                 end
  end.

  Fixpoint β_pop {n : nat} : β_tape n → option (β_tape n) :=
      match n as n0 return β_tape n0 → option (β_tape n0) with
      | 0 => λ _, Some β_empty
      | S m => λ t,
                 v ← β_first t ;
                 match v with
                 | 0%fin =>
                     l' ← β_list_pop_first (triangle_bottom t);
                     t' ← β_pop $ triangle_remove_bottom t;
                     Some (triangle_glue_bottom t' l')
                                 
                 | _ =>
                     l' ← β_list_pop_first (triangle_top t);
                     t' ← β_pop $ triangle_remove_top t;
                     Some (triangle_glue_top t' l')
                 end
  end.

  Definition β_split {n : nat} (t : β_tape n) : option (fin (S n) * β_tape n) :=
    h ← β_head t ;
    t' ← β_pop t;
    Some (h, t').

  Fixpoint β_decode_k {n : nat} (t : β_tape n) (k : nat) : option (list (fin (S n))) :=
    match k with
    | 0 => Some []
    | S k' => '(hd, t') ← β_split t ;
               tl ← β_decode_k t' k' ;
               Some (hd::tl)
  end.

  Definition β_decode {n : nat} : β_tape n → option (list (fin (S n))) :=
    match n as n0 return β_tape n0 → option (list (fin (S n0))) with
    | 0 => const (Some [])
    | S m => λ t, β_decode_k t (length $ fin_list_head $ triangle_top t)
    end.
  
  Lemma β_push_head :
    ∀ {n : nat} (t : β_tape n) (v : fin (S n)),
    β_head (β_push t v) = Some v.
  Proof.
    elim=>[|n IH] t v; first by full_inv_fin.
    inv_fin v => [|i].
    - simpl.
      unfold β_first.
      rewrite β_list_head_first_top_bottom triangle_bottom_glue β_list_push_head_first /= triangle_remove_glue_bottom IH //.
    - simpl.
      unfold β_first.
      rewrite triangle_top_glue β_list_push_head_first /= triangle_remove_glue_top IH //.
  Qed.

   Lemma β_push_pop :
    ∀ {n : nat} (t : β_tape n) (v : fin (S n)),
    β_pop (β_push t v) = Some t.
  Proof.
    elim=>[|n IH] t v; first by (full_inv_fin; inv_triangle t).
    inv_fin v => [|i].
    - simpl.
      unfold β_first.
      rewrite β_list_head_first_top_bottom triangle_bottom_glue β_list_push_head_first /= triangle_remove_glue_bottom IH β_list_push_pop_first /= -triangle_glue_remove_bottom //.
    - simpl.
      unfold β_first.
      rewrite triangle_top_glue β_list_push_head_first /= triangle_remove_glue_top IH β_list_push_pop_first /= -triangle_glue_remove_top //.
  Qed.

  Lemma β_push_split :
    ∀ {n : nat} (t : β_tape n) (v : fin (S n)),
    β_split (β_push t v) = Some (v, t).
  Proof.
    move=> n t v.
    unfold β_split.
    rewrite β_push_head /= β_push_pop //.
  Qed.
  
  Lemma β_encode_decode :
    ∀ {n : nat} (l : list (fin (S (S n)))),
    β_decode (β_encode l) = Some l.
  Proof.
    move=>n.
    elim=>[|h t IH] /=.
    - rewrite β_empty_top //.
    - rewrite β_push_length_first_top /= β_push_split /=.
      unfold β_decode in IH.
      rewrite IH //=.
  Qed.

  Definition is_abs_loc (n : nat) (α : val) (Δ : triangle loc n) :=
    ∀ (i : fin n) (j : fin (S i)),
    ⊢ WP α #i #j [{ v, ⌜v = #(triangle_get Δ i j)⌝ }].

  Definition own_polya_tape
    {n : nat}
    (p q : nat)
    (Δ : triangle loc n)
    (l : list (fin (S n)))
    := (∃ (τ : β_tape n),
           ⌜β_decode τ = Some l⌝ ∗
           ([∗ list] i ∈ fin_enum n,
              [∗ list] j ∈ fin_enum (S i),
                own_bernoulli_tape
                  (triangle_get Δ i j)
                  (p + j)%nat
                  (q + i)
                  (triangle_get τ i j)
           )
       )%I. 
  
End Polya.
