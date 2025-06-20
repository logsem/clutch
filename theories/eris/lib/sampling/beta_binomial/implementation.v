From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils.
From clutch.eris.lib.sampling.bernoulli Require Import interface.
From clutch.eris.lib.sampling.binomial Require Import interface.

Section Polya.
  
  Set Default Proof Using "Type*".
  Context `{!erisGS Σ}.
  Context `{!bernoulli_spec bernoulli balloc}.

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
  
  Definition polyalloc_row : val :=
    rec: "polyalloc_row" "red" "black" "n" :=
      if: "n" = #0 then (λ: "x", "x")
      else
        let: "α0" := balloc "red" ("red" + "black") in
        let: "α" := "polyalloc_row" "red" ("black" + #1) ("n" - #1) in
        (λ: "i",
           if: "i" = #0
           then "α0"
           else "α" ("i" - #1)
        ).
  
  Definition polyalloc : val :=
      rec: "polyalloc" "red" "black" "n" :=
      if: "n" = #0 then (λ: "x", "x")
      else
        let: "αr" := polyalloc_row "red" "black" "n" in
        let: "α" := "polyalloc" ("red" + #1) "black" ("n" - #1) in
        (λ: "i" "j",
           if: "j" = #0
           then "αr" "i"
           else "α" "i" ("j" - #1))
  .
  
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

  Lemma triangle_0_nil : ∀ (A : Type) (τ : triangle A 0), τ = trig_nil.
  Proof.
    move=>A τ.
    by inv_triangle τ.
  Qed.
  
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
    | S m => λ l a, fin_cons (fin_list_head l) (fin_list_snoc (fin_list_tail l) a)
                    

    end.
  
  Fixpoint fin_list_last {A : Type} {n : nat} : fin_list A (S n) → A :=
    match n as n0 return fin_list A (S n0) → A with
    | 0 => fin_list_head
    | S m => fin_list_last ∘ fin_list_tail
    end.

  Lemma fin_list_last_tail :
    ∀ {A : Type} {n : nat} (t : fin_list A (S (S n))),
    fin_list_last (fin_list_tail t) = fin_list_last t.
  Proof.
    move=>A n t.
    inv_fin_list t => t l //.
  Qed.
  
  Fixpoint fin_list_liat {A : Type} {n : nat} : fin_list A (S n) → fin_list A n :=
    match n as n0 return fin_list A (S n0) → fin_list A n0 with
    | 0 => fin_list_tail
    | S m => λ l, fin_cons (fin_list_head l) (fin_list_liat (fin_list_tail l))
    end.
  
  Lemma fin_list_snoc_liat_last :
    ∀ {A : Type} {n : nat} (l : fin_list A (S n)),
    l = fin_list_snoc (fin_list_liat l) (fin_list_last l).
  Proof.
    move=>A.
    elim=>[|n IH] l; inv_fin_list l => a l //=.
    rewrite -IH //.
  Qed.

  Lemma fin_list_tail_snoc :
    ∀ {A : Type} {n : nat} (h : A) (t : fin_list A (S n)),
    fin_list_tail (fin_list_snoc t h) = fin_list_snoc (fin_list_tail t) h.
  Proof.
    move=>A.
    elim=>[|n IH] h t; inv_fin_list t => //.
  Qed.

  Lemma fin_list_head_liat :
    ∀ {A : Type} {n : nat} (t : fin_list A (S (S n))),
    fin_list_head (fin_list_liat t) = fin_list_head t.
  Proof.
    move=>* //.
  Qed.
    
  Lemma fin_list_last_snoc :
    ∀ {A : Type} {n : nat} (h : A) (t : fin_list A n),
    fin_list_last (fin_list_snoc t h) = h.
  Proof.
    move=>A.
    elim=>[|n IH] h t; inv_fin_list t => //=.
  Qed.

  Lemma fin_list_last_cons_S :
    ∀ {A : Type} {n : nat} (h : A) (t : fin_list A (S n)),
    fin_list_last (fin_cons h t) = fin_list_last t.
  Proof.
    move=>* //.
  Qed.
  
  Lemma fin_list_last_cons_0 :
    ∀ {A : Type} (h : A) (t : fin_list A 0),
    fin_list_last (fin_cons h t) = h.
  Proof.
    move=>* //.
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

  Lemma fin_list_liat_cons_S :
    ∀ {A : Type} {n : nat} (h : A) (t : fin_list A (S n)),
    fin_list_liat (fin_cons h t) = fin_cons h (fin_list_liat t).
  Proof.
    move=>A.
    elim=>[|n IH] h t; inv_fin_list t => //=.
  Qed.

  Lemma fin_list_liat_cons_0 :
    ∀ {A : Type} (h : A) (t : fin_list A 0),
    fin_list_liat (fin_cons h t) = fin_nil.
  Proof.
    move=>A h t /=.
    by inv_fin_list t.
  Qed.


  Lemma fin_list_cons_snoc :
    ∀ {A : Type} {n : nat} (h1 h2 : A) (t : fin_list A n),
    fin_cons h1 (fin_list_snoc t h2) = fin_list_snoc (fin_cons h1 t) h2.
  Proof.
    move=>A n h1 h2 t //.
  Qed.

  Lemma fin_list_tail_liat :
    ∀ {A : Type} {n : nat} (l : fin_list A (S (S n))),
    fin_list_tail (fin_list_liat l) = fin_list_liat (fin_list_tail l).
  Proof.
    move=>* //.
  Qed.
  
  #[global] Opaque fin_list_snoc fin_list_last fin_list_liat.
  
  Fixpoint fin_list_get {A : Type} {n : nat} : fin_list A n → fin n → A :=
    match n as n0 return fin_list A n0 → fin n0 → A with
    | 0 => λ _, fin_0_inv _
    | S m => λ l i,
               fin_S_inv (const A) (fin_list_head l) (λ j, fin_list_get (fin_list_tail l) j) i
    end.
  
  Fixpoint fin_list_set {A : Type} {n : nat} : fin_list A n → fin n → A → fin_list A n :=
     match n as n0 return fin_list A n0 → fin n0 → A → fin_list A n0 with
     | 0 => λ _, fin_0_inv _
     | S m => λ l i a, fin_S_inv (const (fin_list A (S m)))
                         (fin_cons a (fin_list_tail l))
                         (λ j, fin_cons (fin_list_head l) (fin_list_set (fin_list_tail l) j a)) i
     end.

  Lemma fin_list_get_cons_0 :
    ∀ {A : Type} {n : nat} (l : fin_list A (S n)) (a : A),
    fin_list_get (fin_cons a l) 0%fin = a.
  Proof.
    move=>* //.
  Qed.

  Lemma fin_list_get_cons_S :
    ∀ {A : Type} {n : nat} (l : fin_list A n) (a : A) (i : fin n),
    fin_list_get (fin_cons a l) (FS i)%fin = fin_list_get l i.
  Proof.
    move=>* //.
  Qed.

  Lemma fin_list_set_0 :
    ∀ {A : Type} {n : nat} (l : fin_list A (S n)) (a : A),
    fin_list_set l 0%fin a = fin_cons a (fin_list_tail l).
  Proof. reflexivity. Qed.

  Lemma fin_list_get_0 :
    ∀ {A : Type} {n : nat} (l : fin_list A (S n)),
    fin_list_get l 0%fin = fin_list_head l. 
  Proof. reflexivity. Qed.

  Lemma fin_list_get_FS :
    ∀ {A : Type} {n : nat} (l : fin_list A (S n)) (i : fin n),
    fin_list_get l (FS i) = fin_list_get (fin_list_tail l) i.
  Proof. reflexivity. Qed.

  Lemma fin_list_set_FS :
    ∀ {A : Type} {n : nat} (l : fin_list A (S n)) (i : fin n) (a : A),
    fin_list_set l (FS i) a = fin_cons (fin_list_head l) (fin_list_set (fin_list_tail l) i a).
  Proof. reflexivity. Qed.

  Lemma fin_list_get_max :
    ∀ {A : Type} {n : nat} (l : fin_list A (S n)),
    fin_list_get l (fin_max n) = fin_list_last l. 
  Proof.
    move=>A.
    elim=>[|n IH] l /=; first by inv_fin_list l.
    rewrite {3}(fin_list_cons_head_tail l) fin_list_last_cons_S -IH //.
  Qed.

  Lemma fin_list_set_max :
    ∀ {A : Type} {n : nat} (l : fin_list A (S n)) (a : A),
    fin_list_set l (fin_max n) a = fin_list_snoc (fin_list_liat l) a. 
  Proof.
    move=>A.
    elim=>[|n IH] l a /=; first by inv_fin_list l.
    rewrite {5}(fin_list_cons_head_tail l) fin_list_liat_cons_S -fin_list_cons_snoc -IH //.
  Qed.
  
  Lemma fin_list_get_set_eq :
    ∀ {A : Type} {n : nat} (l : fin_list A n) (i : fin n) (a : A),
    fin_list_get (fin_list_set l i a) i = a.
  Proof.
    move=>A.
    elim=>[|n IH] l i a; inv_fin i => [|i]; inv_fin_list l => //=.
  Qed.

  Lemma fin_list_get_set_ne :
    ∀ {A : Type} {n : nat} (l : fin_list A n) (i j : fin n) (a : A),
    i ≠ j →
    fin_list_get (fin_list_set l i a) j = fin_list_get l j.
  Proof.
    move=>A.
    elim=>[|n IH] l i j; inv_fin i => [|i] a i_ne_j; inv_fin j=>[|j] Si_ne_Sj //=.
    apply IH.
    move=> contra.
    by subst.
  Qed.
  
  Lemma fin_list_set_get :
    ∀ {A : Type} {n : nat} (l : fin_list A n) (i : fin n),
    fin_list_set l i (fin_list_get l i) = l.
  Proof.
    move=>A.
    elim=>[|n IH] l i ; inv_fin i => [|i]; inv_fin_list l => //= a l.
    rewrite IH //.
  Qed.

  Lemma fin_list_get_inj :
    ∀ {A : Type} {n : nat} (l : fin_list A (S n)) (i : fin n),
    fin_list_get l (fin_S_inj i) = fin_list_get (fin_list_liat l) i.
  Proof.
    move=>A.
    elim=>[|n IH] l i; inv_fin i.
    - inv_fin_list l => a l //.
    - move=>i /=.
      rewrite -IH //.
  Qed.
  
  Lemma fin_list_set_inj :
    ∀ {A : Type} {n : nat} (l : fin_list A (S n)) (i : fin n) (a : A),
    fin_list_set l (fin_S_inj i) a = fin_list_snoc (fin_list_set (fin_list_liat l) i a) (fin_list_last l).
  Proof.
    move=>A.
    elim=>[|n IH] l i a; inv_fin i.
    - inv_fin_list l => i l /=.
      rewrite -fin_list_cons_snoc -fin_list_snoc_liat_last //.
    - move=>i /=.
      rewrite -fin_list_cons_snoc fin_list_head_liat -IH //.
  Qed.

  Definition triangle_tail
    {A : Type} {n : nat} (t : triangle A (S n)) : fin_list A (S n) :=
    triangle_S_inv (const (fin_list A (S n))) (λ _ l, l) t.

  Definition triangle_head
    {A : Type} {n : nat} (t : triangle A (S n)) : triangle A n :=
    triangle_S_inv (const (triangle A n)) (λ h _, h) t.

  Lemma triangle_snoc_head_tail {A : Type} {n : nat} (t : triangle A (S n)) :
    t = trig_snoc (triangle_head t) (triangle_tail t).
  Proof. by inv_triangle t. Qed.

  Fixpoint triangle_top {A : Type} {n : nat} : triangle A n → fin_list A n :=
    match n as n0 return triangle A n0 → fin_list A n0 with
    | 0 => const fin_nil
    | S m => λ t,
               fin_list_snoc
                 (triangle_top (triangle_head t))
                 (fin_list_head (triangle_tail t))
    end.

  Fixpoint triangle_bottom {A : Type} {n : nat} : triangle A n → fin_list A n :=
    match n as n0 return triangle A n0 → fin_list A n0 with
    | 0 => const fin_nil
    | S m => λ t,
               fin_list_snoc
                 (triangle_bottom (triangle_head t))
                 (fin_list_last (triangle_tail t))
    end.

  Fixpoint triangle_glue_top {A : Type} {n : nat} : triangle A n → fin_list A (S n) → triangle A (S n) :=
    match n as n0 return triangle A n0 → fin_list A (S n0) → triangle A (S n0) with
    | 0 => trig_snoc
    | S m => λ t l, trig_snoc
                      (triangle_glue_top (triangle_head t) (fin_list_liat l))
                      (fin_cons (fin_list_last l) (triangle_tail t))
    end.

  Fixpoint triangle_glue_bottom {A : Type} {n : nat} : triangle A n → fin_list A (S n) → triangle A (S n) :=
    match n as n0 return triangle A n0 → fin_list A (S n0) → triangle A (S n0) with
    | 0 => trig_snoc
    | S m => λ t l, trig_snoc
                      (triangle_glue_bottom (triangle_head t) (fin_list_liat l))
                      (fin_list_snoc (triangle_tail t) (fin_list_last l))
    end.

  Fixpoint triangle_remove_top {A : Type} {n : nat} : triangle A (S n) → triangle A n :=
    match n as n0 return triangle A (S n0) → triangle A n0 with
    | 0 => const trig_nil
    | S m => λ t,
               trig_snoc
                 (triangle_remove_top (triangle_head t))
                 (fin_list_tail (triangle_tail t))
    end.

  Fixpoint triangle_remove_bottom {A : Type} {n : nat} : triangle A (S n) → triangle A n :=
    match n as n0 return triangle A (S n0) → triangle A n0 with
    | 0 => const trig_nil
    | S m => λ t,
               trig_snoc
                 (triangle_remove_bottom (triangle_head t))
                 (fin_list_liat (triangle_tail t))
    end.

  Lemma triangle_remove_top_0 :
    ∀ {A : Type} (τ : triangle A 1), triangle_remove_top τ = trig_nil.
  Proof.
    move=>A τ.
    inv_triangle τ => τ l //.
  Qed.
  
  Lemma triangle_remove_bottom_0 :
    ∀ {A : Type} (τ : triangle A 1), triangle_remove_bottom τ = trig_nil.
  Proof.
    move=>A τ.
    inv_triangle τ => τ l //.
  Qed.
  
  Lemma triangle_glue_remove_top :
    ∀ {A : Type} {n : nat} (t : triangle A (S n)),
    t = triangle_glue_top (triangle_remove_top t) (triangle_top t).
  Proof.
    move=>A.
    elim=>[|n IH] t; inv_triangle t => t l.
    - inv_triangle t.
      inv_fin_list l => a l.
      by inv_fin_list l.
    - inv_triangle t => t l' /=.
      rewrite fin_list_liat_snoc -IH fin_list_last_snoc
              -fin_list_cons_head_tail //.
  Qed.

  Lemma triangle_glue_remove_bottom :
    ∀ {A : Type} {n : nat} (t : triangle A (S n)),
    t = triangle_glue_bottom (triangle_remove_bottom t) (triangle_bottom t).
  Proof.
    move=>A.
    elim=>[|n IH] t; inv_triangle t => t l.
    - inv_triangle t.
      inv_fin_list l => a l.
      by inv_fin_list l.
    - inv_triangle t => t l' /=.
      rewrite fin_list_liat_snoc -IH fin_list_last_snoc
              -fin_list_snoc_liat_last //.
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

  Lemma triangle_remove_top_bottom : 
    ∀ {A : Type} {n : nat} (t : triangle A (S (S n))),
    triangle_remove_top (triangle_remove_bottom t) = 
    triangle_remove_bottom (triangle_remove_top t).
  Proof.
    move=>A.
    elim=>[|n IH] t; inv_triangle t => t l //=.
    rewrite IH //.
  Qed.
  
  Lemma triangle_remove_bottom_glue_top :
    ∀ {A : Type} {n : nat} (τ : triangle A (S n)) (l : fin_list A (S (S n))),
      triangle_remove_bottom (triangle_glue_top τ l) =
      triangle_glue_top (triangle_remove_bottom τ) (fin_list_tail l).
  Proof.
    move=>A.
    elim=>[|n IH] τ l.
    - inv_triangle τ => τ lτ /=.
      inv_fin_list l => a l.
      inv_fin_list l => b l.
      inv_fin_list l.
      inv_fin_list lτ => c lτ.
      rewrite fin_list_liat_cons_S fin_list_last_cons_S fin_list_last_cons_0 fin_list_liat_cons_0 //=.
    - inv_triangle τ => τ lτ /=.
      rewrite -fin_list_tail_liat -IH //.
  Qed.

  Lemma triangle_bottom_glue_top :
    ∀ {A : Type} {n : nat} (τ : triangle A (S n)) (l : fin_list A (S (S n))),
      triangle_bottom (triangle_glue_top τ l) =
      fin_cons (fin_list_head l) (triangle_bottom τ).
  Proof.
    move=>A.
    elim=>[|n IH] τ l.
    - inv_triangle τ => τ lτ /=.
      inv_fin_list l => a l.
      inv_fin_list l => b l.
      inv_fin_list l.
      inv_fin_list lτ => c lτ //.
    - inv_triangle τ => τ lτ /=.
      rewrite fin_list_cons_snoc.
      f_equal.
      rewrite -(fin_list_head_liat l) -IH //.
  Qed.

  Lemma triangle_head_glue_top : 
    ∀ {A : Type} {n : nat} (τ : triangle A (S n)) (l : fin_list A (S (S n))),
    triangle_head (triangle_glue_top τ l) = triangle_glue_top (triangle_head τ) (fin_list_liat l).
  Proof. reflexivity. Qed.

  Lemma triangle_tail_glue_top : 
    ∀ {A : Type} {n : nat} (τ : triangle A (S n)) (l : fin_list A (S (S n))),
    triangle_tail (triangle_glue_top τ l) = fin_cons (fin_list_last l) (triangle_tail τ).
  Proof. reflexivity. Qed.

   Lemma triangle_head_glue_bottom : 
    ∀ {A : Type} {n : nat} (τ : triangle A (S n)) (l : fin_list A (S (S n))),
    triangle_head (triangle_glue_bottom τ l) = triangle_glue_bottom (triangle_head τ) (fin_list_liat l).
  Proof. reflexivity. Qed.

  Lemma triangle_tail_glue_bottom : 
    ∀ {A : Type} {n : nat} (τ : triangle A (S n)) (l : fin_list A (S (S n))),
    triangle_tail (triangle_glue_bottom τ l) = fin_list_snoc (triangle_tail τ) (fin_list_last l).
  Proof. reflexivity. Qed.

  Lemma triangle_head_remove_top : 
    ∀ {A : Type} {n : nat} (τ : triangle A (S (S n))),
    triangle_head (triangle_remove_top τ) = triangle_remove_top (triangle_head τ).
  Proof. reflexivity. Qed.

  Lemma triangle_head_remove_bottom : 
    ∀ {A : Type} {n : nat} (τ : triangle A (S (S n))),
    triangle_head (triangle_remove_bottom τ) = triangle_remove_bottom (triangle_head τ).
  Proof. reflexivity. Qed.
  
  Lemma triangle_tail_remove_top : 
    ∀ {A : Type} {n : nat} (τ : triangle A (S (S n))),
    triangle_tail (triangle_remove_top τ) = fin_list_tail (triangle_tail τ).
  Proof. reflexivity. Qed.

  Lemma triangle_tail_remove_bottom : 
    ∀ {A : Type} {n : nat} (τ : triangle A (S (S n))),
    triangle_tail (triangle_remove_bottom τ) = fin_list_liat (triangle_tail τ).
  Proof. reflexivity. Qed.
  
  Lemma triangle_top_bottom_first :
    ∀ {A : Type} {n : nat} (t : triangle A (S n)),
    fin_list_head (triangle_top t) = fin_list_head (triangle_bottom t).
  Proof.
    move=>A.
    elim=>[|n IH] t; inv_triangle t => t l //=.
    rewrite !fin_list_head_snoc IH //.
  Qed.
 
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

  Lemma triangle_get_top : ∀ {A : Type} {n : nat} (t : triangle A n) (i : fin n),
    triangle_get t i 0 = fin_list_get (triangle_top t) i.
  Proof.
    move=>A [|n] t i; first inv_fin i.
    inv_triangle t => t l .
    inv_fin_list l => a l.
    inv_fin i => [|i] //=.
  Qed.

  Lemma triangle_top_split_snoc :
    ∀ {A : Type} {n : nat}
      (t : triangle A n) (l : fin_list A (S n)),
    triangle_top (trig_snoc t l) = fin_list_snoc (triangle_top t) (fin_list_head l).
  Proof. reflexivity. Qed.

  Lemma triangle_bottom_split_snoc :
    ∀ {A : Type} {n : nat}
      (t : triangle A n) (l : fin_list A (S n)),
    triangle_bottom (trig_snoc t l) = fin_list_snoc (triangle_bottom t) (fin_list_last l).
  Proof. reflexivity. Qed.

   Lemma triangle_top_last_tail_first :
    ∀ {A : Type} {n : nat}
      (t : triangle A (S n)),
    fin_list_last (triangle_top t) = fin_list_head (triangle_tail t).
  Proof.
    move=>A n t.
    rewrite {1}(triangle_snoc_head_tail t) triangle_top_split_snoc fin_list_last_snoc //.
  Qed.
  
  Lemma triangle_bottom_tail_last :
    ∀ {A : Type} {n : nat}
      (t : triangle A (S n)),
    fin_list_last (triangle_bottom t) = fin_list_last (triangle_tail t).
  Proof.
    move=>A n t.
    rewrite {1}(triangle_snoc_head_tail t) triangle_bottom_split_snoc fin_list_last_snoc //.
  Qed.


  Lemma triangle_bottom_split_cons :
    ∀ {A : Type} {n : nat}
      (t : triangle A (S n)),
    triangle_bottom t = fin_cons (fin_list_head (triangle_top t)) (triangle_bottom (triangle_remove_top t)).
  Proof.
    move=>A.
    elim=>[|n IH] t /=.
    - inv_triangle t => t l /=.
      inv_fin_list l => a l.
      inv_fin_list l => //.
    - inv_triangle t => t l /=.
      rewrite fin_list_cons_snoc fin_list_last_tail.
      f_equal.
      rewrite -IH //.
  Qed.
  
  Lemma triangle_get_bottom :
    ∀ {A : Type} {n : nat} (t : triangle A n) (i : fin n),
    triangle_get t i (nat_to_fin (Nat.lt_succ_diag_r i)) =
    fin_list_get (triangle_bottom t) i.
  Proof.
    move=>A.
    elim=>[|n IH] t i; first inv_fin i.
    destruct n.
    - inv_fin i => [|i]; last inv_fin i.
      inv_triangle t => t l /=.
      unfold triangle_get.
      simpl.
      inv_fin_list l => a l //.
    - inv_triangle t => t l.
      rewrite triangle_bottom_split_cons.
      inv_fin i => [//|i].
      simpl nat_to_fin.
      rewrite fin_list_get_cons_S -IH.
      remember (nat_to_fin _) as Hii.
      remember (nat_to_fin (Nat.lt_succ_diag_r i)) as Hi.
      replace Hii with Hi; last first.
      {
        subst.
        apply nat_to_fin_proof_ext.
      }
      done.
  Qed.

  Lemma triangle_top_remove_bottom :
     ∀ {A : Type} {n : nat} (t : triangle A (S n)),
    triangle_top (triangle_remove_bottom t) =
    fin_list_tail (triangle_top t).
  Proof.
    move=>A.
    elim=>[|n IH] t;
          inv_triangle t => t l.
    - by inv_triangle t.
    - simpl.
      rewrite IH fin_list_tail_snoc //.
  Qed.
    
  Lemma triangle_column_bottom :
    ∀ {A : Type} {n : nat} (t : triangle A (S n)) (i : fin n),
    triangle_column (triangle_remove_bottom t) i =
    fin_list_liat (triangle_column t (FS i)).
  Proof.
    move=>A.
    elim=>[|n IH] t i; first inv_fin i.
    destruct n.
    - inv_fin i => [|i]; last inv_fin i.
      inv_triangle t => t l /=.
      inv_fin_list l => a l /=.
      inv_fin_list l => b l /=.
      inv_fin_list l.
      inv_triangle t => t l' //=.
    - inv_fin i => [|i].
      + inv_triangle t => t l /=.
        specialize (IH t 0%fin).
        inv_fin_list l => a l /=.
        inv_fin_list l => b l /=.
        inv_triangle t => t l' IH //=.
      + #[local] Opaque triangle_remove_bottom triangle_remove_top fin_list_get triangle_top.
        remember (S n) as k.
        simpl.
        rewrite triangle_remove_top_bottom IH.
        subst k.
        setoid_rewrite fin_list_liat_cons_S at 2.
        f_equal.
        rewrite triangle_top_remove_bottom //.
  Qed.
  
  Lemma triangle_get_remove_bottom :
    ∀ {A : Type} {n : nat} (t : triangle A (S n)) (i : fin n) (j : fin (S i)),
    triangle_get t (FS i) (fin_S_inj j) =
    triangle_get (triangle_remove_bottom t) i j.
  Proof.
    move=>A [|n] t i j; first inv_fin i.
    unfold triangle_get.
    rewrite triangle_column_bottom fin_list_get_inj //.
  Qed.
  
  #[global] Opaque
    triangle_top
    triangle_bottom
    triangle_remove_top
    triangle_remove_bottom
    triangle_glue_top
    triangle_glue_bottom.

  Fixpoint fin_list_const {n : nat} {A : Type} (a : A) : fin_list A n :=
    match n as n0 return fin_list A n0 with
    | 0 => fin_nil
    | S m => fin_cons a (fin_list_const a)
    end.
  
  Fixpoint trig_const {n : nat} {A : Type} (a : A) : triangle A n :=
    match n as n0 return triangle A n0 with
    | 0 => trig_nil
    | S m => trig_snoc (trig_const a) (fin_list_const a)
    end.

  Lemma fin_list_const_cons_snoc : ∀ {n : nat} {A : Type} (a : A), @fin_list_snoc A n (fin_list_const a) a = fin_cons a (fin_list_const a).
  Proof.
    elim=>[|n IH] A a //=.
    rewrite -{2}IH //.
  Qed.

  Lemma fin_list_const_head : ∀ {n : nat} {A : Type} (a : A), @fin_list_head A n (fin_list_const a) = a.
  Proof. reflexivity. Qed.
   
  Lemma fin_list_const_last : ∀ {n : nat} {A : Type} (a : A), @fin_list_last A n (fin_list_const a) = a.
  Proof.
    elim=>[//|n IH /=] A a.
    rewrite fin_list_last_cons_S //.
  Qed.

  Lemma fin_list_const_tail : ∀ {n : nat} {A : Type} (a : A), @fin_list_tail A n (fin_list_const a) = fin_list_const a.
  Proof. reflexivity. Qed.
   
  Lemma fin_list_const_liat : ∀ {n : nat} {A : Type} (a : A), @fin_list_liat A n (fin_list_const a) = fin_list_const a.
  Proof.
    elim=>[//|n IH /=] A a.
    rewrite fin_list_liat_cons_S IH //.
  Qed.

  Lemma fin_list_const_get : ∀ {n : nat} {A : Type} (a : A) (i : fin n), @fin_list_get A n (fin_list_const a) i = a.
  Proof.
    elim=>[|n IH] A a i /=; inv_fin i; first done.
    move=>i /=.
    rewrite -{3}(IH _ a i) //.
  Qed.

  Lemma trig_const_top : ∀ {n : nat} {A : Type} (a : A), @triangle_top A n (trig_const a) = fin_list_const a.
  Proof.
    elim=>[|n IH] //= A a.
    cbv [triangle_top].
    simpl.
    cbv [triangle_top] in IH.
    rewrite IH.
    apply fin_list_const_cons_snoc.
  Qed.

   Lemma trig_const_remove_top : ∀ {n : nat} {A : Type} (a : A), @triangle_remove_top A n (trig_const a) = trig_const a.
  Proof.
    elim=>[|n IH] //= A a.
    cbv [triangle_remove_top].
    simpl.
    cbv [triangle_remove_top] in IH.
    rewrite IH //.
  Qed.

  Lemma trig_const_bottom : ∀ {n : nat} {A : Type} (a : A), @triangle_bottom A n (trig_const a) = fin_list_const a.
  Proof.
    elim=>[|n IH] //= A a.
    cbv [triangle_bottom].
    simpl.
    cbv [triangle_bottom] in IH.
    rewrite IH fin_list_const_last fin_list_const_cons_snoc //.
  Qed.

  Lemma trig_const_remove_bottom : ∀ {n : nat} {A : Type} (a : A), @triangle_remove_bottom A n (trig_const a) = trig_const a.
  Proof.
    elim=>[|n IH] //= A a.
    cbv [triangle_remove_bottom].
    simpl.
    cbv [triangle_remove_bottom] in IH.
    rewrite IH fin_list_const_liat //.
  Qed.

  Lemma trig_const_head : ∀ {n : nat} {A : Type} (a : A), @triangle_head A n (trig_const a) = trig_const a.
  Proof. reflexivity. Qed.
    
  Lemma trig_const_tail : ∀ {n : nat} {A : Type} (a : A), @triangle_tail A n (trig_const a) = fin_list_const a.
  Proof. reflexivity. Qed.
 
  
    
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
  
  Definition β_empty_list {n : nat} : fin_list (list (fin 2)) n := @fin_list_const n (list (fin 2)) [].
  Definition β_empty {n : nat} : β_tape n := @trig_const n (list (fin 2)) [].
   
  Definition tl_error {A : Type} (l : list A) : option (list A) :=
    match l with
    | [] => None
    | _::t => Some t
    end.

  Fixpoint liat_error {A : Type} (l : list A) : option (list A) :=
    match l with
    | [] => None
    | [_] => Some []
    | h::t => cons h <$> liat_error t
    end.

  Lemma liat_error_snoc : ∀ {A : Type} (l : list A) (a : A),
    liat_error (l ++ [a]) = Some l.
  Proof.
    move=>A.
    elim=>[//|h1 [|h2 t] IH] a //=.
    specialize (IH a).
    simpl in IH.
    rewrite IH //.
  Qed.

  Definition β_list_push_first {n : nat}
    (l : fin_list (list (fin 2)) (S n)) (v : fin 2) : fin_list (list (fin 2)) (S n)
    := fin_cons (v::fin_list_head l) (fin_list_tail l).

  Definition β_list_hsup_first {n : nat}
    (l : fin_list (list (fin 2)) (S n)) (v : fin 2) : fin_list (list (fin 2)) (S n)
    := fin_cons (fin_list_head l ++ [v]) (fin_list_tail l).

  Definition β_list_pop_first {n : nat}
    (l : fin_list (list (fin 2)) (S n))
    : option (fin_list (list (fin 2)) (S n))
    := hd' ← tl_error (fin_list_head l) ;
       Some (fin_cons hd' (fin_list_tail l)).

  Definition β_list_opo_first {n : nat}
    (l : fin_list (list (fin 2)) (S n))
    : option (fin_list (list (fin 2)) (S n))
   := hd' ← liat_error (fin_list_head l);
      Some (fin_cons hd' (fin_list_tail l)).

  Definition β_list_head_first {n : nat}
    (l : fin_list (list (fin 2)) (S n)) : option (fin 2) := 
      head (fin_list_head l)
  .

  Definition β_list_daeh_first {n : nat}
    (l : fin_list (list (fin 2)) (S n)) : option (fin 2) := 
      last (fin_list_head l)
  .
  
  Lemma β_list_push_pop_first {n : nat} :
    ∀ (l : fin_list (list (fin 2)) (S n))
      (v : fin 2),
    β_list_pop_first (β_list_push_first l v) = Some l.
  Proof.
    move=>l v.
    by inv_fin_list l.
  Qed.

  Lemma β_list_hsup_opo_first {n : nat} :
    ∀ (l : fin_list (list (fin 2)) (S n))
      (v : fin 2),
    β_list_opo_first (β_list_hsup_first l v) = Some l.
  Proof.
    move=>l v.
    inv_fin_list l => a l /=.
    rewrite /β_list_hsup_first /β_list_opo_first /= liat_error_snoc //.
  Qed.
  
  Lemma β_list_push_head_first {n : nat} :
    ∀ (l : fin_list (list (fin 2)) (S n))
      (v : fin 2),
    β_list_head_first (β_list_push_first l v) = Some v.
  Proof.
    move=>l v //.
  Qed.

  Lemma β_list_hsup_daeh_first {n : nat} :
    ∀ (l : fin_list (list (fin 2)) (S n))
      (v : fin 2),
    β_list_daeh_first (β_list_hsup_first l v) = Some v.
  Proof.
    move=>l v.
    inv_fin_list l => a l /=.
    rewrite /β_list_daeh_first fin_list_head_cons last_snoc //.
  Qed.

  Lemma β_list_head_first_top_bottom {n : nat} :
    ∀ (t : β_tape (S n)), β_list_head_first (triangle_top t) = β_list_head_first (triangle_bottom t).
  Proof.
    move=>t.
    unfold β_list_head_first.
    f_equal.
    apply triangle_top_bottom_first.
  Qed.

   Lemma β_list_daeh_first_top_bottom {n : nat} :
    ∀ (t : β_tape (S n)), β_list_daeh_first (triangle_top t) = β_list_daeh_first (triangle_bottom t).
  Proof.
    move=>t.
    unfold β_list_daeh_first.
    f_equal.
    apply triangle_top_bottom_first.
  Qed.
  
  Lemma β_list_push_first_fin_head {n : nat} :
    ∀ (l : fin_list (list (fin 2)) (S n))
      (v : fin 2),
    fin_list_head (β_list_push_first l v) = v::fin_list_head l.
  Proof.
    move=>l v //.
  Qed.

   Lemma β_list_hsup_first_fin_head {n : nat} :
    ∀ (l : fin_list (list (fin 2)) (S n))
      (v : fin 2),
    fin_list_head (β_list_hsup_first l v) = fin_list_head l ++ [v].
  Proof.
    move=>l v //.
  Qed.

   Lemma β_list_hsup_first_fin_tail {n : nat} :
    ∀ (l : fin_list (list (fin 2)) (S n))
      (v : fin 2),
    fin_list_tail (β_list_hsup_first l v) = fin_list_tail l.
  Proof.
    move=>l v //.
  Qed.

  Lemma β_list_push_hsup_empty {n : nat} :
    ∀ (i : fin 2), β_list_push_first (@β_empty_list (S n)) i = β_list_hsup_first (@β_empty_list (S n)) i.
  Proof. reflexivity. Qed.
  
  #[local] Opaque
   β_list_push_first
   β_list_pop_first
   β_list_head_first
   β_list_hsup_first
   β_list_opo_first
   β_list_daeh_first.

  Fixpoint fin_list_list_concat {A : Type} {n : nat} :
    fin_list (list A) n → fin_list (list A) n → fin_list (list A) n :=
    match n as n0 return
          fin_list (list A) n0 → fin_list (list A) n0 → fin_list (list A) n0
    with
    | 0 => λ _ _, fin_nil
    | S m => λ l1 l2, fin_cons (fin_list_head l1 ++ fin_list_head l2) (fin_list_list_concat (fin_list_tail l1) (fin_list_tail l2))
    end.

  Lemma fin_list_list_concat_assoc :
    ∀ (A : Type) (n : nat) (l1 l2 l3 : fin_list (list A) n),
    fin_list_list_concat (fin_list_list_concat l1 l2) l3 = fin_list_list_concat l1 (fin_list_list_concat l2 l3).
  Proof.
    move=>A.
    elim=>[//|n IH] l1 l2 l3.
    inv_fin_list l1=>h1 l1.
    inv_fin_list l2=>h2 l2.
    inv_fin_list l3=>h3 l3.
    rewrite /= app_assoc IH //.
  Qed.

  Lemma fin_list_list_concat_head :
    ∀ (A : Type) (n : nat) (l1 l2 : fin_list (list A) (S n)),
    fin_list_head (fin_list_list_concat l1 l2) = fin_list_head l1 ++ fin_list_head l2.
  Proof. reflexivity. Qed.

  Lemma fin_list_list_concat_snoc :
    ∀ (A : Type) (n : nat) (l1 l2 : fin_list (list A) n) (h1 h2 : list A),
    (fin_list_list_concat (fin_list_snoc l1 h1) (fin_list_snoc l2 h2)) =
      fin_list_snoc (fin_list_list_concat l1 l2) (h1 ++ h2).
  Proof.
    move=>A.
    elim=>[//|n IH] l1 l2 h1 h2.
    simpl.
    rewrite -fin_list_cons_snoc -IH //.
  Qed.

  Lemma fin_list_list_concat_last :
    ∀ (A : Type) (n : nat) (l1 l2 : fin_list (list A) (S n)),
    fin_list_last (fin_list_list_concat l1 l2) = fin_list_last l1 ++ fin_list_last l2.
  Proof.
    move=>A n l1 l2.
    rewrite {1}(fin_list_snoc_liat_last l1) {1}(fin_list_snoc_liat_last l2) fin_list_list_concat_snoc fin_list_last_snoc //.
  Qed.

  Lemma fin_list_list_concat_liat :
    ∀ (A : Type) (n : nat) (l1 l2 : fin_list (list A) (S n)),
    fin_list_liat (fin_list_list_concat l1 l2) = fin_list_list_concat (fin_list_liat l1) (fin_list_liat l2).
  Proof.
    move=>A n l1 l2.
    rewrite {1}(fin_list_snoc_liat_last l1) {1}(fin_list_snoc_liat_last l2) fin_list_list_concat_snoc fin_list_liat_snoc //.
  Qed.

  Lemma fin_list_list_concat_nil_l :
    ∀ (A : Type) (n : nat) (l : fin_list (list A) n),
    fin_list_list_concat (fin_list_const []) l = l.
  Proof.
    move=>A.
    elim=>[|n IH] l; inv_fin_list l=>// h l.
    rewrite /= IH //.
  Qed.

  Lemma fin_list_list_concat_nil_r :
    ∀ (A : Type) (n : nat) (l : fin_list (list A) n),
    fin_list_list_concat l (fin_list_const []) = l.
  Proof.
    move=>A.
    elim=>[|n IH] l; inv_fin_list l=>// h l.
    rewrite /= IH app_nil_r //.
  Qed.
  
  Lemma β_list_push_first_concat :
    ∀ (n : nat) (l : fin_list (list (fin 2)) (S n)) (i : fin 2),
    β_list_push_first l i = fin_list_list_concat (β_list_push_first β_empty_list i) l.
  Proof.
    move=>n l i.
    inv_fin_list l=>h l /=.
    rewrite fin_list_list_concat_nil_l //.
  Qed.

   Lemma β_list_hsup_first_concat :
    ∀ (n : nat) (l : fin_list (list (fin 2)) (S n)) (i : fin 2),
    β_list_hsup_first l i = fin_list_list_concat l (β_list_hsup_first β_empty_list i).
  Proof.
    move=>n l i.
    inv_fin_list l=>h l /=.
    rewrite fin_list_list_concat_nil_r //.
  Qed.
  
  Fixpoint triangle_list_concat {n : nat} : β_tape n → β_tape n → β_tape n :=
    match n as n0 return β_tape n0 → β_tape n0 → β_tape n0 with
    | 0 => λ _ _, trig_nil
    | S m => λ t1 t2,
               trig_snoc (triangle_list_concat
                            (triangle_head t1)
                            (triangle_head t2)
                 ) (fin_list_list_concat (triangle_tail t1) (triangle_tail t2))
               
    end.

  #[local] Opaque fin_list_list_concat.
  
  Lemma triangle_list_concat_top :
    ∀ (n : nat) (t1 t2 : β_tape n),
    triangle_top (triangle_list_concat t1 t2) = fin_list_list_concat (triangle_top t1) (triangle_top t2).
  Proof.
    elim=>[//|n IH] t1 t2 /=.
    inv_triangle t1=>t1 l1.
    inv_triangle t2=>t2 l2.
    rewrite !triangle_top_split_snoc IH /= fin_list_list_concat_head fin_list_list_concat_snoc //.
  Qed.
    
  Lemma triangle_list_concat_remove_top :
    ∀ (n : nat) (t1 t2 : β_tape (S n)),
    triangle_remove_top (triangle_list_concat t1 t2) = triangle_list_concat (triangle_remove_top t1) (triangle_remove_top t2).
  Proof.
    elim=>[//|n IH] t1 t2 /=.
    specialize (IH (triangle_head t1) (triangle_head t2)).
    rewrite -IH //.
  Qed.

  Lemma triangle_list_concat_glue_top :
    ∀ (n : nat) (t1 t2 : β_tape n) (h1 h2 : fin_list (list (fin 2)) (S n)),
    triangle_glue_top (triangle_list_concat t1 t2) (fin_list_list_concat h1 h2) =
    triangle_list_concat (triangle_glue_top t1 h1) (triangle_glue_top t2 h2).
  Proof.
    move=>n t1 t2 h1 h2.
    rewrite
      (triangle_glue_remove_top (triangle_list_concat (triangle_glue_top _ _) _))
        triangle_list_concat_top triangle_list_concat_remove_top
        !triangle_remove_glue_top !triangle_top_glue //.
  Qed.

 Lemma triangle_list_concat_bottom :
    ∀ (n : nat) (t1 t2 : β_tape n),
    triangle_bottom (triangle_list_concat t1 t2) = fin_list_list_concat (triangle_bottom t1) (triangle_bottom t2).
  Proof.
    elim=>[//|n IH] t1 t2 /=.
    inv_triangle t1=>t1 l1.
    inv_triangle t2=>t2 l2.
    rewrite !triangle_bottom_split_snoc fin_list_list_concat_snoc fin_list_list_concat_last -IH //.
  Qed.
    
  Lemma triangle_list_concat_remove_bottom :
    ∀ (n : nat) (t1 t2 : β_tape (S n)),
    triangle_remove_bottom (triangle_list_concat t1 t2) = triangle_list_concat (triangle_remove_bottom t1) (triangle_remove_bottom t2).
  Proof.
    elim=>[//|n IH] t1 t2 /=.
    specialize (IH (triangle_head t1) (triangle_head t2)).
    rewrite -IH.
    cbv [triangle_remove_bottom].
    rewrite fin_list_list_concat_liat //.
  Qed.
  
  Lemma triangle_list_concat_glue_bottom :
    ∀ (n : nat) (t1 t2 : β_tape n) (h1 h2 : fin_list (list (fin 2)) (S n)),
    triangle_glue_bottom (triangle_list_concat t1 t2) (fin_list_list_concat h1 h2) =
    triangle_list_concat (triangle_glue_bottom t1 h1) (triangle_glue_bottom t2 h2).
  Proof.
    move=>n t1 t2 h1 h2.
    rewrite
      (triangle_glue_remove_bottom (triangle_list_concat (triangle_glue_bottom _ _) _))
        triangle_list_concat_bottom triangle_list_concat_remove_bottom
        !triangle_remove_glue_bottom !triangle_bottom_glue //.
  Qed.


  Lemma triangle_list_concat_assoc :
    ∀ (n : nat) (t1 t2 t3 : β_tape n),
    triangle_list_concat (triangle_list_concat t1 t2) t3 = triangle_list_concat t1 (triangle_list_concat t2 t3).
  Proof.
    elim=>[//|n IH] t1 t2 t3.
    inv_triangle t1=>t1 l1. 
    inv_triangle t2=>t2 l2. 
    inv_triangle t3=>t3 l3.
    rewrite /= !fin_list_list_concat_assoc IH //.
  Qed.

  Fixpoint β_push {n : nat} : β_tape n → fin_list (fin 2) n → β_tape n :=
    match n as n0 return β_tape n0 → fin_list (fin 2) n0 → β_tape n0 with
    | 0 => λ _ _, trig_nil
    | S m => λ t l,
               fin_S_inv (const (β_tape (S m)))
                 (triangle_glue_bottom
                    (β_push (triangle_remove_bottom t) (fin_list_tail l))
                    (β_list_push_first (triangle_bottom t) 0%fin)
                 )
                 (λ _,
                    triangle_glue_top
                      (β_push (triangle_remove_top t) (fin_list_tail l))
                      (β_list_push_first (triangle_top t) 1%fin)
                 )
                 (fin_list_head l)
    end.
  
  Fixpoint β_hsup {n : nat} : β_tape n → fin_list (fin 2) n → β_tape n :=
    match n as n0 return β_tape n0 → fin_list (fin 2) n0 → β_tape n0 with
    | 0 => λ _ _, trig_nil
    | S m => λ t l,
               fin_S_inv (const (β_tape (S m)))
                 (triangle_glue_bottom
                    (β_hsup (triangle_remove_bottom t) (fin_list_tail l))
                    (β_list_hsup_first (triangle_bottom t) 0%fin)
                 )
                 (λ _,
                    triangle_glue_top
                      (β_hsup (triangle_remove_top t) (fin_list_tail l))
                      (β_list_hsup_first (triangle_top t) 1%fin)
                 )
                 (fin_list_head l)
    end.

  Lemma β_push_concat : ∀ (n : nat) (t : β_tape n) (l : fin_list (fin 2) n),
    β_push t l = triangle_list_concat (β_push β_empty l) t.
  Proof.
    elim=>[//|n IH] t l.
    inv_fin_list l=>i l.
    inv_fin i=>[|i].
    - rewrite /= IH β_list_push_first_concat triangle_list_concat_glue_bottom
              -triangle_glue_remove_bottom trig_const_bottom trig_const_remove_bottom //.
    - rewrite /= IH β_list_push_first_concat triangle_list_concat_glue_top
              -triangle_glue_remove_top trig_const_top trig_const_remove_top //.
  Qed.

 Lemma β_hsup_concat : ∀ (n : nat) (t : β_tape n) (l : fin_list (fin 2) n),
    β_hsup t l = triangle_list_concat t (β_hsup β_empty l).
  Proof.
    elim=>[//|n IH] t l.
    inv_fin_list l=>i l.
    inv_fin i=>[|i].
    - rewrite /= IH β_list_hsup_first_concat triangle_list_concat_glue_bottom
              -triangle_glue_remove_bottom trig_const_bottom trig_const_remove_bottom //.
    - rewrite /= IH β_list_hsup_first_concat triangle_list_concat_glue_top
              -triangle_glue_remove_top trig_const_top trig_const_remove_top //.
  Qed.

   Lemma β_push_hsup_empty : ∀ (n : nat) (i : fin_list (fin 2) n), β_push β_empty i = β_hsup β_empty i.
  Proof.
    elim=>[//|n IH] i.
    inv_fin_list i=>hi ti.
    inv_fin hi=>[|hi]=>/=.
    - rewrite !trig_const_remove_bottom trig_const_bottom IH //.
    - rewrite !trig_const_remove_top trig_const_top IH //.
  Qed.

  Lemma β_push_hsup :
    ∀ (n : nat) (τ : β_tape n) (lt lb : fin_list (fin 2) n),
    β_push (β_hsup τ lb) lt = β_hsup (β_push τ lt) lb.
  Proof.
    move=>n τ lt lb.
    rewrite (β_push_concat _ (β_hsup _ _)) (β_hsup_concat _ (β_push _ _))
      (β_push_concat _ τ) (β_hsup_concat _ τ) triangle_list_concat_assoc //.
  Qed.
  
  Fixpoint β_arbitrary {n : nat} : fin (S n) → fin_list (fin 2) n :=
    match n as n0 return fin (S n0) → fin_list (fin 2) n0 with
    | 0 => const fin_nil
    | S m => fin_S_inv (const (fin_list (fin 2) (S m)))
               (fin_cons 0%fin (β_arbitrary 0%fin))
               (λ j, fin_cons 1%fin (β_arbitrary j))
    end.
  
  Lemma β_push_length_first_top {n : nat} :
    ∀ (t : β_tape (S n))
      (v : fin_list (fin 2) (S n)),
    length (fin_list_head (triangle_top (β_push t v))) =
    S (length (fin_list_head (triangle_top t))).
  Proof.
    move=>t v.
    inv_fin_list v => i v /=.
    inv_fin i => [|i].
    - rewrite !triangle_top_bottom_first triangle_bottom_glue β_list_push_first_fin_head //.
    - rewrite triangle_top_glue β_list_push_first_fin_head //.
  Qed.
  
  Definition β_fold {n : nat} : list (fin_list (fin 2) n) → β_tape n :=
    foldr (flip β_push) β_empty.

  Lemma β_hsup_fold {n : nat} :
    ∀ (l : list (fin_list (fin 2) n)) (h : fin_list (fin 2) n),
    β_hsup (β_fold l) h = β_fold (l ++ [h]).
  Proof.
    elim=>[|hl tl IH] h /=.
    - rewrite β_push_hsup_empty //.
    - rewrite -β_push_hsup IH //.
  Qed.
  
  Definition β_encode {n : nat} : list (fin (S n)) → β_tape n :=
    β_fold ∘ fmap β_arbitrary.

  Definition β_first {n : nat} (t : β_tape (S n)) : option (fin 2) :=
    β_list_head_first (triangle_top t).

  Definition β_daeh_first {n : nat} (t : β_tape (S n)) : option (fin 2) :=
    β_list_daeh_first (triangle_top t).
  
  Fixpoint β_head {n : nat} : β_tape n → option (fin_list (fin 2) n) :=
      match n as n0 return β_tape n0 → option (fin_list (fin 2) n0) with
      | 0 => λ _, Some fin_nil
      | S m => λ t,
                 v ← β_first t ;
                 match v with
                 | 0%fin => fin_cons 0%fin <$> β_head (triangle_remove_bottom t)
                 | _ => fin_cons 1%fin <$> β_head (triangle_remove_top t)
                 end
  end.

  Fixpoint β_daeh {n : nat} : β_tape n → option (fin_list (fin 2) n) :=
      match n as n0 return β_tape n0 → option (fin_list (fin 2) n0) with
      | 0 => λ _, Some fin_nil
      | S m => λ t,
                 v ← β_daeh_first t ;
                 match v with
                 | 0%fin => fin_cons 0%fin <$> β_daeh (triangle_remove_bottom t)
                 | _ => fin_cons 1%fin <$> β_daeh (triangle_remove_top t)
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

  Fixpoint β_opo {n : nat} : β_tape n → option (β_tape n) :=
    match n as n0 return β_tape n0 → option (β_tape n0) with
    | 0 => λ _, Some β_empty
    | S m => λ t,
               v ← β_daeh_first t ;
               match v with
               | 0%fin =>
                   l' ← β_list_opo_first (triangle_bottom t);
                   t' ← β_opo $ triangle_remove_bottom t;
                   Some (triangle_glue_bottom t' l')
                        
               | _ =>
                   l' ← β_list_opo_first (triangle_top t);
                   t' ← β_opo $ triangle_remove_top t;
                   Some (triangle_glue_top t' l')
               end
  end.


  Definition β_split {n : nat} (t : β_tape n) : option (fin_list (fin 2) n * β_tape n) :=
    h ← β_head t ;
    t' ← β_pop t;
    Some (h, t').

   Definition β_tilps {n : nat} (t : β_tape n) : option (fin_list (fin 2) n * β_tape n) :=
    h ← β_daeh t ;
    t' ← β_opo t;
    Some (h, t').
  
  Fixpoint fin_list_fin_2_sum {n : nat} : fin_list (fin 2) n → fin (S n) :=
    match n as n0 return fin_list (fin 2) n0 → fin (S n0) with
    | 0 => const 0%fin
    | S m => λ l, fin_hsum (fin_list_head l) (fin_S_inj (fin_list_fin_2_sum (fin_list_tail l)))
    end.

  Lemma fin_list_fin_2_sum_0 : ∀ (l : fin_list (fin 2) 0), fin_list_fin_2_sum l = 0%fin.
  Proof. reflexivity. Qed.

  Lemma fin_list_fin_2_sum_S : ∀ (n : nat) (l : fin_list (fin 2) (S n)), fin_list_fin_2_sum l = fin_hsum (fin_list_head l) (fin_S_inj (fin_list_fin_2_sum (fin_list_tail l))).
  Proof. reflexivity. Qed.

  Lemma fin_list_fin_2_sum_0_const_0 : ∀ (n : nat) (l : fin_list (fin 2) n), fin_list_fin_2_sum l = 0%fin → l = fin_list_const 0%fin.
  Proof.
    elim=>[|n IH] l sum_l; inv_fin_list l=> // h t sum_h_t.
    inv_fin h=>[|h] /= sum_h_t.
    - rewrite (IH t) //.
      inv_fin (fin_list_fin_2_sum t) => [//|st] Sst_eq_0.
      discriminate.
    - rewrite fin_succ_inj in sum_h_t.
      inv_fin h=>[//|].
      move=>h.
      inv_fin h.
  Qed.

  Lemma fin_list_fin_2_sum_const_0_eq_0 : ∀ (n : nat), fin_list_fin_2_sum (@fin_list_const n _ 0%fin) = 0%fin.
  Proof.
    elim=>[|n /= ->] //.
  Qed.

  Lemma sum_arbitrary : ∀ {n : nat} (i : fin (S n)), fin_list_fin_2_sum (β_arbitrary i) = i.
  Proof.
    elim=>[|n IH] i /=; full_inv_fin => /=; rewrite IH //=.
    rewrite fin_succ_inj //.
  Qed.

  #[global] Opaque β_arbitrary fin_list_fin_2_sum.
  
  Fixpoint β_decode_k {n : nat} (t : β_tape n) (k : nat) : option (list (fin (S n))) :=
    match k with
    | 0 => Some []
    | S k' => '(hd, t') ← β_split t ;
               tl ← β_decode_k t' k' ;
               Some ((fin_list_fin_2_sum hd)::tl)
  end.

  Definition β_decode {n : nat} : β_tape n → option (list (fin (S n))) :=
    match n as n0 return β_tape n0 → option (list (fin (S n0))) with
    | 0 => const (Some [])
    | S m => λ t, β_decode_k t (length $ fin_list_head $ triangle_top t)
    end.
  
  Lemma β_push_head :
    ∀ {n : nat} (t : β_tape n) (v : fin_list (fin 2) n),
    β_head (β_push t v) = Some v.
  Proof.
    elim=>[|n IH] t v; first by inv_fin_list v.
    inv_fin_list v => i v.
    inv_fin i => [|i].
    - simpl.
      unfold β_first.
      rewrite β_list_head_first_top_bottom triangle_bottom_glue β_list_push_head_first /= triangle_remove_glue_bottom IH //.
    - simpl.
      unfold β_first.
      rewrite triangle_top_glue β_list_push_head_first /= triangle_remove_glue_top IH //.
      inv_fin i => [//|i].
      inv_fin i.
  Qed.

   Lemma β_hsup_daeh :
    ∀ {n : nat} (t : β_tape n) (v : fin_list (fin 2) n),
    β_daeh (β_hsup t v) = Some v.
  Proof.
    elim=>[|n IH] t v; first by inv_fin_list v.
    inv_fin_list v => i v.
    inv_fin i => [|i].
    - simpl.
      unfold β_daeh_first.
      rewrite β_list_daeh_first_top_bottom triangle_bottom_glue β_list_hsup_daeh_first /= triangle_remove_glue_bottom IH //.
    - simpl.
      unfold β_daeh_first.
      rewrite triangle_top_glue β_list_hsup_daeh_first /= triangle_remove_glue_top IH //.
      inv_fin i => [//|i].
      inv_fin i.
  Qed.

  Lemma β_push_pop :
    ∀ {n : nat} (t : β_tape n) (v : fin_list (fin 2) n),
    β_pop (β_push t v) = Some t.
  Proof.
    elim=>[|n IH] t v.
    { inv_fin_list v. by inv_triangle t. } 
    inv_fin_list v => i v.
    inv_fin i => [|i].
    - simpl.
      unfold β_first.
      rewrite β_list_head_first_top_bottom triangle_bottom_glue β_list_push_head_first /= triangle_remove_glue_bottom IH β_list_push_pop_first /= -triangle_glue_remove_bottom //.
    - simpl.
      unfold β_first.
      rewrite triangle_top_glue β_list_push_head_first /= triangle_remove_glue_top IH β_list_push_pop_first /= -triangle_glue_remove_top //.
  Qed.

  Lemma β_hsup_opo :
    ∀ {n : nat} (t : β_tape n) (v : fin_list (fin 2) n),
    β_opo (β_hsup t v) = Some t.
  Proof.
    elim=>[|n IH] t v.
    { inv_fin_list v. by inv_triangle t. } 
    inv_fin_list v => i v.
    inv_fin i => [|i].
    - simpl.
      unfold β_daeh_first.
      rewrite β_list_daeh_first_top_bottom triangle_bottom_glue β_list_hsup_daeh_first /= triangle_remove_glue_bottom IH β_list_hsup_opo_first /= -triangle_glue_remove_bottom //.
    - simpl.
      unfold β_daeh_first.
      rewrite triangle_top_glue β_list_hsup_daeh_first /= triangle_remove_glue_top IH β_list_hsup_opo_first /= -triangle_glue_remove_top //.
  Qed.
  
  Lemma β_push_split :
    ∀ {n : nat} (t : β_tape n) (v : fin_list (fin 2) n),
    β_split (β_push t v) = Some (v, t).
  Proof.
    move=> n t v.
    unfold β_split.
    rewrite β_push_head /= β_push_pop //.
  Qed.

  Lemma β_hsup_tilps :
    ∀ {n : nat} (t : β_tape n) (v : fin_list (fin 2) n),
    β_tilps (β_hsup t v) = Some (v, t).
  Proof.
    move=> n t v.
    unfold β_tilps.
    rewrite β_hsup_daeh /= β_hsup_opo //.
  Qed.
  
  Lemma β_encode_decode :
    ∀ {n : nat} (l : list (fin (S (S n)))),
    β_decode (β_encode l) = Some l.
  Proof.
    move=>n.
    elim=>[|h t IH] /=.
    - rewrite trig_const_top //.
    - rewrite β_push_length_first_top /= β_push_split /=.
      unfold β_decode in IH.
      rewrite IH /=.
      do 2 f_equal.
      apply sum_arbitrary.
  Qed.
   
  Definition β_last_row_well_formed {n : nat} : β_tape (S n) → Prop :=
    match n as n0 return β_tape (S n0) → Prop with
    | 0 => const True
    | S m => (λ t,
                let ht := triangle_head t in
                let l := triangle_tail t in
                let fst := fin_list_head l in
                let mid := fin_list_tail (fin_list_liat l) in 
                let lst := fin_list_last l in
                length fst =
                length (fin_list_last (triangle_top ht)) -
                  list_sum (fin_to_nat <$> fin_list_last (triangle_top ht)) ∧
                length lst = list_sum (fin_to_nat <$> fin_list_last (triangle_top ht)) ∧
                ∀ (i : fin m),
                length (fin_list_get mid i) = 
                length (fin_list_get (triangle_tail ht) (FS i)) -
                  list_sum (fin_to_nat <$> fin_list_get (triangle_tail ht) (FS i)) + 
                  list_sum (fin_to_nat <$> fin_list_get (triangle_tail ht) (fin_S_inj i))
             )%nat
    end.

 Fixpoint β_well_formed {n : nat} : β_tape n → Prop :=
    match n as n0 return β_tape n0 → Prop with
    | 0 => const True
    | S m => λ t,
               β_well_formed (triangle_head t) ∧ β_last_row_well_formed t
    end.

 Lemma empty_last_row : ∀ (n : nat), β_last_row_well_formed (@β_empty (S n)).
  Proof.
    case=>[//|n] ht l fst mid lst.
    simpl in ht.
    change ht with (@β_empty (S n)).
    change l with (@β_empty_list (S (S n))) in *.
    change fst with ([] : list (fin 2)).
    replace lst with ([] : list (fin 2)) by (rewrite /lst fin_list_const_last //).
    replace mid with (@β_empty_list n) by  (rewrite /mid fin_list_const_liat fin_list_const_tail //).
    clear ht l fst mid lst.
    rewrite trig_const_top trig_const_tail fin_list_const_last /=.
    split; first reflexivity.
    split; first reflexivity.
    move=>i.
    rewrite !fin_list_const_get //=.
  Qed.
    
 Lemma empty_well_formed : ∀ (n : nat), β_well_formed (@β_empty n).
  Proof.
    elim=>[|n IH] //=.
    split; first assumption.
    apply empty_last_row.
  Qed.

  Lemma β_hsup_head :
    ∀ (n : nat) (τ : β_tape (S n))
      (i : fin_list (fin 2) (S n)),
    triangle_head (β_hsup τ i) = β_hsup (triangle_head τ) (fin_list_liat i).
  Proof.
    elim=>[|n IH] τ i; first apply triangle_0_nil.
    inv_triangle τ=>τ l /=.
    inv_fin_list i=>hi ti /=.
    rewrite fin_list_liat_cons_S.
    inv_fin hi=>[|hi].
    - rewrite triangle_head_glue_bottom IH
        triangle_bottom_split_snoc fin_list_liat_cons_S
        fin_list_head_snoc fin_list_tail_snoc fin_list_liat_snoc //.
    - rewrite triangle_head_glue_top IH
        triangle_top_split_snoc fin_list_liat_cons_S
        fin_list_head_snoc fin_list_tail_snoc fin_list_liat_snoc //.
  Qed.

  Lemma fin_hsum_2_inj_inj : ∀ (n : nat) (a : fin 2) (b : fin n),
    fin_hsum a (fin_S_inj (fin_S_inj b)) =
    fin_S_inj (fin_hsum a (fin_S_inj b)).
  Proof.
    move=>n a b; inv_fin a; first done.
    move=>a /=.
    inv_fin a; last (move=>a; inv_fin a).
    rewrite !fin_succ_inj //.
  Qed.
  
  Lemma fin_list_fin_2_sum_last_liat :
    ∀ (n : nat) (l : fin_list (fin 2) (S n)),
    fin_list_fin_2_sum l = fin_hsum (fin_list_last l) (fin_S_inj (fin_list_fin_2_sum (fin_list_liat l))).
  Proof.
    elim=>[|n IH] l; inv_fin_list l=>k l; first inv_fin_list l=>//.
    rewrite fin_list_fin_2_sum_S IH fin_list_tail_cons
      fin_list_last_cons_S fin_list_head_cons
      fin_list_liat_cons_S fin_list_fin_2_sum_S
      fin_list_head_cons fin_list_tail_cons
      -!fin_hsum_2_inj_inj fin_hsum_comm //
    .
  Qed.
  
  Lemma β_hsup_tail :
    ∀ (n : nat) (τ : β_tape (S n))
      (i : fin_list (fin 2) (S n)),
    let tl := triangle_tail τ in
    let k := fin_list_fin_2_sum (fin_list_liat i) in
    triangle_tail (β_hsup τ i) = fin_list_set tl k (fin_list_get tl k ++ [fin_list_last i]).
  Proof.
    elim=>[|n IH] τ i tl k.
    { inv_triangle τ=>τ l tl.
      inv_triangle τ=>tl.
      simpl in tl.
      subst tl.
      inv_fin_list i=>k i0 k0.
      inv_fin_list i0=>k0.
      replace k0 with (0%fin : fin 1) by reflexivity.
      clear k0.
      inv_fin_list l=>h l /=.
      inv_fin k=>[|k] /=.
      - by inv_fin_list l.
      - inv_fin_list l.
        by inv_fin k=>[|k]; last inv_fin k.
    }
    inv_fin_list i=>k i0 k0.
    inv_fin k=>[|k] k0.
    #[local] Opaque fin_list_set fin_list_get.
    - rewrite triangle_tail_glue_bottom IH fin_list_tail_cons triangle_tail_remove_bottom.
      replace (fin_list_last (β_list_hsup_first (triangle_bottom τ) 0)) with (fin_list_last (triangle_bottom τ)); last first.
      {
        rewrite {1}(fin_list_cons_head_tail (triangle_bottom τ)) !fin_list_last_cons_S //.
      }
      rewrite /k0 !(fin_list_last_cons_S 0%fin i0) !fin_list_liat_cons_S !fin_list_fin_2_sum_S triangle_bottom_tail_last fin_list_set_inj fin_list_get_inj //.
    - inv_fin k; last (move=>k; inv_fin k); move=>k0.
      rewrite triangle_tail_glue_top IH fin_list_tail_cons triangle_tail_remove_top.
      replace (fin_list_last (β_list_hsup_first (triangle_top τ) 1)) with (fin_list_last (triangle_top τ)); last first.
      {
        rewrite {1}(fin_list_cons_head_tail (triangle_top τ)) !fin_list_last_cons_S //.
      }
      rewrite /k0 !(fin_list_last_cons_S 1%fin i0) !fin_list_liat_cons_S !fin_list_fin_2_sum_S triangle_top_last_tail_first /= fin_succ_inj //.
  Qed.

  Lemma list_sum_fin_2_le_len : ∀ (l : list (fin 2)), list_sum $ fin_to_nat <$> l ≤ length l.
  Proof.
    elim=>[//|h t IH].
    rewrite fmap_cons.
    inv_fin h=>[|h]; last (inv_fin h=>[|h]; last inv_fin h); simpl; lia.
  Qed.
    
  Lemma β_hsup_well_formed_last_row :
    ∀ (n : nat) (τ : β_tape (S n))
      (i : fin_list (fin 2) (S n)),
    β_last_row_well_formed τ → β_last_row_well_formed (β_hsup τ i).
  Proof.
    move=>[|n] τ i τ_wf; first done.
    unfold β_last_row_well_formed.
    rewrite triangle_top_last_tail_first !β_hsup_head !β_hsup_tail.
    set (k := fin_list_fin_2_sum (fin_list_liat i)).
    rewrite -!fin_list_get_0.
    destruct τ_wf as (head_wf & last_wf & mid_wf).
    destruct (decide (k = 0)%fin) as [k_eq_0 | k_ne_0];
      last destruct (decide (k = fin_max _)%fin) as [k_eq_max | k_ne_max].
    - rewrite k_eq_0.
      apply (fin_list_fin_2_sum_0_const_0) in k_eq_0 as sum_0.
      rewrite sum_0 fin_list_const_liat fin_list_const_last
        fin_list_fin_2_sum_const_0_eq_0 !fin_list_get_set_eq.
      split; last split.
      + rewrite !app_length fmap_app list_sum_app Nat.add_0_r !fin_list_get_0 head_wf triangle_top_last_tail_first /=.
        pose proof (list_sum_fin_2_le_len (fin_list_head (triangle_tail (triangle_head τ)))).
        lia.
      + rewrite -fin_list_get_max fin_list_get_set_ne; last done.
        rewrite fmap_app list_sum_app Nat.add_0_r
          fin_list_get_0 fin_list_get_max -triangle_top_last_tail_first //.
      + move=>j.
        rewrite -fin_list_get_FS -fin_list_get_inj /=
                (fin_list_get_set_ne _ _ (FS (fin_S_inj j)));
        last done.
        rewrite (fin_list_get_set_ne _ _ (FS j)); last done.
        destruct n; inv_fin j => [|j].
        * rewrite fin_list_get_set_eq fin_list_get_FS fin_list_get_inj fmap_app list_sum_app Nat.add_0_r -fin_list_tail_liat mid_wf //.
        * rewrite fin_list_get_set_ne; last done.
          rewrite fin_list_get_FS fin_list_get_inj /=.
          by specialize (mid_wf (FS j)%fin).
    - (* Add lemma for fin_list_fin_2_sum l = fin_max n → l = fin_list_const 1%fin *)
          
        
  Admitted.

  Lemma β_hsup_well_formed :
    ∀ (n : nat) (τ : β_tape n)
      (i : fin_list (fin 2) n),
    β_well_formed τ → β_well_formed (β_hsup τ i).
  Proof.
    elim=>[//|n IH] τ i τ_wf /=.
    rewrite β_hsup_head.
    split; first apply IH.
    { destruct n; first done.
      by destruct τ_wf.
    }
    apply β_hsup_well_formed_last_row.
    destruct n; first done.
    by destruct τ_wf.
  Qed.
    
  Definition is_abs_loc (n : nat) (α : val) (Δ : triangle loc n) :=
    ∀ (i : fin n) (j : fin (S i)),
    ⊢ WP α #i #j [{ v, ⌜v = #(triangle_get Δ i j)⌝ }].

  Definition own_top_list
    {n : nat}
    (p q : nat)
    (αs : fin_list loc n)
    (ls : fin_list (list (fin 2)) n)
    :=
    ([∗ list] i ∈ fin_enum n,
         own_bernoulli_tape
           (fin_list_get αs i)
           p
           (q + i)%nat
           (fin_list_get ls i)
    )%I.

  Definition own_bottom_list
    {n : nat}
    (p q : nat)
    (αs : fin_list loc n)
    (ls : fin_list (list (fin 2)) n)
    :=
    ([∗ list] i ∈ fin_enum n,
         own_bernoulli_tape
           (fin_list_get αs i)
           (p + i)%nat
           (q + i)%nat
           (fin_list_get ls i)
    )%I.
  
  Definition own_trig
    {n : nat}
    (p q : nat)
    (Δ : triangle loc n)
    (τ : β_tape n)
    :=
    ([∗ list] i ∈ fin_enum n,
       [∗ list] j ∈ fin_enum (S i),
         own_bernoulli_tape
           (triangle_get Δ i j)
           (p + j)%nat
           (q + i)
           (triangle_get τ i j)
    )%I.
  
  Lemma own_trig_split_top_1
    {n : nat}
    (p q : nat)
    (Δ : triangle loc (S n))
    (τ : β_tape (S n)) :
    own_trig p q Δ τ -∗
    own_trig (S p) (S q) (triangle_remove_top Δ) (triangle_remove_top τ) ∗
    own_top_list p q (triangle_top Δ) (triangle_top τ).
  Proof.
    iIntros "Hτ".
    unfold own_trig at 1.
    simpl.
    rewrite big_sepL_sep.
    iDestruct "Hτ" as "([Hhd _]  & Htltop & Htl)".
    iSplitL "Htl".
    { do 2 setoid_rewrite big_sepL_fmap.
      erewrite big_opL_ext; first done.
      move=>_ i _ /=.
      simpl.
      rewrite Nat.add_1_r Nat.add_succ_r Nat.add_0_r.
      f_equal.
      apply big_opL_ext.
      move=>_ j _ /=.
      rewrite Nat.add_succ_r //.
    }
    unfold own_top_list.
    rewrite big_sepL_cons.
    fold fin_enum.
    rewrite !Nat.add_0_r !triangle_get_top.
    iFrame.
    #[local] Opaque triangle_get triangle_top fin_list_get.
    erewrite big_opL_ext; first done.
    move=>_ i _ /=.
    rewrite !triangle_get_top //.
  Qed.
  
  Lemma own_trig_split_top_2
    {n : nat}
    (p q : nat)
    (Δ : triangle loc (S n))
    (τ : β_tape (S n)) :
    own_trig (S p) (S q) (triangle_remove_top Δ) (triangle_remove_top τ) ∗
    own_top_list p q (triangle_top Δ) (triangle_top τ) -∗
    own_trig p q Δ τ.
  Proof.
    iIntros "[Hτ Htop]".
    unfold own_trig at 2.
    simpl.
    rewrite big_sepL_sep.
    unfold own_top_list.
    simpl.
    iDestruct "Htop" as "[Hhd Htltop]".
    iSplitL "Hhd".
    { rewrite !Nat.add_0_r !triangle_get_top //. }
    iSplitL "Htltop".
    {
      erewrite big_opL_ext; first done.
      move=>_ i _ /=.
      rewrite !triangle_get_top Nat.add_0_r //.
    }
    do 2 setoid_rewrite big_sepL_fmap.
    erewrite big_opL_ext; first done.
    move=>_ i _ /=.
    simpl.
    rewrite Nat.add_1_r Nat.add_succ_r Nat.add_0_r.
    f_equal.
    apply big_opL_ext.
    move=>_ j _ /=.
    rewrite Nat.add_succ_r //.
  Qed.
  
  Lemma own_trig_split_top
    {n : nat}
    (p q : nat)
    (Δ : triangle loc (S n))
    (τ : β_tape (S n)) :
    own_trig p q Δ τ ⊣⊢
    own_trig (S p) (S q) (triangle_remove_top Δ) (triangle_remove_top τ) ∗
    own_top_list p q (triangle_top Δ) (triangle_top τ).
  Proof.
    iSplit.
    - iApply own_trig_split_top_1.
    - iApply own_trig_split_top_2.
  Qed.

  Lemma fin_enum_split : ∀ {n : nat}, fin_enum (S n) = (fin_S_inj <$> fin_enum n) ++ [nat_to_fin (Nat.lt_succ_diag_r n)].
  Proof.
    move=>n.
    rewrite -enum_fin_split //.
  Qed.
  
  Lemma own_trig_split_bottom_1
    {n : nat}
    (p q : nat)
    (Δ : triangle loc (S n))
    (τ : β_tape (S n)) :
    own_trig p q Δ τ -∗
    own_trig p (S q) (triangle_remove_bottom Δ) (triangle_remove_bottom τ) ∗
    own_bottom_list p q (triangle_bottom Δ) (triangle_bottom τ).
  Proof.
    iIntros "Hτ".
    unfold own_trig at 1.
    erewrite big_opL_ext; last first.
    {
      move=>? i ?.
      rewrite fin_enum_split //.
    }
    setoid_rewrite big_sepL_app.
    rewrite big_sepL_sep.
    setoid_rewrite big_sepL_singleton.
    iDestruct "Hτ" as "([_ Hτ] & Hbot)".
    iSplitL "Hτ".
    { do 2 setoid_rewrite big_sepL_fmap.
      fold fin_enum.
      erewrite big_opL_ext; first done.
      move=>_ i _ /=.
      simpl.
      rewrite !Nat.add_succ_r !Nat.add_0_r.
      rewrite -!triangle_get_remove_bottom //.
      f_equal. 
      apply big_opL_ext.
      move=>_ j _ /=.
      rewrite -!fin_S_inj_to_nat !triangle_get_remove_bottom //.
    } 
    unfold own_bottom_list.
    erewrite big_opL_ext; first done.
    move=>_ i _ /=.
    rewrite !fin_to_nat_to_fin !triangle_get_bottom //.
  Qed.

  Lemma own_trig_split_bottom_2
    {n : nat}
    (p q : nat)
    (Δ : triangle loc (S n))
    (τ : β_tape (S n)) :
    own_trig p (S q) (triangle_remove_bottom Δ) (triangle_remove_bottom τ) ∗
    own_bottom_list p q (triangle_bottom Δ) (triangle_bottom τ) -∗
    own_trig p q Δ τ.
  Proof.
    iIntros "[Hτ Hbot]".
    unfold own_trig at 2.
    erewrite big_opL_ext; last first.
    {
      move=>? i ?.
      rewrite fin_enum_split //.
    }
    setoid_rewrite big_sepL_app.
    rewrite big_sepL_sep.
    setoid_rewrite big_sepL_singleton.
    iSplitL "Hτ".
    { setoid_rewrite big_sepL_fmap.
      simpl.
      iSplitR; first done.
      setoid_rewrite big_sepL_fmap.
      erewrite big_opL_ext; first done.
      move=>_ i _ /=.
      simpl.
      rewrite !Nat.add_succ_r !Nat.add_0_r.
      rewrite -!triangle_get_remove_bottom //.
      f_equal. 
      apply big_opL_ext.
      move=>_ j _ /=.
      rewrite -!fin_S_inj_to_nat !triangle_get_remove_bottom //.
    } 
    unfold own_bottom_list.
    erewrite big_opL_ext; first done.
    move=>_ i _ /=.
    rewrite !fin_to_nat_to_fin !triangle_get_bottom //.
  Qed.
  
  Lemma own_trig_split_bottom
    {n : nat}
    (p q : nat)
    (Δ : triangle loc (S n))
    (τ : β_tape (S n)) :
    own_trig p q Δ τ ⊣⊢
    own_trig p (S q) (triangle_remove_bottom Δ) (triangle_remove_bottom τ) ∗
    own_bottom_list p q (triangle_bottom Δ) (triangle_bottom τ).
  Proof.
    iSplit.
    - iApply own_trig_split_bottom_1.
    - iApply own_trig_split_bottom_2.
  Qed.
  
  Lemma own_trig_glue_top
    {n : nat}
    (p q : nat)
    (Δ : triangle loc n)
    (τ : β_tape n)
    (αs : fin_list loc (S n))
    (ls : fin_list (list (fin 2)) (S n)) :
    own_trig (S p) (S q) Δ τ ∗
    own_top_list p q αs ls ⊣⊢
    own_trig p q (triangle_glue_top Δ αs) (triangle_glue_top τ ls).
  Proof.
    rewrite -{1}(triangle_top_glue Δ αs) -{1}(triangle_top_glue τ ls)
            -{1}(triangle_remove_glue_top Δ αs) -{1}(triangle_remove_glue_top τ ls).
    remember (triangle_glue_top Δ αs) as Δ'.
    remember (triangle_glue_top τ ls) as τ'.
    rewrite own_trig_split_top.
    iSplit;
      iIntros "[Hτ Hl]";
      iFrame.
  Qed.

  Lemma own_trig_glue_top_1
    {n : nat}
    (p q : nat)
    (Δ : triangle loc n)
    (τ : β_tape n)
    (αs : fin_list loc (S n))
    (ls : fin_list (list (fin 2)) (S n)) :
    own_trig (S p) (S q) Δ τ ∗
    own_top_list p q αs ls -∗
    own_trig p q (triangle_glue_top Δ αs) (triangle_glue_top τ ls).
  Proof.
    iApply (bi.equiv_entails_1_1 _ _ (own_trig_glue_top _ _ _ _ _ _)).
  Qed.

  Lemma own_trig_glue_top_2
    {n : nat}
    (p q : nat)
    (Δ : triangle loc n)
    (τ : β_tape n)
    (αs : fin_list loc (S n))
    (ls : fin_list (list (fin 2)) (S n)) :
    own_trig p q (triangle_glue_top Δ αs) (triangle_glue_top τ ls) -∗
    own_trig (S p) (S q) Δ τ ∗
    own_top_list p q αs ls.
  Proof.
    iApply (bi.equiv_entails_1_2 _ _ (own_trig_glue_top _ _ _ _ _ _)).
  Qed.
  
  Lemma own_trig_glue_bottom
    {n : nat}
    (p q : nat)
    (Δ : triangle loc n)
    (τ : β_tape n)
    (αs : fin_list loc (S n))
    (ls : fin_list (list (fin 2)) (S n)) :
    own_trig p (S q) Δ τ ∗
    own_bottom_list p q αs ls ⊣⊢
    own_trig p q (triangle_glue_bottom Δ αs) (triangle_glue_bottom τ ls).
  Proof.
    rewrite -{1}(triangle_bottom_glue Δ αs) -{1}(triangle_bottom_glue τ ls)
            -{1}(triangle_remove_glue_bottom Δ αs) -{1}(triangle_remove_glue_bottom τ ls).
    rewrite own_trig_split_bottom //.
  Qed.

  Lemma own_trig_glue_bottom_1
    {n : nat}
    (p q : nat)
    (Δ : triangle loc n)
    (τ : β_tape n)
    (αs : fin_list loc (S n))
    (ls : fin_list (list (fin 2)) (S n)) :
    own_trig p (S q) Δ τ ∗
    own_bottom_list p q αs ls -∗
    own_trig p q (triangle_glue_bottom Δ αs) (triangle_glue_bottom τ ls).
  Proof.
    iApply (bi.equiv_entails_1_1 _ _ (own_trig_glue_bottom _ _ _ _ _ _)).
  Qed.

  Lemma own_trig_glue_bottom_2
    {n : nat}
    (p q : nat)
    (Δ : triangle loc n)
    (τ : β_tape n)
    (αs : fin_list loc (S n))
    (ls : fin_list (list (fin 2)) (S n)) :
    own_trig p q (triangle_glue_bottom Δ αs) (triangle_glue_bottom τ ls) -∗
    own_trig p (S q) Δ τ ∗
    own_bottom_list p q αs ls.
  Proof.
    iApply (bi.equiv_entails_1_2 _ _ (own_trig_glue_bottom _ _ _ _ _ _)).
  Qed.
  
  Lemma own_top_list_split_1
    {n : nat}
    (p q : nat)
    (αs : fin_list loc (S n))
    (ls : fin_list (list (fin 2)) (S n)) :
    own_top_list p q αs ls -∗
    own_bernoulli_tape (fin_list_head αs) p q (fin_list_head ls) ∗
    own_top_list p (S q) (fin_list_tail αs) (fin_list_tail ls).
  Proof.
    iIntros "[Hh Hτ]".
    fold fin_enum.
    iSplitL "Hh".
    - rewrite Nat.add_0_r //.
    - rewrite big_sepL_fmap.
      erewrite big_opL_ext; first done.
      move=>_ i _ /=.
      rewrite Nat.add_succ_r !fin_list_get_FS //.
  Qed.

   Lemma own_top_list_split_2
    {n : nat}
    (p q : nat)
    (αs : fin_list loc (S n))
    (ls : fin_list (list (fin 2)) (S n)) :
    own_bernoulli_tape (fin_list_head αs) p q (fin_list_head ls) ∗
    own_top_list p (S q) (fin_list_tail αs) (fin_list_tail ls) -∗
    own_top_list p q αs ls.
  Proof.
    iIntros "[Hh Hτ]".
    fold fin_enum.
    iSplitL "Hh".
    - rewrite Nat.add_0_r //.
    - rewrite big_sepL_fmap.
      erewrite big_opL_ext; first done.
      move=>_ i _ /=.
      rewrite Nat.add_succ_r !fin_list_get_FS //.
  Qed.

  Lemma own_top_list_split
    {n : nat}
    (p q : nat)
    (αs : fin_list loc (S n))
    (ls : fin_list (list (fin 2)) (S n)) :
    own_top_list p q αs ls ⊣⊢
    own_bernoulli_tape (fin_list_head αs) p q (fin_list_head ls) ∗
    own_top_list p (S q) (fin_list_tail αs) (fin_list_tail ls).
  Proof.
    iSplit.
    - iApply own_top_list_split_1.
    - iApply own_top_list_split_2.
  Qed.

  Lemma own_top_list_cons
    {n : nat}
    (p q : nat)
    (α : loc)
    (l : list (fin 2))
    (αs : fin_list loc n)
    (ls : fin_list (list (fin 2)) n) :
    own_bernoulli_tape α p q l ∗
    own_top_list p (S q) αs ls ⊣⊢
    own_top_list p q (fin_cons α αs) (fin_cons l ls).
  Proof.
    rewrite -{1}(fin_list_head_cons α αs)
            -{1}(fin_list_head_cons l ls)
            -{1}(fin_list_tail_cons α αs)
            -{1}(fin_list_tail_cons l ls).
    rewrite own_top_list_split //.
  Qed.

  Lemma own_top_list_cons_1
    {n : nat}
    (p q : nat)
    (α : loc)
    (l : list (fin 2))
    (αs : fin_list loc n)
    (ls : fin_list (list (fin 2)) n) :
    own_bernoulli_tape α p q l ∗
    own_top_list p (S q) αs ls -∗
    own_top_list p q (fin_cons α αs) (fin_cons l ls).
  Proof.
    iApply (bi.equiv_entails_1_1 _ _ (own_top_list_cons _ _ _ _ _ _)).
  Qed.

  Lemma own_top_list_cons_2
    {n : nat}
    (p q : nat)
    (α : loc)
    (l : list (fin 2))
    (αs : fin_list loc n)
    (ls : fin_list (list (fin 2)) n) :
    own_top_list p q (fin_cons α αs) (fin_cons l ls) -∗
    own_bernoulli_tape α p q l ∗
    own_top_list p (S q) αs ls.
  Proof.
    iApply (bi.equiv_entails_1_2 _ _ (own_top_list_cons _ _ _ _ _ _)).
  Qed.

  Lemma own_trig_1
    (p q : nat)
    (αs : fin_list loc 1)
    (ls : fin_list (list (fin 2)) 1) :
    own_trig p q (trig_snoc trig_nil αs) (trig_snoc trig_nil ls)
    ⊣⊢ own_bernoulli_tape (fin_list_head αs) p q (fin_list_head ls).
  Proof.
    inv_fin_list αs => α αs.
    inv_fin_list αs.
    inv_fin_list ls => l ls.
    inv_fin_list ls.
    unfold own_trig.
    rewrite !big_sepL_singleton !Nat.add_0_r //.
  Qed.

  Definition own_polya_tape
    {n : nat}
    (p q : nat)
    (Δ : triangle loc n)
    (l : list (fin (S n)))
    := (∃ (lτ : list (fin_list (fin 2) n)),
           own_trig p q Δ (β_fold lτ) ∗ ⌜l = fin_list_fin_2_sum <$> lτ⌝
       )%I.
  
  Lemma own_top_list_presample :
    ∀ (e : expr) (p q n : nat)
      (αs : fin_list loc (S n))
      (ls : fin_list (list (fin 2)) (S n))
      (Φ : val → iProp Σ),
    to_val e = None →
    own_top_list p q αs ls ∗
    (∀ (i : fin 2),
       own_top_list p q αs (β_list_hsup_first ls i) -∗
       WP e [{ v, Φ v }]
    ) ⊢ WP e [{ v, Φ v }].
  Proof.
    iIntros (e p q n αs ls Φ e_not_val) "[Hαs Hnext]".
    iPoseProof (own_top_list_split_1 with "Hαs") as "[Hα Hαs]".
    wp_apply (twp_presample_bernoulli with "[$Hα Hαs Hnext]"); first done.
    iIntros (i) "Hα".
    wp_apply "Hnext".
    iPoseProof (own_top_list_cons_1 with "[$Hα $Hαs]") as "Hαs".
    rewrite -fin_list_cons_head_tail //.
  Qed.

  Lemma own_trig_presample :
    ∀ (e : expr) (p q n : nat)
      (Δ : triangle loc n)
      (τ : β_tape n)
      (Φ : val → iProp Σ),
    to_val e = None →
    own_trig p q Δ τ ∗
    (∀ (i : fin_list (fin 2) n),
       own_trig p q Δ (β_hsup τ i) -∗
       WP e [{ v, Φ v }]
    ) ⊢ WP e [{ v, Φ v }].
  Proof.
    iIntros (e p q n).
    iInduction (n) as [|n] "IH" forall (p q).
    - iIntros (Δ τ Φ e_not_val) "[HΔ Hnext]".
      inv_triangle Δ.
      inv_triangle τ.
      simpl.
      wp_apply ("Hnext" $! fin_nil with "HΔ").
    - iIntros (Δ τ Φ e_not_val) "[HΔ Hnext]".
      destruct n.
        { inv_triangle τ => τ lτ.
          inv_triangle Δ => Δ lΔ.
          inv_triangle τ.
          inv_triangle Δ.
          rewrite own_trig_1.
          wp_apply (twp_presample_bernoulli with "[$HΔ Hnext]") as (i) "Hα";
            first done.
          wp_apply ("Hnext" $! (fin_cons i fin_nil)).
          full_inv_fin.
          - simpl.
            rewrite own_trig_1 //.
          - simpl.
            rewrite own_trig_1 //.
        } 
      iPoseProof (own_trig_split_top with "HΔ") as "[HΔ Hα]".
        wp_apply (own_top_list_presample with "[$Hα HΔ Hnext]") as (i) "Hα";
          first done.
      full_inv_fin.
      + iPoseProof (own_trig_glue_top_1 with "[$Hα $HΔ]") as "HΔ".
        rewrite -triangle_glue_remove_top.
        iPoseProof (own_trig_split_bottom with "HΔ") as "[HΔ Hα]".
        rewrite !triangle_remove_bottom_glue_top !triangle_bottom_glue_top
                -triangle_remove_top_bottom β_list_hsup_first_fin_tail
                -triangle_top_remove_bottom -triangle_glue_remove_top.
        wp_apply ("IH" with "[] [$HΔ Hα Hnext]") as (i) "HΔ"; first done.
        wp_apply ("Hnext" $! (fin_cons 0%fin i)).
        cbv [β_list_hsup_first].
        rewrite fin_list_head_cons triangle_top_bottom_first.
        iPoseProof (own_trig_glue_bottom_1 with "[$Hα $HΔ]") as "HΔ".
        rewrite -triangle_glue_remove_bottom.
        simpl.
        cbv [β_list_hsup_first].
        rewrite !triangle_bottom_split_cons //.
      + wp_apply ("IH" with "[] [$HΔ Hα Hnext]") as (i) "HΔ"; first done.
        wp_apply ("Hnext" $! (fin_cons 1%fin i)).
        iPoseProof (own_trig_glue_top_1 with "[$Hα $HΔ]") as "HΔ".
        rewrite -triangle_glue_remove_top //.
  Qed.
  
End Polya.                        
