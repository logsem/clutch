From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils.

#[local] Open Scope R.

Class bernoulli_spec `{!erisGS Σ} (bernoulli_prog : val) (bernoulli_alloc : val) :=
  BernoulliSpec {
    twp_bernoulli_scale (N M : nat) (ε ε1 ε2 : R) (p := N / S M) :
      N ≤ S M →
      0 <= ε1 →
      0 <= ε2 →
      ε1 * (1 - p) + ε2 * p = ε →
      [[{↯ ε}]]
        bernoulli_prog #() #N #M
      [[{
        (k : nat), RET #k;
        (⌜k = 0%nat⌝ ∗ ↯ ε1) ∨
        (⌜k = 1%nat⌝ ∗ ↯ ε2)
      }]];

    own_bernoulli_tape :
      loc → nat → nat → list (fin 2) → iPropI Σ;

    twp_bernoulli_alloc (N M : nat) :
      [[{ True }]]
        bernoulli_alloc #N #M
      [[{ (α : loc), RET #lbl:α; own_bernoulli_tape α N M [] }]];

    twp_presample_bernoulli 
      (e : expr) (α : loc) (Φ : val → iProp Σ) 
      (N M : nat) (ns : list (fin 2)) : 
      to_val e = None →
      own_bernoulli_tape α N M ns ∗ 
      (∀ i : fin 2, own_bernoulli_tape α N M (ns ++ [i]) -∗ WP e [{ v, Φ v }]) 
      ⊢ WP e [{ v, Φ v }];


    twp_presample_bernoulli_adv_comp 
      (e : expr) (α : loc) (Φ : val → iProp Σ) 
      (N M : nat) (ns : list (fin 2)) (ε : R) (D : fin 2 → R): 
      N ≤ M + 1 →
      (∀ i : fin 2, 0 <= D i) →
      D 0%fin * (1 - N / (M + 1)) + D 1%fin * (N / (M + 1)) = ε →
      to_val e = None → 
      ↯ ε ∗ 
      own_bernoulli_tape α N M ns ∗ 
      (∀ i : fin 2, 
         ↯ (D i) ∗ own_bernoulli_tape α N M (ns ++ [i]) -∗ 
         WP e [{ v, Φ v }])
      ⊢ WP e [{ v, Φ v }];


    twp_bernoulli_tape (N M : nat) (α : loc) (ns : list (fin 2)) (n : fin 2) :
      [[{ own_bernoulli_tape α N M (n::ns) }]]
        bernoulli_prog (#lbl:α) #N #M
      [[{ RET #n ; own_bernoulli_tape α N M ns }]];

    twp_presample_bernoulli_planner 
      (N M : nat) (e : expr) (ε : nonnegreal) (L : nat) 
      (α : loc) (Φ : val → iProp Σ) (prefix : list (fin 2)) 
      (suffix : list (fin 2) → list (fin 2)) :
      (0 < N < S M)%nat →
      to_val e = None →
      (∀ junk : list (fin 2), 
         (0 < length (suffix (prefix ++ junk)) <= L)%nat) → 
      0 < ε → 
      ↯ ε ∗ 
      own_bernoulli_tape α N M prefix ∗
      ((∃ junk : list (fin 2), 
           own_bernoulli_tape α N M (prefix ++ junk ++ suffix (prefix ++ junk))) -∗ 
       WP e [{ v, Φ v }])
      ⊢ WP e [{ v, Φ v }]
    }.

Set Default Proof Using "Type*".

Section BernoulliSpecLemmas.

  Context `{!erisGS Σ}.
  Context `{!bernoulli_spec bernoulli balloc}.
 
  #[local] Ltac done ::= 
    solve[
      lia |
      lra |
      nra |
      real_solver  |
      tactics.done |
      auto
    ].
  Lemma bernoulli_case (N M : nat) :
    N ≤ S M →
    [[{True}]]
      bernoulli #() #N #M
    [[{v, RET v; ⌜v = #0⌝ ∨ ⌜v = #1⌝}]].
  Proof.
    iIntros "% %Φ _ HΦ".
    iMod ec_zero as "Herr".
    wp_apply (twp_bernoulli_scale N M _ 0 0 with "Herr")%R as "% [[-> _] | [-> _]]" => //;
    iApply "HΦ" => //.
  Qed.

  Lemma bernoulli_success_spec (N M : nat) (ε ε' : R) (p := N / S M) :
    (0 <= ε')%R →
    ε = (ε' * (N / S M)) → 
    [[{↯ ε ∗ ↯ (1 - (N / S M))}]]
      bernoulli #() #N #M 
    [[{ RET #1; ↯ ε'}]].
  Proof.
    iIntros (Hε' ->) "%Φ [Herr Hcost] HΦ".
    iAssert (⌜N ≤ S M⌝)%I with "[Hcost]" as "%H_N_le_SM".
    { destruct (decide (S M < N)%nat); last by iPureIntro; done.
      cred_contra. rewrite Rcomplements.Rlt_minus_l. simpl_expr. }
    iPoseProof (ec_combine with "[$Herr $Hcost]") as "Herr".
    wp_apply (twp_bernoulli_scale _ _ _ 1 ε' with "Herr")%R; try done.
    iIntros "%k [(_ & Herr) | (-> & Herr)]"; first cred_contra. 
    by iApply "HΦ"; iFrame.
  Qed.

  Lemma bernoulli_success_spec_simple (N M : nat) :
    [[{↯ (1 - (N / S M))}]]
      bernoulli #() #N #M
    [[{ RET #1; True }]].
  Proof.
    iIntros (Φ) "Herr HΦ".
    iMod ec_zero as "Hzero".
    wp_apply (bernoulli_success_spec _ _ 0 0 with "[$Herr $Hzero]") as "_" => //.
    by iApply "HΦ".
  Qed.

  Lemma bernoulli_failure_spec (N M : nat) (ε ε' : R) :
    (0 <= ε')%R →
    ε = (ε' * (1 - N / S M)) →
    [[{↯ ε ∗ ↯ (N / S M)}]] 
      bernoulli #() #N #M 
    [[{ RET #0; ↯ ε'}]].
  Proof.
    iIntros (Hε ->) "%Φ [Herr Hcost] HΦ".
    iAssert (⌜N ≤ S M⌝)%I with "[Hcost]" as "%H_N_le_SM".
    { destruct (decide (S M < N)%nat) as [Hlt |Hge%not_lt];
      [cred_contra; simpl_expr | done]. }
    iPoseProof (ec_combine with "[$Herr $Hcost]") as "Herr".
    wp_apply (twp_bernoulli_scale _ _ _ ε' 1 with "[$Herr]")%R => //.
    iIntros "%k [(-> & Herr) | (-> & Herr)]"; last cred_contra.
    by iApply "HΦ"; iFrame.
  Qed.

  Lemma bernoulli_failure_spec_simple (N M : nat) :
    [[{↯ (N / S M)}]] 
      bernoulli #() #N #M 
    [[{ RET #0; True }]].
  Proof.
    iIntros (Φ) "Herr HΦ".
    iMod ec_zero as "Hzero".
    wp_apply (bernoulli_failure_spec _ _ 0%R 0%R with "[$Herr $Hzero]") as "_" => //.
    by iApply "HΦ".
  Qed.


  Lemma bernoulli_0 (M : nat) : 
    [[{True}]] 
      bernoulli #() #0 #M 
    [[{ RET #0; True }]].
  Proof.
    iIntros.
    iMod ec_zero as "Herr".
    rewrite -Nat2Z.inj_0.
    iApply (bernoulli_failure_spec_simple with "[Herr]").
    { iApply (ec_eq with "Herr"). simpl_expr. }
    done.
  Qed.

  Lemma bernoulli_1 (M : nat) : 
    [[{True}]] 
      bernoulli #() #(S M) #M 
    [[{ RET #1; True }]].
  Proof.
    iIntros.
    iMod ec_zero as "Herr".
    rewrite -Nat2Z.inj_0.
    iApply (bernoulli_success_spec_simple with "[Herr]").
    { iApply (ec_eq with "Herr"). simpl_expr. }
    done.
  Qed.
  
  Lemma twp_bernoulli_n_success_presample_1
    (e : expr) (α : loc) (Φ : val → iProp Σ)
    (p q r : nat) (ns : list (fin 2)) :
    (p = q + 1)%nat →
    to_val e = None →
    own_bernoulli_tape α p q ns ∗
    (own_bernoulli_tape α p q (ns ++ repeat 1%fin r) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }].
  Proof.
    iIntros (-> e_not_val) "[Hα Hnext]".
    iInduction (r) as [|r] "IH" forall (Φ ns).
    - wp_apply "Hnext".
      rewrite app_nil_r //.
    - iMod ec_zero as "Herr".
      wp_apply
        (twp_presample_bernoulli_adv_comp _ α _ (q + 1) q _ 0%R
           (λ k, if bool_decide (k = 0)%fin then 1%R else 0%R)
           ltac:(reflexivity) with "[$Hα Hnext $Herr]")
        as (i) "H";
        try done.
      {
        rewrite plus_INR INR_1 Rdiv_diag //.
      }
      case_bool_decide;
        iDestruct "H" as "[Herr Hα]";
        first cred_contra.
      replace i with (1%fin : fin 2) by full_inv_fin.
      wp_apply ("IH" with "Hα") as "Hα".
      wp_apply "Hnext".
      rewrite -app_assoc //.
  Qed.

  Lemma twp_bernoulli_n_success_presample
    (e : expr) (α : loc) (Φ : val → iProp Σ)
    (p q r : nat) (ns : list (fin 2)) (ε : R) :
    (0 < p)%nat →
    (p ≤ q + 1)%nat →
    (0 < ε)%R → 
    to_val e = None →
    ↯ ε ∗
    own_bernoulli_tape α p q ns ∗
    (if bool_decide (r = 0)%nat
     then own_bernoulli_tape α p q ns -∗ WP e [{ Φ }]
     else
       ∀ (suf : list (fin 2)), ⌜list_sum $ fin_to_nat <$> suf = (r - 1)%nat⌝ -∗ own_bernoulli_tape α p q (ns ++ suf ++ [1%fin]) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }].
  Proof.
    iIntros (p_gt_0 p_le_Sq).
    destruct (decide (p = q + 1)%nat) as [-> | p_ne_Sq].
    {
      iIntros (_ e_not_val) "(_ & Hα & Hnext)".
      wp_apply (twp_bernoulli_n_success_presample_1 _ _ _ _ _ r with "[$Hα Hnext]") as "Hα"; try done.
      case_bool_decide as is_r_0.
      { rewrite is_r_0 app_nil_r.
        by wp_apply "Hnext".
      }
      destruct r; first lia.
      rewrite -(Nat.add_1_r r) repeat_app.
      wp_apply ("Hnext" with "[] Hα").
      iPureIntro.
      rewrite fmap_repeat list_sum_repeat /=.
      lia.
    }
    iInduction (r) as [|r] "IH" forall (Φ ns ε);
      iIntros (ε_pos e_not_val) "(Herr & Hα & Hnext)".
    - by wp_apply "Hnext".
    - iRevert "Hα Hnext".
      assert (p < q + 1)%nat as p_lt_Sq by lia.
      set (s0 := (p / (q + 1))%R).
      set (s1 := (1 - s0)%R).
      set (s2 := (1 / s1)%R).
      set (s3 := ((s2 + 1) / 2)%R).
      set (s4 := (1 - s3 * s1)%R).
      set (s5 := (s4 / s0)%R).
      assert (0 < q + 1)%R by real_solver.
      assert (0 < p)%R by real_solver.
      assert (0 < s0 < 1)%R.
      {
        unfold s0.
        split; simpl_expr.
        rewrite -INR_1 -plus_INR.
        by apply lt_INR.
      }
      assert (0 < s1 < 1)%R by (unfold s1; lra).
      assert (1 < s2)%R.
      { unfold s2. simpl_expr. }
      assert (1 < s3)%R by (unfold s3; lra).
      assert (0 < s4)%R.
      {
        unfold s4.
        rewrite -Rcomplements.Rminus_lt_0.
        unfold s3, s2.
        rewrite -Rmult_div_swap -Rcomplements.Rdiv_lt_1; last lra.
        rewrite Rmult_plus_distr_r -Rmult_div_swap Rmult_div_l; lra.
      }
      assert (0 < s5)%R.
      { unfold s5. simpl_expr. }
      assert (s5 * s0 + s3 * s1 = 1)%R.
      {
        unfold s5, s4.
        rewrite -Rmult_div_swap Rmult_div_l; lra.
      }
      iRevert (ns).
      iApply (ec_ind_amp _ s3 with "[] Herr"); try done.
      iModIntro.
      clear ε ε_pos.
      iIntros (ε ε_pos) "IHec Herr %ns Hα Hnext".
      set (D (i : fin 2) := match i with
                            | 0%fin => (s3 * ε)%R
                            | _ => (s5 * ε)%R
                            end).
      wp_apply (twp_presample_bernoulli_adv_comp _ α _ p q _ ε D with "[IHec $Herr $Hα Hnext]"); try done.
      { unfold D.
        move=>i.
        inv_fin i => [|_]; nra.
      }
      { simpl.
        fold s0 s1.
        nra.
      }
      iFrame.
      iIntros (i).
      full_inv_fin; simpl.
      + iIntros "[Herr Hα]".
        wp_apply ("IHec" with "Herr Hα").
        iIntros (suf sum_suf) "Hα".
        rewrite -app_assoc (app_assoc _ suf).
        wp_apply "Hnext"; last iFrame.
        { rewrite -sum_suf //. }
      + iClear "IHec".
        iIntros "[Herr Hα]".
        wp_apply "IH"; last iFrame.
        { iPureIntro. nra. }
        { done. }
        case_bool_decide as is_r_0.
        { iIntros "Hα".
          wp_apply ("Hnext" $! []); last iFrame.
          rewrite is_r_0 //.
        } 
        iIntros (suf sum_suf) "Hα".
        rewrite -app_assoc (app_assoc _ suf).
        wp_apply "Hnext"; last iFrame.
        rewrite /= sum_suf //.
        iPureIntro.
        lia.
  Qed.
  
End BernoulliSpecLemmas.
