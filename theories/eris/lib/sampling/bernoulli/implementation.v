From clutch.eris Require Import eris.
From clutch.eris.lib.sampling.bernoulli Require Import tape lemmas interface.
From clutch.eris.lib.sampling Require Import utils.

#[local] Open Scope R.

#[local] Ltac done ::= 
  solve[
    lia |
    lra |
    nra |
    real_solver  |
    tactics.done |
    auto
  ].

Section BernoulliImpl.
  Context `{!erisGS Σ}.
  
  Definition bernoulli : val := 
    λ: "α" "N" "M",
      let: "x" := rand("α") "M" in 
      if: "x" < "N" then #1 else #0.

  Lemma twp_bernoulli_scale (N M : nat) (ε ε1 ε2 : R) (p := N / S M) :
    (N ≤ S M)%nat →
    0 <= ε1 →
    0 <= ε2 →
    (ε1 * (1 - p)) + (ε2 * p) = ε →
    [[{↯ ε}]]
      bernoulli #() #N #M
    [[{
        (k : nat), RET #k; 
        (⌜k = 0%nat⌝ ∗ ↯ ε1) ∨
        (⌜k = 1%nat⌝ ∗ ↯ ε2)
    }]].
  Proof.
    iIntros (HNleM ε1_pos ε2_pos Heq Φ) "Herr HΦ".
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
    wp_apply (twp_couple_rand_adv_comp1 _ _ _ ε' f with "Herr") as "%x Herr"; unfold f.
    { move=>>;
      by case_bool_decide. }
    { rewrite SeriesC_scal_l. rewrite Rmult_comm.
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
    repeat case_bool_decide; wp_pures; try lia.
    - iApply ("HΦ" $! 1)%nat; auto.
    - iApply ("HΦ" $! 0)%nat; auto.
  Qed.
  
  Lemma bernoulli_case (N M : nat) :
    [[{True}]] 
      bernoulli #() #N #M 
    [[{ v, RET v; ⌜v = #0⌝ ∨ ⌜v = #1⌝}]].
  Proof.
    iIntros "%Φ _ HΦ".
    rewrite /bernoulli; wp_pures.
    wp_apply (twp_rand with "[$]") as "%n _".
    wp_pures; case_bool_decide;
    wp_pures; iApply "HΦ"; auto.
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
    iIntros (HNone) "[(%l & Hα & %Htl) Hnext]".
    wp_apply twp_presample; first done.
    iFrame.
    iIntros (k) "Htape".
    destruct (decide (N ≤ k)) as [N_le_k | k_lt_N%not_le].
    - iApply "Hnext".
      iFrame.
      iPureIntro.
      by apply is_bernoulli_translation_app_0.
    - iApply "Hnext".
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
    iIntros (N_le_SM D_nonneg D_expected_ε HNone) "((%l & Hα & %Htl) & Herr & Hnext)".
    set f :=
      λ (n : fin (S M)), 
        if bool_decide (fin_to_nat n < N)%nat then D 1%fin else D 0%fin.
    wp_apply (twp_presample_adv_comp _ M _ _ _ _ _ _ f); unfold f; first done; last iFrame.
    { move=>>.
      case_bool_decide; apply D_nonneg.
    }
    { rewrite SeriesC_scal_l. rewrite Rmult_comm.
      simpl_expr.
      Opaque INR.
      rewrite SeriesC_case //=.
      rewrite -S_INR in D_expected_ε.
      rewrite -D_expected_ε Rmult_plus_distr_l -!Rmult_assoc
                 !(Rmult_comm _ (D _)) !Rmult_assoc.
      simpl_expr.
      rewrite Rmult_minus_distr_l.
      simpl_expr.
    }
    iIntros (n) "[Herr Hα]".
    case_bool_decide;
      wp_apply "Hnext";
      iFrame;
      iPureIntro.
    - apply is_bernoulli_translation_app_1 => //. 
    - apply is_bernoulli_translation_app_0 => //.
  Qed.
    

  Lemma twp_bernoulli_tape (N M : nat) (α : loc) (ns : list (fin 2)) (n : fin 2) :
    [[{ own_bernoulli_tape α N M (n::ns) }]]
      bernoulli (#lbl:α) #N #M
    [[{ RET #n ; own_bernoulli_tape α N M ns }]].
  Proof.
    iIntros (Φ) "Htape HΦ".
    rewrite /bernoulli {1}/own_bernoulli_tape.
    iDestruct "Htape" as "(%l & Hα & %Htl)".
    case: l Htl => [Hcontra | h t Htl]; first by apply is_bernoulli_translation_length in Hcontra. 
    wp_pures.
    wp_apply (twp_rand_tape with "Hα").
    iIntros "Hα".
    wp_pures.
    apply is_bernoulli_translation_cons in Htl as [(-> & HNleh & Htl)| (-> & HhltN & Htl)]; bool_decide.
    - wp_pures.
      iApply "HΦ".
      by iFrame.
    - wp_pures.
      iApply "HΦ".
      by iFrame.
  Qed.


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
      move=>>.
      rewrite /suffix2 bernoulli_to_tape_length tape_to_bernoulli_app.
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

  #[global] Instance bernoulli_impl : bernoulli_spec bernoulli :=
    BernoulliSpec _ _ _ twp_bernoulli_scale bernoulli_case own_bernoulli_tape twp_presample_bernoulli twp_presample_bernoulli_adv_comp twp_bernoulli_tape twp_presample_bernoulli_planner.
  
End BernoulliImpl.
