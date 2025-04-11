From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils.

#[local] Open Scope R.

Class bernoulli_spec `{!erisGS Σ} (bernoulli_prog : val) :=
  BernoulliSpec {
      
      twp_bernoulli_scale :
      ∀ (N M : nat) (ε ε1 ε2 : R) 
        (p := N / S M),
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

  bernoulli_case :
      ∀ (N M : nat),
        (*TODO: See to add N <= S M  *)
        [[{True}]]
          bernoulli_prog #() #N #M
          [[{v, RET v; ⌜v = #0⌝ ∨ ⌜v = #1⌝}]];

  own_bernoulli_tape :
      loc → nat → nat → list (fin 2) → iPropI Σ;
  
  twp_presample_bernoulli : 
      ∀ (e : expr) (α : loc) (Φ : val → iProp Σ) 
        (N M : nat) (ns : list (fin 2)),
        to_val e = None →
        own_bernoulli_tape α N M ns ∗ 
        (∀ i : fin 2, 
           own_bernoulli_tape α N M (ns ++ [i]) -∗ WP e [{ v, Φ v }]) 
        ⊢ WP e [{ v, Φ v }];
  
  twp_presample_bernoulli_adv_comp : 
      ∀ (e : expr) (α : loc) (Φ : val → iProp Σ) 
        (N M : nat) (ns : list (fin 2)) (ε : R) (D : fin 2 → R),
        N ≤ M + 1 →
        (∀ i : fin 2, 0 <= D i) →
        D 0%fin * (1 - N / (M + 1)) + D 1%fin * (N / (M + 1)) = ε →
        to_val e = None → 
        own_bernoulli_tape α N M ns ∗ 
        ↯ ε ∗ 
        (∀ i : fin 2, 
           ↯ (D i) ∗ own_bernoulli_tape α N M (ns ++ [i]) -∗ 
           WP e [{ v, Φ v }])
        ⊢ WP e [{ v, Φ v }];

  twp_bernoulli_tape :
      ∀ (N M : nat) (α : loc) (ns : list (fin 2)) (n : fin 2),
        [[{ own_bernoulli_tape α N M (n::ns) }]]
          bernoulli_prog (#lbl:α) #N #M
          [[{ RET #n ; own_bernoulli_tape α N M ns }]];
      
      twp_presample_bernoulli_planner :
      ∀ (N M : nat) (e : expr) (ε : nonnegreal) (L : nat) 
        (α : loc) (Φ : val → iProp Σ) (prefix : list (fin 2)) 
        (suffix : list (fin 2) → list (fin 2)),
        (0 < N < S M)%nat →
        to_val e = None →
        (∀ junk : list (fin 2), 
           (0 < length (suffix (prefix ++ junk)) <= L)%nat) → 
        0 < ε → 
        ↯ ε ∗ 
        own_bernoulli_tape α N M prefix ∗
        ((∃ junk : list (fin 2), 
      own_bernoulli_tape α N M (prefix ++ junk ++ suffix (prefix ++ junk))) 
         -∗ WP e [{ v, Φ v }])
        ⊢ WP e [{ v, Φ v }]
    }.

Set Default Proof Using "Type*".

Section BernoulliSpecLemmas.

  Context `{!erisGS Σ}.
  Context `{!bernoulli_spec bernoulli}.
 
  #[local] Ltac done ::= 
    solve[
      lia |
      lra |
      nra |
      real_solver  |
      tactics.done |
      auto
      ].
  
  Lemma bernoulli_success_spec (N M : nat) (ε ε' : R) (p := N / S M) :
    (0 <= ε')%R →
    ε = (ε' * (N / S M)) → 
    [[{↯ ε ∗ ↯ (1 - (N / S M))}]]
      bernoulli #() #N #M 
    [[{ v, RET v; ↯ ε' ∗ ⌜v = #1⌝ }]].
  Proof.
    iIntros (Hε' ->) "%Φ [Herr Hcost] HΦ".
    destruct (decide (S M < N)%nat) as [Hlt | Hge%not_lt].
    { cred_contra. rewrite Rcomplements.Rlt_minus_l. simpl_expr. }
    iPoseProof (ec_combine with "[$Herr $Hcost]") as "Herr".
    wp_apply (twp_bernoulli_scale _ _ _ 1 ε' with "Herr")%R; [lia|lra..|].
    iIntros "%k [(_ & Herr) | (-> & Herr)]"; first cred_contra. 
    by iApply "HΦ"; iFrame.
  Qed.

  Lemma bernoulli_success_spec_simple (N M : nat) :
    [[{↯ (1 - (N / S M))}]]
      bernoulli #() #N #M
    [[{ v, RET v; ⌜v = #1⌝ }]].
  Proof.
    iIntros (Φ) "Herr HΦ".
    iMod ec_zero as "Hzero".
    wp_apply (bernoulli_success_spec _ _ 0%R 0%R with "[$Herr $Hzero]") as "%v [_ Hv]" => //.
    iApply ("HΦ" with "Hv").
  Qed.

  Lemma bernoulli_failure_spec (N M : nat) (ε ε' : R) :
    (0 <= ε')%R →
    ε = (ε' * (1 - N / S M)) →
    [[{↯ ε ∗ ↯ (N / S M)}]] 
      bernoulli #() #N #M 
    [[{ v, RET v; ↯ ε' ∗ ⌜v = #0⌝ }]].
  Proof.
    iIntros (Hε ->) "%Φ [Herr Hcost] HΦ".
    destruct (decide (S M < N)%nat) as [Hlt |Hge%not_lt].
    { cred_contra. simpl_expr. }
    iPoseProof (ec_combine with "[$Herr $Hcost]") as "Herr".
    wp_apply (twp_bernoulli_scale _ _ _ ε' 1 with "[$Herr]")%R => //.
    iIntros "%k [(-> & Herr) | (-> & Herr)]";last cred_contra.
    by iApply "HΦ"; iFrame.
  Qed.

  Lemma bernoulli_failure_spec_simple (N M : nat) :
    [[{↯ (N / S M)}]] 
      bernoulli #() #N #M 
    [[{ v, RET v; ⌜v = #0⌝ }]].
  Proof.
    iIntros (Φ) "Herr HΦ".
    iMod ec_zero as "Hzero".
    wp_apply (bernoulli_failure_spec _ _ 0%R 0%R with "[$Herr $Hzero]") as "%v [_ Hv]" => //.
    iApply ("HΦ" with "Hv").
  Qed.
End BernoulliSpecLemmas.
