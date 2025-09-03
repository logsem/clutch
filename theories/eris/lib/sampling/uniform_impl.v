From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import abstract_planner distr_impl utils.

Instance uniform_impl {N : nat} :
  distr_impl (dmap (LitV ∘ LitInt ∘ Z.of_nat ∘ fin_to_nat) (dunif (S N))).
Proof.
  
  refine (MkDistrImpl _
            (λ: "α", rand("α") #N) (alloc #N)
            loc
            (λ _ _ Δ l, ∃ l', Δ ↪ (N; l') ∗
                              ⌜l = fmap (λ (k : fin (S N)), #k) l'⌝)%I
            (λ _ _ Δ α, ⌜α = #lbl:Δ⌝)%I #() _ _ _ _).
  - iIntros (Σ erisGS0 D ε L ε_ge_0 D_bounds D_sum Φ) "Herr HΦ".
    wp_pures.
    set (D' (k : fin (S N)) := D #k).
    wp_apply (twp_couple_rand_adv_comp _ _ _ _ D' with "Herr [HΦ]").
    { move=>k. apply D_bounds. }
    { rewrite (dmap_expected_value _ _ _ L) in D_sum;
        last (move=>a; apply D_bounds).
      rewrite D_sum /pmf /dunif !(S_INR N) /D' /=.
      apply SeriesC_ext.
      move=>k.
      lra.
    }
    iIntros (k) "Herr".
    by iApply "HΦ".
  - iIntros (Σ erisGS0 Φ) "_ HΦ".
    wp_apply (twp_alloc_tape _ N _ _ _ Φ with "[$] [HΦ]") as (α) "Htape".
    iApply "HΦ".
    by iFrame.
  - iIntros (Σ erisGS0 e ε Δ l D L Φ e_not_val ε_ge_0 D_bounds D_sum) "(Herr & (%l' & Htape & ->) & Hnext)".
    set (D' (k : fin (S N)) := D #k).
    unshelve wp_apply (twp_presample_adv_comp _ N _ _ _ _ _ _ D' _ e_not_val with "[$Herr $Htape Hnext]").
    { move=>k. apply D_bounds. }
    { rewrite (dmap_expected_value _ _ _ L) in D_sum;
        last (move=>a; apply D_bounds).
      rewrite -D_sum /pmf /dunif !(S_INR N) /D' /=.
      apply SeriesC_ext.
      move=>k.
      lra.
    }
    iIntros (k) "[Herr Htape]".
    wp_apply "Hnext".
    iFrame.
    rewrite fmap_app //.
  - iIntros (Σ erisGS0 α Δ l v Φ) "[(%l' & Htape & %Heq) ->] HΦ".
    destruct l' as [|v' l']; first discriminate.
    injection Heq as -> ->.
    wp_pures.
    wp_apply (twp_rand_tape with "Htape") as "Htape".
    iApply "HΦ".
    iExists l'.
    by iFrame.
Defined.
