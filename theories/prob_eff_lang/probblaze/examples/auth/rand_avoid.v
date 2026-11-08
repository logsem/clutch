(* Presampling onto two tapes, coupled by a bijection, where the value put on
   the left tape avoids a list of bad values; the error credit pays for the
   excluded values.  This is [brel_couple_TT] with the "avoid" coupling of
   [brel_couple_couple_avoid]; it is what a one-time MAC proof needs: the
   verifier's key is read lazily, from a tape, after the forgery attempt. *)

From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext fin.
From clutch.prob Require Import couplings_app.
From clutch.prob_eff_lang.probblaze Require Import logic.
From clutch.prob_eff_lang.probblaze Require Import syntax notation semantics metatheory erasure.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws spec_ra coupling_rules.

Section wp.
  Context `{!probblazeRGS Σ}.

  Lemma wp_couple_tapes_avoid N (l : list (fin (S N))) f `{Bij nat nat f} E e α αₛ ns nsₛ Φ :
    NoDup l →
    (∀ n, n < S N → f n < S N)%nat →
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (N; nsₛ) ∗ ↯ (length l / S N) ∗
    (∀ n : fin (S N), ⌜n ∉ l⌝ -∗
       α ↪N (N; ns ++ [fin_to_nat n]) ∗ αₛ ↪ₛN (N; nsₛ ++ [f n]) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hl Hdom) "(>Hα & >Hαₛ & Hε & Hwp)".
    destruct (restr_bij_fin (S N) f Hdom) as [g [HBij Hfg]].
    iDestruct "Hα" as (fs) "(<-&Hα)".
    iDestruct "Hαₛ" as (fsₛ) "(<-&Hαₛ)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1 & Hl1) & Hauth2 & Hε2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2&Hl2)/=".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ec_supply_ec_inv with "Hε2 Hε") as %(ε & ε' & -> & Hε).
    iApply (spec_coupl_erasables
              (λ σ2 σ2', ∃ n : fin (S N), n ∉ l ∧
                 σ2 = state_upd_tapes <[α := ((N; fs ++ [n]) : syntax.tape)]> σ1 ∧
                 σ2' = state_upd_tapes <[αₛ := ((N; fsₛ ++ [g n]) : syntax.tape)]> σ1')
              (state_step σ1 α) (state_step σ1' αₛ) ε ε'); [done|..].
    { rewrite (state_step_unfold σ1 α N fs) // (state_step_unfold σ1' αₛ N fsₛ) //.
      apply ARcoupl_map; first apply cond_nonneg.
      pose proof (f_inv_bij g) as Hbij'.
      eapply ARcoupl_mono; [done|done| |by rewrite Hε|].
      2: apply (ARcoupl_dunif_avoid_bij (S N) l (f_inv g) Hl).
      intros n m [Hn Hnm]. exists n. split; first done. split; first done.
      do 2 f_equal. rewrite Hnm. by rewrite f_inv_cancel_r. }
    { by eapply state_step_erasable. }
    { by eapply state_step_erasable. }
    iIntros (σ2 σ2' (n & Hn & -> & ->)).
    iApply spec_coupl_ret.
    iMod (ghost_map_update ((N; fs ++ [n]) : syntax.tape) with "Ht1 Hα") as "[$ Hα]".
    iMod (ghost_map_update ((N; fsₛ ++ [g n]) : syntax.tape) with "Ht2 Hαₛ") as "[$ Hαₛ]".
    iMod (ec_supply_decrease with "Hε2 Hε") as (x1 x3 Hx ?) "Hε2".
    iModIntro. iMod "Hclose'" as "_". iFrame.
    iSplitL "Hε2".
    { iApply ec_supply_eq; [|done]. simplify_eq/=. lra. }
    iApply ("Hwp" $! n with "[//]").
    iSplitL "Hα".
    { iExists _. iFrame. rewrite fmap_app //. }
    iExists _. iFrame. rewrite fmap_app -Hfg //.
  Qed.

End wp.

Section rel.
  Context `{!probblazeRGS Σ}.

  Lemma rel_couple_TT_avoid (N : nat) (l : list (fin (S N))) f `{Bij nat nat f} E e1 e2 X R α αₛ ns nsₛ :
    NoDup l →
    (∀ n, n < S N → f n < S N)%nat →
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (N; nsₛ) ∗ ↯ (length l / S N) ∗
    (∀ n : fin (S N), ⌜n ∉ l⌝ -∗
       α ↪N (N; ns ++ [fin_to_nat n]) ∗ αₛ ↪ₛN (N; nsₛ ++ [f n]) -∗ REL e1 ≤ e2 @ E <|X|> {{R}})
    ⊢ REL e1 ≤ e2 @ E <|X|> {{R}}.
  Proof.
    iIntros (Hl Hdom) "(Hα & Hαs & Hε & Hlog)".
    rewrite {2}(rel_unfold E e1 e2 X R) /rel_pre obs_refines_eq /obs_refines_def.
    iIntros (k1 k2 S) "Hkwp %K2 %ε' He2 Hnais Herr' Hpos/=".
    iApply (wp_couple_tapes_avoid N l f); [done|done|].
    iFrame.
    iIntros (n Hn) "(Hα & Hαs)".
    iSpecialize ("Hlog" $! n Hn with "[$]").
    rewrite !rel_unfold /rel_pre obs_refines_eq /obs_refines_def.
    iApply ("Hlog" with "Hkwp He2 Hnais Herr' Hpos").
  Qed.

  Lemma brel_couple_TT_avoid (N : nat) (l : list (fin (S N))) f `{Bij nat nat f} E e1 e2 X R α αₛ ns nsₛ :
    NoDup l →
    (∀ n, n < S N → f n < S N)%nat →
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (N; nsₛ) ∗ ↯ (length l / S N) ∗
    (∀ n : fin (S N), ⌜n ∉ l⌝ -∗
       α ↪N (N; ns ++ [fin_to_nat n]) ∗ αₛ ↪ₛN (N; nsₛ ++ [f n]) -∗ BREL e1 ≤ e2 @ E <|X|> {{R}})
    ⊢ BREL e1 ≤ e2 @ E <|X|> {{R}}.
  Proof.
    iIntros (??) "(Hα & Hαs & Hε & Hrel) #Hvalid Hdistinct".
    iApply (rel_couple_TT_avoid N l f); [done|done|].
    iFrame.
    iIntros (n Hn) "Hαs".
    by iApply ("Hrel" with "[//] [$] [$] [$]").
  Qed.

End rel.
