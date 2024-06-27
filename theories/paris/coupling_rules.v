(** * Coupling rules  *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.paris Require Import lifting ectx_lifting.
From clutch.prob_lang Require Import lang notation tactics metatheory erasure.
From clutch.prob_lang.spec Require Import spec_rules.
From clutch.paris Require Export primitive_laws.

Section rules.
  Context `{!parisGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

  #[local] Open Scope R.

  (** helper lemma  *)
  Lemma ARcoupl_steps_ctx_bind_r `{Countable A} (μ : distr A)
    e1' σ1' R (ε : nonnegreal) K :
    to_val e1' = None →
    ARcoupl μ (prim_step e1' σ1') R ε →
    ARcoupl μ (prim_step (fill K e1') σ1')
      (λ a '(e2', σ2'), ∃ e2'', (e2', σ2') = (fill K e2'', σ2') ∧ R a (e2'', σ2')) ε.
  Proof.
    intros Hcpl Hv.
    rewrite fill_dmap //= -(dret_id_right μ ) /=.
    eapply (ARcoupl_dbind' ε 0%NNR); [done|done|simpl; lra| |done].
    intros ? [] ?.
    apply ARcoupl_dret=>/=; [done|]. eauto.
  Qed.

  (** TODO: This should be generalizable to injective functions [N] -> [M]
      Then we can get the exact couplings with bijections as a corollary *)
  Lemma wp_couple_tapes (N M : nat) E e α αₛ ns nsₛ Φ (ε : R) :
    (N <= M)%nat →
    (S M - S N) / S M = ε →
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗
    ↯ ε ∗
    (∀ (n : fin (S N)) (m : fin (S M)),
        ⌜fin_to_nat n = fin_to_nat m⌝ -∗
        α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) -∗
        WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (NMpos NMε) "(>Hα & >Hαₛ & Hε & Hwp)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2)/=".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ec_supply_ec_inv with "Hε2 Hε") as %(?&?&->&<-).
    iApply spec_coupl_erasables; [done|..].
    { by apply ARcoupl_state_state. }
    { by eapply state_step_erasable. }
    { by eapply state_step_erasable. }
    iIntros (σ2 σ2' (n & m & nm & -> & ->)).
    iApply spec_coupl_ret.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?%lookup_total_correct.
    iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Ht1 Hα") as "[$ Hα]".
    iMod (ghost_map_update ((M; nsₛ ++ [m]) : tape) with "Ht2 Hαₛ") as "[$ Hαₛ]".
    iMod (ec_supply_decrease with "Hε2 Hε") as (????) "H".
    iModIntro. iMod "Hclose'" as "_". iFrame.
    iDestruct ("Hwp" with "[//] [$]") as "$".
    iApply ec_supply_eq; [|done].
    simplify_eq/=; lra.
  Qed.

  Lemma wp_couple_tapes_bij N f `{Bij (fin (S N)) (fin (S N)) f} E e α αₛ ns nsₛ Φ :
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (N; nsₛ) ∗
      (∀ n : fin (S N), α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (N; nsₛ ++ [f n])  -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros "(>Hα & >Hαₛ & Hwp)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2)/=".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace ε_now with (0 + ε_now)%NNR; last first.
    { apply nnreal_ext; simpl; lra. }
    iApply spec_coupl_erasables; [done|..].
    { apply ARcoupl_exact.
      (* eauto unifies the wrong premise? *)
      apply Rcoupl_state_state; [apply H | apply H1 | apply H0 ]. }
    { by eapply state_step_erasable. }
    { by eapply state_step_erasable. }
    iIntros (σ2 σ2' (n & ? & ?)).
    iApply spec_coupl_ret.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?%lookup_total_correct.
    simplify_map_eq.
    iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Ht1 Hα") as "[$ Hα]".
    iMod (ghost_map_update ((N; nsₛ ++ [f n]) : tape) with "Ht2 Hαₛ") as "[$ Hαₛ]".
    iModIntro. iMod "Hclose'" as "_".
    replace (0 + ε_now)%NNR with ε_now; last first.
    { apply nnreal_ext; simpl; lra. }
    iFrame.
    iApply ("Hwp" with "[$]").
  Qed.

  Lemma wp_couple_tapes_rev (N M : nat) E e α αₛ ns nsₛ Φ (ε : R) :
    (M <= N)%nat →
    (S N - S M) / S N = ε →
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗
    ↯ ε ∗
    (∀ (n : fin (S N)) (m : fin (S M)),
        ⌜fin_to_nat n = fin_to_nat m⌝ -∗
        α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) -∗
        WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (NMpos NMε) "( >Hα & >Hαₛ & Hε & Hwp)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2)".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ec_supply_ec_inv with "Hε2 Hε") as %(?&?&->&<-).
    iApply spec_coupl_erasables; [done|..].
    { by apply ARcoupl_state_state_rev. }
    { by eapply state_step_erasable. }
    { by eapply state_step_erasable. }
    iIntros (σ2 σ2' (n & m & nm & ? & ?)).
    iApply spec_coupl_ret.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?%lookup_total_correct.
    simplify_map_eq.
    iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Ht1 Hα") as "[$ Hα]".
    iMod (ghost_map_update ((M; nsₛ ++ [m]) : tape) with "Ht2 Hαₛ") as "[$ Hαₛ]".
    iMod (ec_supply_decrease with "Hε2 Hε") as (????) "H".
    iModIntro. iMod "Hclose'" as "_".
    iFrame. iDestruct ("Hwp" with "[//] [$]") as "$".
    iApply ec_supply_eq; [|done].
    simplify_eq/=; lra.
  Qed.

  Lemma wp_rand_avoid_l {N} (m : fin (S N)) (z : Z) E (ε : R) :
    TCEq N (Z.to_nat z) →
    ε = 1 / (S N) →
    {{{ ↯ ε }}}
      rand #z @ E
    {{{ (n : fin (S N)), RET #n; ⌜n ≠ m⌝ }}}.
  Proof.
    iIntros (-> -> Φ) "Hε Hwp".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ec_supply_ec_inv with "Hε2 Hε") as %(ε &?& -> & ?).
    iApply prog_coupl_step_l_dret; [done|solve_red|..].
    { by apply (ARcoupl_rand_no_coll_l). }
    iIntros (?? (n & [= -> ->] & ? & [=])).
    iMod (ec_supply_decrease with "Hε2 Hε") as (????) "Hs".
    simplify_eq.
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iFrame.
    rewrite -wp_value.
    iDestruct ("Hwp" with "[//]") as "$".
    iApply ec_supply_eq; [|done].
    lra.
  Qed.

  Lemma wp_rand_avoid_r {N} (m : fin (S N)) (z : Z) K e E Φ (ε : R) :
    TCEq N (Z.to_nat z) →
    ε = 1 / (S N) →
    ⤇ fill K (rand #z) ∗
    ↯ ε ∗
    (∀ (n : fin (S N)),
       ⤇ fill K #n -∗ ⌜n ≠ m⌝-∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (-> ->) "(HK & Hε & Hwp)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct (spec_auth_prog_agree with "Hauth2 HK") as "->".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ec_supply_ec_inv with "Hε2 Hε") as %(ε &?& -> & ?).
    iApply (spec_coupl_erasable_steps 1 _ (dret σ1)); [done|..].
    { rewrite pexec_1 step_or_final_no_final //; last first.
      { apply reducible_not_final. solve_red. }
      eapply ARcoupl_steps_ctx_bind_r; [done|].
      by apply (ARcoupl_rand_no_coll_r _ m). }
    { apply dret_erasable. }
    iIntros (??? (?& [=-> ] & (?&->&[=-> ->]&?))) "!>".
    iApply spec_coupl_ret.
    iMod (spec_update_prog (fill K #_) with "Hauth2 HK") as "[$ HK]".
    iMod (ec_supply_decrease with "Hε2 Hε") as (????) "H".
    simplify_eq.
    iMod "Hclose'" as "_".
    iFrame.
    iDestruct ("Hwp" with "[$] [//]") as "$".
    iApply ec_supply_eq; [|done].
    lra.
  Qed.

  (** rand(unit, N) ~ rand(unit, M) coupling, N <= M, under inj *)
  Lemma wp_couple_rand_rand_inj (N M : nat) (f: nat → nat) z w K E (ε : R) :
    (∀ n, n < S N → f n < S M)%nat →
    (∀ n1 n2, n1 < S N → n2 < S N → f n1 = f n2 → n1 = n2)%nat →
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat w) →
    (N <= M)%nat →
    (S M - S N) / S M = ε →
    {{{ ⤇ fill K (rand #w) ∗ ↯ ε }}}
      rand #z @ E
    {{{ (n : fin (S N)), RET #n; ⤇ fill K #(f n) }}}.
  Proof.
    iIntros (Hdom Hinj).

    set g := (λ m : fin (S N), Fin.of_nat_lt (Hdom m (fin_to_nat_lt m))).
    assert (Inj eq eq g).
    { intros m1 m2 Heq.
      assert (fin_to_nat (g m1) = f (fin_to_nat m1)) as H1.
      { rewrite /g fin_to_nat_to_fin //. }
      assert (fin_to_nat (g m2) = f (fin_to_nat m2)) as H2.
      { rewrite /g fin_to_nat_to_fin //. }
      apply fin_to_nat_inj.
      apply Hinj; [apply fin_to_nat_lt..|].
      rewrite -H1 -H2 //. by f_equal. }

    iIntros (-> -> HNM Hε ?) "(Hr & Hε) Hcnt".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ec_supply_ec_inv with "Hε2 Hε") as %(? &?& -> & ?).
    iApply prog_coupl_steps; [done|solve_red|solve_red|..].
    { apply ARcoupl_steps_ctx_bind_r, (ARcoupl_rand_rand_inj _ _ g); done || lra. }
    iIntros (???? (?& [=->] & (n & [=-> ->] & [=-> ->]))).
    iMod (spec_update_prog (fill K #(g _)) with "Hauth2 Hr") as "[$ Hspec0]".
    iMod (ec_supply_decrease with "Hε2 Hε") as (????) "H".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iModIntro. iFrame.
    rewrite -wp_value.
    rewrite /g fin_to_nat_to_fin.
    iDestruct ("Hcnt" with "[$]") as "$".
    iApply ec_supply_eq; [|done].
    simplify_eq. lra.
  Qed.

  (** rand(unit, N) ~ rand(unit, M) coupling, N <= M, under equality *)
  Lemma wp_couple_rand_rand_leq (N M : nat) z w K E (ε : R) :
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat w) →
    (N <= M)%nat →
    (S M - S N) / S M = ε →
    {{{ ⤇ fill K (rand #w) ∗ ↯ ε }}}
      rand #z @ E
    {{{ (n : fin (S N))(m : fin (S M)), RET #n;
        ⌜fin_to_nat n = fin_to_nat m⌝ ∗ ⤇ fill K #m }}}.
  Proof.
    iIntros (-> -> HNM <- ?) "(Hr & Hε) Hwp".
    iApply (wp_couple_rand_rand_inj _ _ (λ x, x) with "[$]"); [lia|lia|done|done|].
    assert (∀ x : fin (S (Z.to_nat z)), x < S (Z.to_nat w))%nat as T.
    { intros. pose proof fin_to_nat_lt x. lia. }
    iModIntro. iIntros. iApply ("Hwp" $! n (nat_to_fin (T n))).
    rewrite fin_to_nat_to_fin //.
    by iFrame.
  Qed.

  (** rand(unit, N) ~ rand(unit, M) coupling, M <= N, along an injection *)
  Lemma wp_couple_rand_rand_rev_inj (N M : nat) (f : nat -> nat) z w K E (ε : R) :
    (∀ n, n < S M -> f n < S N)%nat →
    (∀ n1 n2, n1 < S M → n2 < S M → f n1 = f n2 → n1 = n2)%nat →
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat w) →
    (M <= N)%nat →
    (S N - S M) / S N = ε →
    {{{ ⤇ fill K (rand #w) ∗ ↯ ε }}}
      rand #z @ E
    {{{ (m : fin (S M)), RET #(f m); ⤇ fill K #m  }}}.
  Proof.
    iIntros (Hdom Hinj).

    set g := (λ m : fin (S M), Fin.of_nat_lt (Hdom m (fin_to_nat_lt m))).
    assert (Inj eq eq g).
    { intros m1 m2 Heq.
      assert (fin_to_nat (g m1) = f (fin_to_nat m1)) as H1.
      { rewrite /g fin_to_nat_to_fin //. }
      assert (fin_to_nat (g m2) = f (fin_to_nat m2)) as H2.
      { rewrite /g fin_to_nat_to_fin //. }
      apply fin_to_nat_inj.
      apply Hinj; [apply fin_to_nat_lt..|].
      rewrite -H1 -H2 //. by f_equal. }

    iIntros (-> -> HNM <- ?) "(Hr & Hε) Hwp".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ec_supply_ec_inv with "Hε2 Hε") as %(? & ? & -> & ?).
    iApply prog_coupl_steps; [done|solve_red|solve_red|..].
    { eapply ARcoupl_steps_ctx_bind_r; [done|].
      by eapply (ARcoupl_rand_rand_rev_inj _ _ g). }
    iIntros (???? (?& [=->] & (n & [=-> ->] & [=-> ->]))).
    iMod (spec_update_prog (fill K #_) with "Hauth2 Hr") as "[$ Hspec0]".
    iMod (ec_supply_decrease with "Hε2 Hε") as (????) "H".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iModIntro. iFrame.
    rewrite /g fin_to_nat_to_fin //.
    rewrite -wp_value.
    iDestruct ("Hwp" with "[$]") as "$".
    iApply ec_supply_eq; [|done].
    simplify_eq. lra.
  Qed.

  (** rand(unit, N) ~ rand(unit, M) coupling, N <= M, under equality *)
  Lemma wp_couple_rand_rand_rev_leq (N M : nat) z w K E (ε : R) :
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat w) →
    (M <= N)%nat →
    (S N - S M) / S N = ε →
    {{{ ⤇ fill K (rand #w) ∗ ↯ ε }}}
      rand #z @ E
    {{{ (n : fin (S N)) (m : fin (S M)), RET #n;
        ⌜fin_to_nat n = m⌝ ∗ ⤇ fill K #m }}}.
  Proof.
    iIntros (-> -> HNM <- ?) "(Hr & Hε) Hwp".
    iApply (wp_couple_rand_rand_rev_inj _ _ (λ x, x) with "[$]"); [lia|lia|done|done|..].
    assert (∀ x : fin (S(Z.to_nat w)), x < S (Z.to_nat z))%nat as T.
    { intros. pose proof fin_to_nat_lt x. lia. }
    iIntros "!>" (m) "Hs".
    iSpecialize ("Hwp" $! (nat_to_fin (T m)) m).
    rewrite fin_to_nat_to_fin //.
    iApply ("Hwp" with "[$Hs //]").
  Qed.


  (** * rand(N) ~ rand(N) coupling *)
  (*
    There should be an easier proof of this using wp_couple_rand_rand_inj,
    but that uses an injective function nat -> nat as opposed to fin (S N) -> fin (S N)
  *)
  Lemma wp_couple_rand_rand N f `{Bij (fin (S N)) (fin (S N)) f} z K E :
    TCEq N (Z.to_nat z) →
    {{{ ⤇ fill K (rand #z) }}}
      rand #z @ E
    {{{ (n : fin (S N)), RET #n; ⤇ fill K #(f n) }}}.
  Proof.
    iIntros (H0 Ψ) "Hr HΨ".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε) "[Hσ [Hs Hε]]".
    iDestruct (spec_auth_prog_agree with "Hs Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".

    replace ε with (0 + ε)%NNR; last first.
    { apply nnreal_ext; simpl; lra. }
    iApply (prog_coupl_steps _ _ _
              (λ ρ2 ρ2',
                ∃ (n : fin _), ρ2 = (Val #n, σ1) ∧ ρ2' = (fill K #(f n), σ1')))
    ; [done|solve_red|solve_red|..].
    { rewrite /= fill_dmap //.
      rewrite /= -(dret_id_right (prim_step _ _)) /=.
      apply ARcoupl_exact.
      eapply Rcoupl_dmap.
      eapply Rcoupl_mono.
      - apply (Rcoupl_rand_rand _ f).
        by rewrite H0.
      - intros [] [] (b & [=] & [=])=>/=.
        simplify_eq. eauto. }
    iIntros (e2 σ2 e2' σ2' (b & [= -> ->] & [= -> ->])) "!> !>".
    iMod (spec_update_prog with "Hs Hr") as "[$ Hr]".
    iMod "Hclose" as "_".
    replace (0 + ε)%NNR with ε; last first.
    { apply nnreal_ext; simpl; lra. }
    iFrame.
    iApply wp_value.
    by iApply "HΨ".
  Qed.

  (** coupling rand and rand but avoid certain values*)
  Lemma wp_couple_rand_rand_avoid N (l:list _) z K E :
    TCEq N (Z.to_nat z) →
    NoDup l -> 
    {{{ ↯ (length l/(N+1)) ∗
          ⤇ fill K (rand #z) }}}
      rand #z @ E
      {{{ (n : fin (S N)), RET #n; ⌜n∉l⌝ ∗ ⤇ fill K #n }}}.
  Proof.
  Admitted.
  

  (** fragmented state rand N ~ state rand M, N>=M, under injective function from M to N*)
  Lemma wp_couple_fragmented_rand_rand_inj {M N} (f: fin (S M) → fin (S N)) {_ : Inj (=) (=) f}
    ns nsₛ α αₛ e E Φ:
    (M <= N)%nat →
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗
    (∀ (n : fin (S N)),
       if bool_decide (∃ m, f m = n) then
         ∀ m, α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) ∗ ⌜f m = n⌝ -∗
              WP e @ E {{ Φ }}
       else
         α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ) -∗
         WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hineq) "(>Hα & >Hαₛ & Hwp)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2)/=".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    simplify_map_eq.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε_now) with (0 + ε_now)%NNR; last (apply nnreal_ext; simpl; lra).
    iApply spec_coupl_erasables; [done|..].
    { by apply ARcoupl_exact, Rcoupl_fragmented_rand_rand_inj. }
    { by eapply state_step_erasable. }
    { eapply erasable_dbind_predicate.
      - solve_distr_mass.
      - by eapply state_step_erasable.
      - apply dret_erasable. }
    iIntros (?? [n H']).
    case_bool_decide in H'.
    - destruct Hf as [m' <-].
      destruct H' as (m & ? & ? & Hfm).
      simplify_eq.
      iMod (ghost_map_update ((N; ns ++ [f _]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
      iMod (ghost_map_update ((M; nsₛ ++ [_]) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]".
      iModIntro.
      iApply spec_coupl_ret.
      iMod "Hclose'" as "_".
      iSpecialize ("Hwp" $! (f m')).
      rewrite bool_decide_eq_true_2; [|naive_solver].
      iSpecialize ("Hwp" $! m').
      iDestruct ("Hwp" with "[$Hα $Hαₛ]") as "Hwp"; [done|].
      assert (0 + ε_now = ε_now)%NNR as ->.
      { apply nnreal_ext; simpl; lra. }
      by iFrame.
    - destruct H' as [??]. simplify_eq.
      iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
      iModIntro.
      iApply spec_coupl_ret.
      iMod "Hclose'" as "_".
      iSpecialize ("Hwp" $! n).
      rewrite bool_decide_eq_false_2 //.
      iDestruct ("Hwp" with "[$]") as "Hwp".
      assert (0 + ε_now = ε_now)%NNR as ->.
      { apply nnreal_ext; simpl; lra. }
      by iFrame.
  Qed.

  (** fragmented state rand N ~ state rand M, N>=M, under equality*)
  Lemma wp_couple_fragmented_rand_rand_leq (M N : nat) ns nsₛ α αₛ e E Φ:
    (M <= N)%nat →
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗
    (∀ (n : fin (S N)),
       match decide (n < S M)%nat with
       | left Hproof =>
           α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [nat_to_fin Hproof]) -∗
           WP e @ E {{ Φ }}
       | _ =>
           α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ) -∗
           WP e @ E {{ Φ }}
       end)
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hineq) "(>Hα & >Hαₛ & Hwp)".

    assert (∀ x : fin (S M), fin_to_nat x < S N)%nat as H.
    { intros. pose proof (fin_to_nat_lt x). lia. }
    set f := (λ x, nat_to_fin (H x)).
    assert (Inj (eq) (eq) f) as Hinj.
    { rewrite /f. intros ?? H0.
      apply (f_equal fin_to_nat) in H0. rewrite !fin_to_nat_to_fin in H0.
      by apply fin_to_nat_inj. }

    iApply (wp_couple_fragmented_rand_rand_inj f with "[$Hα $Hαₛ Hwp]"); [done|].
    iIntros (n).
    case_bool_decide as H1.
    - destruct H1 as [n' <-].
      iIntros (?) "(?&?&%Hid)".
      apply Hinj in Hid as ->.
      iSpecialize ("Hwp" $! (f n')).
      case_match eqn:H'; last first.
      { exfalso.
        cut (f n' < S M)%nat; first lia.
        rewrite /f. rewrite fin_to_nat_to_fin.
        apply fin_to_nat_lt. }
      replace (nat_to_fin l) with (n').
      { iApply "Hwp". iFrame. }
      apply fin_to_nat_inj. rewrite fin_to_nat_to_fin. by rewrite /f fin_to_nat_to_fin.
    - iSpecialize ("Hwp" $! n).
      case_match; [|iFrame].
      exfalso. apply H1. exists (nat_to_fin l). rewrite /f.
      apply fin_to_nat_inj. by rewrite !fin_to_nat_to_fin.
  Qed.

  (** * fragmented state rand N ~ state rand M, M>=N, under injective function from N to M*)
  Lemma wp_couple_fragmented_rand_rand_inj_rev {M N} (f: fin (S N) → fin (S M)) {_: Inj (=) (=) f}
    ns nsₛ α αₛ e E Φ:
    (N <= M)%nat →
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗
    (∀ (m : fin (S M)),
        if bool_decide (∃ n, f n = m) then
          ∀ n, α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) ∗ ⌜f n = m⌝ -∗
               WP e @ E {{ Φ }}
        else
          α ↪ (N; ns) ∗ αₛ ↪ₛ (M; nsₛ++[m]) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hineq) "(>Hα & >Hαₛ & Hwp)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2)/=".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε_now) with (0+ε_now)%NNR; last (apply nnreal_ext; simpl; lra).
    iApply spec_coupl_erasables; [done|..].
    { by apply ARcoupl_exact, Rcoupl_swap, Rcoupl_fragmented_rand_rand_inj. }
    { eapply erasable_dbind_predicate.
      - solve_distr_mass.
      - by eapply state_step_erasable.
      - apply dret_erasable. }
    { by eapply state_step_erasable. }
    iIntros (?? [n H']).
    case_bool_decide in H'.
    - destruct Hf as [m' <-].
      destruct H' as (m & ? & ? & Hfm).
      simplify_eq.
      iMod (ghost_map_update ((N; ns ++ [_]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
      iMod (ghost_map_update ((M; nsₛ ++ [_]) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]".
      iModIntro. iApply spec_coupl_ret. iMod "Hclose'" as "_".
      iSpecialize ("Hwp" $! (f m')).
      rewrite bool_decide_eq_true_2; [|naive_solver].
      iSpecialize ("Hwp" $! m').
      iDestruct ("Hwp" with "[$Hα $Hαₛ]") as "Hwp"; [done|].
      assert (0 + ε_now = ε_now)%NNR as ->.
      { apply nnreal_ext; simpl; lra. }
      by iFrame.
    - destruct H' as [??]. simplify_eq.
      iMod (ghost_map_update ((M; nsₛ ++ [_]) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]".
      iModIntro. iApply spec_coupl_ret. iMod "Hclose'" as "_".
      iSpecialize ("Hwp" $! n).
      rewrite bool_decide_eq_false_2 //.
      iDestruct ("Hwp" with "[$]") as "Hwp".
      assert (0 + ε_now = ε_now)%NNR as ->.
      { apply nnreal_ext; simpl; lra. }
      by iFrame.
  Qed.

  (** fragmented state rand N ~ state rand M, M>=N, under injective function from N to M,
      but with errors for rejection sampling! *)
  Lemma wp_couple_fragmented_rand_rand_inj_rev' {M N} (f : fin(S N) → fin (S M)) {_: Inj (=) (=) f}
    ns nsₛ α αₛ e E Φ (ε : R) :
    0 <= ε →
    (N < M)%nat →
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗ ↯ ε ∗
    (∀ (m : fin (S M)),
       if bool_decide (∃ n, f n = m) then
         ∀ n, α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) ∗ ⌜f n = m⌝ -∗
              WP e @ E {{ Φ }}
     else
       ∀ (ε' : R),
         ⌜ε' = (S M / (S M - S N) * ε)%R⌝ ∗
         α ↪ (N; ns) ∗ αₛ ↪ₛ (M; nsₛ++[m]) ∗ ↯ ε' -∗
         WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hε Hineq) "(>Hα & >Hαₛ & Hε & Hwp)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2)".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ec_supply_bound with "[$][$]") as %Hle.
    
    set ε' := mknonnegreal _ Hε.
    
    set ε_now1 := nnreal_minus ε_now ε' Hle.
    set ε_now2 := (ε_now + ε' * nnreal_nat (S N) / nnreal_nat (S M - S N))%NNR.
    set (E2 σ := if bool_decide (∃ x, σ = state_upd_tapes <[αₛ:=(M; nsₛ ++ [f x])]> σ1')
                 then ε_now1 else ε_now2).
    assert (∀ σ, E2 σ <= Rmax ε_now1 ε_now2)%R.
    { intros ?. rewrite /E2. apply Rmax_Rle. case_bool_decide; by [left| right]. }

    iApply (spec_coupl_erasables_exp E2 (Rmax ε_now1 ε_now2) 0%NNR).
    { eapply ARcoupl_exact, Rcoupl_swap, Rcoupl_fragmented_rand_rand_inj; done || lia. }
    { apply erasable_dbind_predicate.
      - solve_distr_mass.
      - by eapply state_step_erasable.
      - apply dret_erasable. }
    { by eapply state_step_erasable. }
    { done. }
    { simpl. erewrite state_step_unfold; [|done].
      (* TODO: cleanup *)
      rewrite /Expval.
      erewrite (SeriesC_ext _
                  (λ b : state,
                      if bool_decide (b ∈ (λ x, state_upd_tapes <[αₛ:=(M; nsₛ ++ [x])]> σ1')
                                        <$> (fin_enum (S M)))
                     then /(S M) * E2 b else 0)%R); last first.
      { intros n.
        case_bool_decide as Hin; last first.
        { apply Rmult_eq_0_compat_r. rewrite /dmap/dbind/dbind_pmf/pmf/=.
          apply SeriesC_0. intros. apply Rmult_eq_0_compat_l.
          rewrite /dret_pmf. case_bool_decide; last lra.
          subst. exfalso. apply Hin. erewrite elem_of_list_fmap.
          exists x; split; first done. replace (fin_enum (S M)) with (enum (fin (S M))) by done.
          apply elem_of_enum. }
        rewrite elem_of_list_fmap in Hin. destruct Hin as [y [-> ?]].
        apply Rmult_eq_compat_r. rewrite /dmap/dbind/dbind_pmf/pmf/=.
        rewrite SeriesC_scal_l.
        replace (SeriesC _) with 1%R; first lra.
        symmetry.
        rewrite /dret_pmf.
        erewrite (SeriesC_ext _ (λ x, if bool_decide (x = y) then 1 else 0))%R;
          first apply SeriesC_singleton.
        intros.
        case_bool_decide as H2i.
        - apply state_upd_tapes_same in H2i. simplify_eq.
          case_bool_decide; done.
        - case_bool_decide; last done.
          subst. done. }
      { trans (SeriesC (λ x, if bool_decide (∃ y, f y = x) then / S M * ε_now1 else / S M * ε_now2))%R.
        - rewrite Rplus_0_l.
          set (h σ := match decide (∃ x, σ = state_upd_tapes <[αₛ:=(M; nsₛ ++ [x])]> σ1') with
                    | left Hproof => Some (epsilon Hproof)
                    | _ => None
                    end).
          etrans; last eapply (SeriesC_le_inj _ h).
          + apply Req_le_sym. apply SeriesC_ext. (** should be ok *)
            intros s. rewrite /h. case_match eqn:Heqn; last first.
            { rewrite bool_decide_eq_false_2; first (simpl;lra).
              erewrite elem_of_list_fmap.
              intros [? [->?]]. apply n.
              naive_solver. }
            pose proof epsilon_correct _ e0 as H'.
            rewrite bool_decide_eq_true_2; last first.
            { destruct e0 as [x ?]. subst. rewrite elem_of_list_fmap.
              eexists _. split; first done.
              replace (fin_enum _) with (enum (fin (S M))) by done.
              apply elem_of_enum. }
            rewrite !S_INR.
            rewrite /E2.
            simpl in *. subst.
            case_bool_decide as H1'.
            * rewrite bool_decide_eq_true_2.
              { rewrite /ε_now1. simpl; lra. }
              destruct H1' as [y ?]. exists y. rewrite H3. done.
            * rewrite bool_decide_eq_false_2.
              { rewrite /ε_now2; simpl; lra. }
              intros [x H2'].
              apply H1'. rewrite H' in H2'. apply state_upd_tapes_same in H2'. simplify_eq.
              naive_solver.
          + intros. case_bool_decide; apply Rmult_le_pos; try done.
            all: rewrite <-Rdiv_1_l; apply Rcomplements.Rdiv_le_0_compat; try lra.
            all: apply pos_INR_S.
          + intros n1 n2 m. rewrite /h. do 2 case_match; try done.
            intros.
            pose proof epsilon_correct _ e0.
            pose proof epsilon_correct _ e1. simpl in *. simplify_eq.
            rewrite H7 H8. by repeat f_equal.
          + apply ex_seriesC_finite.
        - eset (diff:=elements (((list_to_set (enum (fin(S M)))):gset _ )∖ ((list_to_set(f<$>enum (fin(S N)))):gset _))).
          erewrite (SeriesC_ext _
                      (λ x : fin (S M), (if bool_decide (x ∈ f<$> enum (fin(S N))) then / S M * ε_now1 else 0%R) +
                                         if bool_decide (x ∈ diff ) then / S M * ε_now2 else 0%R
                   ))%R; last first.
          { (** annoying lemma again *)
            intros n. rewrite /diff.
            case_bool_decide as H1'.
            - destruct H1' as [? H1']. rewrite bool_decide_eq_true_2; last first.
              + subst. apply elem_of_list_fmap_1. apply elem_of_enum.
              + subst. rewrite bool_decide_eq_false_2; first lra.
                rewrite elem_of_elements.
                rewrite not_elem_of_difference; right.
                rewrite elem_of_list_to_set. apply elem_of_list_fmap_1; apply elem_of_enum.
            - rewrite bool_decide_eq_false_2; last first.
              { rewrite elem_of_list_fmap. intros [?[??]].
                subst. apply H1'. naive_solver. }
              rewrite bool_decide_eq_true_2; first lra.
              rewrite elem_of_elements. rewrite elem_of_difference.
              split; rewrite elem_of_list_to_set; first apply elem_of_enum.
              rewrite elem_of_list_fmap. intros [?[??]].
              subst. apply H1'. naive_solver.
          }
        rewrite SeriesC_plus; try apply ex_seriesC_finite.
        rewrite !SeriesC_list_2; last first.
        { apply NoDup_fmap_2; [done|apply NoDup_enum]. }
        { rewrite /diff. eapply NoDup_elements. }
        rewrite fmap_length. rewrite fin.length_enum_fin.
        rewrite /diff.
        replace (length _) with (S M - S N)%nat; last first.
        { erewrite <-size_list_to_set; last apply NoDup_elements.
          erewrite list_to_set_elements.
          rewrite size_difference.
          - rewrite !size_list_to_set; [|apply NoDup_fmap; [auto|apply NoDup_enum]|apply NoDup_enum]; auto.
            rewrite fmap_length.
            rewrite !fin.length_enum_fin. done.
          - intros ??. apply elem_of_list_to_set. apply elem_of_enum.
        }
        rewrite /ε_now1 /ε_now2. simpl. rewrite -/(INR (S N)) -/(INR (S M)). rewrite !S_INR.
        rewrite !Rmult_assoc.
        rewrite minus_INR; last lia.
        cut ((N+1)/ (M + 1) * ε_now - (N+1)/(M+1) *ε+
               (M-N)/ (M + 1) * ε_now + ((N + 1)/(M+1) * ((M-N)/ (M - N))) * ε <= ε_now)%R; first lra.
        rewrite Rdiv_diag; last first.
        { assert (N < M)%R; real_solver. }
        cut ((N + 1) / (M + 1) * ε_now+ (M - N) / (M + 1) * ε_now <= ε_now)%R; first lra.
        cut ((M + 1) / (M + 1) * ε_now <= ε_now)%R; first lra.
        rewrite Rdiv_diag; first lra.
        pose proof pos_INR M. lra. }
      Unshelve. all : eapply gset_fin_set. }

    iIntros (?? [m H']).
    case_bool_decide in H' as H1'.
    - destruct H' as (n&?&?&?).
      destruct H1' as [n' <-].
      assert (n' = n) as -> by (by apply (inj _)).
      simplify_eq.
      iApply spec_coupl_ret.
      iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Ht1 Hα") as "[$ Hα]".
      iMod (ghost_map_update ((M; nsₛ ++ [f n]) : tape) with "Ht2 Hαₛ") as "[$ Hαₛ]".
      iModIntro. iMod "Hclose'" as "_".
      iSpecialize ("Hwp" $! (f n)).
      rewrite bool_decide_eq_true_2; last naive_solver.
      iSpecialize ("Hwp" $! (n)). iFrame.
      iDestruct ("Hwp" with "[$Hα $Hαₛ]") as "Hwp"; [done|].
      replace (ε_now) with (ε' + ε_now1)%NNR; last first.
      { apply nnreal_ext. simpl. lra. }
      iMod (ec_supply_decrease with "[$] [$]") as (????) "H".
      iFrame.
      rewrite /E2 bool_decide_eq_true_2; [|eauto].
      iApply ec_supply_eq; [|done].
      simplify_eq /=. lra. 
    - destruct H' as [??]. simplify_eq.
      replace (E2 _) with (ε_now2); last first.
      { rewrite /E2. rewrite bool_decide_eq_false_2 //.
        intros [? H2']. apply state_upd_tapes_same in H2'. simplify_eq. naive_solver. }
      destruct (Rle_or_lt 1 ε_now2).
      { iModIntro. by iApply spec_coupl_ret_err_ge_1. }
      iModIntro.
      iApply spec_coupl_ret.
      iMod (ghost_map_update ((M; nsₛ ++ [m]) : tape) with "Ht2 Hαₛ") as "[? Hαₛ]".
      iMod "Hclose'" as "_".
      iSpecialize ("Hwp" $! m).
      rewrite bool_decide_eq_false_2 //.
      rewrite !S_INR /=.
      iFrame.
      iMod (ec_supply_increase with "[$Hε2]") as "[$ Hε']".
      { by eapply Rle_lt_trans. }
      iCombine "Hε Hε'" as "Hε".
      iApply ("Hwp" with "[$Hα $Hαₛ $Hε]").
      iPureIntro. simpl. rewrite -/(INR (S N)). rewrite S_INR.
      replace (INR M + 1 - (INR N + 1))%R with (INR M - INR N)%R by lra.
      rewrite -{1}(Rmult_1_l ε).
      rewrite Rmult_assoc (Rmult_comm ε).
      rewrite -Rmult_plus_distr_r. apply Rmult_eq_compat_r.
      rewrite Rdiv_def.
      replace (1)%R with ((INR M - INR N)*/(INR M - INR N))%R at 1; last first.      
      { apply Rinv_r. apply lt_INR in Hineq. lra. }
      rewrite minus_INR; [|real_solver].
      rewrite -Rmult_plus_distr_r. lra.
  Qed.

  Lemma wp_couple_fragmented_rand_rand_leq_rev' {M N : nat} ns nsₛ α αₛ e E Φ (ε : R) :
    0 <= ε →
    (N < M)%nat →
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗ ↯ ε ∗
    (∀ (m : fin (S M)),
       match decide (fin_to_nat m < S N)%nat with
       | left Hproof =>
           α ↪ (N; ns ++ [nat_to_fin Hproof]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) -∗
           WP e @ E {{ Φ }}
       | _ =>
           ∀ (ε' : R),
             ⌜ε' = (S M / (S M - S N) * ε)%R⌝ ∗
             α ↪ (N; ns) ∗ αₛ ↪ₛ (M; nsₛ++[m]) ∗ ↯ ε' -∗
             WP e @ E {{ Φ }}
       end)
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hε Hineq) "(>Hα & >Hαₛ & Hε & Hwp)".
    assert (∀ x : fin(S N), fin_to_nat x < S M)%nat as H.
    { intros. pose proof fin_to_nat_lt x. lia. }
    pose (f := λ x, nat_to_fin (H x)).
    assert (Inj (eq) (eq) f) as Hinj.
    { rewrite /f. intros ?? H0. apply (f_equal fin_to_nat) in H0. rewrite !fin_to_nat_to_fin in H0.
      by apply fin_to_nat_inj. }
    iApply (wp_couple_fragmented_rand_rand_inj_rev' f with "[$Hα $Hαₛ $Hε Hwp]"); [done|done|].
    iIntros (n).
    case_bool_decide as H1.
    - destruct H1 as [n' <-].
      iIntros (?) "(?&?&%Hid)".
      apply Hinj in Hid as ->.
      iSpecialize ("Hwp" $! (f n')).
      case_match eqn:H'; last first.
      { exfalso.
        cut (f n' < S N)%nat; [lia|].
        rewrite /f. rewrite fin_to_nat_to_fin.
        apply fin_to_nat_lt. }
      replace (nat_to_fin l) with (n').
      { iApply "Hwp". iFrame. }
      apply fin_to_nat_inj. rewrite fin_to_nat_to_fin. by rewrite /f fin_to_nat_to_fin.
    - iSpecialize ("Hwp" $! n).
      case_match; [|iFrame].
      exfalso. apply H1. exists (nat_to_fin l). rewrite /f.
      apply fin_to_nat_inj. by rewrite !fin_to_nat_to_fin.
  Qed.

  (** wp_couple_exp *)
  Lemma wp_couple_exp (M N p:nat) 
    (f : list (fin (S N)) → fin (S M))
    (Hinj : ∀ (l1 l2 : list _), length l1 = p → length l2 = p → f l1 = f l2 -> l1 = l2) ns nsₛ α αₛ e E Φ:
    (S N ^ p = S M)%nat->
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗
    (∀ (l : list (fin (S N))) (m:fin (S M)),
       ⌜length l = p /\ f l = m⌝ -∗ 
       α ↪ (N; ns ++ l) -∗ αₛ ↪ₛ (M; nsₛ ++ [m]) -∗
       WP e @ E {{ Φ }}
    )
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Heq) "(>Hα & >Hαₛ & Hwp)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2)/=".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    simplify_map_eq.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε_now) with (0+ε_now)%NNR; last (apply nnreal_ext; simpl; lra).
    iApply spec_coupl_erasables; [done|..].
    - apply ARcoupl_exact. apply Rcoupl_state_state_exp.
      all: exact.
    - eapply iterM_state_step_erasable; done.
    - by eapply state_step_erasable.
    - iIntros (σ2 σ2') "%K".
      destruct K as (xs' & z & Hlen & -> & -> & <-).
      iMod (ghost_map_update ((N; ns ++ xs') : tape) with "Ht1 Hα") as "[Ht1 Hα]".
      iMod (ghost_map_update ((M; nsₛ ++ [f xs']) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]".
      iModIntro.
      iApply spec_coupl_ret.
      iMod "Hclose'".
      iSpecialize ("Hwp" $! xs' (f xs') with "[][$][$]"); first done.
      iFrame.
      replace (0+_)%NNR with (ε_now); first done.
      apply nnreal_ext. simpl; lra.
  Qed.

  Lemma wp_couple_exp_rev (M N p:nat) 
    (f:(list (fin (S N))) -> fin (S M))
    (Hinj: forall (l1 l2:list _), length l1 = p -> length l2 = p -> f l1 = f l2 -> l1 = l2) ns nsₛ α αₛ e E Φ:
    (S N ^ p = S M)%nat->
    ▷ α ↪ (M; ns) ∗ ▷ αₛ ↪ₛ (N; nsₛ) ∗
    (∀ (l : list (fin (S N))) (m:fin (S M)),
       ⌜length l = p /\ f l = m⌝ -∗ 
       α ↪ (M; ns ++ [m]) -∗ αₛ ↪ₛ (N; nsₛ ++ l) -∗
       WP e @ E {{ Φ }}
    )
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Heq) "(>Hα & >Hαₛ & Hwp)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2)/=".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    simplify_map_eq.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε_now) with (0+ε_now)%NNR; last (apply nnreal_ext; simpl; lra).
    iApply spec_coupl_erasables; [done|..].
    - apply ARcoupl_exact. apply Rcoupl_swap. apply Rcoupl_state_state_exp.
      all: exact.
    - by eapply state_step_erasable.
    - eapply iterM_state_step_erasable; done.
    - iIntros (σ2 σ2') "%K".
      destruct K as (xs' & z & Hlen & -> & -> & <-).
      iMod (ghost_map_update ((M; ns ++ [f xs']) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
      iMod (ghost_map_update ((N; nsₛ ++ xs') : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]".
      iModIntro.
      iApply spec_coupl_ret.
      iSpecialize ("Hwp" $! xs' (f xs') with "[][$][$]"); first done.
      iMod "Hclose'".
      iFrame.
      replace (0+_)%NNR with (ε_now); try iFrame; try done.
      apply nnreal_ext. simpl; lra.
  Qed.

  (** * Exact couplings  *)
  Lemma wp_couple_tape_rand N f `{Bij (fin (S N)) (fin (S N)) f} K E α z ns Φ e :
    TCEq N (Z.to_nat z) →
    ▷ α ↪ (N; ns) ∗ ⤇ fill K (rand #z) ∗
    (∀ n : fin (S N), α ↪ (N; ns ++ [n]) ∗ ⤇ fill K #(f n) -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (->) "(>Hα & Hj & Hwp)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε) "[[Hh1 Ht1] [Hauth2 Herr]]".
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iDestruct (spec_auth_prog_agree with "Hauth2 Hj") as %-> .
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε) with (0 + ε)%NNR by (apply nnreal_ext; simpl; lra).
    iApply (spec_coupl_erasable_steps 1 _ (state_step σ1 α)); [done|..].
    { rewrite pexec_1 step_or_final_no_final; last first.
      { apply reducible_not_final. solve_red. }
      apply ARcoupl_steps_ctx_bind_r => /=; [done|].
      by apply ARcoupl_exact, Rcoupl_pos_R, Rcoupl_state_rand. }
    { by eapply state_step_erasable. }
    iIntros(σ2 e2' σ2' (? & [= ->] & (? & -> & [= -> ->]) & ? & ?)).
    iApply spec_coupl_ret.
    iMod (spec_update_prog (fill K #(f _)) with "Hauth2 Hj") as "[$ Hspec0]".
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iMod (ghost_map_update ((_; ns ++ [_]) : tape) with "Ht1 Hα") as "[$ Hα]".
    iModIntro. iMod "Hclose'" as "_".
    iSpecialize ("Hwp" with "[$]").
    iFrame.
    replace (_+_)%NNR with (ε) by (apply nnreal_ext; simpl; lra).
    done.
  Qed.

  (** * rand(unit, N) ~ state_step(α', N) coupling *)
  Lemma wp_couple_rand_tape N f `{Bij (fin (S N)) (fin (S N)) f} z E α ns :
    TCEq N (Z.to_nat z) →
    {{{ ▷ α ↪ₛ (N; ns) }}}
      rand #z @ E
    {{{ (n : fin (S N)), RET #n; α ↪ₛ (N; ns ++ [f n]) }}}.
  Proof.
    iIntros (-> ?) ">Hαs Hwp".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε) "[[Hh1 Ht1] [Hauth2 Herr]]".
    iDestruct (spec_auth_lookup_tape with "Hauth2 Hαs") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    replace (ε) with (0+ε)%NNR at 2 by (apply nnreal_ext; simpl; lra).
    iApply prog_coupl_step_l_erasable; [done|solve_red|..].
    { apply ARcoupl_exact. by eapply (Rcoupl_rand_state _ f). }
    { by eapply state_step_erasable. }
    iIntros (??? (n & [= -> ->] & ->)).
    iMod (spec_auth_update_tape (_; ns ++ [f _]) with "Hauth2 Hαs") as "[Htapes Hαs]".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iFrame.
    iApply wp_value.
    iApply ("Hwp" $! _ with "[$Hαs]").
  Qed.

  Lemma wp_couple_rand_rand_lbl N f `{Bij (fin (S N)) (fin (S N)) f} z K E α :
    TCEq N (Z.to_nat z) →
    {{{ α ↪ₛ (N; []) ∗ ⤇ fill K (rand(#lbl:α) #z) }}}
      rand #z @ E
      {{{ (n : fin (S N)), RET #n; α ↪ₛ (N; []) ∗ ⤇ fill K #(f n) }}}.
  Proof.
    iIntros (-> ?) "(Hα & Hspec) Hwp".
    iApply wp_spec_update.
    iApply (wp_couple_rand_tape with "[$Hα]").
    iIntros "!>" (n) "Hα".
    iMod (step_rand with "[$]") as "[? ?]".
    iModIntro.
    iApply ("Hwp" with "[$]").
  Qed.

  Lemma wp_couple_rand_lbl_rand_lbl N f `{Bij (fin (S N)) (fin (S N)) f} z K E α α' :
    TCEq N (Z.to_nat z) →
    {{{ ▷ α ↪ (N; []) ∗ ▷ α' ↪ₛ (N; []) ∗ ⤇ fill K (rand(#lbl:α') #z) }}}
      rand(#lbl:α) #z @ E
    {{{ (n : fin (S N)), RET #n; α ↪ (N; []) ∗ α' ↪ₛ (N; []) ∗ ⤇ fill K #(f n) }}}.
  Proof.
    iIntros (??) "(>Hα & >Hαs & Hr) HΨ".
    iMod ec_zero.
    iApply (wp_couple_tapes_bij).
    iFrame.
    iIntros (n) "(Hα & Hαs) /=".
    iMod (step_rand with "[$Hr $Hαs]") as "[? ?]".
    iApply (wp_rand_tape with "Hα").
    iIntros "!> Hα".
    iApply ("HΨ" with "[$]").
  Qed.


  (** * rand(α, N) ~ rand(α, N) wrong bound coupling *)
  Lemma wp_couple_rand_lbl_rand_lbl_wrong N M f `{Bij (fin (S N)) (fin (S N)) f} z K E α α' xs ys :
    TCEq N (Z.to_nat z) →
    N ≠ M →
    {{{ ▷ α ↪ (M; xs) ∗ ▷ α' ↪ₛ (M; ys) ∗ ⤇ fill K (rand(#lbl:α') #z) }}}
      rand(#lbl:α) #z @ E
    {{{ (n : fin (S N)), RET #n; α ↪ (M; xs) ∗ α' ↪ₛ (M; ys) ∗ ⤇ fill K #(f n) }}}.
  Proof.
    iIntros (-> ? Ψ) "(>Hα & >Hαs & Hr) Hwp".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε) "[[Hh Ht] [Hs Herr]]".
    iDestruct (ghost_map_lookup with "Ht Hα") as %?.
    iDestruct (spec_auth_lookup_tape with "Hs Hαs") as %?.
    iDestruct (spec_auth_prog_agree with "Hs Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    replace ε with (0 + ε)%NNR; last first.
    { apply nnreal_ext; simpl; lra. }
    iApply (prog_coupl_steps _ _ _
              (λ ρ2 ρ2',
                ∃ (n : fin _), ρ2 = (Val #n, σ1) ∧ ρ2' = (fill K #(f n), σ1')))
    ; [done|solve_red|solve_red|..].
    { rewrite /= fill_dmap //.
      rewrite -(dret_id_right (prim_step _ _)) /=.
      apply ARcoupl_exact.
      apply Rcoupl_dmap.
      eapply Rcoupl_mono; [by eapply (Rcoupl_rand_lbl_rand_lbl_wrong _ _ f)|].
      intros [] [] (b & [=] & [=])=>/=.
      simplify_eq. eauto. }
    iIntros (e2 σ2 e2' σ2' (b & [= -> ->] & [= -> ->])) "!>".
    iModIntro.
    iMod (spec_update_prog with "Hs Hr") as "[$ Hr]".
    replace (0 + ε)%NNR with ε; last first.
    { apply nnreal_ext; simpl; lra. }
    iFrame.
    iMod "Hclose" as "_".
    iApply wp_value.
    by iApply ("Hwp" with "[$]").
  Qed.


End rules.
