(** * Coupling rules  *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext fin tactics.
From clutch.common Require Import con_language con_ectx_language con_ectxi_language.
From clutch.foxtrot Require Import lifting ectx_lifting.
From clutch.con_prob_lang Require Import lang notation tactics metatheory erasure.
From clutch.foxtrot Require Export primitive_laws oscheduler full_info proofmode.

Section rules.
  Context `{!foxtrotGS Σ}.
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
      (λ a '(e2', σ2', efs), ∃ e2'', (e2') = (fill K e2'') ∧ R a (e2'', σ2', efs)) ε.
  Proof.
    intros Hcpl Hv.
    rewrite fill_dmap //= -(dret_id_right μ ) /=.
    eapply (ARcoupl_dbind' ε 0%NNR); [apply cond_nonneg|done|simpl; lra| |done].
    intros ? [[]] ?.
    apply ARcoupl_dret=>/=; [done|]. eauto.
  Qed.

  (* (** TODO: This should be generalizable to injective functions [N] -> [M] *)
  (*     Then we can get the exact couplings with bijections as a corollary *) *)
  (* Lemma wp_couple_tapes (N M : nat) E e α αₛ ns nsₛ Φ (ε : R) : *)
  (*   (N <= M)%nat → *)
  (*   (S M - S N) / S M = ε → *)
  (*   ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗ *)
  (*   ↯ ε ∗ *)
  (*   (∀ (n : nat), *)
  (*       ⌜ n ≤ N ⌝ -∗ *)
  (*       α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ ++ [n]) -∗ *)
  (*       WP e @ E {{ Φ }}) *)
  (*   ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (NMpos NMε) "(>Hα & >Hαₛ & Hε & Hwp)". *)
  (*   iApply wp_lift_step_spec_couple. *)
  (*   iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)". *)
  (*   iDestruct "Hauth2" as "(HK&Hh2&Ht2)/=". *)
  (*   iDestruct "Hα" as (fs) "(%&Hα)". *)
  (*   iDestruct "Hαₛ" as (fsₛ) "(%&Hαₛ)". *)
  (*   iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?. *)
  (*   iDestruct (ghost_map_lookup with "Ht1 Hα") as %?. *)
  (*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'". *)
  (*   iDestruct (ec_supply_ec_inv with "Hε2 Hε") as %(?&?&->&<-). *)
  (*   iApply spec_coupl_erasables; [done|..]. *)
  (*   { by apply ARcoupl_state_state. } *)
  (*   { by eapply state_step_erasable. } *)
  (*   { by eapply state_step_erasable. } *)
  (*   iIntros (σ2 σ2' (n & m & nm & -> & ->)). *)
  (*   iApply spec_coupl_ret. *)
  (*   iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct. *)
  (*   iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?%lookup_total_correct. *)
  (*   iMod (ghost_map_update ((N; fs ++ [n]) : tape) with "Ht1 Hα") as "[$ Hα]". *)
  (*   iMod (ghost_map_update ((M; fsₛ ++ [m]) : tape) with "Ht2 Hαₛ") as "[$ Hαₛ]". *)
  (*   iMod (ec_supply_decrease with "Hε2 Hε") as (????) "H". *)
  (*   iModIntro. iMod "Hclose'" as "_". iFrame. *)
  (*   pose proof (fin_to_nat_lt n). *)
  (*   iDestruct ("Hwp" $! n with "[]") as "Hwp". *)
  (*   { iPureIntro; lia. } *)
  (*   iSplitL "H". *)
  (*   { iApply ec_supply_eq; [|done]. *)
  (*     simplify_eq/=; lra. } *)
  (*   iModIntro. *)
  (*   iApply "Hwp". *)
  (*   iSplitL "Hα". *)
  (*   - iExists _. iFrame. *)
  (*     rewrite fmap_app. *)
  (*     simplify_eq. done. *)
  (*   - iExists _. iFrame. *)
  (*     rewrite nm. *)
  (*     rewrite fmap_app. *)
  (*     simplify_eq. done. *)
  (* Qed. *)

  (* Lemma wp_couple_tapes_bij N f `{Bij nat nat f} E e α αₛ ns nsₛ Φ : *)
  (*   (forall n, n < S N -> f n < S N)%nat -> *)
  (*   ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (N; nsₛ) ∗ *)
  (*     (∀ n : nat, α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (N; nsₛ ++ [f n]) ∗ ⌜ n ≤ N ⌝  -∗ *)
  (*                   WP e @ E {{ Φ }}) *)
  (*     ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (Hdom) "(>Hα & >Hαₛ & Hwp)". *)
  (*   iApply wp_lift_step_spec_couple. *)
  (*   iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)". *)
  (*   iDestruct "Hauth2" as "(HK&Hh2&Ht2)/=". *)
  (*   iDestruct "Hα" as (fs) "(<-&Hα)". *)
  (*   iDestruct "Hαₛ" as (fsₛ) "(<-&Hαₛ)". *)
  (*   destruct (restr_bij_fin (S N) f) as [g [HBij Hfg]]. *)
  (*   { intros n Hn. *)
  (*     by apply Hdom. *)
  (*   } *)
  (*   iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?. *)
  (*   iDestruct (ghost_map_lookup with "Ht1 Hα") as %?. *)
  (*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'". *)
  (*   replace ε_now with (0 + ε_now)%NNR; last first. *)
  (*   { apply nnreal_ext; simpl; lra. } *)
  (*   iApply spec_coupl_erasables; [done|..]. *)
  (*   { apply ARcoupl_exact. *)
  (*     (* eauto unifies the wrong premise? *) *)
  (*     apply Rcoupl_state_state; [apply HBij | apply H1 | apply H0 ]. } *)
  (*   { by eapply state_step_erasable. } *)
  (*   { by eapply state_step_erasable. } *)
  (*   iIntros (σ2 σ2' (n & ? & ?)). *)
  (*   iApply spec_coupl_ret. *)
  (*   iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct. *)
  (*   iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?%lookup_total_correct. *)
  (*   simplify_map_eq. *)
  (*   iMod (ghost_map_update ((N; fs ++ [n]) : tape) with "Ht1 Hα") as "[$ Hα]". *)
  (*   iMod (ghost_map_update ((N; fsₛ ++ [g n]) : tape) with "Ht2 Hαₛ") as "[$ Hαₛ]". *)
  (*   iModIntro. iMod "Hclose'" as "_". *)
  (*   replace (0 + ε_now)%NNR with ε_now; last first. *)
  (*   { apply nnreal_ext; simpl; lra. } *)
  (*   iFrame. *)
  (*   iApply ("Hwp" $! (fin_to_nat n) with "[-]"). *)
  (*   iSplitL "Hα". *)
  (*   { iExists _. iFrame. *)
  (*     iPureIntro. *)
  (*     rewrite fmap_app //. } *)
  (*   iSplitL "Hαₛ". *)
  (*   { iExists _. iFrame. *)
  (*     iPureIntro. *)
  (*     rewrite fmap_app -Hfg //. } *)
  (*   iPureIntro. *)
  (*   apply (fin.fin_to_nat_le n). *)
  (* Qed. *)

  (* Lemma wp_couple_tapes_rev (N M : nat) E e α αₛ ns nsₛ Φ (ε : R) : *)
  (*   (M <= N)%nat → *)
  (*   (S N - S M) / S N = ε → *)
  (*   ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗ *)
  (*   ↯ ε ∗ *)
  (*   (∀ (n m : nat), *)
  (*       ⌜n = m⌝ -∗ *)
  (*       α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ ++ [m]) -∗ *)
  (*       ⌜m ≤ M⌝ -∗ *)
  (*       WP e @ E {{ Φ }}) *)
  (*   ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (NMpos NMε) "( >Hα & >Hαₛ & Hε & Hwp)". *)
  (*   iApply wp_lift_step_spec_couple. *)
  (*   iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)". *)
  (*   iDestruct "Hauth2" as "(HK&Hh2&Ht2)". *)
  (*   iDestruct "Hα" as (fs) "(<-&Hα)". *)
  (*   iDestruct "Hαₛ" as (fsₛ) "(<-&Hαₛ)". *)
  (*   iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?. *)
  (*   iDestruct (ghost_map_lookup with "Ht1 Hα") as %?. *)
  (*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'". *)
  (*   iDestruct (ec_supply_ec_inv with "Hε2 Hε") as %(?&?&->&<-). *)
  (*   iApply spec_coupl_erasables; [done|..]. *)
  (*   { by apply ARcoupl_state_state_rev. } *)
  (*   { by eapply state_step_erasable. } *)
  (*   { by eapply state_step_erasable. } *)
  (*   iIntros (σ2 σ2' (n & m & nm & ? & ?)). *)
  (*   iApply spec_coupl_ret. *)
  (*   iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct. *)
  (*   iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?%lookup_total_correct. *)
  (*   simplify_map_eq. *)
  (*   iMod (ghost_map_update ((N; fs ++ [n]) : tape) with "Ht1 Hα") as "[$ Hα]". *)
  (*   iMod (ghost_map_update ((M; fsₛ ++ [m]) : tape) with "Ht2 Hαₛ") as "[$ Hαₛ]". *)
  (*   iMod (ec_supply_decrease with "Hε2 Hε") as (????) "H". *)
  (*   iModIntro. iMod "Hclose'" as "_". *)
  (*   iFrame. *)
  (*   iDestruct ("Hwp" with "[//] [-H] []") as "$". *)
  (*   - iSplitL "Hα". *)
  (*     { iExists _. iFrame. *)
  (*       iPureIntro. *)
  (*       rewrite fmap_app //. } *)
  (*     iExists _. iFrame. *)
  (*     iPureIntro. *)
  (*     rewrite fmap_app //. *)
  (*   - iPureIntro. *)
  (*     apply (fin_to_nat_le m). *)
  (*   - iApply ec_supply_eq; [|done]. *)
  (*     simplify_eq/=; lra. *)
  (* Qed. *)

  (* Lemma wp_rand_avoid_l {N} (m : nat) (z : Z) E (ε : R) : *)
  (*   TCEq N (Z.to_nat z) → *)
  (*   ε = 1 / (S N) → *)
  (*   {{{ ↯ ε }}} *)
  (*     rand #z @ E *)
  (*   {{{ (n : nat), RET #n; ⌜n ≠ m⌝ ∗ ⌜ n ≤ N ⌝ }}}. *)
  (* Proof. *)
  (*   iIntros (-> -> Φ) "Hε Hwp". *)
  (*   iApply wp_lift_step_prog_couple; [done|]. *)
  (*   iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)". *)
  (*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'". *)
  (*   iDestruct (ec_supply_ec_inv with "Hε2 Hε") as %(ε &?& -> & ?). *)
  (*   iApply prog_coupl_step_l_dret; [done|solve_red|..]. *)
  (*   { by apply (ARcoupl_rand_no_coll_l _ (fin_force (Z.to_nat z) m)). } *)
  (*   iIntros (?? (n & [= -> ->] & ? & [=])). *)
  (*   iMod (ec_supply_decrease with "Hε2 Hε") as (????) "Hs". *)
  (*   simplify_eq. *)
  (*   do 2 iModIntro. *)
  (*   iMod "Hclose'" as "_". *)
  (*   iFrame. *)
  (*   rewrite -wp_value. *)
  (*   iDestruct ("Hwp" with "[]") as "$". *)
  (*   - iPureIntro. *)
  (*     split; eauto. *)
  (*     + destruct (le_gt_dec m (Z.to_nat z)). *)
  (*       * intro H3. apply H1. apply fin_to_nat_inj. *)
  (*         rewrite fin_force_to_nat_le; auto. *)
  (*       * pose proof (fin_to_nat_le n). lia. *)
  (*     + apply (fin_to_nat_le). *)
  (*  - iApply ec_supply_eq; [|done]. *)
  (*    lra. *)
  (* Qed. *)

  (* Lemma wp_rand_avoid_r {N} (m : nat) (z : Z) K e E Φ (ε : R) : *)
  (*   TCEq N (Z.to_nat z) → *)
  (*   ε = 1 / (S N) → *)
  (*   ⤇ fill K (rand #z) ∗ *)
  (*   ↯ ε ∗ *)
  (*   (∀ (n : nat), *)
  (*      ⤇ fill K #n -∗ ⌜n ≠ m⌝ -∗ ⌜ n ≤ N ⌝ -∗ WP e @ E {{ Φ }}) *)
  (*   ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (-> ->) "(HK & Hε & Hwp)". *)
  (*   iApply wp_lift_step_spec_couple. *)
  (*   iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)". *)
  (*   iDestruct (spec_auth_prog_agree with "Hauth2 HK") as "->". *)
  (*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'". *)
  (*   iDestruct (ec_supply_ec_inv with "Hε2 Hε") as %(ε &?& -> & ?). *)
  (*   iApply (spec_coupl_erasable_steps 1 _ (dret σ1)); [done|..]. *)
  (*   { rewrite pexec_1 step_or_final_no_final //; last first. *)
  (*     { apply reducible_not_final. solve_red. } *)
  (*     eapply ARcoupl_steps_ctx_bind_r; [done|]. *)
  (*     by apply (ARcoupl_rand_no_coll_r _ (fin_force (Z.to_nat z) m)). } *)
  (*   { apply dret_erasable. } *)
  (*   iIntros (??? (n & [=-> ] & (y&->&[=-> ->]&?))) "!>". *)
  (*   iApply spec_coupl_ret. *)
  (*   iMod (spec_update_prog (fill K #_) with "Hauth2 HK") as "[$ HK]". *)
  (*   iMod (ec_supply_decrease with "Hε2 Hε") as (????) "H". *)
  (*   simplify_eq. *)
  (*   iMod "Hclose'" as "_". *)
  (*   iFrame. *)
  (*   iDestruct ("Hwp" with "[$] []") as "Hwp". *)
  (*   { *)
  (*     iPureIntro. *)
  (*     destruct (le_gt_dec m (Z.to_nat z)). *)
  (*     - intro H3. apply H2. apply fin_to_nat_inj. *)
  (*       rewrite fin_force_to_nat_le; auto. *)
  (*     - pose proof (fin_to_nat_le y). lia. *)
  (*   } *)
  (*   iSplitL "H". *)
  (*   { iApply ec_supply_eq; [|done]. *)
  (*     lra. } *)
  (*   iApply "Hwp". *)
  (*   iPureIntro. *)
  (*   apply (fin_to_nat_le y). *)
  (* Qed. *)

  (* (** rand(unit, N) ~ rand(unit, M) coupling, N <= M, under inj *) *)
  (* Lemma wp_couple_rand_rand_inj (N M : nat) (f: nat → nat) z w K E (ε : R) : *)
  (*   (∀ n, n < S N → f n < S M)%nat → *)
  (*   (∀ n1 n2, n1 < S N → n2 < S N → f n1 = f n2 → n1 = n2)%nat → *)
  (*   TCEq N (Z.to_nat z) → *)
  (*   TCEq M (Z.to_nat w) → *)
  (*   (N <= M)%nat → *)
  (*   (S M - S N) / S M = ε → *)
  (*   {{{ ⤇ fill K (rand #w) ∗ ↯ ε }}} *)
  (*     rand #z @ E *)
  (*   {{{ (n : nat), RET #n; ⤇ fill K #(f n) ∗ ⌜ n ≤ N ⌝ }}}. *)
  (* Proof. *)
  (*   iIntros (Hdom Hinj). *)

  (*   set g := (λ m : fin (S N), Fin.of_nat_lt (Hdom m (fin_to_nat_lt m))). *)
  (*   assert (Inj eq eq g). *)
  (*   { intros m1 m2 Heq. *)
  (*     assert (fin_to_nat (g m1) = f (fin_to_nat m1)) as H1. *)
  (*     { rewrite /g fin_to_nat_to_fin //. } *)
  (*     assert (fin_to_nat (g m2) = f (fin_to_nat m2)) as H2. *)
  (*     { rewrite /g fin_to_nat_to_fin //. } *)
  (*     apply fin_to_nat_inj. *)
  (*     apply Hinj; [apply fin_to_nat_lt..|]. *)
  (*     rewrite -H1 -H2 //. by f_equal. } *)

  (*   iIntros (-> -> HNM Hε ?) "(Hr & Hε) Hcnt". *)
  (*   iApply wp_lift_step_prog_couple; [done|]. *)
  (*   iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)". *)
  (*   iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->. *)
  (*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'". *)
  (*   iDestruct (ec_supply_ec_inv with "Hε2 Hε") as %(? &?& -> & ?). *)
  (*   iApply prog_coupl_steps; [done|solve_red|solve_red|..]. *)
  (*   { apply ARcoupl_steps_ctx_bind_r, (ARcoupl_rand_rand_inj _ _ g); done || lra. } *)
  (*   iIntros (???? (?& [=->] & (n & [=-> ->] & [=-> ->]))). *)
  (*   iMod (spec_update_prog (fill K #(g _)) with "Hauth2 Hr") as "[$ Hspec0]". *)
  (*   iMod (ec_supply_decrease with "Hε2 Hε") as (????) "H". *)
  (*   do 2 iModIntro. *)
  (*   iMod "Hclose'" as "_". *)
  (*   iModIntro. iFrame. *)
  (*   rewrite -wp_value. *)
  (*   rewrite /g fin_to_nat_to_fin. *)
  (*   iDestruct ("Hcnt" with "[$Hspec0]") as "$". *)
  (*   { *)
  (*     iPureIntro. *)
  (*     apply fin_to_nat_le. *)
  (*   } *)
  (*   iApply ec_supply_eq; [|done]. *)
  (*   simplify_eq. lra. *)
  (* Qed. *)

  (* (** rand(unit, N) ~ rand(unit, M) coupling, N <= M, under equality *) *)
  (* Lemma wp_couple_rand_rand_leq (N M : nat) z w K E (ε : R) : *)
  (*   TCEq N (Z.to_nat z) → *)
  (*   TCEq M (Z.to_nat w) → *)
  (*   (N <= M)%nat → *)
  (*   (S M - S N) / S M = ε → *)
  (*   {{{ ⤇ fill K (rand #w) ∗ ↯ ε }}} *)
  (*     rand #z @ E *)
  (*   {{{ (n : nat), RET #n; *)
  (*       ⌜ n ≤ N ⌝ ∗ ⤇ fill K #n }}}. *)
  (* Proof. *)
  (*   iIntros (-> -> HNM <- ?) "(Hr & Hε) Hwp". *)
  (*   iApply (wp_couple_rand_rand_inj _ _ (λ x, x) with "[$]"); [lia|lia|done|done|]. *)
  (*   iModIntro. iIntros (?) "[? %]". iApply ("Hwp" $! n). *)
  (*   iFrame. *)
  (*   iPureIntro. lia. *)
  (* Qed. *)

  (* (** rand(unit, N) ~ rand(unit, M) coupling, M <= N, along an injection *) *)
  (* Lemma wp_couple_rand_rand_rev_inj (N M : nat) (f : nat -> nat) z w K E (ε : R) : *)
  (*   (∀ n, n < S M -> f n < S N)%nat → *)
  (*   (∀ n1 n2, n1 < S M → n2 < S M → f n1 = f n2 → n1 = n2)%nat → *)
  (*   TCEq N (Z.to_nat z) → *)
  (*   TCEq M (Z.to_nat w) → *)
  (*   (M <= N)%nat → *)
  (*   (S N - S M) / S N = ε → *)
  (*   {{{ ⤇ fill K (rand #w) ∗ ↯ ε }}} *)
  (*     rand #z @ E *)
  (*   {{{ (m : nat), RET #(f m); ⤇ fill K #m ∗ ⌜ m ≤ M ⌝ }}}. *)
  (* Proof. *)
  (*   iIntros (Hdom Hinj). *)

  (*   set g := (λ m : fin (S M), Fin.of_nat_lt (Hdom m (fin_to_nat_lt m))). *)
  (*   assert (Inj eq eq g). *)
  (*   { intros m1 m2 Heq. *)
  (*     assert (fin_to_nat (g m1) = f (fin_to_nat m1)) as H1. *)
  (*     { rewrite /g fin_to_nat_to_fin //. } *)
  (*     assert (fin_to_nat (g m2) = f (fin_to_nat m2)) as H2. *)
  (*     { rewrite /g fin_to_nat_to_fin //. } *)
  (*     apply fin_to_nat_inj. *)
  (*     apply Hinj; [apply fin_to_nat_lt..|]. *)
  (*     rewrite -H1 -H2 //. by f_equal. } *)

  (*   iIntros (-> -> HNM <- ?) "(Hr & Hε) Hwp". *)
  (*   iApply wp_lift_step_prog_couple; [done|]. *)
  (*   iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)". *)
  (*   iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->. *)
  (*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'". *)
  (*   iDestruct (ec_supply_ec_inv with "Hε2 Hε") as %(? & ? & -> & ?). *)
  (*   iApply prog_coupl_steps; [done|solve_red|solve_red|..]. *)
  (*   { eapply ARcoupl_steps_ctx_bind_r; [done|]. *)
  (*     by eapply (ARcoupl_rand_rand_rev_inj _ _ g). } *)
  (*   iIntros (???? (?& [=->] & (n & [=-> ->] & [=-> ->]))). *)
  (*   iMod (spec_update_prog (fill K #_) with "Hauth2 Hr") as "[$ Hspec0]". *)
  (*   iMod (ec_supply_decrease with "Hε2 Hε") as (????) "H". *)
  (*   do 2 iModIntro. *)
  (*   iMod "Hclose'" as "_". *)
  (*   iModIntro. iFrame. *)
  (*   rewrite /g fin_to_nat_to_fin //. *)
  (*   rewrite -wp_value. *)
  (*   iDestruct ("Hwp" with "[$Hspec0]") as "$". *)
  (*   { iPureIntro. *)
  (*     apply fin_to_nat_le. } *)
  (*   iApply ec_supply_eq; [|done]. *)
  (*   simplify_eq. lra. *)
  (* Qed. *)

  (* (** rand(unit, N) ~ rand(unit, M) coupling, N <= M, under equality *) *)
  (* Lemma wp_couple_rand_rand_rev_leq (N M : nat) z w K E (ε : R) : *)
  (*   TCEq N (Z.to_nat z) → *)
  (*   TCEq M (Z.to_nat w) → *)
  (*   (M <= N)%nat → *)
  (*   (S N - S M) / S N = ε → *)
  (*   {{{ ⤇ fill K (rand #w) ∗ ↯ ε }}} *)
  (*     rand #z @ E *)
  (*   {{{ (n : nat ), RET #n; *)
  (*       ⌜ n ≤ N ⌝ ∗ ⤇ fill K #n }}}. *)
  (* Proof. *)
  (*   iIntros (-> -> HNM <- ?) "(Hr & Hε) Hwp". *)
  (*   iApply (wp_couple_rand_rand_rev_inj _ _ (λ x, x) with "[$]"); [lia|lia|done|done|..]. *)
  (*   iIntros "!>" (m) "[? %]". *)
  (*   iSpecialize ("Hwp" $! m). *)
  (*   iApply ("Hwp" with "[-]"). *)
  (*   iFrame. *)
  (*   iPureIntro. lia. *)
  (* Qed. *)


  (** * rand(N) ~ rand(N) coupling *)
  (* *)
  (*   There should be an easier proof of this using wp_couple_rand_rand_inj, *)
  (*   but that uses an injective function nat -> nat as opposed to fin (S N) -> fin (S N) *)
  (* *)
  Lemma wp_couple_rand_rand N f `{Bij nat nat f} j z K E :
    TCEq N (Z.to_nat z) →
    (forall n:nat, (n < S N)%nat -> (f n < S N)%nat) ->
    {{{ j ⤇ fill K (rand #z) }}}
      rand #z @ E
    {{{ (n : nat), RET #n; ⌜ n ≤ N ⌝ ∗ j ⤇ fill K #(f n) }}}.
  Proof.
    iIntros (-> Hdom Ψ) "Hr HΨ".
    destruct (restr_bij_fin (S _) f Hdom) as [ff [Hbij Hff]].
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 ρ1 ε) "[Hσ [Hs Hε]]".
    iDestruct (spec_auth_prog_agree with "Hs Hr") as "%Hsome".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    (* replace ε with (0 + ε)%NNR; last first. *)
    (* { apply nnreal_ext; simpl; lra. } *)
    rewrite /prog_coupl.
    destruct ρ1 as [l s].
    assert (j < length l)%nat.
    { by eapply lookup_lt_Some. }
    iExists _, (full_info_one_step_stutter_osch j), 0%NNR, (λ _, ε), ε.
    solve_red.
    repeat iSplit.
    - done.
    - rewrite Expval_const; last done.
      iPureIntro.
      rewrite Rplus_0_l.
      trans (ε*1); last (simpl; lra).
      by apply Rmult_le_compat.
    - iPureIntro. rewrite full_info_one_step_stutter_osch_lim_exec/=.
      rewrite head_prim_step_eq/=.
      (* apply ARcoupl_map; first done. *)
      rewrite /step'.
      rewrite Hsome.
      case_match eqn:Heqn.
      { apply mk_is_Some in Heqn. apply fill_val in Heqn. simpl in *. by destruct Heqn. }
      rewrite fill_dmap //=.
      rewrite head_prim_step_eq///=.
      rewrite !dmap_comp.
      apply ARcoupl_map; first done.
      simpl.
      apply ARcoupl_exact.
      eapply Rcoupl_mono.
      + apply (Rcoupl_dunif); apply Hbij.
      + simpl.
        intros ? ? ->.
        instantiate (1 := (λ x y, ∃ (a:fin(S (Z.to_nat z))),
                              x= (Val (#a), σ1, []) /\
                              y=([(cfg_to_cfg' (l, s), j);
                                  (cfg_to_cfg' (<[j:=fill K #(ff a)]> l ++ [], s), length (<[j:=fill K #(ff a)]> l ++ []))],
                                   (<[j:=fill K #(ff a)]> l ++ [], s))
                    )).
        naive_solver.
    - simpl.
      iPureIntro.
      intros?????(?&?&H')(?&?&?).
      destruct!/=.
      rewrite !app_nil_r in H'.
      eapply f_equal in H'.
      erewrite !list_lookup_insert in H'; try done.
      by simplify_eq.
    - simpl.
      iIntros (?????[a ?]).
      destruct!/=.
      iMod (spec_update_prog with "[$][$]") as "[HK Hs]".
      iModIntro. iNext.
      iMod "Hclose".
      rewrite app_nil_r.
      iFrame.
      iModIntro.
      wp_pures.
      iApply "HΨ".
      rewrite Hff. iFrame.
      iModIntro. iPureIntro.
      pose proof fin_to_nat_lt a. lia.
  Qed.

  
  Lemma wp_couple_rand_rand' N f `{Bij nat nat f} j z K E :
    TCEq N (Z.to_nat z) →
    (forall n:nat, (n < S N)%nat -> (f n < S N)%nat) ->
    {{{ j ⤇ fill K (rand #z) }}}
      rand #z @ E
      {{{ (n : nat), RET #(f n); ⌜ n ≤ N ⌝ ∗ j ⤇ fill K #n }}}.
  Proof.
    iIntros (Heq Hdom Ψ) "Hr HΨ".
    rewrite Heq.
    wp_apply (wp_couple_rand_rand _ (f_inv f) with "[$]").
    - intros.
      apply f_inv_restr; naive_solver.
    - iIntros (?) "(%&Hspec)".
      replace n with (f (f_inv f n)); last apply f_inv_cancel_r.
      iApply "HΨ".
      rewrite f_inv_cancel_l.
      iFrame.
      iPureIntro.
      rewrite -Heq.
      assert (f_inv f n< S N)%nat; last lia.
      apply f_inv_restr; try lia; naive_solver.
      Unshelve.
      apply f_inv_bij.
  Qed.

  (** * Coupling a rand on LHS with two rands on the RHS *)

  Lemma wp_couple_rand_two_rands N M f K K' E z z' x j j':
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat z')->
    x=Z.of_nat ((S N)*(S M)-1) -> 
    (∀ n m, n < S N -> m< S M -> f n m < (S N)*(S M))%nat →
    (∀ n n' m m', n < S N -> n' < S N -> m < S M -> m' < S M -> f n m = f n' m' -> n=n' /\ m=m')%nat ->
    (forall x, x<(S N)*(S M) -> exists n m, n< S N /\ m < S M /\ f n m = x)%nat ->
    {{{ j ⤇ fill K (rand #N) ∗ j'⤇ fill K' (rand #M) }}}
      rand #x @ E
      {{{ (x:nat), RET #x; ∃ (n m:nat), ⌜(n<=N)%nat⌝ ∗ ⌜(m<=M)%nat⌝ ∗ ⌜x=f n m⌝ ∗ j ⤇ fill K #n ∗ j'⤇ fill K' #m }}}.
  Proof.
    iIntros (->->-> Hcond1 Hcond2 Hcond3 Φ) "[Hj Hj'] HΦ".
    iApply wp_lift_step_prog_couple; first done.
    iIntros (σ1 ρ1 ε) "[Hσ [Hs Hε]]".
    iDestruct (spec_auth_prog_agree with "Hs Hj") as "%Hsome".
    iDestruct (spec_auth_prog_agree with "Hs Hj'") as "%Hsome'".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    rewrite /prog_coupl.
    destruct ρ1 as [l s].
    assert (j < length l)%nat.
    { by eapply lookup_lt_Some. }
    assert (j' < length l)%nat.
    { by eapply lookup_lt_Some. }
    iDestruct (ghost_map_elem_ne with "[$][$]") as "%".
    iExists _, (full_info_cons_osch (λ _, dret j) (λ _, full_info_one_step_stutter_osch j')), 0%NNR, (λ _, ε), ε.
    solve_red.
    repeat iSplit.
    - done.
    - rewrite Expval_const; last done.
      iPureIntro.
      rewrite Rplus_0_l.
      trans (ε*1); last (simpl; lra).
      by apply Rmult_le_compat.
    - iPureIntro.
      Local Opaque full_info_cons_osch.
      Local Opaque full_info_one_step_stutter_osch full_info_lift_osch. simpl.
      rewrite full_info_cons_osch_lim_exec/=.
      rewrite dret_id_left Hsome.
      rewrite fill_not_val; last done.
      rewrite fill_dmap //=.
      rewrite !head_prim_step_eq /= !dmap_comp.
      rewrite !Nat2Z.id.
      erewrite dbind_ext_right_strong; last first.
      { instantiate (1:= (λ '(_,_), _)).
        intros [l0 ] Hpos.
        apply dmap_pos in Hpos. simpl in *. destruct!/=.
        rewrite full_info_lift_osch_lim_exec.
        rewrite full_info_one_step_stutter_osch_lim_exec.
        rewrite dmap_comp.
        rewrite app_nil_r.
        instantiate (1:= dmap _ _).
        rewrite /step'. f_equal. 
        rewrite list_lookup_insert_ne; last done.
        rewrite Hsome'.
        rewrite fill_not_val; last done.
        rewrite fill_dmap//=.
        rewrite head_prim_step_eq/=.
        rewrite !dmap_comp. 
        rewrite !Nat2Z.id. repeat f_equal.
        - instantiate (1:=( λ '(e,s0,l''), (<[j':=e]>l0++l'', _))).
          extensionality x.
          destruct x as [[]]. f_equal. 
        - instantiate (1:= (λ _, _)). f_equal.
      }
      rewrite {4}/dmap.
      rewrite -dbind_assoc'.
      erewrite dbind_ext_right; last first.
      { intros. by rewrite dret_id_left/= dmap_comp/=app_nil_r. }

      (** Here we define the f' function that is specialized to fin *)
      rewrite Nat.sub_0_r.
      assert (∀ n m : nat,
             (n < S (Z.to_nat z))%nat
             → (m < S (Z.to_nat z'))%nat → (f n m < S(Z.to_nat z' + Z.to_nat z * S (Z.to_nat z')))%nat) as Hcond1'.
      { intros. naive_solver. }
      set (f' := λ '((n,m): (fin (S (Z.to_nat z)) * fin (S (Z.to_nat z')))),
             nat_to_fin (Hcond1' _ _ (fin_to_nat_lt n) (fin_to_nat_lt m))
          ).
      assert (Bij f') as Hbij.
      { split.
        - intros [x y][x' y'].
          rewrite /f'.
          intros Heq.
          apply (f_equal fin_to_nat) in Heq.
          rewrite !fin_to_nat_to_fin in Heq.
          apply Hcond2 in Heq; destruct!/=; first naive_solver.
          all: apply fin_to_nat_lt.
        - intros x.
          pose proof fin_to_nat_lt x.
          apply Hcond3 in H2 as (n'&m'&Hn'&Hm'&Hrewrite).
          exists (nat_to_fin Hn',nat_to_fin Hm').
          rewrite /f'.
          apply fin_to_nat_inj.
          by rewrite !fin_to_nat_to_fin -Hrewrite.
      }
      rewrite (dunifP_decompose _ _ _ f' ); last lia.
      rewrite /dmap -dbind_assoc'.
      replace 0%R with (0+0) by lra.
      eapply ARcoupl_dbind; [done|done| |apply ARcoupl_eq].
      intros ? n ->.
      rewrite -dbind_assoc'.
      replace 0%R with (0+0) by lra.
      eapply ARcoupl_dbind; [done|done| |apply ARcoupl_eq].
      intros ? m ->.
      simpl. rewrite app_nil_r dret_id_left' fin_to_nat_to_fin.
      rewrite !insert_length.
      instantiate (1:= λ x y, ∃ (n:fin(S (Z.to_nat z))) (m:fin(S (Z.to_nat z'))), x = (Val #(f n m),σ1,[])/\ y=([(cfg_to_cfg' (l, s), j); (cfg_to_cfg' (<[j:=fill K #n]> l, s), j');
         (cfg_to_cfg' (<[j':=fill K' #m]> (<[j:=fill K #n]> l), s), length l)],
        (<[j':=fill K' #m]> (<[j:=fill K #n]> l), s))).
      apply ARcoupl_dret; naive_solver.
    - iPureIntro. simpl. intros ????? (n&m&K1&K2) (n'&m'&K3&K4). destruct!/=.
      assert (n=n'). 
      { apply (f_equal (λ x, x!!j)) in K2.
        rewrite !list_lookup_insert in K2; naive_solver.
      }
      subst.
      replace m with m'; first done.
      cut ((<[j':=fill K' #m']> (<[j:=fill K #n']> l))!!j' = (<[j':=fill K' #m]> (<[j:=fill K #n']> l)!!j')).
      + rewrite !list_lookup_insert; try rewrite insert_length; naive_solver.
      + by f_equal.
    - simpl.
      iIntros (?????) "(%n&%m&%)". destruct!/=.
      iMod (spec_update_prog with "Hs Hj") as "[Hs ?]".
      iMod (spec_update_prog with "Hs Hj'") as "[??]".
      iFrame.
      iModIntro. iNext. iMod "Hclose".
      iModIntro. iFrame.
      wp_pures.
      iApply "HΦ".
      iFrame. iPureIntro.
      pose proof fin_to_nat_lt n.
      pose proof fin_to_nat_lt m; lia.
  Qed. 
  
  (* (** coupling rand and rand but avoid certain values*) *)
  (* Lemma wp_couple_rand_rand_avoid N (l:list _) z K E : *)
  (*   TCEq N (Z.to_nat z) → *)
  (*   NoDup l ->  *)
  (*   {{{ ↯ (length l/(N+1)) ∗ *)
  (*         ⤇ fill K (rand #z) }}} *)
  (*     rand #z @ E *)
  (*     {{{ (n : fin (S N)), RET #n; ⌜n∉l⌝ ∗ ⤇ fill K #n }}}. *)
  (* Proof. *)
  (*   iIntros (H0 Hl Ψ) "[Hε Hr] HΨ". *)
  (*   iApply wp_lift_step_prog_couple; [done|]. *)
  (*   iIntros (σ1 e1' σ1' ε) "[Hσ [Hs Hε2]]". *)
  (*   iDestruct (spec_auth_prog_agree with "Hs Hr") as %->. *)
  (*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose". *)
  (*   iDestruct (ec_supply_ec_inv with "Hε2 Hε") as %(x & x1 & -> & H). *)
  (*   iApply (prog_coupl_steps _ _ _ *)
  (*             (* (λ ρ2 ρ2', *) *)
  (*             (*   ∃ (n : fin _), n∉l /\ρ2 = (Val #n, σ1) ∧ ρ2' = (fill K #(n), σ1')) *)) *)
  (*   ; [done|solve_red|solve_red|..]. *)
  (*   { eapply ARcoupl_steps_ctx_bind_r; first done. *)
  (*     apply ARcoupl_rand_rand_avoid_list; first done. *)
  (*     - by rewrite S_INR.  *)
  (*     - by apply TCEq_eq. *)
  (*   } *)
  (*   iIntros (e2 σ2 e2' σ2' (b & [= ->] & (?&?&[= -> ->] & [= -> ->]))) "!> !>". *)
  (*   iMod (spec_update_prog with "Hs Hr") as "[$ Hr]". *)
  (*   iMod (ec_supply_decrease with "Hε2 Hε") as (x2 x3 H1 ?) "H". *)
  (*   replace (x3) with (x1); last first. *)
  (*   { apply nnreal_ext. inversion H1. *)
  (*     lra. *)
  (*   } *)
  (*   iMod "Hclose" as "_". *)
  (*   (* replace (0 + ε)%NNR with ε; last first. *) *)
  (*   (* { apply nnreal_ext; simpl; lra. } *) *)
  (*   iFrame. *)
  (*   iApply wp_value. *)
  (*   iApply "HΨ". *)
  (*   iFrame. *)
  (*   by iPureIntro. *)
  (* Qed. *)

  (* Local Lemma length_remove_dups `{EqDecision A} (l:list A): *)
  (*   length (remove_dups l) <= length l. *)
  (* Proof. *)
  (*   induction l; first done. *)
  (*   simpl. *)
  (*   case_match; simpl. *)
  (*   all: rewrite -!/(INR (S _)); rewrite !S_INR; lra. *)
  (* Qed. *)

  (* Lemma wp_couple_rand_rand_avoid' N (l:list _) z K E : *)
  (*   TCEq N (Z.to_nat z) → *)
  (*   {{{ ↯ (length l/(N+1)) ∗ *)
  (*         ⤇ fill K (rand #z) }}} *)
  (*     rand #z @ E *)
  (*     {{{ (n : fin (S N)), RET #n; ⌜n∉l⌝ ∗ ⤇ fill K #n }}}. *)
  (* Proof. *)
  (*   set (l':=remove_dups l). *)
  (*   iIntros (H0 Ψ) "[Hε Hr] HΨ". *)
  (*   iApply (wp_couple_rand_rand_avoid with "[-HΨ]"). *)
  (*   - apply NoDup_remove_dups. *)
  (*   - iFrame. *)
  (*     iApply (ec_weaken with "[$]"). *)
  (*     split. *)
  (*     + apply Rcomplements.Rdiv_le_0_compat. *)
  (*       * apply pos_INR. *)
  (*       * pose proof pos_INR N. lra. *)
  (*     + rewrite !Rdiv_def. *)
  (*       apply Rmult_le_compat_r. *)
  (*       * apply Rlt_le. apply Rinv_0_lt_compat. pose proof pos_INR N. lra. *)
  (*       * apply length_remove_dups.  *)
  (*   - iModIntro. iIntros (?) "[%?]". *)
  (*     iApply "HΨ". iFrame. *)
  (*     iPureIntro. *)
  (*     by rewrite -elem_of_remove_dups. *)
  (* Qed. *)
  

  (* (** fragmented state rand N ~ state rand M, N>=M, under injective function from M to N*) *)
  (* Lemma wp_couple_fragmented_rand_rand_inj {M N} (f: nat → nat) {_ : Inj (=) (=) f} *)
  (*   ns nsₛ α αₛ e E Φ: *)
  (*   (M <= N)%nat → *)
  (*   (forall n : nat, (n < S M)%nat -> (f n < S N)%nat) -> *)
  (*   ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗ *)
  (*   (∀ (n : nat), *)
  (*      ⌜ n ≤ N ⌝ -∗ *)
  (*      if bool_decide (∃ m:nat, m ≤ M /\ f m = n) then *)
  (*        ∀ m : nat, α ↪N (N; ns ++ [f m]) ∗ αₛ ↪ₛN (M; nsₛ ++ [m]) ∗ ⌜ f m ≤ N ⌝ ∗ ⌜ m ≤ M ⌝ -∗ *)
  (*             WP e @ E {{ Φ }} *)
  (*      else *)
  (*        α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ) ∗ ⌜ n ≤ N ⌝ -∗ *)
  (*        WP e @ E {{ Φ }}) *)
  (*   ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (Hineq Hdom) "(>Hα & >Hαₛ & Hwp)". *)
  (*   edestruct (restr_inj_fin (S M) (S N) f (le_n_S M N Hineq) Hdom) as [g [HgInj HgEq]]. *)
  (*   iDestruct "Hα" as (fs) "(<-&Hα)". *)
  (*   iDestruct "Hαₛ" as (fsₛ) "(<-&Hαₛ)". *)
  (*   iApply wp_lift_step_spec_couple. *)
  (*   iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)". *)
  (*   iDestruct "Hauth2" as "(HK&Hh2&Ht2)/=". *)
  (*   iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?. *)
  (*   iDestruct (ghost_map_lookup with "Ht1 Hα") as %?. *)
  (*   simplify_map_eq. *)
  (*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'". *)
  (*   replace (ε_now) with (0 + ε_now)%NNR; last (apply nnreal_ext; simpl; lra). *)
  (*   iApply spec_coupl_erasables; [done|..]. *)
  (*   { by apply ARcoupl_exact, Rcoupl_fragmented_rand_rand_inj. } *)
  (*   { by eapply state_step_erasable. } *)
  (*   { eapply erasable_dbind_predicate. *)
  (*     - solve_distr_mass. *)
  (*     - by eapply state_step_erasable. *)
  (*     - apply dret_erasable. } *)
  (*   iIntros (?? [n H']). *)
  (*   case_bool_decide in H'. *)
  (*   - destruct Hf as [m' <-]. *)
  (*     destruct H' as (m & ? & ? & Hfm). *)
  (*     simplify_eq. *)
  (*     iMod (ghost_map_update ((N; fs ++ [g _]) : tape) with "Ht1 Hα") as "[Ht1 Hα]". *)
  (*     iMod (ghost_map_update ((M; fsₛ ++ [_]) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]". *)
  (*     iModIntro. *)
  (*     iApply spec_coupl_ret. *)
  (*     iMod "Hclose'" as "_". *)
  (*     iSpecialize ("Hwp" $! (f m')). *)
  (*     rewrite bool_decide_eq_true_2. *)
  (*     2: { exists m'. *)
  (*          split; auto. *)
  (*          apply fin_to_nat_le. } *)
  (*     iSpecialize ("Hwp" $! _ m'). *)
  (*     iDestruct ("Hwp" with "[$Hα $Hαₛ]") as "Hwp". *)
  (*     { iPureIntro. *)
  (*       split; [rewrite fmap_app /= HgEq // |]. *)
  (*       split; [rewrite fmap_app /=  // |]. *)
  (*       split; auto. *)
  (*       - apply Nat.lt_succ_r, Hdom, fin_to_nat_lt. *)
  (*       - apply fin_to_nat_le. *)
  (*     } *)
  (*     assert (0 + ε_now = ε_now)%NNR as ->. *)
  (*     { apply nnreal_ext; simpl; lra. } *)
  (*     by iFrame. *)
  (*   - destruct H' as [??]. simplify_eq. *)
  (*     iMod (ghost_map_update ((N; fs ++ [n]) : tape) with "Ht1 Hα") as "[Ht1 Hα]". *)
  (*     iModIntro. *)
  (*     iApply spec_coupl_ret. *)
  (*     iMod "Hclose'" as "_". *)
  (*     iSpecialize ("Hwp" $! (fin_to_nat n)). *)
  (*     rewrite bool_decide_eq_false_2 //. *)
  (*     2: { *)
  (*       intros [m [Hm1 Hm2]]. *)
  (*       apply Hf. *)
  (*       assert (m < S M)%nat as Hm3. *)
  (*       { lia. } *)
  (*       exists (nat_to_fin Hm3). *)
  (*       apply fin_to_nat_inj. *)
  (*       rewrite HgEq -Hm2. *)
  (*       rewrite fin_to_nat_to_fin //. *)
  (*     } *)
  (*     iDestruct ("Hwp" with "[]") as "Hwp". *)
  (*     { iPureIntro. apply fin_to_nat_le. } *)
  (*     assert (0 + ε_now = ε_now)%NNR as ->. *)
  (*     { apply nnreal_ext; simpl; lra. } *)
  (*     iFrame. *)
  (*     iApply "Hwp". *)
  (*     iModIntro. *)
  (*     iSplitL "Hα". *)
  (*     { iFrame. rewrite fmap_app //. } *)
  (*     iSplitL "Hαₛ". *)
  (*     { iFrame. auto. } *)
  (*     iPureIntro. apply fin_to_nat_le. *)
  (*     Unshelve. *)
  (*     apply Nat.lt_succ_r, Hdom, fin_to_nat_lt. *)
  (* Qed. *)

  (* (** fragmented state rand N ~ state rand M, N>=M, under equality*) *)
  (* Lemma wp_couple_fragmented_rand_rand_leq (M N : nat) ns nsₛ α αₛ e E Φ: *)
  (*   (M <= N)%nat → *)
  (*   ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗ *)
  (*   (∀ (n : nat), *)
  (*      ⌜ n ≤ N ⌝ -∗ *)
  (*      if (bool_decide (n < S M)%nat) *)
  (*        then *)
  (*          α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ ++ [n]) ∗ ⌜ n ≤ M ⌝ -∗ *)
  (*          WP e @ E {{ Φ }} *)
  (*        else *)
  (*          α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ) ∗ ⌜ n ≤ N ⌝ -∗ *)
  (*          WP e @ E {{ Φ }} *)
  (*   ) *)
  (*   ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (Hineq) "(>Hα & >Hαₛ & Hwp)". *)

  (*   (* *)
  (*   assert (∀ x : fin (S M), fin_to_nat x < S N)%nat as H. *)
  (*   { intros. pose proof (fin_to_nat_lt x). lia. } *)
  (*   set f := (λ x, nat_to_fin (H x)). *)
  (*   assert (Inj (eq) (eq) f) as Hinj. *)
  (*   { rewrite /f. intros ?? H0. *)
  (*     apply (f_equal fin_to_nat) in H0. rewrite !fin_to_nat_to_fin in H0. *)
  (*     by apply fin_to_nat_inj. } *) *)

  (*   iApply (wp_couple_fragmented_rand_rand_inj (λ x, x) with "[$Hα $Hαₛ Hwp]"); [done| intros; lia |]. *)
  (*   iIntros (n) "%Hn". *)
  (*   case_bool_decide as H1. *)
  (*   - destruct H1 as [n' [Hn' <-]]. *)
  (*     iIntros (?) "(?&?&%&%)". *)
  (*     iSpecialize ("Hwp" $! m). *)
  (*     rewrite bool_decide_eq_true_2; last by lia. *)
  (*     iApply "Hwp"; auto. *)
  (*     by iFrame. *)
  (*   - iSpecialize ("Hwp" $! n). *)
  (*     case_match. *)
  (*     2: { iIntros "(?&?&%)". *)
  (*          iApply "Hwp"; auto. *)
  (*          by iFrame. } *)
  (*     exfalso. apply H1. *)
  (*     exists n. split; auto. *)
  (*     apply bool_decide_eq_true_1 in H. *)
  (*     lia. *)
  (* Qed. *)

  (* (** * fragmented state rand N ~ state rand M, M>=N, under injective function from N to M*) *)
  (* Lemma wp_couple_fragmented_rand_rand_inj_rev {M N} (f: nat -> nat) {_: Inj (=) (=) f} *)
  (*   ns nsₛ α αₛ e E Φ: *)
  (*   (N <= M)%nat → *)
  (*   (forall n, n < S N -> f n < S M)%nat -> *)
  (*   ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗ *)
  (*   (∀ (m : nat), *)
  (*       ⌜ m ≤ M ⌝ -∗ *)
  (*       if bool_decide (∃ n:nat, n ≤ N /\ f n = m) then *)
  (*         ∀ n, α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ ++ [f n]) ∗ ⌜n ≤ N⌝ ∗ ⌜f n ≤ M⌝ -∗ *)
  (*              WP e @ E {{ Φ }} *)
  (*       else *)
  (*         α ↪N (N; ns) ∗ αₛ ↪ₛN (M; nsₛ++[m]) ∗ ⌜m ≤ M⌝ -∗ WP e @ E {{ Φ }}) *)
  (*   ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (Hineq Hdom) "(>Hα & >Hαₛ & Hwp)". *)
  (*   edestruct (restr_inj_fin (S N) (S M) f (le_n_S N M Hineq) Hdom) as [g [HgInj HgEq]]. *)
  (*   iDestruct "Hα" as (fs) "(<-&Hα)". *)
  (*   iDestruct "Hαₛ" as (fsₛ) "(<-&Hαₛ)". *)
  (*   iApply wp_lift_step_spec_couple. *)
  (*   iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)". *)
  (*   iDestruct "Hauth2" as "(HK&Hh2&Ht2)/=". *)
  (*   iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?. *)
  (*   iDestruct (ghost_map_lookup with "Ht1 Hα") as %?. *)
  (*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'". *)
  (*   replace (ε_now) with (0+ε_now)%NNR; last (apply nnreal_ext; simpl; lra). *)
  (*   iApply spec_coupl_erasables; [done|..]. *)
  (*   { by apply ARcoupl_exact, Rcoupl_swap, Rcoupl_fragmented_rand_rand_inj. } *)
  (*   { eapply erasable_dbind_predicate. *)
  (*     - solve_distr_mass. *)
  (*     - by eapply state_step_erasable. *)
  (*     - apply dret_erasable. } *)
  (*   { by eapply state_step_erasable. } *)
  (*   iIntros (?? [m H']). *)
  (*   case_bool_decide in H'. *)
  (*   - destruct Hf as [m' <-]. *)
  (*     destruct H' as (n & ? & ? & Hfn). *)
  (*     simplify_eq. *)
  (*     iMod (ghost_map_update ((N; fs ++ [_]) : tape) with "Ht1 Hα") as "[Ht1 Hα]". *)
  (*     iMod (ghost_map_update ((M; fsₛ ++ [_]) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]". *)
  (*     iModIntro. iApply spec_coupl_ret. iMod "Hclose'" as "_". *)
  (*     iSpecialize ("Hwp" $! (f m')). *)
  (*     rewrite bool_decide_eq_true_2. *)
  (*     2: { exists m'. *)
  (*          split; auto. *)
  (*          apply fin_to_nat_le. } *)
  (*     iSpecialize ("Hwp" $! _ m'). *)
  (*     iDestruct ("Hwp" with "[$Hα $Hαₛ]") as "Hwp". *)
  (*     { iPureIntro. *)
  (*       split; [rewrite fmap_app /=  // |]. *)
  (*       split; [rewrite fmap_app /= -HgEq // |]. *)
  (*       split; auto. *)
  (*       - apply fin_to_nat_le. *)
  (*       - apply Nat.lt_succ_r, Hdom, fin_to_nat_lt. *)
  (*     } *)
  (*     assert (0 + ε_now = ε_now)%NNR as ->. *)
  (*     { apply nnreal_ext; simpl; lra. } *)
  (*     by iFrame. *)
  (*   - destruct H' as [??]. simplify_eq. *)
  (*     iMod (ghost_map_update ((M; fsₛ ++ [m]) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]". *)
  (*     iModIntro. iApply spec_coupl_ret. iMod "Hclose'" as "_". *)
  (*     iSpecialize ("Hwp" $! m). *)
  (*     rewrite bool_decide_eq_false_2 //. *)
  (*     2: { *)
  (*       intros [n [Hn1 Hn2]]. *)
  (*       apply Hf. *)
  (*       assert (n < S N)%nat as Hn3 by lia. *)
  (*       exists (nat_to_fin Hn3). *)
  (*       apply fin_to_nat_inj. *)
  (*       rewrite HgEq -Hn2. *)
  (*       rewrite fin_to_nat_to_fin //. *)
  (*     } *)
  (*     iDestruct ("Hwp" with "[]") as "Hwp"; [iPureIntro; apply fin_to_nat_le | ]. *)
  (*     assert (0 + ε_now = ε_now)%NNR as ->. *)
  (*     { apply nnreal_ext; simpl; lra. } *)
  (*     iFrame. *)
  (*     iApply "Hwp". *)
  (*     iSplitL "Hα"; [by iFrame |]. *)
  (*     iSplitL; [|iPureIntro; apply fin_to_nat_le ]. *)
  (*     iFrame. *)
  (*     rewrite fmap_app /= //. *)
  (*     Unshelve. *)
  (*     apply Nat.lt_succ_r, Hdom, fin_to_nat_lt. *)
  (* Qed. *)

  (* (** fragmented state rand N ~ state rand M, M>=N, under injective function from N to M, *)
  (*     but with errors for rejection sampling! *) *)
  (* Lemma wp_couple_fragmented_rand_rand_inj_rev' {M N} (f : nat -> nat) {_: Inj (=) (=) f} *)
  (*   ns nsₛ α αₛ e E Φ (ε : R) : *)
  (*   0 <= ε → *)
  (*   (N < M)%nat → *)
  (*   (forall n, n < S N -> f n < S M)%nat -> *)
  (*   ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗ ↯ ε ∗ *)
  (*   (∀ (m : nat), *)
  (*      ⌜ m ≤ M ⌝ -∗ *)
  (*      if bool_decide (∃ n:nat, n ≤ N /\ f n = m) then *)
  (*        ∀ n, α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ ++ [f n]) ∗ ⌜ n ≤ N ⌝ ∗ ⌜ f n ≤ M ⌝ -∗ *)
  (*             WP e @ E {{ Φ }} *)
  (*    else *)
  (*      ∀ (ε' : R), *)
  (*        ⌜ε' = (S M / (S M - S N) * ε)%R⌝ ∗ *)
  (*        α ↪N (N; ns) ∗ αₛ ↪ₛN (M; nsₛ++[m]) ∗ ↯ ε' ∗ ⌜ m ≤ M ⌝ -∗ *)
  (*        WP e @ E {{ Φ }}) *)
  (*   ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (Hε Hineq Hdom) "(>Hα & >Hαₛ & Hε & Hwp)". *)
  (*   edestruct (restr_inj_fin (S N) (S M) f (le_n_S N M (Nat.lt_le_incl _ _ Hineq)) Hdom) as [g [HgInj HgEq]]. *)
  (*   iDestruct "Hα" as (fs) "(<-&Hα)". *)
  (*   iDestruct "Hαₛ" as (fsₛ) "(<-&Hαₛ)". *)
  (*   iApply wp_lift_step_spec_couple. *)
  (*   iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)". *)
  (*   iDestruct "Hauth2" as "(HK&Hh2&Ht2)". *)
  (*   iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?. *)
  (*   iDestruct (ghost_map_lookup with "Ht1 Hα") as %?. *)
  (*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'". *)
  (*   iDestruct (ec_supply_bound with "[$][$]") as %Hle. *)
    
  (*   set ε' := mknonnegreal _ Hε. *)
    
  (*   set ε_now1 := nnreal_minus ε_now ε' Hle. *)
  (*   set ε_now2 := (ε_now + ε' * nnreal_nat (S N) / nnreal_nat (S M - S N))%NNR. *)
  (*   set (E2 σ := if bool_decide (∃ x, σ = state_upd_tapes <[αₛ:=(M; fsₛ ++ [g x])]> σ1') *)
  (*                then ε_now1 else ε_now2). *)
  (*   assert (∀ σ, E2 σ <= Rmax ε_now1 ε_now2)%R. *)
  (*   { intros ?. rewrite /E2. apply Rmax_Rle. case_bool_decide; by [left| right]. } *)

  (*   iApply (spec_coupl_erasables_exp E2 (Rmax ε_now1 ε_now2) 0%NNR). *)
  (*   { eapply ARcoupl_exact, Rcoupl_swap, Rcoupl_fragmented_rand_rand_inj; done || lia. } *)
  (*   { apply erasable_dbind_predicate. *)
  (*     - solve_distr_mass. *)
  (*     - by eapply state_step_erasable. *)
  (*     - apply dret_erasable. } *)
  (*   { by eapply state_step_erasable. } *)
  (*   { done. } *)
  (*   { simpl. erewrite state_step_unfold; [|done]. *)
  (*     (* TODO: cleanup *) *)
  (*     rewrite /Expval. *)
  (*     erewrite (SeriesC_ext _ *)
  (*                 (λ b : state, *)
  (*                     if bool_decide (b ∈ (λ x, state_upd_tapes <[αₛ:=(M; fsₛ ++ [x])]> σ1') *)
  (*                                       <$> (fin_enum (S M))) *)
  (*                    then /(S M) * E2 b else 0)%R); last first. *)
  (*     { intros n. *)
  (*       case_bool_decide as Hin; last first. *)
  (*       { apply Rmult_eq_0_compat_r. rewrite /dmap/dbind/dbind_pmf/pmf/=. *)
  (*         apply SeriesC_0. intros. apply Rmult_eq_0_compat_l. *)
  (*         rewrite /dret_pmf. case_bool_decide; last lra. *)
  (*         subst. exfalso. apply Hin. erewrite elem_of_list_fmap. *)
  (*         exists x; split; first done. replace (fin_enum (S M)) with (enum (fin (S M))) by done. *)
  (*         apply elem_of_enum. } *)
  (*       rewrite elem_of_list_fmap in Hin. destruct Hin as [y [-> ?]]. *)
  (*       apply Rmult_eq_compat_r. rewrite /dmap/dbind/dbind_pmf/pmf/=. *)
  (*       rewrite SeriesC_scal_l. *)
  (*       replace (SeriesC _) with 1%R; first lra. *)
  (*       symmetry. *)
  (*       rewrite /dret_pmf. *)
  (*       erewrite (SeriesC_ext _ (λ x, if bool_decide (x = y) then 1 else 0))%R; *)
  (*         first apply SeriesC_singleton. *)
  (*       intros. *)
  (*       case_bool_decide as H2i. *)
  (*       - apply state_upd_tapes_same in H2i. simplify_eq. *)
  (*         case_bool_decide; done. *)
  (*       - case_bool_decide; last done. *)
  (*         subst. done. } *)
  (*     { trans (SeriesC (λ x, if bool_decide (∃ y, g y = x) then / S M * ε_now1 else / S M * ε_now2))%R. *)
  (*       - rewrite Rplus_0_l. *)
  (*         set (h σ := match decide (∃ x, σ = state_upd_tapes <[αₛ:=(M; fsₛ ++ [x])]> σ1') with *)
  (*                   | left Hproof => Some (epsilon Hproof) *)
  (*                   | _ => None *)
  (*                   end). *)
  (*         etrans; last eapply (SeriesC_le_inj _ h). *)
  (*         + apply Req_le_sym. apply SeriesC_ext. (** should be ok *) *)
  (*           intros s. rewrite /h. case_match eqn:Heqn; last first. *)
  (*           { rewrite bool_decide_eq_false_2; first (simpl;lra). *)
  (*             erewrite elem_of_list_fmap. *)
  (*             intros [? [->?]]. apply n. *)
  (*             naive_solver. } *)
  (*           pose proof epsilon_correct _ e0 as H'. *)
  (*           rewrite bool_decide_eq_true_2; last first. *)
  (*           { destruct e0 as [x ?]. subst. rewrite elem_of_list_fmap. *)
  (*             eexists _. split; first done. *)
  (*             replace (fin_enum _) with (enum (fin (S M))) by done. *)
  (*             apply elem_of_enum. } *)
  (*           rewrite !S_INR. *)
  (*           rewrite /E2. *)
  (*           simpl in *. subst. *)
  (*           case_bool_decide as H1'. *)
  (*           * rewrite bool_decide_eq_true_2. *)
  (*             { rewrite /ε_now1. simpl; lra. } *)
  (*             destruct H1' as [y ?]. exists y. rewrite H3. done. *)
  (*           * rewrite bool_decide_eq_false_2. *)
  (*             { rewrite /ε_now2; simpl; lra. } *)
  (*             intros [x H2']. *)
  (*             apply H1'. rewrite H' in H2'. apply state_upd_tapes_same in H2'. simplify_eq. *)
  (*             naive_solver. *)
  (*         + intros. case_bool_decide; apply Rmult_le_pos; try done. *)
  (*           all: rewrite <-Rdiv_1_l; apply Rcomplements.Rdiv_le_0_compat; try lra. *)
  (*           all: apply pos_INR_S. *)
  (*         + intros n1 n2 m. rewrite /h. do 2 case_match; try done. *)
  (*           intros. *)
  (*           pose proof epsilon_correct _ e0. *)
  (*           pose proof epsilon_correct _ e1. simpl in *. simplify_eq. *)
  (*           rewrite H7 H8. by repeat f_equal. *)
  (*         + apply ex_seriesC_finite. *)
  (*       - eset (diff:=elements (((list_to_set (enum (fin(S M)))):gset _ )∖ ((list_to_set(g<$>enum (fin(S N)))):gset _))). *)
  (*         erewrite (SeriesC_ext _ *)
  (*                     (λ x : fin (S M), (if bool_decide (x ∈ g<$> enum (fin(S N))) then / S M * ε_now1 else 0%R) + *)
  (*                                        if bool_decide (x ∈ diff ) then / S M * ε_now2 else 0%R *)
  (*                  ))%R; last first. *)
  (*         { (** annoying lemma again *) *)
  (*           intros n. rewrite /diff. *)
  (*           case_bool_decide as H1'. *)
  (*           - destruct H1' as [? H1']. rewrite bool_decide_eq_true_2; last first. *)
  (*             + subst. apply elem_of_list_fmap_1. apply elem_of_enum. *)
  (*             + subst. rewrite bool_decide_eq_false_2; first lra. *)
  (*               rewrite elem_of_elements. *)
  (*               rewrite not_elem_of_difference; right. *)
  (*               rewrite elem_of_list_to_set. apply elem_of_list_fmap_1; apply elem_of_enum. *)
  (*           - rewrite bool_decide_eq_false_2; last first. *)
  (*             { rewrite elem_of_list_fmap. intros [?[??]]. *)
  (*               subst. apply H1'. naive_solver. } *)
  (*             rewrite bool_decide_eq_true_2; first lra. *)
  (*             rewrite elem_of_elements. rewrite elem_of_difference. *)
  (*             split; rewrite elem_of_list_to_set; first apply elem_of_enum. *)
  (*             rewrite elem_of_list_fmap. intros [?[??]]. *)
  (*             subst. apply H1'. naive_solver. *)
  (*         } *)
  (*       rewrite SeriesC_plus; try apply ex_seriesC_finite. *)
  (*       rewrite !SeriesC_list_2; last first. *)
  (*       { apply NoDup_fmap_2; [done|apply NoDup_enum]. } *)
  (*       { rewrite /diff. eapply NoDup_elements. } *)
  (*       rewrite fmap_length. rewrite fin.length_enum_fin. *)
  (*       rewrite /diff. *)
  (*       replace (length _) with (S M - S N)%nat; last first. *)
  (*       { erewrite <-size_list_to_set; last apply NoDup_elements. *)
  (*         erewrite list_to_set_elements. *)
  (*         rewrite size_difference. *)
  (*         - rewrite !size_list_to_set; [|apply NoDup_fmap; [auto|apply NoDup_enum]|apply NoDup_enum]; auto. *)
  (*           rewrite fmap_length. *)
  (*           rewrite !fin.length_enum_fin. done. *)
  (*         - intros ??. apply elem_of_list_to_set. apply elem_of_enum. *)
  (*       } *)
  (*       rewrite /ε_now1 /ε_now2. simpl. rewrite -/(INR (S N)) -/(INR (S M)). rewrite !S_INR. *)
  (*       rewrite !Rmult_assoc. *)
  (*       rewrite minus_INR; last lia. *)
  (*       cut ((N+1)/ (M + 1) * ε_now - (N+1)/(M+1) *ε+ *)
  (*              (M-N)/ (M + 1) * ε_now + ((N + 1)/(M+1) * ((M-N)/ (M - N))) * ε <= ε_now)%R; first lra. *)
  (*       rewrite Rdiv_diag; last first. *)
  (*       { assert (N < M)%R; real_solver. } *)
  (*       cut ((N + 1) / (M + 1) * ε_now+ (M - N) / (M + 1) * ε_now <= ε_now)%R; first lra. *)
  (*       cut ((M + 1) / (M + 1) * ε_now <= ε_now)%R; first lra. *)
  (*       rewrite Rdiv_diag; first lra. *)
  (*       pose proof pos_INR M. lra. } *)
  (*     Unshelve. all : eapply gset_fin_set. } *)

  (*   iIntros (?? [m H']). *)
  (*   case_bool_decide in H' as H1'. *)
  (*   - destruct H' as (n&?&?&?). *)
  (*     destruct H1' as [n' <-]. *)
  (*     assert (n' = n) as -> by (by apply (inj _)). *)
  (*     simplify_eq. *)
  (*     iApply spec_coupl_ret. *)
  (*     iMod (ghost_map_update ((N; fs ++ [n]) : tape) with "Ht1 Hα") as "[$ Hα]". *)
  (*     iMod (ghost_map_update ((M; fsₛ ++ [g n]) : tape) with "Ht2 Hαₛ") as "[$ Hαₛ]". *)
  (*     iModIntro. iMod "Hclose'" as "_". *)
  (*     iSpecialize ("Hwp" $! (f n)). *)
  (*     rewrite bool_decide_eq_true_2. *)
  (*     2: { exists n. *)
  (*          split; auto. *)
  (*          apply fin_to_nat_le. } *)

  (*     iSpecialize ("Hwp" $! _ (n)). iFrame. *)
  (*     iDestruct ("Hwp" with "[$Hα $Hαₛ]") as "Hwp". *)
  (*     { iPureIntro. *)
  (*       split; [rewrite fmap_app /=  // |]. *)
  (*       split; [rewrite fmap_app /= HgEq // |]. *)
  (*       split; [apply fin_to_nat_le | ]. *)
  (*       apply Nat.lt_succ_r, Hdom, fin_to_nat_lt. *)
  (*     } *)
  (*     replace (ε_now) with (ε' + ε_now1)%NNR; last first. *)
  (*     { apply nnreal_ext. simpl. lra. } *)
  (*     iMod (ec_supply_decrease with "[$] [$]") as (????) "H". *)
  (*     iFrame. *)
  (*     rewrite /E2 bool_decide_eq_true_2; [|eauto]. *)
  (*     iApply ec_supply_eq; [|done]. *)
  (*     simplify_eq /=. lra.  *)

  (*   - destruct H' as [??]. simplify_eq. *)
  (*     replace (E2 _) with (ε_now2); last first. *)
  (*     { rewrite /E2. rewrite bool_decide_eq_false_2 //. *)
  (*       intros [? H2']. apply state_upd_tapes_same in H2'. simplify_eq. naive_solver. } *)
  (*     destruct (Rle_or_lt 1 ε_now2). *)
  (*     { iModIntro. by iApply spec_coupl_ret_err_ge_1. } *)
  (*     iModIntro. *)
  (*     iApply spec_coupl_ret. *)
  (*     iMod (ghost_map_update ((M; fsₛ ++ [m]) : tape) with "Ht2 Hαₛ") as "[? Hαₛ]". *)
  (*     iMod "Hclose'" as "_". *)
  (*     iSpecialize ("Hwp" $! m). *)
  (*     rewrite bool_decide_eq_false_2 //. *)
  (*     2: { *)
  (*       intros [n [Hn1 Hn2]]. *)
  (*       apply H1'. *)
  (*       assert (n < S N)%nat as Hn3 by lia. *)
  (*       exists (nat_to_fin Hn3). *)
  (*       apply fin_to_nat_inj. *)
  (*       rewrite HgEq -Hn2. *)
  (*       rewrite fin_to_nat_to_fin //. *)
  (*     } *)
  (*     rewrite !S_INR /=. *)
  (*     iFrame. *)
  (*     iMod (ec_supply_increase with "[$Hε2]") as "[$ Hε']". *)
  (*     { by eapply Rle_lt_trans. } *)
  (*     iCombine "Hε Hε'" as "Hε". *)
  (*     iApply ("Hwp" $! _ with "[$Hα $Hαₛ $Hε]"). *)
  (*     iPureIntro. *)
  (*     split. *)
  (*     1:{ *)
  (*       simpl. rewrite -/(INR (S N)). rewrite S_INR. *)
  (*       replace (INR M + 1 - (INR N + 1))%R with (INR M - INR N)%R by lra. *)
  (*       rewrite -{1}(Rmult_1_l ε). *)
  (*       rewrite Rmult_assoc (Rmult_comm ε). *)
  (*       rewrite -Rmult_plus_distr_r. apply Rmult_eq_compat_r. *)
  (*       rewrite Rdiv_def. *)
  (*       replace (1)%R with ((INR M - INR N)*/(INR M - INR N))%R at 1; last first.       *)
  (*       { apply Rinv_r. apply lt_INR in Hineq. lra. } *)
  (*       rewrite minus_INR; [|real_solver]. *)
  (*       rewrite -Rmult_plus_distr_r. lra. } *)
  (*     split; auto. *)
  (*     split; [ | apply fin_to_nat_le ]. *)
  (*     rewrite fmap_app //. *)
  (*     Unshelve. *)
  (*     + apply Nat.lt_succ_r, Hdom, fin_to_nat_lt. *)
  (*     + apply fin_to_nat_le. *)
  (* Qed. *)

  (* Lemma wp_couple_fragmented_rand_rand_leq_rev' {M N : nat} ns nsₛ α αₛ e E Φ (ε : R) : *)
  (*   0 <= ε → *)
  (*   (N < M)%nat → *)
  (*   ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗ ↯ ε ∗ *)
  (*   (∀ (m : nat), *)
  (*      ⌜ m ≤ M ⌝ -∗ *)
  (*      if bool_decide (m < S N)%nat *)
  (*        then *)
  (*          α ↪N (N; ns ++ [m]) ∗ αₛ ↪ₛN (M; nsₛ ++ [m]) ∗ ⌜ m ≤ N ⌝ -∗ *)
  (*          WP e @ E {{ Φ }} *)
  (*        else *)
  (*          ∀ (ε' : R), *)
  (*            ⌜ε' = (S M / (S M - S N) * ε)%R⌝ ∗ *)
  (*            α ↪N (N; ns) ∗ αₛ ↪ₛN (M; nsₛ++[m]) ∗ ↯ ε' ∗ ⌜ m ≤ M ⌝ -∗ *)
  (*            WP e @ E {{ Φ }} *)
  (*     ) *)
  (*   ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (Hε Hineq) "(>Hα & >Hαₛ & Hε & Hwp)". *)
  (*   iApply (wp_couple_fragmented_rand_rand_inj_rev' (λ x, x) with "[$Hα $Hαₛ $Hε Hwp]"); [done|done| .. ]. *)
  (*   { intros; lia. } *)
  (*   iIntros (n) "%Hn". *)
  (*   case_bool_decide as H1. *)
  (*   - destruct H1 as [n' [Hn' <-]]. *)
  (*     iIntros (?) "(?&?&%&%)". *)
  (*     iSpecialize ("Hwp" $! n with "[//]"). *)
  (*     rewrite bool_decide_eq_true_2; last by lia. *)
  (*     iSpecialize ("Hwp" with "[-]"); iFrame. *)
  (*     done. *)
  (*   - iSpecialize ("Hwp" $! n with "[//]"). *)
  (*     rewrite bool_decide_eq_false_2; [iFrame |]. *)
  (*     intro. apply H1. *)
  (*     exists n. lia. *)
  (* Qed. *)

  (* (** wp_couple_exp *) *)
  (* Lemma wp_couple_exp (M N p:nat)  *)
  (*   (f : list nat → nat) *)
  (*   (Hdom: forall (l : list nat), Forall (λ x, (x < S N)%nat) l -> (f l < S M)%nat) *)
  (*   (Hinj: forall (l1 l2:list nat), *)
  (*       Forall (λ x, (x < S N)%nat) l1 -> *)
  (*       Forall (λ x, (x < S N)%nat) l2 -> *)
  (*       length l1 = p -> length l2 = p -> f l1 = f l2 -> l1 = l2) ns nsₛ α αₛ e E Φ: *)
  (*   (S N ^ p = S M)%nat-> *)
  (*   ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗ *)
  (*   (∀ (l : list nat) (m: nat), *)
  (*      ⌜Forall (λ x, (x < S N)%nat) l⌝ -∗ *)
  (*      ⌜(m < S M)%nat ⌝ -∗ *)
  (*      ⌜length l = p /\ f l = m⌝ -∗  *)
  (*      α ↪N (N; ns ++ l) -∗ αₛ ↪ₛN (M; nsₛ ++ [m]) -∗ *)
  (*      WP e @ E {{ Φ }} *)
  (*   ) *)
  (*   ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (Heq) "(>Hα & >Hαₛ & Hwp)". *)
  (*   iDestruct "Hα" as (fs) "(<-&Hα)". *)
  (*   iDestruct "Hαₛ" as (fsₛ) "(<-&Hαₛ)". *)
  (*   destruct (restr_list_inj_fixed_length (S N) (S M) p f) as [g [Hg1 Hg2]]; auto. *)
  (*   iApply wp_lift_step_spec_couple. *)
  (*   iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)". *)
  (*   iDestruct "Hauth2" as "(HK&Hh2&Ht2)/=". *)
  (*   iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?. *)
  (*   iDestruct (ghost_map_lookup with "Ht1 Hα") as %?. *)
  (*   simplify_map_eq. *)
  (*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'". *)
  (*   replace (ε_now) with (0+ε_now)%NNR; last (apply nnreal_ext; simpl; lra). *)
  (*   iApply spec_coupl_erasables; [done|..]. *)
  (*   - apply ARcoupl_exact. apply Rcoupl_state_state_exp. *)
  (*     all: exact. *)
  (*   - eapply iterM_state_step_erasable; done. *)
  (*   - by eapply state_step_erasable. *)
  (*   - iIntros (σ2 σ2') "%K". *)
  (*     destruct K as (xs' & z & Hlen & -> & -> & <-). *)
  (*     iMod (ghost_map_update ((N; fs ++ xs') : tape) with "Ht1 Hα") as "[Ht1 Hα]". *)
  (*     iMod (ghost_map_update ((M; fsₛ ++ [g xs']) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]". *)
  (*     iModIntro. *)
  (*     iApply spec_coupl_ret. *)
  (*     iMod "Hclose'". *)
  (*     iSpecialize ("Hwp" $! (fin_to_nat <$> xs') (g xs') with "[][][]"). *)
  (*     + iPureIntro. *)
  (*       apply fin_forall_leq. *)
  (*     + iPureIntro. apply fin_to_nat_lt. *)
  (*     + iPureIntro; split; auto. *)
  (*       rewrite fmap_length //. *)
  (*     + iFrame. *)
  (*       replace (0+_)%NNR with (ε_now). *)
  (*       2:{ apply nnreal_ext. simpl; lra. } *)
  (*       iFrame. *)
  (*       iApply ("Hwp" with "[Hα][-]"). *)
  (*       * rewrite -fmap_app. iFrame. done. *)
  (*       * iFrame. rewrite fmap_app. done. *)
  (* Qed. *)


  (* Lemma wp_couple_exp_decoder (M N p : nat ) ns nsₛ α αₛ e E Φ: *)
  (*   (S N ^ p = S M)%nat -> *)
  (*   ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗ *)
  (*   (∀ (l : list nat) (m: nat), *)
  (*      ⌜Forall (λ x, (x < S N)%nat) l⌝ -∗ *)
  (*      ⌜(m < S M)%nat ⌝ -∗ *)
  (*      ⌜length l = p⌝ -∗  *)
  (*      α ↪N (N; ns ++ l) -∗ αₛ ↪ₛN (M; nsₛ ++ [@decoder_nat N l]) -∗ *)
  (*      WP e @ E {{ Φ }} *)
  (*   ) *)
  (*   ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (Heq) "(>Hα & >Hαₛ & Hwp)". *)
  (*   set (f := (λ l : list nat, if bool_decide (length l = p) then @decoder_nat N l else 0%nat )). *)
  (*   iApply (wp_couple_exp M N p f); auto. *)
  (*   { *)
  (*     rewrite -Heq /f. *)
  (*     intros l Hl. *)
  (*     case_bool_decide; simplify_eq. *)
  (*     - by apply fin.decoder_aux_ineq. *)
  (*     - lia. *)
  (*   } *)
  (*   { *)
  (*     rewrite /f. *)
  (*     intros ?????<-. *)
  (*     case_bool_decide; [|done]. *)
  (*     rewrite bool_decide_eq_true_2; auto. *)
  (*     intro. *)
  (*     by apply (@fin.decoder_aux_inj N). *)
  (*   } *)
  (*   iFrame. *)
  (*   rewrite /f. *)
  (*   iIntros (??) "% % (%&%) Hα Hαs". *)
  (*   case_bool_decide; [|done]. *)
  (*   iApply ("Hwp" with "[//] [//] [//] Hα [Hαs]"). *)
  (*   simplify_eq. *)
  (*   iFrame. *)
  (* Qed. *)


  (* Lemma wp_couple_exp_decoder_lr (M N p : nat ) ns nsₛ α αₛ e E Φ: *)
  (*   (S N ^ p = S M)%nat -> *)
  (*   ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗ *)
  (*   (∀ (l : list nat) (m: nat), *)
  (*      ⌜Forall (λ x, (x < S N)%nat) l⌝ -∗ *)
  (*      ⌜(m < S M)%nat ⌝ -∗ *)
  (*      ⌜length l = p⌝ -∗  *)
  (*      α ↪N (N; ns ++ l) -∗ αₛ ↪ₛN (M; nsₛ ++ [@decoder_nat_lr N l]) -∗ *)
  (*      WP e @ E {{ Φ }} *)
  (*   ) *)
  (*   ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (Heq) "(>Hα & >Hαₛ & Hwp)". *)
  (*   set (f := (λ l : list nat, if bool_decide (length l = p) then @decoder_nat_lr N l else 0%nat )). *)
  (*   iApply (wp_couple_exp M N p f); auto. *)
  (*   { *)
  (*     rewrite -Heq /f. *)
  (*     intros l Hl. *)
  (*     case_bool_decide; simplify_eq. *)
  (*     - by apply fin.decoder_lr_aux_ineq. *)
  (*     - lia. *)
  (*   } *)
  (*   { *)
  (*     rewrite /f. *)
  (*     intros ?????<-. *)
  (*     case_bool_decide; [|done]. *)
  (*     rewrite bool_decide_eq_true_2; auto. *)
  (*     intro. *)
  (*     by apply (@fin.decoder_lr_aux_inj N). *)
  (*   } *)
  (*   iFrame. *)
  (*   rewrite /f. *)
  (*   iIntros (??) "% % (%&%) Hα Hαs". *)
  (*   case_bool_decide; [|done]. *)
  (*   iApply ("Hwp" with "[//] [//] [//] Hα [Hαs]"). *)
  (*   simplify_eq. *)
  (*   iFrame. *)
  (* Qed. *)


  (* Lemma wp_couple_exp_rev (M N p:nat) *)
  (*   (f:(list nat) -> nat) *)
  (*   (Hdom: forall (l : list nat), Forall (λ x, (x < S N)%nat) l -> (f l < S M)%nat) *)
  (*   (Hinj: forall (l1 l2:list nat), *)
  (*       Forall (λ x, (x < S N)%nat) l1 -> *)
  (*       Forall (λ x, (x < S N)%nat) l2 -> *)
  (*       length l1 = p -> length l2 = p -> f l1 = f l2 -> l1 = l2) ns nsₛ α αₛ e E Φ: *)
  (*   (S N ^ p = S M)%nat-> *)
  (*   ▷ α ↪N (M; ns) ∗ ▷ αₛ ↪ₛN (N; nsₛ) ∗ *)
  (*   (∀ (l : list nat) (m: nat), *)
  (*      ⌜Forall (λ x, (x < S N)%nat) l⌝ -∗ *)
  (*      ⌜(m < S M)%nat ⌝ -∗ *)
  (*      ⌜length l = p /\ f l = m⌝ -∗  *)
  (*      α ↪N (M; ns ++ [m]) -∗ αₛ ↪ₛN (N; nsₛ ++ l) -∗ *)
  (*      WP e @ E {{ Φ }} *)
  (*   ) *)
  (*   ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (Heq) "(>Hα & >Hαₛ & Hwp)". *)
  (*   iApply wp_lift_step_spec_couple. *)
  (*   iDestruct "Hα" as (fs) "(<-&Hα)". *)
  (*   iDestruct "Hαₛ" as (fsₛ) "(<-&Hαₛ)". *)
  (*   destruct (restr_list_inj_fixed_length (S N) (S M) p f) as [g [Hg1 Hg2]]; auto. *)
  (*   iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)". *)
  (*   iDestruct "Hauth2" as "(HK&Hh2&Ht2)/=". *)
  (*   iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?. *)
  (*   iDestruct (ghost_map_lookup with "Ht1 Hα") as %?. *)
  (*   simplify_map_eq. *)
  (*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'". *)
  (*   replace (ε_now) with (0+ε_now)%NNR; last (apply nnreal_ext; simpl; lra). *)
  (*   iApply spec_coupl_erasables; [done|..]. *)
  (*   - apply ARcoupl_exact. apply Rcoupl_swap. apply Rcoupl_state_state_exp. *)
  (*     all: exact. *)
  (*   - by eapply state_step_erasable. *)
  (*   - eapply iterM_state_step_erasable; done. *)
  (*   - iIntros (σ2 σ2') "%K". *)
  (*     destruct K as (xs' & z & Hlen & -> & -> & <-). *)
  (*     iMod (ghost_map_update ((M; fs ++ [g xs']) : tape) with "Ht1 Hα") as "[Ht1 Hα]". *)
  (*     iMod (ghost_map_update ((N; fsₛ ++ xs') : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]". *)
  (*     iModIntro. *)
  (*     iApply spec_coupl_ret. *)
  (*     iSpecialize ("Hwp" $! (fin_to_nat <$> xs') (g xs') with "[][][]"). *)
  (*     + iPureIntro. *)
  (*       apply fin_forall_leq. *)
  (*     + iPureIntro. apply fin_to_nat_lt. *)
  (*     + iPureIntro; split; auto. *)
  (*       rewrite fmap_length //. *)
  (*     + iFrame. *)
  (*       replace (0+_)%NNR with (ε_now). *)
  (*       2:{ apply nnreal_ext. simpl; lra. } *)
  (*       iFrame. *)
  (*       iMod "Hclose'". *)
  (*       iApply ("Hwp" with "[Hα][-]"). *)
  (*       * iFrame. rewrite fmap_app //. *)
  (*       * iFrame. rewrite -fmap_app //. *)
  (* Qed. *)



  (* Lemma wp_couple_exp_decoder_rev (M N p:nat) ns nsₛ α αₛ e E Φ: *)
  (*   (S N ^ p = S M)%nat-> *)
  (*   ▷ α ↪N (M; ns) ∗ ▷ αₛ ↪ₛN (N; nsₛ) ∗ *)
  (*   (∀ (l : list nat) (m: nat), *)
  (*      ⌜Forall (λ x, (x < S N)%nat) l⌝ -∗ *)
  (*      ⌜(m < S M)%nat ⌝ -∗ *)
  (*      ⌜length l = p⌝ -∗  *)
  (*      α ↪N (M; ns ++ [@decoder_nat N l]) -∗ αₛ ↪ₛN (N; nsₛ ++ l) -∗ *)
  (*      WP e @ E {{ Φ }} *)
  (*   ) *)
  (*   ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (Heq) "(>Hα & >Hαₛ & Hwp)". *)
  (*   set (f := (λ l : list nat, if bool_decide (length l = p) then @decoder_nat N l else 0%nat )). *)
  (*   iApply (wp_couple_exp_rev M N p f); auto. *)
  (*   { *)
  (*     rewrite -Heq /f. *)
  (*     intros l Hl. *)
  (*     case_bool_decide; simplify_eq. *)
  (*     - by apply fin.decoder_aux_ineq. *)
  (*     - lia. *)
  (*   } *)
  (*   { *)
  (*     rewrite /f. *)
  (*     intros ?????<-. *)
  (*     case_bool_decide; [|done]. *)
  (*     rewrite bool_decide_eq_true_2; auto. *)
  (*     intro. *)
  (*     by apply (@fin.decoder_aux_inj N). *)
  (*   } *)
  (*   iFrame. *)
  (*   rewrite /f. *)
  (*   iIntros (??) "% % (%&%) Hα Hαs". *)
  (*   case_bool_decide; [|done]. *)
  (*   simplify_eq. *)
  (*   iApply ("Hwp" with "[//] [//] [//] Hα [Hαs]"). *)
  (*   iFrame. *)
  (* Qed. *)


  (* Lemma wp_couple_exp_decoder_lr_rev (M N p:nat) ns nsₛ α αₛ e E Φ: *)
  (*   (S N ^ p = S M)%nat-> *)
  (*   ▷ α ↪N (M; ns) ∗ ▷ αₛ ↪ₛN (N; nsₛ) ∗ *)
  (*   (∀ (l : list nat) (m: nat), *)
  (*      ⌜Forall (λ x, (x < S N)%nat) l⌝ -∗ *)
  (*      ⌜(m < S M)%nat ⌝ -∗ *)
  (*      ⌜length l = p⌝ -∗  *)
  (*      α ↪N (M; ns ++ [@decoder_nat_lr N l]) -∗ αₛ ↪ₛN (N; nsₛ ++ l) -∗ *)
  (*      WP e @ E {{ Φ }} *)
  (*   ) *)
  (*   ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (Heq) "(>Hα & >Hαₛ & Hwp)". *)
  (*   set (f := (λ l : list nat, if bool_decide (length l = p) then @decoder_nat_lr N l else 0%nat )). *)
  (*   iApply (wp_couple_exp_rev M N p f); auto. *)
  (*   { *)
  (*     rewrite -Heq /f. *)
  (*     intros l Hl. *)
  (*     case_bool_decide; simplify_eq. *)
  (*     - by apply fin.decoder_lr_aux_ineq. *)
  (*     - lia. *)
  (*   } *)
  (*   { *)
  (*     rewrite /f. *)
  (*     intros ?????<-. *)
  (*     case_bool_decide; [|done]. *)
  (*     rewrite bool_decide_eq_true_2; auto. *)
  (*     intro. *)
  (*     by apply (@fin.decoder_lr_aux_inj N). *)
  (*   } *)
  (*   iFrame. *)
  (*   rewrite /f. *)
  (*   iIntros (??) "% % (%&%) Hα Hαs". *)
  (*   case_bool_decide; [|done]. *)
  (*   simplify_eq. *)
  (*   iApply ("Hwp" with "[//] [//] [//] Hα [Hαs]"). *)
  (*   iFrame. *)
  (* Qed. *)

  (** * Exact couplings  *)
  Lemma pupd_couple_tape_rand N f `{Bij nat nat f} K E α z ns j:
    TCEq N (Z.to_nat z) →
    (∀ n, n < S N -> f n < S N)%nat →
    ▷ α ↪N (N; ns) -∗ j ⤇ fill K (rand #z) -∗
    pupd E E (∃ (n:nat), α ↪N (N; ns ++ [n]) ∗ j ⤇ fill K #(f n) ∗ ⌜ n ≤ N ⌝).
  Proof.
    iIntros (-> Hdom) ">Hα Hj".
    iDestruct "Hα" as (fs) "(<-&Hα)".
    destruct (restr_bij_fin (_) f Hdom) as [ff [Hbij Hff]].
    rewrite pupd_unseal/pupd_def.
    iIntros (σ ρ1 ε1) "([? Ht]&Hs&?)".
    iDestruct (ghost_map_lookup with "Ht [$]") as %?.
    iDestruct (spec_auth_prog_agree with "Hs Hj") as "%Hsome".
    iApply spec_coupl_rec.
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose".
    destruct ρ1 as [es σ'].
    assert (j < length es)%nat.
    { by eapply lookup_lt_Some. }
    iExists _, (state_step σ α), (full_info_one_step_stutter_osch j), 0%NNR, (λ _, ε1), ε1.
    repeat iSplit.
    - iPureIntro. by eapply state_step_sch_erasable.
    - done.
    - iPureIntro. rewrite Rplus_0_l.
      rewrite Expval_const; last done.
      trans (ε1 * 1)%R; last (simpl; lra).
      by apply Rmult_le_compat.
    - rewrite full_info_one_step_stutter_osch_lim_exec/state_step.
      rewrite bool_decide_eq_true_2; last first.
      { rewrite elem_of_dom. naive_solver. }
      setoid_rewrite lookup_total_correct; last done.
      simpl.
      replace 0%R with (0+0)%R by lra.
      rewrite /dmap.
      iPureIntro.
      rewrite /step'.
      rewrite Hsome//.
      rewrite fill_not_val; last done.
      rewrite fill_dmap//=.
      rewrite head_prim_step_eq///=.
      rewrite -dbind_assoc'.
      rewrite dmap_comp.
      rewrite /dmap.
      rewrite -!dbind_assoc'.
      eapply ARcoupl_dbind; [lra|lra| |]; last first.
      { apply ARcoupl_exact. 
        apply (Rcoupl_dunif); apply Hbij.
      }
      intros ??->.
      rewrite !dbind_assoc'.
      rewrite !dret_id_left'.
      simpl.
      rewrite app_nil_r.
      rewrite insert_length.
      instantiate (1:= λ x y, exists (a:fin(S (Z.to_nat z))), x =(state_upd_tapes <[α:=(Z.to_nat z; fs ++ [a])]> σ)/\y= ([(cfg_to_cfg' (es, σ'), j); (cfg_to_cfg' (<[j:=fill K #(ff a)]> es, σ'), length es)],
                                                                                                                     (<[j:=fill K #(ff a)]> es, σ'))).
      apply ARcoupl_dret; naive_solver.
    - iPureIntro. intros ????? (a&?&H') [a' ?]. destruct!/=.
      assert (a=a') as ->; last naive_solver.
      eapply f_equal in H'. erewrite !list_lookup_insert in H'; try done.
      by simplify_eq. 
    - simpl.
      iIntros (??? (x&?&?)).
      simplify_eq.
      iApply spec_coupl_ret.
      iMod (ghost_map_update with "Ht [$]") as "(?&?)".
      iMod (spec_update_prog with "[$][$]") as "[??]".
      iModIntro.
      iMod "Hclose".
      iModIntro.
      rewrite Hff.
      iFrame. 
      rewrite fmap_app. simpl.
      iPureIntro; split; first done.
      pose proof fin_to_nat_lt x. lia.
  Qed.

  
  Lemma pupd_couple_two_tapes_rand N M f K E α α' z z' x ns ms j:
    TCEq N (Z.to_nat z) →
    TCEq M (Z.to_nat z')->
    x= Z.of_nat ((S N)*(S M)-1) ->
    (∀ n m, n < S N -> m< S M -> f n m < (S N)*(S M))%nat →
    (∀ n n' m m', n < S N -> n' < S N -> m < S M -> m' < S M -> f n m = f n' m' -> n=n' /\ m=m')%nat ->
    (forall x, x<(S N)*(S M) -> exists n m, n< S N /\ m < S M /\ f n m = x)%nat ->
    ▷ α ↪N (N; ns) -∗ ▷α'↪N (M;ms)-∗ j ⤇ fill K (rand #x) -∗
    pupd E E (∃ (n m:nat), α ↪N (N; ns ++ [n]) ∗ α' ↪N (M; ms ++ [m]) ∗ j ⤇ fill K #(f n m) ∗ ⌜ (n ≤ N)%nat ⌝ ∗ ⌜(m<=M)%nat⌝).
  Proof.
    iIntros (->->-> Hcond1 Hcond2 Hcond3) ">(%fs&%&Hα) >(%fs'&%&Hα') Hj".
    rewrite pupd_unseal/pupd_def.
    iIntros (σ1 ρ1 ε) "[[Hh Ht] [Hs Hε]]".
    iDestruct (spec_auth_prog_agree with "Hs Hj") as "%Hsome".
    iDestruct (ghost_map_lookup with "Ht [$Hα]") as "%Hlookup".
    iDestruct (ghost_map_lookup with "Ht [$Hα']") as "%Hlookup'".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    destruct ρ1 as [l s].
    assert (j < length l)%nat.
    { by eapply lookup_lt_Some. }
    simpl.
    rewrite Nat.sub_0_r.
    iApply spec_coupl_rec.
    iDestruct (ghost_map_elem_ne with "Hα Hα'") as "%".
    iExists _, (dbind (λ σ1', state_step σ1' α') (state_step σ1 α)), (full_info_one_step_stutter_osch j), 0%NNR, (λ _, ε), ε.
    repeat iSplit.
    - iPureIntro. apply sch_erasable_dbind; first eapply state_step_sch_erasable; first done.
      intros σ'. rewrite {1}/state_step. rewrite bool_decide_eq_true_2; last by rewrite elem_of_dom.
      setoid_rewrite lookup_total_correct at 1; last done.
      simpl.
      intros Hpos.
      apply dmap_pos in Hpos. destruct Hpos as (?&->&Hpos).
      eapply state_step_sch_erasable.
      simpl. by rewrite lookup_insert_ne.
    - done. 
    - rewrite Expval_const; last done.
      iPureIntro.
      rewrite Rplus_0_l.
      trans (ε*1); last (simpl; lra).
      by apply Rmult_le_compat.
    - iPureIntro.
      rewrite full_info_one_step_stutter_osch_lim_exec.
      rewrite /state_step.
      rewrite bool_decide_eq_true_2; last by rewrite elem_of_dom.
      setoid_rewrite lookup_total_correct at 2; last done.
      simpl.
      rewrite Hsome.
      rewrite fill_not_val; last done.
      rewrite fill_dmap//=.
      rewrite head_prim_step_eq//= !dmap_comp.
      rewrite !Nat2Z.id.

      (** Here we define the f' function that is specialized to fin *)
      rewrite Nat.sub_0_r.
      assert (∀ n m : nat,
             (n < S (Z.to_nat z))%nat
             → (m < S (Z.to_nat z'))%nat → (f n m < S(Z.to_nat z' + Z.to_nat z * S (Z.to_nat z')))%nat) as Hcond1'.
      { intros. naive_solver. }
      set (f' := λ '((n,m): (fin (S (Z.to_nat z)) * fin (S (Z.to_nat z')))),
             nat_to_fin (Hcond1' _ _ (fin_to_nat_lt n) (fin_to_nat_lt m))
          ).
      assert (Bij f') as Hbij.
      { split.
        - intros [x y][x' y'].
          rewrite /f'.
          intros Heq.
          apply (f_equal fin_to_nat) in Heq.
          rewrite !fin_to_nat_to_fin in Heq.
          apply Hcond2 in Heq; destruct!/=; first naive_solver.
          all: apply fin_to_nat_lt.
        - intros x.
          pose proof fin_to_nat_lt x as H3.
          apply Hcond3 in H3 as (n'&m'&Hn'&Hm'&Hrewrite).
          exists (nat_to_fin Hn',nat_to_fin Hm').
          rewrite /f'.
          apply fin_to_nat_inj.
          by rewrite !fin_to_nat_to_fin -Hrewrite.
      }
      rewrite (dunifP_decompose _ _ _ f' ); last lia.
      rewrite /dmap -!dbind_assoc'.
      replace 0%R with (0+0) by lra.
      eapply ARcoupl_dbind; [done|done| |apply ARcoupl_eq].
      intros ? n ->.
      rewrite dret_id_left.
      rewrite bool_decide_eq_true_2; last first.
      { rewrite elem_of_dom. simpl. rewrite lookup_insert_ne; naive_solver. }
      setoid_rewrite lookup_total_correct; last first.
      { simpl. by rewrite lookup_insert_ne. }
      simpl.
      rewrite -dbind_assoc'.
      replace 0%R with (0+0) by lra.
      eapply ARcoupl_dbind; [done|done| |apply ARcoupl_eq].
      intros ? m ->.
      rewrite dret_id_left.
      rewrite app_nil_r fin_to_nat_to_fin.
      rewrite insert_length.
      instantiate (1:= λ x y, ∃ (n:fin(S (Z.to_nat z))) (m:fin(S (Z.to_nat z'))), x = {|
         heap := heap σ1;
         tapes := <[α':=(Z.to_nat z'; fs' ++ [m])]> (<[α:=(Z.to_nat z; fs ++ [n])]> (tapes σ1))
       |}/\ y=([(cfg_to_cfg' (l, s), j); (cfg_to_cfg' (<[j:=fill K #(f n m)]> l, s), length l)],
        (<[j:=fill K #(f n m)]> l, s))).
      apply ARcoupl_dret; naive_solver.
    - iPureIntro. simpl. intros ????? (n&m&K1&K2) (n'&m'&K3&K4). destruct!/=.
      assert (n=n'/\m=m'). 
      { apply (f_equal (λ x, x!!j)) in K2.
        rewrite !list_lookup_insert in K2; try done.
        simplify_eq.
        apply Hcond2 in K2; first naive_solver.
        all: apply fin_to_nat_lt.
      }
      by destruct!/=.
    - simpl.
      iIntros (???) "(%n&%m&%)". destruct!/=.
      iMod (spec_update_prog with "Hs Hj") as "[Hs ?]".
      iMod (ghost_map_update with "Ht Hα") as "[Ht ?]".
      iMod (ghost_map_update with "Ht Hα'") as "[Ht ?]".
      iModIntro. iApply spec_coupl_ret.
      iMod "Hclose".
      iModIntro. iFrame.
      rewrite !fmap_app.
      pose proof fin_to_nat_lt n.
      pose proof fin_to_nat_lt m.
      iPureIntro; repeat split; lia.
  Qed.

  
  (* (** * rand(unit, N) ~ state_step(α', N) coupling *) *)
  (* Lemma wp_couple_rand_tape N f `{Bij nat nat f} z E α ns : *)
  (*   TCEq N (Z.to_nat z) → *)
  (*   (∀ n, n < S N -> f n < S N)%nat → *)
  (*   {{{ ▷ α ↪ₛN (N; ns) }}} *)
  (*     rand #z @ E *)
  (*   {{{ (n : nat), RET #n; α ↪ₛN (N; ns ++ [f n]) ∗ ⌜ n ≤ N ⌝ }}}. *)
  (* Proof. *)
  (*   iIntros (H0 Hdom ?) ">Hαs Hwp". *)
  (*   iDestruct "Hαs" as (fs) "(<-&Hαs)". *)
  (*   destruct (restr_bij_fin (S N) f Hdom) as [ff [Hbij Hff]]. *)
  (*   iApply wp_lift_step_prog_couple; [done|]. *)
  (*   iIntros (σ1 e1' σ1' ε) "[[Hh1 Ht1] [Hauth2 Herr]]". *)
  (*   iDestruct (spec_auth_lookup_tape with "Hauth2 Hαs") as %?. *)
  (*   iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'". *)
  (*   replace (ε) with (0+ε)%NNR at 2 by (apply nnreal_ext; simpl; lra). *)
  (*   iApply prog_coupl_step_l_erasable; [done|solve_red|..]. *)
  (*   { apply ARcoupl_exact. *)
  (*     eapply (Rcoupl_rand_state _ ff); eauto. *)
  (*     rewrite -H0//. } *)
  (*   { by eapply state_step_erasable. } *)
  (*   iIntros (??? (n & [= -> ->] & ->)). *)
  (*   iMod (spec_auth_update_tape (_; fs ++ [ff _]) with "Hauth2 Hαs") as "[Htapes Hαs]". *)
  (*   do 2 iModIntro. *)
  (*   iMod "Hclose'" as "_". *)
  (*   iFrame. *)
  (*   iApply wp_value. *)
  (*   iApply ("Hwp" $! _ with "[$Hαs]"). *)
  (*   iPureIntro. *)
  (*   rewrite fmap_app -Hff. *)
  (*   split; auto. *)
  (*   apply fin_to_nat_le. *)
  (* Qed. *)

  Lemma wp_couple_rand_rand_lbl N f `{Bij nat nat f} z K E α j :
    TCEq N (Z.to_nat z) →
    (∀ n, n < S N -> f n < S N)%nat →
    {{{ α ↪ₛN (N; []) ∗ j ⤇ fill K (rand(#lbl:α) #z) }}}
      rand #z @ E
      {{{ (n : nat), RET #n; α ↪ₛN (N; []) ∗ j ⤇ fill K #(f n) ∗ ⌜ n ≤ N ⌝ }}}.
  Proof.
    iIntros (-> Hdom Ψ) "[Hα Hr] HΨ".
    destruct (restr_bij_fin (S _) f Hdom) as [ff [Hbij Hff]].
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 [l s] ε) "[Hσ [Hs Hε]]".
    iDestruct (spec_auth_prog_agree with "Hs Hr") as "%Hsome".
    iDestruct (spec_tapeN_to_empty with "[$]") as "Hα".
    iDestruct (spec_auth_lookup_tape with "Hs Hα") as "%Hlookup".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    (* replace ε with (0 + ε)%NNR; last first. *)
    (* { apply nnreal_ext; simpl; lra. } *)
    rewrite /prog_coupl.
    assert (j < length l)%nat.
    { by eapply lookup_lt_Some. }
    iExists _, (full_info_one_step_stutter_osch j), 0%NNR, (λ _, ε), ε.
    solve_red.
    repeat iSplit.
    - done.
    - rewrite Expval_const; last done.
      iPureIntro.
      rewrite Rplus_0_l.
      trans (ε*1); last (simpl; lra).
      by apply Rmult_le_compat.
    - iPureIntro. rewrite full_info_one_step_stutter_osch_lim_exec/=.
      rewrite head_prim_step_eq/=.
      (* apply ARcoupl_map; first done. *)
      rewrite /step'.
      rewrite Hsome.
      case_match eqn:Heqn.
      { apply mk_is_Some in Heqn. apply fill_val in Heqn. simpl in *. by destruct Heqn. }
      rewrite fill_dmap //=.
      rewrite head_prim_step_eq///=.
      rewrite Hlookup bool_decide_eq_true_2; last done.
      rewrite !dmap_comp.
      apply ARcoupl_map; first done.
      simpl.
      apply ARcoupl_exact.
      eapply Rcoupl_mono.
      + apply (Rcoupl_dunif); apply Hbij.
      + simpl.
        intros ? ? ->.
        instantiate (1 := (λ x y, ∃ (a:fin(S (Z.to_nat z))),
                              x= (Val (#a), σ1, []) /\
                              y=([(cfg_to_cfg' (l, s), j);
                                  (cfg_to_cfg' (<[j:=fill K #(ff a)]> l ++ [], s), length (<[j:=fill K #(ff a)]> l ++ []))],
                                   (<[j:=fill K #(ff a)]> l ++ [], s))
                    )).
        naive_solver.
    - simpl.
      iPureIntro.
      intros?????(?&?&H')(?&?&?).
      destruct!/=.
      rewrite !app_nil_r in H'.
      eapply f_equal in H'.
      erewrite !list_lookup_insert in H'; try done.
      by simplify_eq.
    - simpl.
      iIntros (?????[a ?]).
      destruct!/=.
      iMod (spec_update_prog with "[$][$]") as "[HK Hs]".
      iModIntro. iNext.
      iMod "Hclose".
      rewrite app_nil_r.
      iFrame.
      iModIntro.
      wp_pures.
      iApply "HΨ".
      rewrite Hff. iFrame.
      iModIntro. iPureIntro.
      pose proof fin_to_nat_lt a.
      rewrite fmap_nil; split; [done|lia]. 
  Qed.

  Lemma wp_couple_rand_lbl_rand_lbl N f `{Bij nat nat f} z K E α α' j :
    TCEq N (Z.to_nat z) →
    (∀ n, n < S N -> f n < S N)%nat →
    {{{ ▷ α ↪N (N; []) ∗ ▷ α' ↪ₛN (N; []) ∗ j ⤇ fill K (rand(#lbl:α') #z) }}}
      rand(#lbl:α) #z @ E
    {{{ (n : nat), RET #n; α ↪N (N; []) ∗ α' ↪ₛN (N; []) ∗ j ⤇ fill K #(f n) ∗ ⌜ n ≤ N ⌝ }}}.
  Proof.
    iIntros (-> Hdom Ψ) "(>Htape & >Htape' & Hr) HΨ".
    iApply wp_lift_step_prog_couple; [done|].
    destruct (restr_bij_fin _ f Hdom) as [g [HBij Hfg]]; auto.
    iIntros ([σh σt] ρ1 ε) "[[Hh Ht] [Hs Hε]]".
    iDestruct (spec_auth_prog_agree with "Hs Hr") as "%Hsome".
    iDestruct (spec_auth_lookup_tape with "[$] [Htape']") as "%Hsome'".
    { iDestruct (spec_tapeN_to_empty with "[$]") as "$". }
    simpl.
    iDestruct (ghost_map_lookup with "[$Ht] [Htape]") as "%Hsome''".
    { iDestruct (tapeN_to_empty with "[$]") as "$". }
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    (* replace ε with (0 + ε)%NNR; last first. *)
    (* { apply nnreal_ext; simpl; lra. } *)
    rewrite /prog_coupl.
    destruct ρ1 as [l s].
    assert (j < length l)%nat.
    { by eapply lookup_lt_Some. }
    
    iExists _, (full_info_one_step_stutter_osch j), 0%NNR, (λ _, ε), ε.
    iSplit.
    { iPureIntro. apply head_prim_reducible. rewrite /head_reducible. simpl.
      rewrite Hsome''. rewrite bool_decide_eq_true_2; last done.
      eexists _. rewrite dmap_pos.
      eexists _; split; first done.
      apply (dunifP_pos _ 0%fin). }
    repeat iSplit.
    - done.
    - rewrite Expval_const; last done.
      iPureIntro.
      rewrite Rplus_0_l.
      trans (ε*1); last (simpl; lra).
      by apply Rmult_le_compat.
    - iPureIntro. rewrite full_info_one_step_stutter_osch_lim_exec/=.
      rewrite head_prim_step_eq/=.
      (* apply ARcoupl_map; first done. *)
      rewrite /step'.
      rewrite Hsome.
      rewrite Hsome''.
      rewrite bool_decide_eq_true_2; last done.
      case_match eqn:Heqn.
      { apply mk_is_Some in Heqn. apply fill_val in Heqn. simpl in *. by destruct Heqn. }
      rewrite fill_dmap //=.
      rewrite head_prim_step_eq///=.
      rewrite Hsome'. rewrite bool_decide_eq_true_2; last done.
      rewrite !dmap_comp.
      apply ARcoupl_map; first done.
      simpl.
      apply ARcoupl_exact.
      eapply Rcoupl_mono.
      + eapply (Rcoupl_dunif). apply HBij.
      + simpl.
        intros ? ? ->.
        instantiate (1 := (λ x y, ∃ (a:fin(S (Z.to_nat z))),
                              x= (Val #a, {| heap := σh; tapes := σt |}, []) /\
                              y= ([(cfg_to_cfg' (l, s), j);
                                   (cfg_to_cfg' (<[j:=fill K #(g a)]> l ++ [], s), length (<[j:=fill K #(g a)]> l ++ []))],
                                    (<[j:=fill K #(g a)]> l ++ [], s))
                    )).
        naive_solver.
    - simpl.
      iPureIntro.
      intros?????(?&?&H')(?&?&?).
      destruct!/=.
      rewrite !app_nil_r in H'.
      eapply f_equal in H'.
      erewrite !list_lookup_insert in H'; try done.
      by simplify_eq.
    - simpl.
      iIntros (?????[a ?]).
      destruct!/=.
      iMod (spec_update_prog with "[$][$]") as "[HK Hs]".
      iModIntro. iNext.
      iMod "Hclose".
      rewrite app_nil_r.
      iFrame.
      iModIntro.
      wp_pures.
      iApply "HΨ". iFrame.
      iModIntro. rewrite Hfg.
      iFrame.
      iPureIntro. 
      pose proof fin_to_nat_lt a. lia.
  Qed.

  (** * rand(α, N) ~ rand(α, N) wrong bound coupling *)
  Lemma wp_couple_rand_lbl_rand_lbl_wrong N M f `{Bij nat nat f} z K E α α' xs ys j:
    TCEq N (Z.to_nat z) →
    N ≠ M →
    (∀ n, n < S N -> f n < S N)%nat →
    {{{ ▷ α ↪N (M; xs) ∗ ▷ α' ↪ₛN (M; ys) ∗ j ⤇ fill K (rand(#lbl:α') #z) }}}
      rand(#lbl:α) #z @ E
    {{{ (n : nat), RET #n; α ↪N (M; xs) ∗ α' ↪ₛN (M; ys) ∗ j⤇ fill K #(f n) ∗ ⌜ n ≤ N ⌝ }}}.
  Proof.
    iIntros (-> Hneq Hdom Ψ) "(>Htape & >Htape' & Hr) HΨ".
    iApply wp_lift_step_prog_couple; [done|].
    destruct (restr_bij_fin _ f Hdom) as [g [HBij Hfg]]; auto.
    iIntros ([σh σt] ρ1 ε) "[[Hh Ht] [Hs Hε]]".
    iDestruct (spec_auth_prog_agree with "Hs Hr") as "%Hsome".
    iDestruct "Htape" as (fs) "(<-&Hα)".
    iDestruct "Htape'" as (fsₛ) "(<-&Hαs)".
    iDestruct (ghost_map_lookup with "Ht Hα") as %Hsome'.
    iDestruct (spec_auth_lookup_tape with "Hs Hαs") as %Hsome''.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    (* replace ε with (0 + ε)%NNR; last first. *)
    (* { apply nnreal_ext; simpl; lra. } *)
    rewrite /prog_coupl.
    destruct ρ1 as [l s].
    assert (j < length l)%nat.
    { by eapply lookup_lt_Some. }
    
    iExists _, (full_info_one_step_stutter_osch j), 0%NNR, (λ _, ε), ε.
    iSplit.
    { iPureIntro. apply head_prim_reducible. rewrite /head_reducible. simpl.
      rewrite Hsome'. rewrite bool_decide_eq_false_2; last done.
      eexists _. rewrite dmap_pos.
      eexists _; split; first done.
      apply (dunifP_pos _ 0%fin). }
    repeat iSplit.
    - done.
    - rewrite Expval_const; last done.
      iPureIntro.
      rewrite Rplus_0_l.
      trans (ε*1); last (simpl; lra).
      by apply Rmult_le_compat.
    - iPureIntro. rewrite full_info_one_step_stutter_osch_lim_exec/=.
      rewrite head_prim_step_eq/=.
      (* apply ARcoupl_map; first done. *)
      rewrite /step'.
      rewrite Hsome.
      rewrite Hsome'.
      rewrite bool_decide_eq_false_2; last done.
      case_match eqn:Heqn.
      { apply mk_is_Some in Heqn. apply fill_val in Heqn. simpl in *. by destruct Heqn. }
      rewrite fill_dmap //=.
      rewrite head_prim_step_eq///=.
      rewrite Hsome''. rewrite bool_decide_eq_false_2; last done.
      rewrite !dmap_comp.
      apply ARcoupl_map; first done.
      simpl.
      apply ARcoupl_exact.
      eapply Rcoupl_mono.
      + eapply (Rcoupl_dunif). apply HBij.
      + simpl.
        intros ? ? ->.
        instantiate (1 := (λ x y, ∃ (a:fin(S (Z.to_nat z))),
                              x= (Val #a, {| heap := σh; tapes := σt |}, []) /\
                              y= ([(cfg_to_cfg' (l, s), j);
                                   (cfg_to_cfg' (<[j:=fill K #(g a)]> l ++ [], s), length (<[j:=fill K #(g a)]> l ++ []))],
                                    (<[j:=fill K #(g a)]> l ++ [], s))
                    )).
        naive_solver.
    - simpl.
      iPureIntro.
      intros?????(?&?&H')(?&?&?).
      destruct!/=.
      rewrite !app_nil_r in H'.
      eapply f_equal in H'.
      erewrite !list_lookup_insert in H'; try done.
      by simplify_eq.
    - simpl.
      iIntros (?????[a ?]).
      destruct!/=.
      iMod (spec_update_prog with "[$][$]") as "[HK Hs]".
      iModIntro. iNext.
      iMod "Hclose".
      rewrite app_nil_r.
      iFrame.
      iModIntro.
      wp_pures.
      iApply "HΨ". iFrame.
      iModIntro. rewrite Hfg.
      iFrame.
      iPureIntro. 
      pose proof fin_to_nat_lt a. repeat split; lia.
  Qed.


End rules.
