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
  

  (** fragmented rand N ~ rand M, N>=M, under injective function from M to N*)
  Lemma wp_couple_fragmented_rand_rand_inj {M N} (f: nat → nat) {_ : Inj (=) (=) f} j K E:
    (M <= N)%nat →
    (forall n : nat, (n < S M)%nat -> (f n < S N)%nat) ->
    {{{ j ⤇ fill K (rand #M) }}}  
      rand #N @ E
      {{{ (n:nat), RET #n; ⌜(n<=N)%nat⌝ ∗ (((∃ (m:nat), ⌜(m<=M)%nat⌝ ∗ ⌜(f m = n)%nat⌝ ∗ j⤇ fill K #m))∨(⌜¬ ∃ (m:nat), (m<=M)%nat ∧ f m = n⌝ ∗ j ⤇ fill K (rand #M))) }}}. 
  Proof.
    iIntros (Hineq Hdom Φ) "Hr HΦ".
    edestruct (restr_inj_fin (S M) (S N) f (le_n_S M N Hineq) Hdom) as [g [HgInj HgEq]].
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
    iExists _, (full_info_cons_osch (λ _, dmap (λ n, if bool_decide (∃ (m:nat), (m<=M)%nat /\ f m = fin_to_nat n) then j else (length l + n)%nat) (dunifP N)) (λ x, if bool_decide (x=j) then full_info_stutter_osch full_info_inhabitant else full_info_inhabitant)), 0%NNR, (λ _, ε), ε.
    solve_red.
    repeat iSplit.
    - done.
    - rewrite Expval_const; last done.
      iPureIntro.
      rewrite Rplus_0_l.
      trans (ε*1); last (simpl; lra).
      by apply Rmult_le_compat.
    - iPureIntro.
      simpl.
      rewrite head_prim_step_eq///=.
      rewrite full_info_cons_osch_lim_exec.
      rewrite /dmap.
      rewrite -dbind_assoc'.
      rewrite Nat2Z.id.
      unshelve erewrite (dunif_fragmented _ _ f) at 1; last apply Hineq; first naive_solver.
      rewrite -dbind_assoc'.
      replace 0 with (0+0) by lra.
      eapply ARcoupl_dbind; [lra|lra| |apply ARcoupl_eq].
      intros ? n ->.
      case_bool_decide as H'.
      + (* we step on an accepted thing *)
        destruct H' as [m H'].
        rewrite bool_decide_eq_true_2; last first.
        { eexists _; split; last done. pose proof fin_to_nat_lt m. lia. }
        rewrite /dmap -dbind_assoc'.
        rewrite dret_id_left.
        rewrite /step' Hsome fill_not_val; last done.
        rewrite fill_dmap//= head_prim_step_eq//=.
        rewrite !dmap_comp.
        rewrite /dmap -dbind_assoc'.
        rewrite Nat2Z.id.
        replace 0 with (0+0) by lra.
        eapply ARcoupl_dbind; [lra|lra| |apply ARcoupl_eq].
        intros ? m' ->.
        rewrite bool_decide_eq_true_2; last done.
        rewrite !dret_id_left/=.
        rewrite fin_to_nat_to_fin.
        rewrite full_info_lift_osch_lim_exec full_info_stutter_osch_lim_exec full_info_inhabitant_lim_exec app_nil_r !dmap_dret app_nil_r/= insert_length.
        instantiate (1:= (λ x y, ∃ (n:fin(S N)),
                             x= (Val #n, σ1, []) /\
                             if bool_decide (∃ m : fin (S M), f m = n)
                             then
                               (∃ m':fin (S M), f m' = n /\ y = ([(cfg_to_cfg' (l, s), j); (cfg_to_cfg' (<[j:=fill K #m']> l, s), length l)],
                                                                  (<[j:=fill K #m']> l, s)))
                             else y= ([(cfg_to_cfg' (l, s), (length l + fin_to_nat n)%nat)], (l, s))
                    )).
        apply ARcoupl_dret; first done.
        exists (nat_to_fin (Hdom _ (fin_to_nat_lt m'))).
        rewrite fin_to_nat_to_fin.
        rewrite bool_decide_eq_true_2; naive_solver.
      + (* we reject this value *)
        rewrite bool_decide_eq_false_2; last first.
        { intros [x[??]]. apply H'. assert (x< S M)%nat as Hineq'; first lia.
          eexists (nat_to_fin Hineq'). by rewrite fin_to_nat_to_fin. }
        rewrite !dret_id_left.
        rewrite /step'.
        rewrite lookup_ge_None_2; last lia.
        rewrite dret_id_left bool_decide_eq_false_2; last (simpl in *; lia). 
        rewrite full_info_lift_osch_lim_exec full_info_inhabitant_lim_exec.
        rewrite dmap_dret app_nil_r.
        apply ARcoupl_dret; first done.
        eexists _; split; first done.
        by rewrite bool_decide_eq_false_2.
    - iPureIntro. simpl. intros ????? (n&?&K1) (n'&?&K2). destruct!/=.
      case_bool_decide as H'; case_bool_decide as H''.
      + destruct K1 as [m1]. destruct K2 as [m2]. destruct H' as [m3]. destruct H'' as [m4].
        destruct!/=.
        replace (fin_to_nat n) with (f m1).
        replace (fin_to_nat n') with (f m2).
        replace m1 with m2; first done.
        assert (<[j:=fill K #m2]> l!!j = <[j:=fill K #m1]> l!!j) as Hlookup; first by f_equal.
        rewrite !list_lookup_insert in Hlookup; try lia.
        by simplify_eq.
      + destruct!/=.
      + destruct!/=.
      + destruct!/=.
        split; last done.
        by assert (fin_to_nat n = fin_to_nat n') as -> by lia.
    - simpl.
      iIntros (????? (n&?&H1)). destruct!/=.
      case_bool_decide as H2.
      + (* we got an accepted value *)
        destruct H1 as [m']. destruct H2 as [m]. destruct!/=.
        assert (m=m'); last subst.
        { apply fin_to_nat_inj. apply H. congruence. }
        iMod (spec_update_prog with "[$][$]") as "[??]".
        iModIntro.
        iNext.
        iMod "Hclose".
        iModIntro.
        iFrame.
        wp_pures.
        iApply "HΦ".
        pose proof fin_to_nat_lt n.
        iModIntro. 
        iSplit; first (iPureIntro; lia).
        iLeft. iFrame.
        iPureIntro. split; last done.
        pose proof fin_to_nat_lt m'. lia.
      + (* we got a rejected value *)
        iModIntro.
        simplify_eq. 
        iNext.
        iMod "Hclose".
        iFrame. iModIntro.
        wp_pures.
        iApply "HΦ".
        pose proof fin_to_nat_lt n.
        iModIntro.
        iSplit; first (iPureIntro; lia).
        iRight.
        iFrame.
        iPureIntro.
        intros (m&Hm&?).
        apply H2.
        assert (m<S M)%nat as Hineq' by lia.
        exists (nat_to_fin Hineq').
        by rewrite fin_to_nat_to_fin.
  Qed.
  
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

  (** fragmented state rand N ~ rand M, M>=N, under injective function from N to M, *)
  (**     but with errors for rejection sampling! *)
  Lemma pupd_couple_fragmented_tape_rand_inj_rev' {M N} (f : nat -> nat) {_: Inj (=) (=) f}
    ns α j K E (ε : R) :
    0 <= ε →
    (N < M)%nat →
    (forall n, n < S N -> f n < S M)%nat ->
    ▷ α ↪N (N; ns) -∗ ↯ ε -∗ j ⤇ fill K (rand #M) -∗
    pupd E E (∃ (m:nat), ⌜(m<=M)%nat⌝ ∗ j ⤇ fill K #m ∗
                       ((∃ (n:nat), ⌜(n<=N)%nat⌝ ∗ ⌜f n = m⌝ ∗ α ↪N (N; ns++[n]))∨
                          (⌜¬ (∃ (n:nat), (n<=N)%nat /\ f n = m)⌝ ∗ α ↪N (N; ns) ∗ ↯ (S M / (S M - S N) * ε)%R))).
  Proof.
    iIntros (Hε Hineq Hdom) ">Hα Herr Hr".
    (* edestruct (restr_inj_fin (S N) (S M) f (le_n_S N M (Nat.lt_le_incl _ _ Hineq)) Hdom) as [g [HgInj HgEq]]. *)
    iDestruct "Hα" as (fs) "(<-&Hα)".
    rewrite pupd_unseal/pupd_def.
    iIntros (σ ρ1 ε_now) "([? Ht]&Hs&Hε2)".
    iDestruct (ghost_map_lookup with "Ht Hα") as %?.
    iDestruct (spec_auth_prog_agree with "[$][$]") as "%Hlookup".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ec_supply_bound with "[$][$]") as %Hle.
    
    set ε' := mknonnegreal _ Hε.
    set ε_now1 := nnreal_minus ε_now ε' Hle.
    set ε_now2 := (ε_now + ε' * nnreal_nat (S N) / nnreal_nat (S M - S N))%NNR.
    set (E2 (ρ:cfg) := if bool_decide (∃ (n:fin(S N)), (ρ.1)!!j = Some (fill K #(f n)))
                       then ε_now1 else ε_now2).
    assert (∀ ρ, E2 ρ <= Rmax ε_now1 ε_now2)%R as Hbound.
    { intros ?. rewrite /E2. apply Rmax_Rle. case_bool_decide; by [left| right]. }
    set (E2' (m:fin(S M)) := if bool_decide (∃ (n:fin(S N)), f n = m)
                       then ε_now1 else ε_now2).
    destruct ρ1 as [l s].
    assert (j < length l)%nat.
    { by eapply lookup_lt_Some. }
    iApply spec_coupl_rec.
    iExists _, (dbind (λ m, if bool_decide (∃ (n:fin (S N)), (f (fin_to_nat n)) = fin_to_nat m) then state_step σ α else dret σ) (dunifP M)), (full_info_one_step_stutter_osch j), 0%NNR, (λ p, E2 (p.2)), (Rmax ε_now1 ε_now2).
    repeat iSplit.
    - iPureIntro. apply sch_erasable_dbind_predicate.
      + apply dunif_mass. lia.
      + by eapply state_step_sch_erasable.
      + apply dret_sch_erasable.
    - iPureIntro. naive_solver.
    - iPureIntro.
      simpl.
      rewrite Rplus_0_l.
      rewrite full_info_one_step_stutter_osch_lim_exec/step' Hlookup.
      rewrite fill_not_val//=.
      rewrite fill_dmap//=.
      rewrite head_prim_step_eq/=.
      rewrite Nat2Z.id.
      rewrite !dmap_comp.
      rewrite Expval_dmap/=; [|done|]; last first.
      { eapply ex_expval_bounded. intros; split; [apply cond_nonneg|apply Hbound]. }
      rewrite /Expval.
      setoid_rewrite dunif_pmf.
      rewrite SeriesC_scal_l.
      erewrite (SeriesC_ext _ E2'); last first.
      { intros . simpl.
        rewrite /E2/E2'.
        rewrite app_nil_r.
        case_bool_decide as H'.
        - destruct H' as [n' H'].
          rewrite list_lookup_insert in H'; last done.
          simplify_eq.
          rewrite bool_decide_eq_true_2; naive_solver.
        - rewrite bool_decide_eq_false_2; first naive_solver.
          intros [? ?].
          apply H'.
          eexists _. rewrite list_lookup_insert; last done.
          by repeat f_equal. 
      }
      rewrite /E2'.
      (* hardcore calculation *)
      eset (diff:=elements (((list_to_set (fin_to_nat <$> (enum (fin(S M))))):gset _ )∖ ((list_to_set((f∘fin_to_nat)<$>enum (fin(S N)))):gset _))).
      erewrite (SeriesC_ext _
                  (λ x : fin (S M), (if bool_decide (fin_to_nat x ∈ (f∘fin_to_nat )<$> enum (fin(S N))) then ε_now1 else 0%R) +
                                      if bool_decide (fin_to_nat x ∈ diff ) then ε_now2 else 0%R
               ))%R; last first.
      { intros n. rewrite /diff.
        case_bool_decide as H1'.
        - destruct H1' as [? H1']. rewrite bool_decide_eq_true_2; last first.
          + rewrite -H1'. apply elem_of_list_fmap. eexists _; split; first done. apply elem_of_enum.
          + subst. rewrite bool_decide_eq_false_2; first lra.
            rewrite elem_of_elements.
            rewrite not_elem_of_difference; right.
            rewrite elem_of_list_to_set. rewrite elem_of_list_fmap.
            rewrite -H1'. eexists _; split; first done.
            apply elem_of_enum.
        - rewrite bool_decide_eq_false_2; last first.
          { rewrite elem_of_list_fmap. intros [?[??]].
            subst. apply H1'. naive_solver. }
          rewrite bool_decide_eq_true_2; first lra.
          rewrite elem_of_elements. rewrite elem_of_difference.
          split; rewrite elem_of_list_to_set.
          + apply elem_of_list_fmap_1; apply elem_of_enum.
          + rewrite elem_of_list_fmap. intros [?[??]].
            subst. apply H1'. naive_solver.
      }
      rewrite SeriesC_plus; try apply ex_seriesC_finite.
      erewrite (SeriesC_ext _ (λ x : fin (S M), ε_now1 * if bool_decide (fin_to_nat x ∈ (list_to_set $ f ∘ fin_to_nat <$> enum (fin (S N)):gset _)) then 1 else 0)); last first.
      { intros. case_bool_decide.
        - rewrite bool_decide_eq_true_2; first lra.
          by rewrite elem_of_list_to_set.
        - rewrite bool_decide_eq_false_2; first lra.
          by rewrite elem_of_list_to_set. }
      erewrite (SeriesC_ext (λ _, if bool_decide _ then _ else _ ) (λ x : fin (S M), ε_now2 * if bool_decide (fin_to_nat x ∈ ((list_to_set diff):gset _)) then 1 else 0)); last first.
      { intros. case_bool_decide.
        - rewrite bool_decide_eq_true_2; first lra.
          by rewrite elem_of_list_to_set.
        - rewrite bool_decide_eq_false_2; first lra.
          by rewrite elem_of_list_to_set. }
      rewrite !SeriesC_scal_l.
      rewrite !SeriesC_fin_in_set; last first.
      { intros ?. rewrite elem_of_list_to_set.
        rewrite elem_of_list_fmap.
        intros. destruct!/=.
        apply Hdom.
        apply fin_to_nat_lt.
      }
      { rewrite /diff.
        intros ?. rewrite elem_of_list_to_set.
        rewrite elem_of_elements.
        rewrite elem_of_difference.
        rewrite elem_of_list_to_set elem_of_list_fmap.
        intros. destruct!/=.
        apply fin_to_nat_lt.
      }
      rewrite !size_list_to_set; last first.
      { apply NoDup_fmap_2; last apply NoDup_enum.
        eapply compose_inj; last done.
        apply fin_to_nat_inj.
      }
      { rewrite /diff.
        apply NoDup_elements.
      }
      rewrite /diff.
      rewrite fmap_length.
      replace (enum _) with (fin_enum (S N)) by done.
      rewrite length_enum_fin.
      rewrite -length_elements_size_gset.
      Local Opaque fin_enum.
      rewrite size_difference; last first.
      { intros ?. rewrite !elem_of_list_to_set.
        rewrite !elem_of_list_fmap.
        intros [y]. destruct!/=.
        exists (nat_to_fin (Hdom _ (fin_to_nat_lt y))).
        rewrite !fin_to_nat_to_fin; split; first done.
        replace (fin_enum _) with (enum (fin (S M)))by done.
        apply elem_of_enum.
      }
      rewrite !size_list_to_set; last first.
      { apply NoDup_fmap; first apply fin_to_nat_inj. apply NoDup_enum. }
      { apply NoDup_fmap; last replace (fin_enum _) with (enum(fin(S N))) by done.
        - eapply compose_inj; last done. apply fin_to_nat_inj.
        - apply NoDup_enum. }
      rewrite !fmap_length.
      rewrite !length_enum_fin.
      rewrite /ε_now1/ε_now2.
      Local Opaque INR.
      simpl.
      trans (/ S M * ((ε_now * (S N + (M-N)%nat)- ε* (S N- (S N)*/(M-N)%nat*(M-N)%nat )))); first (simpl; lra).
      rewrite Rmult_assoc.
      rewrite Rinv_l; last first.
      { apply not_0_INR. lia. }
      trans (/ S M * (ε_now * (S N + (M - N)%nat))); first lra.
      rewrite -plus_INR.
      replace (_+_)%nat with (S M) by lia.
      trans (/ S M * S M *ε_now); first lra.
      rewrite Rinv_l; first (simpl; lra).
      apply not_0_INR. lia.
    - iPureIntro. rewrite full_info_one_step_stutter_osch_lim_exec/step' Hlookup.
      rewrite fill_not_val//=.
      rewrite fill_dmap//=.
      rewrite head_prim_step_eq/=.
      rewrite Nat2Z.id.
      rewrite !dmap_comp.
      rewrite /dmap.
      replace (INR _) with (0+0)%R; last by rewrite Rplus_0_l.
      unshelve erewrite (dunif_fragmented _ N f) at 2; last lia.
      { intros. by apply Hdom. }
      rewrite -dbind_assoc'.
      eapply ARcoupl_dbind; [done|done| |apply ARcoupl_eq].
      intros ? m ->.
      simpl.
      case_bool_decide as H2.
      + (* accepted value *)
        destruct H2 as [n H2].
        erewrite state_step_unfold; last done.
        rewrite /dmap -dbind_assoc'.
        replace 0 with (0+0)%R by lra.
        eapply ARcoupl_dbind; [done|done| |apply ARcoupl_eq].
        intros ? n' ->.
        rewrite dret_id_left.
        rewrite app_nil_r insert_length fin_to_nat_to_fin.
        instantiate (1:= (λ x y, ∃ (m:fin(S M)),
                             if bool_decide (∃ n : fin (S N), f n = m)
                             then
                               ∃ (n':fin (S N)), x= (state_upd_tapes <[α:=(N; fs ++ [n'])]> σ) /\ y=([(cfg_to_cfg' (l, s), j); (cfg_to_cfg' (<[j:=fill K #(f n')]> l, s), length l)],
        (<[j:=fill K #(f n')]> l, s))
                             else x=σ /\ y= ([(cfg_to_cfg' (l, s), j); (cfg_to_cfg' (<[j:=fill K #m]> l, s), length l)],
        (<[j:=fill K #m]> l, s))
                    )).
        apply ARcoupl_dret; first done.
        exists m.
        rewrite bool_decide_eq_true_2; naive_solver.
      + (* rejected value *)
        rewrite dret_id_left.
        rewrite app_nil_r insert_length.
        apply ARcoupl_dret; first done.
        exists m.
        rewrite bool_decide_eq_false_2; last done.
        naive_solver.
    - iPureIntro.
      intros ?????[m1 K1][m2 K2]. case_bool_decide as C1; case_bool_decide as C2.
      + destruct K1 as [n1]. destruct K2 as [n2]. destruct!/=.
        replace n1 with n2; first done.
        assert (<[j:=fill K #(f n2)]> l!!j = <[j:=fill K #(f n1)]> l!!j) as Heq; first by f_equal.
        rewrite !list_lookup_insert in Heq; try lia. by destruct!/=. 
      + destruct!/=.
        exfalso.
        apply C2.
        assert (<[j:=fill K #(f n')]> l !!j= <[j:=fill K #m1]> l!!j)as Heq; first by f_equal.
        rewrite !list_lookup_insert in Heq; try lia. destruct!/=.
        naive_solver.
      + destruct!/=. exfalso. apply C1.
        assert (<[j:=fill K #(m2)]> l !!j= <[j:=fill K #(f n')]> l!!j)as Heq; first by f_equal.
        rewrite !list_lookup_insert in Heq; try lia. destruct!/=.
        naive_solver.
      + destruct!/=. split; first done.
        congruence.
    - simpl. iIntros (????).
      destruct!/=.
      case_bool_decide as H3.
      + (* accepted *)
        destruct!/=.
        iMod (spec_update_prog with "[$][$]") as "[HK Hs]".
        iMod (ghost_map_update with "Ht [$]") as "(?&?)".
        replace (ε_now) with (ε' + ε_now1)%NNR; last first.
        { apply nnreal_ext. simpl. lra. }
        iMod (ec_supply_decrease with "[$] [$]") as (?? H2 ?) "H".
        replace (E2 _) with (ε_now1); last first.
        { rewrite /E2. subst.
          rewrite bool_decide_eq_true_2; first done.
          eexists _. by rewrite list_lookup_insert. 
        }
        iModIntro. 
        iApply spec_coupl_ret.
        iFrame.
        iMod "Hclose'".
        iModIntro.
        iSplitL "H".
        * iApply ec_supply_eq; [|done].
          simplify_eq/=. lra.
        * iSplit; last (iLeft; iPureIntro; eexists (fin_to_nat _)).
          -- iPureIntro.
             apply Nat.lt_succ_r.
             apply Hdom.
             apply fin_to_nat_lt.
          -- repeat split; [apply Nat.lt_succ_r|by rewrite fmap_app].
             apply fin_to_nat_lt.
      + (* rejected *)
        destruct!/=.
        iMod (spec_update_prog with "[$][$]") as "[HK Hs]".
        replace (E2 _) with (ε_now2); last first.
        { rewrite /E2. subst.
          rewrite bool_decide_eq_false_2; first done.
          intros [? Heq]. rewrite list_lookup_insert in Heq; last done.
          simplify_eq. apply H3. naive_solver.
        }
        destruct (Rle_or_lt 1 ε_now2).
        { iModIntro. by iApply spec_coupl_ret_err_ge_1. }
        iModIntro.
        iApply spec_coupl_ret.
        iFrame.
        iMod (ec_supply_increase with "[$]") as "[$ Herr']".
        { by eapply Rle_lt_trans. }
        iCombine "Herr Herr'" as "Herr".
        iMod "Hclose'".
        iModIntro.
        iSplit.
        { iPureIntro. apply Nat.lt_succ_r. apply fin_to_nat_lt. }
        iRight.
        iSplitR.
        * iPureIntro.
          intros [].
          apply H3. destruct!/=.
          unshelve eexists (nat_to_fin _); last by rewrite fin_to_nat_to_fin.
          lia.
        * iSplitR; first done.
          iApply (ec_eq with "[$]").
          simpl.
          assert (ε * (1+S N * /(M-N)%nat - S M/(S M -S N))=0); simpl; last lra.
          rewrite -minus_INR; last lia.
          simpl.
          erewrite <-(Rinv_r (M-N)%nat); last (apply not_0_INR; lia).
          apply Rmult_eq_0_compat_l.
          assert ((M - N)%nat * / (M - N)%nat + (S N -S M)/ (M - N)%nat = 0); last lra.
          rewrite Rinv_r; last (apply not_0_INR; lia).
          rewrite -Ropp_minus_distr.
          rewrite -minus_INR; last lia.
          rewrite Rdiv_opp_l.
          simpl.
          rewrite Rdiv_diag; last (apply not_0_INR; lia).
          lra.
  Qed.

  Local Transparent INR.
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


  (** * Lemmas for von neumann coin example *)
  Lemma pupd_couple_von_neumann_1 {N:nat} (l1 l2: list (nat*nat)) α β ns ns' j K E:
    Forall (λ x, x.1<=N/\x.2<=N)%nat l1 ->
    Forall (λ x, x.1<=N/\x.2<=N)%nat l2 ->
    NoDup (l1++l2) ->
    length l1 = length l2 ->
    (0<length l1 )%nat ->
    (2* length l1 <=S N * S N)%nat ->
    ▷ α ↪N (N; ns) -∗
    ▷ β ↪N (N; ns') -∗
    j ⤇ fill K (rand #1) -∗
    pupd E E (∃ x y, ⌜(x<=N)%nat⌝ ∗ ⌜(y<=N)%nat⌝ ∗ α ↪N (N; ns++[x]) ∗ β ↪N (N; ns'++[y]) ∗
                     if bool_decide ((x,y)∈l1) then j ⤇ fill K #1
                     else if bool_decide ((x,y)∈l2) then j⤇ fill K #0
                          else j⤇ fill K (rand #1)
      ).
  Proof.
    iIntros (Hl1 Hl2 Hnodup Hlen Hlen' Hpos) ">Hα >Hβ Hspec".
    (* edestruct (restr_inj_fin (S N) (S M) f (le_n_S N M (Nat.lt_le_incl _ _ Hineq)) Hdom) as [g [HgInj HgEq]]. *)
    iDestruct "Hα" as (fs) "(<-&Hα)".
    iDestruct "Hβ" as (fs') "(<-&Hβ)".
    rewrite pupd_unseal/pupd_def.
    iIntros (σ ρ1 ε_now) "([? Ht]&Hs&Hε2)".
    iDestruct (ghost_map_lookup with "Ht Hα") as %?.
    iDestruct (ghost_map_lookup with "Ht Hβ") as %?.
    iDestruct (spec_auth_prog_agree with "[$][$]") as "%Hlookup".
    iDestruct (ghost_map_elem_ne with "Hα Hβ") as "%".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    
    destruct ρ1 as [l s].
    assert (j < length l)%nat.
    { by eapply lookup_lt_Some. }
    iApply spec_coupl_rec.
    assert (∃ f: fin (S N) * fin (S N) -> fin (S ((S N * S N - 1))), Bij f) as [f Hbij].
    { cut (card (fin (S N) * fin (S N)) = card (fin (S ((S N * S N - 1))))).
      - rewrite finite_bijective.
        intros [f []].
        exists f. done. 
      - rewrite prod_card !fin_card. lia.
    }
    set (f_inv f) as f'.
    


    (* create fragmented_f*)

    
    (* fragmented f maps 2*length l1 *)
    set (λ (n:nat), match l1!!n with
                  | Some x => x
                  | None =>
                      match l2!!(n-length l1)%nat with
                      | Some x => x
                      | None => (0,0)%nat
                      end
                  end
        ) as fragmented_f'.
    set (λ (n:nat), match (l1++l2)!!n with
                  | Some x => x
                  | None =>(0,0)
                  end
        )%nat as fragmented_f_alt.
    assert (∀ x, fragmented_f' x = fragmented_f_alt x) as Hfrag_eq.
    { intros. rewrite /fragmented_f' /fragmented_f_alt.
      case_match eqn :Heqn.
      - rewrite lookup_app_l; last (eapply lookup_lt_is_Some; by rewrite Heqn).
        by rewrite Heqn.
      - case_match eqn:Heqn'.
        + rewrite lookup_app_r; first by rewrite Heqn'.
          by apply lookup_ge_None_1.
        + rewrite lookup_ge_None_2; first done.
          rewrite app_length.
          apply lookup_ge_None_1 in Heqn'. lia.
    }
    assert (∀ n, (fragmented_f' n).1 < S N /\ (fragmented_f' n).2 < S N)%nat as Hfragmented_f'.
    {
      intros. rewrite /fragmented_f'.
      case_match eqn :Heqn1.
      - eapply Forall_lookup_1 in Hl1; last done. lia.
      - case_match eqn:Heqn2; last (simpl; lia).
        eapply Forall_lookup_1 in Hl2; last done. lia.
    }
    set (λ n,
           if bool_decide (n<2*length l1)%nat then 
             fin_to_nat $ f (nat_to_fin $ proj1 (Hfragmented_f' n), nat_to_fin $ proj2 (Hfragmented_f' n))
           else n+S N * S N
        )%nat as fragmented_f.
    assert (Inj (=) (=) fragmented_f).
    { rewrite /fragmented_f.
      intros ??.
      case_bool_decide as Heqn1; case_bool_decide as Heqn2.
      - intros Hinj.
        apply fin_to_nat_inj in Hinj.
        apply Hbij in Hinj.
        inversion Hinj as [[K1 K2]].
        apply (f_equal fin_to_nat) in K1, K2.
        rewrite !fin_to_nat_to_fin in K1 K2.
        assert (fragmented_f' x = fragmented_f' y) as Heq.
        { by apply injective_projections. }
        rewrite !Hfrag_eq in Heq.
        rewrite /fragmented_f_alt in Heq.
        rewrite NoDup_alt in Hnodup.
        pose proof Hnodup x y.
        case_match eqn :K'; last first.
        { apply lookup_ge_None_1 in K'. rewrite app_length in K'. lia. }
        case_match eqn:K''; last first. 
        { apply lookup_ge_None_1 in K''. rewrite app_length in K''. lia. }
        subst. naive_solver.
      - pose proof fin_to_nat_lt (f (nat_to_fin (proj1 (Hfragmented_f' x)), nat_to_fin (proj2 (Hfragmented_f' x)))). intros. lia.
      - pose proof fin_to_nat_lt (f (nat_to_fin (proj1 (Hfragmented_f' y)), nat_to_fin (proj2 (Hfragmented_f' y)))). intros. lia.
      - lia. 
    }
    
    
    (* f_decompose *)
    set ((λ (n:fin (S (2*length l1 -1))),
            match decide (fin_to_nat n < (S (length l1-1)))%nat with
                  | left p => (1%fin, nat_to_fin p)
                  | _ =>
                      match decide (fin_to_nat n - length l1 < (S (length l1-1)))%nat with
                      | left p => (0%fin, nat_to_fin p)
                      | _ => (0,0)%fin
                      end
                  end
         ): _ -> fin (S 1) * fin (S (length l1 -1))) as f_decompose'.
    assert (Bij f_decompose').
    { split.
      - intros x y. rewrite /f_decompose'.
        repeat case_match; intros Heq; try simplify_eq;
          try apply (f_equal fin_to_nat) in Heq; try rewrite !fin_to_nat_to_fin in Heq; apply fin_to_nat_inj; try done; pose proof fin_to_nat_lt x; pose proof fin_to_nat_lt y; lia.
      - rewrite /f_decompose'.
        intros [x y].
        assert ((1- fin_to_nat x)%nat * length l1 + fin_to_nat y < S (2*length l1 -1))%nat as Hineq.
        { pose proof fin_to_nat_lt x. pose proof fin_to_nat_lt y. simpl in *. destruct (fin_to_nat x) as [|[|]]; simpl; lia. }
        exists (nat_to_fin Hineq).
        rewrite !fin_to_nat_to_fin.
        pose proof fin_to_nat_lt x.
        pose proof fin_to_nat_lt y.
        destruct (fin_to_nat x) as [|[|]] eqn:Heqn.
        + case_match; first lia.
          case_match; last lia.
          f_equal; apply fin_to_nat_inj; try rewrite fin_to_nat_to_fin; last lia. by simpl.
        + case_match; last lia.
          f_equal; apply fin_to_nat_inj; try rewrite fin_to_nat_to_fin; last lia. by simpl.
        + lia.
    }
    set (f_inv f_decompose') as f_decompose.
    assert (Bij f_decompose) by apply f_inv_bij.
    
    
    (* LHS is simply state step of α followed by β*)
    (* RHS is a scheduler that samples from (0-(SN * SN -1)), if the number is smaller than length l1 * 2, then we take a step of j, other we dont, plus some bookkeeping with full_info_stutter
     *)

    eset (λ x y, ∃ a c,
            x= state_upd_tapes <[β := (N;fs' ++ [c])]> (state_upd_tapes <[α:=(N;fs ++ [a])]> σ) /\
            if bool_decide (∃ (m : fin (S (2*length l1 -1))), fragmented_f m = f (a, c))
            then ∃ (m : fin (S (2*length l1 -1))), fragmented_f m = f (a, c) /\ let '(b,idx) := f_inv f_decompose m in
        y=([(cfg_to_cfg' (l, s), j); (cfg_to_cfg' (<[j:=fill K #b]> l, s), (length l + idx)%nat)],
        (<[j:=fill K #b]> l, s))
            else y= ([(cfg_to_cfg' (l, s), (length l + fin_to_nat (f (a,c)))%nat)], (l, s))
           ) as P.
    
    iExists P.
    iExists (dbind (λ σ', state_step σ' β) (state_step σ α)).
    iExists (full_info_cons_osch (λ _, dmap (λ n, if bool_decide ((λ x:fin (S N) * fin (S N), (fin_to_nat x.1, fin_to_nat x.2)) (f_inv f n)∈ l1 ++ l2)%nat then j else (length l + n)%nat) (dunifP ((S N) *(S N)-1)%nat))
               (λ x, if bool_decide (x=j) then
                       full_info_cons_osch (λ _, dmap (λ n, length l + fin_to_nat n)%nat (dunifP (length l1 -1))) (λ _, full_info_inhabitant)
                     else full_info_inhabitant)), 0%NNR, (λ _, ε_now), ε_now.
    repeat iSplit.
    - iPureIntro. apply sch_erasable_dbind; first eapply state_step_sch_erasable; first done.
      intros σ'. rewrite {1}/state_step. rewrite bool_decide_eq_true_2; last by rewrite elem_of_dom.
      setoid_rewrite lookup_total_correct at 1; last done.
      simpl.
      intros Hpos'.
      apply dmap_pos in Hpos'. destruct Hpos' as (?&->&Hpos').
      eapply state_step_sch_erasable.
      simpl. by rewrite lookup_insert_ne.
    - done.
    - rewrite Expval_const; last done.
      iPureIntro.
      rewrite Rplus_0_l.
      trans (ε_now*1); last (simpl; lra).
      by apply Rmult_le_compat.
    - iPureIntro.
      (* unfold definitions *)
      rewrite full_info_cons_osch_lim_exec/dmap-dbind_assoc'.
      rewrite /state_step.
      rewrite bool_decide_eq_true_2; last by rewrite elem_of_dom.
      setoid_rewrite lookup_total_correct at 2; last done.
      erewrite (dbind_ext_right_strong _ _ (λ σ', dmap (λ n : fin (S N), state_upd_tapes <[β := (N; fs' ++[n])]> σ') (dunifP N))); last first.
      { intros σ' Hσ'.
        apply dmap_pos in Hσ'.
        destruct Hσ' as (?&->&Hσ').
        rewrite bool_decide_eq_true_2; last first.
        { rewrite elem_of_dom. 
          simpl.
          rewrite lookup_insert_ne; naive_solver.
        }
        setoid_rewrite lookup_total_correct; last by rewrite lookup_insert_ne.
        done. 
      }
      set ((λ x, state_upd_tapes <[β:=(N; fs' ++ [x.2])]> x.1)) as fn.
      assert ((dbind (λ σ', dmap (λ n : fin (S N), state_upd_tapes <[β:=(N; fs' ++ [n])]> σ') (dunifP N))
       (dmap (λ n : fin (S N), state_upd_tapes <[α:=(N; fs ++ [n])]> σ) (dunifP N))) = (dbind (λ σ', dmap (λ n : fin (S N), fn (σ', n)) (dunifP N))
                                                                                          (dmap (λ n : fin (S N), state_upd_tapes <[α:=(N; fs ++ [n])]> σ) (dunifP N)))) as -> by done.
      erewrite (dbind_dmap_inj_rearrange); last first. 
      { rewrite /fn. intros [][].
        intros H'.
        apply state_upd_tapes_same' in H' as H''.
        rewrite !(upd_diff_tape_comm _ _ β) in H'; try done.
        apply state_upd_tapes_same' in H' as H'''.
        simpl in *. by simplify_eq. }
      { intros ??. apply state_upd_tapes_same'. }
      replace (dbind _ _) with (dbind
                                  (λ ac,
                                     let '(a, c) := f_inv f ac in
                                     dret (fn (state_upd_tapes <[α:=(N; fs ++ [a])]> σ, c))) 
                                  (dunifP (S N * S N -1))); last first.
      { rewrite dunifP_decompose; last done.
        rewrite -dbind_assoc'.
        apply dbind_ext_right.
        intros ?.
        rewrite /dmap.
        rewrite -dbind_assoc'.
        apply dbind_ext_right.
        intros ?.
        rewrite dret_id_left.
        by rewrite f_inv_cancel_l.
      }
      rewrite {1}(dunif_fragmented _ (2*length l1 -1)%nat fragmented_f).
      { rewrite /fragmented_f.
        intros. simpl in *. rewrite bool_decide_eq_true_2; last lia.
        apply fin_to_nat_lt.
      } 
      2:{ lia. }
      intros Hbound.
      rewrite -!dbind_assoc'.
      simpl.
      replace 0%R with (0+0)%R by lra.
      eapply ARcoupl_dbind; [done|done| |apply ARcoupl_eq].
      intros ? ac ->.
      rewrite dret_id_left.
      case_bool_decide as Heqn1.
      + (* we step on an accepted value *)
        rewrite bool_decide_eq_true_2; last first.
        { rewrite /fragmented_f in Heqn1.
          destruct Heqn1 as [m Heqn1].
          pose proof fin_to_nat_lt m.
          case_bool_decide; last lia.
          apply fin_to_nat_inj in Heqn1. subst.
          rewrite f_inv_cancel_l !fin_to_nat_to_fin.
          rewrite -surjective_pairing.
          rewrite Hfrag_eq.
          rewrite /fragmented_f_alt.
          case_match eqn:Heqn'.
          - by eapply elem_of_list_lookup_2.
          - apply lookup_ge_None_1 in Heqn'. rewrite app_length in Heqn'. lia.
        }
        rewrite Hlookup.
        rewrite bool_decide_eq_true_2; last done.
        rewrite fill_not_val//. rewrite fill_dmap//=.
        rewrite head_prim_step_eq/=.
        replace(Z.to_nat 1) with 1%nat by done.
        
        erewrite (dunifP_decompose ); [|by apply f_inv_bij|]; last lia.
        rewrite /dmap -!dbind_assoc'.
        replace 0%R with (0+0) by lra.
        eapply ARcoupl_dbind; [done|done| |apply ARcoupl_eq].
        intros ? b ->.
        rewrite !dret_id_left.
        rewrite full_info_lift_osch_lim_exec full_info_cons_osch_lim_exec.
        rewrite /dmap -!dbind_assoc'.
        replace 0%R with (0+0) by lra.
        eapply ARcoupl_dbind; [done|done| |apply ARcoupl_eq].
        rewrite /step'.
        intros ? c ->.
        rewrite !dret_id_left.
        rewrite lookup_ge_None_2; last first.
        { rewrite app_nil_r. rewrite insert_length. lia. }
        rewrite dret_id_left.
        rewrite full_info_lift_osch_lim_exec app_nil_r full_info_inhabitant_lim_exec.
        rewrite dmap_dret dret_id_left app_nil_r.
        simpl.
        rewrite /P.
        case_match eqn :Heq.
        apply (f_equal f) in Heq.
        rewrite f_inv_cancel_r in Heq.
        apply (f_equal fin_to_nat) in Heq.
        rewrite fin_to_nat_to_fin in Heq.
        rewrite /fragmented_f in Heq.
        case_match; last first.
        { pose proof fin_to_nat_lt (f (t, t0)). lia. }
        simplify_eq.
        apply ARcoupl_dret; first done.
        eexists _, _; split; first done.
        simpl.
        rewrite bool_decide_eq_true_2; last first.
        { rewrite /fragmented_f. eexists _.
          rewrite bool_decide_eq_true_2; first done.
          pose proof fin_to_nat_lt (f_decompose (b, c)). simpl in *.
          rewrite -/f_decompose. lia.
        }
        rewrite /fragmented_f.
        eexists _.
        rewrite bool_decide_eq_true_2; first (split; first done); last first.
        { pose proof fin_to_nat_lt (f_decompose (b, c)). simpl in *.
          rewrite -/f_decompose. lia. }
        rewrite -/f_decompose.
        erewrite f_inv_cancel_l; first done.
        apply f_inv_bij.
      + (* we step on a rejected value*)
        rewrite dret_id_left.
        case_match eqn :Heq.
        rewrite bool_decide_eq_false_2; last first.
        { intros Hcontra.
          simpl in *.
          apply Heqn1.
          rewrite /fragmented_f.
          rewrite elem_of_list_lookup in Hcontra.
          destruct Hcontra as [idx Hcontra].
          assert (idx<S (2*length l1-1))%nat as Hineq.
          { apply lookup_lt_Some in Hcontra. rewrite app_length in Hcontra. lia. }
          eexists (nat_to_fin Hineq).
          rewrite bool_decide_eq_true_2.
          - apply (f_equal f) in Heq. rewrite f_inv_cancel_r in Heq. subst.
            f_equal. f_equal. f_equal; apply fin_to_nat_inj; rewrite fin_to_nat_to_fin; rewrite Hfrag_eq/fragmented_f_alt; by rewrite fin_to_nat_to_fin Hcontra.
          - rewrite fin_to_nat_to_fin; lia.
        }
        rewrite lookup_ge_None_2; last lia.
        rewrite bool_decide_eq_false_2; last (simpl in *; lia).
        rewrite dret_id_left.
        rewrite full_info_lift_osch_lim_exec full_info_inhabitant_lim_exec dmap_dret app_nil_r.
        apply ARcoupl_dret; first done.
        rewrite /P.
        eexists _, _; split; first done.
        simpl.
        rewrite bool_decide_eq_false_2; last first.
        { intros (?&H').
          apply Heqn1. eexists _. setoid_rewrite H'.
          rewrite -Heq. by rewrite f_inv_cancel_r.
        }
        rewrite -Heq. by rewrite f_inv_cancel_r.
    - iPureIntro.
      rewrite /P.
      intros ????? (a&c&->&A1) (a0&c0&->&A2). 
      (* bad hypothesis names :) *)
      case_bool_decide as K1; case_bool_decide as K2.
      + destruct A1, A2.
        destruct (f_inv f_decompose x0) eqn :K3, (f_inv f_decompose x) eqn :K4.
        destruct!/=.
        rewrite -H8 in K1. simplify_eq.
        rewrite -K2 in H7. simplify_eq.
        assert (t1=t).
        { apply (f_equal (λ x, x!!j)) in H10.
          rewrite !list_lookup_insert in H10; try done.
          by simplify_eq.
        }
        subst.
        assert (t0=t2).
        { simpl in *. apply fin_to_nat_inj. lia. }
        subst. rewrite -K3 in K4.
        apply (f_equal f_decompose) in K4.
        rewrite !f_inv_cancel_r in K4.
        subst.
        rewrite H8 in K2. by simplify_eq.
      + destruct!/=.
      + destruct!/=.
      + simplify_eq. split; last done.
        assert ((a,c)=(a0,c0)); last by simplify_eq.
        apply Hbij.
        simpl in *. apply fin_to_nat_inj. lia.
    - simpl. rewrite /P. iIntros (????).
      destruct!/=.
      case_bool_decide as Hcase.
      + (* accepted *)
        destruct H8 as [x[]].
        destruct (f_inv f_decompose x) as [t t0] eqn:Hx.
        destruct!/=.
        iMod (spec_update_prog with "[$][$]") as "[HK Hs]".
        iMod (ghost_map_update with "[$]Hα") as "(?&?)".
        iMod (ghost_map_update with "[$]Hβ") as "(?&?)".
        iModIntro.
        iApply spec_coupl_ret.
        iMod "Hclose'" as "_".
        iFrame.
        iModIntro.
        rewrite !fmap_app.
        iExists _, _; repeat iSplit; [| | try done..].
        * iPureIntro. apply Nat.lt_succ_r. apply fin_to_nat_lt.
        * iPureIntro. apply Nat.lt_succ_r. apply fin_to_nat_lt.
        * apply (f_equal f_decompose) in Hx.
          rewrite f_inv_cancel_r in Hx.
          subst.
          rewrite /fragmented_f in H6.
          case_bool_decide; last first.
          { pose proof fin_to_nat_lt (f(a,c)). lia. }
          simplify_eq.
          rewrite !fin_to_nat_to_fin -surjective_pairing.
          case_bool_decide as K1.
          -- rewrite Hfrag_eq in K1.
             rewrite /fragmented_f_alt in K1.
             case_match eqn :Hlookup'; last first.
             { apply lookup_ge_None_1 in Hlookup'.
               rewrite app_length in Hlookup'.
               pose proof fin_to_nat_lt (f_decompose (t, t0)). lia.
             }
             pose proof fin_to_nat_lt t as Hineq.
             destruct (fin_to_nat t) as [|[|]] eqn:Heqn'; try iFrame; try lia.
             rewrite /f_decompose in Hlookup'.
             exfalso.
             rewrite /f_inv in Hlookup'.
             pose proof epsilon_correct _  (surj f_decompose' (t, t0)) as Hep.
             simpl in *.
             remember (epsilon(surj f_decompose' (t, t0))) as x.
             rewrite /f_decompose' in Hep.
             pose proof fin_to_nat_lt x.
             case_match; first simplify_eq.
             case_match; last lia.
             simplify_eq.
             rewrite lookup_app_r in Hlookup'; last lia.
             rewrite NoDup_app in Hnodup.
             apply Hnodup in K1. apply K1. erewrite elem_of_list_lookup. naive_solver.
          -- case_bool_decide as K2; last first.
             { rewrite Hfrag_eq in K1, K2.
               assert (fragmented_f_alt (f_decompose (t,t0)) ∉l1++l2) as Hnotin by (rewrite elem_of_app; naive_solver).
               rewrite /fragmented_f_alt in Hnotin.
               case_match eqn :Hlookup'.
               - rewrite elem_of_list_lookup in Hnotin.
                 exfalso. naive_solver.
               - apply lookup_ge_None_1 in Hlookup'.
                 pose proof fin_to_nat_lt (f_decompose (t, t0)). rewrite app_length in Hlookup'. lia.
             }
             rewrite Hfrag_eq in K1, K2.
             rewrite /fragmented_f_alt in K2.
             case_match eqn:Hlookup'; last first.
             { apply lookup_ge_None_1 in Hlookup'.
               rewrite app_length in Hlookup'.
               pose proof fin_to_nat_lt (f_decompose (t, t0)). lia.
             }
             pose proof fin_to_nat_lt t as Hineq.
             destruct (fin_to_nat t) as [|[|]] eqn:Heqn'; try iFrame; try lia.
             rewrite /f_decompose in Hlookup'.
             exfalso.
             rewrite /f_inv in Hlookup'.
             pose proof epsilon_correct _  (surj f_decompose' (t, t0)) as Hep.
             simpl in *.
             remember (epsilon(surj f_decompose' (t, t0))) as x.
             rewrite /f_decompose' in Hep.
             pose proof fin_to_nat_lt x.
             case_match; last first.
             { case_match; [simplify_eq|lia]. }
             rewrite lookup_app_l in Hlookup'; last lia.
             rewrite NoDup_app in Hnodup.
             unfold not in Hnodup.
             eapply Hnodup; last done.
             erewrite elem_of_list_lookup. naive_solver.
      + simplify_eq.
        iMod (ghost_map_update with "[$]Hα") as "(?&?)".
        iMod (ghost_map_update with "[$]Hβ") as "(?&?)".
        iModIntro.
        iApply spec_coupl_ret.
        iMod "Hclose'" as "_".
        iFrame.
        iModIntro.
        rewrite !fmap_app.
        iExists _, _; repeat iSplit; [| | try done..].
        * iPureIntro. apply Nat.lt_succ_r. apply fin_to_nat_lt.
        * iPureIntro. apply Nat.lt_succ_r. apply fin_to_nat_lt.
        * rewrite !bool_decide_eq_false_2; first done.
          -- rewrite elem_of_list_lookup.
             intros [idx Hidx].
             assert (idx < length l2)%nat.
             { eapply lookup_lt_is_Some_1; by rewrite Hidx. }
             assert (idx+length l1 < S (2*length l1 -1))%nat as Hineq by lia.
             apply Hcase.
             exists (nat_to_fin Hineq).
             rewrite /fragmented_f.
             rewrite !fin_to_nat_to_fin.
             rewrite bool_decide_eq_true_2; last lia.
             do 3 f_equal; apply fin_to_nat_inj; rewrite fin_to_nat_to_fin;
             rewrite /fragmented_f'.
             ++ case_match eqn:Heqn.
                { apply lookup_lt_Some in Heqn. lia. }
                rewrite Nat.add_sub.
                by rewrite Hidx.
             ++ case_match eqn:Heqn.
                { apply lookup_lt_Some in Heqn. lia. }
                rewrite Nat.add_sub.
                by rewrite Hidx.
          -- rewrite elem_of_list_lookup.
             intros [idx Hidx].
             assert (idx < length l1)%nat.
             { eapply lookup_lt_is_Some_1; by rewrite Hidx. }
             assert (idx < S (2*length l1 -1))%nat as Hineq by lia.
             apply Hcase.
             exists (nat_to_fin Hineq).
             rewrite /fragmented_f.
             rewrite !fin_to_nat_to_fin.
             rewrite bool_decide_eq_true_2; last lia.
             do 3 f_equal; apply fin_to_nat_inj; rewrite fin_to_nat_to_fin;
             rewrite /fragmented_f'.
             ++ case_match eqn:Heqn; last done.
                by simplify_eq.
             ++ case_match eqn:Heqn; last done.
                by simplify_eq.
  Qed. 



  Lemma pupd_couple_von_neumann_2 {N:nat} (l1 l2: list (nat*nat)) α ns j K j' K' E ε:
    Forall (λ x, x.1<=N/\x.2<=N)%nat l1 ->
    Forall (λ x, x.1<=N/\x.2<=N)%nat l2 ->
    NoDup (l1++l2) ->
    length l1 = length l2 ->
    (0<length l1 )%nat ->
    (2* length l1 <S N * S N)%nat ->
    (ε>0)%R ->
    j ⤇ fill K (rand #N) -∗
    j' ⤇ fill K' (rand #N) -∗
    ▷ α ↪N (1; ns) -∗
    ↯ ε -∗
    pupd E E (∃ x y, ⌜(x<=N)%nat⌝ ∗ ⌜(y<=N)%nat⌝ ∗ j⤇ fill K #x ∗ j' ⤇ fill K' #y ∗
                     if bool_decide ((x,y)∈l1) then α ↪N (1; ns ++ [1%nat])
                     else if bool_decide ((x,y)∈l2) then α ↪N (1; ns ++ [0%nat])
                          else α ↪N (1; ns) ∗ ↯ ((((N+1)* (N+1))%nat / ((N+1)*(N+1) - 2 * (length l1))%nat)%R * ε)
      ).
  Proof.
    iIntros (Hl1 Hl2 Hnodup Hlen Hlen' Hlen'' Hpos) "Hspec Hspec' >Hα Hε".
    (* edestruct (restr_inj_fin (S N) (S M) f (le_n_S N M (Nat.lt_le_incl _ _ Hineq)) Hdom) as [g [HgInj HgEq]]. *)
    iDestruct "Hα" as (fs) "(<-&Hα)".
    rewrite pupd_unseal/pupd_def.
    iIntros (σ ρ1 ε_now) "([? Ht]&Hs&Hε2)".
    iDestruct (ghost_map_lookup with "Ht Hα") as %?.
    iDestruct (spec_auth_prog_agree with "[$]Hspec") as "%Hlookup".
    iDestruct (spec_auth_prog_agree with "[$]Hspec'") as "%Hlookup'".
    iDestruct (ghost_map_elem_ne with "Hspec Hspec'") as "%".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    
    destruct ρ1 as [l s].
    assert (j < length l)%nat.
    { by eapply lookup_lt_Some. }
    assert (j' < length l)%nat.
    { by eapply lookup_lt_Some. }
    iApply spec_coupl_rec.
    assert (∃ f: fin (S N) * fin (S N) -> fin (S ((S N * S N - 1))), Bij f) as [f Hbij].
    { cut (card (fin (S N) * fin (S N)) = card (fin (S ((S N * S N - 1))))).
      - rewrite finite_bijective.
        intros [f []].
        exists f. done. 
      - rewrite prod_card !fin_card. lia.
    }
    set (f_inv f) as f'.
    


    (* create fragmented_f*)

    
    (* fragmented f maps 2*length l1 *)
    set (λ (n:nat), match l1!!n with
                  | Some x => x
                  | None =>
                      match l2!!(n-length l1)%nat with
                      | Some x => x
                      | None => (0,0)%nat
                      end
                  end
        ) as fragmented_f'.
    set (λ (n:nat), match (l1++l2)!!n with
                  | Some x => x
                  | None =>(0,0)
                  end
        )%nat as fragmented_f_alt.
    assert (∀ x, fragmented_f' x = fragmented_f_alt x) as Hfrag_eq.
    { intros. rewrite /fragmented_f' /fragmented_f_alt.
      case_match eqn :Heqn.
      - rewrite lookup_app_l; last (eapply lookup_lt_is_Some; by rewrite Heqn).
        by rewrite Heqn.
      - case_match eqn:Heqn'.
        + rewrite lookup_app_r; first by rewrite Heqn'.
          by apply lookup_ge_None_1.
        + rewrite lookup_ge_None_2; first done.
          rewrite app_length.
          apply lookup_ge_None_1 in Heqn'. lia.
    }
    assert (∀ n, (fragmented_f' n).1 < S N /\ (fragmented_f' n).2 < S N)%nat as Hfragmented_f'.
    {
      intros. rewrite /fragmented_f'.
      case_match eqn :Heqn1.
      - eapply Forall_lookup_1 in Hl1; last done. lia.
      - case_match eqn:Heqn2; last (simpl; lia).
        eapply Forall_lookup_1 in Hl2; last done. lia.
    }
    set (λ n,
           if bool_decide (n<2*length l1)%nat then
             fin_to_nat $ f (nat_to_fin $ proj1 (Hfragmented_f' n), nat_to_fin $ proj2 (Hfragmented_f' n))
           else n+S N * S N
        )%nat as fragmented_f.
    assert (Inj (=) (=) fragmented_f).
    { rewrite /fragmented_f.
      intros ??.
      case_bool_decide as Heqn1; case_bool_decide as Heqn2.
      - intros Hinj.
        apply fin_to_nat_inj in Hinj.
        apply Hbij in Hinj.
        inversion Hinj as [[K1 K2]].
        apply (f_equal fin_to_nat) in K1, K2.
        rewrite !fin_to_nat_to_fin in K1 K2.
        assert (fragmented_f' x = fragmented_f' y) as Heq.
        { by apply injective_projections. }
        rewrite !Hfrag_eq in Heq.
        rewrite /fragmented_f_alt in Heq.
        rewrite NoDup_alt in Hnodup.
        pose proof Hnodup x y.
        case_match eqn :C1; last first.
        { apply lookup_ge_None_1 in C1. rewrite app_length in C1. lia. }
        case_match eqn:C2; last first.
        { apply lookup_ge_None_1 in C2. rewrite app_length in C2. lia. }
        subst. naive_solver.
      - pose proof fin_to_nat_lt (f (nat_to_fin (proj1 (Hfragmented_f' x)), nat_to_fin (proj2 (Hfragmented_f' x)))). intros. lia.
      - pose proof fin_to_nat_lt (f (nat_to_fin (proj1 (Hfragmented_f' y)), nat_to_fin (proj2 (Hfragmented_f' y)))). intros. lia.
      - lia.
    }
    
    
    (* f_decompose *)
    set ((λ (n:fin (S (2*length l1 -1))),
            match decide (fin_to_nat n < (S (length l1-1)))%nat with
                  | left p => (1%fin, nat_to_fin p)
                  | _ =>
                      match decide (fin_to_nat n - length l1 < (S (length l1-1)))%nat with
                      | left p => (0%fin, nat_to_fin p)
                      | _ => (0,0)%fin
                      end
                  end
         ): _ -> fin (S 1) * fin (S (length l1 -1))) as f_decompose'.
    assert (Bij f_decompose').
    { split.
      - intros x y. rewrite /f_decompose'.
        repeat case_match; intros Heq; try simplify_eq;
          try apply (f_equal fin_to_nat) in Heq; try rewrite !fin_to_nat_to_fin in Heq; apply fin_to_nat_inj; try done; pose proof fin_to_nat_lt x; pose proof fin_to_nat_lt y; lia.
      - rewrite /f_decompose'.
        intros [x y].
        assert ((1- fin_to_nat x)%nat * length l1 + fin_to_nat y < S (2*length l1 -1))%nat as Hineq.
        { pose proof fin_to_nat_lt x. pose proof fin_to_nat_lt y. simpl in *. destruct (fin_to_nat x) as [|[|]]; simpl; lia. }
        exists (nat_to_fin Hineq).
        rewrite !fin_to_nat_to_fin.
        pose proof fin_to_nat_lt x.
        pose proof fin_to_nat_lt y.
        destruct (fin_to_nat x) as [|[|]] eqn:Heqn.
        + case_match; first lia.
          case_match; last lia.
          f_equal; apply fin_to_nat_inj; try rewrite fin_to_nat_to_fin; last lia. by simpl.
        + case_match; last lia.
          f_equal; apply fin_to_nat_inj; try rewrite fin_to_nat_to_fin; last lia. by simpl.
        + lia.
    }
    set (f_inv f_decompose') as f_decompose.
    assert (Bij f_decompose) by apply f_inv_bij.
    assert (∀ x, x< 2*length l1 -> fragmented_f' (x) ∈ l1 ++ l2)%nat as Hin.
    { intros.
      rewrite Hfrag_eq.
      rewrite /fragmented_f_alt.
      case_match eqn:C.
      -- by eapply elem_of_list_lookup_2.
      -- apply lookup_ge_None_1 in C. rewrite app_length in C. lia.
    }
    
    assert (∀ n m, (∃ b c, fragmented_f (f_decompose (b, c)) = f (n, m)) <-> (fin_to_nat n, fin_to_nat m)∈l1++l2) as Hin'.
    {
      intros n m.
      split. 
      - elim. intros b. elim. intros c. rewrite /fragmented_f.
        pose proof fin_to_nat_lt (f_decompose (b,c)).
        rewrite bool_decide_eq_true_2; last lia.
        intros H'. simplify_eq.
        rewrite !fin_to_nat_to_fin.
        rewrite -surjective_pairing.
        apply Hin. lia.
      - intros Hcase. apply elem_of_list_lookup in Hcase.
        destruct Hcase as [idx Hcase].
        assert (idx < (S (length l1 + (length l1 + 0) - 1)))%nat as Hidx.
        { apply lookup_lt_Some in Hcase. rewrite app_length in Hcase. lia. }
        exists (f_decompose' (nat_to_fin Hidx)).1, (f_decompose' (nat_to_fin Hidx)).2.
        rewrite -surjective_pairing. rewrite /f_decompose. rewrite f_inv_cancel_l.
        rewrite fin_to_nat_to_fin.
        rewrite /fragmented_f.
        rewrite bool_decide_eq_true_2; last lia.
        do 3 f_equal; apply fin_to_nat_inj; rewrite !fin_to_nat_to_fin Hfrag_eq/fragmented_f_alt Hcase//.  
    }
    
    iDestruct (ec_supply_bound with "[$][$]") as %Hle.
    assert (0<=ε)%R as Hε by lra.
    set ε' := mknonnegreal _ Hε.
    set ε_now1 := nnreal_minus ε_now ε' Hle.
    set ε_now2 := (ε_now + ε' * nnreal_nat (2*length l1) / nnreal_nat ((S N) * (S N) - 2*length l1))%NNR.

    set (E2 (ρ:cfg) := if bool_decide (∃ (n m:fin(S N)), (ρ.1)!!j = Some (fill K #(n)) /\
                                                         (ρ.1)!!j'= Some (fill K' #m) /\
                                                         (fin_to_nat n, fin_to_nat m)∈(l1++l2)%nat
                            )
                       then ε_now1 else ε_now2).
    assert (∀ ρ, E2 ρ <= Rmax ε_now1 ε_now2)%R as Hbound.
    { intros ?. rewrite /E2. apply Rmax_Rle. case_bool_decide; by [left| right]. }

    eset (λ x y, ∃ (n m : fin (S N)), y = ([(cfg_to_cfg' (l, s), j); (cfg_to_cfg' (<[j:=fill K #n]> l, s), j');
         (cfg_to_cfg' (<[j':=fill K' #m]> (<[j:=fill K #n]> l), s), length l)],
        (<[j':=fill K' #m]> (<[j:=fill K #n]> l), s))/\
            if bool_decide (∃ b c, fragmented_f (f_decompose (b, c))= f (n, m))
            then (∃ b c, fragmented_f (f_decompose (b, c))= f (n, m) /\ x= (state_upd_tapes <[α:=(1%nat; fs ++ [b])]> σ) )
            else x=σ
           ) as P.
    
    iExists P.
    iExists (dbind (λ m, if bool_decide ((λ x:fin (S N) * fin (S N), (fin_to_nat x.1, fin_to_nat x.2)) (f_inv f m)∈ l1 ++ l2)%nat then state_step σ α else dret σ) (dunifP ((S N) * (S N)-1))).
    iExists (full_info_cons_osch (λ _, dret j) (λ _, full_info_one_step_stutter_osch j')), 0%NNR, (λ p, E2 (p.2)), (Rmax ε_now1 ε_now2).
    repeat iSplit.
      - iPureIntro. apply sch_erasable_dbind_predicate.
      + apply dunif_mass. lia.
      + by eapply state_step_sch_erasable.
      + apply dret_sch_erasable.
    - iPureIntro. naive_solver.
    - iPureIntro. rewrite Rplus_0_l.
      rewrite full_info_cons_osch_lim_exec/dmap.
      rewrite dret_id_left.
      rewrite /step'.
      rewrite Hlookup.
      rewrite fill_not_val//. rewrite fill_dmap//=.
      rewrite head_prim_step_eq/=.
      rewrite !dmap_comp.
      erewrite (dbind_ext_right_strong (dmap _ _) _ (λ x, dmap
    ((λ '(l', ρ'), ((cfg_to_cfg' (l, s), j) :: l', ρ'))
     ∘ (λ ρ' : cfg, ([(cfg_to_cfg' x, j'); (cfg_to_cfg' ρ', length ρ'.1)], ρ'))
     ∘ ((λ '(expr', σ', efs), (<[j':=expr']> x.1 ++ efs, σ'))
        ∘ con_language.fill_lift' (fill K') ∘ λ n : fin (S (Z.to_nat N)), (Val #(fin_to_nat n), s, [])))
    (dunifP (Z.to_nat N)))); last first.
      { intros ? Hd. apply dmap_pos in Hd.
        destruct!/=.
        rewrite app_nil_r.
        rewrite full_info_lift_osch_lim_exec full_info_one_step_stutter_osch_lim_exec.
        rewrite /step'.
        rewrite list_lookup_insert_ne; last done.
        rewrite Hlookup'.
        rewrite fill_not_val//. rewrite fill_dmap//=.
        rewrite head_prim_step_eq/=.
        by rewrite !dmap_comp.
      }
      rewrite Nat2Z.id.
      
      set ((λ w: _*fin (S N), ((λ '(l', ρ'), ((cfg_to_cfg' (l, s), j) :: l', ρ'))
             ∘ (λ ρ' : cfg, ([(cfg_to_cfg' w.1, j'); (cfg_to_cfg' ρ', length ρ'.1)], ρ'))
             ∘ ((λ '(expr', σ', efs), (<[j':=expr']> w.1.1 ++ efs, σ'))
                  ∘ con_language.fill_lift' (fill K')) ) (Val #(fin_to_nat w.2), s, []))) as fn.
      assert ((λ x : cfg,
          dmap
            ((λ '(l', ρ'), ((cfg_to_cfg' (l, s), j) :: l', ρ'))
             ∘ (λ ρ' : cfg, ([(cfg_to_cfg' x, j'); (cfg_to_cfg' ρ', length ρ'.1)], ρ'))
             ∘ ((λ '(expr', σ', efs), (<[j':=expr']> x.1 ++ efs, σ'))
                ∘ con_language.fill_lift' (fill K') ∘ λ n : fin (S N), (Val #(fin_to_nat n), s, []))) 
            (dunifP N)) =
              (λ b, dmap (λ c, fn (b,c)) (dunifP N))
             ) as Hrewrite by done.
      setoid_rewrite Hrewrite.
      erewrite (dbind_dmap_inj_rearrange); last first. 
      { rewrite /fn. intros [][]. simpl.
        rewrite !app_nil_r. rewrite !insert_length.
        intros H'. destruct!/=.
        apply (f_equal (λ x, x!!j)) in H6.
        rewrite !list_lookup_insert in H6; try done.
        apply (f_equal (λ x, x!!j')) in H7.
        rewrite !list_lookup_insert in H7; try by rewrite !insert_length.
        by simplify_eq.
      } 
      { intros ??. simpl. rewrite !app_nil_r.
        intros H'. apply (f_equal (λ x, x.1!!j)) in H'.
        rewrite !list_lookup_insert in H'; try done.
        by simplify_eq. }
      simpl. 
      assert ((dbind (λ a : fin (S N), dmap (λ c : fin (S N), fn (<[j:=fill K #a]> l ++ [], s, c)) (dunifP N))
       (dunifP N))= (dbind
                                  (λ ac,
                                     dret (fn (<[j:=fill K (Val #(fin_to_nat ((f_inv f ac).1)))]> l, s, (f_inv f ac).2))) 
                                  (dunifP (S N * S N -1)))) as Hrewrite'; last rewrite Hrewrite'. 
      { rewrite dunifP_decompose; last done.
        rewrite -dbind_assoc'.
        apply dbind_ext_right.
        intros ?.
        rewrite /dmap.
        rewrite -dbind_assoc'.
        apply dbind_ext_right.
        intros ?.
        rewrite dret_id_left.
        rewrite app_nil_r.
        by rewrite f_inv_cancel_l.
      }
      rewrite dmap_fold.
      rewrite Expval_dmap/=; [|done|]; last first.
      { eapply ex_expval_bounded. intros; split; [apply cond_nonneg|apply Hbound]. }
      rewrite /Expval.
      setoid_rewrite dunif_pmf.
      rewrite SeriesC_scal_l.
      
      set (E2' (m:fin(S (S N * S N -1))) := if bool_decide ((fin_to_nat (f_inv f m).1,fin_to_nat (f_inv f m).2) ∈l1++l2)
                               then ε_now1 else ε_now2).
      erewrite (SeriesC_ext _ E2'); last first.
      { intros . simpl.
        rewrite /E2/E2'.
        rewrite app_nil_r.
        case_bool_decide as H'.
        - destruct H' as [n' [m' [K1 [K2 K3]]]].
          pose proof fin_to_nat_lt n'.
          pose proof fin_to_nat_lt m'.
          rewrite list_lookup_insert_ne in K1; last done.
          rewrite list_lookup_insert in K1; last done.
          rewrite list_lookup_insert in K2; last (by rewrite insert_length).
          simplify_eq. by rewrite bool_decide_eq_true_2.
        - case_bool_decide as Hcontra; last done.
          exfalso.
          apply H'. eexists _, _. repeat split; try done.
          + rewrite list_lookup_insert_ne; last done.
            by apply list_lookup_insert.
          + apply list_lookup_insert. by rewrite insert_length.
      } 
      rewrite /E2'.
      eapply Forall_app_2 in Hl2; last apply Hl1.
      remember (l1++l2) as l3 eqn :Heqnl3.
      assert (∃ (l':list (fin (S N) * fin (S N))), (λ x, (fin_to_nat x.1, fin_to_nat x.2)) <$> l' = l3) as [l' Hl'].
      { clear -Hl2.
        induction l3 as [|a]; first (by eexists []).
        rewrite Forall_cons in Hl2.
        destruct Hl2 as [? Hl2].
        destruct!/=. simpl in *.
        assert (a.1<S N)%nat as Ha1 by lia.
        assert (a.2<S N)%nat as Ha2 by lia.
        apply IHl3 in Hl2 as [l' ?].
        exists ((nat_to_fin Ha1, nat_to_fin Ha2)::l').
        simpl. f_equal; last done.
        destruct a.
        f_equal; by rewrite fin_to_nat_to_fin.
      }
      eset (right_l := (list_to_set$ fin_to_nat <$> (f<$> l')): gset _).
      (* hardcore calculation *)
      eset (diff:= (((list_to_set (fin_to_nat <$> (enum (fin(S (S N * S N -1)))))):gset _ )∖ right_l)).
      erewrite (SeriesC_ext _
                  (λ x : fin (S _), (if bool_decide (fin_to_nat x ∈ right_l) then ε_now1 else 0%R) +
                                      if bool_decide (fin_to_nat x ∈ diff ) then ε_now2 else 0%R
               ))%R; last first.
      
      { intros x.
        case_bool_decide as Hcase.
        - rewrite /diff/right_l.
          rewrite -Hl' in Hcase.
          rewrite elem_of_list_fmap in Hcase.
          destruct Hcase as (y&Hcase1&Hcase).
          inversion Hcase1 as [[Hcase2 Hcase3]].
          apply fin_to_nat_inj in Hcase2, Hcase3.
          assert (f_inv f x=y).
          + rewrite (surjective_pairing y).
            rewrite -Hcase2 -Hcase3.
            by rewrite -surjective_pairing.
          + subst.
            rewrite bool_decide_eq_true_2; last first.
            * rewrite elem_of_list_to_set elem_of_list_fmap.
              eexists (x); split; first done.
              rewrite elem_of_list_fmap.
              exists (f_inv f x).
              rewrite f_inv_cancel_r; by split.
            * rewrite bool_decide_eq_false_2; first lra.
              rewrite not_elem_of_difference.
              right.
              rewrite elem_of_list_to_set elem_of_list_fmap.
              eexists _; split; first done.
              rewrite elem_of_list_fmap.
              eexists _; split; try done.
              by rewrite f_inv_cancel_r.
        - rewrite /diff/right_l.
          rewrite -Hl' in Hcase.
          rewrite elem_of_list_fmap in Hcase.
          rewrite bool_decide_eq_false_2; last first.
          + rewrite elem_of_list_to_set -list_fmap_compose.
            rewrite elem_of_list_fmap.
            intros (?&Heq&?).
            apply Hcase.
            eexists _; split; first done.
            apply fin_to_nat_inj in Heq.
            subst.
            rewrite f_inv_cancel_l//.
          + rewrite bool_decide_eq_true_2; first lra.
            rewrite elem_of_difference.
            split.
            * rewrite elem_of_list_to_set.
              rewrite elem_of_list_fmap.
              eexists _; split; first done.
              apply elem_of_enum.
            * rewrite elem_of_list_to_set -list_fmap_compose.
              rewrite elem_of_list_fmap.
              intros (?&Heq&?).
              apply fin_to_nat_inj in Heq.
              subst.
              apply Hcase.
              eexists _; split; first done.
              by rewrite f_inv_cancel_l.
      } 
      rewrite SeriesC_plus; [|apply ex_seriesC_finite..].
      rewrite !SeriesC_fin_in_set'; last first.
      { rewrite /right_l.
        intros x.
        rewrite elem_of_list_to_set -list_fmap_compose.
        rewrite elem_of_list_fmap.
        intros (y&?&?).
        subst.
        apply (fin_to_nat_lt (f y)).
      }
      { rewrite /diff/right_l.
        intros x.
        rewrite elem_of_difference.
        rewrite elem_of_list_to_set elem_of_list_fmap.
        intros [(y&?&?)].
        subst.
        apply fin_to_nat_lt.
      }
      assert (NoDup l').
      { erewrite <-NoDup_fmap; first by erewrite Hl'.
        intros x ? Heq.
        inversion Heq as [[H7 H8]].
        apply fin_to_nat_inj in H7, H8.
        rewrite (surjective_pairing x) H7 H8.
        by rewrite -surjective_pairing.
      }
      assert (length l' = length l3) as Hlen3.
      { rewrite -Hl'. by rewrite fmap_length. }
      rewrite /right_l.
      rewrite size_list_to_set; last first.
      { apply NoDup_fmap; first apply fin_to_nat_inj.
        apply NoDup_fmap; last done. apply Hbij.
      }
      rewrite !fmap_length.
      rewrite Hlen3.
      rewrite /diff/right_l.
      rewrite size_difference; last first. 
      { intros ?. rewrite !elem_of_list_to_set.
        rewrite -list_fmap_compose.
        rewrite !elem_of_list_fmap.
        intros (y&?&?). subst.
        eexists _; split; first done.
        apply elem_of_enum.
      } 
      rewrite !size_list_to_set; last first.
      { apply NoDup_fmap; first apply fin_to_nat_inj.
        apply NoDup_enum.
      }
      { repeat apply NoDup_fmap.
        - apply fin_to_nat_inj.
        - apply Hbij.
        - done.
      }
      rewrite !fmap_length.
      rewrite Hlen3.
      rewrite length_enum_fin.
      rewrite Heqnl3 app_length.
      rewrite /ε_now1/ε_now2.
      Local Opaque INR.
      simpl.
      rewrite Rmult_plus_distr_r.
      rewrite Rmult_assoc.
      rewrite -plus_n_O Nat.sub_0_r.
      rewrite -Hlen.
      rewrite Rinv_l; last first.
      { apply not_0_INR. lia. }
      rewrite Rmult_1_r.
      rewrite Rmult_minus_distr_r.
      rewrite -Rplus_assoc.
      rewrite -!Rplus_minus_swap.
      rewrite Rplus_minus_r.
      rewrite minus_INR; last lia.
      rewrite Rmult_minus_distr_l.
      rewrite Rplus_minus.
      rewrite -Rmult_assoc.
      rewrite !(Rmult_comm (/ _)).
      rewrite Rmult_assoc.
      rewrite Rinv_l; first lra.
      apply not_0_INR; lia.
      Local Transparent INR.
    - iPureIntro.
      (* unfold definitions *)
      rewrite full_info_cons_osch_lim_exec/dmap.
      rewrite dret_id_left.
      rewrite /step'.
      rewrite Hlookup.
      rewrite fill_not_val//. rewrite fill_dmap//=.
      rewrite head_prim_step_eq/=.
      rewrite !dmap_comp.
      erewrite (dbind_ext_right_strong (dmap _ _) _ (λ x, dmap
    ((λ '(l', ρ'), ((cfg_to_cfg' (l, s), j) :: l', ρ'))
     ∘ (λ ρ' : cfg, ([(cfg_to_cfg' x, j'); (cfg_to_cfg' ρ', length ρ'.1)], ρ'))
     ∘ ((λ '(expr', σ', efs), (<[j':=expr']> x.1 ++ efs, σ'))
        ∘ con_language.fill_lift' (fill K') ∘ λ n : fin (S (Z.to_nat N)), (Val #(fin_to_nat n), s, [])))
    (dunifP (Z.to_nat N)))); last first.
      { intros ? Hd. apply dmap_pos in Hd.
        destruct!/=.
        rewrite app_nil_r.
        rewrite full_info_lift_osch_lim_exec full_info_one_step_stutter_osch_lim_exec.
        rewrite /step'.
        rewrite list_lookup_insert_ne; last done.
        rewrite Hlookup'.
        rewrite fill_not_val//. rewrite fill_dmap//=.
        rewrite head_prim_step_eq/=.
        by rewrite !dmap_comp.
      }
      rewrite Nat2Z.id.
      
      set ((λ w: _*fin (S N), ((λ '(l', ρ'), ((cfg_to_cfg' (l, s), j) :: l', ρ'))
             ∘ (λ ρ' : cfg, ([(cfg_to_cfg' w.1, j'); (cfg_to_cfg' ρ', length ρ'.1)], ρ'))
             ∘ ((λ '(expr', σ', efs), (<[j':=expr']> w.1.1 ++ efs, σ'))
                  ∘ con_language.fill_lift' (fill K')) ) (Val #(fin_to_nat w.2), s, []))) as fn.
      assert ((λ x : cfg,
          dmap
            ((λ '(l', ρ'), ((cfg_to_cfg' (l, s), j) :: l', ρ'))
             ∘ (λ ρ' : cfg, ([(cfg_to_cfg' x, j'); (cfg_to_cfg' ρ', length ρ'.1)], ρ'))
             ∘ ((λ '(expr', σ', efs), (<[j':=expr']> x.1 ++ efs, σ'))
                ∘ con_language.fill_lift' (fill K') ∘ λ n : fin (S N), (Val #(fin_to_nat n), s, []))) 
            (dunifP N)) =
              (λ b, dmap (λ c, fn (b,c)) (dunifP N))
             ) as Hrewrite by done.
      setoid_rewrite Hrewrite.
      erewrite (dbind_dmap_inj_rearrange); last first. 
      { rewrite /fn. intros [][]. simpl.
        rewrite !app_nil_r. rewrite !insert_length.
        intros H'. destruct!/=.
        apply (f_equal (λ x, x!!j)) in H6.
        rewrite !list_lookup_insert in H6; try done.
        apply (f_equal (λ x, x!!j')) in H7.
        rewrite !list_lookup_insert in H7; try by rewrite !insert_length.
        by simplify_eq.
      } 
      { intros ??. simpl. rewrite !app_nil_r.
        intros H'. apply (f_equal (λ x, x.1!!j)) in H'.
        rewrite !list_lookup_insert in H'; try done.
        by simplify_eq. }
      simpl. 
      assert ((dbind (λ a : fin (S N), dmap (λ c : fin (S N), fn (<[j:=fill K #a]> l ++ [], s, c)) (dunifP N))
       (dunifP N))= (dbind
                                  (λ ac,
                                     let '(a, c) := f_inv f ac in
                                     dret (fn (<[j:=fill K (Val #(fin_to_nat a))]> l, s, c))) 
                                  (dunifP (S N * S N -1)))) as Hrewrite'; last rewrite Hrewrite'. 
      { rewrite dunifP_decompose; last done.
        rewrite -dbind_assoc'.
        apply dbind_ext_right.
        intros ?.
        rewrite /dmap.
        rewrite -dbind_assoc'.
        apply dbind_ext_right.
        intros ?.
        rewrite dret_id_left.
        rewrite app_nil_r.
        by rewrite f_inv_cancel_l.
      }
      simpl.
      rewrite {2}(dunif_fragmented _ (2*length l1 -1)%nat fragmented_f).
      { rewrite /fragmented_f.
        intros. simpl in *. rewrite bool_decide_eq_true_2; last lia.
        apply fin_to_nat_lt.
      } 
      2:{ lia. }
      intros Hbound'.
      rewrite -!dbind_assoc'.
      simpl.
      replace 0%R with (0+0)%R by lra.
      eapply ARcoupl_dbind; [done|done| |apply ARcoupl_eq].
      intros ? ac ->.
      case_bool_decide as Heqn1.
      + (* we step on an accepted value *)
        rewrite bool_decide_eq_true_2; last first.
        { rewrite /fragmented_f.
          apply elem_of_list_lookup in Heqn1 as Heqn2. 
          destruct Heqn2 as [idx Heqn2].
          assert (idx < (S (length l1 + (length l1 + 0) - 1)))%nat as Hidx.
          { cut (idx < length (l1++l2))%nat.
            - rewrite app_length. lia.
            - eapply lookup_lt_is_Some_1. by rewrite Heqn2. }
          exists (nat_to_fin Hidx).
          rewrite bool_decide_eq_true_2; last first.
          - pose proof fin_to_nat_lt (nat_to_fin Hidx). lia.
          - f_equal.
            apply (f_inv_bij f).
            rewrite f_inv_cancel_l.
            destruct (f_inv f ac) eqn:He.
            f_equal.
            + apply fin_to_nat_inj.
              rewrite fin_to_nat_to_fin.
              rewrite Hfrag_eq.
              rewrite /fragmented_f_alt.
              rewrite fin_to_nat_to_fin Heqn2.
              simpl.
              f_equal. by rewrite He.
            + apply fin_to_nat_inj.
              rewrite fin_to_nat_to_fin.
              rewrite Hfrag_eq.
              rewrite /fragmented_f_alt.
              rewrite fin_to_nat_to_fin Heqn2.
              simpl.
              f_equal. by rewrite He.
        }
        erewrite (dunifP_decompose ); [|by apply f_inv_bij|]; last lia.
        erewrite state_step_unfold; last done.
        rewrite /dmap -!dbind_assoc'.
        replace 0%R with (0+0) by lra.
        eapply ARcoupl_dbind; [done|done| |apply ARcoupl_eq].
        intros ? b ->.
        rewrite <-(dbind_const (dunifP (length l1 -1)%nat) (dret _)); last apply dunifP_mass.
        rewrite -!dbind_assoc'.
        replace 0%R with (0+0) by lra.
        eapply ARcoupl_dbind; [done|done| |apply ARcoupl_eq].
        intros ? c ->.
        rewrite !dret_id_left.
        case_match eqn :Heq.
        apply (f_equal f ) in Heq.
        rewrite f_inv_cancel_r in Heq.
        apply (f_equal fin_to_nat) in Heq.
        rewrite fin_to_nat_to_fin in Heq.
        rewrite /fn/=.
        rewrite app_nil_r !insert_length.
        apply ARcoupl_dret; first done.
        rewrite /P.
        eexists _, _.
        split; first done.
        rewrite bool_decide_eq_true_2; last naive_solver.
        eexists _, _; naive_solver.
      + (* we step on a rejected value*)
        rewrite bool_decide_eq_false_2; last first.
        { intros [x Hx]. apply Heqn1.
          rewrite /fragmented_f in Hx.
          pose proof fin_to_nat_lt x.
          case_bool_decide; last lia.
          apply fin_to_nat_inj in Hx. subst.
          rewrite !f_inv_cancel_l !fin_to_nat_to_fin. 
          rewrite -surjective_pairing.
          apply Hin.
          lia.
        }
        rewrite dret_id_left.
        case_match eqn:Heq. simpl in *.
        apply (f_equal f ) in Heq.
        rewrite f_inv_cancel_r in Heq.
        subst.
        rewrite /fn/= app_nil_r !insert_length.
        apply ARcoupl_dret; first done. 
        rewrite /P.
        eexists _, _; split; first done.
        rewrite bool_decide_eq_false_2; first done.
        rewrite /fragmented_f.
        intros (b&c&?).
        destruct!/=.
        case_bool_decide.
        * simplify_eq.
          rewrite !fin_to_nat_to_fin in Heqn1.
          rewrite Hfrag_eq -surjective_pairing in Heqn1.
          rewrite /fragmented_f_alt in Heqn1.
          apply Heqn1.
          case_match eqn:C.
          -- by eapply elem_of_list_lookup_2.
          -- apply lookup_ge_None_1 in C. rewrite app_length in C. lia.
        * pose proof fin_to_nat_lt (f_decompose (b,c)); lia.
      
    - iPureIntro.
      rewrite /P.
      intros ????? (a&c&H6&A1) (a0&c0&H7&A2).
      destruct!/=.
      apply (f_equal (λ x, x!!j)) in H6.
      apply (f_equal (λ x, x!!j')) in H7.
      rewrite !list_lookup_insert in H6, H7; try rewrite insert_length; try lia.
      simplify_eq.
      case_bool_decide as T1; destruct!/=.
      + split; last done.
        rewrite -H8 in H6. by simplify_eq.
      + naive_solver.
    - simpl. rewrite /P. iIntros (????).
      destruct!/=.
      case_bool_decide as Hcase.
      + (* accepted *)
        destruct H8 as (b&c&H8).
        destruct!/=.
        rewrite -Hcase in H6. simplify_eq.
        iMod (spec_update_prog with "[$][$Hspec]") as "[HK Hs]".
        iMod (spec_update_prog with "[$][$Hspec']") as "[HK ?]".
        iMod (ghost_map_update with "[$]Hα") as "(?&?)".
        replace (ε_now) with (ε' + ε_now1)%NNR; last first.
        { apply nnreal_ext. simpl. lra. }
        iMod (ec_supply_decrease with "[$] [$]") as (?? ? ?) "H".
        replace (E2 _) with (ε_now1); last first.
        { rewrite /E2. subst.
          rewrite bool_decide_eq_true_2; first done.
          pose proof fin_to_nat_lt b0.
          pose proof fin_to_nat_lt c0.
          rewrite /fragmented_f in Hcase.
          pose proof fin_to_nat_lt (f_decompose (b0, c0)).
          case_bool_decide; last lia.
          simplify_eq.
          rewrite !fin_to_nat_to_fin.
          eexists _, _.
          rewrite list_lookup_insert_ne; last done.
          rewrite list_lookup_insert; last lia.
          erewrite fin_to_nat_to_fin.
          split; first done.
          rewrite list_lookup_insert; last (rewrite insert_length; lia).
          erewrite fin_to_nat_to_fin.
          split; first done.
          rewrite -surjective_pairing.
          apply Hin. lia.
        }
        iModIntro. 
        iApply spec_coupl_ret.
        iMod "Hclose'" as "_".
        iFrame.
        iModIntro.
        iSplitL "H".
        * iApply ec_supply_eq; last done.
          simplify_eq/=. lra.
        * repeat iSplit.
          -- iPureIntro. apply Nat.lt_succ_r. apply fin_to_nat_lt.
          -- iPureIntro. apply Nat.lt_succ_r. apply fin_to_nat_lt.
          -- rewrite /fragmented_f in Hcase.
             rewrite bool_decide_eq_true_2 in Hcase; last first.
             { pose proof fin_to_nat_lt (f_decompose (b0, c0)). lia. }
             simplify_eq.
             rewrite !fin_to_nat_to_fin.
             rewrite -surjective_pairing.
             rewrite Hfrag_eq.
             case_bool_decide as K1.
             ++ rewrite /fragmented_f_alt/f_decompose in K1.
                rewrite /f_inv in K1.
                pose proof epsilon_correct _  (surj f_decompose' (b0, c0)) as Hep.
                simpl in *.
                remember (epsilon(surj f_decompose' (b0, c0))) as x.
                rewrite /f_decompose' in Hep.
                case_match.
                { simplify_eq. iFrame. by rewrite fmap_app. }
                rewrite lookup_app_r in K1; last lia.
                destruct (l2 !!(x-length l1)%nat) eqn:Hcontra; last first.
                { apply lookup_ge_None_1 in Hcontra. pose proof fin_to_nat_lt x. lia. }
                exfalso. rewrite NoDup_app in Hnodup. unfold not in Hnodup.
                destruct Hnodup as [?[Hnodup]].
                eapply Hnodup; first done.
                eapply elem_of_list_lookup. naive_solver.
             ++ case_bool_decide as K2.
                ** rewrite /fragmented_f_alt/f_decompose in K2.
                   rewrite /f_inv in K2.
                   pose proof epsilon_correct _  (surj f_decompose' (b0, c0)) as Hep.
                   simpl in *.
                   remember (epsilon(surj f_decompose' (b0, c0))) as x.
                   rewrite /f_decompose' in Hep.
                   case_match; last first.
                   { case_match; simplify_eq; iFrame; rewrite fmap_app//. }
                   simplify_eq.
                   exfalso.
                   apply K1.
                   rewrite /f_decompose/f_inv.
                   rewrite /fragmented_f_alt.
                   rewrite lookup_app_l; last lia.
                   destruct (l1 !! _) eqn:Heqn.
                   { rewrite elem_of_list_lookup. naive_solver. }
                   exfalso.
                   apply lookup_ge_None_1 in Heqn. lia.
                ** exfalso.
                   assert (fragmented_f_alt (f_decompose (b0, c0))∉l1++l2) as Hnotin.
                   { rewrite elem_of_app. intros []; naive_solver. }
                   rewrite /fragmented_f_alt in Hnotin.
                   case_match eqn :H7.
                   --- apply Hnotin. eapply elem_of_list_lookup. naive_solver.
                   --- apply lookup_ge_None_1 in H7. pose proof fin_to_nat_lt (f_decompose (b0, c0)).
                       rewrite app_length in H7. lia.
      + iMod (spec_update_prog with "[$][$Hspec]") as "[HK Hs]".
        iMod (spec_update_prog with "[$][$Hspec']") as "[HK ?]".
        replace (E2 _) with (ε_now2); last first.
        { rewrite /E2. subst.
          rewrite bool_decide_eq_false_2; first done.
          rewrite /fragmented_f in Hcase.
          intros (x&y&Hcase1&Hcase2&Hcase3).
          rewrite list_lookup_insert_ne in Hcase1; last done.
          rewrite list_lookup_insert in Hcase1; last lia.
          simplify_eq.
          rewrite list_lookup_insert in Hcase2; last (rewrite insert_length; lia).
          simplify_eq.
          apply Hcase.
          apply elem_of_list_lookup in Hcase3.
          destruct Hcase3 as [idx Hcase3].
          assert (idx < (S (length l1 + (length l1 + 0) - 1)))%nat as Hidx.
          { apply lookup_lt_Some in Hcase3. rewrite app_length in Hcase3. lia. }
          exists (f_decompose' (nat_to_fin Hidx)).1, (f_decompose' (nat_to_fin Hidx)).2.
          rewrite -surjective_pairing. rewrite /f_decompose. rewrite f_inv_cancel_l.
          rewrite fin_to_nat_to_fin.
          rewrite bool_decide_eq_true_2; last lia.
          do 3 f_equal; apply fin_to_nat_inj; rewrite !fin_to_nat_to_fin Hfrag_eq/fragmented_f_alt Hcase3//.
        }
        subst.
        destruct (Rle_or_lt 1 ε_now2).
        { iModIntro. by iApply spec_coupl_ret_err_ge_1. }
        iModIntro.
        iApply spec_coupl_ret.
        iFrame.
        iMod (ec_supply_increase with "[$]") as "[$ Herr']".
        { by eapply Rle_lt_trans. }
        iCombine "Hε Herr'" as "Herr".
        iMod "Hclose'".
        iModIntro.
        iSplit.
        { iPureIntro. apply Nat.lt_succ_r. apply fin_to_nat_lt. }
        iSplit.
        { iPureIntro. apply Nat.lt_succ_r. apply fin_to_nat_lt. }
        rewrite bool_decide_eq_false_2; last first. 
        { rewrite Hin' in Hcase. intros Hcontra. apply Hcase. rewrite elem_of_app. by left. }
        rewrite bool_decide_eq_false_2; last first.
        { rewrite Hin' in Hcase. intros Hcontra. apply Hcase. rewrite elem_of_app. by right. }
        iFrame. iSplit; try done. 
        iApply (ec_eq with "[$]").
        simpl.
        assert (ε*1+ ε * (length l1 + (length l1 + 0))%nat * / (S (N + N * S N) - (length l1 + (length l1 + 0)))%nat =ε *
                                                                                                                    ((N + 1) * (N + 1))%nat / ((N + 1) * (N + 1) - (length l1 + (length l1 + 0)))%nat); try lra.
        rewrite Rmult_assoc.
        rewrite -Rmult_plus_distr_l.
        rewrite -Rmult_div_assoc.
        f_equal. 
        simpl.
        erewrite <-(Rinv_r (S (N + N * S N) - (length l1 + (length l1 + 0)))%nat); last first.
        { apply not_0_INR; lia. }
        rewrite -Rdiv_def.
        rewrite -Rdiv_plus_distr.
        rewrite minus_INR; last lia.
        rewrite -Rplus_minus_swap.
        rewrite Rplus_minus_r.
        f_equal.
        * f_equal. lia.
        * rewrite -minus_INR; last lia. f_equal. lia.
          Unshelve.
          -- rewrite Hfrag_eq. rewrite /fragmented_f_alt.
             case_match eqn:Hcase; last (simpl;lia).
             eapply Forall_app_2 in Hl2; last apply Hl1.
             eapply Forall_lookup_1 in Hl2; last done.
             lia.
          -- rewrite Hfrag_eq. rewrite /fragmented_f_alt.
             case_match eqn:Hcase; last (simpl;lia).
             eapply Forall_app_2 in Hl2; last apply Hl1.
             eapply Forall_lookup_1 in Hl2; last done.
             lia.
  Qed.

  
  (** * Lemmas for associativity of probabilitic choice *)
  Lemma pupd_couple_associativity {p q r s x y:nat} α β ns ns' j K j' K' E:
    (p<=(q+1))%nat ->
    (r<=(s+1))%nat->
    (x=(q+1)*(s+1)-1)%nat ->
    (y=(q+1)*(s+1)-p*r-1)%nat ->
    ▷ α ↪N (s; ns) -∗
    ▷ β ↪N (q; ns') -∗
    j ⤇ fill K (rand #x) -∗
    j' ⤇ fill K' (rand #y) -∗
    pupd E E (∃ resl resl' resr resr',
          ⌜(resl <= s)%nat⌝ ∗ ⌜(resl'<=q)%nat⌝ ∗ ⌜(resr <= (q+1)*(s+1)-1)%nat⌝ ∗ ⌜(resr'<=(q+1)*(s+1)-p*r-1)%nat⌝ ∗
          α ↪N (s;ns++[resl])∗ β↪N (q;ns'++[resl']) ∗ j⤇fill K (#resr) ∗ j' ⤇ fill K' (#resr') ∗
          ⌜if bool_decide(resr<p*r)%nat then (resl' <p /\ resl<r)%nat
            else if bool_decide(resr'<r*(q+1-p))%nat then (resl' >=p /\ resl<r)%nat
                 else (resl>=r)%nat⌝
      ).
  Proof.
    iIntros (Hpq Hrs -> -> ) ">Hα >Hβ Hspec1 Hspec2".
    destruct (decide (p=q+1/\r=s+1))%nat as [[->->]|Hneq].
    { iMod (pupd_rand with "[$]") as "(%&?&%)".
      iMod (pupd_rand with "[$]") as "(%&?&%)".
      iMod (pupd_presample with "[$Hα]") as "(%&?&%)".
      iMod (pupd_presample with "[$Hβ]") as "(%&?&%)".
      iFrame.
      iModIntro.
      repeat iSplit; try done.
      iPureIntro. 
      rewrite bool_decide_eq_true_2; last lia.
      lia.
    }
    assert (0<(q+1)*(s+1)-p*r)%nat.
    { apply lt_minus_O_lt.
      apply not_and_or_not in Hneq as [|].
      - apply Nat.le_lt_trans with (p*(s+1))%nat.
        + apply Nat.mul_le_mono; lia.
        + apply Nat.mul_lt_mono_pos_r; lia.
      - apply Nat.le_lt_trans with ((q+1)*r)%nat.
        + apply Nat.mul_le_mono; lia.
        + apply Nat.mul_lt_mono_pos_l; lia.
    }
    iDestruct "Hα" as (fs) "(<-&Hα)".
    iDestruct "Hβ" as (fs') "(<-&Hβ)".
    rewrite pupd_unseal/pupd_def.
    iIntros (σ ρ1 ε_now) "([? Ht]&Hs&Hε2)".
    iDestruct (ghost_map_lookup with "Ht Hα") as %?.
    iDestruct (ghost_map_lookup with "Ht Hβ") as %?.
    iDestruct (spec_auth_prog_agree with "[$][$Hspec1]") as "%Hlookup1".
    iDestruct (spec_auth_prog_agree with "[$][$Hspec2]") as "%Hlookup2".
    iDestruct (ghost_map_elem_ne with "Hα Hβ") as "%".
    iDestruct (ghost_map_elem_ne with "Hspec1 Hspec2") as "%".
    destruct ρ1 as [l σ_spec].
    assert (j < length l)%nat.
    { by eapply lookup_lt_Some. }
    assert (j' < length l)%nat.
    { by eapply lookup_lt_Some. }
    iApply spec_coupl_rec.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    pose (λ (n:nat), if (bool_decide (n<S((q+1)*(s+1)-p*r-1))%nat)
                   then
                     p*r+n
                   else n+(q+1)*(s+1))%nat as f_frag.
    assert (forall m, m<(q+1)*(s+1)-p*r -> p*r<=f_frag m)%nat as Hfragineq.
    { intros.
      rewrite /f_frag.
      rewrite bool_decide_eq_true_2; lia. }
    assert (Inj (=) (=) f_frag) as Hinj.
    {
      rewrite /f_frag.
      intros x y.
      repeat case_bool_decide; lia.
    }
    set ((λ x, state_upd_tapes <[β:=(q; fs' ++ [x.2])]> x.1)) as fn.
    pose (λ (n:fin (S s)) (m:fin (S q)),
            if bool_decide (fin_to_nat n<r /\ fin_to_nat m<p)%nat
            then n*p+m
            else if bool_decide (fin_to_nat n<r)%nat
                 then let m' :=fin_to_nat m- p in
                     p*r+ m'*r +n
                 else
                   let n':=n-r in
                  r*(q+1)+ n'*(q+1) + m
         )%nat as f'.
    assert (∀ n m, f' n m < S ((q+1)*(s+1)-1))%nat as Hf'.
    { intros n m.
      rewrite /f'. replace (S _) with ((q+1)*(s+1))%nat by lia.
      case_bool_decide.
      - apply Nat.lt_le_trans with (n*p+p)%nat; first lia.
        trans (p*(n+1))%nat; first lia.
        apply Nat.mul_le_mono; lia.
      - case_bool_decide.
        + apply Nat.lt_le_trans with ((p*r)+(m-p)*r+r)%nat; first lia.
          trans (p*r+(m-p+1)*r)%nat; first lia.
          rewrite -Nat.mul_add_distr_r.
          replace (_+(_-_+_))%nat with (m+1)%nat by lia.
          pose proof fin_to_nat_lt m. 
          apply Nat.mul_le_mono; lia.
        + pose proof fin_to_nat_lt n.
          pose proof fin_to_nat_lt m.
          (* rewrite Nat.mul_sub_distr_l. *)
          (* rewrite (Nat.add_sub_assoc (r*_)%nat) ; last first. *)
          (* { apply Nat.mul_le_mono; lia. } *)
          rewrite -Nat.mul_add_distr_r.
          replace (_+(n-_))%nat with (fin_to_nat n) by lia.
          apply Nat.le_lt_trans with (n*(q+1)+m)%nat; first lia.
          apply Nat.lt_le_trans with ((n+1)*(q+1))%nat; first lia.
          rewrite Nat.mul_comm.
          apply Nat.mul_le_mono; lia.
    }
    pose (λ '(n,m), nat_to_fin (Hf' n m)) as f.
    assert (Bij f) as Hbij.
    { rewrite /f. split.
      - intros [x1 y1][x2 y2].
        intros H'.
        apply (f_equal fin_to_nat) in H'.
        rewrite !fin_to_nat_to_fin in H'.
        rewrite /f' in H'.
        repeat case_bool_decide.
        + apply Nat.mul_split_l in H'; try lia. by destruct!/=.
        + assert (x1*p+y1<p*r)%nat; last lia.
          apply Nat.lt_le_trans with (x1*p+p)%nat; first lia.
          trans (p*(x1+1))%nat; first lia.
          apply Nat.mul_le_mono; lia.
        + assert (x1*p+y1<r*(q+1))%nat; last lia.
          apply Nat.lt_le_trans with (x1*p+p)%nat; first lia.
          trans ((x1+1)*p)%nat; first lia.
          apply Nat.mul_le_mono; lia.
        + assert (x2*p+y2<p*r)%nat; last lia.
          apply Nat.lt_le_trans with (x2*p+p)%nat; first lia.
          trans (p*(x2+1))%nat; first lia.
          apply Nat.mul_le_mono; lia.
        + assert (((y1 - p) * r + x1)%nat = ((y2 - p) * r + x2)%nat) as H'' by lia.
          apply Nat.mul_split_l in H''; try lia.
          destruct!/=.
          f_equal; try lia.
          pose proof fin_to_nat_lt y1.
          pose proof fin_to_nat_lt y2.
          apply fin_to_nat_inj. lia.
        + assert ((p * r + (y1 - p) * r + x1 < r*(q+1))%nat); last lia.
          rewrite -Nat.mul_add_distr_r.
          pose proof fin_to_nat_lt y1.
          rewrite -Nat.le_add_sub; last lia.
          apply Nat.lt_le_trans with (r*y1+r)%nat; first lia.
          trans (r*(y1+1))%nat; first lia.
          apply Nat.mul_le_mono; lia.
        + assert (x2*p+y2<r*(q+1))%nat; last lia.
          apply Nat.lt_le_trans with (x2*p+p)%nat; first lia.
          trans ((x2+1)*p)%nat; first lia.
          apply Nat.mul_le_mono; lia.
        + assert ((p * r + (y2 - p) * r + x2<r*(q+1))%nat); last lia.
          rewrite -Nat.mul_add_distr_r.
          pose proof fin_to_nat_lt y2.
          rewrite -Nat.le_add_sub; last lia.
          apply Nat.lt_le_trans with (r*y2+r)%nat; first lia.
          trans (r*(y2+1))%nat; first lia.
          apply Nat.mul_le_mono; lia.
        + assert (((x1 - r) * (q + 1 ) + (y1))%nat =
                  ((x2 - r) * (q + 1 ) + (y2))%nat) as L; first lia.
          pose proof fin_to_nat_lt x1.
          pose proof fin_to_nat_lt y1.
          pose proof fin_to_nat_lt x2.
          pose proof fin_to_nat_lt y2.
          apply Nat.mul_split_l in L; try lia.
          destruct!/=. f_equal; apply fin_to_nat_inj; lia.
      - intros x.
        pose proof fin_to_nat_lt x.
        destruct (decide (x<p*r)%nat).
        + assert (fin_to_nat x/p<S s)%nat as K1.
          { apply Nat.Div0.div_lt_upper_bound.
            eapply Nat.lt_le_trans; first exact.
            apply Nat.mul_le_mono; lia.
          }
          assert (fin_to_nat x`mod` p<S q)%nat as K2.
          { eapply Nat.lt_le_trans; first apply Nat.mod_upper_bound; lia. }
          exists (nat_to_fin K1, nat_to_fin K2).
          apply fin_to_nat_inj.
          rewrite !fin_to_nat_to_fin.
          rewrite /f'.
          rewrite !fin_to_nat_to_fin.
          rewrite bool_decide_eq_true_2.
          * rewrite {3}(Nat.div_mod_eq x p). lia.
          * split; last (apply Nat.mod_upper_bound; lia).
            apply Nat.Div0.div_lt_upper_bound. lia.
        + destruct (decide (x<r*(q+1)))%nat.
          * assert ((fin_to_nat x-p*r)`mod`r<S s)%nat as K1.
            { eapply Nat.lt_le_trans; first apply Nat.mod_upper_bound; lia. }
            assert ((fin_to_nat x-p*r)/r+p<S q)%nat as K2.
            { assert (((x - p * r) `div` r < (q+1-p))%nat); last lia.
              apply Nat.Div0.div_lt_upper_bound.
              assert (x - p * r +p*r< r * (q + 1 - p)+p*r)%nat; last lia.
              rewrite Nat.sub_add; last lia.
              assert (x<r*(q+1-p+p))%nat; last lia.
              rewrite Nat.sub_add; lia.
            }
            eexists (nat_to_fin K1, nat_to_fin K2).
            apply fin_to_nat_inj.
            rewrite fin_to_nat_to_fin /f' !fin_to_nat_to_fin.
            rewrite bool_decide_eq_false_2; last lia.
            rewrite bool_decide_eq_true_2; last (apply Nat.mod_upper_bound; lia).
            rewrite (Nat.mul_comm (_-_)%nat).
            rewrite Nat.add_sub.
            rewrite -Nat.add_assoc.
            rewrite -Nat.div_mod_eq.
            lia.
          * assert ((fin_to_nat x-r*(q+1))/(q+1)+r<S s)%nat as K1.
            { assert ((x - r * (q + 1)) `div` (q + 1)  < (s+1-r))%nat; last lia.
              apply Nat.Div0.div_lt_upper_bound.
              assert (x - r * (q + 1) +r*(q+1)< (q + 1) * (s + 1 - r) +(q+1)*r)%nat; last lia.
              rewrite Nat.sub_add; last lia.
              assert (x<(q+1)*(s+1-r+r))%nat; last lia.
              rewrite Nat.sub_add; lia. }
            assert ((fin_to_nat x-r*(q+1))`mod`(q+1)<S q)%nat as K2.
            { assert ((x - r * (q + 1)) `mod` (q + 1)  < q+1)%nat; last lia.
              apply Nat.mod_upper_bound; lia.
            }
            eexists (nat_to_fin K1, nat_to_fin K2).
            apply fin_to_nat_inj.
            rewrite fin_to_nat_to_fin /f' !fin_to_nat_to_fin.
            rewrite bool_decide_eq_false_2; last lia.
            rewrite bool_decide_eq_false_2; last lia.
            rewrite Nat.add_sub.
            rewrite (Nat.mul_comm (_/_)%nat).
            rewrite -Nat.add_assoc.
            rewrite -Nat.div_mod_eq. lia.
    }
    iExists (λ x x', ∃ (qs : fin _), if bool_decide (∃ (m:fin (_)), f_frag m = qs)
                       then ∃ (a:fin (S s)) c, x= (fn (state_upd_tapes (<[α:=(s; fs++[a]):tape]> ) σ, c)) /\ ∃ y, f_frag y= (fin_to_nat (f (a, c))) /\
                                   x' = ([(cfg_to_cfg' (l, σ_spec), j); (cfg_to_cfg' (<[j:=fill K #(fin_to_nat (qs))]> l, σ_spec), j');
                                         (cfg_to_cfg' (<[j':=fill K' #(y)]> (<[j:=fill K #(fin_to_nat (qs))]> l), σ_spec),
                                            length l)],
                                          (<[j':=fill K' #(y)]> (<[j:=fill K #(fin_to_nat ( qs))]> l), σ_spec)) 
                       else 
        (∃ a c (y:fin (S ((q + 1) * (s + 1) - p * r - 1))), qs = f (a,c) /\ x=(fn (state_upd_tapes <[α:=(s; fs ++ [a]):tape]> σ, c)) /\
        x' = ([(cfg_to_cfg' (l, σ_spec), j); (cfg_to_cfg' (<[j:=fill K #(qs)]> l, σ_spec), j');
         (cfg_to_cfg' (<[j':=fill K' #y]> (<[j:=fill K #(qs)]> l), σ_spec), length l)],
        (<[j':=fill K' #y]> (<[j:=fill K #(qs)]> l), σ_spec)))
        ).
    iExists (dbind (λ σ', state_step σ' β) (state_step σ α)).
    iExists (full_info_cons_osch (λ _, dret j) (λ _, full_info_one_step_stutter_osch j')).
    iExists 0%NNR, (λ _, ε_now), ε_now.

    
    
    repeat iSplit.
    - iPureIntro. apply sch_erasable_dbind; first eapply state_step_sch_erasable; first done.
      intros ?. rewrite {1}/state_step. rewrite bool_decide_eq_true_2; last by rewrite elem_of_dom.
      setoid_rewrite lookup_total_correct at 1; last done.
      simpl.
      intros Hpos'.
      apply dmap_pos in Hpos'. destruct Hpos' as (?&->&Hpos').
      eapply state_step_sch_erasable.
      simpl. by rewrite lookup_insert_ne.
    - done.
    - rewrite Expval_const; last done.
      iPureIntro.
      rewrite Rplus_0_l.
      trans (ε_now*1); last (simpl; lra).
      by apply Rmult_le_compat.
    - iPureIntro.
      rewrite /state_step.
      rewrite bool_decide_eq_true_2; last by rewrite elem_of_dom.
      setoid_rewrite lookup_total_correct at 2; last done.
      erewrite (dbind_ext_right_strong _ _ (λ σ', dmap (λ n : fin (S q), state_upd_tapes <[β := (q; fs' ++[n])]> σ') (dunifP q))); last first.
      { intros σ' Hσ'.
        apply dmap_pos in Hσ'.
        destruct Hσ' as (?&->&Hσ').
        rewrite bool_decide_eq_true_2; last first.
        { rewrite elem_of_dom. 
          simpl.
          rewrite lookup_insert_ne; naive_solver.
        }
        setoid_rewrite lookup_total_correct; last by rewrite lookup_insert_ne.
        done. 
      }
      assert ((dbind (λ σ', dmap (λ n : fin (S q), state_upd_tapes <[β:=(q; fs' ++ [n])]> σ') (dunifP q))
       (dmap (λ n : fin (S s), state_upd_tapes <[α:=(s; fs ++ [n])]> σ) (dunifP s))) = (dbind (λ σ', dmap (λ n : fin (S q), fn (σ', n)) (dunifP q))
                                                                                          (dmap (λ n : fin (S s), state_upd_tapes <[α:=(s; fs ++ [n])]> σ) (dunifP s)))) as -> by done.
      erewrite (dbind_dmap_inj_rearrange); last first. 
      { rewrite /fn. intros [][].
        intros H'.
        apply state_upd_tapes_same' in H' as H''.
        rewrite !(upd_diff_tape_comm _ _ β) in H'; try done.
        apply state_upd_tapes_same' in H' as H'''.
        simpl in *. by simplify_eq. }
      { intros ??. apply state_upd_tapes_same'. }
      rewrite /dmap.
      assert ((dbind
       (λ a : fin (S s),
          dbind (λ a0 : fin (S q), dret (fn (state_upd_tapes <[α:=(s; fs ++ [a])]> σ, a0)))
            (dunifP q)) (dunifP s)) =
              (dbind  (λ ac,
                         let '(a, c) := f_inv f ac in
                         dret (fn (state_upd_tapes <[α:=(s; fs ++ [a])]> σ, c))) 
                 (dunifP ((q+1)*(s+1)-1)))
             ) as ->.
      { rewrite dunifP_decompose; last lia.
        rewrite -dbind_assoc'.
        apply dbind_ext_right.
        intros ?.
        rewrite /dmap.
        rewrite -dbind_assoc'.
        apply dbind_ext_right. intros ?.
        rewrite dret_id_left.
        by rewrite f_inv_cancel_l.
      }
      rewrite full_info_cons_osch_lim_exec dret_id_left /step'.
      rewrite Hlookup1.
      rewrite fill_not_val; last done.
      rewrite fill_dmap//=.
      rewrite head_prim_step_eq//= !dmap_comp.
      rewrite !Nat2Z.id.
      erewrite (dunif_fragmented _ ((q + 1) * (s + 1) - p * r - 1))%nat at 1; [..|done|lia].
      rewrite -!dbind_assoc'.
      replace 0 with (0+0) by lra.
      eapply ARcoupl_dbind; [lra|lra| |apply ARcoupl_eq].
      intros ? qs ->.
      rewrite dret_id_left. simpl. rewrite app_nil_r.
      rewrite full_info_lift_osch_lim_exec full_info_one_step_stutter_osch_lim_exec.
      rewrite /step'.
      rewrite list_lookup_insert_ne; last done.
      rewrite Hlookup2.
      rewrite fill_not_val//=.
      rewrite fill_dmap//=.
      rewrite head_prim_step_eq//= !dmap_comp.
      rewrite !Nat2Z.id.
      case_bool_decide as Hd.
      + rewrite -!dbind_assoc'.
        replace 0 with (0+0) by lra.
        eapply ARcoupl_dbind; [lra|lra| |apply ARcoupl_eq].
        intros ? y ->.
        rewrite !dret_id_left/=.
        rewrite app_nil_r.
        rewrite !insert_length.
        case_match eqn:Heqn.
        apply (f_equal f) in Heqn.
        rewrite f_inv_cancel_r/f in Heqn.
        apply (f_equal fin_to_nat) in Heqn.
        rewrite !fin_to_nat_to_fin in Heqn.
        apply ARcoupl_dret; first done.
        eexists _.
        rewrite bool_decide_eq_true_2; last done.
        eexists _, _.
        split; first done.
        rewrite fin_to_nat_to_fin.
        naive_solver.
      + erewrite <-(dbind_const (dunifP _) (dbind _ _)); last first.
        { apply dunif_mass. lia. }
        rewrite /dmap.
        replace 0 with (0+0) by lra.
        eapply ARcoupl_dbind; [lra|lra| |apply ARcoupl_eq].
        intros ? y ->.
        rewrite dret_id_left. simpl. rewrite app_nil_r !insert_length.
        case_match eqn :Heqn.
        apply ARcoupl_dret; first done.
        eexists _.
        rewrite bool_decide_eq_false_2; last done.
        eexists _, _, _.
        repeat split; try done.
        apply fin_to_nat_inj.
        rewrite !fin_to_nat_to_fin.
        apply (f_equal f) in Heqn.
        rewrite f_inv_cancel_r in Heqn.
        subst.
        rewrite /f.
        by rewrite fin_to_nat_to_fin.
      Unshelve. 
      { intros.
        rewrite /f_frag.
        rewrite bool_decide_eq_true_2; lia.
      }
    - iPureIntro.
      intros ????? (qs&A1) (qs'&A2).
      case_bool_decide as K1;
        case_bool_decide as K2.
      + destruct A1 as (a&c&->&(y&?&?)).
        destruct A2 as (a'&c'&->&(y'&?&?)).
        destruct K1 as [m K1].
        destruct K2 as [m' K2].
        simplify_eq.
        assert (<[j:=fill K #(qs')]> l !!j= <[j:=fill K #(qs)]> l!!j) as A1 by (by f_equal) .
        rewrite !list_lookup_insert in A1; try lia. simplify_eq.
        assert (<[j':=fill K' #y']> (<[j:=fill K #(qs)]> l)!!j' = <[j':=fill K' #y]> (<[j:=fill K #(qs)]> l)!!j') as A1 by (by f_equal) .
        rewrite !list_lookup_insert in A1; try (by rewrite insert_length||lia). simplify_eq.
        split; last done.
        rewrite -K1 in K2.
        apply Hinj in K2.
        apply fin_to_nat_inj in K2. subst.
        assert (f(a,c)=f(a',c')) as H'.
        { apply fin_to_nat_inj.
          etrans; last exact. done.
        }
        apply Hbij in H'. by simplify_eq.
      + destruct A2 as (a'&c'&->&(y'&?&?)).
        destruct A1 as (a&c&y&->&->&?).
        simplify_eq.
        exfalso.
        assert (<[j:=fill K #(qs')]> l !!j= <[j:=fill K #((nat_to_fin (Hf' a c)))]> l!!j) as A1 by (by f_equal) .
        rewrite !list_lookup_insert in A1; try lia. simplify_eq.
      + destruct A1 as (a'&c'&->&(y'&?&?)).
        destruct A2 as (a&c&y&->&->&?).
        simplify_eq.
        exfalso.
        assert (<[j:=fill K #(nat_to_fin (Hf' a c))]> l!!j = <[j:=fill K #( qs)]> l!!j) as A1 by (by f_equal) .
        rewrite !list_lookup_insert in A1; try lia. simplify_eq.
      + destruct A1 as (a&c&y&->&->&?).
        destruct A2 as (a'&c'&y'&->&->&?).
        simplify_eq.
        assert (<[j:=fill K #(nat_to_fin (Hf' a' c'))]> l!!j = <[j:=fill K #(nat_to_fin (Hf' a c))]> l!!j) as A1 by (by f_equal) .
        rewrite !list_lookup_insert in A1; try lia. simplify_eq.
        rewrite -/(f (a, c)) in A1.
        rewrite -/(f (a', c')) in A1.
        simplify_eq.
        assert (<[j':=fill K' #y']> (<[j:=fill K #(nat_to_fin (Hf' a c))]> l)!!j' =
       <[j':=fill K' #y]> (<[j:=fill K #(nat_to_fin (Hf' a c))]> l)!!j') as A1 by (by f_equal) .
        rewrite !list_lookup_insert in A1; try (by rewrite insert_length||lia). by simplify_eq.
    - iIntros (??? (qs & Hcond)).
      case_bool_decide as K1.
      + destruct Hcond as (a&c&->&(y&Heq&?)).
        destruct K1 as [m K1].
        simplify_eq.
        iMod (spec_update_prog with "[$][$Hspec1]") as "[HK Hs]".
        iMod (spec_update_prog with "[$][$Hspec2]") as "[HK ?]".
        iMod (ghost_map_update with "[$]Hα") as "(?&?)".
        iMod (ghost_map_update with "[$]Hβ") as "(?&?)".
        iApply spec_coupl_ret.
        iFrame.
        iModIntro.
        iMod "Hclose".
        iModIntro.
        iPureIntro. simpl.
        eexists a, c.
        pose proof fin_to_nat_lt a.
        pose proof fin_to_nat_lt c.
        pose proof fin_to_nat_lt qs.
        pose proof fin_to_nat_lt (f(a,c)).
        pose proof fin_to_nat_lt m.
        rewrite !fmap_app/=.
        repeat split; try (lia||done).
        * rewrite /f_frag in Heq.
          case_bool_decide; lia.
        * case_bool_decide as Heq'.
          -- unshelve epose proof Hfragineq (fin_to_nat m) _; lia.
          -- rewrite /f_frag in Heq.
             case_bool_decide; last lia.
             rewrite /f fin_to_nat_to_fin/f' in Heq. 
             case_bool_decide.
             ++ exfalso.
                assert (p*a+c<p*r)%nat; last lia.
                apply Nat.lt_le_trans with (p*a+p)%nat.
                --- apply Nat.add_lt_mono_l. lia.
                --- trans (p*(a+1))%nat; first lia.
                    apply Nat.mul_le_mono; lia.
             ++ case_bool_decide.
                --- rewrite bool_decide_eq_true_2; first lia.
                    assert (y=(c-p)*r+a)%nat as ->; first lia.
                    apply Nat.lt_le_trans with ((c-p)*r+r)%nat; first lia.
                    trans ((c-p+1)*r)%nat; first lia.
                    rewrite Nat.mul_comm.
                    apply Nat.mul_le_mono; lia.
                --- rewrite bool_decide_eq_false_2; first lia.
                    apply Nat.le_ngt.
                    assert (r * (q + 1) + (a - r) * (q + 1 - p) <=p*r+y)%nat as H''; first lia.
                    rewrite -Nat.le_sub_le_add_l in H''.
                    trans (r*(q+1)-r*p)%nat; lia. 
      + destruct Hcond as (a&c&y&->&->&?).
        simplify_eq.
        iMod (spec_update_prog with "[$][$Hspec1]") as "[HK Hs]".
        iMod (spec_update_prog with "[$][$Hspec2]") as "[HK ?]".
        iMod (ghost_map_update with "[$]Hα") as "(?&?)".
        iMod (ghost_map_update with "[$]Hβ") as "(?&?)".
        iApply spec_coupl_ret.
        iFrame.
        iModIntro.
        iMod "Hclose".
        iModIntro.
        rewrite !fmap_app.
        rewrite !fin_to_nat_to_fin.
        iPureIntro.
        exists a, c.
        pose proof fin_to_nat_lt a.
        pose proof fin_to_nat_lt y.
        pose proof fin_to_nat_lt c.
        pose proof fin_to_nat_lt (f(a,c)) as Hf.
        repeat split; try (done||lia).
        -- rewrite /f fin_to_nat_to_fin in Hf. lia.
        -- assert (f' a c < p*r)%nat as Hineq.
           { rewrite /f'.
             case_bool_decide.
             - apply Nat.lt_le_trans with (a*p+p)%nat; first lia.
               trans (p*(a+1))%nat; first lia.
               apply Nat.mul_le_mono; lia.
             - case_bool_decide;
                 exfalso; apply K1.
               + eexists (nat_to_fin _).
                 rewrite /f_frag.
                 rewrite bool_decide_eq_true_2; last apply fin_to_nat_lt.
                 rewrite /f !fin_to_nat_to_fin/f'.
                 rewrite bool_decide_eq_false_2; last done.
                 rewrite bool_decide_eq_true_2; last done.
                 rewrite -Nat.add_assoc. done.
                 Unshelve.
                 replace (S _) with ((q+1)*(s+1)-p*r)%nat by lia.
                 assert ((c - p) * r +p*r+ a < (q + 1) * (s + 1) )%nat; last lia.
                 rewrite -Nat.mul_add_distr_r.
                 rewrite Nat.sub_add; last lia.
                 apply Nat.lt_le_trans with (c*r+r)%nat; first lia.
                 trans ((c+1)*r)%nat; first lia.
                 apply Nat.mul_le_mono; lia.
               + rewrite /f!fin_to_nat_to_fin/f'.
                 rewrite bool_decide_eq_false_2; last done.
                 rewrite bool_decide_eq_false_2; last done.
                 rewrite /f_frag.
                 
                 assert ((r * (q + 1) + (a - r) * (q + 1) + c)%nat - p*r < S ((q+1)*(s+1)-p*r-1))%nat as Hineq.
                 { replace (S (_-1)) with ((q+1)*(s+1)-p*r)%nat by lia.
                   assert (r * (q + 1) + (a - r) * (q + 1) + c  < (q + 1) * (s + 1) )%nat; last lia.
                   rewrite -Nat.mul_add_distr_r.
                   rewrite -Nat.le_add_sub; last lia.
                   apply Nat.lt_le_trans with (a*(q+1)+(q+1))%nat; first lia.
                   trans ((a+1)*(q+1))%nat; first lia.
                   rewrite Nat.mul_comm.
                   apply Nat.mul_le_mono; lia. }
                 eexists (nat_to_fin Hineq).
                 rewrite fin_to_nat_to_fin.
                 rewrite bool_decide_eq_true_2; last lia.
                 rewrite -Nat.le_add_sub; first lia.
                 trans ((q+1)*r)%nat; last lia.
                 apply Nat.mul_le_mono; lia.
           }
           rewrite bool_decide_eq_true_2; last done.
           rewrite /f' in Hineq.
           case_bool_decide; first lia.
           case_bool_decide; first lia.
           assert (p*r<=(q+1)*r)%nat; last lia.
           apply Nat.mul_le_mono; lia.
  Qed.

  
  Lemma wp_couple_toss {x y k:nat} j K E:
    (k>0)%nat -> 
    (x=(y+1)*k-1)%nat ->
    {{{ j ⤇ fill K (rand #y) }}}
      rand #x@E
      {{{ (n:nat), RET #n; j⤇fill K (#(n/k)%nat) }}}.
  Proof. 
    iIntros (Hk -> Φ) "Hspec HΦ".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 [l s] ε) "[Hσ [Hs Hε]]".
    iDestruct (spec_auth_prog_agree with "Hs Hspec") as "%Hsome".
    assert (j < length l)%nat.
    { by eapply lookup_lt_Some. }
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    rewrite /prog_coupl.
      pose (λ (n:fin(S y)) (m:fin(S (k-1))%nat), n*k+m)%nat as f'.
      assert (∀ n m, f' n m <S((y+1)*k-1))%nat as Hf'.
      { intros n m. pose proof fin_to_nat_lt n.
        pose proof fin_to_nat_lt m.
        rewrite /f'.
        replace (S _) with ((y+1)*k)%nat by lia.
        rewrite Nat.mul_add_distr_r.
        apply Nat.lt_le_trans with (n*k+k)%nat; first lia.
        rewrite Nat.mul_1_l. apply Nat.add_le_mono; last lia.
        apply Nat.mul_le_mono; lia.
      }
      pose (λ '(n,m), nat_to_fin (Hf' n m)) as f.
      assert (Bij f).
      { rewrite /f. split.
        - intros [a b ] [c d] H'.
          apply (f_equal fin_to_nat) in H'.
          rewrite !fin_to_nat_to_fin !/f' in H'.
          pose proof fin_to_nat_lt a.
          pose proof fin_to_nat_lt b.
          pose proof fin_to_nat_lt c.
          pose proof fin_to_nat_lt d.
          apply Nat.mul_split_l in H'; try lia.
          by destruct!/=.
        - intros n.
          pose proof fin_to_nat_lt n.
          assert (fin_to_nat n/k < S y)%nat as y'.
          { apply Nat.div_lt_upper_bound; first lia.
            eapply Nat.lt_le_trans; first done. lia.
          }
          assert (fin_to_nat n `mod` k < S (k-1))%nat as k'.
          { replace (S _) with k by lia. apply Nat.mod_upper_bound. lia. }
          exists (nat_to_fin y', nat_to_fin k').
          apply fin_to_nat_inj.
          rewrite !fin_to_nat_to_fin.
          rewrite /f'.
          rewrite !fin_to_nat_to_fin.
          rewrite Nat.mul_comm.
          by rewrite -Nat.div_mod_eq.
      }
    iExists (λ a b, ∃ (n:fin (S y)) (m:fin(S (k-1))%nat), a =  (Val #(fin_to_nat n * k + fin_to_nat m )%nat, σ1, []) /\ b = ([(cfg_to_cfg' (l, s), j)] ++ [(cfg_to_cfg' (<[j:=fill K #(fin_to_nat n)]> l, s), (fin_to_nat m + length l)%nat)],
        (<[j:=fill K #(fin_to_nat n)]> l, s))), (full_info_cons_osch (λ _, dret j) (λ _, full_info_cons_osch (λ _, dmap (λ x, fin_to_nat x + length l)%nat (dunifP (k-1)%nat)) (λ _, full_info_inhabitant))), 0%NNR, (λ _, ε), ε.
    repeat iSplit.
    - iPureIntro. apply head_prim_reducible. solve_red.
    - done.
    - rewrite Expval_const; last done.
      iPureIntro.
      rewrite Rplus_0_l.
      trans (ε*1); last (simpl; lra).
      by apply Rmult_le_compat.
    - iPureIntro.
      simpl.
      rewrite head_prim_step_eq///=.
      rewrite full_info_cons_osch_lim_exec.
      rewrite /dmap.
      rewrite dret_id_left.
      rewrite /step'.
      rewrite Hsome.
      rewrite fill_not_val//.
      rewrite fill_dmap//=.
      rewrite head_prim_step_eq//=.
      rewrite !dmap_comp.
      rewrite /dmap -!dbind_assoc'.
      rewrite !Nat2Z.id.
      rewrite (dunifP_decompose _ _ _ f); last first.
      { f_equal. replace (S (k-1))%nat with k by lia. lia. }
      simpl.
      rewrite -dbind_assoc'.
      replace 0 with (0+0) by lra.
      eapply ARcoupl_dbind; [lra|lra| |apply ARcoupl_eq].
      intros ? n ->.
      rewrite dret_id_left. rewrite app_nil_r.
      rewrite full_info_lift_osch_lim_exec full_info_cons_osch_lim_exec.
      rewrite /dmap -!dbind_assoc'.
      replace 0 with (0+0) by lra.
      eapply ARcoupl_dbind; [lra|lra| |apply ARcoupl_eq].
      intros ? m ->.
      rewrite !dret_id_left.
      rewrite /step'.
      rewrite lookup_ge_None_2; last first.
      { rewrite insert_length; lia. }
      rewrite dret_id_left.
      rewrite full_info_lift_osch_lim_exec full_info_inhabitant_lim_exec.
      rewrite /dmap !dret_id_left.
      rewrite fin_to_nat_to_fin.
      rewrite app_nil_r.
      apply ARcoupl_dret; naive_solver.
    - iPureIntro. simpl. intros ????? (n&H1&K1) (n'&H2&K2). destruct!/=.
      assert (<[j:=fill K #n]> l!!j = <[j:=fill K #n']> l!!j) as Hlookup; first by f_equal.
      rewrite !list_lookup_insert in Hlookup; try lia.
      simplify_eq. split; last done.
      repeat f_equal. apply fin_to_nat_inj. lia.
    - simpl.
      iIntros (????? (n&m&H1)). destruct!/=.
      iFrame.
      iMod (spec_update_prog with "[$][$]") as "[??]".
      iFrame.
      iModIntro.
      iNext.
      iMod "Hclose".
      iModIntro.
      iSplitL; last done.
      wp_pures.
      iApply "HΦ".
      iModIntro.
      rewrite Nat.div_add_l; last lia.
      pose proof fin_to_nat_lt n.
      pose proof fin_to_nat_lt m.
      rewrite Nat.div_small; last lia.
      by rewrite Nat.add_0_r.
  Qed.
  
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
