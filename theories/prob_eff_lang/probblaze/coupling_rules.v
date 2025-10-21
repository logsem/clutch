(** * Coupling rules  *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext fin.
From clutch.prob_eff_lang.probblaze Require Import ectx_lifting.
From clutch.prob_eff_lang.probblaze Require Import syntax notation metatheory erasure.
From clutch.prob_eff_lang.probblaze Require Import spec_rules.
From clutch.prob_eff_lang.probblaze Require Export primitive_laws semantics.

Section rules.
  Context `{!probblazeGS Σ}.

(** helper lemma -- move to coupling_rules *)
  Lemma ARcoupl_steps_ctx_bind_r `{Countable A} (μ : distr A)
    e1' σ1' R (ε : nonnegreal) K :
    uncaught_eff e1' = None →
    to_val e1' = None →
    ARcoupl μ (prim_step e1' σ1') R ε →
    ARcoupl μ (prim_step (fill K e1') σ1')
      (λ a '(e2', σ2'), ∃ e2'', (e2', σ2') = (fill K e2'', σ2') ∧ R a (e2'', σ2')) ε.
  Proof.
    intros Hcpl Hv.
    rewrite fill_dmap_uncaught' //= -{2}(dret_id_right μ ) /=.
    eapply (ARcoupl_dbind' ε 0%NNR); [ apply cond_nonneg |done | simpl; lra | ].
    intros ? [] ?.
    apply ARcoupl_dret=>/=; [done|]. eauto.
  Qed.

  Lemma wp_couple_rand_rand N f `{Bij nat nat f} z K E :
    TCEq N (Z.to_nat z) →
    (forall n:nat, (n < S N)%nat -> (f n < S N)%nat) ->
    {{{ ⤇ semantics.fill K (rand #z) }}}
      rand #z @ E
    {{{ (n : nat), RET #n; ⌜ n ≤ N ⌝ ∗ ⤇ semantics.fill K #(f n) }}}.
  Proof.
    iIntros (H0 Hdom Ψ) "Hr HΨ".
    destruct (restr_bij_fin (S N) f Hdom) as [ff [Hbij Hff]].
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε) "[Hσ [Hs Hε]]".
    iDestruct (spec_auth_prog_agree with "Hs Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".

    replace ε with (0 + ε)%NNR; last first.
    { apply nnreal_ext; simpl; lra. }
    iApply (prog_coupl_steps _ _ _
              (λ ρ2 ρ2',
                ∃ (n : fin _), ρ2 = (syntax.Val #n, σ1) ∧ ρ2' = (semantics.fill K #(f n), σ1')))
    ; [done| | |..].
    { eexists. simpl. apply head_step_prim_step. apply head_step_support_equiv_rel. unshelve constructor; eauto using Fin.F1. by apply TCEq_eq. }
    { eexists. simpl. apply fill_step. apply head_step_prim_step. apply head_step_support_equiv_rel. unshelve constructor; eauto using Fin.F1. by apply TCEq_eq. }
    { rewrite /= semantics.fill_dmap //.
      rewrite /= -(dret_id_right (semantics.prim_step _ _)) /=.
      apply ARcoupl_exact.
      eapply Rcoupl_dmap.
      eapply Rcoupl_mono.
      - apply (Rcoupl_rand_rand _ ff).
        by rewrite H0.
      - intros [] [] (b & [=] & [=])=>/=.
        simplify_eq.
        rewrite Hff. eauto. }
    iIntros (e2 σ2 e2' σ2' (b & [= -> ->] & [= -> ->])) "!> !>".
    iMod (spec_update_prog with "Hs Hr") as "[$ Hr]".
    iMod "Hclose" as "_".
    replace (0 + ε)%NNR with ε; last first.
    { apply nnreal_ext; simpl; lra. }
    iFrame.
    iApply wp_value.
    iApply "HΨ".
    iFrame.
    iPureIntro.
    apply fin_to_nat_le.
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
    iIntros (H0 Hl Ψ) "[Hε Hr] HΨ".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε) "[Hσ [Hs Hε2]]".
    iDestruct (spec_auth_prog_agree with "Hs Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    iDestruct (ec_supply_ec_inv with "Hε2 Hε") as %(x & x1 & -> & H).
    iApply (prog_coupl_steps _ _ _
           (* (λ ρ2 ρ2', *)
           (*   ∃ (n : fin _), n∉l /\ρ2 = (Val #n, σ1) ∧ ρ2' = (fill K #(n), σ1')) *))
    ; [done| | |..].
    1,2: eexists; simpl; try apply fill_step; apply head_step_prim_step; apply head_step_support_equiv_rel; unshelve constructor; eauto using Fin.F1; by apply TCEq_eq. 
    { simpl. eapply ARcoupl_steps_ctx_bind_r; [done|done|].
      apply ARcoupl_rand_rand_avoid_list; first done.
      - by rewrite S_INR. 
      - by apply TCEq_eq.
    }
    iIntros (e2 σ2 e2' σ2' (b & [= ->] & (?&?&[= -> ->] & [= -> ->]))) "!> !>".
    iMod (spec_update_prog with "Hs Hr") as "[$ Hr]".
    iMod (ec_supply_decrease with "Hε2 Hε") as (x2 x3 H1 ?) "H".
    replace (x3) with (x1); last first.
    { apply nnreal_ext. inversion H1.
      lra.
    }
    iMod "Hclose" as "_".
    (* replace (0 + ε)%NNR with ε; last first. *)
    (* { apply nnreal_ext; simpl; lra. } *)
    iFrame.
    iApply wp_value.
    iApply "HΨ".
    iFrame.
    by iPureIntro.
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
    {{{ (n : nat), RET #n; ⤇ fill K #(f n) ∗ ⌜ n ≤ N ⌝ }}}.
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
    iApply prog_coupl_steps; [done| | |..].
    1,2: eexists; simpl; try apply fill_step; apply head_step_prim_step; apply head_step_support_equiv_rel; unshelve constructor; eauto using Fin.F1; by apply TCEq_eq. 
    { apply ARcoupl_steps_ctx_bind_r, (ARcoupl_rand_rand_inj _ _ g); done || lra. }
    iIntros (???? (?& [=->] & (n & [=-> ->] & [=-> ->]))).
    iMod (spec_update_prog (fill K #(g _)) with "Hauth2 Hr") as "[$ Hspec0]".
    iMod (ec_supply_decrease with "Hε2 Hε") as (????) "H".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iModIntro. iFrame.
    rewrite -wp_value.
    rewrite /g fin_to_nat_to_fin.
    iDestruct ("Hcnt" with "[$Hspec0]") as "$".
    {
      iPureIntro.
      apply fin_to_nat_le.
    }
    iApply ec_supply_eq; [|done].
    simplify_eq. lra.
  Qed.

  (** fragmented state rand N ~ state rand M, N>=M, under injective function from M to N*)
  Lemma wp_couple_fragmented_rand_rand_inj {M N} (f: nat → nat) {_ : Inj (=) (=) f}
    ns nsₛ α αₛ e E Φ:
    (M <= N)%nat →
    (forall n : nat, (n < S M)%nat -> (f n < S N)%nat) ->
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗
    (∀ (n : nat),
       ⌜ n ≤ N ⌝ -∗
       if bool_decide (∃ m:nat, m ≤ M /\ f m = n) then
         ∀ m : nat, α ↪N (N; ns ++ [f m]) ∗ αₛ ↪ₛN (M; nsₛ ++ [m]) ∗ ⌜ f m ≤ N ⌝ ∗ ⌜ m ≤ M ⌝ -∗
              WP e @ E {{ Φ }}
       else
         α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ) ∗ ⌜ n ≤ N ⌝ -∗
         WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hineq Hdom) "(>Hα & >Hαₛ & Hwp)".
    edestruct (restr_inj_fin (S M) (S N) f (le_n_S M N Hineq) Hdom) as [g [HgInj HgEq]].
    iDestruct "Hα" as (fs) "(<-&Hα)".
    iDestruct "Hαₛ" as (fsₛ) "(<-&Hαₛ)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1 & Hl1) & Hauth2 & Hε2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2&Hl2)/=".
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
      iMod (ghost_map_update ((N; fs ++ [g _]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
      iMod (ghost_map_update ((M; fsₛ ++ [_]) : tape) with "Ht2 Hαₛ") as "[Ht2 Hαₛ]".
      iModIntro.
      iApply spec_coupl_ret.
      iMod "Hclose'" as "_".
      iSpecialize ("Hwp" $! (f m')).
      rewrite bool_decide_eq_true_2.
      2: { exists m'.
           split; auto.
           apply fin_to_nat_le. }
      iSpecialize ("Hwp" $! _ m').
      iDestruct ("Hwp" with "[$Hα $Hαₛ]") as "Hwp".
      { iPureIntro.
        split; [rewrite fmap_app /= HgEq // |].
        split; [rewrite fmap_app /=  // |].
        split; auto.
        - apply Nat.lt_succ_r, Hdom, fin_to_nat_lt.
        - apply fin_to_nat_le.
      }
      assert (0 + ε_now = ε_now)%NNR as ->.
      { apply nnreal_ext; simpl; lra. }
      by iFrame.
    - destruct H' as [??]. simplify_eq.
      iMod (ghost_map_update ((N; fs ++ [n]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
      iModIntro.
      iApply spec_coupl_ret.
      iMod "Hclose'" as "_".
      iSpecialize ("Hwp" $! (fin_to_nat n)).
      rewrite bool_decide_eq_false_2 //.
      2: {
        intros [m [Hm1 Hm2]].
        apply Hf.
        assert (m < S M)%nat as Hm3.
        { lia. }
        exists (nat_to_fin Hm3).
        apply fin_to_nat_inj.
        rewrite HgEq -Hm2.
        rewrite fin_to_nat_to_fin //.
      }
      iDestruct ("Hwp" with "[]") as "Hwp".
      { iPureIntro. apply fin_to_nat_le. }
      assert (0 + ε_now = ε_now)%NNR as ->.
      { apply nnreal_ext; simpl; lra. }
      iFrame.
      iApply "Hwp".
      iModIntro.
      iSplitL "Hα".
      { iFrame. rewrite fmap_app //. }
      iSplitL "Hαₛ".
      { iFrame. auto. }
      iPureIntro. apply fin_to_nat_le.
      Unshelve.
      apply Nat.lt_succ_r, Hdom, fin_to_nat_lt.
  Qed.

(** fragmented state rand N ~ state rand M, M>=N, under injective function from N to M,
      but with errors for rejection sampling! *)
  Lemma wp_couple_fragmented_rand_rand_inj_rev' {M N} (f : nat -> nat) {_: Inj (=) (=) f}
    ns nsₛ α αₛ e E Φ (ε : R) :
    0 <= ε →
    (N < M)%nat →
    (forall n, n < S N -> f n < S M)%nat ->
    ▷ α ↪N (N; ns) ∗ ▷ αₛ ↪ₛN (M; nsₛ) ∗ ↯ ε ∗
    (∀ (m : nat),
       ⌜ m ≤ M ⌝ -∗
       if bool_decide (∃ n:nat, n ≤ N /\ f n = m) then
         ∀ n, α ↪N (N; ns ++ [n]) ∗ αₛ ↪ₛN (M; nsₛ ++ [f n]) ∗ ⌜ n ≤ N ⌝ ∗ ⌜ f n ≤ M ⌝ -∗
              WP e @ E {{ Φ }}
     else
       ∀ (ε' : R),
         ⌜ε' = (S M / (S M - S N) * ε)%R⌝ ∗
         α ↪N (N; ns) ∗ αₛ ↪ₛN (M; nsₛ++[m]) ∗ ↯ ε' ∗ ⌜ m ≤ M ⌝ -∗
         WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hε Hineq Hdom) "(>Hα & >Hαₛ & Hε & Hwp)".
    edestruct (restr_inj_fin (S N) (S M) f (le_n_S N M (Nat.lt_le_incl _ _ Hineq)) Hdom) as [g [HgInj HgEq]].
    iDestruct "Hα" as (fs) "(<-&Hα)".
    iDestruct "Hαₛ" as (fsₛ) "(<-&Hαₛ)".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1 & Hl1) & Hauth2 & Hε2)".
    iDestruct "Hauth2" as "(HK&Hh2&Ht2&Hl2)".
    iDestruct (ghost_map_lookup with "Ht2 Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ec_supply_bound with "[$][$]") as %Hle.
    
    set ε' := mknonnegreal _ Hε.
    
    set ε_now1 := nnreal_minus ε_now ε' Hle.
    set ε_now2 := (ε_now + ε' * nnreal_nat (S N) / nnreal_nat (S M - S N))%NNR.
    set (E2 σ := if bool_decide (∃ x, σ = state_upd_tapes <[αₛ:=(M; fsₛ ++ [g x])]> σ1')
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
                      if bool_decide (b ∈ (λ x, state_upd_tapes <[αₛ:=(M; fsₛ ++ [x])]> σ1')
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
      { trans (SeriesC (λ x, if bool_decide (∃ y, g y = x) then / S M * ε_now1 else / S M * ε_now2))%R.
        - rewrite Rplus_0_l.
          set (h σ := match decide (∃ x, σ = state_upd_tapes <[αₛ:=(M; fsₛ ++ [x])]> σ1') with
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
        - eset (diff:=elements (((list_to_set (enum (fin(S M)))):gset _ )∖ ((list_to_set(g<$>enum (fin(S N)))):gset _))).
          erewrite (SeriesC_ext _
                      (λ x : fin (S M), (if bool_decide (x ∈ g<$> enum (fin(S N))) then / S M * ε_now1 else 0%R) +
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
      iMod (ghost_map_update ((N; fs ++ [n]) : tape) with "Ht1 Hα") as "[$ Hα]".
      iMod (ghost_map_update ((M; fsₛ ++ [g n]) : tape) with "Ht2 Hαₛ") as "[$ Hαₛ]".
      iModIntro. iMod "Hclose'" as "_".
      iSpecialize ("Hwp" $! (f n)).
      rewrite bool_decide_eq_true_2.
      2: { exists n.
           split; auto.
           apply fin_to_nat_le. }

      iSpecialize ("Hwp" $! _ (n)). iFrame.
      iDestruct ("Hwp" with "[$Hα $Hαₛ]") as "Hwp".
      { iPureIntro.
        split; [rewrite fmap_app /=  // |].
        split; [rewrite fmap_app /= HgEq // |].
        split; [apply fin_to_nat_le | ].
        apply Nat.lt_succ_r, Hdom, fin_to_nat_lt.
      }
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
      iMod (ghost_map_update ((M; fsₛ ++ [m]) : tape) with "Ht2 Hαₛ") as "[? Hαₛ]".
      iMod "Hclose'" as "_".
      iSpecialize ("Hwp" $! m).
      rewrite bool_decide_eq_false_2 //.
      2: {
        intros [n [Hn1 Hn2]].
        apply H1'.
        assert (n < S N)%nat as Hn3 by lia.
        exists (nat_to_fin Hn3).
        apply fin_to_nat_inj.
        rewrite HgEq -Hn2.
        rewrite fin_to_nat_to_fin //.
      }
      rewrite !S_INR /=.
      iFrame.
      iMod (ec_supply_increase with "[$Hε2]") as "[$ Hε']".
      { by eapply Rle_lt_trans. }
      iCombine "Hε Hε'" as "Hε".
      iApply ("Hwp" $! _ with "[$Hα $Hαₛ $Hε]").
      iPureIntro.
      split.
      1:{
        simpl. rewrite -/(INR (S N)). rewrite S_INR.
        replace (INR M + 1 - (INR N + 1))%R with (INR M - INR N)%R by lra.
        rewrite -{1}(Rmult_1_l ε).
        rewrite Rmult_assoc (Rmult_comm ε).
        rewrite -Rmult_plus_distr_r. apply Rmult_eq_compat_r.
        rewrite Rdiv_def.
        replace (1)%R with ((INR M - INR N)*/(INR M - INR N))%R at 1; last first.      
        { apply Rinv_r. apply lt_INR in Hineq. lra. }
        rewrite minus_INR; [|real_solver].
        rewrite -Rmult_plus_distr_r. lra. }
      split; auto.
      split; [ | apply fin_to_nat_le ].
      rewrite fmap_app //.
      Unshelve.
      + apply Nat.lt_succ_r, Hdom, fin_to_nat_lt.
      + apply fin_to_nat_le.
  Qed.

End rules.
