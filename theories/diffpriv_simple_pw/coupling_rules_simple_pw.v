(** * Coupling rules  *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext fin.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv_simple_pw Require Import lifting_simple_pw ectx_lifting_simple_pw.
From clutch.prob_lang Require Import lang notation tactics metatheory erasure.
From clutch.prob_lang.spec Require Import spec_rules.
From clutch.diffpriv_simple_pw Require Export primitive_laws_simple_pw.

Section rules.
  Context `{!diffprivGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

  #[local] Open Scope R.

  (** helper lemma  *)
  Lemma DPcoupl_steps_ctx_bind_r `{Countable A} (μ : distr A)
    e1' σ1' R (ε δ: nonnegreal) K :
    to_val e1' = None →
    DPcoupl μ (prim_step e1' σ1') R ε δ →
    DPcoupl μ (prim_step (fill K e1') σ1')
      (λ a '(e2', σ2'), ∃ e2'', (e2', σ2') = (fill K e2'', σ2') ∧ R a (e2'', σ2')) ε δ.
  Proof.
    intros Hcpl Hv.
    rewrite fill_dmap //= -(dret_id_right μ ) /=.
    eapply (DPcoupl_dbind' ε 0 _ δ 0); [lra|done|done|lra| |done].
    intros ? [] ?.
    apply DPcoupl_dret=>/=; [done|done|]. eauto.
  Qed.

  Lemma DPcoupl_laplace_step
    (loc loc' k k' : Z)
    (Hdist : (Z.abs (k + loc - loc') <= k')%Z)
    (num den : Z) ε ε' σ1 σ1' :
    (IZR num / IZR den) = ε →
    0 < IZR num / IZR den →
    ε' = (IZR k' * ε) →
    DPcoupl (language.prim_step (Laplace #num #den #loc) σ1)
      (prim_step (Laplace #num #den #loc') σ1')
      (λ ρ2 ρ2', ∃ (z : Z),
          ρ2 = (Val #z, σ1) ∧ ρ2' = (Val #(z+k), σ1'))
      ε' 0.
  Proof.
    intros ?Hε??Hε'. simpl. fold cfg.
    rewrite ?head_prim_step_eq /= ; try by exact 0%Z.
    rewrite /dmap.
    replace 0 with (0 + 0) by lra.
    replace ε' with (ε' + 0) by lra.
    eapply DPcoupl_dbind => //.
    2:{ case_decide ; [|done].
        rewrite /laplace_rat.
        rewrite Hε' -Hε.
        apply Mcoupl_to_DPcoupl.
        eapply (Mcoupl_laplace).
        done.
    }
    simpl.
    intros z1 z2 Hres.
    apply DPcoupl_dret; [done|done|]. subst.
    exists z1. done.
  Qed.

  Lemma hoare_couple_laplace (loc loc' k k' : Z)
    (Hdist : (Z.abs (k + loc - loc') <= k')%Z)
    (num den : Z) (ε ε' : R) K E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    ε' = (IZR k' * ε) →
    {{{ ⤇ fill K (Laplace #num #den #loc') ∗ ↯m ε' }}}
      Laplace #num #den #loc @ E
      {{{ (z : Z), RET #z; ⤇ fill K #(z+k) }}}.
  Proof.
    iIntros (Hε εpos Hε').
    iIntros (?) "(Hr & Hε) Hcnt".
    iApply wp_lift_step_couple.
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1) & Hauth2 & (Hε2 & Hδ)) /=".
    iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ecm_supply_ecm_inv with "Hε2 Hε") as %(ε'' & ε''' & -> & Hε'').
    iSplit ; [iPureIntro ; solve_red|].
    iExists _,ε'',ε''',0%NNR,δ_now,1%nat. iSplit.
    { iPureIntro.
      rewrite pexec_1.
      rewrite step_or_final_no_final. 2: apply reducible_not_final ; solve_red.
      apply DPcoupl_steps_ctx_bind_r => //. rewrite Hε''. simpl.
      eapply DPcoupl_laplace_step => //. } simpl.
    repeat iSplit. 1,2: real_solver.
    iIntros (???? (?& [=->] & (z & [=-> ->] & [=-> ->]))).
    iMod (spec_update_prog (fill K #(_)) with "Hauth2 Hr") as "[$ Hspec0]".
    iMod (ecm_supply_decrease with "Hε2 Hε") as (???Herr Hε''') "H".
    do 2 iModIntro.
    iMod "Hclose'" as "_".
    iModIntro. iFrame.
    rewrite -wp_value.
    iDestruct ("Hcnt" with "[$Hspec0]") as "$".
    simplify_eq. rewrite Hε'' Hε''' in Herr.
    rewrite Rplus_comm in Herr. apply Rplus_eq_reg_r in Herr. clear -Herr.
    apply nnreal_ext in Herr. subst. done.
    Unshelve. all: exact 0%Z.
  Qed.


  Definition WP_PWEQ_no_K := ∀ e e' E,
    (
      ∀ (RES : val),
      ⤇ e' -∗
          WP e @ E
            {{ v, ∃ v' : val, ⤇ (Val v') ∗ ⌜v = RES → v' = RES⌝ }} )
-∗
    (⤇ e'
    -∗
     WP e @ E
      {{ v, ∃ v' : val, ⤇ (Val v') ∗ ⌜v = v'⌝ }}).

  Lemma wp_pweq_no_K : (* ∀ (e e' : expr) (* ε δ *),
       (* state_interp σ ∗ spec_interp (e', σ') ∗ err_interp ε δ ∗ *)
       (∀ (RES : val), WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜v = RES → v' = RES⌝ }}) -∗
       (* state_interp σ ∗ spec_interp (e', σ') ∗ err_interp ε δ ∗ *)
       ⤇ e' -∗
       WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜v = v'⌝ }} *)
  WP_PWEQ_no_K.
  Proof.
    iIntros (???) "pw rhs".
    rewrite wp_unfold /wp_pre //=.
    destruct (to_val e) eqn:He.
    { iSpecialize ("pw" $! v).
      rewrite wp_unfold /wp_pre //= He. iMod ("pw" with "rhs") as "pw". iModIntro. iDestruct "pw" as "(%v' & v' & %pweq)".
      iExists v'. iFrame. rewrite pweq => //.
    }
    (* iIntros (e1 e1' σ1 σ1' ε δ) "(HT & S & E & pw)". *)
    iIntros (?????) "(HT & S & ε & δ)".
    iDestruct (spec_auth_prog_agree with "S rhs") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplit.
    { iSpecialize ("pw" $! #42 with "rhs").
      rewrite wp_unfold /wp_pre //= He. iSpecialize ("pw" with "[$]").
      (* TODO reducibility requirement; can probably be fixed *)
      admit.
    }
    iRight.
    iNext.
    iMod "Hclose'" as "_".
    iModIntro. iSplit.
    -
      (* The current goal is weird, see comments below. *)
      (* What if we drop persistence and consume the auth fragment instead? *)
      iAssert (∀ v, ∃ K,
                  (∀ e' σ', spec_auth (fill K e', σ') -∗
                            (∃ (v' : val) (σ' : state), spec_auth (@pair expr state (fill K (Val v')) σ') ∗ ⌜v = v'⌝))
                  ={E}=∗
                  ∃ v', ⤇ fill K v' ∗ ⌜v = v'⌝)%I
        with "[-]" as "alt_goal_no_pers".

      (* iAssert (∀ v, (∀ e' σ', spec_auth (e', σ') -∗ (∃ (v' : val) (σ' : state), spec_auth (@pair expr state (Val v') σ') ∗ ⌜v = v'⌝)) ={E}=∗ ∃ v', ⤇ v' ∗ ⌜v = v'⌝)%I with "[-]" as "alt_goal_no_pers". *)
      2: admit.
      iIntros "%". iExists []. iIntros "h".
      assert (e' = fill [] e') as -> by auto.
      iDestruct ("h" with "S") as "(%v' & %σ' & S' & %eq)".
      iModIntro.
      iExists v'. iSplit. 2: by rewrite eq.
      iDestruct (spec_auth_prog_agree with "S' rhs") as %<-.
      done.


      (* (* Weird: this should be trivial. The current postcondition should be weak enough to be implied by whatever the
         pweq clause of the WP assumed here. Should the WP mention (⤇ v') instead of (spec_auth (v', σ')) ? *)
         (* If the implication wasn't persistent, we could use "rhs". Let's pretend that's the case... *)
         iAssert (∀ v, (∃ (v' : val) (σ' : state), spec_auth (@pair expr state (Val v') σ') ∗ ⌜v = v'⌝) ={E}=∗ ∃ v', ⤇ v' ∗ ⌜v = v'⌝)%I with "[-]" as "alt_goal_no_pers".
         2: admit.
         (* iModIntro. *)
         iIntros "% (%v' & %σ' & S' & %eq)".
         iModIntro.
         iExists v'. iSplit. 2: by rewrite eq.
         iDestruct (spec_auth_prog_agree with "S' rhs") as %->.
         (* now we can conclude with by framing "rhs". *)

         (* But this doesn't make much sense: the context is actually inconsistent because we have two authoritative views
         of the spec resource. So we could have derived anything. *)
         rewrite /spec_auth. simpl.
         iDestruct "S" as "[S _]".
         iDestruct "S'" as "[S' _]".
         iCombine "S" "S'" as "H".
         iDestruct (own_valid with "H") as "%Hvalid".
         exfalso. destruct Hvalid as [Hvalid _]. clear -Hvalid.
         apply (λ x, proj1 (dfrac_valid_own x)) in Hvalid.
         (* we have our contradiction :/ *)

         done. *)
    - iIntros (RES).
      iApply (wp_strong_mono with "[pw rhs]") => //.
      + iApply ("pw" $! RES). done.
      + simpl. iIntros "%v (%v' & rhs & %pweq) !>".
        iExists v',σ1'.
        iDestruct (spec_auth_prog_agree with "S rhs") as %->.
        iSplit. 2: iPureIntro ; exact pweq.
        iFrame.
  Admitted.

  Definition WP_PWEQ := ∀ e e' K E,
    (
      ∀ (RES : val),
      ⤇ fill K e' -∗
          WP e @ E
            {{ v, ∃ v' : val, ⤇ fill K (Val v') ∗ ⌜v = RES → v' = RES⌝ }} )
-∗
    (⤇ fill K e'
    -∗
     WP e @ E
      {{ v, ∃ v' : val, ⤇ fill K (Val v') ∗ ⌜v = v'⌝ }}).

  Lemma wp_pweq : WP_PWEQ.
  Proof.
    iIntros (????) "pw rhs".
    rewrite wp_unfold /wp_pre //=.
    destruct (to_val e) eqn:He.
    { iSpecialize ("pw" $! v).
      rewrite wp_unfold /wp_pre //= He. iMod ("pw" with "rhs") as "pw". iModIntro. iDestruct "pw" as "(%v' & v' & %pweq)".
      iExists v'. iFrame. rewrite pweq => //.
    }
    (* iIntros (e1 e1' σ1 σ1' ε δ) "(HT & S & E & pw)". *)
    iIntros (?????) "(HT & S & ε & δ)".
    iDestruct (spec_auth_prog_agree with "S rhs") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplit. 1: admit.
    iRight.
    iNext.
    iMod "Hclose'".
    iModIntro. iSplit.
    -
      iAssert (∀ v,
                ∃ K,
                  (∀ e' σ', spec_auth (fill K e', σ') -∗
                            (∃ (v' : val) (σ' : state),
                                spec_auth (@pair expr state (fill K (Val v')) σ') ∗ ⌜v = v'⌝))
                  ={E}=∗
                  ∃ v', ⤇ fill K v' ∗ ⌜v = v'⌝)%I with "[-]" as "alt_goal_no_pers".
      2: admit.
      iIntros "%". iExists K. iIntros "h".
      (* assert (e' = fill [] e') as -> by auto. *)
      iDestruct ("h" with "S") as "(%v' & %σ' & S' & %eq)".
      iModIntro.
      iExists v'. iSplit. 2: by rewrite eq.
      iDestruct (spec_auth_prog_agree with "S' rhs") as %<-.
      done.

    (* - iModIntro.
         + iIntros "%v (%v' & %σ' & rhs & %eq) !>". iExists v'. iSplit. 2: by rewrite eq. admit. *)
    - iIntros (RES).
      iApply (wp_strong_mono with "[pw rhs]") => //.
      + iApply ("pw" $! RES). done.
      + simpl. iIntros "%v (%v' & rhs & %pweq) !>".
        iAssert (∃ v1' (σv' : state) K (_ : LanguageCtx K), spec_auth
                                        (@pair expr state (K (Val v1')) σv')
                                         ∗ ⌜v = RES → v1' = RES⌝)%I with "[-]" as "_".
        2: admit.
        iExists v',σ1',(fill K),_.
        iDestruct (spec_auth_prog_agree with "S rhs") as %->.
        iSplit. 2: iPureIntro ; exact pweq.
        iFrame.
  Admitted.


End rules.
