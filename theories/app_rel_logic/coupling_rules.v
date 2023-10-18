(** * Coupling rules  *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.app_rel_logic Require Import lifting ectx_lifting.
From clutch.prob_lang Require Import lang notation tactics metatheory.
From clutch.app_rel_logic Require Export primitive_laws spec_rules.

Section rules.
  Context `{!clutchGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

  (** * Approximate state_step(α, N) ~ state_step(α', N) coupling *)
  Lemma ARcoupl_state_state N M σ1 σ2 α1 α2 xs ys (ε : nonnegreal) :
    (0 < S N <= S M)%R →
    (((S M - S N) / S N) = ε)%R →
    σ1.(tapes) !! α1 = Some (N; xs) →
    σ2.(tapes) !! α2 = Some (M; ys) →
    ARcoupl
      (state_step σ1 α1)
      (state_step σ2 α2)
      (λ σ1' σ2', ∃ (n : fin (S N)) (m : fin (S M)),
          (fin_to_nat n = m) ∧
          σ1' = state_upd_tapes <[α1 := (N; xs ++ [n])]> σ1 ∧
          σ2' = state_upd_tapes <[α2 := (M; ys ++ [m])]> σ2)
      ε.
  Proof.
    intros NMpos NMε Hα1 Hα2.
    rewrite /state_step.
    do 2 (rewrite bool_decide_eq_true_2; [|by eapply elem_of_dom_2]).
    rewrite (lookup_total_correct _ _ _ Hα1).
    rewrite (lookup_total_correct _ _ _ Hα2).
    replace ε with (nnreal_plus ε nnreal_zero); last first.
    { apply nnreal_ext; simpl; lra. }
    unshelve eapply ARcoupl_dbind.
    { exact (λ (n : fin (S N)) (m : fin (S M)), fin_to_nat n = m). }
    { destruct ε ; done. } { simpl ; lra. }
    2: { rewrite -NMε. by apply ARcoupl_dunif_leq. }
    intros n m nm.
    apply ARcoupl_dret.
    simpl in nm. eauto.
  Qed.

  Lemma wp_couple_tapes N M E e α αₛ ns nsₛ Φ (ε : nonnegreal) :
    to_val e = None →
    (∀ σ1, reducible e σ1) →
    nclose specN ⊆ E →
    (0 < S N <= S M)%R →
    (((S M - S N) / S N) = ε)%R →
    spec_ctx ∗
    ▷ α ↪ (N; ns) ∗ ▷ αₛ ↪ₛ (M; nsₛ) ∗
    € ε ∗
    (∀ (n : fin (S N)) (m : fin (S M)),
        ⌜(fin_to_nat n = m)⌝ →
        α ↪ (N; ns ++ [n]) ∗ αₛ ↪ₛ (M; nsₛ ++ [m]) -∗
        WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He Hred ? NMpos NMε) "(#Hinv & >Hα & >Hαₛ & Hε & Hwp)".
    iApply wp_lift_step_fupd_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now) "((Hh1 & Ht1) & Hauth2 & Hε2)".
    iInv specN as (ρ' e0' σ0' n_spec_steps) ">(Hspec0 & %Hexec & Hauth & Hheap & Htapes)" "Hclose".
    iDestruct (spec_interp_auth_frag_agree with "Hauth2 Hspec0") as %<-.
    iDestruct (ghost_map_lookup with "Htapes Hαₛ") as %?.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iSplitR ; [done|].
    (* Get up to speed with the spec resource (tracked in spec_ctx) *)
    iApply exec_coupl_det_r; [done|].
    (* split ε_now into ε + (ε_now - ε) *)
    iDestruct (ec_supply_bound with "Hε2 Hε") as %Hle.
    set (ε' := nnreal_minus ε_now ε Hle ).
    replace ε_now with (nnreal_plus ε ε'); last first.
    { apply nnreal_ext; simpl; lra. }
    (* Do a coupled [state_step] on both sides  *)
    iApply (exec_coupl_state_steps α αₛ).
    { rewrite /= /get_active.
      apply elem_of_list_In, in_prod;
        apply elem_of_list_In, elem_of_elements, elem_of_dom; auto. }
    iExists _.
    iSplit.
    { iPureIntro.
      eapply ARcoupl_state_state ; eauto.
    }
    iIntros (σ2 σ2' (n & m & nm & ? & ?)).
    (* Update our resources *)
    iMod (spec_interp_update (e0', (state_upd_tapes <[αₛ:=(M; nsₛ ++ [m]) : tape]> σ0'))
           with "Hauth2 Hspec0") as "[Hauth2 Hspec0]".
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %?%lookup_total_correct.
    iDestruct (ghost_map_lookup with "Htapes Hαₛ") as %?%lookup_total_correct.
    simplify_map_eq.
    iMod (ghost_map_update ((N; ns ++ [n]) : tape) with "Ht1 Hα") as "[Ht1 Hα]".
    iMod (ghost_map_update ((M; nsₛ ++ [m]) : tape) with "Htapes Hαₛ") as "[Htapes Hαₛ]".
    (* Update Hε2 *)
    iMod (ec_decrease_supply with "Hε2 Hε") as "Hε2".
    (* Close the [spec_ctx] invariant again, so the assumption can access all invariants *)
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hauth Hheap Hspec0 Htapes]") as "_".
    { iModIntro. rewrite /spec_inv.
      iExists _, _, (state_upd_tapes _ _), 0. simpl.
      iFrame. rewrite exec_O dret_1_1 //. }
    (* Our [WP] assumption with the updated resources now suffices to prove the goal *)
    iSpecialize ("Hwp" $! n m nm with "[$Hα $Hαₛ]").
    rewrite !wp_unfold /wp_pre /= He.
    iMod ("Hwp" $! (state_upd_tapes <[α:=(N; ns ++ [n]) : tape]> _)
           with "[$Hh1 $Hauth2 $Ht1 $Hε2]") as "[Hred Hwp]".
    iModIntro. done.
  Qed.


End rules.
