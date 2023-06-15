From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Import fancy_updates ghost_map.
From iris.bi Require Export fixpoint big_op.
From iris.algebra Require Import auth excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.bi Require Import weakestpre.
From clutch.tpr Require Import weakestpre.
From clutch.prob_lang Require Import lang.
From clutch.prob Require Import couplings distribution.

Notation Decidable P := (∀ a, Decision (P a)).

Class mc (A : Type) `{Countable A} := MC {
  mc_step : A → distr A;

  mc_final : A → Prop;
  mc_final_decision :> Decidable mc_final;

  mc_final_is_final a a' :
    mc_final a → mc_step a a' = 0;
}.

(* TODO: move *)
Definition specUR (A : Type) : ucmra := optionUR (exclR (leibnizO A)).
Definition authUR_spec (A : Type) : ucmra := authUR (specUR A).

Class specG (A : Type) (Σ : gFunctors) `{Countable A} := SpecG {
  specG_authUR :> inG Σ (authUR_spec A);
  specG_gname : gname;
}.

Section spec_auth.
  Context `{specG A Σ}.

  Definition spec_auth (a : A) : iProp Σ :=
    own specG_gname (● (Excl' a : specUR _)).
  Definition spec_frag (a : A) : iProp Σ :=
    own specG_gname (◯ (Excl' a : specUR _)).

  Lemma spec_auth_frag_agree a a' :
    spec_auth a -∗ spec_frag a' -∗ ⌜a = a'⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as
      %[Hexcl ?]%auth_both_valid_discrete.
    rewrite Excl_included in Hexcl.
    by apply leibniz_equiv in Hexcl.
  Qed.

  Lemma spec_update a'' a a' :
    spec_auth a -∗ spec_frag a' ==∗ spec_auth a'' ∗ spec_frag a''.
  Proof.
    iIntros "Ha Hf".
    iDestruct (spec_auth_frag_agree with "Ha Hf") as %->.
    iMod (own_update_2 with "Ha Hf") as "[Ha Hf]".
    { eapply auth_update .
      eapply (@option_local_update _ _ _ (Excl a'' : exclR (leibnizO A))).
      by eapply exclusive_local_update. }
    by iFrame.
  Qed.
End spec_auth.

#[global]
Instance spec_auth_spec {A Σ} `{Countable A} `{!mc A, !specG A Σ} : spec A Σ :=
  Spec mc_step spec_auth.

Section mc_exec.
  Context `{mc A}.

  (* TODO: general construction for this pattern where [exec_val] and [mc_exec] are instantiations *)

  Fixpoint mc_exec (n : nat) (a : A) {struct n} : distr A :=
    match bool_decide (mc_final a), n with
      | true, _ => dret a
      | false, 0 => dzero
      | false, S n => mc_step a ≫= mc_exec n
    end.

End mc_exec.

Section adequacy.
  Context `{Countable A, !mc A}.
  Context `{!irisGS prob_lang Σ, !specG A Σ}.

  Lemma step_fupdN_Sn (P : iProp Σ) n :
    (|={∅}▷=>^(S n) P) ⊣⊢ |={∅}▷=> |={∅}▷=>^n P.
  Proof. done. Qed.

  Local Lemma rwp_mc_final φ :
    ∀ e E Φ,
      RWP e @ E ⟨⟨ Φ ⟩⟩ -∗
      ∀ σ a,
        ⌜mc_final a⌝ ∗
        (∀ v, Φ v -∗ ∃ (a' : A), spec_frag a' ∗ ⌜φ v a'⌝) ∗
         state_interp σ ∗ spec_auth a -∗
    |={E,∅}=> ⌜Rcoupl (lim_exec_val (e, σ)) (dret a) φ ⌝.
  Proof.
    iApply rwp_ind; [solve_proper|].
    iIntros "!#" (e E Φ). rewrite /rwp_pre.
    case_match.
    - iIntros "Hvs" (σ a) "(%Hf & Hφ & Hσ & Ha)".
      iMod ("Hvs" with "[$]") as "(?& Hauth &HΦ)".
      iDestruct ("Hφ" with "HΦ") as "[% [Hfrag %]]".
      iDestruct (spec_auth_frag_agree with "Hauth Hfrag") as %<-.
      iApply fupd_mask_intro; [set_solver|]; iIntros "_".
      iPureIntro.
      erewrite lim_exec_val_val; [|done]. by apply Rcoupl_dret.
    - iIntros "Hstep" (σ a) "(%Hf & Hφ & Hσ & Ha)". rewrite /rwp_step /=.
      iMod ("Hstep" with "[$]") as "(% & [(%R & %Hcpl & HR) | (% & %Hcpl & _)])".
      + rewrite lim_exec_val_prim_step prim_step_or_val_no_val //=.
        rewrite -(dret_id_right (dret a)).
        iApply (fupd_mono _ _ (⌜∀ ρ', R ρ' a → Rcoupl (lim_exec_val ρ') (dret a) φ⌝)).
        { iIntros (Hcont). iPureIntro. eapply Rcoupl_dbind; [|by apply Rcoupl_pos_R].
          intros ρ' a' (HR & ? & ->%dret_pos). eauto. }
        iIntros ([e' σ'] HR).
        iMod ("HR"  with "[//]") as "HR".
        iMod "HR" as "(Hσ & Ha & HR)".
        iApply ("HR" with "[$Hσ $Ha $Hφ //]").
      + eapply Rcoupl_pos_R in Hcpl.
        eapply Rcoupl_inhabited_l in Hcpl as (?&?&?&?& Hs); last first.
        { rewrite prim_step_mass //. lra. }
        rewrite mc_final_is_final // in Hs. lra.
  Qed.

  Local Lemma rwp_mc_not_final (φ : val → A → Prop) n :
    ∀ e E Φ,
      RWP e @ E ⟨⟨ Φ ⟩⟩ -∗
      ∀ σ a,
        ⌜¬ mc_final a⌝ ∗
        (∀ v, Φ v -∗ ∃ a', spec_frag a' ∗ ⌜mc_final a'⌝ ∗ ⌜φ v a'⌝) ∗
        (□ (∀ (e' : expr) (σ' : state) (a' : A),
               state_interp σ' ∗ spec_auth a' ∗ RWP e' @ E ⟨⟨ Φ ⟩⟩ ={E,∅}=∗
               |={∅}▷=>^n ⌜mc_exec n a' ≾ lim_exec_val (e', σ') : flip φ⌝)) ∗
        state_interp σ ∗ spec_auth a -∗
      |={E,∅}=> |={∅}▷=>^(S n) ⌜mc_exec (S n) a ≾ lim_exec_val (e, σ) : flip φ⌝.
  Proof.
    iApply rwp_strong_ind; [solve_proper|].
    iIntros "!#" (e E Φ) "Hrwp".
    iIntros (σ a) "[% (Hφ & #IH & Hσ & Ha)] /=".
    rewrite bool_decide_eq_false_2 //.
    rewrite /rwp_pre.
    case_match.
    - iMod ("Hrwp" with "[$]") as "(? & Hauth & HΦ)".
      iDestruct ("Hφ" with "HΦ") as "[% [Hfrag [% %]]]".
      by iDestruct (spec_auth_frag_agree with "Hauth Hfrag") as %<-.
    - rewrite /rwp_step.
      iMod ("Hrwp" with "[$]") as "(% & [(%R & %Hcpl & HR) | (%R & %Hcpl & HR)])".
      + rewrite -(dret_id_left (λ a, mc_step a ≫= mc_exec n)).
        rewrite lim_exec_val_prim_step prim_step_or_val_no_val; [|done].
        iModIntro.
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ ρ', R ρ' a → mc_step a ≫= mc_exec n ≾ lim_exec_val ρ' : flip φ⌝)%I).
        { iIntros (?). iPureIntro.
          eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl', Rcoupl_pos_R].
          intros a' [e' σ'] (HR & Hs & <-%dret_pos). eauto. }
        rewrite -step_fupdN_Sn.
        iIntros ([e' σ'] HR).
        iMod ("HR" with "[//]") as "HR".
        iMod "HR" as "(Hσ' & Ha & HR)".
        iMod ("HR"  with "[$Hφ $IH $Hσ' $Ha //]") as "HR".
        rewrite bool_decide_eq_false_2 //.
      + rewrite lim_exec_val_prim_step prim_step_or_val_no_val; [|done].
        iModIntro.
        iApply (step_fupdN_mono _ _ _ (⌜∀ ρ' a', R ρ' a' → mc_exec n a' ≾ lim_exec_val ρ' : flip φ⌝)%I).
        { iIntros (HR). iPureIntro.
          eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl'].
          intros ???. by apply HR. }
        rewrite -step_fupdN_Sn.
        iIntros ([e' σ'] a' HR) "/=".
        iMod ("HR" with "[//]") as "HR".
        do 2 iModIntro.
        iMod "HR" as "(Hσ' & Ha' & HR)".
        iApply "IH". iFrame.
        rewrite bi.and_elim_r //.
  Qed.

  Theorem wp_refRcoupl_step_fupdN (e : expr) (σ : state) (a : A) (n : nat) (φ : val → A → Prop)  :
    state_interp σ ∗ spec_auth a ∗ RWP e ⟨⟨ v, ∃ (a : A), spec_frag a ∗ ⌜mc_final a⌝ ∗ ⌜φ v a⌝ ⟩⟩ ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜lim_exec_val (e, σ) ≿ mc_exec n a : φ⌝.
  Proof.
    iInduction n as [|n] "IH" forall (e σ a).
    - iIntros "(Hσ & Ha & Hrwp) /=".
      case_bool_decide.
      + iMod (rwp_mc_final with "Hrwp [$Hσ $Ha]") as %Hcpl.
        { iSplit; [done|]. iIntros (v) "(% & ? & % & %)". iExists _. eauto. }
        iModIntro. iPureIntro.
        by apply Rcoupl_refRcoupl'.
      + iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iPureIntro. apply refRcoupl_dzero.
    - iIntros "(Hσ & Ha & Hrwp) /=".
      case_bool_decide as Hf.
      + iMod (rwp_mc_final with "Hrwp [$Hσ $Ha]") as %Hcpl.
        { iSplit; [done|]. iIntros (v) "(% & ? & % & %)". iExists _. eauto. }
        do 4 iModIntro.
        iApply step_fupdN_intro; [done|]. iModIntro.
        iPureIntro. by apply Rcoupl_refRcoupl'.
      + rewrite -step_fupdN_Sn.
        replace (mc_step a ≫= mc_exec n) with (mc_exec (S n) a); last first.
        { rewrite /= bool_decide_eq_false_2 //. }
        iApply (rwp_mc_not_final with "Hrwp [$Hσ $Ha]").
        iFrame "% #". eauto.
   Qed.

End adequacy.
