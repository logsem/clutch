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

  Lemma rwp_mc_final (e : expr) (σ : state) (a : A) (φ : val → A → Prop) Φ E :
    mc_final a →
    (∀ v, Φ v -∗ ∃ (a' : A), spec_frag a' ∗ ⌜φ v a'⌝) ∗
    state_interp σ ∗ spec_auth a ∗ RWP e @ E ⟨⟨ Φ ⟩⟩ ⊢
    |={E,∅}=> ⌜Rcoupl (lim_exec_val (e, σ)) (dret a) φ ⌝.
  Proof.
    iIntros (Hf) "(HΦ & Hσ & Ha & HRWP)".
    iRevert (σ a Hf) "Hσ Ha HΦ"; iRevert "HRWP"; iRevert (e E Φ).
    iApply rwp_ind; [solve_proper|].
    iIntros "!#" (e E Φ). rewrite /rwp_pre.
    case_match.
    - iIntros "Hvs" (σ a Hf) "Hσ Ha Hφ".
      iMod ("Hvs" with "[$]") as "(?& Hauth &HΦ)".
      iDestruct ("Hφ" with "HΦ") as "[% [Hfrag %]]".
      iDestruct (spec_auth_frag_agree with "Hauth Hfrag") as %<-.
      iApply fupd_mask_intro; [set_solver|]; iIntros "_".
      iPureIntro.
      erewrite lim_exec_val_val; [|done]. by apply Rcoupl_dret.
    - iIntros "Hstep" (σ a Hf) "Hσ Ha Hφ". rewrite /rwp_step /=.
      iMod ("Hstep" with "[$]") as "(% & [(%R & %Hcpl & HR) | (% & %Hcpl & _)])".
      + rewrite lim_exec_val_prim_step prim_step_or_val_no_val //=.
        rewrite -(dret_id_right (dret a)).
        iApply (fupd_mono _ _ (⌜∀ ρ', R ρ' a → Rcoupl (lim_exec_val ρ') (dret a) φ⌝)).
        { iIntros (Hcont). iPureIntro. eapply Rcoupl_dbind; [|by apply Rcoupl_pos_R].
          intros ρ' a' (HR & ? & ->%dret_pos). eauto. }
        iIntros ([e' σ'] HR).
        iMod ("HR"  with "[//]") as "HR".
        iMod "HR" as "(?&?&HR)".
        iMod ("HR" with "[//] [$] [$] [$]"). done.
      + eapply Rcoupl_pos_R in Hcpl.
        eapply Rcoupl_inhabited_l in Hcpl as (?&?&?&?& Hs); last first.
        { rewrite prim_step_mass //. lra. }
        rewrite mc_final_is_final // in Hs. lra.
  Qed.

  Theorem wp_refRcoupl_step_fupdN (e : expr) (σ : state) (a : A) (n : nat) (φ : val → A → Prop)  :
    state_interp σ ∗ spec_auth a ∗ RWP e ⟨⟨ v, ∃ (a : A), spec_frag a ∗ ⌜mc_final a⌝ ∗ ⌜φ v a⌝ ⟩⟩ ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜lim_exec_val (e, σ) ≿ mc_exec n a : φ⌝.
  Proof.
    iInduction n as [|n] "IH" forall (e σ a).
    - iIntros "(Hσ & Ha & Hrwp) /=".
      case_bool_decide.
      + iMod (rwp_mc_final with "[$Hσ $Ha $Hrwp]") as %Hcpl; [done| |].
        { iIntros (v) "(% & ? & % & %)". iExists _. eauto. }
        iModIntro. iPureIntro.
        by apply Rcoupl_refRcoupl'.
      + iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iPureIntro. apply refRcoupl_dzero.
    - iIntros "(Hσ & Ha & Hrwp) /=".
      case_bool_decide.
      + iMod (rwp_mc_final with "[$Hσ $Ha $Hrwp]") as %Hcpl; [done| |].
        { iIntros (v) "(% & ? & % & %)". iExists _. eauto. }
        do 4 iModIntro.
        iApply step_fupdN_intro; [done|]. iModIntro.
        iPureIntro. by apply Rcoupl_refRcoupl'.
      + rewrite rwp_unfold /rwp_pre.
        case_match.
        { iMod ("Hrwp" with "[$]") as "(? & Hauth & (% & Hfrag & % & %))".
          by iDestruct (spec_auth_frag_agree with "Hauth Hfrag") as %<-. }
        rewrite /rwp_step.
        iMod ("Hrwp" with "[$]") as "(% & [(%R & %Hcpl & HR) | (% & %Hcpl & _)])".
        * (* Hmmm... Our induction step now wants us to reason about a step of
             the model, [mc_step], but the case of the [RWP] we're considering is
             only taking a step of the program ([Hcpl])... *)


    Admitted.

End adequacy.
