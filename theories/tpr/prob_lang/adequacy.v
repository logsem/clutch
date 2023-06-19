From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Import fancy_updates ghost_map.
From iris.bi Require Export fixpoint big_op.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.tpr Require Import weakestpre spec_ra.
From clutch.prob_lang Require Import lang.
From clutch.prob Require Import couplings distribution markov.

(* TODO: move *)
Class tprG A Σ := TprG {
  tprG_invG :> invGS_gen HasNoLc Σ;
  tprG_heap  : ghost_mapG Σ loc val;
  tprG_tapes : ghost_mapG Σ loc tape;
  tprG_heap_name : gname;
  tprG_tapes_name : gname;
  tprG_specG :> specG A Σ;
}.

Definition heap_auth `{tprG Σ} :=
  @ghost_map_auth _ _ _ _ _ tprG_heap tprG_heap_name.
Definition tapes_auth `{tprG Σ} :=
  @ghost_map_auth _ _ _ _ _ tprG_tapes tprG_tapes_name.

Global Instance tprG_tprwpG `{!tprG A Σ} : tprwpG prob_lang Σ := {
  iris_invGS := _;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes))%I;
}.

#[global]
Instance spec_auth_spec {A B Σ} `{Countable A} `{!markov A B, !specG A Σ} : spec A Σ :=
  Spec step specA.

Section adequacy.
  Context {A B} `{Countable A, Countable B, !markov A B, tprG A Σ}.

  Lemma step_fupdN_Sn (P : iProp Σ) n :
    (|={∅}▷=>^(S n) P) ⊣⊢ |={∅}▷=> |={∅}▷=>^n P.
  Proof. done. Qed.

  #[local] Lemma rwp_mc_final (φ : val → B → Prop) :
    ∀ e E Φ,
      RWP e @ E ⟨⟨ Φ ⟩⟩ -∗
      ∀ σ a b,
        ⌜to_final a = Some b⌝ ∗
        (∀ v, Φ v -∗ ∃ (a' : A) (b' : B), specF a' ∗ ⌜to_final a' = Some b'⌝ ∗ ⌜φ v b'⌝) ∗
         state_interp σ ∗ specA a -∗
    |={E,∅}=> ⌜Rcoupl (lim_exec_val (e, σ)) (dret b) φ ⌝.
  Proof.
    iApply rwp_ind; [solve_proper|].
    iIntros "!#" (e E Φ). rewrite /rwp_pre.
    case_match.
    - iIntros "Hvs" (σ a b) "(%Hf & Hφ & Hσ & Ha)".
      iMod ("Hvs" with "[$]") as "(?& Hauth &HΦ)".
      iDestruct ("Hφ" with "HΦ") as "(% & % & Hfrag & % & %)".
      iDestruct (specA_frag_agree with "Hauth Hfrag") as %<-.
      simplify_option_eq.
      iApply fupd_mask_intro; [set_solver|]; iIntros "_".
      iPureIntro.
      erewrite lim_exec_val_val; [|done]. by apply Rcoupl_dret.
    - iIntros "Hstep" (σ a b) "(%Hf & Hφ & Hσ & Ha)". rewrite /rwp_step /=.
      iMod ("Hstep" with "[$]") as "(% & [(%R & %Hcpl & HR) | (% & %Hcpl & _)])".
      + rewrite lim_exec_val_prim_step prim_step_or_val_no_val //=.
        rewrite -(dret_id_left (λ _, dret b) a).
        iApply (fupd_mono _ _ (⌜∀ ρ', R ρ' a → Rcoupl (lim_exec_val ρ') (dret b) φ⌝)).
        { iIntros (Hcont). iPureIntro. eapply Rcoupl_dbind; [|by apply Rcoupl_pos_R].
          intros ρ' a' (HR & ? & ->%dret_pos). eauto. }
        iIntros ([e' σ'] HR).
        iMod ("HR"  with "[//]") as "HR".
        iMod "HR" as "(Hσ & Ha & HR)".
        iApply ("HR" with "[$Hσ $Ha $Hφ //]").
      + eapply Rcoupl_pos_R in Hcpl.
        eapply Rcoupl_inhabited_l in Hcpl as (?&?&?&?& Hs); last first.
        { rewrite prim_step_mass //. lra. }
        rewrite to_final_is_final // in Hs. lra.
  Qed.

  #[local] Lemma rwp_mc_not_final (φ : val → B → Prop) n :
    ∀ e E Φ,
      RWP e @ E ⟨⟨ Φ ⟩⟩ -∗
      ∀ (σ : state) (a : A),
        ⌜¬ is_final a⌝ ∗
        (∀ v, Φ v -∗ ∃ (a' : A) (b : B), specF a' ∗ ⌜to_final a' = Some b⌝ ∗ ⌜φ v b⌝) ∗
        (□ (∀ (e' : expr) (σ' : state) (a' : A),
               state_interp σ' ∗ specA a' ∗ RWP e' @ E ⟨⟨ Φ ⟩⟩ ={E,∅}=∗
               |={∅}▷=>^n ⌜lim_exec_val (e', σ') ≿ exec n a' : φ⌝)) ∗
        state_interp σ ∗ specA a -∗
      |={E,∅}=> |={∅}▷=>^(S n) ⌜lim_exec_val (e, σ) ≿ exec (S n) a : φ⌝.
  Proof.
    iApply rwp_strong_ind; [solve_proper|].
    iIntros "!#" (e E Φ) "Hrwp".
    iIntros (σ a) "[% (Hφ & #IH & Hσ & Ha)] /=".
    rewrite to_final_None_1 //.
    rewrite /rwp_pre.
    case_match.
    - iMod ("Hrwp" with "[$]") as "(? & Hauth & HΦ)".
      iDestruct ("Hφ" with "HΦ") as "(% & % & [Hfrag [%Hf %]])".
      apply to_final_Some_2 in Hf.
      by iDestruct (specA_frag_agree with "Hauth Hfrag") as %<-.
    - rewrite /rwp_step.
      iMod ("Hrwp" with "[$]") as "(% & [(%R & %Hcpl & HR) | (%R & %Hcpl & HR)])".
      + rewrite -(dret_id_left (λ a, step a ≫= exec n)).
        rewrite lim_exec_val_prim_step prim_step_or_val_no_val; [|done].
        iModIntro.
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ ρ', R ρ' a → step a ≫= exec n ≾ lim_exec_val ρ' : flip φ⌝)%I).
        { iIntros (?). iPureIntro.
          eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl', Rcoupl_pos_R].
          intros a' [e' σ'] (HR & Hs & <-%dret_pos). eauto. }
        rewrite -step_fupdN_Sn.
        iIntros ([e' σ'] HR).
        iMod ("HR" with "[//]") as "HR".
        iMod "HR" as "(Hσ' & Ha & HR)".
        iMod ("HR"  with "[$Hφ $IH $Hσ' $Ha //]") as "HR".
        rewrite to_final_None_1 //.
      + rewrite lim_exec_val_prim_step prim_step_or_val_no_val; [|done].
        iModIntro.
        iApply (step_fupdN_mono _ _ _ (⌜∀ ρ' a', R ρ' a' → exec n a' ≾ lim_exec_val ρ' : flip φ⌝)%I).
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

  Theorem wp_refRcoupl_step_fupdN (e : expr) (σ : state) (a : A) (n : nat) (φ : val → B → Prop)  :
    state_interp σ ∗ specA a ∗ RWP e ⟨⟨ v, ∃ a' b, specF a' ∗ ⌜to_final a' = Some b⌝ ∗ ⌜φ v b⌝ ⟩⟩ ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜lim_exec_val (e, σ) ≿ exec n a : φ⌝.
  Proof.
    iInduction n as [|n] "IH" forall (e σ a).
    - iIntros "(Hσ & Ha & Hrwp) /=".
      case_match.
      + iMod (rwp_mc_final with "Hrwp [$Hσ $Ha]") as %Hcpl.
        { iSplit; [eauto with markov|]. iIntros (v) "(%a' & % & ? & % & %)". iExists _. eauto. }
        iModIntro. iPureIntro.
        by apply Rcoupl_refRcoupl'.
      + iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iPureIntro. apply refRcoupl_dzero.
    - iIntros "(Hσ & Ha & Hrwp) /=".
      case_match.
      + iMod (rwp_mc_final with "Hrwp [$Hσ $Ha]") as %Hcpl.
        { iSplit; [done|]. iIntros (v) "(% & % & ? & % & %)". iExists _. eauto. }
        do 4 iModIntro.
        iApply step_fupdN_intro; [done|]. iModIntro.
        iPureIntro. by apply Rcoupl_refRcoupl'.
      + rewrite -step_fupdN_Sn.
        replace (step a ≫= exec n) with (exec (S n) a); last first.
        { rewrite exec_Sn step_or_final_no_final //. eauto with markov. }
        iApply (rwp_mc_not_final with "Hrwp [$Hσ $Ha]").
        iFrame "% #". eauto with markov.
   Qed.

End adequacy.

Class tprGpreS A Σ := TprGpreS {
  tprGpre_iris  :> invGpreS Σ;
  tprGpre_heap  :> ghost_mapG Σ loc val;
  tprGpre_tapes :> ghost_mapG Σ loc tape;
  tpr_spec      :> specPreG A Σ;
}.

Definition tprΣ A: gFunctors :=
  #[invΣ;
    ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    specΣ A].
Global Instance subG_tprGPreS {A Σ} : subG (tprΣ A) Σ → tprGpreS A Σ.
Proof. solve_inG. Qed.

Theorem wp_refRcoupl `{Countable A, Countable B} `{!markov A B} Σ `{!tprGpreS A Σ} e σ a n φ :
  (∀ `{!tprG A Σ},
    ⊢ specF a -∗ RWP e ⟨⟨ v, ∃ a' b, specF a' ∗ ⌜to_final a' = Some b⌝ ∗ ⌜φ v b⌝ ⟩⟩) →
  lim_exec_val (e, σ) ≿ exec n a : φ.
Proof.
  intros Hwp.
  eapply (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod (spec_alloc a) as (HspecG) "[Hauth Hfrag]".
  set (HclutchG := TprG _ Σ _ _ _ γH γT HspecG).
  iApply wp_refRcoupl_step_fupdN.
  iFrame.
  by iApply (Hwp with "[Hfrag]").
Qed.

Corollary wp_refRcoupl_mass `{Countable A, Countable B} `{!markov A B} Σ `{!tprGpreS A Σ} e σ a :
  (∀ `{!tprG A Σ}, ⊢ specF a -∗ RWP e ⟨⟨ v, ∃ a', specF a' ∗ ⌜is_final a'⌝ ⟩⟩) →
  SeriesC (lim_exec a) <= SeriesC (lim_exec_val (e, σ)).
Proof.
  intros Hrwp.
  apply lim_exec_continous_mass.
  intros.
  eapply (refRcoupl_mass_eq _ _ (λ _ _, True)).
  eapply wp_refRcoupl; [done|].
  iIntros (?) "Hfrag".
  iApply rwp_mono; [|iApply (Hrwp with "Hfrag")].
  iIntros (?) "(% & ? & [% %])". eauto.
Qed.
