From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Import fancy_updates ghost_map.
From iris.bi Require Export fixpoint big_op.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.tpr Require Import weakestpre spec.
From clutch.prob_lang Require Import lang.
From clutch.prob Require Import couplings distribution markov.

(* TODO: generalize to any language *)


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

Section adequacy.
  Context {A B} `{Countable A, Countable B, !markov A B, tprG A Σ}.
  Implicit Type e : expr.
  Implicit Type σ : state.
  Implicit Type a : A.
  Implicit Type b : B.                     

  Lemma step_fupdN_Sn (P : iProp Σ) n :
    (|={∅}▷=>^(S n) P) ⊣⊢ |={∅}▷=> |={∅}▷=>^n P.
  Proof. done. Qed.

  #[local] Lemma rwp_mc_final (φ : val → B → Prop) e σ E a b :
    to_final a = Some b →
    RWP e @ E ⟨⟨ v, ∃ a' b', specF a' ∗ ⌜to_final a' = Some b'⌝ ∗ ⌜φ v b'⌝ ⟩⟩ -∗
    state_interp σ ∗ specA a ={E,∅}=∗
    ⌜Rcoupl (lim_exec_val (e, σ)) (dret b) φ ⌝.
  Proof.
    iIntros (Hf) "Hrwp".
    iRevert (σ Hf).
    iApply (rwp_ind' (λ E e, _) with "[] Hrwp").
    clear.
    iIntros "!#" (e E) "Hrwp %σ %Hf [Hσ Ha]".
    rewrite /rwp_pre.
    iSpecialize ("Hrwp" with "[$]").
    case_match eqn:Hv.
    - iMod "Hrwp" as "(? & Hauth & (% & % & Hfrag & % & %))".
      iDestruct (spec_auth_agree with "Hauth Hfrag") as %<-.
      simplify_option_eq.
      iApply fupd_mask_intro; [set_solver|]; iIntros "_".
      iPureIntro.
      erewrite lim_exec_val_val; [|done]. by apply Rcoupl_dret.
    - rewrite rwp_coupl_unfold.
      iMod "Hrwp" as (?) "[%R [(% & HR) | [(%Hcpl & HR) | (%Hcpl & HR)]]]".
      + rewrite lim_exec_val_prim_step prim_step_or_val_no_val //=.
        rewrite -{2}(dret_id_left (λ _, dret b) a).
        iApply (fupd_mono _ _ (⌜∀ ρ', R ρ' a → Rcoupl (lim_exec_val ρ') (dret b) φ⌝)).
        { iIntros (Hcont). iPureIntro. eapply Rcoupl_dbind; [|by apply Rcoupl_pos_R].
          intros ρ' a' (HR & ? & ->%dret_pos). eauto. }
        iIntros ([e' σ'] HR).
        iMod ("HR"  with "[//]") as "HR".
        iMod "HR" as "(Hσ & Ha & HR)".
        iApply ("HR" with "[//] [$Hσ $Ha]").
      + eapply Rcoupl_pos_R in Hcpl.
        eapply Rcoupl_inhabited_l in Hcpl as (?&?&?&?& Hs); last first.
        { rewrite dret_mass //. lra. }
        rewrite to_final_is_final // in Hs. lra.
      + eapply Rcoupl_pos_R in Hcpl.
        eapply Rcoupl_inhabited_l in Hcpl as (?&?&?&?& Hs); last first.
        { rewrite prim_step_mass //. lra. }
        rewrite to_final_is_final // in Hs. lra.
  Qed.
  
  #[local] Lemma rwp_mc_not_final (φ : val → B → Prop) n e σ E a :
    let Φ v := (∃ a' b, specF a' ∗ ⌜to_final a' = Some b⌝ ∗ ⌜φ v b⌝)%I in
    to_final a = None →
    RWP e @ E ⟨⟨ Φ ⟩⟩ -∗
    (□ (∀ e' σ' a',
           state_interp σ' ∗ specA a' ∗ RWP e' @ E ⟨⟨ Φ ⟩⟩ ={E,∅}=∗
           |={∅}▷=>^n ⌜lim_exec_val (e', σ') ≿ exec n a' : φ⌝)) ∗
    state_interp σ ∗ specA a ={E,∅}=∗ |={∅}▷=>^(S n) 
    ⌜lim_exec_val (e, σ) ≿ exec (S n) a : φ⌝.
  Proof. 
    iIntros (Φ Hnf) "Hrwp". 
    iRevert (σ a Hnf).
    iApply (rwp_strong_ind' (λ E e, _) with "[] Hrwp").
    clear e E.
    iIntros "!>" (e E) "Hrwp %σ %a %Hnf (#IH & Hσ & Ha)".
    rewrite /rwp_pre /Φ.
    iSpecialize ("Hrwp" with "[$]").
    case_match eqn:Hv.
    - iMod "Hrwp" as "(?& Hauth & (% & % & Hfrag & % & ?))".
      iDestruct (spec_auth_agree with "Hauth Hfrag") as %<-. 
      simplify_option_eq.
    - iMod "Hrwp" as "(%Hred & H)". iModIntro.
      
      (* iRevert (Hv Hred Hnf). *)
      (* iApply (rwp_coupl_ind (λ e σ a, _) with "[] H"). *)
      (* clear e σ a. *)
      rewrite rwp_coupl_unfold.
      iDestruct "H" as "[%R [(% & HR) | [(%Hcpl & HR) | (%Hcpl & HR)]]]".
      (* iIntros "!#" (e σ a') "[%R [(% & HR) | [(%Hcpl & HR) | (%Hcpl & HR)]]] % % %". *)
      + (* [rwp_coupl] base case *)
        iEval (rewrite -(dret_id_left (exec (S n)))).
        rewrite lim_exec_val_prim_step prim_step_or_val_no_val; [|done].
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ ρ', R ρ' a → exec (S n) a ≾ lim_exec_val ρ' : flip φ⌝)%I).
        { iIntros (Hcnt). iPureIntro.
          eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl', Rcoupl_pos_R].
          intros a1 [e' σ'] (HR & Hs & <-%dret_pos). eauto. }
        iIntros ([e' σ'] HR).
        iMod ("HR" with "[//]") as "HR".
        iMod "HR" as "(Hσ' & Ha & HR)".
        by iMod ("HR" with "[//] [$Hσ' $Ha $IH]") as "HR".
      + (* [rwp_coupl] inductive case *)
        rewrite exec_Sn_not_final; [|by eapply to_final_None_2].
        iEval (rewrite -(dret_id_left (lim_exec_val))).
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ a, R (e, σ) a → exec n a ≾ lim_exec_val (e, σ) : flip φ⌝)%I).
        { iIntros (HR). iPureIntro.
          eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl', Rcoupl_pos_R].
          intros a1 [? ?] (? & [= -> ->]%dret_pos & Hs). eauto. }
        iIntros (a'' HR).
        iMod ("HR" with "[//]") as "HR".
        do 3 iModIntro. 
        admit. 

          
        
      + (* [rwp_coupl] base case *)
        rewrite lim_exec_val_prim_step prim_step_or_val_no_val; [|done].
        rewrite exec_Sn_not_final; [|by eapply to_final_None_2].
        iApply (step_fupdN_mono _ _ _ (⌜∀ ρ' a', R ρ' a' → exec n a' ≾ lim_exec_val ρ' : flip φ⌝)%I).
        { iIntros (HR). iPureIntro.
          eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl'].
          intros ???. by apply HR. }
        iIntros ([e' σ'] a0 HR) "/=".
        iMod ("HR" with "[//]") as "HR".
        do 2 iModIntro.
        iMod "HR" as "(Hσ' & Ha' & [_ HR])".
        iApply "IH". iFrame.
  Admitted.
        

  Theorem wp_refRcoupl_step_fupdN (e : expr) (σ : state) (a : A) (n : nat) (φ : val → B → Prop)  :
    state_interp σ ∗ specA a ∗ RWP e ⟨⟨ v, ∃ a' b, specF a' ∗ ⌜to_final a' = Some b⌝ ∗ ⌜φ v b⌝ ⟩⟩ ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜lim_exec_val (e, σ) ≿ exec n a : φ⌝.
  Proof.
    iInduction n as [|n] "IH" forall (e σ a).
    - iIntros "(Hσ & Ha & Hrwp) /=".
      case_match.
      + iMod (rwp_mc_final with "Hrwp [$Hσ $Ha]") as %Hcpl; [done|].
        iModIntro. iPureIntro.
        by apply Rcoupl_refRcoupl'.
      + iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iPureIntro. apply refRcoupl_dzero.
    - iIntros "(Hσ & Ha & Hrwp) /=".
      case_match.
      + iMod (rwp_mc_final with "Hrwp [$Hσ $Ha]") as %Hcpl; [done|].
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
  iMod (spec_auth_alloc a) as (HspecG) "[Hauth Hfrag]".
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
  apply lim_exec_leq_mass.
  intros.
  eapply (refRcoupl_mass_eq _ _ (λ _ _, True)).
  eapply wp_refRcoupl; [done|].
  iIntros (?) "Hfrag".
  iApply rwp_mono; [|iApply (Hrwp with "Hfrag")].
  iIntros (?) "(% & ? & [% %])". eauto.
Qed.
