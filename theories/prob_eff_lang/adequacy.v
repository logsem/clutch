From iris.proofmode       Require Import base tactics classes proofmode.
From iris.base_logic.lib  Require Import ghost_map.
From clutch.approxis      Require Import app_weakestpre adequacy primitive_laws.
From clutch.prob_eff_lang Require Import weakestpre protocol_agreement iEff lang spec_ra erasure.
Import uPred.



Notation "'EWP' e @ E  <| Ψ '|' '>' {{ v , Φ } }" :=
  (ewp_def E e%E Ψ%ieff (λ v, Φ)%I)
  (at level 20, e, E, Ψ, Φ at level 200,
     format "'[' 'EWP'  e  '/' '[' @ E <|  Ψ  '|' '>'  {{  v ,  Φ  } } ']' ']'") : bi_scope.

Notation "'EWP' e @ E  <| Ψ '|' '>' {{ Φ } }" :=
  (ewp_def E e%E Ψ%ieff Φ)
  (at level 20, e, E, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[' @ E <|  Ψ  '|' '>'  {{ Φ } } ']' ']'") : bi_scope.


Lemma ewp_imp_wp `{!spec_updateGS (lang_markov eff_prob_lang) Σ,
                     !app_weakestpre.approxisWpGS eff_prob_lang Σ}
  (e : expr) (Φ : val → iProp Σ) :
  EWP e @ ⊤ <| iEff_bottom |> {{ v, Φ v }} ⊢
  WP e @ ⊤ {{v, Φ v }}.
Proof.
  iLöb as "IH" forall (e).
  destruct (to_val e) as [ v    |] eqn:?; [|
  destruct (to_eff e) as [(v, k)|] eqn:?  ].
  - rewrite ewp_unfold /ewp_pre wp_unfold /wp_pre /= Heqo.  iIntros "$".
  - rewrite -(of_to_eff _ _ _ Heqo0).
    iIntros "Hewp".
    rewrite ewp_unfold /ewp_pre wp_unfold /wp_pre /=.
    iIntros (σ1 e1' σ1' ε1) "(Hstate&Hspec&Herr)".
    iMod ("Hewp" with "[Hstate Hspec Herr]") as "Hewp"; [iFrame|].
    iModIntro.
    iApply spec_coupl_bind; [done | | iFrame "Hewp"].
    iIntros (????) "Hewp".
    iApply fupd_spec_coupl.
    iMod "Hewp" as "(?&?&?&Hpa)".
    by rewrite protocol_agreement_bottom.
  - rewrite ewp_unfold /ewp_pre wp_unfold /wp_pre /= Heqo Heqo0.
    iIntros "H" (σ1 e1' σ1' ε1) "(Hstate & Hspec & Herr)".
    iMod ("H" with "[$Hstate $Hspec $Herr]") as "H".
    iModIntro.
    iApply spec_coupl_mono; [done | | done].
    iIntros (σ2 e2' σ2' ε2) "H".
    iApply prog_coupl_mono; [|done].
    iIntros (e3 σ3 e3' σ3' ε3) "H". iNext.
    iApply spec_coupl_mono; [done | | done].
    iIntros (σ5 e4' σ4 ε4) "H".
    iMod "H" as "(?&?&?&?)". iModIntro. iFrame.
    by iApply "IH".
Qed.

(* Move to a separate file *)
Class probeffGS Σ := HeapG {
  probeffGS_invG : invGS_gen HasNoLc Σ;
  (* CMRA for the state *)
  probeffGS_heap : ghost_mapG Σ loc val;
  probeffGS_tapes : ghost_mapG Σ loc tape;
  (* ghost names for the state *)
  probeffGS_heap_name : gname;
  probeffGS_tapes_name : gname;
  (* CMRA and ghost name for the spec *)
  probeffGS_spec :: specG_prob_eff_lang Σ;
  (* CMRA and ghost name for the error *)
  probeffGS_error :: ecGS Σ;
}.

Class probeffGpreS Σ := ProbeffGpreS {
  probeffGpreS_iris  :: invGpreS Σ;
  probeffGpreS_heap  :: ghost_mapG Σ loc val;
  probeffGpreS_tapes :: ghost_mapG Σ loc tape;
  probeffGpreS_spec :: specGpreS Σ;
  probeffGpreS_err   :: ecGpreS Σ;
                          }.

Definition heap_auth `{probeffGS Σ} :=
  @ghost_map_auth _ _ _ _ _ probeffGS_heap probeffGS_heap_name.
Definition tapes_auth `{probeffGS Σ} :=
  @ghost_map_auth _ _ _ _ _ probeffGS_tapes probeffGS_tapes_name.

Global Instance probeffGS_irisGS `{!probeffGS Σ} : approxisWpGS eff_prob_lang Σ := {
  approxisWpGS_invGS := probeffGS_invG;
  state_interp σ := (heap_auth 1 σ.(heap) ∗ tapes_auth 1 σ.(tapes))%I;
  err_interp := ec_supply;
}.

Section adequacy.
  Context `{probeffGS Σ}.

  Lemma ewp_adequacy_spec_coupl n m e1 σ1 e1' σ1' Z φ ε :
    spec_coupl ∅ σ1 e1' σ1' ε Z -∗
    (∀ σ2 e2' σ2' ε', Z σ2 e2' σ2' ε' ={∅}=∗ |={∅}▷=>^n ⌜ARcoupl (exec m (e1, σ2)) (lim_exec (e2', σ2')) φ ε'⌝) -∗
    |={∅}=> |={∅}▷=>^n ⌜ARcoupl (exec m (e1, σ1)) (lim_exec (e1', σ1')) φ ε⌝.
  Proof.
    iRevert (σ1 e1' σ1' ε).
    iApply spec_coupl_ind.
    iIntros "!>" (σ1 e1' σ1' ε)
      "[% | [H | (%T & %k & %μ1 & %μ1' & %ε' & %X2 & %r & % & % & % & %Hμ1 & %Hμ1' & H)]] HZ".
    - iApply step_fupdN_intro; [done|].
      do 2 iModIntro. iPureIntro. by apply ARcoupl_1.
    - by iMod ("HZ" with "[$]").
    - iApply (step_fupdN_mono _ _ _ ⌜_⌝).
      { iPureIntro. intros. eapply ARcoupl_erasure_erasable_exp_rhs; [..|done]; eauto. }
      iIntros (σ2 e2' σ2' HT).
      iMod ("H" with "[//]") as "[H _]".
      by iApply "H".
  Qed.

 Lemma ewp_adequacy_prog_coupl n m e1 σ1 e1' σ1' Z φ ε :
    to_val e1 = None ->
    prog_coupl e1 σ1 e1' σ1' ε Z -∗
    (∀ e2 σ2 e2' σ2' ε', Z e2 σ2 e2' σ2' ε' ={∅}=∗ |={∅}▷=>^n ⌜ARcoupl (exec m (e2, σ2)) (lim_exec (e2', σ2')) φ ε'⌝) -∗
    |={∅}=> |={∅}▷=>^n ⌜ARcoupl (exec (S m) (e1, σ1)) (lim_exec (e1', σ1')) φ ε⌝.
  Proof.
    iIntros (Hnone).
    rewrite exec_Sn.
    rewrite /step_or_final /= Hnone.
    iIntros "(%R & %k & %μ1' & %ε1 & %X2 & %r & % & % & % & % & % & Hcnt) Hcoupl /=".
    iApply (step_fupdN_mono _ _ _ ⌜_⌝).
    { iPureIntro. intros. eapply ARcoupl_erasure_erasable_exp_lhs; [..|done]; eauto. }
    iIntros (e2 σ2 e2' σ2' ε2).
    iMod ("Hcnt" with "[//]") as "Hcnt".
    by iApply "Hcoupl".
  Qed.

  Lemma ewp_adequacy_val_fupd (e e' : expr) (σ σ' : state) n φ v ε:
    to_val e = Some v →
    state_interp σ ∗ spec_interp (e', σ') ∗ err_interp ε ∗
    EWP e @ ⊤ <| iEff_bottom |> {{ v, ∃ v' : val, ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤, ∅}=> ⌜ARcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ ε⌝.
  Proof.
    iIntros (He) "(Hσ & Hs & Hε & Hwp)".
    rewrite ewp_unfold /ewp_pre /= He.
    iMod ("Hwp" with "[$]") as "Hwp".
    iApply (ewp_adequacy_spec_coupl 0 with "Hwp").
    iIntros (σ1 e1' σ1' ε') "> (? & Hs & Hε & (% & Hv & %)) /=".
    iDestruct (spec_auth_prog_agree with "Hs Hv") as %->.
    erewrite exec_is_final; [|done].
    erewrite lim_exec_final; [|done].
    iApply fupd_mask_intro; [set_solver|]; iIntros "_".
    iPureIntro. by eapply ARcoupl_dret.
  Qed.

  Lemma ewp_adequacy_step_fupdN ε (e e' : expr) (σ σ' : state) n φ :
    state_interp σ ∗ spec_interp (e', σ') ∗ err_interp ε ∗
    EWP e @ ⊤ <| iEff_bottom |> {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜ARcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ ε⌝.
  Proof.
    iIntros "(Hσ & HspecI_auth & Hε & Hwp)".
    iInduction n as [|n] "IH" forall (e σ e' σ' ε).
    {   destruct (to_val e) as [ v         |] eqn:He;
      [|destruct (to_eff e) as [(v, k)|] eqn:He'].
        - iMod (ewp_adequacy_val_fupd with "[$]") as %?; [done|].
          by iApply step_fupdN_intro.
        - rewrite ewp_unfold /ewp_pre. rewrite He He'.
          iMod ("Hwp" with "[$]") as "Hewp".
          iApply (ewp_adequacy_spec_coupl 0 with "Hewp").
          iIntros (????) ">(?&?&?&Hpa)".
          by iDestruct (protocol_agreement_bottom with "Hpa") as "Hcontra".
        - iApply fupd_mask_intro; [done|]; iIntros "_ /=".
          iPureIntro. rewrite He. by apply ARcoupl_dzero. }
     destruct (to_val e) as [ v         |] eqn:He;
   [|destruct (to_eff e) as [(v, k)|]      eqn:He'].
    { iMod (ewp_adequacy_val_fupd with "[$]") as %?; [done|].
      iApply step_fupdN_intro; [done|].
      do 3 iModIntro. done. }
    { rewrite ewp_unfold /ewp_pre. rewrite He He'.
      iMod ("Hwp" with "[$]") as "Hewp".
      iApply (ewp_adequacy_spec_coupl with "Hewp").
      iIntros (????) ">(?&?&?&Hpa)".
      by iDestruct (protocol_agreement_bottom with "Hpa") as "Hcontra". }
    iEval (rewrite ewp_unfold /ewp_pre /= He He') in "Hwp".
    iMod ("Hwp" with "[$]") as "Hwp".
    iApply (ewp_adequacy_spec_coupl with "Hwp").
    iIntros (σ2 e2' σ2' ε') "Hprog".
    iApply (ewp_adequacy_prog_coupl with "Hprog"); [done|].
    iIntros (e3 σ3 e3' σ3' ε3) "Hspec".
    iIntros "!> !> !>".
    iApply (ewp_adequacy_spec_coupl with "Hspec").
    iIntros (σ4 e4' σ4' ε4) ">(Hσ & Hs & Hε & Hcnt)".
    iApply ("IH" with "Hσ Hs Hε Hcnt").
  Qed.

End adequacy.
  

Lemma ewp_adequacy_exec_n Σ `{!probeffGpreS Σ} (e e' : expr) (σ σ' : state) n φ (ε : R) :
  (0 <= ε)%R →
  (∀ `{probeffGS Σ}, ⊢ ⤇ e' -∗ ↯ ε -∗ EWP e @ ⊤ <| iEff_bottom |> {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }}) →
  ARcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ ε.
Proof.
  intros Heps Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod spec_ra_init as (HspecGS) "(Hs & Hj & ?)".
  destruct (decide (ε < 1)%R) as [? | H%Rnot_lt_le].
  - set ε' := mknonnegreal _ Heps.
    iMod (ec_alloc ε') as (?) "[HE He]"; [done|].
    set (HprobeffGS := HeapG Σ _ _ _ γH γT HspecGS _).
    iApply (ewp_adequacy_step_fupdN ε').
    iFrame "Hh Ht Hs HE".
    by iApply (Hwp with "[Hj] [He]").
  - iApply fupd_mask_intro; [done|]; iIntros "_".
    iApply step_fupdN_intro; [done|]; iModIntro.
    iPureIntro. by apply ARcoupl_1.
Qed.



Theorem ewp_adequacy Σ `{probeffGpreS Σ} (e e' : expr) (σ σ' : state) (ε : R) φ :
  (0 <= ε)%R →
  (∀ `{probeffGS Σ}, ⊢  ⤇ e' -∗ ↯ ε -∗ EWP e @ ⊤ <| iEff_bottom |> {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
  ARcoupl (lim_exec (e, σ)) (lim_exec (e', σ')) φ ε.
Proof.
  intros ? Hewp.
  apply lim_exec_ARcoupl; [done|].
  intros n.
  by eapply ewp_adequacy_exec_n.
Qed.

Corollary ewp_adequacy_error_lim Σ `{probeffGpreS Σ} (e e' : expr) (σ σ' : state) (ε : R) φ :
  (0 <= ε)%R →
  (∀ `{probeffGS Σ} (ε' : R),
      (ε < ε')%R → ⊢ ⤇ e' -∗ ↯ ε' -∗ EWP e @ ⊤ <| iEff_bottom |> {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
  ARcoupl (lim_exec (e, σ)) (lim_exec (e', σ')) φ ε.
Proof.
  intros ? Hewp.
  apply ARcoupl_limit.
  intros ε' Hineq.
  assert (0 <= ε')%R as Hε'.
  { trans ε; [done|lra]. }
  pose (mknonnegreal ε' Hε') as NNRε'.
  assert (ε' = (NNRbar_to_real (NNRbar.Finite NNRε'))) as Heq; [done|].
  rewrite Heq.
  eapply ewp_adequacy; [done|done|].
  iIntros (?).
  by iApply Hewp.
Qed.

Corollary ewp_adequacy_mass Σ `{!probeffGpreS Σ} (e e' : expr) (σ σ' : state) φ (ε : R) :
  (0 <= ε)%R →
  (∀ `{probeffGS Σ}, ⊢  ⤇ e' -∗ ↯ ε -∗ EWP e @ ⊤ <| iEff_bottom |> {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
  (SeriesC (lim_exec (e, σ)) <= SeriesC (lim_exec (e', σ')) + ε)%R.
Proof.
  intros ? Hewp.
  eapply ARcoupl_mass_leq.
  by eapply ewp_adequacy.
Qed.
