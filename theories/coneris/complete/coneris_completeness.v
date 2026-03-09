
From clutch.coneris.complete Require Export coneris_completeness_prelims.
From clutch.base_logic Require Import error_credits.
From clutch.con_prob_lang Require Import lang.
From clutch.coneris Require Import weakestpre.
From iris.prelude Require Export prelude options.
From iris.bi Require Export bi fractional.
From iris.proofmode Require Import base proofmode classes.

Local Open Scope R.

Section lang_complete.

Class coneris_lang_completeness_gen Σ 
        `{!coneristpinvGS Σ con_prob_ectx_lang,
          !ecGS Σ,
          !conerisWpGS con_prob_lang Σ} :=
  ConerisLangCompleteness {

  heap_inv : list (expr con_prob_lang) → state con_prob_lang → iProp Σ;
  heap_inv_timeless :> ∀ C σ, Timeless (heap_inv C σ);

  coneris_lang_completeness :
    ∀ n (C : list (expr con_prob_lang)) (e1 : expr con_prob_lang)
      (σ : state con_prob_lang) E,
      reducible e1 σ →
      n ↪cthread e1 -∗
      heap_inv C σ ∗ con_tp_inv C ∗ ⌜con_cfg_safe C σ⌝ ={E}=∗

      (* ATOMIC CASE: open invariants *)
      (∃ (K : ectx con_prob_ectx_lang) (e1' : expr con_prob_lang),
        ⌜e1 = fill K e1'⌝ ∗
        ⌜Atomic StronglyAtomic e1'⌝ ∗
        ∀ Φ (ε1 : cfg con_prob_lang → R),
          ⌜∃ r : R, ∀ ρ, ε1 ρ <= r⌝ →
          ⌜∀ C' σ' n' e',
              C' !! n' = Some e' → reducible e' σ' →
              Expval (prim_step e' σ')
                     (λ '(e'', σ'', efs), ε1 (<[n' := e'']> C' ++ efs, σ''))
                <= ε1 (C', σ') ⌝ →
          ⌜∀ ρ, 0 <= ε1 ρ⌝ →
          ⌜∀ C' σ' n' e', C' !! n' = Some e' → stuck e' σ' → ε1 (C', σ') = 1⌝ →
          (▷ ∀ v2 σ' efs,
            ⌜head_step e1' σ (of_val v2, σ', efs) > 0⌝ -∗
            n ↪cthread e1 -∗
            con_tp_inv C ==∗
            (heap_inv (<[n := fill K (of_val v2)]> C ++ efs) σ' 
              -∗ ↯ (ε1 ((<[n := fill K (of_val v2)]> C ++ efs), σ'))
              -∗ Φ v2) ∗
            [∗ list] m↦etp ∈ efs, WP etp @ ⊤ {{_, True}}) -∗
          ↯ (ε1 (C, σ)) -∗
          WP e1' @ E {{Φ}}) ∨

      (* NON-ATOMIC CASE: pure step *)
      (heap_inv C σ ∗ con_tp_inv C ∗
        ∀ Ψ E2,
          (▷ |={E2,E}=> ∃ σ1 C1,
            heap_inv C1 σ1 ∗ con_tp_inv C1 ∗ ⌜con_cfg_safe C1 σ1⌝ ∗
            ∀ e2,
              ⌜pure_step e1 e2⌝ -∗
              n ↪cthread e1 -∗
              con_tp_inv C1 ==∗
              (heap_inv (<[n := e2]> C1) σ1
                 ={E,E2}=∗ WP e2 @ E2 {{Ψ}})) -∗
          WP e1 @ E2 {{Ψ}})
}.

Global Existing Instance heap_inv_timeless.

End lang_complete.


Definition err_lb_con (φ : val con_prob_lang → Prop) (n : nat)
    (ρ : cfg con_prob_lang) : R. Admitted.

Lemma err_lb_con_nn φ n ρ : 0 <= err_lb_con φ n ρ. 
Admitted.
Lemma err_lb_con_bound φ n ρ : err_lb_con φ n ρ <= 1. 
Admitted.

Lemma err_lb_con_val φ v n ρ :
  ρ.1 !! n = Some (Val v) →
  err_lb_con φ n ρ = if bool_decide (φ v) then 0 else 1. 
Admitted.

Lemma err_lb_con_step φ n m C σ e :
  C !! m = Some e → reducible e σ →
  err_lb_con φ n (C, σ) >=
  Expval (prim_step e σ) (λ '(e', σ', efs), err_lb_con φ n (<[m := e']> C ++ efs, σ')). 
Admitted.

Lemma err_lb_con_stuck φ C n m e σ : 
  C !! m = Some e → 
  stuck e σ → 
  err_lb_con φ n (C, σ) = 1. 
Admitted.


Section completeness.

Context {Σ : gFunctors}.
Context `{!coneristpinvGS Σ con_prob_ectx_lang,
          !ecGS Σ,
          !conerisWpGS con_prob_lang Σ,
          !cinvG Σ,
          !coneris_lang_completeness_gen Σ}.

Lemma fractional_divide_n (Q : Qp → iProp Σ) (Hf : Fractional Q) (p : positive) q :
  Q q -∗
  [∗ list] _ ∈ seq 0 (Pos.to_nat p), Q (q / pos_to_Qp p)%Qp.
Proof.
  revert q. induction p as [|p IHp] using Pos.peano_ind; intros q.
  - rewrite /= Qp.div_1. by iIntros "$".
  - iIntros "Hq".
    assert ((q / pos_to_Qp (Pos.succ p))%Qp + ((q * pos_to_Qp p) / pos_to_Qp (Pos.succ p))%Qp = q)%Qp as Heq. 
    { rewrite -Qp.div_add_distr -{1}(Qp.mul_1_r q) -Qp.mul_add_distr_l pos_to_Qp_add Pos.add_1_l.
      rewrite -{2}(Qp.mul_1_l (pos_to_Qp (Pos.succ p))) Qp.div_mul_cancel_r Qp.div_1 //. }
    rewrite -{1}Heq Hf Pos2Nat.inj_succ seq_S /= big_sepL_snoc.
    iDestruct "Hq" as "[$ Hq]". iPoseProof (IHp with "Hq") as "Hres".
    iApply (big_sepL_wand with "Hres").
    iApply big_sepL_intro. iIntros "!>" (???) "H".
    iStopProof. f_equiv.
    rewrite Qp.div_div Qp.div_mul_cancel_r //.
Qed.

Lemma wp_inv_open_maybe e s E1 E2 Φ :
  (|={E1,E2}=> 
    (∃ K e', ⌜ConLanguageCtx K⌝ ∗ ⌜e = K e'⌝ ∗ ⌜(Atomic StronglyAtomic e')⌝ 
      ∗ WP e' @ s; E2 {{ v, |={E2,E1}=> WP K (of_val v) @ s; E1 {{ Φ }} }})
    ∨ |={E2,E1}=> WP e @ s; E1 {{ Φ }})
  -∗ WP e @ s; E1 {{ Φ }}.
Proof.
Admitted.


Let N := nroot .@ "completeness".

Definition cfg_inv φ n : iProp Σ :=
  ∃ cfg,
    heap_inv (fst cfg) (snd cfg) ∗
    con_tp_inv (fst cfg) ∗
    ↯ (err_lb_con φ n cfg).

Definition is_ccfg φ n γ : iProp Σ :=
  cinv N γ (cfg_inv φ n).

Lemma con_cfg_safe_step C n e σ e' σ' efs :
    con_cfg_safe C σ →
    C !! n = Some e →
    prim_step e σ (e', σ', efs) > 0 →
    con_cfg_safe (Λ := con_prob_lang) (<[n := e']> C ++ efs) σ'.
Proof. 
Admitted.

Lemma wp_completeness φ γ q n e :
  is_ccfg φ 0 γ -∗
  cinv_own γ q -∗
  n ↪cthread e -∗
  WP e @ ⊤ {{λ v, n ↪cthread (Val v) ∗ ∃ q', cinv_own γ q'}}.
Proof.
  iIntros "#Hinv".
  iLöb as "IH" forall (q e n).
  iIntros "Hq He". 
  iApply wp_inv_open_maybe.
  iMod (cinv_acc with "Hinv Hq") as "(>Hinv2&Hq&Hclose)". 1: done.
  iDestruct "Hinv2" as "(%cfg&Hheap&Htpinv&Hx)".
  iPoseProof (con_tp_inv_lookup with "Htpinv He") as "%Hlu".
  destruct (to_val e) eqn : Hve. {
    iRight. rewrite -(of_to_val _ _ Hve) /=.
    iModIntro. 
    iMod ("Hclose" with "[Hheap Htpinv Hx]") as "_".
    {
      iNext.
      iExists (_, _). simpl. iFrame. 
      by destruct cfg.
    } 
    iModIntro.
    iApply pgl_wp_value'.
    iFrame.
  }
  destruct (decide (reducible e cfg.2)). 2 : {
    destruct cfg.
    erewrite err_lb_con_stuck; eauto; last by rewrite /stuck -not_reducible.
    iPoseProof (ec_contradict with "Hx") as "Hx"; auto; lra.
  }
  iMod (coneris_lang_completeness with "He [$Hheap $Htpinv]") as "[H|H]"; first done.
  - iPureIntro. 
    rewrite /con_cfg_safe.
    admit.
  - iDestruct "H" as "(%K&%e1&%Heq&%Hatomic&H)". iModIntro.
    iLeft. 
    iExists (fill K), e1. iSplitR.
    { iPureIntro. apply con_ectx_lang_ctx. } 
    iSplitR; first done.
    iSplitR. 
    { iPureIntro. done. } 
    iApply ("H" with "[][][][][Hq Hclose] [Hx]"); last by destruct cfg.
    5 : {
      iNext.
      iIntros (v2 σ2' efs Hbase) "He Htpinv".
      iPoseProof (fractional_divide_n _ _ (Pos.of_nat (S (length efs))) with "Hq") as "Hp".
      rewrite Nat2Pos.id // seq_S big_sepL_snoc /=.
      iDestruct "Hp" as "[Hefsfrac Hq]".
      iMod (con_tp_inv_new_threads _ efs with "Htpinv") as "(Htpinv&Hefs)".
      iMod (con_tp_inv_update with "Htpinv He") as "(Htpinv&He)". iModIntro.
      iSplitR "Hefs Hefsfrac"; last first.
      + iPoseProof (big_sepL2_sepL_2 with "Hefs Hefsfrac") as "Hefsfracs"; first by rewrite length_seq.
        rewrite big_sepL2_const_sepL_l. iDestruct "Hefsfracs" as "[_ Hefs]".
        iApply (big_sepL_wand with "Hefs").
        iApply big_sepL_intro. iIntros "!>" (n' e' Hefs) "[He Hq]".
        iApply (pgl_wp_wand with "[-]").
        1: iApply ("IH" with "Hq He").
        iIntros. done.
      + subst e. iIntros "Hheap".
        rewrite insert_app_l; last by eapply lookup_lt_Some.
        iIntros "Hs".
        iMod ("Hclose" with "[Hheap Htpinv Hs]") as "?"; last first.
        {
          iModIntro. iApply (pgl_wp_wand with "[-]").
          1: iApply ("IH" with "Hq He").
          iIntros (v) "[$ (%q'&$&%Hfork)] %".
        }
        iNext. iExists (_, _). simpl. iFrame.
    }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
  - iDestruct "H" as "(Hheap & Htpinv & H)". iModIntro. iRight.
    iMod ("Hclose" with "[Hheap Htpinv Hx]") as "?".
    { iNext. iExists (_, _). simpl. iFrame. by destruct cfg. }
    iModIntro. iApply ("H" with "[Hq]").
    iNext. iMod (cinv_acc with "Hinv Hq") as "(>Hinv2&Hq&Hclose)". 1: done.
    iDestruct "Hinv2" as "(%cfg2&Hheap&Htpinv&Herr)".
    iModIntro. iFrame.
    iSplitL "". { admit. }
    iIntros (e2 Hpure) "He Htpinv".
    iPoseProof (con_tp_inv_lookup with "Htpinv He") as "%Hlu2".
    iMod (con_tp_inv_update with "Htpinv He") as "(Htpinv&He)".
    iModIntro.
    iIntros "Hheap".
    iMod ("Hclose" with "[Hheap Htpinv Herr]") as "_".
    {
      iNext.
      iExists (_, _). simpl. iFrame. 
      admit.
    }
    iModIntro.
    iApply (pgl_wp_wand with "[-]").
    1: iApply ("IH" with "Hq He").
    iIntros (v) "[$ (%q'&$&%Hfork)] %Heq".
Admitted.

End completeness.

Lemma coneris_sem_completeness `{
          !coneristpinvGS Σ con_prob_ectx_lang,
          !ecGS Σ,
          !conerisWpGS con_prob_lang Σ,
          !cinvG Σ,
          !coneris_lang_completeness_gen Σ} e σ φ :
  con_tp_inv_ini -∗
  heap_inv [e] σ -∗ 
  ↯ (err_lb_con φ 0 ([e], σ)) -∗
  WP e @ ⊤ {{ v, ⌜φ v⌝ }}.
Proof.
  iIntros "Hini Hheap Herr".
  iApply fupd_pgl_wp.
  iMod (con_tp_inv_set [e] with "Hini") as "(Hauth&Hfrags)".
  iMod (cinv_alloc _ _ (cfg_inv φ 0) with "[Hauth Hheap Herr]") as (γ') "(#Hinv&Hq)".
  { iNext. iFrame. }
  rewrite big_sepL_singleton.
  iModIntro.
  iApply pgl_wp_fupd.
  iApply (pgl_wp_wand with "[-]").
  1: iApply (wp_completeness φ γ' with "Hinv Hq Hfrags").
  iIntros (v) "(Hv&%q'&Hq')".
  iMod (cinv_acc with "Hinv Hq'") as "(>Hinv2&Hq'&Hclose2)". 1: done.
  iDestruct "Hinv2" as "(%&Hheap&Htpinv&Herr)".
  iPoseProof (con_tp_inv_lookup with "Htpinv Hv") as "%Hlu".
  destruct (decide (φ v)). 2 : {
    iExFalso. iApply ec_contradict; last iFrame.
    erewrite err_lb_con_val; eauto.
    by case_bool_decide.
  }
  iMod ("Hclose2" with "[-Hv Hq']").
  { iExists _. iFrame. }
  by iModIntro.
Qed.