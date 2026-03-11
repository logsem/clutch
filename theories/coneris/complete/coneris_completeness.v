
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
      heap_inv C σ ∗ con_tp_inv C  ={E}=∗

      (* ATOMIC CASE: open invariants *)
      (∃ (K : ectx con_prob_ectx_lang) (e1' : expr con_prob_lang),
        ⌜e1 = fill K e1'⌝ ∗
        ⌜Atomic StronglyAtomic e1'⌝ ∗
        ⌜∃ σ', (head_reducible e1' σ')⌝ ∗
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
            heap_inv C1 σ1 ∗ con_tp_inv C1 ∗
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
  Expval (prim_step e σ) (λ '(e', σ', efs), err_lb_con φ n (<[m := e']> C ++ efs, σ')) <= err_lb_con φ n (C, σ). 
Admitted.

Lemma err_lb_con_stuck φ C n m e σ : 
  C !! m = Some e → 
  stuck e σ → 
  err_lb_con φ n (C, σ) = 1. 
Admitted.

Lemma reducible_to_head (e : expr con_prob_lang) σ:
  reducible e σ →
  ∃ K e', e = fill K e' ∧ head_reducible e' σ.
Proof.
  rewrite /reducible /= /con_ectx_language.prim_step //=.
  intros [??].
  destruct (decomp e) eqn: Hde; simpl in *.
  rewrite Hde in H.
  apply dmap_pos in H as [((?&?)&?)[??]].
  exists l, e0. simpl in *.
  apply decomp_fill in Hde as <-.
  split; eauto; by eexists.
Qed.

Lemma head_redex_unique' K K' (e : expr con_prob_ectx_lang) e' σ σ':
  fill K e = fill K' e' →
  head_reducible e σ →
  head_reducible e' σ' →
  K = K' ∧ e = e'.
Proof.
  intros Heq [[e2 σ2] Hred] [[e2' σ2'] Hred'].
    edestruct (step_by_val K' K e' e) as [K'' HK];
      [by eauto using val_head_stuck..|].
  simpl in *.
  subst K. move: Heq. rewrite -fill_comp /=. intros <-%(inj (fill _)).
  destruct (con_ectx_language.head_ctx_step_val _ _ _ _ Hred') as [[]%not_eq_None_Some|HK''].
  { by eapply val_head_stuck. } 
  subst. rewrite /empty_ectx //=.
Qed.

Lemma wp_inv_open_maybe' `{!conerisWpGS con_prob_lang Σ} e σ s E1 N Φ :
  reducible e σ →
  (|={E1,E1 ∖ ↑ N}=> 
    (∃ (K : ectx con_prob_ectx_lang) e', ⌜e = fill K e'⌝ ∗ ⌜(Atomic StronglyAtomic e')⌝ ∗ ⌜∃ σ', (head_reducible e' σ')⌝
      ∗ WP e' @ s; E1 ∖ ↑ N {{ v, |={E1 ∖ ↑ N,E1}=> WP fill K (of_val v) @ s; E1 {{ Φ }} }})
    ∨ |={E1 ∖ ↑ N,E1}=> WP e @ s; E1 {{ Φ }})
  -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (Hred) "H".
  apply reducible_to_head in Hred as (K&e'&->&Hred').
  destruct (decide (Atomic StronglyAtomic e')).
  - iApply pgl_wp_bind.
    iMod "H" as "[H|H]".
    + iDestruct "H" as "(%K' & %e'' & % & %Hato & (%σ''&%Hred'') & Hwp)". 
      eapply (head_redex_unique') in H as [-> <-]; eauto.
    + iMod "H".
      iApply pgl_wp_mono; 
        first by iIntros (v) "H"; iApply fupd_mask_intro_subseteq; [set_solver | iExact "H"].  
      iApply (pgl_wp_bind_inv with "H").
  - iApply fupd_pgl_wp.
    iApply (fupd_mask_frame_acc with "H"); first set_solver.
    iIntros "[H|H]".
    + iDestruct "H" as "(%K' & %e'' & % & %Hato & (%σ''&%Hred'') & Hwp)". 
      eapply (head_redex_unique') in H as [-> <-]; eauto. 
      contradiction. 
    + iMod "H". iModIntro. by iIntros.
Qed.

Lemma wp_inv_open_maybe `{!conerisWpGS con_prob_lang Σ} e s E1 N Φ :
  (|={E1,E1 ∖ ↑ N}=> 
    (∃ (K : ectx con_prob_ectx_lang) e', ⌜e = fill K e'⌝ ∗ ⌜(Atomic StronglyAtomic e')⌝ ∗ ⌜∃ σ', (head_reducible e' σ')⌝
      ∗ WP e' @ s; E1 ∖ ↑ N {{ v, |={E1 ∖ ↑ N,E1}=> WP fill K (of_val v) @ s; E1 {{ Φ }} }})
    ∨ |={E1 ∖ ↑ N,E1}=> WP e @ s; E1 {{ Φ }})
  -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  destruct (decide (∃ σ, reducible e σ)) as [[??]|]; first by eapply wp_inv_open_maybe'.
  pose proof (not_exists_forall_not _ _ n) as Hnred.
  iIntros "H".
  iApply fupd_pgl_wp.
  iApply (fupd_mask_frame_acc with "H"); first set_solver.
  iIntros "[(%K' & %e'' & % & %Hato & (%σ''&%Hred'') & Hwp)|H]"; subst.
  - exfalso. 
    by eapply Hnred, head_prim_fill_reducible.
  - iMod "H". iModIntro. by iIntros.
Qed.

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

Let N := nroot .@ "completeness".

Definition cfg_inv φ n : iProp Σ :=
  ∃ cfg,
    heap_inv (fst cfg) (snd cfg) ∗
    con_tp_inv (fst cfg) ∗
    ↯ (err_lb_con φ n cfg).

Definition is_ccfg φ n γ : iProp Σ :=
  cinv N γ (cfg_inv φ n).

Lemma wp_completeness φ γ q n e:
  is_ccfg φ 0 γ -∗
  cinv_own γ q -∗
  n ↪cthread e -∗
  WP e @ ⊤ {{λ v, n ↪cthread (Val v) ∗ ∃ q', cinv_own γ q'}}.
Proof.
  iIntros "#Hinv".
  iLöb as "IH" forall (q e n).
  iIntros "Hq He". 
  destruct (to_val e) eqn : Hve. {
    apply of_to_val in Hve as <-. 
    iApply pgl_wp_value_fupd'. iModIntro. iFrame.
  }
  iApply wp_inv_open_maybe.
  iMod (cinv_acc with "Hinv Hq") as "(>Hinv2&Hq&Hclose)". 1: done.
  iDestruct "Hinv2" as "(%cfg&Hheap&Htpinv&Hx)".
  iPoseProof (con_tp_inv_lookup with "Htpinv He") as "%Hlu".
  destruct (decide (reducible e cfg.2)). 2 : {
    destruct cfg.
    erewrite err_lb_con_stuck; eauto; last by rewrite /stuck -not_reducible.
    iPoseProof (ec_contradict with "Hx") as "Hx"; auto; lra.
  }
  iMod (coneris_lang_completeness with "He [$Hheap $Htpinv]") as "[H|H]"; first done.
  - iDestruct "H" as "(%K&%e1&%Heq&%Hatomic&%Hred&H)". iModIntro.
    iLeft.
    iExists K, e1.
    iSplitR; first done.
    iSplitR.
    { iPureIntro. done. }
    iSplitL ""; first by (iPureIntro; exact Hred).
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
    all : iPureIntro.
    { eexists => ?. apply err_lb_con_bound. }
    { intros. by apply err_lb_con_step. }
    { apply err_lb_con_nn. }
    { intros. by erewrite err_lb_con_stuck. }
  - iDestruct "H" as "(Hheap & Htpinv & H)". iModIntro. iRight.
    iMod ("Hclose" with "[Hheap Htpinv Hx]") as "?".
    { iNext. iExists (_, _). simpl. iFrame. by destruct cfg. }
    iModIntro. iApply ("H" with "[Hq]").
    iNext. iMod (cinv_acc with "Hinv Hq") as "(>Hinv2&Hq&Hclose)". 1: done.
    iDestruct "Hinv2" as "(%cfg2&Hheap&Htpinv&Herr)".
    iModIntro. iFrame.
    iIntros (e2 Hpure) "He Htpinv".
    iPoseProof (con_tp_inv_lookup with "Htpinv He") as "%Hlu2".
    iMod (con_tp_inv_update with "Htpinv He") as "(Htpinv&He)".
    iModIntro.
    iIntros "Hheap".
    iMod ("Hclose" with "[Hheap Htpinv Herr]") as "_".
    {
      iNext.
      iExists (_, _). simpl. iFrame. 
      inversion Hpure. destruct cfg2 as [C' σ']. 
      iApply (ec_weaken with "Herr"); split; first by apply err_lb_con_nn.
      etrans; last eapply err_lb_con_step; [| eauto| apply pure_step_safe]. 
      eapply pmf_1_eq_dret in pure_step_det as ->.
      rewrite Expval_dret //=. by rewrite app_nil_r.
    }
    iModIntro.
    iApply (pgl_wp_wand with "[-]").
    1: iApply ("IH" with "Hq He").
    iIntros (v) "[$ (%q'&$&%Hfork)] %Heq".
Qed.

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