From iris.proofmode Require Import base proofmode classes.
From iris.base_logic Require Export invariants lib.ghost_map lib.cancelable_invariants.
From iris.program_logic Require Export weakestpre total_weakestpre language adequacy.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.

Section prelims.
  Context {Λ : language}.

  Record adequate_nofork (s : stuckness) (e1 : language.expr Λ) (σ1 : language.state Λ)
      (φ : language.val Λ → language.state Λ → Prop) := {
    adequate_nofork_result t2 σ2 v2 :
     rtc erased_step ([e1], σ1) (language.of_val v2 :: t2, σ2) → φ v2 σ2;
    adequate_nofork_not_stuck t2 σ2 e2 :
     s = NotStuck →
     rtc erased_step ([e1], σ1) (t2, σ2) →
     e2 ∈ t2 → not_stuck e2 σ2;
    adequate_nofork_efs_nil t2 σ2 e2 :
     rtc erased_step ([e1], σ1) (t2, σ2) →
     e2 ∈ t2 → ∀ κ e' σ' efs, language.prim_step e2 σ2 κ e' σ' efs → efs = nil
  }.

  Inductive prim_steps {Λ : language} : Λ.(expr) → Λ.(state) → list Λ.(observation) → Λ.(expr) → Λ.(state) → list Λ.(expr) → Prop :=
    prim_steps_once e1 σ1 κ1 e2 σ2 efs1 :
      prim_step e1 σ1 κ1 e2 σ2 efs1 →
      prim_steps e1 σ1 κ1 e2 σ2 efs1
  | prim_steps_next e1 σ1 κ1 e2 σ2 efs1 κ2 e3 σ3 efs2 :
      prim_step e1 σ1 κ1 e2 σ2 efs1 →
      prim_steps e2 σ2 κ2 e3 σ3 efs2 →
      prim_steps e1 σ1 (κ1 ++ κ2) e3 σ3 (efs1 ++ efs2).

  Inductive Forking := DoesFork | DoesNotFork.

  Definition cfg_not_stuck (C : cfg Λ) :=
    Forall (λ e, not_stuck e (snd C)) (fst C).

  Definition cfg_forking (C : cfg Λ) (f : Forking) :=
    f = DoesNotFork → Forall (λ e, ∀ e' σ' κ efs, prim_step e (snd C) κ e' σ' efs → efs = nil) (fst C).

  Definition cfg_safe_forking (C : cfg Λ) f :=
    ∀ C2, rtc erased_step C C2 → cfg_not_stuck C2 ∧ cfg_forking C2 f.

  Definition cfg_safe (C : cfg Λ) :=
    ∀ C2, rtc erased_step C C2 → cfg_not_stuck C2.

  Lemma cfg_safe_from_forking C f :
    cfg_safe_forking C f → cfg_safe C.
  Proof.
    intros H C2 Hrtc. destruct (H C2 Hrtc) as [??]. done.
  Qed.

  Lemma prim_steps_fill K e1 σ1 κ1 e2 σ2 efs1 :
    LanguageCtx K →
    @prim_steps Λ e1 σ1 κ1 e2 σ2 efs1 →
    prim_steps (K e1) σ1 κ1 (K e2) σ2 efs1.
  Proof.
    intros ?.
    induction 1; [econstructor 1|econstructor 2].
    - eapply fill_step. done.
    - eapply fill_step. done.
    - done.
  Qed.

  Lemma cfg_step (C : cfg Λ) n e κ e' σ' efs :
    fst C !! n = Some e →
    prim_step e (snd C) κ e' σ' efs →
    step C κ ((<[ n := e' ]> (fst C)) ++ efs, σ').
  Proof.
    intros Hlu Hprim.
    destruct C as [tp σ]. simpl in *.
    eapply elem_of_list_split_length in Hlu as (tp1&tp2&->&->).
    opose proof (insert_app_r _ _ 0) as Happr.
    rewrite Nat.add_0_r in Happr.
    erewrite Happr. clear Happr.
    econstructor. 3: done. 1: done.
    rewrite -app_assoc /=. done.
  Qed.

  Lemma cfg_steps_tc (C : cfg Λ) n e κ e' σ' efs :
    fst C !! n = Some e →
    @prim_steps Λ e (snd C) κ e' σ' efs →
    tc erased_step C ((<[ n := e' ]> (fst C)) ++ efs, σ').
  Proof.
    intros Hlu Hprim.
    destruct C as [tp σ]. simpl in *.
    induction Hprim as [|?????????? Hprim Hsteps IH] in Hlu,tp|-*.
    { eapply tc_once. eexists. eapply cfg_step; done. }
    etrans.
    { eapply tc_once. eexists. eapply cfg_step; done. }
    eapply lookup_lt_Some in Hlu as Hln.
    eapply tc_rtc_r.
    { eapply IH. rewrite lookup_app_l. 1: by eapply list_lookup_insert.
      rewrite length_insert. done. }
    eapply rtc_tc. left. f_equal.
    rewrite !insert_app_l. 2: by rewrite length_insert.
    rewrite list_insert_insert -app_assoc. done.
  Qed.

  Lemma cfg_steps (C : cfg Λ) n e κ e' σ' efs :
    fst C !! n = Some e →
    @prim_steps Λ e (snd C) κ e' σ' efs →
    rtc erased_step C ((<[ n := e' ]> (fst C)) ++ efs, σ').
  Proof.
    intros ??. eapply tc_rtc. by eapply cfg_steps_tc.
  Qed.

  Lemma cfg_safe_step C f n e κ e' σ' efs :
    cfg_safe_forking C f →
    fst C !! n = Some e →
    prim_step e (snd C) κ e' σ' efs →
    cfg_safe_forking ((<[ n := e' ]> (fst C)) ++ efs, σ') f ∧
    (f = DoesNotFork → efs = nil).
  Proof.
    intros Hsafe Hlu Hprim.
    split.
    - intros C2 Hrtc. eapply Hsafe. etrans.
      2: exact Hrtc.
      eapply rtc_once.
      exists κ.
      by eapply cfg_step.
    - destruct (Hsafe C) as [_ Hfork]. 1: reflexivity.
      intros ->. specialize (Hfork eq_refl).
      eapply Forall_lookup_1 in Hfork; last done.
      eapply Hfork in Hprim. done.
  Qed.

  Lemma cfg_safe_steps C f n e κ e' σ' efs :
    cfg_safe_forking C f →
    fst C !! n = Some e →
    @prim_steps Λ e (snd C) κ e' σ' efs →
    cfg_safe_forking ((<[ n := e' ]> (fst C)) ++ efs, σ') f ∧
    (f = DoesNotFork → efs = nil).
  Proof.
    intros Hsafe Hlu Hprim. destruct C as [tp σ1]; simpl in *.
    induction Hprim as [?????? Hprim|?????????? Hprim Hsteps IH] in Hsafe,Hlu,tp|-*.
    { eapply (cfg_safe_step (tp, σ1)); done. }
    eapply cfg_safe_step in Hsafe as [Hsafe2 Hnf]. 2-3: done.
    simpl in Hsafe2. eapply lookup_lt_Some in Hlu as Hln. eapply IH in Hsafe2 as [Hsafe3 Hnf2].
    2: { rewrite lookup_app_l. 1: by eapply list_lookup_insert.
         rewrite length_insert. done. }
    rewrite !insert_app_l in Hsafe3. 2: by rewrite length_insert.
    rewrite list_insert_insert -app_assoc in Hsafe3.
    split; first done.
    intros ->. rewrite Hnf // Hnf2 //.
  Qed.


  Lemma prim_val_stuck v σ κ e2 σ' efs :
    @prim_step Λ (of_val v) σ κ e2 σ' efs → False.
  Proof.
    intros HH%val_stuck. by rewrite to_of_val in HH.
  Qed.

  Local Instance val_atomic a (v : val Λ) : Atomic a (of_val v).
  Proof.
    intros ????? []%prim_val_stuck.
  Qed.

End prelims.

Section tpinv.

  Context {Λ : language}.
  Context `{!ghost_mapG Σ nat Λ.(expr)}.

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

  Context {γ_cfg : gname}.

  Definition tp_inv (tp : list Λ.(expr)) : iProp Σ :=
    ∃ (m : gmap nat _),
      ⌜∀ n, m !! n = tp !! n⌝
    ∗ ghost_map_auth γ_cfg 1 m.

  Lemma tp_inv_lookup tp n e1 :
    tp_inv tp -∗
    n ↪[γ_cfg] e1 -∗
    ⌜tp !! n = Some e1⌝.
  Proof.
    iIntros "(%m&%Heq&Hm) Hn".
    iPoseProof (ghost_map_lookup with "Hm Hn") as "%HH".
    iPureIntro. rewrite -Heq. done.
  Qed.

  Lemma tp_inv_update tp n e1 e2 :
    tp_inv tp -∗
    n ↪[γ_cfg] e1 ==∗
    tp_inv (<[ n := e2]> tp) ∗ n ↪[γ_cfg] e2.
  Proof.
    iIntros "Htp Hn".
    iPoseProof (tp_inv_lookup with "Htp Hn") as "%Hlu".
    iDestruct "Htp" as "(%m&%Hm&Hm)".
    iMod (ghost_map_update e2 with "Hm Hn") as "(Hm&$)".
    iModIntro. iExists _. iFrame "Hm".
    iPureIntro.
    intros n'. destruct (decide (n = n')) as [->|Hne].
    - rewrite lookup_insert list_lookup_insert //.
      eapply lookup_lt_is_Some. by eexists.
    - rewrite list_lookup_insert_ne // lookup_insert_ne //.
  Qed.

  Lemma tp_inv_new_threads efs tp :
    tp_inv tp ==∗
    tp_inv (tp ++ efs) ∗ [∗ list] n↦e' ∈ efs, (length tp + n) ↪[γ_cfg] e'.
  Proof.
    iIntros "(%m&%Hm&Hm)".
    iMod (ghost_map_insert_big (map_seq (length tp) efs)  with "Hm") as "(Hm&Hefs)".
    - eapply map_disjoint_spec. intros n e1 e2 (Hlen&Hluefs)%lookup_map_seq_Some Hl2.
      rewrite Hm in Hl2. eapply lookup_lt_Some in Hl2. lia.
  Admitted.
(*     - iModIntro. rewrite big_sepM_map_seq. iFrame "Hefs".
      iExists _. iFrame. iPureIntro.
      intros n. destruct (decide (n < length tp)) as [Hlt|Hge].
      + rewrite lookup_app_l // -Hm lookup_union_r //.
        eapply lookup_map_seq_None. left. lia.
      + assert (length tp ≤ n) as Hge' by lia.
        rewrite lookup_app_r //.
        rewrite lookup_union_l.
        2: { rewrite Hm. by eapply lookup_ge_None_2. }
        rewrite lookup_map_seq. rewrite option_guard_True //.

  Qed. *)
End tpinv.

Global Arguments tp_inv {Λ} {Σ} {_} _ _.

Section magic_rule.
  Context `{irisGS_gen hlc Λ Σ}.

  Lemma wp_inv_open_maybe_help1 (e : expr Λ) s E1 E2 Φ :
    to_val e = None →
    (|={E1,E2}=> 
      (∃ K e', ⌜LanguageCtx K⌝ ∗ ⌜e = K e'⌝ ∗ ⌜(Atomic (stuckness_to_atomicity s) e')⌝ 
        ∗ WP e' @ s; E2 {{ v, |={E2,E1}=> WP K (of_val v) @ s; E1 {{ Φ }} }})
      ∨ |={E2,E1}=> WP e @ s; E1 {{ Φ }})
    -∗ WP e @ s; E1 {{ Φ }}.
  Proof.
    iIntros (Hnv) "H".
    rewrite wp_unfold /wp_pre Hnv.
    iMod "H" as "[H|>$]".
    iDestruct "H" as "(%K & %e' & % & -> & %Hato & Hwp)".
    rewrite wp_unfold /wp_pre.
    destruct (to_val e') as [?|] eqn:Heq.
    { eapply of_to_val in Heq. rewrite Heq.
      do 2 iMod "Hwp". rewrite wp_unfold /wp_pre Hnv. done. }
    iIntros (σ n κ κs n2) "Hσ".
    iMod ("Hwp" with "Hσ") as "[%Hred Hc]".
    iModIntro. iSplit.
    { iPureIntro. destruct s; last done.
      by eapply reducible_fill. }
    iIntros (x σ2 efs (e2&->&Hprim)%fill_step_inv); last done.
    iIntros "H£". iSpecialize ("Hc" $! _ _ _ Hprim with "H£").
    iApply (step_fupdN_mono with "Hc").
    iIntros "Hc". iMod "Hc" as "(Hσ & Hc & $)".
    eapply Hato in Hprim.
    rewrite wp_unfold /wp_pre.
    destruct (to_val e2) eqn:Hve2.
    { iMod "Hc" as ">Hc". iFrame "Hσ". eapply of_to_val in Hve2. by subst. }
    destruct s; simpl in *; last by inversion Hprim.
    iMod ("Hc" with "[Hσ]") as "[%Hredu _]". 
    { by erewrite app_nil_r. }
    by eapply not_reducible in Hredu.
  Qed.

  Lemma wp_inv_open_maybe (e : expr Λ) s E1 E2 Φ :
    (|={E1,E2}=> 
      (∃ K e', ⌜LanguageCtx K⌝ ∗ ⌜e = K e'⌝ ∗ ⌜(Atomic (stuckness_to_atomicity s) e')⌝ 
        ∗ WP e' @ s; E2 {{ v, |={E2,E1}=> WP K (of_val v) @ s; E1 {{ Φ }} }})
      ∨ |={E2,E1}=> WP e @ s; E1 {{ Φ }})
    -∗ WP e @ s; E1 {{ Φ }}.
  Proof.
    iIntros "H".
    destruct (to_val e) as [v|] eqn:Hev; last by iApply wp_inv_open_maybe_help1.
    eapply of_to_val in Hev. subst e. iApply (wp_atomic).
    1: eapply val_atomic.
    iMod "H" as "[H|H]"; last first.
    { iModIntro. rewrite !wp_value_fupd'.
      iModIntro. iMod "H". done. }
    iDestruct "H" as "(%K & %e' & % & %Hvke & %Hato & Hwp)".
    destruct (to_val e') as [v'|] eqn:Hev'.
    { eapply of_to_val in Hev'. subst e'. rewrite !wp_value_fupd'.
      iMod "Hwp". do 2 iModIntro. rewrite -Hvke wp_value_fupd'. by iMod "Hwp". }
    eapply of_to_val_flip in Hvke.
    eapply fill_not_val in Hev'. congruence.
  Qed.

  Lemma twp_inv_open_maybe_help1 (e : expr Λ) s E1 E2 Φ :
    to_val e = None →
    (|={E1,E2}=> 
      (∃ K e', ⌜LanguageCtx K⌝ ∗ ⌜e = K e'⌝ ∗ ⌜(Atomic (stuckness_to_atomicity s) e')⌝ 
        ∗ WP e' @ s; E2 [{ v, |={E2,E1}=> WP K (of_val v) @ s; E1 [{ Φ }] }])
      ∨ |={E2,E1}=> WP e @ s; E1 [{ Φ }])
    -∗ WP e @ s; E1 [{ Φ }].
  Proof.
    iIntros (Hnv) "H".
    rewrite twp_unfold /twp_pre Hnv.
    iMod "H" as "[H|>$]".
    iDestruct "H" as "(%K & %e' & % & -> & %Hato & Hwp)".
    rewrite twp_unfold /twp_pre.
    destruct (to_val e') as [?|] eqn:Heq.
    { eapply of_to_val in Heq. rewrite Heq.
      do 2 iMod "Hwp". rewrite twp_unfold /twp_pre Hnv. done. }
    iIntros (σ n κ n2) "Hσ".
    iMod ("Hwp" with "Hσ") as "[%Hred Hc]".
    iModIntro. iSplit.
    { iPureIntro. destruct s; last done.
      by eapply reducible_no_obs_fill. }
    iIntros (κ2 x σ2 efs (e2&->&Hprim)%fill_step_inv); last done.
    iMod ("Hc" $! _ _ _ _ Hprim) as "(-> & Hσ & Hc & $)".
    eapply Hato in Hprim.
    rewrite twp_unfold /twp_pre.
    destruct (to_val e2) eqn:Hve2.
    { iMod "Hc" as ">Hc". iFrame "Hσ". eapply of_to_val in Hve2. subst. iModIntro. iFrame. done. }
    destruct s; simpl in *; last by inversion Hprim.
    iMod ("Hc" with "Hσ") as "[%Hredu _]".
    eapply reducible_no_obs_reducible in Hredu.
    by eapply not_reducible in Hredu.
  Qed.

  Lemma twp_inv_open_maybe (e : expr Λ) s E1 E2 Φ :
    (|={E1,E2}=> 
      (∃ K e', ⌜LanguageCtx K⌝ ∗ ⌜e = K e'⌝ ∗ ⌜(Atomic (stuckness_to_atomicity s) e')⌝ 
        ∗ WP e' @ s; E2 [{ v, |={E2,E1}=> WP K (of_val v) @ s; E1 [{ Φ }] }])
      ∨ |={E2,E1}=> WP e @ s; E1 [{ Φ }])
    -∗ WP e @ s; E1 [{ Φ }].
  Proof.
    iIntros "H".
    destruct (to_val e) as [v|] eqn:Hev; last by iApply twp_inv_open_maybe_help1.
    eapply of_to_val in Hev. subst e. iApply (twp_atomic).
    1: eapply val_atomic.
    iMod "H" as "[H|H]"; last first.
    { iModIntro. rewrite !twp_value_fupd'.
      iModIntro. iMod "H". done. }
    iDestruct "H" as "(%K & %e' & % & %Hvke & %Hato & Hwp)".
    destruct (to_val e') as [v'|] eqn:Hev'.
    { eapply of_to_val in Hev'. subst e'. rewrite !twp_value_fupd'.
      iMod "Hwp". do 2 iModIntro. rewrite -Hvke twp_value_fupd'. by iMod "Hwp". }
    eapply of_to_val_flip in Hvke.
    eapply fill_not_val in Hev'. congruence.
  Qed.

End magic_rule.


  