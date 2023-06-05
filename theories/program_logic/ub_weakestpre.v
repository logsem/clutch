From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext.
From clutch.prob Require Export couplings distribution union_bounds.
From clutch.program_logic Require Export exec language.

Import uPred.

Local Open Scope R.

(** [irisGS] specifies the interface for the resource algebras implementing the
    [state] and [cfg] of a [language] [Λ]. For the purposes of defining the
    weakest precondition, we only need [irisGS] to give meaning to invariants,
    and provide predicates describing valid states via [state_interp] and valid
    specification configurations via [spec_interp]. *)
Class irisGS (Λ : language) (Σ : gFunctors) := IrisG {
  iris_invGS :> invGS_gen HasNoLc Σ;
  state_interp : state Λ → iProp Σ;
  err_interp : R → iProp Σ;
}.
Global Opaque iris_invGS.
Global Arguments IrisG {Λ Σ}.

(* TODO: upstream? *)
Lemma least_fixpoint_ne_outer {PROP : bi} {A : ofe}
    (F1 : (A → PROP) → (A → PROP)) (F2 : (A → PROP) → (A → PROP)) n :
  (∀ Φ x, F1 Φ x ≡{n}≡ F2 Φ x) → ∀ x1 x2,
  x1 ≡{n}≡ x2 → bi_least_fixpoint F1 x1 ≡{n}≡ bi_least_fixpoint F2 x2.
Proof.
  intros HF x1 x2 Hx. rewrite /bi_least_fixpoint /=.
  do 3 f_equiv; last solve_proper. repeat f_equiv. apply HF.
Qed.



(** * The coupling modality [exec_coupl]  *)
Section exec_ub.
  Context `{!irisGS Λ Σ}.

  Definition exec_ub_pre (Z : cfg Λ → iProp Σ) (Φ : R * cfg Λ → iProp Σ) :=
    (λ (x : R * cfg Λ),
      let '(ε, (e1, σ1)) := x in
      (* [prim_step] *)
      (∃ R, ⌜reducible e1 σ1⌝ ∗
            ⌜ub_lift (prim_step e1 σ1) R ε⌝ ∗
            ∀ ρ2, ⌜ R ρ2 ⌝ ={∅}=∗ Z ρ2 ) ∨
      (* [state_step]  *)
      ([∨ list] α ∈ get_active σ1,
      (* We allow an explicit weakening of the grading, but maybe it is not needed *)
        (∃ R ε1 ε2, ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜ ub_lift (state_step σ1 α) R ε1 ⌝ ∗
              ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ Φ (ε2,((e1, σ2)))))
    )%I.

  Canonical Structure RO := leibnizO R.

  Local Instance exec_state_ub_pre_NonExpansive Z Φ :
    NonExpansive (exec_ub_pre Z Φ).
  Proof.
    rewrite /exec_ub_pre.
    intros n (?&(?&?)) (?&(?&?)) [ [=] [[=] [=]]].
    by simplify_eq.
  Qed.

  Local Instance exec_coupl_pre_mono Z : BiMonoPred (exec_ub_pre Z).
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    rewrite /exec_ub_pre.
    iIntros ((ε&(e1 & σ1))) "Hexec".
    iDestruct "Hexec" as "[H | H]".
    - by iLeft.
    - iRight.
      iInduction (get_active σ1) as [| l] "IH" forall "H".
      { rewrite big_orL_nil //. }
      rewrite !big_orL_cons.
      iDestruct "H" as "[(% & % & % & %Hsum & Hlift & HΦ) | H]".
      + iLeft. iExists R2.
        iExists ε1. iExists _.
        iSplit; [try done|].
        iSplit; [try done|].
        iIntros. iApply "Hwand". by iApply "HΦ".
      + iRight. by iApply "IH".
  Qed.

  Definition exec_ub' Z := bi_least_fixpoint (exec_ub_pre Z).
  Definition exec_ub e σ Z ε := exec_ub' Z (ε, (e, σ)).

  Lemma exec_ub_unfold e1 σ1 Z ε :
    exec_ub e1 σ1 Z ε ≡
      ((∃ R, ⌜reducible e1 σ1⌝ ∗
            ⌜ub_lift (prim_step e1 σ1) R ε⌝ ∗
            ∀ ρ2, ⌜ R ρ2 ⌝ ={∅}=∗ Z ρ2 ) ∨
      ([∨ list] α ∈ get_active σ1,
        (∃ R ε1 ε2, ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜ ub_lift (state_step σ1 α) R ε1 ⌝ ∗
              ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ exec_ub e1 σ2 Z ε2 )))%I.
  Proof. rewrite /exec_ub/exec_ub' least_fixpoint_unfold //. Qed.

  Local Definition cfgO := (prodO (exprO Λ) (stateO Λ)).


  Lemma exec_ub_mono_grading e1 σ1 (Z : cfg Λ → iProp Σ) ε ε' :
    ⌜(ε <= ε')⌝ -∗
    exec_ub e1 σ1 Z ε -∗ exec_ub e1 σ1 Z ε'.
  Proof.
    iIntros "Hleq H_ub". iRevert "Hleq".
    rewrite /exec_ub /exec_ub'.
    Search bi_least_fixpoint.
    set (Φ := (λ x, ∀ ε'', ((⌜(x.1 <= ε'' )⌝ -∗ (bi_least_fixpoint (exec_ub_pre Z) (ε'', x.2)))))%I : prodO RO cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n (?&(?&?)) (?&(?&?)) [ [=] [[=] [=]]]. by simplify_eq. }
    iPoseProof (least_fixpoint_ind (exec_ub_pre Z) Φ with "[]") as "H"; last first.
    { iApply ("H" with "H_ub"). }
    iIntros "!#" ([ε'' [? σ']]). rewrite /exec_ub_pre.
    iIntros "[ (% & % & % & H) | H ] %ε3 %Hleq' /="; simpl in Hleq'.
    - rewrite least_fixpoint_unfold.
      iLeft. iExists _.
      iSplit; [done|].
      iSplit.
      { iPureIntro.
        apply (UB_mon_grading _ _ _ _ Hleq') in H1. by apply ub_lift_pos_R. }
      iIntros ([] (?&?)). iMod ("H" with "[//]").
      iModIntro. eauto.
    - rewrite least_fixpoint_unfold.
      iRight.
      iInduction (get_active σ') as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(%R2 & %ε1 & %ε2 & (%Hleq2 & %Hub & H)) | Ht]".
      + iLeft.
        iExists R2. iExists ε1. iExists ε2.
        iSplit; [ iPureIntro; lra | ].
        iSplit; [ done | ].
        iIntros.
        iApply ("H" with "[//]").
        iPureIntro. simpl; lra.
      + iRight. by iApply ("IH" with "Ht").
  Qed.


  Lemma exec_ub_strong_mono e1 σ1 (Z1 Z2 : cfg Λ → iProp Σ) ε ε' :
    ⌜(ε <= ε')⌝ -∗
    (∀ e2 σ2, (⌜∃ σ, prim_step e1 σ (e2, σ2) > 0⌝ ∗ Z1 (e2, σ2) -∗ Z2 (e2, σ2))) -∗
    exec_ub e1 σ1 Z1 ε -∗ exec_ub e1 σ1 Z2 ε'.
  Proof.
    iIntros "%Hleq HZ H_ub".
    iApply exec_ub_mono_grading; auto.
    iRevert "HZ".
    rewrite /exec_ub /exec_ub'.
    set (Φ := (λ x,(∀ e2 σ2, ⌜∃ σ, prim_step x.2.1 σ (e2, σ2) > 0⌝ ∗ Z1 (e2, σ2) -∗ Z2 (e2, σ2)) -∗
                  (bi_least_fixpoint (exec_ub_pre Z2) x ))%I : prodO RO cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n (?&(?&?)) (?&(?&?)) [[=] [[=] [=]]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter (exec_ub_pre Z1) Φ with "[]") as "H"; last first.
    { by iApply ("H" with "H_ub"). }
    iIntros "!#" ([ε'' [? σ']]). rewrite /exec_ub_pre.
    iIntros "[ (% & % & % & H) | H ] HZ /=".
    - rewrite least_fixpoint_unfold.
      iLeft. iExists _.
      iSplit; [done|].
      iSplit.
      { iPureIntro.
        by apply ub_lift_pos_R. }
      iIntros ([] (?&?)). iMod ("H" with "[//]").
      iModIntro. iApply "HZ". eauto.
    - rewrite least_fixpoint_unfold.
      iRight.
      iInduction (get_active σ') as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(%R2 & %ε1 & %ε2 & (% & % & H)) | Ht]".
      + iLeft. iExists R2. iExists ε1. iExists ε2.
        iSplit; [iPureIntro; lra | ].
        iSplit; [done | ].
        iIntros.
        by iApply ("H" with "[//]"). 
      + iRight. by iApply ("IH" with "Ht").
  Qed.

  Lemma exec_ub_mono (Z1 Z2 : cfg Λ → iProp Σ) e1 σ1 ε1 ε2 :
    ⌜(ε1 <= ε2)⌝ -∗ (∀ ρ, Z1 ρ -∗ Z2 ρ ) -∗ exec_ub e1 σ1 Z1 ε1 -∗ exec_ub e1 σ1 Z2 ε2.
  Proof.
    iIntros "%Hleq HZ". iApply exec_ub_strong_mono; auto.
    iIntros (??) "[_ ?]". by iApply "HZ".
  Qed.

  Lemma exec_ub_mono_pred (Z1 Z2 : cfg Λ → iProp Σ) e1 σ1 ε :
    (∀ ρ, Z1 ρ -∗ Z2 ρ ) -∗ exec_ub e1 σ1 Z1 ε -∗ exec_ub e1 σ1 Z2 ε.
  Proof.
    iIntros "HZ". iApply exec_ub_strong_mono; auto.
    iIntros (??) "[_ ?]". by iApply "HZ".
  Qed.

  Lemma exec_ub_strengthen e1 σ1 (Z : cfg Λ → iProp Σ) ε :
    exec_ub e1 σ1 Z ε -∗
    exec_ub e1 σ1 (λ '(e2, σ2), ⌜∃ σ, prim_step e1 σ (e2, σ2) > 0⌝ ∧ Z (e2, σ2)) ε.
  Proof.
    iApply exec_ub_strong_mono; [iPureIntro; lra | ].
    iIntros (??) "[[% ?] ?]". iSplit; [|done]. by iExists _.
  Qed.

  Lemma exec_ub_bind K `{!LanguageCtx K} e1 σ1 (Z : cfg Λ → iProp Σ) ε :
    to_val e1 = None →
    exec_ub e1 σ1 (λ '(e2, σ2), Z (K e2, σ2)) ε -∗ exec_ub (K e1) σ1 Z ε.
  Proof.
    iIntros (Hv) "Hub".
    iAssert (⌜to_val e1 = None⌝)%I as "-#H"; [done|].
    iRevert "H".
    rewrite /exec_ub /exec_ub'.
    set (Φ := (λ x, ⌜to_val x.2.1 = None⌝ -∗
                     bi_least_fixpoint (exec_ub_pre Z) (x.1, (K x.2.1, x.2.2)))%I
           : prodO RO cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n (?&(?&?)) (?&(?&?)) [[=] [[=] [=]]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter
                  (exec_ub_pre (λ '(e2, σ2), Z (K e2, σ2))) Φ
                 with "[]") as "H"; last first.
    { iIntros (?). iApply ("H" $! (_, (_, _)) with "Hub [//]"). }
    iIntros "!#" ([ε' [? σ']]). rewrite /exec_ub_pre.
    iIntros "[(% & % & % & H) | H] %Hv'".
    - rewrite least_fixpoint_unfold.
      iLeft. simpl.
      iExists (λ '(e2, σ2), ∃ e2', e2 = K e2' ∧ R2 (e2', σ2)).
      rewrite fill_dmap //=.
      iSplit; [eauto using reducible_fill|].
      iSplit.
      { iPureIntro.
        rewrite <- Rplus_0_r.
        eapply (ub_lift_dbind _ _ R2).
        - eapply ub_nonneg_grad; eauto.
        - lra.
        - intros [] ?? =>/=.
          apply ub_lift_dret.
          eauto.
        - auto.
       }
      iIntros ([] (? & -> & ?)).
      by iMod ("H" with "[//]").
    - rewrite least_fixpoint_unfold /=.
      iRight. 
      iInduction (get_active σ') as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(%R2 & %ε1 & %ε2 & (%Hleq & %Hub & H)) | Ht]".
      + iLeft.
        iExists _.
        iExists _.
        iExists _.
        iSplit; [done|].
        iSplit; [done|].
        iIntros. by iApply ("H" with "[//]").
      + iRight. by iApply ("IH" with "Ht").
  Qed.

  Lemma exec_ub_prim_step e1 σ1 Z ε :
    (∃ R, ⌜reducible e1 σ1⌝ ∗
          ⌜ub_lift (prim_step e1 σ1) R ε⌝ ∗
          ∀ ρ2, ⌜R ρ2⌝ ={∅}=∗ Z ρ2)
    ⊢ exec_ub e1 σ1 Z ε.
  Proof.
    iIntros "H".
    rewrite {1}exec_ub_unfold.
    by iLeft.
  Qed.

  (* TODO: Maybe allow weakening of the grading *)
  Lemma exec_ub_state_step α e1 σ1 Z ε ε' :
    α ∈ get_active σ1 →
    (∃ R, ⌜ub_lift (state_step σ1 α) R ε⌝ ∗
          ∀ σ2 , ⌜R σ2 ⌝ ={∅}=∗ exec_ub e1 σ2 Z ε')
    ⊢ exec_ub e1 σ1 Z (ε + ε').
  Proof.
    iIntros (?) "H".
    iDestruct "H" as (?) "H".
    rewrite {1}exec_ub_unfold.
    iRight.
    iApply big_orL_elem_of; eauto.
  Qed.

  (* This lemma might not be true anymore *)
  (*
  Lemma exec_ub_reducible e σ Z ε :
    exec_ub e σ Z ε ={∅}=∗ ⌜reducible e σ⌝.
  Proof.
    rewrite /exec_ub /exec_ub'.
    set (Φ := (λ x, |={∅}=> ⌜reducible x.2.1 x.2.2⌝)%I : prodO RO cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n (?&(?&?)) (?&(?&?)) [[=] [[=] [=]]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter (exec_ub_pre Z) Φ
                 with "[]") as "H"; last first.
    { done. }
    iIntros "!>" ((ε' & [e1 σ1])). rewrite /exec_ub_pre.
    iIntros "[(% & % & % & H) | H] /="; auto.
    rewrite /Φ/=.
    Search "big_orL".
    iDestruct (big_orL_mono _ (λ n αs, |={∅}=> ⌜reducible e1 σ1⌝)%I  with "H") as "H".
      { iIntros (? α' ?%elem_of_list_lookup_2) "(%R2 & %ε1 & %ε2 & %Hleq & %Hub & H)".
        eapply ub_lift_pos_R in Hub.
        eapply Rcoupl_inhabited_l in Hcpl as (σ2 & [] & ? & ? & ?); last first.
        { rewrite state_step_mass //. lra. }
        iApply (pure_impl_1 (reducible e1 σ2)).
        { iPureIntro. by eapply state_step_reducible. }
        by iMod ("H" with "[//]"). }
      iInduction (get_active σ1) as [| α] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[? | H]"; [done|].
      by iApply "IH".
    - iDestruct (big_orL_mono _ (λ n αs, |={∅}=> ⌜reducible e1 σ1⌝)%I  with "H") as "H".
      { iIntros (? [α1 α2] [? ?]%elem_of_list_lookup_2%elem_of_list_prod_1) "(% & %Hcpl & H)".
        eapply Rcoupl_pos_R in Hcpl.
        eapply Rcoupl_inhabited_l in Hcpl as (σ2 &?&?& Hs &?); last first.
        { rewrite state_step_mass //. lra. }
        iApply (pure_impl_1 (reducible e1 σ2)).
        { iPureIntro. by eapply state_step_reducible. }
        by iMod ("H" with "[//]"). }
      iInduction (list_prod (get_active σ1) (get_active σ1')) as [| [α α']] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[? | H]"; [done|].
      by iApply "IH".
  Qed.
  *)

  (*
  Lemma exec_coupl_det_r n e1 σ1 e1' σ1' e2' σ2' Z :
    exec n (e1', σ1') (e2', σ2') = 1 →
    exec_coupl e1 σ1 e2' σ2' Z -∗
    exec_coupl e1 σ1 e1' σ1' Z.
  Proof.
    iIntros (Hexec%pmf_1_eq_dret) "Hcpl".
    iApply exec_coupl_exec_r.
    iExists _, n. iSplit.
    { iPureIntro. apply Rcoupl_pos_R, Rcoupl_trivial.
      - apply dret_mass.
      - rewrite Hexec; apply dret_mass. }
    iIntros (e2'' σ2'' (_ & _ & H)).
    rewrite Hexec in H. by apply dret_pos in H as [= -> ->].
  Qed.
  *)

End exec_ub.

(** * The weakest precondition  *)
Definition ub_wp_pre `{!irisGS Λ Σ} (s : stuckness)
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 ε,
      state_interp σ1 ∗ err_interp ε ={E,∅}=∗
      ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
      ∃ ε1 ε2, ⌜ ε1 + ε2 <= ε ⌝ ∗
      exec_ub e1 σ1 (λ '(e2, σ2),
        ▷ |={∅,E}=> state_interp σ2 ∗ err_interp ε2 ∗ wp E e2 Φ) ε1
end%I.

Local Instance wp_pre_contractive `{!irisGS Λ Σ} s : Contractive (ub_wp_pre s).
Proof.
  rewrite /ub_wp_pre /= => n wp wp' Hwp E e1 Φ /=.
  do 13 (f_equiv).
  apply least_fixpoint_ne_outer; [|done].
  intros Ψ [ε' [e' σ']]. rewrite /exec_ub_pre.
  do 10 f_equiv.
  f_contractive.
  do 3 f_equiv.
  apply Hwp.
Qed.


(* TODO: get rid of stuckness in notation [iris/bi/weakestpre.v] so that we don't have to do this *)
Local Definition ub_wp_def `{!irisGS Λ Σ} : Wp (iProp Σ) (expr Λ) (val Λ) stuckness :=
  λ (s : stuckness), fixpoint (ub_wp_pre s).
Local Definition ub_wp_aux : seal (@ub_wp_def). Proof. by eexists. Qed.
Definition ub_wp' := ub_wp_aux.(unseal).
Global Arguments ub_wp' {Λ Σ _}.
Global Existing Instance ub_wp'.
Local Lemma ub_wp_unseal `{!irisGS Λ Σ} : wp = @ub_wp_def Λ Σ _.
Proof. rewrite -ub_wp_aux.(seal_eq) //. Qed.

Section ub_wp.
Context `{!irisGS Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types ρ : cfg Λ.
Implicit Types ε : R.

(* Weakest pre *)
Lemma ub_wp_unfold s E e Φ :
  WP e @ s; E {{ Φ }} ⊣⊢ ub_wp_pre s (wp (PROP:=iProp Σ) s) E e Φ.
Proof. rewrite ub_wp_unseal. apply (fixpoint_unfold (ub_wp_pre s)). Qed.

Global Instance ub_wp_ne s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !ub_wp_unfold /ub_wp_pre /=.
  do 13 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? []]. rewrite /exec_ub_pre.
  do 10 f_equiv.
  f_contractive.
  do 3 f_equiv. rewrite IH; [done|lia|].
  intros ?. eapply dist_S, HΦ.
Qed.

Global Instance ub_wp_proper s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply ub_wp_ne=>v; apply equiv_dist.
Qed.
Global Instance ub_wp_contractive s E e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !ub_wp_unfold /ub_wp_pre He /=.
  do 12 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [? []]. rewrite /exec_ub_pre.
  do 10 f_equiv.
  f_contractive. do 6 f_equiv.
Qed.

Lemma ub_wp_value_fupd' s E Φ v : WP of_val v @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. rewrite ub_wp_unfold /ub_wp_pre to_of_val. auto. Qed.

Lemma ub_wp_strong_mono s1 s2 E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  WP e @ s1; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s2; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
  rewrite !ub_wp_unfold /ub_wp_pre /=.
  destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1 ε) "[Hσ Hε]".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "[% H]".
  iDestruct "H" as (ε1  ε2  Hleq) "H".
  iModIntro.
  iSplit; [by destruct s1, s2 | ].
  iExists _.
  iExists _.
  iSplit; [done | ].
  iApply (exec_ub_mono_pred with "[Hclose HΦ] H").
  iIntros ([e2 σ2]) "H".
  iModIntro.
  iMod "H" as "(?&?& Hwp)". iFrame.
  iMod "Hclose" as "_". iModIntro.
  iApply ("IH" with "[] Hwp"); auto.
Qed.

Lemma fupd_ub_wp s E e Φ : (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite ub_wp_unfold /ub_wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1 ε) "Hi". iMod "H". by iApply "H".
Qed.
Lemma ub_wp_fupd s E e Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (ub_wp_strong_mono s s E with "H"); auto. Qed.

Lemma ub_wp_atomic s E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !ub_wp_unfold /ub_wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (σ1 ε) "[Hσ Hε]". iMod "H".
  iMod ("H" with "[$]") as "[$ H]".
  iModIntro.
  iDestruct "H" as (ε1  ε2  Hleq) "H".
  iExists _.
  iExists _.
  iSplit; [done | ].
  iDestruct (exec_ub_strengthen with "H") as "H".
  iApply (exec_ub_mono_pred with "[] H").
  iIntros ([e2 σ2]) "[[% %Hstep] H]".
  iModIntro.
  iMod "H" as "(Hσ & Hρ & H)".
  destruct s.
  - rewrite !ub_wp_unfold /ub_wp_pre.
    destruct (to_val e2) as [v2|] eqn:He2.
    + iDestruct "H" as ">> $". by iFrame.
    + iMod ("H" with "[$]") as "H".
      iDestruct "H" as (? ε3 ε4 Hleq2) "H".
      pose proof (atomic σ e2 σ2 Hstep) as H3.
      case_match.
      * rewrite /is_Some in H3.
        destruct H3.
        simplify_eq.
      * apply not_reducible in H3.
        done.
  - destruct (atomic σ e2 σ2 Hstep).
    rewrite <- (of_to_val _ _ H).
    rewrite ub_wp_value_fupd'. iMod "H" as ">H".
    iModIntro.
    iFrame.
    by iApply ub_wp_value_fupd'.
Qed.

Lemma ub_wp_step_fupd s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite !ub_wp_unfold /ub_wp_pre. iIntros (-> ?) "HR H".
  iIntros (σ1 ε) "[Hσ Hε]". iMod "HR".
  iMod ("H" with "[$Hσ $Hε]") as "[% H]".
  iModIntro.
  iDestruct "H" as (ε3 ε4 Hleq2) "H".
  iSplit; [done | ].
  iExists _.
  iExists _.
  iSplit; [done | ].
  iApply (exec_ub_mono_pred with "[HR] H").
  iIntros ([e2 σ2]) "H".
  iModIntro.
  iMod "H" as "(Hσ & Hρ & H)".
  iMod "HR".
  iFrame "Hσ Hρ".
  iApply (ub_wp_strong_mono s s E2 with "H"); [done..|].
  iIntros "!>" (v) "H". by iApply "H".
Qed.

Lemma ub_wp_bind K `{!LanguageCtx K} s E e Φ :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite ub_wp_unfold /ub_wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_ub_wp. }
  rewrite ub_wp_unfold /ub_wp_pre fill_not_val /=; [|done].
  iIntros (σ1 ε) "[Hσ Hε]".
  iMod ("H" with "[$Hσ $Hε]") as "(%Hs & % & % & % & H)".
  iModIntro.
  iSplit.
  - iPureIntro. destruct s; auto.
    apply reducible_fill; auto.
  - iExists ε1.
    iExists ε2.
    iSplit; [by iPureIntro | ].
    iApply exec_ub_bind; [done |].
    iApply (exec_ub_mono with "[] [] H").
    + iPureIntro; lra.
    + iIntros ([e2 σ2]) "H".
      iModIntro.
      iMod "H" as "(Hσ & Hρ & H)".
      iModIntro.
      iFrame "Hσ Hρ". by iApply "IH".
Qed.

(* Lemma wp_bind_inv K `{!LanguageCtx K} s E e Φ : *)
(*   WP K e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }}. *)
(* Proof. *)
(*   iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre /=. *)
(*   destruct (to_val e) as [v|] eqn:He. *)
(*   { apply of_to_val in He as <-. by rewrite !wp_unfold /wp_pre. } *)
(*   rewrite fill_not_val //. *)
(*   iIntros (σ1 ns κ κs nt) "Hσ". iMod ("H" with "[$]") as "[% H]". *)
(*   iModIntro; iSplit. *)
(*   { destruct s; eauto using reducible_fill_inv. } *)
(*   iIntros (e2 σ2 efs Hstep) "Hcred". *)
(*   iMod ("H" $! _ _ _ with "[] Hcred") as "H"; first eauto using fill_step. *)
(*   iIntros "!> !>". iMod "H". iModIntro. iApply (step_fupdN_wand with "H"). *)
(*   iIntros "H". iMod "H" as "($ & H & $)". iModIntro. by iApply "IH". *)
(* Qed. *)

(** * Derived rules *)
Lemma ub_wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (ub_wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma ub_wp_stuck_mono s1 s2 E e Φ :
  s1 ⊑ s2 → WP e @ s1; E {{ Φ }} ⊢ WP e @ s2; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (ub_wp_strong_mono with "H"); auto. Qed.
Lemma ub_wp_stuck_weaken s E e Φ :
  WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }}.
Proof. apply ub_wp_stuck_mono. by destruct s. Qed.
Lemma ub_wp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (ub_wp_strong_mono with "H"); auto. Qed.
Global Instance ub_wp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply ub_wp_mono. Qed.
Global Instance ub_wp_flip_mono' s E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply ub_wp_mono. Qed.

Lemma ub_wp_value_fupd s E Φ e v : IntoVal e v → WP e @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. intros <-. by apply ub_wp_value_fupd'. Qed.
Lemma ub_wp_value' s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
Proof. rewrite ub_wp_value_fupd'. auto. Qed.
Lemma ub_wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. apply ub_wp_value'. Qed.

Lemma ub_wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (ub_wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma ub_wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (ub_wp_strong_mono with "H"); auto with iFrame. Qed.

Lemma ub_wp_frame_step_l s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (ub_wp_step_fupd with "Hu"); try done.
  iApply (ub_wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma ub_wp_frame_step_r s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  WP e @ s; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply ub_wp_frame_step_l.
Qed.
Lemma ub_wp_frame_step_l' s E e Φ R :
  TCEq (to_val e) None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (ub_wp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma ub_wp_frame_step_r' s E e Φ R :
  TCEq (to_val e) None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (ub_wp_frame_step_r s E E); try iFrame; eauto. Qed.

Lemma ub_wp_wand s E e Φ Ψ :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (ub_wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma ub_wp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (ub_wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e Φ Ψ :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (ub_wp_wand with "Hwp H"). Qed.
Lemma ub_wp_frame_wand s E e Φ R :
  R -∗ WP e @ s; E {{ v, R -∗ Φ v }} -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (ub_wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End ub_wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisGS Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_ub_wp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite ub_wp_frame_l. apply ub_wp_mono, HR. Qed.

  Global Instance is_except_0_ub_wp s E e Φ : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_ub_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_ub_wp p s E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_ub_wp.
  Qed.

  Global Instance elim_modal_fupd_ub_wp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_ub_wp.
  Qed.

  Global Instance elim_modal_fupd_ub_wp_atomic p s E1 E2 e P Φ :
    ElimModal (Atomic (stuckness_to_atomicity s) e) p false
            (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?.
    by rewrite intuitionistically_if_elim
      fupd_frame_r wand_elim_r ub_wp_atomic.
  Qed.

  Global Instance add_modal_fupd_ub_wp s E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_ub_wp. Qed.

  Global Instance elim_acc_ub_wp_atomic {X} E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic (stuckness_to_atomicity s) e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; E1 {{ Φ }})
            (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (ub_wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_ub_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply ub_wp_fupd.
    iApply (ub_wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.
