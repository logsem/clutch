From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext NNRbar.
From clutch.prob Require Export generic_lifting distribution.
From clutch.common Require Export exec language.
From iris.bi Require Export weakestpre.

Import uPred.

Class irisGS (Λ : language) (Σ : gFunctors) := IrisG {
  iris_invGS :: invGS_gen HasNoLc Σ;
  state_interp : state Λ → iProp Σ;
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



(** * The mlift modality [exec_mlift]  *)
Section exec_mlift.
  Context `{!irisGS Λ Σ}.

  Context (M : mlift).

  Definition exec_mlift_pre (Z : cfg Λ → iProp Σ) (Φ : cfg Λ → iProp Σ) :=
    (λ (x  : cfg Λ),
      let '(e1, σ1) := x in
      (* [prim_step] *)
      (∃ R, ⌜M.(mlift_funct) (prim_step e1 σ1) R ⌝ ∗
            ∀ ρ2, ⌜ R ρ2 ⌝ ={∅}=∗ Z ρ2 ) ∨
      (* [state_step]  *)
      ([∨ list] α ∈ get_active σ1,
        (∃ R , ⌜ M.(mlift_funct) (state_step σ1 α) R ⌝ ∗
              ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ Φ ((e1, σ2))))
    )%I.

  Local Instance exec_state_ub_pre_NonExpansive Z Φ :
    NonExpansive (exec_mlift_pre Z Φ).
  Proof.
    rewrite /exec_mlift_pre.
    intros n (?&?) (?&?) [[=] [=]].
    by simplify_eq.
  Qed.

  Local Instance exec_coupl_pre_mono Z : BiMonoPred (exec_mlift_pre Z).
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    rewrite /exec_mlift_pre.
    iIntros ((e1 & σ1)) "Hexec".
    iDestruct "Hexec" as "[H | H]".
    - by iLeft.
    - iRight.
      iInduction (get_active σ1) as [| l] "IH" forall "H".
      { rewrite big_orL_nil //. }
      rewrite !big_orL_cons.
      iDestruct "H" as "[(% & Hlift & HΦ) | H]".
      + iLeft. iExists R2.
        iSplit; [try done|].
        iIntros. iApply "Hwand". by iApply "HΦ".
      + iRight. by iApply "IH".
  Qed.

  Definition exec_mlift' Z := bi_least_fixpoint (exec_mlift_pre Z).
  Definition exec_mlift e σ Z := exec_mlift' Z (e, σ).

  Lemma exec_mlift_unfold e1 σ1 Z :
    exec_mlift e1 σ1 Z ≡
      ((∃ R, ⌜M.(mlift_funct) (prim_step e1 σ1) R ⌝ ∗
            ∀ ρ2, ⌜ R ρ2 ⌝ ={∅}=∗ Z ρ2 ) ∨
      ([∨ list] α ∈ get_active σ1,
        (∃ R, ⌜ M.(mlift_funct) (state_step σ1 α) R ⌝ ∗
              ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ exec_mlift e1 σ2 Z )))%I.
  Proof. rewrite /exec_mlift/exec_mlift' least_fixpoint_unfold //. Qed.

  Local Definition cfgO := (prodO (exprO Λ) (stateO Λ)).


  Lemma exec_mlift_strong_mono e1 σ1 (Z1 Z2 : cfg Λ → iProp Σ) :
    (∀ e2 σ2, (⌜∃ σ, (prim_step e1 σ (e2, σ2) > 0)%R⌝ ∗ Z1 (e2, σ2) -∗ Z2 (e2, σ2))) -∗
    exec_mlift e1 σ1 Z1 -∗ exec_mlift e1 σ1 Z2.
  Proof.
    iIntros "HZ H_mlift".
    iRevert "HZ".
    rewrite /exec_mlift /exec_mlift'.
    set (Φ := (λ x,(∀ e2 σ2, ⌜∃ σ, (prim_step x.1 σ (e2, σ2) > 0)%R⌝ ∗ Z1 (e2, σ2) -∗ Z2 (e2, σ2)) -∗
                  (bi_least_fixpoint (exec_mlift_pre Z2) x ))%I : cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n (?&?) (?&?) [[=] [=]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter (exec_mlift_pre Z1) Φ with "[]") as "H"; last first.
    { by iApply ("H" with "H_mlift"). }
    iIntros "!#" ([? σ']). rewrite /exec_mlift_pre.
    iIntros "[ (% & % & H) | H ] HZ /=".
    - rewrite least_fixpoint_unfold.
      iLeft. iExists _.
      iSplit.
      { iPureIntro.
        by apply M.(mlift_posR). }
      iIntros ([] (?&?)). iMod ("H" with "[//]").
      iModIntro. iApply "HZ". eauto.
    - rewrite least_fixpoint_unfold.
      iRight.
      iInduction (get_active σ') as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(%R2 & (% & H)) | Ht]".
      + iLeft. iExists R2.
        iSplit; [done | ].
        iIntros.
        by iApply ("H" with "[//]").
      + iRight. by iApply ("IH" with "Ht").
  Qed.

  Lemma exec_mlift_mono (Z1 Z2 : cfg Λ → iProp Σ) e1 σ1 :
    (∀ ρ, Z1 ρ -∗ Z2 ρ ) -∗ exec_mlift e1 σ1 Z1 -∗ exec_mlift e1 σ1 Z2.
  Proof.
    iIntros "HZ". iApply exec_mlift_strong_mono; auto.
    iIntros (??) "[_ ?]". by iApply "HZ".
  Qed.

  Lemma exec_mlift_mono_pred (Z1 Z2 : cfg Λ → iProp Σ) e1 σ1 :
    (∀ ρ, Z1 ρ -∗ Z2 ρ ) -∗ exec_mlift e1 σ1 Z1 -∗ exec_mlift e1 σ1 Z2.
  Proof.
    iIntros "HZ". iApply exec_mlift_strong_mono; auto.
    iIntros (??) "[_ ?]". by iApply "HZ".
  Qed.

  Lemma exec_mlift_strengthen e1 σ1 (Z : cfg Λ → iProp Σ) :
    exec_mlift e1 σ1 Z -∗
    exec_mlift e1 σ1 (λ '(e2, σ2), ⌜∃ σ, (prim_step e1 σ (e2, σ2) > 0)%R⌝ ∧ Z (e2, σ2)).
  Proof.
    iApply exec_mlift_strong_mono.
    iIntros (??) "[[% ?] ?]". iSplit; [|done]. by iExists _.
  Qed.

  Lemma exec_mlift_bind K `{!LanguageCtx K} e1 σ1 (Z : cfg Λ → iProp Σ)  :
    to_val e1 = None →
    exec_mlift e1 σ1 (λ '(e2, σ2), Z (K e2, σ2)) -∗ exec_mlift (K e1) σ1 Z.
  Proof.
    iIntros (Hv) "Hmlift".
    iAssert (⌜to_val e1 = None⌝)%I as "-#H"; [done|].
    iRevert "H".
    rewrite /exec_mlift /exec_mlift'.
    set (Φ := (λ x, ⌜to_val x.1 = None⌝ -∗
                     bi_least_fixpoint (exec_mlift_pre Z) (K x.1, x.2))%I
           : cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n (?&?) (?&?) [[=] [=]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter
                  (exec_mlift_pre (λ '(e2, σ2), Z (K e2, σ2))) Φ
                 with "[]") as "H"; last first.
    { iIntros (?). iApply ("H" $! (_, _) with "Hmlift [//]"). }
    iIntros "!#" ([? σ']). rewrite /exec_mlift_pre.
    iIntros "[(% & % & H) | H] %Hv'".
    - rewrite least_fixpoint_unfold.
      iLeft. simpl.
      iExists (λ '(e2, σ2), ∃ e2', e2 = K e2' ∧ R2 (e2', σ2)).
      rewrite fill_dmap //=.
      iSplit.
      { iPureIntro.
        eapply (M.(mlift_bind) _ _ R2); eauto.
        intros [] ? =>/=.
        apply M.(mlift_unit).
        eauto.
       }
      iIntros ([] (? & -> & ?)).
      by iMod ("H" with "[//]").
    - rewrite least_fixpoint_unfold /=.
      iRight. 
      iInduction (get_active σ') as [| l] "IH".
      { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(%R2 & (%Hleq & H)) | Ht]".
      + iLeft.
        iExists _.
        iSplit; [done|].
        iIntros. by iApply ("H" with "[//]").
      + iRight. by iApply ("IH" with "Ht").
  Qed.

  Lemma exec_mlift_prim_step e1 σ1 Z :
    (∃ R, ⌜M.(mlift_funct) (prim_step e1 σ1) R⌝ ∗
          ∀ ρ2, ⌜R ρ2⌝ ={∅}=∗ Z ρ2)
    ⊢ exec_mlift e1 σ1 Z.
  Proof.
    iIntros "H".
    rewrite {1}exec_mlift_unfold.
    by iLeft.
  Qed.

  (* TODO: Maybe allow weakening of the grading *)
  Lemma exec_mlift_state_step α e1 σ1 Z :
    α ∈ get_active σ1 →
    (∃ R, ⌜M.(mlift_funct) (state_step σ1 α) R ⌝ ∗
          ∀ σ2 , ⌜R σ2 ⌝ ={∅}=∗ exec_mlift e1 σ2 Z )
    ⊢ exec_mlift e1 σ1 Z.
  Proof.
    iIntros (?) "H".
    iDestruct "H" as (?) "H".
    rewrite {1}exec_mlift_unfold.
    iRight.
    iApply big_orL_elem_of; eauto.
  Qed.

(*
  Lemma exec_ub_reducible e σ Z1 Z2 ε1 ε2 :
    (exec_ub e σ Z1 ε1)  ={∅}=∗ ⌜irreducible e σ⌝ -∗ (exec_ub e σ Z2 ε2).
  Proof.
    rewrite /exec_ub /exec_ub'.
    set (Φ := (λ x, |={∅}=> ⌜irreducible x.2.1 x.2.2⌝ -∗ (exec_ub x.2.1 x.2.2 Z2 ε2))%I : prodO NNRO cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n (?&(?&?)) (?&(?&?)) [[=] [[=] [=]]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter (exec_ub_pre Z1) Φ
                 with "[]") as "H"; last first.
    { done. }
    iIntros "!>" ((ε' & [e1 σ1])). rewrite /exec_ub_pre.
    iIntros "[(% & % & % & H) | H] /="; auto;
    rewrite /Φ/=.
    - iModIntro.
      iIntros.
      exfalso.
      pose proof (not_reducible e1 σ1) as (H3 & H4).
      by apply H4.
    - iDestruct (big_orL_mono _ (λ n αs, |={∅}=> ⌜irreducible e1 σ1⌝ -∗ exec_ub e1 σ1 Z2 ε2)%I  with "H") as "H".
      { intros.
        iIntros.
        iModIntro.
        iIntros.
        rewrite exec_ub_unfold.
        iRight.
        iApply (big_orL_elem_of _ _ y).
        - eapply elem_of_list_lookup_2; eauto.
        -
*)

(*
  Lemma exec_ub_irreducible e σ Z ε :
    ⌜irreducible e σ⌝ ⊢ exec_ub e σ Z ε.
  Proof.
    iIntros "H".
    rewrite {1}exec_ub_unfold.
    iRight.
    iInduction (get_active σ) as [| l] "IH".
    { rewrite big_orL_nil //. }
      rewrite 2!big_orL_cons.
      iDestruct "H" as "[(%R2 & %ε1 & %ε2 & (%Hleq & %Hub & H)) | Ht]".
*)

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

End exec_mlift.


(** * The weakest precondition  *)
Definition mlift_wp_pre `{!irisGS Λ Σ} (M : mlift)
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1,
      state_interp σ1 ={E,∅}=∗
      ⌜reducible (e1, σ1)⌝ ∗
      exec_mlift M e1 σ1 (λ '(e2, σ2),
        ▷ |={∅,E}=> state_interp σ2 ∗ wp E e2 Φ)
end%I.

Local Instance wp_pre_contractive `{!irisGS Λ Σ} M : Contractive (mlift_wp_pre M).
Proof.
  rewrite /mlift_wp_pre /= => n wp wp' Hwp E e1 Φ /=.
  do 6 (f_equiv);
  apply least_fixpoint_ne_outer; [|done].
  intros Ψ [e' σ']. rewrite /exec_mlift_pre.
  do 9 f_equiv.
  f_contractive.
  do 2 f_equiv.
  apply Hwp.
Qed.


(* We use the extra argument to pass the mlift to the Wp *)
Local Definition mlift_wp_def `{!irisGS Λ Σ} : Wp (iProp Σ) (expr Λ) (val Λ) mlift := λ M0, fixpoint (mlift_wp_pre M0).
Local Definition mlift_wp_aux : seal (@mlift_wp_def). Proof. by eexists. Qed.
Definition mlift_wp' := mlift_wp_aux.(unseal).
Global Arguments mlift_wp' {Λ Σ _}.
Global Existing Instance mlift_wp'.
Local Lemma mlift_wp_unseal `{!irisGS Λ Σ} : wp = @mlift_wp_def Λ Σ _.
Proof. rewrite -mlift_wp_aux.(seal_eq) //. Qed.

Section wp_mlift.

Context `{!irisGS Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types ρ : cfg Λ.


(* Weakest pre *)
Lemma mlift_wp_unfold M E e Φ :
  WP e @ M; E {{ Φ }} ⊣⊢ mlift_wp_pre M (wp (PROP:=iProp Σ) M) E e Φ.
Proof. rewrite mlift_wp_unseal. apply (fixpoint_unfold (mlift_wp_pre M)). Qed.

Global Instance mlift_wp_ne M E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) M E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !mlift_wp_unfold /mlift_wp_pre /=.
  do 6 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? []. rewrite /exec_mlift_pre.
  do 9 f_equiv.
  f_contractive_fin.
  do 2 f_equiv. rewrite IH; [done|lia|].
  intros ?. eapply dist_S, HΦ.
Qed.

Global Instance mlift_wp_proper M E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) M E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply mlift_wp_ne=>v; apply equiv_dist.
Qed.
Global Instance mlift_wp_contractive M E e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) M E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !mlift_wp_unfold /mlift_wp_pre He /=.
  do 5 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? []. rewrite /exec_mlift_pre.
  do 9 f_equiv.
  f_contractive. do 5 f_equiv.
Qed.

Lemma mlift_wp_value_fupd' M E Φ v : WP of_val v @ M; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. rewrite mlift_wp_unfold /mlift_wp_pre to_of_val. auto. Qed.

(* Removed the stuckness assumption s1 ⊑ s2, maybe something similar
   can be done for mlifts? *)
Lemma mlift_wp_strong_mono M E1 E2 e Φ Ψ :
  E1 ⊆ E2 →
  WP e @ M; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ M; E2 {{ Ψ }}.
Proof.
  iIntros (HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
  rewrite !mlift_wp_unfold /mlift_wp_pre /=.
  destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1) "Hσ".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "[% H]".
  iModIntro.
  iSplit; [by destruct M | ].
  iApply (exec_mlift_mono_pred with "[Hclose HΦ] H").
  iIntros ([e2 σ2]) "H".
  iModIntro.
  iMod "H" as "[? Hwp]". iFrame.
  iMod "Hclose" as "_". iModIntro.
  iApply ("IH" with "[] Hwp"); auto.
Qed.

Lemma fupd_mlift_wp M E e Φ : (|={E}=> WP e @ M; E {{ Φ }}) ⊢ WP e @ M; E {{ Φ }}.
Proof.
  rewrite mlift_wp_unfold /mlift_wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1). iMod "H". by iApply "H".
Qed.
Lemma mlift_wp_fupd M E e Φ : WP e @ M; E {{ v, |={E}=> Φ v }} ⊢ WP e @ M; E {{ Φ }}.
Proof. iIntros "H". iApply (mlift_wp_strong_mono M E with "H"); auto. Qed.

(* Do we want WeaklyAtomic here? *)
Lemma mlift_wp_atomic M E1 E2 e Φ `{!Atomic WeaklyAtomic e} :
  (|={E1,E2}=> WP e @ M; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ M; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !mlift_wp_unfold /mlift_wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (σ1) "Hσ". iMod "H".
  iMod ("H" with "[$]") as "[$ H]".
  iModIntro.
  iDestruct (exec_mlift_strengthen with "H") as "H".
  iApply (exec_mlift_mono_pred with "[] H").
  iIntros ([e2 σ2]) "[[% %Hstep] H]".
  iModIntro.
  iMod "H" as "(Hσ & H)".
  rewrite !mlift_wp_unfold /mlift_wp_pre.
  destruct (to_val e2) as [v2|] eqn:He2.
  - iDestruct "H" as ">> $". by iFrame.
  - iMod ("H" with "[$]") as "H".
    iDestruct "H" as (?) "H".
    pose proof (atomic σ e2 σ2 Hstep) as H3.
    case_match.
    + rewrite /is_Some in H3.
      destruct H3.
      simplify_eq.
    + apply not_reducible in H3.
      done.
Qed.


Lemma mlift_wp_step_fupd M E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ M; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ M; E1 {{ Φ }}.
Proof.
  rewrite !mlift_wp_unfold /mlift_wp_pre. iIntros (-> ?) "HR H".
  iIntros (σ1) "Hσ". iMod "HR".
  iMod ("H" with "[$Hσ]") as "[% H]".
  iModIntro.
  iSplit; [done | ].
  iApply (exec_mlift_mono_pred with "[HR] H").
  iIntros ([e2 σ2]) "H".
  iModIntro.
  iMod "H" as "(Hσ & H)".
  iMod "HR".
  iFrame "Hσ".
  iApply (mlift_wp_strong_mono M E2 with "H"); [done..|].
  iIntros "!>" (v) "H". by iApply "H".
Qed.

Lemma mlift_wp_bind K `{!LanguageCtx K} M E e Φ :
  WP e @ M; E {{ v, WP K (of_val v) @ M; E {{ Φ }} }} ⊢ WP K e @ M; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite mlift_wp_unfold /mlift_wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_mlift_wp. }
  rewrite mlift_wp_unfold /mlift_wp_pre fill_not_val /=; [|done].
  iIntros (σ1) "Hσ".
  iMod ("H" with "[$Hσ]") as "(%Hs & H)".
  iModIntro.
  iSplit.
  - iPureIntro.
    apply reducible_fill; auto.
  - iApply exec_mlift_bind; [done |].
    iApply (exec_mlift_mono with "[] H").
    iIntros ([e2 σ2]) "H".
    iModIntro.
    iMod "H" as "(Hσ & H)".
    iModIntro.
    iFrame "Hσ". by iApply "IH".
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
Lemma mlift_wp_mono M E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ M; E {{ Φ }} ⊢ WP e @ M; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (mlift_wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.

(* Can we adapt this for mlifts? *)
(*
Lemma mlift_wp_stuck_mono s1 s2 E e Φ :
  s1 ⊑ s2 → WP e @ s1; E {{ Φ }} ⊢ WP e @ s2; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (mlift_wp_strong_mono with "H"); auto. Qed.
Lemma mlift_wp_stuck_weaken s E e Φ :
  WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }}.
Proof. apply mlift_wp_stuck_mono. by destruct s. Qed.
*)
Lemma mlift_wp_mask_mono M E1 E2 e Φ : E1 ⊆ E2 → WP e @ M; E1 {{ Φ }} ⊢ WP e @ M; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (mlift_wp_strong_mono with "H"); auto. Qed.
Global Instance mlift_wp_mono' M E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) M E e).
Proof. by intros Φ Φ' ?; apply mlift_wp_mono. Qed.
Global Instance mlift_wp_flip_mono' M E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) M E e).
Proof. by intros Φ Φ' ?; apply mlift_wp_mono. Qed.

Lemma mlift_wp_value_fupd M E Φ e v : IntoVal e v → WP e @ M; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. intros <-. by apply mlift_wp_value_fupd'. Qed.
Lemma mlift_wp_value' M E Φ v : Φ v ⊢ WP (of_val v) @ M; E {{ Φ }}.
Proof. rewrite mlift_wp_value_fupd'. auto. Qed.
Lemma mlift_wp_value M E Φ e v : IntoVal e v → Φ v ⊢ WP e @ M; E {{ Φ }}.
Proof. intros <-. apply mlift_wp_value'. Qed.

Lemma mlift_wp_frame_l M E e Φ R : R ∗ WP e @ M; E {{ Φ }} ⊢ WP e @ M; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (mlift_wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma mlift_wp_frame_r M E e Φ R : WP e @ M; E {{ Φ }} ∗ R ⊢ WP e @ M; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (mlift_wp_strong_mono with "H"); auto with iFrame. Qed.

Lemma mlift_wp_frame_step_l M E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ WP e @ M; E2 {{ Φ }} ⊢ WP e @ M; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (mlift_wp_step_fupd with "Hu"); try done.
  iApply (mlift_wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma mlift_wp_frame_step_r M E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  WP e @ M; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ M; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply mlift_wp_frame_step_l.
Qed.
Lemma mlift_wp_frame_step_l' M E e Φ R :
  TCEq (to_val e) None → ▷ R ∗ WP e @ M; E {{ Φ }} ⊢ WP e @ M; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (mlift_wp_frame_step_l M E E); try iFrame; eauto. Qed.
Lemma mlift_wp_frame_step_r' M E e Φ R :
  TCEq (to_val e) None → WP e @ M; E {{ Φ }} ∗ ▷ R ⊢ WP e @ M; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (mlift_wp_frame_step_r M E E); try iFrame; eauto. Qed.

Lemma mlift_wp_wand M E e Φ Ψ :
  WP e @ M; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ M; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (mlift_wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma mlift_wp_wand_l M E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ M; E {{ Φ }} ⊢ WP e @ M; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (mlift_wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r M E e Φ Ψ :
  WP e @ M; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ M; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (mlift_wp_wand with "Hwp H"). Qed.
Lemma mlift_wp_frame_wand M E e Φ R :
  R -∗ WP e @ M; E {{ v, R -∗ Φ v }} -∗ WP e @ M; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (mlift_wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End wp_mlift.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisGS Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_mlift_wp p M E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ M; E {{ Φ }}) (WP e @ M; E {{ Ψ }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite mlift_wp_frame_l. apply mlift_wp_mono, HR. Qed.

  Global Instance is_except_0_mlift_wp M E e Φ : IsExcept0 (WP e @ M; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_mlift_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_mlift_wp p M E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ M; E {{ Φ }}) (WP e @ M; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_mlift_wp.
  Qed.

  Global Instance elim_modal_fupd_mlift_wp p M E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ M; E {{ Φ }}) (WP e @ M; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_mlift_wp.
  Qed.

  Global Instance elim_modal_fupd_mlift_wp_atomic p M E1 E2 e P Φ :
    ElimModal (Atomic WeaklyAtomic e) p false
            (|={E1,E2}=> P) P
            (WP e @ M; E1 {{ Φ }}) (WP e @ M; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?.
    by rewrite intuitionistically_if_elim
      fupd_frame_r wand_elim_r mlift_wp_atomic.
  Qed.

  Global Instance add_modal_fupd_mlift_wp M E e P Φ :
    AddModal (|={E}=> P) P (WP e @ M; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_mlift_wp. Qed.

  Global Instance elim_acc_mlift_wp_atomic {X} E1 E2 α β γ e M Φ :
    ElimAcc (X:=X) (Atomic WeaklyAtomic e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ M; E1 {{ Φ }})
            (λ x, WP e @ M; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (mlift_wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_mlift_wp_nonatomic {X} E α β γ e M Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ M; E {{ Φ }})
            (λ x, WP e @ M; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply mlift_wp_fupd.
    iApply (mlift_wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.
