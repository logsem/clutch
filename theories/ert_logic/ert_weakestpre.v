From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export fixpoint big_op.
From iris.prelude Require Import options.

From clutch.bi Require Export weakestpre.
From clutch.prelude Require Import stdpp_ext iris_ext NNRbar.
From clutch.prob Require Export couplings distribution.
From clutch.common Require Export language.

From clutch.ert_logic Require Export expected_time_credits.

Import uPred.

#[local] Open Scope R_scope.

Class Costfun {Λ} := {
  cost : expr Λ → R;
  cost_bounded : ∃ r, ∀ e, cost e <= r;
  cost_nonneg e : 0 <= cost e;
  }.

Arguments Costfun Λ : clear implicits.

Class CostLanguageCtx {Λ} (cf : Costfun Λ) (K : expr Λ → expr Λ) := {
  cost_languagectx :: LanguageCtx (Λ := Λ) K;
  cost_fill e : cost (K e) = cost e;
}.

Class ertwpG (Λ : language) (Σ : gFunctors) := ErtwpG {
  ertwpG_invGS :: invGS_gen HasNoLc Σ;
  ertwpG_etcGS :: etcGS Σ;

  state_interp : state Λ → iProp Σ;
  costfun :: Costfun Λ;
}.
Global Opaque ertwpG_invGS.
Global Opaque ertwpG_etcGS.
Global Arguments ErtwpG {Λ Σ}.

(** * The expected runtime modality [ERM]  *)
Section ERM.
  Context `{!ertwpG Λ Σ}.
  Implicit Types x : nonnegreal.
  Implicit Types Z : cfg Λ → nonnegreal → iProp Σ.

  Definition ERM_pre (Z : cfg Λ → nonnegreal → iProp Σ) (Φ : cfg Λ * nonnegreal → iProp Σ) :=
    (λ (ρx : cfg Λ * nonnegreal),
      let '((e1, σ1), x) := ρx in
      (* [prim_step] with adv composition *)
      (∃ (X2 : cfg Λ → nonnegreal),
          ⌜reducible (e1, σ1)⌝ ∗
          ⌜∃ r, ∀ ρ, X2 ρ <= r⌝ ∗
          ⌜(cost e1 + SeriesC (λ ρ, prim_step e1 σ1 ρ * X2 ρ) <= x)%R⌝ ∗
          ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={∅}=∗ Z (e2, σ2) (X2 (e2, σ2))) (* ∨
         (* [state_step] with adv composition*)
         ([∨ list] α ∈ get_active σ1,
           (∃ R (x1 : nonnegreal) (x2 : cfg Λ -> nonnegreal),
             ⌜ ∃ r, ∀ ρ, (x2 ρ <= r)%R ⌝ ∗
             ⌜ (x1 + SeriesC (λ σ2, (state_step σ1 α σ2) * x2 (e1, σ2)) <= x)%R ⌝ ∗
             ⌜ub_lift (state_step σ1 α) R x1⌝ ∗
                 ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ exec_stutter (fun x' => Φ ((e1, σ2), x')) (x2 (e1, σ2)))) *)
    )%I.

  Local Instance exec_state_ub_pre_NonExpansive Z Φ :
    NonExpansive (ERM_pre Z Φ).
  Proof.
    rewrite /ERM_pre.
    intros n ((?&?)&?) ((?&?)&?) [ [[=] [=]] [=]].
    by simplify_eq.
  Qed.

  Local Instance exec_coupl_pre_mono Z : BiMonoPred (ERM_pre Z).
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    rewrite /ERM_pre.
    iIntros (((e1 & σ1) & x)) "Hexec".
    done.
  Qed.

  Definition ERM' Z := bi_least_fixpoint (ERM_pre Z).
  Definition ERM e σ x Z := ERM' Z ((e, σ), x).

  Lemma ERM_unfold e1 σ1 Z x :
    ERM e1 σ1 x Z ≡
      (
      (* [prim_step] with adv composition *)
      (∃ (X2 : cfg Λ → nonnegreal),
          ⌜reducible (e1, σ1)⌝ ∗
          ⌜∃ r, ∀ ρ, (X2 ρ <= r)%R⌝ ∗
          ⌜(cost e1 + SeriesC (λ ρ, prim_step e1 σ1 ρ * X2 ρ) <= x)%R⌝ ∗
          ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={∅}=∗ Z (e2, σ2) (X2 (e2, σ2))) (* ∨
         (* [state_step] with adv composition*)
         ([∨ list] α ∈ get_active σ1,
           (∃ R (x1 : nonnegreal) (x2 : cfg Λ -> nonnegreal),
             ⌜ ∃ r, forall ρ, (x2 ρ <= r)%R ⌝ ∗
             ⌜ (x1 + SeriesC (λ σ2, (state_step σ1 α σ2) * x2 (e1, σ2)) <= x)%R ⌝ ∗
             ⌜ub_lift (state_step σ1 α) R x1⌝ ∗
                 ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ exec_stutter (fun x' => Φ ((e1, σ2), x')) (x2 (e1, σ2)))) *))
        %I.
  Proof. rewrite /ERM/ERM' least_fixpoint_unfold //. Qed.

  Local Definition cfgO := prodO (exprO Λ) (stateO Λ).

  Lemma ERM_mono_grading e σ Z (x x' : nonnegreal) :
    x <= x' →
    ERM e σ x Z -∗ ERM e σ x' Z.
  Proof.
    iIntros (Hleq) "H_ub". iRevert (Hleq).
    rewrite /ERM /ERM'.
    set (Φ := (λ ρx : prodO cfgO _, ∀ (x'' : nonnegreal),
                    ((⌜(ρx.2 <= x'' )%R⌝ -∗ (bi_least_fixpoint (ERM_pre Z) (ρx.1, x''))))
              )%I : prodO cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n ((?&?)&?) ((?&?)&?) [ [[=] [=]] [=]]. by simplify_eq. }
    iPoseProof (least_fixpoint_ind (ERM_pre Z) Φ with "[]") as "H"; last first.
    { iApply ("H" with "H_ub"). }
    iIntros "!#" ([[? σ'] x'']). rewrite /ERM_pre.
    iIntros "(% & % & % & % & H) %x3 %Hleq' /="; simpl in Hleq'.
    - rewrite least_fixpoint_unfold.
      iExists _.
      repeat (iSplit; try done).
      iPureIntro. by etrans.
  Qed.

  Lemma ERM_strong_mono e1 σ1 Z1 Z2 (x x' : nonnegreal) :
    x <= x' →
    (∀ e2 σ2 x'', (⌜∃ σ, prim_step e1 σ (e2, σ2) > 0⌝ ∗ Z1 (e2, σ2) x'' -∗ Z2 (e2, σ2) x'')) -∗
    ERM e1 σ1 x Z1 -∗ ERM e1 σ1 x' Z2.
  Proof.
    iIntros (Hleq) "HZ H_ub".
    iApply ERM_mono_grading; [done|].
    iRevert "HZ".
    rewrite /ERM /ERM'.
    set (Φ := (λ ρx, (∀ e2 σ2 x'', ⌜∃ σ, (prim_step ρx.1.1 σ (e2, σ2) > 0)%R⌝ ∗ Z1 (e2, σ2) x'' -∗ Z2 (e2, σ2) x'') -∗
                  (bi_least_fixpoint (ERM_pre Z2) ρx ))%I : prodO cfgO _ → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter (ERM_pre Z1) Φ with "[]") as "H"; last first.
    { by iApply ("H" with "H_ub"). }
    iIntros "!#" ([[? σ'] x'']). rewrite /ERM_pre.
    iIntros "(% & % & % & % & H) HZ /=".
    rewrite least_fixpoint_unfold.
    iExists _.
    repeat (iSplit; [done|]).
    iIntros (? ? ?). iMod ("H" with "[//]").
    iModIntro.
    simpl.
    iApply "HZ". eauto.
  Qed.

  Lemma ERM_mono Z1 Z2 e1 σ1 x1 x2 :
    x1 <= x2 →
    (∀ ρ x, Z1 ρ x -∗ Z2 ρ x) -∗ ERM e1 σ1 x1 Z1 -∗ ERM e1 σ1 x2 Z2.
  Proof.
    iIntros "%Hleq HZ". iApply ERM_strong_mono; [done|].
    iIntros (???) "[_ ?]". by iApply "HZ".
  Qed.

  Lemma ERM_mono_pred Z1 Z2 e1 σ1 x :
    (∀ ρ x, Z1 ρ x -∗ Z2 ρ x) -∗ ERM e1 σ1 x Z1 -∗ ERM e1 σ1 x Z2.
  Proof.
    iIntros "HZ". iApply ERM_strong_mono; [done|].
    iIntros (???) "[_ ?]". by iApply "HZ".
  Qed.

  Lemma ERM_strengthen e1 σ1 Z ε :
    ERM e1 σ1 ε Z -∗
    ERM e1 σ1 ε (λ '(e2, σ2) ε', ⌜∃ σ, (prim_step e1 σ (e2, σ2) > 0)%R⌝ ∧ Z (e2, σ2) ε').
  Proof.
    iApply ERM_strong_mono; [lra|].
    iIntros (???) "[[% ?] ?]". iSplit; [|done]. by iExists _.
  Qed.

  Lemma ERM_bind `{!CostLanguageCtx costfun K} e1 σ1 Z x :
    to_val e1 = None →
    ERM e1 σ1 x (λ '(e2, σ2) x', Z (K e2, σ2) x') -∗ ERM (K e1) σ1 x Z.
  Proof.
    iIntros (Hv) "Hub".
    iAssert (⌜to_val e1 = None⌝)%I as "-#H"; [done|].
    iRevert "H".
    rewrite /ERM /ERM'.
    set (Φ := (λ ρx, ⌜to_val ρx.1.1 = None⌝ -∗
                     bi_least_fixpoint (ERM_pre Z) ((K ρx.1.1, ρx.1.2), ρx.2))%I
           : prodO cfgO _ → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter
                  (ERM_pre (λ '(e2, σ2) x', Z (K e2, σ2) x')) Φ
                 with "[]") as "H"; last first.
    { iIntros (?). iApply ("H" $! ((_, _), _) with "Hub [//]"). }
    iIntros "!#" ([[? σ'] x']). rewrite /ERM_pre.
    iIntros " (% & % & (%r & %Hr) & % & H) %Hv'".
    - rewrite least_fixpoint_unfold.
      simpl.
      (* TODO factor this madness into some lemma(s)... *)
      destruct (partial_inv_fun K) as (Kinv & HKinv).
      assert (∀ e e', Kinv e' = Some e -> K e = e') as HKinv1; [intros; by apply HKinv |].
      assert (∀ e e', Kinv e = None -> K e' ≠ e) as HKinv2; [intros; by apply HKinv |].
      assert (∀ e, Kinv (K e) = Some e) as HKinv3.
      { intro e.
        destruct (Kinv (K e)) eqn:H3.
        - apply HKinv1 in H3. f_equal. by apply fill_inj.
        - eapply (HKinv2 _ e) in H3. done. }
      set (x3 := (λ '(e,σ), from_option (λ e', X2 (e',σ)) nnreal_zero (Kinv e))).
      assert (∀ e2 σ2, x3 (K e2, σ2) = X2 (e2, σ2)) as Haux.
      { intros e2 σ2. rewrite /x3 HKinv3 //. }
      iExists x3.
      iSplit; [iPureIntro; by apply reducible_fill|].
      iSplit.
      { iPureIntro. exists r. intros (e&σ). rewrite /x3.
        destruct (Kinv e); simpl; try real_solver.
        etrans; [ | eapply (Hr (e, σ)); eauto]. apply cond_nonneg. }
      iSplit.
      + iPureIntro.
        (* TODO: factor this out into some lemma(s)... *)
        etrans; [| apply H1].
        rewrite cost_fill.
        apply Rplus_le_compat_l.
        transitivity (SeriesC (λ '(e,σ), (prim_step (K o) σ' (K e, σ) * x3 (K e, σ))%R));
          last first.
        { right. apply SeriesC_ext; intros [e σ].
          rewrite Haux. f_equal. rewrite -fill_step_prob //. }
        etrans; [| eapply (SeriesC_le_inj _ (λ '(e,σ), (Kinv e ≫= (λ e', Some (e',σ)))))].
        * apply SeriesC_le.
          -- intros (e & σ); simpl; split.
             ++ apply Rmult_le_pos; [done|]. apply cond_nonneg.
             ++ destruct (Kinv e) eqn:He; simpl.
                 ** rewrite (HKinv1 _ _ He) He /from_option //.
                 ** destruct (decide (prim_step (K o) σ' (e, σ) > 0)%R) as [Hgt | Hngt].
                    --- pose proof (fill_step_inv _ _ _ _ Hv' Hgt) as (e2' & (H3&?)).
                        by destruct (HKinv2 e e2' He).
                    ---  apply Rnot_gt_le in Hngt.
                         assert (prim_step (K o) σ' (e, σ) = 0%R); [by apply Rle_antisym | ].
                         lra.
          -- apply (ex_seriesC_le _ (λ '(e, σ), (prim_step (K o) σ' (e, σ) * x3 (e, σ))%R)).
             ++ intros (e & σ); simpl; split.
                ** destruct (Kinv e); simpl; try lra.
                   apply Rmult_le_pos; [done|]. apply cond_nonneg.
                ** destruct (Kinv e) eqn:He; simpl; try real_solver.
                   rewrite HKinv3 /= (HKinv1 _ _ He) //.
             ++ apply (ex_seriesC_le _ (λ ρ, ((prim_step (K o) σ' ρ ) * r)%R)); [ | apply ex_seriesC_scal_r; auto].
                intros (e&σ); split.
                ** apply Rmult_le_pos; [done|].
                   rewrite /x3. apply cond_nonneg.
                ** rewrite /x3. destruct (Kinv e); simpl; try real_solver.
                   apply Rmult_le_compat_l; [done|].
                   etrans; [|eapply (Hr (e, σ)); eauto]. apply cond_nonneg.
        * intros []. apply Rmult_le_pos; [done|]. apply cond_nonneg.
        * intros (e3&σ3) (e4&σ4) (e5&σ5) ? ?.
          destruct (Kinv e3) eqn:He3; destruct (Kinv e4) eqn:He4; simpl in *; simplify_eq.
          f_equal; auto.
          rewrite -(HKinv1 _ _ He3).
          by rewrite -(HKinv1 _ _ He4).
        * apply (ex_seriesC_le _ (λ '(e, σ), ((prim_step (K o) σ' (K e, σ)) * r)%R)).
          -- intros (e&σ); split.
             ++ apply Rmult_le_pos; [done|]. apply cond_nonneg.
             ++ rewrite /x3 HKinv3 /=. real_solver.
          -- apply (ex_seriesC_ext (λ ρ, ((prim_step o σ' ρ) * r)%R));
               [|by apply ex_seriesC_scal_r].
             intros []. apply Rmult_eq_compat_r.
             rewrite fill_step_prob //.
      + iIntros (? ? ?).
        opose proof (fill_step_inv _ _ _ _ _ H2); [done|].
        destruct H3 as [xx [Hxx xxprim]].
        rewrite Hxx Haux.
        by iMod ("H" with "[]").
  Qed.

  Lemma ERM_prim_step e1 σ1 Z x :
    (∃ x2, ⌜reducible (e1, σ1)⌝ ∗ ⌜0 <= x2⌝ ∗ ⌜cost e1 + x2 <= x⌝ ∗
           ∀ e2 σ2 , ⌜prim_step e1 σ1 (e2, σ2) > 0⌝%R ={∅}=∗ Z (e2, σ2) x2)
    ⊢ ERM e1 σ1 x Z.
  Proof.
    iIntros "(%x2&%&%&%&H)".
    rewrite ERM_unfold.
    iExists (λ _, x2).
    repeat iSplit; try done.
    - iExists x2. done.
    - iPureIntro. rewrite SeriesC_scal_r. rewrite prim_step_mass; last done. lra.
  Qed.

  Lemma ERM_adv_comp e1 σ1 Z x :
    (∃ (X2 : cfg Λ → nonnegreal),
        ⌜reducible (e1, σ1)⌝ ∗
        ⌜∀ ρ, 0 <= X2 ρ⌝ ∗
        ⌜∃ r, ∀ ρ, X2 ρ <= r⌝ ∗
        ⌜(cost e1 + SeriesC (λ ρ, prim_step e1 σ1 ρ * X2 ρ) <= x)%R⌝ ∗
        ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={∅}=∗ Z (e2, σ2) (X2 (e2, σ2)))
    ⊢ ERM e1 σ1 x Z.
  Proof.
    iIntros "(% & % & % & % & % & H)".
    rewrite {1}ERM_unfold.
    iExists _.
    repeat (iSplit; [done|]).
    eauto.
  Qed.

  Lemma ERM_strong_ind (Ψ : expr Λ → state Λ → nonnegreal → iProp Σ) Z :
    (∀ n e σ x, Proper (dist n) (Ψ e σ x)) →
    ⊢ (□ (∀ e σ x, ERM_pre Z (λ '((e, σ), x), Ψ e σ x ∧ ERM e σ x Z)%I ((e, σ), x) -∗ Ψ e σ x) →
       ∀ e σ x, ERM e σ x Z -∗ Ψ e σ x)%I.
  Proof.
    iIntros (HΨ). iIntros "#IH" (e σ x) "H".
    set (Ψ' := (λ '((e, σ), x), Ψ e σ x):
           (prodO (prodO (exprO Λ) (stateO Λ)) _) → iProp Σ).
    assert (NonExpansive Ψ').
    { intros n [[e1 σ1]?] [[e2 σ2]?]
        [[?%leibniz_equiv ?%leibniz_equiv]?%leibniz_equiv].
      simplify_eq/=. f_equiv. }
    rewrite /ERM/ERM'.
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iModIntro. iIntros ([[??]?]) "H". by iApply "IH".
  Qed.

End ERM.

(** * The weakest precondition  *)
Definition ert_wp_pre `{!ertwpG Λ Σ}
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 x1,
      state_interp σ1 ∗ etc_supply x1 ={E,∅}=∗
      ERM e1 σ1 x1 (λ '(e2, σ2) x2,
        ▷ |={∅,E}=> state_interp σ2 ∗ etc_supply x2 ∗ wp E e2 Φ)
end%I.

Local Instance wp_pre_contractive `{!ertwpG Λ Σ} : Contractive (ert_wp_pre).
Proof.
  rewrite /ert_wp_pre /= => n wp wp' Hwp E e1 Φ /=.
  do 7 (f_equiv).
  apply least_fixpoint_ne_outer; [|done].
  intros Ψ [[e' σ'] ε']. rewrite /ERM_pre.
  do 11 f_equiv.
  { f_contractive. do 3 f_equiv. apply Hwp. }
Qed.

Local Definition ert_wp_def `{!ertwpG Λ Σ} : Wp (iProp Σ) (expr Λ) (val Λ) () :=
  {| wp := λ _ : (), fixpoint (ert_wp_pre); wp_default := () |}.
Local Definition ert_wp_aux : seal (@ert_wp_def). Proof. by eexists. Qed.
Definition ert_wp' := ert_wp_aux.(unseal).
Global Arguments ert_wp' {Λ Σ _}.
Global Existing Instance ert_wp'.
Local Lemma ert_wp_unseal `{!ertwpG Λ Σ} : wp = (@ert_wp_def Λ Σ _).(wp).
Proof. rewrite -ert_wp_aux.(seal_eq) //. Qed.

Section ert_wp.
Context `{!ertwpG Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types ρ : cfg Λ.
Implicit Types x : R.

(* Weakest pre *)
Lemma ert_wp_unfold s E e Φ :
  WP e @ s; E {{ Φ }} ⊣⊢ ert_wp_pre (wp (PROP:=iProp Σ) s) E e Φ.
Proof. rewrite ert_wp_unseal. apply (fixpoint_unfold (ert_wp_pre)). Qed.

Global Instance ert_wp_ne s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !ert_wp_unfold /ert_wp_pre /=.
  do 7 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[]?]. rewrite /ERM_pre.
  do 11 f_equiv.
  (* rewrite /exec_stutter. *)
  (* do 10 f_equiv.  *)
  f_contractive_fin.
  rewrite IH; [done|lia|].
  intros ?. eapply dist_S, HΦ.
Qed.

Global Instance ert_wp_proper s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply ert_wp_ne=>v; apply equiv_dist.
Qed.
Global Instance ert_wp_contractive s E e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !ert_wp_unfold /ert_wp_pre He /=.
  do 6 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[]?]. rewrite /ERM_pre.
  do 11 f_equiv. f_contractive. do 6 f_equiv.
Qed.

Lemma ert_wp_value_fupd' s E Φ v : WP of_val v @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. rewrite ert_wp_unfold /ert_wp_pre to_of_val. auto. Qed.

Lemma ert_wp_strong_mono E1 E2 e Φ Ψ s :
  E1 ⊆ E2 →
  WP e @ s ; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s ; E2 {{ Ψ }}.
Proof.
  iIntros (HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
  rewrite !ert_wp_unfold /ert_wp_pre /=.
  destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1 x) "[Hσ Hx]".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "H".
  iApply (ERM_mono_pred with "[Hclose HΦ] H").
  iIntros ([e2 σ2]?) "H".
  iModIntro.
  iMod "H" as "(?&?& Hwp)". iFrame.
  iMod "Hclose" as "_". iModIntro.
  iApply ("IH" with "[] Hwp"); auto.
Qed.

Lemma fupd_ert_wp s E e Φ : (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite ert_wp_unfold /ert_wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
   iIntros (σ1 x) "Hi". iMod "H". by iApply "H".
Qed.
Lemma ert_wp_fupd s E e Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (ert_wp_strong_mono E with "H"); auto. Qed.

Lemma ert_wp_atomic E1 E2 e Φ `{!Atomic StronglyAtomic e} a :
  (|={E1,E2}=> WP e @ a; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ a; E1 {{ Φ }}.
Proof.
  iIntros "H".
  rewrite !ert_wp_unfold /ert_wp_pre.
  destruct (to_val e) as [v|] eqn:He; [by do 2 iMod "H"|].
  iIntros (σ1 x1) "(Hσ&Hx)".
  iSpecialize ("H" $! σ1 x1).
  iMod ("H" with "[Hσ Hx]") as "H"; [iFrame|].
  iMod "H"; iModIntro.
  iApply (ERM_strong_mono with "[] H"); [done|].
  iIntros (e2 σ2 x2) "([%σ' %Hstep]&H)".
  iNext.
  iMod "H" as "(Hσ&Hx&Hwp)".
  rewrite !ert_wp_unfold /ert_wp_pre.
  destruct (to_val e2) as [?|] eqn:He2.
  + iFrame. do 2 (iMod "Hwp"). by do 2 iModIntro.
  + iMod ("Hwp" $! _ _ with "[Hσ Hx]") as "Hwp"; [iFrame|].
    specialize (atomic _ _ _ Hstep) as []. congruence.
Qed.

Lemma ert_wp_step_fupd s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite !ert_wp_unfold /ert_wp_pre. iIntros (-> ?) "HR H".
  iIntros (σ1 x) "[Hσ Hx]". iMod "HR".
  iMod ("H" with "[$Hσ $Hx]") as "H".
  iModIntro.
  iApply (ERM_mono_pred with "[HR] H").
  iIntros ([e2 σ2] ?) "H".
  iModIntro.
  iMod "H" as "(Hσ & Hρ & H)".
  iMod "HR".
  iFrame "Hσ Hρ".
  iApply (ert_wp_strong_mono E2 with "H"); [done..|].
  iIntros "!>" (v) "H". by iApply "H".
Qed.

Lemma ert_wp_bind K `{!CostLanguageCtx costfun K} s E e Φ :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite ert_wp_unfold /ert_wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_ert_wp. }
  rewrite ert_wp_unfold /ert_wp_pre fill_not_val /=; [|done].
  iIntros (σ1 x) "[Hσ Hx]".
  iMod ("H" with "[$Hσ $Hx]") as "H".
  iModIntro.
  iApply ERM_bind; [done|].
  iApply (ERM_mono with "[] H"); [done|].
  iIntros ([e2 σ2] ?) "H".
  iModIntro.
  iMod "H" as "(Hσ & Hρ & H)".
  iModIntro.
  iFrame "Hσ Hρ". by iApply "IH".
Qed.

(** * Derived rules *)
Lemma ert_wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (ert_wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma ert_wp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (ert_wp_strong_mono with "H"); auto. Qed.
Global Instance ert_wp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply ert_wp_mono. Qed.
Global Instance ert_wp_flip_mono' s E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply ert_wp_mono. Qed.

Lemma ert_wp_value_fupd s E Φ e v : IntoVal e v → WP e @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. intros <-. by apply ert_wp_value_fupd'. Qed.
Lemma ert_wp_value' s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
Proof. rewrite ert_wp_value_fupd'. auto. Qed.
Lemma ert_wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. apply ert_wp_value'. Qed.

Lemma ert_wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (ert_wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma ert_wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (ert_wp_strong_mono with "H"); auto with iFrame. Qed.

Lemma ert_wp_frame_step_l s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (ert_wp_step_fupd with "Hu"); try done.
  iApply (ert_wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma ert_wp_frame_step_r s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  WP e @ s; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply ert_wp_frame_step_l.
Qed.
Lemma ert_wp_frame_step_l' s E e Φ R :
  TCEq (to_val e) None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (ert_wp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma ert_wp_frame_step_r' s E e Φ R :
  TCEq (to_val e) None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (ert_wp_frame_step_r s E E); try iFrame; eauto. Qed.

Lemma ert_wp_wand s E e Φ Ψ :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (ert_wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma ert_wp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (ert_wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e Φ Ψ :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (ert_wp_wand with "Hwp H"). Qed.
Lemma ert_wp_frame_wand s E e Φ R :
  R -∗ WP e @ s; E {{ v, R -∗ Φ v }} -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (ert_wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End ert_wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!ertwpG Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_ert_wp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite ert_wp_frame_l. apply ert_wp_mono, HR. Qed.

  Global Instance is_except_0_ert_wp s E e Φ : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_ert_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_ert_wp p s E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_ert_wp.
  Qed.

  Global Instance elim_modal_fupd_ert_wp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_ert_wp.
  Qed.

  Global Instance elim_modal_fupd_ert_wp_atomic p s E1 E2 e P Φ :
    ElimModal (Atomic StronglyAtomic e) p false
            (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?.
    by rewrite intuitionistically_if_elim
      fupd_frame_r wand_elim_r ert_wp_atomic.
  Qed.

  Global Instance add_modal_fupd_ert_wp s E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_ert_wp. Qed.

  Global Instance elim_acc_ert_wp_atomic {X} E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic StronglyAtomic e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; E1 {{ Φ }})
            (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (ert_wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_ert_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply ert_wp_fupd.
    iApply (ert_wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.
