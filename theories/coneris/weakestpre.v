From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export fixpoint big_op.
From iris.prelude Require Import options.

From clutch.bi Require Export weakestpre.
From clutch.prelude Require Import stdpp_ext iris_ext NNRbar.
From clutch.prob Require Export couplings distribution graded_predicate_lifting.
From clutch.common Require Export con_language.

Import uPred.

Local Open Scope NNR_scope.

Class conerisWpGS (Λ : conLanguage) (Σ : gFunctors) := ConerisWpGS {
  conerisWpGS_invGS :: invGS_gen HasNoLc Σ;
  state_interp : state Λ → iProp Σ;
  fork_post: val Λ -> iProp Σ;
  err_interp : nonnegreal → iProp Σ;
}.
Global Opaque conerisWpGS_invGS.
Global Arguments ConerisWpGS {Λ Σ}.


Section glm.
  Context `{conerisWpGS Λ Σ}.
  Implicit Types ε : nonnegreal.

  (* Simple one without adv comp or state steps*)
  Definition glm_pre
    (Z : (expr Λ * state Λ * list (expr Λ)) -> nonnegreal -> iProp Σ) (Φ : partial_cfg Λ * nonnegreal -> iProp Σ) :=
    (λ (x : partial_cfg Λ * nonnegreal),
       let '((e1, σ1), ε) := x in
       (∃ R (ε1 ε2: nonnegreal),
           ⌜reducible e1 σ1⌝ ∗
           ⌜(ε1 + ε2 <= ε)%R⌝ ∗
           ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗
           (∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗
                        Z (e2, σ2, efs) ε2)
       )
    )%I.

  Canonical Structure NNRO := leibnizO nonnegreal.

  Local Instance exec_state_ub_pre_NonExpansive Z Φ :
    NonExpansive (glm_pre Z Φ).
  Proof.
    rewrite /glm_pre.
    intros n ((?&?)&?) ((?&?)&?) [ [[=] [=]] [=]].
    by simplify_eq.
  Qed.
  
  Local Instance exec_coupl_pre_mono Z : BiMonoPred (glm_pre Z).
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    rewrite /glm_pre.
    iIntros (((e1 & σ1) & ε)) "Hexec".
    done.
  Qed.

  
  Definition glm' Z := bi_least_fixpoint (glm_pre Z).
  Definition glm e σ ε Z := glm' Z ((e, σ), ε).

  Lemma glm_unfold (e1 : exprO Λ) (σ1 : stateO Λ) Z (ε : NNRO) :
    glm e1 σ1 ε Z ≡
      ((∃ R (ε1 : nonnegreal) (ε2 : nonnegreal),
           ⌜reducible e1 σ1⌝ ∗
           ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗
           ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗
           (∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗
                         Z (e2, σ2, efs) ε2)))%I.
  Proof.
    rewrite /glm/glm' least_fixpoint_unfold//.
  Qed.

  Local Definition partial_cfgO := (prodO (exprO Λ) (stateO Λ)).
  
  Lemma glm_mono_grading e σ Z ε ε' :
    ⌜(ε <= ε')%R⌝ -∗
    glm e σ ε Z -∗ glm e σ ε' Z.
  Proof.
    iIntros "Hleq H_ub". iRevert "Hleq".
    rewrite /glm /glm'.
    set (Φ := (λ x, ∀ (ε'' : nonnegreal), ((⌜(x.2 <= ε'' )%R⌝ -∗ (bi_least_fixpoint (glm_pre Z) (x.1, ε'')))))%I : prodO partial_cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n ((?&?)&?) ((?&?)&?) [ [[=] [=]] [=]]. by simplify_eq. }
    iPoseProof (least_fixpoint_ind (glm_pre Z) Φ with "[]") as "H"; last first.
    { iApply ("H" with "H_ub"). }
    iIntros "!#" ([[? σ'] ε'']). rewrite /glm_pre.
    iIntros "(% & % & % & % & % & % & H) %ε3 %Hleq' /="; simpl in Hleq'.
    rewrite least_fixpoint_unfold.
    iExists _,_,_.
    repeat iSplit; try done.
    iPureIntro; etrans; done.
  Qed.
  
  Lemma glm_strong_mono e1 σ1 Z1 Z2 ε ε' :
    ⌜(ε <= ε')%R⌝ -∗
    (∀ e2 σ2 ε'', (⌜∃ σ, (prim_step e1 σ (e2, σ2) > 0)%R⌝ ∗ Z1 (e2, σ2) ε'' -∗ Z2 (e2, σ2) ε'')) -∗
    glm e1 σ1 ε Z1 -∗ glm e1 σ1 ε' Z2.
  Proof.
    iIntros "%Hleq HZ H_ub".
    iApply glm_mono_grading; auto.
    iRevert "HZ".
    rewrite /glm /glm'.
    set (Φ := (λ x,(∀ e2 σ2 ε'', ⌜∃ σ, (prim_step x.1.1 σ (e2, σ2) > 0)%R⌝ ∗ Z1 (e2, σ2) ε'' -∗ Z2 (e2, σ2) ε'') -∗
                  (bi_least_fixpoint (glm_pre Z2) x ))%I : prodO partial_cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter (glm_pre Z1) Φ with "[]") as "H"; last first.
    { by iApply ("H" with "H_ub"). }
    iIntros "!#" ([[? σ'] ε'']). rewrite /glm_pre.
    iIntros "(% & % & % & % & % & % & H) HZ /=".
    rewrite least_fixpoint_unfold.
    iExists _,_,_.
    do 2 (iSplit; first done).
    iSplit; first (iPureIntro; by apply pgl_pos_R).
    iIntros (???[??]).
    iMod ("H" with "[//]").
    iModIntro.
    iApply "HZ". iFrame.
    iPureIntro. naive_solver.
  Qed.

  Lemma glm_mono Z1 Z2 e1 σ1 ε1 ε2 :
    ⌜(ε1 <= ε2)%R⌝ -∗ (∀ ρ ε, Z1 ρ ε -∗ Z2 ρ ε) -∗ glm e1 σ1 ε1 Z1 -∗ glm e1 σ1 ε2 Z2.
  Proof.
    iIntros "%Hleq HZ". iApply glm_strong_mono; auto.
    iIntros (???) "[_ ?]". by iApply "HZ".
  Qed.

  Lemma glm_mono_pred Z1 Z2 e1 σ1 ε :
    (∀ ρ ε, Z1 ρ ε -∗ Z2 ρ ε) -∗ glm e1 σ1 ε Z1 -∗ glm e1 σ1 ε Z2.
  Proof.
    iIntros "HZ". iApply glm_strong_mono; auto.
    iIntros (???) "[_ ?]". by iApply "HZ".
  Qed.

  Lemma glm_strengthen e1 σ1 Z ε :
    glm e1 σ1 ε Z -∗
    glm e1 σ1 ε (λ '(e2, σ2) ε', ⌜∃ σ, (prim_step e1 σ (e2, σ2) > 0)%R⌝ ∧ Z (e2, σ2) ε').
  Proof.
    iApply glm_strong_mono; [iPureIntro; lra | ].
    iIntros (???) "[[% ?] ?]". iSplit; [|done]. by iExists _.
  Qed.


  Lemma glm_bind K `{!ConLanguageCtx K} e1 σ1 Z ε :
    to_val e1 = None →
    glm e1 σ1 ε (λ '(e2, σ2, efs) ε', Z (K e2, σ2, efs) ε') -∗ glm (K e1) σ1 ε Z.
  Proof.
    iIntros (Hv) "Hub".
    iAssert (⌜to_val e1 = None⌝)%I as "-#H"; [done|].
    iRevert "H".
    rewrite /glm /glm'.
    set (Φ := (λ x, ⌜to_val x.1.1 = None⌝ -∗
                     bi_least_fixpoint (glm_pre Z) ((K x.1.1, x.1.2), x.2))%I
           : prodO partial_cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros n ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    iPoseProof (least_fixpoint_iter
                  (glm_pre (λ '(e2, σ2, efs) ε', Z (K e2, σ2, efs) ε')) Φ
                 with "[]") as "H"; last first.
    { iIntros (?). iApply ("H" $! ((_, _), _) with "Hub [//]"). }
    iIntros "!#" ([[? σ'] ε']). rewrite /glm_pre.
    iIntros " (% & % & % & % & % & % & H) %Hv'".
    rewrite least_fixpoint_unfold.
    destruct (partial_inv_fun K) as (Kinv & HKinv).
    assert (forall e e', Kinv e' = Some e -> K e = e') as HKinv1; [intros; by apply HKinv |].
    assert (forall e e', Kinv e = None -> K e' ≠ e) as HKinv2; [intros; by apply HKinv |].
    assert (forall e, Kinv (K e) = Some e) as HKinv3.
    { intro e.
      destruct (Kinv (K e)) eqn:H4.
      - apply HKinv1 in H4. f_equal. by apply fill_inj.
      - eapply (HKinv2 _ e) in H4. done. }
    iExists (λ '(e2, σ2, efs), ∃ e2', e2 = K e2' ∧ R2 (e2', σ2, efs)),_,ε2.
    iSplit; [iPureIntro; by apply reducible_fill|].
    iSplit; [ | iSplit].
    2:{ iPureIntro.
        rewrite <- Rplus_0_r.
        rewrite fill_dmap //=.
        eapply (pgl_dbind _ _ R2).
        - eapply pgl_nonneg_grad; eauto.
        - lra.
        - intros [[]] ? =>/=.
          apply pgl_dret.
          eauto.
        - auto.
    }
    + done.
    + iIntros (???[?[->?]]). iApply "H".
      done.
  Qed.

  Lemma glm_prim_step e1 σ1 Z ε :
    (∃ R ε1 ε2, ⌜reducible e1 σ1⌝ ∗ ⌜ (ε1 + ε2 <= ε)%R ⌝ ∗ ⌜pgl (prim_step e1 σ1) R ε1⌝ ∗
          ∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗ Z (e2, σ2, efs) ε2)
    ⊢ glm e1 σ1 ε Z.
  Proof.
    iIntros "(%R&%ε1&%ε2&%&%&%&H)".
    rewrite glm_unfold.
    iExists R, ε1, ε2.
    by repeat iSplit.
  Qed. 

  Lemma glm_strong_ind (Ψ : expr Λ → state Λ → nonnegreal → iProp Σ) Z :
    (∀ n e σ ε, Proper (dist n) (Ψ e σ ε)) →
    ⊢ (□ (∀ e σ ε, glm_pre Z (λ '((e, σ), ε), Ψ e σ ε ∧ glm e σ ε Z)%I ((e, σ), ε) -∗ Ψ e σ ε) →
       ∀ e σ ε, glm e σ ε Z -∗ Ψ e σ ε)%I.
  Proof.
    iIntros (HΨ). iIntros "#IH" (e σ ε) "H".
    set (Ψ' := (λ '((e, σ), ε), Ψ e σ ε):
           (prodO (prodO (exprO Λ) (stateO Λ)) NNRO) → iProp Σ).
    assert (NonExpansive Ψ').
    { intros n [[e1 σ1]?] [[e2 σ2]?]
        [[?%leibniz_equiv ?%leibniz_equiv]?%leibniz_equiv].
      simplify_eq/=. f_equiv. }
    rewrite /glm/glm'.
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iModIntro. iIntros ([[??]?]) "H". by iApply "IH".
  Qed. 
    
End glm.

(** * The weakest precondition *)

Definition pgl_wp_pre `{!conerisWpGS Λ Σ}
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ :=
  (λ E e1 Φ,
     match to_val e1 with
     | Some v => |={E}=>Φ v
     | None => ∀ σ1 ε1,
     state_interp σ1 ∗ err_interp ε1 ={E, ∅}=∗
     glm e1 σ1 ε1
       (λ '(e2, σ2, efs) (ε2: nonnegreal),  ▷|={∅,E}=> 
          state_interp σ2 ∗  err_interp ε2 ∗ wp E e2 Φ ∗
          [∗ list] ef ∈efs, wp ⊤ ef fork_post
       )
     end
  )%I.


Local Instance wp_pre_contractive `{!conerisWpGS Λ Σ} : Contractive (pgl_wp_pre).
Proof.
  rewrite /pgl_wp_pre /= => n wp wp' Hwp E e1 Φ /=.
  do 7 (f_equiv).
  apply least_fixpoint_ne_outer; [|done].
  intros Ψ [[e' σ'] ε']. rewrite /glm_pre.
  do 17 f_equiv.
  f_contractive.
  repeat f_equiv; apply Hwp.
Qed.

(* TODO: get rid of stuckness in notation [iris/bi/weakestpre.v] so that we don't have to do this *)
Local Definition pgl_wp_def `{!conerisWpGS Λ Σ} : Wp (iProp Σ) (expr Λ) (val Λ) () :=
  {| wp := λ _ : (), fixpoint (pgl_wp_pre); wp_default := () |}.
Local Definition pgl_wp_aux : seal (@pgl_wp_def). Proof. by eexists. Qed.
Definition pgl_wp' := pgl_wp_aux.(unseal).
Global Arguments pgl_wp' {Λ Σ _}.
Global Existing Instance pgl_wp'.
Local Lemma pgl_wp_unseal `{!conerisWpGS Λ Σ} : wp = (@pgl_wp_def Λ Σ _).(wp).
Proof. rewrite -pgl_wp_aux.(seal_eq) //. Qed.

