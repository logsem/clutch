From clutch.prob_eff_lang.probblaze Require Import primitive_laws.
From iris.proofmode Require Import base proofmode.
From clutch.prob_eff_lang.probblaze Require Import syntax semantics notation class_instances logic.

(* Consider generalizing the PureExec construction *)
(* Definition prel `{Σ : gFunctors} (e1 e2 : expr) (Φ : val → val → iProp Σ) : iProp Σ := 
       ∃ (v1 v2 : val),
       ⌜rtc pure_step e1 v1⌝ ∗ ⌜rtc pure_step e2 v2⌝ ∗ Φ v1 v2. *)
  (* match (to_val e1), (to_val e2) with
     | Some v1, Some v2 => Φ v1 v2
     | Some v1, None => ∃ (v2 : val), (∃ n2, ⌜nsteps pure_step n2 e2 v2⌝) ∗ Φ v1 v2
     | None, Some v2 =>  ∃ (v1 : val), (∃ n1, ⌜nsteps pure_step n1 e1 v1⌝) ∗ Φ v1 v2
     | None, None => ∃ (v1 v2 : val) n1 n2,  ⌜nsteps pure_step n1 e1 v1 ∧ nsteps pure_step n2 e2 v2⌝ ∗ Φ v1 v2
     end.  *)

Definition prel_pre `{Σ : gFunctors} (Φ : val → val → iProp Σ)
    (R : (expr * expr) -d> iProp Σ) : (expr * expr) -d> iProp Σ :=
  λ ee, let (e1, e2) := ee in
  match to_val e1, to_val e2 with
  | Some v1, Some v2 => Φ v1 v2
  | Some v1, None    => (∀ e2', ⌜pure_step e2 e2'⌝ -∗ R ((Val v1), e2'))%I
  | None,    Some v2 => (∀ e1', ⌜pure_step e1 e1'⌝ -∗ R (e1', (Val v2)))%I
  | None,    None    => (∀ e1', ⌜pure_step e1 e1'⌝ -∗ R (e1', e2))%I
  end.

Local Lemma prel_pre_mono `{Σ : gFunctors} (wp1 wp2 : expr * expr → iProp Σ) Φ :
  ⊢ (□ ∀ ee, wp1 ee -∗ wp2 ee) →
    ∀ ee, prel_pre Φ wp1 ee -∗ prel_pre Φ wp2 ee.
Proof.
  iIntros "#H"; iIntros ((e1, e2)) "Hwp". rewrite /prel_pre.
  destruct (to_val e1), (to_val e2) as [v1 v2|]; first done; iIntros (e') "He'"; iApply "H"; by iApply "Hwp".
Qed.

Local Instance prel_pre_mono_pred `{Σ : gFunctors } Φ :
  BiMonoPred (@prel_pre Σ Φ).
Proof.
  constructor; last solve_proper.
  iIntros (wp1 wp2 ??) "#H". by iApply prel_pre_mono.
Qed.

Local Definition prel_def `{!probblazeRGS Σ}
    (e1 e2 : expr) (Φ : val → val → iProp Σ) : iProp Σ :=
  bi_least_fixpoint (prel_pre Φ) (e1, e2).
Local Definition prel_aux : seal (@prel_def). Proof. by eexists. Qed.
Definition prel := prel_aux.(unseal).
Global Arguments prel {Σ _}.
Local Lemma prel_unseal `{!probblazeRGS Σ} : prel = @prel_def Σ _.
Proof. rewrite -prel_aux.(seal_eq) //. Qed.

Notation "'PREL' e1 ≤ e2 '[{' Φ '}]'" := (prel e1%E e2%E Φ)
                                           (at level 20, e1, e2, Φ at next level, only parsing) : bi_scope.
Notation "'PREL' e1 ≤ e2 '[{' v1 ; v2 , Φ '}]'" := (prel e1%E e2%E (λ v1 v2, Φ)%I)
                                                   (at level 20, v1 ident, v2 ident, e1, e2, Φ at next level) : bi_scope.

Section prel.
  Context `{!probblazeRGS Σ}.

Lemma prel_unfold e1 e2 Φ :
  prel e1 e2 Φ ⊣⊢ prel_pre Φ (fun '(e1', e2') => prel e1' e2' Φ) (e1, e2).
Proof. by rewrite prel_unseal /prel /prel_def least_fixpoint_unfold. Qed.
Lemma prel_ind Φ `{NonExpansive Ψ} :
  □ (∀ e, prel_pre Φ (λ '(e1, e2), Ψ (e1, e2) ∧ PREL e1 ≤ e2 [{ v1; v2, Φ v1 v2 }]) e -∗ Ψ e) -∗
  (∀ e1 e2, PREL e1 ≤ e2 [{ v1; v2, Φ v1 v2 }] -∗ Ψ (e1, e2)). 
Proof.
  iIntros "#IH" (e1 e2) "H //=". rewrite prel_unseal.
  iApply (least_fixpoint_ind _ Ψ with "IH H").
Qed.

Lemma prel_intuitionistically e1 e2 Φ : 
  (□ prel e1 e2 Φ) -∗ prel e1 e2 (λ v1 v2, □ (Φ v1 v2)).
Proof.
  iIntros "#H". iAssert (PREL e1 ≤ e2 [{ v1; v2, Φ v1 v2 }])%I as "H'"; first done.
  iRevert "H H'". rewrite {1}bi.intuitionistically_elim. iRevert (e1 e2).
  iApply (@prel_ind _ (λ ee, □ PREL ee.1 ≤ ee.2 [{v1; v2, Φ v1 v2}] -∗ PREL ee.1 ≤ ee.2 [{v1; v2, (□ Φ v1 v2)}])%I).
  1 : solve_proper.
  iIntros ((e1, e2)) "!# IH #H //=".
  rewrite !prel_unfold /prel_pre.
  destruct (to_val e1) as [v1|]; destruct (to_val e2) as [v2|]; first done.
  all : iIntros (?) "#Hs"; iApply ("IH" with "[$]"); iModIntro; by iApply "H".
Qed. 

Notation "'PREL' e1 ≤ e2 '[{' Φ '}]'" := (prel e1%E e2%E Φ)
                                           (at level 20, e1, e2, Φ at next level, only parsing) : bi_scope.
Notation "'PREL' e1 ≤ e2 '[{' v1 ; v2 , Φ '}]'" := (prel e1%E e2%E (λ v1 v2, Φ)%I)
                                                   (at level 20, v1 ident, v2 ident, e1, e2, Φ at next level) : bi_scope.
Lemma pure_step_eq (e : expr) e1 e2 : pure_step e e1 → pure_step e e2 → e1 = e2.
Proof.
  intros He1 He2.
  inversion He1. inversion He2.
  simpl in *.
  eapply det_step_is_unique.
Admitted.


Lemma brel_step_r e1 e2 Φ :
  (∀ e2', ⌜pure_step e2 e2'⌝ -∗ brel ⊤ e1 e2' ⊥ Φ) -∗ brel ⊤ e1 e2 ⊥ Φ.
Proof.
  iIntros "Hstep".
  
Admitted.

Lemma prel_brel e1 e2 Φ :                         
  prel e1 e2 Φ -∗ brel ⊤ e1 e2 ⊥ Φ.
Proof. 
  iRevert (e1 e2).
  iApply (@prel_ind _ (λ e, brel ⊤ e.1 e.2 ⊥ Φ)).
  1 : solve_proper.
  iIntros ((e1,e2)) "!# IH //=".
  destruct (to_val e1) as [v1|] eqn:He1; destruct (to_val e2) as [v2|] eqn:He2.
  - apply of_to_val in He1 as <-. apply of_to_val in He2 as <-.
    iApply brel_value. by iIntros "$ !>".
  - apply of_to_val in He1 as <-. iApply brel_step_r. iIntros (?) "Hs". 
    iDestruct ("IH" with "Hs") as "($&_)".
    
  (* provable *)
  (* iIntros "(%&%&%He1&%He2&HΦ)". 
     apply rtc_nsteps in He1 as (n&He1).
     apply rtc_nsteps in He2 as (m&He2).
     destruct n, m. 
     - inversion He1. inversion He2. simplify_eq.
       iApply brel_value. by iIntros "$ !>".
     - inversion He1.
       iApply brel_pure_step_r; [by intros ?|done|]. 
       iApply brel_value. by iIntros "$ !>".
     - inversion He2.
       iApply brel_pure_step_later; [by intros ?|done|]. 
       iApply brel_value. by iIntros "!> !> $ !>".
     - iApply brel_pure_step_r; [by intros ?|done|]. 
       iApply brel_pure_step_later; [by intros ?|done|]. 
       iApply brel_value. by iIntros "!> !> $ !>". *)
Admitted.

Lemma prel_mono e1 e2 Φ Ψ : 
  (∀ v1 v2, Φ v1 v2 -∗ Ψ v1 v2) -∗
  PREL e1 ≤ e2 [{ v1; v2, Φ v1 v2}] -∗ prel e1 e2 Ψ.
Proof.
  iIntros "Hvv Hprel". 
  iRevert "Hvv". iRevert (e1 e2) "Hprel".
  iApply (@prel_ind _ (λ ee, (∀ v1 v2 : val, Φ v1 v2 -∗ Ψ v1 v2) -∗ PREL ee.1 ≤ ee.2 [{v1; v2, Ψ v1 v2}])%I).
  1: solve_proper.
  iIntros ((e1,e2)) "!# IH //= Hvv".
  rewrite !prel_unfold /prel_pre.
  destruct (to_val e1) as [v1|]; destruct (to_val e2) as [v2|]; first by iApply "Hvv".
  all : iIntros (?) "Hs"; iApply ("IH" with "[$][$]").
Qed.


(* (* pure_step is a partial function — uses pure_step_det + pmf_1_supp_eq *)
   Lemma pure_step_eq (e : expr) e1 e2 : pure_step e e1 → pure_step e e2 → e1 = e2.
   Admitted.
   
   (* the pure normal form of e is unique — induct on the first rtc;
      values can't step (reducible_not_val), so the other rtc must match step-for-step *)
   Lemma rtc_pure_step_val_det (e : expr) (v v' : val) :
     rtc pure_step e v → rtc pure_step e v' → v = v'.
   Admitted. *)

Global Instance pwp_persistent Φ e1 e2 :
  (∀ v1 v2, Persistent (Φ v1 v2)) → Persistent (PREL e1 ≤ e2 [{ v1;v2, Φ v1 v2 }]).
Proof.
  intros. rewrite prel_unseal.
  apply (least_fixpoint_persistent_absorbing _); simpl; try apply _.
  rewrite /prel_pre //=.
  intros ?? (e1', e2'). 
  destruct (to_val e1') as [v1|]; destruct (to_val e2') as [v2|]; first done.
  - apply bi.forall_persistent. intros x. apply wand_persistent; [apply pure_plain|done|].
Admitted.
  

Lemma prel_forall `{!Inhabited A} e1 e2 (Φ : A → val → val → iProp Σ) :
  (∀ x, PREL e1 ≤ e2 [{ (Φ x) }]) -∗ PREL e1 ≤ e2 [{ v1; v2, (∀ x, Φ x v1 v2) }].
Proof. 
  iIntros "Hprel".
  iAssert (PREL e1 ≤ e2 [{ v1; v2, True }])%I with "[#]" as "Hwp".
  { set (x := @inhabitant A _).
    iSpecialize ("Hprel" $! x). 
    iApply (prel_mono with "[][$Hprel]"); by iIntros (??) "_". }
  iRevert "Hwp Hprel".
  rewrite bi.intuitionistically_elim. iRevert (e1 e2).
  iApply (@prel_ind _ (λ ee, (∀ x : A, PREL ee.1 ≤ ee.2 [{v1; v2, Φ x v1 v2}]) -∗ PREL ee.1 ≤ ee.2 [{v1; v2, ∀ x : A, Φ x v1 v2}])%I). 
  1 : solve_proper.
  iIntros ((e1, e2)) "!> IH H //=". rewrite prel_unfold /prel_pre.
  destruct (to_val e1) as [v1|] eqn:He1; destruct (to_val e2) as [v2|] eqn:He2.
  - iIntros (?). iSpecialize ("H" $! x). by rewrite prel_unfold /prel_pre He1 He2.
  - iIntros (e2' He2'). apply of_to_val in He1 as <-. iApply "IH"; try done.
    iIntros (?). iSpecialize ("H" $! x). rewrite prel_unfold /prel_pre He2 //=.
    by iApply "H".
  - iIntros (e1' He1'). apply of_to_val in He2 as <-. iApply "IH"; try done.
    iIntros (?). iSpecialize ("H" $! x). rewrite prel_unfold /prel_pre He1 //=.
    by iApply "H".
  - iIntros (e1' He1'). iApply "IH"; try done.
    iIntros (?). iSpecialize ("H" $! x). rewrite prel_unfold /prel_pre He2 He1 //=.
    by iApply "H".
Qed. 

End prel.
