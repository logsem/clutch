(* shallow_handler.v *)

(* This theory introduces a novel reasoning rule for shallow handlers. *)

From iris.proofmode      Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop.
(* From iris.program_logic  Require Import weakestpre. *)

(* From lib   Require Import base. *)
From clutch.approxis Require Import app_weakestpre.
From clutch.prob_eff_lang.hazel_prob Require Import notation weakestpre protocol_agreement
                                         iEff primitive_laws lang spec_ra. (* probeffGS is imported from adequacy *)
(* From logic Require Export heap. *)

Section shallow_handler.
 Context `{!probeffGS Σ}.

(** * Shallow Handlers. *)

(* Return clause judgement. *)

Definition shallow_return_handler E r Ψ' Φ Φ' :=
  (∀ v, Φ v -∗ ▷ EWP (App r (Val v)) @ E <| Ψ' |> {{ Φ' }})%I.
Arguments shallow_return_handler _ _%_E _%_ieff _%_I _%_I.

(* Global Instance shallow_return_handler_ne E r n :
     Proper
       ((dist n) ==> (dist n) ==> (dist n) ==> (dist n))
     (shallow_return_handler E r).
   Proof.
     intros ?????????. rewrite /shallow_return_handler.
     f_equiv=>v. f_equiv. done. by solve_proper.
   Qed.
   Global Instance is_shallow_return_proper E h :
     Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (shallow_return_handler E h).
   Proof.
     intros ?????????. apply equiv_dist=>n;
     apply shallow_return_handler_ne; by apply equiv_dist.
   Qed. *)

(* Effect clause judgement. *)

Definition shallow_effect_handler E h Ψ_eff Ψ Ψ' (Φ Φ' : _ -d> _) :=
  (∀ v k,
    protocol_agreement v Ψ_eff (λ w,
        EWP App (Val k) (Val w) @ E <| Ψ |> {{ Φ }}) -∗
    ▷ EWP App (App h (Val v)) (Val k) @ E <| Ψ' |> {{ Φ' }})%I.
Arguments shallow_effect_handler _ _%_E _%_ieff _%_ieff _%_ieff _%_I _%_I.

(* Global Instance shallow_effect_handler_ne E h n :
     Proper
       ((dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n))
     (shallow_effect_handler E h).
   Proof.
     intros ??? ??? ??? ??? ???. rewrite /shallow_effect_handler /protocol_agreement.
     by repeat (apply H || solve_proper || f_equiv).
   Qed.
   Global Instance is_shallow_handler_proper E h :
     Proper
       ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡))
     (shallow_effect_handler E h).
   Proof.
     intros ??? ??? ??? ??? ???. apply equiv_dist=>n;
     apply shallow_effect_handler_ne; by apply equiv_dist.
   Qed. *)

Lemma shallow_effect_handler_bottom E h Ψ Ψ' Φ Φ' :
  ⊢ shallow_effect_handler E h ⊥ Ψ Ψ' Φ Φ'.
Proof. iIntros (v k) "H". by rewrite protocol_agreement_bottom. Qed.

(* Lemma shallow_effect_handler_marker_elim E f h Ψ_eff Ψ Ψ' Φ Φ' :
     shallow_effect_handler E h (f #> Ψ_eff) Ψ Ψ' Φ Φ' ⊢
       (∀ v k,
         protocol_agreement v Ψ_eff (λ w,
             EWP App (Val k) (Val w) @ E <| Ψ |> {{ Φ }}) -∗
         ▷ EWP App (App h (Val (f v))) (Val k) @ E <| Ψ' |> {{ Φ' }}).
   Proof.
     iIntros "Hewp" (v k) "Hprot_agr".
     iApply "Hewp". by iApply protocol_agreement_marker_intro.
   Qed.
   
   Lemma shallow_effect_handler_marker_intro E f {Hf: Marker f} h Ψ_eff Ψ Ψ' Φ Φ' :
     (∀ v k,
       protocol_agreement v Ψ_eff (λ w,
           EWP App (Val k) (Val w) @ E <| Ψ |> {{ Φ }}) -∗
       ▷ EWP App (App h (Val (f v))) (Val k) @ E <| Ψ' |> {{ Φ' }}) ⊢
       shallow_effect_handler E h (f #> Ψ_eff) Ψ Ψ' Φ Φ'.
   Proof.
     iIntros "Hewp" (v k) "Hprot_agr".
     case (marker_dec_range v) as [(w & Hw)|Hv].
     { inversion Hw. iApply "Hewp".
       by iApply (@protocol_agreement_marker_elim _ f marker_inj). }
     { iNext. iDestruct "Hprot_agr" as (Q) "[HP _]".
       rewrite iEff_marker_eq. iDestruct "HP" as (w) "[-> _]". by case (Hv w). }
   Qed.
   
   Lemma shallow_effect_handler_sum_intro E h Ψ1 Ψ2 Ψ Ψ' Φ Φ' :
     ((shallow_effect_handler E h Ψ1 Ψ Ψ' Φ Φ') ∧
      (shallow_effect_handler E h Ψ2 Ψ Ψ' Φ Φ')) ⊢
        shallow_effect_handler E h (Ψ1 <+> Ψ2) Ψ Ψ' Φ Φ'.
   Proof.
     iIntros "Hhandler" (v k) "Hprot_agr".
     iDestruct (protocol_agreement_sum_elim with "Hprot_agr") as "[H|H]".
     { iDestruct "Hhandler" as "[Hhandler _]"; by iApply "Hhandler". }
     { iDestruct "Hhandler" as "[_ Hhandler]"; by iApply "Hhandler". }
   Qed.
   
   Lemma shallow_effect_handler_sum_elim E h Ψ1 Ψ2 Ψ Ψ' Φ Φ' :
     shallow_effect_handler E h (Ψ1 <+> Ψ2) Ψ Ψ' Φ Φ' ⊢
       (shallow_effect_handler E h Ψ1 Ψ Ψ' Φ Φ') ∧
       (shallow_effect_handler E h Ψ2 Ψ Ψ' Φ Φ').
   Proof.
     iIntros "Hhandler". iSplit; iIntros (v k) "Hprot_agr"; iApply "Hhandler".
     { by iApply protocol_agreement_sum_intro_l. }
     { by iApply protocol_agreement_sum_intro_r. }
   Qed. *)

(* Lemma shallow_effect_handler_strong_mono
     E h Ψ1_eff Ψ2_eff Ψ1 Ψ2 Ψ' Φ1 Φ2 Φ' :
      (shallow_effect_handler E h Ψ2_eff Ψ2 Ψ' Φ2 Φ' -∗
         Ψ1_eff ⊑ Ψ2_eff -∗ Ψ1 ⊑ Ψ2 -∗ □ (∀ v, Φ1 v ={E}=∗ Φ2 v) -∗
       shallow_effect_handler E h Ψ1_eff Ψ1 Ψ' Φ1 Φ')%ieff.
   Proof.
     iIntros "Hhandler #HΨ_eff #HΨ #HΦ". iIntros (v k) "Hp".
     iAssert (protocol_agreement v Ψ2_eff (λ w,
                 EWP App (Val k) (Val w) @ E <|Ψ2|> {{Φ2}}))%I
     with "[HΦ Hp]" as "Hp".
     { iApply (protocol_agreement_strong_mono with "Hp"); try auto.
       iIntros "!>" (w) "Hewp". iApply (ewp_strong_mono with "Hewp"); by auto. }
     iSpecialize ("Hhandler" with "Hp"). iNext.
     iApply (ewp_strong_mono with "Hhandler"); try auto.
     by iApply iEff_le_refl.
   Qed. *)


(* Shallow handler judgement. *)

Definition shallow_handler E h r Ψ_eff Ψ Ψ' (Φ Φ' : _ -d> _) : iProp Σ :=
  (shallow_return_handler E   r         Ψ' Φ Φ') ∧
  (shallow_effect_handler E h   Ψ_eff Ψ Ψ' Φ Φ').
Arguments shallow_handler _ _%_E _%_E _%_ieff _%_ieff _%_ieff _%_I _%_I.

Global Instance shallow_handler_ne E h r n :
  Proper
    ((dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n))
  (shallow_handler E h r).
Proof.
  intros ??? ??? ??? ??? ???. rewrite /shallow_handler.
  f_equiv; try solve_proper. Admitted. (* by apply shallow_effect_handler_ne.
   Qed. *)
Global Instance shallow_handler_proper E h r :
  Proper
    ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡))
  (shallow_handler E h r).
Proof.
  intros ??? ??? ??? ??? ???.
  apply equiv_dist=>n. apply shallow_handler_ne; apply equiv_dist; done.
Qed.

(* Reasoning rule for [TryWith]: a shallow single-effect handler. *)

Lemma pure_prim_step_try_with_eff v k e₂ e₃ :
  pure_prim_step (TryWith (Eff v k) e₂ e₃) (App e₂ (Val v) (Cont k)).
Proof.
  apply Build_pure_prim_step.
  - intros ?. eexists. simpl. apply head_step_prim_step.
    apply head_step_support_equiv_rel. by apply TryWithEffS.
  - intros ?. unfold prim_step. simpl.
    rewrite fill_lift_empty. rewrite dmap_dret.
    apply dret_1_1. done.
Qed.

(* TODO: Move to lang.v *)
Lemma pure_prim_step_cont k w :
  pure_prim_step (App (Cont k) (Val w)) (fill k w).
Proof.
  apply Build_pure_prim_step.
  - intros ?. eexists. simpl. apply head_step_prim_step.
    apply head_step_support_equiv_rel. by apply ContS.
  -intros ?. unfold prim_step. simpl.
   rewrite fill_lift_empty. rewrite dmap_dret. by apply dret_1_1.
Qed.

Lemma pure_prim_step_try_with_val v e₂ e₃ :
  pure_prim_step (TryWith (Val v) e₂ e₃) (App e₃ (Val v)).
Proof.
  apply Build_pure_prim_step.
  - intros ?. eexists. apply head_step_prim_step.
    apply head_step_support_equiv_rel. by apply TryWithRetS.
  - intros ?. unfold prim_step. simpl. rewrite fill_lift_empty.
    rewrite dmap_dret. by apply dret_1_1.
Qed.

Lemma ewp_try_with E Ψ Ψ' Φ Φ' e h r :
  EWP          e      @ E <| Ψ  |> {{ Φ  }} -∗ shallow_handler E h r Ψ Ψ Ψ' Φ Φ' -∗
  EWP (TryWith e h r) @ E <| Ψ' |> {{ Φ' }}.
Proof.
  iLöb as "IH" forall (e Ψ).
  destruct (to_val e) as [ v    |] eqn:He; [|
  destruct (to_eff e) as [(v, k)|] eqn:He' ].
  - iIntros "HΦ [Hr _]".
    rewrite <-(of_to_val _ _ He).
    iApply fupd_ewp.
    iApply ewp_pure_step'. { apply pure_prim_step_try_with_val. }
    iApply "Hr".
    rewrite ewp_unfold /ewp_pre. simpl.
    admit.
  - rewrite <-(of_to_eff _ _ _ He').
    iIntros "H Hhandler".
    iDestruct "Hhandler" as "[_ Hh]".
    iApply ewp_pure_step'; [apply pure_prim_step_try_with_eff|].
    iSpecialize ("Hh" $! v (Cont k) with "[H]"). { admit. }
    (* { iApply (protocol_agreement_mono with "H").
         iIntros "!>" (w) "Hk".
         iApply ewp_pure_step'; [apply pure_prim_step_cont|].
         by iApply "Hk".
       } *)
    by iApply "Hh".
  - iIntros "He Hhandler".
    rewrite !ewp_unfold /ewp_pre He He'. simpl.
    iIntros (σ1 e1' σ1' ε1) "((?&?)&?&?)".
    iMod ("He" $! σ1 e1' σ1' ε1 with "[$]") as "He".
    iModIntro.
    iApply (spec_coupl_mono with "[][He]"); [done| |done].
    iIntros (????) "Hprog".
    iApply prog_coupl_mono. 
Admitted.
(*     iSplitR.
       + iPureIntro. revert H; unfold reducible. simpl.
         rewrite /prim_step'; simpl.
         destruct 1 as [obs [e₄ [σ₄ [efs Hstep]]]].
         case obs in Hstep; [|done].
         case efs in Hstep; [|done].
         inversion Hstep. simplify_eq.
         exists [], (TryWith (fill K e2') h r), σ₄, [].
         by apply (Ectx_prim_step _ _ _ _ (ConsCtx (TryWithCtx h r) K) e1' e2').
       + iModIntro. iIntros (e₄ σ₄) "%".
         destruct k; [|done]. rename H0 into Hstep. simpl in Hstep.
         assert (Hstep' : ∃ e₅, prim_step e σ₁ e₅ σ₄ ∧ e₄ = TryWith e₅ h r).
         { inversion Hstep. destruct K as [|Ki K].
           - simpl in H; simplify_eq. inversion H2; naive_solver.
           - destruct Ki; try naive_solver. simpl in H0, H1, H2; simplify_eq.
             exists (fill K e2'). simpl. split;[| done].
             by apply (Ectx_prim_step _ _ _ _ K e1' e2').
         }
         destruct Hstep' as [e₅ [Hstep' ->]].
         iDestruct ("He" $! e₅ σ₄ Hstep') as "> He".
         iIntros "!> !>". iMod "He". iModIntro.
         iMod "He" as "[$ He]". iModIntro.
         by iApply ("IH" with "He Hhandler").
   Qed. *)

End shallow_handler.
