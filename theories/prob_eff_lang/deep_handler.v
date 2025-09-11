(* deep_handler.v

   Here, we define a deep effect handler as a program of
   the language [eff_lang] which only provides shallow
   handlers as a primitive construct for catching effects.

   We also introduce the proposition [deep_handler] for stating
   the correctness of a handler implementation.

*)

From stdpp                 Require Import list.
From iris.proofmode        Require Import base tactics classes.
(* From iris.program_logic    Require Import weakestpre. *)
From clutch.prob_eff_lang  Require Import notation weakestpre lang primitive_laws iEff shallow_handler protocol_agreement lang.


(** * Deep Handler. *)

(* Program definition. *)

Definition deep_try_with : val := rec: "deep_try_with" "e" "h" "r" :=
  TryWith ("e" #())
  (* effect: *) (λ: "v" "k",
                  ("h" "v" (λ: "w",
                     "deep_try_with" (λ: <>, "k" "w") "h" "r")))
  (* return: *) "r".


(** * Reasoning Rules. *)

Section deep_handler.
Context `{!probeffGS Σ}.

(* Deep handler judgment. *)

Definition deep_handler_pre :
  (coPset -d> expr -d> expr -d> _ -d> iEff Σ -d> _ -d> (val -d> iPropO Σ) -d> iPropO Σ) →
  (coPset -d> expr -d> expr -d> _ -d> iEff Σ -d> _ -d> (val -d> iPropO Σ) -d> iPropO Σ)
  := λ deep_handler E h r Ψ Ψ' Φ Φ',
  ((shallow_return_handler E r Ψ' Φ Φ') ∧
   (∀ v k,
     protocol_agreement v Ψ (λ w, ∀ Ψ'' Φ'',
       ( ▷ deep_handler E h r Ψ Ψ'' Φ Φ'' -∗
         EWP (Val k) (Val w) @ E <| Ψ'' |> {{ Φ'' }})) -∗
     ▷ EWP App (App h (Val v)) (Val k) @ E <| Ψ' |> {{ Φ' }}))%I.
Arguments deep_handler_pre _ _%_E _%_E _%_ieff _%_ieff _%_I _%_I.

Local Instance deep_handler_pre_contractive : Contractive deep_handler_pre.
Proof.
  rewrite /deep_handler_pre => n handler handler' Hhandler E h r Ψ Ψ' Φ Φ'.
  repeat (f_contractive || f_equiv). intros ?; simpl.
  repeat (f_contractive || f_equiv). apply Hhandler.
Qed.
Definition deep_handler_def := fixpoint deep_handler_pre.
Definition deep_handler_aux : seal deep_handler_def. Proof. by eexists. Qed.
Definition deep_handler := deep_handler_aux.(unseal).
Definition deep_handler_eq : deep_handler = deep_handler_def
  := deep_handler_aux.(seal_eq).
Arguments deep_handler _ _%_E _%_E _%_ieff _%_ieff _%_I _%_I.

Global Lemma deep_handler_unfold E h r Ψ Ψ' Φ Φ' :
  deep_handler E h r Ψ Ψ' Φ Φ' ⊣⊢
  deep_handler_pre deep_handler E h r Ψ Ψ' Φ Φ'.
Proof.
  rewrite deep_handler_eq /deep_handler_def.
  by apply (fixpoint_unfold deep_handler_pre).
Qed.

(* Global Instance deep_handler_ne E h r n :
     Proper
       ((dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n)) (* no Dist (val → iPropI Σ) *)
     (deep_handler E h r).
   Proof.
     induction (lt_wf n) as [n _ IH]=> Ψ1 Ψ2 HΨ Ψ'1 Ψ'2 HΨ' Φ1 Φ2 HΦ Φ'1 Φ'2 HΦ'.
     rewrite !deep_handler_unfold /deep_handler_pre.
     repeat (apply protocol_agreement_ne||apply ewp_ne||f_contractive||f_equiv);
     try done; try (eapply dist_le; eauto with lia).
     intros ?. do 2 (f_equiv=>?). f_equiv. f_contractive.
     apply IH; try lia; eapply dist_le; eauto with lia.
   Qed.
   Global Instance deep_handler_proper E h r :
     Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡)) (deep_handler E h r).
   Proof.
     intros ??? ??? ??? ???.
     apply equiv_dist=>n. apply deep_handler_ne; apply equiv_dist; done.
   Qed. *)

(* Lemma deep_handler_sum_elim_l E h r Ψ1 Ψ2 Ψ' Φ Φ' :
     deep_handler E h r (Ψ1 <+> Ψ2) Ψ' Φ Φ' ⊢ deep_handler E h r Ψ1 Ψ' Φ Φ'.
   Proof.
     iLöb as "IH" forall (Ψ' Φ'). iIntros "Hhandler".
     rewrite !deep_handler_unfold.
     iSplit; [by iDestruct "Hhandler" as "[$ _]"|].
     iIntros (v k) "Hprot_agr". iApply "Hhandler".
     iApply (protocol_agreement_strong_mono with "Hprot_agr"); try done.
     - by iApply iEff_le_sum_l.
     - iIntros "!>" (w) "Hhandler".
       iIntros (Ψ'' Φ'') "Hhandler'". iApply "Hhandler". by iApply "IH".
   Qed.
   
   Lemma deep_handler_sum_elim_r E h r Ψ1 Ψ2 Ψ' Φ Φ' :
     deep_handler E h r (Ψ1 <+> Ψ2) Ψ' Φ Φ' ⊢ deep_handler E h r Ψ2 Ψ' Φ Φ'.
   Proof. rewrite iEff_sum_comm. by iApply deep_handler_sum_elim_l. Qed.
   
   Lemma deep_handler_sum_elim E (f g : val → val) h r Ψ1 Ψ2 Ψ' Φ Φ' :
     deep_handler E h r (Ψ1 <+> Ψ2) Ψ' Φ Φ' ⊢
       ((deep_handler E h r Ψ1 Ψ' Φ Φ') ∧
        (deep_handler E h r Ψ2 Ψ' Φ Φ'))%I.
   Proof.
     iIntros "Hhandler". iSplit.
     { by iApply deep_handler_sum_elim_l. }
     { by iApply deep_handler_sum_elim_r. }
   Qed. *)

(* Deep handler reasoning rule. *)

Lemma ewp_deep_try_with E Ψ Ψ' Φ Φ' (e : expr) (h r : val) :
  EWP e @ E <| Ψ |> {{ Φ }} -∗ deep_handler E h r Ψ Ψ' Φ Φ' -∗
  EWP (deep_try_with (λ: <>, e) h r) @ E <| Ψ' |> {{ Φ' }}.
Proof.
  iLöb as "IH" forall (Ψ Ψ' Φ Φ' e).
  unfold deep_try_with.
  iIntros "He Hhandler".
  iApply (ewp_bind ([AppLCtx _])).
  iApply (ewp_bind ([AppLCtx _])).
  iApply (ewp_bind ([AppRCtx _])).
  iApply ewp_pure_step; [apply pure_prim_step_rec|].
  iApply ewp_value_fupd'. iModIntro. simpl.
  iApply ewp_pure_step; [apply pure_prim_step_beta|]. simpl.
  iApply ewp_pure_step; [apply pure_prim_step_rec|]. simpl.
  iApply ewp_value_fupd'. iModIntro.
  iApply ewp_pure_step; [apply pure_prim_step_beta|].
  iApply ewp_pure_step; [apply pure_prim_step_rec|]. simpl.
  iApply ewp_value_fupd'. iModIntro.
  iApply ewp_pure_step; [apply pure_prim_step_beta|]. simpl.
  iApply (ewp_try_with with "[He] [Hhandler]").
  + iApply ewp_pure_step; [apply pure_prim_step_beta| ]. simpl.
    iApply "He".
  + rewrite deep_handler_unfold.
    iSplit; [ by iDestruct "Hhandler" as "[$ _]" |].
    iDestruct "Hhandler" as "[_ H]".
    iIntros (v k) "H'".
    iApply (ewp_bind [AppLCtx _]).
    iApply (ewp_bind [AppLCtx _]).
    iApply ewp_pure_step; [apply pure_prim_step_rec|].
    iApply ewp_value_fupd'; iNext; iModIntro.
    iApply ewp_pure_step; [apply pure_prim_step_beta|]. simpl.
    iApply ewp_pure_step; [apply pure_prim_step_rec|].
    iApply ewp_value_fupd'; iModIntro.
    iApply ewp_pure_step; [apply pure_prim_step_beta|]. simpl.
    iApply ewp_pure_step'.
    { apply (pure_prim_step_fill [AppRCtx (h v)]). apply pure_prim_step_rec. }
    simpl.
    iApply "H".
    iApply (protocol_agreement_strong_mono with "H'"); try auto.
    { iModIntro. iIntros (??) "$". }
    iIntros "!#" (w) "Hk". iIntros (Ψ'' Φ'') "Hhandler".
    iApply ewp_pure_step'; [apply pure_prim_step_beta| ]. simpl.
    by iApply ("IH" with "[Hk] Hhandler").
Qed.

End deep_handler.


Notation DeepTryWith e h r :=
  (App (App (App deep_try_with (Lam BAnon e)) h) r) (only parsing).

Notation "'try:' e 'with' 'effect' h | 'return' r 'end'" :=
  (DeepTryWith e h r)
  (e, h, r at level 200, only parsing) : expr_scope.
