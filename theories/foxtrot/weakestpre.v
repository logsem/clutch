
From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export fixpoint big_op.
From iris.prelude Require Import options.

From clutch.bi Require Export weakestpre.
From clutch.prelude Require Import stdpp_ext iris_ext NNRbar.
From clutch.con_prob_lang Require Import lang erasure.
From clutch.common Require Export sch_erasable con_language.
From clutch.prob Require Export couplings_app distribution.

Import uPred.

Set Default Proof Using "Type*".


Local Open Scope NNR_scope.
#[global] Hint Resolve cond_nonneg : core.

Section spec_transition.
  Definition spec_transition_compress (ρ: cfg con_prob_lang) (μ : distr (option nat))
    (f: nat -> cfg con_prob_lang -> distr (cfg con_prob_lang)) (μ' : distr (cfg con_prob_lang))
    : distr (cfg con_prob_lang) :=
    (μ ≫= (λ (o:option nat),
             match o with
             | Some tid => (dbind (λ ρ', f tid ρ') (step tid ρ))
             | None => μ'
             end
    )).

  Inductive spec_transition (ρ:cfg con_prob_lang) : distr (cfg con_prob_lang) ->  Prop :=
  | spec_transition_dret : spec_transition ρ (dret ρ)
  | spec_transition_bind (μ : distr (option nat))
      (f: nat -> cfg con_prob_lang -> distr (cfg con_prob_lang)) (μ' : distr (cfg con_prob_lang)):
    (∀ (tid:nat), (μ (Some tid) > 0)%R -> 
                (forall ρ', step tid ρ ρ' > 0 -> spec_transition ρ' (f tid ρ'))) ->
    ((μ None > 0)%R -> spec_transition ρ μ') ->
    spec_transition ρ (spec_transition_compress ρ μ f μ')
  .

  Lemma spec_transition_bind' ρ μ μ1 f μ2 :
    μ=spec_transition_compress ρ μ1 f μ2 ->
    (∀ (tid:nat), (μ1 (Some tid) > 0)%R -> 
                (forall ρ', step tid ρ ρ' > 0 -> spec_transition ρ' (f tid ρ'))) ->
    ((μ1 None > 0)%R -> spec_transition ρ μ2) ->
    spec_transition ρ μ.
  Proof.
    intros -> ??.
    by apply spec_transition_bind.
  Qed.
End spec_transition.

Class foxtrotWpGS (Λ : conLanguage) (Σ : gFunctors) := FoxtrotWpGS {
  foxtrotWpGS_invGS :: invGS_gen HasNoLc Σ;
  state_interp : state Λ → iProp Σ;
  spec_interp : cfg Λ -> iProp Σ;                                                         
  fork_post: val Λ -> iProp Σ;
  err_interp : nonnegreal → iProp Σ;
}.
Global Opaque foxtrotWpGS_invGS.
Global Arguments FoxtrotWpGS {Λ Σ}.
Canonical Structure NNRO := leibnizO nonnegreal.
#[global] Hint Resolve cond_nonneg : core.


Section modalities.
  Context `{H:!foxtrotWpGS con_prob_lang Σ}.
  Implicit Types ε : nonnegreal.

  (** spec_coupl *)
  Definition spec_coupl_pre Z
    (Φ : state con_prob_lang * cfg con_prob_lang * nonnegreal -> iProp Σ) :
    (state con_prob_lang * cfg con_prob_lang * nonnegreal -> iProp Σ) :=
    (λ x,
      let '(σ1, ρ, ε) := x in
      ⌜(1<=ε)%R⌝ ∨
        Z σ1 ρ ε ∨
        ∃ (S: state con_prob_lang -> cfg con_prob_lang -> Prop) (μ : distr (cfg con_prob_lang))
          (ε1 ε2: nonnegreal),
          ⌜spec_transition ρ μ ⌝ ∗
          ⌜ ε1 + ε2 <= ε ⌝ ∗
          ⌜ ARcoupl (dret σ1) μ S ε1 ⌝ ∗
          ∀ ρ', ⌜S σ1 ρ'⌝ ={∅}=∗ Φ (σ1, ρ', ε2)
    )%I.
      (* ( ∃ μ (ε2 : state con_prob_lang -> nonnegreal), *)
          (* ⌜ sch_erasable (λ t _ _ sch, TapeOblivious t sch) μ σ1 ⌝ ∗ *)
          (* ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
          (* ⌜ (Expval μ ε2 <= ε)%R ⌝ ∗ *)
          (* ∀ σ2, |={∅}=> Φ (σ2, ε2 σ2)))%I. *)

    
  #[local] Instance spec_coupl_pre_ne Z Φ :
    NonExpansive (spec_coupl_pre Z Φ).
  Proof.
    rewrite /spec_coupl_pre.
    intros ?[[?[??]]?][[?[??]]?] ([[=][=]]&[=]).
    by simplify_eq.
  Qed.

  #[local] Instance spec_coupl_pre_mono Z : BiMonoPred (spec_coupl_pre Z).
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    iIntros ([[??]?]) "[H|[H|(%&%&%&%&%&%&%&H)]]".
    - by iLeft.
    - iRight; by iLeft.
    - iRight; iRight.
      repeat iExists _; repeat (iSplit; [done|]).
      iIntros (??).
      iApply "Hwand".
      iApply ("H" with "[//]").
  Qed.

  Definition spec_coupl' Z := bi_least_fixpoint (spec_coupl_pre Z).
  Definition spec_coupl σ ρ ε Z:= spec_coupl' Z ((σ, ρ), ε).

  Lemma spec_coupl_unfold σ1 ρ ε Z :
    spec_coupl σ1 ρ ε Z ≡
      (⌜(1<=ε)%R⌝ ∨
        Z σ1 ρ ε ∨
        ∃ (S: state con_prob_lang -> cfg con_prob_lang -> Prop) (μ : distr (cfg con_prob_lang))
          (ε1 ε2: nonnegreal),
          ⌜spec_transition ρ μ ⌝ ∗
          ⌜ ε1 + ε2 <= ε ⌝ ∗
          ⌜ ARcoupl (dret σ1) μ S ε1 ⌝ ∗
          ∀ ρ', ⌜S σ1 ρ'⌝ ={∅}=∗ spec_coupl σ1 ρ' ε2 Z)%I.
  Proof. rewrite /spec_coupl /spec_coupl' least_fixpoint_unfold //. Qed.

  Lemma spec_coupl_ret_err_ge_1 σ1 ρ1 Z (ε : nonnegreal) :
    (1 <= ε)%R → ⊢ spec_coupl σ1 ρ1 ε Z.
  Proof. iIntros. rewrite spec_coupl_unfold. by iLeft. Qed.

  Lemma spec_coupl_ret σ1 ρ1 Z ε :
    Z σ1 ρ1 ε -∗ spec_coupl σ1 ρ1 ε Z.
  Proof. iIntros. rewrite spec_coupl_unfold. by iRight; iLeft. Qed.

  Lemma spec_coupl_rec σ1 ρ1 (ε : nonnegreal) Z :
     (∃ (S: state con_prob_lang -> cfg con_prob_lang -> Prop) (μ : distr (cfg con_prob_lang))
          (ε1 ε2: nonnegreal),
          ⌜spec_transition ρ1 μ ⌝ ∗
          ⌜ ε1 + ε2 <= ε ⌝ ∗
          ⌜ ARcoupl (dret σ1) μ S ε1 ⌝ ∗
          ∀ ρ2, ⌜S σ1 ρ2⌝ ={∅}=∗ spec_coupl σ1 ρ2 ε2 Z)%I
    ⊢ spec_coupl σ1 ρ1 ε Z.
  Proof. iIntros "H". rewrite spec_coupl_unfold. repeat iRight. done. Qed.

  Lemma spec_coupl_ind (Ψ Z : state con_prob_lang → cfg con_prob_lang -> nonnegreal → iProp Σ) :
    ⊢ (□ (∀ σ ρ ε,
             spec_coupl_pre Z (λ '(σ', ρ', ε'),
                 Ψ σ' ρ' ε' ∧ spec_coupl σ' ρ' ε' Z)%I ((σ, ρ), ε) -∗ Ψ σ ρ ε) →
       ∀ σ ρ ε, spec_coupl σ ρ ε Z -∗ Ψ σ ρ ε)%I.
  Proof.
    iIntros "#IH" (σ ρ ε) "H".
    set (Ψ' := (λ '(σ, ρ, ε), Ψ σ ρ ε) :
           (prodO (prodO (stateO con_prob_lang) (cfgO con_prob_lang)) NNRO) → iProp Σ).
    assert (NonExpansive Ψ').
    { intros n [[σ1 ρ1] ε1] [[σ2 ρ2] ε2].
      intros [[[=][=]][=]].
      by simplify_eq/=. }
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iIntros "!#" ([[??] ?]) "H". by iApply "IH".
  Qed.

  Lemma fupd_spec_coupl σ1 ρ1 Z (ε : nonnegreal) :
    (|={∅}=> spec_coupl σ1 ρ1 ε Z) ⊢ spec_coupl σ1 ρ1 ε Z.
  Proof.
    iIntros "H".
    iApply spec_coupl_rec.
    iExists (λ x y, x= σ1/\y=ρ1), (dret _), nnreal_zero, (ε).
    repeat iSplit.
    - iPureIntro. apply spec_transition_dret.
    - iPureIntro. simpl. lra. 
    - iPureIntro.
      by apply ARcoupl_dret.
    - iIntros (? [??]); by simplify_eq.
  Qed.
  
  Lemma spec_coupl_mono σ1 ρ1 Z1 Z2 ε :
    (∀ σ2 ρ2 ε', Z1 σ2 ρ2 ε' -∗ Z2 σ2 ρ2 ε') -∗
    spec_coupl σ1 ρ1 ε Z1 -∗ spec_coupl σ1 ρ1 ε Z2.
  Proof.
    iIntros "HZ Hs".
    iRevert "HZ".
    iRevert (σ1 ρ1 ε) "Hs".
    iApply spec_coupl_ind.
    iIntros "!#" (σ ρ ε)
      "[% | [? | (%&%&%&%&%&%&%&H)]] Hw".
    - iApply spec_coupl_ret_err_ge_1. lra.
    - iApply spec_coupl_ret. by iApply "Hw".
    - iApply spec_coupl_rec.
      repeat iExists _.
      repeat iSplit; try done.
      iIntros (??).
      iMod ("H" $! _ with "[//]") as "[IH _]".
      by iApply "IH".
  Qed.

  Lemma spec_coupl_mono_err ε1 ε2 σ1 ρ1 Z :
    (ε1 <= ε2)%R → spec_coupl σ1 ρ1 ε1 Z -∗ spec_coupl σ1 ρ1 ε2 Z.
  Proof.
    iIntros (Heps) "Hs".
    iApply spec_coupl_rec.
    set (ε' := nnreal_minus ε2 ε1 Heps).
    iExists (λ x y, x=σ1/\y=ρ1), (dret _), nnreal_zero, (ε1).
    repeat iSplit.
    - iPureIntro. apply spec_transition_dret.
    - iPureIntro; simpl; lra.
    - iPureIntro. by apply ARcoupl_dret. 
    - iIntros (? [??]); by simplify_eq.
  Qed.
  
  Lemma spec_coupl_bind σ1 ρ1 Z1 Z2 ε :
    (∀ σ2 ρ2 ε', Z1 σ2 ρ2 ε' -∗ spec_coupl σ2 ρ2 ε' Z2) -∗
    spec_coupl σ1 ρ1 ε Z1 -∗
    spec_coupl σ1 ρ1 ε Z2.
  Proof.
    iIntros "HZ Hs".
    iRevert "HZ".
    iRevert (σ1 ρ1 ε) "Hs".
    iApply spec_coupl_ind.
    iIntros "!#" (σ ρ ε)
      "[% | [H | (%&%&%&%&%&%&%&H)]] HZ".
    - by iApply spec_coupl_ret_err_ge_1.
    - iApply ("HZ" with "H").
    - iApply spec_coupl_rec.
      repeat iExists _.
      repeat iSplit; try done.
      iIntros (??).
      iMod ("H" $! _ with "[//]") as "[H _]".
      by iApply "H".
  Qed.

  (** TODO: state step for LHS *)
(*   Lemma spec_coupl_state_step α σ1 Z (ε ε' : nonnegreal) : *)
(*     α ∈ get_active σ1 → *)
(*     (∃ R, ⌜pgl (state_step σ1 α) R ε⌝ ∗ *)
(*           ∀ σ2 , ⌜R σ2 ⌝ ={∅}=∗ spec_coupl σ2 ε' Z) *)
(*     ⊢ spec_coupl σ1 (ε + ε') Z. *)
(*   Proof. *)
(*     iIntros (Hin) "(%R&%&H)". *)
(*     iApply spec_coupl_rec'. *)
(*     iExists R, (state_step σ1 α), ε, (λ _, ε'). *)
(*     repeat iSplit; try done. *)
(*     - iPureIntro. *)
(*       simpl in *. *)
(*       rewrite elem_of_elements elem_of_dom in Hin. *)
(*       destruct Hin. *)
(*       by eapply state_step_sch_erasable. *)
(*     - iPureIntro; eexists _; done. *)
(*     - iPureIntro. rewrite Expval_const; last done. rewrite state_step_mass; [simpl;lra|done].  *)
(*   Qed. *)

(*   Lemma spec_coupl_iterM_state_adv_comp N α σ1 Z (ε : nonnegreal) : *)
(*     (α ∈ get_active σ1 -> *)
(*      (∃ R ε1 (ε2 : _ -> nonnegreal), *)
(*         ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
(*         ⌜ (ε1 + Expval (iterM N (λ σ, state_step σ α) σ1) ε2 <= ε)%R ⌝ ∗ *)
(*         ⌜pgl (iterM N (λ σ, state_step σ α) σ1) R ε1⌝ ∗ *)
(*         ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ spec_coupl σ2 (ε2 σ2) Z) *)
(*       ⊢ spec_coupl σ1 ε Z)%I. *)
(*   Proof. *)
(*     iIntros (Hin) "(%R & %ε1 & %ε2 & % & %Hε & % & H)". *)
(*     iApply spec_coupl_rec'. *)
(*     iExists R, _, ε1, ε2. *)
(*     repeat iSplit; try done. *)
(*     - iPureIntro. *)
(*       simpl in *. *)
(*       rewrite elem_of_elements elem_of_dom in Hin. *)
(*       destruct Hin. *)
(*       by eapply iterM_state_step_sch_erasable. *)
(*   Qed.  *)
  
(*   Lemma spec_coupl_state_adv_comp α σ1 Z (ε : nonnegreal) : *)
(*     (α ∈ get_active σ1 -> *)
(*      (∃ R ε1 (ε2 : _ -> nonnegreal), *)
(*         ⌜ exists r, forall ρ, (ε2 ρ <= r)%R ⌝ ∗ *)
(*         ⌜ (ε1 + Expval (state_step σ1 α) ε2 <= ε)%R ⌝ ∗ *)
(*         ⌜pgl (state_step σ1 α) R ε1⌝ ∗ *)
(*         ∀ σ2, ⌜ R σ2 ⌝ ={∅}=∗ spec_coupl σ2 (ε2 σ2) Z) *)
(*       ⊢ spec_coupl σ1 ε Z)%I. *)
(*   Proof. *)
(*     iIntros (Hin) "(%R & %ε1 & %ε2 & % & %Hε & % & H)". *)
(*     iApply (spec_coupl_iterM_state_adv_comp 1%nat); first done. *)
(*     repeat iExists _. simpl. rewrite dret_id_right. *)
(*     by repeat iSplit. *)
(*   Qed. *)
  

  (** * One step prog coupl *)

  Definition prog_coupl e1 σ1 ρ1 ε Z : iProp Σ :=
    (∃ (R : (expr con_prob_lang * state con_prob_lang * list (expr con_prob_lang)) -> cfg con_prob_lang -> Prop)
       μ (ε1 ε2:nonnegreal),
           ⌜reducible e1 σ1⌝ ∗
           ⌜ spec_transition ρ1 μ ⌝ ∗
           ⌜ ε1 + ε2 <= ε%R⌝ ∗
           ⌜ ARcoupl (prim_step e1 σ1) μ R ε1 ⌝ ∗
           (∀ e2 σ2 efs ρ2, ⌜R (e2, σ2, efs) ρ2⌝ ={∅}=∗
                         Z e2 σ2 efs ρ2 ε2 )
       )%I.

  Lemma prog_coupl_mono_err e σ ρ Z ε ε':
    (ε<=ε')%R -> prog_coupl e σ ρ ε Z -∗ prog_coupl e σ ρ ε' Z.
  Proof.
    iIntros (?) "(%&%&%&%&%&%&%&%&H)".
    repeat iExists _.
    repeat iSplit; try done.
    iPureIntro.
    etrans; exact.
  Qed.

  Lemma prog_coupl_strong_mono e1 σ1 ρ1 Z1 Z2 ε :
    (∀ e2 σ2 ρ2 ε' efs, ⌜∃ σ, (prim_step e1 σ (e2, σ2, efs) > 0)%R⌝ ∗ Z1 e2 σ2 efs ρ2 ε' -∗ Z2 e2 σ2 efs ρ2 ε') -∗
    prog_coupl e1 σ1 ρ1 ε Z1 -∗ prog_coupl e1 σ1 ρ1 ε Z2.
  Proof.
    iIntros "Hm (%&%&%&%&%&%&%&%Hcoupl&H) /=".
    rewrite /prog_coupl.
    apply ARcoupl_pos_R in Hcoupl.
    iExists _, _, _, _.
    repeat iSplit; try done.
    simpl.
    iIntros (????(?&?&?)).
    iApply "Hm". iMod ("H" with "[//]").
    iFrame. iPureIntro. naive_solver.
  Qed.
  
  Lemma prog_coupl_mono e1 σ1 ρ1 Z1 Z2 ε :
    (∀ e2 σ2 efs ρ2 ε', Z1 e2 σ2 efs ρ2 ε' -∗ Z2 e2 σ2 efs ρ2 ε') -∗
    prog_coupl e1 σ1 ρ1 ε Z1 -∗ prog_coupl e1 σ1 ρ1 ε Z2.
  Proof.
    iIntros "Hm".
    rewrite /prog_coupl.
    iIntros "(%&%&%&%&%&%&%&%&H)".
    repeat iExists _; repeat iSplit; try done.
    iIntros. iApply "Hm". by iApply "H".
  Qed.
  
  Lemma prog_coupl_strengthen e1 σ1 ρ1 Z ε :
    prog_coupl e1 σ1 ρ1 ε Z -∗
    prog_coupl e1 σ1 ρ1 ε (λ e2 σ2 efs ρ2 ε',
                             ⌜(∃ σ, (prim_step e1 σ (e2, σ2, efs) > 0)%R)⌝ ∧ Z e2 σ2 efs ρ2 ε').
  Proof.
    iIntros "(%&%&%&%&%&%&%&%Hcoupl&H) /=".
    rewrite /prog_coupl.
    apply ARcoupl_pos_R in Hcoupl.
    iExists _, _, _, _.
    repeat iSplit; try done. simpl.
    iIntros (????(?&?&?)).
    iMod ("H" with "[//]") as "$".
    iPureIntro. naive_solver.
  Qed.

  Lemma prog_coupl_ctx_bind K `{!ConLanguageCtx K} e1 σ1 ρ1 Z ε:
    to_val e1 = None ->
    prog_coupl e1 σ1 ρ1 ε (λ e2 σ2 efs ρ2 ε', Z (K e2) σ2 efs ρ2 ε') -∗ prog_coupl (K e1) σ1 ρ1 ε Z.
  Proof.
    iIntros (Hv) "H".
    (* iDestruct (prog_coupl_strengthen with "[][$]") as "H". *)
    (* { iModIntro. by iIntros. } *)
    iDestruct "H" as "(%R&%μ&%ε1&%ε2&%&%&%&%&H)".
    (** (classical) inverse of context [K] *)
    destruct (partial_inv_fun K) as (Kinv & HKinv).
    assert (∀ e, Kinv (K e) = Some e) as HKinv3.
    { intro e.
      destruct (Kinv (K e)) eqn:Heq;
        eapply HKinv in Heq; by simplify_eq. }
    (* set (ε2' := (λ '(e, σ, efs), from_option (λ e', ε2 (e', σ, efs)) 1%NNR (Kinv e))). *)
    (* assert (∀ e2 σ2 efs, ε2' (K e2, σ2, efs) = ε2 (e2, σ2, efs)) as Hε2'. *)
    (* { intros. rewrite /ε2' HKinv3 //. } *)
    rewrite /prog_coupl.
    iExists (λ '(e2, σ2, efs) ρ2, ∃ e2', e2 = K e2' /\ R (e2', σ2, efs) ρ2), μ, ε1, ε2.
    repeat iSplit; try iPureIntro.
    - by apply reducible_fill.
    - done.
    - done.
    - rewrite fill_dmap //.
      rewrite /dmap.
      rewrite -(dret_id_right μ) //.
      eapply (ARcoupl_dbind' _ nnreal_zero); last done; [done|done|simpl; lra|].
      iIntros ([[??]?]??).
      apply ARcoupl_dret; naive_solver.
    - iIntros (????(?&->&?)).
      by iApply "H".
  Qed.
  
  Lemma prog_coupl_reducible e σ ρ Z ε :
    prog_coupl e σ ρ ε Z -∗ ⌜reducible e σ⌝.
  Proof. by iIntros "(%&%&%&%&%&?)". Qed.
 
(** TODO: add nice lemmas for using prog_coupl, e.g. prim_step only on the left*)

End modalities.

(** * The weakest precondition  *)
Definition wp_pre `{!foxtrotWpGS con_prob_lang Σ}
    (wp : coPset -d> expr con_prob_lang -d> (val con_prob_lang -d> iPropO Σ) -d> iPropO Σ) :
     coPset -d> expr con_prob_lang -d> (val con_prob_lang -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  (∀ σ1 ρ1 ε1,
      state_interp σ1 ∗ spec_interp ρ1 ∗ err_interp ε1 ={E, ∅}=∗
      spec_coupl σ1 ρ1 ε1 (λ σ2 ρ2 ε2,
        match to_val e1 with
        | Some v => |={∅, E}=> state_interp σ2 ∗ spec_interp ρ2 ∗ err_interp ε2 ∗ Φ v
        | None =>
            prog_coupl e1 σ2 ρ2 ε2 (λ e3 σ3 efs ρ3 ε3,
                ▷ spec_coupl σ3 ρ3 ε3 (λ σ4 ρ4 ε4,
                   |={∅, E}=> state_interp σ4 ∗ spec_interp ρ4 ∗ err_interp ε4 ∗
                             wp E e3 Φ ∗[∗ list] ef ∈efs, wp ⊤ ef fork_post))
      end))%I.


Local Instance wp_pre_contractive `{!foxtrotWpGS con_prob_lang Σ} : Contractive (wp_pre).
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E e1 Φ /=.
  do 8 f_equiv.
  apply least_fixpoint_ne_outer; [|done].
  intros Ψ [[e' σ'] ε'].
  rewrite /spec_coupl_pre.
  do 3 f_equiv.
  rewrite /prog_coupl.
  do 22 f_equiv.
  f_contractive.
  apply least_fixpoint_ne_outer; [|done].
  intros ? [[??]?].
  rewrite /spec_coupl_pre.
  repeat f_equiv; apply Hwp.
Qed.
