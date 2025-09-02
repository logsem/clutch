 (** An axiomatization of evaluation-context based languages, including a proof
    that this gives rise to a "language" in our sense. *)
Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz Logic.FunctionalExtensionality Reals.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp classical_sets.
From iris.prelude Require Import options.
From iris.algebra Require Import ofe.
From clutch.bi Require Import weakestpre.
From mathcomp.analysis Require Import measure ereal.
(* From clutch.prob.monad Require Import laws types meas_markov. *)
From clutch.prob.monad Require Import giry meas_markov.
From clutch.meas_lang Require Import language prelude.

Require Import mathcomp.reals_stdlib.Rstruct.
Require Import mathcomp.reals.reals.
From Coq Require Import ssrfun.
Set Warnings "hiding-delimiting-key".

Section ectx_language_mixin.
  Local Open Scope classical_set_scope.
  Context {d_expr d_val d_state d_ectx: measure_display}.
  Context {exprT valT stateT ectxT: Type}.
  Context `{SigmaAlgebra d_expr exprT}.
  Context `{SigmaAlgebra d_val valT}.
  Context `{SigmaAlgebra d_state stateT}.
  Context `{SigmaAlgebra d_ectx ectxT}.
  Notation val := (toPackedType d_val valT).
  Notation expr := (toPackedType d_expr exprT).
  Notation state := (toPackedType d_state stateT).
  Notation ectx := (toPackedType d_ectx ectxT).
  Context (of_val : val -> expr).
  Context (to_val : expr -> (option val)).
  Context (head_step : (expr * state)%type -> (giryM (expr * state)%type)).
  Context (empty_ectx : ectx).
  Context (comp_ectx : ectx → ectx → ectx). (* TODO: Does this need to be measurable? I assume yes. *)
  Context (fill : (ectx * expr)%type -> expr).
  Context (decomp : expr → (ectx * expr)%type).

  Record MeasEctxLanguageMixin := {
    mixin_of_val_meas : measurable_fun setT of_val;
    mixin_to_val_meas : measurable_fun setT to_val;
    mixin_head_step_meas : measurable_fun setT head_step;
    mixin_fill_meas : measurable_fun setT fill;
    mixin_decomp_meas : measurable_fun setT decomp;

    mixin_expr_meas_points : forall (e : expr), measurable [set e];
    mixin_val_meas_points : forall (v : val), measurable [set v];
    mixin_state_meas_points : forall (v : state), measurable [set v];

    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;

    mixin_head_stuck e σ : (¬ is_zero (head_step (e, σ))) → to_val e = None;
    mixin_head_step_mass e σ : (¬ is_zero (head_step (e, σ))) -> is_prob (head_step (e, σ))  ;

    mixin_fill_empty e : fill (empty_ectx, e) = e;
    mixin_fill_comp K1 K2 e : fill (K1, (fill (K2, e))) = fill ((comp_ectx K1 K2), e);
    mixin_fill_inj K : Inj (=) (=) ((curry fill) K);
    mixin_fill_val K e : is_Some (to_val (fill (K, e))) → is_Some (to_val e);


    (** [decomp] decomposes an expression into an evaluation context and its head redex  *)
    mixin_decomp_fill K e e' :
      decomp e = (K, e') → fill (K, e') = e;
    mixin_decomp_val_empty K e e' :
      decomp e = (K, e') → is_Some (to_val e') → K = empty_ectx;
    mixin_decomp_fill_comp e e' K K' :
      to_val e = None → decomp e = (K', e') → decomp (fill (K, e)) = (comp_ectx K K', e');

    (** Given a head redex [e1_redex] somewhere in a term, and another
        decomposition of the same term into [fill K' e1'] such that [e1'] is
        not a value, then the head redex context is [e1']'s context [K']
        filled with another context [K''].  In particular, this implies [e1 =
        fill K'' e1_redex] by [fill_inj], i.e., [e1]' contains the head redex.

        This implies there can be only one head redex, see
        [head_redex_unique]. *)
    mixin_step_by_val K' K_redex e1' e1_redex σ1 :
      fill (K', e1') = fill (K_redex, e1_redex) →
      to_val e1' = None →
      (¬ is_zero (head_step (e1_redex, σ1))) →
      ∃ K'', K_redex = comp_ectx K' K'';

    (** If [fill K e] takes a head step, then either [e] is a value or [K] is
      the empty evaluation context. In other words, if [e] is not a value
      wrapping it in a context does not add new head redex positions. *)
    mixin_head_ctx_step_val K e σ1 :
      (¬ is_zero (head_step ((fill (K, e)), σ1))) →
      is_Some (to_val e) ∨ K = empty_ectx;
  }.
End ectx_language_mixin.

Structure meas_ectxLanguage := MeasEctxLanguage {
  d_expr : measure_display;
  d_val: measure_display;
  d_state: measure_display;
  d_ectx: measure_display;
  exprT : Type;
  valT : Type;
  stateT : Type;
  ectxT : Type;
  expr_SigmaAlgebra : SigmaAlgebra d_expr exprT;
  val_SigmaAlgebra : SigmaAlgebra d_val valT;
  state_SigmaAlgebra : SigmaAlgebra d_state stateT;
  ectx_SigmaAlgebra : SigmaAlgebra d_ectx ectxT;

  of_val : (toPackedType d_val valT) → (toPackedType d_expr exprT);
  to_val : (toPackedType d_expr exprT) → option (toPackedType d_val valT);
  empty_ectx : (toPackedType d_ectx ectxT);
  comp_ectx : (toPackedType d_ectx ectxT) → (toPackedType d_ectx ectxT) → (toPackedType d_ectx ectxT);
  fill : ((toPackedType d_ectx ectxT) * (toPackedType d_expr exprT))%type -> (toPackedType d_expr exprT);
  decomp : (toPackedType d_expr exprT) → ((toPackedType d_ectx ectxT) * (toPackedType d_expr exprT))%type;
  head_step : ((toPackedType d_expr exprT) * (toPackedType d_state stateT))%type -> (giryM ((toPackedType d_expr exprT) * (toPackedType d_state stateT))%type);
  ectx_language_mixin :
    MeasEctxLanguageMixin of_val to_val head_step empty_ectx comp_ectx fill decomp;
}.

#[global] Existing Instance expr_SigmaAlgebra.
#[global] Existing Instance val_SigmaAlgebra.
#[global] Existing Instance state_SigmaAlgebra.
#[global] Existing Instance ectx_SigmaAlgebra.

Notation val Λ := (toPackedType (d_val Λ) (valT Λ)).
Notation expr Λ := (toPackedType (d_expr Λ) (exprT Λ)).
Notation state Λ := (toPackedType (d_state Λ) (stateT Λ)).
Notation ectx Λ := (toPackedType (d_ectx Λ) (ectxT Λ)).

Bind Scope expr_scope with exprT.
Bind Scope val_scope with valT.

Global Arguments MeasEctxLanguage {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments empty_ectx {_}.
Global Arguments comp_ectx {_} _ _.
Global Arguments decomp {_} _.
Global Arguments fill {_} _.
Global Arguments head_step {_}.

(* From an ectx_language, we can construct a language. *)
Section ectx_language.
  Context {Λ : meas_ectxLanguage}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types K : ectx Λ.

  (* Only project stuff out of the mixin that is not also in language *)
  Lemma head_step_meas : measurable_fun setT (@head_step Λ).
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_meas : measurable_fun setT (@fill Λ).
  Proof. apply ectx_language_mixin. Qed.
  Lemma decomp_meas : measurable_fun setT (@decomp Λ).
  Proof. apply ectx_language_mixin. Qed.
  Lemma head_not_stuck e σ : (¬ is_zero (head_step (e, σ))) → to_val e = None.
  Proof. apply ectx_language_mixin. Qed.
  Lemma head_step_mass e σ : (¬ is_zero (head_step (e, σ))) -> is_prob (head_step (e, σ)).
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_empty e : fill (empty_ectx, e) = e.
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_comp K1 K2 e : fill (K1, (fill (K2, e))) = fill ((comp_ectx K1 K2), e).
  Proof. apply ectx_language_mixin. Qed.
  Global Instance fill_inj K : Inj (=) (=) ((curry fill) K).
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_val K e : is_Some (to_val (fill (K, e))) → is_Some (to_val e).
  Proof. apply ectx_language_mixin. Qed.
  Lemma decomp_fill K e e' : decomp e = (K, e') → fill (K, e') = e.
  Proof. apply ectx_language_mixin. Qed.
  Lemma decomp_val_empty K e e' :
    decomp e = (K, e') → is_Some (to_val e') → K = empty_ectx.
  Proof. apply ectx_language_mixin. Qed.
  Lemma decomp_fill_comp K K' e e' : to_val e = None → decomp e = (K', e') → decomp (fill (K, e)) = (comp_ectx K K', e').
  Proof. apply ectx_language_mixin. Qed.
  Lemma step_by_val K' K_redex e1' e1_redex σ1 :
      fill (K', e1') = fill (K_redex, e1_redex) →
      to_val e1' = None →
      (¬ is_zero (head_step (e1_redex, σ1))) →
      ∃ K'', K_redex = comp_ectx K' K''.
  Proof. apply ectx_language_mixin. Qed.
  Lemma head_ctx_step_val K e σ1 :
      (¬ is_zero (head_step ((fill (K, e)), σ1))) →
      is_Some (to_val e) ∨ K = empty_ectx.
  Proof. apply ectx_language_mixin. Qed.

  Class head_reducible (e : expr Λ) (σ : state Λ) :=
    head_reducible_step : ¬ is_zero (head_step (e, σ)).
  Definition head_irreducible (e : expr Λ) (σ : state Λ) :=
    is_zero (head_step (e, σ)).
  Definition head_stuck (e : expr Λ) (σ : state Λ) :=
    to_val e = None ∧ head_irreducible e σ.

  (* All non-value redexes are at the root. In other words, all sub-redexes are
     values. *)
  Definition sub_redexes_are_values (e : expr Λ) :=
    ∀ K e', e = fill (K, e') → to_val e' = None → K = empty_ectx.

  Definition fill_liftU : (ectx Λ * (expr Λ * state Λ)) → (expr Λ * state Λ) :=
    mProd
      ( ssrfun.comp fill $
        mProd fst (ssrfun.comp fst snd) )
      ( ssrfun.comp snd snd ).

  Lemma fill_liftU_meas : measurable_fun setT fill_liftU.
  Proof.
    mcrunch_prod.
    { eapply @measurable_compT; first by eauto with measlang.
      { by apply fill_meas. }
      mcrunch_prod.
      { by eauto with measlang. }
      by mcrunch_comp.
    }
    { by mcrunch_comp. }
  Qed.

  Definition fill_lift (K : ectx Λ) : (expr Λ * state Λ) → (expr Λ * state Λ) :=
    fun x => fill_liftU (K, x).

  Lemma fill_lift_meas K: measurable_fun setT (fill_lift K).
  Proof.
    rewrite /fill_lift.
    assert ((λ x, fill_liftU (K, x)) = fill_liftU \o (λ x, (K, x))) as Hrewrite.
    { apply functional_extensionality_dep.
      by intros [??]. }
    rewrite Hrewrite.
    eapply @measurable_comp; [| |apply fill_liftU_meas|]; try done.
    apply pair1_measurable.
  Qed.
  
  Lemma fill_lift_comp (K1 K2 : ectx Λ) :
    fill_lift (comp_ectx K1 K2) = fill_lift K1 ∘ fill_lift K2.
  Proof.
    extensionality ρ. destruct ρ.
    rewrite /fill_lift/fill_liftU //=.
    rewrite -fill_comp //=.
  Qed.

  Lemma fill_lift_empty :
    fill_lift empty_ectx = (λ ρ, ρ).
  Proof.
    extensionality ρ. destruct ρ.
    rewrite /fill_lift/fill_liftU //= fill_empty //.
  Qed.
  Instance inj_fill (K : ectx Λ) : Inj eq eq (fill_lift K).
  Proof.
    intros [] [].
    move=> [H1 ->].
    have HF : ((curry fill) K) s = ((curry fill) K) s1 by rewrite //=.
    by rewrite (fill_inj K _ _ HF).
  Qed.

  (** FIXME: What a strange little measurability proof. *)
  (* Definition prim_step : (expr Λ * state Λ)%type -> giryM (expr Λ * state Λ)%type := *)
  (*   gMap' (fill_liftU \o (fst \o decomp \o fst △ id)) \o head_step \o ((snd \o decomp \o fst) △ snd). *)
  Definition prim_step : (toPackedType _ (exprT Λ * stateT Λ)%type) -> giryM (toPackedType _ (exprT Λ * stateT Λ)%type) :=
    λ '(e, σ),
      let '(K, e') := decomp e in
      gMap' (fill_lift K) (head_step (e', σ)). 

  Definition prim_step' : (toPackedType _ (exprT Λ * stateT Λ)%type) -> giryM (toPackedType _ (exprT Λ * stateT Λ)%type) :=
    gMap' fill_liftU \o
    (gProd \o (gRet \o fst △ (head_step \o snd)) \o (fst \o decomp \o fst △ (snd \o decomp \o fst △ snd))).

  Lemma prim_step_prim_step' : prim_step = prim_step'.
    extensionality ρ. destruct ρ as [e s].
    rewrite /prim_step/prim_step'.
    destruct (decomp e) eqn:Hdecomp.
    simpl. rewrite /fill_lift. rewrite Hdecomp/=.
    (* need lemmas about gRet and gMap *)
  Admitted.
  
  Lemma prim_step_meas: measurable_fun setT prim_step.
  Proof.
    rewrite prim_step_prim_step'.
    rewrite /prim_step'.
    eapply measurable_comp; [| |apply gMap'_meas_fun|].
    { done. }
    { done. }
    { apply fill_liftU_meas. }
    mf_cmp_tree; try done.
    - mf_cmp_tree; try done.
      + eapply @gProd_meas_fun.
      + mf_prod; mf_cmp_tree; try done.
        * apply gRet_meas_fun.
        * apply head_step_meas.
    - mf_prod; repeat mf_cmp_tree; try done.
      + apply decomp_meas.
      + mf_prod. repeat mf_cmp_tree; try done.
        apply decomp_meas.
  Qed.
    
  (*
    ssrfun.comp
      ( giryM_map (ssrfun.comp fill_liftU $ mProd (ssrfun.comp fst $ ssrfun.comp decomp fst) (fun x => x)) _ )
      .
  Next Obligation.
    eapply @measurable_compT; first by eauto with measlang.
    { by apply fill_liftU_meas. }
    eapply @measurable_compT; first by eauto with measlang.
    { eapply @measurable_compT; first by eauto with measlang.
      { mcrunch_prod.
        { mcrunch_comp.
          eapply @measurable_compT; first by eauto with measlang.
          { by apply decomp_meas. }
          { by eauto with measlang. }
        }
        { by eapply measurable_id. }
      }
      { by eapply measurable_id. }
    }
    { by eapply measurable_id. }
  Qed.
*)
  Lemma fill_not_val K e : to_val e = None → to_val (fill (K, e)) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Definition ectx_lang_mixin : MeasLanguageMixin (@of_val Λ) to_val prim_step.
  Proof. split.
         - by apply ectx_language_mixin.
         - by apply ectx_language_mixin.
         - apply prim_step_meas.
         - by apply ectx_language_mixin.
         - by apply ectx_language_mixin.
         - by apply ectx_language_mixin.
         - by apply ectx_language_mixin.
         - by apply ectx_language_mixin. 
         - intros e σ.
           rewrite /prim_step.
           case_match.
           apply decomp_fill in H. subst.
           intros Hneg.
           apply fill_not_val.
           eapply head_not_stuck.
           intros Hzero; apply Hneg.
           apply is_zero_gMap'; [apply fill_lift_meas|done].
         - intros e σ.
           rewrite /prim_step.
           destruct (decomp e) as [K e'] eqn:Heqn.
           apply decomp_fill in Heqn. subst.
           intros Hneg.
           assert (¬ is_zero (head_step (e', σ))).
           { intros Hzero; apply Hneg. apply is_zero_gMap'; last done.
             apply fill_lift_meas.
           }
           unshelve rewrite gMap'_gMap; first apply fill_lift_meas. 
           rewrite -is_prob_gMap; last done.
           by apply head_step_mass.
  Qed.

  Canonical Structure ectx_lang : meas_language := MeasLanguage _ _ _ ectx_lang_mixin.

  (*
  Definition head_atomic (a : atomicity) (e : expr Λ) : Prop :=
    ∀ σ e' σ',
      head_step e σ (e', σ') > 0 →
      if a is WeaklyAtomic then irreducible (e', σ') else is_Some (to_val e').
  *)

  (** * Some lemmas about this language *)

  Lemma not_head_reducible e σ : ¬head_reducible e σ ↔ head_irreducible e σ.
  Proof.
    unfold head_reducible, head_irreducible. split.
    { by apply classical.NNP_P. }
    { by apply classical.P_NNP. }
  Qed.

  (** The decomposition into head redex and context is unique.
      In all sensible instances, [comp_ectx K' empty_ectx] will be the same as
      [K'], so the conclusion is [K = K' ∧ e = e'], but we do not require a law
      to actually prove that so we cannot use that fact here. *)
  Lemma head_redex_unique K K' e e' σ :
    fill (K, e) = fill (K', e') →
    head_reducible e σ →
    head_reducible e' σ →
    K = comp_ectx K' empty_ectx ∧ e = e'.
  Proof.
    intros Heq H1 H2.
    edestruct (step_by_val K' K e' e) as [K'' HK].
    { by symmetry; apply Heq. }
    { by eapply head_not_stuck, H2. }
    { by eapply H1. }
    subst K. move: Heq. rewrite -fill_comp.
    intro HI.
    have HI' := (fill_inj _ _ _ HI).
    rewrite <- HI' in H2.
    destruct (head_ctx_step_val _ _ σ H2) as [HA | HA].
    { exfalso.
      erewrite head_not_stuck in HA; [by destruct HA |].
      by eapply H1. }
    { subst K''.
      split; [done|].
      rewrite <-HI'.
      by rewrite fill_empty. }
  Qed.

  Lemma fill_prim_step_dbind K e1 σ1 :
    to_val e1 = None →
    prim_step ((fill (K, e1)), σ1) = gMap' (fill_lift K) (prim_step (e1, σ1)).
  Proof.
    intros Hval. rewrite /prim_step.
    destruct (decomp e1) as [K1 e1'] eqn:Heq.
    destruct (decomp (fill (K, e1))) as [K1' e1''] eqn:Heq'.
    apply (decomp_fill_comp K) in Heq; [|done].
    rewrite Heq in Heq'; simplify_eq.
    (* Need lemmas for gMap', in particular composition of gMaps *)
  Admitted.

  (*  head_prim_step_pmf_eq e1 σ1: Same thing but pointwise *)

  Lemma head_prim_step_eq e1 σ1:
    head_reducible e1 σ1 →
    prim_step (e1, σ1) ≡μ head_step (e1, σ1).
  Proof.
    intros Hred.
    rewrite /= /prim_step.
    destruct (decomp e1) as [K e1'] eqn:Heq.
    edestruct (decomp_fill _ _ _ Heq).
    destruct (head_ctx_step_val _ _ _ Hred) as [| ->].
    - assert (K = empty_ectx) as -> by eauto using decomp_val_empty.
      rewrite fill_lift_empty fill_empty.
      rewrite gMap'_id.
      reflexivity.
    - rewrite fill_lift_empty fill_empty.
      rewrite gMap'_id.
      reflexivity.
  Qed.

  (*
  (* MARKUS: Renamed becuase it was breaking the build *)
  (* MARKUS: Commented out because it's not used, and I think the pointwise evaluations shouldn't be used anyways.
     The "right" version of this lemma should say that measure_eq (head_step (e1, σ1) ρ) gZero iff
     measure_eq (prim_step (e1, σ1) ρ) gZero. But I'm not sure we even need that yet.
   *)
  Lemma head_prim_step' e1 σ1 ρ :
    (lt_ereal 0 (head_step (e1, σ1) ρ)) → lt_ereal 0 (prim_step (e1, σ1) ρ).
  Proof. intros H. erewrite head_prim_step_eq; first done.
         - rewrite /head_reducible.
           intro H'. assert (head_step (e1, σ1) ρ = 0)%E as Hrewrite.
           { rewrite H'; first done.
             (** hmmmm... ask markus *)
             admit. }
           rewrite Hrewrite in H.
           rewrite lt_def_ereal in H.
           apply andb_prop_elim in H as [H _].
           cbv in H. by repeat case_match.
         - (** same problem as above *)
  Admitted.
*)

  (* Proof breaks when no @ for some reason *)
  Lemma head_prim_step e1 σ1 : ¬ (is_zero (head_step (e1, σ1))) -> ¬ (is_zero (prim_step (e1, σ1))).
  Proof. intros ?. by rewrite (@head_prim_step_eq _ _ _). Qed.


  Local Open Scope classical_set_scope.
  
  Lemma prim_step_iff e1 e2 σ1 σ2 :
    lt_ereal 0 (prim_step (e1, σ1) [set (e2, σ2)]) ↔
    ∃ K e1' e2',
      fill (K, e1') = e1 ∧
      fill (K, e2') = e2 ∧
      lt_ereal 0 (head_step (e1', σ1) [set (e2', σ2)]).
  Proof.
    split.
    - rewrite /prim_step. intros Hs.
      destruct (decomp e1) as [K e1'] eqn:Heq.
      apply decomp_fill in Heq.
      (** Derive lemmas for gMap' pos *)
      admit.
      (* eapply dmap_pos in Hs as [[] [[=] ?]]. *)
      (* simplify_eq. do 3 eexists; eauto. *)
    - intros (K & e1' & e2' & Hfill1 & Hfill2 & Hs). simplify_eq.
      rewrite fill_prim_step_dbind.
      + (** Lemmas for gMap' pos *)
        admit.
      + eapply head_not_stuck with σ1.
        intros Hzero; rewrite Hzero in Hs.
        * simpl in Hs.
          destroy_mathcomp; simpl in *.
          epose proof elimT (RltbP 0 0) _; first lra.
          Unshelve.
          rewrite /is_true/Is_true in Hs *.
          by case_match.
        * rewrite prod1.
          eapply @measurableX.
          { eapply @expr_meas_points. }
          { eapply @state_meas_points. }
  Admitted.

  (*  Markov lemmas *)

  Lemma head_step_not_stuck e σ : (¬ is_zero (head_step (e, σ))) → not_stuck (e, σ).
  Proof.
    rewrite /not_stuck /reducible /=. intros Hs.
    erewrite <-head_prim_step_eq in Hs; last done.
    by right.
  Qed.

  
  Lemma head_val_stuck e σ : is_Some (to_val e) -> (is_zero (head_step (e, σ))).
  Proof.
    pose proof head_not_stuck e σ.
    apply contraPP.
    by intros ->%H.
  Qed.
  
  Lemma fill_reducible K e σ : reducible (e, σ) → reducible (fill (K, e), σ).
  Proof.
    rewrite /reducible/step/=.
    destruct (decomp e) as [K1 e1] eqn:Heqn1.
    destruct (decomp (fill (K, e))) as [K2 e2] eqn:Heqn2.
    intros H. intros H'. apply H.
    apply is_zero_gMap'; first apply fill_lift_meas.
    erewrite decomp_fill_comp in Heqn2; last done.
    - simplify_eq. (* apply decomp_fill in Heqn1 as Heqn2. subst. *)
      (* rewrite fill_comp in H'. *)
      destruct (to_val e2) eqn:Hval.
      + by apply head_val_stuck.
      + erewrite decomp_fill_comp in H'; last done.
        * eapply gMap'_is_zero; last done. apply fill_lift_meas.
        * apply decomp_fill in Heqn1. subst. by apply fill_not_val.
    - assert (to_val e1 = None).
      { eapply head_not_stuck.
        intros ?.
        apply H. 
        eapply is_zero_gMap'; last done.
        apply fill_lift_meas.
      }
      apply decomp_fill in Heqn1. subst.
      by apply fill_not_val.
  Qed. 
  Lemma head_prim_reducible e σ : head_reducible e σ → reducible (e, σ).
  Proof. intros.
         by apply head_prim_step.
  Qed.
  Lemma head_prim_fill_reducible e K σ :
    head_reducible e σ → reducible (fill (K, e), σ).
  Proof. intro. by apply fill_reducible, head_prim_reducible. Qed.
  (* Lemma state_step_head_reducible e σ σ' α : *)
  (*   state_step σ α σ' > 0 → head_reducible e σ ↔ head_reducible e σ'. *)
  (* Proof. eapply state_step_head_not_stuck. Qed. *)
  Lemma head_prim_irreducible e σ : irreducible (e, σ) → head_irreducible e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using head_prim_reducible.
  Qed.



  Lemma prim_head_reducible e σ :
    reducible (e, σ) → sub_redexes_are_values e → head_reducible e σ.
  Proof.
    rewrite /reducible/head_reducible/sub_redexes_are_values/=.
    destruct (decomp e) as [K e'] eqn:Heqn1.
    intros Hzero H Hzero'.
    apply Hzero. clear Hzero.
    apply decomp_fill in Heqn1; subst.
    destruct (to_val e') eqn:Heqn2.
    - apply is_zero_gMap'; first apply fill_lift_meas.
      destruct (classical.ExcludedMiddle (is_zero (head_step (e', σ)))) as [|H']; first done.
      apply head_not_stuck in H'. rewrite H' in Heqn2. done.
    - assert (K=empty_ectx) as ->.
      { eapply H; done. }
      rewrite fill_lift_empty in Hzero' *.
      rewrite fill_empty in Hzero'.
      by rewrite gMap'_id.
  Qed.
  Lemma prim_head_irreducible e σ :
    head_irreducible e σ → sub_redexes_are_values e → irreducible (e, σ).
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using prim_head_reducible.
  Qed.

  Lemma head_stuck_stuck e σ :
    head_stuck e σ → sub_redexes_are_values e → stuck (e, σ).
  Proof.
    intros [] ?. split; [by eapply to_final_None_2|].
    by apply prim_head_irreducible.
  Qed.

  (** We dont have anything about atomic i think?*)
  (* Lemma ectx_language_atomic a e : *)
  (*   head_atomic a e → sub_redexes_are_values e → Atomic a e. *)
  (* Proof. *)
  (*   intros Hatomic Hsub σ e' σ' (K & e1' & e2' & <- & <- & Hs)%prim_step_iff. *)
  (*   assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck. *)
  (*   rewrite fill_empty in Hatomic. *)
  (*   eapply Hatomic. rewrite fill_empty. eauto. *)
  (* Qed. *)



  (** Not sure how to express this in measure theortic terms *)
  (*
  Lemma head_reducible_prim_step_ctx K e1 σ1 e2 σ2:
    head_reducible e1 σ1 →
    prim_step (fill K e1) σ1 (e2, σ2) > 0 →
    ∃ e2', e2 = fill K e2' ∧ head_step e1 σ1 (e2', σ2) > 0.
  Proof.
    intros [[e2'' σ2''] HhstepK] (K' & e1' & e2' & HKe1 & HKe2 & Hs)%prim_step_iff.
    symmetry in HKe1.
    edestruct (step_by_val K) as [K'' HK]; eauto using val_head_stuck; simplify_eq/=.
    rewrite -fill_comp in HKe1; simplify_eq.
    exists (fill K'' e2'). rewrite fill_comp. split; [done|].
    destruct (head_ctx_step_val _ _ _ _ HhstepK) as [[]%not_eq_None_Some|HK''].
    { by eapply val_head_stuck. }
    subst. rewrite !fill_empty //.
  Qed.
*)

  (** Following lemma easily derived from head_prim_step_eq*)
  (** propose that we remove this *)
  (* Lemma head_reducible_prim_step e1 σ1 ρ : *)
  (*   head_reducible e1 σ1 → *)
  (*   prim_step e1 σ1 ρ > 0 → head_step e1 σ1 ρ > 0. *)
  (* Proof. *)
  (*   intros. destruct ρ. *)
  (*   edestruct (head_reducible_prim_step_ctx empty_ectx) as (?&?&?); *)
  (*     rewrite ?fill_empty; eauto. *)
  (*   by simplify_eq; rewrite fill_empty. *)
  (* Qed. *)
  

  (** Following lemma is true by definition *)
  (** propose that we remove this *)
  (* Lemma not_head_reducible_dzero e σ : *)
  (*   head_irreducible e σ → head_step e σ = dzero. *)
  (* Proof. *)
  (*   rewrite /reducible. *)
  (*   intros Hred%not_head_reducible. apply dzero_ext=> ρ. *)
  (*   destruct (Req_dec (head_step e σ ρ) 0); [done|]. *)
  (*   exfalso. apply Hred. *)
  (*   exists ρ. *)
  (*   pose proof (pmf_le_1 (head_step e σ) ρ). *)
  (*   pose proof (pmf_pos (head_step e σ) ρ). *)
  (*   lra. *)
  (* Qed. *)

  (* Every evaluation context is a context. *)
  Global Program Instance ectx_lang_ctx K : MeasLanguageCtx (curry fill K) := {
      K_measurable := _;
      fill_not_val e := _;
      fill_inj  := _;
      fill_dmap e1 σ1 := _
  }.
  Next Obligation. move=>Ki; apply curry_meas_fun. apply fill_meas. Qed. 
  Next Obligation. simpl. apply fill_not_val. Qed.
  Next Obligation. intros K e σ Hval.
                   eapply (fill_prim_step_dbind K e σ) in Hval.
                   erewrite <-gMap'_gMap.
                   simpl in *. by rewrite Hval.
  Qed.


  Record pure_head_step (e1 e2 : expr Λ) := {
    pure_head_step_safe σ1 : head_reducible e1 σ1;
    pure_head_step_det σ1 : is_det (e2, σ1) (head_step (e1, σ1))
  }.
  
  Lemma pure_head_step_pure_step e1 e2 : pure_head_step e1 e2 → pure_step e1 e2.
  Proof.
    intros [Hp1 Hp2]. split.
    - intros. apply head_prim_step. naive_solver.
    - intros σ. simpl. rewrite -/(prim_step (e1, σ)). erewrite head_prim_step_eq; naive_solver.
  Qed.

  (** This is not an instance because HeapLang's [wp_pure] tactic already takes
      care of handling the evaluation context.  So the instance is redundant.
      If you are defining your own language and your [wp_pure] works
      differently, you might want to specialize this lemma to your language and
      register that as an instance. *)
  Lemma pure_exec_fill K φ n e1 e2 :
    PureExec φ n e1 e2 →
    PureExec φ n (fill (K, e1)) (fill (K, e2)).
  Proof. apply: pure_exec_ctx. Qed.

End ectx_language.

Global Arguments ectx_lang : clear implicits.
Coercion ectx_lang : meas_ectxLanguage >-> meas_language.

(* This definition makes sure that the fields of the [language] record do not
refer to the projections of the [ectxLanguage] record but to the actual fields
of the [ectxLanguage] record. This is crucial for canonical structure search to
work.

Note that this trick no longer works when we switch to canonical projections
because then the pattern match [let '...] will be desugared into projections. *)

Program Definition MeasLanguageOfEctx (Λ : meas_ectxLanguage) : meas_language :=
  let '@MeasEctxLanguage _ _ _ _ exprT valT stateT ectxT _ _ _ _
        of_val to_val empty_ctx comp_ctx _ _ head_step mix := Λ in
  MeasLanguage _ _ _ (@ectx_lang_mixin (MeasEctxLanguage _ _ _ _ mix)).

Global Arguments MeasLanguageOfEctx : simpl never.
