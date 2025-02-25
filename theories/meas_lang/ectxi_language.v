(** An axiomatization of languages based on evaluation context items, including
    a proof that these are instances of general ectx-based languages. *)
Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz Logic.FunctionalExtensionality Program.Wf Reals.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp classical_sets.
From iris.prelude Require Import options.
From iris.algebra Require Import ofe.
From clutch.bi Require Import weakestpre.
From mathcomp.analysis Require Import reals measure ereal Rstruct.
From clutch.prob.monad Require Export giry meas_markov.
From clutch.meas_lang Require Import language ectx_language.
Set Warnings "hiding-delimiting-key".


Section ectxi_language_mixin.
  Local Open Scope classical_set_scope.

  Context {d_expr d_val d_state d_ectx_item: measure_display}.
  Context {expr : measurableType d_expr}.
  Context {val : measurableType d_val}.
  Context {state : measurableType d_state}.

  Context {ectx_item : measurableType d_ectx_item}.

  Context (of_val : val → expr).

  Context (to_val : expr → option val).

  Context (fill_item : (ectx_item * expr)%type -> expr).

  Context (decomp_item : expr → option (ectx_item * expr)%type).

  Context (expr_ord : expr → expr → Prop).

  Context (head_step : (expr * state)%type -> (giryM (expr * state)%type)).

  Record MeasEctxiLanguageMixin := {
    mixin_of_val_meas : measurable_fun setT of_val;
    mixin_to_val_meas : measurable_fun setT to_val;
    mixin_fill_item_meas : measurable_fun setT fill_item;
    mixin_decomp_item_meas : measurable_fun setT decomp_item;
    mixin_head_step_meas : measurable_fun setT head_step;

    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_stuck e1 σ1 : (¬ (is_zero (head_step (e1, σ1)))) → to_val e1 = None;
    mixin_prim_step_mass e σ : (¬ is_zero (head_step (e, σ))) -> is_prob (head_step (e, σ))  ;

    mixin_fill_item_val Ki e : is_Some (to_val (fill_item (Ki, e))) → is_Some (to_val e);
    (** [fill_item] is always injective on the expression for a fixed
        context. *)
    mixin_fill_item_inj Ki : Inj (=) (=) ((curry fill_item) Ki);
    (** [fill_item] with (potentially different) non-value expressions is
        injective on the context. *)
    mixin_fill_item_no_val_inj Ki1 Ki2 e1 e2 :
      to_val e1 = None → to_val e2 = None →
      fill_item (Ki1, e1) = fill_item (Ki2, e2) → Ki1 = Ki2;

    (** a well-founded order on expressions *)
    mixin_expr_ord_wf : well_founded expr_ord;
    (** [decomp_item] produces "smaller" expressions (typically it will be
        structurally decreasing) *)
    mixin_decomp_ord Ki e e' : decomp_item e = Some (Ki, e') → expr_ord e' e;
    mixin_decomp_fill_item Ki e :
      to_val e = None → decomp_item (fill_item (Ki, e)) = Some (Ki, e);
    mixin_decomp_fill_item_2 e e' Ki :
      decomp_item e = Some (Ki, e') → fill_item (Ki, e') = e ∧ to_val e' = None;

    (** If [fill_item Ki e] takes a head step, then [e] is a value (unlike for
        [ectx_language], an empty context is impossible here).  In other words,
        if [e] is not a value then wrapping it in a context does not add new
        head redex positions. *)
    mixin_head_ctx_step_val Ki e σ1 :
      (¬ is_zero (head_step ((fill_item (Ki, e)), σ1))) → is_Some (to_val e);
  }.
End ectxi_language_mixin.


Structure meas_ectxiLanguage := MeasEctxiLanguage {
  d_expr : measure_display;
  d_val : measure_display;
  d_state : measure_display;
  d_ectx_item : measure_display;
  expr : measurableType d_expr;
  val : measurableType d_val;
  state : measurableType d_state;
  ectx_item : measurableType d_ectx_item;
  of_val : val → expr;
  to_val : expr → option val;
  fill_item : (ectx_item * expr)%type -> expr;
  decomp_item : expr → option (ectx_item * expr)%type;
  expr_ord : expr → expr → Prop;
  head_step : (expr * state)%type -> (giryM (expr * state)%type);
  ectxi_language_mixin :
    MeasEctxiLanguageMixin of_val to_val fill_item decomp_item expr_ord head_step
}.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Global Arguments MeasEctxiLanguage {_ _ _ _ _ _ _ _ _ _ _ _ _} _.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments fill_item {_} _.
Global Arguments decomp_item {_} _.
Global Arguments expr_ord {_} _ _.
Global Arguments head_step {_}.

Section ectxi_language.
  Context {Λ : meas_ectxiLanguage}.
  Implicit Types (e : expr Λ) (Ki : ectx_item Λ).
  Notation ectx := (list (ectx_item Λ)).

  (* Only project stuff out of the mixin that is not also in ectxLanguage *)
  Lemma fill_item_meas : measurable_fun setT (@fill_item Λ).
  Proof. apply ectxi_language_mixin. Qed.
  Lemma decomp_item_meas : measurable_fun setT (@decomp_item Λ).
  Proof. apply ectxi_language_mixin. Qed.
  Lemma head_step_meas : measurable_fun setT (@head_step Λ).
  Proof. apply ectxi_language_mixin. Qed.

  Global Instance fill_item_inj Ki : Inj (=) (=) ((curry fill_item) Ki).
  Proof. apply ectxi_language_mixin. Qed.
  Lemma fill_item_val Ki e : is_Some (to_val (fill_item (Ki, e))) → is_Some (to_val e).
  Proof. apply ectxi_language_mixin. Qed.
  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item (Ki1, e1) = fill_item (Ki2, e2) → Ki1 = Ki2.
  Proof. apply ectxi_language_mixin. Qed.
  Lemma expr_ord_wf : well_founded (@expr_ord Λ).
  Proof. apply ectxi_language_mixin. Qed.
  Lemma decomp_ord Ki e e' :
    decomp_item e = Some (Ki, e') → expr_ord e' e.
  Proof. apply ectxi_language_mixin. Qed.
  Lemma decomp_fill_item e Ki :
    to_val e = None → decomp_item (fill_item (Ki, e)) = Some (Ki, e).
  Proof. apply ectxi_language_mixin. Qed.
  Lemma decomp_fill_item_2 e e' Ki :
    decomp_item e = Some (Ki, e') → fill_item (Ki, e') = e ∧ to_val e' = None.
  Proof. apply ectxi_language_mixin. Qed.
  Lemma head_ctx_step_val Ki e σ1 :
    (¬ is_zero (head_step ((fill_item (Ki, e)), σ1))) → is_Some (to_val e).
  Proof. apply ectxi_language_mixin. Qed.
  Lemma fill_item_not_val K e : to_val e = None → to_val (fill_item (K, e)) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_item_val. Qed.


  (*
  (* Shoule be easier to show this is measurable *)
  (* Still can't makke is measurable by construction due to the nonstructural recursion, but I can do that
   in the next step. *)
  Program Fixpoint fill_pre (x : (ectx * expr Λ)%type) {measure (length x.1)} : expr Λ :=
    match x.1 with
    | [] => snd x
    | (_ :: _) => fill_item (𝜋_cons_v (fst x), fill_pre (𝜋_cons_vs (fst x), (snd x)))
    end.
  Next Obligation.
    intros.
    unfold filtered_var in Heq_anonymous.
    rewrite <- Heq_anonymous.
    rewrite /𝜋_cons_vs//=.
    by apply Nat.lt_succ_diag_r.
  Qed.
  Next Obligation.
    unfold well_founded.
    intro l.
    destruct l as (ll, lv).
    induction ll as [|l' IH].
    { admit. }
    { admit. }
  Admitted.
   *)

  Definition fill (K : (ectx * expr Λ)%type) : expr Λ := foldl (fun e' k => fill_item (k, e')) (snd K) (fst K).

  Lemma fill_measurable : measurable_fun setT fill.
  Proof.
    (* Stratify by shape of ectx (AKA length) and do induction. *)
  Admitted.
  Hint Resolve fill_measurable : measlang.



  Lemma fill_app (K1 K2 : ectx) e : fill ((K1 ++ K2), e) = fill (K2, (fill (K1, e))).
  Proof. apply foldl_app. Qed.

  Lemma fill_cons (k : ectx_item Λ) (K2 : ectx) e : fill ((k :: K2), e) = fill (K2, (fill ([k], e))).
  Proof. apply (fill_app [k] K2). Qed.

  Program Fixpoint decomp (e : expr Λ) {wf expr_ord e} : ectx * expr Λ :=
    match decomp_item e with
    | Some (Ki, e') => let '(K, e'') := decomp e' in (K ++ [Ki], e'')
    | None => ([], e)
    end.
  Solve Obligations with eauto using decomp_ord, expr_ord_wf.


  (* How to prove this? *)
  Lemma decomp_measurable : measurable_fun setT decomp.
  Proof.
  Admitted.
  Hint Resolve decomp_measurable : measlang.


  Lemma decomp_unfold e :
    decomp e =
      match decomp_item e with
      | Some (Ki, e') => let '(K, e'') := decomp e' in (K ++ [Ki], e'')
      | None => ([], e)
      end.
  Proof.
    rewrite /decomp WfExtensionality.fix_sub_eq_ext /= -/decomp.
    repeat case_match; try done.
  Qed.

  Lemma decomp_inv_nil e e' :
    decomp e = ([], e') → decomp_item e = None ∧ e = e'.
  Proof.
    rewrite decomp_unfold.
    destruct (decomp_item e) as [[Ki e'']|] eqn:Heq; [|by intros [=]].
    destruct (decomp e''). intros [= Hl He].
    assert (l = []) as ->.
    { destruct l; inversion Hl. }
    inversion Hl.
  Qed.

  (* TODO: move *)
  Lemma list_snoc_singleton_inv {A} (l1 l2 : list A) (a1 a2 : A) :
    l1 ++ [a1] = l2 ++ [a2] → l1 = l2 ∧ a1 = a2.
  Proof.
    revert l2. induction l1 as [|a l1].
    { intros [| ? []] [=]=>//. }
    intros [].
    { intros [=]; destruct l1; simplify_eq. }
    { intros [= -> []%IHl1]. simplify_eq=>//. }
  Qed.

  Lemma decomp_inv_cons Ki K e e'' :
    decomp e = (K ++ [Ki], e'') → ∃ e', decomp_item e = Some (Ki, e') ∧ decomp e' = (K, e'').
  Proof.
    rewrite decomp_unfold.
    destruct (decomp_item e) as [[Ki' e']|] eqn:Heq'.
    2 : { intros [=]. by destruct K. }
    destruct (decomp e') as [K' e'''] eqn:Heq.
    intros [= [<- <-]%list_snoc_singleton_inv ->].
    eauto.
  Qed.

  Lemma decomp_fill K e e' : decomp e = (K, e') → fill (K, e') = e.
  Proof. Admitted.

  Lemma decomp_to_val_emp K e e' : decomp e = (K, e') → is_Some (to_val e') → K = [].
  Proof. Admitted.

  (* FIXME: Rename *)
  Lemma decomp_lemma_1 e e' K K' :  to_val e = None → decomp e = (K', e') → decomp (fill (K, e)) = (flip app K K', e').
  Proof. Admitted.


  Lemma decomp_lemma_2 K' K_redex e1' e1_redex σ1  :
    fill (K', e1') = fill (K_redex, e1_redex)
    → to_val e1' = None
      → ¬ is_zero (head_step (e1_redex, σ1))
        → ∃ K'' , K_redex = flip app K' K''.
  Proof. Admitted.


  Lemma decomp_lemma_3 K e σ1 : ¬ is_zero (head_step (fill (K, e), σ1)) → is_Some (to_val e) ∨ K = [].
  Proof. Admitted.

  Definition meas_ectxi_lang_ectx_mixin :
    MeasEctxLanguageMixin of_val to_val head_step [] (flip (++)) fill decomp.
  Proof.
    assert (fill_val : ∀ K e, is_Some (to_val (curry fill K e)) → is_Some (to_val e)).
    { intros K. induction K as [|Ki K IH]=> e //=. by intros ?%IH%fill_item_val. }
    assert (fill_not_val : ∀ K e, to_val e = None → to_val (curry fill K e) = None).
    { intros K e. rewrite !eq_None_not_Some. eauto. }
    split.
    { by apply ectxi_language_mixin. }
    { by apply ectxi_language_mixin. }
    { admit. (* by apply ectxi_language_mixin. (* Works but is hella slow. Why?  *) *) }
    { by apply fill_measurable. }
    { by apply decomp_measurable. }
    { by apply ectxi_language_mixin. }
    { by apply ectxi_language_mixin. }
    { by apply ectxi_language_mixin. }
    { by apply ectxi_language_mixin. }
    { done. }
    { intros K1 K2 e. by rewrite /fill /= foldl_app. }
    { intros K.
      induction K as [|Ki K IH]; rewrite /Inj.
      { done. }
      { move=> x y.
        unfold curry.
        rewrite fill_cons.
        unfold curry in IH.
        move=> H.
        apply IH in H.
        rewrite /fill//= in H.
        have H' := fill_item_inj Ki x y.
        apply H'.
        by rewrite /curry. }
    }
    { done. }
    { by apply decomp_fill. }
    { by apply decomp_to_val_emp. }
    { by apply decomp_lemma_1. }
    { by apply decomp_lemma_2. }
    { by apply decomp_lemma_3. }
     

    (*
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - done.
    - intros K1 K2 e. by rewrite /fill /= foldl_app.
    - intros K; induction K as [|Ki K IH]; rewrite /Inj; naive_solver.
    - done.

      ------------

    - induction K as [|Ki K] using rev_ind; intros e e'.
      { intros [? ->]%decomp_inv_nil=>//. }
      intros (e'' & Hrei & Hre)%decomp_inv_cons.
      rewrite fill_app /= (IHK e'') //.
      by apply decomp_fill_item_2.
    - intros K. induction K as [|Ki K] using rev_ind; [done|].
      intros ?? (e'' & Hrei & Hre)%decomp_inv_cons Hv.
      specialize (IHK _ _ Hre Hv). simplify_eq.
      apply decomp_inv_nil in Hre as [? ?]; simplify_eq.
      by apply decomp_fill_item_2 in Hrei as [_ ?%eq_None_not_Some].
    - intros e e' K K'. revert K' e e'.
      induction K as [|Ki K] using rev_ind.
      { intros ??? =>/=. rewrite app_nil_r //. }
      intros K' e e' Hval Hre. rewrite fill_app /=.
      rewrite decomp_unfold.
      rewrite decomp_fill_item; [|auto using fill_item_not_val].
      rewrite (IHK K' _ e') //=.
      rewrite !app_assoc //.
    - intros K K' e1 e1' σ1 [e2 σ2] Hfill Hred Hstep; revert K' Hfill.
      induction K as [|Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r.
      destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
      { rewrite fill_app in Hstep. apply head_ctx_step_val in Hstep.
        apply fill_val in Hstep. by apply not_eq_None_Some in Hstep. }
      rewrite !fill_app /= in Hfill.
      assert (Ki = Ki') as ->.
      { eapply fill_item_no_val_inj, Hfill; eauto using val_head_stuck.
        apply fill_not_val. revert Hstep. apply ectxi_language_mixin. }
      simplify_eq. destruct (IH K') as [K'' ->]; auto.
      exists K''. by rewrite assoc.
    - intros K e1 σ1 [e2 σ2].
      destruct K as [|Ki K _] using rev_ind; simpl; first by auto.
      rewrite fill_app /=.
      intros ?%head_ctx_step_val; eauto using fill_val.
     *)
  Admitted.



  Canonical Structure meas_ectxi_lang_ectx := MeasEctxLanguage meas_ectxi_lang_ectx_mixin.
  Canonical Structure meas_ectxi_lang := MeasLanguageOfEctx meas_ectxi_lang_ectx.

  Lemma fill_not_val K e : to_val e = None → to_val (fill (K, e)) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Lemma ectxi_language_sub_redexes_are_values e :
    (∀ Ki e', e = fill_item (Ki, e') → is_Some (to_val e')) →
    sub_redexes_are_values e.
  Proof.
    intros Hsub K e' ->. destruct K as [|Ki K _] using @rev_ind=> //=.
    intros []%eq_None_not_Some. eapply fill_val, Hsub. by rewrite /= fill_app.
  Qed.

  Global Program Instance ectxi_lang_ctx_item Ki : MeasLanguageCtx ((curry fill_item) Ki) := {
      K_measurable := _;
      fill_not_val e := _;
      fill_inj  := _;
      fill_dmap e1 σ1 := _
  }.
  Next Obligation. by move=>Ki; apply (curry_meas_fun R), fill_item_meas. Qed.
  Next Obligation. Admitted.
  Next Obligation. Admitted.

End ectxi_language.

Global Arguments meas_ectxi_lang_ectx : clear implicits.
Global Arguments meas_ectxi_lang : clear implicits.
Coercion meas_ectxi_lang_ectx : meas_ectxiLanguage >-> meas_ectxLanguage.
Coercion meas_ectxi_lang : meas_ectxiLanguage >-> meas_language.

Program Definition MeasEctxLanguageOfEctxi (Λ : meas_ectxiLanguage) : meas_ectxLanguage :=
 let '@MeasEctxiLanguage _ _ _ _ expr val state ectx_item of_val to_val fill_item decomp_item expr_old head_step mix := Λ in
 MeasEctxLanguage (@meas_ectxi_lang_ectx_mixin Λ).

Global Arguments MeasEctxLanguageOfEctxi : simpl never.
