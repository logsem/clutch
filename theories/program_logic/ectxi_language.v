(** An axiomatization of languages based on evaluation context items, including
    a proof that these are instances of general ectx-based languages. *)
From Coq Require Import Reals Psatz ClassicalEpsilon.
From Coq.Program Require Import Wf.
From stdpp Require Import decidable countable.
From iris.prelude Require Export prelude.
From self.prelude Require Import classical.
From self.program_logic Require Import language ectx_language.
From self.prob Require Import distribution.

(** TAKE CARE: When you define an [ectxiLanguage] canonical structure for your
language, you need to also define a corresponding [language] and [ectxLanguage]
canonical structure for canonical structure inference to work properly. You
should use the coercion [EctxLanguageOfEctxi] and [LanguageOfEctx] for that, and
not [ectxi_lang] and [ectxi_lang_ectx], otherwise the canonical projections will
not point to the right terms.

A full concrete example of setting up your language can be found in [heap_lang].
Below you can find the relevant parts:

  Module heap_lang.
    (* Your language definition *)

    Lemma heap_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
    Proof. (* ... *) Qed.
  End heap_lang.

  Canonical Structure heap_ectxi_lang := EctxiLanguage heap_lang.heap_lang_mixin.
  Canonical Structure heap_ectx_lang := EctxLanguageOfEctxi heap_ectxi_lang.
  Canonical Structure heap_lang := LanguageOfEctx heap_ectx_lang.
 *)

Section ectxi_language_mixin.
  Context {expr val ectx_item state : Type}.
  Context `{Countable expr, Countable state}.

  Context (of_val : val → expr).
  Context (to_val : expr → option val).

  Context (fill_item : ectx_item → expr → expr).
  Context (reshape_item : expr → option (ectx_item * expr)).
  Context (expr_ord : expr → expr → Prop).

  Context (head_step  : expr → state → distr (expr * state)).
  Context (state_step : state → distr state).

  Record EctxiLanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_stuck e1 σ1 ρ : head_step e1 σ1 ρ > 0 → to_val e1 = None;

    mixin_fill_item_val Ki e : is_Some (to_val (fill_item Ki e)) → is_Some (to_val e);
    (** [fill_item] is always injective on the expression for a fixed
        context. *)
    mixin_fill_item_inj Ki : Inj (=) (=) (fill_item Ki);
    (** [fill_item] with (potentially different) non-value expressions is
        injective on the context. *)
    mixin_fill_item_no_val_inj Ki1 Ki2 e1 e2 :
      to_val e1 = None → to_val e2 = None →
      fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2;

    (** a well-founded order on expressions *)
    mixin_expr_ord_wf : well_founded expr_ord;
    (** [reshape_item] produces "smaller" expressions (typically it will be
        structurally decreasing) *)
    mixin_reshape_ord Ki e e' : reshape_item e = Some (Ki, e') → expr_ord e' e;

    mixin_reshape_fill_item Ki e e' : reshape_item e = Some (Ki, e') → fill_item Ki e' = e;
    mixin_reshape_item_head e σ ρ : head_step e σ ρ > 0 → reshape_item e = None;
    (* mixin_reshape_item_None e : reshape_item e = None → is_Some (to_val e); *)
    (* mixin_reshape_item_fill_comp e e' e'' K K' K'' : *)
    (*   reshape_item e = Some (Ki', e') → reshape_item (fill_item Ki e) = Some (Ki'', e'') → K'' = comp_ectx K K' ∧ e' = e'';       *)

    (** If [fill_item Ki e] takes a head step, then [e] is a value (unlike for
        [ectx_language], an empty context is impossible here).  In other words,
        if [e] is not a value then wrapping it in a context does not add new
        head redex positions. *)
    mixin_head_ctx_step_val Ki e σ1 ρ :
      head_step (fill_item Ki e) σ1 ρ > 0 → is_Some (to_val e);
  }.
End ectxi_language_mixin.

Structure ectxiLanguage := EctxiLanguage {
  expr : Type;
  val : Type;
  ectx_item : Type;
  state : Type;

  expr_eqdec : EqDecision expr;
  state_eqdec : EqDecision state;
  expr_countable : Countable expr;
  state_countable : Countable state;

  of_val : val → expr;
  to_val : expr → option val;

  fill_item : ectx_item → expr → expr;
  reshape_item : expr → option (ectx_item * expr);
  expr_ord : expr → expr → Prop;

  head_step : expr → state → distr (expr * state);
  state_step : state → distr state;

  ectxi_language_mixin :
    EctxiLanguageMixin of_val to_val fill_item reshape_item expr_ord head_step
}.

#[global] Existing Instance expr_eqdec.
#[global] Existing Instance state_eqdec.
#[global] Existing Instance expr_countable.
#[global] Existing Instance state_countable.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Global Arguments EctxiLanguage {_ _ _ _ _ _ _ _ _} _.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments fill_item {_} _ _.
Global Arguments reshape_item {_} _.
Global Arguments expr_ord {_} _ _.
Global Arguments head_step {_} _ _.
Global Arguments state_step {_} _.

Section ectxi_language.
  Context {Λ : ectxiLanguage}.
  Implicit Types (e : expr Λ) (Ki : ectx_item Λ).
  Notation ectx := (list (ectx_item Λ)).

  (* Only project stuff out of the mixin that is not also in ectxLanguage *)
  Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. apply ectxi_language_mixin. Qed.
  Lemma fill_item_val Ki e : is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. apply ectxi_language_mixin. Qed.
  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof. apply ectxi_language_mixin. Qed.
  Lemma expr_ord_wf : well_founded (@expr_ord Λ).
  Proof. apply ectxi_language_mixin. Qed.
  Lemma reshape_ord Ki e e' :
    reshape_item e = Some (Ki, e') → expr_ord e' e.
  Proof. apply ectxi_language_mixin. Qed.
  Lemma reshape_fill_item e e' Ki :
    reshape_item e = Some (Ki, e') → fill_item Ki e' = e.
  Proof. apply ectxi_language_mixin. Qed.
  Lemma reshape_item_head e σ ρ :
    head_step e σ ρ > 0 → reshape_item e = None.
  Proof. apply ectxi_language_mixin. Qed.
  Lemma head_ctx_step_val Ki e σ1 ρ :
    head_step (fill_item Ki e) σ1 ρ > 0 → is_Some (to_val e).
  Proof. apply ectxi_language_mixin. Qed.

  Definition fill (K : ectx) (e : expr Λ) : expr Λ := foldl (flip fill_item) e K.

  Lemma fill_app (K1 K2 : ectx) e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
  Proof. apply foldl_app. Qed.

  Program Fixpoint reshape (e : expr Λ) {wf expr_ord e} : ectx * expr Λ :=
    match reshape_item e with
    | Some (Ki, e') => let '(K, e'') := reshape e' in (K ++ [Ki], e'')
    | None => ([], e)
    end.
  Solve Obligations with eauto using reshape_ord, expr_ord_wf.

  
  (* Program Fixpoint reshape_aux (e : expr Λ) (K : ectx) {wf expr_ord e} : ectx * expr Λ := *)
  (*   match reshape_item e with *)
  (*   | Some (Ki, e') => reshape_aux e' (Ki :: K) *)
  (*   | None => (K, e) *)
  (*   end. *)
  (* Solve Obligations with eauto using reshape_ord, expr_ord_wf. *)
  (* Definition reshape (e : expr Λ)  : ectx * expr Λ := *)
  (*   let '(K, e) := reshape_aux e [] in (reverse K, e). *)

  (* Axiom reshape_item_None : ∀ e, reshape_item e = None → to_val e = None. *)


  Lemma reshape_inv_nil e e' :
    reshape e = ([], e') → reshape_item e = None ∧ e = e'.
  Proof.
    rewrite /reshape WfExtensionality.fix_sub_eq_ext /= -/reshape.
    destruct (reshape_item e) as [[Ki e'']| e''] eqn:Heq; [|by intros [=]].
    destruct (reshape e''). intros [= Hl He].
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
    - intros [=]; destruct l1; simplify_eq.
    - intros [= -> []%IHl1]. simplify_eq=>//.
  Qed.

  Search rev_ind.

  Lemma snoc_case {A} (xs : list A) : xs = [] ∨ ∃ x xs', xs = xs' ++ [x].
  Proof. induction xs using rev_ind; eauto. Qed.

  Lemma reshape_inv_cons Ki K e e'' :
    reshape e = (K ++ [Ki], e'') → ∃ e', reshape_item e = Some (Ki, e') ∧ reshape e' = (K, e'').
  Proof.
    rewrite /reshape WfExtensionality.fix_sub_eq_ext /= -/reshape.
    destruct (reshape_item e) as [[Ki' e']|] eqn:Heq'.
    2 : { intros [=]. by destruct K. }
    destruct (reshape e') as [K' e'''] eqn:Heq.
    intros [= [<- <-]%list_snoc_singleton_inv ->].
    eauto.
  Qed.

  #[local] Lemma reshape_fill K e e' : reshape e = (K, e') → fill K e' = e.
  Proof.
    revert e e'; induction K as [|Ki K] using rev_ind; intros e e'.
    { intros [? ->]%reshape_inv_nil=>//. }
    intros (e'' & Hrei%reshape_fill_item & Hre)%reshape_inv_cons.
    rewrite fill_app /= (IHK e'') //.
  Qed.

  (* Axiom bar : ∀e Ki, reshape_item (fill_item Ki e) = Some (Ki, e). *)

  Lemma foo K Ki e :
    reshape (fill K e) = (K, e) →
    reshape (fill_item Ki (fill K e)) = (K ++ [Ki], e).
  Proof.
    (* intros Hr.  *)
    (* rewrite /reshape WfExtensionality.fix_sub_eq_ext /= -/reshape. *)
    (* case_match eqn:Heq. *)
    (* 2 : {  *)


    (* revert Ki e. induction K as [|Ki' K] using rev_ind; intros Ki e He=>/=.  *)
    (* - rewrite /reshape WfExtensionality.fix_sub_eq_ext /= -/reshape. *)
    (*   rewrite bar He //. *)
    (* -  *)
    (*   rewrite fill_app /=.  *)
    (*   rewrite fill_app /= in He. *)
    (*   specialize (IHK Ki). *)
    (*   eapply IHK. *)
    (*   rewrite -app_assoc.  *)

    (*   destruct (reshape_item (fill_item Ki e)) as [[Ki' e']|] eqn:Heq. *)
    (*   + destruct (reshape e') as [K' e'']. *)
    (*     apply reshape_fill_item in Heq.  *)


    (* destruct (reshape_item (fill_item Ki (fill K e))) as [[Ki' e']|] eqn:Heq. *)
    (* - apply reshape_fill_item in Heq.  *)
    (*   destruct (reshape e') as [K' e'']. *)


  Admitted.

  Lemma reshape_filled e K :
    reshape_item e = None → reshape (fill K e) = (K, e).
  Proof.
    revert e; induction K as [|Ki K] using rev_ind; intros e.
    - rewrite /reshape WfExtensionality.fix_sub_eq_ext /= -/reshape. intros ->=>//.
    - intros Hre. rewrite fill_app /=. apply foo; eauto.
  Qed.

  Definition ectxi_lang_ectx_mixin :
    EctxLanguageMixin of_val to_val [] (flip (++)) fill reshape head_step.
  Proof.
    assert (fill_val : ∀ K e, is_Some (to_val (fill K e)) → is_Some (to_val e)).
    { intros K. induction K as [|Ki K IH]=> e //=. by intros ?%IH%fill_item_val. }
    assert (fill_not_val : ∀ K e, to_val e = None → to_val (fill K e) = None).
    { intros K e. rewrite !eq_None_not_Some. eauto. }
    split.
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - done.
    - intros K1 K2 e. by rewrite /fill /= foldl_app.
    - intros K; induction K as [|Ki K IH]; rewrite /Inj; naive_solver.
    - done.
    - apply reshape_fill.
    - intros e e' K σ ρ Hs.
      destruct (snoc_case K) as [-> | (Ki & K' & ->)].
      { intros [? <-]%reshape_inv_nil=>//. }
      intros (e'' & Hrei & Hre)%reshape_inv_cons.
      apply reshape_item_head in Hs. simplify_eq.
    - intros e e' K K'. revert K.
      induction K' as [|Ki K'] using rev_ind.
      { intros K [? <-]%reshape_inv_nil. simpl. by apply reshape_filled. }
      admit.
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
  Admitted.

  Canonical Structure ectxi_lang_ectx := EctxLanguage ectxi_lang_ectx_mixin.
  Canonical Structure ectxi_lang := LanguageOfEctx ectxi_lang_ectx.

  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Lemma ectxi_language_sub_redexes_are_values e :
    (∀ Ki e', e = fill_item Ki e' → is_Some (to_val e')) →
    sub_redexes_are_values e.
  Proof.
    intros Hsub K e' ->. destruct K as [|Ki K _] using @rev_ind=> //=.
    intros []%eq_None_not_Some. eapply fill_val, Hsub. by rewrite /= fill_app.
  Qed.

  Global Instance ectxi_lang_ctx_item Ki : LanguageCtx (fill_item Ki).
  Proof. change (LanguageCtx (fill [Ki])). apply _. Qed.
End ectxi_language.

Global Arguments ectxi_lang_ectx : clear implicits.
Global Arguments ectxi_lang : clear implicits.
Coercion ectxi_lang_ectx : ectxiLanguage >-> ectxLanguage.
Coercion ectxi_lang : ectxiLanguage >-> language.

Definition EctxLanguageOfEctxi (Λ : ectxiLanguage) : ectxLanguage :=
  let '@EctxiLanguage E V C St K of_val to_val fill head mix := Λ in
  @EctxLanguage E V (list C) St K of_val to_val _ _ _ _
    (@ectxi_lang_ectx_mixin (@EctxiLanguage E V C St K of_val to_val fill head mix)).

Global Arguments EctxLanguageOfEctxi : simpl never.
