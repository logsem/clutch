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
From mathcomp.analysis Require Import measure ereal.
From clutch.prob.monad Require Export giry meas_markov.
From clutch.meas_lang Require Import language ectx_language prelude.

Require Import mathcomp.reals_stdlib.Rstruct.
Require Import mathcomp.reals.reals.
Set Warnings "hiding-delimiting-key".


Section ectxi_language_mixin.
  Local Open Scope classical_set_scope.
  Context {d_expr d_val d_state d_ectx_item: measure_display}.
  Context {exprT valT stateT ectx_itemT: Type}.
  Context `{SigmaAlgebra d_expr exprT}.
  Context `{SigmaAlgebra d_val valT}.
  Context `{SigmaAlgebra d_state stateT}.
  Context `{SigmaAlgebra d_ectx_item ectx_itemT}.
  Notation val := (toPackedType d_val valT).
  Notation expr := (toPackedType d_expr exprT).
  Notation state := (toPackedType d_state stateT).
  Notation ectx_item := (toPackedType d_ectx_item ectx_itemT).
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

    mixin_expr_meas_points : forall (e : expr), measurable [set e];
    mixin_val_meas_points : forall (v : val), measurable [set v];
    mixin_state_meas_points : forall (v : state), measurable [set v];

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
  d_val: measure_display;
  d_state: measure_display;
  d_ectx_item: measure_display;
  exprT : Type;
  valT : Type;
  stateT : Type;
  ectx_itemT : Type;
  expr_SigmaAlgebra : SigmaAlgebra d_expr exprT;
  val_SigmaAlgebra : SigmaAlgebra d_val valT;
  state_SigmaAlgebra : SigmaAlgebra d_state stateT;
  ectx_item_SigmaAlgebra : SigmaAlgebra d_ectx_item ectx_itemT;

  of_val : (toPackedType d_val valT) → (toPackedType d_expr exprT);
  to_val : (toPackedType d_expr exprT) → option (toPackedType d_val valT);

  fill_item : ((toPackedType d_ectx_item ectx_itemT) * (toPackedType d_expr exprT))%type -> (toPackedType d_expr exprT);
  decomp_item : (toPackedType d_expr exprT) → option ((toPackedType d_ectx_item ectx_itemT) * (toPackedType d_expr exprT))%type;
  expr_ord : (toPackedType d_expr exprT) → (toPackedType d_expr exprT) → Prop;

  head_step : ((toPackedType d_expr exprT) * (toPackedType d_state stateT))%type -> (giryM ((toPackedType d_expr exprT) * (toPackedType d_state stateT))%type);
  ectxi_language_mixin :
    MeasEctxiLanguageMixin of_val to_val fill_item decomp_item expr_ord head_step
}.

Bind Scope expr_scope with exprT.
Bind Scope val_scope with valT.

#[global] Existing Instance expr_SigmaAlgebra.
#[global] Existing Instance val_SigmaAlgebra.
#[global] Existing Instance state_SigmaAlgebra.
#[global] Existing Instance ectx_item_SigmaAlgebra.

Notation val Λ := (toPackedType (d_val Λ) (valT Λ)).
Notation expr Λ := (toPackedType (d_expr Λ) (exprT Λ)).
Notation state Λ := (toPackedType (d_state Λ) (stateT Λ)).
Notation ectx_item Λ := (toPackedType (d_ectx_item Λ) (ectx_itemT Λ)).

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

  
  Local Open Scope classical_set_scope.
  Lemma fill_measurable : measurable_fun setT fill.
  Proof with ms_solve; apply list_length_cov_meas_set.
    rewrite /fill.
    assert (setT (T:=ectx* _) = \bigcup_n  (list_length_cov n `*` setT)) as ->.
    { rewrite eqEsubset; split; intros [l s]; simpl; last done.
      intros _.
      exists (length l); first done.
      simpl. split; last done. apply: list_length_cov_length'.
    }
    apply measurable_fun_bigcup.
    { intros. ms_solve. apply list_length_cov_meas_set. }
    intros n; induction n as [|n IHn].
    { simpl. apply: (mathcomp_measurable_fun_ext _ _ (snd)).
      - ms_solve. apply list_length_cov_meas_set.
      - apply: measurable_snd_restriction.
        ms_solve. apply list_length_cov_meas_set.
      - rewrite list_length_cov_0/list_cov_empty. intros []. simpl. by intros [->].
    }
    apply: (mathcomp_measurable_fun_ext _ _ ((λ K : list (ectx_item Λ) * expr Λ,
                                                foldl (λ e' (k : ectx_item Λ), fill_item (k, e')) K.2 K.1) \o (𝜋_cons_vs \o fst △ (fill_item \o (𝜋_cons_v \o fst △ snd))))).
    - ms_solve. apply list_length_cov_meas_set.
    - apply: measurable_comp; [| |apply:IHn |].
      + ms_solve. apply list_length_cov_meas_set.
      + rewrite list_length_cov_Sn. intros [l s]. rewrite /list_cov_cons.
        simpl.
        intros [[][[[?[]]]]]; simpl in *; subst; simpl in *; simplify_eq. naive_solver.
      + mf_prod.
        * ms_solve. apply list_length_cov_meas_set.
        * apply: measurable_comp; [| |apply:𝜋_cons_vs_meas_fun|].
          -- apply list_cov_cons_meas_set.
          -- rewrite list_length_cov_Sn. intros ?. simpl. intros [?[[]]]; by subst.
          -- apply: measurable_fst_restriction. idtac...
        * apply: measurable_compT.
          -- ms_solve. apply list_length_cov_meas_set.
          -- apply fill_item_meas.
          -- mf_prod; last apply: measurable_snd_restriction.
             ++ idtac...
             ++ apply:  measurable_comp; last apply: measurable_fst_restriction; last first.
                ** idtac...
                ** apply 𝜋_cons_v_meas_fun.
                ** rewrite list_length_cov_Sn. intros ?. simpl.
                   intros [[][[]]]; by subst.
                ** apply list_cov_cons_meas_set.
             ++ idtac...
    - rewrite list_length_cov_Sn. intros []. simpl. rewrite /list_cov_cons/=.
      intros [[[?[]]]]; by subst.
  Qed. 
  Hint Resolve fill_measurable : measlang.


  Lemma fill_app (K1 K2 : ectx) e : fill ((K1 ++ K2), e) = fill (K2, (fill (K1, e))).
  Proof. apply foldl_app. Qed.

  Lemma fill_cons (k : ectx_item Λ) (K2 : ectx) e : fill ((k :: K2), e) = fill (K2, (fill ([k], e))).
  Proof. apply (fill_app [k] K2). Qed.

  Lemma fill_not_val K e : to_val e = None → to_val (fill (K, e)) = None.
  Proof.
    revert e.
    induction K as [|Ki K] using rev_ind; simpl; first naive_solver.
    intros e Hval; rewrite fill_app/=.
    apply fill_item_not_val. naive_solver.
  Qed.

  Program Fixpoint decomp (e : expr Λ) {wf expr_ord e} : ectx * expr Λ :=
    match decomp_item e with
    | Some (Ki, e') => let '(K, e'') := decomp e' in (K ++ [Ki], e'')
    | None => ([], e)
    end.
  Solve Obligations with eauto using decomp_ord, expr_ord_wf.

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
  Proof.
    remember (length K) as n eqn:Heqn.
    revert K e e' Heqn.
    induction n as [|n IHn]; intros K e e' Hn.
    - assert (K= []) as ->.
      { destruct K; simpl in *; first done. lia. }
      intros H. apply decomp_inv_nil in H as [? ->].
      by rewrite /fill.
    - rewrite decomp_unfold.
      case_match; last first.
      { intros; simplify_eq. }
      repeat case_match. simplify_eq.
      intros; simplify_eq.
      rewrite fill_app. apply decomp_fill_item_2.
      etrans; first exact.
      f_equal. f_equal.
      simpl. symmetry. apply IHn; last done.
      rewrite app_length in Hn. simpl in *. lia.
  Qed.

  Lemma decomp_to_val_emp K e e' : decomp e = (K, e') → is_Some (to_val e') → K = [].
  Proof.
    revert e e'. induction K as [|Ki K] using rev_ind; [done|].
    intros ?? (e'' & Hrei & Hre)%decomp_inv_cons Hv.
    specialize (IHK _ _ Hre Hv). simplify_eq.
    apply decomp_inv_nil in Hre as [? ?]; simplify_eq.
    by apply decomp_fill_item_2 in Hrei as [_ ?%eq_None_not_Some].
  Qed.

  Lemma decomp_fill_comp e e' K K' :  to_val e = None → decomp e = (K', e') → decomp (fill (K, e)) = (flip app K K', e').
  Proof.
    revert K' e e'.
    induction K as [|Ki K] using rev_ind.
    { intros ??? =>/=. rewrite app_nil_r //. }
    intros K' e e' Hval Hre. rewrite fill_app /=.
    rewrite decomp_unfold.
    rewrite decomp_fill_item.
    - rewrite (IHK K' _ e') //=.
      rewrite !app_assoc //.
    - simpl. by apply fill_not_val.
  Qed.

  Lemma decomp_step_by_val K' K_redex e1' e1_redex σ1  :
    fill (K', e1') = fill (K_redex, e1_redex)
    → to_val e1' = None
      → ¬ is_zero (head_step (e1_redex, σ1))
        → ∃ K'' , K_redex = flip app K' K''.
  Proof.
    revert K_redex  e1' e1_redex σ1.
    induction K' as [|Ki K IH] using rev_ind => /= K' e1' e1_redex σ1 Hfill; eauto using app_nil_r.
    destruct K' as [|Ki' K' _] using @rev_ind; first rewrite {2}/fill/= in Hfill; simplify_eq/=.
    { intros Hval Hstep. rewrite fill_app in Hstep. apply head_ctx_step_val in Hstep.
      simpl in Hstep.
      eapply fill_not_val in Hval.
      by apply not_eq_None_Some in Hstep. }
    rewrite !fill_app /= in Hfill.
    intros Hval Hstep.
    assert (Ki = Ki') as ->.
    { eapply fill_item_no_val_inj, Hfill; simpl; first by apply fill_not_val.
      apply fill_not_val. by eapply ectxi_language_mixin. }
    simplify_eq. apply fill_item_inj in Hfill. simpl in *.
    eapply IH in Hfill as [K'' ->]; [|done..].
    exists K''. by rewrite assoc.
  Qed.


  Fixpoint decomp' n (e:expr Λ) :=
    match n with
    | 0 => match decomp_item e with
          | Some _ => None
          | None => Some ([], e)
          end
    | S n' => match decomp_item e with
            | None => None
            | Some (Ki, e') =>
                match decomp' n' e' with
                | Some (K, e'') => Some (K++[Ki], e'')
                | None => None
                end
             end
    end.

  Lemma decomp_decomp' n e K e': decomp' n e = Some (K, e') -> decomp e = (K, e').
  Proof.
    revert e K e'.
    induction n; simpl.
    - intros. case_match; first done.
      simplify_eq. rewrite decomp_unfold. by case_match.
    - intros. case_match eqn:Hx; last done.
      case_match. subst. case_match eqn:Hy; last done.
      case_match. subst. apply IHn in Hy.
      simplify_eq. rewrite decomp_unfold. by rewrite Hx Hy.
  Qed.

  Lemma decomp_decomp2' e : decomp' (length (decomp e).1) e = Some (decomp e).
  Proof.
    remember (length (decomp e).1) as n eqn:Heqn.
    revert e Heqn.
    induction n; simpl.
    - intros ? Hlength.
      destruct (decomp e) as [l ?] eqn:Heqn.
      assert (l=[]) as ->.
      { by apply nil_length_inv. }
      apply decomp_inv_nil in Heqn as [H ?]. subst. by rewrite H.
    - intros e Hlength.
      case_match eqn:H; last first.
      { rewrite decomp_unfold in Hlength. rewrite H in Hlength.
        simplify_eq.
      }
      case_match.
      subst.
      rewrite decomp_unfold in Hlength. rewrite H in Hlength.
      case_match eqn:H'.
      simpl in *.
      rewrite app_length in Hlength. simpl in *.
      assert (length l = n) by lia.
      subst. erewrite IHn; last by rewrite H'.
      rewrite H'. by rewrite decomp_unfold H H'.
  Qed. 
  
  (* How to prove this? *)
  Lemma decomp_measurable : measurable_fun setT decomp.
  Proof.
    assert (setT = \bigcup_i (preimage (decomp' i) option_cov_Some)) as Hrewrite; last rewrite Hrewrite.
    { rewrite eqEsubset; split; intros t; simpl; last done.
      intros _.
      exists (length (decomp t).1); first done.
      simpl. rewrite decomp_decomp2'. by eexists _.
    } 
    rewrite measurable_fun_bigcup; last first.
    - intros n.
      induction n.
      + assert (preimage (decomp' 0) option_cov_Some = preimage decomp_item option_cov_None) as ->.
        * rewrite eqEsubset; split; intros ?; simpl; rewrite /option_cov_Some/option_cov_None/=.
          -- intros []. by case_match.
          -- intros ->. naive_solver.
        * rewrite <-setTI.
          apply: decomp_item_meas; ms_solve.
          apply: option_cov_None_meas_set.
      + assert (preimage (decomp' (S n)) option_cov_Some =
                (preimage decomp_item (option_cov_Some`&`
                  (preimage (snd \o 𝜋_Some_v) (preimage (decomp' n) option_cov_Some))))
               ) as ->.
        { rewrite eqEsubset; split; intros ?; simpl; rewrite /option_cov_Some/=.
          - intros []. case_match eqn:H1; last done.
            case_match. case_match eqn:H2; last done. case_match.
            subst. simplify_eq. naive_solver.
          - intros [[[] H][[]H']]. rewrite H in H'. simpl in *.
            rewrite H H'. naive_solver.
        }
        rewrite <-setTI.
        apply decomp_item_meas; ms_solve; try apply option_cov_Some_meas_set.
        apply: measurable_comp; last first.
        * apply: 𝜋_Some_v_meas_fun.
        * apply measurable_snd_restriction.
          apply: measurableT.
        * done.
        * done.
    - intros n.
      induction n as [|n' IHn].
      + admit.
      + admit.
  Admitted.
  Hint Resolve decomp_measurable : measlang.
  
  Lemma head_ctx_step_fill_val K e σ1 : ¬ is_zero (head_step (fill (K, e), σ1)) → is_Some (to_val e) ∨ K = [].
  Proof.
    destruct K as [|Ki K _] using rev_ind; simpl; first by auto.
    rewrite fill_app /=.
    intros H%head_ctx_step_val; eauto using fill_val. simpl in *.
    left.
    destruct (to_val e) eqn:Heqn; first done.
    eapply fill_not_val in Heqn. by erewrite Heqn in H.
  Qed.

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
    { apply head_step_meas. }
    { by apply fill_measurable. }
    { by apply decomp_measurable. }
    { by apply ectxi_language_mixin. }
    { by apply ectxi_language_mixin. }
    { by apply ectxi_language_mixin. }
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
    { by apply decomp_fill_comp. }
    { by apply decomp_step_by_val. }
    { by apply head_ctx_step_fill_val. }
  Qed.

  Canonical Structure meas_ectxi_lang_ectx := MeasEctxLanguage _ _ _ _ meas_ectxi_lang_ectx_mixin.
  Canonical Structure meas_ectxi_lang := MeasLanguageOfEctx meas_ectxi_lang_ectx.


  Lemma ectxi_language_sub_redexes_are_values e :
    (∀ Ki e', e = fill_item (Ki, e') → is_Some (to_val e')) →
    sub_redexes_are_values e.
  Proof.
    intros Hsub K e' ->. destruct K as [|Ki K _] using @rev_ind=> //=.
    intros []%eq_None_not_Some.
    simpl in *.
    eapply (fill_val (Λ := meas_ectxi_lang_ectx)), Hsub.
    by rewrite /= fill_app.
  Qed.

  Definition curry_fill_item := curry (@fill_item Λ).
  
  Global Instance ectxi_lang_ctx_item Ki : MeasLanguageCtx (Λ := meas_ectxi_lang)(curry_fill_item Ki).
  Proof. change (MeasLanguageCtx (Λ := meas_ectxi_lang) (curry fill [Ki])). apply _. Qed.

End ectxi_language.

Global Arguments meas_ectxi_lang_ectx : clear implicits.
Global Arguments meas_ectxi_lang : clear implicits.
Coercion meas_ectxi_lang_ectx : meas_ectxiLanguage >-> meas_ectxLanguage.
Coercion meas_ectxi_lang : meas_ectxiLanguage >-> meas_language.


Definition MeasEctxLanguageOfEctxi (Λ : meas_ectxiLanguage) : meas_ectxLanguage :=
 let '@MeasEctxiLanguage _ _ _ _
       expr val state ectx_item
       _ _ _ _ of_val to_val fill_item decomp_item expr_old head_step mix := Λ in
 MeasEctxLanguage _ _ _ _ (@meas_ectxi_lang_ectx_mixin (MeasEctxiLanguage _ _ _ _ _ mix)).

Global Arguments MeasEctxLanguageOfEctxi : simpl never.
