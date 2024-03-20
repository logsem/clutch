From clutch.ert_logic Require Import ert_weakestpre problang_wp.

(** Cost model for where all steps have cost [1]  *)
Program Definition Cost1 {Λ} : Costfun Λ := (Build_Costfun _ (λ _, 1) _ _).
Next Obligation. by eexists 1. Qed.
Next Obligation. intros; simpl. lra. Qed.

Instance CostLanguageCtx_Cost1_prob_lang (K : ectx prob_ectx_lang)  :
  CostLanguageCtx Cost1 (fill K).
Proof. constructor; [apply _|done]. Qed.

(** Utility function  *)
Fixpoint at_redex {A} (f : expr → A) (e : expr) : option A :=
  let noval (e' : expr) :=
    match e' with Val _ => Some $ f e | _ => at_redex f e' end in
  match e with
  | App e1 e2      =>
      match e2 with
      | (Val v)    => noval e1
      | _          => at_redex f e2
      end
  | UnOp op e1      => noval e1
  | BinOp op e1 e2 =>
      match e2 with
      | Val v      => noval e1
      | _          => at_redex f e2
      end
  | If e0 e1 e2    => noval e0
  | Pair e1 e2     =>
      match e2 with
      | Val v      => noval e1
      | _          => at_redex f e2
      end
  | Fst e          => noval e
  | Snd e          => noval e
  | InjL e         => noval e
  | InjR e         => noval e
  | Case e0 e1 e2  => noval e0
  | AllocN e1 e2        =>
      match e2 with
      | Val v      => noval e1
      | _          => at_redex f e2
      end

  | Load e         => noval e
  | Store e1 e2    =>
      match e2 with
      | Val v      => noval e1
      | _          => at_redex f e2
      end
  | AllocTape e    => noval e
  | Rand e1 e2     =>
      match e2 with
      | Val v      => noval e1
      | _          => at_redex f e2
      end
  | _              => None
  end.

Lemma at_redex_bounds (b : R) (f: expr → R) e (x : R):
  (∀ e, f e <= b)%R →
  at_redex f e = Some x → (x <= b)%R.
Proof.
  intros Hbound Har.
  revert x Har.
  induction e; simpl; intros; try done;
    repeat case_match; naive_solver.
Qed.

Lemma at_redex_pos (f : expr → R) e (x : R):
  (∀ e, 0 <= f e)%R →
  at_redex f e = Some x -> (0 <= x)%R.
Proof.
  intros Hbound Har.
  revert x Har. induction e; simpl; intros; try done; repeat case_match; naive_solver.
Qed.

Lemma at_redex_fill (K : ectx prob_ectx_lang) (f : expr → R) (e : expr) b:
  at_redex f e = Some b → at_redex f (fill K e) = Some b.
Proof.
  induction K as [|Ki K IHK] in e |-*; [done|].
  destruct Ki => /= He; rewrite IHK //=; by case_match.
Qed.

Lemma at_redex_fill_None (f:expr->R) e a:
  to_val e = None -> at_redex f e = None -> at_redex f (fill_item a e) = None.
Proof.
  revert a; induction e; simpl; intros Hv Har; try done.
  all: by destruct Hv.
Qed.

(** Cost model for [App]  *)
Definition cost_app (e : expr) : R :=
  match e with
  | App _ _ => 1
  | _ => 0
  end.

Program Definition CostApp : Costfun prob_lang :=
  Build_Costfun _ (λ e, match at_redex cost_app e with None => 0 | Some r => r end) _ _.
Next Obligation.
  exists 1. intros. simpl. case_match.
  - eapply at_redex_bounds; [|done]. intros. rewrite /cost_app. case_match; lra.
  - lra.
Defined.
Next Obligation.
  intros. simpl. case_match.
  - eapply at_redex_pos; [|done]. intros; rewrite /cost_app. case_match; lra.
  - done.
Defined.

Instance CostLanguageCtx_CostApp_prob_lang (K : ectx prob_ectx_lang)  :
  CostLanguageCtx CostApp (fill K).
Proof.
  constructor; [apply _|].
  intros e Hv => /=.
  destruct (at_redex _ e) eqn:He.
  { by erewrite at_redex_fill. }
  revert e Hv He. induction K; simpl.
  - intros. case_match; [done|lra].
  - intros.
    destruct (to_val (fill_item a e)) eqn :H1;
      destruct (at_redex cost_app (fill_item a e)) eqn :H2; last first.
    + specialize (IHK _ H1 H2). done.
    + epose proof at_redex_fill_None _ _ _ Hv He. erewrite H2 in H. done.
    + apply mk_is_Some in H1. apply fill_item_val in H1. rewrite Hv in H1. inversion H1. done.
    + apply mk_is_Some in H1. apply fill_item_val in H1. rewrite Hv in H1. inversion H1. done.
Defined.

(** Cost model for [rand] *)
Definition cost_rand (e : expr) : R :=
  match e with
  | Rand _ _ => 1
  | _ => 0
  end.

Program Definition CostRand : Costfun prob_lang :=
  Build_Costfun _ (λ e, match at_redex cost_rand e with None => nnreal_zero | Some r => r end) _ _.
Next Obligation.
  exists 1. intros. simpl. case_match.
  - eapply at_redex_bounds; [|done]. intros. rewrite /cost_rand. case_match; lra.
  - lra.
Defined.
Next Obligation.
  intros. simpl. case_match.
  - eapply at_redex_pos; [|done]. intros; rewrite /cost_rand. case_match; lra.
  - done.
Defined.

Instance CostLanguageCtx_CostRand_prob_lang (K : ectx prob_ectx_lang)  :
  CostLanguageCtx CostRand (fill K).
Proof.
  constructor; [apply _|].
  intros e Hv => /=.
  destruct (at_redex _ e) eqn:He.
  { by erewrite at_redex_fill. }
  revert e Hv He. induction K; simpl.
  - intros. case_match; [done|lra].
  - intros.
    destruct (to_val (fill_item a e)) eqn :H1;
      destruct (at_redex cost_rand (fill_item a e)) eqn :H2; last first.
    + specialize (IHK _ H1 H2). done.
    + epose proof at_redex_fill_None _ _ _ Hv He. erewrite H2 in H. done.
    + apply mk_is_Some in H1. apply fill_item_val in H1. rewrite Hv in H1. inversion H1. done.
    + apply mk_is_Some in H1. apply fill_item_val in H1. rewrite Hv in H1. inversion H1. done.
Defined.
