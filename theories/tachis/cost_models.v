From clutch.tachis Require Import ert_weakestpre problang_wp.
#[local] Open Scope R.

(** Utility functions *)
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
  | Tick e         => noval e
  | Laplace e1 e2 e3 =>
      match e3 with
      | Val v3 => match e2 with
                  | Val v2 => noval e1
                  | _ => at_redex f e2
                  end
      | _ => at_redex f e3
      end
  | _              => None
  end.

Lemma at_redex_pos (f : expr → R) e (x : R):
  (∀ e, 0 <= f e) →
  at_redex f e = Some x -> 0 <= x.
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

Lemma at_redex_fill_item_None (f : expr → R) e Ki :
  to_val e = None → at_redex f e = None → at_redex f (fill_item Ki e) = None.
Proof. by destruct Ki, e. Qed.

Lemma at_redex_fill_None (f : expr → R) e K :
  to_val e = None → at_redex f e = None → at_redex f (fill K e) = None.
Proof.
  induction K as [|Ki K IHK] in e |-* => /= ? ?; [done|].
  destruct (to_val (fill_item Ki e)) eqn: H1.
  { by erewrite fill_item_not_val in H1. }
  destruct  (at_redex f (fill_item Ki e)) eqn: H2.
  + by erewrite at_redex_fill_item_None in H2.
  + by eapply IHK.
Qed.

(** Combinator for building cost functions at redex position *)
Definition at_redex_cost f e := default 0%R (at_redex f e).
Arguments at_redex_cost /.

Lemma at_redex_cost_fill K (f : expr → R) (e : expr) :
  to_val e = None → at_redex_cost f (fill K e) = at_redex_cost f e.
Proof.
  intros Hv => /=.
  destruct (at_redex f e) eqn:He.
  { by erewrite at_redex_fill. }
  by erewrite at_redex_fill_None.
Qed.

Lemma at_redex_cost_nonneg (f : expr → R) :
  (∀ e, 0 <= f e) → (∀ e, 0 <= at_redex_cost f e).
Proof.
  intros Hf e => /=.
  destruct (at_redex f e) eqn:He; [|done].
  by eapply at_redex_pos.
Qed.

Instance CostLanguageCtx_at_redex_Cost C f K :
  TCEq C.(cost) (at_redex_cost f) →
  CostLanguageCtx C (fill K).
Proof.
  intros Hc.
  constructor; [apply _|].
  intros.
  rewrite Hc.
  by eapply at_redex_cost_fill.
Qed.

(** * Cost models *)

(** ** Cost [1] for all steps  *)
Program Definition Cost1 {Λ} : Costfun Λ := Build_Costfun _ (λ _, 1) _.
Next Obligation. intros; simpl. lra. Qed.

Instance CostLanguageCtx_Cost1_prob_lang (K : ectx prob_ectx_lang)  :
  CostLanguageCtx Cost1 (fill K).
Proof. constructor; [apply _|done]. Qed.

(** Cost [1] model for [App]  *)
Definition cost_app (e : expr) : R :=
  match e with
  | App _ _ => 1
  | _ => 0
  end.

Program Definition CostApp : Costfun prob_lang :=
  Build_Costfun _ (at_redex_cost cost_app) _.
Next Obligation. eapply at_redex_cost_nonneg. intros [] => /=; lra. Qed.

(** ** Cost [1] model for [rand] *)
Definition cost_rand (e : expr) : R :=
  match e with
  | Rand _ _ => 1
  | _ => 0
  end.

Program Definition CostRand : Costfun prob_lang :=
  Build_Costfun _ (at_redex_cost cost_rand) _.
Next Obligation. eapply at_redex_cost_nonneg. intros [] => /=; lra. Qed.

(** ** Entropy cost model for [rand] *)
Definition cost_entropy base (e : expr) : R :=
  match e with
  | Rand (Val (LitV (LitInt N))) _ => Rlog base (S (Z.abs_nat N))
  | _ => 0
  end.

Program Definition CostEntropy base (_ : (1 < base)%R) : Costfun prob_lang :=
  Build_Costfun _ (at_redex_cost (cost_entropy base)) _.
Next Obligation.
  intros ???.
  apply at_redex_cost_nonneg => e'.
  rewrite /cost_entropy.
  repeat (case_match ; try lra). simplify_eq.
  assert (1 <= (S (Z.abs_nat n)))%R.
  { rewrite -INR_1. apply le_INR. lia. }
  rewrite /Rlog.
  assert (∀ x, 1 <= x -> 0 <= ln x)%R as ln_0_le.
  {
    clear. intros.
    rewrite -ln_1.
    apply Rcomplements.ln_le ; lra.
  }
  assert (∀ x, 1 < x -> 0 < ln x)%R as ln_0_lt.
  {
    clear. intros.
    rewrite -ln_1.
    apply ln_increasing ; lra.
  }
  apply Rcomplements.Rdiv_le_0_compat.
  - by apply ln_0_le.
  - by apply ln_0_lt.
Qed.

(** ** Cost [n] for [tick n]  *)
Definition cost_tick (e : expr) : R :=
  match e with
  | tick (Val (LitV (LitInt z))) => Z.to_nat z
  | _ => 0
  end.

Program Definition CostTick : Costfun prob_lang :=
  Build_Costfun _ (at_redex_cost cost_tick) _.
Next Obligation.
  eapply at_redex_cost_nonneg.
  intros [] => /=; try lra.
  repeat (case_match; try lra).
  apply pos_INR.
Qed.
