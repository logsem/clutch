From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import base proofmode classes.

From clutch.common Require Export language ectx_language.
From clutch.prob_lang Require Import notation tactics metatheory.
From clutch.prob_lang Require Export lang.

Local Open Scope R.

(** Syntactic non-allocating predicate: no AllocN or AllocTape sub-terms *)
Fixpoint na_expr (e : prob_lang.expr) : Prop :=
  match e with
  | Val v => na_val v
  | Var _ => True
  | Rec f x e => na_expr e
  | App e1 e2 => na_expr e1 ∧ na_expr e2
  | UnOp _ e => na_expr e
  | BinOp _ e1 e2 => na_expr e1 ∧ na_expr e2
  | If e0 e1 e2 => na_expr e0 ∧ na_expr e1 ∧ na_expr e2
  | Pair e1 e2 => na_expr e1 ∧ na_expr e2
  | Fst e => na_expr e
  | Snd e => na_expr e
  | InjL e => na_expr e
  | InjR e => na_expr e
  | Case e0 e1 e2 => na_expr e0 ∧ na_expr e1 ∧ na_expr e2
  | AllocN _ _ => False
  | Load e => na_expr e
  | Store e1 e2 => na_expr e1 ∧ na_expr e2
  | AllocTape _ => False
  | Rand e1 e2 => na_expr e1 ∧ na_expr e2
  | Laplace e1 e2 e3 => na_expr e1 ∧ na_expr e2 ∧ na_expr e3
  | Tick e => na_expr e
  end
with na_val (v : prob_lang.val) : Prop :=
  match v with
  | LitV _ => True
  | RecV f x e => na_expr e
  | PairV v1 v2 => na_val v1 ∧ na_val v2
  | InjLV v => na_val v
  | InjRV v => na_val v
  end.

(** All heap values are na_expr *)
Definition na_state (σ : prob_lang.state) : Prop :=
  ∀ l v, σ.(heap) !! l = Some v → na_val v.

Lemma na_of_val v : na_expr (Val v) ↔ na_val v.
Proof. simpl. tauto. Qed.

Lemma na_subst x v e : na_expr e → na_val v → na_expr (subst x v e).
Proof.
  revert x v.
  induction e; simpl; intros x' v' Hna Hnav; auto;
  try (destruct Hna; split; auto; fail).
  - (* Var *) destruct (decide _); simpl; auto.
  - (* Rec *) destruct (decide _); simpl; auto.
  - (* If *) destruct Hna as (?&?&?). repeat split; auto.
  - (* Case *) destruct Hna as (?&?&?). repeat split; auto.
  - (* Laplace *) destruct Hna as (?&?&?). repeat split; auto.
Qed.

Lemma na_subst' mx v e : na_expr e → na_val v → na_expr (subst' mx v e).
Proof. destruct mx; simpl; auto using na_subst. Qed.

Lemma na_fill_item_inv Ki e : na_expr (fill_item Ki e) → na_expr e.
Proof. destruct Ki; simpl; tauto. Qed.

Lemma na_fill_inv : ∀ e K,
  na_expr (fill K e) → na_expr e.
Proof.
  intros e K. revert e.
  induction K as [|Ki K IH]; simpl; auto.
  intros e H. apply IH in H. by apply na_fill_item_inv in H.
Qed.

Lemma na_fill_item_replace Ki e e' : na_expr (fill_item Ki e) → na_expr e' → na_expr (fill_item Ki e').
Proof. destruct Ki; simpl; tauto. Qed.

Lemma na_fill_replace K e e' : na_expr (fill K e) → na_expr e' → na_expr (fill K e').
Proof.
  revert e e'.
  induction K as [|Ki K IH]; simpl; auto.
  intros e e' H Hna'.
  apply IH with (e := fill_item Ki e); auto.
  apply na_fill_item_replace with (e := e); auto.
  by eapply na_fill_inv.
Qed.

Lemma na_no_allocN : ∀ {v1 v2},
  na_expr (AllocN v1 v2) →
  False.
Proof. simpl. tauto. Qed.

Lemma na_no_allocTape : ∀ {e1},
  na_expr (AllocTape e1) →
  False.
Proof. simpl. tauto. Qed.

Lemma na_head_step e1 σ e2 σ' :
  na_expr e1 →
  na_state σ →
  head_step e1 σ (e2, σ') > 0 →
  na_expr e2 ∧ na_state σ'.
Proof.
  intros Hna Hna_st Hstep.
  rewrite head_step_support_equiv_rel in Hstep.
  induction Hstep; subst; simpl in *; (try by constructor); try tauto.
  (* beta *)
  - destruct Hna as [Hna1 Hna2]. simpl in Hna1.
    split; [| assumption].
    apply na_subst'; auto. apply na_subst'; auto.
  (* un_op *)
  - destruct (un_op_eval op v) eqn:?; [|done].
    split; [| assumption]. simpl. 
    destruct op, v; simpl in *; (try discriminate); destruct l; simplify_eq; constructor.
  (* bin_op *)
  - rewrite /bin_op_eval in H.
    destruct op; simpl in *; destruct v1, v2; simpl in *; try discriminate;
    (try destruct l); (try discriminate); (try destruct l0); inversion H; (try by constructor); case_decide; simplify_eq;
    (try by constructor).
  (* load *)
  - destruct (heap σ !! l) eqn:?; [|done].
    split; [simpl; apply Hna_st with l; auto | assumption]. by simplify_eq. 
  (* store *)
  - destruct (heap σ !! l) eqn:?; [|done].
    split; [simpl; auto |].
    intros l' v' Hlookup. simpl in Hlookup.
    rewrite /state_upd_heap //= in Hlookup.
    destruct (decide (l = l')) as [<-|Hne].
    + rewrite lookup_insert in Hlookup. injection Hlookup; intros; subst.
      destruct Hna as [_ Hna2]. simpl in Hna2. auto.
    + rewrite lookup_insert_ne in Hlookup; auto. 
      by eapply Hna_st.
Qed.

Lemma na_step e σ e' σ' :
  na_expr e →
  na_state σ →
  prim_step e σ (e', σ') > 0 →
  na_expr e' ∧ na_state σ'.
Proof.
  intros Hna Hna_st Hstep.
  rewrite //= prim_step_iff in Hstep.
  destruct Hstep as (K & e1 & e2 & <- & <- & Hstep).
  pose proof (na_fill_inv _ _ Hna) as Hna1.
  destruct (na_head_step _ _ _ _ Hna1 Hna_st Hstep) as [Hna2 Hna_st'].
  split; [| auto].
  eapply (na_fill_replace _ e1) ; eauto.
Qed.

Definition na e σ := na_expr e ∧ na_state σ.