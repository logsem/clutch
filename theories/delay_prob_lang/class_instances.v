From Coq Require Import Reals Psatz.
From clutch.prob Require Export distribution.
From clutch.common Require Export language. 
From clutch.delay_prob_lang Require Export lang.
From clutch.delay_prob_lang Require Import tactics notation.
From iris.prelude Require Import options.

Global Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.
Global Instance as_val_val v : AsVal (Val v).
Proof. by eexists. Qed.

(** * Instances of the [Atomic] class *)
Section atomic.
  Local Ltac solve_atomic :=
    apply strongly_atomic_atomic, ectx_language_atomic;
    [intros ????; simpl; by inv_head_step
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

  Global Instance rec_atomic s f x e : Atomic s (Rec f x e).
  Proof. solve_atomic. Qed.
  Global Instance injl_atomic s v : Atomic s (InjL (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance injr_atomic s v : Atomic s (InjR (Val v)).
  Proof. solve_atomic. Qed.
  (** The instance below is a more general version of [Skip] *)
  Global Instance beta_atomic s f x v1 v2 : Atomic s (App (RecV f x (Val v1)) (Val v2)).
  Proof. destruct f,x; solve_atomic. Qed.

  Global Instance unop_atomic s op v : Atomic s (UnOp op (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance binop_atomic s op v1 v2 : Atomic s (BinOp op (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance if_true_atomic s v1 e2 :
    Atomic s (If (Val $ LitV $ LitBool true) (Val v1) e2).
  Proof. solve_atomic. Qed.
  Global Instance if_false_atomic s e1 v2 :
    Atomic s (If (Val $ LitV $ LitBool false) e1 (Val v2)).
  Proof. 
    apply strongly_atomic_atomic, ectx_language_atomic; last (apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver).
    intros ??? H. simpl. inv_head_step; try done.
    unshelve epose proof urn_subst_equal_obv σ false _ as H'; first done.
    eapply urn_subst_equal_unique in H; last first; done.
  Qed. 

  Global Instance fst_atomic s v : Atomic s (Fst (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance snd_atomic s v : Atomic s (Snd (Val v)).
  Proof. solve_atomic. Qed.

  Global Instance alloc_atomic s v : Atomic s (Alloc (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance load_atomic s v : Atomic s (Load (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance store_atomic s v1 v2 : Atomic s (Store (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.

  Global Instance rand_atomic s z : Atomic s (Rand (Val (LitV (LitInt z)))).
  Proof. solve_atomic. Qed.
  Global Instance drand_atomic s z : Atomic s (DRand (Val (LitV (LitInt z)))).
  Proof. solve_atomic. Qed.
End atomic.

(** * Instances of the [PureExec] class *)
(** The behavior of the various [wp_] tactics with regard to lambda differs in
the following way:

- [wp_pures] does *not* reduce lambdas/recs that are hidden behind a definition.
- [wp_rec] and [wp_lam] reduce lambdas/recs that are hidden behind a definition.

To realize this behavior, we define the class [AsRecV v f x erec], which takes a
value [v] as its input, and turns it into a [RecV f x erec] via the instance
[AsRecV_recv : AsRecV (RecV f x e) f x e]. We register this instance via
[Hint Extern] so that it is only used if [v] is syntactically a lambda/rec, and
not if [v] contains a lambda/rec that is hidden behind a definition.

To make sure that [wp_rec] and [wp_lam] do reduce lambdas/recs that are hidden
behind a definition, we activate [AsRecV_recv] by hand in these tactics. *)
Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Global Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Global Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

Section pure_exec.
  Local Ltac solve_exec_safe := intros; subst; eexists; eapply head_step_support_equiv_rel; eauto with head_step.
  Local Ltac solve_exec_puredet :=
    intros; simpl;
    (repeat case_match); simplify_eq;
    rewrite dret_1_1 //.
  Local Ltac solve_pure_exec :=
    subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

  Global Instance pure_recc f x (erec : expr) :
    PureExec True 1 (Rec f x erec) (Val $ RecV f x erec).
  Proof.
    solve_pure_exec.
  Qed.

  Global Instance pure_pairc (v1 v2 : val) :
    PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_injlc (v : val) :
    PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_injrc (v : val) :
    PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
    PureExec True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
  Proof. unfold AsRecV in *. subst. solve_pure_exec. Qed.

  Global Instance pure_unop op v v' :
    PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
  Proof. solve_pure_exec. Qed.

  Global Instance pure_binop op v1 v2 v' :
    PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v') | 10.
  Proof. solve_pure_exec. Qed.

  (* Lower-cost instance for [EqOp]. *)
  Global Instance pure_eqop bl1 bl2 :
    PureExec (is_simple_base_lit bl1 = true /\ is_simple_base_lit bl2 = true) 1
      (BinOp EqOp (Val $ LitV bl1) (Val $ LitV bl2))
      (Val $ LitV $ LitBool $ bool_decide (bl1 = bl2)) | 1.
  Proof.
    intros [H1 H2].
    apply nsteps_once, pure_head_step_pure_step; constructor; try solve_exec_safe.
    - apply BinOpS; destruct bl1; by destruct bl2.
    - intros. simpl. destruct bl1; destruct bl2; try done; simpl; rewrite dret_1_1//.
  Qed.

  Global Instance pure_if_true e1 e2 :
    PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
  Proof. intros _. apply nsteps_once, pure_head_step_pure_step; constructor; try solve_exec_safe.
         - apply IfTrueS. by apply urn_subst_equal_obv.
         - simpl. intros. rewrite bool_decide_eq_true_2; first rewrite dret_1_1//.
           by apply urn_subst_equal_obv.
  Qed.
  Global Instance pure_if_false e1 e2 :
    PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
  Proof. intros _. apply nsteps_once, pure_head_step_pure_step; constructor; try solve_exec_safe.
         - apply IfFalseS. by apply urn_subst_equal_obv.
         - simpl. intros σ1. rewrite bool_decide_eq_false_2; first rewrite bool_decide_eq_true_2; first rewrite dret_1_1//.
           + by apply urn_subst_equal_obv.
           + intros H. unshelve epose proof urn_subst_equal_obv σ1 false _ as H'; first done.
             eapply urn_subst_equal_unique in H; last done. done.
  Qed. 

  Global Instance pure_fst v1 v2 :
    PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_snd v1 v2 :
    PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inl v e1 e2 :
    PureExec True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_case_inr v e1 e2 :
    PureExec True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
  Proof. solve_pure_exec. Qed.

  (* Global Instance pure_tick (z : Z) : *)
  (*   PureExec True 1 (Tick #z) #(). *)
  (* Proof. solve_pure_exec. Qed. *)
End pure_exec.
