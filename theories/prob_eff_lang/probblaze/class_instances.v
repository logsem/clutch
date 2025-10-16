From Coq Require Import Reals Psatz.
From clutch.prob Require Export distribution.
From clutch.common Require Export language. 
From clutch.prob_eff_lang.probblaze Require Export syntax semantics.
From clutch.prob_eff_lang.probblaze Require Import notation.
From iris.prelude Require Import options.

Global Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.
Global Instance as_val_val v : AsVal (Val v).
Proof. by eexists. Qed.

(** * Instances of the [Atomic] class *)
Section atomic.

  (* Helper lemmas from ectx_language and ectxi_language *)
  Definition sub_redexes_are_values (e : expr) :=
    ∀ K e', e = fill K e' → to_val e' = None → K = [].
  
  Definition head_atomic (a : atomicity) (e : expr) : Prop :=
    ∀ σ e' σ',
      head_step e σ (e', σ') > 0 →
      if a is WeaklyAtomic then irreducible (e', σ') else is_Some (to_val e').

  

  Lemma ectx_language_atomic a e :
    head_atomic a e → sub_redexes_are_values e → Atomic a e.
  Proof.
    intros Hatomic Hsub σ e' σ' (K & e1' & e2' & Hdecomp & <- & Hs)%prim_step_iff.
    apply decomp_fill in Hdecomp. simplify_eq.
    assert (K = []) as -> by eauto 10 using val_head_stuck.
    rewrite fill_empty in Hatomic.
    eapply Hatomic. rewrite fill_empty. eauto.
  Qed.

  Lemma ectxi_language_sub_redexes_are_values e :
    (∀ Ki e', e = fill_frame Ki e' → is_Some (to_val e')) →
    sub_redexes_are_values e.
  Proof.
    intros Hsub K e' ->. destruct K as [|Ki K]; first done.
    intros []%eq_None_not_Some.
    destruct (Hsub Ki (fill K e')) as [v Heq]; first done.
    by destruct (fill_val _ _ _ Heq) as [-> <-]. 
  Qed.
  
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
  Proof. solve_atomic. Qed.

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

  Global Instance rand_atomic s z l : Atomic s (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl l)))).
  Proof. solve_atomic. Qed.
  Global Instance rand_atomic_int s z : Atomic s (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))).
  Proof. solve_atomic. Qed.
  Global Instance alloc_tape_atomic s z : Atomic s (AllocTape (Val (LitV (LitInt z)))).
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
    Local Ltac solve_exec_safe := intros; subst; eexists; simpl; apply head_step_prim_step; eapply head_step_support_equiv_rel; eauto with head_step.
  Local Ltac solve_exec_puredet :=
    intros; simpl; unfold prim_step; simpl;
    (repeat case_match); simplify_eq;
    try (rewrite fill_lift_empty; rewrite dmap_dret);
    rewrite dret_1_1 //.
  Local Ltac solve_pure_exec :=
    subst; intros ?; apply nsteps_once; simpl;
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
    PureExec True 1 (App (Val v1) (Val v2)) (val_subst' x v2 (val_subst' f v1 erec)).
  Proof. unfold AsRecV in *. subst. solve_pure_exec. Qed.

  Global Instance pure_unop op v v' :
    PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
  Proof. solve_pure_exec. Qed.

  Global Instance pure_binop op v1 v2 v' :
    PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v') | 10.
  Proof. solve_pure_exec. Qed.

  (* (* Lower-cost instance for [EqOp]. *)
     Global Instance pure_eqop v1 v2 :
       PureExec (vals_compare_safe v1 v2) 1
         (BinOp EqOp (Val v1) (Val v2))
         (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
     Proof.
       intros Hcompare.
       cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
       { intros. revert Hcompare. intros ?. apply nsteps_once. constructor.
         - solve_exec_safe.
         
       rewrite /bin_op_eval /= decide_True //.
     Admitted. *)

  Global Instance pure_if_true e1 e2 :
    PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
  Proof. solve_pure_exec. Qed.
  Global Instance pure_if_false e1 e2 :
    PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
  Proof. solve_pure_exec. Qed.

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

  Global Instance pure_kont k v :
    PureExec True 1 (App (Val $ KontV k) (Val v)) (semantics.fill k (Val v)).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_handle_eff l k v h r :
    let k' := HandleCtx l h r :: k in
    PureExec (l ∉ ectx_labels k) 1
      (Handle (EffLabel l) (fill k (Do (EffLabel l) (Val v))) h r)
      (App (App h (Val v)) (Val $ KontV k')).
  Proof. 
    intros ?. unfold k'.
    subst; intros ?; apply nsteps_once; constructor.
    - intros; subst.  eexists. simpl. apply head_step_prim_step.
      apply head_step_support_equiv_rel.
      apply HandleEffS; first done. by apply to_of_eff.
    - intros. simpl. 
      rewrite /prim_step.
      assert (decomp (Handle l (fill k (do: l v)) h r) = ([], Handle l (fill k (do: l v)) h r)) as ->.
      { rewrite decomp_unfold. unfold decomp_frame. erewrite to_eff_fill; [|apply to_eff_eff]. rewrite app_nil_r.
        rewrite decide_True; eauto. }
      rewrite fill_lift_empty. rewrite dmap_id. simpl. erewrite to_eff_fill; [|apply to_eff_eff].
      rewrite app_nil_r. rewrite decide_True; [|done]. rewrite decide_True; [|done].
      by apply dret_1_1.
  Qed.
      

  Global Instance pure_handle_ret l v h r :
    PureExec True 1 (Handle (EffLabel l) (Val v) h r) (App r (Val v)).
  Proof. solve_pure_exec. Qed.
End pure_exec.
