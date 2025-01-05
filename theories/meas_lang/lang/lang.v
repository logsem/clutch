(* TODO cleanup imports *)
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp Require Import functions.
From mathcomp.analysis Require Import reals measure itv lebesgue_measure probability.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp fintype.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.common Require Export locations.
From clutch.meas_lang Require Import ectxi_language ectx_language.
From Coq Require Export Reals.
From clutch.prob.monad Require Export laws extras.
From mathcomp.analysis Require Export Rstruct.
From mathcomp Require Import classical_sets.
Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude types constructors shapes cover projections tapes state.
(* From Coq Require Import Reals Psatz.
From stdpp Require Export binders strings.
From stdpp Require Import fin.
From stdpp Require Import gmap fin_maps countable fin.
From clutch.prob Require Export distribution.
From clutch.common Require Export language ectx_language ectxi_language locations.
From iris.prelude Require Import options.
From mathcomp Require Import ssrbool eqtype fintype choice all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed normedtype sequences esum numfun measure lebesgue_measure lebesgue_integral. *)

Local Open Scope classical_set_scope.

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Global Instance of_val_inj {T1 T2 T3 T4 : Type} : Inj (=) (=) (@of_val T1 T2 T3 T4).
Proof. intros ??. congruence. Qed.

Global Instance state_inhabited : Inhabited state := populate {| heap := gmap_empty; tapes := gmap_empty; utapes := gmap_empty |}.
Global Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

Canonical Structure stateO := leibnizO state.
Canonical Structure locO := leibnizO loc.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.




(** Evaluation contexts *)
Inductive ectx_item :=
  | AppLCtx (v2 : val)
  | AppRCtx (e1 : expr)
  | UnOpCtx (op : un_op)
  | BinOpLCtx (op : bin_op) (v2 : val)
  | BinOpRCtx (op : bin_op) (e1 : expr)
  | IfCtx (e1 e2 : expr)
  | PairLCtx (v2 : val)
  | PairRCtx (e1 : expr)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : expr) (e2 : expr)
  | AllocNLCtx (v2 : val)
  | AllocNRCtx (e1 : expr)
  | LoadCtx
  | StoreLCtx (v2 : val)
  | StoreRCtx (e1 : expr)
  | AllocTapeCtx
  | RandLCtx (v2 : val)
  | RandRCtx (e1 : expr)
  | URandCtx
  | TickCtx.

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx v2 => App e (of_val v2)
  | AppRCtx e1 => App e1 e
  | UnOpCtx op => UnOp op e
  | BinOpLCtx op v2 => BinOp op e (Val v2)
  | BinOpRCtx op e1 => BinOp op e1 e
  | IfCtx e1 e2 => If e e1 e2
  | PairLCtx v2 => Pair e (Val v2)
  | PairRCtx e1 => Pair e1 e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | InjLCtx => InjL e
  | InjRCtx => InjR e
  | CaseCtx e1 e2 => Case e e1 e2
  | AllocNLCtx v2 => AllocN e (Val v2)
  | AllocNRCtx e1 => AllocN e1 e
  | LoadCtx => Load e
  | StoreLCtx v2 => Store e (Val v2)
  | StoreRCtx e1 => Store e1 e
  | AllocTapeCtx => AllocTape e
  | RandLCtx v2 => Rand e (Val v2)
  | RandRCtx e1 => Rand e1 e
  | URandCtx => URand e
  | TickCtx => Tick e
  end.

Definition decomp_item (e : expr) : option (ectx_item * expr) :=
  let noval (e : expr) (ei : ectx_item) :=
    match e with Val _ => None | _ => Some (ei, e) end in
  match e with
  | App e1 e2      =>
      match e2 with
      | (Val v)    => noval e1 (AppLCtx v)
      | _          => Some (AppRCtx e1, e2)
      end
  | UnOp op e      => noval e (UnOpCtx op)
  | BinOp op e1 e2 =>
      match e2 with
      | Val v      => noval e1 (BinOpLCtx op v)
      | _          => Some (BinOpRCtx op e1, e2)
      end
  | If e0 e1 e2    => noval e0 (IfCtx e1 e2)
  | Pair e1 e2     =>
      match e2 with
      | Val v      => noval e1 (PairLCtx v)
      | _          => Some (PairRCtx e1, e2)
      end
  | Fst e          => noval e FstCtx
  | Snd e          => noval e SndCtx
  | InjL e         => noval e InjLCtx
  | InjR e         => noval e InjRCtx
  | Case e0 e1 e2  => noval e0 (CaseCtx e1 e2)
  | AllocN e1 e2        =>
      match e2 with
      | Val v      => noval e1 (AllocNLCtx v)
      | _          => Some (AllocNRCtx e1, e2)
      end

  | Load e         => noval e LoadCtx
  | Store e1 e2    =>
      match e2 with
      | Val v      => noval e1 (StoreLCtx v)
      | _          => Some (StoreRCtx e1, e2)
      end
  | AllocTape e    => noval e AllocTapeCtx
  | Rand e1 e2     =>
      match e2 with
      | Val v      => noval e1 (RandLCtx v)
      | _          => Some (RandRCtx e1, e2)
      end
  | URand e        => noval e URandCtx
  | Tick e         => noval e TickCtx
  | _              => None
  end.


Definition binder_eq (b1 b2 : <<discr binder>> ) : bool. Admitted.

(** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr)  : expr :=
  match e with
  | Val _ => e
  | Var y =>  if (binder_eq x y) then Val v else Var y
  | Rec f y e =>
     Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x v e else e
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  | UnOp op e => UnOp op (subst x v e)
  | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
  | Fst e => Fst (subst x v e)
  | Snd e => Snd (subst x v e)
  | InjL e => InjL (subst x v e)
  | InjR e => InjR (subst x v e)
  | Case e0 e1 e2 => Case (subst x v e0) (subst x v e1) (subst x v e2)
  | AllocN e1 e2 => AllocN (subst x v e1) (subst x v e2)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | AllocTape e => AllocTape (subst x v e)
  | AllocUTape => AllocUTape
  | Rand e1 e2 => Rand (subst x v e1) (subst x v e2)
  | URand e => URand (subst x v e)
  | Tick e => Tick (subst x v e)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => λ x, x end.

Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt z) => Some $ LitV $ LitInt (Z.lnot z)
  | MinusUnOp, LitV (LitInt z) => Some $ LitV $ LitInt (- z)%Z
  | MinusUnOp, LitV (LitReal r) => Some $ LitV $ LitReal (- r)%R
  | _, _ => None
  end.


Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : base_lit :=
  match op with
  | PlusOp => LitInt (n1 + n2)
  | MinusOp => LitInt (n1 - n2)
  | MultOp => LitInt (n1 * n2)
  | QuotOp => LitInt (n1 `quot` n2)
  | RemOp => LitInt (n1 `rem` n2)
  | AndOp => LitInt (Z.land n1 n2)
  | OrOp => LitInt (Z.lor n1 n2)
  | XorOp => LitInt (Z.lxor n1 n2)
  | ShiftLOp => LitInt (n1 ≪ n2)
  | ShiftROp => LitInt (n1 ≫ n2)
  | LeOp => LitBool (bool_decide (n1 ≤ n2))
  | LtOp => LitBool (bool_decide (n1 < n2))
  | EqOp => LitBool (bool_decide (n1 = n2))
  | OffsetOp => LitInt (n1 + n2) (* Treat offsets as ints *)
  end%Z.


Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp => None (* InEquality *)
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  | OffsetOp => None
  end.

Definition bin_op_eval_loc (op : bin_op) (l1 : loc) (v2 : base_lit) : option base_lit :=
  match op, v2 with
  | OffsetOp, LitInt off => Some $ LitLoc (l1 +ₗ off)
  | LeOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 ≤ₗ l2))
  | LtOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 <ₗ l2))
  | _, _ => None
  end.

Definition bin_op_eval_real (op : bin_op) (r1 r2 : R) : option base_lit :=
  match op with
  | PlusOp => Some $ LitReal (r1 + r2)
  | MinusOp => Some $ LitReal (r1 - r2)
  | MultOp => Some $ LitReal (r1 * r2)
  | LeOp => Some $ LitBool $ bool_decide $ classical.make_decision (r1 <= r2)%R
  | LtOp => Some $ LitBool $ bool_decide $ classical.make_decision (r1 < r2)%R
  | EqOp => Some $ LitBool $ bool_decide $ classical.make_decision (r1 = r2)%R
  | _ => None
  end%R.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if decide (op = EqOp) then
    if decide (v1 = v2) then
      Some $ LitV $ LitBool $ bool_decide (v1 = v2)
    else
      None
  else
    match v1 , v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => Some $ LitV $ bin_op_eval_int op n1 n2
    | LitV (LitReal r1), LitV (LitReal r2) => LitV <$> bin_op_eval_real op r1 r2
    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | LitV (LitLoc l1), LitV v2 => LitV <$> bin_op_eval_loc op l1 v2
    | _, _ => None
    end.

(* #[local] Open Scope R.  *)


Definition cfg : measurableType _ := (expr * state)%type.

Section unif.
  Local Open Scope ereal_scope.
  Local Open Scope classical_set_scope.
  (* Uniform space over [0, 1]*)
  Definition unif_base : subprobability _ R := uniform_prob (@Num.Internals.ltr01 R).
End unif.









Section meas_semantics.
  Local Open Scope ereal_scope.
  Local Open Scope classical_set_scope.

  (** The head_step relation
        - Cover for the pattern match
        - Function for each case (doesn't use pattern match)
          - Measuability of each function on the cover

        Since the top-level cover is just pattern matching on expr, it's of the form
          (measurable expr set, setT of states)
        This means that I can define it in terms of generic lifts of ecov.
   *)

  (* Lift a set S to [ (s, σ) | s ∈ S, σ ∈ State ] *)
  Definition NonStatefulS {A : Type} (S : set A) : set (A * state) := preimage fst S.

  Lemma NonStatefulS_measurable {d} {T : measurableType d} (S : set T) (HS : measurable S) :
      measurable (NonStatefulS S).
  Proof.
    rewrite <- (setTI (NonStatefulS S)).
    rewrite /NonStatefulS.
    apply measurable_fst; [|done].
    by eapply @measurableT.
  Qed.


  (**  The top-level cover for head_step *)

  Definition cover_rec             : set cfg := NonStatefulS ecov_rec. (*[set c | ∃ f x e σ,      c = (Rec f x e, σ) ]. **)
  (*
  Definition cover_pair            : set cfg := [set c | ∃ v1 v2 σ,      c = (Pair (Val v1) (Val v2), σ) ].
  Definition cover_injL            : set cfg := [set c | ∃ v σ,          c = (InjL v, σ) ].
  Definition cover_injR            : set cfg := [set c | ∃ v σ,          c = (InjR v, σ) ].
  Definition cover_app             : set cfg := [set c | ∃ f x e1 v2 σ,  c = (App (Val (RecV f x e1)) (Val v2) , σ) ].
  Definition cover_unop_ok         : set cfg := [set c | ∃ v op w σ,     c = (UnOp op (Val v), σ) /\ un_op_eval op v = Some w].
  Definition cover_unop_stuck      : set cfg := [set c | ∃ v op σ,       c = (UnOp op (Val v), σ) /\ un_op_eval op v = None ].
  Definition cover_binop_ok        : set cfg := [set c | ∃ v1 v2 op w σ, c = (BinOp op (Val v1) (Val v2), σ) /\ bin_op_eval op v1 v2 = Some w].
  Definition cover_binop_stuck     : set cfg := [set c | ∃ v1 v2 op σ,   c = (BinOp op (Val v1) (Val v2), σ) /\ bin_op_eval op v1 v2 = None].
  Definition cover_ifT             : set cfg := [set c | ∃ e1 e2 σ,      c = (If (Val (LitV (LitBool true))) e1 e2, σ) ].
  Definition cover_ifF             : set cfg := [set c | ∃ e1 e2 σ,      c = (If (Val (LitV (LitBool false))) e1 e2, σ) ].
  Definition cover_fst             : set cfg := [set c | ∃ v1 v2 σ,      c = (Fst (Val (PairV v1 v2)), σ) ].
  Definition cover_snd             : set cfg := [set c | ∃ v1 v2 σ,      c = (Snd (Val (PairV v1 v2)), σ) ].
  Definition cover_caseL           : set cfg := [set c | ∃ v e1 e2 σ,    c = (Case (Val (InjLV v)) e1 e2, σ) ].
  Definition cover_caseR           : set cfg := [set c | ∃ v e1 e2 σ,    c = (Case (Val (InjRV v)) e1 e2, σ) ].
  Definition cover_allocN_ok       : set cfg := [set c | ∃ N v σ,        c = (AllocN (Val (LitV (LitInt N))) (Val v), σ) /\ bool_decide (0 < Z.to_nat N)%nat = true].
  Definition cover_allocN_stuck    : set cfg := [set c | ∃ N v σ,        c = (AllocN (Val (LitV (LitInt N))) (Val v), σ) /\ bool_decide (0 < Z.to_nat N)%nat = false].
  Definition cover_load_ok         : set cfg := [set c | ∃ l w σ,        c = (Load (Val (LitV (LitLoc l))), σ) /\ σ.(heap) !! l = Some w].
  Definition cover_load_stuck      : set cfg := [set c | ∃ l σ,          c = (Load (Val (LitV (LitLoc l))), σ) /\ σ.(heap) !! l = None].
  Definition cover_store_ok        : set cfg := [set c | ∃ l w w' σ,     c = (Store (Val (LitV (LitLoc l))) (Val w), σ) /\ σ.(heap) !! l = Some w'].
  Definition cover_store_stuck     : set cfg := [set c | ∃ l w σ,        c = (Store (Val (LitV (LitLoc l))) (Val w), σ) /\ σ.(heap) !! l = None ].
  Definition cover_randE           : set cfg := [set c | ∃ N σ,          c = (Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)), σ) ].
  Definition cover_alloctape       : set cfg := [set c | ∃ z σ,          c = (AllocTape (Val (LitV (LitInt z))), σ) ].
  Definition cover_randT_notape    : set cfg := [set c | ∃ N l σ,        c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = None ].
  Definition cover_randT_mismatch  : set cfg := [set c | ∃ N l b σ,      c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = Some b /\ (bool_decide (b.(btape_bound) = Z.to_nat N) = false)].
  Definition cover_randT_empty     : set cfg := [set c | ∃ N l b σ,      c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = Some b /\ (bool_decide (b.(btape_bound) = Z.to_nat N) = true) /\ (b.(btape_tape) !! 0) = None].
  Definition cover_randT           : set cfg := [set c | ∃ N l b n σ,    c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = Some b /\ (bool_decide (b.(btape_bound) = Z.to_nat N) = true) /\ (b.(btape_tape) !! 0) = Some n].
  Definition cover_allocutape      : set cfg := [set c | ∃ σ,            c = (AllocUTape, σ) ].
  Definition cover_urandE          : set cfg := [set c | ∃ σ,            c = (URand (Val (LitV LitUnit)), σ) ].
  Definition cover_urandT_notape   : set cfg := [set c | ∃ σ l,          c = (URand (Val (LitV (LitLbl l))), σ) /\ σ.(utapes) !! l = None ].
  Definition cover_urandT_empty    : set cfg := [set c | ∃ σ l τ,        c = (URand (Val (LitV (LitLbl l))), σ) /\ σ.(utapes) !! l = Some τ /\ (τ !! 0) = None].
  Definition cover_urandT          : set cfg := [set c | ∃ σ l τ v,      c = (URand (Val (LitV (LitLbl l))), σ) /\ σ.(utapes) !! l = Some τ /\ (τ !! 0) = Some v].
  Definition cover_tick            : set cfg := [set c | ∃ σ n,          c = (Tick (Val (LitV (LitInt n))), σ) ].
  *)
  Definition cover_maybe_stuck     : set cfg := setT.

  Definition cfg_cover : list (set cfg) := [
    cover_rec;
    (*
    cover_pair;
    cover_injL;
    cover_injR;
    cover_app;
    cover_unop_ok;
    cover_unop_stuck;
    cover_binop_ok;
    cover_binop_stuck;
    cover_ifT;
    cover_ifF;
    cover_fst;
    cover_snd;
    cover_caseL;
    cover_caseR;
    cover_allocN_ok;
    cover_allocN_stuck;
    cover_load_ok;
    cover_load_stuck;
    cover_store_stuck;
    cover_store_ok;
    cover_randE;
    cover_alloctape;
    cover_randT_notape;
    cover_randT_mismatch;
    cover_randT_empty;
    cover_randT;
    cover_allocutape;
    cover_urandE;
    cover_urandT_notape;
    cover_urandT_empty;
    cover_urandT;
    cover_tick;
    *)
    cover_maybe_stuck
  ].

  (**The top-level cover is a cover *)

  Lemma cfg_cover_is_cover : List.fold_right setU set0 cfg_cover = setT.
  Proof.
    rewrite /cfg_cover/=/cover_maybe_stuck.
    rewrite setTU.
    repeat rewrite setUT.
    done.
  Qed.

  (** The top-level cover is measurable *)
  (* TODO: Register hint database for this *)

  Lemma cover_rec_measurable : measurable cover_rec.
  Proof. by apply NonStatefulS_measurable, ecov_rec_meas. Qed.


  (**  Top-level functions *)

  (* Generic lifting of a curried constructor on expr to a curried constructor on states *)
  Definition NonStatefulU {A : Type} (C : A -> expr) : (A * state) -> cfg := fun x => (C x.1, x.2).

  (** NOTE!!! ssrfun.comp, measurable_comp *)

  Lemma NonStatefulU_meas {d} {A : measurableType d} (C : A -> expr) (S : set A) (HS : measurable S)
      (HC : measurable_fun S C) : measurable_fun (NonStatefulS S) (NonStatefulU C).
  Proof.
    rewrite /NonStatefulU//=.
    have H1 : measurable_fun (T:=A) (U:=A) S m_id.
    { apply mathcomp_measurable_fun_restiction_setT; [done|].
      by apply measurable_mapP.
    }
    apply (measurable_fun_prod' (ssrfun.comp C fst) snd (NonStatefulS S) (NonStatefulS_measurable S HS)).
    - eapply measurable_comp.
      3: { by apply HC. }
      + by apply HS.
      + by rewrite /NonStatefulS/preimage/subset//=; move=> t [??<-].
      + apply (mathcomp_measurable_fun_restiction_setT (NonStatefulS S) (NonStatefulS_measurable S HS) fst).
        by apply measurable_fst.
    - apply (mathcomp_measurable_fun_restiction_setT (NonStatefulS S) (NonStatefulS_measurable S HS) snd).
        by apply measurable_snd.
  Qed.



  (** Top-level functions *)
  Definition head_stepM_rec : cfg -> giryM cfg :=
    (ssrfun.comp (giryM_ret R) (NonStatefulU (ssrfun.comp ValU $ ssrfun.comp RecVU 𝜋_RecU))).


  Definition head_stepM_def (c : cfg) : giryM cfg :=
    let (e1, σ1) := c in
    match e1 with
    | Rec _ _ _ => head_stepM_rec c
    | _ => giryM_zero
    end.


  (** Top-level functions measurabiilty *)
  Lemma head_stepM_rec_meas : measurable_fun cover_rec head_stepM_def.
  Proof.
  (* Old proof
      eapply (mathcomp_measurable_fun_ext cover_rec _ head_stepM_meas_def_Rec head_stepM_def).
      - (* This function is measurable by construction *)
        unfold head_stepM_meas_def_Rec.
        eapply measurable_fun_compose'. { admit. }
        - have X : cover_rec = NonStatefulS ecov_rec. { admit. }
          rewrite X; clear X.
          apply NonStatefulU_meas.
          eapply measurable_fun_compose'. { admit.  }
          - apply 𝜋_RecU_measurable.
          - eapply measurable_fun_compose'. { admit.  }
            - apply RecVU_measurable.
            - apply ValU_measurable.
        - apply measurable_mapP.
      - (* The two functions are equal on this set. *)
        intros x.
        rewrite /cover_rec/=.
        do 4 move=> [?+].
        by move=>->//=.
      *)
  Admitted.


  (**  Head step measurability *)
  Lemma cfg_cover_measurable :
      Forall (fun S => measurable S) cfg_cover.
  Proof.
    repeat (try apply Forall_cons; split); last by apply List.Forall_nil.
    - admit.
    - admit.
  Admitted.


  Lemma head_stepM_def_restricted_measurable :
      Forall (fun S => measurable_fun S head_stepM_def) cfg_cover.
  Proof.
    repeat (try apply Forall_cons; split); last by apply List.Forall_nil.
    - admit.
    - admit.
  Admitted.

  Local Lemma head_stepM_def_measurable :
    @measurable_fun _ _ cfg (giryM cfg) setT head_stepM_def.
  Proof.
    apply (@measurable_by_cover_list _ _ _ _ head_stepM_def cfg_cover).
    - by apply cfg_cover_measurable.
    - by apply cfg_cover_is_cover.
    - suffices HFdep :
          (Forall (λ l : set cfg,
                     elem_of_list l cfg_cover ->
                     measurable_fun (T:=cfg) (U:=types.giryM cfg) l (head_stepM_def \_ l)) cfg_cover).
      { apply Forall_forall.
        intros x Hx.
        by apply (iffLR (Forall_forall _ _) HFdep x Hx Hx).
      }
      eapply (Forall_impl _ _ _ head_stepM_def_restricted_measurable).
      intros S H HS.
      apply mathcomp_restriction_is_measurable in H; last first.
      { eapply Forall_forall.
        - by apply cfg_cover_measurable.
        - by apply HS. }
      by apply mathcomp_restriction_setT.
  Qed.

  HB.instance Definition _ :=
    isMeasurableMap.Build _ _ _ _ _ head_stepM_def_measurable.

  Definition head_stepM : measurable_map cfg (giryM cfg) :=
    head_stepM_def.

End meas_semantics.


(*
  Definition head_stepM_def (c : cfg) : giryM cfg :=
    let (e1, σ1) := c in
    match e1 with
    | Rec f x e =>
        giryM_ret R ((Val $ RecV f x e, σ1) : cfg)
    | Pair (Val v1) (Val v2) =>
        giryM_ret R ((Val $ PairV v1 v2, σ1) : cfg)
    | InjL (Val v) =>
        giryM_ret R ((Val $ InjLV v, σ1) : cfg)
    | InjR (Val v) =>
        giryM_ret R ((Val $ InjRV v, σ1) : cfg)
    | App (Val (RecV f x e1)) (Val v2) =>
        giryM_ret R ((subst' x v2 (subst' f (RecV f x e1) e1) , σ1) : cfg)
    | UnOp op (Val v) =>
        match un_op_eval op v with
          | Some w => giryM_ret R ((Val w, σ1) : cfg)
          | _ => giryM_zero
        end
    | BinOp op (Val v1) (Val v2) =>
        match bin_op_eval op v1 v2 with
          | Some w => giryM_ret R ((Val w, σ1) : cfg)
          | _ => giryM_zero
        end
    | If (Val (LitV (LitBool true))) e1 e2  =>
        giryM_ret R ((e1 , σ1) : cfg)
    | If (Val (LitV (LitBool false))) e1 e2 =>
        giryM_ret R ((e2 , σ1) : cfg)
    | Fst (Val (PairV v1 v2)) =>
        giryM_ret R ((Val v1 , σ1) : cfg) (* Syntax error when I remove the space between v1 and , *)
    | Snd (Val (PairV v1 v2)) =>
        giryM_ret R ((Val v2, σ1) : cfg)
    | Case (Val (InjLV v)) e1 e2 =>
        giryM_ret R ((App e1 (Val v), σ1) : cfg)
    | Case (Val (InjRV v)) e1 e2 =>
        giryM_ret R ((App e2 (Val v), σ1) : cfg)
    | AllocN (Val (LitV (LitInt N))) (Val v) =>
        let ℓ := fresh_loc σ1.(heap) in
        if bool_decide (0 < Z.to_nat N)%nat
          then giryM_ret R ((Val $ LitV $ LitLoc ℓ, state_upd_heap_N ℓ (Z.to_nat N) v σ1) : cfg)
          else giryM_zero
    | Load (Val (LitV (LitLoc l))) =>
        match σ1.(heap) !! l with
          | Some v => giryM_ret R ((Val v, σ1) : cfg)
          | None => giryM_zero
        end
    | Store (Val (LitV (LitLoc l))) (Val w) =>
        match σ1.(heap) !! l with
          | Some v => giryM_ret R ((Val $ LitV LitUnit, state_upd_heap <[l:=w]> σ1) : cfg)
          | None => giryM_zero
        end
    (* Uniform sampling from [0, 1 , ..., N] *)
    | Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)) =>
        giryM_map
          (m_discr (fun (n : 'I_(S (Z.to_nat N))) => ((Val $ LitV $ LitInt $ fin_to_nat n, σ1) : cfg)))
          (giryM_unif (Z.to_nat N))
    | AllocTape (Val (LitV (LitInt z))) =>
        let ι := fresh_loc σ1.(tapes) in
        giryM_ret R ((Val $ LitV $ LitLbl ι, state_upd_tapes <[ι := {| btape_tape := emptyTape ; btape_bound := (Z.to_nat z) |} ]> σ1) : cfg)
    (* Rand with a tape *)
    | Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))) =>
        match σ1.(tapes) !! l with
        | Some btape =>
            (* There exists a tape with label l *)
            let τ := btape.(btape_tape) in
            let M := btape.(btape_bound) in
            if (bool_decide (M = Z.to_nat N)) then
              (* Tape bounds match *)
              match (τ !! 0) with
              | Some v =>
                  (* There is a next value on the tape *)
                  let σ' := state_upd_tapes <[ l := {| btape_tape := (tapeAdvance τ); btape_bound := M |} ]> σ1 in
                  (giryM_ret R ((Val $ LitV $ LitInt $ Z.of_nat v, σ') : cfg))
              | None =>
                  (* Next slot on tape is empty *)
                  giryM_map
                    (m_discr (fun (v : 'I_(S (Z.to_nat N))) =>
                       (* Fill the tape head with new sample *)
                       let τ' := <[ (0 : nat) := Some (v : nat) ]> τ in
                       (* Advance the tape *)
                       let σ' := state_upd_tapes <[ l := {| btape_tape := (tapeAdvance τ'); btape_bound := M |} ]> σ1 in
                       (* Return the new sample and state *)
                       ((Val $ LitV $ LitInt $ Z.of_nat v, σ') : cfg)))
                   (giryM_unif (Z.to_nat N))
              end
            else
              (* Tape bounds do not match *)
              (* Do not advance the tape, but still generate a new sample *)
              giryM_map
                (m_discr (fun (n : 'I_(S (Z.to_nat N))) => (((Val $ LitV $ LitInt $ fin_to_nat n) : <<discr expr>>), σ1) : cfg))
                (giryM_unif (Z.to_nat N))
        | None => giryM_zero
        end
    | AllocUTape =>
        let ι := fresh_loc σ1.(utapes) in
        giryM_ret R ((Val $ LitV $ LitLbl ι, state_upd_utapes <[ ι := emptyTape ]> σ1) : cfg)
    (* Urand with no tape *)
    | URand (Val (LitV LitUnit)) => giryM_zero (* FIXME giryM_map urand_step unif_base *)
    (* Urand with a tape *)
    | URand (Val (LitV (LitLbl l))) =>
        match σ1.(utapes) !! l with
        | Some τ =>
            (* tape l is allocated *)
            match (τ !! 0) with
            | Some u =>
                (* Head has a sample *)
                let σ' := state_upd_utapes <[ l := (tapeAdvance τ) ]> σ1 in
                (giryM_ret R ((Val $ LitV $ LitReal u, σ') : cfg))
            | None =>
                (* Head has no sample *)
                giryM_zero
                (* FIXME giryM_map urand_tape_step unif_base *)
            end
        | None => giryM_zero
        end
    | Tick (Val (LitV (LitInt n))) => giryM_ret R ((Val $ LitV $ LitUnit, σ1) : cfg)
    | _ => giryM_zero
    end.
*)

  (*


  Definition urand_tape_step : measurable_map ((R : realType) : measurableType _) cfg.
  Admitted.
    (* This funciton needs to do this: *)
    (* (fun (u : R) =>
         (* Fill tape head with new sample *)
         let τ' := <[ (0 : nat) := Some u ]> τ in
         (* Advance tape *)
         let σ' := state_upd_utapes <[ l := (tapeAdvance τ') ]> σ1 in
         (* Return the update value an state *)
         ((Val $ LitV $ LitReal u, σ') : cfg)) *)






(*
Lemma state_step_unfold σ α N ns:
  tapes σ !! α = Some (N; ns) ->
  state_step σ α = dmap (λ n, state_upd_tapes (<[α := (N; ns ++ [n])]>) σ) (dunifP N).
Proof.
  intros H.
  rewrite /state_step.
  rewrite bool_decide_eq_true_2; last first.
  { by apply elem_of_dom. }
  by rewrite (lookup_total_correct (tapes σ) α (N; ns)); last done.
Qed.
*)

(** Basic properties about the language *)
Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.

(* ??? *)
(*
Lemma val_head_stuck e σ ρ :
  head_step e σ ρ > 0 → to_val e = None.
Proof. destruct ρ, e; [|done..]. rewrite /pmf /=. lra. Qed.

Lemma head_ctx_step_val Ki e σ ρ :
  head_step (fill_item Ki e) σ ρ > 0 → is_Some (to_val e).
Proof.
  destruct ρ, Ki ;
    rewrite /pmf/= ;
    repeat case_match; clear -H ; inversion H; intros ; (lra || done).
Qed.

*)

Local Open Scope classical_set_scope.

(** A relational characterization of the support of [head_step] to make it easier to
    do inversion and prove reducibility easier c.f. lemma below *)
Inductive head_step_rel : expr -> state -> expr -> state → Prop :=
(* Values *)
| RecS f x e σ :
  head_step_rel (Rec f x e) σ (Val $ RecV f x e) σ
| PairS v1 v2 σ :
  head_step_rel (Pair (Val v1) (Val v2)) σ (Val $ PairV v1 v2) σ
| InjLS v σ :
  head_step_rel (InjL $ Val v) σ (Val $ InjLV v) σ
| InjRS v σ :
  head_step_rel (InjR $ Val v) σ (Val $ InjRV v) σ

(* Pure reductions *)
| BetaS f x e1 v2 e' σ :
  e' = subst' x v2 (subst' f (RecV f x e1) e1) →
  head_step_rel (App (Val $ RecV f x e1) (Val v2)) σ e' σ
| UnOpS op v v' σ :
  un_op_eval op v = Some v' →
  head_step_rel (UnOp op (Val v)) σ (Val v') σ
| BinOpS op v1 v2 v' σ :
  bin_op_eval op v1 v2 = Some v' →
  head_step_rel (BinOp op (Val v1) (Val v2)) σ (Val v') σ
| IfTrueS e1 e2 σ :
  head_step_rel (If (Val $ LitV $ LitBool true) e1 e2) σ e1 σ
| IfFalseS e1 e2 σ :
  head_step_rel (If (Val $ LitV $ LitBool false) e1 e2) σ e2 σ
| FstS v1 v2 σ :
  head_step_rel (Fst (Val $ PairV v1 v2)) σ (Val v1) σ
| SndS v1 v2 σ :
  head_step_rel (Snd (Val $ PairV v1 v2)) σ (Val v2) σ
| CaseLS v e1 e2 σ :
  head_step_rel (Case (Val $ InjLV v) e1 e2) σ (App e1 (Val v)) σ
| CaseRS v e1 e2 σ :
  head_step_rel (Case (Val $ InjRV v) e1 e2) σ (App e2 (Val v)) σ

(* Heap *)
| AllocNS z N v σ l :
  l = fresh_loc σ.(heap) →
  N = Z.to_nat z →
  (0 < N)%nat ->
  head_step_rel
    (AllocN (Val (LitV (LitInt z))) (Val v)) σ
    (Val $ LitV $ LitLoc l) (state_upd_heap_N l N v σ)
| LoadS l v σ :
  σ.(heap) !! l = Some v →
  head_step_rel (Load (Val $ LitV $ LitLoc l)) σ (of_val v) σ
| StoreS l v w σ :
  σ.(heap) !! l = Some v →
  head_step_rel (Store (Val $ LitV $ LitLoc l) (Val w)) σ
    (Val $ LitV LitUnit) (state_upd_heap <[l:=w]> σ)

(* Rand *)
| RandNoTapeS z N (n_int : Z) (n_nat : nat) σ:
  N = Z.to_nat z →
  n_nat < N ->
  Z.of_nat n_nat = n_int ->
  head_step_rel (Rand (Val $ LitV $ LitInt z) (Val $ LitV LitUnit)) σ (Val $ LitV $ LitInt n_int) σ
| AllocTapeS z N σ l :
  l = fresh_loc σ.(tapes) →
  N = Z.to_nat z →
  head_step_rel (AllocTape (Val (LitV (LitInt z)))) σ
    (Val $ LitV $ LitLbl l) (state_upd_tapes <[l := {| btape_tape := emptyTape ; btape_bound := N |}]> σ)
| RandTapeS l z N n b b' σ :
  N = Z.to_nat z →
  σ.(tapes) !! l = Some {| btape_tape := b ; btape_bound := N |} ->
  b !! 0 = Some (Z.to_nat n) ->
  b' = tapeAdvance b ->
  head_step_rel (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl l)))) σ
    (Val $ LitV $ LitInt $ n) (state_upd_tapes <[l := {| btape_tape := b' ; btape_bound := N|}]> σ)
| RandTapeEmptyS l z N (n_nat : nat) (n_int : Z) σ :
  N = Z.to_nat z →
  Z.of_nat n_nat = n_int ->
  n_nat < N ->
  σ.(tapes) !! l = Some {| btape_tape := emptyTape; btape_bound := N |} →
  head_step_rel (Rand (Val (LitV (LitInt z))) (Val $ LitV $ LitLbl l)) σ  (Val $ LitV $ LitInt $ n_int) σ
| RandTapeOtherS l z M N b (n_nat : nat) (n_int : Z) σ :
  N = Z.to_nat z →
  Z.of_nat n_nat = n_int ->
  n_nat < N ->
  σ.(tapes) !! l = Some {| btape_tape := b ; btape_bound := M |} →
  N ≠ M →
  head_step_rel (Rand (Val (LitV (LitInt z))) (Val $ LitV $ LitLbl l)) σ (Val $ LitV $ LitInt n_int) σ

(* Urand *)
| URandNoTapeS (r : R) σ :
  (0 <= r)%R ->
  (r <= 1)%R ->
  head_step_rel (URand (Val $ LitV LitUnit)) σ (Val $ LitV $ LitReal r) σ
| AllocUTapeS σ l :
  l = fresh_loc σ.(tapes) →
  head_step_rel AllocUTape σ
    (Val $ LitV $ LitLbl l) (state_upd_utapes <[l := emptyTape]> σ)
| URandTapeS l b b' r σ :
  σ.(utapes) !! l = Some b ->
  b !! 0 = Some r ->
  b' = tapeAdvance b ->
  head_step_rel (URand (Val (LitV (LitLbl l)))) σ
    (Val $ LitV $ LitReal $ r) (state_upd_utapes <[l := b]> σ)
| URandTapeEmptyS l (r : R) b σ :
  (0 <= r)%R ->
  (r <= 1)%R ->
  σ.(utapes) !! l = Some b →
  head_step_rel (URand (Val $ LitV $ LitLbl l)) σ (Val $ LitV $ LitReal r) σ

(* Tick *)
| TickS σ z :
  head_step_rel (Tick $ Val $ LitV $ LitInt z) σ (Val $ LitV $ LitUnit) σ.

Create HintDb head_step.
Global Hint Constructors head_step_rel : head_step.
(* 0%fin always has non-zero mass, so propose this choice if the reduct is
   unconstrained. *)
Global Hint Extern 1
  (head_step_rel (Rand (Val (LitV _)) (Val (LitV LitUnit))) _ _ _) =>
         eapply (RandNoTapeS _ _ 0%fin) : head_step.
Global Hint Extern 1
  (head_step_rel (Rand (Val (LitV _)) (Val (LitV (LitLbl _)))) _ _ _) =>
         eapply (RandTapeEmptyS _ _ _ 0%fin) : head_step.
Global Hint Extern 1
  (head_step_rel (Rand (Val (LitV _)) (Val (LitV (LitLbl _)))) _ _ _) =>
         eapply (RandTapeOtherS _ _ _ _ _ 0%fin) : head_step.

(*
Ltac inv_head_step :=
  repeat
    match goal with
    | H : context [@bool_decide ?P ?dec] |- _ =>
        try (rewrite bool_decide_eq_true_2 in H; [|done]);
        try (rewrite bool_decide_eq_false_2 in H; [|done]);
        destruct_decide (@bool_decide_reflect P dec); simplify_eq
    | _ => progress simplify_map_eq; simpl in *; inv_distr; repeat case_match; inv_distr
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : is_Some (_ !! _) |- _ => destruct H
    end.

Lemma head_step_support_equiv_rel e1 e2 σ1 σ2 :
  head_step e1 σ1 (e2, σ2) > 0 ↔ head_step_rel e1 σ1 e2 σ2.
Proof.
  split.
  - intros ?. destruct e1; inv_head_step; eauto with head_step.
  - inversion 1; simplify_map_eq/=; try case_bool_decide; simplify_eq; solve_distr; done.
Qed.

Lemma state_step_support_equiv_rel σ1 α σ2 :
  state_step σ1 α σ2 > 0 ↔ state_step_rel σ1 α σ2.
Proof.
  rewrite /state_step. split.
  - case_bool_decide; [|intros; inv_distr].
    case_match. intros ?. inv_distr.
    econstructor; eauto with lia.
  - inversion_clear 1.
    rewrite bool_decide_eq_true_2 // H1. solve_distr.
Qed.

Lemma state_step_head_step_not_stuck e σ σ' α :
  state_step σ α σ' > 0 → (∃ ρ, head_step e σ ρ > 0) ↔ (∃ ρ', head_step e σ' ρ' > 0).
Proof.
  rewrite state_step_support_equiv_rel.
  inversion_clear 1.
  split; intros [[e2 σ2] Hs].
  (* TODO: the sub goals used to be solved by [simplify_map_eq]  *)
  - destruct e; inv_head_step; try by (unshelve (eexists; solve_distr)).
    + destruct (decide (α = l1)); simplify_eq.
      * rewrite lookup_insert in H11. done.
      * rewrite lookup_insert_ne // in H11. rewrite H11 in H7. done.
    + destruct (decide (α = l1)); simplify_eq.
      * rewrite lookup_insert in H11. done.
      * rewrite lookup_insert_ne // in H11. rewrite H11 in H7. done.
    + destruct (decide (α = l1)); simplify_eq.
      * rewrite lookup_insert in H10. done.
      * rewrite lookup_insert_ne // in H10. rewrite H10 in H7. done.
  - destruct e; inv_head_step; try by (unshelve (eexists; solve_distr)).
    + destruct (decide (α = l1)); simplify_eq.
      * apply not_elem_of_dom_2 in H11. done.
      * rewrite lookup_insert_ne // in H7. rewrite H11 in H7.  done.
    + destruct (decide (α = l1)); simplify_eq.
      * rewrite lookup_insert // in H7.
        apply not_elem_of_dom_2 in H11. done.
      * rewrite lookup_insert_ne // in H7. rewrite H11 in H7. done.
    + destruct (decide (α = l1)); simplify_eq.
      * rewrite lookup_insert // in H7.
        apply not_elem_of_dom_2 in H10. done.
      * rewrite lookup_insert_ne // in H7. rewrite H10 in H7. done.
Qed.

*)

(*
Lemma head_step_mass e σ :
  (∃ ρ, head_step e σ ρ > 0) → SeriesC (head_step e σ) = 1.
Proof.
  intros [[] Hs%head_step_support_equiv_rel].
  inversion Hs;
    repeat (simplify_map_eq/=; solve_distr_mass || case_match; try (case_bool_decide; done)).
Qed.
*)
Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof. destruct Ki2, Ki1; naive_solver eauto with f_equal. Qed.
Fixpoint height (e : expr) : nat :=
  match e with
  | Val _ => 1
  | Var _ => 1
  | Rec _ _ e => 1 + height e
  | App e1 e2 => 1 + height e1 + height e2
  | UnOp _ e => 1 + height e
  | BinOp _ e1 e2 => 1 + height e1 + height e2
  | If e0 e1 e2 => 1 + height e0 + height e1 + height e2
  | Pair e1 e2 => 1 + height e1 + height e2
  | Fst e => 1 + height e
  | Snd e => 1 + height e
  | InjL e => 1 + height e
  | InjR e => 1 + height e
  | Case e0 e1 e2 => 1 + height e0 + height e1 + height e2
  | AllocN e1 e2 => 1 + height e1 + height e2
  | Load e => 1 + height e
  | Store e1 e2 => 1 + height e1 + height e2
  | AllocTape e => 1 + height e
  | AllocUTape => 1
  | Rand e1 e2 => 1 + height e1 + height e2
  | URand e => 1 + height e
  | Tick e => 1 + height e
  end.

Definition expr_ord (e1 e2 : expr) : Prop := (height e1 < height e2)%nat.

Lemma expr_ord_wf' h e : (height e ≤ h)%nat → Acc expr_ord e.
Proof.
  rewrite /expr_ord. revert e; induction h.
  { destruct e; simpl; lia. }
  intros []; simpl;
    constructor; simpl; intros []; eauto with lia.
Defined.

Lemma expr_ord_wf : well_founded expr_ord.
Proof. red; intro; eapply expr_ord_wf'; eauto. Defined.


(* TODO: this proof is slow, but I do not see how to make it faster... *)
(* TODO: Uncomment the slow proof *)
Lemma decomp_expr_ord Ki e e' : decomp_item e = Some (Ki, e') → expr_ord e' e.
Proof. Admitted.
(*
  rewrite /expr_ord /decomp_item.
  destruct Ki ; repeat destruct_match ; intros [=] ; subst ; cbn ; lia.
Qed. *)

Lemma decomp_fill_item Ki e :
  to_val e = None → decomp_item (fill_item Ki e) = Some (Ki, e).
Proof. destruct Ki ; simpl ; by repeat destruct_match. Qed.

(* TODO: this proof is slow, but I do not see how to make it faster... *)
(* TODO: Uncomment the slow proof *)
Lemma decomp_fill_item_2 e e' Ki :
  decomp_item e = Some (Ki, e') → fill_item Ki e' = e ∧ to_val e' = None.
Proof. Admitted.
(*
  rewrite /decomp_item ;
    destruct e ; try done ;
    destruct Ki ; cbn ; repeat destruct_match ; intros [=] ; subst ; auto.
Qed. *)

Local Open Scope classical_set_scope.

Definition fill_item_mf (K : ectx_item) : measurable_map expr expr.
Admitted.
(*   := m_discr (fill_item K : <<discr expr>> -> <<discr expr>>).  *)

Definition meas_lang_mixin :
  @MeasEctxiLanguageMixin _ _ _ expr val state ectx_item
    of_val to_val fill_item_mf decomp_item expr_ord head_stepM_def.
Proof.
  split.
  - apply to_of_val.
  - apply of_to_val.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.


End meas_lang.

(** Language *)


Canonical Structure meas_ectxi_lang := MeasEctxiLanguage meas_lang.head_stepM meas_lang.meas_lang_mixin.
Canonical Structure meas_ectx_lang := MeasEctxLanguageOfEctxi meas_ectxi_lang.
Canonical Structure meas_lang := MeasLanguageOfEctx meas_ectx_lang.

(* Prefer meas_lang names over ectx_language names. *)
Export meas_lang.
*)
