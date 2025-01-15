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
From clutch.meas_lang.lang Require Export prelude types constructors shapes cover projections tapes state subst pureops.
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
  Hint Resolve NonStatefulS_measurable : measlang.





  (**  The top-level cover for head_step *)

  (* [set c | ∃ f x e σ, c = (Rec f x e, σ) ]. *)
  Definition cover_rec : set cfg :=
    NonStatefulS ecov_rec.

  (*[set c | ∃ v1 v2 σ, c = (Pair (Val v1) (Val v2), σ) ].*)
  Program Definition cover_pair : set cfg :=
    NonStatefulS $
    setI ecov_pair $
    preimage 𝜋_PairU $
    (ecov_val `*` ecov_val).

  (* [set c | ∃ v σ, c = (InjL (Val v), σ) ]. *)
  Definition cover_injL : set cfg :=
    NonStatefulS $
    setI ecov_injl $
    preimage 𝜋_InjLU $
    ecov_val.

  (* [set c | ∃ v σ, c = (InjR (Val v), σ) ]. *)
  Definition cover_injR : set cfg :=
    NonStatefulS $
    setI ecov_injr $
    preimage 𝜋_InjRU $
    ecov_val.

  (*  [set c | ∃ f x e1 v2 σ,  c = (App (Val (RecV f x e1)) (Val v2) , σ) ]. *)
  Definition cover_app : set cfg :=
    NonStatefulS $
    setI ecov_app $
    preimage 𝜋_AppU $
    setX
      ( setI ecov_val $
        preimage 𝜋_Val_v $
        vcov_rec )
      ecov_val.

  Definition cover_unop_ok' : set expr :=
    setI ecov_unop $
    preimage 𝜋_UnOpU $
    setI (setX setT ecov_val) $
    preimage (mProd fst (ssrfun.comp 𝜋_Val_v snd)) $
    auxcov_unop_ok.

  Definition cover_unop_ok : set cfg :=
    setI setT $
    preimage fst $
    cover_unop_ok'.

  Definition cover_unop_stuck : set cfg :=
    setI setT $
    preimage fst $
    setI ecov_unop $
    preimage 𝜋_UnOpU $
    setI (setX setT ecov_val) $
    preimage (mProd fst (ssrfun.comp 𝜋_Val_v snd)) $
    auxcov_unop_stuck.

  Definition cover_binop_ok' : set expr :=
    setI ecov_binop $
    preimage 𝜋_BinOpU $
    setI (setX (setX setT ecov_val) ecov_val) $
    preimage
      (mProd
         (mProd
            (ssrfun.comp fst fst)
            (ssrfun.comp (ssrfun.comp 𝜋_Val_v snd) fst))
         (ssrfun.comp 𝜋_Val_v snd)) $
    auxcov_binop_ok.

  Definition cover_binop_ok : set cfg :=
    setI setT $
    preimage fst $
    cover_binop_ok'.


  Definition cover_binop_stuck : set cfg :=
    setI setT $
    preimage fst $
    setI ecov_binop $
    preimage 𝜋_BinOpU $
    setI (setX (setX setT ecov_val) ecov_val) $
    preimage
      (mProd
         (mProd
            (ssrfun.comp fst fst)
            (ssrfun.comp (ssrfun.comp 𝜋_Val_v snd) fst))
         (ssrfun.comp 𝜋_Val_v snd)) $
    auxcov_binop_stuck.

  (* [set c | ∃ e1 e2 σ, c = (If (Val (LitV (LitBool true))) e1 e2, σ) ]*)
  Definition cover_ifT : set cfg :=
    NonStatefulS $
    setI ecov_if $
    preimage 𝜋_If_c $
    setI ecov_val $
    preimage 𝜋_Val_v $
    setI vcov_lit $
    preimage 𝜋_LitV_v $
    setI bcov_LitBool $
    preimage 𝜋_LitBool_b $
    [set true].

  (* [set c | ∃ e1 e2 σ, c = (If (Val (LitV (LitBool false))) e1 e2, σ) ] *)
  Definition cover_ifF : set cfg :=
    NonStatefulS $
    setI ecov_if $
    preimage 𝜋_If_c $
    setI ecov_val $
    preimage 𝜋_Val_v $
    setI vcov_lit $
    preimage 𝜋_LitV_v $
    setI bcov_LitBool $
    preimage 𝜋_LitBool_b $
    [set false].

  (* [set c | ∃ v1 v2 σ, c = (Fst (Val (PairV v1 v2)), σ) ] *)
  Definition cover_fst : set cfg :=
    NonStatefulS $
    setI ecov_fst $
    preimage 𝜋_Fst_e $
    setI ecov_val $
    preimage 𝜋_Val_v $
    vcov_pair.

  (* [set c | ∃ v1 v2 σ, c = (Snd (Val (PairV v1 v2)), σ) ] *)
  Definition cover_snd : set cfg :=
    NonStatefulS $
    setI ecov_snd $
    preimage 𝜋_Snd_e $
    setI ecov_val $
    preimage 𝜋_Val_v $
    vcov_pair.

  (* [set c | ∃ v e1 e2 σ, c = (Case (Val (InjLV v)) e1 e2, σ) ] *)
  Program Definition cover_caseL : set cfg :=
    NonStatefulS $
    setI ecov_case $
    preimage 𝜋_Case_c $
    setI ecov_val $
    preimage 𝜋_Val_v $
    vcov_injlv.

  (* [set c | ∃ v e1 e2 σ, c = (Case (Val (InjRV v)) e1 e2, σ) ] *)
  Definition cover_caseR : set cfg :=
    NonStatefulS $
    setI ecov_case $
    preimage 𝜋_Case_c $
    setI ecov_val $
    preimage 𝜋_Val_v $
    vcov_injrv.

  (* [set c | ∃ σ n, c = (Tick (Val (LitV (LitInt n))), σ) ]  *)
  Definition cover_tick : set cfg :=
    NonStatefulS $
    setI ecov_tick $
    preimage 𝜋_Tick_e $
    setI ecov_val $
    preimage 𝜋_Val_v $
    setI vcov_lit $
    preimage 𝜋_LitV_v $
    bcov_LitInt.

  (*
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
  *)

  Definition cfg_cover_pre : list (set cfg) := [
    cover_rec;
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
    (*
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
    *)
    cover_tick
  ].

  Definition cover_maybe_stuck : set cfg. Admitted. (* compliment of union of cfg_cover_pre *)

  Definition cfg_cover : list (set cfg) := cfg_cover_pre ++ [cover_maybe_stuck].



  (**The top-level cover is a cover *)

  Lemma cfg_cover_is_cover : List.fold_right setU set0 cfg_cover = setT.
  Proof.
    (* FIXME

    rewrite /cfg_cover/=/cover_maybe_stuck.
    rewrite setTU.
    repeat rewrite setUT.
    done. *)
  Admitted.


  (** The top-level cover is measurable *)

  Lemma cover_rec_meas : measurable cover_rec.
  Proof. by apply NonStatefulS_measurable; eauto with measlang. Qed.
  Hint Resolve cover_rec_meas : measlang.

  Lemma cover_pair_meas : measurable cover_pair.
  Proof.
    apply NonStatefulS_measurable.
    apply 𝜋_PairU_meas; eauto with measlang.
    apply measurableX; by eauto with measlang.
  Qed.
  Hint Resolve cover_pair_meas : measlang.

  Lemma cover_injL_meas : measurable cover_injL.
  Proof.
    apply NonStatefulS_measurable.
    by apply 𝜋_InjLU_meas; eauto with measlang.
  Qed.

  Hint Resolve cover_injL_meas : measlang.

  Lemma cover_injR_meas : measurable cover_injR.
  Proof.
    apply NonStatefulS_measurable.
    by apply 𝜋_InjRU_meas; eauto with measlang.
  Qed.
  Hint Resolve cover_injR_meas : measlang.

  Lemma cover_app_meas : measurable cover_app.
  Proof.
    apply NonStatefulS_measurable.
    apply 𝜋_AppU_meas; eauto with measlang.
    apply measurableX.
    - by apply 𝜋_ValU_meas; eauto with measlang.
    - by eauto with measlang.
  Qed.
  Hint Resolve cover_app_meas : measlang.

  Lemma cover_unop_ok'_meas : measurable cover_unop_ok'.
  Proof.
    apply 𝜋_UnOpU_meas; eauto with measlang.
    eapply (measurable_fun_prod' fst (ssrfun.comp 𝜋_Val_v snd) (setX (setT : set <<discr un_op>>) ecov_val)).
    { apply measurableX; by eauto with measlang. }
    { apply mathcomp_measurable_fun_restiction_setT.
      { apply measurableX; by eauto with measlang. }
      by apply measurable_fst. }
    3: { by apply auxcov_unop_ok_meas. }
    2: { apply measurableX; by eauto with measlang. }
    eapply measurable_comp.
    3: { by eapply 𝜋_Val_v_meas. }
    - by apply ecov_val_meas.
    - rewrite /subset//=.
      by move=>?//=[?[??]]<-//=.
    - eapply (mathcomp_measurable_fun_restiction_setT ([set: <<discr un_op >>] `*` ecov_val) _ snd).
      simpl.
      apply (@measurable_snd _ _ <<discr un_op>> expr).
    Unshelve.
    { apply measurableX; by eauto with measlang. }
  Qed.
  Hint Resolve cover_unop_ok'_meas : measlang.

  Lemma cover_unop_ok_meas : measurable cover_unop_ok.
  Proof. apply @measurable_fst; by eauto with measlang. Qed.
  Hint Resolve cover_unop_ok_meas : measlang.

  Lemma cover_unop_stuck_meas : measurable cover_unop_stuck.
  Proof.
    apply @measurable_fst; first by eauto with measlang.
    apply 𝜋_UnOpU_meas; eauto with measlang.
    eapply (measurable_fun_prod' fst (ssrfun.comp 𝜋_Val_v snd) (setX (setT : set <<discr un_op>>) ecov_val)).
    { apply measurableX; by eauto with measlang. }
    { apply mathcomp_measurable_fun_restiction_setT.
      { apply measurableX; by eauto with measlang. }
      by apply measurable_fst. }
    3: { by apply auxcov_unop_stuck_meas. }
    2: { apply measurableX; by eauto with measlang. }
    eapply measurable_comp.
    3: { by eapply 𝜋_Val_v_meas. }
    - by apply ecov_val_meas.
    - rewrite /subset//=.
      by move=>?//=[?[??]]<-//=.
    - eapply (mathcomp_measurable_fun_restiction_setT ([set: <<discr un_op >>] `*` ecov_val) _ snd).
      simpl.
      apply (@measurable_snd _ _ <<discr un_op>> expr).
    Unshelve.
    { apply measurableX; by eauto with measlang. }
  Qed.
  Hint Resolve cover_unop_stuck_meas : measlang.

  Lemma cover_binop_ok'_meas : measurable cover_binop_ok'.
  Proof.
    apply 𝜋_BinOpU_meas; eauto with measlang.
    eapply (measurable_fun_prod'
              (mProd (ssrfun.comp fst fst) (ssrfun.comp (ssrfun.comp 𝜋_Val_v snd) fst))
              (ssrfun.comp 𝜋_Val_v snd)
              (setX (setX setT ecov_val) ecov_val)).
    1,4: try by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang).
    3: by eauto with measlang.
    { have H := (measurable_fun_prod'
                (ssrfun.comp fst fst)
                (ssrfun.comp (ssrfun.comp 𝜋_Val_v snd) fst)
                (setT `*` ecov_val `*` ecov_val)).
      apply H; clear H. (* Script hangs when I apply this directly *)
      { by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang). }
      { eapply @mathcomp_measurable_fun_restiction_setT.
        { by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang). }
        apply @measurable_compT.
        { by apply @measurableT.}
        { by apply measurable_fst. }
        by apply @measurable_fst.
      }
      eapply (@measurable_comp _ _ _ _ _ _ (setX setT ecov_val)).
      {  apply measurableX; by eauto with measlang. }
      { rewrite /subset//=.
        move=> [??[++]]//=.
        move=> [[??]?]//=.
        move=> [[??]?].
        move=> [+].
        by move=> ?<-//=. }
      { eapply @measurable_comp.
        3: { by apply 𝜋_Val_v_meas. }
        { by eauto with measlang. }
        { rewrite /subset//=.
          move=>?[[??]]//=.
          by move=>[??]<-//.
        }
        eapply @mathcomp_measurable_fun_restiction_setT.
        { apply measurableX; by eauto with measlang. }
        by apply @measurable_snd. }
      { eapply @mathcomp_measurable_fun_restiction_setT.
        { by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang). }
        by apply @measurable_fst. }
    }
    { eapply measurable_comp.
      3: { by apply 𝜋_Val_v_meas. }
      1: by eauto with measlang.
      1: {
        rewrite /subset//=.
        move=>?[+[++]].
        move=>[[??]?].
        move=>[?[+]]//=.
        move=>??.
        by move=>?<-//.
      }
      { eapply @mathcomp_measurable_fun_restiction_setT.
        { by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang). }
        { by apply @measurable_snd. }
      }
    }
  Qed.
  Hint Resolve cover_binop_ok'_meas : measlang.

  Lemma cover_binop_ok_meas : measurable cover_binop_ok.
  Proof. apply @measurable_fst; by eauto with measlang. Qed.
  Hint Resolve cover_binop_ok_meas : measlang.

  Lemma cover_binop_stuck_meas : measurable cover_binop_stuck.
  Proof.
    apply @measurable_fst; first by eauto with measlang.
    apply 𝜋_BinOpU_meas; eauto with measlang.
    eapply (measurable_fun_prod'
              (mProd (ssrfun.comp fst fst) (ssrfun.comp (ssrfun.comp 𝜋_Val_v snd) fst))
              (ssrfun.comp 𝜋_Val_v snd)
              (setX (setX setT ecov_val) ecov_val)).
    1,4: try by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang).
    3: by eauto with measlang.
    { have H := (measurable_fun_prod'
                (ssrfun.comp fst fst)
                (ssrfun.comp (ssrfun.comp 𝜋_Val_v snd) fst)
                (setT `*` ecov_val `*` ecov_val)).
      apply H; clear H. (* Script hangs when I apply this directly *)
      { by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang). }
      { eapply @mathcomp_measurable_fun_restiction_setT.
        { by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang). }
        apply @measurable_compT.
        { by apply @measurableT.}
        { by apply measurable_fst. }
        by apply @measurable_fst.
      }
      eapply (@measurable_comp _ _ _ _ _ _ (setX setT ecov_val)).
      {  apply measurableX; by eauto with measlang. }
      { rewrite /subset//=.
        move=> [??[++]]//=.
        move=> [[??]?]//=.
        move=> [[??]?].
        move=> [+].
        by move=> ?<-//=. }
      { eapply @measurable_comp.
        3: { by apply 𝜋_Val_v_meas. }
        { by eauto with measlang. }
        { rewrite /subset//=.
          move=>?[[??]]//=.
          by move=>[??]<-//.
        }
        eapply @mathcomp_measurable_fun_restiction_setT.
        { apply measurableX; by eauto with measlang. }
        by apply @measurable_snd. }
      { eapply @mathcomp_measurable_fun_restiction_setT.
        { by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang). }
        by apply @measurable_fst. }
    }
    { eapply measurable_comp.
      3: { by apply 𝜋_Val_v_meas. }
      1: by eauto with measlang.
      1: {
        rewrite /subset//=.
        move=>?[+[++]].
        move=>[[??]?].
        move=>[?[+]]//=.
        move=>??.
        by move=>?<-//.
      }
      { eapply @mathcomp_measurable_fun_restiction_setT.
        { by (apply measurableX; try by eauto with measlang; apply measurableX; by eauto with measlang). }
        { by apply @measurable_snd. }
      }
    }
  Qed.
  Hint Resolve cover_binop_stuck_meas : measlang.

  Lemma cover_ifT_meas : measurable cover_ifT.
  Proof.
    apply NonStatefulS_measurable.
    apply 𝜋_If_c_meas; first by eauto with measlang.
    apply 𝜋_Val_v_meas; first by eauto with measlang.
    apply 𝜋_LitV_v_meas; first by eauto with measlang.
    apply 𝜋_LitBool_b_meas; first by eauto with measlang.
    by rewrite /measurable/discr_meas//=.
  Qed.
  Hint Resolve cover_ifT_meas : measlang.

  Lemma cover_ifF_meas : measurable cover_ifF.
  Proof.
    apply NonStatefulS_measurable.
    apply 𝜋_If_c_meas; first by eauto with measlang.
    apply 𝜋_Val_v_meas; first by eauto with measlang.
    apply 𝜋_LitV_v_meas; first by eauto with measlang.
    apply 𝜋_LitBool_b_meas; first by eauto with measlang.
    by rewrite /measurable/discr_meas//=.
  Qed.
  Hint Resolve cover_ifF_meas : measlang.

  Lemma cover_fst_meas : measurable cover_fst.
  Proof.
    apply NonStatefulS_measurable.
    apply 𝜋_Fst_e_meas; first by eauto with measlang.
    apply 𝜋_Val_v_meas; first by eauto with measlang.
    eauto with measlang.
  Qed.
  Hint Resolve cover_fst_meas : measlang.

  Lemma cover_snd_meas : measurable cover_snd.
  Proof.
    apply NonStatefulS_measurable.
    apply 𝜋_Snd_e_meas; first by eauto with measlang.
    apply 𝜋_Val_v_meas; first by eauto with measlang.
    eauto with measlang.
  Qed.
  Hint Resolve cover_snd_meas : measlang.

  Lemma cover_caseL_meas : measurable cover_caseL.
  Proof.
    apply NonStatefulS_measurable.
    apply 𝜋_Case_c_meas; first by eauto with measlang.
    apply 𝜋_Val_v_meas; first by eauto with measlang.
    eauto with measlang.
  Qed.
  Hint Resolve cover_caseL_meas : measlang.

  Lemma cover_caseR_meas : measurable cover_caseR.
  Proof.
    apply NonStatefulS_measurable.
    apply 𝜋_Case_c_meas; first by eauto with measlang.
    apply 𝜋_Val_v_meas; first by eauto with measlang.
    eauto with measlang.
  Qed.
  Hint Resolve cover_caseR_meas : measlang.

  Lemma cover_tick_meas : measurable cover_tick.
  Proof.
    apply NonStatefulS_measurable.
    apply 𝜋_Tick_e_meas; first by eauto with measlang.
    apply 𝜋_Val_v_meas; first by eauto with measlang.
    apply 𝜋_LitV_v_meas; first by eauto with measlang.
    eauto with measlang.
  Qed.
  Hint Resolve cover_tick_meas : measlang.

  Lemma cover_maybe_stuck_meas : measurable cover_maybe_stuck.
  Proof. Admitted.

  (**  Top-level functions *)

  (* Generic lifting of a curried constructor on expr to a curried constructor on states *)
  Definition NonStatefulU {A : Type} (C : A -> expr) : (A * state) -> cfg := fun x => (C x.1, x.2).

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

  (*
  Section MAddState.
    Definition mAddState_def (x : state) (e : expr) : cfg := (e, x).
    Lemma mAddState_def_measurable (x : state) : @measurable_fun _ _ expr cfg setT (mAddState_def x).
    Proof. apply measurable_fun_prod'_expr; done. Qed.
    HB.instance Definition _ (x : state) :=
      isMeasurableMap.Build _ _ expr cfg (mAddState_def x) (mAddState_def_measurable x).
  End MAddState.

  Definition mAddState (x : state) : measurable_map expr cfg := mAddState_def x.

  (* Lift a monadic calculation returning exprs to a monadic function which returns cfg, with the state unchanged. *)
  Definition PReaderMU {A : Type} (C : (A * state) -> giryM expr) (x : A * state) : giryM cfg
    := giryM_map (mAddState x.2) (C x).

  (* If C is a measurable monaic function on A*state, its reader lifting is also measurable. *)
  Lemma PReaderMU_meas {d} {A : measurableType d} (C : (A * state) -> giryM expr) (S : set (A * state))
      (HS : measurable S) (HC : measurable_fun S C) : measurable_fun S (PReaderMU C).
  Proof.
    (* This definitely needs to be provable. I'm just not sure if the setT requirement in map will be good enough. *)
    rewrite /PReaderMU.
    move=> _ Y HY.
    rewrite /preimage.
    have HT1 : giryM_display.-measurable [set: types.giryM expr] by eauto.
    have Measurable1 := @measurable_mapP _ _ _ _ (giryM_map (mAddState _)) (HT1 _) Y HY.
    clear HT1.
    have Measurable2 := HC HS.
    clear HY.
    (* Maybe some way to commute with map could do the reduction in this special case? *)
    rewrite /preimage/setI//= in Measurable1, Measurable2; rewrite /preimage/setI//=.

  Admitted.


(* Generic lifting of a curried monadic function on expr to a monadic function on states *)
Definition PNonStatefulMU {A : Type} (C : A -> giryM expr) : (A * state) -> giryM cfg
  := PReaderMU (ssrfun.comp C fst).

Lemma PNonStatefulMU_meas {d} {A : measurableType d} (C : A -> giryM expr) (S : set A)
    (HS : measurable S) (HC : measurable_fun S C) : measurable_fun (NonStatefulS S) (PNonStatefulMU C).
Proof.
  apply PReaderMU_meas.
  { by apply NonStatefulS_measurable. }
  eapply measurable_comp.
  3: { by apply HC. }
  * done.
  * rewrite /subset/NonStatefulS//=.
    by move=>?[+]; move=>[+]; move=>??//=?<-.
  eapply @mathcomp_measurable_fun_restiction_setT; try by eauto with measlang.
  by apply NonStatefulS_measurable.
Qed.
   *)

  (** Top-level functions *)
  (* | Rec f x e => giryM_ret R ((Val $ RecV f x e, σ1) : cfg)  *)
  Definition head_stepM_rec : cfg -> giryM cfg :=
    ssrfun.comp (giryM_ret R) $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp RecVU 𝜋_RecU.

  (* | Pair (Val v1) (Val v2) => giryM_ret R ((Val $ PairV v1 v2, σ1) : cfg)   *)
  Definition head_stepM_pair : cfg -> giryM cfg :=
    ssrfun.comp (giryM_ret R) $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp PairVU $
    mProd
      (ssrfun.comp 𝜋_Val_v 𝜋_Pair_l)
      (ssrfun.comp 𝜋_Val_v $ 𝜋_Pair_r).

  (* | InjL (Val v) => giryM_ret R ((Val $ InjLV v, σ1) : cfg) *)
  Definition head_stepM_injL : cfg -> giryM cfg :=
    ssrfun.comp (giryM_ret R) $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp InjLVU $
    ssrfun.comp 𝜋_ValU $
    𝜋_InjLU.

  (* | InjR (Val v) => giryM_ret R ((Val $ InjRV v, σ1) : cfg) *)
  Definition head_stepM_injR : cfg -> giryM cfg :=
    ssrfun.comp (giryM_ret R) $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp InjRVU $
    ssrfun.comp 𝜋_ValU $
    𝜋_InjRU.

  (* | App (Val (RecV f x e1)) (Val v2) => giryM_ret R ((subst' x v2 (subst' f (RecV f x e1) e1) , σ1) : cfg)  *)
  Definition head_stepM_app : cfg -> giryM cfg :=
    ssrfun.comp (giryM_ret R) $
    NonStatefulU $
    ssrfun.comp substU' $ (* subst' ...  *)
    mProd
      (ssrfun.comp 𝜋_RecV_x $ ssrfun.comp 𝜋_Val_v $ 𝜋_App_l) (* x *)
    (mProd
      (ssrfun.comp 𝜋_Val_v $ 𝜋_App_r) (* v2 *)
    (ssrfun.comp substU' $ (* subst' ...  *)
    mProd
      (ssrfun.comp 𝜋_RecV_f $ ssrfun.comp 𝜋_Val_v $ 𝜋_App_l) (* f *)
    (mProd
       (ssrfun.comp 𝜋_Val_v $ 𝜋_App_l) (* RecV f x e1 *)
       (ssrfun.comp 𝜋_RecV_e $ ssrfun.comp 𝜋_Val_v $ 𝜋_App_l)))) (* e1 *).

  (* | UnOp op (Val v) =>
        match un_op_eval op v with
          | Some w => giryM_ret R ((Val w, σ1) : cfg)
          | _ => giryM_zero
        end
   *)

  (* The function (on configurations) to do when the cfg is a UnOp that is valid *)
  Definition head_stepM_unop_ok : cfg -> giryM cfg :=
    ssrfun.comp (giryM_ret R) $
    mProd
      ( ssrfun.comp ValU $
        ssrfun.comp un_op_evalC $
        ssrfun.comp
          (mProd
            𝜋_UnOp_op
            (ssrfun.comp 𝜋_Val_v 𝜋_UnOp_e)) $
        fst )
      snd.

  (* TODO: Delete *)
  Definition head_stepM_unop_stuck : cfg -> giryM cfg :=
    cst giryM_zero.

  (* The function (on configurations) to do when the cfg is a BinOp that is valid *)
  Definition head_stepM_binop_ok : cfg -> giryM cfg :=
    ssrfun.comp (giryM_ret R) $
    mProd
      ( ssrfun.comp ValU $
        ssrfun.comp bin_op_evalC $
        ssrfun.comp
          (mProd
              (mProd
                 𝜋_BinOp_op
                 (ssrfun.comp 𝜋_Val_v 𝜋_BinOp_l))
              (ssrfun.comp 𝜋_Val_v 𝜋_BinOp_r)) $
        fst )
      snd.

  (* TODO: Delete *)
  Definition head_stepM_binop_stuck : cfg -> giryM cfg :=
    cst giryM_zero.


  (* | If (Val (LitV (LitBool true))) e1 e2  => giryM_ret R ((e1 , σ1) : cfg) *)
  Definition head_stepM_ifT : cfg -> giryM cfg :=
    ssrfun.comp (giryM_ret R) $
    NonStatefulU $
    𝜋_If_l.

  (* | If (Val (LitV (LitBool false))) e1 e2 => giryM_ret R ((e2 , σ1) : cfg) *)
  Definition head_stepM_ifF : cfg -> giryM cfg :=
    ssrfun.comp (giryM_ret R) $
    NonStatefulU $
    𝜋_If_r.

  (* | Fst (Val (PairV v1 v2)) => giryM_ret R ((Val v1, σ1) : cfg) *)
  Definition head_stepM_fst : cfg -> giryM cfg :=
    ssrfun.comp (giryM_ret R) $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp 𝜋_PairV_l $
    ssrfun.comp 𝜋_ValU $
    𝜋_Fst_e.

  (* | Snd (Val (PairV v1 v2)) => giryM_ret R ((Val v2, σ1) : cfg) *)
  Definition head_stepM_snd : cfg -> giryM cfg :=
    ssrfun.comp (giryM_ret R) $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp 𝜋_PairV_r $
    ssrfun.comp 𝜋_ValU $
    𝜋_Snd_e.

  (* | Case (Val (InjLV v)) e1 e2 => giryM_ret R ((App e1 (Val v), σ1) : cfg) *)
  Definition head_stepM_caseL : cfg -> giryM cfg :=
    ssrfun.comp (giryM_ret R) $
    NonStatefulU $
    ssrfun.comp AppU $
    mProd
      𝜋_Case_l
      ( ssrfun.comp ValU $
        ssrfun.comp 𝜋_InjLV_v $
        ssrfun.comp 𝜋_Val_v $
        𝜋_Case_c ).

  (* | Case (Val (InjRV v)) e1 e2 => giryM_ret R ((App e2 (Val v), σ1) : cfg) *)
  Definition head_stepM_caseR : cfg -> giryM cfg :=
    ssrfun.comp (giryM_ret R) $
    NonStatefulU $
    ssrfun.comp AppU $
    mProd
      𝜋_Case_r
      ( ssrfun.comp ValU $
        ssrfun.comp 𝜋_InjRV_v $
        ssrfun.comp 𝜋_Val_v $
        𝜋_Case_c ).


  (* | Tick (Val (LitV (LitInt n))) => giryM_ret R ((Val $ LitV $ LitUnit, σ1) : cfg) *)
  Definition head_stepM_tick : cfg -> giryM cfg :=
    ssrfun.comp (giryM_ret R) $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp LitVU $
    cst LitUnit.

  Definition head_stepM_stuck : cfg -> giryM cfg :=
    cst giryM_zero.

  (* TODO: Eventually we could make this definition look less goofy?
     The functions don't _need_ each case to be defeq to a measurable function,
     since we're proving the restriction of head_stepM_def to every set in the cover
     is propeq to measurable function instead (see: head_stepM_rec_meas).
   *)
  Definition head_stepM_def (c : cfg) : giryM cfg :=
    let (e1, σ1) := c in
    match e1 with
    | Rec _ _ _                           => head_stepM_rec c
    | Pair (Val _) (Val _)                => head_stepM_pair c
    | InjL (Val _)                        => head_stepM_injL c
    | InjR (Val _)                        => head_stepM_injR c
    | App (Val (RecV _ _ _)) (Val _)      => head_stepM_app c
    | UnOp op (Val v)                     => match un_op_eval op v with
                                               | Some _ => head_stepM_unop_ok c
                                               | _ => head_stepM_unop_stuck c
                                             end
    | BinOp op (Val v1) (Val v2)          => match bin_op_eval op v1 v2 with
                                              | Some _ => head_stepM_binop_ok c
                                              | None => head_stepM_binop_stuck c
                                             end
    | If (Val (LitV (LitBool true))) _ _  => head_stepM_ifT c
    | If (Val (LitV (LitBool false))) _ _ => head_stepM_ifT c
    | Fst (Val (PairV _ _))               => head_stepM_fst c
    | Snd (Val (PairV _ _))               => head_stepM_snd c
    | Case (Val (InjLV _)) _ _            => head_stepM_caseL c
    | Case (Val (InjRV _)) _ _            => head_stepM_caseR c
    | Tick (Val (LitV (LitInt _)))        => head_stepM_tick c
    | _                                   => head_stepM_stuck c
    end.

  Hint Resolve measurable_compT : measlang.
  Hint Resolve measurable_mapP : measlang.

  (* Combining solve_packaged_meas and solve_toplevel_meas is too slow! *)
  Ltac solve_toplevel_meas :=
    repeat (
      try (apply measurable_compT);
      try (by eauto with measlang)
    ).

  (** Measurability of head_step restricted to the different sets in the cover *)
  Lemma head_stepM_rec_meas : measurable_fun cover_rec head_stepM_def.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_rec head_stepM_def).
    - solve_toplevel_meas.
      apply @NonStatefulU_meas; solve_toplevel_meas. (* How to integrate this into the tactic w/o stack overflow?*)
      (* Why do these not get applied form the hintdb? *)
      - by apply ValU_measurable.
      - by apply RecVU_measurable.
    - (* The trick: the two functions are equal on this set. *)
      move=>[??].
      do 3 (move=>[+]; move=>?).
      by move=>/=->/=.
    Unshelve. by eauto with measlang.
  Qed.
  Hint Resolve head_stepM_rec_meas : measlang.


  Lemma head_stepM_pair_meas : measurable_fun cover_pair head_stepM_def.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_pair head_stepM_def).
    - (* FIXME: Duplicate proof from above *)
      have S : expr_cyl.-sigma.-measurable (ecov_pair `&` 𝜋_PairU @^-1` (ecov_val `*` ecov_val)).
      { apply 𝜋_PairU_meas; last apply measurableX; by eauto with measlang.  }
      apply measurable_compT; try by eauto with measlang.
      apply @NonStatefulU_meas; try done.
      (*  solve_toplevel_meas. *)
      (* FIXME: Remove whatever hint is making this overapproximate the cover set
          I think it's measurable_compT, which we only want to use for certain compositions... *)
      apply measurable_compT; try by eauto with measlang.
      + by apply ValU_measurable.
      apply measurable_compT; try by eauto with measlang.
      + by apply PairVU_measurable.
      apply measurable_fun_prod'_expr; try by eauto with measlang.
      + eapply measurable_comp.
        3: by apply 𝜋_Val_v_meas.
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?[+[+[++]]].
          move=>????<-.
          by rewrite /ecov_val//=.
        * rewrite <-(setIid ecov_pair).
          rewrite <-setIA.
          by apply measurable_fun_setI1; try by eauto with measlang.
      + eapply measurable_comp.
        3: { by apply 𝜋_Val_v_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?[+[+[++]]].
          move=>????<-.
          by rewrite /ecov_val//=.
        * rewrite <-(setIid ecov_pair).
          rewrite <-setIA.
          by apply measurable_fun_setI1; try by eauto with measlang.
        all: try (by eauto with measlang).
    - move=>[e?].
      move=>/=[+].
      move=>[?[?+]].
      move=>//=->//=.
      move=>[++].
      rewrite /ecov_val//=.
      do 2 move=>[?->].
      by rewrite //=.
    Unshelve. by eauto with measlang.
  Qed.
  Hint Resolve head_stepM_pair_meas : measlang.

  Lemma head_stepM_injL_meas : measurable_fun cover_injL head_stepM_def.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_injL head_stepM_def).
    - apply measurable_compT; try by eauto with measlang.
      have S : (expr_cyl.-sigma.-measurable (ecov_injl `&` 𝜋_InjLU @^-1` ecov_val)).
      { apply 𝜋_InjLU_meas; by eauto with measlang. }
      apply @NonStatefulU_meas; first done.
      apply measurable_compT; try by eauto with measlang.
      + by apply ValU_measurable.
      apply measurable_compT; try by eauto with measlang.
      + by apply InjLVU_measurable.
      eapply measurable_comp.
      3: { by apply 𝜋_Val_v_meas. }
      * by eauto with measlang.
      * rewrite /subset//=.
        move=>?[+[+[++]]].
        move=>???-><-.
        by eexists _; eauto.
      * rewrite <-(setIid ecov_injl).
        rewrite <-setIA.
        apply measurable_fun_setI1; try by eauto with measlang.
    - move=>[e?].
      move=>/=[+].
      move=>[?+].
      move=>//=->//=.
      move=>[?->].
      rewrite /ecov_val//=.
    Unshelve. by eauto with measlang.
  Qed.
  Hint Resolve head_stepM_injL_meas : measlang.

  Lemma head_stepM_injR_meas : measurable_fun cover_injR head_stepM_def.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_injR head_stepM_def).
    - apply measurable_compT; try by eauto with measlang.
      have S : (expr_cyl.-sigma.-measurable (ecov_injr `&` 𝜋_InjRU @^-1` ecov_val)).
      { apply 𝜋_InjRU_meas; by eauto with measlang. }
      apply @NonStatefulU_meas; first done.
      apply measurable_compT; try by eauto with measlang.
      + by apply ValU_measurable.
      apply measurable_compT; try by eauto with measlang.
      + by apply InjRVU_measurable.
      eapply measurable_comp.
      3: { by apply 𝜋_Val_v_meas. }
      * by eauto with measlang.
      * rewrite /subset//=.
        move=>?[+[+[++]]].
        move=>???-><-.
        by eexists _; eauto.
      * rewrite <-(setIid ecov_injr).
        rewrite <-setIA.
        apply measurable_fun_setI1; try by eauto with measlang.
    - move=>[e?].
      move=>/=[+].
      move=>[?+].
      move=>//=->//=.
      move=>[?->].
      rewrite /ecov_val//=.
    Unshelve. by eauto with measlang.
  Qed.
  Hint Resolve head_stepM_injR_meas : measlang.

  (* FIXME: Many of the subproofs here are repetitive *)
  Lemma head_stepM_app_meas : measurable_fun cover_app head_stepM_def.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_app head_stepM_def).
    - apply measurable_compT; try by eauto with measlang.
      have S : expr_cyl.-sigma.-measurable (ecov_app `&` 𝜋_AppU @^-1` ((ecov_val `&` 𝜋_Val_v @^-1` vcov_rec) `*` ecov_val)).
      { apply 𝜋_AppU_meas; try by eauto with measlang.
        apply measurableX; by eauto with measlang. }
      apply @NonStatefulU_meas; first done.
      apply measurable_compT; try by eauto with measlang.
      { by apply substU'_measurable. }
      apply measurable_fun_prod'_expr; try by eauto with measlang.
      { eapply measurable_comp.
        3: { by eapply 𝜋_RecV_x_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?[+[+[++]]].
          move=>?[+].
          move=>?[+]; move=>?->//=.
          move=>[[++]+]; move=>?->//=.
          move=>[+[+[++]]]; move=>???->.
          move=>[++]; move=>??.
          move=><-//=.
          rewrite/vcov_rec/RecVC//=.
          by do 3 eexists.
        rewrite <-(setIid ecov_app).
        rewrite <-setIA.
        apply measurable_fun_setI2; try by eauto with measlang.
        eapply measurable_comp.
        3: { by eapply 𝜋_Val_v_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?.
          move=>[+[+[++]]].
          move=>?.
          move=> [+[++[++]]].
          move=>??->//=.
          move=>[++]; move=>?->//=.
          move=>[+[+[++]]]; move=>???->.
          move=>[++]; move=>??<-.
          rewrite /ecov_val/ValC//=.
          by eexists.
        rewrite <-(setIid ecov_app).
        rewrite <-setIA.
        apply measurable_fun_setI1; try by eauto with measlang.
      }
      apply measurable_fun_prod'_expr; try by eauto with measlang.
      { eapply measurable_comp.
        3: { by eapply 𝜋_Val_v_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?.
          move=>[+[+[++]]].
          move=>?.
          move=> [+[++[++]]].
          move=>??->//=.
          move=>[++]; move=>?->//=.
          move=>[+[+[++]]]; move=>????.
          by move=>?<-.
        rewrite <-(setIid ecov_app).
        rewrite <-setIA.
        by apply measurable_fun_setI1; try by eauto with measlang.
      }
      apply measurable_compT; try by eauto with measlang.
      { by apply substU'_measurable. }
      apply measurable_fun_prod'_expr; try by eauto with measlang.
      { eapply measurable_comp.
        3: { by eapply 𝜋_RecV_f_meas. } (* FIXME: Literally one charachter changed between this an a prior case lol *)
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?[+[+[++]]].
          move=>?[+].
          move=>?[+]; move=>?->//=.
          move=>[[++]+]; move=>?->//=.
          move=>[+[+[++]]]; move=>???->.
          move=>[++]; move=>??.
          move=><-//=.
          rewrite/vcov_rec/RecVC//=.
          by do 3 eexists.
        rewrite <-(setIid ecov_app).
        rewrite <-setIA.
        apply measurable_fun_setI2; try by eauto with measlang.
        eapply measurable_comp.
        3: { by eapply 𝜋_Val_v_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?.
          move=>[+[+[++]]].
          move=>?.
          move=> [+[++[++]]].
          move=>??->//=.
          move=>[++]; move=>?->//=.
          move=>[+[+[++]]]; move=>???->.
          move=>[++]; move=>??<-.
          rewrite /ecov_val/ValC//=.
          by eexists.
        rewrite <-(setIid ecov_app).
        rewrite <-setIA.
        apply measurable_fun_setI1; try by eauto with measlang.
      }
      apply measurable_fun_prod'_expr; try by eauto with measlang.
      { eapply measurable_comp.
        3: { by eapply 𝜋_Val_v_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?.
          move=>[+[+[++]]].
          move=>?.
          move=> [+[++[++]]].
          move=>??->//=.
          move=>[++]; move=>?->//=.
          move=>[+[+[++]]]; move=>????.
          move=>?<-.
          rewrite /ecov_val/ValC//=.
          by eexists.
        rewrite <-(setIid ecov_app).
        rewrite <-setIA.
        by apply measurable_fun_setI1; try by eauto with measlang.
      }
      { eapply measurable_comp.
        3: { by eapply 𝜋_RecV_e_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?[+[+[++]]].
          move=>?[+].
          move=>?[+]; move=>?->//=.
          move=>[[++]+]; move=>?->//=.
          move=>[+[+[++]]]; move=>???->.
          move=>[++]; move=>??.
          move=><-//=.
          rewrite/vcov_rec/RecVC//=.
          by do 3 eexists.
       eapply measurable_comp.
       3: { by eapply 𝜋_Val_v_meas. }
       * by eauto with measlang.
       * rewrite /subset//=.
         move=>?.
         move=>[+[+[++]]].
         move=>?.
         move=> [+[++[++]]].
         move=>??->//=.
         move=>[++]; move=>?->//=.
         move=>[+[+[++]]]; move=>????.
         move=>?<-.
         rewrite /ecov_val/ValC//=.
         by eexists.
        rewrite <-(setIid ecov_app).
        rewrite <-setIA.
        by apply measurable_fun_setI1; try by eauto with measlang.
      }
    - move=>[e?].
      move=>[[++]+].
      move=>?[++]; move=>?//=->.
      move=>[+[++]]//=.
      move=>[++]//=; move=>[+].
      move=>?//=->.
      move=>[+[++]].
      move=>??//=[+].
      move=>?->//=.
      by move=>?->//=.
    Unshelve. by eauto with measlang.
  Qed.
  Hint Resolve head_stepM_app_meas : measlang.

  Lemma head_stepM_unop_ok_meas : measurable_fun cover_unop_ok head_stepM_def.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_unop_ok head_stepM_def).
    - apply measurable_compT; try by eauto with measlang.
      eapply @measurable_fun_prod'.
      { by eauto with measlang. }
      2: { eapply @mathcomp_measurable_fun_restiction_setT.
           - by eauto with measlang.
           - by apply measurable_snd.
      }
      apply measurable_compT; try by eauto with measlang.
      { by apply ValU_measurable. }
      eapply @measurable_comp.
      3: { by eapply un_op_evalC_meas. }
      + by eauto with measlang.
      + rewrite /subset//=.
        move=>[??][[??]+]//=.
        move=>[++]//=.
        move=>?[++]//=.
        move=>[?[+]]//=.
        move=>?->//=.
        move=>[[?+]+]//=.
        move=>[?->]//=.
        move=>[?+]//=.
        rewrite//=.
        move=>?<-.
        rewrite /auxcov_unop_ok//=.
        by eexists _.
      apply (@measurable_comp _ _ _ _ _ _ cover_unop_ok').
      { by eauto with measlang. }
      { rewrite /subset/cover_unop_ok//=.
        move=>?[++].
        move=>?[?+].
        by move=>?<-//.
      }
      2: { eapply @mathcomp_measurable_fun_restiction_setT.
           - by eauto with measlang.
           - by apply measurable_fst.
      }
      eapply @measurable_fun_prod'.
      { by eauto with measlang. }
      { unfold cover_unop_ok'.
        rewrite <-(setIid ecov_unop).
        rewrite <-setIA.
        by apply measurable_fun_setI1; try by eauto with measlang. }
      eapply @measurable_comp.
      3: { by apply 𝜋_Val_v_meas. }
      { by eauto with measlang. }
      { rewrite /subset//=.
        move=>?[++].
        move=>?[++].
        move=>[?[++]].
        move=>?->//=.
        move=>[[?+]+].
        move=>[?+].
        move=>->//=.
        move=>[?+]//=.
        simpl.
        move=> ? <- //=.
        rewrite /ecov_val//=.
        by eexists.
      }
      { unfold cover_unop_ok'.
        rewrite <-(setIid ecov_unop).
        rewrite <-setIA.
        by apply measurable_fun_setI1; try by eauto with measlang. }
    - move=> [e?].
      move=>[?[+]]//=.
      move=>[++]; move=>?//=.
      move=>[?->].
      move=>[[_[++]][++]]//=.
      move=>?//=->.
      move=>?//=.
      move=>->//=.
    Unshelve. by eauto with measlang.
  Qed.
  Hint Resolve head_stepM_unop_ok_meas : measlang.

  Lemma head_stepM_unop_stuck_meas : measurable_fun cover_unop_stuck head_stepM_def.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_unop_stuck head_stepM_def).
    - by apply measurable_cst.
    - move=>[e?].
      move=>[?[+]]//=.
      move=>[?[++]]//=.
      move=>?//=->.
      move=>[[++]+]//=.
      move=>?.
      move=>[+]; move=>?//=->//=.
      rewrite /auxcov_unop_stuck//=.
      by move=>->//=.
    Unshelve. by eauto with measlang.
  Qed.
  Hint Resolve head_stepM_unop_stuck_meas : measlang.

  Lemma head_stepM_binop_ok_meas : measurable_fun cover_binop_ok head_stepM_def.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_binop_ok head_stepM_def).
    - apply measurable_compT; try by eauto with measlang.
      eapply (@measurable_fun_prod' _ _ _ _ _ _
              (ssrfun.comp ValU (ssrfun.comp bin_op_evalC (ssrfun.comp (Package3 𝜋_BinOp_op (ssrfun.comp 𝜋_Val_v 𝜋_BinOp_l) (ssrfun.comp 𝜋_Val_v 𝜋_BinOp_r)) fst)))
              snd).
      { by eauto with measlang. }
      2: { eapply @mathcomp_measurable_fun_restiction_setT.
           - by eauto with measlang.
           - by apply measurable_snd.
      }
      apply measurable_compT; try by eauto with measlang.
      { by apply ValU_measurable. }
      eapply @measurable_comp.
      3: { by eapply bin_op_evalC_meas. }
      + by eauto with measlang.
      + rewrite /subset//=.
        move=> [[??]?][[??]+]//=.
        move=> [++]//=.
        move=> ?[++]//=.
        move=> [?[?[?+]]]//=.
        move=>//=->//=.
        move=> [[[?+]+]+]//=.
        move=> [?->]//=.
        move=> [?->]//=.
        by move=> +<-//=.
      eapply (@measurable_comp _ _ _ _ _ _ cover_binop_ok').
      4: { eapply @mathcomp_measurable_fun_restiction_setT.
           - by eauto with measlang.
           - by apply measurable_fst.
      }
      { by eauto with measlang. }
      { rewrite /subset//=.
        move=>?[[??]+]//=.
        move=>[++]//=.
        move=>?.
        by move=>+<-//=.
      }
      apply @measurable_fun_prod'.
      { by eauto with measlang. }
      { apply @measurable_fun_prod'.
        { by eauto with measlang. }
        { unfold cover_binop_ok'.
          rewrite <-(setIid ecov_binop).
          rewrite <-setIA.
          by apply measurable_fun_setI1; try by eauto with measlang. }
        { eapply @measurable_comp.
          3: { by apply 𝜋_Val_v_meas. }
          { by eauto with measlang. }
          2: { rewrite /cover_binop_ok'.
               rewrite <-(setIid ecov_binop).
               rewrite <-setIA.
               by apply measurable_fun_setI1; try by eauto with measlang. }
          { rewrite /subset//=.
            move=>?[++].
            move=>?[++].
            move=>[?[?[?+]]]//=.
            move=>->//=.
            move=>[[[?+]+][++]]//=.
            move=>[?->]//=.
            move=>[?->]//=.
            move=>??<-//=.
            rewrite /ecov_val//=.
            by eexists _.
          }
        }
      }
      { eapply @measurable_comp.
        3: { by apply 𝜋_Val_v_meas. }
        { by eauto with measlang. }
        { rewrite /subset//=.
          move=>?[++].
          move=>?+<-//=.
          rewrite /ecov_val//=.
          move=>[++]//=.
          move=>[?[?[?+]]]//=.
          move=>->//=.
          by move=>[[[?+]+]+]//=.
        }
        rewrite /cover_binop_ok'.
        rewrite <-(setIid ecov_binop).
        rewrite <-setIA.
        by apply measurable_fun_setI1; try by eauto with measlang.
      }
    - move=>[e?].
      move=>[++].
      move=>?//=.
      move=>[++]//=.
      move=>[+[+[++]]].
      move=>???->//=.
      move=>[[[?+]+]+].
      move=>[?->]//=.
      move=>[?->]//=.
      by move=>[?->]//=.
    Unshelve. by eauto with measlang.
  Qed.
  Hint Resolve head_stepM_binop_ok_meas : measlang.

  Lemma head_stepM_binop_stuck_meas : measurable_fun cover_binop_stuck head_stepM_def.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_binop_stuck head_stepM_def).
    - by apply measurable_cst.
    - move=>[e?].
      move=>[?+]//=.
      move=>[++]//=.
      move=>[++]//=.
      move=>?[++]//=.
      move=>?[?+]//=.
      rewrite //=; move=>->//=.
      move=>[[[?+]+]+]//=.
      move=>[?+]//=; move=>->//=.
      move=>[?+]//=; move=>->//=.
      rewrite /auxcov_binop_stuck//=.
      by move=>->.
    Unshelve. by eauto with measlang.
  Qed.
  Hint Resolve head_stepM_binop_stuck_meas : measlang.

  Lemma head_stepM_ifT_meas : measurable_fun cover_ifT head_stepM_def.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_ifT head_stepM_def).
    - apply measurable_compT; try by eauto with measlang.
      have S : expr_cyl.-sigma.-measurable (ecov_if `&` 𝜋_If_c @^-1` (ecov_val `&` 𝜋_Val_v @^-1` (vcov_lit `&` 𝜋_LitV_v @^-1` (bcov_LitBool `&` 𝜋_LitBool_b @^-1` [set true])))).
     { apply 𝜋_If_c_meas; first by eauto with measlang.
       apply 𝜋_Val_v_meas; first by eauto with measlang.
       apply 𝜋_LitV_v_meas; first by eauto with measlang.
       apply 𝜋_LitBool_b_meas; first by eauto with measlang.
       by rewrite /measurable/discr_meas//=.
      }
      apply @NonStatefulU_meas; first done.
      rewrite <-(setIid ecov_if).
      rewrite <-setIA.
      by apply measurable_fun_setI1; eauto with measlang.
    - move=>[e?].
      move=>/=[+]; do 3 move=>[?+].
      move=>//=->.
      move=>[+[+[++]]]/=.
      move=>/=[+]; move=>?->.
      move=>/=[+]; move=>?->.
      move=>/=[+]; move=>?->.
      move=>/=->//=.
    Unshelve. by eauto with measlang.
  Qed.
  Hint Resolve head_stepM_ifT_meas : measlang.

  Lemma head_stepM_ifF_meas : measurable_fun cover_ifF head_stepM_def.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_ifT head_stepM_def).
    - apply measurable_compT; try by eauto with measlang.
      have S : expr_cyl.-sigma.-measurable (ecov_if `&` 𝜋_If_c @^-1` (ecov_val `&` 𝜋_Val_v @^-1` (vcov_lit `&` 𝜋_LitV_v @^-1` (bcov_LitBool `&` 𝜋_LitBool_b @^-1` [set false])))).
     { apply 𝜋_If_c_meas; first by eauto with measlang.
       apply 𝜋_Val_v_meas; first by eauto with measlang.
       apply 𝜋_LitV_v_meas; first by eauto with measlang.
       apply 𝜋_LitBool_b_meas; first by eauto with measlang.
       by rewrite /measurable/discr_meas//=.
      }
      apply @NonStatefulU_meas; first done.
      rewrite <-(setIid ecov_if).
      rewrite <-setIA.
      by apply measurable_fun_setI1; eauto with measlang.
    - move=>[e?].
      move=>/=[+]; do 3 move=>[?+].
      move=>//=->.
      move=>[+[+[++]]]/=.
      move=>/=[+]; move=>?->.
      move=>/=[+]; move=>?->.
      move=>/=[+]; move=>?->.
      move=>/=->//=.
    Unshelve. by eauto with measlang.
  Qed.
  Hint Resolve head_stepM_ifF_meas : measlang.

  Lemma head_stepM_fst_meas : measurable_fun cover_fst head_stepM_def.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_fst head_stepM_def).
    - apply measurable_compT; try by eauto with measlang.
      have S : expr_cyl.-sigma.-measurable (ecov_fst `&` 𝜋_Fst_e @^-1` (ecov_val `&` 𝜋_Val_v @^-1` vcov_pair)).
      { apply 𝜋_Fst_e_meas; first by eauto with measlang.
        apply 𝜋_Val_v_meas; first by eauto with measlang.
        by eauto with measlang. }
      apply @NonStatefulU_meas; first done.
      apply measurable_compT; try by eauto with measlang.
      + by apply ValU_measurable.
      eapply measurable_comp.
      3: { by apply 𝜋_PairV_l_meas. }
      * by eauto with measlang.
      * rewrite /subset//=.
        move=>?[+[+[++]]].
        by move=>????<-//=.
      eapply measurable_comp.
      3: { by apply 𝜋_ValU_meas. }
      * by eauto with measlang.
      * rewrite /subset//=.
        move=>?[+[+[++]]].
        by move=>????<-//=.
      * rewrite <-(setIid ecov_fst).
        rewrite <-setIA.
        apply measurable_fun_setI1; try by eauto with measlang.
    - move=>[e?].
      move=>/=[+]; move=>[?+].
      move=>//=->.
      move=>[++]/=.
      move=>/=[+]; move=>?->.
      move=>[+]/=; move=>?.
      move=>[+]/=; move=>?.
      by move=>->/=.
    Unshelve. by eauto with measlang.
  Qed.
  Hint Resolve head_stepM_fst_meas : measlang.

  Lemma head_stepM_snd_meas : measurable_fun cover_snd head_stepM_def.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_snd head_stepM_def).
    - apply measurable_compT; try by eauto with measlang.
      have S : expr_cyl.-sigma.-measurable (ecov_snd `&` 𝜋_Snd_e @^-1` (ecov_val `&` 𝜋_Val_v @^-1` vcov_pair)).
      { apply 𝜋_Snd_e_meas; first by eauto with measlang.
        apply 𝜋_Val_v_meas; first by eauto with measlang.
        by eauto with measlang. }
      apply @NonStatefulU_meas; first done.
      apply measurable_compT; try by eauto with measlang.
      + by apply ValU_measurable.
      eapply measurable_comp.
      3: { by apply 𝜋_PairV_r_meas. }
      * by eauto with measlang.
      * rewrite /subset//=.
        move=>?[+[+[++]]].
        by move=>????<-//=.
      eapply measurable_comp.
      3: { by apply 𝜋_ValU_meas. }
      * by eauto with measlang.
      * rewrite /subset//=.
        move=>?[+[+[++]]].
        by move=>????<-//=.
      * rewrite <-(setIid ecov_snd).
        rewrite <-setIA.
        apply measurable_fun_setI1; try by eauto with measlang.
    - move=>[e?].
      move=>/=[+]; move=>[?+].
      move=>//=->.
      move=>[++]/=.
      move=>/=[+]; move=>?->.
      move=>[+]/=; move=>?.
      move=>[+]/=; move=>?.
      by move=>->/=.
    Unshelve. by eauto with measlang.
  Qed.
  Hint Resolve head_stepM_snd_meas : measlang.

  Lemma head_stepM_caseL_meas : measurable_fun cover_caseL head_stepM_def.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_caseL head_stepM_def).
    - apply measurable_compT; try by eauto with measlang.
      have S : expr_cyl.-sigma.-measurable (ecov_case `&` 𝜋_Case_c @^-1` (ecov_val `&` 𝜋_Val_v @^-1` vcov_injlv)).
      { apply 𝜋_Case_c_meas; first by eauto with measlang.
        apply 𝜋_Val_v_meas; first by eauto with measlang.
        by eauto with measlang.
      }
      apply @NonStatefulU_meas; first done.
      apply measurable_compT; try by eauto with measlang.
      + by apply AppU_measurable.
      apply measurable_fun_prod'_expr; try by eauto with measlang.
      + rewrite <-(setIid ecov_case).
        rewrite <-setIA.
        apply measurable_fun_setI1; try by eauto with measlang.
        apply measurable_compT; try by eauto with measlang.
        + by apply ValU_measurable.
        eapply measurable_comp.
        3: { by apply 𝜋_InjLV_v_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?[+[+[++]]].
          by move=>????<-//=.
        eapply measurable_comp.
        3: { by apply 𝜋_Val_v_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?[+[+[++]]].
          by move=>????<-//=.
        rewrite <-(setIid ecov_case).
        rewrite <-setIA.
        by apply measurable_fun_setI1; try by eauto with measlang.
    - move=>[e?].
      move=>/=[+]; move=>[?+].
      move=>/=[?[?->]]/=.
      move=>[[++][++]]//=.
      do 2 move=>?//=->.
      by move=>//=.
    Unshelve. by eauto with measlang.
  Qed.
  Hint Resolve head_stepM_caseL_meas : measlang.

  Lemma head_stepM_caseR_meas : measurable_fun cover_caseR head_stepM_def.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_caseR head_stepM_def).
    - apply measurable_compT; try by eauto with measlang.
      have S : expr_cyl.-sigma.-measurable (ecov_case `&` 𝜋_Case_c @^-1` (ecov_val `&` 𝜋_Val_v @^-1` vcov_injrv)).
      { apply 𝜋_Case_c_meas; first by eauto with measlang.
        apply 𝜋_Val_v_meas; first by eauto with measlang.
        by eauto with measlang.
      }
      apply @NonStatefulU_meas; first done.
      apply measurable_compT; try by eauto with measlang.
      + by apply AppU_measurable.
      apply measurable_fun_prod'_expr; try by eauto with measlang.
      + rewrite <-(setIid ecov_case).
        rewrite <-setIA.
        apply measurable_fun_setI1; try by eauto with measlang.
        apply measurable_compT; try by eauto with measlang.
        + by apply ValU_measurable.
        eapply measurable_comp.
        3: { by apply 𝜋_InjRV_v_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?[+[+[++]]].
          by move=>????<-//=.
        eapply measurable_comp.
        3: { by apply 𝜋_Val_v_meas. }
        * by eauto with measlang.
        * rewrite /subset//=.
          move=>?[+[+[++]]].
          by move=>????<-//=.
        rewrite <-(setIid ecov_case).
        rewrite <-setIA.
        by apply measurable_fun_setI1; try by eauto with measlang.
    - move=>[e?].
      move=>/=[+]; move=>[?+].
      move=>/=[?[?->]]/=.
      move=>[[++][++]]//=.
      do 2 move=>?//=->.
      by move=>//=.
    Unshelve. by eauto with measlang.
  Qed.
  Hint Resolve head_stepM_caseR_meas : measlang.

  Lemma head_stepM_tick_meas : measurable_fun cover_tick head_stepM_def.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_tick head_stepM_def).
    - apply measurable_compT; try by eauto with measlang.
      have S : expr_cyl.-sigma.-measurable (ecov_tick `&` 𝜋_Tick_e @^-1` (ecov_val `&` 𝜋_Val_v @^-1` (vcov_lit `&` 𝜋_LitV_v @^-1` bcov_LitInt))).
      { apply 𝜋_Tick_e_meas; first by eauto with measlang.
        apply 𝜋_Val_v_meas; first by eauto with measlang.
        apply 𝜋_LitV_v_meas; first by eauto with measlang.
        by eauto with measlang. }
      apply @NonStatefulU_meas; first done.
      apply measurable_compT; try by eauto with measlang.
      + by apply ValU_measurable.
      apply measurable_compT; try by eauto with measlang.
      + by apply LitVU_measurable.
    - move=>[e?].
      move=>/=[+]; move=>[?+].
      move=>//=->.
      move=>[+[++]]/=.
      move=>/=[+]; move=>?->.
      move=>[+]/=; move=>?->.
      move=>[+]/=; move=>?->.
      by move=>//=.
    Unshelve. by eauto with measlang.
  Qed.
  Hint Resolve head_stepM_tick_meas : measlang.

  Lemma head_stepM_stuck_meas : measurable_fun cover_maybe_stuck head_stepM_def.
  Proof.
    (* TODO/FIXME: This is circular. To fix this, the maybe stuck case
       will need to be the difference from all the other cases, and then we can
       show that we land in the last case.

       This will also change the is_cover proof (to be something like (U F) U (X - U F) = X) *)
  Admitted.
  Hint Resolve head_stepM_stuck_meas : measlang.


  (**  Head step measurability *)
  Lemma cfg_cover_measurable :
      Forall (fun S => measurable S) cfg_cover.
  Proof.
    repeat (try apply Forall_cons; split); last by apply List.Forall_nil.
    - by apply cover_rec_meas.
    - by apply cover_pair_meas.
    - by apply cover_injL_meas.
    - by apply cover_injR_meas.
    - by apply cover_app_meas.
    - by apply cover_unop_ok_meas.
    - by apply cover_unop_stuck_meas.
    - by apply cover_binop_ok_meas.
    - by apply cover_binop_stuck_meas.
    - by apply cover_ifT_meas.
    - by apply cover_ifF_meas.
    - by apply cover_fst_meas.
    - by apply cover_snd_meas.
    - by apply cover_caseL_meas.
    - by apply cover_caseR_meas.
    - by apply cover_tick_meas.
    - by apply cover_maybe_stuck_meas.
  Qed.

  Lemma head_stepM_def_restricted_measurable :
      Forall (fun S => measurable_fun S head_stepM_def) cfg_cover.
  Proof.
    repeat (try apply Forall_cons; split); last by apply List.Forall_nil.
    - by apply head_stepM_rec_meas.
    - by apply head_stepM_pair_meas.
    - by apply head_stepM_injL_meas.
    - by apply head_stepM_injR_meas.
    - by apply head_stepM_app_meas.
    - by apply head_stepM_unop_ok_meas.
    - by apply head_stepM_unop_stuck_meas.
    - by apply head_stepM_binop_ok_meas.
    - by apply head_stepM_binop_stuck_meas.
    - by apply head_stepM_ifT_meas.
    - by apply head_stepM_ifF_meas.
    - by apply head_stepM_fst_meas.
    - by apply head_stepM_snd_meas.
    - by apply head_stepM_caseL_meas.
    - by apply head_stepM_caseR_meas.
    - by apply head_stepM_tick_meas.
    - by apply head_stepM_stuck_meas.
  Qed.

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
    | ...
    | BinOp op (Val v1) (Val v2) =>
        match bin_op_eval op v1 v2 with
          | Some w => giryM_ret R ((Val w, σ1) : cfg)
          | _ => giryM_zero
        end
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
