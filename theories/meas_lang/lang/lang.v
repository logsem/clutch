(* TODO cleanup imports *) Set Warnings "-hiding-delimiting-key".
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
From clutch.prob.monad Require Export giry.
From mathcomp.analysis Require Export Rstruct.
From mathcomp Require Import classical_sets.
Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude types constructors shapes cover projections tapes state subst pureops heapops randops cfg fill.
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
Set Warnings "hiding-delimiting-key".
Set Warnings "+spurious-ssr-injection".

Module meas_lang.

Canonical Structure stateO := leibnizO state.
Canonical Structure locO := leibnizO loc.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.

Section meas_semantics.
  Local Open Scope ereal_scope.
  Local Open Scope classical_set_scope.

  (**  The top-level cover for head_step *)

  (* Lift a set S to [ (s, σ) | s ∈ S, σ ∈ State ] *)
  Definition NonStatefulS {A : Type} (S : set A) : set (A * state) := preimage fst S.

  Lemma NonStatefulS_measurable {d} {T : measurableType d} (S : set T) (HS : measurable S) :
      measurable (NonStatefulS S).
  Proof.
    rewrite <- (setTI (NonStatefulS S)); rewrite /NonStatefulS.
    apply @measurable_fst; last done.
    by eapply @measurableT.
  Qed.
  Hint Resolve NonStatefulS_measurable : measlang.

  (* [set c | ∃ f x e σ, c = (Rec f x e, σ) ]. *)
  Definition cover_rec : set cfg :=
    NonStatefulS ecov_rec.

  (*[set c | ∃ v1 v2 σ, c = (Pair (Val v1) (Val v2), σ) ].*)
  Definition cover_pair : set cfg :=
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

  (* [set e | ∃ N v, e = AllocN (Val (LitV (LitInt N))) (val v)] *)
  Definition auxcov_allocN : set cfg  :=
    setI setT $
    preimage fst $
    setI ecov_alloc $
    preimage 𝜋_AllocNU $
    setX
      ( setI ecov_val $
        preimage 𝜋_ValU $
        setI vcov_lit $
        preimage 𝜋_LitVU $
        bcov_LitInt )
      ecov_val.

  Definition aux_allocN_Z : cfg -> <<discr Z>> :=
    ssrfun.comp 𝜋_LitIntU $
    ssrfun.comp 𝜋_LitVU $
    ssrfun.comp 𝜋_ValU $
    ssrfun.comp fst $
    ssrfun.comp 𝜋_AllocNU $
    fst.

  Definition aux_allocN_v : cfg -> val :=
    ssrfun.comp 𝜋_ValU $
    ssrfun.comp snd $
    ssrfun.comp 𝜋_AllocNU $
    fst.

  Definition aux_allocN_σ : cfg -> state :=
    snd.

  Definition aux_allocN : cfg -> (val * state) :=
    mProd aux_allocN_v aux_allocN_σ.

  (*  [set c | ∃ N v σ, c = (AllocN (Val (LitV (LitInt N))) (Val v), σ) /\ bool_decide (0 < Z.to_nat N)%nat = true]. *)
  Definition cover_allocN_ok : set cfg :=
    setI auxcov_allocN $ preimage aux_allocN auxcov_allocN_ok.

  (* [set c | ∃ N v σ, c = (AllocN (Val (LitV (LitInt N))) (Val v), σ) /\ bool_decide (0 < Z.to_nat N)%nat = false].*)
  Definition cover_allocN_stuck : set cfg :=
    setI auxcov_allocN $ preimage aux_allocN auxcov_allocN_stuck.


  (* [set e | ∃ l e = (Load (Val (LitV (LitLoc l))))] *)
  Definition auxcov_load : set expr :=
    setI ecov_load $
    preimage 𝜋_LoadU $
    setI ecov_val $
    preimage 𝜋_ValU $
    setI vcov_lit $
    preimage 𝜋_LitVU $
    bcov_LitLoc.

  (* Project down to the loc of a load expression *)
  Definition aux_load_loc : expr -> <<discr loc>> :=
    ssrfun.comp 𝜋_LitLocU $
    ssrfun.comp 𝜋_LitV_v $
    ssrfun.comp 𝜋_Val_v $
    𝜋_LoadU.

(*
    | Store (Val (LitV (LitLoc l))) (Val w) =>
        match σ1.(heap) !! l with
          | Some v => gRet ((Val $ LitV LitUnit, state_upd_heap <[l:=w]> σ1) : cfg)
          | None => gZero
        end
*)


  (* [set e | ∃ N v, e = Store (Val (LitV (LitLoc L))) (val v)] *)
  Definition auxcov_store : set cfg  :=
    setI setT $
    preimage fst $
    setI ecov_store $
    preimage 𝜋_StoreU $
    setX
      ( setI ecov_val $
        preimage 𝜋_ValU $
        setI vcov_lit $
        preimage 𝜋_LitVU $
        bcov_LitLoc )
      ecov_val.


  Definition aux_store_loc : cfg -> <<discr loc>> :=
    ssrfun.comp 𝜋_LitLocU $
    ssrfun.comp 𝜋_LitVU $
    ssrfun.comp 𝜋_ValU $
    ssrfun.comp fst $
    ssrfun.comp 𝜋_StoreU $
    fst.

  Definition aux_store_v : cfg -> val :=
    ssrfun.comp 𝜋_ValU $
    ssrfun.comp snd $
    ssrfun.comp 𝜋_StoreU $
    fst.

  Definition aux_store_σ : cfg -> state :=
    snd.

  Definition aux_store : cfg -> (<<discr loc>> * val * state) :=
    mProd (mProd aux_store_loc aux_store_v ) aux_store_σ.

  Definition cover_store_ok : set cfg :=
    setI auxcov_store $ preimage aux_store auxcov_store_ok.

  Definition cover_store_stuck : set cfg :=
    setI auxcov_store $ preimage aux_store auxcov_store_stuck.

  (* [set c | ∃ l w σ, c = (Load (Val (LitV (LitLoc l))), σ) /\ σ.(heap) !! l = Some w]. *)
  Definition cover_load_ok : set cfg :=
    setI (setX auxcov_load setT) $
    preimage
      (mProd (ssrfun.comp aux_load_loc fst) snd)
      auxcov_load_ok.

  (* [set c | ∃ l σ, c = (Load (Val (LitV (LitLoc l))), σ) /\ σ.(heap) !! l = None]. *)
  Definition cover_load_stuck : set cfg :=
    setI (setX auxcov_load setT) $
    preimage
      (mProd (ssrfun.comp aux_load_loc fst) snd)
      auxcov_load_stuck.

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


  (*  [set c | ∃ z σ,          c = (AllocTape (Val (LitV (LitInt z))), σ) ]. *)
  Definition cover_allocTape : set cfg :=
    NonStatefulS $
    setI ecov_alloctape $
    preimage 𝜋_AllocTapeU $
    setI ecov_val $
    preimage 𝜋_ValU $
    setI vcov_lit $
    preimage 𝜋_LitV_v $
    bcov_LitInt.

  (* [set c | ∃ σ,            c = (AllocUTape, σ) ] *)
  Definition cover_allocUTape : set cfg :=
    NonStatefulS $ ecov_allocutape.

  (* Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)) *)
  Definition cover_rand : set cfg :=
    NonStatefulS $
    setI ecov_rand $
    preimage 𝜋_RandU $
    setX
      ( setI ecov_val $
         preimage 𝜋_ValU $
         setI vcov_lit $
         preimage 𝜋_LitV_v $
         bcov_LitInt )
      ( setI ecov_val $
         preimage 𝜋_ValU $
         setI vcov_lit $
         preimage 𝜋_LitV_v $
         bcov_LitUnit ).

  (*  (URand (Val (LitV LitUnit)), σ) *)
  Definition cover_urand : set cfg :=
    NonStatefulS $
    setI ecov_urand $
    preimage 𝜋_URandU $
    setI ecov_val $
    preimage 𝜋_ValU $
    setI vcov_lit $
    preimage 𝜋_LitV_v $
    bcov_LitUnit.

  Definition cover_randT : set cfg :=
    NonStatefulS $
    setI ecov_rand $
    preimage 𝜋_RandU $
    setX
      ( setI ecov_val $
         preimage 𝜋_ValU $
         setI vcov_lit $
         preimage 𝜋_LitV_v $
         bcov_LitInt )
      ( setI ecov_val $
         preimage 𝜋_ValU $
         setI vcov_lit $
         preimage 𝜋_LitV_v $
         bcov_LitLbl ).

  Definition cover_urandT : set cfg :=
    NonStatefulS $
    setI ecov_urand $
    preimage 𝜋_URandU $
    setI ecov_val $
    preimage 𝜋_ValU $
    setI vcov_lit $
    preimage 𝜋_LitV_v $
    bcov_LitLbl.

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
    cover_allocN_ok;
    cover_allocN_stuck;
    cover_load_ok;
    cover_load_stuck;
    cover_store_ok;
    cover_store_stuck;
    cover_allocTape;
    cover_allocUTape;
    cover_rand;
    cover_urand;
    cover_randT;
    cover_urandT;
    cover_tick
  ].

  Program Definition cover_maybe_stuck : set cfg :=
    setC $ List.fold_right setU set0 cfg_cover_pre.

  Definition cfg_cover : list (set cfg) := cover_maybe_stuck :: cfg_cover_pre.


  (**The top-level cover is a cover *)

  Lemma cfg_cover_is_cover : List.fold_right setU set0 cfg_cover = setT.
  Proof. by rewrite foldr_cons setvU. Qed.

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
        { by apply @measurableT. }
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
        { by apply @measurableT. }
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


  Lemma auxcov_allocN_meas : measurable auxcov_allocN.
  Proof.
    apply @measurable_fst.
    { by eauto with measlang. }
    apply 𝜋_AllocNU_meas.
    { by eauto with measlang. }
    apply measurableX.
    { by eauto with measlang. }
    { by eauto with measlang. }
  Qed.
  Hint Resolve auxcov_allocN_meas : measlang.

  (*
  Ltac subset_proof_simp_unfold :=
    match goal with
      | [ |- ∀ (a : expr_T) (b : (gmap loc val_T * gmap loc (nat * (nat * tapes.nf (option <<discr Z >>))) *
          gmap loc (nat * tapes.nf (option state.R)))), ?E ]        => move=>??//=
      | [ |- ∀ (x : expr_pre), ((?A = ?B) -> ?E) ]       => move=>?->//=
      | [ |- ∀ (x : val_pre), ((?A = ?B) -> ?E) ]        => move=>?->//=
      | [ |- ∀ (x : base_lit_pre), ((?A = ?B) -> ?E) ]   => move=>?->//=
      | [ |- ∀ x : @Measurable.sort default_measure_display TZ, ((?E = ?E1) → ?G)] => move=>?->//=
      | [ |- ∀ (x : expr_pre), ?E ]                      => move=>?//=
    end.

  Ltac subset_proof_simp_destruct := move=> [++].

  Ltac subset_proof_simp :=
    try rewrite/subset//=;
    move=>?;
    repeat (repeat subset_proof_simp_destruct; subset_proof_simp_unfold).
*)

  Lemma aux_allocN_Z_meas : measurable_fun auxcov_allocN aux_allocN_Z.
  Proof. Admitted.
  (*
    unfold aux_allocN_Z.
    unfold auxcov_allocN.
    eapply (@measurable_comp _ _ _ _ _ _ _ 𝜋_LitIntU).
    3: by eauto with measlang.
    1: by eauto with measlang.
    { subset_proof_simp.
      repeat move=>[++]; move=>??//=.
      rewrite /bcov_LitInt.
      move=><-//=.
      by eexists.
    }
    mcrunch_comp.
    { subset_proof_simp.
      repeat move=>[++]; move=>??//=.
      rewrite /vcov_lit.
      move=><-//=.
      by eexists.
    }
    mcrunch_comp.
    { subset_proof_simp.
      repeat move=>[++]; move=>??//=.
      rewrite /ecov_val.
      move=><-//=.
      by eexists.
    }
    mcrunch_comp.
    mcrunch_comp.
    {
      rewrite /subset//=.
      move=>?.
      repeat move=>[++]; subset_proof_simp_unfold.
      repeat move=>[++]; subset_proof_simp_unfold.
      repeat move=>[++]; subset_proof_simp_unfold.
      repeat move=>[++]; subset_proof_simp_unfold.
      repeat move=>[++]; subset_proof_simp_unfold.
      repeat move=>[++]; subset_proof_simp_unfold.
      repeat move=>[++]; subset_proof_simp_unfold.
      rewrite /ecov_alloc.
      move=><-//=.
      eexists _.
      eexists _.
      done.
    }
    mcrunch_fst.
  Qed.
*)
  Hint Resolve aux_allocN_Z_meas : measlang.

  Lemma aux_allocN_v_meas : measurable_fun auxcov_allocN aux_allocN_v.
  Proof.
    unfold aux_allocN_v.
    unfold auxcov_allocN.
    eapply (@measurable_comp _ _ _ _ _ _ _ 𝜋_ValU).
    3: by eauto with measlang.
    1: by eauto with measlang.
    { rewrite /subset//=.
      move=>?.
      repeat move=>[++]; move=>??//=.
      repeat move=>[++]; move=>?//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>??//=.
      by move=>?<-//=.
    }
    mcrunch_comp.
    mcrunch_comp.
    { rewrite /subset//=.
      move=>?.
      repeat move=>[++]; move=>??//=.
      repeat move=>[++]; move=>?//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      rewrite /ecov_alloc//=.
      move=><-//=.
      eexists.
      by eexists.
    }
    by eapply @measurable_fst_restriction; eauto with measlang.
  Qed.
  Hint Resolve aux_allocN_v_meas : measlang.

  Lemma aux_allocN_σ_meas : measurable_fun auxcov_allocN aux_allocN_σ.
  Proof.
    by eapply @measurable_snd_restriction; eauto with measlang.
  Qed.
  Hint Resolve aux_allocN_σ_meas : measlang.

  Lemma aux_allocN_meas : measurable_fun auxcov_allocN aux_allocN.
  Proof.
    mcrunch_prod; try by eauto with measlang.
  Qed.
  Hint Resolve aux_allocN_meas : measlang.

  Lemma cover_allocN_ok_meas : measurable cover_allocN_ok.
  Proof.
    mcrunch_prod; try by eauto with measlang.
  Qed.
  Hint Resolve cover_allocN_ok_meas : measlang.

  Lemma cover_allocN_stuck_meas : measurable cover_allocN_stuck.
  Proof.
    mcrunch_prod; try by eauto with measlang.
  Qed.
  Hint Resolve cover_allocN_stuck_meas : measlang.

  Lemma auxcov_load_meas : measurable auxcov_load.
  Proof. unfold auxcov_load. by eauto with measlang. Qed.
  Hint Resolve auxcov_load_meas : measlang.

  Lemma aux_load_loc_meas : measurable_fun auxcov_load aux_load_loc.
  Proof.
    unfold aux_load_loc.
    unfold auxcov_load.
    eapply (@measurable_comp _ _ _ _ _ _ _ 𝜋_LitLocU).
    3: by apply 𝜋_LitLocU_meas.
    { by eauto with measlang. }
    { rewrite /subset//=.
      move=>?[++].
      move=>?[++].
      move=>[?->]//=.
      move=>[++].
      move=>[?->]//=.
      move=>[++].
      move=>[?->]//=.
      by move=>?<-//.
    }
    eapply (@measurable_comp _ _ _ _ _ _ _ 𝜋_LitV_v).
    3: by apply 𝜋_LitVU_meas.
    { by eauto with measlang. }
    { rewrite /subset//=.
      move=>?[++].
      move=>?[++].
      move=>[?->]//=.
      move=>[++].
      move=>[?->]//=.
      move=>[++].
      move=>[?->]//=.
      move=>[++].
      move=>[?->]//=.
      move=><-//.
      rewrite /vcov_lit/LitVC//=.
      by eexists _.
    }
    eapply (@measurable_comp _ _ _ _ _ _ _ 𝜋_Val_v).
    3: by apply 𝜋_ValU_meas.
    { by eauto with measlang. }
    { rewrite /subset//=.
      move=>?[++].
      move=>?[++].
      move=>[?->]//=.
      move=>[++].
      move=>[?->]//=.
      move=>[++].
      move=>[?->]//=.
      move=>[++].
      move=>[?->]//=.
      move=><-//.
      rewrite /vcov_lit/LitVC//=.
      rewrite /ecov_val//=.
      by eexists _.
    }
    rewrite <-(setIid ecov_load).
    rewrite <-setIA.
    by apply measurable_fun_setI1; try by eauto with measlang.
  Qed.
  Hint Resolve aux_load_loc_meas : measlang.

  Lemma cover_load_ok_meas : measurable cover_load_ok.
  Proof.
    have S1 : (expr_cyl.-sigma, _).-prod.-measurable (auxcov_load `*` [set: state]).
    { by apply measurableX; eauto with measlang. }
    (*
    apply (@measurable_fun_prod' _ _ _ _ _ _ (ssrfun.comp aux_load_loc fst) snd).
    1, 4: done.
    3: by eauto with measlang.
    { eapply @measurable_comp.
      3: by apply aux_load_loc_meas.
      1: by eauto with measlang.
      { rewrite /subset//=.
        move=>?[+[++]].
        by move=>???<-//. }
      eapply @mathcomp_measurable_fun_restiction_setT.
      { by eauto with measlang. }
      { by apply measurable_fst. }
    }
    { eapply @mathcomp_measurable_fun_restiction_setT.
      { by eauto with measlang. }
      { by apply measurable_snd. }
    }
  Qed. *)
  Admitted.
  Hint Resolve cover_load_ok_meas : measlang.

  Lemma cover_load_stuck_meas : measurable cover_load_stuck.
  Proof. Admitted.
  (*
    have S1 : (expr_cyl.-sigma, _).-prod.-measurable (auxcov_load `*` [set: state]).
    { by apply measurableX; eauto with measlang. }
    apply (@measurable_fun_prod' _ _ _ _ _ _ (ssrfun.comp aux_load_loc fst) snd).
    1, 4: done.
    3: eauto with measlang.
    { eapply @measurable_comp.
      3: by apply aux_load_loc_meas.
      1: by eauto with measlang.
      { rewrite /subset//=.
        move=>?[+[++]].
        by move=>???<-//. }
      eapply @mathcomp_measurable_fun_restiction_setT.
      { by eauto with measlang. }
      { by apply measurable_fst. }
    }
    { eapply @mathcomp_measurable_fun_restiction_setT.
      { by eauto with measlang. }
      { by apply measurable_snd. }
    }
  Qed. *)
  Hint Resolve cover_load_stuck_meas : measlang.


  Lemma auxcov_store_meas : measurable auxcov_store.
  Proof.
    apply @measurable_fst.
    { by eauto with measlang. }
    apply 𝜋_StoreU_meas.
    { by eauto with measlang. }
    apply measurableX.
    { by eauto with measlang. }
    { by eauto with measlang. }
  Qed.
  Hint Resolve auxcov_store_meas : measlang.

  Lemma aux_store_loc_meas : measurable_fun auxcov_store aux_store_loc.
  Proof.
    unfold aux_store_loc.
    unfold auxcov_store.
    eapply (@measurable_comp _ _ _ _ _ _ _ 𝜋_LitLocU).
    3: by eauto with measlang.
    1: by eauto with measlang.
    { rewrite /subset//=.
      move=>?.
      repeat move=>[++]; move=>??//=.
      repeat move=>[++]; move=>?//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>??//=.
      rewrite /bcov_LitLoc.
      move=><-//=.
      by eexists.
    }
    mcrunch_comp.
    { rewrite /subset//=.
      move=>?.
      repeat move=>[++]; move=>??//=.
      repeat move=>[++]; move=>?//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>??//=.
      rewrite /vcov_lit.
      move=><-//=.
      by eexists.
    }
    mcrunch_comp.
    {
      move=>?.
      repeat move=>[++]; move=>??//=.
      repeat move=>[++]; move=>?//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>??//=.
      rewrite /ecov_val.
      move=><-//=.
      by eexists.
    }
    mcrunch_comp.
    mcrunch_comp.
    {
      move=>?.
      repeat move=>[++]; move=>??//=.
      repeat move=>[++]; move=>?//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      rewrite /ecov_alloc.
      move=><-//=.
      eexists _.
      eexists _.
      done.
    }
  by eapply @measurable_fst_restriction; eauto with measlang.
  Qed.
  Hint Resolve aux_store_loc_meas : measlang.

  Lemma aux_store_v_meas : measurable_fun auxcov_store aux_store_v.
  Proof.
    unfold aux_store_v.
    unfold auxcov_store.
    eapply (@measurable_comp _ _ _ _ _ _ _ 𝜋_ValU).
    3: by eauto with measlang.
    1: by eauto with measlang.
    { rewrite /subset//=.
      move=>?.
      repeat move=>[++]; move=>??//=.
      repeat move=>[++]; move=>?//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>??//=.
      by move=>?<-//=.
    }
    mcrunch_comp.
    mcrunch_comp.
    { rewrite /subset//=.
      move=>?.
      repeat move=>[++]; move=>??//=.
      repeat move=>[++]; move=>?//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      rewrite /ecov_alloc//=.
      move=><-//=.
      eexists.
      by eexists.
    }
    by eapply @measurable_fst_restriction; eauto with measlang.
  Qed.
  Hint Resolve aux_store_v_meas : measlang.

  Lemma aux_store_σ_meas : measurable_fun auxcov_store aux_store_σ.
  Proof. by eapply @measurable_snd_restriction; eauto with measlang. Qed.
  Hint Resolve aux_store_σ_meas : measlang.

  Lemma aux_store_meas : measurable_fun auxcov_store aux_store.
  Proof.
    mcrunch_prod; try by eauto with measlang.
    mcrunch_prod; by eauto with measlang.
  Qed.
  Hint Resolve aux_store_meas : measlang.

  Lemma cover_store_ok_meas : measurable cover_store_ok.
  Proof.
    mcrunch_prod; try by eauto with measlang.
    mcrunch_prod; by eauto with measlang.
  Qed.
  Hint Resolve cover_store_ok_meas : measlang.

  Lemma cover_store_stuck_meas : measurable cover_store_stuck.
  Proof.
    mcrunch_prod; try by eauto with measlang.
    mcrunch_prod; by eauto with measlang.
  Qed.
  Hint Resolve cover_store_stuck_meas : measlang.

  Lemma cover_ifT_meas : measurable cover_ifT.
  Proof.
    apply NonStatefulS_measurable.
    apply 𝜋_If_c_meas; first by eauto with measlang.
    apply 𝜋_Val_v_meas; first by eauto with measlang.
    apply 𝜋_LitV_v_meas; first by eauto with measlang.
    apply 𝜋_LitBool_b_meas; first by eauto with measlang.
    by rewrite /measurable/discr_measurable//=.
  Qed.
  Hint Resolve cover_ifT_meas : measlang.

  Lemma cover_ifF_meas : measurable cover_ifF.
  Proof.
    apply NonStatefulS_measurable.
    apply 𝜋_If_c_meas; first by eauto with measlang.
    apply 𝜋_Val_v_meas; first by eauto with measlang.
    apply 𝜋_LitV_v_meas; first by eauto with measlang.
    apply 𝜋_LitBool_b_meas; first by eauto with measlang.
    by rewrite /measurable/discr_measurable//=.
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

  Lemma cover_allocTape_meas : measurable cover_allocTape.
  Proof.
    apply NonStatefulS_measurable.
    apply 𝜋_AllocTapeU_meas; first by eauto with measlang.
    apply 𝜋_ValU_meas; first by eauto with measlang.
    apply 𝜋_LitVU_meas; first by eauto with measlang.
    by eauto with measlang.
  Qed.
  Hint Resolve cover_allocTape_meas : measlang.

  Lemma cover_allocUTape_meas : measurable cover_allocUTape.
  Proof.
    apply NonStatefulS_measurable.
    by eauto with measlang.
  Qed.
  Hint Resolve cover_allocUTape_meas : measlang.

  Lemma cover_rand_meas : measurable cover_rand.
  Proof.
    apply NonStatefulS_measurable.
    apply 𝜋_RandU_meas; first by eauto with measlang.
    apply measurableX.
    { apply 𝜋_ValU_meas; first by eauto with measlang.
      apply 𝜋_LitVU_meas; first by eauto with measlang.
      by eauto with measlang. }
    { apply 𝜋_ValU_meas; first by eauto with measlang.
      apply 𝜋_LitVU_meas; first by eauto with measlang.
      by eauto with measlang. }
  Qed.
  Hint Resolve cover_rand_meas : measlang.

  Lemma cover_urand_meas : measurable cover_urand.
  Proof.
    apply NonStatefulS_measurable.
    apply 𝜋_URandU_meas; first by eauto with measlang.
    apply 𝜋_ValU_meas; first by eauto with measlang.
    apply 𝜋_LitVU_meas; first by eauto with measlang.
    by eauto with measlang.
  Qed.
  Hint Resolve cover_urand_meas : measlang.

  Lemma cover_randT_meas : measurable cover_randT.
  Proof.
    apply NonStatefulS_measurable.
    apply 𝜋_RandU_meas; first by eauto with measlang.
    apply measurableX.
    { apply 𝜋_ValU_meas; first by eauto with measlang.
      apply 𝜋_LitVU_meas; first by eauto with measlang.
      by eauto with measlang. }
    { apply 𝜋_ValU_meas; first by eauto with measlang.
      apply 𝜋_LitVU_meas; first by eauto with measlang.
      by eauto with measlang. }
  Qed.
  Hint Resolve cover_randT_meas : measlang.

  Lemma cover_urandT_meas : measurable cover_urandT.
  Proof.
    apply NonStatefulS_measurable.
    apply 𝜋_URandU_meas; first by eauto with measlang.
    apply 𝜋_ValU_meas; first by eauto with measlang.
    apply 𝜋_LitVU_meas; first by eauto with measlang.
    by eauto with measlang.
  Qed.
  Hint Resolve cover_urandT_meas : measlang.

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
  Proof.
    apply measurableC.
    rewrite //=.
    repeat (eapply (@measurableU _ cfg _); first by eauto with measlang).
    by eapply @measurable0.
  Qed.
  Hint Resolve cover_maybe_stuck_meas : measlang.

  (**  Top-level functions *)

  (* Generic lifting of a curried constructor on expr to a curried constructor on states *)
  Definition NonStatefulU {A : Type} (C : A -> expr) : (A * state) -> cfg := fun x => (C x.1, x.2).

  Lemma NonStatefulU_meas {d} {A : measurableType d} (C : A -> expr) (S : set A) (HS : measurable S)
      (HC : measurable_fun S C) : measurable_fun (NonStatefulS S) (NonStatefulU C).
  Proof.
    rewrite /NonStatefulU//=.
    have H1 : measurable_fun (T:=A) (U:=A) S (fun x => x).
    { apply mathcomp_measurable_fun_restiction_setT; [done|].
      by apply measurable_id.
    }
    apply (measurable_fun_prod' (ssrfun.comp C fst) snd (NonStatefulS S) (NonStatefulS_measurable S HS)).
    - eapply measurable_comp.
      3: { by apply HC. }
      + by apply HS.
      + by rewrite /NonStatefulS/preimage/subset//=; move=> t [??<-].
      + apply (mathcomp_measurable_fun_restiction_setT (NonStatefulS S) (NonStatefulS_measurable S HS) fst).
        by eapply @measurable_fst_restriction; eauto with measlang.
    - apply (mathcomp_measurable_fun_restiction_setT (NonStatefulS S) (NonStatefulS_measurable S HS) snd).
        by eapply @measurable_snd_restriction; eauto with measlang.
  Qed.

  (** Top-level functions *)
  (* | Rec f x e => gRet ((Val $ RecV f x e, σ1) : cfg)  *)
  Definition head_stepM_rec : cfg -> giryM cfg :=
    ssrfun.comp gRet $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp RecVU 𝜋_RecU.

  (* | Pair (Val v1) (Val v2) => gRet ((Val $ PairV v1 v2, σ1) : cfg)   *)
  Definition head_stepM_pair : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp PairVU $
    mProd
      (ssrfun.comp 𝜋_Val_v 𝜋_Pair_l)
      (ssrfun.comp 𝜋_Val_v $ 𝜋_Pair_r).

  (* | InjL (Val v) => gRet ((Val $ InjLV v, σ1) : cfg) *)
  Definition head_stepM_injL : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp InjLVU $
    ssrfun.comp 𝜋_ValU $
    𝜋_InjLU.

  (* | InjR (Val v) => gRet ((Val $ InjRV v, σ1) : cfg) *)
  Definition head_stepM_injR : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp InjRVU $
    ssrfun.comp 𝜋_ValU $
    𝜋_InjRU.

  (* | App (Val (RecV f x e1)) (Val v2) => gRet ((subst' x v2 (subst' f (RecV f x e1) e1) , σ1) : cfg)  *)
  Definition head_stepM_app : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
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
          | Some w => gRet ((Val w, σ1) : cfg)
          | _ => gZero
        end
   *)

  (* The function (on configurations) to do when the cfg is a UnOp that is valid *)
  Definition head_stepM_unop_ok : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
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
    cst gZero.

  (* The function (on configurations) to do when the cfg is a BinOp that is valid *)
  Definition head_stepM_binop_ok : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
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
    cst gZero.


  (*
    | AllocN (Val (LitV (LitInt N))) (Val v) =>
        if bool_decide (0 < Z.to_nat N)%nat
          then
            let ℓ := fresh_loc σ1.(heap) in
            gRet ((Val $ LitV $ LitLoc ℓ, state_upd_heap_N ℓ (Z.to_nat N) v σ1) : cfg)
          else gZero

   *)
  Definition head_stepM_allocN_ok : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    mProd
      (ssrfun.comp ValU $
       ssrfun.comp LitVU $
       ssrfun.comp LitLocU $
       ssrfun.comp state_allocNCE $
       aux_allocN)
      (ssrfun.comp state_allocNCS $
       aux_allocN).

  (* TODO: Delete *)
  Definition head_stepM_allocN_stuck: cfg -> giryM cfg :=
    cst gZero.

  (*
    | Load (Val (LitV (LitLoc l))) =>
        match σ1.(heap) !! l with
          | Some v => gRet ((Val v, σ1) : cfg)
          | None => gZero
        end
   *)
  Definition head_stepM_load_ok : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    mProd
      ( ssrfun.comp ValU $
        ssrfun.comp state_loadC $
        (mProd (ssrfun.comp aux_load_loc fst) snd) )
      snd.

  (* TODO: Delete *)
  Definition head_stepM_load_stuck: cfg -> giryM cfg :=
    cst gZero.

  Definition head_stepM_store_ok : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    mProd
      (ssrfun.comp state_storeE $ aux_store)
      (ssrfun.comp state_storeS $ aux_store).

  (* TODO: Delete *)
  Definition head_stepM_store_stuck: cfg -> giryM cfg :=
    cst gZero.

  (* | If (Val (LitV (LitBool true))) e1 e2  => gRet ((e1 , σ1) : cfg) *)
  Definition head_stepM_ifT : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    𝜋_If_l.

  (* | If (Val (LitV (LitBool false))) e1 e2 => gRet ((e2 , σ1) : cfg) *)
  Definition head_stepM_ifF : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    𝜋_If_r.

  (* | Fst (Val (PairV v1 v2)) => gRet ((Val v1, σ1) : cfg) *)
  Definition head_stepM_fst : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp 𝜋_PairV_l $
    ssrfun.comp 𝜋_ValU $
    𝜋_Fst_e.

  (* | Snd (Val (PairV v1 v2)) => gRet ((Val v2, σ1) : cfg) *)
  Definition head_stepM_snd : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp 𝜋_PairV_r $
    ssrfun.comp 𝜋_ValU $
    𝜋_Snd_e.

  (* | Case (Val (InjLV v)) e1 e2 => gRet ((App e1 (Val v), σ1) : cfg) *)
  Definition head_stepM_caseL : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    ssrfun.comp AppU $
    mProd
      𝜋_Case_l
      ( ssrfun.comp ValU $
        ssrfun.comp 𝜋_InjLV_v $
        ssrfun.comp 𝜋_Val_v $
        𝜋_Case_c ).

  (* | Case (Val (InjRV v)) e1 e2 => gRet ((App e2 (Val v), σ1) : cfg) *)
  Definition head_stepM_caseR : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    ssrfun.comp AppU $
    mProd
      𝜋_Case_r
      ( ssrfun.comp ValU $
        ssrfun.comp 𝜋_InjRV_v $
        ssrfun.comp 𝜋_Val_v $
        𝜋_Case_c ).


  Definition head_stepM_allocTape_aux : cfg -> (<<discr Z>> * state)%type :=
    mProd
      (ssrfun.comp 𝜋_LitInt_z $
       ssrfun.comp 𝜋_LitV_v $
       ssrfun.comp 𝜋_Val_v $
       ssrfun.comp 𝜋_AllocTape_e $
       fst)
      snd.
  (*
    | AllocTape (Val (LitV (LitInt z))) =>
        let ι := fresh_loc σ1.(tapes) in
        gRet ((Val $ LitV $ LitLbl ι, state_upd_tapes <[ι := {| btape_tape := emptyTape ; btape_bound := (Z.to_nat z) |} ]> σ1) : cfg)
      destruct and apply RandAllcoTapeE/S
  *)
  Definition head_stepM_allocTape : cfg -> giryM cfg :=
    if_in (ssrfun.comp rand_allocTape_ok_cov head_stepM_allocTape_aux)
      (ssrfun.comp (gRet) $
        mProd
        (ssrfun.comp ValU $
          ssrfun.comp LitVU $
          ssrfun.comp LitLblU $
          ssrfun.comp rand_allocTapeE $
          head_stepM_allocTape_aux)
        (ssrfun.comp rand_allocTapeS $
          head_stepM_allocTape_aux))
        (cst gZero).


  (*
    | AllocUTape =>
        let ι := fresh_loc σ1.(utapes) in
        gRet ((Val $ LitV $ LitLbl ι, state_upd_utapes <[ ι := emptyTape ]> σ1) : cfg)
   *)
  Definition head_stepM_allocUTape : cfg -> giryM cfg :=
    if_in (ssrfun.comp rand_allocUTape_ok_cov snd)
      (ssrfun.comp (gRet) $
      mProd
        (ssrfun.comp ValU $
         ssrfun.comp LitVU $
         ssrfun.comp LitLblU $
         ssrfun.comp rand_allocUTapeE $
         snd)
        (ssrfun.comp rand_allocUTapeS $
         snd))
      (cst gZero).

  (* Rand (Val (LitInt N)) (Val LitUnit) -> ... *)
  Definition head_stepM_aux_rand : cfg -> (<<discr Z>> * state)%type :=
    mProd
      (ssrfun.comp 𝜋_LitInt_z $
       ssrfun.comp 𝜋_LitV_v $
       ssrfun.comp 𝜋_Val_v $
       ssrfun.comp 𝜋_Rand_N $
       fst)
      snd.

  Definition head_stepM_rand : cfg -> giryM cfg :=
    ssrfun.comp rand_rand head_stepM_aux_rand.

  Definition head_stepM_aux_urand : cfg -> state :=
    snd.

  Definition head_stepM_urand : cfg -> giryM cfg :=
    ssrfun.comp rand_urand head_stepM_aux_urand.

  (* Rand (Val (LitInt N)) (Val (LitLbl t)) -> ... *)
  Definition head_stepM_aux_randT : cfg -> (<<discr Z >> * <<discr loc >> * state)%type :=
    mProd
      (mProd
        (ssrfun.comp 𝜋_LitInt_z $
         ssrfun.comp 𝜋_LitV_v $
         ssrfun.comp 𝜋_Val_v $
         ssrfun.comp 𝜋_Rand_N $
         fst)
        (ssrfun.comp 𝜋_LitLbl_l $
         ssrfun.comp 𝜋_LitV_v $
         ssrfun.comp 𝜋_Val_v $
         ssrfun.comp 𝜋_Rand_t $
         fst))
      snd.

  Definition head_stepM_randT : cfg -> giryM cfg :=
    ssrfun.comp rand_randT head_stepM_aux_randT.

  (* URand  (Val (LitLbl t)) -> ... *)
  Definition head_stepM_aux_urandT : cfg -> (<<discr loc >> * state)%type :=
    mProd
      (ssrfun.comp 𝜋_LitLbl_l $
       ssrfun.comp 𝜋_LitV_v $
       ssrfun.comp 𝜋_Val_v $
       ssrfun.comp 𝜋_URand_e $
       fst)
      snd.

  Definition head_stepM_urandT : cfg -> giryM cfg :=
    ssrfun.comp rand_urandT head_stepM_aux_urandT.

  (* | Tick (Val (LitV (LitInt n))) => gRet ((Val $ LitV $ LitUnit, σ1) : cfg) *)
  Definition head_stepM_tick : cfg -> giryM cfg :=
    ssrfun.comp (gRet) $
    NonStatefulU $
    ssrfun.comp ValU $
    ssrfun.comp LitVU $
    cst LitUnit.

  Definition head_stepM_stuck : cfg -> giryM cfg :=
    cst gZero.




  (* TODO: Eventually we could make this definition look less goofy?
     The functions don't _need_ each case to be defeq to a measurable function,
     since we're proving the restriction of head_stepM to every set in the cover
     is propeq to measurable function instead (see: head_stepM_rec_meas).
   *)
  Definition head_stepM (c : cfg) : giryM cfg :=
    let (e1, σ1) := c in
    match e1 with
    | Rec _ _ _                                            => head_stepM_rec c
    | Pair (Val _) (Val _)                                 => head_stepM_pair c
    | InjL (Val _)                                         => head_stepM_injL c
    | InjR (Val _)                                         => head_stepM_injR c
    | App (Val (RecV _ _ _)) (Val _)                       => head_stepM_app c
    | UnOp op (Val v)                                      => match un_op_eval op v with
                                                              | Some _ => head_stepM_unop_ok c
                                                              | _ => head_stepM_unop_stuck c
                                                              end
    | BinOp op (Val v1) (Val v2)                           => match bin_op_eval op v1 v2 with
                                                              | Some _ => head_stepM_binop_ok c
                                                              | None => head_stepM_binop_stuck c
                                                             end
    | If (Val (LitV (LitBool true))) _ _                   => head_stepM_ifT c
    | If (Val (LitV (LitBool false))) _ _                  => head_stepM_ifT c
    | Fst (Val (PairV _ _))                                => head_stepM_fst c
    | Snd (Val (PairV _ _))                                => head_stepM_snd c
    | Case (Val (InjLV _)) _ _                             => head_stepM_caseL c
    | Case (Val (InjRV _)) _ _                             => head_stepM_caseR c
    | AllocN (Val (LitV (LitInt N))) (Val v)               => (if_in cover_allocN_ok
                                                                head_stepM_allocN_ok
                                                                head_stepM_allocN_stuck) c
    | Load (Val (LitV (LitLoc l)))                         => (if_in cover_load_ok
                                                                head_stepM_load_ok
                                                                head_stepM_load_stuck) c
    | Store (Val (LitV (LitLoc l))) (Val v)                => (if_in cover_store_ok
                                                                head_stepM_store_ok
                                                                head_stepM_store_stuck) c
    | AllocTape (Val (LitV (LitInt z)))                    => head_stepM_allocTape c
    | AllocUTape                                           => head_stepM_allocUTape c
    | Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit))    => head_stepM_rand c
    | URand (Val (LitV LitUnit))                           => head_stepM_urand c
    | Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))) => head_stepM_randT c
    | URand (Val (LitV (LitLbl l)))                        => head_stepM_urandT c
    | Tick (Val (LitV (LitInt _)))                         => head_stepM_tick c
    | _                                                    => head_stepM_stuck c
    end.

  Hint Resolve measurable_compT : measlang.

  (* Combining solve_packaged_meas and solve_toplevel_meas is too slow! *)
  Ltac solve_toplevel_meas :=
    repeat (
      try (apply measurable_compT);
      try (by eauto with measlang)
    ).

  Hint Resolve gRet_meas_fun : measlang.



  (** Measurability of head_step restricted to the different sets in the cover *)
  Lemma head_stepM_rec_meas : measurable_fun cover_rec head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_rec head_stepM).
    - solve_toplevel_meas.
      { by apply gRet_meas_fun. }
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

  Lemma head_stepM_pair_meas : measurable_fun cover_pair head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_pair head_stepM).
    - (* FIXME: Duplicate proof from above *)
      have S : expr_cyl.-sigma.-measurable (ecov_pair `&` 𝜋_PairU @^-1` (ecov_val `*` ecov_val)).
      { apply 𝜋_PairU_meas; last apply measurableX; by eauto with measlang.  }
      apply measurable_compT.
      { by apply cover_pair_meas. }
      { by apply gRet_meas_fun. }
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

  Lemma head_stepM_injL_meas : measurable_fun cover_injL head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_injL head_stepM).
    - apply measurable_compT.
      { by apply cover_injL_meas. }
      { by apply gRet_meas_fun. }
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

  Lemma head_stepM_injR_meas : measurable_fun cover_injR head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_injR head_stepM).
    - apply measurable_compT.
      { by apply cover_injR_meas. }
      { by apply gRet_meas_fun. }
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
  Lemma head_stepM_app_meas : measurable_fun cover_app head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_app head_stepM).
    - apply measurable_compT.
      { by apply cover_app_meas. }
      { by apply gRet_meas_fun. }
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

  Lemma head_stepM_unop_ok_meas : measurable_fun cover_unop_ok head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_unop_ok head_stepM).
    - apply measurable_compT.
      { by apply cover_unop_ok_meas. }
      { by apply gRet_meas_fun. }
      eapply @measurable_fun_prod'.
      { by eauto with measlang. }
      2: { eapply @mathcomp_measurable_fun_restiction_setT.
           - by eauto with measlang.
           - by eapply @measurable_snd_restriction; eauto with measlang.
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
           - by eapply @measurable_fst_restriction; eauto with measlang.
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

  Lemma head_stepM_unop_stuck_meas : measurable_fun cover_unop_stuck head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_unop_stuck head_stepM).
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

  Lemma head_stepM_binop_ok_meas : measurable_fun cover_binop_ok head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_binop_ok head_stepM).
    - apply measurable_compT.
      { by apply cover_binop_ok_meas. }
      { by apply gRet_meas_fun. }
  Admitted.
  (*
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

*)
  Hint Resolve head_stepM_binop_ok_meas : measlang.

  Lemma head_stepM_binop_stuck_meas : measurable_fun cover_binop_stuck head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_binop_stuck head_stepM).
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

  Lemma head_stepM_allocN_ok_meas : measurable_fun cover_allocN_ok head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_allocN_ok).
    - mcrunch_comp.
      mcrunch_prod.
      { mcrunch_compC ValU_measurable.
        mcrunch_compC LitVU_measurable.
        mcrunch_compC LitLocU_measurable.
        mcrunch_comp.
        { rewrite /subset/cover_allocN_ok/auxcov_allocN_ok//=.
          move=> [??].
          repeat move=>[++]; move=>??//=.
          repeat move=>[++]; move=>?//=.
          repeat move=>[++]; move=>?->//=.
          repeat move=>[++]; move=>?->//=.
          repeat move=>[++]; move=>?->//=.
          repeat move=>[++]; move=>?->//=.
          repeat move=>[++]; move=>?->//=.
          repeat rewrite /aux_allocN_Z/aux_allocN_v/aux_allocN//=.
          move=>?.
          by move=>[?<-].
        }
        unfold cover_allocN_ok.
        rewrite <-(setIid auxcov_allocN).
        rewrite <-setIA.
        apply (measurable_fun_setI1 aux_allocN auxcov_allocN); by eauto with measlang.
      }
      { mcrunch_comp.
        { rewrite /subset/cover_allocN_ok/auxcov_allocN_ok//=.
          move=> [??].
          repeat move=>[++]; move=>??//=.
          repeat move=>[++]; move=>?//=.
          repeat move=>[++]; move=>?->//=.
          repeat move=>[++]; move=>?->//=.
          repeat move=>[++]; move=>?->//=.
          repeat move=>[++]; move=>?->//=.
          repeat move=>[++]; move=>?->//=.
          repeat rewrite /aux_allocN_Z/aux_allocN_v/aux_allocN//=.
          move=>?.
          by move=>[?<-].
        }
        unfold cover_allocN_ok.
        rewrite <-(setIid auxcov_allocN).
        rewrite <-setIA.
        apply (measurable_fun_setI1 aux_allocN auxcov_allocN); by eauto with measlang.
      }
    - move=> [??].
      repeat move=>[++]; move=>?//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat rewrite /auxcov_allocN_ok/aux_allocN_Z///=.
      move=> H.
      rewrite ifIn_eq_left; [done|].
      rewrite /cover_allocN_ok//=.
      split; [|done].
      rewrite /auxcov_allocN/ecov_alloc/ecov_val/vcov_lit/bcov_LitInt //=.
      split; [done|].
      split; [eexists _; eexists _; done|].
      split; [|eexists _; done].
      split; [eexists _; done|].
      split; eexists _; done.
    Unshelve. by eauto with measlang.
  Qed.
  Hint Resolve head_stepM_allocN_ok_meas : measlang.

  Lemma head_stepM_allocN_stuck_meas : measurable_fun cover_allocN_stuck head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_allocN_stuck).
    - by apply measurable_cst.
    - move=> [??].
      repeat move=>[++]; move=>?//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat move=>[++]; move=>?->//=.
      repeat rewrite /auxcov_allocN_stuck/aux_allocN_Z///=.
      move=> H.
      rewrite ifIn_eq_right; [done|].
      (* Easy *)
    Admitted.
    (*
    Unshelve. by eauto with measlang.
  Qed.
*)
  Hint Resolve head_stepM_allocN_stuck_meas : measlang.

  Lemma head_stepM_load_ok_meas : measurable_fun cover_load_ok head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_load_ok).
    - mcrunch_comp.
      mcrunch_prod.
      2: by eapply @measurable_snd_restriction; eauto with measlang.
      mcrunch_compC ValU_measurable.
      mcrunch_comp.
      { rewrite /subset/auxcov_load_ok/aux_load_loc//=.
        move=>[??].
        do 3 (move=>[+]/=; move=>?//=; try move=>->//=).
        move=>?.
        do 1 (move=>[+]/=; try move=>->//=).
        do 2 move=><-//=.
        by eexists _.
      }
      mcrunch_prod; last by eapply @measurable_snd_restriction; eauto with measlang.
      mcrunch_comp; last by eapply @measurable_fst_restriction; eauto with measlang.
      { rewrite /subset/cover_load_ok/auxcov_load//=.
        move=>?.
        (repeat move=>[++]); move=>??//=.
        (repeat move=>[++]); move=>?->//=.
        (repeat move=>[++]); move=>?->//=.
        (repeat move=>[++]); move=>?->//=.
        (repeat move=>[++]); move=>?->//=.
        move=>?//=.
        (repeat move=>[++]); move=>?//=.
        move=>?<-//=.
        rewrite /ecov_load/ecov_val/vcov_lit/bcov_LitLoc//=.
        split; first by eexists _.
        split; first by eexists _.
        split; first by eexists _.
        by eexists.
      }
    - move=>[??].
      repeat ((repeat move=>[++]//=); move=>?//=->//=).
      move=>?//=.
      rewrite /auxcov_load_ok//=.
      rewrite ifIn_eq_left; last first.
  Admitted.
 (*

        by repeat ((repeat move=>[++]//=); move=>?//=->//=). }
    Unshelve. by eauto with measlang.
  Qed.*)
  Hint Resolve head_stepM_load_ok_meas : measlang.

  Lemma head_stepM_load_stuck_meas : measurable_fun cover_load_stuck head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_load_stuck head_stepM).
    - by apply measurable_cst.
    - move=>[e?].
  Admitted.
  (*
      by repeat ((repeat move=>[++]//=); move=>?//=->//=).
    Unshelve. by eauto with measlang.
  Qed.
*)
  Hint Resolve head_stepM_load_stuck_meas : measlang.

  Lemma head_stepM_store_ok_meas : measurable_fun cover_store_ok head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_store_ok).
    - mcrunch_comp.
      mcrunch_prod.
      { mcrunch_comp.
        { rewrite /subset/cover_store_ok/auxcov_store//=.
          move=>[[??]?].
          (repeat move=>[++]); move=>??//=.
          (repeat move=>[++]); move=>?//=.
          (repeat move=>[++]); move=>?->//=.
          (repeat move=>[++]); move=>?->//=.
          (repeat move=>[++]); move=>?->//=.
          (repeat move=>[++]); move=>?->//=.
          (repeat move=>[++]); move=>?->//=.
          repeat (rewrite /auxcov_store_ok/aux_store_loc/aux_store/aux_store_v//=).
          (repeat move=>[++]); move=>?//=.
          move=>?.
          move=>[+].
          move=><-?<-.
          by eexists _.
        }
        unfold cover_store_ok.
        rewrite <-(setIid auxcov_store).
        rewrite <-setIA.
        apply (measurable_fun_setI1 aux_store auxcov_store); by eauto with measlang.
      }
      { mcrunch_comp.
        { rewrite /subset/cover_store_ok/auxcov_store//=.
          move=>[[??]?].
          (repeat move=>[++]); move=>??//=.
          (repeat move=>[++]); move=>?//=.
          (repeat move=>[++]); move=>?->//=.
          (repeat move=>[++]); move=>?->//=.
          (repeat move=>[++]); move=>?->//=.
          (repeat move=>[++]); move=>?->//=.
          (repeat move=>[++]); move=>?->//=.
          repeat (rewrite /auxcov_store_ok/aux_store_loc/aux_store/aux_store_v//=).
          (repeat move=>[++]); move=>?//=.
          move=>?.
          move=>[+].
          move=><-?<-.
          by eexists _.
        }
        unfold cover_store_ok.
        rewrite <-(setIid auxcov_store).
        rewrite <-setIA.
        apply (measurable_fun_setI1 aux_store auxcov_store); by eauto with measlang.
      }
    - move=>[e?].
      (repeat move=>[++]); move=>?//=.
      (repeat move=>[++]); move=>?->//=.
      (repeat move=>[++]); move=>?->//=.
      (repeat move=>[++]); move=>?->//=.
      (repeat move=>[++]); move=>?->//=.
      (repeat move=>[++]); move=>?->//=.
      rewrite /auxcov_store_ok//=.
    Admitted.
  (*
      by (repeat move=>[++]); move=>?->//=.
    Unshelve. by eauto with measlang.
  Qed.
*)
  Hint Resolve head_stepM_store_ok_meas : measlang.

  Lemma head_stepM_store_stuck_meas : measurable_fun cover_store_stuck head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_store_stuck).
    - by apply measurable_cst.
    - move=>[e?].
      (repeat move=>[++]); move=>?//=.
      (repeat move=>[++]); move=>?->//=.
      (repeat move=>[++]); move=>?->//=.
      (repeat move=>[++]); move=>?->//=.
      (repeat move=>[++]); move=>?->//=.
      (repeat move=>[++]); move=>?->//=.
      rewrite /auxcov_store_stuck//=.
    Admitted.
  (*
      by move=>->.
    Unshelve. by eauto with measlang.
  Qed.
*)
  Hint Resolve head_stepM_load_stuck_meas : measlang.


  Lemma head_stepM_ifT_meas : measurable_fun cover_ifT head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_ifT head_stepM).
    - apply measurable_compT.
      { by apply cover_ifT_meas. }
      { by apply gRet_meas_fun. }
      have S : expr_cyl.-sigma.-measurable (ecov_if `&` 𝜋_If_c @^-1` (ecov_val `&` 𝜋_Val_v @^-1` (vcov_lit `&` 𝜋_LitV_v @^-1` (bcov_LitBool `&` 𝜋_LitBool_b @^-1` [set true])))).
     { apply 𝜋_If_c_meas; first by eauto with measlang.
       apply 𝜋_Val_v_meas; first by eauto with measlang.
       apply 𝜋_LitV_v_meas; first by eauto with measlang.
       apply 𝜋_LitBool_b_meas; first by eauto with measlang.
       by rewrite /measurable/discr_measurable//=.
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

  Lemma head_stepM_ifF_meas : measurable_fun cover_ifF head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_ifT head_stepM).
    - apply measurable_compT.
      { by apply cover_ifF_meas. }
      { by apply gRet_meas_fun. }
      have S : expr_cyl.-sigma.-measurable (ecov_if `&` 𝜋_If_c @^-1` (ecov_val `&` 𝜋_Val_v @^-1` (vcov_lit `&` 𝜋_LitV_v @^-1` (bcov_LitBool `&` 𝜋_LitBool_b @^-1` [set false])))).
     { apply 𝜋_If_c_meas; first by eauto with measlang.
       apply 𝜋_Val_v_meas; first by eauto with measlang.
       apply 𝜋_LitV_v_meas; first by eauto with measlang.
       apply 𝜋_LitBool_b_meas; first by eauto with measlang.
       by rewrite /measurable/discr_measurable//=.
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

  Lemma head_stepM_fst_meas : measurable_fun cover_fst head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_fst head_stepM).
    - apply measurable_compT.
      { by apply cover_fst_meas. }
      { by apply gRet_meas_fun. }
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

  Lemma head_stepM_snd_meas : measurable_fun cover_snd head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_snd head_stepM).
    - apply measurable_compT.
      { by apply cover_snd_meas. }
      { by apply gRet_meas_fun. }
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

  Lemma head_stepM_caseL_meas : measurable_fun cover_caseL head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_caseL head_stepM).
    - apply measurable_compT.
      { by apply cover_caseL_meas. }
      { by apply gRet_meas_fun. }
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

  Lemma head_stepM_caseR_meas : measurable_fun cover_caseR head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_caseR head_stepM).
    - apply measurable_compT.
      { by apply cover_caseR_meas. }
      { by apply gRet_meas_fun. }
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

  Lemma head_stepM_allocTape_meas : measurable_fun cover_allocTape head_stepM.
  Proof.
  Admitted.
  Hint Resolve head_stepM_allocTape_meas : measlang.

  Lemma head_stepM_allocUTape_meas : measurable_fun cover_allocUTape head_stepM.
  Proof.
  Admitted.
  Hint Resolve head_stepM_allocUTape_meas : measlang.

  Lemma head_stepM_rand_meas : measurable_fun cover_rand head_stepM.
  Proof.
  Admitted.
  Hint Resolve head_stepM_rand_meas : measlang.

  Lemma head_stepM_urand_meas : measurable_fun cover_urand head_stepM.
  Proof.
  Admitted.
  Hint Resolve head_stepM_urand_meas : measlang.

  Lemma head_stepM_randT_meas : measurable_fun cover_randT head_stepM.
  Proof.
  Admitted.
  Hint Resolve head_stepM_randT_meas : measlang.

  Lemma head_stepM_urandT_meas : measurable_fun cover_urandT head_stepM.
  Proof.
  Admitted.
  Hint Resolve head_stepM_urandT_meas : measlang.

  Lemma head_stepM_tick_meas : measurable_fun cover_tick head_stepM.
  Proof.
    eapply (mathcomp_measurable_fun_ext _ _ head_stepM_tick head_stepM).
    - apply measurable_compT.
      { by apply cover_tick_meas. }
      { by apply gRet_meas_fun. }
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

  Lemma head_stepM_stuck_meas : measurable_fun cover_maybe_stuck head_stepM.
  Proof.
    unfold cover_maybe_stuck.
    (* Need to show that, if its not in any of the prior cases, its in the last case
       Probably the easiest way to do this:
          Unfold foldr
          Distribute ~` over disjunction, destruct conjunction
          Case split on expr, by cases get false
     *)
  Admitted.
  Hint Resolve head_stepM_stuck_meas : measlang.


  (**  Head step measurability *)
  Lemma cfg_cover_measurable :
      Forall (fun S => measurable S) cfg_cover.
  Proof.
    repeat (try apply Forall_cons; split); last by apply List.Forall_nil.
    - by apply cover_maybe_stuck_meas.
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
    - by apply cover_allocN_ok_meas.
    - by apply cover_allocN_stuck_meas.
    - by apply cover_load_ok_meas.
    - by apply cover_load_stuck_meas.
    - by apply cover_store_ok_meas.
    - by apply cover_store_stuck_meas.
    - by apply cover_allocTape_meas.
    - by apply cover_allocUTape_meas.
    - by apply cover_rand_meas.
    - by apply cover_urand_meas.
    - by apply cover_randT_meas.
    - by apply cover_urandT_meas.
    - by apply cover_tick_meas.
  Qed.

  Lemma head_stepM_restricted_measurable :
      Forall (fun S => measurable_fun S head_stepM) cfg_cover.
  Proof.
    repeat (try apply Forall_cons; split); last by apply List.Forall_nil.
    - by apply head_stepM_stuck_meas.
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
    - by apply head_stepM_allocN_ok_meas.
    - by apply head_stepM_allocN_stuck_meas.
    - by apply head_stepM_load_ok_meas.
    - by apply head_stepM_load_stuck_meas.
    - by apply head_stepM_store_ok_meas.
    - by apply head_stepM_store_stuck_meas.
    - by apply head_stepM_allocTape_meas.
    - by apply head_stepM_allocUTape_meas.
    - by apply head_stepM_rand_meas.
    - by apply head_stepM_urand_meas.
    - by apply head_stepM_randT_meas.
    - by apply head_stepM_urandT_meas.
    - by apply head_stepM_tick_meas.
  Qed.

  Lemma head_stepM_measurable :
    @measurable_fun _ _ cfg (giryM cfg) setT head_stepM.
  Proof.
    apply (@measurable_by_cover_list _ _ _ _ head_stepM cfg_cover).
    - by apply cfg_cover_measurable.
    - by apply cfg_cover_is_cover.
    - suffices HFdep :
          (Forall (λ l : set cfg,
                     elem_of_list l cfg_cover ->
                     measurable_fun (T:=cfg) (U:=giryM cfg) l (head_stepM \_ l)) cfg_cover).
      { apply Forall_forall.
        intros x Hx.
        by apply (iffLR (Forall_forall _ _) HFdep x Hx Hx).
      }
      eapply (Forall_impl _ _ _ head_stepM_restricted_measurable).
      intros S H HS.

      (*
      apply @mathcomp_restriction_is_measurable in H.
      { eapply @Forall_forall; last first.

        - admit.
        - (*  by apply cfg_cover_measurable. *) admit.
        - by apply HS. }
      by apply mathcomp_restriction_setT.
      *)
  Admitted.

End meas_semantics.

  (*


  Definition urand_tape_step : measurable_map ((R : realType) : measurableType _) cfg.
    (* This funciton needs to do this: *)
    (* (fun (u : R) =>
         (* Fill tape head with new sample *)
         let τ' := <[ (0 : nat) := Some u ]> τ in
         (* Advance tape *)
         let σ' := state_upd_utapes <[ l := (tapeAdvance τ') ]> σ1 in
         (* Return the update value an state *)
         ((Val $ LitV $ LitReal u, σ') : cfg)) *)

*)










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
Global Instance fill_item_inj Ki : Inj eq eq (curry fill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item (Ki, e))) → is_Some (to_val e).
Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.

Lemma val_head_stuck e1 σ1 : ¬ is_zero (head_stepM (e1, σ1)) → to_val e1 = None.
Proof. Admitted.

(*
Lemma val_head_stuck e σ ρ :
  head_step e σ ρ > 0 → to_val e = None.
Proof. destruct ρ, e; [|done..]. rewrite /pmf /=. lra. Qed.
*)



Lemma head_step_ctx_val Ki e σ1 : ¬ is_zero (head_stepM (fill_item (Ki, e), σ1)) → is_Some (to_val e).
Proof. Admitted.

(*

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
  e' = subst x v2 (subst f (RecV f x e1) e1) →
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

(* Heap
| AllocNS z N v σ l :
  l = fresh_loc (heap σ) →
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
*)
(* Rand *)
| RandNoTapeS z N (n_int : Z) (n_nat : nat) σ:
  N = Z.to_nat z →
  n_nat < N ->
  Z.of_nat n_nat = n_int ->
  head_step_rel (Rand (Val $ LitV $ LitInt z) (Val $ LitV LitUnit)) σ (Val $ LitV $ LitInt n_int) σ
(*
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
*)
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
(*
Global Hint Extern 1
  (head_step_rel (Rand (Val (LitV _)) (Val (LitV (LitLbl _)))) _ _ _) =>
         eapply (RandTapeEmptyS _ _ _ 0%fin) : head_step.
Global Hint Extern 1
  (head_step_rel (Rand (Val (LitV _)) (Val (LitV (LitLbl _)))) _ _ _) =>
         eapply (RandTapeOtherS _ _ _ _ _ 0%fin) : head_step.
*)
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

Lemma head_step_mass e σ : ¬ is_zero (head_stepM (e, σ)) → is_prob (head_stepM (e, σ)).
Proof. Admitted.

(*
Lemma head_step_mass e σ :
  (∃ ρ, head_step e σ ρ > 0) → SeriesC (head_step e σ) = 1.
Proof.
  intros [[] Hs%head_step_support_equiv_rel].
  inversion Hs;
    repeat (simplify_map_eq/=; solve_distr_mass || case_match; try (case_bool_decide; done)).
Qed.
*)

Definition meas_lang_mixin :
  @MeasEctxiLanguageMixin _ _ _ _ expr val state ectx_item
    of_val to_val fill_item decomp_item expr_ord head_stepM.
Proof.
  split.
  - by apply ValU_measurable.
  - by apply to_val_meas.
  - by apply fill_item_def_measurable.
  - by apply decomp_item_meas.
  - by apply head_stepM_measurable.
  - by apply to_of_val.
  - by apply of_to_val.
  - by apply val_head_stuck.
  - by apply head_step_mass.
  - by apply fill_item_some.
  - by apply fill_item_inj.
  - by apply fill_item_no_val_inj.
  - by apply expr_ord_wf.
  - by apply decomp_expr_ord.
  - by apply decomp_fill_item.
  - by apply decomp_fill_item_2.
  - by apply head_step_ctx_val.
Qed.

End meas_lang.

(** Language *)

Canonical Structure meas_ectxi_lang := MeasEctxiLanguage meas_lang.head_stepM meas_lang.meas_lang_mixin.
Canonical Structure meas_ectx_lang := MeasEctxLanguageOfEctxi meas_ectxi_lang.
Canonical Structure meas_lang := MeasLanguageOfEctx meas_ectx_lang.

(* Prefer meas_lang names over ectx_language names. *)
Export meas_lang.
