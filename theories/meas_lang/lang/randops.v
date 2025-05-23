(* TODO cleanup imports *)
Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp Require Import functions.
From mathcomp.analysis Require Import measure lebesgue_measure probability.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp fintype.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.common Require Export locations.
From clutch.meas_lang Require Import ectxi_language ectx_language.
From Coq Require Export Reals.
From clutch.prob.monad Require Export giry.
From mathcomp Require Import classical_sets.
Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude types constructors shapes cover projections tapes state cfg.
Require Import ssrfun.

Require Import mathcomp.reals_stdlib.Rstruct.
Require Import mathcomp.reals.reals.
Set Warnings "hiding-delimiting-key".

Local Open Scope classical_set_scope.

Local Notation RR := ((R : realType) : measurableType _)%type.

(* FIXME: Move *)
Section unif.
  Local Open Scope ereal_scope.

  Axiom unif_base : giryM RR.
    (* broken, how do
        := @uniform_prob _ _ _ _.
        (@Num.Internals.ltr01 TR). *)

  Axiom unifN_base : <<discr Z>> -> giryM <<discr Z>>.

  Lemma unifN_base_meas_fun : measurable_fun setT unifN_base.
  Proof.
    into_gen_measurable.
    by intros ?.
  Qed. 
  Hint Resolve unifN_base_meas_fun : mf_fun.

End unif.

(* These changed to setT since all tape maps are finite*)
(* The set of states with a finite number of tapes *)
Definition AllocTape_eval_cov_ok : set (<<discr Z>> * state)%type :=
  setT.

(* The set of states with a finite number of utapes *)
Definition AllocUTape_eval_cov_ok : set state :=
  setT.

Definition RandT_eval_cov_noTape' (_ : <<discr Z>>) (ℓ  : <<discr loc>>) : set state :=
  (hp_eval ℓ \o tapes) @^-1` option_cov_None.

(* Location ℓ has no tape *)
Definition RandT_eval_cov_noTape : set (<<discr Z>> * <<discr loc>> * state)%type :=
  \bigcup_z \bigcup_l [set (z, l, σ) | σ in RandT_eval_cov_noTape' z l].

(* Location ℓ has a tape with the bound not equal to z *)
Definition RandT_eval_cov_boundMismatch' (z : <<discr Z>>) (ℓ  : <<discr loc>>) : set state :=
      ((hp_eval ℓ \o tapes) @^-1` option_cov_Some)
  `&` ((fst \o of_option (hp_eval ℓ \o tapes)) @^-1` [set t : <<discr nat>> | t ≠ Z.to_nat z]).

Definition RandT_eval_cov_boundMismatch : set (<<discr Z>> * <<discr loc>> * state)%type :=
  \bigcup_z \bigcup_l [set (z, l, σ) | σ in RandT_eval_cov_boundMismatch' z l].

(* Location ℓ has a tape with the right bound but the next space empty *)
Definition RandT_eval_cov_nextEmpty' (z : <<discr Z>>) (ℓ  : <<discr loc>>) : set state :=
      ((hp_eval ℓ \o tapes) @^-1` option_cov_Some)
  `&` ((fst \o of_option (hp_eval ℓ \o tapes)) @^-1` [set t : <<discr nat>> | t = Z.to_nat z])
  `&` ((sequence_evalC \o snd \o (of_option (hp_eval ℓ \o tapes))) @^-1` option_cov_None).

Definition RandT_eval_cov_nextEmpty : set (<<discr Z>> * <<discr loc>> * state)%type :=
  \bigcup_z \bigcup_l [set (z, l, σ) | σ in RandT_eval_cov_nextEmpty' z l].

Definition RandT_eval_cov_ok' (z : <<discr Z>>) (ℓ  : <<discr loc>>) : set state :=
      ((hp_eval ℓ \o tapes) @^-1` option_cov_Some)
  `&` ((fst \o of_option (hp_eval ℓ \o tapes)) @^-1` [set t : <<discr nat>> | t = Z.to_nat z])
  `&` ((sequence_evalC \o snd \o (of_option (hp_eval ℓ \o tapes))) @^-1` option_cov_Some).

Definition RandT_eval_cov_ok : set (<<discr Z>> * <<discr loc>> * state)%type :=
  \bigcup_z \bigcup_l [set (z, l, σ) | σ in RandT_eval_cov_ok' z l].

Definition URandT_eval_cov_noTape' (ℓ : <<discr loc>>) : set state:=
  (hp_eval ℓ \o utapes) @^-1` option_cov_None.

Definition URandT_eval_cov_noTape : set (<<discr loc>> * state)%type :=
  \bigcup_l [set (l, σ) | σ in URandT_eval_cov_noTape' l].

Definition URandT_eval_cov_nextEmpty' (ℓ : <<discr loc>>) : set state :=
      (hp_eval ℓ \o utapes) @^-1` option_cov_Some
  `&` ((sequence_evalC \o (of_option (hp_eval ℓ \o utapes))) @^-1` option_cov_None).

Definition URandT_eval_cov_nextEmpty : set (<<discr loc>> * state)%type :=
  \bigcup_l [set (l, σ) | σ in URandT_eval_cov_nextEmpty' l].

Definition URandT_eval_cov_ok' (ℓ : <<discr loc>>) : set state :=
      (hp_eval ℓ \o utapes) @^-1` option_cov_Some
  `&` ((sequence_evalC \o (of_option (hp_eval ℓ \o utapes))) @^-1` option_cov_Some).

Definition URandT_eval_cov_ok : set (<<discr loc>> * state)%type :=
  \bigcup_l [set (l, σ) | σ in URandT_eval_cov_ok' l].

Local Lemma rand_measurable_lemma ℓ : measurable ((hp_eval ℓ \o tapes) @^-1` option_cov_Some).
Proof.
  rewrite comp_preimage.
  rewrite <-setTI.
  apply: measurable_compT; first ms_solve.
  - rewrite -setXTT.
    apply: fst_setX_meas_fun; ms_solve.
  - apply: prod_of_state_meas_fun.
    ms_solve.
  - ms_solve.
  - apply: hp_sigma_algebra_singleton. apply: option_cov_Some_meas_set.
Qed.

Local Lemma rand_measurable_lemma' ℓ : measurable ((hp_eval ℓ \o tapes) @^-1` option_cov_None).
Proof.
  rewrite comp_preimage.
  rewrite <-setTI.
  apply: measurable_compT; first ms_solve.
  - rewrite -setXTT.
    apply: fst_setX_meas_fun; ms_solve.
  - apply: prod_of_state_meas_fun.
    ms_solve.
  - ms_solve.
  - apply: hp_sigma_algebra_singleton. apply: option_cov_None_meas_set.
Qed.

Local Lemma urand_measurable_lemma ℓ : measurable ((hp_eval ℓ \o utapes) @^-1` option_cov_Some).
Proof.
  rewrite comp_preimage.
  rewrite <-setTI.
  apply: measurable_compT; ms_solve.
  - apply: prod_of_state_meas_fun.
    ms_solve.
  - apply: hp_sigma_algebra_singleton. apply: option_cov_Some_meas_set.
Qed.

Local Lemma urand_measurable_lemma' ℓ : measurable ((hp_eval ℓ \o utapes) @^-1` option_cov_None).
Proof.
  rewrite comp_preimage.
  rewrite <-setTI.
  apply: measurable_compT; ms_solve.
  - apply: prod_of_state_meas_fun.
    ms_solve.
  - apply: hp_sigma_algebra_singleton. apply: option_cov_None_meas_set.
Qed. 

Lemma RandT_eval_cov_ok'_meas_set (z : <<discr Z>>) (ℓ : <<discr loc>>) :
  measurable (RandT_eval_cov_ok' z ℓ).
Proof.
  rewrite /RandT_eval_cov_ok'.
  rewrite -setIA setIIr.
  pose proof rand_measurable_lemma ℓ.
  apply: measurable_setI.
  - apply: apply_measurable_fun; ms_solve.
    apply measurable_compT; ms_solve.
    apply: of_option_meas_fun.
    apply: measurable_compT; ms_solve.
    + apply hp_eval_meas_fun.
    + apply tapes_meas_fun.
  - apply: apply_measurable_fun; ms_solve; last apply option_cov_Some_meas_set.
    apply measurable_compT; ms_solve.
    + rewrite -setXTT.
      apply: snd_setX_meas_fun; ms_solve.
      apply sequence_evalC_meas_fun.
    + apply of_option_meas_fun.
      apply: measurable_compT; ms_solve.
      * apply hp_eval_meas_fun.
      * apply tapes_meas_fun.
Qed. 

Lemma RandT_eval_cov_noTape'_meas_set (z : <<discr Z>>) (ℓ : <<discr loc>>) :
    measurable (RandT_eval_cov_noTape' z ℓ).
Proof.
  by pose proof rand_measurable_lemma' ℓ.
Qed. 

Lemma RandT_eval_cov_nextEmpty'_meas_set (z : <<discr Z>>) (ℓ : <<discr loc>>) :
  measurable (RandT_eval_cov_nextEmpty' z ℓ).
Proof.
  rewrite /RandT_eval_cov_nextEmpty'.
  rewrite -setIA setIIr.
  pose proof rand_measurable_lemma ℓ.
  pose proof rand_measurable_lemma' ℓ.
  apply: measurable_setI.
  - apply: apply_measurable_fun; ms_solve.
    apply measurable_compT; ms_solve.
    apply: of_option_meas_fun.
    apply: measurable_compT; ms_solve.
    + apply hp_eval_meas_fun.
    + apply tapes_meas_fun.
  - apply: apply_measurable_fun; ms_solve; last apply option_cov_None_meas_set.
    apply measurable_compT; ms_solve.
    + rewrite -setXTT.
      apply: snd_setX_meas_fun; ms_solve.
      apply sequence_evalC_meas_fun.
    + apply of_option_meas_fun.
      apply: measurable_compT; ms_solve.
      * apply hp_eval_meas_fun.
      * apply tapes_meas_fun.
Qed. 

Lemma RandT_eval_cov_boundMismatch'_meas_set (z : <<discr Z>>) (ℓ : <<discr loc>>) :
  measurable (RandT_eval_cov_boundMismatch' z ℓ).
Proof.
  rewrite /RandT_eval_cov_boundMismatch'.
  pose proof rand_measurable_lemma ℓ.
  apply: apply_measurable_fun; ms_solve.
  apply measurable_compT; ms_solve.
  apply: of_option_meas_fun.
  apply: measurable_compT; ms_solve.
  - apply hp_eval_meas_fun.
  - apply tapes_meas_fun.
Qed. 


Lemma URandT_eval_cov_ok'_meas_set (ℓ  : <<discr loc>>) :
  measurable (URandT_eval_cov_ok' ℓ).
Proof.
  rewrite /URandT_eval_cov_ok'.
  pose proof urand_measurable_lemma ℓ.
  apply: apply_measurable_fun; ms_solve; last apply option_cov_Some_meas_set.
  apply measurable_compT; ms_solve.
  - apply sequence_evalC_meas_fun.
  - apply of_option_meas_fun.
    apply: measurable_compT; ms_solve.
    * apply hp_eval_meas_fun.
    * apply utapes_meas_fun.
Qed. 

Lemma URandT_eval_cov_noTape'_meas_set (ℓ : <<discr loc>>) :
  measurable (URandT_eval_cov_noTape' ℓ).
Proof.
  by pose proof urand_measurable_lemma' ℓ.
Qed. 

Lemma URandT_eval_cov_nextEmpty'_meas_set (ℓ : <<discr loc>>) :
  measurable (URandT_eval_cov_nextEmpty' ℓ).
Proof. 
  rewrite /URandT_eval_cov_nextEmpty'.
  pose proof urand_measurable_lemma ℓ.
  pose proof urand_measurable_lemma' ℓ.
  apply: apply_measurable_fun; ms_solve; last apply option_cov_None_meas_set.
  apply measurable_compT; ms_solve.
  - apply sequence_evalC_meas_fun.
  - apply of_option_meas_fun.
    apply: measurable_compT; ms_solve.
    + apply hp_eval_meas_fun.
    + apply utapes_meas_fun.
Qed. 

Hint Resolve RandT_eval_cov_ok'_meas_set            : mf_set.
Hint Resolve RandT_eval_cov_noTape'_meas_set        : mf_set.
Hint Resolve RandT_eval_cov_nextEmpty'_meas_set     : mf_set.
Hint Resolve RandT_eval_cov_boundMismatch'_meas_set : mf_set.
Hint Resolve RandT_eval_cov_boundMismatch'_meas_set : mf_set.
Hint Resolve URandT_eval_cov_ok'_meas_set           : mf_set.
Hint Resolve URandT_eval_cov_noTape'_meas_set       : mf_set.
Hint Resolve URandT_eval_cov_nextEmpty'_meas_set    : mf_set.

Local Lemma int_loc_curry_meas_set (f : <<discr Z>> -> <<discr loc>> -> set state) :
  (∀ z ℓ, measurable (f z ℓ)) -> measurable (\bigcup_z \bigcup_l [set (z, l, σ) | σ in f z l]).
Proof.
  intros H.
  assert ((\bigcup_z \bigcup_l [set (z, l, σ) | σ in f z l]) =
          (\bigcup_z \bigcup_l [set ((ConstructiveExtra.Z_inj_nat_rev z), loc_enum l, σ) | σ in f (ConstructiveExtra.Z_inj_nat_rev z) (loc_enum l)])
         ) as ->.
  { rewrite eqEsubset; split; intros [[x y ]z ]; simpl.
    - intros [??[]]. simpl in *. destruct!/=.
      pose proof loc_enum_surj y as [y' <-].
      repeat eexists _; last first.
      + by erewrite ConstructiveExtra.Z_inj_nat_id.
      + by rewrite ConstructiveExtra.Z_inj_nat_id.
      + done.
      + done.
    - intros [??[]]. simpl in *. destruct!/=.
      by repeat eexists _.
  }
  apply bigcup_measurable.
  intros ??.
  apply bigcup_measurable.
  intros.
  assert (
      forall x y,
    [set (x, y, σ)
    | σ in f x y] =
    (set1 x) `*` (set1 y) `*` (f x y)
    ) as ->.
  { intros.
    rewrite eqEsubset; split; intros ?; simpl; intros; destruct!/=; naive_solver.
  }
  apply measurableX; last done.
  by apply measurableX.
Qed. 

Local Lemma loc_curry_meas_set (f : <<discr loc>> -> set state) :
  (∀ ℓ, measurable (f ℓ)) -> measurable (\bigcup_l [set (l, σ) | σ in f l]).
Proof.
  intros H.
  assert ((\bigcup_l [set (l, σ) | σ in f l]) =
          (\bigcup_l [set (loc_enum l, σ) | σ in f (loc_enum l)])
         ) as ->.
  { rewrite eqEsubset; split; intros [x y ]; simpl.
    - intros [??[]]. simpl in *. destruct!/=.
      pose proof loc_enum_surj x as [x' <-].
      eexists _; naive_solver.
    - intros [??[]]. simpl in *. destruct!/=.
      by repeat eexists _. }
  apply bigcup_measurable.
  intros.
  assert (
      forall x,
    [set (x, σ)
    | σ in f x ] =
    (set1 x) `*`  (f x )
    ) as ->.
  { intros.
    rewrite eqEsubset; split; intros ?; simpl; intros; destruct!/=; naive_solver.
  }
  by apply measurableX.
Qed. 
  


Lemma AllocTape_eval_cov_ok_meas_set : measurable AllocTape_eval_cov_ok.
Proof.
  by rewrite /AllocTape_eval_cov_ok.
Qed. 
Lemma AllocUTape_eval_cov_ok_meas_set : measurable AllocUTape_eval_cov_ok.
Proof. by rewrite /AllocUTape_eval_cov_ok.
Qed.

Lemma RandT_eval_cov_ok_meas_set : measurable RandT_eval_cov_ok.
Proof. by ms_unfold; apply int_loc_curry_meas_set; ms_done. Qed.

Lemma RandT_eval_cov_noTape_meas_set : measurable RandT_eval_cov_noTape.
Proof. by ms_unfold; apply int_loc_curry_meas_set; ms_done. Qed.

Lemma RandT_eval_cov_nextEmpty_meas_set : measurable RandT_eval_cov_nextEmpty.
Proof. by ms_unfold; apply int_loc_curry_meas_set; ms_done. Qed.

Lemma RandT_eval_cov_boundMismatch_meas_set : measurable RandT_eval_cov_boundMismatch.
Proof. by ms_unfold; apply int_loc_curry_meas_set; ms_done. Qed.

Lemma URandT_eval_cov_ok_meas_set : measurable URandT_eval_cov_ok.
Proof. by ms_unfold; apply loc_curry_meas_set; ms_done. Qed.

Lemma URandT_eval_cov_noTape_meas_set : measurable URandT_eval_cov_noTape.
Proof. by ms_unfold; apply loc_curry_meas_set; ms_done. Qed.

Lemma URandT_eval_cov_nextEmpty_meas_set : measurable URandT_eval_cov_nextEmpty.
Proof. by ms_unfold; apply loc_curry_meas_set; ms_done. Qed.

Hint Resolve AllocTape_eval_cov_ok_meas_set         : mf_set.
Hint Resolve AllocUTape_eval_cov_ok_meas_set        : mf_set.
Hint Resolve RandT_eval_cov_ok_meas_set             : mf_set.
Hint Resolve RandT_eval_cov_noTape_meas_set         : mf_set.
Hint Resolve RandT_eval_cov_nextEmpty_meas_set      : mf_set.
Hint Resolve RandT_eval_cov_boundMismatch_meas_set  : mf_set.
Hint Resolve URandT_eval_cov_ok_meas_set            : mf_set.
Hint Resolve URandT_eval_cov_noTape_meas_set        : mf_set.
Hint Resolve URandT_eval_cov_nextEmpty_meas_set     : mf_set.

(* FIXME: Move *)
Definition Z_to_nat' : <<discr Z>> -> <<discr nat>> := Z.to_nat.

Definition AllocTape_eval_ok : (<<discr Z>> * state)%type -> giryM cfg :=
  gRet \o (ValU \o LitVU \o LitLblU \o fresh \o tapes \o snd
          △ state_of_prod \o
            ( heap \o snd
            △ hp_updateC \o (fresh \o tapes \o snd △ (Some \o (Z_to_nat' \o fst △ cst emptyTape) △ tapes \o snd))
            △ utapes \o snd)).

Definition AllocUTape_eval_ok : state -> giryM cfg :=
  gRet \o (ValU \o LitVU \o LitLblU \o fresh \o utapes
          △ state_of_prod \o
             ( heap
             △ tapes
             △ hp_updateC \o (fresh \o utapes △ (cst (Some emptyTape) △ utapes)))).

Local Notation S' := (S : <<discr nat>> -> <<discr nat>>).

Definition RandT_eval_ok : (<<discr Z>> * <<discr loc>> * state)%type -> giryM cfg :=
  gRet \o (ValU \o LitVU \o LitIntU \o of_option sequence_evalC \o snd \o of_option hp_evalC \o (snd \o fst △ tapes \o snd)
          △ state_of_prod \o
             ( heap \o snd
             △ (hp_updateC \o
                  (    snd \o fst
                  △ ( Some \o (fst △ (S' \o fst \o snd △ snd \o snd)) \o of_option hp_evalC \o (snd \o fst △ tapes \o snd)
                  △   tapes \o snd)))
             △ utapes \o snd)).

Definition RandT_eval_nextEmpty : (<<discr Z>> * <<discr loc>> * state)%type -> giryM cfg :=
  gMap' (  ValU \o LitVU \o LitIntU \o fst
        △ state_of_prod \o
           (  heap \o snd \o snd
           △ hp_updateC \o
               (    snd \o fst \o snd
               △ ( Some \o (    fst \o of_option hp_evalC \o (snd \o fst \o snd △ tapes \o snd \o snd)
                            △ ( S' \o fst \o snd \o of_option hp_evalC \o (snd \o fst \o snd △ tapes \o snd \o snd)
                            △   sequence_updateC \o
                                  (     fst \o snd \o of_option hp_evalC \o (snd \o fst \o snd △ tapes \o snd \o snd)
                                  △ (  Some \o fst
                                  △    snd \o snd \o of_option hp_evalC \o (snd \o fst \o snd △ tapes \o snd \o snd)))))
               △   tapes \o snd \o snd))
           △ utapes \o snd \o snd )) \o
  gProd \o (unifN_base \o fst \o fst △ gRet).

Definition RandT_eval_boundMismatch : (<<discr Z>> * <<discr loc>> * state)%type -> giryM cfg :=
  gMap' (ValU \o LitVU \o LitIntU \o fst △ snd \o snd) \o
  gProd \o (unifN_base \o fst \o fst △ gRet).

Definition URandT_eval_ok : (<<discr loc>> * state)%type -> giryM cfg :=
  gRet \o (ValU \o LitVU \o LitRealU \o of_option sequence_evalC \o of_option hp_evalC \o (fst △ utapes \o snd)
          △ state_of_prod \o
            (  heap \o snd
            △ tapes \o snd
            △ hp_updateC \o
                (    fst
                △ ( Some \o (S' \o fst △ snd) \o of_option hp_evalC \o (fst △ utapes \o snd)
                △   utapes \o snd)))).

 Definition URandT_eval_nextEmpty : (<<discr loc>> * state)%type -> giryM cfg :=
  gMap' ( ValU \o LitVU \o LitRealU \o fst
        △ state_of_prod \o
           (  heap \o snd \o snd
           △ tapes \o snd \o snd
           △ hp_updateC \o
              (    fst \o snd
              △ ( Some \o ( S' \o fst \o of_option hp_evalC \o (fst \o snd △ utapes \o snd \o snd)
                          △ sequence_updateC \o
                            (    fst \o of_option hp_evalC \o (fst \o snd △ utapes \o snd \o snd)
                            △ ( Some \o fst
                            △   snd \o of_option hp_evalC \o (fst \o snd △ utapes \o snd \o snd))))
              △   utapes \o snd \o snd)))) \o
    gProd \o (cst unif_base △ gRet).

Lemma AllocTape_eval_ok_meas_fun         : measurable_fun AllocTape_eval_cov_ok AllocTape_eval_ok.
Proof.
  rewrite /AllocTape_eval_cov_ok/AllocTape_eval_ok.
  apply: measurable_compT; ms_solve; first apply: gRet_meas_fun.
  mf_prod.
  - apply measurable_compT; first ms_solve; last by apply: measurable_snd_restriction.
    apply measurable_compT; first ms_solve; last by apply: tapes_meas_fun.
    apply measurable_compT; first ms_solve; last by apply: fresh_meas_fun.
    apply measurable_compT; first ms_solve; last by apply: LitLblU_meas_fun.
    apply measurable_compT; first ms_solve; last by apply: LitVU_meas_fun.
    apply ValU_meas_fun.
  - apply measurable_compT; first ms_solve; first by apply: state_of_prod_meas_fun.
    apply: (measurable_fun_prod'); first ms_solve; last first.
    { rewrite -setXTT.
      apply: snd_setX_meas_fun; ms_solve.
      apply utapes_meas_fun.
    }
    mf_prod.
    { rewrite -setXTT.
      apply: snd_setX_meas_fun; ms_solve.
      apply heap_meas_fun. }
    apply measurable_compT; first ms_solve; first apply hp_updateC_meas_fun.
    mf_prod.
    { rewrite -setXTT.
      apply: snd_setX_meas_fun; ms_solve.
      apply: measurable_compT; first ms_solve.
      - apply fresh_meas_fun.
      - apply tapes_meas_fun.
    }
    mf_prod; last first.
    { rewrite -setXTT.
      apply: snd_setX_meas_fun; ms_solve.
      apply tapes_meas_fun.
    }
    apply: measurable_compT; first done; first apply: Some_meas_fun.
    mf_prod.
    rewrite -setXTT.
    apply: fst_setX_meas_fun; ms_solve.
Qed. 
Lemma AllocUTape_eval_ok_meas_fun        : measurable_fun AllocUTape_eval_cov_ok AllocUTape_eval_ok.
Proof.
  rewrite /AllocUTape_eval_cov_ok/AllocUTape_eval_ok.
  apply: measurable_compT; ms_solve; first apply: gRet_meas_fun.
  mf_prod.
  - apply measurable_compT; first ms_solve; last by apply: utapes_meas_fun.
    apply measurable_compT; first ms_solve; last by apply: fresh_meas_fun.
    apply measurable_compT; first ms_solve; last by apply: LitLblU_meas_fun.
    apply measurable_compT; first ms_solve; last by apply: LitVU_meas_fun.
    apply ValU_meas_fun.
  - apply measurable_compT; first ms_solve; first by apply: state_of_prod_meas_fun.
    apply: (measurable_fun_prod'); first ms_solve.
    { mf_prod.
      - apply heap_meas_fun.
      - apply tapes_meas_fun.
    }
    apply measurable_compT; first ms_solve; first apply hp_updateC_meas_fun.
    mf_prod.
    { apply: measurable_compT; first ms_solve.
      - apply fresh_meas_fun.
      - apply utapes_meas_fun.
    }
    mf_prod.
    apply: utapes_meas_fun.
Qed. 
Lemma RandT_eval_ok_meas_fun             : measurable_fun RandT_eval_cov_ok RandT_eval_ok.
Proof.
  rewrite /RandT_eval_cov_ok/RandT_eval_ok.
  apply: measurable_compT; first ms_solve; first apply: gRet_meas_fun.
  mf_prod.
  - apply: measurable_comp. 
Admitted.
Lemma RandT_eval_nextEmpty_meas_fun      : measurable_fun RandT_eval_cov_nextEmpty RandT_eval_nextEmpty. Admitted.
Lemma RandT_eval_boundMismatch_meas_fun  : measurable_fun RandT_eval_cov_boundMismatch RandT_eval_boundMismatch. Admitted.
Lemma URandT_eval_ok_meas_fun            : measurable_fun URandT_eval_cov_ok URandT_eval_ok. Admitted.
Lemma URandT_eval_nextEmpty_meas_fun     : measurable_fun URandT_eval_cov_nextEmpty URandT_eval_nextEmpty. Admitted.

Hint Resolve AllocTape_eval_ok_meas_fun         : mf_fun.
Hint Resolve AllocUTape_eval_ok_meas_fun        : mf_fun.
Hint Resolve RandT_eval_ok_meas_fun             : mf_fun.
Hint Resolve RandT_eval_nextEmpty_meas_fun      : mf_fun.
Hint Resolve RandT_eval_boundMismatch_meas_fun  : mf_fun.
Hint Resolve URandT_eval_ok_meas_fun            : mf_fun.
Hint Resolve URandT_eval_nextEmpty_meas_fun     : mf_fun.

Definition AllocTape_eval  : (<<discr Z>> * state)%type -> giryM cfg :=
  if_in AllocTape_eval_cov_ok AllocTape_eval_ok (cst gZero).

Definition AllocUTape_eval : state -> giryM cfg :=
  if_in AllocUTape_eval_cov_ok AllocUTape_eval_ok (cst gZero).

Definition Rand_eval : (<<discr Z>> * state)%type -> giryM cfg :=
  gProd \o (gMap' (ValU \o LitVU \o LitIntU) \o unifN_base \o fst △ gRet \o snd).

Definition URand_eval : state -> giryM cfg :=
  gProd \o (cst (gMap' (ValU \o LitVU \o LitRealU) unif_base) △ gRet).

Definition RandT_eval : (<<discr Z>> * <<discr loc>> * state)%type -> giryM cfg :=
  if_in RandT_eval_cov_noTape (cst gZero) $                      (*  No tape *)
  if_in RandT_eval_cov_boundMismatch RandT_eval_boundMismatch $  (*  Yes tape but mismatch bound *)
  if_in RandT_eval_cov_nextEmpty RandT_eval_nextEmpty $          (*  Yes tape, bounds match, but empty *)
  RandT_eval_ok.                                                 (*  Yes tape, bounds match, next nonempty *)

Definition URandT_eval : (<<discr loc>> * state)%type -> giryM cfg :=
  if_in URandT_eval_cov_noTape (cst gZero) $                      (*  No tape *)
  if_in URandT_eval_cov_nextEmpty URandT_eval_nextEmpty $         (*  Yes tape, but empty *)
  URandT_eval_ok.                                                 (*  Yes tape, next nonempty *)

Lemma AllocTape_eval_meas_fun  : measurable_fun setT AllocTape_eval.
Proof.
  mf_unfold_fun.
  apply: if_in_meas_fun.
  - ms_solve. 
  - ms_solve.
  - rewrite setIT. apply: AllocTape_eval_ok_meas_fun.
  - apply measurable_cst.
Qed. 
Lemma AllocUTape_eval_meas_fun : measurable_fun setT AllocUTape_eval.
Proof.
  mf_unfold_fun.
  apply: if_in_meas_fun.
  - ms_solve. 
  - ms_solve.
  - rewrite setIT. apply: AllocUTape_eval_ok_meas_fun.
  - apply measurable_cst.
Qed. 
Lemma Rand_eval_meas_fun       : measurable_fun setT Rand_eval. 
Proof.
  mf_unfold_fun.
  apply: measurable_compT; ms_solve.
  { apply: gProd_meas_fun. }
  mf_prod; last first.
  { rewrite -setXTT.
    apply: snd_setX_meas_fun; ms_solve.
    apply gRet_meas_fun.
  }
  rewrite -setXTT.
  apply: fst_setX_meas_fun; ms_solve.
  Qed. 
Lemma RandT_eval_meas_fun      : measurable_fun setT RandT_eval.
Proof. 
  mf_unfold_fun.
  apply: if_in_meas_fun.
  - ms_solve. 
  - ms_solve.
  - apply measurable_cst.
  - apply: if_in_meas_fun; ms_solve.
    + rewrite setIT.
      rewrite setIidl; first apply RandT_eval_boundMismatch_meas_fun.
      intros [[]].
      rewrite /RandT_eval_cov_boundMismatch/RandT_eval_cov_noTape.
      rewrite /RandT_eval_cov_boundMismatch'/RandT_eval_cov_noTape'.
      rewrite /bigcup/option_cov_None/option_cov_Some/=. intros ??. destruct!/=.
    + apply: if_in_meas_fun; ms_solve.
      * rewrite setIT.
        rewrite setIidl; first apply RandT_eval_nextEmpty_meas_fun.
        rewrite /RandT_eval_cov_nextEmpty/RandT_eval_cov_boundMismatch/RandT_eval_cov_noTape.
        rewrite /RandT_eval_cov_nextEmpty'/RandT_eval_cov_boundMismatch'/RandT_eval_cov_noTape'.
        rewrite /bigcup/option_cov_None/option_cov_Some/=.
        intros [[]].
        simpl. intros. split; intros ?; destruct!/=.
      * rewrite setIT.
        apply: measurable_funS; last apply RandT_eval_ok_meas_fun; ms_solve.
        rewrite -!setCU.
        rewrite subsets_disjoint.
        rewrite -!setCU.
        rewrite -setCT.
        f_equal.
        rewrite eqEsubset; split; intros [[x y ]z ]; first done; simpl.
        intros _.
        rewrite /RandT_eval_cov_nextEmpty/RandT_eval_cov_boundMismatch/RandT_eval_cov_noTape/RandT_eval_cov_ok.
        rewrite /RandT_eval_cov_nextEmpty'/RandT_eval_cov_boundMismatch'/RandT_eval_cov_noTape'/RandT_eval_cov_ok'. 
        rewrite /bigcup/=.
        rewrite /option_cov_Some/option_cov_None/=. simpl in *.
        destruct (hp_eval y (tapes z)) eqn:Heqn1; last naive_solver.
        destruct (decide ((of_option (hp_eval y \o tapes) z).1 = Z.to_nat x) ) as [e|] eqn:Heqn2; last first.
        { left. right. left.
          repeat eexists _; try done.
          rewrite Heqn1. naive_solver.
        }
        destruct ((sequence_evalC (of_option (hp_eval y \o tapes) z).2)) eqn: Heqn3.
        -- right. repeat eexists _; try done.
           rewrite !Heqn1. rewrite e. rewrite Heqn3. naive_solver.
        -- repeat left.
           repeat eexists _; try done.
           rewrite Heqn1 e Heqn3. naive_solver.
Qed. 
Lemma URand_eval_meas_fun      : measurable_fun setT URand_eval.
Proof.
  mf_unfold_fun.
  apply: measurable_compT; ms_solve.
  { apply: gProd_meas_fun. }
  mf_prod.
Qed. 
Lemma URandT_eval_meas_fun     : measurable_fun setT URandT_eval.
Proof.
  rewrite /URandT_eval.
  apply: if_in_meas_fun; ms_solve.
  rewrite setIT.
  apply: if_in_meas_fun; ms_solve.
  { rewrite setIidl; first apply URandT_eval_nextEmpty_meas_fun.
    rewrite /URandT_eval_cov_nextEmpty/URandT_eval_cov_noTape.
    rewrite /URandT_eval_cov_nextEmpty'/URandT_eval_cov_noTape'.
    rewrite /option_cov_None/option_cov_Some/bigcup/=.
    intros [].
    simpl.
    intros ??. destruct!/=.
  }
  apply: measurable_funS; last apply URandT_eval_ok_meas_fun; ms_solve.
  rewrite -!setCU.
  rewrite subsets_disjoint.
  rewrite -!setCU.
  rewrite -setCT.
  f_equal.
  rewrite eqEsubset; split; intros [x y ]; first done; simpl.
  intros _.
  rewrite /URandT_eval_cov_nextEmpty/URandT_eval_cov_noTape/URandT_eval_cov_ok.
  rewrite /URandT_eval_cov_nextEmpty'/URandT_eval_cov_noTape'/URandT_eval_cov_ok'.
  rewrite /bigcup/=.
  rewrite /option_cov_Some/option_cov_None/=. simpl in *.
  destruct (hp_eval x (utapes y)) eqn:Heqn1; last naive_solver.
  destruct ((sequence_evalC (of_option (hp_eval x \o utapes) y))) eqn: Heqn3.
  - right. repeat eexists _; try done. 
    rewrite !Heqn1. rewrite Heqn3. naive_solver.
  - repeat left.
    repeat eexists _; try done.
    rewrite Heqn1 Heqn3. naive_solver.
Qed. 
Hint Resolve AllocTape_eval_meas_fun  : mf_fun.
Hint Resolve AllocUTape_eval_meas_fun : mf_fun.
Hint Resolve Rand_eval_meas_fun       : mf_fun.
Hint Resolve RandT_eval_meas_fun      : mf_fun.
Hint Resolve URand_eval_meas_fun      : mf_fun.
Hint Resolve URandT_eval_meas_fun     : mf_fun.

