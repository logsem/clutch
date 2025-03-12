Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Export Reals.
From stdpp Require Import binders.
From mathcomp Require Import eqtype choice boolp classical_sets.
From mathcomp.analysis Require Import measure.
From mathcomp.analysis Require Export reals Rstruct.
From clutch.common Require Import locations.
From clutch.prob.monad Require Import giry.
From clutch.prob.monad Require Export prelude.
From Coq Require Import ssrfun.
Set Warnings "hiding-delimiting-key".

(* Instances for Z *)
HB.instance Definition _ := gen_eqMixin Z.
HB.instance Definition _ := gen_choiceMixin Z.
HB.instance Definition _ := isPointed.Build Z inhabitant.
HB.saturate Z.

(* Instances for binder *)
HB.instance Definition _ := gen_eqMixin binder.
HB.instance Definition _ := gen_choiceMixin binder.
HB.instance Definition _ := isPointed.Build binder inhabitant.
HB.saturate binder.

(* Instances for loc *)
HB.instance Definition _ := gen_eqMixin loc.
HB.instance Definition _ := gen_choiceMixin loc.
HB.instance Definition _ := isPointed.Build loc inhabitant.
HB.saturate loc.

Hint Resolve gRet_meas_fun : measlang.

Local Open Scope classical_set_scope.

Definition loc_enum : nat -> <<discr loc>>. Admitted.
Lemma loc_enum_surj : forall l, exists n, loc_enum n = l.
Proof. Admitted.

Create HintDb ml_fun.
Create HintDb ml_set.

Hint Resolve gRet_meas_fun : mf_fun.

Ltac ms_done := by eauto with mf_set.

Ltac mf_done := by eauto with mf_fun.

Ltac ms_unfold := match goal with | |- (measurable ?X) => unfold X end.

Ltac ms_prod := match goal with | |- (measurable (_ `*` _)) => apply measurableX end.

Lemma apply_measurable_fun {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
  (D : set T1) (f : T1 -> T2) (S : set T2) :
      measurable_fun D f -> measurable D -> measurable S -> measurable (D `&` f @^-1` S).
Proof. intros H1 H2 H3. apply H1; done. Qed.

Ltac ms_fun :=
  match goal with
  | |- (measurable (?Dom `&` ?Fun @^-1` ?S)) =>
        apply (apply_measurable_fun Dom Fun S); [ try by mf_done | try by ms_done | ]
  end.

Ltac ms_solve :=
  repeat match goal with
         (* First try searching existing database of measurable sets *)
         | |- _ => by ms_done
         (* Try applying basic measurability lemmas *)
         | |- (measurable (_ `*` _)) => ms_prod
         | |- (measurable (_ `&` _ @^-1` _)) => ms_fun
         end.



Ltac mf_unfold_fun := match goal with | |- (measurable_fun _ ?X) => unfold X end.

Ltac mf_unfold_dom := match goal with | |- (measurable_fun ?X _) => unfold X end.

Ltac mf_reassoc :=
  repeat match goal with
         | |- context[(?f \o ?g) \o ?h] => rewrite <- (ssrfun.compA f g h)
         end.

Ltac mf_cmp_fst :=
  match goal with
  | |- (measurable_fun (?S1 `*` ?S2) (?f \o fst)) => eapply @fst_setX_meas_fun; [ try by ms_done | try by ms_solve | ]
  | |- (measurable_fun setT (_ \o fst)) => fail
  end.

Ltac mf_cmp_snd :=
  match goal with
  | |- (measurable_fun (?S1 `*` ?S2) (?f \o snd)) => eapply @snd_setX_meas_fun; [ try by ms_done | try by ms_solve | ]
  | |- (measurable_fun setT (_ \o snd)) => fail
  end.

Ltac mf_prod :=
  match goal with
  | |- (measurable_fun ?S (?f △ ?g)) => eapply (@measurable_fun_prod' _ _ _ _ _ _ f g S); [ try by ms_solve | try by mf_done | try by mf_done ]
  end.

Ltac mf_cmp_tree :=
  match goal with
  | |- (measurable_fun (?fDom `&` ?f @^-1` ?S) (_ \o ?f)) =>
        eapply (measurable_comp (F:=S));
        [ try by ms_done
        | try by eauto with projection_subs
        |
        | rewrite <- (setIid fDom), <- (setIA fDom);
          apply measurable_fun_setI1;
          try (by ms_done || by ms_solve || by mf_done)
        ]
  | |- (measurable_fun ?S (_ \o ?f)) =>
        eapply (measurable_comp (F:=setT));
        [ try by ms_done
        | try by apply subsetT
        |
        | try by mf_done ]
  end.
