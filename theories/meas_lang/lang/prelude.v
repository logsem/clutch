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

Create HintDb measlang.

(* Fix giryM to be the giry type with stdlib-valued real numbers *)
Notation giryM := (giryM (R := R)).

Global Instance classical_eq_dec {T : Type} : EqDecision T.
Proof. intros ??; apply ClassicalEpsilon.excluded_middle_informative. Defined.

(* Instances for Z *)
HB.instance Definition _ := gen_eqMixin Z.
HB.instance Definition _ := gen_choiceMixin Z.
HB.instance Definition _ := isPointed.Build Z inhabitant.

(* Instances for binder *)
HB.instance Definition _ := gen_eqMixin binder.
HB.instance Definition _ := gen_choiceMixin binder.
HB.instance Definition _ := isPointed.Build binder inhabitant.

(* Instances for loc *)
HB.instance Definition _ := gen_eqMixin loc.
HB.instance Definition _ := gen_choiceMixin loc.
HB.instance Definition _ := isPointed.Build loc inhabitant.

Local Open Scope classical_set_scope.

Section subspaces.
  (** Mathcomp needs measurable spaces to be pointed
      This means that we could only construct subset spaces for nonempty subsets
      And this seems to confuse HB.

      For now, it's easier to define is_sub_measurable as an unbundled type not
      in the hierarchy, and re-prove the results we need about it. Many of them
      can be copy-pasted.

      The reason we want subspace measurability is to define the measurability of
      projection functions and constructors. This allows us to prove that head_step
      is measurable (in the HB sense). If we need these functions to be HB measurable
      elsewhere, we may need to figure out how to get proper subset spaces in
      the hierarchy.
   *)

  (*
  (* A set S is measurable in the space T1|_E *)
  Definition sub_measurable {d1} {T1 : measurableType d1} (E S : set T1) : Prop :=
    [set (E `&` m) | m in (d1.-measurable : set (set T1))] S.

  Lemma sub_measurable0 {d1} {T1 : measurableType d1} (E : set T1) : sub_measurable E set0.
  Proof. Admitted.

  Lemma sub_measurableC {d1} {T1 : measurableType d1} (E S : set T1) :
    sub_measurable E S -> sub_measurable E (E `\` S).
  Proof. Admitted.

  Lemma bigcup_sub_measurableC {d1} {T : measurableType d1} (E: set T) (F : sequences.sequence (set T)) (P : set nat) :
    (∀ k : nat, P k → sub_measurable E (F k)) → sub_measurable E (\bigcup_(i in P) F i).
  Proof. Admitted.
   *)


  (** If a set is sub_measurable, and a function out of it is a sub-measurable function,
      the restriction to the set is mathcomp-measurable *)
  Lemma mathcomp_restriction_is_measurable {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
    (E : set T1) (HE : d1.-measurable E) (f : T1 -> T2) :
    measurable_fun E f -> measurable_fun setT (f \_ E).
  Proof.
    move=> Hf.
    have HT : d1.-measurable (setT : set T1) by eapply @measurableT.
    apply (measurable_restrict f HE HT).
    by rewrite setTI.
  Qed.

  Lemma mathcomp_restriction_measurable_of_measurable {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
    (E : set T1) (HE : d1.-measurable E) (f : T1 -> T2) :
    measurable_fun setT (f \_ E) ->
    measurable_fun E f.
  Proof.
    move=> Hf.
    have HT : d1.-measurable (setT : set T1) by eapply @measurableT.
    rewrite <- (@setTI _ E).
    by apply <- (measurable_restrict f HE HT).
  Qed.

  Lemma mathcomp_measurable_fun_ext {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
     (E : set T1) (HE : d1.-measurable E) (f g : T1 -> T2) :
     measurable_fun E f -> (∀ x, E x -> f x = g x) -> measurable_fun E g.
  Proof.
    intros H1 H2.
    apply (mathcomp_restriction_measurable_of_measurable E HE).
    apply (mathcomp_restriction_is_measurable E HE) in H1.
    suffices HS : (f \_ E = g \_ E) by rewrite <-HS.
    unfold restrict.
    apply functional_extensionality.
    intro x.
    remember (x \in E) as D.
    destruct D; [|done].
    apply H2.
    symmetry in HeqD.
    have Z : is_true (x \in E) by auto.
    by rewrite in_setE in Z.
  Qed.


  (* TODO: Delete me (but not yet)
    intro H.
    unfold measurable_fun.
    intros ? S SMeas.
    rewrite setTI.
    unfold restrict.
    unfold preimage.
    unfold measurable_fun in H.
    have H' := H HE S SMeas; clear H.
    destruct (ExcludedMiddle (S point)).
    - (* point is in S *)
      suffices X : (~` E) `|` (E `&` f @^-1` S) = [set t | S (if t \in E then f t else point)].
      { have H'' := measurableU _ _ (measurableC HE) H'.
        rewrite X in H''.
        by apply H''. }
      apply functional_extensionality.
      intro t.
      simpl.
      apply propext.
      split.
      + intros [ Ht | [Ht Hs] ].
        * by rewrite (memNset Ht).
        * by rewrite (mem_set Ht).
      + intros HS.
        destruct (ExcludedMiddle (E t)).
        * right.
          rewrite (mem_set H1) in HS.
          split; done.
        * by left.
    - (* point is not in S, preimage is .... *)
      suffices X : (E `&` f @^-1` S) = [set t | S (if t \in E then f t else point)].
      { by rewrite X in H'; apply H'. }
      apply functional_extensionality.
      intro t.
      simpl.
      apply propext.
      split.
      + intros [Ht HS].
        by rewrite (mem_set Ht).
      + intros HS.
        destruct (ExcludedMiddle (E t)).
        * rewrite (mem_set H1) in HS.
          split; done.
        * exfalso.
          apply H.
          by rewrite (memNset H1) in HS.
    *)


  Lemma mathcomp_restriction_setT {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
    (E : set T1) (f : T1 -> T2) :
    measurable_fun setT (f \_ E) -> measurable_fun E (f \_ E).
  Proof.
    move=> H ? Y ?.
    apply measurableI; [done|].
    unfold measurable_fun in H.
    suffices W : d1.-measurable ([set: T1] `&` f \_ E @^-1` Y) by rewrite setTI in W.
    apply H; [|done].
    by eapply @measurableT.
  Qed.

  Lemma mathcomp_measurable_fun_restiction_setT {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
    (E : set T1) (HE : measurable E) (f : T1 -> T2) :
    measurable_fun setT f -> measurable_fun E f.
  Proof.
    move=> H ???.
    apply measurableI; [done|].
    rewrite <- (setTI (_ @^-1` _) ).
    by apply H.
  Qed.



End subspaces.



(* FIXME: move *)
Definition image3 {TA TB TC rT} (A : set TA) (B : set TB) (C : set TC) (f : TA -> TB -> TC -> rT) :=
  [set z | exists2 x, A x & exists2 y, B y & exists2 w, C w & f x y w = z].
Arguments image3 _ _ _ _ _ _ _ _ /.


Lemma eq_measurable {d} {T : measurableType d} (X Y : set T) :
  d.-measurable X -> Y = X -> d.-measurable Y.
Proof. by move=>?->. Qed.

(** A function into a generated measurableType is a measurable function
    when the preimages of the generators are measurable.  *)
Ltac into_gen_measurable := eapply measurability; [by eauto|].

Definition fin_to_nat {N : nat} (x : 'I_(S N)) : Z.
Admitted.

(** Strict generalization of the version in mathcomp *)
Lemma prod_measurable_funP' {d d1 d2} {T : measurableType d} {T1 : measurableType d1} {T2 : measurableType d2}
  (h : T -> T1 * T2) (S : set T) (HS : measurable S) :
  measurable_fun S h <-> measurable_fun S (ssrfun.comp fst h) /\ measurable_fun S (ssrfun.comp snd h).
Proof.
  (* Proof: Conjugate by the restriction lemma, and apply the setT version *)
  split.
  - intro H.
    apply (mathcomp_restriction_is_measurable S HS h) in H.
    apply (prod_measurable_funP (h \_ S)) in H.
    destruct H as [H1 H2].
    by split; apply (mathcomp_restriction_measurable_of_measurable S HS); rewrite restrict_comp.
  - intros [H1 H2].
    eapply (mathcomp_restriction_is_measurable S HS _) in H1.
    eapply (mathcomp_restriction_is_measurable S HS _) in H2.
    rewrite restrict_comp in H1; [|done].
    rewrite restrict_comp in H2; [|done].
    have X := iffRL (prod_measurable_funP (h \_ S)) (conj H1 H2).
    apply (mathcomp_restriction_measurable_of_measurable S HS _ X).
Qed.

(** Strict generalization of the version in mathcomp *)
Lemma measurable_fun_prod' {d d1 d2} {T : measurableType d} {T1 : measurableType d1} {T2 : measurableType d2}
  (f : T -> T1) (g : T -> T2) (S : set T) (HS : measurable S):
  measurable_fun S f -> measurable_fun S g ->
  measurable_fun S (fun x => (f x, g x)).
Proof. by move=>??; exact/prod_measurable_funP'. Qed.

Notation mProd f g := (fun x => (f x, g x)).

Lemma measurable_compT {d1 d2 d3} {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}
       (f : T2 → T3) (E : set T1) (g : T1 → T2)
       (HE : d1.-measurable E) (Hf : measurable_fun setT f)
       (Hg : measurable_fun E g) : measurable_fun E (ssrfun.comp f g).
Proof.
  have MT : measurable (setT : set T2) by eauto.
  by eapply (measurable_comp MT _ Hf Hg).
  Unshelve.
  by rewrite /subset//=.
Qed.

Lemma measurable_compT' {d1 d2 d3} {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}
       (f : T2 → T3) (E : set T1) (g : T1 → T2)
       (HE : d1.-measurable E) (Hf : measurable_fun setT f)
       (Hg : measurable_fun E g) : measurable_fun E (ssrfun.comp f g).
Proof.
  have MT : measurable (setT : set T2) by eauto.
  by eapply (measurable_comp MT _ Hf Hg).
  Unshelve.
  by rewrite /subset//=.
Qed.

Lemma measurable_fun_setI1 {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
   (f : T1 -> T2) (S1 S2 : set T1) (MS1 : measurable S1) (MS2 : measurable S2) (MF : measurable_fun S1 f) :
   measurable_fun (S1 `&` S2) f.
Proof.
  move=>???.
  rewrite (setIC S1 S2); rewrite <-setIA.
  apply measurableI; [done|].
  apply MF; done.
Qed.


Lemma measurable_fun_setI2 {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
   (f : T1 -> T2) (S1 S2 : set T1) (MS1 : measurable S1) (MS2 : measurable S2) (MF : measurable_fun S2 f) :
   measurable_fun (S1 `&` S2) f.
Proof. by rewrite (setIC S1 S2); apply measurable_fun_setI1. Qed.


Lemma measurable_fst_restriction {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} {S : set (T1 * T2)%type} (H : measurable S) :
  measurable_fun S fst.
Proof.
  eapply @mathcomp_measurable_fun_restiction_setT.
  - done.
  - by apply measurable_fst.
Qed.

Lemma measurable_snd_restriction {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} {S : set (T1 * T2)%type} (H : measurable S) :
  measurable_fun S snd.
Proof.
  eapply @mathcomp_measurable_fun_restiction_setT.
  - done.
  - by apply measurable_snd.
Qed.


(* Extremely annoyingly, I need to redefine these so that they don't take measurable_maps as arguments.
   This is because I'll only be able to give them a measurable_fun out of a particular set.
 *)
Definition giryM_map_def' {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
  (m : giryM T1) (f : T1 -> T2) : giryM T2. Admitted.

Definition giryM_bind' {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
    (f : T1 -> (giryM T2)) : (giryM T1) -> (giryM T2)
  := fun m => giryM_join_def' (giryM_map_def' m f).

Definition bind_set {d1} {T1 : measurableType d1} (S : set T1) : set (giryM T1) :=
  [set giryM_ret _ x | x in S].

Lemma bind_set_meas d1 {T1 : measurableType d1} (S : set T1) (HS : d1.-measurable S) : measurable (bind_set S).
Proof. Admitted.

Definition giryM_bind'_measurable {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
      (S : set T1) (HS : d1.-measurable S) (f : T1 -> giryM T2) (Hf : measurable_fun S f) :
      measurable_fun (bind_set S) (giryM_bind' f).
Proof. Admitted.
