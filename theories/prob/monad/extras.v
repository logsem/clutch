(** Misc shared results *)
From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import normedtype.
From mathcomp.analysis Require Import reals ereal signed (* topology *) normedtype esum numfun measure lebesgue_measure lebesgue_integral.
From HB Require Import structures.

From clutch.prob.monad Require Export types.
From clutch.prelude Require Import classical.

Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type".

Section Lib.
  Local Open Scope classical_set_scope.
  Lemma measurable_if_pushfowrard_subset {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : T1 -> T2) :
        (d2.-measurable  `<=` [set s : set T2 | d1.-measurable ( f@^-1` s )]) -> (measurable_fun setT f). Proof.
    intro HS.
    rewrite /measurable_fun.
    rewrite /subset in HS.
    intros X Y HY.
    specialize (HS Y HY).
    simpl in HS.
    rewrite setTI.
    apply HS.
  Qed.

  (* I think that the injectivity requirement is not necessary? *)
  Lemma measurable_by_cover_inj {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : T1 -> T2)
      (F : sequences.sequence (set T1))
      (Hrange : range f = setT)
      (HI : injective f)
      (Hmeas: forall i, measurable (F i))
      (Hcover : (\bigcup_i (F i)) = setT)
      (Hrestriction : forall i, measurable_fun (F i) (restrict (F i) f)) :
      measurable_fun setT f.
  Proof.
    unfold measurable_fun.
    intros _ s Hs.
    rewrite setTI.
    (* Rewrite s to be s intersect setT *)
    rewrite <- (setTI s).
    (* Rewrite setT to be union of B i *)
    have Bcover : (\bigcup_i ((fun i => image (F i) f) i)) = (setT : set T2).
    { rewrite <- image_bigcup.
      rewrite Hcover.
      apply Hrange. }
    simpl.
    rewrite <- Bcover.
    rewrite setI_bigcupl.
    rewrite preimage_bigcup.
    apply bigcupT_measurable.
    intro i.
    unfold measurable_fun in Hrestriction.
    unfold restrict in Hrestriction.
    have X := Hrestriction i (Hmeas i) s Hs.
    have HR : (F i `&` (fun u : T1 => if u \in F i then f u else point) @^-1` s) = (f @^-1` ([set f x | x in F i] `&` s)).
    { apply functional_extensionality.
      intro t.
      simpl.
      (* This proof is terrible, but only because of their insistence on using reflection *)
      pose K := ExcludedMiddle (F i t).
      destruct K.
      - have H' := H.
        rewrite <- in_setE in H'.
        rewrite H'.
        apply propext.
        split; last first.
        - intros [H1 H2]; split; assumption.
        - intros [H1 H2].
          split; last assumption.
          exists t; [assumption|reflexivity].
      - rewrite (memNset H).
        rewrite (notTE H).
        rewrite (propext (base.False_and (s point))).
        simpl.
        apply propext.
        split; first (intro K; destruct K).
        intros [[t' Ht' Htt'] B].
        apply H.
        rewrite <- (HI _ _ Htt').
        apply Ht'.
    }
    rewrite HR in X.
    apply X.
  Qed.


  Lemma rest_map_lemma {T1 : Type} {T2 : pointedType} (t : T1) (X : set T1) (Ht : X t) (f : T1 -> T2) :
    (f \_ X) t = f t.
  Proof. by rewrite /restrict (mem_set Ht). Qed.

  Lemma measurable_by_cover {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : T1 -> T2)
      (F : sequences.sequence (set T1))
      (Hmeas: forall i, measurable (F i))
      (Hcover : (\bigcup_i (F i)) = setT)
      (Hrestriction : forall i, measurable_fun (F i) (restrict (F i) f)) :
      measurable_fun setT f.
  Proof.
    unfold measurable_fun.
    intros _ s Hs.
    rewrite setTI.
    have preimage_lemma_1 : (f @^-1` s) = \bigcup_i ((F i) `&` ((f \_ (F i)) @^-1` s)).
    { apply functional_extensionality.
      intro t.
      apply propext.
      split.
      - intro H.
        unfold bigcup.
        simpl.
        have T : [set: T1] t by simpl.
        rewrite <- Hcover in T.
        unfold bigcup in T.
        simpl in T.
        destruct T as [i _ Hi].
        exists i; [done|].
        split; [done|].
        rewrite (rest_map_lemma Hi f).
        unfold preimage in H.
        simpl in H.
        by trivial.
      - intro H.
        unfold bigcup in H.
        simpl in H.
        destruct H as [i _ [Hi H]].
        rewrite (rest_map_lemma Hi f) in H.
        unfold preimage.
        simpl.
        by trivial.
    }
    rewrite preimage_lemma_1.
    apply bigcupT_measurable.
    intro i.
    rewrite /measurable_fun in Hrestriction.
    apply Hrestriction.
    - by apply Hmeas.
    - by trivial.
  Qed.

  (* Turn a list into a sequence, with setT as the default element *)
  Fixpoint list_set_to_seq {T : Type} (L : list (set T)) : sequences.sequence (set T) :=
    fun i =>
      match L, i with
      | (x :: xs), 0 => x
      | (x :: xs), (S i) => list_set_to_seq xs i
      | _, _ => set0
      end.


  Lemma measurable_restrict_set0 {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : T1 -> T2) :
       measurable_fun set0 (restrict set0 f).
  Proof.
    intros ???.
    rewrite set0I.
    by apply measurable0.
  Qed.

  Lemma measurable_by_cover_list {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : T1 -> T2)
      (L : list (set T1))
      (Hmeas: List.Forall measurable L)
      (Hcover : List.fold_right setU set0 L = setT)
      (Hrestriction : List.Forall (fun l => measurable_fun l (restrict l f)) L) :
      measurable_fun setT f.
  Proof.
    apply (@measurable_by_cover  _ _ _ _ f (list_set_to_seq L)).
    - clear Hcover Hrestriction.
      intro i.
      generalize dependent L.
      induction i.
      + intros L H1.
        destruct L.
        * simpl list_set_to_seq.
          by eapply @measurable0.
        * simpl list_set_to_seq.
          by apply List.Forall_inv in H1.
      + intros L H1.
        destruct L.
        * simpl list_set_to_seq.
          by eapply @measurable0.
        * simpl list_set_to_seq.
          apply IHi.
          by apply List.Forall_inv_tail in H1.
    - clear Hmeas Hrestriction.
      rewrite <- Hcover.
      clear Hcover.
      induction L.
      + unfold bigcup.
        simpl.
        apply functional_extensionality; intro x; apply propext; split; simpl; [|tauto].
        intros [_ F].
        done.
      + rewrite list.foldr_cons.
        rewrite <- IHL.
        apply functional_extensionality.
        intro x.
        apply propext.
        unfold bigcup.
        simpl.
        split.
        * intros [A B].
          destruct A; [by left|].
          right.
          by exists A.
        * intros [A | [B C]].
          -- by exists 0.
          -- exists (B.+1); done.
    - clear Hmeas Hcover.
      intro i.
      generalize dependent L.
      induction i.
      + intros L H1.
        destruct L.
        * simpl list_set_to_seq.
          by apply measurable_restrict_set0.
        * simpl list_set_to_seq.
          by apply List.Forall_inv in H1.
      + intros L H1.
        destruct L.
        * simpl list_set_to_seq.
          by apply measurable_restrict_set0.
        * simpl list_set_to_seq.
          apply IHi.
          by apply List.Forall_inv_tail in H1.
  Qed.

End Lib.


(*
Section subset_salgebra_instance.
Local Open Scope classical_set_scope.

Context d1 (T1 : measurableType d1).

(* Hierachy Builder problem:
    I want to make a sigma algebra over {a : T1 | A a}
    In order to do that, I need {a : T1 | A a} to be pointed (for some reason)
    In order to do that, I need to internalize the nonemptiness into the type, or else it breaks the canonical structures.
    Hopefully that explains the insane type here I'm using here.
 *)

Definition ne_subset (A : set T1) (p : T1) (_ : A p) : Type := {a : T1 | A a}.


(* The type of subsets of A. Has to be written this way to work wiht the sigma algebra construction, even though it's annoying to use later.*)

Definition sub (A : set T1) {p : T1} (Hp : A p) : Type := set (@ne_subset A _ Hp).

Definition sub_to_ambient (A : set T1) {p : T1} (Hp : A p) (s : @sub A p Hp) : set T1 :=
  [set (proj1_sig x) | x in s ].

(* A subset S1 of A is the intersection of a larger set S2 with A *)
Program Definition is_restriction (A : set T1) {p : T1} (Hp : A p) (S1 : @sub A p Hp) (S2 : set T1) : Prop :=
  forall a : T1, forall H : A a, S2 a <-> S1 _.
Next Obligation. intros A S1 S2 a H p Hp. unfold ne_subset. exists p. apply Hp. Defined.
(* For all elements a, if a is in A, then a is in S2 iff a is in S1*)

(* The sigma algebra is the set of subsets of A, which are equal to restrictions of a measurable set. *)
Definition subset_system {A : set T1} {p : T1} (Hp : A p) (_ : d1.-measurable A) : set (@sub A p Hp) :=
  [set X | exists M : set T1, d1.-measurable M /\ is_restriction X M].

Lemma subset_algebra_set0 {A : set T1} {p : T1} (Hp : A p) (H : d1.-measurable A) : subset_system H (set0 : @sub A p Hp).
Proof.
  unfold subset_system; simpl.
  exists set0.
  split.
  - by apply measurable0.
  - rewrite /is_restriction.
    intros a Ha.
    by simpl.
Qed.

Lemma subset_algebra_setC {A : set T1} {p : T1} (Hp : A p) (H : d1.-measurable A) (B : @sub A p Hp) :
  @subset_system A p Hp H B ->
  @subset_system A p Hp H (~` B).
Proof.
  unfold subset_system; simpl.
  intros [S [HS HBS]].
  exists (~` S).
  split.
  - simpl.
    by apply measurableC.
  - unfold is_restriction.
    simpl.
    intros a Ha.
    rewrite /is_restriction in HBS.
    have HBS' := HBS a Ha.
    (* Deal with HB's idiotic reflections, then trivial *)
    admit.
Admitted.


Definition subset_algebra_bigcup {A : set T1} {p : T1} (Hp : A p) (H : d1.-measurable A) (F : sequences.sequence _) :
  (forall i, @subset_system A p Hp H (F i)) ->
  @subset_system A p Hp H (\bigcup_i (F i)).
Proof.
  intro H1.
  unfold subset_system.
  simpl.
  exists ((\bigcup_i (sub_to_ambient (F i))) `&` A).
  split.
  - rewrite setI_bigcupl.
    apply bigcup_measurable.
    intros k _.
    apply measurableI; last by trivial.
    unfold subset_system in H1.
    destruct (H1 k) as [S [H3 H4]].
    unfold sub_to_ambient.
    unfold is_restriction in H4.
    admit.
  - unfold is_restriction.
    intros a Ha.
    split.
    - intro H2.
      admit.
    - intro H2.
      admit.
Admitted.

(* Why do sigma algebras have to be pointed??? This is stupid *)

Definition make_point {A : set T1} {p : T1} (Hp : A p) : @ne_subset A p Hp :=
  exist _ p Hp.

HB.instance Definition _ {A : set T1} {p : T1} (Hp : A p) := isPointed.Build (@ne_subset A p Hp) (make_point Hp).

Definition sub_display (A : set T1) : measure_display.
Proof. exact. Qed.

(*
HB.instance Definition subset_algebra_mixin {A : set T1} (H : d1.-measurable A) {p : T1} (Hp : A p) :=
  @isMeasurable.Build
    (sub_display A)
    (@ne_subset A p Hp)
    (@subset_system H)
    (@subset_algebra_set0)
    (@subset_algebra_setC)
    (@subset_algebra_bigcup).
*)
*)


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
     measurable_fun E f -> (forall x, E x -> f x = g x) -> measurable_fun E g.
  Proof.
    intros H1 H2.
    apply (mathcomp_restriction_measurable_of_measurable HE).
    apply (mathcomp_restriction_is_measurable HE) in H1.
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
  Global Arguments mathcomp_measurable_fun_ext {_} {_} {_} {_}.


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

  Global Arguments mathcomp_measurable_fun_restiction_setT {_} {_} {_} {_}.

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

(*  Definition fin_to_nat {N : nat} (x : 'I_(S N)) : Z.
Admitted. *)

(** Strict generalization of the version in mathcomp *)
Lemma prod_measurable_funP' {d d1 d2} {T : measurableType d} {T1 : measurableType d1} {T2 : measurableType d2}
  (h : T -> T1 * T2) (S : set T) (HS : measurable S) :
  measurable_fun S h <-> measurable_fun S (ssrfun.comp fst h) /\ measurable_fun S (ssrfun.comp snd h).
Proof.
  (* Proof: Conjugate by the restriction lemma, and apply the setT version *)
  split.
  - intro H.
    apply (@mathcomp_restriction_is_measurable _ _ _ _ S HS h) in H.
    apply (prod_measurable_funP (h \_ S)) in H.
    destruct H as [H1 H2].
    by split; apply (@mathcomp_restriction_measurable_of_measurable _ _ _ _ S HS); rewrite restrict_comp.
  - intros [H1 H2].
    eapply (@mathcomp_restriction_is_measurable _ _ _ _ S HS _) in H1.
    eapply (@mathcomp_restriction_is_measurable _ _ _ _ S HS _) in H2.
    rewrite restrict_comp in H1; [|done].
    rewrite restrict_comp in H2; [|done].
    have X := iffRL (prod_measurable_funP (h \_ S)) (conj H1 H2).
    apply (@mathcomp_restriction_measurable_of_measurable _ _ _ _ S HS _ X).
Qed.

(** Strict generalization of the version in mathcomp *)
Lemma measurable_fun_prod' {d d1 d2} {T : measurableType d} {T1 : measurableType d1} {T2 : measurableType d2}
  (f : T -> T1) (g : T -> T2) (S : set T) (HS : measurable S):
  measurable_fun S f -> measurable_fun S g ->
  measurable_fun S (fun x => (f x, g x)).
Proof. by move=>??; exact/prod_measurable_funP'. Qed.
Global Arguments measurable_fun_prod' {_} {_} {_} {_} {_} {_}.

Notation mProd f g := (fun x => (f x, g x)).

Lemma measurable_compT {d1 d2 d3} {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}
       (f : T2 -> T3) (E : set T1) (g : T1 -> T2)
       (HE : d1.-measurable E) (Hf : measurable_fun setT f)
       (Hg : measurable_fun E g) : measurable_fun E (ssrfun.comp f g).
Proof.
  have MT : measurable (setT : set T2) by eauto.
  by eapply (measurable_comp MT _ Hf Hg).
  Unshelve.
  by rewrite /subset//=.
Qed.

Lemma measurable_compT' {d1 d2 d3} {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}
       (f : T2 -> T3) (E : set T1) (g : T1 -> T2)
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
Global Arguments measurable_fun_setI1 {_} {_} {_} {_}.


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

(** Tactics *)

(* Really slow when I add it to mcrunch *)
Ltac mcrunch_fst := apply measurable_fst_restriction; by eauto with measlang.

Ltac mcrunch_snd := apply measurable_snd_restriction; by eauto with measlang.

(** Wrapper around eauto for finishing tactics *)
Ltac mcrunch := by eauto with measlang.

(** For proving the measurability of a composition where the first composite function
    can be solved by eauto on a set, and the measurability is not on the top set. *)
Ltac mcrunch_comp :=
  ( eapply @measurable_comp; [ | | by eauto with measlang | ]; try by eauto with measlang ).

(** For proving the measurability of a composition by a constructor.
    First argument is the constructor measurability proof. *)
Ltac mcrunch_compC H :=
  ( eapply @measurable_compT; [ by eauto with measlang | by apply H | ] ).

(** Measurability of mprod
    Doesn't always work, if it gets confused you need to unroll the arguments to
    measurable_fun_prod' *)
Ltac mcrunch_prod := ( eapply @measurable_fun_prod'; first by eauto with measlang ).


Section measurable_curry.
  Local Open Scope classical_set_scope.

  (** Currying a function and then applying to a value yields a measurable function *)

  Context (R : realType). (* This is due to a bug in mathcomp analysis, delete me. *)

  Context {d1 d2 d3 : measure_display}.
  Context {T1 : measurableType d1}.
  Context {T2 : measurableType d2}.
  Context {T3 : measurableType d3}.

  Context (f : (T1 * T2) -> T3).
  Context (mf : measurable_fun setT f).
  Context (x : T1).

  Lemma curry_meas : measurable_fun setT ((curry f) x).
  Proof using R T1 T2 T3 d1 d2 d3 f mf x.
    intros _ U MU.
    rewrite setTI /curry //=.
    suffices H : ((fun y : T2 => f (x, y)) @^-1` U) = xsection (f @^-1` U) x.
    { rewrite H.
      eapply (measurable_xsection R _). (* I can see no reason why measurable_xsection needs R? *)
      rewrite <- (setTI (preimage _ _)).
      eapply (@mf _ U MU).
      Unshelve. by apply @measurableT.
    }
    apply /predeqP =>y /=.
    rewrite /xsection/=.
    by rewrite in_setE //=.
  Qed.

End measurable_curry.
