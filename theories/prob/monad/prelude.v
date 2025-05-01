From HB Require Import structures.
From mathcomp Require Import all_ssreflect classical_sets boolp functions.
From clutch.prelude Require Import classical.
From mathcomp.analysis Require Import reals ereal measure lebesgue_measure lebesgue_integral sequences function_spaces.
From stdpp Require Import base decidable.
From clutch.prob.monad Require Export preprelude.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type*".

Reserved Notation "'<<discr' G '>>'" (at level 2, format "'<<discr' G '>>'").
Reserved Notation "G .-discr" (at level 1, format "G .-discr").
Reserved Notation "G .-discr.-measurable" (at level 2, format "G .-discr.-measurable").

Global Instance classical_eq_dec {T : Type} : EqDecision T.
Proof. by intros ??; apply make_decision. Defined.

Local Open Scope classical_set_scope.

Definition discrType (T : Type) : Type := T.

Section discr_salgebra_instance.
  Variables (T : pointedType).

  Definition discr_measurable : set (set (discrType T)) := setT.

  Lemma discr_measurable0 : discr_measurable set0.
  Proof. by []. Qed.

  Lemma discr_measurableC X : discr_measurable X -> discr_measurable (~` X).
  Proof. by []. Qed.

  Lemma discr_measurableU (F : sequence (set T)) : (forall i, discr_measurable (F i)) -> discr_measurable (\bigcup_i F i).
  Proof. by []. Qed.

  Definition discr_display : Type -> measure_display.
  Proof. done. Qed.

  HB.instance Definition _ := gen_eqMixin (discrType T).
  HB.instance Definition _ := gen_choiceMixin (discrType T).
  HB.instance Definition _ := isPointed.Build (discrType T) point.
  HB.instance Definition _ := @isMeasurable.Build (discr_display T) (discrType T) discr_measurable
                               discr_measurable0 discr_measurableC discr_measurableU.
End discr_salgebra_instance.

Notation "'<<discr' G '>>'" := (discrType G) : classical_set_scope.
Notation "G .-discr" := (discr_display G) : measure_display_scope.
Notation "G .-discr.-measurable" :=
  (((G.-discr).-measurable : set (set (<<discr G>>))) )%classic.


Section discr_meas_fun.
  Context {d2} {T1 : pointedType} {T2 : measurableType d2}.
  Context {D : set <<discr T1>>} {f : <<discr T1>> -> T2}.

  Lemma discr_meas_fun : measurable_fun D f.
  Proof. by rewrite /measurable_fun/measurable/discr_measurable//. Qed.
End discr_meas_fun.


Section fin_pointed.
  Local Open Scope ereal_scope.
  Context {R : realType}.
  Variable (m : nat).

  Definition Ism_inhabitant : 'I_(S m). by eapply (@Ordinal _), leqnn. Defined.

  HB.instance Definition _ N := isPointed.Build ('I_(S m)) Ism_inhabitant.
End fin_pointed.

Section curry.
  Context (R : realType). (* This is due to a bug in mathcomp analysis, delete me. *)

  Context {d1 d2 d3 : measure_display}.
  Context {T1 : measurableType d1}.
  Context {T2 : measurableType d2}.
  Context {T3 : measurableType d3}.

  Context (f : (T1 * T2) -> T3).
  Context (mf : measurable_fun setT f).
  Context (x : T1).

  Lemma curry_meas_fun : measurable_fun setT ((curry f) x).
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

End curry.

Section uncurry_nat.

  Lemma uncurry_nat_measurable {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
          (f : nat -> T1 -> T2) (Hf : forall i, measurable_fun setT (f i)) :
        measurable_fun setT (uncurry f).
  Proof.
    intros _ Y HY.
    have -> : ((uncurry f) @^-1` Y) = (\bigcup_i ((setX [set i] ((f i) @^-1` Y)) : set (nat * _)%type)).
    { rewrite /uncurry/preimage/setX//=.
      apply /predeqP =>[[n ?]] /=.
      split.
      { intros H. by exists n. }
      { move=>[x ?]//=. by move=>[-> ?]//=. }
    }
    rewrite setTI.
    apply bigcup_measurable.
    intros i ?.
    apply measurableX.
    { by rewrite /measurable//=. }
    rewrite <-(setTI (preimage _ _)).
    by eapply (Hf i _ Y HY).
    Unshelve. by apply @measurableT.
  Qed.

End uncurry_nat.

Lemma uncurry_measurable {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} {T: pointedType}
  (f : <<discr T>> -> T1 -> T2) (Hf : forall i, measurable_fun setT (f i)) (T_enum: nat -> <<discr T>>):
  (forall x, ∃ (n:nat), T_enum n = x) ->
        measurable_fun setT (uncurry f).
   Proof.
    intros Hsurj ? Y HY.
    have -> : ((uncurry f) @^-1` Y) = \bigcup_i ((setX [set T_enum i] ((f $ T_enum i) @^-1` Y)) : set (_ * _)%type).
    { rewrite /uncurry/preimage/setX//=.
      apply /predeqP =>[[l ]] /=.
      split.
      { intros H'.
        destruct (Hsurj l) as [i Hi].
        exists i; [done|].
        by rewrite Hi //=. }
      { move=>[x ?]//=. by move=>[-> ?]//=. }
    }
    rewrite setTI.
    apply bigcup_measurable.
    intros i ?.
    apply measurableX.
    { by rewrite /measurable//=. }
    rewrite <-(setTI (preimage _ _)).
    by eapply (Hf _ _ Y HY).
    Unshelve. by apply @measurableT.
   Qed.
   
#[short(type=genSingletonType)]
HB.structure Definition GenSingletons := {T of isPointed T & Countable T}.

(* NOTE: Must run ``HB.saturate T`` to let ``t : discreteType`` (a ``pointedType`` and ``countType``)
   Check (nat : pointedType).
   Check (nat : countType).
   Fail Check (nat : genSingletonType).
   HB.saturate nat.
   Check (nat : genSingletonType).
*)

Section discr_gen_singletons.
  Context {T : genSingletonType}.

  Lemma discr_generated_by_singletons : T.-discr.-measurable = <<s singletons>>.
  Proof.
    (* The type is countable so setT is the union of singletons *)
  Admitted.

  (*

(* Not the best way to prove this. Use Countable instances instead of my custom enum functions. *)
(* The result is true for all countable discrete types. *)
Lemma binder_generated_by_singletons : binder.-discr.-measurable = <<s binder_singletons >>.
Proof.
  apply /predeqP =>y //=.
  simpl in *.
  split.
  - move=> _.
    have ->: y = \bigcup_i ([set (binder_enum i)] `&` y).
    { rewrite /bigcup//=.
      apply /predeqP =>z /=.
      split.
      - move=> ?.
        destruct (binder_enum_surj z) as [i ?].
        by exists i.
      - by move=> [i ?][-> ?].
    }
    apply sigma_algebra_bigcup.
    move=> i.
    destruct (ExcludedMiddle (y (binder_enum i))).
    + apply sub_sigma_algebra.
      rewrite /binder_singletons/setI //=.
      exists (binder_enum i).
      apply /predeqP =>z /=.
      split.
      + by move=> [? ?].
      + by move=>->.
    + have -> : ([set binder_enum i] `&` y) = set0.
      { rewrite /setI//=.
      apply /predeqP =>z /=.
      split.
      + by move=>[-> ?].
      + by move=>?. }
      apply sigma_algebra0.
  - move=> _. by rewrite /measurable/=/discr_measurable/=.
Qed.
   *)

End discr_gen_singletons.


Section Lib.
  Lemma measurable_if_pushfowrard_subset {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : T1 -> T2) :
        (d2.-measurable  `<=` [set s : set T2 | d1.-measurable ( f@^-1` s )]) -> (measurable_fun setT f).
  Proof.
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
      (* This proof is terrible, but fixable  *)
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

  Lemma rest_map_lemma' {T1 : Type} {T2 : pointedType} (t : T1) (X : set T1) (Ht : ¬ X t) (f : T1 -> T2) :
    (f \_ X) t = point.
  Proof. by rewrite /restrict (memNset Ht). Qed.

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
End subspaces.


Definition image3 {TA TB TC rT} (A : set TA) (B : set TB) (C : set TC) (f : TA -> TB -> TC -> rT) :=
  [set z | exists2 x, A x & exists2 y, B y & exists2 w, C w & f x y w = z].
Arguments image3 _ _ _ _ _ _ _ _ /.

Definition image4 {TA TB TC TD rT} (A : set TA) (B : set TB) (C : set TC) (D : set TD) (f : TA -> TB -> TC -> TD -> rT) :=
  [set z | exists2 x, A x & exists2 y, B y & exists2 w, C w & exists2 v, D v & f x y w v = z].
Arguments image4 _ _ _ _ _ _ _ _ _ /.

Lemma eq_measurable {d} {T : measurableType d} (X Y : set T) :
  d.-measurable X -> Y = X -> d.-measurable Y.
Proof. by move=>?->. Qed.


Notation mProd f g := (fun x => (f x, g x)).
Notation "f △ g" := (mProd f g) (at level 70, no associativity).

Section products.

  (** Strict generalization of the version in mathcomp *)
  Lemma prod_measurable_funP' {d d1 d2} {T : measurableType d} {T1 : measurableType d1} {T2 : measurableType d2}
    (h : T -> T1 * T2) (S : set T) (HS : measurable S) :
    measurable_fun S h <-> measurable_fun S (ssrfun.comp fst h) /\ measurable_fun S (ssrfun.comp snd h).
  Proof.
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

End products.


Section comp.

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

End comp.

(** A function into a generated measurableType is a measurable function
    when the preimages of the generators are measurable.  *)

(** FIXME: Depricated hintDB*)
Create HintDb measlang.

Ltac into_gen_measurable := eapply measurability; [by eauto|].

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

















Section option_salgebra_instance.
  Context {d1} {T1 : measurableType d1}.

  Definition option_S : Type := option (set T1).
  Definition option_T : Type := option T1.

  Check image.
  Program Definition option_ST (k : option_S) : set option_T :=
    match k with
    | None => [set None]
    | Some s => image s Some (* (fun y => exists2 x, s x & Some x = y)*)
    end.
  Definition option_ML : set option_S :=
    fun k =>
      match k with
      | None => True
      | Some s => d1.-measurable s
      end.

  Definition option_cyl : set (set option_T) := image option_ML option_ST.

  HB.instance Definition _ := gen_eqMixin option_T.
  HB.instance Definition _ := gen_choiceMixin option_T.
  HB.instance Definition _ := isPointed.Build option_T None.

  (* FIXME: Remove *)
  Lemma option_meas_obligation :
    forall A : set option_T, <<s option_cyl>> A -> <<s option_cyl >> (~` A).
  Proof. eapply sigma_algebraC. Qed.

  HB.instance Definition _ := @isMeasurable.Build
    (sigma_display option_cyl)
    (option T1)
    <<s option_cyl>>
    (@sigma_algebra0 _ setT option_cyl)
    option_meas_obligation
    (@sigma_algebra_bigcup _ setT option_cyl).

End option_salgebra_instance.

Section option.

  Lemma Some_meas_fun {d1} {T : measurableType d1} : measurable_fun (setT : set T) Some.
  Proof.
    into_gen_measurable.
    rewrite /preimage_class. intros ?. simpl.
    intros [?[[]?]]; subst.
    { rewrite /option_ML in H.
      rewrite setTI.
      have -> : (Some @^-1` option_ST (Some s)) = s; [|done].
      rewrite /preimage/option_ST//=.
      rewrite eqEsubset; split.
      { move=>?[??] [+]. by move=><-. }
      { move=>??//=. eexists _; done. }
    }
    { have -> : ((Some @^-1` option_ST None)=set0).
      { move=>??; rewrite eqEsubset; by split.  }
      by eapply @measurableI.
    }
  Qed.
  Hint Resolve Some_meas_fun : measlang.

  (* Shapes? *)

  Definition 𝜋_Some_v {d1} {T : measurableType d1} (k : option T) : T := match k with | Some v => v | _ => point end.
  Definition option_cov_Some {d1} {T : measurableType d1} : set (option T) := [set e | exists x, e = Some x].
  Definition option_cov_None {d1} {T : measurableType d1} : set (option T) := [set e | e = None].
  Lemma option_cov_Some_meas_set {d1} {T : measurableType d1} : measurable (option_cov_Some : set (option T)).
  Proof. Admitted.
  Hint Resolve option_cov_Some_meas_set : measlang.
  Lemma option_cov_None_meas_set {d1} {T : measurableType d1} : measurable (option_cov_None : set (option T)).
  Proof. Admitted.
  Hint Resolve option_cov_None_meas_set : measlang.
  Lemma 𝜋_Some_v_meas_fun {d1} {T : measurableType d1} (k : option T) : measurable_fun (option_cov_Some : set (option T)) 𝜋_Some_v.
  Proof. Admitted.
  Hint Resolve 𝜋_Some_v_meas_fun : measlang.

End option.



Section list_salgebra_instance.
  Context {d1} {T1 : measurableType d1}.

  Definition list_S : Type := list (set T1).
  Definition list_T : Type := list T1.
  Fixpoint list_ST (k : list_S) : set list_T :=
    match k with
    | [::] => [set [::]]
    | (s :: xs) => image2 s (list_ST xs) (fun x y => x :: y)
    end.
  Fixpoint list_ML (k : list_S) : Prop :=
      match k with
      | [::] => True
      | (s :: xs) => d1.-measurable s /\ list_ML xs
      end.

  Definition list_cyl : set (set list_T) := image list_ML list_ST.

  HB.instance Definition _ := isPointed.Build (list T1) [::].

  (* FIXME: Remove *)
  Lemma list_meas_obligation :
    forall A : set list_T, <<s list_cyl>> A -> <<s list_cyl >> (~` A).
  Proof. eapply sigma_algebraC. Qed.

  HB.instance Definition _ := @isMeasurable.Build
    (sigma_display list_cyl)
    (list T1)
    <<s list_cyl>>
    (@sigma_algebra0 _ setT list_cyl)
    list_meas_obligation
    (@sigma_algebra_bigcup _ setT list_cyl).

  (* NOTE: This is probably bad because it chains typeclass instances through the canonical structures
     rather than being a regular higher-order typeclass. Does it work through? The lifted types
     _should_ be defeq to a measurableType right? *)
  Global Instance list_sigma_algebra : SigmaAlgebra (sigma_display list_cyl) (list T1) :=
    {| axioms := @Measurable.class (sigma_display list_cyl) (list T1) |}.

End list_salgebra_instance.


Section list.
  Definition consU {d1} {T : measurableType d1} : (T * list T)%type -> list T := uncurry List.cons.

  Lemma cons_meas_fun {d1} {T : measurableType d1} : measurable_fun setT (consU : (T * list T)%type -> list T).
  Proof. Admitted.
  Hint Resolve cons_meas_fun : measlang.

  (* Shapes? *)

  Definition 𝜋_cons_v {d1} {T : measurableType d1} (k : list T) : T := match k with | (v :: _) => v | _ => point end.
  Definition 𝜋_cons_vs {d1} {T : measurableType d1} (k : list T) : list T := match k with | (_ :: v) => v | _ => point end.
  Definition list_cov_cons {d1} {T : measurableType d1} : set (list T) := [set e | exists x y, e = x :: y].
  Definition list_cov_empty {d1} {T : measurableType d1} : set (list T) := [set e | e = [::]].
  Lemma list_cov_cons_meas_set {d1} {T : measurableType d1} : measurable (list_cov_cons : set (list T)).
  Proof. Admitted.
  Hint Resolve list_cov_cons_meas_set : measlang.
  Lemma list_cov_empty_meas_set {d1} {T : measurableType d1} : measurable (list_cov_empty : set (list T)).
  Proof. Admitted.
  Hint Resolve list_cov_empty_meas_set : measlang.
  Lemma 𝜋_cons_v_meas_fun {d1} {T : measurableType d1} (k : list T) : measurable_fun (list_cov_cons : set (list T)) 𝜋_cons_v.
  Proof. Admitted.
  Hint Resolve 𝜋_cons_v_meas_fun : measlang.
  Lemma 𝜋_cons_vs_meas_fun {d1} {T : measurableType d1} (k : list T) : measurable_fun (list_cov_cons : set (list T)) 𝜋_cons_vs.
  Proof. Admitted.
  Hint Resolve 𝜋_cons_vs_meas_fun : measlang.
End list.

Section extern_if.
  Context {T : Type}.
  Context (P : Prop).

  Definition extern_if (default : T) (f : P -> T) : T :=
    match (pselect P) with
    | left H => f H
    | right _ => default
    end.

  Lemma extern_if_eq {default : T} {f : P -> T} (H : P) :
    extern_if default f = f H.
  Proof.
    rewrite /extern_if//=.
    destruct (pselect P) as [H' | H'].
    { f_equal. by apply proof_irrelevance. }
    { exfalso. by apply H', H. }
  Qed.
  
  Lemma extern_if_neq {default : T} {f : P -> T} (H : not P) :
    extern_if default f = default.
  Proof.
    rewrite /extern_if//=.
    destruct (pselect P) as [H' | H'].
    { exfalso. by apply H, H'. }
    { by f_equal. }
  Qed.

End extern_if.

Section of_option.
  Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.

  Definition of_option (f : T1 -> option T2) : T1 -> T2 := 𝜋_Some_v \o f.

  Lemma of_option_meas_fun (f : T1 -> option T2) (Hf : measurable_fun setT f) :
    measurable_fun (preimage f option_cov_Some) (of_option f).
  Proof. Admitted.
  Hint Resolve of_option_meas_fun : measlang.

End of_option.

Section if_in.
  Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.

  Definition if_in (D : set T1) (f1 f2 : T1 -> T2) : T1 -> T2 :=
    fun x => if (@bool_decide (D x) (make_decision _)) then f1 x else f2 x.

  Lemma ifIn_eq_left (D : set T1) (f1 f2 : T1 -> T2) (x : T1) : D x -> if_in D f1 f2 x = f1 x.
  Proof. move=>?; rewrite /if_in; by case_bool_decide. Qed.

  Lemma ifIn_eq_right (D : set T1) (f1 f2 : T1 -> T2) (x : T1) : ¬ D x -> if_in D f1 f2 x = f2 x.
  Proof. move=>?; rewrite /if_in; by case_bool_decide. Qed.

  Lemma if_in_split (D : set T1) (f1 f2 : T1 -> T2) (x : T1) P:
    (D x -> P (f1 x)) -> (¬ D x -> P (f2 x)) -> P (if_in D f1 f2 x).
  Proof.
    rewrite /if_in.
    case_bool_decide.
    - intros H1 ?. by apply H1.
    - intros ? H2. by apply H2.
  Qed.

  Lemma if_in_meas_fun (D DT : set T1) (H : measurable D) (HDT  : measurable DT) (f1 f2 : T1 -> T2)
                       (Hf1 : measurable_fun (D `&` DT) f1) (Hf2 : measurable_fun ((~` D) `&` DT) f2) :
    measurable_fun DT (if_in D f1 f2).
  Proof.
    have -> : DT = (D `&` DT) `|` (~` D `&` DT).
    { by rewrite <- setIUl; rewrite setUv setTI. }
    apply <- measurable_funU; first split.
    - eapply mathcomp_measurable_fun_ext; [| by apply Hf1 |].
      + by apply measurableI.
      + by move=>//= ? [? ?]; rewrite ifIn_eq_left.
    - eapply mathcomp_measurable_fun_ext; [| by apply Hf2 |].
      + apply measurableI; last done. by apply measurableC.
      + by move=>//= ? [? ?]; rewrite ifIn_eq_right.
    - apply measurableI; last done. by apply measurableC.
    - by apply measurableI.
  Qed.
  Hint Resolve if_in_meas_fun : measlang.

End if_in.

Lemma fst_setX_meas_fun {d1 d2 d3} {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}
    (D1 : set T1) (D2 : set T2) {H1 : measurable D1} {H2 : measurable D2} (f : T1 -> T3) :
  measurable_fun D1 f -> measurable_fun (setX D1 D2) (f \o fst).
Proof.
  intros ?.
  eapply (@measurable_comp _ _ _ _ _ _ D1); try done.
  { by rewrite /subset//=; move=>?[?[??]]<-//=. }
  apply @mathcomp_measurable_fun_restiction_setT.
  { by apply measurableX. }
  { by apply measurable_fst. }
Qed.

Lemma snd_setX_meas_fun {d1 d2 d3} {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}
    (D1 : set T1) (D2 : set T2) {H1 : measurable D1} {H2 : measurable D2} (f : T2 -> T3) :
  measurable_fun D2 f -> measurable_fun (setX D1 D2) (f \o snd).
Proof.
  intros ?.
  eapply (@measurable_comp _ _ _ _ _ _ D2); try done.
  { by rewrite /subset//=; move=>?[?[??]]<-//=. }
  apply @mathcomp_measurable_fun_restiction_setT.
  { by apply measurableX. }
  { by apply measurable_snd. }
Qed.


Lemma prod1 (T S : Type) (t : T) (s : S) : [set (t, s)] = [set t] `*` [set s].
Proof.
  rewrite /setX.
  apply functional_extensionality; intro x; simpl.
  apply propext.
  split.
  - by move=>->//.
  - by move=>[<-<-]; case x.
Qed.
