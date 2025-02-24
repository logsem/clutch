Set Warnings "-hiding-delimiting-key".
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
From clutch.meas_lang.lang Require Export prelude types.
Set Warnings "hiding-delimiting-key".

Local Open Scope classical_set_scope.


(** Uncurried constructors: These ones can be shown to be measurable directly *)
Definition LitIntU  (v : TZ)                                      := LitIntC v.
Definition LitBoolU (v : TB)                                      := LitBoolC v.
Definition LitUnitU                                               := LitUnitC.
Definition LitLocU  (v : TL)                                      := LitLocC v.
Definition LitLblU  (v : TL)                                      := LitLblC v.
Definition LitRealU (v : TR)                                      := LitRealC v.

Definition ValU (v : val)                                         := ValC v.
Definition VarU (v : <<discr binder>>)                            := VarC v.
Definition RecU (v : <<discr binder>> * <<discr binder>> * expr)  := RecC v.1.1 v.1.2 v.2.
Definition AppU (v : expr * expr)                                 := AppC v.1 v.2.
Definition UnOpU (v : <<discr un_op>> * expr)                     := UnOpC v.1 v.2.
Definition BinOpU (v : <<discr bin_op>> * expr * expr)            := BinOpC v.1.1 v.1.2 v.2.
Definition IfU (v : expr * expr * expr)                           := IfC v.1.1 v.1.2 v.2.
Definition PairU (v : expr * expr)                                := PairC v.1 v.2.
Definition FstU (v : expr)                                        := FstC v.
Definition SndU (v : expr)                                        := SndC v.
Definition InjLU (v : expr)                                       := InjLC v.
Definition InjRU (v : expr)                                       := InjRC v.
Definition CaseU (v : expr * expr * expr)                         := CaseC v.1.1 v.1.2 v.2.
Definition AllocNU (v : expr * expr)                              := AllocNC v.1 v.2.
Definition LoadU (v : expr)                                       := LoadC v.
Definition StoreU (v : expr * expr)                               := StoreC v.1 v.2.
Definition AllocTapeU (v : expr)                                  := AllocTapeC v.
Definition RandU (v : expr * expr)                                := RandC v.1 v.2.
Definition AllocUTapeU                                            := AllocUTapeC.
Definition UrandU (v : expr)                                      := URandC v.
Definition TickU (v : expr)                                       := TickC v.

Definition LitVU (v : base_lit)                                   := LitVC v.
Definition RecVU (v : <<discr binder>> * <<discr binder>> * expr) := RecVC v.1.1 v.1.2 v.2.
Definition PairVU (v : val * val)                                 := PairVC v.1 v.2.
Definition InjLVU (v : val)                                       := InjLVC v.
Definition InjRVU (v : val)                                       := InjRVC v.


Section constructor_measurability.
  (** For each uncurried constructor ConstrU, prove:
          ConstrU_measurable : measurable_fun setT ConstrU
   *)

  Local Lemma MZ {d} {T : measurableType d} (S : set T)  : S = set0 -> measurable S.
  Proof. by move=>->; apply measurable0. Qed.
  Hint Resolve MZ : measlang.

  Local Lemma MT {d} {T : measurableType d} (S : set T)  : S = setT -> measurable S.
  Proof. by move=>->; eapply @measurableT. Qed.
  Hint Resolve MT : measlang.

  Local Lemma Prod2Decomp {T1 T2 T : Type} (P1 : set T1) (P2 : set T2) (FU : T1 * T2 -> T) :
    (∀ {a b c d}, curry FU a b = curry FU c d -> b = d) ->
    [set t | (exists2 x : T1, P1 x & exists2 y : T2, P2 y & (curry FU) x y = FU t) ] =
    [set t | (exists2 x : T1, True    & exists2 y : T2, P2 y & (curry FU) x y = FU t) ] `&`
    [set t | (exists2 x : T1, P1 x & exists2 y : T2, True    & (curry FU) x y = FU t) ].
  Proof.
    move=> R.
    apply/seteqP; split=> x/=.
    - move=> [a ? [b ? <-]].
      split; (exists a; [done|]; exists b; done).
    - move=> [[a ?] [b ?]] <- [c ? [d ?]] H.
      exists c; [done|]; exists b; [done|].
      rewrite <- H.
      f_equal.
      symmetry.
      apply (R _ _ _ _ H).
  Qed.

  Local Lemma Prod3Decomp {T1 T2 T3 T : Type} (P1 : set T1) (P2 : set T2) (P3 : set T3) (FU : T1 * T2 * T3 -> T) :
    (forall a b, FU a = FU b -> a = b) ->
    [set t | (exists2 x : T1, P1 x & exists2 y : T2, P2 y & exists2 z : T3, P3 z & (curry3 FU) x y z = FU t) ] =
    [set t | (exists2 x : T1, P1 x & exists2 y : T2, True    & exists2 z : T3, True    & (curry3 FU) x y z = FU t) ] `&`
    [set t | (exists2 x : T1, True    & exists2 y : T2, P2 y & exists2 z : T3, True    & (curry3 FU) x y z = FU t) ] `&`
    [set t | (exists2 x : T1, True    & exists2 y : T2, True    & exists2 z : T3, P3 z & (curry3 FU) x y z = FU t) ].
  Proof.
    move=> HI.
    rewrite /setI/=.
    apply/seteqP; split=> x/=.
    { move=> [w ?] [y ?] [z ?] <- //=.
      split.
      split.
      all: exists w; [done|].
      all: exists y; [done|].
      all: exists z; [done|].
      all: done. }
    { move=> [[+ +]+].
      move=> [y Hy] [? _] [? _] H1.
      move=> [? _] [z Hz] [? _] H2.
      move=> [? _] [? _] [w Hw] H3.
      exists y; [done|].
      exists z; [done|].
      exists w; [done|].
      apply HI in H1, H2, H3.
      unfold curry3.
      f_equal.
      destruct x as [[? ?] ?].
      inversion H1.
      inversion H2.
      inversion H3.
      done. }
  Qed.



  (** The bulk of the trivial case work for the constructor measurability:
      Proves
        'measurable [set t | (exists2 x : ..., S x & A x = B t)]
      when A and B are different constructors *)
  Ltac ctor_triv_case :=
    apply MZ; apply /predeqP =>y /=; split; [| by move=>?];
    (by move=> ?//) +
    (by move=> [?]//) +
    (by move=> [??[???]]//) +
    (by move=> [??[??[???]]]//).

  Hint Resolve measurability : measlang.

  (** Base_lit constructors, uncurried *)
  Lemma LitIntU_measurable : measurable_fun setT LitIntU.
  Proof. into_gen_measurable. by rewrite //=. Qed.
  Hint Resolve LitIntU_measurable : measlang.

  Lemma LitBoolU_measurable : measurable_fun setT LitBoolU.
  Proof. into_gen_measurable. by rewrite //=. Qed.
  Hint Resolve LitBoolU_measurable : measlang.

  Lemma LitLocU_measurable : measurable_fun setT LitLocU.
  Proof. into_gen_measurable. by rewrite //=. Qed.
  Hint Resolve LitLocU_measurable : measlang.

  Lemma LitLblU_measurable : measurable_fun setT LitLblU.
  Proof. into_gen_measurable. by rewrite //=. Qed.
  Hint Resolve LitLblU_measurable : measlang.


  Lemma LitRealU_measurable : measurable_fun setT LitRealU.
  Proof.
    into_gen_measurable.
    move=> ? [? [D H <-] <-] /=.
    rewrite setTI.
    destruct D; rewrite /preimage/=.
    6: { simpl in H.
         eapply eq_measurable; [ by apply H |].
         apply/seteqP; split=>?//=.
         - by move=>[??][<-].
         - by move=>?; eexists _; eauto.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve LitRealU_measurable : measlang.

  (** Expr Constructors: Each *C function is (.. * ... * ...) / expr -measurable *)
  Lemma ValU_measurable : measurable_fun setT ValU.
  Proof.
    into_gen_measurable.
    move=> ? [? [D H <-] <-] /=.
    rewrite setTI.
    destruct D; rewrite /preimage/=.
    1: { apply sub_sigma_algebra.
         exists v; [done|].
         apply/seteqP; split=>?//=.
         - by move=>?; eexists _; eauto.
         - by move=>[??[<-]].
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve ValU_measurable : measlang.

  Lemma VarU_measurable : measurable_fun setT VarU.
  Proof. into_gen_measurable. by rewrite //=. Qed.
  Hint Resolve VarU_measurable : measlang.


  Lemma RecU_measurable : measurable_fun setT RecU.
  Proof.
    into_gen_measurable.
    move=> ? [? [D H <-] <-] /=.
    rewrite setTI.
    rewrite /preimage/=.
    destruct D.
    3: {
      simpl.
      suffices -> :
        [set t | (exists2 x0 : expr_T, expr_ST D x0 & Rec f x x0 = RecU t)] =
        [set t | (exists2 x0 : expr_T, expr_ST D x0 & t.2 = x0)] `&`
        ( [set t | t.1.1 = f ] `&`
          [set t | t.1.2 = x ]).
      { apply measurableI.
        - apply sub_sigma_algebra.
          rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
          right.
          simpl in H.
          exists (expr_ST D).
          { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D. }
          rewrite setTI.
          apply/predeqP; simpl; split.
          + by move=>?; exists x0.2.
          + by move=>[??]->.
        - apply measurableI.
          + apply sub_sigma_algebra.
            rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
            left.
            simpl in H.
            exists [set t | t.1 = f].
            { apply sub_sigma_algebra.
              simpl.
              left.
              exists [set f]. { by rewrite /measurable/=/discr_measurable/=. }
              by rewrite setTI /=. }
            by rewrite setTI /=.
          + apply sub_sigma_algebra.
            rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
            left.
            simpl in H.
            exists [set t | t.2 = x].
            { apply sub_sigma_algebra.
              simpl.
              right.
              exists [set x]. { by rewrite /measurable/=/discr_measurable/=. }
              by rewrite setTI /=. }
            by rewrite setTI /=.
      }
      apply/seteqP; split=> y/=.
      - move=> [a ? [<- <- <-]].
        split; [|by intuition].
        by exists a.
      - move=> [[e ?] He [<- <-]].
        exists e; [done|].
        by destruct y; rewrite <-He; simpl; intuition.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve RecU_measurable : measlang.

  Lemma AppU_measurable : measurable_fun setT AppU.
  Proof.
    into_gen_measurable.
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    4: {
         simpl in HD.
         destruct HD as [HD0 HD1].
         rewrite Prod2Decomp.
         { apply measurableI.
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             right.
             exists (expr_ST D2).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D2. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??][?<-]].
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             left.
             exists (expr_ST D1).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D1. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??[<- ?]]].
        }
        by move=>????[??]//.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve AppU_measurable : measlang.

  Lemma UnOpU_measurable : measurable_fun setT UnOpU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    5: {
      simpl.
      suffices -> :
        [set t | (exists2 x : expr_T, expr_ST D x & UnOp op x = UnOpU t)] =
        [set t | exists x0 : expr_T, exists o, (expr_ST D x0 /\ UnOp o x0 = UnOpU t)] `&`
        [set t | t.1 = op ].
      { apply measurableI.
        + rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
          apply sub_sigma_algebra.
          simpl in HD.
          simpl.
          right.
          exists (expr_ST D).
          { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D. }
          rewrite setTI /=.
          apply/seteqP; split=> x/=.
          + move=>?. exists x.2. exists x.1. split; [done|]. by intuition.
          + move=> [? [? [? H]]].
            inversion H.
            by rewrite <- H2.
        + rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
          apply sub_sigma_algebra.
          simpl.
          left.
          exists [set op]. { by rewrite /measurable/=/discr_measurable/=. }
          by rewrite setTI /=. }
      apply/seteqP; split=> y/=.
      - move=> [a ? [-> Ha]]; split; [|done].
        exists a. exists y.1. split; [done|].
        by rewrite Ha //=.
      - move=> [[a [? [? Ha]]] <-].
        simpl in HD.
        exists a; [done|].
        destruct y; simpl.
        rewrite /UnOpU/UnOpC/=.
        f_equal.
        inversion Ha. by intuition.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve UnOpU_measurable : measlang.

  Lemma BinOpU_measurable : measurable_fun setT BinOpU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    6: {
      suffices -> :
         [set t | (exists2 x : expr_T, expr_ST D1 x & exists2 y : expr_T, expr_ST D2 y & BinOp op x y = BinOpU t)] =
        ([set t | (exists2 x : expr_T, expr_ST D1 x & exists2 y : expr_T, True            & exists op, BinOp op x y = BinOpU t)] `&`
         [set t | (exists2 x : expr_T, True            & exists2 y : expr_T, expr_ST D2 y & exists op, BinOp op x y = BinOpU t)]) `&`
        [set t | t.1.1 = op ].
      { simpl in HD.
        destruct HD as [HD0 HD1].
        apply measurableI.
        apply measurableI.
        - apply sub_sigma_algebra; rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
          left.
          exists (setT `*` (expr_ST D1)).
          { apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=.
            right.
            exists (expr_ST D1). { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D1.  }
            rewrite setTI.
            rewrite /setX/=.
            apply/seteqP; split=> x/=; by intuition.
          }
          rewrite setTI.
          apply/seteqP; split=> x/=.
          + move=> [? ?].
            exists x.1.2; [done|].
            exists x.2; [done|].
            exists x.1.1.
            destruct x as [[??]?].
            by intuition.
          + move=> [??][??][?][?<-?].
            by intuition.
        - apply sub_sigma_algebra; rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
          right.
          exists (expr_ST D2).
          { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D2. }
          rewrite setTI.
          apply/seteqP; split=> y/=.
          + move=> H.
            exists y.1.2; [done|].
            exists y.2; [done|].
            exists y.1.1.
            destruct y as [yy yyy]; destruct yy; simpl.
            by rewrite /BinOpU/=.
          + by move=> [? _ [? ?]] [? [? ?]] <-.
        - apply sub_sigma_algebra; rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
          left.
          exists ([set op] `*` setT).
          { apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=.
            left.
            exists [set op]. { by rewrite /discr_measurable/measurable/=/expr_cyl/=. }
            rewrite setTI.
            rewrite /setX/=.
            apply/seteqP; split=> x/=; by intuition.
          }
          rewrite setTI.
          apply/seteqP; split=> x/=.
          + move=> [? ?]; done.
          + by intuition.
      }
      apply/seteqP; split=> y/=.
      - move=> [? W][? Z][A B C].
        rewrite B in W.
        rewrite C in Z.
        split; [split|].
        + exists y.1.2; [done|]; exists y.2; [done|]; exists y.1.1; done.
        + exists y.1.2; [done|]; exists y.2; [done|]; exists y.1.1; done.
        + by intuition.
      - move=> [[[? p][??]]].
        move=> [?[? H1 ?]].
        rewrite H1 in p.
        move=> [??][? p2][?[?? H2]]Hop.
        rewrite H2 in p2.
        exists y.1.2; [done|].
        exists y.2; [done|].
        destruct y as [[??]?].
        rewrite /BinOpU/BinOpC/=.
        simpl in Hop.
        by rewrite Hop.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve BinOpU_measurable : measlang.

  Lemma IfU_measurable : measurable_fun setT IfU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    7: {
      simpl in HD.
      destruct HD as [HD0 [HD1 HD2]].
      rewrite Prod3Decomp.
      apply measurableI.
      apply measurableI.
      - apply sub_sigma_algebra.
        rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
        left.
        exists (expr_ST D1 `*` setT).
        { apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=.
          left.
          exists (expr_ST D1). { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D1.  }
          rewrite setTI.
          rewrite /setX/=.
          apply/seteqP; split=> x/=; by intuition.
        }
        rewrite setTI.
        apply/seteqP; split=> x/=.
        + move=> [? _].
          exists x.1.1; [done|].
          exists x.1.2; [done|].
          exists x.2; [done|].
          destruct x as [[??]?].
          by intuition.
        + move=> [??][??][??][<-]??.
          by intuition.
      - apply sub_sigma_algebra.
        rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
        left.
        exists (setT `*` expr_ST D2).
        { apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=.
          right.
          exists (expr_ST D2). { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D2. }
          rewrite setTI.
          rewrite /setX/=.
          apply/seteqP; split=> x/=; by intuition.
        }
        rewrite setTI.
        apply/seteqP; split=> x/=.
        + move=> [? ?].
          exists x.1.1; [done|].
          exists x.1.2; [done|].
          exists x.2; [done|].
          destruct x as [[??]?].
          by intuition.
        + move=> [??][??][??][? <- ?].
          by intuition.
      - apply sub_sigma_algebra.
        rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
        right.
        exists (expr_ST D3).  { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D3. }
        rewrite setTI.
        apply/seteqP; split=> x/=.
        + move=>?.
          exists x.1.1; [done|].
          exists x.1.2; [done|].
          exists x.2; [done|].
          destruct x as [[??]?].
          by intuition.
        + move=> [??][??][??][??<-].
          by intuition.
        + by move=> [[??]?] [[??]?] [-> -> ->].
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve IfU_measurable : measlang.

  Lemma PairU_measurable : measurable_fun setT PairU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    8: {
         simpl in HD.
         destruct HD as [HD0 HD1].
         rewrite Prod2Decomp.
         { apply measurableI.
           - apply sub_sigma_algebra.
             right.
             eexists _; [by apply sub_sigma_algebra; exists D2 |].
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??][?<-]].
           - apply sub_sigma_algebra.
             left.
             eexists _; [by apply sub_sigma_algebra; exists D1 |].
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??[<- ?]]].
        }
        by move=>????[??]//.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve PairU_measurable : measlang.

  Lemma FstU_measurable : measurable_fun setT FstU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    9: {
         apply sub_sigma_algebra.
         rewrite /expr_cyl/=.
         simpl in HD.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve FstU_measurable : measlang.

  Lemma SndU_measurable : measurable_fun setT SndU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    10: {
         apply sub_sigma_algebra.
         rewrite /expr_cyl/=.
         simpl in HD.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve SndU_measurable : measlang.

  Lemma InjLU_measurable : measurable_fun setT InjLU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    11: {
         apply sub_sigma_algebra.
         rewrite /expr_cyl/=.
         simpl in HD.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve InjLU_measurable : measlang.

  Lemma InjRU_measurable : measurable_fun setT InjRU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    12: {
         apply sub_sigma_algebra.
         rewrite /expr_cyl/=.
         simpl in HD.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve InjRU_measurable : measlang.

  Lemma CaseU_measurable : measurable_fun setT CaseU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    13: {
      simpl in HD.
      destruct HD as [HD0 [HD1 HD2]].
      rewrite Prod3Decomp.
      apply measurableI.
      apply measurableI.
      - apply sub_sigma_algebra.
        rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
        left.
        exists (expr_ST D1 `*` setT).
        { apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=.
          left.
          exists (expr_ST D1). { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D1.  }
          rewrite setTI.
          rewrite /setX/=.
          apply/seteqP; split=> x/=; by intuition.
        }
        rewrite setTI.
        apply/seteqP; split=> x/=.
        + move=> [? _].
          exists x.1.1; [done|].
          exists x.1.2; [done|].
          exists x.2; [done|].
          destruct x as [[??]?].
          by intuition.
        + move=> [??][??][??][<-]??.
          by intuition.
      - apply sub_sigma_algebra.
        rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
        left.
        exists (setT `*` expr_ST D2).
        { apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=.
          right.
          exists (expr_ST D2). { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D2. }
          rewrite setTI.
          rewrite /setX/=.
          apply/seteqP; split=> x/=; by intuition.
        }
        rewrite setTI.
        apply/seteqP; split=> x/=.
        + move=> [? ?].
          exists x.1.1; [done|].
          exists x.1.2; [done|].
          exists x.2; [done|].
          destruct x as [[??]?].
          by intuition.
        + move=> [??][??][??][? <- ?].
          by intuition.
      - apply sub_sigma_algebra.
        rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
        right.
        exists (expr_ST D3).  { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D3. }
        rewrite setTI.
        apply/seteqP; split=> x/=.
        + move=>?.
          exists x.1.1; [done|].
          exists x.1.2; [done|].
          exists x.2; [done|].
          destruct x as [[??]?].
          by intuition.
        + move=> [??][??][??][??<-].
          by intuition.
        + by move=> [[??]?] [[??]?] [-> -> ->].
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve CaseU_measurable : measlang.

  Lemma AllocNU_measurable : measurable_fun setT AllocNU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    14: {
         simpl in HD.
         destruct HD as [HD0 HD1].
         rewrite Prod2Decomp.
         { apply measurableI.
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             right.
             exists (expr_ST D2).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D2. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??][?<-]].
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             left.
             exists (expr_ST D1).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D1. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??[<- ?]]].
        }
        by move=>????[??]//.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve AllocNU_measurable : measlang.

  Lemma LoadU_measurable : measurable_fun setT LoadU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    15: {
         apply sub_sigma_algebra.
         rewrite /expr_cyl/=.
         simpl in HD.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve LoadU_measurable : measlang.

  Lemma StoreU_measurable : measurable_fun setT StoreU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    16: {
         simpl in HD.
         destruct HD as [HD0 HD1].
         rewrite Prod2Decomp.
         { apply measurableI.
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             right.
             exists (expr_ST D2).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D2. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??][?<-]].
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             left.
             exists (expr_ST D1).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D1. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??[<- ?]]].
        }
        by move=>????[??]//.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve StoreU_measurable : measlang.

  Lemma AllocTapeU_measurable : measurable_fun setT AllocTapeU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    17: {
         apply sub_sigma_algebra.
         rewrite /expr_cyl/=.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve AllocTapeU_measurable : measlang.

  Lemma RandU_measurable : measurable_fun setT RandU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    18: {
         simpl in HD.
         destruct HD as [HD0 HD1].
         rewrite Prod2Decomp.
         { apply measurableI.
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             right.
             exists (expr_ST D2).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D2. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??][?<-]].
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             left.
             exists (expr_ST D1).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D1. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??[<- ?]]].
        }
        by move=>????[??]//.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve RandU_measurable : measlang.

  (*
  Lemma AllocUTapeU_measurable : measurable_fun setT AllocUTapeU.
  *)

  Lemma UrandU_measurable : measurable_fun setT UrandU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    20: {
         apply sub_sigma_algebra.
         rewrite /expr_cyl/=.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve UrandU_measurable : measlang.

  Lemma TickU_measurable : measurable_fun setT TickU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    21: {
         apply sub_sigma_algebra.
         rewrite /expr_cyl/=.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve TickU_measurable : measlang.

  (** Val constructors *)

  Lemma LitVU_measurable : measurable_fun setT LitVU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    1: {
         apply sub_sigma_algebra.
         rewrite /base_lit_cyl/=.
         exists l; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve LitVU_measurable : measlang.

  Lemma RecVU_measurable : measurable_fun setT RecVU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    2: {
      simpl.
      suffices -> :
        [set t | (exists2 x0 : expr_T, expr_ST e x0 & RecV f x x0 = RecVU t)] =
        [set t | (exists2 x0 : expr_T, expr_ST e x0 & t.2 = x0)] `&`
        ( [set t | t.1.1 = f ] `&`
          [set t | t.1.2 = x ]).
      { apply measurableI.
        - apply sub_sigma_algebra.
          rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
          right.
          simpl in HD.
          eexists _.
          2: {
            rewrite setTI.
            apply/predeqP; simpl; split.
            + by move=>?; exists x0.2.
            + by move=>[??]->.
          }
          1: {
            apply sub_sigma_algebra.
            rewrite /measurable/=/expr_cyl/=.
            by exists e.
          }
        - apply measurableI.
          + apply sub_sigma_algebra.
            rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
            left.
            simpl in HD.
            exists [set t | t.1 = f].
            { apply sub_sigma_algebra.
              simpl.
              left.
              exists [set f]. { by rewrite /measurable/=/discr_measurable/=. }
              by rewrite setTI /=. }
            by rewrite setTI /=.
          + apply sub_sigma_algebra.
            rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
            left.
            simpl in HD.
            exists [set t | t.2 = x].
            { apply sub_sigma_algebra.
              simpl.
              right.
              exists [set x]. { by rewrite /measurable/=/discr_measurable/=. }
              by rewrite setTI /=. }
            by rewrite setTI /=.
      }
      apply/seteqP; split=> y/=.

      - move=> [a ? [b ? <-]].
        split.
        + exists a; done.
        + by intuition.
      - move=> [[? ?] H] [<- <-].
        exists y.2.
        + by rewrite H.
        + destruct y as [[??]?]; by rewrite /=.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve RecVU_measurable : measlang.

  Lemma PairVU_measurable : measurable_fun setT PairVU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    3: {
         simpl in HD.
         destruct HD as [HD0 HD1].
         rewrite Prod2Decomp.
         { apply measurableI.
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             right.
             exists (val_ST D2).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D2. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??][?<-]].
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             left.
             exists (val_ST D1).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D1. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??[<- ?]]].
        }
        by move=>????[??]//.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve PairVU_measurable : measlang.

  Lemma InjLVU_measurable : measurable_fun setT InjLVU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    4: {
         apply sub_sigma_algebra.
         rewrite /base_lit_cyl/=.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve InjLVU_measurable : measlang.

  Lemma InjRVU_measurable : measurable_fun setT InjRVU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    5: {
         apply sub_sigma_algebra.
         rewrite /base_lit_cyl/=.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve InjRVU_measurable : measlang.

End constructor_measurability.
