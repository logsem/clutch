Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From stdpp Require Import binders.
From mathcomp Require Import boolp classical_sets.
From mathcomp.analysis Require Import measure.
From clutch.common Require Export locations.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude types.
Set Warnings "hiding-delimiting-key".

Local Open Scope classical_set_scope.

(** Uncurried constructors: These ones can be shown to be measurable directly *)

Notation LitIntU     := LitIntC.
Notation LitBoolU    := LitBoolC.
Notation LitUnitU    := LitUnitC.
Notation LitLocU     := LitLocC.
Notation LitLblU     := LitLblC.
Notation LitRealU    := LitRealC.

Notation ValU        := ValC.
Notation VarU        := VarC.
Notation RecU        := (uncurry3 RecC).
Notation AppU        := (uncurry AppC).
Notation UnOpU       := (uncurry UnOpC).
Notation BinOpU      := (uncurry3 BinOpC).
Notation IfU         := (uncurry3 IfC).
Notation PairU       := (uncurry PairC).
Notation FstU        := FstC.
Notation SndU        := SndC.
Notation InjLU       := InjLC.
Notation InjRU       := InjRC.
Notation CaseU       := (uncurry3 CaseC).
Notation AllocU      := AllocC.
Notation LoadU       := LoadC.
Notation StoreU      := (uncurry StoreC).
Notation AllocTapeU  := AllocTapeC.
Notation RandU       := (uncurry RandC).
Notation AllocUTapeU := AllocUTapeC.
Notation UrandU      := URandC.
Notation TickU       := TickC.

Notation LitVU       := LitVC.
Notation RecVU       := (uncurry3 RecVC).
Notation PairVU      := (uncurry PairVC).
Notation InjLVU      := InjLVC.
Notation InjRVU      := InjRVC.


Section constructor_measurability.

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
  Lemma LitIntU_meas_fun : measurable_fun setT LitIntU.
  Proof. into_gen_measurable. by rewrite //=. Qed.
  Hint Resolve LitIntU_meas_fun : measlang.
  Hint Resolve LitIntU_meas_fun : mf_fun.

  Lemma LitBoolU_meas_fun : measurable_fun setT LitBoolU.
  Proof. into_gen_measurable. by rewrite //=. Qed.
  Hint Resolve LitBoolU_meas_fun : measlang.
  Hint Resolve LitBoolU_meas_fun : mf_fun.

  Lemma LitLocU_meas_fun : measurable_fun setT LitLocU.
  Proof. into_gen_measurable. by rewrite //=. Qed.
  Hint Resolve LitLocU_meas_fun : measlang.
  Hint Resolve LitLocU_meas_fun : mf_fun.

  Lemma LitLblU_meas_fun : measurable_fun setT LitLblU.
  Proof. into_gen_measurable. by rewrite //=. Qed.
  Hint Resolve LitLblU_meas_fun : measlang.
  Hint Resolve LitLblU_meas_fun : mf_fun.


  Lemma LitRealU_meas_fun : measurable_fun setT LitRealU.
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
  Hint Resolve LitRealU_meas_fun : measlang.
  Hint Resolve LitRealU_meas_fun : mf_fun.

  (** Expr Constructors: Each *C function is (.. * ... * ...) / expr -measurable *)

  Local Ltac expr_ctor_meas_fun_cases :=
    into_gen_measurable;
    rewrite /preimage_class/subset//=;
    move=> S //= [_ [+ + <-] <-];
    move=> [+|+|+ + +|+ + |+ +|+ + +|+ + +|+ +|+|+|+|+|+ + +|+|+|+ +|+|+ +||+|+];
    rewrite /preimage/=.

  Local Ltac ctor_2_separate_preimage := rewrite Prod2Decomp; last (by move=>????[??]//).

  Ltac ctor_triv_case' :=
    ( (by move=> ?//) +
      (by move=> [?]//) +
      (by move=> [??[???]]//) +
      (by move=> [??[??[???]]]//)).

  Ltac ctor_triv_cases_2 :=
    intros; apply MZ; apply /predeqP =>[+] /=;
    move=>[??];
    split; [| by move=>?]; rewrite /AppU/uncurry//=; move=>[_+];
    ctor_triv_case'.


  Lemma ValU_meas_fun : measurable_fun setT ValU.
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
  Hint Resolve ValU_meas_fun : measlang.
  Hint Resolve ValU_meas_fun : mf_fun.

  Lemma VarU_meas_fun : measurable_fun setT VarU.
  Proof. into_gen_measurable. by rewrite //=. Qed.
  Hint Resolve VarU_meas_fun : measlang.
  Hint Resolve VarU_meas_fun : mf_fun.


  Lemma RecU_meas_fun : measurable_fun setT RecU.
  Proof.
    have -> : RecU = (fun x => RecC x.1.1 x.1.2 x.2) by
      apply functional_extensionality; intros [[??]?]. rewrite /RecU//=.
    into_gen_measurable.
    move=> ? [? [D H <-] <-] /=.
    rewrite setTI.
    rewrite /preimage/=.
    destruct D.
    3: {
      simpl.
      suffices -> :
        [set t | (exists2 x0 : expr_T, expr_ST D x0 & Rec f x x0 = RecC t.1.1 t.1.2 t.2)] =
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
  Hint Resolve RecU_meas_fun : measlang.
  Hint Resolve RecU_meas_fun : mf_fun.

  Lemma AppU_meas_fun : measurable_fun setT AppU.
  Proof. (* Note: All 2-argument proofs in this file are identical to AppU *)
    expr_ctor_meas_fun_cases.
    all: try by ctor_triv_cases_2.
    intros D0 D1 [??]; rewrite setTI.
    ctor_2_separate_preimage; apply measurableI.
    - apply sub_sigma_algebra.
      right.
      eexists (expr_ST _); [by apply sub_sigma_algebra; eexists _ |].
      rewrite setTI.
      apply/seteqP; split=> x/=; rewrite //=; destruct x.
      + by eexists _; [done|]; eexists _; [done|]; rewrite //=.
      + by move=> [??[??][?<-]].
     - apply sub_sigma_algebra.
       rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
       left.
       exists (expr_ST D0).
       { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D0. }
       rewrite setTI.
       apply/seteqP; split=> x/=; destruct x.
       + by move=>?; eexists _; [done|]; eexists _; done.
       + by move=> [??[??[<- ?]]].
  Qed.
  Hint Resolve AppU_meas_fun : measlang.
  Hint Resolve AppU_meas_fun : mf_fun.

  Lemma UnOpU_meas_fun : measurable_fun setT UnOpU.
  Proof.
    expr_ctor_meas_fun_cases.
    all: try by ctor_triv_cases_2.
    intros op D ?; rewrite setTI.
    simpl.
    suffices -> :
      [set t | (exists2 x : expr_T, expr_ST D x & UnOp op x = UnOpU t)] =
      [set t | exists x0 : expr_T, exists o, (expr_ST D x0 /\ UnOp o x0 = UnOpU t)] `&`
      [set t | t.1 = op ].
    { apply measurableI.
      + rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
        apply sub_sigma_algebra.
        simpl.
        right.
        exists (expr_ST D).
        { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D. }
        rewrite setTI /=.
        apply/seteqP; split=> x/=; destruct x; simpl.
        + by move=>?; eexists _; exists d; split; [done|].
        + move=> [? [? [? H]]].
          inversion H.
          by rewrite <- H2.
      + rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
        apply sub_sigma_algebra.
        simpl.
        left.
        exists [set op]. { by rewrite /measurable/=/discr_measurable/=. }
        by rewrite setTI /=. }
    apply/seteqP; split=> y/=; destruct y.
    - move=> [??]; move=> [+]; move=>-><-//=; split; [|done].
      eexists _; eexists _; done.
    - move=> [[?[?[?+]]]+] //=.
      move=>[+]; move=><-<-//=; move=><-//=.  eexists _; done.
  Qed.
  Hint Resolve UnOpU_meas_fun : measlang.
  Hint Resolve UnOpU_meas_fun : mf_fun.

  Lemma BinOpU_meas_fun : measurable_fun setT BinOpU.
  Proof.
    have -> : BinOpU = (fun x => BinOpC x.1.1 x.1.2 x.2) by
      apply functional_extensionality; intros [[??]?]; rewrite //=.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [_ [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    6: {
      suffices -> :
         [set t | (exists2 x : expr_T, expr_ST D1 x & exists2 y : expr_T, expr_ST D2 y & BinOp op x y = BinOpC t.1.1 t.1.2 t.2)] =
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
          + destruct x as [[x1 x2] x3]; simpl.
            move=> [??][??][?][?<-?].
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
          + destruct y as [[??]?].
            by move=> [? _ [? ?]] [? [? ?]] <-.
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
        + exists y.1.2; [done|]; exists y.2; [done|]; exists y.1.1. destruct y as [[??]?]; done.
        + exists y.1.2; [done|]; exists y.2; [done|]; exists y.1.1. destruct y as [[??]?]; done.
        + by intuition.
      - destruct y as [[y1 y2]y3]. simpl.
        move=> [[[? p][??]]].
        move=> [?[? H1 ?]].

        rewrite H1 in p.
        move=> [??][? p2][?[?? H2]]Hop.
        rewrite H2 in p2.
        exists y2; [done|].
        exists y3; [done|].
        rewrite /BinOpU/BinOpC/=.
        simpl in Hop.
        by rewrite Hop.
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve BinOpU_meas_fun : measlang.
  Hint Resolve BinOpU_meas_fun : mf_fun.

  Lemma IfU_meas_fun : measurable_fun setT IfU.
  Proof.
    have -> : IfU = (fun x => IfC x.1.1 x.1.2 x.2) by
      apply functional_extensionality; intros [[??]?]; rewrite //=.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [_ [D HD <-] <-]; rewrite setTI.
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
        + destruct x as [[??]?].
          move=> [??][??][??][<-]??.
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
        + destruct x as [[??]?].
          move=> [??][??][??][? <- ?].
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
        + destruct x as [[??]?].
          move=> [??][??][??][??<-].
          by intuition.
        + by move=> [[??]?] [[??]?] [-> -> ->].
    }
    all: by ctor_triv_case.
  Qed.
  Hint Resolve IfU_meas_fun : measlang.
  Hint Resolve IfU_meas_fun : mf_fun.

  Lemma PairU_meas_fun : measurable_fun setT PairU.
  Proof. (* Note: All 2-argument proofs in this file are identical to AppU *)
    expr_ctor_meas_fun_cases.
    all: try by ctor_triv_cases_2.
    intros D0 D1 [??]; rewrite setTI.
    ctor_2_separate_preimage; apply measurableI.
    - apply sub_sigma_algebra.
      right.
      eexists (expr_ST _); [by apply sub_sigma_algebra; eexists _ |].
      rewrite setTI.
      apply/seteqP; split=> x/=; rewrite //=; destruct x.
      + by eexists _; [done|]; eexists _; [done|]; rewrite //=.
      + by move=> [??[??][?<-]].
     - apply sub_sigma_algebra.
       rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
       left.
       exists (expr_ST D0).
       { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D0. }
       rewrite setTI.
       apply/seteqP; split=> x/=; destruct x.
       + by move=>?; eexists _; [done|]; eexists _; done.
       + by move=> [??[??[<- ?]]].
  Qed.
  Hint Resolve PairU_meas_fun : measlang.
  Hint Resolve PairU_meas_fun : mf_fun.

  Lemma FstU_meas_fun : measurable_fun setT FstU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [_ [D HD <-] <-]; rewrite setTI.
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
  Hint Resolve FstU_meas_fun : measlang.
  Hint Resolve FstU_meas_fun : mf_fun.

  Lemma SndU_meas_fun : measurable_fun setT SndU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [_ [D HD <-] <-]; rewrite setTI.
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
  Hint Resolve SndU_meas_fun : measlang.
  Hint Resolve SndU_meas_fun : mf_fun.

  Lemma InjLU_meas_fun : measurable_fun setT InjLU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [_ [D HD <-] <-]; rewrite setTI.
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
  Hint Resolve InjLU_meas_fun : measlang.
  Hint Resolve InjLU_meas_fun : mf_fun.

  Lemma InjRU_meas_fun : measurable_fun setT InjRU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [_ [D HD <-] <-]; rewrite setTI.
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
  Hint Resolve InjRU_meas_fun : measlang.
  Hint Resolve InjRU_meas_fun : mf_fun.

  Lemma CaseU_meas_fun : measurable_fun setT CaseU.
  Proof.
    have -> : CaseU = (fun x => CaseC x.1.1 x.1.2 x.2) by
      apply functional_extensionality; intros [[??]?]; rewrite //=.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [_ [D HD <-] <-]; rewrite setTI.
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
  Hint Resolve CaseU_meas_fun : measlang.
  Hint Resolve CaseU_meas_fun : mf_fun.

  Lemma AllocU_meas_fun : measurable_fun setT AllocU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [_ [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    14: {
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
  Hint Resolve AllocU_meas_fun : measlang.
  Hint Resolve AllocU_meas_fun : mf_fun.

  Lemma LoadU_meas_fun : measurable_fun setT LoadU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [_ [D HD <-] <-]; rewrite setTI.
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
  Hint Resolve LoadU_meas_fun : measlang.
  Hint Resolve LoadU_meas_fun : mf_fun.

  Lemma StoreU_meas_fun : measurable_fun setT StoreU.
  Proof. (* Note: All 2-argument proofs in this file are identical to AppU *)
    expr_ctor_meas_fun_cases.
    all: try by ctor_triv_cases_2.
    intros D0 D1 [??]; rewrite setTI.
    ctor_2_separate_preimage; apply measurableI.
    - apply sub_sigma_algebra.
      right.
      eexists (expr_ST _); [by apply sub_sigma_algebra; eexists _ |].
      rewrite setTI.
      apply/seteqP; split=> x/=; rewrite //=; destruct x.
      + by eexists _; [done|]; eexists _; [done|]; rewrite //=.
      + by move=> [??[??][?<-]].
     - apply sub_sigma_algebra.
       rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
       left.
       exists (expr_ST D0).
       { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D0. }
       rewrite setTI.
       apply/seteqP; split=> x/=; destruct x.
       + by move=>?; eexists _; [done|]; eexists _; done.
       + by move=> [??[??[<- ?]]].
  Qed.
  Hint Resolve StoreU_meas_fun : measlang.
  Hint Resolve StoreU_meas_fun : mf_fun.

  Lemma AllocTapeU_meas_fun : measurable_fun setT AllocTapeU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [_ [D HD <-] <-]; rewrite setTI.
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
  Hint Resolve AllocTapeU_meas_fun : measlang.
  Hint Resolve AllocTapeU_meas_fun : mf_fun.

  Lemma RandU_meas_fun : measurable_fun setT RandU.
  Proof. (* Note: All 2-argument proofs in this file are identical to AppU *)
    expr_ctor_meas_fun_cases.
    all: try by ctor_triv_cases_2.
    intros D0 D1 [??]; rewrite setTI.
    ctor_2_separate_preimage; apply measurableI.
    - apply sub_sigma_algebra.
      right.
      eexists (expr_ST _); [by apply sub_sigma_algebra; eexists _ |].
      rewrite setTI.
      apply/seteqP; split=> x/=; rewrite //=; destruct x.
      + by eexists _; [done|]; eexists _; [done|]; rewrite //=.
      + by move=> [??[??][?<-]].
     - apply sub_sigma_algebra.
       rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
       left.
       exists (expr_ST D0).
       { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D0. }
       rewrite setTI.
       apply/seteqP; split=> x/=; destruct x.
       + by move=>?; eexists _; [done|]; eexists _; done.
       + by move=> [??[??[<- ?]]].
  Qed.
  Hint Resolve RandU_meas_fun : measlang.
  Hint Resolve RandU_meas_fun : mf_fun.

  (*
  Lemma AllocUTapeU_meas_fun : measurable_fun setT AllocUTapeU.
  *)

  Lemma UrandU_meas_fun : measurable_fun setT UrandU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [_ [D HD <-] <-]; rewrite setTI.
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
  Hint Resolve UrandU_meas_fun : measlang.
  Hint Resolve UrandU_meas_fun : mf_fun.

  Lemma TickU_meas_fun : measurable_fun setT TickU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [_ [D HD <-] <-]; rewrite setTI.
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
  Hint Resolve TickU_meas_fun : measlang.
  Hint Resolve TickU_meas_fun : mf_fun.

  (** Val constructors *)

  Lemma LitVU_meas_fun : measurable_fun setT LitVU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [_ [D HD <-] <-]; rewrite setTI.
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
  Hint Resolve LitVU_meas_fun : measlang.
  Hint Resolve LitVU_meas_fun : mf_fun.

  Lemma RecVU_meas_fun : measurable_fun setT RecVU.
  Proof.
    have -> : RecVU = (fun x => RecVC x.1.1 x.1.2 x.2) by
      apply functional_extensionality; intros [[??]?]; rewrite //=.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [_ [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    2: {
      simpl.
      suffices -> :
        [set t | (exists2 x0 : expr_T, expr_ST e x0 & RecV f x x0 = RecVC t.1.1 t.1.2 t.2)] =
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
  Hint Resolve RecVU_meas_fun : measlang.
  Hint Resolve RecVU_meas_fun : mf_fun.

  Lemma PairVU_meas_fun : measurable_fun setT PairVU.
  Proof.
    have -> : PairVU = (fun x => PairVC x.1 x.2) by
      apply functional_extensionality; intros [??]; rewrite //=.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [_ [D HD <-] <-]; rewrite setTI.
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
  Hint Resolve PairVU_meas_fun : measlang.
  Hint Resolve PairVU_meas_fun : mf_fun.

  Lemma InjLVU_meas_fun : measurable_fun setT InjLVU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [_ [D HD <-] <-]; rewrite setTI.
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
  Hint Resolve InjLVU_meas_fun : measlang.
  Hint Resolve InjLVU_meas_fun : mf_fun.

  Lemma InjRVU_meas_fun : measurable_fun setT InjRVU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [_ [D HD <-] <-]; rewrite setTI.
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
  Hint Resolve InjRVU_meas_fun : measlang.
  Hint Resolve InjRVU_meas_fun : mf_fun.

End constructor_measurability.
