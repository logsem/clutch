From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis RInt_gen AutoDerive Lub.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import indicators.
From clutch.eris.examples Require Import lazy_real.
Set Default Proof Using "Type*".
#[local] Open Scope R.
Import Hierarchy.
Import RiemannInt.
Import SF_seq.
Import Rbar.
Import RList.


(* foob2

Define sup and inf as filterlims

Define the upper and lower Darboux integrals analgously to the Coquelicot Riemann integral


  - Problem: Riemann_sum uses sample points (snd y), not enough for doing sup/inf instead of max/min

Definition is_RInt (f : R → V) (a b : R) (If : V) :=
  filterlim (fun ptd ⇒ scal (sign (b-a)) (Riemann_sum f ptd)) (Riemann_fine a b) (locally If).

-> Instead of Riemann_fine

Change "SF_sup_seq" to take any partition and just overwrite the points

*)

(** General Analysis *)

Definition Bounded (f : R → R) (a b : R) : Prop :=
  ∃ M : R, ∀ x, Rmin a b <= x <= Rmax a b → Rabs (f x) <= M.

Definition Bounded2 (f : R → R → R) (ax bx ay bye : R) : Prop :=
  ∃ M : R, ∀ x y, Rmin ax bx <= x <= Rmax ax bx → Rmin ay bye <= y <= Rmax ay bye → Rabs (f x y) <= M.

Definition FunLe (f g : R → R) (a b : R) : Prop :=
  ∀ x, Rmin a b <= x <= Rmax a b → f x <= g x.

Definition FunLe2 (f g : R → R → R) (ax bx ay bye : R) : Prop :=
  ∀ x y, Rmin ax bx <= x <= Rmax ax bx → Rmin ay bye <= y <= Rmax ay bye → f x y <= g x y.

Lemma Inf_fct_mono {a b xa xb} {f g} (Hfg : FunLe f g xa xb) (Hle : a <= b) :
  Inf_fct f a b <= Inf_fct g a b.
Proof. Admitted.

Lemma Sup_fct_mono {a b xa xb} {f g} (Hfg : FunLe f g xa xb) (Hle : a <= b) :
  Sup_fct f a b <= Sup_fct g a b.
Proof. Admitted.

Definition RleR : ssrbool.rel R :=
  fun r1 r2 => ssrbool.is_left (Rle_lt_dec r1 r2).

(* In order to sort a list:
Check path.sort RleR. *)


(** 1D Darboux Sums *)

Section Darboux_sum.

(* Darboux step functions: hijacks the "sample point" field to store partition values instead. *)
Definition Darboux_seq := @SF_seq R.

(* a :: L ++ [b] is a partition of the interval [a, b] *)
Record Part_wf (a b : R) (L : list R) : Prop := {
    part_ord : sorted Rle (a :: L ++ (cons b nil));
}.

(* P is a step function on the interval [a, b] *)
Record Darboux_wf (P : Darboux_seq) (a b : R) : Prop := {
    (* The partition starts with a and ends with b *)
    darb_left : SF_h P = a;
    darb_right : seq.last (SF_h P) (seq.unzip1 (SF_t P)) = b;
    (* The middle part is a wf partition on [a, b] *)
    darb_part : Part_wf a b (seq.belast (SF_h P) (seq.unzip1 (SF_t P)));
}.


(* Construct the upper step function for a given step function *)
Definition Darboux_sup_seq (f : R → R) L : Darboux_seq :=
  SF_seq_f2 (fun x y => real $ Sup_fct f x y) L.

(* Construct the lower step function for a given step function *)
Definition Darboux_inf_seq (f : R → R) L : Darboux_seq :=
  SF_seq_f2 (fun x y => real $ Inf_fct f x y)  L.

(* Compat: a Darboux sequence that is pointwise greater than the given step function P *)
Definition Darboux_raise_seq (f : R → R) (P : @SF_seq R) :=
  Darboux_sup_seq f (SF_lx P).

(* Compat: a Darboux sequence that is pointwise lesser than the given step function P *)
Definition Darboux_lower_seq (f : R → R) (P : @SF_seq R) :=
  Darboux_inf_seq f (SF_lx P).

(* Compat: a Darboux sequence that gives an equal Darboux sum to the Riemann sum of f on ptd *)
Definition Darboux_seq_of_Riemann (f : R → R) (ptd : @SF_seq R) : Darboux_seq :=
  SF_map f ptd.

(* Darboux sums *)
Definition Darboux_sum (ptd : Darboux_seq) : R :=
  seq.foldr plus zero (seq.pairmap (fun x y => scal (fst y - fst x) (snd y)) (SF_h ptd, zero) (SF_t ptd)).

Lemma Riemann_pairmap_junk (x x' : R) {L} {ptd : @SF_seq R} :
  (seq.pairmap (λ x y : R * R, scal (y.1 - x.1) (y.2)) (SF_h ptd, x) L) =
  (seq.pairmap (λ x y : R * R, scal (y.1 - x.1) (y.2)) (SF_h ptd, x') L).
Proof. induction L; rewrite //=. Qed.

(* Riemann sums can be converted into Darboux sums *)
Lemma Darboux_Riemann_compat (f : R → R) (ptd : @SF_seq R) :
   Riemann_sum f ptd = Darboux_sum (Darboux_seq_of_Riemann f ptd).
Proof.
  rewrite /Riemann_sum /Darboux_sum /Darboux_seq_of_Riemann //=.
  have X :=
    Rcomplements.pairmap_map (λ x y : R * R, scal (y.1 - x.1) (y.2))
      (λ x : R * R, (x.1, f x.2)) (SF_t ptd) (SF_h ptd, zero).
  rewrite //= in X. rewrite //=.
  replace
    (@seq.foldr R R (@plus (ModuleSpace.AbelianMonoid R_Ring R_ModuleSpace))
       (@zero (ModuleSpace.AbelianMonoid R_Ring R_ModuleSpace))
       (@seq.pairmap (prod R R) R
          (fun x y : prod R R => @scal R_Ring R_ModuleSpace (Rminus (@fst R R y) (@fst R R x)) (@snd R R y))
          (@pair R R (@SF_h R ptd) (@zero (ModuleSpace.AbelianMonoid R_Ring R_ModuleSpace)))
          (@seq.map (prod R R) (prod R R) (fun x : prod R R => @pair R R (@fst R R x) (f (@snd R R x))) (@SF_t R ptd)))) with
    (@seq.foldr R R (@plus (ModuleSpace.AbelianMonoid R_Ring R_ModuleSpace))
       (@zero (ModuleSpace.AbelianMonoid R_Ring R_ModuleSpace))
       (@seq.pairmap (prod R R) R
          (fun x y : prod R R => @scal R_Ring R_ModuleSpace (Rminus (@fst R R y) (@fst R R x)) (@snd R R y))
          (@pair R R (@SF_h R ptd) (f zero))
          (@seq.map (prod R R) (prod R R) (fun x : prod R R => @pair R R (@fst R R x) (f (@snd R R x))) (@SF_t R ptd)))).
  2: { by rewrite (@Riemann_pairmap_junk (f zero) zero (seq.map (λ x : R * R, (x.1, f x.2)) (SF_t ptd)) ptd). }
  by rewrite X.
Qed.

(* Lower sum for a list a :: L *)
Definition DarbouxLowerSum (f : R → R) (a b : R) (L : list R) : R :=
  Darboux_sum (Darboux_inf_seq f (a :: L ++ (cons b nil))).

(* Upper sum for a list a :: L *)
Definition DarbouxUpperSum (f : R → R) (a b : R) (L : list R) : R :=
  Darboux_sum (Darboux_sup_seq f (a :: L ++ (cons b nil))).

(* Lower sums <= Upper sums *)
Theorem DarbouxSum_Lower_Upper {f a b} (L : list R) (Hwf : Part_wf a b L) (HB : Bounded f a b) :
  DarbouxLowerSum f a b L <= DarbouxUpperSum f a b L.
Proof.
  (*
  rewrite /DarbouxLowerSum /DarbouxUpperSum /Darboux_sum /Darboux_inf_seq /Darboux_sup_seq /SF_seq_f2 //=.
  destruct Hwf as [Hord Hright].
  induction L as [| x L IHL] in a, b, Hord, HB |-*.
  - simpl. lra.
  - simpl.
    assert (Hjunk1: seq.foldr plus zero (seq.pairmap (λ x0 y : R * R, scal (y.1 - x0.1) y.2)
      (x, real (Inf_fct f a x)) (seq.pairmap (λ x0 y : R, (y, real (Inf_fct f x0 y))) x L)) =
      seq.foldr plus zero (seq.pairmap (λ x0 y : R * R, scal (y.1 - x0.1) y.2)
      (x, zero) (seq.pairmap (λ x0 y : R, (y, real (Inf_fct f x0 y))) x L))).
    { induction L; simpl; auto. }
    assert (Hjunk2: seq.foldr plus zero (seq.pairmap (λ x0 y : R * R, scal (y.1 - x0.1) y.2)
      (x, real (Sup_fct f a x)) (seq.pairmap (λ x0 y : R, (y, real (Sup_fct f x0 y))) x L)) =
      seq.foldr plus zero (seq.pairmap (λ x0 y : R * R, scal (y.1 - x0.1) y.2)
      (x, zero) (seq.pairmap (λ x0 y : R, (y, real (Sup_fct f x0 y))) x L))).
    { induction L; simpl; auto. }
    rewrite Hjunk1 Hjunk2.
    apply Rplus_le_compat.
    + admit. (* Need: Inf_fct f a x <= Sup_fct f a x and scal preserves inequality *)
    + apply: IHL.
      * rewrite //= in Hord.
        destruct L; simpl; [done | ].
        admit.
      * admit.
  *)
Admitted.

Theorem DarbouxSum_Lower_MonoFun {f g a b} (L : list R) (Hwf : Part_wf a b L) (HBf : Bounded f a b)
  (HBg : Bounded g a b) (Hfg : FunLe f g a b) : DarbouxLowerSum f a b L <= DarbouxLowerSum g a b L.
Proof. Admitted.

Theorem DarbouxSum_Upper_MonoFun {f g a b} (L : list R) (Hwf : Part_wf a b L) (HBf : Bounded f a b)
  (HBg : Bounded g a b) (Hfg : FunLe f g a b) : DarbouxUpperSum f a b L <= DarbouxUpperSum g a b L.
Proof. Admitted.

End Darboux_sum.

(** 1D Darboux Integrals *)

Section DarbouxInt1.

Definition DarbouxInt_Lower (f : R → R) (a b : R) : R :=
  real $ Glb_Rbar (fun (IV : R) => exists L : list R, Part_wf a b L ∧ IV = DarbouxLowerSum f a b L).

Definition DarbouxInt_Upper (f : R → R) (a b : R) : R :=
  real $ Lub_Rbar (fun (IV : R) => exists L : list R, Part_wf a b L ∧ IV = DarbouxUpperSum f a b L).


End DarbouxInt1.

(** 2D Darboux Sums *)

Section DarbouxSum2.


End DarbouxSum2.

(** 2D Darboux Integrals *)

Section DarbouxInt2.


End DarbouxInt2.










(*

It should be the case that, if I define the integrals using suprama and infima over wf darboux sequences, then

    Lower darboux   <=   Lifted riemann   <=   Upper darboux
     = glb sums         = limit sums           = lub sums
       any wf list        lifted unif_part       any wf list
                          prove this is wf

The relationship between the glb/lub's and limits might be tricky, unless I define them with filterlims or something.
But the relationship between the functions holds pointwise, should be easy to prove.

This is the only place I need (or want) to talk about the lifted sums.
   Darboux_raise_seq
   Darboux_lower_seq
   Darboux_seq_of_Riemann

Instead, I'll be talking about plain Darboux sums
   Darboux_inf_seq (some wf list)
   Darboux_sup_seq (some wf list)

I can define refinements on wf lists,
Inequality along refinements
Ineuqality between lower and upper sums

I can also define the 2D Darboux lower and upper sums, similar lemmas
*)










