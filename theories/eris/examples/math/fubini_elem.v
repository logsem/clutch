From clutch.eris.examples.math Require Import prelude continuity2.
From clutch.eris Require Import infinite_tape.
Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(** WIP:
An elementary proof of the Fubini axiom.
This proof is following the proofs found in chapter 3 of Munkres, Analysis on Manifolds.
 *)




(*

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

(* Darboux sums *)
Definition Darboux_sum (ptd : Darboux_seq) : R :=
  seq.foldr plus zero (seq.pairmap (fun x y => scal (fst y - fst x) (snd y)) (SF_h ptd, zero) (SF_t ptd)).

Lemma Riemann_pairmap_junk (x x' : R) {L} {ptd : @SF_seq R} :
  (seq.pairmap (λ x y : R * R, scal (y.1 - x.1) (y.2)) (SF_h ptd, x) L) =
  (seq.pairmap (λ x y : R * R, scal (y.1 - x.1) (y.2)) (SF_h ptd, x') L).
Proof. induction L; rewrite //=. Qed.


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
  rewrite /DarbouxLowerSum /DarbouxUpperSum /Darboux_sum /Darboux_inf_seq /Darboux_sup_seq /SF_seq_f2 //=.
  destruct Hwf as [Hord].
  induction L as [| x L IHL] in a, b, Hord, HB |-*.
  - simpl.
    admit. (* Base case: single interval [a,b] *)
  - simpl.
    assert (Hjunk1: seq.foldr plus zero (seq.pairmap (λ x0 y : R * R, scal (y.1 - x0.1) y.2)
      (x, real (Inf_fct f a x)) (seq.pairmap (λ x0 y : R, (y, real (Inf_fct f x0 y))) x (L ++ cons b nil))) =
      seq.foldr plus zero (seq.pairmap (λ x0 y : R * R, scal (y.1 - x0.1) y.2)
      (x, zero) (seq.pairmap (λ x0 y : R, (y, real (Inf_fct f x0 y))) x (L ++ cons b nil)))).
    { induction L; simpl; auto. }
    assert (Hjunk2: seq.foldr plus zero (seq.pairmap (λ x0 y : R * R, scal (y.1 - x0.1) y.2)
      (x, real (Sup_fct f a x)) (seq.pairmap (λ x0 y : R, (y, real (Sup_fct f x0 y))) x (L ++ cons b nil))) =
      seq.foldr plus zero (seq.pairmap (λ x0 y : R * R, scal (y.1 - x0.1) y.2)
      (x, zero) (seq.pairmap (λ x0 y : R, (y, real (Sup_fct f x0 y))) x (L ++ cons b nil)))).
    { induction L; simpl; auto. }
    rewrite Hjunk1 Hjunk2.
    apply Rplus_le_compat.
    + admit. (* Need: Inf_fct f a x <= Sup_fct f a x and scal preserves inequality *)
    + apply: IHL.
      * admit. (* Need to extract sorted (x :: L ++ [b]) from sorted (a :: x :: L ++ [b]) *)
      * admit. (* bounded *)
Admitted.

Theorem DarbouxSum_Lower_MonoFun {f g a b} (L : list R) (Hwf : Part_wf a b L) (HBf : Bounded f a b)
  (HBg : Bounded g a b) (Hfg : FunLe f g a b) : DarbouxLowerSum f a b L <= DarbouxLowerSum g a b L.
Proof.
  rewrite /DarbouxLowerSum /Darboux_sum /Darboux_inf_seq /SF_seq_f2 //=.
  destruct Hwf as [Hord].
  induction L as [| x L IHL] in a, b, Hord, HBf, HBg, Hfg |-*.
  - simpl. admit. (* Base case: f ≤ g implies Inf_fct f a b ≤ Inf_fct g a b *)
  - simpl.
    assert (Hjunk1: seq.foldr plus zero (seq.pairmap (λ x0 y : R * R, scal (y.1 - x0.1) y.2)
      (x, real (Inf_fct f a x)) (seq.pairmap (λ x0 y : R, (y, real (Inf_fct f x0 y))) x (L ++ cons b nil))) =
      seq.foldr plus zero (seq.pairmap (λ x0 y : R * R, scal (y.1 - x0.1) y.2)
      (x, zero) (seq.pairmap (λ x0 y : R, (y, real (Inf_fct f x0 y))) x (L ++ cons b nil)))).
    { induction L; simpl; auto. }
    assert (Hjunk2: seq.foldr plus zero (seq.pairmap (λ x0 y : R * R, scal (y.1 - x0.1) y.2)
      (x, real (Inf_fct g a x)) (seq.pairmap (λ x0 y : R, (y, real (Inf_fct g x0 y))) x (L ++ cons b nil))) =
      seq.foldr plus zero (seq.pairmap (λ x0 y : R * R, scal (y.1 - x0.1) y.2)
      (x, zero) (seq.pairmap (λ x0 y : R, (y, real (Inf_fct g x0 y))) x (L ++ cons b nil)))).
    { induction L; simpl; auto. }
    rewrite Hjunk1 Hjunk2.
    apply Rplus_le_compat.
    + admit. (* Need: Inf_fct_mono for f ≤ g and scal preserves inequality *)
    + apply: IHL.
      * admit. (* sorted (x :: L ++ [b]) from sorted (a :: x :: L ++ [b]) *)
      * admit. (* Bounded f x b from Bounded f a b *)
      * admit. (* Bounded g x b from Bounded g a b *)
      * admit. (* FunLe f g x b from FunLe f g a b *)
Admitted.

Theorem DarbouxSum_Upper_MonoFun {f g a b} (L : list R) (Hwf : Part_wf a b L) (HBf : Bounded f a b)
  (HBg : Bounded g a b) (Hfg : FunLe f g a b) : DarbouxUpperSum f a b L <= DarbouxUpperSum g a b L.
Proof. (* Similar to DarbouxSum_Lower_MonoFun *) Admitted.

End Darboux_sum.

(** 1D Darboux Integrals *)

Section DarbouxInt1.

Definition DarbouxInt_Lower (f : R → R) (a b : R) : Rbar :=
  Glb_Rbar (fun (IV : R) => exists L : list R, Part_wf a b L ∧ IV = DarbouxLowerSum f a b L).

Definition DarbouxInt_Upper (f : R → R) (a b : R) : Rbar :=
  Lub_Rbar (fun (IV : R) => exists L : list R, Part_wf a b L ∧ IV = DarbouxUpperSum f a b L).

Definition DarbouxIntegrable (f : R → R) (a b : R) : Prop :=
  DarbouxInt_Lower f a b = DarbouxInt_Upper f a b.

(* If the function is bounded, then the lower interal is finite. This allows conversion to a real number. *)
Theorem DarbouxInt_Lower_Finite {f a b} (HB : Bounded f a b) : is_finite (DarbouxInt_Lower f a b).
Proof. Admitted.

(* If the function is bounded, then the upper interal is finite. This allows conversion to a real number. *)
Theorem DarbouxInt_Upper_Finite {f a b} (HB : Bounded f a b) : is_finite (DarbouxInt_Upper f a b).
Proof. Admitted.

Theorem DarbouxInt_Lower_Upper {f a b} (HB : Bounded f a b) :
  DarbouxInt_Lower f a b <= DarbouxInt_Upper f a b.
Proof. (* Pointwise bound, plus existence to strip the real *) Admitted.

Theorem DarbouxInt_Lower_MonoFun {f g a b} (HBf : Bounded f a b) (HBg : Bounded g a b)
  (Hfle : FunLe f g a b) : DarbouxInt_Lower f a b <= DarbouxInt_Lower g a b.
Proof. Admitted.

Theorem DarbouxInt_Upper_MonoFun {f g a b} (HBf : Bounded f a b) (HBg : Bounded g a b)
  (Hfle : FunLe f g a b) : DarbouxInt_Upper f a b <= DarbouxInt_Upper g a b.
Proof. Admitted.

End DarbouxInt1.


(** Riemann Integrability compat *)

Section DarbouxRiemann.

(* Compat: a Darboux sequence that is pointwise greater than the given step function P *)
Definition Darboux_raise_seq (f : R → R) (P : @SF_seq R) :=
  Darboux_sup_seq f (SF_lx P).

(* Compat: a Darboux sequence that is pointwise lesser than the given step function P *)
Definition Darboux_lower_seq (f : R → R) (P : @SF_seq R) :=
  Darboux_inf_seq f (SF_lx P).

(* Compat: a Darboux sequence that gives an equal Darboux sum to the Riemann sum of f on ptd *)
Definition Darboux_seq_of_Riemann (f : R → R) (ptd : @SF_seq R) : Darboux_seq :=
  SF_map f ptd.

(* Riemann sums can be converted into Darboux sums *)
Lemma Darboux_Riemann_sum_compat (f : R → R) (ptd : @SF_seq R) :
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

(*
Lemma filterlim_real_to_Rbar {T : Type} (f : T → R) (F : (T → Prop) → Prop) (r : R) :
  filterlim (fun t => Finite $ f t) F (Rbar_locally (Finite r)) →
  filterlim f F (locally r).
Proof.
  intros ?.
A dmitted.
*)

(* TODO: Need special case for a = b, where the Riemann integral becomes 0 *)
Lemma Darboux_Riemann {f : R → R} {a b : R} :
  a < b →
  Bounded f a b →
  DarbouxIntegrable f a b →
  is_RInt f a b (real $ DarbouxInt_Lower f a b).
Proof.
  intros Hab HB HD.
  rewrite /is_RInt.

  (* Simplify the sign expression *)
  rewrite Rcomplements.sign_eq_1; [|lra].
  rewrite /scal//= /mult//=.
  replace (fun ptd : @SF_seq R => Rmult (IZR (Zpos xH)) (@Riemann_sum (NormedModule.ModuleSpace R_AbsRing R_NormedModule) f ptd))
     with (fun ptd : @SF_seq R => (@Riemann_sum (NormedModule.ModuleSpace R_AbsRing R_NormedModule) f ptd)).
  2: { apply functional_extensionality. intros ?. lra. }

  (* Apply the squeeze theorem *)
  suffices Hsqueeze :
    filterlim (fun ptd : SF_seq => Darboux_sum (Darboux_lower_seq f ptd)) (Riemann_fine a b) (Rbar_locally (DarbouxInt_Lower f a b)) ∧
    filterlim (fun ptd : SF_seq => Darboux_sum (Darboux_raise_seq f ptd)) (Riemann_fine a b) (Rbar_locally (DarbouxInt_Lower f a b)).
  { destruct Hsqueeze as [H1 H2].
    have HsqueezeF : Riemann_fine a b (λ x : SF_seq, Darboux_sum (Darboux_lower_seq f x) <= Riemann_sum f x <= Darboux_sum (Darboux_raise_seq f x)).
    { (* Inequality between functions *) admit. }
    have HF : Filter (Riemann_fine a b).
    { apply filter_filter. }
    have X :=
      @Lim_seq.filterlim_le_le _ (Riemann_fine a b) (filter_filter)
        (λ ptd : SF_seq, Darboux_sum (Darboux_lower_seq f ptd))
        (λ ptd : SF_seq, Riemann_sum f ptd)
        (λ ptd : SF_seq, Darboux_sum (Darboux_raise_seq f ptd))
        (DarbouxInt_Lower f a b)
        HsqueezeF
        H1 H2.
    (* Prove that the Finite Rbar and R filters are equal *)
    admit.
  }
  (* Now we need to connect the filterlims to the infima/suprema *)
  split.
  { admit. }
  { admit. }
Admitted.

End DarbouxRiemann.


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
*)




(*

An old attempt:

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

Lemma Glb_le_Lub {E} : Glb_Rbar E <= Lub_Rbar E.
Proof.
(* Idea: Case anaysis on both. In the finite/finite case, reduce to stdlib lub's which are stated
 in terms of upper and lower bounds. Other 8 cases should be trivial or impossible. *)
Admitted.

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


Record Partition : Type := mkPartition { part_head : R; part_parts : list R }.

Definition part_list (P : Partition) := part_head P :: part_parts P.

Definition part_first (P : Partition) := part_head P.

Definition part_last (P : Partition) := seq.last (part_head P) (part_parts P).

Definition IsPartition (P : Partition) (a b : R) : Prop :=
  part_first P = Rmin a b ∧
  part_last P = Rmax a b ∧
  sorted Rle (part_list P).

Lemma part_list_ordered {P a b} :
  IsPartition P a b →
  ordered_Rlist (part_list P).
Proof. intros [?[??]]. by apply sorted_compat. Qed.

Lemma part_list_left {P a b} :
  IsPartition P a b → pos_Rl (part_list P) 0 = Rmin a b.
Proof. intros [?[??]]. rewrite /part_list //=. Qed.

Lemma part_list_right {P a b} :
  IsPartition P a b →
  seq.last (part_head P) (part_list P) = Rmax a b.
Proof. intros [?[??]]. rewrite /part_list //=. Qed.

Theorem IsPartition_bound_left {P : Partition} {a b} (HP : IsPartition P a b) :
  part_first P = a.
Proof. (* Because the list is sorted *) Admitted.

Theorem IsPartition_bound_right {P : Partition} {a b} (HP : IsPartition P a b) :
  part_last P = b.
Proof. (* Because the list is sorted *) Admitted.

Theorem IsPartition_bounds {P : Partition} {a b} (HP : IsPartition P a b) : a <= b.
Proof. (* Because the list is sorted *) Admitted.

Record Partition2 : Type := mkPartition2 {part2_x : Partition; part2_y : Partition}.

Definition IsPartition2 (P : Partition2) (xa xb ya yb : R) : Prop :=
  IsPartition (part2_x P) xa xb ∧ IsPartition (part2_y P) ya yb.

Definition sort (l : list R) : list R :=
  cons_ORlist l nil.

Lemma sort_length (l : list R) : length (sort l) = length l.
Proof. rewrite /sort. rewrite RList_P11 //=. lia. Qed.

Lemma ordered_Rlist_empty : ordered_Rlist [].
Proof. intros ??. simpl in H. lia. Qed.

Lemma sort_sorted {l} : sorted Rle (sort l).
Proof. rewrite /sort. apply sorted_compat, RList_P2, ordered_Rlist_empty. Qed.

Lemma sort_cons_comm {l1 l2} : sort (l1 ++ l2) = sort (l2 ++ l1).
Proof. Admitted.

Definition CommonPartition (p1 p2 : Partition) : Partition :=
  let l1 := part_list p1 in
  let l2 := part_list p2 in
  match sort (l1 ++ l2) with
  | h :: t => mkPartition h t
  | nil => p1 (* Dead code *)
  end.

Lemma Partition_length (p : Partition) : (0 < length (part_list p))%nat.
Proof. rewrite /part_list cons_length; lia. Qed.

Lemma CommonPartition_Symm {p1 p2 : Partition} : CommonPartition p1 p2 = CommonPartition p2 p1.
Proof.
  rewrite /CommonPartition.
  suffices HORL : sort (part_list p1 ++ part_list p2) = sort (part_list p2 ++ part_list p1).
  { rewrite HORL.
    destruct (sort (part_list p2 ++ part_list p1)) as [|??] eqn:Heq; last done.
    exfalso.
    pose proof (Partition_length p1).
    rewrite -length_zero_iff_nil in Heq.
    rewrite sort_length in Heq.
    rewrite cons_length in Heq.
    lia.
  }
  by rewrite sort_cons_comm.
Qed.

(* This definition does not require the two partitions to be partitions. *)
Definition PartitionRefinement (p1 p2 : Partition) : Prop :=
  incl (part_list p1) (part_list p2).

Lemma CommonPartition_refines_left (P Q : Partition) : PartitionRefinement P (CommonPartition P Q).
Proof.
  unfold PartitionRefinement, CommonPartition.
  destruct (sort (part_list P ++ part_list Q)) eqn:Hmerge.
  - apply incl_refl.
  - simpl.
    unfold incl.
    intros a Ha.
    replace (part_list {| part_head := r; part_parts := l |}) with (r :: l); [| rewrite /part_list//=].
    rewrite <- Hmerge.
    apply RList.RList_P9.
    left.
    apply in_or_app.
    by left.
Qed.

Lemma CommonPartition_refines_right (P Q : Partition) : PartitionRefinement Q (CommonPartition P Q).
Proof. rewrite CommonPartition_Symm. apply CommonPartition_refines_left. Qed.


(** ** Conversion between Partition and stdlib subdivision lists *)

Definition stepfun_to_partition {a b} (f : StepFun a b) : Partition :=
  match subdivision f with
  | nil => mkPartition a nil  (* impossible case *)
  | h :: t => mkPartition h t
  end.

(* Every stdlib partition can be converted to a Darboux partition *)
Lemma stepfun_gives_partition {a b} (f : StepFun a b) :
  a <= b →
  IsPartition (stepfun_to_partition f) a b.
Proof.
  intros Hab.
  unfold IsPartition, stepfun_to_partition, part_list.
  pose proof (StepFun_P1 f) as Hadapted.
  (* adapted_couple gives us properties of the StepFun *)
  unfold adapted_couple in Hadapted.
  destruct Hadapted as [Hord [Hleft [Hright [Hlen Hconst]]]].
  destruct (subdivision f) as [|h t] eqn:Hsub.
  { (* Subdivision has nonnegative length. *) simpl in Hlen. discriminate Hlen. }
  simpl.
  split; [|split].
  { exact Hleft. }
  { (* Convert right endpoint to pos_Rl *)
    assert (Hconv : forall l x, seq.last x l = pos_Rl (x :: l) (pred (length (x :: l)))).
    { intros l.
      induction l as [|y l' IH]; intro x; simpl.
      - reflexivity.
      - rewrite IH. reflexivity.
    }
    rewrite /part_last.
    rewrite Hconv.
    exact Hright.
  }
  { destruct t as [|h1 t']; first done.
    split.
    + unfold ordered_Rlist in Hord.
      simpl in Hord.
      apply (Hord 0%nat).
      simpl. lia.
    + apply sorted_compat.
      unfold ordered_Rlist in Hord.
      unfold ordered_Rlist.
      intros i Hi.
      apply (Hord (S i)).
      simpl in *. lia.
  }
Qed.


(* Relevant: Check rbar_finite_real_eq. Check Sup_fct_maj. Search is_finite. *)
Definition Sup_fct2 (f : R → R → R) (xa xb ya yb : R) : R :=
  match Req_EM_T xa xb with
  | left _ =>  0
  | right Hab =>
      match Req_EM_T ya yb with
      | left _ => 0
      | right Hab' =>
          Lub_Rbar (fun z => ∃ x y, z = f x y ∧ Rmin xa xb < x < Rmax xa xb ∧ Rmin ya yb < y < Rmax ya yb )
      end
  end.

Definition Inf_fct2 (f : R → R → R) (xa xb ya yb : R) : R :=
  match Req_EM_T xa xb with
  | left _ =>  0
  | right Hab =>
      match Req_EM_T ya yb with
      | left _ => 0
      | right Hab' =>
          Glb_Rbar (fun z => ∃ x y, z = f x y ∧ Rmin xa xb < x < Rmax xa xb ∧ Rmin ya yb < y < Rmax ya yb )
      end
  end.

Lemma Inf_fct2_mono {xa xb ya yb} {f g} (Hfg : FunLe2 f g xa xb ya yb)
  (Hlex : xa <= xb) (Hley : ya <= yb) :
  Inf_fct2 f xa xb ya yb <= Inf_fct2 g xa xb ya yb.
Proof. Admitted.

Lemma Sup_fct2_mono {xa xb ya yb} {f g} (Hfg : FunLe2 f g xa xb ya yb)
  (Hlex : xa <= xb) (Hley : ya <= yb) :
  Sup_fct2 f xa xb ya yb<= Sup_fct2 g xa xb ya yb.
Proof. Admitted.


Definition Rects (P : Partition) : list (R * R) :=
  seq.pairmap (fun x y => (x, y)) (part_head P) (part_parts P).

Lemma pairs_sorted {xa xb a b P} (HP : IsPartition P xa xb) :
 In (a, b) (Rects P) -> (a <= b).
Proof. Admitted.

Definition DarbouxLowerSum1 (f : R → R) (P : Partition) : R :=
  foldr Rplus 0%R $ List.map (fun '(a, b) => (b - a) * (real $ Inf_fct f a b)) (Rects P).

Definition DarbouxUpperSum1 (f : R → R) (P : Partition) : R :=
  foldr Rplus 0%R $ List.map (fun '(a, b) => (b - a) * (real $ Sup_fct f a b)) (Rects P).

Definition DarbouxLowerSum2 (f : R → R → R) (P : Partition2) : R :=
  foldr Rplus 0%R $ List.map
    (fun '(Ix, Iy) => (snd Ix - fst Ix) * (snd Iy - fst Iy) * (real $ Inf_fct2 f (fst Ix) (snd Ix) (fst Iy) (snd Iy))) (list_prod (Rects (part2_x P)) (Rects (part2_y P))).

Definition DarbouxUpperSum2 (f : R → R → R) (P : Partition2) : R :=
  foldr Rplus 0%R $ List.map
    (fun '(Ix, Iy) => (snd Ix - fst Ix) * (snd Iy - fst Iy) * (real $ Sup_fct2 f (fst Ix) (snd Ix) (fst Iy) (snd Iy))) (list_prod (Rects (part2_x P)) (Rects (part2_y P))).


Theorem DarbouxLowerUpperLe1 {f P xa xb} (Hf : Bounded f xa xb) (HP : IsPartition P xa xb) :
  DarbouxLowerSum1 f P <= DarbouxUpperSum1 f P.
Proof.
  rewrite /DarbouxLowerSum1 /DarbouxUpperSum1 /Rects.
  remember (seq.pairmap (fun x y : R => (x, y)) (part_head P) (part_parts P)) as pairs eqn:Hpairs.
  assert (Hpairs_sorted : forall a b, In (a, b) pairs -> a <= b).
  { intros ???. apply (pairs_sorted HP). by rewrite /Rects -Hpairs. }
  destruct HP as [Hleft [Hright Hsorted]].
  clear Hpairs.
  induction pairs as [|[a b] rest IH].
  - by simpl.
  - apply Rplus_le_compat; [|apply IH; intros; apply Hpairs_sorted; right; assumption].
    unfold Inf_fct, Sup_fct.
    destruct (Req_dec_T a b); [lra|].
    assert (Hab : a <= b).
    { apply Hpairs_sorted. left. reflexivity. }
    assert (H0 : 0 <= b - a) by lra.
    apply Rmult_le_compat_l; [exact H0|].
    apply Glb_le_Lub.
Qed.

Theorem DarbouxLowerSum1_mono {f g P xa xb} (Hf : Bounded f xa xb) (Hg : Bounded g xa xb)
  (HP : IsPartition P xa xb) (Hfg : FunLe f g xa xb) : DarbouxLowerSum1 f P <= DarbouxLowerSum1 g P.
Proof.
  rewrite /DarbouxLowerSum1 /Rects.
  remember (seq.pairmap (fun x y : R => (x, y)) (part_head P) (part_parts P)) as pairs eqn:Hpairs.
  assert (Hpairs_sorted : forall a b, In (a, b) pairs -> a <= b).
  { intros ???. apply (pairs_sorted HP). by rewrite /Rects -Hpairs. }
  clear Hpairs.
  induction pairs as [|[a b] rest IH].
  - simpl. lra.
  - simpl.
    apply Rplus_le_compat; [|apply IH].
    2: { intros ???. apply Hpairs_sorted. by apply in_cons. }
    have Hle : a <= b. { apply Hpairs_sorted; by apply in_eq. }
    apply Rmult_le_compat_l; [lra|].
    eapply Inf_fct_mono; done.
Qed.

Theorem DarbouxUpperSum1_mono
  {f g P xa xb} (Hf : Bounded f xa xb) (Hg : Bounded g xa xb)
  (HP : IsPartition P xa xb) (Hfg : FunLe f g xa xb) : DarbouxUpperSum1 f P <= DarbouxUpperSum1 g P.
Proof.
  rewrite /DarbouxUpperSum1 /Rects.
  remember (seq.pairmap (fun x y : R => (x, y)) (part_head P) (part_parts P)) as pairs eqn:Hpairs.
  assert (Hpairs_sorted : forall a b, In (a, b) pairs -> a <= b).
  { intros ???. apply (pairs_sorted HP). by rewrite /Rects -Hpairs. }
  clear Hpairs.
  induction pairs as [|[a b] rest IH].
  - simpl. lra.
  - simpl.
    apply Rplus_le_compat; [|apply IH].
    2: { intros ???. apply Hpairs_sorted. by apply in_cons. }
    have Hle : a <= b. { apply Hpairs_sorted; by apply in_eq. }
    apply Rmult_le_compat_l; [lra|].
    eapply Sup_fct_mono; done.
Qed.

Theorem DarbouxLowerUpperLe2 {xxa xxb yya yyb : R} {f : R → R → R}
  (P : Partition2) (HP : IsPartition2 P xxa xxb yya yyb) (Hf : Bounded2 f xxa xxb yya yyb) :
  DarbouxLowerSum2 f P <= DarbouxUpperSum2 f P.
Proof.
  destruct HP as [HPx HPy].
  assert (Hpairs_sorted : forall xa xb ya yb, In ((xa, xb), (ya, yb)) (list_prod (Rects (part2_x P)) (Rects (part2_y P))) -> xa <= xb /\ ya <= yb).
  { intros ?????.
    apply in_prod_iff in H; destruct H.
    split.
    { apply (pairs_sorted HPx). apply H. }
    { apply (pairs_sorted HPy). apply H0. }
  }
  destruct HPx as [Hleft_x [Hright_x Hsorted_x]].
  destruct HPy as [Hleft_y [Hright_y Hsorted_y]].
  rewrite /DarbouxLowerSum2 /DarbouxUpperSum2.
  remember (list_prod (Rects (part2_x P)) (Rects (part2_y P))) as pairs eqn:Hpairs.
  clear Hpairs.
  induction pairs as [|[[xa xb] [ya yb]] rest IH].
  - by simpl.
  - rewrite //=.
    apply Rplus_le_compat; [|apply IH; intros; apply Hpairs_sorted; right; assumption].
    unfold Inf_fct2, Sup_fct2.
    destruct (Req_EM_T xa xb); [lra|].
    destruct (Req_EM_T ya yb); [lra|].
    assert (Hab : xa <= xb /\ ya <= yb).
    { apply Hpairs_sorted. left. reflexivity. }
    destruct Hab as [Hxa Hya].
    assert (H0x : 0 <= xb - xa) by lra.
    assert (H0y : 0 <= yb - ya) by lra.
    apply Rmult_le_compat_l; [apply Rmult_le_pos; assumption|].
    apply Glb_le_Lub.
Qed.

Theorem DarbouxLowerSum2_mono
  {f g P xa xb ya yb} (Hf : Bounded2 f xa xb ya yb) (Hg : Bounded2 g xa xb ya yb)
  (HP : IsPartition2 P xa xb ya yb) (Hfg : FunLe2 f g xa xb ya yb) :
  DarbouxLowerSum2 f P <= DarbouxLowerSum2 g P.
Proof.
  destruct HP as [HPx HPy].
  assert (Hpairs_sorted : forall xa xb ya yb, In ((xa, xb), (ya, yb)) (list_prod (Rects (part2_x P)) (Rects (part2_y P))) -> xa <= xb /\ ya <= yb).
  { intros ?????.
    apply in_prod_iff in H; destruct H.
    split.
    { apply (pairs_sorted HPx). apply H. }
    { apply (pairs_sorted HPy). apply H0. }
  }
  destruct HPx as [Hleft_x [Hright_x Hsorted_x]].
  destruct HPy as [Hleft_y [Hright_y Hsorted_y]].
  rewrite /DarbouxLowerSum2 /DarbouxUpperSum2.
  remember (list_prod (Rects (part2_x P)) (Rects (part2_y P))) as pairs eqn:Hpairs.
  clear Hpairs.
  induction pairs as [|[[xxa xxb] [yya yyb]] rest IH].
  - by simpl.
  - rewrite //=.
    apply Rplus_le_compat.
    2: { apply IH. intros ?????. apply Hpairs_sorted. by apply in_cons. }
    have HIn : In (xxa, xxb, (yya, yyb)) ((xxa, xxb, (yya, yyb)) :: rest); [by apply in_eq|].
    destruct (Hpairs_sorted xxa xxb yya yyb HIn).
    apply Rmult_le_compat_l. { apply Rmult_le_pos; lra. }
    apply Inf_fct2_mono; try done.
    (* Prove that the rectangle is a subrectangle of the whole thing, or maybe specialize earlier on. *)
    admit.
Admitted.

Theorem DarbouxUpperSum2_mono
  {f g P xa xb ya yb} (Hf : Bounded2 f xa xb ya yb) (Hg : Bounded2 g xa xb ya yb)
  (HP : IsPartition2 P xa xb ya yb) (Hfg : FunLe2 f g xa xb ya yb) :
  DarbouxUpperSum2 f P <= DarbouxUpperSum2 g P.
Proof.
  destruct HP as [HPx HPy].
  assert (Hpairs_sorted : forall xa xb ya yb, In ((xa, xb), (ya, yb)) (list_prod (Rects (part2_x P)) (Rects (part2_y P))) -> xa <= xb /\ ya <= yb).
  { intros ?????.
    apply in_prod_iff in H; destruct H.
    split.
    { apply (pairs_sorted HPx). apply H. }
    { apply (pairs_sorted HPy). apply H0. }
  }
  destruct HPx as [Hleft_x [Hright_x Hsorted_x]].
  destruct HPy as [Hleft_y [Hright_y Hsorted_y]].
  rewrite /DarbouxLowerSum2 /DarbouxUpperSum2.
  remember (list_prod (Rects (part2_x P)) (Rects (part2_y P))) as pairs eqn:Hpairs.
  clear Hpairs.
  induction pairs as [|[[xxa xxb] [yya yyb]] rest IH].
  - by simpl.
  - rewrite //=.
    apply Rplus_le_compat.
    2: { apply IH. intros ?????. apply Hpairs_sorted. by apply in_cons. }
    have HIn : In (xxa, xxb, (yya, yyb)) ((xxa, xxb, (yya, yyb)) :: rest); [by apply in_eq|].
    destruct (Hpairs_sorted xxa xxb yya yyb HIn).
    apply Rmult_le_compat_l. { apply Rmult_le_pos; lra. }
    apply Sup_fct2_mono; try done.
    (* Prove that the rectangle is a subrectangle of the whole thing, or maybe specialize earlier on. *)
    admit.
Admitted.


Definition DarbouxLowerInt1 (f : R → R) (a b : R) : Rbar :=
  real $ Glb_Rbar (fun IF => ∃ P, IsPartition P a b ∧ IF = DarbouxLowerSum1 f P).

Definition DarbouxUpperInt1 (f : R → R) (a b : R) : Rbar :=
  real $ Lub_Rbar (fun IF => ∃ P, IsPartition P a b ∧ IF = DarbouxUpperSum1 f P).

Definition DarbouxLowerInt2 (f : R → R → R) (xa xb ya yb : R) : Rbar :=
  real $ Glb_Rbar (fun IF => ∃ P, IsPartition2 P xa xb ya yb ∧ IF = DarbouxLowerSum2 f P).

Definition DarbouxUpperInt2 (f : R → R → R) (xa xb ya yb : R) : Rbar :=
  real $ Lub_Rbar (fun IF => ∃ P, IsPartition2 P xa xb ya yb ∧ IF = DarbouxUpperSum2 f P).

Lemma DarbouxLowerInt1_mono {f g} {a b} :
  (FunLe f g a b) →
  Bounded f a b →
  Bounded g a b →
  DarbouxLowerInt1 f a b <= DarbouxLowerInt1 g a b.
Proof.
  intros ?.
  rewrite /DarbouxLowerInt1.
  (* Glb comparison if set comparison *)
Admitted.

Lemma DarbouxUpperInt1_mono {f g} {a b} :
  (FunLe f g a b) →
  Bounded f a b →
  Bounded g a b →
  DarbouxUpperInt1 f a b <= DarbouxUpperInt1 g a b.
Proof.
  (* Lub/Glb comparison if set comparison *)
Admitted.

Lemma DarbouxLowerInt2_mono {f g} {xa xb ya yb} :
  (FunLe2 f g xa xb ya yb) →
  Bounded2 f xa xb ya yb →
  Bounded2 g xa xb ya yb →
  DarbouxLowerInt2 f xa xb ya yb <= DarbouxLowerInt2 g xa xb ya yb.
Proof.
  (* Lub/Glb comparison if set comparison *)
Admitted.

Lemma DarbouxUpperInt2_mono {f g} {xa xb ya yb} :
  (FunLe2 f g xa xb ya yb) →
  Bounded2 f xa xb ya yb →
  Bounded2 g xa xb ya yb →
  DarbouxUpperInt2 f xa xb ya yb <= DarbouxUpperInt2 g xa xb ya yb.
Proof.
  (* Lub/Glb comparison if set comparison *)
Admitted.

Definition DarbouxIntegrable1 (f : R → R) (a b : R) : Prop :=
  DarbouxLowerInt1 f a b = DarbouxUpperInt1 f a b.

Definition DarbouxIntegrable2 (f : R → R → R) (xa xb ya yb : R) : Prop :=
  DarbouxLowerInt2 f xa xb ya yb = DarbouxUpperInt2 f xa xb ya yb.

Definition FubiniILower (f : R → R → R) (ya yb : R) : R → R :=
  fun x => DarbouxLowerInt1 (f x) ya yb.

Definition FubiniIUpper (f : R → R → R) (ya yb : R) : R → R :=
  fun x => DarbouxUpperInt1 (f x) ya yb.

Theorem FubiniLower12 {f : R → R → R} {P : Partition2} {xa xb ya yb : R}:
  IsPartition2 P xa xb ya yb →
  Bounded2 f xa xb ya yb →
  DarbouxLowerSum2 f P <= DarbouxLowerSum1 (FubiniILower f ya yb) (part2_x P).
Proof.
  (* From the paper *)
Admitted.

Theorem FubiniUpper12 {f : R → R → R} {P : Partition2} {xa xb ya yb : R}:
  IsPartition2 P xa xb ya yb →
  Bounded2 f xa xb ya yb →
  DarbouxLowerSum1 (FubiniIUpper f ya yb) (part2_x P) <= DarbouxUpperSum2 f P.
Proof.
  (* From the paper *)
Admitted.

Theorem Fubini_LowerIntegrable {f : R → R → R} {xa xb ya yb : R} (Hf : Bounded2 f xa xb ya yb)
  (HInt : DarbouxIntegrable2 f xa xb ya yb) :
  DarbouxLowerInt1 (FubiniILower f ya yb) xa xb = DarbouxUpperInt1 (FubiniILower f ya yb) xa xb.
Proof. (* Sandwich *) Admitted.

Theorem Fubini_UpperIntegrable {f : R → R → R} {xa xb ya yb : R} (Hf : Bounded2 f xa xb ya yb)
  (HInt : DarbouxIntegrable2 f xa xb ya yb) :
  DarbouxLowerInt1 (FubiniIUpper f ya yb) xa xb = DarbouxUpperInt1 (FubiniIUpper f ya yb) xa xb.
Proof. (* Sandwich *) Admitted.

Theorem Fubini_Lower {f : R → R → R} {xa xb ya yb : R} (Hf : Bounded2 f xa xb ya yb)
  (HInt : DarbouxIntegrable2 f xa xb ya yb) :
  DarbouxLowerInt1 (FubiniILower f ya yb) xa xb = DarbouxLowerInt2 f xa xb ya yb.
Proof. (* Sandwich *) Admitted.

(** Darboux/Riemann compatability, assuming Darboux integrability *)


Definition SF_seq_make (Fint : R → R → R) (P : Partition) : @SF_seq R :=
  SF_seq_f2 (fun a b => Fint a b) (part_list P).

Lemma SF_seq_make_sorted {a b} (Fint : R → R → R) {P : Partition} (HP : IsPartition P a b) :
  SF_sorted Rle (SF_seq_make Fint P).
Proof. rewrite -SF_sorted_f2. by destruct HP as [?[??]]. Qed.

Program Definition SF_make {a b} (Fint : R → R → R) {P : Partition} (HP : IsPartition P a b) : StepFun a b :=
  SF_compat_le (SF_seq_make Fint P) (SF_seq_make_sorted Fint HP) .
Next Obligation.
  intros ?????.
  rewrite /SF_seq_make//=.
  have ? := IsPartition_bounds HP.
  destruct HP as [?[??]].
  rewrite /part_first in H; rewrite H.
  by apply Rmin_left.
Qed.
Next Obligation.
  intros ?????.
  rewrite /SF_seq_make//=.
  have ? := IsPartition_bounds HP.
  destruct HP as [?[??]].
  rewrite /part_last in H0.
  rewrite /seq.unzip1 //=.
  rewrite Rcomplements.map_pairmap //=.
  replace (seq.pairmap (λ _ y : R, y) (part_head P) (part_parts P)) with (part_parts P); last first.
  { admit. }
  rewrite H0.
  by apply Rmax_right.
Admitted.

(* Hard, eq_rect *)
Lemma SF_make_eval {a b} (Fint : R → R → R) {P : Partition} (HP : IsPartition P a b) (t : R) :
  SF_make Fint HP t = SF_fun (SF_seq_make Fint P) 0 t.
Proof. Admitted.

Definition DarbouxApproxStepFun (f : R → R) (P : Partition) (HP : IsPartition P (part_first P) (part_last P)) :
    StepFun (part_first P) (part_last P) :=
  SF_make (fun a b => ((real $ Sup_fct f a b) + (real $ Inf_fct f a b)) / 2) HP.

Definition DarbouxErrorStepFun (f : R → R) (P : Partition) (HP : IsPartition P (part_first P) (part_last P)) :
    StepFun (part_first P) (part_last P) :=
  SF_make (fun a b => ((real $ Sup_fct f a b) - (real $ Inf_fct f a b)) / 2) HP.

(** ** Forward direction: Darboux integrability → Riemann integrability *)

(* Darboux integrability means we can make upper - lower arbitrarily small *)
Lemma DarbouxDifference {f a b} :
  Bounded f a b →
  DarbouxIntegrable1 f a b →
  forall eps : posreal,
    exists P, IsPartition P a b ∧
      DarbouxUpperSum1 f P - DarbouxLowerSum1 f P < eps.
Proof. Admitted.

(* Main theorem: Darboux → Riemann *)
Theorem DarbouxRiemann_integrable_compat {f a b} :
  Bounded f a b →
  DarbouxIntegrable1 f a b →
  Riemann_integrable f a b.
Proof.
  intros HB HI eps.
  destruct (ClassicalEpsilon.constructive_indefinite_description _ (DarbouxDifference HB HI eps)) as [P [HP Heps]].
  have HF : part_first P = a.
  { admit. }
  have HL : part_last P = b.
  { admit. }
  rewrite -HF in HP.
  rewrite -HL in HP.
  pose SF_M := DarbouxApproxStepFun f P HP.
  pose SF_E := DarbouxErrorStepFun f P HP.
  rewrite -HF -HL.
  exists SF_M.
  exists SF_E.
  split.
  { intros ??.
    rewrite /SF_M /SF_E.
    rewrite SF_make_eval SF_make_eval.
    admit. }
  { rewrite /SF_E.
    rewrite /DarbouxErrorStepFun.
    Locate sf_SF_val_fun .

    admit. }
Admitted.

Theorem Darboux_Riemann_compat {f a b}
  (HB : Bounded f a b)
  (HD : DarbouxIntegrable1 f a b) :
  RiemannInt (DarbouxRiemann_integrable_compat HB HD) = real $ DarbouxLowerInt1 f a b.
Proof.
Admitted.



(* Old stuff *)

Definition FubiniPred (f : R → R → R_CompleteNormedModule) : Prop :=
  forall x y, Continuity.continuity_2d_pt f x y.

(* Helper lemma: 2D continuity implies continuity of partial functions *)
Lemma continuity_2d_implies_continuous_y (f : R → R → R_CompleteNormedModule) (x : R) (a b : R) :
  (forall x y, Continuity.continuity_2d_pt f x y) →
  (forall z, Rmin a b <= z <= Rmax a b -> Continuity.continuous (fun y => f x y) z).
Proof.
  intros Hcont z Hz.
  unfold Continuity.continuous.
  unfold Continuity.continuity_2d_pt in Hcont.
  specialize (Hcont x z).
  apply filterlim_locally.
  intro eps.
  specialize (Hcont eps).
  apply (locally_2d_1d_const_x _ x z) in Hcont.
  apply filter_imp with (2 := Hcont).
  intros y0 Hy0.
  unfold ball. simpl. unfold AbsRing_ball.
  rewrite /abs /minus /plus /opp /=.
  replace (f x y0 + - f x z) with (f x y0 - f x z) by ring.
  exact Hy0.
Qed.

Lemma continuity_2d_implies_continuous_x (f : R → R → R_CompleteNormedModule) (y : R) (c d : R) :
  (forall x y, Continuity.continuity_2d_pt f x y) →
  (forall z, Rmin c d <= z <= Rmax c d -> Continuity.continuous (fun x => f x y) z).
Proof.
  intros Hcont z Hz.
  unfold Continuity.continuous.
  unfold Continuity.continuity_2d_pt in Hcont.
  specialize (Hcont z y).
  apply filterlim_locally.
  intro eps.
  specialize (Hcont eps).
  apply (locally_2d_1d_const_y _ z y) in Hcont.
  apply filter_imp with (2 := Hcont).
  intros x0 Hx0.
  unfold ball. simpl. unfold AbsRing_ball.
  rewrite /abs /minus /plus /opp /=.
  replace (f x0 y + - f z y) with (f x0 y - f z y) by ring.
  exact Hx0.
Qed.

Lemma FubiniIntInt {f : R → R → R_CompleteNormedModule} {a b c d : R} :
  FubiniPred f →
  RInt (fun x => RInt (fun y => f x y) a b) c d = RInt (λ y, RInt (fun x => f x y) c d) a b.
Proof.
  intro Hcont.
  assert (Hex_y : forall x, ex_RInt (fun y => f x y) a b).
  { intro x. apply ex_RInt_continuous.
    apply (continuity_2d_implies_continuous_y f x a b Hcont). }
  assert (Hex_x : forall y, ex_RInt (fun x => f x y) c d).
  { intro y. apply ex_RInt_continuous.
    apply (continuity_2d_implies_continuous_x f y c d Hcont). }
  assert (HRiemann_y : forall x, Riemann_integrable (fun y => f x y) a b).
  { intro x. apply ex_RInt_Reals_0. apply Hex_y. }
  assert (HRiemann_x : forall y, Riemann_integrable (fun x => f x y) c d).
  { intro y. apply ex_RInt_Reals_0. apply Hex_x. }
  replace (fun x => RInt (fun y => f x y) a b) with (fun x => RiemannInt (HRiemann_y x)).
  2: { apply functional_extensionality. intro x. symmetry.
       apply is_RInt_unique. apply ex_RInt_Reals_aux_1. }
  replace (fun y => RInt (fun x => f x y) c d) with (fun y => RiemannInt (HRiemann_x y)).
  2: { apply functional_extensionality. intro y. symmetry.
       apply is_RInt_unique. apply ex_RInt_Reals_aux_1. }
  assert (HRiemann_outer_xy : Riemann_integrable (fun x => RiemannInt (HRiemann_y x)) c d).
  { admit. (* TODO: Prove continuity of x => RiemannInt (HRiemann_y x) *) }
  assert (HRiemann_outer_yx : Riemann_integrable (fun y => RiemannInt (HRiemann_x y)) a b).
  { admit. (* TODO: Prove continuity of y => RiemannInt (HRiemann_x y) *) }
  replace (RInt (fun x => RiemannInt (HRiemann_y x)) c d) with (RiemannInt HRiemann_outer_xy).
  2: { symmetry. apply is_RInt_unique. apply ex_RInt_Reals_aux_1. }
  replace (RInt (fun y => RiemannInt (HRiemann_x y)) a b) with (RiemannInt HRiemann_outer_yx).
  2: { symmetry. apply is_RInt_unique. apply ex_RInt_Reals_aux_1. }
Abort.


(*
1. nth - Standard list indexing function:
nth (default : T) (s : seq T) (n : nat) : T
1. Used with SF_lx or SF_ly to get elements at specific positions.

1. Example from indicators.v:677-679 (in pointed_subdiv definition):
Definition pointed_subdiv (ptd : @SF_seq R) :=
  forall i : nat, (i < SF_size ptd)%nat ->
    nth 0 (SF_lx ptd) i <= nth 0 (SF_ly ptd) i <= nth 0 (SF_lx ptd) (S i).
2. Accessor functions:
  - SF_h ptd - Gets the head (first x-coordinate)
  - SF_lx ptd - Gets the list of all x-coordinates
  - SF_ly ptd - Gets the list of all y-values (the data at each point)
  - SF_t ptd - Gets the tail (list of pairs (R * T))
3. SF_size ptd - Returns the number of intervals (length of SF_ly)
*)

(*

Search Glb_Rbar.
Search is_glb_Rbar.
Search is_lub.

  Predicate-based approach (from Raxioms.v):

  Definition is_upper_bound (E:R -> Prop) (m:R) :=
    forall x:R, E x -> x <= m.

  Definition bound (E:R -> Prop) :=
    exists m : R, is_upper_bound E m.

  Definition is_lub (E:R -> Prop) (m:R) :=
    is_upper_bound E m /\ (forall b:R, is_upper_bound E b -> m <= b).

  Completeness axiom (existence):

  Lemma completeness :
    forall E:R -> Prop,
      bound E -> (exists x : R, E x) -> { m:R | is_lub E m }.


emmas Relating is_lub to Coquelicot

  From Coquelicot's Lub.v:

  Main Connection Lemmas

  1. Lub_Rbar_correct (line 268-272):
  Lemma Lub_Rbar_correct (E : R -> Prop) :
    is_lub_Rbar E (Lub_Rbar E).
  1. States that Lub_Rbar E satisfies the is_lub_Rbar property.
  2. is_lub_Rbar_unique (line 251-258):
  Lemma is_lub_Rbar_unique (E : R -> Prop) (l : Rbar) :
    is_lub_Rbar E l -> Lub_Rbar E = l.
  2. If l is a lub, then Lub_Rbar E = l.

  Coquelicot's is_lub_Rbar Definition

  Definition is_lub_Rbar (E : R -> Prop) (l : Rbar) :=
    is_ub_Rbar E l /\ (forall b, is_ub_Rbar E b -> Rbar_le l b).

  This is analogous to stdlib's is_lub but:
  - Works with Rbar (extended reals)
  - Uses is_ub_Rbar instead of is_upper_bound
  - Uses Rbar_le instead of <=

  Bridging to Stdlib's is_lub

  While there's no direct lemma, you can bridge via:
  - When Lub_Rbar E = Finite r, you can extract r and relate to stdlib
  - Use that is_lub_Rbar is the natural extension of is_lub to Rbar

  Bottom line: Coquelicot's Lub_Rbar_correct gives you that Lub_Rbar E is provably the lub in the is_lub_Rbar sense, which extends stdlib's is_lub concept to handle infinities.

*)

(*
(** ** Reverse direction: Riemann integrability → Darboux integrability *)

(* Bounds on Sup_fct and Inf_fct from step function approximation *)
Lemma sup_fct_bounded_by_stepfun {f phi psi a b c e} :
  (forall t, a < t < b → Rabs (f t - phi t) <= psi t) →
  (forall t, a < t < b → phi t = c) →  (* phi constant on (a,b) *)
  (forall t, a < t < b → psi t <= e) →  (* psi bounded on (a,b) *)
  real (Sup_fct f a b) <= c + e.
Proof. Admitted.

Lemma inf_fct_bounded_by_stepfun {f phi psi a b c e} :
  (forall t, a < t < b → Rabs (f t - phi t) <= psi t) →
  (forall t, a < t < b → phi t = c) →  (* phi constant on (a,b) *)
  (forall t, a < t < b → psi t <= e) →  (* psi bounded on (a,b) *)
  c - e <= real (Inf_fct f a b).
Proof. Admitted.

(* Common refinement of two step functions *)
Lemma stepfun_common_partition {a b} (f g : StepFun a b) :
  { P : Partition |
    IsPartition P a b ∧
    incl (subdivision f) (part_list P) ∧
    incl (subdivision g) (part_list P) }.
Proof. Admitted.

(* On common refinement, can bound sup - inf by psi *)
Lemma darboux_diff_interval_bounded {f phi psi a b} :
  a < b →
  (forall t, a < t < b → Rabs (f t - phi t) <= psi t) →
  (forall t, a < t < b → phi t = phi a) →  (* phi constant *)
  (forall t, a <= t <= b → psi t <= psi a) →  (* psi bounded *)
  real (Sup_fct f a b) - real (Inf_fct f a b) <= 2 * psi a.
Proof. Admitted.

(* Summing over partition gives bound on Darboux difference
Lemma darboux_sums_diff_bounded {f phi psi} {a b} (P : Partition) :
  IsPartition P a b →
  incl (subdivision phi) (part_list P) →
  incl (subdivision psi) (part_list P) →
  (forall t, Rmin a b <= t <= Rmax a b → Rabs (f t - phi t) <= psi t) →
  DarbouxUpperSum1 f P - DarbouxLowerSum1 f P <= 2 * RiemannInt_SF psi.
Proof. Admitted. *)

(* Upper integral bounded above by upper sum on any partition *)
Lemma darboux_upper_int_le_sum {f a b P} :
  IsPartition P a b →
  Bounded f a b →
  real (DarbouxUpperInt1 f a b) <= DarbouxUpperSum1 f P.
Proof. Admitted.

(* Lower integral bounded below by lower sum on any partition *)
Lemma darboux_lower_int_ge_sum {f a b P} :
  IsPartition P a b →
  Bounded f a b →
  DarbouxLowerSum1 f P <= real (DarbouxLowerInt1 f a b).
Proof. Admitted.

(* Main theorem: Riemann → Darboux *)
Theorem riemann_integrable_to_darboux {f a b} :
  a <= b →
  Bounded f a b →
  Riemann_integrable f a b →
  DarbouxIntegrable1 f a b.
Proof. Admitted.
*)
*)
