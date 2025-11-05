From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real.
Set Default Proof Using "Type*".
#[local] Open Scope R.


Section Indicators.
Import Hierarchy.

Definition Iverson {T : Type} (P : T → Prop) : T → R :=
  fun t => if decide (P t) then 1 else 0.

Notation "⟦ x ⟧" := (Iverson x).

Lemma Iverson_True {T : Type} {P : T → Prop} {t : T} (H : P t) : ⟦ P ⟧ t = 1.
Proof. rewrite /Iverson; case_decide; [done | by intuition]. Qed.

Lemma Iverson_False {T : Type} {P : T → Prop} {t : T} (H : ¬ P t) : ⟦ P ⟧ t = 0.
Proof. rewrite /Iverson; case_decide; [by intuition | done]. Qed.

Lemma Iverson_add_neg {T : Type} {P : T → Prop} {t : T} :
  ⟦ P ⟧ t + ⟦ not ∘ P ⟧ t = 1.
Proof.
  rewrite /Iverson; case_decide; case_decide; try lra.
  all: simpl in H0; intuition.
Qed.

Lemma Iverson_nonneg {T : Type} {P : T → Prop} {t : T} : (0 <= ⟦ P ⟧ t)%R.
Proof. rewrite /Iverson; case_decide; lra. Qed.

Lemma Iverson_le_1 {T : Type} {P : T → Prop} {t : T} : (⟦ P ⟧ t <= 1)%R.
Proof. rewrite /Iverson; case_decide; lra. Qed.

Lemma SeriesC_Iverson_singleton {T} `{Countable T} {F : T → R} {P : T → Prop} (N0 : T)
    (HN0 : ∀ N, P N <-> N = N0) :
    SeriesC (fun n : T => Iverson P n * F n) = F N0.
Proof.
  rewrite -(SeriesC_singleton' N0 (F N0)).
  f_equal; apply functional_extensionality; intros n.
  case_bool_decide.
  { rewrite Iverson_True; [|rewrite HN0; done]. rewrite H0; lra. }
  { rewrite Iverson_False; [|rewrite HN0; done]. lra. }
Qed.

Lemma Iverson_mul_and {T : Type} {P Q : T → Prop} {t : T} :
  ⟦ P ⟧ t * ⟦ Q ⟧ t = ⟦ fun t => P t ∧ Q t ⟧ t.
Proof.
  rewrite /Iverson; case_decide; case_decide; case_decide.
  all: try lra.
  all: intuition.
Qed.


Lemma RInt_Iverson_ge {rx F} (Hrx : 0 <= rx <= 1) :
  RInt (λ x : R, Iverson (uncurry Rge) (x, rx) * F x) 0 1 =  RInt (λ x : R, F x) rx 1.
Proof. Admitted.

Lemma RInt_Iverson_ge' {rx F} (Hrx : 0 <= rx <= 1) :
  RInt (λ x : R, Iverson (fun x  => not (Rle x rx)) x * F x) 0 1 =  RInt (λ x : R, F x) rx 1.
Proof. Admitted.

Lemma RInt_Iverson_le {rx F} (Hrx : 0 <= rx <= 1) :
  RInt (λ x : R, Iverson (uncurry Rle) (x, rx) * F x) 0 1 =  RInt (λ x : R, F x) 0 rx.
Proof. Admitted.

Lemma RInt_Iverson_le'' {rx F} (Hrx : 0 <= rx <= 1) :
  RInt (λ x : R, Iverson (Rle x) rx * F x) 0 1 =  RInt (λ x : R, F x) 0 rx.
Proof. Admitted.

Lemma RInt_Iverson_ge'' {rx F} (Hrx : 0 <= rx <= 1) :
  RInt (λ x : R, Iverson (Rge x) rx * F x) 0 1 =  RInt (λ x : R, F x) rx 1.
Proof. Admitted.

Lemma RInt_Iverson_le''' {x} (Hx : 0 <= x <= 1) : RInt (Iverson (Rle x)) 0 1 = 1 - x.
Proof. Admitted.

Lemma RInt_Iverson_ge''' {x} (Hx : 0 <= x <= 1) : RInt (Iverson (Rge x)) 0 1 = x.
Proof. Admitted.

Lemma RInt_Iverson_ge'''' {F y} : RInt (λ x0 : R, F x0) 0 y = RInt (λ x0 : R, Iverson (Rge y) x0 * F x0) 0 1.
Proof. Admitted.

Lemma ex_seriesC_single {F N} : ex_seriesC (λ n : nat, Iverson (eq N) n * (F n)).
Proof. Admitted.

End Indicators.

Section Lib.
Import Hierarchy.
(* General analysis facts *)
  
Lemma RInt_add {F1 F2 : R → R} {a b : R} (H1 : ex_RInt F1 a b) (H2 : ex_RInt F2 a b) :
  RInt F1 a b  + RInt F2 a b = RInt (fun x => F1 x + F2 x) a b.
Proof. Admitted.

Lemma RInt_Rmult {F : R → R} {a b r : R} : r * RInt F a b = RInt (fun x => r * F x) a b.
Proof. Admitted.

Lemma RInt_Rmult' {F : R → R} {a b r : R} : (RInt F a b) * r = RInt (fun x => F x * r) a b.
Proof. Admitted.

Lemma ex_RInt_Rmult {F : R → R} {a b r : R} : ex_RInt F a b → ex_RInt (fun x => r * F x) a b.
Proof. Admitted.

Lemma ex_RInt_Rmult' {F : R → R} {a b r : R} : ex_RInt F a b → ex_RInt (fun x => F x * r) a b.
Proof. Admitted.

Lemma ex_RInt_pow {a b N} : ex_RInt (λ y : R, y ^ N) a b.
Proof. Admitted.

Lemma Rexp_nn {z} : 0 <= exp z.
Proof. Admitted.

Lemma Rexp_range {z : R} : z <= 0 -> 0 <= exp z <= 1.
Proof. Admitted.

Lemma ex_RInt_add' (f g : R → R) {h : R → R} {a b : R} (Ha : ex_RInt f a b) (Hb : ex_RInt g a b)
   (Hext : ∀ x, a <= x <= b → f x + g x = h x) : ex_RInt h a b.
Proof. Admitted. (* Check ex_RInt_plus. *)

Lemma ex_RInt_add  {f g : R → R} {a b : R} (Ha : ex_RInt f a b) (Hb : ex_RInt g a b) :
  ex_RInt (fun x => f x + g x) a b.
Proof. Admitted.

Lemma ex_RInt_Iverson_le {x a b}  : ex_RInt (Iverson (Rle x)) a b.
Proof. Admitted.

Lemma ex_RInt_Iverson_ge {x a b}  : ex_RInt (Iverson (Rge x)) a b.
Proof. Admitted.

Lemma ex_RInt_Iverson_eq {x a b}  : ex_RInt (Iverson (eq x)) a b.
Proof. Admitted.

Lemma ex_RInt_Iverson_le' {z a b}  : ex_RInt (Iverson (fun x : R => x <= z)) a b.
Proof. Admitted.

Lemma ex_RInt_Iverson_nle' {z a b}  : ex_RInt (Iverson (fun x : R => ¬ x <= z)) a b.
Proof. Admitted.

Lemma ex_RInt_Iverson_le_uncurry {rx} : ex_RInt (λ y : R, Iverson (uncurry Rle) (y, rx)) 0 1.
Proof. Admitted.

Lemma ex_RInt_Iverson_ge_uncurry {rx} : ex_RInt (λ y : R, Iverson (uncurry Rge) (y, rx)) 0 1.
Proof. Admitted.
(*
Lemma DominatedCvgTheorem {F : nat → R → R} {a b : R} (g : R → R)
  (Hdom : forall n x, Rmin a b <= x <= Rmax a b → 0 <= F n x <= g x)
  (Hint : ex_RInt g a b) :
  is_RInt (fun x => SeriesC (fun n => F n x)) a b (SeriesC (fun n => RInt (fun x => F n x) a b)).
Proof. Admitted.
*)

Lemma ex_RInt_mult (f g : R -> R) (a b : R) :
  ex_RInt f a b ->  ex_RInt g a b ->
  ex_RInt (λ y : R, f y * g y) a b.
Proof.
(* Product of Riemann integrable is Riemann integrable (is this not in the library?) *)
Admitted.

Lemma RInt_pow {a b N} : RInt (λ x : R, x ^ N) a b = b ^ (N + 1)%nat / (N + 1)%nat - a ^ (N + 1)%nat / (N + 1)%nat.
Proof. Admitted.


(* Arzela's Dominated Convergence theorem
Self-contained proof that does not use any measure theory: https://arxiv.org/pdf/1408.1439
Oh, never mind, The theorem presumes that the limit we're trying to prove exists and this cannot
be easily eliminated from the proof.

The monotone convergence theorem for Riemann integrals also assumes the limit is integrable.

In fact, even the Riemann version of the Dominated Convergence theorem has this problem!

Can I prove this for when F is (piecewise) uniformly continuous? ie. continuous, since [a, b] is compact.

Fubini's theorem gives a stronger condition: The set of discontinuities has measure 0.
Here the set of discontinuities is equal to at least every horizontal line (n parameter) plus any discontinuities
associated to the first parameter.

In any case, we are restricting the _continuity_ of the function F, not its integrability, which is stronger.


Proof. Admitted.

 *)


Definition Continuity2 (f : (R * R) -> R) (x y : R) : Prop :=
  filterlim f (locally (x, y)) (locally (f (x, y))).

Definition Discontinuities2 (f : R * R -> R) : R * R -> Prop :=
  fun '(x, y) => ¬ Continuity2 f x y.

(* A set is negligible if it can be covered by countably many balls of arbitrarily small total volume. *)
Definition Negligible (S : R * R -> Prop) : Prop :=
  ∀ (ε : posreal), ∃ (c : nat -> R * R) (r : nat -> nonnegreal),
    (SeriesC (fun n => r n * r n) < ε) /\
    (∀ x, S x -> ∃ n, ball (c n) (r n) x).

Theorem Negligible_Empty : Negligible (fun _ => False).
Proof.
  intro ε.
  exists (fun _ => (0, 0)), (fun _ => mknonnegreal 0 (Rle_refl 0)); constructor.
  { simpl. rewrite SeriesC_0; [apply cond_pos | ]. intros ?; lra. }
  intros ? [].
Qed.

(* Sets *)

Definition Icc (a b : R) : R -> Prop :=
  fun t => Rmin a b <= t <= Rmax a b.

Definition Ici (a : R) : R -> Prop :=
  fun t => a <= t.

Definition Iic (b : R) : R -> Prop :=
  fun t => t <= b.

Definition Iii : R -> Prop :=
  fun t => True.

Definition RII (X Y : R -> Prop) : R * R -> Prop :=
  fun '(tx, ty) => X tx /\ Y ty.

Definition On {T} (S U : T -> Prop) : Prop :=
  ∀ t, S t -> U t.

Definition Int {T} (S U : T -> Prop) : T -> Prop :=
  fun t => S t /\ U t.

Definition Bounded (f : R * R -> R) (M : R) : R * R -> Prop :=
  fun t => Rabs (f t) <= M.

(*
Definition NRtoRR (F : nat → R → R) : R → R → R :=
  fun x y => F (Rcomplements.floor1 x) y.
  (HC : Negligible (Int (RII (Icc xa xb) (Icc ya yb)) (Discontinuities2 f))) :
*)

(* Not 100% sure yet *)
Lemma FubiniNatR_ex {F : nat → R → R} {a b : R} (g : R → R)
  (Hcont : False) :
  ex_RInt (fun x => SeriesC (fun n => F n x)) a b.
Admitted.

(* I need either ex_SeriesC or maybe nn *)
Lemma SeriesC_nat_shift {f : nat → R} : SeriesC f = f 0%nat + SeriesC (f ∘ S).
Proof.
  (* replace (SeriesC f) with (SeriesC (fun n => Iverson (eq 0%nat) n * f 0%nat) + SeriesC (fun n => Iverson (not ∘ eq 0%nat) n * f n)); last first. *)
      (* Locate Series_incr_1. << This is it *)
Admitted.

Lemma ex_SeriesC_nat_shift {f : nat → R} : ex_seriesC f → ex_seriesC (f ∘ S).
Proof. Admitted.

(*
(* Key lemma ? *)
Lemma SeriesC_even_contract {f : nat → R} :
  SeriesC (fun n => Iverson Zeven (Z.of_nat n) * f n) = SeriesC (fun n => f (2 * n)%nat).
Proof.
  apply Rle_antisym.
  { SeriesC_le_inj.
  Search (?x <= ?y) (?y <= ?x) (?x = ?y).
Admitted.
*)

Lemma Zeven_pow {x} {n : nat} (H : Zeven (Z.of_nat n)) : 0 <= x ^ n.
Proof.
  destruct (Zeven_ex _ H) as [m Hm].
  rewrite -(Nat2Z.id n) Hm.
  rewrite Z2Nat.inj_mul; try lia.
  rewrite pow_mult.
  apply pow_le.
  apply pow2_ge_0.
Qed.

Lemma Zodd_neg_pow {n : nat} (H : Zodd (Z.of_nat n)) : (-1) ^ n = (-1).
Proof.
  destruct (Zodd_ex _ H) as [m Hm].
  rewrite -(Nat2Z.id n) Hm.
  rewrite Z2Nat.inj_add; try lia.
  rewrite Z2Nat.inj_mul; try lia.
  rewrite pow_add.
  rewrite pow_1.
  rewrite pow_mult.
  replace (((-1) ^ Z.to_nat 2)) with 1.
  { rewrite pow1. lra. }
  simpl. lra.
Qed.

Definition Hpow x : R := @SeriesC _ numbers.Nat.eq_dec nat_countable (λ k : nat, x ^ k / fact k).
Definition HpowE x : R := @SeriesC _ numbers.Nat.eq_dec nat_countable (λ k : nat, Iverson Zeven k * x ^ k / fact k).
Definition HpowO x : R := @SeriesC _ numbers.Nat.eq_dec nat_countable (λ k : nat, Iverson (not ∘ Zeven) k * x ^ k / fact k).
Definition HpowOS x : R := @SeriesC _ numbers.Nat.eq_dec nat_countable ((λ k : nat, Iverson (not ∘ Zeven) k * x ^ k / fact k) ∘ S).
Definition HpowES x : R := @SeriesC _ numbers.Nat.eq_dec nat_countable ((λ k : nat, Iverson Zeven k * x ^ k / fact k) ∘ S).

Lemma Hpow_cf {x} : Hpow x = exp x.
Proof. by rewrite /Hpow SeriesC_Series_nat -PSeries.PSeries_eq ElemFct.exp_Reals. Qed.

Lemma Hpow_ex : forall y, ex_seriesC (λ k : nat, y ^ k / fact k).
Proof.
  intro y.
  replace (λ k : nat, y ^ k / fact k) with (λ k : nat, / fact k * y ^ k); last first.
  { apply functional_extensionality. intros ?. lra. }
  have Hex : PSeries.ex_pseries (fun k => / fact k) y.
  { (* I'm shocked this isn't proven somewhere...*)
    apply PSeries.CV_disk_correct.
    apply (PSeries.CV_disk_DAlembert _ _ 0); [| | intuition].
    { intros n.
      have ? : 0 < / fact n; [|lra].
      apply Rinv_0_lt_compat.
      apply INR_fact_lt_0.
    }
    { rewrite Lim_seq.is_lim_seq_Reals. apply Alembert_exp. }
  }
  rewrite PSeries.ex_pseries_R in Hex.
  by rewrite ex_seriesC_nat in Hex.
Qed.


Lemma HpowE_ex {x} : ex_seriesC (λ k : nat, Iverson Zeven k * x ^ k / fact k).
Proof.
  apply (ex_seriesC_le _ (λ k : nat, (Rabs x) ^ k / fact k)); last apply Hpow_ex.
  intros n.
  split.
  { rewrite /Iverson.
    case_decide; [|lra].
    rewrite Rmult_1_l.
    apply Rcomplements.Rdiv_le_0_compat; [|apply INR_fact_lt_0].
    by apply Zeven_pow.
  }
  { rewrite /Iverson.
    case_decide.
    { rewrite Rmult_1_l.
      rewrite Rdiv_def.
      apply Rmult_le_compat_r.
      { have HH := INR_fact_lt_0 n. apply Rinv_0_lt_compat in HH. lra. }
      apply pow_maj_Rabs.
      lra.
    }
    { rewrite Rmult_0_l Rdiv_0_l.
      apply Rcomplements.Rdiv_le_0_compat; [|apply INR_fact_lt_0].
      apply pow_le.
      apply Rabs_pos.
    }
  }
Qed.


Lemma HpowO_ex {x} : ex_seriesC (λ k : nat, Iverson (not ∘ Zeven) k * x ^ k / fact k).
Proof.
  destruct (decide (Rle 0 x)).
  { apply (ex_seriesC_le _ (λ k : nat, (Rabs x) ^ k / fact k)); last apply Hpow_ex.
    intro n; split.
    { rewrite /Iverson.
      case_decide; [|lra].
      rewrite Rmult_1_l.
      apply Rcomplements.Rdiv_le_0_compat; [|apply INR_fact_lt_0].
      apply pow_le.
      lra.
    }
    { rewrite /Iverson.
      case_decide.
      { rewrite Rmult_1_l.
        rewrite Rdiv_def.
        apply Rmult_le_compat_r.
        { have HH := INR_fact_lt_0 n. apply Rinv_0_lt_compat in HH. lra. }
        apply pow_maj_Rabs.
        lra.
      }
      { rewrite Rmult_0_l Rdiv_0_l.
        apply Rcomplements.Rdiv_le_0_compat; [|apply INR_fact_lt_0].
        apply pow_le.
        apply Rabs_pos.
      }
    }
  }
  { pose x' := (-1) * x.
    replace (λ k : nat, Iverson (not ∘ Zeven) k * x ^ k / fact k)
       with (λ k : nat, (-1) * (Iverson (not ∘ Zeven) k * x' ^ k / fact k)); last first.
    { apply functional_extensionality. intros k. rewrite /x'.
      rewrite /Iverson.
      case_decide.
      { rewrite Rmult_1_l Rmult_1_l.
        rewrite Rpow_mult_distr.
        rewrite Zodd_neg_pow; [lra|].
        destruct (Zeven_odd_dec k); intuition.
        exfalso; apply H; intuition.
      }
      { by rewrite Rmult_0_l Rmult_0_l Rdiv_0_l Rmult_0_r. }
    }
    apply ex_seriesC_scal_l.
    apply (ex_seriesC_le _ (λ k : nat, (Rabs x') ^ k / fact k)); last apply Hpow_ex.
    intro n'; split.
    { rewrite /Iverson.
      case_decide; [|lra].
      rewrite Rmult_1_l.
      apply Rcomplements.Rdiv_le_0_compat; [|apply INR_fact_lt_0].
      apply pow_le.
      rewrite /x'.
      lra.
    }
    { rewrite /Iverson.
      case_decide.
      { rewrite Rmult_1_l.
        rewrite Rdiv_def.
        apply Rmult_le_compat_r.
        { have HH := INR_fact_lt_0 n'. apply Rinv_0_lt_compat in HH. lra. }
        apply pow_maj_Rabs.
        lra.
      }
      { rewrite Rmult_0_l Rdiv_0_l.
        apply Rcomplements.Rdiv_le_0_compat; [|apply INR_fact_lt_0].
        apply pow_le.
        apply Rabs_pos.
      }
    }
  }
Qed.

Lemma HpowOS_ex {x} : ex_seriesC ((λ k : nat, Iverson (not ∘ Zeven) k * x ^ k / fact k) ∘ S).
Proof. apply ex_SeriesC_nat_shift. apply HpowO_ex. Qed.

Lemma HpowES_ex {x} : ex_seriesC ((λ k : nat, Iverson Zeven k * x ^ k / fact k) ∘ S).
Proof. apply ex_SeriesC_nat_shift. apply HpowE_ex. Qed.

Lemma Hpow_eq {x} : Hpow x = HpowE x + HpowO x.
Proof.
  rewrite /Hpow/HpowE/HpowO.
  rewrite -SeriesC_plus; [| apply HpowE_ex | apply HpowO_ex].
  apply SeriesC_ext. intros n. rewrite //=.
  rewrite -Rmult_plus_distr_r.
  rewrite -Rmult_plus_distr_r.
  rewrite Rmult_assoc.
  rewrite -(Rmult_1_l (x ^ n / fact n)).
  f_equal.
  by rewrite Iverson_add_neg.
Qed.

Lemma HpowO_eq {x} : HpowO x = HpowOS x.
Proof.
  rewrite /HpowO/HpowOS.
  rewrite SeriesC_nat_shift.
  rewrite Iverson_False; [|simpl; intuition].
  by rewrite Rmult_0_l Rdiv_def Rmult_0_l Rplus_0_l.
Qed.

Lemma HpowE_eq {x} : HpowE x = 1 + HpowES x.
Proof.
  rewrite /HpowE/HpowES.
  rewrite SeriesC_nat_shift.
  rewrite Iverson_True; [|simpl; intuition].
  f_equal.
  rewrite //=. lra.
Qed.

Lemma ExpSeriesEven {x} : SeriesC (λ n : nat, Iverson Zeven n * (x^n/(fact n) + x^(n+1)%nat/(fact (n+1)%nat))) = exp x.
Proof.
    rewrite -Hpow_cf.
    rewrite Hpow_eq.
    rewrite HpowO_eq.
    rewrite /HpowOS/HpowE.
    rewrite -SeriesC_plus; [| apply HpowE_ex | apply HpowOS_ex ].
    apply SeriesC_ext. intros n. rewrite //=.
    replace (Iverson (not ∘ Zeven) (S n)) with (Iverson Zeven n); last first.
    { rewrite /Iverson.
      Opaque Zeven.
      case_decide.
      { rewrite decide_True //=.
        apply Zodd_not_Zeven.
        replace (Z.of_nat (S n)%nat) with (Z.succ (Z.of_nat n)) by lia.
        by apply Zodd_Sn.
      }
      { rewrite decide_False //=.
        apply P_NNP.
        replace (Z.of_nat (S n)%nat) with (Z.succ (Z.of_nat n)) by lia.
        apply Zeven_Sn.
        destruct (Zeven_odd_dec n);  intuition. (* lol *)
      }
      Transparent Zeven.
    }
    repeat rewrite Rdiv_def.
    rewrite Rmult_assoc.
    rewrite Rmult_assoc.
    rewrite -Rmult_plus_distr_l.
    do 3 f_equal.
    { by rewrite pow_add Rmult_comm pow_1. }
    { f_equal. by rewrite -{1}(Nat.mul_1_l (fact n)) -Nat.mul_add_distr_r Nat.add_1_l Nat.add_1_r -fact_simpl. }
  Qed.

  Lemma ExpSeriesOdd {x} : SeriesC (λ n : nat, Iverson (not ∘ Zeven) n * (x^n/(fact n) + x^(n+1)%nat/(fact (n+1)%nat))) = -1 + exp x .
  Proof.
    rewrite -Hpow_cf.
    rewrite Hpow_eq.
    rewrite HpowE_eq.
    repeat rewrite -Rplus_assoc.
    rewrite Rplus_opp_l Rplus_0_l.
    rewrite /HpowES/HpowO.
    rewrite -SeriesC_plus; [| apply HpowES_ex | apply HpowO_ex ].
    apply SeriesC_ext. intros n. rewrite //=.
    replace (Iverson Zeven (S n)) with (Iverson (not ∘ Zeven) n); last first.
    { rewrite /Iverson.
      Opaque Zeven.
      case_decide.
      { rewrite decide_True //=.
        replace (Z.of_nat (S n)%nat) with (Z.succ (Z.of_nat n)) by lia.
        apply Zeven_Sn.
        destruct (Zeven_odd_dec n);  intuition. (* lol *)
        exfalso; apply H; apply z.
      }
      { rewrite decide_False //=.
        simpl in H.
        apply NNP_P in H.
        replace (Z.of_nat (S n)%nat) with (Z.succ (Z.of_nat n)) by lia.
        apply Zodd_Sn in H.
        intro HK.
        apply Zodd_not_Zeven in H.
        apply H, HK.
      }
      Transparent Zeven.
    }
    repeat rewrite Rdiv_def.
    repeat rewrite Rmult_assoc.
    rewrite -Rmult_plus_distr_l.
    do 1 f_equal.
    rewrite Rplus_comm.
    f_equal.
    repeat rewrite -Rmult_assoc.
    f_equal.
    { by rewrite pow_add Rmult_comm pow_1. }
    { f_equal. by rewrite -{1}(Nat.mul_1_l (fact n)) -Nat.mul_add_distr_r Nat.add_1_l Nat.add_1_r -fact_simpl. }
  Qed.

  (* I think this can be done by the addition formula using subtraction. Otherwise: taylor series. Otherwise: sad. *)
  Lemma exp_mono {x y : R} : x <= y → exp x <= exp y.
  Proof. Admitted.

  Lemma exp_mono_strict {x y : R} : x < y → exp x < exp y.
  Proof. Admitted.

  Lemma ex_seriesC_mult {f g : nat → R} (Hf : ∀ n : nat, 0 <= f n) (Hg : ∀ n : nat, 0 <= g n) :
    ex_seriesC f → ex_seriesC g → ex_seriesC (fun n => f n * g n).
  Proof. Admitted.

  (* Weierstrass M test, Rudin 7.10 *)
  Lemma UniformConverge_Series {F : R → nat → R} (UB : nat → R) :
    (Series.ex_series UB) →
    (forall x n, Rabs (F x n) <= UB n) →
    filterlim (fun (M : nat) (x : R) => sum_n (F x) M) eventually (locally (λ x : R, Series.Series (F x))).
  Proof. Admitted.

  Lemma ex_RInt_sum_n {a b M} {F : nat → R → R} :
    (∀ n, ex_RInt (F n) a b) → ex_RInt (λ x : R, sum_n (λ n : nat, F n x) M) a b .
  Proof. Admitted.

  Definition Ioo (a b : R) : R → Prop := fun x => Rmin a b < x < Rmax a b.

  Lemma ex_RInt_dom {F : R → R} {a b : R} : ex_RInt (fun x => Iverson (Ioo a b) x * F x) a b ↔ ex_RInt F a b.
  Proof. Admitted.

End Lib.
