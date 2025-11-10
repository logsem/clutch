From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis RInt_gen AutoDerive.
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

Lemma RInt_Iverson_ge {rx F} (Hrx : 0 <= rx <= 1) (Hex : ex_RInt (λ x : R, F x) rx 1) :
  RInt (λ x : R, Iverson (uncurry Rge) (x, rx) * F x) 0 1 = RInt (λ x : R, F x) rx 1.
Proof.
  rewrite -(RInt_Chasles (λ x : R, Iverson (uncurry Rge) (x, rx) * F x) 0 rx 1) /plus //=.
  { replace (RInt (λ x : R, ⟦ uncurry Rge ⟧ (x, rx) * F x) 0 rx) with (RInt (fun x : R => 0) 0 rx); last first.
    { apply RInt_ext; intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      rewrite //=; lra.
    }
    rewrite RInt_const.
    rewrite /scal//=/mult//= Rmult_0_r Rplus_0_l.
    apply RInt_ext; intros ??.
    rewrite Iverson_True; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=. lra.
  }
  { apply (ex_RInt_ext (fun _ : R => 0)); last apply ex_RInt_const.
    intros ??.
    rewrite Iverson_False; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=; lra.
  }
  { apply (ex_RInt_ext (fun x : R => F x)); last apply Hex.
    intros ??.
    rewrite Iverson_True; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=; lra.
  }
Qed.

Lemma RInt_Iverson_ge' {rx F} (Hrx : 0 <= rx <= 1) (Hex : ex_RInt (λ x : R, F x) rx 1) :
  RInt (λ x : R, Iverson (fun x  => not (Rle x rx)) x * F x) 0 1 =  RInt (λ x : R, F x) rx 1.
Proof.
  rewrite -(RInt_Chasles (λ x : R, ⟦ λ x0 : R, ¬ x0 <= rx ⟧ x * F x) 0 rx 1) /plus //=.
  { replace (RInt (λ x : R, ⟦ λ x0 : R, ¬ x0 <= rx ⟧ x * F x) 0 rx) with (RInt (fun x : R => 0) 0 rx); last first.
    { apply RInt_ext; intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      rewrite //=; lra.
    }
    rewrite RInt_const.
    rewrite /scal//=/mult//= Rmult_0_r Rplus_0_l.
    apply RInt_ext; intros ??.
    rewrite Iverson_True; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=. lra.
  }
  { apply (ex_RInt_ext (fun _ : R => 0)); last apply ex_RInt_const.
    intros ??.
    rewrite Iverson_False; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=; lra.
  }
  { apply (ex_RInt_ext (fun x : R => F x)); last apply Hex.
    intros ??.
    rewrite Iverson_True; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=; lra.
  }
Qed.

Lemma RInt_Iverson_le {rx F} (Hrx : 0 <= rx <= 1) (Hex : ex_RInt (λ x : R, F x) 0 rx):
  RInt (λ x : R, Iverson (uncurry Rle) (x, rx) * F x) 0 1 = RInt (λ x : R, F x) 0 rx.
Proof.
  rewrite -(RInt_Chasles (λ x : R, Iverson (uncurry Rle) (x, rx) * F x) 0 rx 1) /plus //=.
  { replace (RInt (λ x : R, ⟦ uncurry Rle ⟧ (x, rx) * F x) rx 1) with (RInt (fun x : R => 0) rx 1); last first.
    { apply RInt_ext; intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      rewrite //=; lra.
    }
    rewrite RInt_const.
    rewrite /scal//=/mult//= Rmult_0_r Rplus_0_r.
    apply RInt_ext; intros ??.
    rewrite Iverson_True; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=. lra.
  }
  { apply (ex_RInt_ext (fun x : R => F x)); last apply Hex.
    intros ??.
    rewrite Iverson_True; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=; lra.
  }
  { apply (ex_RInt_ext (fun _ : R => 0)); last apply ex_RInt_const.
    intros ??.
    rewrite Iverson_False; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=; lra.
  }
Qed.

Lemma RInt_Iverson_le'' {rx F} (Hrx : 0 <= rx <= 1) (Hex : ex_RInt (λ x : R, F x) 0 rx) :
  RInt (λ x : R, Iverson (Rle x) rx * F x) 0 1 =  RInt (λ x : R, F x) 0 rx.
Proof.
  rewrite -(RInt_Chasles (λ x : R, Iverson (Rle x) rx * F x) 0 rx 1) /plus //=.
  { replace (RInt  (λ x : R, Iverson (Rle x) rx * F x) rx 1) with (RInt (fun x : R => 0) rx 1); last first.
    { apply RInt_ext; intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      rewrite //=; lra.
    }
    rewrite RInt_const.
    rewrite /scal//=/mult//= Rmult_0_r Rplus_0_r.
    apply RInt_ext; intros ??.
    rewrite Iverson_True; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=. lra.
  }
  { apply (ex_RInt_ext (fun x : R => F x)); last apply Hex.
    intros ??.
    rewrite Iverson_True; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=; lra.
  }
  { apply (ex_RInt_ext (fun _ : R => 0)); last apply ex_RInt_const.
    intros ??.
    rewrite Iverson_False; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=; lra.
  }
Qed.

Lemma RInt_Iverson_ge'' {rx F} (Hrx : 0 <= rx <= 1) (Hex : ex_RInt (λ x : R, F x) rx 1) :
  RInt (λ x : R, Iverson (Rge x) rx * F x) 0 1 =  RInt (λ x : R, F x) rx 1.
Proof.
  rewrite -(RInt_Chasles (λ x : R, Iverson (Rge x) rx * F x) 0 rx 1) /plus //=.
  { replace (RInt (λ x : R, Iverson (Rge x) rx * F x) 0 rx) with (RInt (fun x : R => 0) 0 rx); last first.
    { apply RInt_ext; intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      rewrite //=; lra.
    }
    rewrite RInt_const.
    rewrite /scal//=/mult//= Rmult_0_r Rplus_0_l.
    apply RInt_ext; intros ??.
    rewrite Iverson_True; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=. lra.
  }
  { apply (ex_RInt_ext (fun _ : R => 0)); last apply ex_RInt_const.
    intros ??.
    rewrite Iverson_False; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=; lra.
  }
  { apply (ex_RInt_ext (fun x : R => F x)); last apply Hex.
    intros ??.
    rewrite Iverson_True; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=; lra.
  }
Qed.

Lemma RInt_Iverson_le''' {x} (Hx : 0 <= x <= 1) : RInt (Iverson (Rle x)) 0 1 = 1 - x.
Proof.
  rewrite -(RInt_Chasles (Iverson (Rle x)) 0 x 1).
  { replace (RInt (Iverson (Rle x)) 0 x) with (RInt (fun x : R => 0) 0 x); last first.
    { apply RInt_ext; intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      rewrite //=; lra.
    }
    rewrite RInt_const.
    rewrite /scal//=/mult//=/plus//= Rmult_0_r Rplus_0_l.
    replace (RInt ⟦ Rle x ⟧ x 1) with (RInt (fun _ : R => 1) x 1); last first.
    { apply RInt_ext; intros ??.
      rewrite Iverson_True; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      rewrite //=; lra.
    }
    rewrite RInt_const.
    rewrite /scal//=/mult//=. lra.
  }
  { apply (ex_RInt_ext (fun x : R => 0)); last apply ex_RInt_const.
    intros ??.
    rewrite Iverson_False; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=; lra.
  }
  { apply (ex_RInt_ext (fun _ : R => 1)); last apply ex_RInt_const.
    intros ??.
    rewrite Iverson_True; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=; lra.
  }
Qed.

Lemma RInt_Iverson_ge''' {x} (Hx : 0 <= x <= 1) : RInt (Iverson (Rge x)) 0 1 = x.
Proof.
  rewrite -(RInt_Chasles (Iverson (Rge x)) 0 x 1).
  { replace (RInt (Iverson (Rge x)) 0 x) with (RInt (fun x : R => 1) 0 x); last first.
    { apply RInt_ext; intros ??.
      rewrite Iverson_True; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      rewrite //=; lra.
    }
    rewrite RInt_const.
    rewrite /scal//=/mult//=/plus//=.
    replace (RInt ⟦ Rge x ⟧ x 1) with (RInt (fun _ : R => 0) x 1); last first.
    { apply RInt_ext; intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      rewrite //=; lra.
    }
    rewrite RInt_const.
    rewrite /scal//=/mult//=. lra.
  }
  { apply (ex_RInt_ext (fun x : R => 1)); last apply ex_RInt_const.
    intros ??.
    rewrite Iverson_True; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=; lra.
  }
  { apply (ex_RInt_ext (fun _ : R => 0)); last apply ex_RInt_const.
    intros ??.
    rewrite Iverson_False; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=; lra.
  }
Qed.

Lemma RInt_Iverson_ge'''' {F y} (Hy : 0 <= y <= 1) (Hex : ex_RInt (λ x : R, F x) 0 y) :
  RInt (λ x0 : R, F x0) 0 y = RInt (λ x0 : R, Iverson (Rge y) x0 * F x0) 0 1.
Proof.
  symmetry.
  rewrite -(RInt_Chasles (λ x0 : R, Iverson (Rge y) x0 * F x0)  0 y 1) /plus //=.
  { replace (RInt  (λ x0 : R, Iverson (Rge y) x0 * F x0) y 1) with (RInt (fun x : R => 0) y 1); last first.
    { apply RInt_ext; intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      rewrite //=; lra.
    }
    rewrite RInt_const.
    rewrite /scal//=/mult//= Rmult_0_r Rplus_0_r.
    apply RInt_ext; intros ??.
    rewrite Iverson_True; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=. lra.
  }
  { apply (ex_RInt_ext (fun x : R => F x)); last apply Hex.
    intros ??.
    rewrite Iverson_True; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=; lra.
  }
  { apply (ex_RInt_ext (fun _ : R => 0)); last apply ex_RInt_const.
    intros ??.
    rewrite Iverson_False; [lra|].
    rewrite Rmin_left in H; [|lra].
    rewrite Rmax_right in H; [|lra].
    rewrite //=; lra.
  }
Qed.

Lemma ex_seriesC_single {F N} : ex_seriesC (λ n : nat, Iverson (eq N) n * (F n)).
Proof.
  replace (λ n : nat, Iverson (eq N) n * (F n)) with (λ n : nat, if bool_decide (n = N) then F N else 0).
  { apply ex_seriesC_singleton. }
  apply functional_extensionality; intros ?.
  case_bool_decide.
  { rewrite Iverson_True; [|intuition]. rewrite H. lra. }
  { rewrite Iverson_False; [|intuition]. lra. }
Qed.

End Indicators.

Section Lib.
Import Hierarchy.
(* General analysis facts *)
  
Lemma RInt_add {F1 F2 : R → R} {a b : R} (H1 : ex_RInt F1 a b) (H2 : ex_RInt F2 a b) :
  RInt F1 a b  + RInt F2 a b = RInt (fun x => F1 x + F2 x) a b.
Proof. rewrite RInt_plus; done. Qed.

Lemma RInt_Rmult {F : R → R} {a b r : R} : r * RInt F a b = RInt (fun x => r * F x) a b.
Proof.
  (* Check RInt_scal. Augh I need another side condition here because non-integrability isn't set to 0 *)
Admitted.

Lemma RInt_Rmult' {F : R → R} {a b r : R} : (RInt F a b) * r = RInt (fun x => F x * r) a b.
Proof. Admitted.

Lemma ex_RInt_Rmult {F : R → R} {a b r : R} : ex_RInt F a b → ex_RInt (fun x => r * F x) a b.
Proof.
  intro H.
  replace (λ x : R, r * F x) with (λ x : R, scal r (F x)); last (apply functional_extensionality; done).
  apply (ex_RInt_scal (V := R_CompleteNormedModule)).
  apply H.
Qed.

Lemma ex_RInt_Rmult' {F : R → R} {a b r : R} : ex_RInt F a b → ex_RInt (fun x => F x * r) a b.
Proof.
  intro H.
  replace (λ x : R, F x * r) with (λ x : R, scal r (F x)); last (apply functional_extensionality; rewrite /scal//=/mult//=; intros ?; lra).
  apply (ex_RInt_scal (V := R_CompleteNormedModule)).
  apply H.
Qed.

Lemma ex_RInt_pow {a b N} : ex_RInt (λ y : R, y ^ N) a b.
Proof.
  apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
  intros ??.
  apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
  by auto_derive.
Qed.

Lemma Rexp_nn {z} : 0 <= exp z.
Proof. have ? := exp_pos z. lra. Qed.

Lemma Rexp_range {z : R} : z <= 0 -> 0 <= exp z <= 1.
Proof.
  split; [apply Rexp_nn|].
  replace z with ((-1) * (-z)) by lra.
  replace (exp (-1 * - z)) with (/ exp (- z) ); last first.
  { apply (Rmult_eq_reg_l (exp (- z))).
    2: { have ? := exp_pos (- z). lra. }
    rewrite -Rdiv_def Rdiv_diag.
    2: { have ? := exp_pos (- z). lra. }
    rewrite -exp_plus.
    replace (- z + -1 * - z) with 0 by lra.
    by rewrite exp_0.
  }
  rewrite -Rinv_1.
  apply Rinv_le_contravar; [lra|].
  eapply Rle_trans.
  2: { eapply exp_ineq1_le. }
  lra.
Qed.

Lemma ex_RInt_add' (f g : R → R) {h : R → R} {a b : R} (Ha : ex_RInt f a b) (Hb : ex_RInt g a b)
   (Hab : a <= b)
   (Hext : ∀ x, a <= x <= b → f x + g x = h x) : ex_RInt h a b.
Proof.
  eapply ex_RInt_ext.
  { rewrite Rmin_left; [|lra].
    rewrite Rmax_right; [|lra].
    intros ??.
    apply Hext.
    lra.
  }
  apply (ex_RInt_plus _ _ _ _ Ha Hb).
Qed.

Lemma ex_RInt_add  {f g : R → R} {a b : R} (Ha : ex_RInt f a b) (Hb : ex_RInt g a b) :
  ex_RInt (fun x => f x + g x) a b.
Proof. apply (ex_RInt_plus _ _ _ _ Ha Hb). Qed.

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

Lemma ex_RInt_mult (f g : R -> R) (a b : R) :
  ex_RInt f a b ->  ex_RInt g a b ->
  ex_RInt (λ y : R, f y * g y) a b.
Proof.
(* Product of Riemann integrable is Riemann integrable (is this not in the library?) *)
Admitted.

Lemma RInt_pow {a b N} : RInt (λ x : R, x ^ N) a b = b ^ (N + 1)%nat / (N + 1)%nat - a ^ (N + 1)%nat / (N + 1)%nat.
Proof. Admitted.


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

(* I need either ex_SeriesC or maybe nn *)
Lemma SeriesC_nat_shift {f : nat → R} : SeriesC f = f 0%nat + SeriesC (f ∘ S).
Proof.
  (* replace (SeriesC f) with (SeriesC (fun n => Iverson (eq 0%nat) n * f 0%nat) + SeriesC (fun n => Iverson (not ∘ eq 0%nat) n * f n)); last first. *)
      (* Locate Series_incr_1. << This is it *)
Admitted.


Lemma SeriesC_nat_shift_rev {f : nat → R} : SeriesC (f ∘ S) = - f 0%nat + SeriesC f.
Proof.
  (* replace (SeriesC f) with (SeriesC (fun n => Iverson (eq 0%nat) n * f 0%nat) + SeriesC (fun n => Iverson (not ∘ eq 0%nat) n * f n)); last first. *)
      (* Locate Series_incr_1. << This is it *)
Admitted.

Lemma ex_SeriesC_nat_shift {f : nat → R} : ex_seriesC f → ex_seriesC (f ∘ S).
Proof. Admitted.

Lemma ex_SeriesC_nat_shiftN_l {f : nat → R} (N : nat) : ex_seriesC (f ∘ (fun n => (n - N))%nat) → ex_seriesC f.
Proof. Admitted.

Lemma ex_SeriesC_nat_shiftN_r {f : nat → R} (N : nat) : ex_seriesC (f ∘ (fun n => (n + N))%nat) → ex_seriesC f.
Proof. Admitted.

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

  Lemma ex_exp_series : Series.ex_series (λ n : nat, / fact n).
  Proof. Admitted.

  Lemma ex_exp_series' {M : nat} : Series.ex_series (λ n : nat, / fact (n - M)).
  Proof. Admitted.

  Definition poke (f : R → R) (a z : R) : R → R := fun x =>
    if (decide (x = a)) then z else f x.


  Lemma ex_RInt_poke {a b c z : R} (f : R → R) (Hf : ex_RInt f a b) (Hi : a < c < b):
    ex_RInt (poke f c z) a b.
  Proof.
    apply (ex_RInt_Chasles  _ _ c).
    { apply (@ex_RInt_ext _ f).
      { intro x. rewrite Rmin_left; try lra. rewrite Rmax_right; try lra. intros ?.
        rewrite /poke. case_decide; try lra. }
      { eapply (@ex_RInt_Chasles_1 R_CompleteNormedModule); last eapply Hf. lra. }
    }
    { apply (@ex_RInt_ext _ f).
      { intro x. rewrite Rmin_left; try lra. rewrite Rmax_right; try lra. intros ?.
        rewrite /poke. case_decide; try lra. }
      { eapply (@ex_RInt_Chasles_2 R_CompleteNormedModule); last eapply Hf. lra. }
    }
  Qed.

  Lemma RInt_poke {a b c z : R} (f : R → R) (Hf : ex_RInt f a b) (Hi : a < c < b) :
    RInt f a b = RInt (poke f c z) a b.
  Proof.
    rewrite -(RInt_Chasles _ _ c).
    3: { eapply (@ex_RInt_Chasles_2 R_CompleteNormedModule); last eapply Hf. lra. }
    2: { eapply (@ex_RInt_Chasles_1 R_CompleteNormedModule); last eapply Hf. lra. }
    rewrite -(RInt_Chasles (poke _ _ _) _ c).
    3: { eapply (@ex_RInt_Chasles_2 R_CompleteNormedModule).
         2: { eapply ex_RInt_poke; [apply Hf |]. lra. }
         lra. }
    2: { eapply (@ex_RInt_Chasles_1 R_CompleteNormedModule).
         2: { eapply ex_RInt_poke; [apply Hf |]. lra. }
         lra. }
    f_equal.
    { apply RInt_ext.
      intro x. rewrite Rmin_left; try lra. rewrite Rmax_right; try lra. intros ?.
      rewrite /poke.
      case_decide; try lra.
    }
    { apply RInt_ext.
      intro x. rewrite Rmin_left; try lra. rewrite Rmax_right; try lra. intros ?.
      rewrite /poke.
      case_decide; try lra.
    }
  Qed.

  Lemma LemDisj : forall (z : fin 2), z = 0%fin ∨ z = 1%fin.
  Proof. Admitted.

  (* Geometric series *)
  Lemma exp_neg_RInt : ex_RInt (λ x : R, exp (- x ^ 2 / 2)) 0 1.
  Proof. Admitted.

  Lemma RInt_pow_fact {a b : R} (M : nat) :
    RInt (fun x1 : R => x1 ^ M / fact M) a b = b ^ (M + 1) / fact (M + 1) - a ^ (M + 1) / fact (M + 1).
  Proof. Admitted.

  Lemma Le_Nat_sum (N : nat) (v : R) : SeriesC (λ n : nat, if bool_decide (n ≤ N) then v else 0) = (N + 1)* v.
  Proof. Admitted.

  Lemma even_pow_neg {x : R} {n : nat} : Zeven n → (- x) ^ n = x ^ n.
  Proof. Admitted.

  Lemma not_even_pow_neg {x : R} {n : nat} : ¬ Zeven n → (- x) ^ n = - x ^ n.
  Proof. Admitted.

  Lemma Geo_ex_SeriesC {𝛾 : R} (H𝛾 : 0 <= 𝛾 <= 1) : ex_seriesC (λ x : nat, 𝛾 ^ x * (1 - 𝛾)).
  Proof. Admitted.

  Lemma exp_inj {x y : R} : exp x = exp y → x = y.
  Proof. Admitted.

  Lemma Derive_exp_neg {x : R} : Derive.Derive (λ x1 : R, exp (- x1)) x = - exp (- x).
  Proof. (* UnaryDiff crap *) Admitted.

  Lemma RInt_gen_ext_eq_Ici {f g : R → R} {M : R} :
    (∀ x : R, M <= x → f x = g x) →
    ex_RInt_gen f (at_point M) (Rbar_locally Rbar.p_infty) →
    RInt_gen f (at_point M) (Rbar_locally Rbar.p_infty) = RInt_gen g (at_point M) (Rbar_locally Rbar.p_infty).
  Proof. Admitted.

  Lemma RInt_gen_ex_Ici {M : R} {F : R → R} (Hex : ∀ b, ex_RInt F M b) :
    ex_RInt_gen F (at_point M) (Rbar_locally (Rbar.p_infty)).
  Proof.
    rewrite /ex_RInt_gen.
    rewrite /is_RInt_gen.
    (* Search filter_prod. *)
  Abort.

  Lemma RInt_sum_n {F : nat → R → R} {a b : R} {M} :
    RInt (fun x : R => sum_n (fun n : nat => F n x) M) a b = sum_n (fun n : nat =>  RInt (fun x : R => F n x) 0 1) M.
  Proof. Admitted.


End Lib.
