From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real.
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

Lemma Rexp_nn {z} : 0 <= exp z.
Proof. Admitted.

Lemma Rexp_range {z : R} : z <= 0 -> 0 <= exp z <= 1.
Proof. Admitted.

End Lib.
