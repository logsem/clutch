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

End Indicators.
