From clutch.eris.examples.math Require Import prelude.
From clutch.eris Require Import infinite_tape.

Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.



(** A basic theory of Indicator functions*)

Section Indicators.

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

End Indicators.


Section Pairity.

Lemma Iverson_Zeven_Sn n : Iverson (not ∘ Zeven) (S n) = Iverson Zeven n.
Proof.
  rewrite /Iverson.
  Opaque Zeven.
  case_decide; case_decide; simpl in *; try done.
  - exfalso.
    replace (Z.of_nat (S n)) with (Z.succ (Z.of_nat n)) in H by lia.
    destruct (Zeven_odd_dec n).
    + intuition.
    + apply Zeven_Sn in z. contradiction.
  - exfalso.
    replace (Z.of_nat (S n)) with (Z.succ (Z.of_nat n)) in H by lia.
    apply Zodd_Sn in H0.
    apply NNP_P in H.
    by apply (Zeven_not_Zodd (Z.succ n)).
  Transparent Zeven.
Qed.

Lemma Iverson_Zeven_Sn' n : Iverson Zeven (S n) = Iverson (not ∘ Zeven) n.
Proof.
  rewrite /Iverson.
  case_decide; case_decide; try lra.
  { exfalso.
    rewrite //= in H0.
    apply NNP_P in H0.
    apply Zodd_Sn in H0.
    apply (Zeven_not_Zodd _ H).
    by rewrite Nat2Z.inj_succ.
  }
  { exfalso.
    rewrite //= in H0.
    apply H.
    rewrite Nat2Z.inj_succ.
    apply Zeven_Sn.
    destruct (Zeven_odd_dec n); try done.
  }
Qed.

End Pairity.


Section Integral.

Ltac replace_ext X Y :=
  replace X with Y; [| apply functional_extensionality; intros; auto].

Lemma RInt_Iverson_ge {rx F} (Hrx : 0 <= rx <= 1) (Hex : ex_RInt (λ x : R, F x) rx 1) :
  RInt (λ x : R, Iverson (uncurry Rge) (x, rx) * F x) 0 1 = RInt (λ x : R, F x) rx 1.
Proof.
  rewrite -(RInt_Chasles (λ x : R, Iverson (uncurry Rge) (x, rx) * F x) 0 rx 1) /plus //=.
  { replace (RInt (λ x : R, Iverson (uncurry Rge)  (x, rx) * F x) 0 rx) with (RInt (fun x : R => 0) 0 rx); last first.
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
  rewrite -(RInt_Chasles (λ x : R, Iverson (λ x0 : R, ¬ x0 <= rx) x * F x) 0 rx 1) /plus //=.
  { replace (RInt (λ x : R, Iverson (λ x0 : R, ¬ x0 <= rx) x * F x) 0 rx) with (RInt (fun x : R => 0) 0 rx); last first.
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
  { replace (RInt (λ x : R, Iverson (uncurry Rle)  (x, rx) * F x) rx 1) with (RInt (fun x : R => 0) rx 1); last first.
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
    replace (RInt (Iverson (Rle x)) x 1) with (RInt (fun _ : R => 1) x 1); last first.
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
    replace (RInt (Iverson (Rge x)) x 1) with (RInt (fun _ : R => 0) x 1); last first.
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

Lemma ex_RInt_Iverson_le {x a b}  : ex_RInt (Iverson (Rle x)) a b.
Proof.
  apply (ex_RInt_Chasles _ a x b).
  { case (decide (x < a)).
    { intros ?.
      apply (ex_RInt_ext (fun _ => 1)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_True; [lra|].
      rewrite Rmin_right in H; [|lra].
      rewrite Rmax_left in H; [|lra].
      lra.
    }
    { intros ?.
      apply (ex_RInt_ext (fun _ => 0)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      lra.
    }
  }
  { case (decide (x < b)).
    { intros ?.
      apply (ex_RInt_ext (fun _ => 1)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_True; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      lra.
    }
    { intros ?.
      apply (ex_RInt_ext (fun _ => 0)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_right in H; [|lra].
      rewrite Rmax_left in H; [|lra].
      lra.
    }
  }
Qed.

Lemma ex_RInt_Iverson_ge {x a b}  : ex_RInt (Iverson (Rge x)) a b.
Proof.
  apply (ex_RInt_Chasles _ a x b).
  { case (decide (x < a)).
    { intros ?.
      apply (ex_RInt_ext (fun _ => 0)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_right in H; [|lra].
      rewrite Rmax_left in H; [|lra].
      lra.
    }
    { intros ?.
      apply (ex_RInt_ext (fun _ => 1)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_True; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      lra.
    }
  }
  { case (decide (x < b)).
    { intros ?.
      apply (ex_RInt_ext (fun _ => 0)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      lra.
    }
    { intros ?.
      apply (ex_RInt_ext (fun _ => 1)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_True; [lra|].
      rewrite Rmin_right in H; [|lra].
      rewrite Rmax_left in H; [|lra].
      lra.
    }
  }
Qed.

Lemma ex_RInt_Iverson_eq {x a b}  : ex_RInt (Iverson (eq x)) a b.
Proof.
  apply (ex_RInt_Chasles _ a x b).
  { case (decide (x < a)).
    { intros ?.
      apply (ex_RInt_ext (fun _ => 0)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_right in H; [|lra].
      rewrite Rmax_left in H; [|lra].
      lra.
    }
    { intros ?.
      apply (ex_RInt_ext (fun _ => 0)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      lra.
    }
  }
  { case (decide (x < b)).
    { intros ?.
      apply (ex_RInt_ext (fun _ => 0)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      lra.
    }
    { intros ?.
      apply (ex_RInt_ext (fun _ => 0)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_right in H; [|lra].
      rewrite Rmax_left in H; [|lra].
      lra.
    }
  }
Qed.

Lemma ex_RInt_Iverson_le' {z a b}  : ex_RInt (Iverson (fun x : R => x <= z)) a b.
Proof.
  apply (ex_RInt_Chasles _ a z b).
  { case (decide (z < a)).
    { intros ?.
      apply (ex_RInt_ext (fun _ => 0)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_right in H; [|lra].
      rewrite Rmax_left in H; [|lra].
      lra.
    }
    { intros ?.
      apply (ex_RInt_ext (fun _ => 1)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_True; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      lra.
    }
  }
  { case (decide (z < b)).
    { intros ?.
      apply (ex_RInt_ext (fun _ => 0)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      lra.
    }
    { intros ?.
      apply (ex_RInt_ext (fun _ => 1)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_True; [lra|].
      rewrite Rmin_right in H; [|lra].
      rewrite Rmax_left in H; [|lra].
      lra.
    }
  }
Qed.

Lemma ex_RInt_Iverson_nle' {z a b}  : ex_RInt (Iverson (fun x : R => ¬ x <= z)) a b.
Proof.
  apply (ex_RInt_Chasles _ a z b).
  { case (decide (z < a)).
    { intros ?.
      apply (ex_RInt_ext (fun _ => 1)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_True; [lra|].
      rewrite Rmin_right in H; [|lra].
      rewrite Rmax_left in H; [|lra].
      lra.
    }
    { intros ?.
      apply (ex_RInt_ext (fun _ => 0)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      lra.
    }
  }
  { case (decide (z < b)).
    { intros ?.
      apply (ex_RInt_ext (fun _ => 1)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_True; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      lra.
    }
    { intros ?.
      apply (ex_RInt_ext (fun _ => 0)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_right in H; [|lra].
      rewrite Rmax_left in H; [|lra].
      lra.
    }
  }
Qed.

Lemma ex_RInt_Iverson_le_uncurry {rx} : ex_RInt (λ y : R, Iverson (uncurry Rle) (y, rx)) 0 1.
Proof.
  apply (ex_RInt_Chasles _ 0 rx 1).
  { case (decide (rx < 0)).
    { intros ?.
      apply (ex_RInt_ext (fun _ => 0)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_right in H; [|lra].
      rewrite Rmax_left in H; [|lra].
      rewrite /uncurry//=.
      lra.
    }
    { intros ?.
      apply (ex_RInt_ext (fun _ => 1)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_True; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      rewrite /uncurry//=.
      lra.
    }
  }
  { case (decide (rx < 1)).
    { intros ?.
      apply (ex_RInt_ext (fun _ => 0)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      rewrite /uncurry//=.
      lra.
    }
    { intros ?.
      apply (ex_RInt_ext (fun _ => 1)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_True; [lra|].
      rewrite Rmin_right in H; [|lra].
      rewrite Rmax_left in H; [|lra].
      rewrite /uncurry//=.
      lra.
    }
  }
Qed.

Lemma ex_RInt_Iverson_ge_uncurry {rx} : ex_RInt (λ y : R, Iverson (uncurry Rge) (y, rx)) 0 1.
Proof.
  apply (ex_RInt_Chasles _ 0 rx 1).
  { case (decide (rx < 0)).
    { intros ?.
      apply (ex_RInt_ext (fun _ => 1)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_True; [lra|].
      rewrite Rmin_right in H; [|lra].
      rewrite Rmax_left in H; [|lra].
      rewrite /uncurry//=.
      lra.
    }
    { intros ?.
      apply (ex_RInt_ext (fun _ => 0)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      rewrite /uncurry//=.
      lra.
    }
  }
  { case (decide (rx < 1)).
    { intros ?.
      apply (ex_RInt_ext (fun _ => 1)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_True; [lra|].
      rewrite Rmin_left in H; [|lra].
      rewrite Rmax_right in H; [|lra].
      rewrite /uncurry//=.
      lra.
    }
    { intros ?.
      apply (ex_RInt_ext (fun _ => 0)); [|apply ex_RInt_const].
      intros ??.
      rewrite Iverson_False; [lra|].
      rewrite Rmin_right in H; [|lra].
      rewrite Rmax_left in H; [|lra].
      rewrite /uncurry//=.
      lra.
    }
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

End Integral.
