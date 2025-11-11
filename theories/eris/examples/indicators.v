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

Lemma RInt_Rmult {F : R → R} {a b r : R} (Hex : ex_RInt F a b) : r * RInt F a b = RInt (fun x => r * F x) a b.
Proof.
  replace (λ x : R, r * F x) with (λ x : R, scal r (F x)) by (rewrite /scal//=/mult//=; lra).
  rewrite RInt_scal.
  { rewrite /scal//=/mult//=; lra. }
  done.
Qed.

Lemma RInt_Rmult' {F : R → R} {a b r : R} (Hex : ex_RInt F a b) : (RInt F a b) * r = RInt (fun x => F x * r) a b.
Proof.
  replace (λ x : R, F x * r) with (λ x : R, scal r (F x)); last (rewrite /scal//=/mult//=; apply functional_extensionality; intros ?; lra).
  rewrite RInt_scal.
  { rewrite /scal//=/mult//=; lra. }
  done.
Qed.

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

Lemma ex_RInt_mult (f g : R -> R) (a b : R) :
  ex_RInt f a b ->  ex_RInt g a b ->
  ex_RInt (λ y : R, f y * g y) a b.
Proof.
  (* Product of Riemann integrable is Riemann integrable (is this not in the library?) *)
Admitted.

Lemma RInt_pow {a b N} : RInt (λ x : R, x ^ N) a b = b ^ (N + 1)%nat / (N + 1)%nat - a ^ (N + 1)%nat / (N + 1)%nat.
Proof.
  have H : (λ x : R, x ^ N) = (Derive.Derive (λ x : R, x ^ (N+1)%nat * / (N +1)%nat)).
  { apply functional_extensionality.
    intros x.
    rewrite Derive.Derive_scal_l.
    rewrite Derive.Derive_pow; [|by auto_derive].
    rewrite Derive.Derive_id.
    replace (Init.Nat.pred (N + 1)) with N; last lia.
    rewrite Rmult_comm Rmult_1_r -Rmult_assoc.
    rewrite Rinv_l; [lra|].
    apply not_0_INR; lia.
  }
  rewrite H.
  rewrite RInt_Derive; [lra| |].
  { intros ??. by auto_derive. }
  { intros ??.
    rewrite -H.
    apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
    by auto_derive.
  }
Qed.

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
Lemma SeriesC_nat_shift {f : nat → R} (Hex :  Series.ex_series f) : SeriesC f = f 0%nat + SeriesC (f ∘ S).
Proof.
  rewrite SeriesC_nat.
  rewrite SeriesC_nat.
  rewrite Series.Series_incr_1; last done.
  f_equal.
Qed.

Lemma SeriesC_nat_shift_rev {f : nat → R} (Hex :  Series.ex_series f) : SeriesC (f ∘ S) = - f 0%nat + SeriesC f.
Proof. have ? := SeriesC_nat_shift Hex. lra. Qed.

Lemma ex_SeriesC_nat_shift {f : nat → R} : ex_seriesC f → ex_seriesC (f ∘ S).
Proof.
  intro H.
  apply ex_seriesC_nat in H.
  apply Series.ex_series_incr_1 in H.
  apply ex_seriesC_nat in H.
  apply H.
Qed.

Lemma ex_SeriesC_nat_shiftN_l {f : nat → R} (N : nat) : ex_seriesC (f ∘ (fun n => (n - N))%nat) → ex_seriesC f.
Proof.
  revert f.
  induction N as [|N IH].
  { intros f.
    replace (f ∘ λ n : nat, (n - 0)%nat) with f; [done|].
    by rewrite /compose//=; apply functional_extensionality; intros ?; rewrite Nat.sub_0_r.
  }
  intros f.
  replace ((f ∘ λ n : nat, (n - S N)%nat)) with (((f ∘ (λ n : nat, (n - 1)%nat)) ∘ λ n : nat, (n - N)%nat)).
  { intros Hf.
    specialize IH with (f ∘ (λ n : nat, (n - 1)%nat)).
    apply IH in Hf.
    apply ex_SeriesC_nat_shift in Hf.
    apply ex_SeriesC_nat_shift in Hf.
    suffices H : Series.ex_series f by apply ex_seriesC_nat in H.
    apply Series.ex_series_incr_1.
    apply ex_seriesC_nat.
    eapply ex_seriesC_ext; [|apply Hf].
    intros n.
    rewrite /compose//=.
  }
  { rewrite /compose//=; apply functional_extensionality; intros ?.
    f_equal.
    lia.
  }
Qed.

Lemma ex_SeriesC_nat_shiftN_r {f : nat → R} (N : nat) : ex_seriesC (f ∘ (fun n => (n + N))%nat) → ex_seriesC f.
Proof.
  induction N as [|N IH].
  { replace (f ∘ λ n : nat, (n + 0)%nat) with f; [done|].
    by rewrite /compose//=; apply functional_extensionality; intros ?; rewrite Nat.add_0_r.
  }
  { intros Hf.
    apply IH.
    suffices H : Series.ex_series (f ∘ λ n : nat, (n + N)%nat) by apply ex_seriesC_nat in H.
    apply Series.ex_series_incr_1.
    apply ex_seriesC_nat.
    eapply ex_seriesC_ext; [|apply Hf].
    intros n.
    rewrite /compose//=.
    f_equal.
    lia.
  }
Qed.

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
  2: { apply ex_seriesC_nat. apply HpowO_ex. }
  rewrite Iverson_False; [|simpl; intuition].
  by rewrite Rmult_0_l Rdiv_def Rmult_0_l Rplus_0_l.
Qed.

Lemma HpowE_eq {x} : HpowE x = 1 + HpowES x.
Proof.
  rewrite /HpowE/HpowES.
  rewrite SeriesC_nat_shift.
  2: { apply ex_seriesC_nat. apply HpowE_ex. }
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

  Lemma Hexp_ex_even {x} : ex_seriesC (λ n : nat, Iverson Zeven n * (x ^ n / fact n + x ^ (n + 1) / fact (n + 1))).
  Proof.
    apply (ex_seriesC_ext (λ n : nat, Iverson Zeven n * x ^ n / fact n + Iverson Zeven n * x ^ (n + 1) / fact (n + 1))).
    { intro n. lra. }
    apply ex_seriesC_plus.
    { apply HpowE_ex. }
    replace (λ x0 : nat, Iverson Zeven x0 * x ^ (x0 + 1) / fact (x0 + 1)) with ((λ x0 : nat, Iverson (not ∘ Zeven) x0 * x ^ x0 / fact x0 ) ∘ S).
    { apply HpowOS_ex. }
    apply functional_extensionality.
    intros ?.
    Opaque fact.
    Opaque pow.
    simpl; f_equal; last (f_equal; f_equal; lia).
    f_equal; last (f_equal; lia).
    Transparent fact.
    Transparent pow.
    rewrite /Iverson.
    case_decide; case_decide; try done; exfalso.
    Opaque Zeven.
    { simpl in H.
      destruct (Zeven_odd_dec x0); try by intuition.
      apply Zeven_Sn in z.
      replace (Z.succ (Z.of_nat x0)) with (Z.of_nat (S x0)) in z by lia.
      done.
    }
    { simpl in H.
      apply Zodd_Sn in H0.
      replace (Z.succ (Z.of_nat x0)) with (Z.of_nat (S x0)) in H0 by lia.
      apply Zodd_not_Zeven in H0.
      done.
    }
  Qed.

  Lemma Hexp_ex_odd {x} : ex_seriesC (λ n : nat, Iverson (not ∘ Zeven) n * (x ^ n / fact n + x ^ (n + 1) / fact (n + 1))).
  Proof.
    apply (ex_seriesC_ext (λ n : nat, Iverson (not ∘ Zeven) n * x ^ n / fact n + Iverson (not ∘ Zeven) n * x ^ (n + 1) / fact (n + 1))).
    { intro n. lra. }
    apply ex_seriesC_plus.
    { apply HpowO_ex. }
    replace (λ x0 : nat, Iverson (not ∘ Zeven) x0 * x ^ (x0 + 1) / fact (x0 + 1)) with ((λ x0 : nat, Iverson (Zeven) x0 * x ^ x0 / fact x0 ) ∘ S).
    { apply HpowES_ex. }
    apply functional_extensionality.
    intros ?.
    Opaque fact.
    Opaque pow.
    simpl; f_equal; last (f_equal; f_equal; lia).
    f_equal; last (f_equal; lia).
    Transparent fact.
    Transparent pow.
    rewrite /Iverson.
    case_decide; case_decide; try done; exfalso.
    Opaque Zeven.
    { simpl in H0.
      apply NNP_P in H0.
      apply Zodd_Sn in H0.
      replace (Z.succ (Z.of_nat x0)) with (Z.of_nat (S x0)) in H0 by lia.
      apply Zodd_not_Zeven in H0.
      done.
    }
    { simpl in H0.
      destruct (Zeven_odd_dec x0); try by intuition.
      apply Zeven_Sn in z.
      replace (Z.succ (Z.of_nat x0)) with (Z.of_nat (S x0)) in z by lia.
      done.
    }
  Qed.

  Lemma exp_mono_strict {x y : R} : x < y → exp x < exp y.
  Proof. apply exp_increasing. Qed.

  Lemma exp_mono {x y : R} : x <= y → exp x <= exp y.
  Proof.
    intros H.
    destruct H.
    { apply exp_increasing in H. lra. }
    { by rewrite H. }
  Qed.

  Lemma ex_seriesC_mult {f g : nat → R} (Hf : ∀ n : nat, 0 <= f n) (Hg : ∀ n : nat, 0 <= g n) :
    ex_seriesC f → ex_seriesC g → ex_seriesC (fun n => f n * g n).
  Proof.
  Admitted.

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
  Proof.
    apply ex_seriesC_nat.
    eapply ex_seriesC_ext; [|apply (@Hpow_ex 1)].
    intros n. simpl.
    rewrite pow1.
    lra.
  Qed.

  Lemma ex_exp_series' {M : nat} : Series.ex_series (λ n : nat, / fact (n - M)).
  Proof.
    apply ex_seriesC_nat.
    replace (λ n : nat, / fact (n - M)) with ((λ n : nat, / fact n) ∘ (fun n : nat => (n - M)%nat)).
  Admitted.

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
  Proof.
    intros z.
    replace (0%fin) with (bool_to_fin false) by rewrite /bool_to_fin//=.
    replace (1%fin) with (bool_to_fin true) by rewrite /bool_to_fin//=.
    destruct (bool_to_fin_surj z).
    destruct x; auto.
  Qed.

  (* Geometric series *)
  Lemma exp_neg_RInt : ex_RInt (λ x : R, exp (- x ^ 2 / 2)) 0 1.
  Proof. Admitted.

  Lemma RInt_pow_fact {a b : R} (M : nat) :
    RInt (fun x1 : R => x1 ^ M / fact M) a b = b ^ (M + 1) / fact (M + 1) - a ^ (M + 1) / fact (M + 1).
  Proof. Admitted.

  Lemma Le_Nat_sum (N : nat) (v : R) : SeriesC (λ n : nat, if bool_decide (n ≤ N) then v else 0) = (N + 1)* v.
  Proof. Admitted.

  Lemma even_pow_neg {x : R} {n : nat} : Zeven n → (- x) ^ n = x ^ n.
  Proof.
    intro H.
    destruct (Zeven_ex _ H).
    replace n with (Z.to_nat (Z.of_nat n)); last first.
    { rewrite Nat2Z.id. done. }
    rewrite H0.
    rewrite Z2Nat.inj_mul; last first.
    { have ? := pos_INR n. lia. }
    { done. }
    rewrite pow_mult.
    rewrite pow_mult.
    replace ((- x) ^ Z.to_nat 2) with ((x) ^ Z.to_nat 2); last first.
    { simpl. lra. }
    done.
  Qed.

  Lemma not_even_pow_neg {x : R} {n : nat} : ¬ Zeven n → (- x) ^ n = - x ^ n.
  Proof.
    intro H.
    destruct (Zeven_odd_dec n); first (by exfalso).
    destruct (Zodd_ex _ z).
    replace n with (Z.to_nat (Z.of_nat n)); last first.
    { rewrite Nat2Z.id. done. }
    rewrite H0.
    rewrite Z2Nat.inj_add; try done.
    2: {
      apply Z.mul_nonneg_nonneg; first lia.
      destruct n. { by simpl in z. }
      have ? := pos_INR n. lia.
    }
    rewrite pow_add.
    rewrite pow_add.
    rewrite Ropp_mult_distr_r.
    f_equal.
    2: { simpl. lra. }
    rewrite Z2Nat.inj_mul; last first.
    { have ? := pos_INR n. lia. }
    { done. }
    rewrite pow_mult.
    rewrite pow_mult.
    replace ((- x) ^ Z.to_nat 2) with ((x) ^ Z.to_nat 2); last first.
    { simpl. lra. }
    done.
  Qed.

  Lemma Geo_ex_SeriesC {𝛾 : R} (H𝛾 : 0 <= 𝛾 <= 1) : ex_seriesC (λ x : nat, 𝛾 ^ x * (1 - 𝛾)).
  Proof.
    destruct H𝛾.
    destruct H0.
    { apply ex_seriesC_scal_r.
      have H𝛾' : Rabs 𝛾 < 1.
      { rewrite Rabs_pos_eq; lra. }
      have H' := Series.ex_series_geom 𝛾 H𝛾'.
      by rewrite ex_seriesC_nat in H'.
    }
    apply (ex_seriesC_ext (fun _ : nat => 0%R)).
    { intros ?; rewrite H0; lra. }
    { apply ex_seriesC_0. }
  Qed.

  Lemma exp_inj {x y : R} : exp x = exp y → x = y.
  Proof. apply exp_inv. Qed.

  Lemma Derive_exp_neg {x : R} : Derive.Derive (λ x1 : R, exp (- x1)) x = - exp (- x).
  Proof.
    have X := UnaryDiff_exp.
    rewrite Derive.Derive_comp; try by auto_derive.
    rewrite Derive.Derive_opp.
    rewrite Derive.Derive_id.
    suffices H : (Derive.Derive exp (- x) =  exp (- x)) by lra.
    (* UnaryDiff crap *)
    destruct X.
    specialize (UnaryDiff_H) with (-x).
Admitted.

  Lemma RInt_gen_ext_eq_Ici {f g : R → R} {M : R} :
    (∀ x : R, M <= x → f x = g x) →
    ex_RInt_gen f (at_point M) (Rbar_locally Rbar.p_infty) →
    RInt_gen f (at_point M) (Rbar_locally Rbar.p_infty) = RInt_gen g (at_point M) (Rbar_locally Rbar.p_infty).
  Proof.
    intros ??.
    apply RInt_gen_ext; [|done].
    simpl.
    eapply (Filter_prod _ _ _ (fun x => x = M) (fun x => M <= x)).
    { rewrite /at_point//=. }
    { rewrite //=. exists M. intuition. lra. }
    intros ??????.
    apply H.
    simpl in H3.
    destruct H3.
    rewrite H1 in H3.
    rewrite Rmin_left in H3; lra.
  Qed.

  Lemma RInt_gen_ex_Ici {M : R} {F : R → R}
    (Hlimit : exists L : R_NormedModule, (filterlimi (λ b : R, is_RInt F M b) (Rbar_locally Rbar.p_infty)) (locally L))
    (Hex : ∀ b, ex_RInt F M b) :
    ex_RInt_gen F (at_point M) (Rbar_locally (Rbar.p_infty)).
  Proof.
    rewrite /ex_RInt_gen.
    rewrite /is_RInt_gen.
    destruct Hlimit as [L HL].
    exists L.
    rewrite /filterlimi//=/filter_le//=/filtermapi//=.
    rewrite /filterlimi//=/filter_le//=/filtermapi//= in HL.
    intros P HP.
    destruct (HL P HP) as [M0 HM0].
    eapply (Filter_prod _ _ _ (fun x => x = M) (fun x => M0 < x)).
    { rewrite /at_point//=. }
    { rewrite /Rbar_locally/=. exists M0; intuition. }
    intros ?? -> H.
    simpl.
    by apply HM0.
  Qed.

  Lemma RInt_gen_Ici {M : R} {F : R → R} {L}
    (Hlimit : filterlimi (λ b : R, is_RInt F M b) (Rbar_locally Rbar.p_infty) (locally L))
    (Hex : ∀ b, ex_RInt F M b) :
    RInt_gen F (at_point M) (Rbar_locally (Rbar.p_infty)) = L.
  Proof.
    have Hcorr : is_RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty) (RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty)).
    { eapply (@RInt_gen_correct R_CompleteNormedModule).
      { apply Proper_StrongProper, at_point_filter. }
      { apply Proper_StrongProper, Rbar_locally_filter. }
      apply RInt_gen_ex_Ici.
      { exists L. done. }
      { by apply Hex. }
    }
    rewrite /RInt_gen//=.
    have Hsc1 : ProperFilter' (Rbar_locally Rbar.p_infty).
    { apply Proper_StrongProper, Rbar_locally_filter. }
    have Hsc2 : Rbar_locally Rbar.p_infty (λ x : R, ∀ y1 y2 : R_CompleteNormedModule, is_RInt F M x y1 → is_RInt F M x y2 → y1 = y2).
    { rewrite /Rbar_locally.
      exists 0%R.
      intros ???? Hint1 Hint2.
      rewrite -(@is_RInt_unique R_CompleteNormedModule F M x y1 Hint1).
      rewrite -(@is_RInt_unique R_CompleteNormedModule F M x y2 Hint2).
      done.
    }
    have H := @iota_filterlimi_locally _ R_CompleteNormedModule R (Rbar_locally Rbar.p_infty) _ (λ b : R, is_RInt F M b) _ _ Hlimit.
    have H' := H Hsc1 Hsc2; clear H.
    rewrite -H'.
    f_equal.
    apply functional_extensionality.
    intro x.
    rewrite /is_RInt_gen.
    apply propositional_extensionality.
    split.
    { rewrite /filterlimi//=/filter_le//=/filtermapi//=.
      intros HP P Hl.
      have HP' := HP P Hl; clear HP.
      inversion HP'.
      simpl in H1.
      rewrite /at_point//= in H.
      rewrite /Rbar_locally//= in H0.
      destruct H0 as [M' HM'].
      exists M'.
      intros b Hb.
      apply H1; [done|].
      by apply HM'.
    }
    { rewrite /filterlimi//=/filter_le//=/filtermapi//=.
      intros HP P Hl.
      destruct (HP P Hl) as [M' HM'].
      eapply (Filter_prod _ _ _ (fun x => x = M) (fun x => M' < x)).
      { rewrite /at_point//=. }
      { rewrite /Rbar_locally/=. exists M'; intuition. }
      intros ?? -> H.
      simpl.
      by apply HM'.
    }
  Qed.

  Lemma RInt_sum_n {F : nat → R → R} {a b : R} {M} :
    RInt (fun x : R => sum_n (fun n : nat => F n x) M) a b = sum_n (fun n : nat =>  RInt (fun x : R => F n x) 0 1) M.
  Proof. Admitted.

  Lemma ex_RInt_div (F : R → R) {a b c} : ex_RInt F a b → ex_RInt (fun x => F x / c) a b.
  Proof. Admitted.

  Lemma ex_seriesC_finite_dec (M : nat) (F : nat → R) :
    ex_seriesC (λ x : nat, if bool_decide (x ≤ M) then F x else 0).
  Proof. Admitted.


End Lib.
