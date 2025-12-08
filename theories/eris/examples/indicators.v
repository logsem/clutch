From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis RInt_gen AutoDerive Lub.
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

Ltac replace_ext X Y :=
  replace X with Y; [| apply functional_extensionality; intros; auto].

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
Proof. pose proof (exp_pos z); lra. Qed.
(* Proof. have ? := exp_pos z. lra. Qed. *)

Lemma Rexp_range {z : R} : z <= 0 -> 0 <= exp z <= 1.
Proof.
  split; [apply Rexp_nn|].
  replace z with ((-1) * (-z)) by lra.
  replace (exp (-1 * - z)) with (/ exp (- z) ); last first.
  { apply (Rmult_eq_reg_l (exp (- z))).
    2: { pose proof (exp_pos (- z)); lra. }
    rewrite -Rdiv_def Rdiv_diag.
    2: { pose proof (exp_pos (- z)); lra. }
    rewrite -exp_plus.
    (* 2: { have ? := exp_pos (- z). lra. } *)
    (* 2: { have ? := exp_pos (- z). lra. } *)
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

Lemma ex_RInt_square (f  : R -> R) (a b : R) :
  ex_RInt f a b → ex_RInt (fun x => (f x) ^ 2) a b.
Proof.
Admitted.

Lemma ex_RInt_mult (f g : R -> R) (a b : R) :
  ex_RInt f a b ->  ex_RInt g a b ->
  ex_RInt (λ y : R, f y * g y) a b.
Proof.
  intros H1 H2.
  replace (λ y : R, f y * g y) with (λ y : R, (1/4) * ((f y + g y) ^ 2 - (f y - g y) ^ 2)); last first.
  { apply functional_extensionality; intros ?. lra. }
  apply ex_RInt_Rmult.
  apply (ex_RInt_minus (V := R_CompleteNormedModule)).
  { apply ex_RInt_square. by apply (ex_RInt_plus (V := R_CompleteNormedModule)). }
  { apply ex_RInt_square. by apply (ex_RInt_minus (V := R_CompleteNormedModule)). }
Qed.

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

Lemma Continuity2_continuous_fst
  {f : R * R → R_CompleteNormedModule} {x y : R} :
  Continuity2 f x y →
  Continuity.continuous (λ x', f (x', y)) x.
Proof.
  unfold Continuity2, Continuity.continuous.
  intros H2.
  apply (filterlim_comp _ _ _ (fun x' => (x', y)) f _ (locally (x, y))).
  2: apply H2.
  rewrite /filterlim/filter_le/filter_map//=.
  rewrite /filtermap//=.
  rewrite /locally//=.
  intros P [e He].
  exists e.
  intros z HZ.
  apply He.
  rewrite /ball//=.
  rewrite /prod_ball//=.
  split; try done.
  apply ball_center.
Qed.

Lemma Continuity2_continuous_snd
  {f : R * R → R_CompleteNormedModule} {x y : R} :
  Continuity2 f x y →
  Continuity.continuous (λ y', f (x, y')) y.
Proof.
  unfold Continuity2, Continuity.continuous.
  intros H2.
  apply (filterlim_comp _ _ _ (fun y' => (x, y')) f _ (locally (x, y))).
  2: apply H2.
  rewrite /filterlim/filter_le/filter_map//=.
  rewrite /filtermap//=.
  rewrite /locally//=.
  intros P [e He].
  exists e.
  intros z HZ.
  apply He.
  rewrite /ball//=.
  rewrite /prod_ball//=.
  split; try done.
  apply ball_center.
Qed.

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

Definition Ioi (a : R) : R -> Prop :=
  fun t => a < t.

Definition Iio (b : R) : R -> Prop :=
  fun t => t < b.

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
Proof. pose proof (SeriesC_nat_shift Hex); lra. Qed.
(* Proof. have ? := SeriesC_nat_shift Hex. lra. Qed. *)

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
    rewrite Iverson_Zeven_Sn.
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
    rewrite Iverson_Zeven_Sn'.
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

  Lemma SeriesC_term_le {h : nat → R} (Hh : ∀ n, 0 <= h n) (Hex : ex_seriesC h) :
    ∀ n, h n <= SeriesC h.
  Proof.
    intros n.
    have Heq : SeriesC h = SeriesC (λ m, if bool_decide (m = n) then h m else 0) +
                           SeriesC (λ m, if bool_decide (m ≠ n) then h m else 0).
    { rewrite -SeriesC_plus.
      - apply SeriesC_ext.
        intros m. case_bool_decide; case_bool_decide; try lra; try (exfalso; auto).
      - apply ex_seriesC_singleton_dependent.
      - apply (ex_seriesC_le _ h); auto.
        intros m. split; case_bool_decide; auto; lra.
    }
    rewrite Heq.
    rewrite SeriesC_singleton_dependent.
    have Hrest : 0 <= SeriesC (λ m, if bool_decide (m ≠ n) then h m else 0).
    { apply SeriesC_ge_0' => m. case_bool_decide; auto. lra. }
    lra.
  Qed.

  Lemma ex_seriesC_mult {f g : nat → R} (Hf : ∀ n : nat, 0 <= f n) (Hg : ∀ n : nat, 0 <= g n) :
    ex_seriesC f → ex_seriesC g → ex_seriesC (fun n => f n * g n).
  Proof.
    intros Hexf Hexg.
    apply (ex_seriesC_le _ (fun n => (SeriesC g) * f n)).
    { intros n. split.
      - apply Rmult_le_pos; auto.
      - rewrite Rmult_comm. apply Rmult_le_compat_r; auto. apply SeriesC_term_le; done.
    }
    by apply ex_seriesC_scal_l.
  Qed.

  (* Weierstrass M test, Rudin 7.10 *)
  Lemma UniformConverge_Series {F : R → nat → R} (UB : nat → R) :
    (Series.ex_series UB) →
    (forall x n, Rabs (F x n) <= UB n) →
    filterlim (fun (M : nat) (x : R) => sum_n (F x) M) eventually (locally (λ x : R, Series.Series (F x))).
  Proof.
    intros H1 H2.
    (* It suffices to show the tails converge uniformly to zero. *)

    (*
    suffices HTail :
      filterlim (λ (M : nat) (x : R), Series.Series (fun n => F x (n + M)%nat)) eventually (locally (fun _ => 0)).
    {
      rewrite /filterlim/filter_le//=/locally//=.
      intros P.
      rewrite /filterlim/filter_le//=/locally//= in HTail.
      specialize (HTail P).
      intros [eps Heps].
      rewrite /filtermap/eventually//=.
      rewrite /filtermap/eventually//= in HTail.
    a dmit. }
    (* This limit is uniformly bounded above by the sequence of upper bounds
       These converge to 0 using h1 and ex_series_lim_0
     *)
     *)
  Admitted.


  Lemma Exchange1 {f : nat → R → R_CompleteNormedModule} {a b : R} {F : R → R}
    (Hex : ∀ n, ex_RInt (f n) a b) (Hunif : filterlim f eventually (locally F)) :
    filterlim (λ n : nat, RInt (f n) a b) eventually (locally (RInt F a b)).
  Proof.
    have H (n : nat) : is_RInt (f n) a b (RInt (f n) a b).
    { apply (RInt_correct (V := R_CompleteNormedModule)), Hex. }
    destruct (filterlim_RInt f a b eventually eventually_filter _ _ H Hunif) as [I [HL HF]].
    rewrite (is_RInt_unique F a b I HF).
    done.
  Qed.

  Lemma Exchange2 {f : R → R → R_CompleteNormedModule} {a b : R} {F : R → R}
    (Hex : ∀ r, ex_RInt (f r) a b) (Hunif : filterlim f (Rbar_locally Rbar.p_infty) (locally F)) :
    filterlim (λ r : R, RInt (f r) a b) (Rbar_locally Rbar.p_infty) (locally (RInt F a b)).
  Proof.
    have H (r : R) : is_RInt (f r) a b (RInt (f r) a b).
    { apply (RInt_correct (V := R_CompleteNormedModule)), Hex. }
    destruct (filterlim_RInt f a b (Rbar_locally Rbar.p_infty) (Rbar_locally_filter Rbar.p_infty) _ _ H Hunif)
        as [I [HL HF]].
    rewrite (is_RInt_unique F a b I HF).
    done.
  Qed.

  Lemma ex_RInt_sum_n {a b M} {F : nat → R → R} :
    (∀ n, ex_RInt (F n) a b) → ex_RInt (λ x : R, sum_n (λ n : nat, F n x) M) a b .
  Proof.
   intro H.
   induction M.
   { replace (λ x : R, sum_n (λ n : nat, F n x) 0) with (λ x : R, F 0%nat x).
     { apply H. }
     apply functional_extensionality; intros ?.
     by rewrite sum_O.
   }
   { replace (λ x : R, sum_n (λ n : nat, F n x) (S M)) with
       (λ x : R, sum_n (λ n : nat, F n x) M + F (S M) x); last first.
     { apply functional_extensionality; intros ?.
       rewrite sum_Sn.
       rewrite /plus//=/zero//=.
     }
     apply (ex_RInt_plus (V := R_CompleteNormedModule));  done.
   }
  Qed.

  Lemma FubiniFinite {a b M} {f : nat → R → R} (Hex : ∀ n, ex_RInt (f n) a b) :
    RInt (λ x : R, sum_n (λ n : nat, f n x) M) a b = sum_n (λ n : nat, RInt (λ x : R, f n x) a b) M.
  Proof.
    induction M.
     { replace (λ x : R, sum_n (λ n : nat, f n x) 0) with (λ x : R, f 0%nat x); last first.
       { apply functional_extensionality; intros ?.
         by rewrite sum_O.
       }
       rewrite sum_O.
       done.
     }
     { replace (λ x : R, sum_n (λ n : nat, f n x) (S M)) with
         (λ x : R, sum_n (λ n : nat, f n x) M + f (S M) x); last first.
       { apply functional_extensionality; intros ?.
         rewrite sum_Sn.
         rewrite /plus//=/zero//=.
       }
       rewrite RInt_plus.
       3: { apply Hex. }
       2: { by apply ex_RInt_sum_n.  }
        rewrite sum_Sn.
       by rewrite IHM.
     }
  Qed.

  Lemma SequeneceLemma1 {r : R} {rb : Rbar.Rbar} (s : nat → R) :
    filterlim s eventually (locally r) →
    filterlim s eventually (Rbar_locally rb) →
    rb = Rbar.Finite r.
  Proof.
    intro Hreal.
    intro Hrbar.
    assert (H1 : Lim_seq.is_lim_seq s (Rbar.Finite r)).
    { unfold Lim_seq.is_lim_seq. assumption. }
    assert (H2 : Lim_seq.is_lim_seq s rb).
    { unfold Lim_seq.is_lim_seq. assumption. }
    apply Lim_seq.is_lim_seq_unique in H1; apply Lim_seq.is_lim_seq_unique in H2.
    by rewrite H2 in H1.
  Qed.

  Lemma seq_lift {s : nat → R} {L : R} :
    filterlim s eventually (locally L) →
    filterlim s eventually (Rbar_locally (Rbar.Finite L)).
  Proof.
  intros H.
  unfold filterlim in *.
  exact H.
  Qed.

  Lemma Filterlim_Series1 {s : nat → R} (Hex : Lim_seq.ex_lim_seq s) :
    filterlim s eventually (Rbar_locally (Lim_seq.Lim_seq s)).
  Proof. apply (Lim_seq.Lim_seq_correct s Hex). Qed.

  Lemma Filterlim_Series {s : nat → R} {L : R} :
    Lim_seq.ex_lim_seq (sum_n s) →
    filterlim (λ M : nat, sum_n (λ n : nat, s n) M) eventually (locally L) →
    Series.Series s = L.
  Proof.
    intros Hex H.
    unfold Series.Series.
    have H1 := @Filterlim_Series1 (sum_n s) Hex.
    rewrite (SequeneceLemma1 _ H H1).
    done.
  Qed.

  Lemma FubiniIntegralSeries {f : nat → R → R_CompleteNormedModule} {a b : R} (UB : nat → R)
    (HexU : Series.ex_series UB) (Hub : forall x n, Rabs (f n x) <= UB n) (Hex : ∀ n, ex_RInt (f n) a b) :
    Series.Series (fun n => RInt (λ x : R, f n x) a b) = RInt (λ x : R, Series.Series (λ n' : nat, f n' x)) a b.
  Proof.
    have H : ∀ n : nat, ex_RInt (λ x : R, sum_n (λ n' : nat, f n' x) n) a b.
    { intros n. apply ex_RInt_sum_n. apply Hex. }
    have HU : filterlim (λ (M : nat) (x : R), sum_n (λ n' : nat, f n' x) M) eventually
                (locally (λ x : R, Series.Series (λ n' : nat, f n' x))).
    { apply (UniformConverge_Series UB); done. }
    have HLimit := @Exchange1 (fun M x => sum_n (fun n' => f n' x) M) a b (fun x => Series.Series (fun n' => f n' x)) H HU.
    (* Exchange the RInt and the sum_n *)
    have H1 : (λ n : nat, RInt (λ x : R, sum_n (λ n' : nat, f n' x) n) a b) =
              (λ n : nat, sum_n (λ n' : nat, RInt (λ x : R, f n' x) a b) n).
    { apply functional_extensionality; intros ?. rewrite FubiniFinite; done. }
    rewrite H1 in HLimit. clear H1.
    rewrite (Filterlim_Series _ HLimit); [done|].
    have Hex' : Series.ex_series (λ n' : nat, RInt (λ x : R, f n' x) a b).
    { apply (Series.ex_series_le _ (fun n => Rabs (b - a) * UB n)).
      2: { by apply @Series.ex_series_scal_l. }
      intros n.
      rewrite /norm//=/abs//=.
      destruct (ClassicalEpsilon.excluded_middle_informative (a <= b)).
      { etrans; first eapply (abs_RInt_le_const _ _ _ (UB n)).
        { done. }
        { by apply Hex. }
        { intros ??. apply Hub. }
        { rewrite Rabs_right; try lra. }
      }
      have HP : b <= a by lra.
      rewrite -opp_RInt_swap.
      2: { apply ex_RInt_swap, Hex. }
      rewrite /opp//=.
      rewrite Rabs_Ropp.
      { etrans; first eapply (abs_RInt_le_const _ _ _ (UB n)).
        { done. }
        { apply ex_RInt_swap, Hex. }
        { intros ??. apply Hub. }
        { replace (b - a) with (- (a - b)) by lra.
          rewrite Rabs_Ropp.
          rewrite Rabs_right; try lra. }
      }
    }
    destruct Hex' as [L HEL].
    unfold Series.is_series in HEL.
    unfold Lim_seq.ex_lim_seq.
    exists (Rbar.Finite L).
    unfold Lim_seq.is_lim_seq.
    by apply seq_lift.
  Qed.


  Lemma FubiniIntegralSeries_Strong {f : nat → R → R_CompleteNormedModule} {a b : R} (UB : nat → R)
    (HexU : Series.ex_series UB) (Hub : forall x n, a < x < b → Rabs (f n x) <= UB n) (Hex : ∀ n, ex_RInt (f n) a b) :
    Series.Series (fun n => RInt (λ x : R, f n x) a b) = RInt (λ x : R, Series.Series (λ n' : nat, f n' x)) a b.
  Proof.
    (* Reduce this to FubiniIntegralSeries by setting f to 0 outside the domain *)
  Admitted.

  Lemma FubiniIntegralSeriesC_Strong {f : nat → R → R_CompleteNormedModule} {a b : R} (UB : nat → R)
    (HexU : ex_seriesC UB) (Hub : forall x n, a < x < b → Rabs (f n x) <= UB n) (Hex : ∀ n, ex_RInt (f n) a b) :
    SeriesC (fun n => RInt (λ x : R, f n x) a b) = RInt (λ x : R, SeriesC (λ n' : nat, f n' x)) a b.
  Proof.
    rewrite SeriesC_nat.
    rewrite (FubiniIntegralSeries_Strong UB); try done.
    2: { by apply ex_seriesC_nat. }
    apply RInt_ext.
    intros ??.
    rewrite SeriesC_nat.
    done.
  Qed.

  Lemma ex_seriesC_RInt {f : nat → R → R_CompleteNormedModule} {a b : R} (UB : nat → R)
    (Hab  : a <= b)
    (Hnn : ∀ x n, a < x < b → 0 <= f n x)
    (HexU : ex_seriesC UB)
    (Hub : forall x n, a <= x <= b → Rabs (f n x) <= UB n)
    (Hex : ∀ n, ex_RInt (f n) a b) :
    ex_seriesC (fun n => RInt (λ x : R, f n x) a b).
  Proof.
    apply (ex_seriesC_le _ (fun n => (b - a) * UB n)); first (intros ?; split).
    2: {
      replace (RInt (λ x : R, f n x) a b) with (Rabs (RInt (λ x : R, f n x) a b)).
      2: {
        rewrite Rabs_right; first done.
        apply Rle_ge.
        apply RInt_ge_0.
        { done. }
        { apply Hex. }
        { intros ??. apply Hnn.  done. }
      }
      { etrans; first eapply (abs_RInt_le_const _ _ _ (UB n)).
        { done.  }
        { apply Hex. }
        { intros ??. apply Hub. lra. }
        { right. f_equal. }
      }
    }
    { apply RInt_ge_0.
      { done. }
      { apply Hex. }
      { intros ??. apply Hnn.  done. }
    }
    apply ex_seriesC_scal_l.
    apply HexU.
  Qed.

  Lemma ex_RInt_SeriesC {f : nat → R → R_CompleteNormedModule} {a b : R} (UB : nat → R)
    (HexU : Series.ex_series UB) (Hub : forall x n, a < x < b → Rabs (f n x) <= UB n) (Hex : ∀ n, ex_RInt (f n) a b) :
    ex_RInt (λ x : R, SeriesC (λ n' : nat, f n' x)) a b.
  Proof.
    (* I'm sure this is true *)
  Admitted.

  Definition Ioo (a b : R) : R → Prop := fun x => Rmin a b < x < Rmax a b.

  Lemma ex_RInt_dom {F : R → R} {a b : R} : ex_RInt (fun x => Iverson (Ioo a b) x * F x) a b ↔ ex_RInt F a b.
  Proof.
  intros.
  unfold Ioo, Iverson.
  split.
  { intros H.
    eapply ex_RInt_ext; [|apply H].
    intros ??.
    simpl.
    rewrite decide_True; lra.
  }
  { intros H.
    eapply ex_RInt_ext; [|apply H].
    intros ??.
    simpl.
    rewrite decide_True; lra.
  }
  Qed.

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
    apply (ex_SeriesC_nat_shiftN_r M).
    rewrite /compose//=.
    eapply ex_seriesC_ext.
    2: { rewrite -ex_seriesC_nat. apply ex_exp_series. }
    intros. rewrite //=.
    f_equal.
    f_equal.
    f_equal.
    lia.
  Qed.

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
  Proof.
    eapply (ex_RInt_continuous (V := R_CompleteNormedModule)).
    intros ??.
    apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
    by auto_derive.
  Qed.

  Lemma RInt_pow_fact {a b : R} (M : nat) :
    RInt (fun x1 : R => x1 ^ M / fact M) a b = b ^ (M + 1) / fact (M + 1) - a ^ (M + 1) / fact (M + 1).
  Proof.
    replace (fun x1 : R => x1 ^ M / fact M) with (Derive.Derive (fun x1 : R => x1 ^ (M + 1) / fact (M + 1))); last first.
    { replace (fun x1 : R => x1 ^ (M + 1) / fact (M + 1)) with (fun x1 : R => x1 ^ (M + 1) * / fact (M + 1)); last first.
      { apply functional_extensionality; intros ?; lra. }
      apply functional_extensionality; intros ?.
      rewrite Derive.Derive_scal_l.
      rewrite Derive.Derive_pow; [|by auto_derive].
      rewrite Derive.Derive_id.
      rewrite Rmult_1_r.
      rewrite (Rmult_comm _ (x ^ Init.Nat.pred (M + 1))).
      rewrite Rdiv_def Rmult_assoc.
      f_equal.
      { f_equal.
        rewrite -Nat.add_pred_r; [|lia].
        lia.
      }
      rewrite Nat.add_1_r.
      rewrite fact_simpl.
      rewrite mult_INR.
      rewrite Rinv_mult.
      rewrite -Rmult_assoc.
      rewrite (Rinv_r); [lra|].
      pose proof (pos_INR_S M); lra.
      (* have ? := pos_INR_S M. lra. *)
  }
  rewrite RInt_Derive.
  { lra. }
  { intros ??. by auto_derive. }
  { intros ??.
    replace (fun x1 : R => x1 ^ (M + 1) / fact (M + 1)) with (fun x1 : R => x1 ^ (M + 1) * / fact (M + 1)); last first.
    { apply functional_extensionality; intros ?; lra. }
    replace (Derive.Derive (λ x1 : R, x1 ^ (M + 1) * / fact (M + 1))) with (fun x1 : R => x1 ^ M / fact M).
    { apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)). by auto_derive. }
    apply functional_extensionality; intros ?.
    rewrite Derive.Derive_scal_l.
    rewrite Derive.Derive_pow; [|by auto_derive].
    rewrite Derive.Derive_id.
    rewrite Rmult_1_r.
    rewrite (Rmult_comm _ (x0 ^ Init.Nat.pred (M + 1))).
    rewrite Rdiv_def Rmult_assoc.
    f_equal.
    { f_equal.
      rewrite -Nat.add_pred_r; [|lia].
      lia.
    }
    rewrite Nat.add_1_r.
    rewrite fact_simpl.
    rewrite mult_INR.
    rewrite Rinv_mult.
    rewrite -Rmult_assoc.
    rewrite (Rinv_r); [lra|].
    pose proof (pos_INR_S M); lra.
    (* have ? := pos_INR_S M. lra. *)
  }
  Qed.

  Lemma Le_Nat_sum (N : nat) (v : R) : SeriesC (λ n : nat, if bool_decide (n ≤ N) then v else 0) = (N + 1)* v.
  Proof.
    rewrite SeriesC_nat_bounded'.
    induction N.
    { rewrite //=. lra. }
    replace ((S N + 1) * v) with ((N + 1) * v + v) by (rewrite S_INR; lra).
    rewrite -IHN //=.
    rewrite Rplus_assoc. f_equal. rewrite Rplus_comm.
    (*
    { replace ((S N + 1) * v) with ((N + 1) * v + v); last first.
      { rewrite S_INR. lra. }
      rewrite -IHN.
      rewrite //=.
      rewrite Rplus_assoc.
      f_equal.
      rewrite Rplus_comm.
      repeat f_equal.
      a dmit.
    }
    *)
  Admitted.

  Lemma even_pow_neg {x : R} {n : nat} : Zeven n → (- x) ^ n = x ^ n.
  Proof.
    intro H.
    destruct (Zeven_ex _ H).
    replace n with (Z.to_nat (Z.of_nat n)); last first.
    { rewrite Nat2Z.id. done. }
    rewrite H0.
    rewrite Z2Nat.inj_mul; last first.
    { pose proof (pos_INR n); lia. }
    (* { have ? := pos_INR n. lia. } *)
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
      pose proof (pos_INR n); lia.
      (* have ? := pos_INR n. lia. *)
    }
    rewrite pow_add.
    rewrite pow_add.
    rewrite Ropp_mult_distr_r.
    f_equal.
    2: { simpl. lra. }
    rewrite Z2Nat.inj_mul; last first.
    { pose proof (pos_INR n); lia. }
    (* { have ? := pos_INR n. lia. } *)
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
    rewrite Derive.Derive_comp; try by auto_derive.
    rewrite Derive.Derive_opp.
    rewrite Derive.Derive_id.
    suffices H : Derive.Derive exp (- x) = exp (- x) by lra.
    rewrite (Derive.is_derive_unique exp (- x) (exp (- x))); first done.
    apply ElemFct.is_derive_exp.
  Qed.


  Lemma ex_RInt_gen_ext_eq_Ici {f g : R → R} {M : R} :
    (∀ x : R, M <= x → f x = g x) →
    ex_RInt_gen f (at_point M) (Rbar_locally Rbar.p_infty) →
    ex_RInt_gen g (at_point M) (Rbar_locally Rbar.p_infty).
  Proof.
    intros ??.
    eapply ex_RInt_gen_ext; [|done].
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

  Lemma is_RInt_gen_filterlim {F : R → R_CompleteNormedModule} {M : R} {l : R_CompleteNormedModule} :
    (∀ b, ex_RInt F M b) →
    filterlim (λ b : R, RInt F M b) (Rbar_locally Rbar.p_infty) (locally l) →
    is_RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty) l.
  Proof.
    intros Hex Hlim.
    intros P HP.
    eapply (Filter_prod _ _ _ (fun r => M = r) _); [rewrite /at_point//= | apply (Hlim P HP) |].
    intros x y HPx HPy.
    simpl.
    exists (RInt F x y).
    rewrite -HPx.
    split; [|apply HPy].
    apply RInt_correct.
    apply Hex.
  Qed.

  Lemma filterlim_is_RInt_gen {F : R → R_CompleteNormedModule} {M : R} {l : R_CompleteNormedModule} :
    (∀ b, ex_RInt F M b) →
    is_RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty) l →
    filterlim (λ b : R, RInt F M b) (Rbar_locally Rbar.p_infty) (locally l).
  Proof.
    intros Hex Hgen.
    intros P HP.
    have Hext : Rbar_locally Rbar.p_infty (fun b => exists y, is_RInt F M b y /\ P y).
    { rewrite /Rbar_locally//=.
      unfold filtermapi in Hgen.
      destruct (Hgen P HP) as [P1 P2 H3 H4 H5].
      rewrite /at_point//= in H3.
      destruct H4 as [M' HM'].
      simpl in H5.
      exists M'. intros ??.
      apply H5; [done|].
      by apply HM'.
    }
    unfold filtermap.
    eapply filter_imp; [|apply Hext].
    intros x [y [Hy Py]].
    have Heq : RInt F M x = y by apply is_RInt_unique.
    rewrite Heq; exact Py.
  Qed.

  Lemma filterlim_RInt_gen {F : R → R_CompleteNormedModule} {M : R} :
    (∀ b, ex_RInt F M b) →
    RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty) =
    iota (fun IF : R => filterlim (λ b : R, RInt F M b) (Rbar_locally Rbar.p_infty) (locally IF)).
  Proof.
    intros ?.
    rewrite /RInt_gen.
    f_equal.
    apply functional_extensionality.
    intros IF.
    apply propositional_extensionality.
    split.
    { by apply filterlim_is_RInt_gen. }
    { by apply is_RInt_gen_filterlim. }
  Qed.

  Lemma RInt_gen_pos_ex {F M}
    (Hpos : forall x, 0 <= F x)
    (Hex : ∀ b, ex_RInt F M b)
    (Hnn : ∀ b, 0 <= RInt F M b) 
    (Hex_L : ex_RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty)) :
    0 <= RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty).
  Proof.
    apply (Lim_seq.filterlim_le (F := Rbar_locally Rbar.p_infty) (fun _ => 0)
             (fun b => RInt F M b) (Rbar.Finite 0) (Rbar.Finite (RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty)))).
      { apply filter_forall; apply Hnn. }
      { apply filterlim_const. }
      { intros P HP.
        unfold Rbar_locally in HP. simpl in HP.
        eapply (filterlim_is_RInt_gen Hex ).
        2: eapply HP.
        apply RInt_gen_correct.
        done.
      }
  Qed.

  Lemma RInt_gen_pos_strong {F M}
    (Hpos : forall x, 0 <= F x)
    (Hex : ∀ b, ex_RInt F M b)
    (Hnn : ∀ b, M <= b → 0 <= RInt F M b)
    (Hex_L : ex_RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty)) :
    0 <= RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty).
  Proof.
    (* Reduces to RInt_gen_pos_ex by setting f to be 0 below M, so that the wrong direction integral is zero. *)
  Admitted.

  Lemma ex_RInt_div (F : R → R) {a b c} : ex_RInt F a b → ex_RInt (fun x => F x / c) a b.
  Proof.
    intro H.
    replace (λ x : R, F x / c) with (λ x : R, F x * / c); last first.
    { apply functional_extensionality; intros ?; rewrite Rdiv_def//=. }
    by apply ex_RInt_Rmult'.
  Qed.

  Lemma ex_seriesC_finite_dec (M : nat) (F : nat → R) :
    ex_seriesC (λ x : nat, if bool_decide (x ≤ M) then F x else 0).
  Proof. apply ex_seriesC_nat_bounded. Qed.

  (* Probably false.
  Lemma ex_RInt_gen_Ici_mult {L : R} {F G : R → R} :
    (∀ x, 0 <= F x) →
    (∀ x, 0 <= G x) →
    ex_RInt_gen F (at_point L) (Rbar_locally Rbar.p_infty) →
    ex_RInt_gen G (at_point L) (Rbar_locally Rbar.p_infty) →
    ex_RInt_gen (fun x => F x * G x) (at_point L) (Rbar_locally Rbar.p_infty).
  Proof.
  Admitted.
  *)

  Lemma is_RInt_gen_bound_partial {F : R → R} {L : R} {lF : R} :
    (∀ x, 0 <= F x) →
    (∀ bl bu, ex_RInt F bl bu) →
    is_RInt_gen F (at_point L) (Rbar_locally Rbar.p_infty) lF →
    ∀ bu, L <= bu → RInt F L bu <= lF.
  Proof.
    intros Hnn Hex HisRInt bu Hb.

    (* Convert is_RInt_gen to filterlim *)
    have Hlim : filterlim (λ bu : R, RInt F L bu) (Rbar_locally Rbar.p_infty) (locally lF).
    { apply (filterlim_is_RInt_gen).
      { intros ?. apply Hex. }
      { apply HisRInt. }
    }

    (* Show that RInt F L b is monotone increasing *)
    have Hmono : ∀ b1 b2, L <= b1 <= b2 → RInt F L b1 <= RInt F L b2.
    { intros b1 b2 [Hb1 Hb2].
      (* Use Chasles: RInt F L b2 = RInt F L b1 + RInt F b1 b2 *)
      have Hex_b1b2 : ex_RInt F b1 b2.
      { apply (ex_RInt_Chasles_2 (V := R_CompleteNormedModule)) with (a := L); try lra.
        apply Hex.
      }
      rewrite -(RInt_Chasles F L b1 b2); [|apply Hex|exact Hex_b1b2].
      (* Show 0 <= RInt F b1 b2 using non-negativity of F *)
      assert (0 <= RInt F b1 b2) as H0.
      { apply RInt_ge_0; try lra.
        { exact Hex_b1b2. }
        { intros x Hx. apply Hnn. }
      }
      rewrite /plus//=.
      apply Rplus_le_0_compat.
      apply RInt_ge_0; done.
    }

    (* Proof by contradiction: suppose RInt F L b > lF *)
    apply Rnot_lt_le. intro Hcontra.
    pose (ε := RInt F L bu - lF).
    have Hε_pos : 0 < ε by (unfold ε; lra).

    (* By filterlim, eventually RInt F L x is within ε/2 of lF *)
    have Hlim_ball : Rbar_locally Rbar.p_infty (λ b', ball lF (ε / 2) (RInt F L b')).
    { have Hε2_pos : 0 < ε/2 by lra.
      apply Hlim. exists (mkposreal (ε/2) Hε2_pos). simpl. intros y Hy. exact Hy. }

    (* Extract witness M such that for all b' > M, the distance is < ε/2 *)
    unfold Rbar_locally in Hlim_ball. destruct Hlim_ball as [M Hlim_ball].

    (* Choose b' >= max(b, M+1), so b' > M and b' >= b *)
    pose (b' := Rmax bu (M + 1)).
    have Hb'_M : M < b' by (unfold b'; generalize (Rmax_r bu (M + 1)); lra).
    have Hball : ball lF (ε / 2) (RInt F L b') by apply Hlim_ball, Hb'_M.
    have Hb'_ge_b : bu <= b' by (unfold b'; apply Rmax_l).

    (* By monotonicity, RInt F L b <= RInt F L b' *)
    have Hmono_bb' : RInt F L bu <= RInt F L b' by (apply Hmono; split; [exact Hb | exact Hb'_ge_b]).

    (* But Hball says |RInt F L b' - lF| < ε/2, contradicting RInt F L b - lF = ε *)
    unfold ball in Hball. simpl in Hball. unfold AbsRing_ball in Hball. simpl in Hball.
    have : Rabs (RInt F L b' - lF) < ε / 2 by exact Hball.
    intro Habs. generalize (Rabs_def2 _ _ Habs). unfold ε. lra.
  Qed.

  Lemma ex_RInt_gen_Ici_compare {L : R} {F G : R → R} :
    (∀ x, Continuity.continuous F x) →
    (∀ x, Continuity.continuous G x) →
    (∀ x, 0 <= G x <= F x) →
    ex_RInt_gen F (at_point L) (Rbar_locally Rbar.p_infty) →
    ex_RInt_gen G (at_point L) (Rbar_locally Rbar.p_infty).
  Proof.
    intros HFcont HGcont Hcomp HFex.
    unfold ex_RInt_gen in *.
    destruct HFex as [lF HFex].

    (* Step 1: G is integrable on [L,b] for all b ≥ L *)
    assert (HGint : ∀ b, L <= b → ex_RInt G L b).
    { intros b Hb.
      apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
      intros z Hz.
      apply HGcont.
    }

    (* Step 2: RInt G L b is monotone in b *)
    assert (Hmono : ∀ b1 b2, L <= b1 <= b2 → RInt G L b1 <= RInt G L b2).
    { intros b1 b2 [Hb1 Hb2].
      (* Need: ex_RInt G b1 b2 *)
      have Hexb1b2 : ex_RInt G b1 b2.
      { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros z Hz.
        apply HGcont.
      }
      (* Use Chasles: RInt G L b2 = RInt G L b1 + RInt G b1 b2 *)
      rewrite -(RInt_Chasles G L b1 b2); [|apply HGint; lra|exact Hexb1b2].
      (* Now show 0 <= RInt G b1 b2 *)
      assert (0 <= RInt G b1 b2) as H0.
      { apply RInt_ge_0; try lra.
        - exact Hexb1b2.
        - intros x Hx. apply Hcomp. }
      rewrite /plus//=.
      apply Rplus_le_0_compat.
      apply RInt_ge_0; try done.
      intros x Hx.
      apply Hcomp.
    }

    (* Step 3: RInt G L b is bounded above by lF *)
    assert (Hbound : ∀ b, L <= b → RInt G L b <= lF).
    { intros b Hb.
       apply Rle_trans with (r2 := RInt F L b).
       - apply RInt_le; try lra.
         { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
           intros ??.
           apply HGcont.
         }
         { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
           intros ??.
           apply HFcont.
         }
         intros ??; apply Hcomp.
       - apply is_RInt_gen_bound_partial; try done.
         { intros x; specialize Hcomp with x; lra. }
         { intros ??.
           apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
           intros ??.
           apply HFcont.
         }
    }

    (* Step 4: Construct the limit as supremum *)
    pose (lG := Lub_Rbar (fun r => ∃ b, L <= b ∧ r = RInt G L b)).
    assert (HlG_finite : Rbar.is_finite lG).
    { (* Use boundedness + monotonicity → finite supremum *)
      apply is_finite_bounded with (p := 0) (q := lF).
      - (* Show 0 <= lG *)
        rewrite /lG.
        apply Lub_Rbar_correct.
        exists L.
        split; [lra|].
        have -> : RInt G L L = zero by apply RInt_point.
        rewrite /zero/=.
        done.
      - (* Show lG <= lF *)
        rewrite /lG.
        apply Lub_Rbar_correct.
        intros r [b [Hb ->]].
        apply Hbound.
        done.
    }

    (* Step 5: Show lG is the limit *)
    exists (Rbar.real lG).
    apply is_RInt_gen_filterlim.
    { intros ?.
      apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
      intros ??.
      apply HGcont.
    }
    intros P HP.
    rewrite /Rbar_locally/filtermap//=.
    rewrite /locally //= in HP.
    destruct HP as [eps HP].
    have HlG_lub : is_lub_Rbar (fun r => ∃ b, L <= b ∧ r = RInt G L b) lG.
    { rewrite /lG. apply Lub_Rbar_correct. }
    destruct HlG_lub as [HlG_ub HlG_least].
    have HlG_val : lG = Rbar.Finite (Rbar.real lG).
    { apply Rbar.is_finite_correct in HlG_finite as [y Heq].
      rewrite Heq. simpl. done.
    }
    have Hnot_ub : ¬ is_ub_Rbar (fun r => ∃ b, L <= b ∧ r = RInt G L b) (Rbar.Finite (Rbar.real lG - eps / 2)).
    { intros Hub.
      have Hle : Rbar.Rbar_le lG (Rbar.Finite (Rbar.real lG - eps / 2)) by apply HlG_least; apply Hub.
      rewrite HlG_val in Hle. simpl in Hle.
      have Heps_pos : 0 < eps by apply cond_pos.
      lra.
    }
    rewrite /is_ub_Rbar in Hnot_ub.
    apply Classical_Pred_Type.not_all_ex_not in Hnot_ub as [r Hr].
    apply Classical_Prop.imply_to_and in Hr as [Hexists Hnot_le].
    destruct Hexists as [M [HM Hr_eq]].
    have Hgt : Rbar.real lG - eps / 2 < r.
    { apply Rnot_le_lt. intros Hle. apply Hnot_le.
      subst r. simpl. apply Hle.
    }
    exists M.
    intros x Hx.
    apply HP.
    rewrite /ball/=/AbsRing_ball/=.
    have HRInt_x_le_lG : RInt G L x <= Rbar.real lG.
    { have : Rbar.Rbar_le (Rbar.Finite (RInt G L x)) lG.
      { apply HlG_ub. exists x. split; [lra|done]. }
      rewrite HlG_val. simpl. done.
    }
    have HRInt_M_le_x : RInt G L M <= RInt G L x.
    { apply Hmono. split; [done|lra]. }
    subst r.
    have Hlower : Rbar.real lG - eps / 2 < RInt G L x.
    { apply Rlt_le_trans with (r2 := RInt G L M); [apply Hgt | apply HRInt_M_le_x]. }
    have Heps_pos : 0 < eps by apply cond_pos.
    have : - eps < RInt G L x - Rbar.real lG < eps by lra.
    intros [H1 H2].
    by apply Rabs_def1.
  Qed.

  (* Extend the function f to the left at point L *)
  Definition LeftExtend (f : R → R) (L : R) : R → R :=
    fun x => Iverson (Iio L) x * f L + Iverson (Ici L) x * f x.

  Lemma LeftExtend_eq_l {f : R → R} {L z : R} :
    z <= L → LeftExtend f L z = f L.
  Proof.
    intros H.
    rewrite /LeftExtend.
    rewrite /Iio/Ici//=.
    destruct (Rle_lt_or_eq _ _ H).
    { rewrite Iverson_True; [|lra].
      rewrite Iverson_False; [|lra].
      lra.
    }
    { rewrite Iverson_False; [|lra].
      rewrite Iverson_True; [|lra].
      rewrite H0.
      lra.
    }
  Qed.

  Lemma LeftExtend_eq_r {f : R → R} {L z : R} :
    L <= z → LeftExtend f L z = f z.
  Proof.
    intros H.
    rewrite /LeftExtend.
    rewrite Iverson_False.
    2: { rewrite /Iio; lra. }
    rewrite Iverson_True.
    2: { rewrite /Ici; lra. }
    lra.
  Qed.

  Lemma LeftExtend_nn {f : R → R} {L z : R} :
    (∀ x, L <= x → 0 <= f x) → 0 <= LeftExtend f L z.
  Proof.
    intros H.
    rewrite /LeftExtend.
    destruct (Rge_or_lt z L).
    { rewrite /Iio/Ici.
      rewrite Iverson_False.
      2: { rewrite /Iio; lra. }
      rewrite Iverson_True.
      2: { rewrite /Ici; lra. }
      rewrite Rmult_0_l Rplus_0_l Rmult_1_l.
      apply H.
      lra.
    }
    { rewrite /Iio/Ici.
      rewrite Iverson_True.
      2: { rewrite /Ici; lra. }
      rewrite Iverson_False.
      2: { rewrite /Iio; lra. }
      rewrite Rmult_0_l Rplus_0_r Rmult_1_l.
      apply H.
      lra.
    }
  Qed.

  Lemma LeftExtend_mono {f g : R → R} {L z : R} :
    (∀ x, L <= x → g x <= f x) → LeftExtend g L z <= LeftExtend f L z.
  Proof.
    intros H.
    rewrite /LeftExtend.
    destruct (Rge_or_lt z L).
    { rewrite /Iio/Ici.
      rewrite Iverson_False.
      2: { rewrite /Iio; lra. }
      rewrite Iverson_True.
      2: { rewrite /Ici; lra. }
      do 2 rewrite Rmult_0_l Rplus_0_l Rmult_1_l.
      apply H.
      lra.
    }
    { rewrite /Iio/Ici.
      rewrite Iverson_True.
      2: { rewrite /Ici; lra. }
      rewrite Iverson_False.
      2: { rewrite /Iio; lra. }
      do 2 rewrite Rmult_0_l Rplus_0_r Rmult_1_l.
      apply H.
      lra.
    }
  Qed.

  Lemma LeftExtend_continuous {f : R → R} {L : R}  :
    (∀ x, L <= x → Continuity.continuous f x) →
    (∀ x, Continuity.continuous (LeftExtend f L) x).
  Proof.
    intros H x.
    destruct (Rtotal_order L x) as [Hlt|[Heq|Hgt]].
    { (* (LeftExtend f L) is equal to f on a neighbourhood of x which is continuous by hypotheses. *)
      assert (Heps1 : 0 < (x - L) / 2) by lra.
      apply Continuity.continuous_ext_loc with (g := f).
      + rewrite /locally//=.
        exists (mkposreal ((x - L) / 2) Heps1).
        intros y Hy.
        rewrite /ball/=/AbsRing_ball/= in Hy.
        symmetry.
        apply LeftExtend_eq_r.
        admit.
      + apply H. lra.
    }
    { (* At the transition point: LeftExtend is constant equal to (f L) on the left and approaches (f L) on the right *)
      admit. }
    { (* (LeftExtend f L) is equal to f on a neighbourhood of x which is continuous by hypotheses. *)
      assert (Heps1 : 0 < (L - x) / 2) by lra.
      apply Continuity.continuous_ext_loc with (g := (fun (z : R) => f L)).
      + rewrite /locally//=.
        exists (mkposreal ((L - x) / 2) Heps1).
        intros y Hy.
        rewrite /ball/=/AbsRing_ball/= in Hy.
        symmetry.
        apply LeftExtend_eq_l.
        admit.
      + apply Continuity.continuous_const.
    }
  Admitted.

  Lemma ex_RInt_gen_Ici_compare_strong {L : R} {F G : R → R} :
    (∀ x, L <= x → Continuity.continuous F x) →
    (∀ x, L <= x → Continuity.continuous G x) →
    (∀ x, L <= x → 0 <= G x <= F x) →
    ex_RInt_gen F (at_point L) (Rbar_locally Rbar.p_infty) →
    ex_RInt_gen G (at_point L) (Rbar_locally Rbar.p_infty).
  Proof.
    intros Hf Hg Hfg Hex.
    apply (@ex_RInt_gen_ext_eq_Ici (LeftExtend G L)).
    { intros ??. by apply LeftExtend_eq_r. }
    apply (@ex_RInt_gen_Ici_compare L (LeftExtend F L) (LeftExtend G L)).
    { intros x; apply LeftExtend_continuous. intuition.  }
    { intros x; apply LeftExtend_continuous. intuition.  }
    { intros x.
      split.
      { apply LeftExtend_nn.
        intros ??.
        apply Hfg.
        done.
      }
      { apply LeftExtend_mono.
        intros ??.
        apply Hfg.
        done.
      }
    }
    apply (@ex_RInt_gen_ext_eq_Ici F).
    { intros ??. symmetry. by apply LeftExtend_eq_r. }
    done.
  Qed.

End Lib.




Section FubiniAx.

  Import Hierarchy.

  (* Current best condition for Fubini's theorem between definite integrals:
     Continuity on a rectangle.
     In fact, this implies boundedness, but we will not use this. *)
  Definition FubiniCondition (f : R → R → R_CompleteNormedModule) (xa xb ya yb : R) : Prop := forall x y,
    Rmin xa xb <= x <= Rmax xa xb →
    Rmin ya yb <= y <= Rmax ya yb →
    Continuity2 (uncurry f) x y.

  (* FubiniCondition implies integrability along any vertical line *)
  Theorem FubiniCondition_ex_RInt_x {f xa xb ya yb} :
    FubiniCondition f xa xb ya yb →
    ∀ y, Rmin ya yb <= y <= Rmax ya yb → ex_RInt (fun x => f x y) xa xb.
  Proof.
    rewrite /FubiniCondition.
    intros ???.
    apply ex_RInt_continuous.
    intros ??.
    specialize H with z y.
    have W := (H H1 H0).
    apply (Continuity2_continuous_fst W).
  Qed.

  (* FubiniCondition implies integrability along any horizontal line *)
  Theorem FubiniCondition_ex_RInt_y {f xa xb ya yb} :
    FubiniCondition f xa xb ya yb →
    ∀ x, Rmin xa xb <= x <= Rmax xa xb → ex_RInt (fun y => f x y) ya yb.
  Proof.
    rewrite /FubiniCondition.
    intros ???.
    apply ex_RInt_continuous.
    intros ??.
    specialize H with x z.
    have W := (H H0 H1).
    apply (Continuity2_continuous_snd W).
  Qed.

  Axiom Fubini_ex_x : ∀ {f xa xb ya yb}, FubiniCondition f xa xb ya yb →
    ex_RInt (fun x => RInt (fun y => f x y) ya yb) xa xb.

  Axiom Fubini_ex_y : ∀ {f xa xb ya yb}, FubiniCondition f xa xb ya yb →
    ex_RInt (fun y => RInt (fun x => f x y) xa xb) ya yb.

  Axiom Fubini_eq : ∀ {f xa xb ya yb}, FubiniCondition f xa xb ya yb →
    RInt (fun x => RInt (fun y => f x y) ya yb) xa xb =  RInt (fun y => RInt (fun x => f x y) xa xb) ya yb.

End FubiniAx.

(* Reduction: This implies Fubini's theorem holds for step functions by Chasales theorem *)

Section FubiniStep.
  Import Hierarchy.


  (* Continuity.continuity_2d_pt_filterlim ???? *)
  Definition IsFubiniCoreRR (f : R → R → R) : Prop :=
    ∀ x y, Continuity2 (uncurry f) x y.

  Definition IsFubiniCoreSR (f : nat → R → R) : Prop :=
    forall n x, Continuity.continuous (f n) x.

  Definition fsum {T : Type} (L : list (T → R)) : T → R := fun t => foldr (fun f s => f t + s) 0 L.

  Definition fsum2 {T U : Type} (L : list (T → U → R)) : T → U → R :=
    fun t u => foldr (fun f s => f t u + s) 0 L.

  (* A function on a rectangle *)
  Definition RectFun_RR : ((R → R → R) * R * R * R * R) → (R → R → R) :=
    fun '(f, xa, xb, ya, yb) x y => Iverson (Ioo xa xb) x * Iverson (Ioo ya yb) y * f x y.

  Definition RectFun_continuity : ((R → R → R) * R * R * R * R) → Prop :=
    fun '(f, xa, xb, ya, yb) => ∀ x y, Ioo xa xb x → Ioo ya yb y → Continuity2 (uncurry f) x y.

  (* Generalized: f is a finite sum of rectangle functions *)
  Definition IsFubiniRR (f : R → R → R) : Prop :=
    ∃ L, f = fsum2 (RectFun_RR <$> L) ∧ Forall RectFun_continuity L.

  Lemma Fubini_Step_ex_x {f xa xb ya yb} : IsFubiniRR f →
    ex_RInt (fun x => RInt (fun y => f x y) ya yb) xa xb.
  Proof.
    intros [L [-> HL]].
    induction L.
    { simpl. apply ex_RInt_const. }
    simpl.
    replace (λ x : R, RInt (λ y : R, RectFun_RR a x y + fsum2 (list_fmap ((R → R → R) * R * R * R * R)%type (R → R → R) RectFun_RR L) x y) ya yb)
       with (λ x : R, RInt (fun y : R => RectFun_RR a x y) ya yb + RInt (λ y : R, fsum2 (list_fmap ((R → R → R) * R * R * R * R)%type (R → R → R) RectFun_RR L) x y) ya yb).
    2: {
      apply functional_extensionality. intros x.
      rewrite RInt_plus.
      { done. }
      { rewrite /RectFun_RR//=.
        apply Forall_inv in HL.
        destruct a as [[[[f xa'] xb'] ya'] yb'].
        rewrite /RectFun_continuity//= in HL.
        apply (@ex_RInt_ext _ (λ y',  (uncurry f) (x, y'))).
        2: {
          apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
          intros ??.
          apply Continuity2_continuous_snd.
          apply HL.
          { admit. }
          { admit. }
        }
        { admit. }
      }
      admit.
    }
  apply (ex_RInt_plus (V := R_CompleteNormedModule)).
    2: { apply IHL. exact (Forall_inv_tail HL). }
    admit.
  Admitted.

  Lemma Fubini_Step_ex_y {f xa xb ya yb} : IsFubiniRR f →
    ex_RInt (fun y => RInt (fun x => f x y) xa xb) ya yb.
  Proof.
  Admitted.

  Lemma Fubini_Step_eq : ∀ {f xa xb ya yb}, IsFubiniRR f →
    RInt (fun x => RInt (fun y => f x y) ya yb) xa xb =  RInt (fun y => RInt (fun x => f x y) xa xb) ya yb.
  Proof.
  Admitted.

End FubiniStep.



(* Reduction: This implies Fubini's theorem holds for improper integrals? *)


Section FubiniImproper.
  Import Hierarchy.

  (* FubiniImproper_ex *)
  Theorem FubiniImproper_ex_x {f xa ya yb} (H : ∀ xb, FubiniCondition f xa xb ya yb) (HInt : True) :
    ex_RInt_gen (fun x => RInt (fun y => f x y) ya yb) (at_point xa) (Rbar_locally Rbar.p_infty).
  Proof.
    unfold ex_RInt_gen.
    suffices Hlim : ∃ l, filterlim (λ b : R, RInt (λ x : R, RInt (λ y : R, f x y) ya yb) xa b) (Rbar_locally Rbar.p_infty) (locally l).
    { destruct Hlim as [l Hl]; exists l.
      apply is_RInt_gen_filterlim; [|exact Hl].
      intros b.
      apply Fubini_ex_x.
      apply H.
    }
    (* Side condition, the integrals needs to be finite? Is there a general theorem I can prove here? *)
    admit.
  Admitted.

  Theorem FubiniImproper_ex_y {f xa ya yb} (H : ∀ xb, FubiniCondition f xa xb ya yb) (HInt : True) :
    ex_RInt (fun y => (RInt_gen (fun x => f x y) (at_point xa) (Rbar_locally Rbar.p_infty))) ya yb.
  Proof.
    unfold ex_RInt.
    suffices Hlim : ∃ l, is_RInt (λ y : R, iota (λ IF : R, filterlim (λ b : R, RInt (λ x : R, f x y) xa b) (Rbar_locally Rbar.p_infty) (locally IF))) ya yb l.
    { destruct Hlim as [l Hl]; exists l.
      eapply is_RInt_ext; [|exact Hl].
      intros y Hy.
      symmetry; apply filterlim_RInt_gen.
      intros xb.
      apply (@FubiniCondition_ex_RInt_x f xa xb ya yb (H xb) y).
      lra.
    }
    (*
    Search RInt_gen iota.
    Check (iota (is_RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty))).
    Search RInt_gen.
    Check filterlim.
    *)
  Admitted.

  Theorem FubiniImproper_eq {f xa ya yb} (H : ∀ xb, FubiniCondition f xa xb ya yb)
    (HInt : True) :
    RInt_gen (fun x => RInt (fun y => f x y) ya yb) (at_point xa) (Rbar_locally Rbar.p_infty) =
    RInt (fun y => (RInt_gen (fun x => f x y) (at_point xa) (Rbar_locally Rbar.p_infty))) ya yb.
  Proof.
    rewrite filterlim_RInt_gen.
    2: {
      intros xb.
      apply Fubini_ex_x.
      apply H.
    }
    replace (RInt (λ y : R, RInt_gen (λ x : R, f x y) (at_point xa) (Rbar_locally Rbar.p_infty)) ya yb)
       with (RInt (λ y : R, iota (λ IF : R, filterlim (λ b : R, RInt (λ x : R, f x y) xa b) (Rbar_locally Rbar.p_infty) (locally IF))) ya yb).
    2: {
      apply RInt_ext.
      intros y Hy.
      symmetry; apply filterlim_RInt_gen.
      intros xb.
      apply (@FubiniCondition_ex_RInt_x f xa xb ya yb (H xb) y).
      lra.
    }
    apply @iota_filterlim_locally.
    { apply Proper_StrongProper. apply Rbar_locally_filter. }
    (* Apply Definite/Definite Fubini *)
    replace (λ xb : R, RInt (λ x : R, RInt (λ y : R, f x y) ya yb) xa xb)
      with  (λ xb : R, RInt (λ y : R, RInt (λ x : R, f x y) xa xb) ya yb).
    2: { apply functional_extensionality. intros xb. rewrite -Fubini_eq; done. }
    apply (@Exchange2 (λ xb y : R, RInt (λ x : R, f x y) xa xb) ya yb
      (λ y : R, iota (λ IF : R, filterlim (λ b : R, RInt (λ x : R, f x y) xa b) (Rbar_locally Rbar.p_infty) (locally IF)))).
    { intros xb. apply Fubini_ex_y. apply H.  }

    replace (λ y : R, iota (λ IF : R, filterlim (λ b : R, RInt (λ x : R, f x y) xa b) (Rbar_locally Rbar.p_infty) (locally IF)))
       with (λ y : R, RInt_gen (λ x : R, f x y) (at_point xa) (Rbar_locally Rbar.p_infty)).
    2: { apply functional_extensionality. intros y. apply filterlim_RInt_gen.
         intros xb. apply (@FubiniCondition_ex_RInt_x f xa xb ya yb (H xb) y).
         (* We can improve FubiniCondition to FubiniConditionU that applies on the entire x/y plane,
            and requires that the function be zero outside of the rectangle.  *)
         admit.
    }

    (* I think we can prove this with something like the Cauchy Critereon

      A family of functions indexed by a real number r converges as the r → ∞
      if for evey epsilon, there exists R such that the for every R' > R,
      the sup of f on [R, R'] is bounded above by epsilon *)



  Admitted.

End FubiniImproper.
