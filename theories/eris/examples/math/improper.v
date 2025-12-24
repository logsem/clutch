From clutch.eris.examples.math Require Import prelude iverson sets piecewise integrals.
From clutch.eris Require Import infinite_tape.
Set Default Proof Using "Type*".
#[local] Open Scope R.
Import Hierarchy.

(** Improper integrals, AKA integrals where one bound is infinite.
This is a special case of RInt_gen. *)

Lemma ex_RInt_gen_0 M:
  ex_RInt_gen (λ _, 0) (at_point M) (Rbar_locally Rbar.p_infty).
Proof.
  eexists 0.
  intros ??.
  rewrite /filtermapi/=.
  econstructor.
  - by instantiate (1:=λ _, True).
  - simpl. instantiate (1:=λ _, True). exists 1. naive_solver.
  - intros x y ? ?.
    exists 0.
    split.
    + pose proof is_RInt_const x y 0 as H2.
      simpl.
      by rewrite scal_zero_r in H2.
    + by apply locally_singleton.
Qed.

Lemma RInt_gen_0 M:
  RInt_gen (λ _, 0) (at_point M) (Rbar_locally Rbar.p_infty) = 0.
Proof.
  apply is_RInt_gen_unique.
  intros ??.
  rewrite /filtermapi/=.
  econstructor.
  - by instantiate (1:=λ _, True).
  - simpl. instantiate (1:=λ _, True). exists 1. naive_solver.
  - intros x y ? ?.
    exists 0.
    split.
    + pose proof is_RInt_const x y 0 as H2.
      simpl.
      by rewrite scal_zero_r in H2.
    + by apply locally_singleton.
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

Lemma ex_RInt_gen_ext_eq_Ioi {f g : R → R} {M : R} :
  (∀ x : R, M < x → f x = g x) →
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

Lemma RInt_gen_ext_eq_Ioi {f g : R → R} {M : R} :
  (∀ x : R, M < x → f x = g x) →
  ex_RInt_gen f (at_point M) (Rbar_locally Rbar.p_infty) →
  RInt_gen f (at_point M) (Rbar_locally Rbar.p_infty) = RInt_gen g (at_point M) (Rbar_locally Rbar.p_infty).
Proof.
  intros ??.
  apply RInt_gen_ext; [|done].
  simpl.
  eapply (Filter_prod _ _ _ (fun x => x = M) (fun x => M < x)).
  { rewrite /at_point//=. }
  { rewrite //=. exists M. intuition. }
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

Lemma RInt_gen_ex_Ici' {M : R} {F : R → R}
  (Hlimit : exists L : R_NormedModule, (filterlimi (λ b : R, is_RInt F M b) (Rbar_locally Rbar.p_infty)) (locally L))
  (Hex : ∀ b, M<b ->ex_RInt F M b) :
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

Lemma RInt_gen_Ici_strong {M : R} {F : R → R} {L}
  (Hlimit : filterlimi (λ b : R, is_RInt F M b) (Rbar_locally Rbar.p_infty) (locally L))
  (Hex : ∀ b, M < b → ex_RInt F M b) :
  RInt_gen F (at_point M) (Rbar_locally (Rbar.p_infty)) = L.
Proof.
  have Hcorr : is_RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty) (RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty)).
  { eapply (@RInt_gen_correct R_CompleteNormedModule).
    { apply Proper_StrongProper, at_point_filter. }
    { apply Proper_StrongProper, Rbar_locally_filter. }
    apply RInt_gen_ex_Ici'.
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

(** Key lemma: An improper integral is the limit of proper integrals *)
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

(** Key lemma: An improper integral is the limit of proper integrals *)
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

Lemma filterlim_is_RInt_gen' {F : R → R_CompleteNormedModule} {M : R} {l : R_CompleteNormedModule} :
  (∀ b, M<b -> ex_RInt F M b) →
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

(** Key lemma: An improper integral is the limit of proper integrals *)
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

Lemma RInt_gen_pos_ex' {F M}
  (Hpos : forall x, M<x -> 0 <= F x)
  (Hex : ∀ b, M<b -> ex_RInt F M b)
  (Hnn : ∀ b, M<b -> 0 <= RInt F M b)
  (Hex_L : ex_RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty)) :
  0 <= RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty).
Proof.
  apply (Lim_seq.filterlim_le (F := Rbar_locally Rbar.p_infty) (fun _ => 0)
           (fun b => RInt F M b) (Rbar.Finite 0) (Rbar.Finite (RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty)))).
  { simpl. naive_solver. }
    { apply filterlim_const. }
    { intros P HP.
      unfold Rbar_locally in HP. simpl in HP.
      eapply (filterlim_is_RInt_gen'); last exact; last by apply RInt_gen_correct.
      intros. naive_solver.
    }
Qed. 

(*
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

(*
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
      a dmit.
    + apply H. lra.
  }
  { (* At the transition point: LeftExtend is constant equal to (f L) on the left and approaches (f L) on the right *)
    a dmit. }
  { (* (LeftExtend f L) is equal to f on a neighbourhood of x which is continuous by hypotheses. *)
    assert (Heps1 : 0 < (L - x) / 2) by lra.
    apply Continuity.continuous_ext_loc with (g := (fun (z : R) => f L)).
    + rewrite /locally//=.
      exists (mkposreal ((L - x) / 2) Heps1).
      intros y Hy.
      rewrite /ball/=/AbsRing_ball/= in Hy.
      symmetry.
      apply LeftExtend_eq_l.
      a dmit.
    + apply Continuity.continuous_const.
  }
A dmitted.

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
*)

Lemma RInt_gen_pos_strong {F M}
  (Hpos : forall x, 0 <= F x)
  (Hex : ∀ b, ex_RInt F M b)
  (Hnn : ∀ b, M <= b → 0 <= RInt F M b)
  (Hex_L : ex_RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty)) :
  0 <= RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty).
Proof.
  rewrite (RInt_gen_ext_eq_Ioi (g:=λ x, if bool_decide (M<=x) then F x else 0)); try done; last (intros; case_bool_decide; lra).
  apply RInt_gen_pos_ex.
  - intros; case_bool_decide; naive_solver.
  - intros.
    destruct (decide (M<=b)).
    + eapply ex_RInt_ext; last done.
      unfold Rmin, Rmax.
      intros. rewrite bool_decide_eq_true_2; first done.
      case_match; lra.
    + eapply (ex_RInt_ext (λ _, 0)); last apply ex_RInt_const.
      unfold Rmin, Rmax.
      intros. rewrite bool_decide_eq_false_2; first done.
      case_match; lra.
  - intros. 
    destruct (decide (M<=b)).
    + erewrite RInt_ext; first naive_solver.
      unfold Rmin, Rmax.
      intros. rewrite bool_decide_eq_true_2; first done.
      case_match; lra.
    + erewrite (RInt_ext _ (λ _, 0)).
      * rewrite RInt_const. rewrite /scal/=/mult/=. lra.
      * unfold Rmin, Rmax.
        intros. rewrite bool_decide_eq_false_2; first done.
        case_match; lra.
  - eapply ex_RInt_gen_ext_eq_Ioi; last done.
    intros.
    case_bool_decide; lra.
Qed. 

(*
Lemma ex_RInt_gen_Ici_scal {M G L} :
  ex_RInt_gen G L (Rbar_locally Rbar.p_infty) →
  ex_RInt_gen (λ x : R, M * G x) L (Rbar_locally Rbar.p_infty).
Proof. A dmitted.

Lemma RInt_gen_Ici_scal {M G L} :
  ex_RInt_gen G L (Rbar_locally Rbar.p_infty) →
  M * RInt_gen G L (Rbar_locally Rbar.p_infty) = RInt_gen (λ x : R, M * G x) L (Rbar_locally Rbar.p_infty).
Proof. A dmitted.
*)

(*
Lemma NegExp_prod_bounded_left {F G : R → R} {M}
  (HFCts : ∀ x, Continuity.continuous F x)
  (HGCts : ∀ x, Continuity.continuous G x)
  (HFnn : ∀ x, 0 <= F x <= M)
  (HGnn : ∀ x, 0 <= G x)
  (HIntG : ex_RInt_gen G (at_point 0) (Rbar_locally Rbar.p_infty)) :
  ex_RInt_gen (fun x => F x * G x) (at_point 0) (Rbar_locally Rbar.p_infty).
Proof.
  apply (@ex_RInt_gen_Ici_compare_strong 0 (fun x => M * G x) (fun x => F x * G x)).
  - intros ??.
    apply @Continuity.continuous_mult.
    { apply Continuity.continuous_const. }
    { done. }
  - (* Continuity of F * G *)
    intros ??.
    apply @Continuity.continuous_mult; done.
  - (* Bound: 0 ≤ F x * G x ≤ M * G x *)
    intros x Hx.
    split.
    + apply Rmult_le_pos; [apply HFnn | apply HGnn].
    + destruct (HFnn x) as [HF0 HFM].
      apply Rmult_le_compat_r; [apply HGnn | apply HFM].
  - (* M * G is integrable from 0 to infinity *)
    apply (@ex_RInt_gen_ext_eq_Ici (fun x => scal M (G x)) (fun x => M * G x) 0).
    + intros x Hx. rewrite /scal /= /mult /=.
      lra.
    + apply ex_RInt_gen_Ici_scal. apply HIntG.
Qed.
*)

(** Helper lemmas for IPCts version *)

Lemma ex_RInt_gen_plus {F G : R → R} {M : R} :
  ex_RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty) →
  ex_RInt_gen G (at_point M) (Rbar_locally Rbar.p_infty) →
  ex_RInt_gen (fun x => F x + G x) (at_point M) (Rbar_locally Rbar.p_infty).
Proof.
  intros [x1 H1].
  intros [x2 H2].
  eapply is_RInt_gen_plus in H2; last apply H1.
  eexists _.
  by rewrite /plus/= in H2.
Qed. 

Lemma ex_RInt_gen_scal_l {F : R → R} {M : R} r:
  ex_RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty) →
  ex_RInt_gen (fun x => r * F x) (at_point M) (Rbar_locally Rbar.p_infty).
Proof.
  intros [x H].
  exists (r*x).
  apply (is_RInt_gen_scal _ r) in H.
  rewrite /scal/=/mult/= in H.
  eapply is_RInt_gen_ext; last done.
  apply (Filter_prod _ _ _ (λ _, True) (λ _, True)); try done.
  simpl.
  by exists 0.
Qed. 

Lemma ex_RInt_gen_scal_r {F : R → R} {M : R} r:
  ex_RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty) →
  ex_RInt_gen (fun x => F x * r) (at_point M) (Rbar_locally Rbar.p_infty).
Proof. 
  intros [x H].
  exists (r*x).
  apply (is_RInt_gen_scal _ r) in H.
  rewrite /scal/=/mult/= in H.
  eapply is_RInt_gen_ext; last done.
  apply (Filter_prod _ _ _ (λ _, True) (λ _, True)); try done; last (intros; lra).
  simpl. by exists 0.
Qed.

Lemma ex_RInt_gen_div {F : R → R} {M : R} r:
  ex_RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty) →
  ex_RInt_gen (fun x => F x / r) (at_point M) (Rbar_locally Rbar.p_infty).
Proof. 
  intros [x H].
  exists (/r * x).
  apply (is_RInt_gen_scal _ (/r)) in H.
  rewrite /scal/=/mult/= in H.
  eapply is_RInt_gen_ext; last done.
  apply (Filter_prod _ _ _ (λ _, True) (λ _, True)); try done; last (intros; lra).
  simpl. by exists 0.
Qed. 

Lemma ex_RInt_gen_fsum {L : list (R → R)} {M : R} :
  Forall (fun f => ex_RInt_gen f (at_point M) (Rbar_locally Rbar.p_infty)) L →
  ex_RInt_gen (fsum L) (at_point M) (Rbar_locally Rbar.p_infty).
Proof.
  induction L as [|a ? IHL].
  - simpl. intros.
    eapply ex_RInt_gen_ext_eq_Ioi; [done|apply ex_RInt_gen_0].
  - rewrite Forall_cons.
    intros [H1 H2].
    apply (ex_RInt_gen_ext_eq_Ioi (f:= λ x, a x + fsum L x)); first done.
    apply ex_RInt_gen_plus; naive_solver.
Qed. 

(** THIS IS WRONG, but luckily no lemma needs this. 
Note that the problem is that we do not have any inequalities on f and g on the boundary, e.g. af *)
(* Lemma IntervalFun_product_bounded {f g : R → R} {af bf ag bg : R} {M : R} : *)
(*   (∀ x, Ioo af bf x → 0 <= f x <= M) → *)
(*   (∀ x, Ioo ag bg x → 0 <= g x) → *)
(*   (∀ x, 0 <= IntervalFun_R (f, af, bf) x * IntervalFun_R (g, ag, bg) x *)
(*         <= M * IntervalFun_R (g, ag, bg) x). *)
(* Proof. *)
(*   intros H1 H2 x. *)
(*   split. *)
(*   - unfold IntervalFun_R, Iverson, Icc, Ioo, Rmin, Rmax in *. *)
(*     repeat case_match; try lra. *)
    

Lemma fsum_product {T : Type} (LF LG : list (T → R)) (x : T) :
  fsum LF x * fsum LG x =
  fsum (map (fun '(f, g) => fun t => f t * g t) (list_prod LF LG)) x.
Proof.
  induction LF as [|f LF IH]; simpl; [lra|].
  rewrite Rmult_plus_distr_r. rewrite IH.
  rewrite map_app fsum_app. f_equal.
  clear.
  induction LG as [|g LG IHLG]; simpl; first lra.
  rewrite Rmult_plus_distr_l.
  rewrite IHLG. lra.
Qed.


(** IPCts version of comparison test *)
Lemma ex_RInt_gen_Ici_compare_IPCts {L : R} {F G : R → R} :
  IPCts F →
  IPCts G →
  (∀ x, 0 <= G x <= F x) →
  ex_RInt_gen F (at_point L) (Rbar_locally Rbar.p_infty) →
  ex_RInt_gen G (at_point L) (Rbar_locally Rbar.p_infty).
Proof.
  intros HF HG Hbound HFex.
  destruct HF as [F0 [LF [HeqF [HcontF HcontF0]]]].
  destruct HG as [G0 [LG [HeqG [HcontG HcontG0]]]].
  unfold ex_RInt_gen in *. destruct HFex as [lF HFex].
  have HeqF' : F = (fun x => F0 x + fsum (IntervalFun_R <$> LF) x).
  { apply functional_extensionality. intros ?. by rewrite HeqF. }
  have HeqG' : G = (fun x => G0 x + fsum (IntervalFun_R <$> LG) x).
  { apply functional_extensionality. intros ?. by rewrite HeqG. }
  assert (HGint : ∀ b, L <= b → ex_RInt G L b).
  { intros b Hb. rewrite HeqG'.  apply IPCts_RInt. exists G0. exists LG. split; done. }
  assert (HFint : ∀ b, L <= b → ex_RInt F L b).
  { intros b Hb. rewrite HeqF'. apply IPCts_RInt. exists F0. exists LF. split; done. }
  assert (Hmono : ∀ b1 b2, L <= b1 <= b2 → RInt G L b1 <= RInt G L b2).
  { intros b1 b2 [Hb1 Hb2].
    have Hexb1b2 : ex_RInt G b1 b2.
    { rewrite HeqG'. apply IPCts_RInt. exists G0. exists LG. split; done. }
    rewrite -(RInt_Chasles G L b1 b2); [|apply HGint; lra|exact Hexb1b2].
    assert (0 <= RInt G b1 b2) as H0.
    { apply RInt_ge_0; try lra; [exact Hexb1b2 | intros x Hx; apply Hbound; lra]. }
    rewrite /plus//=. lra.
  }
  assert (Hbound_F : ∀ b, L <= b → RInt G L b <= lF).
  { intros b Hb.
    apply Rle_trans with (r2 := RInt F L b).
    { apply RInt_le; try lra; [apply HGint; done | apply HFint; done | intros x Hx; apply Hbound; lra]. }
    { apply is_RInt_gen_bound_partial; try done.
      { intros x. specialize Hbound with x. lra. }
      { intros bl bu. rewrite HeqF'. apply IPCts_RInt. exists F0. exists LF. split; done. } }
  }
  pose (lG := Lub_Rbar (fun r => ∃ b, L <= b ∧ r = RInt G L b)).
  assert (HlG_finite : Rbar.is_finite lG).
  { apply is_finite_bounded with (p := 0) (q := lF); rewrite /lG; apply Lub_Rbar_correct.
    { exists L. split; [lra|]. have -> : RInt G L L = zero by apply RInt_point. rewrite /zero/=. done. }
    { intros r [b [Hb ->]]. apply Hbound_F. done. }
  }

  exists (Rbar.real lG).
  apply is_RInt_gen_filterlim.
  { intros b. rewrite HeqG'. apply IPCts_RInt. exists G0. exists LG. split; done. }
  intros P HP.
    rewrite /Rbar_locally/filtermap//=.
    rewrite /locally //= in HP.
    destruct HP as [eps HP].
    have HlG_lub : is_lub_Rbar (fun r => ∃ b, L <= b ∧ r = RInt G L b) lG.
    { rewrite /lG. apply Lub_Rbar_correct. }
    destruct HlG_lub as [HlG_ub HlG_least].
    have HlG_val : lG = Rbar.Finite (Rbar.real lG).
    { apply Rbar.is_finite_correct in HlG_finite as [y Heq].
      rewrite Heq. simpl. done. }
    have Hnot_ub : ¬ is_ub_Rbar (fun r => ∃ b, L <= b ∧ r = RInt G L b) (Rbar.Finite (Rbar.real lG - eps / 2)).
    { intros Hub.
      have Hle : Rbar.Rbar_le lG (Rbar.Finite (Rbar.real lG - eps / 2)) by apply HlG_least; apply Hub.
      rewrite HlG_val in Hle. simpl in Hle.
      have Heps_pos : 0 < eps by apply cond_pos.
      lra. }
    rewrite /is_ub_Rbar in Hnot_ub.
    apply Classical_Pred_Type.not_all_ex_not in Hnot_ub as [r Hr].
    apply Classical_Prop.imply_to_and in Hr as [Hexists Hnot_le].
    destruct Hexists as [M [HM Hr_eq]].
    have Hgt : Rbar.real lG - eps / 2 < r.
    { apply Rnot_le_lt. intros Hle. apply Hnot_le.
      subst r. simpl. apply Hle. }
    exists M.
    intros x Hx.
    apply HP.
    rewrite /ball/=/AbsRing_ball/=.
    have HRInt_x_le_lG : RInt G L x <= Rbar.real lG.
    { have : Rbar.Rbar_le (Rbar.Finite (RInt G L x)) lG.
      { apply HlG_ub. exists x. split; [lra|done]. }
      rewrite HlG_val. simpl. done. }
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

Lemma ex_RInt_gen_Ici_compare_PCts {L : R} {F G : R → R} :
  (∀ x y, PCts F x y) →
  (∀ x y, PCts G x y) →
  (∀ x, 0 <= G x <= F x) →
  ex_RInt_gen F (at_point L) (Rbar_locally Rbar.p_infty) →
  ex_RInt_gen G (at_point L) (Rbar_locally Rbar.p_infty).
Proof.
  intros HF HG Hbound HFex.
  unfold ex_RInt_gen in *. destruct HFex as [lF HFex].
  (* have HeqF' : F = (fun x => F0 x + fsum (IntervalFun_R <$> LF) x). *)
  (* { apply functional_extensionality. intros ?. by rewrite HeqF. } *)
  (* have HeqG' : G = (fun x => G0 x + fsum (IntervalFun_R <$> LG) x). *)
  (* { apply functional_extensionality. intros ?. by rewrite HeqG. } *)
  assert (HGint : ∀ b, L <= b → ex_RInt G L b).
  { intros b Hb.
    by apply PCts_RInt. }
  assert (HFint : ∀ b, L <= b → ex_RInt F L b).
  { intros b Hb.
    by apply PCts_RInt. }
  assert (Hmono : ∀ b1 b2, L <= b1 <= b2 → RInt G L b1 <= RInt G L b2).
  { intros b1 b2 [Hb1 Hb2].
    have Hexb1b2 : ex_RInt G b1 b2.
    { apply: ex_RInt_Chasles_2; last apply HGint; lra. }
    rewrite -(RInt_Chasles G L b1 b2); [|apply HGint; lra|exact Hexb1b2].
    assert (0 <= RInt G b1 b2) as H0.
    { apply RInt_ge_0; try lra; [exact Hexb1b2 | intros x Hx; apply Hbound; lra]. }
    rewrite /plus//=. lra.
  }
  assert (Hbound_F : ∀ b, L <= b → RInt G L b <= lF).
  { intros b Hb.
    apply Rle_trans with (r2 := RInt F L b).
    { apply RInt_le; try lra; [apply HGint; done | apply HFint; done | intros x Hx; apply Hbound; lra]. }
    { apply is_RInt_gen_bound_partial; try done.
      { intros x. specialize Hbound with x. lra. }
      { intros bl bu.
        by apply PCts_RInt.
      }
    }
  }
  pose (lG := Lub_Rbar (fun r => ∃ b, L <= b ∧ r = RInt G L b)).
  assert (HlG_finite : Rbar.is_finite lG).
  { apply is_finite_bounded with (p := 0) (q := lF); rewrite /lG; apply Lub_Rbar_correct.
    { exists L. split; [lra|]. have -> : RInt G L L = zero by apply RInt_point. rewrite /zero/=. done. }
    { intros r [b [Hb ->]]. apply Hbound_F. done. }
  }

  exists (Rbar.real lG).
  apply is_RInt_gen_filterlim.
  { intros b. by apply PCts_RInt. }
  intros P HP.
    rewrite /Rbar_locally/filtermap//=.
    rewrite /locally //= in HP.
    destruct HP as [eps HP].
    have HlG_lub : is_lub_Rbar (fun r => ∃ b, L <= b ∧ r = RInt G L b) lG.
    { rewrite /lG. apply Lub_Rbar_correct. }
    destruct HlG_lub as [HlG_ub HlG_least].
    have HlG_val : lG = Rbar.Finite (Rbar.real lG).
    { apply Rbar.is_finite_correct in HlG_finite as [y Heq].
      rewrite Heq. simpl. done. }
    have Hnot_ub : ¬ is_ub_Rbar (fun r => ∃ b, L <= b ∧ r = RInt G L b) (Rbar.Finite (Rbar.real lG - eps / 2)).
    { intros Hub.
      have Hle : Rbar.Rbar_le lG (Rbar.Finite (Rbar.real lG - eps / 2)) by apply HlG_least; apply Hub.
      rewrite HlG_val in Hle. simpl in Hle.
      have Heps_pos : 0 < eps by apply cond_pos.
      lra. }
    rewrite /is_ub_Rbar in Hnot_ub.
    apply Classical_Pred_Type.not_all_ex_not in Hnot_ub as [r Hr].
    apply Classical_Prop.imply_to_and in Hr as [Hexists Hnot_le].
    destruct Hexists as [M [HM Hr_eq]].
    have Hgt : Rbar.real lG - eps / 2 < r.
    { apply Rnot_le_lt. intros Hle. apply Hnot_le.
      subst r. simpl. apply Hle. }
    exists M.
    intros x Hx.
    apply HP.
    rewrite /ball/=/AbsRing_ball/=.
    have HRInt_x_le_lG : RInt G L x <= Rbar.real lG.
    { have : Rbar.Rbar_le (Rbar.Finite (RInt G L x)) lG.
      { apply HlG_ub. exists x. split; [lra|done]. }
      rewrite HlG_val. simpl. done. }
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

Lemma ex_RInt_gen_Ici_compare_PCts' {L : R} {F G : R → R} :
  (∀ x, L<x -> PCts F L x) →
  (∀ x, L<x -> PCts G L x) →
  (∀ x, L<x -> 0 <= G x <= F x) →
  ex_RInt_gen F (at_point L) (Rbar_locally Rbar.p_infty) →
  ex_RInt_gen G (at_point L) (Rbar_locally Rbar.p_infty).
Proof.
  pose (F' := λ x, if bool_decide (L<x) then F x else 0).
  pose (G' := λ x, if bool_decide (L<x) then G x else 0).
  intros H1 H2 H3 H4.
  apply (ex_RInt_gen_ext_eq_Ioi (f:=G')).
  { intros. rewrite /G'. by rewrite bool_decide_eq_true_2. }
  apply: (ex_RInt_gen_Ici_compare_PCts (F:=F')).
  - intros.
    destruct (decide (Rmax x y <= L)).
    { apply (PCts_ext (λ _, 0)).
      - rewrite /F'.
        intros.
        case_bool_decide; last done.
        unfold Ioo, Rmax, Rmin in *. lra.
      - apply IPCts_PCts. apply IPCts_cts.
        intros. apply Continuity.continuous_const.
    } 
    destruct (decide (L<=Rmin x y)).
    { (* positive territory *)
      apply (PCts_ext F).
      - rewrite /F'.
        intros.
        case_bool_decide; first done.
        unfold Ioo, Rmax, Rmin in *. lra.
      - eapply (PCts_subset _ L _ (Rmax x y)).
        + unfold Rmin, Rmax in *. repeat case_match; lra.
        + unfold Rmin, Rmax in *. repeat case_match; lra.
        + apply H1. unfold Rmin, Rmax in *. repeat case_match; lra.
    }
    (* need to split between both *)
    eapply PCts_split with L.
    + unfold Rmin, Rmax in *. repeat case_match; lra.
    + destruct (decide (x<=y)).
      * apply (PCts_ext (λ _, 0)).
        -- rewrite /F'.
           intros.
           case_bool_decide; last done.
           unfold Ioo, Rmax, Rmin in *. repeat case_match; lra.
        -- apply IPCts_PCts. apply IPCts_cts.
           intros. apply Continuity.continuous_const.
      * apply (PCts_ext F).
        -- rewrite /F'.
           intros.
           case_bool_decide; first done.
           unfold Ioo, Rmax, Rmin in *. repeat case_match; lra.
        -- eapply (PCts_subset _ L _ (Rmax x y)).
           ++ unfold Rmin, Rmax in *. repeat case_match; lra.
           ++ unfold Rmin, Rmax in *. repeat case_match; lra.
           ++ apply H1. unfold Rmin, Rmax in *. repeat case_match; lra.
    + destruct (decide (x<=y)).
      * apply (PCts_ext F).
        -- rewrite /F'.
           intros.
           case_bool_decide; first done.
           unfold Ioo, Rmax, Rmin in *. repeat case_match; lra.
        -- eapply (PCts_subset _ L _ (Rmax x y)).
           ++ unfold Rmin, Rmax in *. repeat case_match; lra.
           ++ unfold Rmin, Rmax in *. repeat case_match; lra.
           ++ apply H1. unfold Rmin, Rmax in *. repeat case_match; lra.
      * apply (PCts_ext (λ _, 0)).
        -- rewrite /F'.
           intros.
           case_bool_decide; last done.
           unfold Ioo, Rmax, Rmin in *. repeat case_match; lra.
        -- apply IPCts_PCts. apply IPCts_cts.
           intros. apply Continuity.continuous_const.
  - intros.
    destruct (decide (Rmax x y <= L)).
    { apply (PCts_ext (λ _, 0)).
      - rewrite /G'.
        intros.
        case_bool_decide; last done.
        unfold Ioo, Rmax, Rmin in *. lra.
      - apply IPCts_PCts. apply IPCts_cts.
        intros. apply Continuity.continuous_const.
    } 
    destruct (decide (L<=Rmin x y)).
    { (* positive territory *)
      apply (PCts_ext G).
      - rewrite /G'.
        intros.
        case_bool_decide; first done.
        unfold Ioo, Rmax, Rmin in *. lra.
      - eapply (PCts_subset _ L _ (Rmax x y)).
        + unfold Rmin, Rmax in *. repeat case_match; lra.
        + unfold Rmin, Rmax in *. repeat case_match; lra.
        + apply H2. unfold Rmin, Rmax in *. repeat case_match; lra.
    }
    (* need to split between both *)
    eapply PCts_split with L.
    + unfold Rmin, Rmax in *. repeat case_match; lra.
    + destruct (decide (x<=y)).
      * apply (PCts_ext (λ _, 0)).
        -- rewrite /G'.
           intros.
           case_bool_decide; last done.
           unfold Ioo, Rmax, Rmin in *. repeat case_match; lra.
        -- apply IPCts_PCts. apply IPCts_cts.
           intros. apply Continuity.continuous_const.
      * apply (PCts_ext G).
        -- rewrite /G'.
           intros.
           case_bool_decide; first done.
           unfold Ioo, Rmax, Rmin in *. repeat case_match; lra.
        -- eapply (PCts_subset _ L _ (Rmax x y)).
           ++ unfold Rmin, Rmax in *. repeat case_match; lra.
           ++ unfold Rmin, Rmax in *. repeat case_match; lra.
           ++ apply H2. unfold Rmin, Rmax in *. repeat case_match; lra.
    + destruct (decide (x<=y)).
      * apply (PCts_ext G).
        -- rewrite /G'.
           intros.
           case_bool_decide; first done.
           unfold Ioo, Rmax, Rmin in *. repeat case_match; lra.
        -- eapply (PCts_subset _ L _ (Rmax x y)).
           ++ unfold Rmin, Rmax in *. repeat case_match; lra.
           ++ unfold Rmin, Rmax in *. repeat case_match; lra.
           ++ apply H2. unfold Rmin, Rmax in *. repeat case_match; lra.
      * apply (PCts_ext (λ _, 0)).
        -- rewrite /G'.
           intros.
           case_bool_decide; last done.
           unfold Ioo, Rmax, Rmin in *. repeat case_match; lra.
        -- apply IPCts_PCts. apply IPCts_cts.
           intros. apply Continuity.continuous_const.
  - intros. rewrite /G'/F'. case_bool_decide; naive_solver.
  -
  apply (ex_RInt_gen_ext_eq_Ioi (f:=F)); last done.
  intros. rewrite /F'. by rewrite bool_decide_eq_true_2.
Qed.

(** Scalar change of variables for improper integrals

Proof plan for ex_RInt_gen_scal_change_of_var:

Goal: Show that if ∫[0,∞) F exists, then ∫[0,∞) F(a·x) exists for a > 0.

Main Strategy: Use substitution u = a·x to relate the two integrals.

Concrete approach using available Coquelicot techniques:

Step 1: State and admit finite change of variables lemma
  Need: ∫[0,b] F(a·x) dx = (1/a) · ∫[0,a·b] F(u) du

  Observation: No built-in change of variables in Coquelicot or this codebase
  Action: State as auxiliary admitted lemma (can prove later from is_RInt primitives)

  Potential techniques for future proof:
    - is_RInt_derive (fundamental theorem, used in exp.v:518)
    - RInt_Derive (inverse direction)
    - ex_RInt_comp_cts axiom (axioms.v:13) for composition

Step 2: Show finite integrals exist
  Prove: ∀ b, 0 < b → ex_RInt (λ x, F (a * x)) 0 b
  Approach: Use admitted change of variables + hypothesis ex_RInt F 0 (a*b)
  Could potentially use ex_RInt_scal (integrals.v:37) if needed

Step 3: Establish the limit
  Show: filterlimi (λ b, is_RInt (λ x, F (a*x)) 0 b) (Rbar_locally Rbar.p_infty)
                   (locally ((1/a) * L))
  where L is the limit of ∫[0,b] F as b → ∞

  Technique: Use filterlim composition (see exp.v:587, is_lim_exp_neg_infty)
  Key: As b → ∞:
    - ∫[0,b] F(a·x) dx = (1/a)·∫[0,a·b] F(u) du (by Step 1)
    - a·b → ∞ since a > 0 (need filterlim for λ b, a*b)
    - ∫[0,a·b] F → L (by hypothesis)
    - Compose limits: (1/a)·∫[0,a·b] F → (1/a)·L
  Use RInt_scal (integrals.v:18) for pulling out scalar (1/a)

Step 4: Apply RInt_gen_ex_Ici
  Use RInt_gen_ex_Ici (improper.v:122) to construct ex_RInt_gen
  Inputs:
    - Existence proof from Step 3: exists L, filterlimi ... (locally L)
    - Finite integrability from Step 2: ∀ b, ex_RInt (λ x, F (a*x)) 0 b
*)

(** Auxiliary lemmas: Finite change of variables for scalar transformations
    These should be provable from is_RInt primitives, but we admit them for now. *)

Lemma ex_RInt_scal_cov {F : R → R} {a b : R} :
  0 < a →
  0 < b →
  ex_RInt F 0 (a * b) →
  ex_RInt (λ x, F (a * x)) 0 b.
Proof.
  intros Ha Hb HexF.
  replace (λ x : R, F (a * x)) with (λ y : R, scal (/ a) (scal a (F (a * y + 0)))).
  2 : {
    funext.
    intros x.
    rewrite /scal/=/mult/=.
    field_simplify; try lra.
    f_equal; lra.
  }
  apply (ex_RInt_scal (λ y, scal a (F (a * y + 0))) 0 b (/a)).
  apply (ex_RInt_comp_lin F a 0 0 b).
  replace (a * 0 + 0) with 0 by lra.
  replace (a * b + 0) with (a * b) by lra.
  done.
Qed.

Lemma RInt_scal_cov {F : R → R} {a b : R} :
  0 < a →
  0 < b →
  ex_RInt F 0 (a * b) →
  RInt (λ x, F (a * x)) 0 b = / a * RInt F 0 (a * b).
Proof.
  intros Ha Hb HexF.
  rewrite (RInt_ext _ (λ x, scal (/a) (scal a (F (a * x + 0))))).
  2: {
    intros x Hx.
    rewrite /scal/=/mult/=.
    field_simplify; try lra.
    f_equal; lra.
  }
  rewrite RInt_scal.
  2: {
    apply (ex_RInt_comp_lin F a 0 0 b).
    replace (a * 0 + 0) with 0 by lra.
    replace (a * b + 0) with (a * b) by lra.
    done.
  }
  rewrite (RInt_comp_lin F a 0 0 b).
  2: {
    replace (a * 0 + 0) with 0 by lra.
    replace (a * b + 0) with (a * b) by lra.
    done.
  }
  replace (a * 0 + 0) with 0 by lra.
  replace (a * b + 0) with (a * b) by lra.
  rewrite /scal/=/mult/=. done.
Qed.

Lemma ex_RInt_gen_scal_change_of_var {F : R → R} {a : R} :
  0 < a →
  (∀ b, 0 < b → ex_RInt F 0 b) →
  ex_RInt_gen F (at_point 0) (Rbar_locally Rbar.p_infty) →
  ex_RInt_gen (λ x, F (a * x)) (at_point 0) (Rbar_locally Rbar.p_infty).
Proof.
  intros Ha HexF HexFgen.
  have Hex_finite : ∀ b, 0 < b → ex_RInt (λ x, F (a * x)) 0 b.
  { intros b Hb.
    apply ex_RInt_scal_cov; try done.
    apply HexF.
    apply Rmult_lt_0_compat; done.
  }
  apply RInt_gen_ex_Ici'; last done.
  destruct HexFgen as [LF HisRIntF].
  exists (/ a * LF).
  rewrite /filterlimi/=/filter_le/=/filtermapi/=.
  intros P HP.
  rewrite /locally in HP. destruct HP as [eps HP].
  have Heps' : 0 < eps * Rabs a.
  { apply Rmult_lt_0_compat; [apply cond_pos | apply Rabs_pos_lt; lra]. }
  rewrite /is_RInt_gen in HisRIntF.
  unfold filterlimi, filter_le, filtermapi in HisRIntF. simpl in HisRIntF.
  have HlimF_ball : ∃ M, ∀ b, M < b → ∃ y, is_RInt F 0 b y ∧ ball LF (mkposreal (eps * Rabs a) Heps') y.
  { have HisRIntF' := HisRIntF (ball LF (mkposreal (eps * Rabs a) Heps')).
    have HballLocal : locally LF (ball LF (mkposreal (eps * Rabs a) Heps')).
    { exists (mkposreal (eps * Rabs a) Heps'). simpl. intros y Hy. apply Hy. }
    specialize (HisRIntF' HballLocal).
    destruct HisRIntF' as [P1 P2 HP1 HP2 HP3].
    rewrite /at_point in HP1. simpl in HP1.
    rewrite /Rbar_locally in HP2. simpl in HP2. destruct HP2 as [M HP2].
    exists M. intros b Hb.
    specialize (HP3 0 b HP1 (HP2 b Hb)).
    simpl in HP3. apply HP3. }
  destruct HlimF_ball as [M HlimF_ball].
  (* Pick witness Rmax 1 (M / a) to ensure b > 0 *)
  exists (Rmax 1 (M / a)).
  intros b Hb.
  (* Prove b > 0 *)
  have Hb_pos : 0 < b.
  { apply Rlt_le_trans with (r2 := 1).
    { lra. }
    { apply Rle_trans with (r2 := Rmax 1 (M / a)); [apply Rmax_l | lra]. } }
  (* Prove M < a * b *)
  have Hab : M < a * b.
  { apply Rmult_lt_reg_r with (r := / a); [apply Rinv_0_lt_compat; lra|].
    field_simplify.
    { rewrite Rmax_Rlt in Hb; apply Hb. }
    { lra. }
    { lra. }
  }
  specialize (HlimF_ball (a * b) Hab).
  destruct HlimF_ball as [yF [HisRIntF_ab HballF]].
  (* We need RInt F 0 (a*b), which equals yF by uniqueness *)
  have HexF_ab : ex_RInt F 0 (a * b).
  { exists yF. done. }
  exists (/ a * RInt F 0 (a * b)).
  split.
  - (* is_RInt (λ x, F (a*x)) 0 b (/ a * RInt F 0 (a*b)) *)
    rewrite -RInt_scal_cov; try lra.
    { apply @RInt_correct.
      apply Hex_finite.
      done.
    }
    { exists yF; done. }
  - (* P (/ a * RInt F 0 (a*b)) *)
    apply HP.
    rewrite /ball/=/AbsRing_ball/=/abs/=/minus/plus/opp/=.
    replace (/ a * RInt F 0 (a * b) + - (/ a * LF)) with (/ a * (RInt F 0 (a * b) + - LF)) by lra.
    rewrite Rabs_mult.
    rewrite /ball/=/AbsRing_ball/=/abs/=/minus/plus/opp/= in HballF.
    have Ha_pos : 0 < Rabs a by (apply Rabs_pos_lt; lra).
    rewrite Rabs_inv.
    apply Rmult_lt_reg_r with (r := Rabs a); [done|].
    rewrite Rmult_assoc.
    rewrite Rmult_comm.
    rewrite Rmult_assoc.
    rewrite Rinv_r; [|apply Rgt_not_eq; done].
    rewrite Rmult_1_r.
    eapply Rle_lt_trans; [|exact HballF].
    right.
    do 2 f_equal.
    by apply is_RInt_unique.
Qed.

Lemma RInt_gen_scal_change_of_var {F : R → R} {a : R} :
  0 < a →
  (∀ b, 0 < b → ex_RInt F 0 b) →
  (∀ b, 0 < b → ex_RInt (λ x, F (a * x)) 0 b) →
  ex_RInt_gen F (at_point 0) (Rbar_locally Rbar.p_infty) →
  RInt_gen (λ x, F (a * x)) (at_point 0) (Rbar_locally Rbar.p_infty) =
    / a * RInt_gen F (at_point 0) (Rbar_locally Rbar.p_infty).
Proof.
  intros Ha HexF HexFscal HexFgen.
  apply RInt_gen_Ici_strong.
  - rewrite /filterlimi/=/filter_le/=/filtermapi/=.
    intros P HP.
    rewrite /locally in HP. destruct HP as [eps HP].
    have Heps' : 0 < eps * Rabs a.
    { apply Rmult_lt_0_compat; [apply cond_pos | apply Rabs_pos_lt; lra]. }
    rewrite /is_RInt_gen in HexFgen.
    destruct HexFgen as [LF HisRIntF].
    rewrite /is_RInt_gen in HisRIntF.
    unfold filterlimi, filter_le, filtermapi in HisRIntF. simpl in HisRIntF.
    have HlimF_ball : ∃ M, ∀ b, M < b → ∃ y, is_RInt F 0 b y ∧ ball LF (mkposreal (eps * Rabs a) Heps') y.
    { have HisRIntF' := HisRIntF (ball LF (mkposreal (eps * Rabs a) Heps')).
      have HballLocal : locally LF (ball LF (mkposreal (eps * Rabs a) Heps')).
      { exists (mkposreal (eps * Rabs a) Heps'). simpl. intros y Hy. apply Hy. }
      specialize (HisRIntF' HballLocal).
      destruct HisRIntF' as [P1 P2 HP1 HP2 HP3].
      rewrite /at_point in HP1. simpl in HP1.
      rewrite /Rbar_locally in HP2. simpl in HP2. destruct HP2 as [M HP2].
      exists M. intros b Hb.
      specialize (HP3 0 b HP1 (HP2 b Hb)).
      simpl in HP3. apply HP3. }
    destruct HlimF_ball as [M HlimF_ball].
    exists (Rmax 1 (M / a)).
    intros b Hb.
    have Hb_pos : 0 < b.
    { apply Rlt_le_trans with (r2 := 1).
      { lra. }
      { apply Rle_trans with (r2 := Rmax 1 (M / a)); [apply Rmax_l | lra]. } }
    have Hab : M < a * b.
    { apply Rmult_lt_reg_r with (r := / a); [apply Rinv_0_lt_compat; lra|].
      field_simplify.
      { rewrite Rmax_Rlt in Hb; apply Hb. }
      { lra. }
      { lra. } }
    specialize (HlimF_ball (a * b) Hab).
    destruct HlimF_ball as [yF [HisRIntF_ab HballF]].
    have HexF_ab : ex_RInt F 0 (a * b).
    { exists yF. done. }
    exists (/ a * RInt F 0 (a * b)).
    split.
    { rewrite -RInt_scal_cov; try lra.
      { apply @RInt_correct. apply HexFscal. done. }
      { exists yF; done. } }
    { apply HP.
      rewrite /ball/=/AbsRing_ball/=/abs/=/minus/plus/opp/=.
      replace (/ a * RInt F 0 (a * b) + - (/ a * RInt_gen F (at_point 0) (Rbar_locally Rbar.p_infty)))
        with (/ a * (RInt F 0 (a * b) + - RInt_gen F (at_point 0) (Rbar_locally Rbar.p_infty))) by lra.
      rewrite Rabs_mult.
      rewrite Rabs_inv.
      have Ha_pos : 0 < Rabs a by (apply Rabs_pos_lt; lra).
      apply Rmult_lt_reg_r with (r := Rabs a); [done|].
      rewrite Rmult_assoc.
      rewrite (Rmult_comm (Rabs _) (Rabs a)).
      rewrite -Rmult_assoc.
      rewrite Rinv_l; [|apply Rgt_not_eq; done].
      rewrite Rmult_1_l.
      eapply Rle_lt_trans; [|exact HballF].
      rewrite /abs/=/minus/plus/opp/=.
      right.
      do 2 f_equal.
      { by apply is_RInt_unique. }
      { f_equal.
        symmetry.
        have Hcorr : is_RInt_gen F (at_point 0) (Rbar_locally Rbar.p_infty)
                       (RInt_gen F (at_point 0) (Rbar_locally Rbar.p_infty)).
        { eapply (@RInt_gen_correct R_CompleteNormedModule).
          { apply Proper_StrongProper, at_point_filter. }
          { apply Proper_StrongProper, Rbar_locally_filter. }
          exists LF. rewrite /is_RInt_gen. done. }
        rewrite /is_RInt_gen in HisRIntF.
        have HisRIntF_LF : is_RInt_gen F (at_point 0) (Rbar_locally Rbar.p_infty) LF
          by (rewrite /is_RInt_gen; done).
        apply eq_sym, (@is_RInt_gen_unique R_CompleteNormedModule); eauto.
        { apply Proper_StrongProper, at_point_filter. }
        { apply Proper_StrongProper, Rbar_locally_filter. } } }
  - intros b Hb. apply HexFscal. done.
Qed.

(** ** Change of variables: negative reflection [0,∞) ↔ (-∞,0] *)

(** Finite versions *)
Lemma ex_RInt_neg {F : R → R} {b : R} :
  0 < b →
  ex_RInt F (- b) 0 →
  ex_RInt (λ x, F (- x)) 0 b.
Proof.
  intros ??.
  replace (λ x : R, F (- x)) with (λ x : R, (-1) * ((-1) * F (- x))).
  2: { funexti.  OK. }
  apply ex_RInt_Rmult.
  eapply ex_RInt_ext.
  2: {
    apply ex_RInt_swap.
    apply ex_RInt_comp_opp.
    rewrite Ropp_0.
    apply H0.
  }
  intros ??.
  rewrite //= /opp//=. lra.
Qed.

Lemma ex_RInt_neg_rev {F : R → R} {b : R} :
  0 < b →
  ex_RInt F 0 b →
  ex_RInt (λ x, F (- x)) (- b) 0.
Proof.
Admitted.

Lemma RInt_neg_rev {F : R → R} {b : R} :
  0 < b →
  ex_RInt F 0 b →
  RInt (λ x, F (- x)) (- b) 0 = RInt F 0 b.
Proof.
Admitted.

Lemma RInt_neg {F : R → R} {b : R} :
  0 < b →
  ex_RInt F (- b) 0 →
  RInt (λ x, F (- x)) 0 b = RInt F (- b) 0.
Proof.
  intros ??.
  symmetry.
  rewrite -opp_RInt_swap.
  2: { by apply ex_RInt_swap. }
  have X := RInt_comp_lin (λ x : R, F x) (-1) 0 0 b.
  rewrite Rmult_0_r Rplus_0_r Rplus_0_r in X.
  replace (-1 * b) with (- b) in X; OK.
  rewrite -X.
  2: { by apply ex_RInt_swap. }
  rewrite /opp//=.
  rewrite /scal//=/mult//=.
  rewrite -RInt_Rmult.
  2: {
    eapply ex_RInt_ext.
    2: { eapply ex_RInt_neg; [done|]. apply H0. }
    intros ??.
    rewrite //=.
    f_equal; OK.
  }
  have HH : ∀ (r : R), Ropp r = (-1) * r by OK.
  rewrite HH.
  rewrite -Rmult_assoc.
  replace (-1 * -1) with 1 by OK.
  rewrite Rmult_1_l.
  f_equal.
  funexti; f_equal; OK.
Qed.

(** Infinite versions *)
Lemma ex_RInt_gen_neg_change_of_var {F : R → R} :
  (∀ b, 0 < b → ex_RInt F (- b) 0) →
  ex_RInt_gen F (Rbar_locally Rbar.m_infty) (at_point 0) →
  ex_RInt_gen (λ x, F (- x)) (at_point 0) (Rbar_locally Rbar.p_infty).
Proof.
  intros HexF HexFgen.
  have Hex_finite : ∀ b, 0 < b → ex_RInt (λ x, F (- x)) 0 b.
  { intros b Hb. apply ex_RInt_neg; [done | apply HexF; done]. }
  apply RInt_gen_ex_Ici'; last done.
  destruct HexFgen as [LF HisRIntF].
  exists LF.
  rewrite /is_RInt_gen in HisRIntF.
  rewrite /filterlimi/=/filter_le/=/filtermapi/=.
  intros P HP.
  unfold filterlimi, filter_le, filtermapi in HisRIntF. simpl in HisRIntF.
  have HisRIntF' := HisRIntF P HP.
  destruct HisRIntF' as [P1 P2 HP1 HP2 HP3].
  rewrite /Rbar_locally in HP1. simpl in HP1. destruct HP1 as [M HP1].
  rewrite /at_point in HP2. simpl in HP2.
  exists (Rmax 1 (- M)).
  intros b Hb.
  have Hb_pos : 0 < b.
  { apply Rlt_le_trans with (r2 := 1).
    { lra. }
    { apply Rle_trans with (r2 := Rmax 1 (- M)); [apply Rmax_l | lra]. } }
  have Hneg_M : - b < M.
  { rewrite Rmax_Rlt in Hb. destruct Hb as [_ Hb]. lra. }
  specialize (HP3 (- b) 0 (HP1 (- b) Hneg_M) HP2).
  simpl in HP3.
  destruct HP3 as [yF [HisRIntF_nb HpyF]].
  have HexF_nb : ex_RInt F (- b) 0.
  { exists yF. done. }
  exists (RInt F (- b) 0).
  split.
  - rewrite -RInt_neg; [|done|done].
    apply @RInt_correct. apply Hex_finite. done.
  - rewrite (is_RInt_unique _ _ _ _ HisRIntF_nb). done.
Qed.

Lemma RInt_gen_neg_change_of_var {F : R → R} :
  (∀ b, 0 < b → ex_RInt F (- b) 0) →
  (∀ b, 0 < b → ex_RInt (λ x, F (- x)) 0 b) →
  ex_RInt_gen F (Rbar_locally Rbar.m_infty) (at_point 0) →
  RInt_gen (λ x, F (- x)) (at_point 0) (Rbar_locally Rbar.p_infty) =
    RInt_gen F (Rbar_locally Rbar.m_infty) (at_point 0).
Proof.
  intros HexF HexFneg HexFgen.
  apply RInt_gen_Ici_strong.
  - rewrite /filterlimi/=/filter_le/=/filtermapi/=.
    intros P HP.
    destruct HexFgen as [LF HisRIntF].
    have HLF_eq : RInt_gen F (Rbar_locally Rbar.m_infty) (at_point 0) = LF.
    { apply (@is_RInt_gen_unique R_CompleteNormedModule).
      { apply Proper_StrongProper, Rbar_locally_filter. }
      { apply Proper_StrongProper, at_point_filter. }
      done. }
    rewrite HLF_eq in HP.
    rewrite /is_RInt_gen in HisRIntF.
    unfold filterlimi, filter_le, filtermapi in HisRIntF. simpl in HisRIntF.
    have HisRIntF' := HisRIntF P HP.
    destruct HisRIntF' as [P1 P2 HP1 HP2 HP3].
    rewrite /Rbar_locally in HP1. simpl in HP1. destruct HP1 as [M HP1].
    rewrite /at_point in HP2. simpl in HP2.
    exists (Rmax 1 (- M)).
    intros b Hb.
    have Hb_pos : 0 < b.
    { apply Rlt_le_trans with (r2 := 1).
      { lra. }
      { apply Rle_trans with (r2 := Rmax 1 (- M)); [apply Rmax_l | lra]. } }
    have Hneg_M : - b < M.
    { rewrite Rmax_Rlt in Hb. destruct Hb as [_ Hb]. lra. }
    specialize (HP3 (- b) 0 (HP1 (- b) Hneg_M) HP2).
    simpl in HP3.
    destruct HP3 as [yF [HisRIntF_nb HpyF]].
    have HexF_nb : ex_RInt F (- b) 0.
    { exists yF. done. }
    exists (RInt F (- b) 0).
    split.
    { rewrite -RInt_neg; [|done|done].
      apply @RInt_correct. apply HexFneg. done. }
    { rewrite (is_RInt_unique _ _ _ _ HisRIntF_nb). done. }
  - intros b Hb. apply HexFneg. done.
Qed.

(** Reverse direction: from [0, ∞) to (-∞, 0] *)
Lemma ex_RInt_gen_neg_change_of_var_rev {F : R → R} :
  (∀ b, 0 < b → ex_RInt F 0 b) →
  ex_RInt_gen F (at_point 0) (Rbar_locally Rbar.p_infty) →
  ex_RInt_gen (λ x, F (- x)) (Rbar_locally Rbar.m_infty) (at_point 0).
Proof.
  intros HexF HexFgen.
  have Hex_finite : ∀ b, 0 < b → ex_RInt (λ x, F (- x)) (- b) 0.
  { intros b Hb. apply ex_RInt_neg_rev; [done | apply HexF; done]. }
  rewrite /ex_RInt_gen /is_RInt_gen.
  destruct HexFgen as [LF HisRIntF].
  exists LF.
  rewrite /filterlimi/=/filter_le/=/filtermapi/=.
  intros P HP.
  rewrite /is_RInt_gen in HisRIntF.
  unfold filterlimi, filter_le, filtermapi in HisRIntF. simpl in HisRIntF.
  have HisRIntF' := HisRIntF P HP.
  destruct HisRIntF' as [P1 P2 HP1 HP2 HP3].
  rewrite /at_point in HP1. simpl in HP1.
  rewrite /Rbar_locally in HP2. simpl in HP2. destruct HP2 as [M HP2].
  eapply (Filter_prod _ _ _ (fun a => a < Rmin (- M) (- 1)) (fun b => b = 0)).
  { rewrite /Rbar_locally/=. exists (Rmin (- M) (- 1)). intros x Hx. done. }
  { rewrite /at_point//=. }
  intros a b Ha Hb. simpl. subst b.
  have Ha_neg : M < - a.
  { have : a < - M by (apply Rlt_le_trans with (r2 := Rmin (- M) (- 1)); [apply Ha | apply Rmin_l]).
    lra. }
  have Ha_pos : 0 < - a.
  { have : a < - 1 by (apply Rlt_le_trans with (r2 := Rmin (- M) (- 1)); [apply Ha | apply Rmin_r]).
    lra. }
  specialize (HP3 0 (- a) HP1 (HP2 (- a) Ha_neg)).
  simpl in HP3.
  destruct HP3 as [yF [HisRIntF_na HpyF]].
  have HexF_na : ex_RInt F 0 (- a).
  { exists yF. done. }
  exists (RInt F 0 (- a)).
  split.
  - rewrite -(RInt_neg_rev Ha_pos HexF_na).
    rewrite Ropp_involutive.
    apply @RInt_correct.
    replace a with (- (- a)) by lra.
    apply Hex_finite.
    lra.
  - rewrite (is_RInt_unique _ _ _ _ HisRIntF_na). done.
Qed.
