From Stdlib Require Import Reals Psatz.
From iris.algebra Require Import ofe.
From Stdlib Require Export Reals.
From clutch.common Require Import con_language.
From clutch.prob Require Export distribution mdp couplings couplings_app.
From Coquelicot Require Import Rbar Lub Lim_seq Series.


From clutch.foxtrot Require Import oscheduler.
From clutch.con_prob_lang Require Import lang.

Local Open Scope R.

Section point.

Class Pointed (A : Type) := {
  point : A;
  penc : A → A;
  pdec : A → A;
  penc_dec : ∀ a, pdec $ penc a = a;
  penc_not_point : ∀ a, penc a ≠ point;
}.

End point.

Global Instance CountableInfPointed `{Countable A} `{Infinite A}: 
  Pointed A.
Admitted.

Section point.

Class APointed (A : Type) (B : Type) := {
  apoint1 : A;
  apoint2 : A;
  apoint1_not_point2 : apoint1 ≠ apoint2;
  apenc : B * A → A;
  apdec : A → B * A;
  apenc_dec : ∀ b a, apdec $ apenc (b, a) = (b, a);
  apenc_not_point1 : ∀ b a, apenc (b, a) ≠ apoint1;
  apenc_not_point2 : ∀ b a, apenc (b, a) ≠ apoint2;
}.

End point.

Global Instance CountableInfAPointed `{Countable A} `{Countable B} `{Infinite A} `{Inhabited B}: 
  APointed A B.
Proof.
Admitted.

Lemma ex_seriesC_minus `{Countable A} (f g : A → R) :
  ex_seriesC f →
  ex_seriesC g →
  ex_seriesC (λ x, f x - g x).
Proof.
  intros.
  apply ex_seriesC_plus; first done.
  apply (ex_seriesC_ext (λ x, (- 1) * g x)); first by real_solver.
  by apply ex_seriesC_scal_l.
Qed.

Lemma lub_Rbar_nbhd (r : R) (P : R → Prop) :
  is_lub_Rbar P r →
  ∀ ε, 0 < ε → 
  ∃ x, P x ∧ r <= x + ε.
Proof.
  intros.
  destruct (decide (∃ x : R, P x ∧ r <= x + ε)); first auto.
  specialize (not_exists_forall_not _ _ n).
  setoid_rewrite not_and_l => Hx.
  pose proof (λ a, Classical_Prop.or_to_imply _ _ $ Hx a).
  assert (is_lub_Rbar P (r - ε)). {
    econstructor.
    - econstructor. pose (H1 _ H2). lra.
    - intros. trans r; [by simpl; lra | by apply H].
  }
  assert (r = r - ε); last lra.
  apply Rbar_finite_eq.
  by apply is_lub_Rbar_unique in H, H2 as <-.
Qed.

Lemma reducible_to_head (e : expr) σ:
  reducible e σ →
  ∃ K e', e = fill K e' ∧ head_reducible e' σ.
Proof.
  rewrite /reducible /= /con_ectx_language.prim_step //=.
  intros [??].
  destruct (decomp e) eqn: Hde; simpl in *.
  rewrite Hde in H.
  apply dmap_pos in H as [((?&?)&?)[??]].
  exists l, e0. simpl in *.
  apply decomp_fill in Hde as <-.
  split; eauto; by eexists.
Qed.

Lemma fin_in_enum n (i : fin n) :
  i ∈ fin_enum n.
Proof.
  induction n; first by inversion i.
  apply (Fin.caseS' i); first by apply elem_of_list_here.
  intros. simpl.
  apply elem_of_list_further.
  eapply elem_of_list_fmap_1_alt; last done.
  by apply IHn.
Qed.

Lemma step_fin : ∀ (e : expr) σ, ∃ (l : list _), ∀ ρ, 0 < prim_step e σ ρ → ρ ∈ l.
Proof.
  intros.
  destruct (decide (con_language.reducible e σ));
  last by exists [] => ρ H; rewrite not_reducible in n; specialize (n ρ); simpl in *; rewrite n in H; lra.
  apply reducible_to_head in r as (K&e0&Hfill&(((e0' & σ') & efs)&Hhs)).
  pose proof Hhs as Hhs'.
  rewrite head_step_support_equiv_rel in Hhs'. 
  inversion Hhs'; simplify_eq.
  1-16, 18-19, 22-26: eexists [_]; setoid_rewrite elem_of_list_singleton; 
    intros [[? s' ] efs] Hx;
    eapply Rlt_gt, fill_step_inv in Hx as [e' [-> Hstep]]; [| apply con_ectx_lang_ctx | done];
    setoid_rewrite head_prim_step_eq in Hstep; [|by eexists];
    rewrite head_step_support_equiv_rel in Hstep; inversion Hstep; subst e' s' efs; simplify_eq; try done. 
  2-4: exists ( (λ n : fin _, (fill K $ Val $ LitV $ LitInt n, σ', [])) <$> (fin_enum (S (Z.to_nat z))));
    intros [[? s' ] efs] Hx;
    eapply Rlt_gt, fill_step_inv in Hx as [e' [-> Hstep]]; [| apply con_ectx_lang_ctx | done];
    setoid_rewrite head_prim_step_eq in Hstep; [|by eexists];
    rewrite head_step_support_equiv_rel in Hstep; inversion Hstep; subst e' s' efs; simplify_eq.
  - by rewrite H0 in H7.
  - eapply elem_of_list_fmap_1_alt; last done. 
    apply fin_in_enum.
  - by rewrite H0 in H7.
  - eapply elem_of_list_fmap_1_alt; last done. 
    apply fin_in_enum.
  - eapply elem_of_list_fmap_1_alt; last done. 
    apply fin_in_enum.
Qed.

Lemma osch_pexec_mass_mono `{Countable sch_int_state} (Ξ : oscheduler sch_int_state) n ρ :
  SeriesC (osch_pexec Ξ (S n) ρ) <= SeriesC (osch_pexec Ξ n ρ).
Proof.
  rewrite osch_pexec_Sn_r dbind_mass.
  apply SeriesC_le.
  - intro a. split.
    + apply Rmult_le_pos; [apply pmf_pos | apply SeriesC_ge_0'; intro; apply pmf_pos].
    + trans (osch_pexec Ξ n ρ a * 1).
      * apply Rmult_le_compat_l; [apply pmf_pos | apply pmf_SeriesC].
      * lra.
  - apply pmf_ex_seriesC.
Qed.

Lemma osch_pexec_mass_mono' `{Countable sch_int_state} (Ξ : oscheduler sch_int_state) n m ρ :
  m ≤ n →
  SeriesC (osch_pexec Ξ n ρ) <= SeriesC (osch_pexec Ξ m ρ).
Proof.
  intro Hle.
  induction Hle as [| k _ IH].
  - lra.
  - etrans; [apply osch_pexec_mass_mono | exact IH].
Qed.

Record full_scheduler (sch_state : Type) `{Countable sch_state} := {
  sch :> oscheduler sch_state ;
  full_distr : ∀ x μ, sch x = Some μ → SeriesC μ = 1
}.

Section err_lb_con.
Context `{Countable sch_int_state} `{Hinf: Infinite sch_int_state} .
Implicit Types (Ξ : full_scheduler sch_int_state) (ζ : sch_int_state).

Program Definition tfsch (i : nat) : full_scheduler sch_int_state := {| sch := {| oscheduler_f := λ x, Some $ dret (point, i%nat) |}; |}.
Next Obligation.
  intros x μ H0 Heq. simpl in Heq. injection Heq as <-. apply dret_mass.
Qed.

Definition err_lb_con (φ : val → Prop) 
  (ρ : cfg) : R := Rbar_lub (λ r, 
    ∃ Ξ ζ m, r = prob (osch_exec_val Ξ m (ζ, ρ)) (λ x, negb $ bool_decide $ φ x) + 1 - SeriesC (osch_pexec Ξ m (ζ, ρ))).

Local Lemma err_lb_con_elem_bound φ ρ Ξ ζ m :
  0 <= prob (osch_exec_val Ξ m (ζ, ρ)) (λ x, negb $ bool_decide $ φ x) + 1 -
      SeriesC (osch_pexec Ξ m (ζ, ρ)) <= 1.
Proof.
  have Hprob_nn := prob_ge_0 (osch_exec_val Ξ m (ζ, ρ)) (λ x, negb $ bool_decide $ φ x).
  have Hpexec_le1 := pmf_SeriesC (osch_pexec Ξ m (ζ, ρ)).
  split; [rewrite -Rplus_minus_assoc; apply Rplus_le_le_0_compat; [real_solver| by apply Rle_0_le_minus]|].
  have Hle : prob (osch_exec_val Ξ m (ζ, ρ)) (λ x, negb $ bool_decide $ φ x) <=
             SeriesC (osch_pexec Ξ m (ζ, ρ)); last lra.
  etransitivity.
  - apply SeriesC_le; last apply pmf_ex_seriesC.
    intro a. real_solver.
  - rewrite /osch_exec_val osch_exec_pexec_relate dbind_mass.
    apply SeriesC_le; auto.
    intros [??]. simpl. destruct (con_lang_mdp_to_final con_prob_lang m0);
    last by rewrite dzero_mass Rmult_0_r; real_solver.
    rewrite dret_mass Rmult_1_r; split; first done.
    rewrite dbind_unfold_pmf /=.
    erewrite SeriesC_ext; first erewrite SeriesC_singleton. 
    2 : {
      intros. simpl. 
      case_bool_decide; first by rewrite H0.
      destruct (Ξ n); [|rewrite dret_0 //=]; real_solver.
    }
    real_solver.
Qed.

Local Lemma err_lb_con_lub_lb φ ρ :
  Rbar_le 0 (Rbar_lub (λ r,
    ∃ Ξ ζ m, r = prob (osch_exec_val Ξ m (ζ, ρ)) (λ x, negb $ bool_decide $ φ x) + 1 -
               SeriesC (osch_pexec Ξ m (ζ, ρ)))).
Proof using Hinf.
  destruct (proj2_sig (Rbar_ex_lub (λ r, ∃ Ξ ζ m,
    r = prob (osch_exec_val Ξ m (ζ, ρ)) (λ x, negb $ bool_decide $ φ x) + 1 -
        SeriesC (osch_pexec Ξ m (ζ, ρ))))) as [Hub _].
  eapply (Rbar_lb_le_ub _ (Rbar.Finite 0) (Rbar_lub _)); last exact Hub.
  - exists (Rbar.Finite (prob (osch_exec_val (osch_state := sch_int_state) (tfsch 0) 0 (point, ρ))
                        (λ x, negb $ bool_decide $ φ x))).
    exists (tfsch 0). exists point. exists 0%nat.
    rewrite osch_pexec_O dret_mass. f_equal. lra.
  - intros x [Ξ [ζ [m ->]]]. simpl.
    exact (proj1 (err_lb_con_elem_bound φ ρ Ξ ζ m)). 
Qed.

Local Lemma err_lb_con_lub_ub φ ρ :
  Rbar_le (Rbar_lub (λ r,
    ∃ Ξ ζ m, r = prob (osch_exec_val Ξ m (ζ, ρ)) (λ x, negb $ bool_decide $ φ x) + 1 -
               SeriesC (osch_pexec Ξ m (ζ, ρ)))) 1.
Proof.
  destruct (proj2_sig (Rbar_ex_lub (λ r, ∃ Ξ ζ m,
    r = prob (osch_exec_val Ξ m (ζ, ρ)) (λ x, negb $ bool_decide $ φ x) + 1 -
        SeriesC (osch_pexec Ξ m (ζ, ρ))))) as [_ Hleast].
  apply Hleast.
  intros x [Ξ [ζ [m ->]]]. simpl.
  exact (proj2 (err_lb_con_elem_bound φ ρ Ξ ζ m)).
Qed.


Lemma err_lb_con_finite φ ρ :
  is_finite (Rbar_lub (λ r,
    ∃ Ξ ζ m, r = prob (osch_exec_val Ξ m (ζ, ρ)) (λ x, negb $ bool_decide $ φ x) + 1 - SeriesC (osch_pexec Ξ m (ζ, ρ)))).
Proof using Hinf.
  apply (Rbar_le_sandwich 0 1).
  - exact (err_lb_con_lub_lb φ ρ).
  - exact (err_lb_con_lub_ub φ ρ).
Qed.

Lemma err_lb_con_nn φ ρ : 0 <= err_lb_con φ ρ.
Proof using Hinf.
  rewrite /err_lb_con.
  apply rbar_le_finite.
  - 
    apply err_lb_con_finite.
  - exact (err_lb_con_lub_lb φ ρ).
Qed.

Lemma err_lb_con_bound φ ρ : err_lb_con φ ρ <= 1.
Proof using Hinf.
  rewrite /err_lb_con.
  apply finite_rbar_le.
  - apply err_lb_con_finite.
  - exact (err_lb_con_lub_ub φ ρ).
Qed.

Lemma err_lb_con_step φ m C σ e :
  C !! m = Some e →
  con_language.reducible e σ →
  Expval (prim_step e σ) (λ '(e', σ', efs), err_lb_con φ (<[m := e']> C ++ efs, σ')) <= err_lb_con φ (C, σ).
Proof using Hinf.
  intros HCm Hred.
  apply Rle_plus_epsilon => ε Hε.
  assert (∀ ρ, ∃ (x : full_scheduler sch_int_state * sch_int_state * nat),
    err_lb_con φ ρ <= prob (osch_exec_val x.1.1 x.2 (x.1.2, ρ)) (λ x, negb $ bool_decide $ φ x) + 1 - SeriesC (osch_pexec x.1.1 x.2 (x.1.2, ρ)) + ε) as H0. {
    intro.
    eapply lub_Rbar_nbhd in Hε.
    2 : {
      eapply (is_lub_Rbar_correct (λ x, ∃ _ _ _, x = _)).
      erewrite err_lb_con_finite.
      eapply (Rbar_is_lub_ext); last by eapply (proj2_sig (Rbar_ex_lub _)).
      split; intros.
      - destruct H0 as (Ξ & ζ & n & Hn). subst. split; [done | by do 3 eexists].
      - destruct H0 as (Hf & Ξ & n & ζ & Hn). do 3 eexists.
        rewrite -(rbar_finite_real_eq x) //=. by rewrite Hn.
    }
    simpl in *.
    destruct Hε as [?[(Ξ&n&ζ&?)]].
    exists (Ξ, ζ, n). subst. by apply H1.
  }
  apply Choice in H0 as f.
  (* Combined oscheduler:
     - at apoint1: choose thread m (returns Some (dret (apoint2, m)))
     - at apoint2: delegate to the chosen Ξ for the current ρ, encoded via apenc
     - at apenc(ρ0, ζ0): delegate to the chosen Ξ for ρ0 with internal state ζ0 *)
  pose (schf' := λ p : sch_int_state * cfg,
    let '(ζ, ρ) := p in
    if bool_decide (ζ = apoint1 (B := cfg)) then
      Some (dret (apoint2 (B := cfg), m))
    else if bool_decide (ζ = apoint2 (B := cfg)) then
      let '(Ξ', ζ', _) := (`f) ρ in
      match Ξ' (ζ', ρ) with
      | Some μ' => Some (dmap (λ ζ1j : sch_int_state * nat, (apenc (ρ, ζ1j.1), ζ1j.2)) μ')
      | None => None
      end
    else
      let '(ρ0, ζ0) := apdec (B := cfg) ζ in
      let '(Ξ', ζ', _) := (`f) ρ0 in
      match Ξ' (ζ0, ρ) with
      | Some μ' => Some (dmap (λ ζ1j : sch_int_state * nat, (apenc (ρ0, ζ1j.1), ζ1j.2)) μ')
      | None => None
      end).

  have Hschf' : ∀ a μ, schf' a = Some μ → SeriesC μ = 1. {
    intros [ζ ρ] μ.
    rewrite /schf' /=.
    case_bool_decide.
    - intros [= <-]. apply dret_mass.
    - case_bool_decide.
      + destruct ((`f) ρ) as [[Ξ_f ζ_f] n_f] eqn : Hfρ.
        destruct (Ξ_f (ζ_f, ρ)) as [μ'|] eqn : Hμ'; simpl; rewrite Hfρ Hμ'//=.
        intros [= <-]. rewrite dmap_mass. exact (full_distr _ Ξ_f (ζ_f, ρ) μ' Hμ').
      + destruct (apdec (B := cfg) ζ) as [ρ0 ζ0].
        destruct ((`f) ρ0) as [[Ξ_f ζ_f] n_f] eqn : Hfρ0.
        rewrite Hfρ0 /=.
        destruct (Ξ_f (ζ0, ρ)) as [μ'|] eqn : Hμ'; simpl.
        * intros [= <-]. rewrite dmap_mass. exact (full_distr _ Ξ_f (ζ0, ρ) μ' Hμ').
        * intros [=].
  }

  set Ξ' : full_scheduler sch_int_state :=
    {| sch := {| oscheduler_f := schf' |}; full_distr := Hschf' |}.

  (* osch_exec_val Ξ' n (apenc(ρ0, ζ), ρ) = osch_exec_val (f ρ0).1.1 n (ζ, ρ) *)
  assert (∀ n ρ ρ0 ζ, osch_exec_val Ξ' n (apenc (ρ0, ζ), ρ) = osch_exec_val ((`f) ρ0).1.1 n (ζ, ρ)) as Hexec_val1. {
    induction n; intros.
    - (* n = 0 *)
      rewrite /osch_exec_val.
      destruct ((`f) ρ0) as [[Ξ_ρ ζ_ρ] n_ρ] eqn : Hf0. simpl.
      destruct (Ξ_ρ (ζ, ρ)) as [μ'|] eqn : Hμ'; rewrite !Hf0 Hμ' /=.
      + have Hsome : is_Some ((Ξ' : oscheduler _) (apenc (ρ0, ζ), ρ)).
        { change (is_Some (schf' (apenc (ρ0, ζ), ρ))).
          rewrite /schf'.
          case_bool_decide.
          - by exfalso; apply (apenc_not_point1 ρ0 ζ).
          - case_bool_decide.
            + by exfalso; apply (apenc_not_point2 ρ0 ζ).
            + rewrite apenc_dec Hf0 Hμ'. done. }
        have Hsome_ρ : is_Some (Ξ_ρ (ζ, ρ)) by rewrite Hμ'.
        do 2 (case_bool_decide; auto); [by exfalso; eapply apenc_not_point2|].
        rewrite apenc_dec Hf0 Hμ' //=.         
      + have Hnone : (Ξ' : oscheduler _) (apenc (ρ0, ζ), ρ) = None.
        { change (schf' (apenc (ρ0, ζ), ρ) = None).
          rewrite /schf'.
          case_bool_decide.
          - by exfalso; apply (apenc_not_point1 ρ0 ζ).
          - case_bool_decide.
            + by exfalso; apply (apenc_not_point2 ρ0 ζ).
            + rewrite apenc_dec Hf0 Hμ'. done. }
        case_bool_decide; first by exfalso; eapply apenc_not_point1.
        case_bool_decide; first by exfalso; eapply apenc_not_point2.
        rewrite apenc_dec Hf0 Hμ' //= !dret_id_left. 
        f_equal.
    - rewrite !osch_exec_val_Sn /osch_step_or_none /osch_step /=.
      case_bool_decide; first by exfalso; eapply apenc_not_point1.
      case_bool_decide; first by exfalso; eapply apenc_not_point2.
      rewrite apenc_dec.
      destruct ((`f) ρ0) as [[Ξ_ρ ζ_ρ] n_ρ] eqn : Hf0.
      destruct (Ξ_ρ (ζ, ρ)) as [μ'|] eqn : Hμ'.
      + rewrite Hf0 Hμ' /= /dmap -!dbind_assoc'.
        apply dbind_ext_right => [[ζ1 j]].
        rewrite dret_id_left /= -!dbind_assoc'.
        apply dbind_ext_right => ρ''.
        rewrite !dret_id_left'. simpl.
        by rewrite IHn Hf0.
      + rewrite Hf0 Hμ' /= /dmap !dret_id_left. 
        rewrite /osch_exec_val in IHn.
        rewrite IHn Hf0 //=.
  }
  assert (∀ n ρ, osch_exec_val Ξ' n (apoint2 (B := cfg), ρ) = osch_exec_val ((`f) ρ).1.1 n (((`f) ρ).1.2, ρ)) as Hexec_val. {
    induction n; intros.
    - rewrite /osch_exec_val.
      destruct ((`f) ρ) as [[Ξ_ρ ζ_ρ] n_ρ] eqn : Hf0.
      destruct (Ξ_ρ (ζ_ρ, ρ)) as [μ'|] eqn : Hμ'.
      + rewrite Hf0 /= Hμ' /=.
        case_bool_decide; first by exfalso; eapply apoint1_not_point2.
        case_bool_decide; last done. 
        by rewrite Hf0 /= Hμ' /= dbind_dzero. 
      + rewrite Hf0 /= Hμ' /=.
        case_bool_decide; first by exfalso; eapply apoint1_not_point2.
        case_bool_decide; last done. 
        by rewrite Hf0 /= Hμ' /= !dret_id_left.
    - rewrite !osch_exec_val_Sn /osch_step_or_none /osch_step /=.
      case_bool_decide; first by exfalso; eapply apoint1_not_point2.
      case_bool_decide; last done.
      destruct ((`f) ρ) as [[Ξ_ρ ζ_ρ] n_ρ] eqn : Hf0.
      destruct (Ξ_ρ (ζ_ρ, ρ)) as [μ'|] eqn : Hμ';
      last by rewrite Hf0 Hμ' /= !dret_id_left' IHn Hf0 /=.
      rewrite Hf0 Hμ' /= /dmap -!dbind_assoc'.
      apply dbind_ext_right => [[ζ1 j]].
      rewrite dret_id_left /= -!dbind_assoc'.
      apply dbind_ext_right => ρ''.
      rewrite !dret_id_left'. simpl.
      by rewrite Hexec_val1 Hf0.
  }

  (* SeriesC (osch_pexec Ξ' n (apenc(ρ0, ζ), ρ)) = SeriesC (osch_pexec (f ρ0).1.1 n (ζ, ρ)) *)
  assert (∀ n ρ ρ0 ζ, SeriesC $ osch_pexec Ξ' n (apenc (ρ0, ζ), ρ) = SeriesC $ osch_pexec ((`f) ρ0).1.1 n (ζ, ρ)) as Hpexec1. {
    induction n; intros; first by rewrite !osch_pexec_O !dret_mass.
    rewrite !osch_pexec_Sn /osch_step_or_none /osch_step /=.
    (* rewrite /schf'. *)
    case_bool_decide; first by exfalso; eapply apenc_not_point1.
    case_bool_decide; first by exfalso; eapply apenc_not_point2.
    rewrite apenc_dec.
    destruct ((`f) ρ0) as [[Ξ_ρ ζ_ρ] n_ρ] eqn : Hf0. simpl.
    rewrite !Hf0 /=. 
    destruct (Ξ_ρ (ζ, ρ)) as [μ'|] eqn : Hμ'; rewrite Hμ' /=.
    2 : {
      pose proof (Expval_dret (A := sch_int_state * con_language.cfg con_prob_lang)) as He. 
      rewrite /Expval in He. by rewrite !dbind_mass !He IHn Hf0. 
    }
    rewrite /dmap -!dbind_assoc' /=. 
    rewrite !dbind_mass. 
    apply SeriesC_ext => [[ζ' i']]. 
    f_equal. 
    rewrite dret_id_left -!dbind_assoc' !dbind_mass.
    apply SeriesC_ext => a.
    f_equal. by rewrite !dret_id_left' IHn Hf0. 
  }
  (* SeriesC (osch_pexec Ξ' n (apoint2, ρ)) = SeriesC (osch_pexec (f ρ).1.1 n ((f ρ).1.2, ρ)) *)
  assert (∀ n ρ, SeriesC $ osch_pexec Ξ' n (apoint2 (B := cfg), ρ) = SeriesC $ osch_pexec ((`f) ρ).1.1 n (((`f) ρ).1.2, ρ)) as Hpexec. {
    induction n; intros; first by rewrite !osch_pexec_O !dret_mass.
    rewrite !osch_pexec_Sn /osch_step_or_none /osch_step /=.
    case_bool_decide; first by exfalso; eapply apoint1_not_point2.
    case_bool_decide; last done.
    destruct ((`f) ρ) as [[Ξ_ρ ζ_ρ] n_ρ] eqn : Hf0. simpl.
    rewrite Hf0 /=. 
    destruct (Ξ_ρ (ζ_ρ, ρ)) as [μ'|] eqn : Hμ'; rewrite Hμ' /=.
    2 : {
      pose proof (Expval_dret (A := sch_int_state * con_language.cfg con_prob_lang)) as He. 
      rewrite /Expval in He. by rewrite !dbind_mass !He IHn Hf0. 
    }
    rewrite /dmap -!dbind_assoc' /= !dbind_mass. 
    apply SeriesC_ext => [[ζ' i']]. 
    f_equal. 
    rewrite dret_id_left -!dbind_assoc' !dbind_mass.
    apply SeriesC_ext => a.
    f_equal. by rewrite !dret_id_left' Hpexec1 Hf0.
  }

  (* Find a uniform step bound n for all successor states *)
  assert (∃ n, ∀ e' σ' efs, 0 < prim_step e σ (e', σ', efs) →
    err_lb_con φ (<[m:=e']> C ++ efs, σ') <=
    prob (osch_exec_val ((`f) (<[m:=e']> C ++ efs, σ')).1.1 n
           (((`f) (<[m:=e']> C ++ efs, σ')).1.2, (<[m:=e']> C ++ efs, σ')))
         (λ x0, negb (bool_decide (φ x0))) + 1 -
    SeriesC (osch_pexec ((`f) (<[m:=e']> C ++ efs, σ')).1.1 n
              (((`f) (<[m:=e']> C ++ efs, σ')).1.2, (<[m:=e']> C ++ efs, σ'))) + ε) as [n Hn]. {
    destruct (step_fin e σ) as [l Hl].
    exists (list_max $ map (λ x, (`f (<[m:=x.1.1]> C ++ x.2, x.1.2)).2) l).
    intros.
    etrans; first by apply (proj2_sig f).
    specialize (Hl _ H1).
    epose proof (iffLR (Forall_map _ _ _) (iffLR (list_max_le
      (map (λ x : expr * state * list expr, ((`f) (<[m:=x.1.1]> C ++ x.2, x.1.2)).2) l) _)
      (Nat.le_refl _))).
    rewrite Forall_forall in H2.
    specialize (H2 _ Hl). simpl in H2.
    apply Rplus_le_compat_r, Rplus_le_compat;
    last by apply Ropp_le_contravar, osch_pexec_mass_mono'. 
    apply Rplus_le_compat_r.
    apply SeriesC_le; last by eapply ex_seriesC_filter_bool_pos.
    intros. case_bool_decide; first real_solver.
    simpl. split; first done.
    by apply osch_exec_val_mono'.
  }
  etrans.
  2 : {
    eapply Rplus_le_compat_r.
    apply rbar_le_finite; [apply err_lb_con_finite|].
    apply (proj2_sig (Rbar_ex_lub _)).
    by exists Ξ', (apoint1 (B := cfg)), (S n).
  }
  (* Expand osch_exec_val and osch_pexec by one step from apoint1 *)
  rewrite /Expval osch_exec_val_Sn osch_pexec_Sn /osch_step_or_none /osch_step /=.
  rewrite /schf'. case_bool_decide; last done.
  rewrite dret_id_left HCm.
  assert (to_val e = None) as Hve; first by destruct Hred; eapply val_stuck.
  rewrite Hve /=. rewrite dmap_comp /compose /= /dmap -!dbind_assoc'.
  rewrite prob_dbind.
  setoid_rewrite dret_id_left.
  rewrite dbind_mass.
  have Hexs1 : ex_seriesC (λ x, prim_step e σ x *
    SeriesC (osch_pexec ((`f) (<[m:=x.1.1]> C ++ x.2, x.1.2)).1.1 n
               (((`f) (<[m:=x.1.1]> C ++ x.2, x.1.2)).1.2, (<[m:=x.1.1]> C ++ x.2, x.1.2)))).
  { eapply ex_expval_bounded; split; real_solver. }
  have Hexs2 : ex_seriesC (λ x : expr * state * list expr, prim_step e σ x *
    prob (osch_exec_val ((`f) (<[m:=x.1.1]> C ++ x.2, x.1.2)).1.1 n
            (((`f) (<[m:=x.1.1]> C ++ x.2, x.1.2)).1.2, (<[m:=x.1.1]> C ++ x.2, x.1.2)))
         (λ x0 : val, negb (bool_decide (φ x0)))).
  { eapply ex_expval_bounded; split; [apply prob_ge_0| apply prob_le_1]. }
  have Hexs3 : ∀ r, ex_seriesC (λ x : expr * state * list expr, prim_step e σ x * r).
  { intros. by apply ex_seriesC_scal_r. }
  eapply Rle_trans with (SeriesC (λ 'a,
    prim_step e σ a * (
      prob (osch_exec_val ((`f) (<[m:=a.1.1]> C ++ a.2, a.1.2)).1.1 n
              (((`f) (<[m:=a.1.1]> C ++ a.2, a.1.2)).1.2, (<[m:=a.1.1]> C ++ a.2, a.1.2)))
           (λ x0 : val, negb (bool_decide (φ x0))) + 1 -
      SeriesC (osch_pexec ((`f) (<[m:=a.1.1]> C ++ a.2, a.1.2)).1.1 n
                 (((`f) (<[m:=a.1.1]> C ++ a.2, a.1.2)).1.2, (<[m:=a.1.1]> C ++ a.2, a.1.2))) + ε))).
  {
    apply SeriesC_le.
    - intros [[??]?]. split.
      + apply Rmult_le_pos; first real_solver; apply err_lb_con_nn.
      + destruct (decide (0 < prim_step e σ (e0, s, l))). 
        2 : { 
          assert (0 = prim_step e σ (e0, s, l)) as Hq; last (rewrite -Hq; lra); 
          apply Rle_antisym; real_solver. 
        }
        apply Rmult_le_compat_l; first real_solver. by apply Hn.
    - setoid_rewrite Rmult_plus_distr_l.
      setoid_rewrite Rmult_minus_distr_l.
      setoid_rewrite Rmult_plus_distr_l.
      apply ex_seriesC_plus => //.
      apply ex_seriesC_minus => //.
      apply ex_seriesC_plus => //.
  }
  setoid_rewrite Rmult_plus_distr_l.
  rewrite SeriesC_plus //=.
  2 : {
    setoid_rewrite Rmult_minus_distr_l.
    setoid_rewrite Rmult_plus_distr_l.
    apply ex_seriesC_minus => //.
    apply ex_seriesC_plus => //.
  }
  setoid_rewrite Rmult_minus_distr_l.
  rewrite SeriesC_minus //=;
    last by setoid_rewrite Rmult_plus_distr_l; apply ex_seriesC_plus => //=.
  setoid_rewrite Rmult_plus_distr_l.
  rewrite SeriesC_plus //= !SeriesC_scal_r (prim_step_mass e σ Hred) !Rmult_1_l.
  apply Req_le.
  do 2 f_equal.
  - f_equal. apply SeriesC_ext => [[[??]?]].
    rewrite Hexec_val //=.
  - apply SeriesC_ext => [[[??]?]].
    rewrite Hpexec //=. 
Qed.

Lemma err_lb_con_val φ v ρ :
  ρ.1 !! 0%nat = Some (of_val v) →
  (if bool_decide (φ v) then 0 else 1) <= err_lb_con φ ρ.
Proof using Hinf.
  intros.
  destruct (proj2_sig (Rbar_ex_lub (λ r, ∃ Ξ ζ m,
  r = prob (osch_exec_val Ξ m (ζ, ρ)) (λ x, negb $ bool_decide $ φ x) + 1 -
    SeriesC (osch_pexec Ξ m (ζ, ρ))))) as [Hub Hl].
  case_bool_decide; first by apply err_lb_con_nn.
  set schf : sch_int_state * cfg -> option (distr (sch_int_state * nat)) := λ _, None.
  have Hschf : ∀ x μ, schf x = Some μ → SeriesC μ = 1;
    first by rewrite /schf; intros; done.
  set Ξ : full_scheduler sch_int_state :=
    {| sch := {| oscheduler_f := schf |}; full_distr := Hschf |}.
  rewrite /err_lb_con /Rbar_lub.
  apply rbar_le_finite; first apply err_lb_con_finite.
  apply Hub. 
  exists Ξ, point, 0%nat.
  destruct ρ.
  rewrite osch_pexec_O /osch_exec_val /= dret_id_left dret_mass /con_lang_mdp_to_final /= H0 to_of_val prob_dret_true;
  last by case_bool_decide.
  real_solver.
Qed.

Lemma err_lb_con_pure_step φ m C σ e e' :
  pure_step e e' →
  C !! m = Some e → con_language.reducible e σ →
  err_lb_con φ (<[m:=e']> C, σ) <= err_lb_con φ (C, σ).
Proof using Hinf.
  intros.
  etrans; last by apply err_lb_con_step.
  inversion H0. 
  erewrite (pmf_1_eq_dret (prim_step e σ)); last by apply pure_step_det.
  by rewrite Expval_dret app_nil_r.
Qed.

Lemma err_lb_con_stuck φ C σ m e :
  C !! m = Some e →
  con_language.stuck e σ →
  err_lb_con φ (C, σ) = 1.
Proof using Hinf.
  intros HCm [Hval Hirr].
  have Hstep : prim_step e σ = dzero.
  { apply dzero_ext. intros x. apply Rle_antisym; last by apply pmf_pos.
    by apply Rnot_lt_le; intros Hx; rewrite -not_reducible in Hirr; apply Hirr; eexists; real_solver. }
  apply Rle_antisym; first by apply err_lb_con_bound.
  apply rbar_le_finite; first by apply err_lb_con_finite.
  apply (proj1 (proj2_sig (Rbar_ex_lub _))).
  exists (tfsch m), point, 1%nat.
  rewrite osch_pexec_Sn.
  erewrite dbind_ext_right; last apply osch_pexec_O.
  rewrite /osch_exec_val /osch_step_or_none /= /osch_step /=.
  rewrite !dret_id_right !dret_id_left HCm Hval Hstep !dmap_dzero !dbind_dzero. 
  rewrite dzero_mass /prob SeriesC_0; real_solver. 
Qed.

End err_lb_con.

