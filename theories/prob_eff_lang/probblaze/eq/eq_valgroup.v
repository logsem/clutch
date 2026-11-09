(* The group operations of [valgroup] in the logic for equivalences. *)

From iris.bi Require Import monpred.
From iris.proofmode Require Import base proofmode classes environments coq_tactics ltac_tactics reduction monpred.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode tactics notation class_instances.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types.
From clutch.prob_eff_lang.probblaze.examples Require Import valgroup.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic.

Import fingroup.
Import fingroup.fingroup.

Section eq_valgroup.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  #[local] Set Default Proof Using "All".
  #[local] Open Scope bi_scope.
  Implicit Types (el er : expr) (Δ : envs (iPropD Σ)).

  Lemma eq_lift_group vl vr : ⟪ sem_ty_group ⟫ vl vr ⊣⊢ ∃ g : vgG, ⌜vl = vgval g ∧ vr = vgval g⌝.
  Proof.
    split=> d. rewrite monPred_at_exist eq_lift_at. destruct d; rewrite /pick /sem_ty_group /=.
    all: iSplit; [iIntros "(%g & -> & ->)"|iIntros "(%g & %Hg)"; destruct Hg as [-> ->]]; iExists g; rewrite ?monPred_at_pure; done.
  Qed.

  (* One rule per operation and side: the result in an evaluation context. *)

  Lemma eq_exp_l E K (b : vgG) (p : nat) er X R :
    EQ fill K (vgval (b ^+ p)) ≈ er @ E <|X|> {{ R }} ⊢ EQ fill K (vexp b #p) ≈ er @ E <|X|> {{ R }}.
  Proof. apply eq_step_l=> ??; [apply brel_exp_l|apply brel_exp_r]. Qed.
  Lemma eq_exp_r E K (b : vgG) (p : nat) el X R :
    EQ el ≈ fill K (vgval (b ^+ p)) @ E <|X|> {{ R }} ⊢ EQ el ≈ fill K (vexp b #p) @ E <|X|> {{ R }}.
  Proof. apply eq_step_r=> ??; [apply brel_exp_l|apply brel_exp_r]. Qed.
  Lemma eq_mult_l E K (a b : vgG) er X R :
    EQ fill K (vgval (a * b)) ≈ er @ E <|X|> {{ R }} ⊢ EQ fill K (vmult a b) ≈ er @ E <|X|> {{ R }}.
  Proof. apply eq_step_l=> ??; [apply brel_mult_l|apply brel_mult_r]. Qed.
  Lemma eq_mult_r E K (a b : vgG) el X R :
    EQ el ≈ fill K (vgval (a * b)) @ E <|X|> {{ R }} ⊢ EQ el ≈ fill K (vmult a b) @ E <|X|> {{ R }}.
  Proof. apply eq_step_r=> ??; [apply brel_mult_l|apply brel_mult_r]. Qed.
  Lemma eq_eq_l E K (a b : vgG) er X R :
    EQ fill K #(bool_decide (a = b)) ≈ er @ E <|X|> {{ R }} ⊢ EQ fill K (veq a b) ≈ er @ E <|X|> {{ R }}.
  Proof. apply eq_step_l=> ??; [apply brel_eq_l|apply brel_eq_r]. Qed.
  Lemma eq_eq_r E K (a b : vgG) el X R :
    EQ el ≈ fill K #(bool_decide (a = b)) @ E <|X|> {{ R }} ⊢ EQ el ≈ fill K (veq a b) @ E <|X|> {{ R }}.
  Proof. apply eq_step_r=> ??; [apply brel_eq_l|apply brel_eq_r]. Qed.

  Lemma tac_eq_exp_l E K Δ el er (b : vgG) (p : nat) X R :
    IntoCtx el (TCEq (vexp b #p)) K →
    envs_entails Δ (EQ fill K (vgval (b ^+ p)) ≈ er @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof. rewrite envs_entails_unseal=> HK ->. apply tc_eq_fill in HK. rewrite -HK. apply eq_exp_l. Qed.
  Lemma tac_eq_exp_r E K Δ el er (b : vgG) (p : nat) X R :
    IntoCtx er (TCEq (vexp b #p)) K →
    envs_entails Δ (EQ el ≈ fill K (vgval (b ^+ p)) @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof. rewrite envs_entails_unseal=> HK ->. apply tc_eq_fill in HK. rewrite -HK. apply eq_exp_r. Qed.
  Lemma tac_eq_mult_l E K Δ el er (a b : vgG) X R :
    IntoCtx el (TCEq (vmult a b)) K →
    envs_entails Δ (EQ fill K (vgval (a * b)) ≈ er @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof. rewrite envs_entails_unseal=> HK ->. apply tc_eq_fill in HK. rewrite -HK. apply eq_mult_l. Qed.
  Lemma tac_eq_mult_r E K Δ el er (a b : vgG) X R :
    IntoCtx er (TCEq (vmult a b)) K →
    envs_entails Δ (EQ el ≈ fill K (vgval (a * b)) @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof. rewrite envs_entails_unseal=> HK ->. apply tc_eq_fill in HK. rewrite -HK. apply eq_mult_r. Qed.
  Lemma tac_eq_eq_l E K Δ el er (a b : vgG) X R :
    IntoCtx el (TCEq (veq a b)) K →
    envs_entails Δ (EQ fill K #(bool_decide (a = b)) ≈ er @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof. rewrite envs_entails_unseal=> HK ->. apply tc_eq_fill in HK. rewrite -HK. apply eq_eq_l. Qed.
  Lemma tac_eq_eq_r E K Δ el er (a b : vgG) X R :
    IntoCtx er (TCEq (veq a b)) K →
    envs_entails Δ (EQ el ≈ fill K #(bool_decide (a = b)) @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof. rewrite envs_entails_unseal=> HK ->. apply tc_eq_fill in HK. rewrite -HK. apply eq_eq_r. Qed.

  Lemma eq_inv_l E K (a : vgG) er X R :
    EQ fill K (vgval (a ^-1)) ≈ er @ E <|X|> {{ R }} ⊢ EQ fill K (vinv a) ≈ er @ E <|X|> {{ R }}.
  Proof. apply eq_step_l=> ??; [apply brel_inv_l|apply brel_inv_r]. Qed.
  Lemma eq_inv_r E K (a : vgG) el X R :
    EQ el ≈ fill K (vgval (a ^-1)) @ E <|X|> {{ R }} ⊢ EQ el ≈ fill K (vinv a) @ E <|X|> {{ R }}.
  Proof. apply eq_step_r=> ??; [apply brel_inv_l|apply brel_inv_r]. Qed.

  Lemma tac_eq_inv_l E K Δ el er (a : vgG) X R :
    IntoCtx el (TCEq (vinv a)) K →
    envs_entails Δ (EQ fill K (vgval (a ^-1)) ≈ er @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof. rewrite envs_entails_unseal=> HK ->. apply tc_eq_fill in HK. rewrite -HK. apply eq_inv_l. Qed.
  Lemma tac_eq_inv_r E K Δ el er (a : vgG) X R :
    IntoCtx er (TCEq (vinv a)) K →
    envs_entails Δ (EQ el ≈ fill K (vgval (a ^-1)) @ E <|X|> {{ R }}) → envs_entails Δ (EQ el ≈ er @ E <|X|> {{ R }}).
  Proof. rewrite envs_entails_unseal=> HK ->. apply tc_eq_fill in HK. rewrite -HK. apply eq_inv_r. Qed.


End eq_valgroup.

Tactic Notation "eq_group_apply" constr(H) := eq_goal_check ltac:(eapply H; [tc_solve | simpl]).

Tactic Notation "eq_exp_l" := eq_group_apply tac_eq_exp_l.
Tactic Notation "eq_exp_r" := eq_group_apply tac_eq_exp_r.
Tactic Notation "eq_mult_l" := eq_group_apply tac_eq_mult_l.
Tactic Notation "eq_mult_r" := eq_group_apply tac_eq_mult_r.
Tactic Notation "eq_eq_l" := eq_group_apply tac_eq_eq_l.
Tactic Notation "eq_eq_r" := eq_group_apply tac_eq_eq_r.
Tactic Notation "eq_inv_l" := eq_group_apply tac_eq_inv_l.
Tactic Notation "eq_inv_r" := eq_group_apply tac_eq_inv_r.

(* Encoding and decoding group elements (with [vg_of_int_sem n = Some g] in
   the context). *)
Tactic Notation "eq_vg_of_int_l" := eq_lift_l brel_vg_of_int_correct_l brel_vg_of_int_correct_r.
Tactic Notation "eq_vg_of_int_r" := eq_lift_r brel_vg_of_int_correct_l brel_vg_of_int_correct_r.
Tactic Notation "eq_vg_of_int_none_l" := eq_lift_l brel_vg_of_int_none_l brel_vg_of_int_none_r.
Tactic Notation "eq_vg_of_int_none_r" := eq_lift_r brel_vg_of_int_none_l brel_vg_of_int_none_r.
Tactic Notation "eq_int_of_vg_l" := eq_lift_l brel_int_of_vg_sem_correct_l brel_int_of_vg_sem_correct_r.
Tactic Notation "eq_int_of_vg_r" := eq_lift_r brel_int_of_vg_sem_correct_l brel_int_of_vg_sem_correct_r.

(* Pure steps and group operations on both sides. *)
Ltac eq_pures' :=
  iStartProof;
  repeat (first [try eq_pures_r | eq_exp_r | eq_mult_r | eq_inv_r | eq_eq_r]);
  repeat (first [try eq_pures_l | eq_exp_l | eq_mult_l | eq_inv_l | eq_eq_l]).
