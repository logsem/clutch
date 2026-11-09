(* The finite value types of [fin_val_type] in the logic for equivalences. *)

From iris.bi Require Import monpred.
From iris.proofmode Require Import base proofmode classes monpred.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode tactics notation.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types.
From clutch.prob_eff_lang.probblaze.examples Require Import fin_val_type.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic.

Section eq_finval.
  Context `{!probblazeRGS Σ} {t : fin_val_type} {s : @fin_val_type_struct t} {fv : @fin_val Σ _ t s}.
  #[local] Open Scope bi_scope.
  Implicit Types (el er : expr).

  Lemma eq_lift_fvt vl vr :
    ⟪ sem_τFT (fin_val := fv) ⟫ vl vr ⊣⊢ ∃ x : fintype.Finite.sort fvT, ⌜vl = fvtval x ∧ vr = fvtval x⌝.
  Proof.
    split=> d. rewrite monPred_at_exist eq_lift_at. destruct d; rewrite /pick /= /sem_ty_fvt /=.
    all: iSplit; [iIntros "(%x & -> & ->)"|iIntros "(%x & %Hx)"; destruct Hx as [-> ->]];
      iExists x; rewrite ?monPred_at_pure; done.
  Qed.

  Lemma eq_fvt_of_int_l E K X R er (n : nat) (x : fintype.Finite.sort fvT) (Hx : fvt_of_int_sem n = Some x) :
    EQ fill K (SOMEV (fvtval x)) ≈ er @ E <|X|> {{ R }} ⊢ EQ fill K (fvt_of_int #n) ≈ er @ E <|X|> {{ R }}.
  Proof.
    apply eq_step_l=> e S.
    - by iApply brel_fvt_of_int_correct_l.
    - by iApply brel_fvt_of_int_correct_r.
  Qed.
  Lemma eq_fvt_of_int_r E K X R el (n : nat) (x : fintype.Finite.sort fvT) (Hx : fvt_of_int_sem n = Some x) :
    EQ el ≈ fill K (SOMEV (fvtval x)) @ E <|X|> {{ R }} ⊢ EQ el ≈ fill K (fvt_of_int #n) @ E <|X|> {{ R }}.
  Proof.
    apply eq_step_r=> e S.
    - by iApply brel_fvt_of_int_correct_l.
    - by iApply brel_fvt_of_int_correct_r.
  Qed.

  Lemma eq_int_of_fvt_l E K X R er (x : fintype.Finite.sort fvT) :
    EQ fill K #(int_of_fvt_sem x) ≈ er @ E <|X|> {{ R }} ⊢ EQ fill K (int_of_fvt (fvtval x)) ≈ er @ E <|X|> {{ R }}.
  Proof.
    apply eq_step_l=> e S.
    - by iApply brel_int_of_fvt_sem_correct_l.
    - by iApply brel_int_of_fvt_sem_correct_r.
  Qed.
  Lemma eq_int_of_fvt_r E K X R el (x : fintype.Finite.sort fvT) :
    EQ el ≈ fill K #(int_of_fvt_sem x) @ E <|X|> {{ R }} ⊢ EQ el ≈ fill K (int_of_fvt (fvtval x)) @ E <|X|> {{ R }}.
  Proof.
    apply eq_step_r=> e S.
    - by iApply brel_int_of_fvt_sem_correct_l.
    - by iApply brel_int_of_fvt_sem_correct_r.
  Qed.

End eq_finval.

(* [eq_fvt_of_int_l Hx], for [Hx : fvt_of_int_sem n = Some x]: decode [#n] in
   [l] (the hypothesis determines the finite type). *)
Tactic Notation "eq_fvt_of_int_l" constr(Hx) :=
  lazymatch type of Hx with
  | @fvt_of_int_sem _ _ ?t ?s _ ?n = Some _ =>
      eq_focus_l (App (Val (@fvt_of_int t s)) (Val (LitV (LitInt (Z.of_nat n)))));
      iApply (eq_fvt_of_int_l _ _ _ _ _ _ _ Hx)
  end.
Tactic Notation "eq_fvt_of_int_r" constr(Hx) :=
  lazymatch type of Hx with
  | @fvt_of_int_sem _ _ ?t ?s _ ?n = Some _ =>
      eq_focus_r (App (Val (@fvt_of_int t s)) (Val (LitV (LitInt (Z.of_nat n)))));
      iApply (eq_fvt_of_int_r _ _ _ _ _ _ _ Hx)
  end.

(* [eq_int_of_fvt_l fv]: encode a value of the finite type of [fv] in [l]. *)
Tactic Notation "eq_int_of_fvt_l" constr(fv) :=
  eq_lift_l (brel_int_of_fvt_sem_correct_l (fin_val := fv)) (brel_int_of_fvt_sem_correct_r (fin_val := fv)).
Tactic Notation "eq_int_of_fvt_r" constr(fv) :=
  eq_lift_r (brel_int_of_fvt_sem_correct_l (fin_val := fv)) (brel_int_of_fvt_sem_correct_r (fin_val := fv)).
