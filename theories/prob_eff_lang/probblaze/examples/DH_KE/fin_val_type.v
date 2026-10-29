From clutch.prob_eff_lang.probblaze Require Import notation types sem_def interp metatheory logic.
From clutch.prob_eff_lang.probblaze Require sem_types.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype  seq choice fintype.
Import fintype.

Local Notation "'cval'" := syntax.val.

Class fin_val_type :=
  Fin_val_type { fvT : finType
               ; fvtval : fvT → cval
               ; card := #|{: fvT}|
               ; fvtval_inj : Inj eq eq fvtval }.

#[warning="-uniform-inheritance"] Coercion fvtval_as {fvt : fin_val_type}
  (x : fvT) : cval := fvtval x.

Class fin_val_type_struct {fvt : fin_val_type} :=
  Fin_val_type_struct
    { int_of_fvt : cval
    ; fvt_of_int : cval
    ; τFT : type

    ; int_of_fvt_closed : is_closed_val int_of_fvt
    ; fvt_of_int_closed : is_closed_val fvt_of_int

    ; int_of_fvt_typed : val_typed int_of_fvt (τFT ⇾ TInt)%ty
    ; fvt_of_int_typed : val_typed fvt_of_int (TInt ⇾ () + τFT)%ty
    ; τFT_multi : le.MultiT τFT
    }.

Definition fvt_of_fvts := λ fvt (FVTS : @fin_val_type_struct fvt), fvt.
Coercion fvt_of_fvts : fin_val_type_struct >-> fin_val_type.

#[export] Hint Resolve int_of_fvt_closed : core.
#[export] Hint Resolve fvt_of_int_closed : core.

Definition sem_ty_fvt `{probblazeRGS Σ} {vg : fin_val_type} : sem_ty Σ :=
  (λ v1 v2, ∃ x : fvT, ⌜ v1 = x ⌝ ∗ ⌜ v2 = x ⌝)%I.

(* Not an instance: enable locally with [#[local] Existing Instance multi_ty_fvt]. *)
Lemma multi_ty_fvt `{probblazeRGS Σ} {fvt : fin_val_type} : sem_types.MultiT (sem_ty_fvt (vg := fvt) : sem_ty Σ).
Proof.
  constructor. iIntros "!#" (v1 v2) "(%x & -> & ->)".
  rewrite /sem_types.sem_ty_mbang /=. iModIntro. by iExists x.
Qed.

Class fin_val `{probblazeRGS Σ} `{fvts : fin_val_type_struct} :=
  Fin_val
    { sem_τFT := sem_ty_fvt
    ; τFT_subtype v1 v2 η μ δ ξ : sem_ty_fvt v1 v2 ⊢ interp._ty η μ δ τFT ξ v1 v2
    ; fvtval_typed : ∀ x : fvT, val_typed (fvtval x) τFT
    ; int_of_fvt_sem : fvT -> nat
    ; int_of_fvt_sem_bound : ∀ x : fvT, (int_of_fvt_sem x < card)%nat
    ; fvt_of_int_sem : nat -> option fvT
    ; fvt_of_int_of_fvt_sem : forall (n : nat) (x : fvT),
        fvt_of_int_sem n = Some x -> int_of_fvt_sem x = n
    ; int_of_fvt_of_int_sem : forall (x : fvT),
        fvt_of_int_sem (int_of_fvt_sem x) = Some x
    ; brel_int_of_fvt_sem_correct_l E K x X R e :
      (BREL (fill K #(int_of_fvt_sem x)) ≤ e @ E <|X|> {{R}}) -∗
      (BREL (fill K (int_of_fvt (fvtval x))) ≤ e @ E <|X|> {{R}})
    ; brel_int_of_fvt_sem_correct_r E K x X R e :
        (BREL e ≤ (fill K #(int_of_fvt_sem x)) @ E <|X|> {{R}}) -∗
        (BREL e ≤ (fill K (int_of_fvt (fvtval x))) @ E <|X|> {{R}})
    ; brel_fvt_of_int_correct_l E K X R e n x :
      fvt_of_int_sem n = Some x ->
      (BREL (fill K (SOMEV (fvtval x))) ≤ e @ E <|X|> {{R}}) -∗
      (BREL (fill K (fvt_of_int (#n))) ≤ e @ E <|X|> {{R}})
    ; brel_fvt_of_int_correct_r E K X R e n x :
      fvt_of_int_sem n = Some x ->
      (BREL e ≤ (fill K (SOMEV (fvtval x))) @ E <|X|> {{R}}) -∗
      (BREL e ≤ (fill K (fvt_of_int (#n))) @ E <|X|> {{R}})
    ; brel_fvt_of_int_none_l E K X R e n :
      fvt_of_int_sem n = None ->
      (BREL (fill K NONEV) ≤ e @ E <|X|> {{R}}) -∗
      (BREL (fill K (fvt_of_int (#n))) ≤ e @ E <|X|> {{R}})
    ; brel_fvt_of_int_none_r E K X R e n :
      fvt_of_int_sem n = None ->
      (BREL e ≤ (fill K NONEV) @ E <|X|> {{R}}) -∗
      (BREL e ≤ (fill K (fvt_of_int (#n))) @ E <|X|> {{R}})
    }.

Definition fvt_of_fv := λ {Σ HΣ} fvt (FVTS : @fin_val_type_struct fvt)  (FV : @fin_val Σ HΣ _ FVTS), fvt.
Coercion fvt_of_fv : fin_val >-> fin_val_type.

Definition fvts_of_fv := λ {Σ HΣ} fvt (FVTS : @fin_val_type_struct fvt)  (FV : @fin_val Σ HΣ _ FVTS), FVTS.
Coercion fvts_of_fv : fin_val >-> fin_val_type_struct.

Definition fvt_sort (fvt : fin_val_type) : Type := fvT.
Coercion fvt_sort : fin_val_type >-> Sortclass.

(** [int_of_fvt_sem] is an injection of [fvT] into {0, .., card-1}, a set with
    exactly [card] elements, hence a bijection onto it.  So every code below
    [card] decodes -- the [NONE] branch of a [fvt_of_int] call on such a code
    is dead.  Mirrors [valgroup.v]'s [vg_of_int_sem_surj]. *)
Section decoding.
  Context `{probblazeRGS Σ} `{fvts : fin_val_type_struct} {FV : fin_val}.

  Lemma int_of_fvt_sem_inj (x y : fvT) :
    int_of_fvt_sem x = int_of_fvt_sem y → x = y.
  Proof.
    intros Heq. pose proof (int_of_fvt_of_int_sem x) as Hx.
    rewrite Heq int_of_fvt_of_int_sem in Hx. by injection Hx.
  Qed.

  Lemma fvt_of_int_sem_surj (n : nat) :
    (n < card)%nat →
    ∃ x : fvT, fvt_of_int_sem n = Some x ∧ int_of_fvt_sem x = n.
  Proof.
    intros Hn.
    have Hb : ∀ x : fvT, is_true (ssrnat.leq (S (int_of_fvt_sem x)) card).
    { intro x. apply/ssrnat.leP. pose proof (int_of_fvt_sem_bound x). lia. }
    pose (F := fun x : fvT => Ordinal (Hb x)).
    have HFinj : ssrfun.injective F.
    { intros a b HF. apply int_of_fvt_sem_inj.
      exact: (f_equal (@nat_of_ord card) HF). }
    have Hcard : is_true (ssrnat.leq #|'I_card| #|{: fvT}|).
    { rewrite card_ord. apply ssrnat.leqnn. }
    have Hn' : is_true (ssrnat.leq (S n) card).
    { apply/ssrnat.leP. lia. }
    move: (inj_card_onto HFinj Hcard (Ordinal Hn')) => Hcod.
    case/codomP: Hcod => x Hx.
    have Hv := f_equal (@nat_of_ord card) Hx. simpl in Hv.
    assert (Hint : int_of_fvt_sem x = n) by lia.
    exists x. split; [| exact Hint]. rewrite -Hint. apply int_of_fvt_of_int_sem.
  Qed.
End decoding.
