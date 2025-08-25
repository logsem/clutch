From iris.proofmode       Require Import tactics.
From iris.base_logic      Require Export lib.iprop.
From iris.algebra         Require Import excl_auth.
From iris.base_logic      Require Import lib.own.
From clutch.prob_eff_lang Require Import lang.

Set Default Proof Using "Type".


(** * Setup of Iris's cameras. *)

Class ieffG Σ :=
  #[global] ieffG_authG ::
    inG Σ (excl_authR (laterO (valO -d> (valO -d> iPropO Σ) -n> iPropO Σ))).

Definition ieffΣ := #[
  GFunctor (authRF (optionURF (exclRF (laterOF (valO -d> (valO -d> idOF) -n> idOF)))))
].

Instance subG_ieffΣ {Σ} : subG ieffΣ Σ → ieffG Σ.
Proof. solve_inG. Qed.


(** * Protocols. *)

Section iEff.
  Set Primitive Projections.
  Record iEff Σ := IEff {
    iEff_car : (val -d> (val -d> iPropO Σ) -n> iPropO Σ)
  }.
End iEff.
Arguments IEff {_} _.
Arguments iEff_car {_} _.

Declare Scope ieff_scope.
Delimit Scope ieff_scope with ieff.
Bind Scope ieff_scope with iEff.
Local Open Scope ieff.

Instance iEff_inhabited {Σ} : Inhabited (iEff Σ) := populate (IEff inhabitant).

Section ieff_ofe.
  Context {Σ : gFunctors}.

  Instance iEff_equiv : Equiv (iEff Σ) := λ e1 e2,
    iEff_car e1 ≡ iEff_car e2.
  Instance iEff_dist : Dist (iEff Σ) := λ n e1 e2,
    iEff_car e1 ≡{n}≡ iEff_car e2.

  Lemma iEff_ofe_mixin : OfeMixin (iEff Σ).
  Proof. by apply (iso_ofe_mixin iEff_car). Qed.
  Canonical Structure iEffO := Ofe (iEff Σ) iEff_ofe_mixin.

  Global Instance iEff_cofe : Cofe iEffO.
  Proof. by apply (iso_cofe IEff iEff_car). Qed.
End ieff_ofe.

Global Instance IEff_ne {Σ} : NonExpansive (IEff (Σ:=Σ)).
Proof. by intros ???. Qed.
Global Instance IEff_proper {Σ} : Proper ((≡) ==> (≡)) (IEff (Σ:=Σ)).
Proof. by intros ???. Qed.
Global Instance iEff_car_ne {Σ} : NonExpansive (iEff_car (Σ:=Σ)).
Proof. by intros ???. Qed.
Global Instance iEff_car_proper {Σ} : Proper ((≡) ==> (≡)) (iEff_car (Σ:=Σ)).
Proof. by intros ???. Qed.

Lemma iEff_equivI' {Σ} `{!BiInternalEq SPROP} (e1 e2 : iEff Σ) :
  e1 ≡ e2 ⊣⊢@{SPROP} iEff_car e1 ≡ iEff_car e2.
Proof.
  apply (anti_symm _).
  - by apply f_equivI, iEff_car_ne.
  - destruct e1; destruct e2. simpl.
    by apply f_equivI, IEff_ne.
Qed.

Lemma iEff_equivI {Σ} `{!BiInternalEq SPROP} (e1 e2 : iEff Σ) :
  e1 ≡ e2 ⊣⊢@{SPROP} ∀ v q, iEff_car e1 v q ≡ iEff_car e2 v q.
Proof.
  trans (iEff_car e1 ≡ iEff_car e2 : SPROP)%I.
  - by apply iEff_equivI'.
  - rewrite discrete_fun_equivI. f_equiv=>v.
    by apply ofe_morO_equivI.
Qed.

(* iEff_bottom. *)
Instance iEff_bottom {Σ} : Bottom (iEff Σ) := IEff (λ _, λne _, False%I).

