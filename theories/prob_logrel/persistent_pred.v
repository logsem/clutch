From stdpp Require Import tactics.
From iris.bi Require Import bi.
From iris.prelude Require Import options.

Section persistent_pred.
  Context (A : Type) (PROP : bi).

  (* The domain of semantic types: persistent Iris predicates type A. *)
  Record persistent_pred := PersPred {
    pers_pred_car :> A → PROP;
    pers_pred_persistent x : Persistent (pers_pred_car x)
  }.
  Local Arguments PersPred _%I {_}.
  Global Existing Instances pers_pred_persistent.

  Local Instance persistent_pred_equiv : Equiv persistent_pred :=
    λ Φ Φ', ∀ x, Φ x ≡ Φ' x.
  Local Instance persistent_pred_dist : Dist persistent_pred :=
    λ n Φ Φ', ∀ x, Φ x ≡{n}≡ Φ' x.
  Definition persistent_pred_ofe_mixin : OfeMixin persistent_pred.
  Proof. by apply (iso_ofe_mixin (pers_pred_car : _ → A -d> _)). Qed.
  Canonical Structure persistent_predO :=
    Ofe persistent_pred persistent_pred_ofe_mixin.

  Global Instance persistent_pred_cofe : Cofe persistent_predO.
  Proof.
    apply (iso_cofe_subtype' (λ Φ : A -d> PROP, ∀ w, Persistent (Φ w))
      PersPred pers_pred_car)=> //.
    - apply _.
    - apply limit_preserving_forall=> w.
      by apply bi.limit_preserving_Persistent=> n ??.
  Qed.

  Global Instance persistent_pred_car_ne n :
    Proper (dist n ==> (=) ==> dist n)
      pers_pred_car.
  Proof. by intros ? ? ? ? ? ->. Qed.
  Global Instance persistent_pred_car_proper :
    Proper ((≡) ==> (=) ==> (≡)) pers_pred_car.
  Proof. by intros ? ? ? ? ? ->. Qed.

  Lemma persistent_pred_ext (f g : persistent_pred) : f ≡ g ↔ ∀ x, f x ≡ g x.
  Proof. done. Qed.

  Global Instance: Inhabited persistent_pred := populate (PersPred (λ _, True))%I.

End persistent_pred.

Global Arguments PersPred {_ _} _%I {_}.
Global Arguments pers_pred_car {_ _} !_ _.
Global Instance: Params (@pers_pred_car) 2 := {}.
