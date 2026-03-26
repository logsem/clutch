From clutch.eris.examples.math Require Import prelude.

Import Hierarchy.
Set Default Proof Using "Type*".

(** * Auto-derive Tactics

    Automation for proving integrability and continuity via [auto_derive].
    The common pattern is:
<<
      apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
      intros ??.
      apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
      by auto_derive.
>>
    These tactics collapse this into one call. *)

(** Prove [continuous f x] from differentiability via [auto_derive]. *)
Ltac continuous_auto_derive :=
  apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule));
  auto_derive; done.

(** Prove [ex_RInt f a b] by showing continuity via [auto_derive]. *)
Ltac ex_RInt_auto_derive :=
  apply (ex_RInt_continuous (V := R_CompleteNormedModule));
  intros ??;
  continuous_auto_derive.
