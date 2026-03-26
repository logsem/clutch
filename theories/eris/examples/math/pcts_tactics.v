From clutch.eris.examples.math Require Import prelude piecewise auto_derive_tactics.

Import Hierarchy.
Set Default Proof Using "Type*".

(** * PCts/IPCts Tactics

    Automation for proving piecewise continuity via [auto_derive].
    The common patterns are:
<<
      apply PCts_cts.
      intros ??.
      continuous_auto_derive.
>>
    and:
<<
      apply IPCts_cts.
      intros ?.
      continuous_auto_derive.
>>
    These tactics collapse each into one call. *)

(** Prove [PCts f a b] by showing differentiability via [auto_derive]. *)
Ltac PCts_auto_derive :=
  apply PCts_cts;
  intros ??;
  continuous_auto_derive.

(** Prove [IPCts f] by showing differentiability via [auto_derive]. *)
Ltac IPCts_auto_derive :=
  apply IPCts_cts;
  intros ?;
  continuous_auto_derive.
