(** * The operations of the group [Zpˣ] ([valgroup_Zpx]) in extractable form

    The instance [cgs_p] contains proof terms that extraction cannot
    handle, and its unit [vunit_p] is computed from mathcomp's unit group.
    The executable instances therefore use the operations directly; the
    two that mention the unit are restated with the literal [#1] and proved
    equal to the originals. *)
From clutch.prob_eff_lang.probblaze Require Import syntax notation.
From clutch.prob_eff_lang.probblaze.examples Require Import valgroup valgroup_Zpx.

Definition vunit_z : val := #1.

Lemma vunit_p_one p''' : vunit_p p''' = vunit_z.
Proof.
  rewrite /vunit_p /= /vgval_p /=.
  rewrite div.modn_small //.
Qed.

Definition vinv_z (p''' : nat) : val :=
  (λ:"x", (vexp' vunit_z (vmult_p p''') "x" (#(S p'''))) `rem` #(S (S (S p'''))))%V.

Lemma vinv_z_eq p''' : vinv_z p''' = vinv_p p'''.
Proof. by rewrite /vinv_z /vinv_p vunit_p_one. Qed.
