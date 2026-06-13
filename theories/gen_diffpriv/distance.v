(** Adjacency metrics ([Distance]) for the generic DP logic.  Ported from
    [clutch.diffpriv.distance], but built over [gen_prob_lang]'s [val] (via
    [gen_prob_lang.inject]) rather than [prob_lang]'s.  Core metrics only
    ([dZ]/[dnat]/[dtensor]); the list metric [dlist]/[list_dist] is deferred
    (it is language-independent and can be added when a list-valued case study
    needs it). *)
From Stdlib Require Export Reals Psatz.
From clutch.gen_prob_lang Require Import inject.
From clutch.gen_prob_lang Require Export lang.
From clutch.prelude Require Import base stdpp_ext.

#[local] Open Scope R.

Class Distance (A : Type) : Type := {
    distance_car :: Inject A val
  ; distance : A -> A -> R
  ; distance_pos a1 a2 : 0 <= distance a1 a2
  ; distance_0 a1 a2 : a1 = a2 → distance a1 a2 = 0
}.
Arguments distance_car {_} _.
Coercion distance_car : Distance >-> Inject.
Arguments distance {_} _ _ _.
Coercion distance : Distance >-> Funclass.

Program Definition dZ : Distance Z := {| distance z z' := Rabs (IZR (z - z')) |}.
Next Obligation. intros => /= ; eauto using Rabs_pos. Qed.
Next Obligation. intros ?? -> => /=; replace (a2 - a2)%Z with 0%Z by lia. exact Rabs_R0. Qed.

Lemma dZ_bounded_cases x y k : dZ x y <= (IZR k) -> (- k <= x - y ∧ x - y <= k)%Z.
Proof.
  rewrite /dZ/distance Rabs_Zabs. intros h. apply le_IZR in h. revert h.
  apply Zabs_ind ; intros ; lia.
Qed.

Program Definition dnat : Distance nat := {| distance n n' := Rabs (IZR (n - n')) |}.
Next Obligation. intros => /= ; eauto using Rabs_pos. Qed.
Next Obligation. intros ?? -> => /=; replace (a2 - a2)%Z with 0%Z by lia. exact Rabs_R0. Qed.

Program Definition dtensor `(dA : Distance A) `(dB : Distance B) : Distance (A * B) :=
  {| distance x y := let (x1, x2) := x in let (y1, y2) := y in dA x1 y1 + dB x2 y2 |}.
Next Obligation. intros ???? [] []. apply Rplus_le_le_0_compat ; apply distance_pos. Qed.
Next Obligation. intros ???? [] [] [=]. rewrite !distance_0 //. lra. Qed.
