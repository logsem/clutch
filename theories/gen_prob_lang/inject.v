(** [Inject A val] for the generic language [gen_prob_lang].  A verbatim copy of
    [clutch.common.inject] retargeted at [gen_prob_lang]'s [val]/[expr]
    (signature-independent), so that case studies which represent data as values
    via [inject]/[$] port unchanged. *)
From clutch.gen_prob_lang Require Import lang notation.
From clutch.prelude Require Import base.
Set Default Proof Using "Type*".

Section inject.
Class Inject (A B : Type) := {
  inject : A → B;
  inject_inj : Inj (=) (=) inject;
}.

Notation "$ x" := (inject x) (at level 8).
#[global] Existing Instance inject_inj.

#[global] Program Instance Inject_option `{!Inject T val} : Inject (option T) val :=
  {| inject := λ o, if o is Some t then SOMEV $t else NONEV |}.
Next Obligation. auto. Qed.
Next Obligation.
  intros ? [] [] [] [=]; [|done]. f_equal. by eapply (inj _).
Qed.

#[global] Program Instance Inject_prod `{!Inject A val, !Inject B val} :
  Inject (A * B) val := {| inject := (λ '(t1, t2), PairV $t1 $t2) |}.
Next Obligation. intros ? [] ? [] [] [] [=]. f_equal; by apply (inj _). Qed.

#[global] Program Instance Inject_sum `{!Inject A val, !Inject B val} : Inject (A + B) val
  := {| inject := λ s, match s with
                       | inl v => InjLV $v
                       | inr v => InjRV $v
                       end |}.
Next Obligation. by intros ? [] ? [] [] [] [= ->%(inj _)]. Qed.

#[global] Program Instance : Inject Z val := {| inject := LitV ∘ LitInt |}.
Next Obligation. by intros ?? [=]. Qed.

#[global] Program Instance : Inject nat val := {| inject := inject ∘ Z.of_nat |}.

(** A [fin M] injects via its underlying [nat] index; the codomain [val] carries
    the range bound [M] (and stays inhabited when [M ≥ 1]).  Injectivity is just
    [Z.of_nat] + [fin_to_nat] injectivity — no proof-irrelevance axiom. *)
#[global] Program Instance Inject_fin (M : nat) : Inject (fin M) val :=
  {| inject := λ k, #(Z.of_nat (fin_to_nat k)) |}.
Next Obligation. intros M k1 k2 [= H%Nat2Z.inj%fin_to_nat_inj]. exact H. Qed.

#[global] Program Instance : Inject bool val := {| inject := LitV ∘ LitBool |}.
Next Obligation. by intros ?? [=]. Qed.

#[global] Program Instance : Inject unit val := {| inject := λ _, #() |}.
Next Obligation. by intros [] []. Qed.

#[global] Program Instance : Inject loc val := {| inject := LitV ∘ LitLoc |}.
Next Obligation. by intros ?? [=]. Qed.

#[global] Program Instance Inject_expr `{!Inject A val} : Inject A expr :=
  {| inject := Val ∘ inject |}.

#[global] Program Instance : Inject val val := {| inject := λ v, v |}.

Fixpoint inject_list `{!Inject A val} (xs : list A) :=
  match xs with
  | [] => NONEV
  | x :: xs' => SOMEV ((inject x), inject_list xs')
  end.

#[global] Program Instance Inject_list `{!Inject A val} : Inject (list A) val :=
  {| inject := inject_list |}.
Next Obligation.
  intros ? [] xs. induction xs as [|x xs IH]; simpl.
  - intros []; by inversion 1.
  - intros []; [by inversion 1|].
    inversion 1 as [H'].
    f_equal; [by apply (inj _)|].
    by apply IH.
Qed.
End inject.
