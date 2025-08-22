From clutch.foxtrot Require Import foxtrot.

(* The bias here is p/(q+1)*)
Definition toss (p q: nat) (e1 e2 :expr): expr :=
    if: rand #q<#p
    then e1
    else e2.

Definition toss' α (p q: nat) (e1 e2 :expr): expr :=
    if: rand(#lbl:α) #q<#p
    then e1
    else e2.
