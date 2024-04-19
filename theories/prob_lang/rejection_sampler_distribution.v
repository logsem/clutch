From Coq Require Import Reals Psatz.
From stdpp Require Export binders strings.
From stdpp Require Import gmap fin_maps countable fin.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.prob Require Export distribution.
From clutch.common Require Export language ectx_language ectxi_language.
From clutch.prob_lang Require Export locations lang.
From iris.prelude Require Import options.

Set Default Proof Using "Type*".
Local Open Scope R.

Section rejection_sampler_distr.
  Fixpoint rej_samp_distr_f (N:nat) (s:gset nat) (l:list nat) :=
    match l with
    | [] => 0
    | x::xs => if bool_decide(xs = [])
             then (if bool_decide(x ∈ s) then size (s)/N else 0)
             else (if bool_decide(x ∈ s) then 0 else (N-size s)/N*rej_samp_distr_f N s xs)
    end.
  
  Definition rej_samp_state_f (σ:state) (α:loc) (N:nat) s  (σ':state):=
    if (bool_decide (α ∈ dom (σ.(tapes)))) then
     let: (N1; ns) := (σ.(tapes)!!!α) in
     let: (N2; ns') := (σ'.(tapes)!!!α) in
     if (bool_decide (N=N1 /\ N1=N2 /\ prefix (fin_to_nat <$> ns) (fin_to_nat <$> ns')))
     then rej_samp_distr_f N s (fin_to_nat <$> (drop (length ns) ns'))
     else 0
    else 0.

  Program Definition rej_samp_state_distr
    (N : nat) (s:gset nat) σ α
    (_:size s < N) (_:∀ x:nat, x ∈ s -> x <N) : distr state :=
    MkDistr (rej_samp_state_f σ α N s) _ _ _.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.


  
    
End rejection_sampler_distr.
