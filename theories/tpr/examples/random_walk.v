From Coq Require Import Reals Psatz.
From Coq.Reals Require Import Rfunctions. 
From Coquelicot Require Import Lim_seq Rbar Hierarchy.
From clutch.prob Require Import distribution.
From clutch.prob Require Import markov.


Module random_walk.

  Definition step (b : bool) :=
    if b then fair_coin else dzero.

  Definition to_final (b : bool) : option bool :=
    if b then None else Some false.

  Local Existing Instance finite_countable | 0.
  Program Instance random_walk : markov bool bool := Markov bool bool _ _ step to_final _.
  Next Obligation. by intros [] [] []; simplify_eq=>/=. Qed.

  Lemma exec_random_walk n :
    SeriesC (exec n true) = 1 - (1/2)^n.
  Proof.
    induction n.
    { rewrite Rminus_eq_0 /= dzero_mass //. }
    rewrite exec_Sn_not_final; [|by eapply to_final_None].
    rewrite /markov.step /=.
    rewrite fair_coin_dbind_mass.
    rewrite IHn.
    erewrite exec_is_final; [|done].
    rewrite dret_mass.
    lra.
  Qed.
  
  Lemma random_walk_terminates :
    SeriesC (lim_exec true) = 1.
  Proof.
    apply (MCT_seriesC _ (λ n, SeriesC (exec n true))); last first. 
   - eapply is_sup_seq_ext. 
     { intros n. rewrite exec_random_walk //. }     
     rewrite /is_sup_seq /=. 
     intros ϵ.
     split.
     + intros n; simpl. 
       transitivity 1%R.
       * apply Rminus_gt_0_lt.         
         assert (1 - (1 - (1 / 2) ^ n) = (1 / 2) ^ n) as -> by lra.         
         apply pow_lt. lra.
       * rewrite -{1}(Rplus_0_r 1). 
         apply Rplus_lt_compat_l, cond_pos.
     + assert (∃ n, (1 / 2) ^ n < ϵ) as [n Hn].
       { case: (pow_lt_1_zero (1/2) _ ϵ (cond_pos ϵ)).
         { apply Rabs_def1; lra. }
         intros n Hn. exists n.
         specialize (Hn n (Nat.le_refl _)).         
         by apply Rabs_def2 in Hn as [? ?]. }
       exists n. lra. 
   - intros. by eapply SeriesC_correct.
   - eauto.
   - eapply exec_mono.
   - eauto. 
  Qed. 

End random_walk.

