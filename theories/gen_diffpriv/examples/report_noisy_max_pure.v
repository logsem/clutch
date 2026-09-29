(** Noise-INDEPENDENT pure lemmas for report-noisy-max: the [list_Z_max] /
    argmax theory and the [dZ] sensitivity helpers.  Shared by the generic
    library and every per-noise instantiation (extracted from the original
    report_noisy_max_lemmas so the generic library and the thin instantiations
    do not form an import cycle). *)
From discprob.basic Require Import seq_ext.
From stdpp Require Import list.
From clutch.prelude Require Import tactics.
From clutch.gen_prob_lang Require Import erasure gwp.list.
From clutch.prob Require Import couplings_dp differential_privacy.
From clutch.gen_diffpriv Require Import all.

Set Default Proof Using "Type".

Lemma dZ_bounded_cases' x y k : (- k <= x - y ∧ x - y <= k)%Z -> (dZ x y <= (IZR k))%R.
Proof.
  rewrite /dZ/distance Rabs_Zabs. intros h. apply IZR_le. lia. 
Qed.

(** list_Z_max *)
(* x is index we are recursing
   a is prev largest value
   i is index of prev largest value
*)
Fixpoint list_Z_max' l x a i:=
  match l with
  | [] => i
  | z::zs => if bool_decide (z > a)%Z
           then list_Z_max' zs (x+1)%nat z x
           else list_Z_max' zs (x+1)%nat a i
  end.

Definition list_Z_max l :=
  match l with
  | [] => 0%nat
  | x::xs => (list_Z_max' (x::xs) 0%nat x 0%nat)
  end.

Lemma list_Z_max_cons hd tl x a i:
  list_Z_max' (hd::tl) x a i =
  if bool_decide (hd>a)%Z then
    list_Z_max' tl (x+1) hd x
  else list_Z_max' tl (x+1)%nat a i.
Proof. done. Qed. 

Lemma list_max_index_eq xs : List_max_index xs = list_Z_max xs.
Proof.
  rewrite /List_max_index /list_Z_max.
  destruct xs as [|xmax xs] => //.
  rewrite /List_max_index_aux.
  simpl.
  intros. rewrite bool_decide_eq_false_2 //. 2: lia.
  generalize 1%nat at 3 4 as inext. generalize 0%nat at 3 4 as imax.
  revert xmax.
  induction xs as [|x xs].
  1: { simpl. done. }
  intros.
  simpl.
  case_bool_decide ; destruct ((xmax <? x)%Z) eqn:hlt => //.
  - apply Z.ltb_ge in hlt. lia.
  - apply Z.ltb_lt in hlt. lia.
Qed.
  
Lemma pw_list_Z_max_bound l x a i:
  i<= x -> 
  i=list_Z_max' l x a i \/ x <= list_Z_max' l x a i.
Proof.
  revert x a i.
  induction l; first naive_solver.
  simpl.
  intros x a0 i ?.
  case_bool_decide.
  - unshelve epose proof IHl (x+1) a x _; first lia.
    destruct!/=; right; lia.
  - unshelve epose proof IHl (x+1) a0 i _; first lia.
    destruct!/=; lia.
Qed.

Lemma pw_list_Z_max_bound' l x a i:
  i<x ->
  list_Z_max' l x a i < (x + length l).
Proof.
  revert x a i.
  induction l as [|hd tl IHl].
  - simpl. intros. lia.
  - simpl.
    intros. 
    case_bool_decide.
    + eapply Nat.lt_le_trans; first apply IHl; lia.
    + eapply Nat.lt_le_trans; first apply IHl; lia.
Qed.

Lemma list_Z_max_bound l:
  0<length l->
  list_Z_max l < length l.
Proof.
  intros.
  destruct l as [|z l]; first (simpl in *; lia).
  rewrite /list_Z_max.
  simpl.
  rewrite bool_decide_eq_false_2; last lia.
  eapply Nat.lt_le_trans; first apply pw_list_Z_max_bound'; lia.
Qed.   

Lemma pw_list_Z_max_after (Δ : Z) l l' x j a a' i i':
  i<= x->
  i'<=x ->
  length l = length l' ->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= IZR Δ)%R) ->
  (i=j -> a+Δ=a' /\ i = i')%Z ->
  (dZ a a' <= IZR Δ)%R ->
  x>j ->
  list_Z_max' l x a i = j ->
  list_Z_max' l' x a' i' = j.
Proof.
  revert l' x j a a' i i'.
  induction l as [|z]; first (intros []; naive_solver).
  intros [|z' ]; first naive_solver.
  intros x j a a' i i' Hineq Hineq' Hlen H H1 H2 H3 H4.
  simpl. simpl in *.
  case_bool_decide.
  { unshelve epose proof pw_list_Z_max_bound l (x+1) z x _; lia. }
  apply dZ_bounded_cases in H2 as H5.
  case_bool_decide.
  - unshelve epose proof pw_list_Z_max_bound l (x+1) a i _ as H7; first lia.
    destruct!/=; last lia.
    exfalso.
    apply H1 in H7.
    subst.
    unshelve epose proof H (z, z') _ as H4; first (rewrite elem_of_cons; naive_solver).
    apply dZ_bounded_cases in H4. simpl in *. lia.
  - eapply IHl; last first; try done; try lia.
    intros.
    apply H.
    rewrite elem_of_cons. naive_solver.
Qed.

Lemma pw_list_Z_max_current (Δ : Z) l l' j a a' i i' z z':
  i<= j->
  i'<=j ->
  length l = length l' ->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= IZR Δ)%R) ->
  (z+Δ=z')%Z ->
  (i=j -> a+Δ=a' /\ i=i')%Z ->
  (dZ a a' <= IZR Δ)%R ->
  list_Z_max' (z::l) j a i = j ->
  list_Z_max' (z'::l') j a' i' = j.
Proof.
  intros H1 H1' H2 H3 H4 H5 H6. subst.
  apply dZ_bounded_cases in H6 as H7.
  simpl.
  intros H.
  case_bool_decide.
  - rewrite bool_decide_eq_true_2; last lia.
    eapply pw_list_Z_max_after; last first; try done; try lia.
    apply dZ_bounded_cases'. lia.
  - case_bool_decide.
    + rewrite Nat.le_lteq in H1. destruct H1 as []; last first.
      * unshelve epose proof H5 _; lia.
      * unshelve epose proof pw_list_Z_max_bound l (j+1) a i _ as H8; first lia.
        destruct H8; last lia.
        assert (i=j) as -> by congruence.
        lia.
    + eapply pw_list_Z_max_after; last first; try done; lia.
Qed. 

Lemma pw_list_Z_max_before (Δ : Z) l l' i i' x z a a' j:
  i<= x->
  (i'<=j)%nat ->
  (x<=j) ->
  length l = length l' ->
  (l!!(j-x)=Some z) ->
  (l'!!(j-x)=Some (z+Δ)%Z)->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= IZR Δ)%R) ->
  (i=j -> a+Δ=a'/\i'=j)%Z ->
  (dZ a a' <= IZR Δ)%R ->
  list_Z_max' (l) x a i = j ->
  list_Z_max' (l') x a' i' = j.
Proof.
  revert l' i i' x z a a' j.
  induction l as [|hd tl IHl]; first (by intros []).
  intros [|hd' tl']; first done.
  intros i i' x z a a' j H1 H1' H2 H3 H4 H5 H6 H7 H8 H9.
  rewrite Nat.le_lteq in H2.
  destruct H2 as [|<-]; last first.
  { eapply pw_list_Z_max_current; last done; try done.
    - by simplify_eq.
    - intros. apply H6.
      simpl.
      rewrite elem_of_cons. naive_solver.
    - rewrite Nat.sub_diag in H5 H4.
      simpl in *. by simplify_eq.
    - intros. naive_solver.
  }
  simpl in *.
  case_bool_decide.
  { unshelve epose proof pw_list_Z_max_bound tl (x+1) hd x _ as H10; first lia.
    destruct H10; first lia.
    case_bool_decide.
    - eapply IHl; last done; try done; try lia.
      + rewrite lookup_cons_Some in H4.
        rewrite Nat.sub_add_distr.
        destruct H4; first lia.
        naive_solver.
      + rewrite lookup_cons_Some in H5.
        rewrite Nat.sub_add_distr.
        destruct H5; first lia.
        naive_solver.
      + intros.
        apply H6. rewrite elem_of_cons; naive_solver.
      + unshelve epose proof H6 (hd, hd') _; last done.
        rewrite elem_of_cons. naive_solver.
    - eapply IHl; last done; last first; try done; try lia.
      + unshelve epose proof H6 (hd, hd') _ as H11; first (rewrite elem_of_cons; naive_solver).
        simpl in *.
        apply dZ_bounded_cases in H8, H11.
        apply dZ_bounded_cases'. lia.
      + intros.
        apply H6. rewrite elem_of_cons; naive_solver.
      + rewrite lookup_cons_Some in H5.
        rewrite Nat.sub_add_distr.
        destruct H5; first lia.
        naive_solver.
      + rewrite lookup_cons_Some in H4.
        rewrite Nat.sub_add_distr.
        destruct H4; first lia.
        naive_solver.
  }
  case_bool_decide.
  - eapply IHl; last done; try lia.
    + rewrite lookup_cons_Some in H4.
      rewrite Nat.sub_add_distr.
      destruct H4; first lia.
      naive_solver.
    + rewrite lookup_cons_Some in H5.
      rewrite Nat.sub_add_distr.
      destruct H5; first lia.
      naive_solver.
    + intros.
      apply H6. rewrite elem_of_cons; naive_solver.
    + unshelve epose proof H6 (hd, hd') _ as H11; first (rewrite elem_of_cons; naive_solver).
        simpl in *.
        apply dZ_bounded_cases in H8, H11.
        apply dZ_bounded_cases'. lia.
  - eapply IHl; last done; try lia.
    + rewrite lookup_cons_Some in H4.
      rewrite Nat.sub_add_distr.
      destruct H4; first lia.
      naive_solver.
    + rewrite lookup_cons_Some in H5.
      rewrite Nat.sub_add_distr.
      destruct H5; first lia.
      naive_solver.
    + intros.
      apply H6. rewrite elem_of_cons; naive_solver.
    + unshelve epose proof H6 (hd, hd') _ as H11; first (rewrite elem_of_cons; naive_solver).
        simpl in *.
        apply dZ_bounded_cases in H8, H11.
        apply dZ_bounded_cases'. lia.
Qed. 
  
  
Lemma pw_list_Z_max_correct (Δ : Z) l l' z (j:nat):
  length l > 0 ->
  length l = length l' ->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= IZR Δ)%R) ->
  (l!!(j)=Some z) ->
  (l'!!(j)=Some (z+Δ)%Z)->
  list_Z_max l = j ->
  list_Z_max l' = j.
Proof.
  destruct l; first (simpl; lia).
  destruct l'; first done.
  rewrite /list_Z_max.
  intros H1 H2 H3 H4 H5 H6.
  eapply pw_list_Z_max_before; last done; try done; try lia.
  - by rewrite Nat.sub_0_r. 
  - by rewrite Nat.sub_0_r.
  - intros H. subst.
    split; last done.
    rewrite -H in H5, H4.
    simpl in *. by simplify_eq.
  - unshelve epose proof H3 (_,_) _ as K; last apply K.
    rewrite elem_of_cons. naive_solver.
Qed. 


(** Noise-independent rate-halving helper (used by every per-noise [*_map_pw]). *)
Lemma ineq_convert num den:
  (0 < IZR num / IZR (2 * den))%R ->
  (0 < IZR num / IZR (den))%R.
Proof.
  intros.
  rewrite mult_IZR in H.
  rewrite Rdiv_mult_distr in H. lra.
Qed.
