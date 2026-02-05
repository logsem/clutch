From discprob.basic Require Import seq_ext.
From stdpp Require Import list.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import couplings_dp.
From clutch.diffpriv Require Import distance.

Set Default Proof Using "Type".

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
  | [] => 0%Z
  | x::xs => (list_Z_max' (x::xs) 0%nat x 0%nat)
  end.

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

Lemma pw_list_Z_max_after l l' x j a a' i:
  i<= x->
  length l = length l' ->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= 1)%R) ->
  (i=j -> a+1=a')%Z ->
  (dZ a a' <=1)%R ->
  x>j ->
  list_Z_max' l x a i = j ->
  list_Z_max' l' x a' i = j.
Proof.
  revert l' x j a a' i.
  induction l as [|z]; first (intros []; naive_solver).
  intros [|z' ]; first naive_solver.
  intros x j a a' i Hineq Hlen H H1 H2 H3 H4.
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
  - eapply IHl; try done; try lia.
    intros.
    apply H.
    rewrite elem_of_cons. naive_solver.
Qed.

Lemma pw_list_Z_max_current l l' j a a' i z z':
  i<= j->
  length l = length l' ->
  (∀ p, p ∈ zip_with (λ x y, (x,y)) l l' -> (dZ p.1 p.2 <= 1)%R) ->
  (z+1=z')%Z ->
  (i=j -> a+1=a')%Z ->
  (dZ a a' <=1)%R ->
  list_Z_max' (z::l) j a i = j ->
  list_Z_max' (z'::l') j a' i = j.
Proof.
  intros H1 H2 H3 H4 H5 H6. subst.
  apply dZ_bounded_cases in H6 as H7.
  simpl. 
  intros H.
  case_bool_decide.
  - rewrite bool_decide_eq_true_2; last lia.
    eapply pw_list_Z_max_after; last first; try done; try lia.
    rewrite /dZ/=.
    replace (_-_)%Z with (-1)%Z by lia.
    by rewrite Rabs_Ropp Rabs_R1.
  - case_bool_decide.
    + rewrite Nat.le_lteq in H1. destruct H1 as []; last first.
      * unshelve epose proof H5 _; lia.
      * unshelve epose proof pw_list_Z_max_bound l (j+1) a i _ as H8; first lia.
        destruct H8; last lia.
        assert (i=j) as -> by congruence.
        lia.
    + eapply pw_list_Z_max_after; last first; try done; lia.
Qed. 





(* Definition list_Z_max l := *)
(*   match l with *)
(*   | [] => 0%Z *)
(*   | x::xs => fold_left Z.max (x::xs) x *)
(*   end. *)

(* Lemma Zmax_rewrite x y: *)
(*   Z.max x y=if bool_decide (y>x)%Z then y else x. *)
(* Proof. *)
(*   case_bool_decide. *)
(*   - rewrite Z.max_r; lia. *)
(*   - rewrite Z.max_l; lia. *)
(* Qed.  *)

(* Lemma list_Z_max_witness' l x: *)
(*   fold_left Z.max l x = x \/ In (fold_left Z.max l x) l . *)
(* Proof. *)
(*   revert x. *)
(*   induction l as [|a ? IHl]; first naive_solver. *)
(*   simpl. *)
(*   intros x. *)
(*   rewrite (Zmax_rewrite). *)
(*   case_bool_decide. *)
(*   - pose proof IHl a. *)
(*     naive_solver. *)
(*   - pose proof IHl x. naive_solver. *)
(* Qed. *)

(* Lemma list_Z_max_witness l: *)
(*   (0<length l)%Z -> *)
(*   In (list_Z_max l) l. *)
(* Proof. *)
(*   intros H. *)
(*   destruct l as [|z]; first (simpl in *; lia). *)
(*   simpl. *)
(*   pose proof list_Z_max_witness' l z. *)
(*   rewrite Zmax_rewrite. case_bool_decide; naive_solver. *)
(* Qed. *)

(* Lemma list_Z_max_bound' x l: *)
(*   (x<=fold_left Z.max l x /\ (∀ y, In y l -> y <= fold_left Z.max l y))%Z. *)
(* Proof. *)
(*   revert x. *)
(*   induction l as [|?? IHl]; first naive_solver. *)
(*   intros x. *)
(*   simpl. *)
(*   rewrite Zmax_rewrite. *)
(*   case_bool_decide. *)
(*   - pose proof IHl a. *)
(*     destruct!/=. *)
(*     split; first lia. *)
(*     intros. *)
(*     destruct!/=. *)
(*     + rewrite Zmax_rewrite. *)
(*       rewrite bool_decide_eq_false_2; [done|lia]. *)
(*     + rewrite Zmax_rewrite. *)
(*       case_bool_decide. *)
(*       * admit. *)
(*       * naive_solver. *)
(*   - pose proof IHl x. *)
(*     destruct!/=. *)
(*     split; first naive_solver. *)
(*     intros. destruct!/=. *)
(*     + rewrite Zmax_rewrite. *)
(*       rewrite bool_decide_eq_false_2; last lia. *)
(*       naive_solver. *)
(*     + admit. *)
(* Admitted. *)
    

(* Fixpoint max_index' (l: list Z) (j:nat) (prev: Z) (ans : nat):= *)
(*   match l with *)
(*   | [] => ans%nat *)
(*   | x :: xs => if bool_decide (prev < x)%Z *)
(*              then max_index' xs (j+1)%nat x j *)
(*              else max_index' xs (j+1)%nat prev ans *)
(*   end. *)
               
(* Definition max_index l := *)
(*   match l with *)
(*   | [] => 0%nat *)
(*   | x :: xs => max_index' xs 1%nat x 0%nat *)
(*   end. *)

(* Lemma max_index_range l: *)
(*   0< length l -> *)
(*   (max_index l< length l). *)
(* Proof. *)
(*   intros Hl. *)
(*   destruct l as [|x xs]; first (simpl in *; lia). *)
(*   clear Hl. *)
(*   simpl. *)
(*   assert (∀ xs j a ans, *)
(*             ans<j+length xs -> *)
(*             max_index' xs j a ans < j+length xs *)
(*          ). *)
(*   { clear. *)
(*     intros xs. *)
(*     induction xs as [|? ? IHxs]; first naive_solver. *)
(*     simpl. *)
(*     intros. *)
(*     case_bool_decide. *)
(*     + eapply Nat.lt_le_trans; first apply IHxs; lia. *)
(*     + eapply Nat.lt_le_trans; first apply IHxs; lia. *)
(*   } *)
(*   apply H. lia. *)
(* Qed.  *)

(* Lemma max_index_correct l z_large: *)
(*   (0<length l)%nat -> *)
(*   (l!!max_index l = Some z_large) ->  *)
(*   (∀ i z, l!!i=Some z -> *)
(*           (i<max_index l /\ (z<z_large)%Z) *)
(*           \/ (max_index l <=i /\ (z<=z_large)%Z)  *)
(*   ). *)
(* Proof. *)
(*   intros Hl. *)
(* Admitted.  *)
  

  

