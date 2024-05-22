From stdpp Require Import vector finite.
From clutch.prelude Require Import base classical.
Require Import Coq.Program.Equality.
Set Default Proof Using "Type*".

Section vector.
  Lemma vec_to_list_VectorDef_to_list {A N} (v:vec A N):
    vec_to_list v = VectorDef.to_list v.
  Proof.
    induction v.
    - simpl. rewrite VectorSpec.to_list_nil. done.
    - simpl. rewrite IHv. rewrite Vector.to_list_cons. done.
  Qed. 

  Lemma vec_eta {A N} (v: vec A (S N)) x:
    vec_to_list v = vec_to_list (Vector.shiftout v) ++ [List.last (VectorDef.to_list v) x].
  Proof.
    dependent destruction v.
    revert h x.
    induction v.
    - by simpl.
    - intros h' x.
      rewrite vec_to_list_cons.
      erewrite IHv.
      f_equal.
  Qed.

  Lemma vec_shiftout {A N} (v:vec A (S N)) (v': vec A N) a:
    vec_to_list (v' +++ list_to_vec [a]) = vec_to_list v -> 
    vec_to_list v' = vec_to_list (Vector.shiftout v).
  Proof.
    dependent destruction v.
    revert v' a h.
    induction v.
    - intros.
      simpl in H.
      pose proof Vector.nil_spec v'. subst. simpl in H. 
      simpl. done.
    - intros v' a h' H.
      dependent destruction v'.
      rewrite -Vector.append_comm_cons in H.
      simpl in H.
      rewrite vec_to_list_cons.
      simplify_eq.
      erewrite (IHv _ a h); last first.
      { simpl. done. }
      done.
  Qed. 
    
End vector.

