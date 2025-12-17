From stdpp Require Import finite list sets.
From clutch.prelude Require Import base classical fin.
From Stdlib.Program Require Import Equality.
Set Default Proof Using "Type*".

Section uniform_list.
  Context `{Hfinite: Finite A}.
  Fixpoint enum_uniform_list (p:nat):=
    match p with
    | O => [[]]
    | S p' =>
        x ← enum (A);
        y ← enum_uniform_list p';
        mret (x::y)
  end.

  Lemma enum_uniform_list_S (p:nat) :
    enum_uniform_list (S p) = 
        x ← enum A;
        y ← enum_uniform_list p;
  mret (x::y).
  Proof.
    simpl. done.
  Qed.

  Lemma elem_of_enum_uniform_list l p:
    l ∈ enum_uniform_list p <-> length l = p.
  Proof.
    split.
    - revert l; induction p; intros l.
      + simpl. rewrite elem_of_list_singleton. by intros ->.
      + rewrite enum_uniform_list_S. rewrite elem_of_list_bind. elim. intros x.
        rewrite elem_of_list_bind. do 2 elim. intros y.
        intros [?%elem_of_list_ret ?]. subst.
        simpl. intros. f_equal. naive_solver.
    - revert l; induction p; intros l.
      + simpl. set_unfold. intros ?%nil_length_inv. naive_solver.
      + destruct l as [|t l'] eqn:Heqn; first done.
        rewrite enum_uniform_list_S.
        intros ?.
        rewrite elem_of_list_bind. exists t.
        rewrite elem_of_list_bind. split; last apply elem_of_enum.
        exists l'. rewrite elem_of_list_ret. simplify_eq. naive_solver.
  Qed.

  Lemma elem_of_enum_uniform_list' l p:
    bool_decide (l∈enum_uniform_list p) = (length l =? p).
  Proof.
    case_bool_decide as H.
    all: rewrite elem_of_enum_uniform_list in H; subst.
    - by rewrite Nat.eqb_refl.
    - symmetry; by rewrite Nat.eqb_neq.
  Qed.

  Lemma bind_length1 (l:list (list A)) a:
    length (l ≫= λ y, mret (a :: y)) = length l.
  Proof.
    induction l.
    - done.
    - rewrite bind_cons.
      rewrite length_app. simpl. f_equal. done.
  Qed.
  
  Lemma bind_length2 (l1 : list A) l2:
    length (l1 ≫= λ x, l2 ≫= λ y, mret (x :: y)) = length l1 * length l2.
  Proof.
    revert l2.
    induction l1.
    - done.
    - intros l2.
      rewrite bind_cons. rewrite length_app.
      rewrite IHl1. rewrite bind_length1.
      simpl. lia.
  Qed.

  Lemma enum_uniform_list_length p:
    length (enum_uniform_list p) = (length (enum A))^p.
  Proof.
    induction p.
    - done.
    - rewrite enum_uniform_list_S.
      rewrite bind_length2.
      rewrite IHp.
      rewrite Nat.pow_succ_r'. lia.
  Qed.

  Lemma NoDup_enum_uniform_list p:
    NoDup (enum_uniform_list p).
  Proof.
    induction p.
    - simpl. apply NoDup_singleton.
    - rewrite enum_uniform_list_S.
      apply NoDup_bind; last apply NoDup_enum.
      + move => ????? /elem_of_list_bind [? [H1 ?]] /elem_of_list_bind[?[ H2?]].
        apply elem_of_list_ret in H1, H2. by simplify_eq.
      + intros ??.
        apply NoDup_bind; last done.
        * intros ????? ?%elem_of_list_ret ?%elem_of_list_ret. by simplify_eq.
        * intros. rewrite /mret/list_ret. apply NoDup_singleton.
  Qed.  

End uniform_list.


Section uniform_fin_list.
  Variables N:nat.
  
  Definition enum_uniform_fin_list:=
    enum_uniform_list (A:=fin (S N)).

  Lemma enum_uniform_fin_list_S (p:nat) :
    enum_uniform_fin_list (S p) = 
        x ← enum (fin (S N));
        y ← enum_uniform_fin_list p;
  mret (x::y).
  Proof.
    simpl. done.
  Qed.

  Lemma elem_of_enum_uniform_fin_list l p:
    l ∈ enum_uniform_fin_list p <-> length l = p.
  Proof.
    apply elem_of_enum_uniform_list.
  Qed.
  
  Lemma elem_of_enum_uniform_fin_list' l p:
    bool_decide (l∈enum_uniform_fin_list p) = (length l =? p).
  Proof.
    apply elem_of_enum_uniform_list'.
  Qed.
  
  Lemma enum_uniform_fin_list_length p:
    length (enum_uniform_fin_list p) = (S N)^p.
  Proof.
    by rewrite enum_uniform_list_length length_enum_fin.
  Qed.
  
  Lemma NoDup_enum_uniform_fin_list p:
    NoDup (enum_uniform_fin_list p).
  Proof.
    apply NoDup_enum_uniform_list.
  Qed.
End uniform_fin_list.
