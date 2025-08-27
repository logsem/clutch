From stdpp Require Import fin finite ssreflect.
From clutch.eris.lib.sampling.utils Require Export fintools.
#[local] Set Asymmetric Patterns.

Inductive fin_list (A : Type) : nat → Type :=
| fin_nil : fin_list A 0
| fin_cons {n : nat} : A → fin_list A n → fin_list A (S n).

Inductive triangle (A : Type) : nat → Type :=
| trig_nil : triangle A 0
| trig_snoc {n : nat} : triangle A n → fin_list A (S n) → triangle A (S n).

#[global] Arguments fin_nil {A}.
#[global] Arguments fin_cons {A} {n}.
#[global] Arguments trig_nil {A}.
#[global] Arguments trig_snoc {A} {n}.

Definition fin_list_0_inv
  {A : Type}
  (P : fin_list A 0 → Type)
  (H : P fin_nil)
  (l : fin_list A 0) : P l :=
  match l as l0 in (fin_list _ 0) return
        ∀ (P : fin_list A 0 → Type),
          P fin_nil →
          P l0
  with
  | fin_nil => λ P H, H 
  end P H.

Definition fin_list_S_inv
  {n : nat} {A : Type}
  (P : fin_list A (S n) → Type)
  (f : ∀ (a : A) (l : fin_list A n), P (fin_cons a l))
  (l : fin_list A (S n)) : P l :=
  match l as l0 in (fin_list _ (S n0)) return
        ∀ (P : fin_list A (S n0) → Type)
          (f : ∀ (a : A) (l : fin_list A n0), P (fin_cons a l)),
          P l0
  with
  | fin_cons n0 a l => λ P f, f a l
  end P f.

Definition triangle_0_inv
  {A : Type}
  (P : triangle A 0 → Type)
  (H : P trig_nil)
  (t : triangle A 0) : P t :=
  match t as t0 in (triangle _ 0) return
        ∀ (P : triangle A 0 → Type),
          P trig_nil →
          P t0
  with
  | trig_nil => λ P H, H 
  end P H.

Definition triangle_S_inv
  {n : nat} {A : Type}
  (P : triangle A (S n) → Type)
  (f : ∀ (t : triangle A n) (l : fin_list A (S n)), P (trig_snoc t l))
  (l : triangle A (S n)) : P l :=
  match l as l0 in (triangle _ (S n0)) return
        ∀ (P : triangle A (S n0) → Type)
          (f : ∀ (t : triangle A n0) (l : fin_list A (S n0)), P (trig_snoc t l)),
          P l0
  with
  | trig_snoc n0 t l => λ P f, f t l
  end P f.

Ltac inv_fin_list l :=
let T := type of l in
match eval hnf in T with
| fin_list _ ?n =>
  match eval hnf in n with
  | 0%nat =>
    generalize dependent l;
    match goal with |- ∀ l, @?P l => apply (fin_list_0_inv P) end
  | S ?n =>
    generalize dependent l;
    match goal with |- ∀ l, @?P l => apply (fin_list_S_inv P) end
  end
end.

Ltac inv_triangle t :=
let T := type of t in
match eval hnf in T with
| triangle _ ?n =>
  match eval hnf in n with
  | 0%nat =>
    generalize dependent t;
    match goal with |- ∀ t, @?P t => apply (triangle_0_inv P) end
  | S ?n =>
    generalize dependent t;
    match goal with |- ∀ t, @?P t => apply (triangle_S_inv P) end
  end
end.

Lemma triangle_0_nil : ∀ (A : Type) (τ : triangle A 0), τ = trig_nil.
Proof.
  move=>A τ.
  by inv_triangle τ.
Qed.

Definition fin_list_head {A : Type} {n : nat} : fin_list A (S n) → A :=
  fin_list_S_inv (const A) const.

Definition fin_list_tail {A : Type} {n : nat} : fin_list A (S n) → fin_list A n :=
  fin_list_S_inv (const (fin_list A n)) (flip const).

Lemma fin_list_cons_head_tail : ∀ {A : Type} {n : nat} (l : fin_list A (S n)),
  l = fin_cons (fin_list_head l) (fin_list_tail l).
Proof.
  move=>A n l.
  inv_fin_list l => a l //.
Qed.

Lemma fin_list_head_cons : ∀ {A : Type} {n : nat} (h : A) (t : fin_list A n),
  fin_list_head (fin_cons h t) = h.
Proof.
  trivial.
Qed.

Lemma fin_list_tail_cons : ∀ {A : Type} {n : nat} (h : A) (t : fin_list A n),
  fin_list_tail (fin_cons h t) = t.
Proof.
  trivial.
Qed.

Fixpoint fin_list_snoc {A : Type} {n : nat} : fin_list A n → A → fin_list A (S n) :=
  match n as n0 return fin_list A n0 → A → fin_list A (S n0) with
  | 0 => λ l a, fin_cons a l
  | S m => λ l a, fin_cons (fin_list_head l) (fin_list_snoc (fin_list_tail l) a)
                  

  end.

Fixpoint fin_list_last {A : Type} {n : nat} : fin_list A (S n) → A :=
  match n as n0 return fin_list A (S n0) → A with
  | 0 => fin_list_head
  | S m => fin_list_last ∘ fin_list_tail
  end.

Lemma fin_list_last_tail :
  ∀ {A : Type} {n : nat} (t : fin_list A (S (S n))),
  fin_list_last (fin_list_tail t) = fin_list_last t.
Proof.
  move=>A n t.
  inv_fin_list t => t l //.
Qed.

Fixpoint fin_list_liat {A : Type} {n : nat} : fin_list A (S n) → fin_list A n :=
  match n as n0 return fin_list A (S n0) → fin_list A n0 with
  | 0 => fin_list_tail
  | S m => λ l, fin_cons (fin_list_head l) (fin_list_liat (fin_list_tail l))
  end.

Lemma fin_list_snoc_liat_last :
  ∀ {A : Type} {n : nat} (l : fin_list A (S n)),
  l = fin_list_snoc (fin_list_liat l) (fin_list_last l).
Proof.
  move=>A.
  elim=>[|n IH] l; inv_fin_list l => a l //=.
  rewrite -IH //.
Qed.

Lemma fin_list_tail_snoc :
  ∀ {A : Type} {n : nat} (h : A) (t : fin_list A (S n)),
  fin_list_tail (fin_list_snoc t h) = fin_list_snoc (fin_list_tail t) h.
Proof.
  move=>A.
  elim=>[|n IH] h t; inv_fin_list t => //.
Qed.

Lemma fin_list_head_liat :
  ∀ {A : Type} {n : nat} (t : fin_list A (S (S n))),
  fin_list_head (fin_list_liat t) = fin_list_head t.
Proof.
  move=>* //.
Qed.
  
Lemma fin_list_last_snoc :
  ∀ {A : Type} {n : nat} (h : A) (t : fin_list A n),
  fin_list_last (fin_list_snoc t h) = h.
Proof.
  move=>A.
  elim=>[|n IH] h t; inv_fin_list t => //=.
Qed.

Lemma fin_list_last_cons_S :
  ∀ {A : Type} {n : nat} (h : A) (t : fin_list A (S n)),
  fin_list_last (fin_cons h t) = fin_list_last t.
Proof.
  move=>* //.
Qed.

Lemma fin_list_last_cons_0 :
  ∀ {A : Type} (h : A) (t : fin_list A 0),
  fin_list_last (fin_cons h t) = h.
Proof.
  move=>* //.
Qed.

Lemma fin_list_liat_snoc :
  ∀ {A : Type} {n : nat} (h : A) (t : fin_list A n),
  fin_list_liat (fin_list_snoc t h) = t.
Proof.
  move=>A.
  elim=>[|n IH] h t; inv_fin_list t => //=.
  move=>a l.
  rewrite IH //.
Qed.

Lemma fin_list_head_snoc : ∀ {A : Type} {n : nat} (h : A) (t : fin_list A (S n)),
  fin_list_head (fin_list_snoc t h) = fin_list_head t.
Proof.
  move=>A n h t.
  by inv_fin_list t.
Qed.

Lemma fin_list_liat_cons_S :
  ∀ {A : Type} {n : nat} (h : A) (t : fin_list A (S n)),
  fin_list_liat (fin_cons h t) = fin_cons h (fin_list_liat t).
Proof.
  move=>A.
  elim=>[|n IH] h t; inv_fin_list t => //=.
Qed.

Lemma fin_list_liat_cons_0 :
  ∀ {A : Type} (h : A) (t : fin_list A 0),
  fin_list_liat (fin_cons h t) = fin_nil.
Proof.
  move=>A h t /=.
  by inv_fin_list t.
Qed.


Lemma fin_list_cons_snoc :
  ∀ {A : Type} {n : nat} (h1 h2 : A) (t : fin_list A n),
  fin_cons h1 (fin_list_snoc t h2) = fin_list_snoc (fin_cons h1 t) h2.
Proof.
  move=>A n h1 h2 t //.
Qed.

Lemma fin_list_tail_liat :
  ∀ {A : Type} {n : nat} (l : fin_list A (S (S n))),
  fin_list_tail (fin_list_liat l) = fin_list_liat (fin_list_tail l).
Proof.
  move=>* //.
Qed.

#[global] Opaque fin_list_snoc fin_list_last fin_list_liat.

Fixpoint fin_list_get {A : Type} {n : nat} : fin_list A n → fin n → A :=
  match n as n0 return fin_list A n0 → fin n0 → A with
  | 0 => λ _, fin_0_inv _
  | S m => λ l i,
             fin_S_inv (const A) (fin_list_head l) (λ j, fin_list_get (fin_list_tail l) j) i
  end.

Fixpoint fin_list_set {A : Type} {n : nat} : fin_list A n → fin n → A → fin_list A n :=
   match n as n0 return fin_list A n0 → fin n0 → A → fin_list A n0 with
   | 0 => λ _, fin_0_inv _
   | S m => λ l i a, fin_S_inv (const (fin_list A (S m)))
                       (fin_cons a (fin_list_tail l))
                       (λ j, fin_cons (fin_list_head l) (fin_list_set (fin_list_tail l) j a)) i
   end.

Lemma fin_list_get_cons_0 :
  ∀ {A : Type} {n : nat} (l : fin_list A (S n)) (a : A),
  fin_list_get (fin_cons a l) 0%fin = a.
Proof.
  move=>* //.
Qed.

Lemma fin_list_get_cons_S :
  ∀ {A : Type} {n : nat} (l : fin_list A n) (a : A) (i : fin n),
  fin_list_get (fin_cons a l) (FS i)%fin = fin_list_get l i.
Proof.
  move=>* //.
Qed.

Lemma fin_list_set_0 :
  ∀ {A : Type} {n : nat} (l : fin_list A (S n)) (a : A),
  fin_list_set l 0%fin a = fin_cons a (fin_list_tail l).
Proof. reflexivity. Qed.

Lemma fin_list_get_0 :
  ∀ {A : Type} {n : nat} (l : fin_list A (S n)),
  fin_list_get l 0%fin = fin_list_head l. 
Proof. reflexivity. Qed.

Lemma fin_list_get_FS :
  ∀ {A : Type} {n : nat} (l : fin_list A (S n)) (i : fin n),
  fin_list_get l (FS i) = fin_list_get (fin_list_tail l) i.
Proof. reflexivity. Qed.

Lemma fin_list_set_FS :
  ∀ {A : Type} {n : nat} (l : fin_list A (S n)) (i : fin n) (a : A),
  fin_list_set l (FS i) a = fin_cons (fin_list_head l) (fin_list_set (fin_list_tail l) i a).
Proof. reflexivity. Qed.

Lemma fin_list_get_max :
  ∀ {A : Type} {n : nat} (l : fin_list A (S n)),
  fin_list_get l (fin_max n) = fin_list_last l. 
Proof.
  move=>A.
  elim=>[|n IH] l /=; first by inv_fin_list l.
  rewrite {3}(fin_list_cons_head_tail l) fin_list_last_cons_S -IH //.
Qed.

Lemma fin_list_set_max :
  ∀ {A : Type} {n : nat} (l : fin_list A (S n)) (a : A),
  fin_list_set l (fin_max n) a = fin_list_snoc (fin_list_liat l) a. 
Proof.
  move=>A.
  elim=>[|n IH] l a /=; first by inv_fin_list l.
  rewrite {5}(fin_list_cons_head_tail l) fin_list_liat_cons_S -fin_list_cons_snoc -IH //.
Qed.

Lemma fin_list_get_set_eq :
  ∀ {A : Type} {n : nat} (l : fin_list A n) (i : fin n) (a : A),
  fin_list_get (fin_list_set l i a) i = a.
Proof.
  move=>A.
  elim=>[|n IH] l i a; inv_fin i => [|i]; inv_fin_list l => //=.
Qed.

Lemma fin_list_get_set_ne :
  ∀ {A : Type} {n : nat} (l : fin_list A n) (i j : fin n) (a : A),
  i ≠ j →
  fin_list_get (fin_list_set l i a) j = fin_list_get l j.
Proof.
  move=>A.
  elim=>[|n IH] l i j; inv_fin i => [|i] a i_ne_j; inv_fin j=>[|j] Si_ne_Sj //=.
  apply IH.
  move=> contra.
  by subst.
Qed.

Lemma fin_list_set_get :
  ∀ {A : Type} {n : nat} (l : fin_list A n) (i : fin n),
  fin_list_set l i (fin_list_get l i) = l.
Proof.
  move=>A.
  elim=>[|n IH] l i ; inv_fin i => [|i]; inv_fin_list l => //= a l.
  rewrite IH //.
Qed.

Lemma fin_list_get_inj :
  ∀ {A : Type} {n : nat} (l : fin_list A (S n)) (i : fin n),
  fin_list_get l (fin_S_inj i) = fin_list_get (fin_list_liat l) i.
Proof.
  move=>A.
  elim=>[|n IH] l i; inv_fin i.
  - inv_fin_list l => a l //.
  - move=>i /=.
    rewrite -IH //.
Qed.

Lemma fin_list_set_inj :
  ∀ {A : Type} {n : nat} (l : fin_list A (S n)) (i : fin n) (a : A),
  fin_list_set l (fin_S_inj i) a = fin_list_snoc (fin_list_set (fin_list_liat l) i a) (fin_list_last l).
Proof.
  move=>A.
  elim=>[|n IH] l i a; inv_fin i.
  - inv_fin_list l => i l /=.
    rewrite -fin_list_cons_snoc -fin_list_snoc_liat_last //.
  - move=>i /=.
    rewrite -fin_list_cons_snoc fin_list_head_liat -IH //.
Qed.

Definition triangle_tail
  {A : Type} {n : nat} (t : triangle A (S n)) : fin_list A (S n) :=
  triangle_S_inv (const (fin_list A (S n))) (λ _ l, l) t.

Definition triangle_head
  {A : Type} {n : nat} (t : triangle A (S n)) : triangle A n :=
  triangle_S_inv (const (triangle A n)) (λ h _, h) t.

Lemma triangle_snoc_head_tail {A : Type} {n : nat} (t : triangle A (S n)) :
  t = trig_snoc (triangle_head t) (triangle_tail t).
Proof. by inv_triangle t. Qed.

Fixpoint triangle_top {A : Type} {n : nat} : triangle A n → fin_list A n :=
  match n as n0 return triangle A n0 → fin_list A n0 with
  | 0 => const fin_nil
  | S m => λ t,
             fin_list_snoc
               (triangle_top (triangle_head t))
               (fin_list_head (triangle_tail t))
  end.

Fixpoint triangle_bottom {A : Type} {n : nat} : triangle A n → fin_list A n :=
  match n as n0 return triangle A n0 → fin_list A n0 with
  | 0 => const fin_nil
  | S m => λ t,
             fin_list_snoc
               (triangle_bottom (triangle_head t))
               (fin_list_last (triangle_tail t))
  end.

Fixpoint triangle_glue_top {A : Type} {n : nat} : triangle A n → fin_list A (S n) → triangle A (S n) :=
  match n as n0 return triangle A n0 → fin_list A (S n0) → triangle A (S n0) with
  | 0 => trig_snoc
  | S m => λ t l, trig_snoc
                    (triangle_glue_top (triangle_head t) (fin_list_liat l))
                    (fin_cons (fin_list_last l) (triangle_tail t))
  end.

Fixpoint triangle_glue_bottom {A : Type} {n : nat} : triangle A n → fin_list A (S n) → triangle A (S n) :=
  match n as n0 return triangle A n0 → fin_list A (S n0) → triangle A (S n0) with
  | 0 => trig_snoc
  | S m => λ t l, trig_snoc
                    (triangle_glue_bottom (triangle_head t) (fin_list_liat l))
                    (fin_list_snoc (triangle_tail t) (fin_list_last l))
  end.

Fixpoint triangle_remove_top {A : Type} {n : nat} : triangle A (S n) → triangle A n :=
  match n as n0 return triangle A (S n0) → triangle A n0 with
  | 0 => const trig_nil
  | S m => λ t,
             trig_snoc
               (triangle_remove_top (triangle_head t))
               (fin_list_tail (triangle_tail t))
  end.

Fixpoint triangle_remove_bottom {A : Type} {n : nat} : triangle A (S n) → triangle A n :=
  match n as n0 return triangle A (S n0) → triangle A n0 with
  | 0 => const trig_nil
  | S m => λ t,
             trig_snoc
               (triangle_remove_bottom (triangle_head t))
               (fin_list_liat (triangle_tail t))
  end.

Lemma triangle_remove_top_0 :
  ∀ {A : Type} (τ : triangle A 1), triangle_remove_top τ = trig_nil.
Proof.
  move=>A τ.
  inv_triangle τ => τ l //.
Qed.

Lemma triangle_remove_bottom_0 :
  ∀ {A : Type} (τ : triangle A 1), triangle_remove_bottom τ = trig_nil.
Proof.
  move=>A τ.
  inv_triangle τ => τ l //.
Qed.

Lemma triangle_glue_remove_top :
  ∀ {A : Type} {n : nat} (t : triangle A (S n)),
  t = triangle_glue_top (triangle_remove_top t) (triangle_top t).
Proof.
  move=>A.
  elim=>[|n IH] t; inv_triangle t => t l.
  - inv_triangle t.
    inv_fin_list l => a l.
    by inv_fin_list l.
  - inv_triangle t => t l' /=.
    rewrite fin_list_liat_snoc -IH fin_list_last_snoc
            -fin_list_cons_head_tail //.
Qed.

Lemma triangle_glue_remove_bottom :
  ∀ {A : Type} {n : nat} (t : triangle A (S n)),
  t = triangle_glue_bottom (triangle_remove_bottom t) (triangle_bottom t).
Proof.
  move=>A.
  elim=>[|n IH] t; inv_triangle t => t l.
  - inv_triangle t.
    inv_fin_list l => a l.
    by inv_fin_list l.
  - inv_triangle t => t l' /=.
    rewrite fin_list_liat_snoc -IH fin_list_last_snoc
            -fin_list_snoc_liat_last //.
Qed.

Lemma triangle_remove_glue_top :
  ∀ {A : Type} {n : nat} (t : triangle A n) (l : fin_list A (S n)),
  triangle_remove_top (triangle_glue_top t l) = t.
Proof.
  move=>A.
  elim=>[|n IH] t l; inv_triangle t => //= t l'.
  rewrite IH //.
Qed.

Lemma triangle_remove_glue_bottom :
  ∀ {A : Type} {n : nat} (t : triangle A n) (l : fin_list A (S n)),
  triangle_remove_bottom (triangle_glue_bottom t l) = t.
Proof.
  move=>A.
  elim=>[|n IH] t l; inv_triangle t => //= t l'.
  rewrite IH fin_list_liat_snoc //.
Qed.

Lemma triangle_top_glue :
  ∀ {A : Type} {n : nat} (t : triangle A n) (l : fin_list A (S n)),
  triangle_top (triangle_glue_top t l) = l.
Proof.
  move=>A.
  elim=>[|n /= IH] t l; inv_triangle t.
  { inv_fin_list l => a l /=.
    by inv_fin_list l.
  }
  move=>t l' /=.
  rewrite IH -fin_list_snoc_liat_last //.
Qed.

Lemma triangle_bottom_glue :
  ∀ {A : Type} {n : nat} (t : triangle A n) (l : fin_list A (S n)),
  triangle_bottom (triangle_glue_bottom t l) = l.
Proof.
  move=>A.
  elim=>[|n /= IH] t l; inv_triangle t.
  { inv_fin_list l => a l /=.
    by inv_fin_list l.
  }
  move=>t l' /=.
  rewrite IH fin_list_last_snoc -fin_list_snoc_liat_last //.
Qed.

Lemma triangle_remove_top_bottom : 
  ∀ {A : Type} {n : nat} (t : triangle A (S (S n))),
  triangle_remove_top (triangle_remove_bottom t) = 
  triangle_remove_bottom (triangle_remove_top t).
Proof.
  move=>A.
  elim=>[|n IH] t; inv_triangle t => t l //=.
  rewrite IH //.
Qed.

Lemma triangle_remove_bottom_glue_top :
  ∀ {A : Type} {n : nat} (τ : triangle A (S n)) (l : fin_list A (S (S n))),
    triangle_remove_bottom (triangle_glue_top τ l) =
    triangle_glue_top (triangle_remove_bottom τ) (fin_list_tail l).
Proof.
  move=>A.
  elim=>[|n IH] τ l.
  - inv_triangle τ => τ lτ /=.
    inv_fin_list l => a l.
    inv_fin_list l => b l.
    inv_fin_list l.
    inv_fin_list lτ => c lτ.
    rewrite fin_list_liat_cons_S fin_list_last_cons_S fin_list_last_cons_0 fin_list_liat_cons_0 //=.
  - inv_triangle τ => τ lτ /=.
    rewrite -fin_list_tail_liat -IH //.
Qed.

Lemma triangle_bottom_glue_top :
  ∀ {A : Type} {n : nat} (τ : triangle A (S n)) (l : fin_list A (S (S n))),
    triangle_bottom (triangle_glue_top τ l) =
    fin_cons (fin_list_head l) (triangle_bottom τ).
Proof.
  move=>A.
  elim=>[|n IH] τ l.
  - inv_triangle τ => τ lτ /=.
    inv_fin_list l => a l.
    inv_fin_list l => b l.
    inv_fin_list l.
    inv_fin_list lτ => c lτ //.
  - inv_triangle τ => τ lτ /=.
    rewrite fin_list_cons_snoc.
    f_equal.
    rewrite -(fin_list_head_liat l) -IH //.
Qed.

Lemma triangle_head_glue_top : 
  ∀ {A : Type} {n : nat} (τ : triangle A (S n)) (l : fin_list A (S (S n))),
  triangle_head (triangle_glue_top τ l) = triangle_glue_top (triangle_head τ) (fin_list_liat l).
Proof. reflexivity. Qed.

Lemma triangle_tail_glue_top : 
  ∀ {A : Type} {n : nat} (τ : triangle A (S n)) (l : fin_list A (S (S n))),
  triangle_tail (triangle_glue_top τ l) = fin_cons (fin_list_last l) (triangle_tail τ).
Proof. reflexivity. Qed.

 Lemma triangle_head_glue_bottom : 
  ∀ {A : Type} {n : nat} (τ : triangle A (S n)) (l : fin_list A (S (S n))),
  triangle_head (triangle_glue_bottom τ l) = triangle_glue_bottom (triangle_head τ) (fin_list_liat l).
Proof. reflexivity. Qed.

Lemma triangle_tail_glue_bottom : 
  ∀ {A : Type} {n : nat} (τ : triangle A (S n)) (l : fin_list A (S (S n))),
  triangle_tail (triangle_glue_bottom τ l) = fin_list_snoc (triangle_tail τ) (fin_list_last l).
Proof. reflexivity. Qed.

Lemma triangle_head_remove_top : 
  ∀ {A : Type} {n : nat} (τ : triangle A (S (S n))),
  triangle_head (triangle_remove_top τ) = triangle_remove_top (triangle_head τ).
Proof. reflexivity. Qed.

Lemma triangle_head_remove_bottom : 
  ∀ {A : Type} {n : nat} (τ : triangle A (S (S n))),
  triangle_head (triangle_remove_bottom τ) = triangle_remove_bottom (triangle_head τ).
Proof. reflexivity. Qed.

Lemma triangle_tail_remove_top : 
  ∀ {A : Type} {n : nat} (τ : triangle A (S (S n))),
  triangle_tail (triangle_remove_top τ) = fin_list_tail (triangle_tail τ).
Proof. reflexivity. Qed.

Lemma triangle_tail_remove_bottom : 
  ∀ {A : Type} {n : nat} (τ : triangle A (S (S n))),
  triangle_tail (triangle_remove_bottom τ) = fin_list_liat (triangle_tail τ).
Proof. reflexivity. Qed.

Lemma triangle_top_bottom_first :
  ∀ {A : Type} {n : nat} (t : triangle A (S n)),
  fin_list_head (triangle_top t) = fin_list_head (triangle_bottom t).
Proof.
  move=>A.
  elim=>[|n IH] t; inv_triangle t => t l //=.
  rewrite !fin_list_head_snoc IH //.
Qed.

Fixpoint triangle_column {A : Type} {n : nat} : triangle A n → ∀ (i : fin n), fin_list A (FS i)%nat :=
match n as n0 return triangle A n0 → ∀ (i : fin n0), fin_list A (FS i)%nat with
| 0 => λ _, fin_0_inv _
| S m => λ t i,
           fin_S_inv (fin_list A ∘ FS)
             (fin_cons
                (fin_list_head (triangle_top t))
                fin_nil)
             (λ j,
                fin_cons
                  (fin_list_get
                     (triangle_top t)
                     (FS j)
                  )
                  (triangle_column (triangle_remove_top t) j)
             )
             i
end.

Fixpoint triangle_row {A : Type} {n : nat} : triangle A n → ∀ (i : fin n), fin_list A (n - i)%nat :=
match n as n0 return triangle A n0 → ∀ (i : fin n0), fin_list A (n0 - i)%nat with
| 0 => λ _, fin_0_inv _
| S m => λ t i,
           fin_S_inv (λ i, fin_list A (S m - i))
             (triangle_top t)
             (triangle_row (triangle_remove_top t))
             i
end.

Definition triangle_get {A : Type} {n : nat} (t : triangle A n) (i : fin n) (j : fin (FS i)) : A :=
  fin_list_get (triangle_column t i) j.

Lemma triangle_get_top : ∀ {A : Type} {n : nat} (t : triangle A n) (i : fin n),
  triangle_get t i 0 = fin_list_get (triangle_top t) i.
Proof.
  move=>A [|n] t i; first inv_fin i.
  inv_triangle t => t l .
  inv_fin_list l => a l.
  inv_fin i => [|i] //=.
Qed.

Lemma triangle_top_split_snoc :
  ∀ {A : Type} {n : nat}
    (t : triangle A n) (l : fin_list A (S n)),
  triangle_top (trig_snoc t l) = fin_list_snoc (triangle_top t) (fin_list_head l).
Proof. reflexivity. Qed.

Lemma triangle_bottom_split_snoc :
  ∀ {A : Type} {n : nat}
    (t : triangle A n) (l : fin_list A (S n)),
  triangle_bottom (trig_snoc t l) = fin_list_snoc (triangle_bottom t) (fin_list_last l).
Proof. reflexivity. Qed.

 Lemma triangle_top_last_tail_first :
  ∀ {A : Type} {n : nat}
    (t : triangle A (S n)),
  fin_list_last (triangle_top t) = fin_list_head (triangle_tail t).
Proof.
  move=>A n t.
  rewrite {1}(triangle_snoc_head_tail t) triangle_top_split_snoc fin_list_last_snoc //.
Qed.

Lemma triangle_bottom_tail_last :
  ∀ {A : Type} {n : nat}
    (t : triangle A (S n)),
  fin_list_last (triangle_bottom t) = fin_list_last (triangle_tail t).
Proof.
  move=>A n t.
  rewrite {1}(triangle_snoc_head_tail t) triangle_bottom_split_snoc fin_list_last_snoc //.
Qed.


Lemma triangle_bottom_split_cons :
  ∀ {A : Type} {n : nat}
    (t : triangle A (S n)),
  triangle_bottom t = fin_cons (fin_list_head (triangle_top t)) (triangle_bottom (triangle_remove_top t)).
Proof.
  move=>A.
  elim=>[|n IH] t /=.
  - inv_triangle t => t l /=.
    inv_fin_list l => a l.
    inv_fin_list l => //.
  - inv_triangle t => t l /=.
    rewrite fin_list_cons_snoc fin_list_last_tail.
    f_equal.
    rewrite -IH //.
Qed.

Lemma triangle_get_bottom :
  ∀ {A : Type} {n : nat} (t : triangle A n) (i : fin n),
  triangle_get t i (nat_to_fin (Nat.lt_succ_diag_r i)) =
  fin_list_get (triangle_bottom t) i.
Proof.
  move=>A.
  elim=>[|n IH] t i; first inv_fin i.
  destruct n.
  - inv_fin i => [|i]; last inv_fin i.
    inv_triangle t => t l /=.
    unfold triangle_get.
    simpl.
    inv_fin_list l => a l //.
  - inv_triangle t => t l.
    rewrite triangle_bottom_split_cons.
    inv_fin i => [//|i].
    simpl nat_to_fin.
    rewrite fin_list_get_cons_S -IH.
    remember (nat_to_fin _) as Hii.
    remember (nat_to_fin (Nat.lt_succ_diag_r i)) as Hi.
    replace Hii with Hi; last first.
    {
      subst.
      apply nat_to_fin_proof_ext.
    }
    done.
Qed.

Lemma triangle_top_remove_bottom :
   ∀ {A : Type} {n : nat} (t : triangle A (S n)),
  triangle_top (triangle_remove_bottom t) =
  fin_list_tail (triangle_top t).
Proof.
  move=>A.
  elim=>[|n IH] t;
        inv_triangle t => t l.
  - by inv_triangle t.
  - simpl.
    rewrite IH fin_list_tail_snoc //.
Qed.
  
Lemma triangle_column_bottom :
  ∀ {A : Type} {n : nat} (t : triangle A (S n)) (i : fin n),
  triangle_column (triangle_remove_bottom t) i =
  fin_list_liat (triangle_column t (FS i)).
Proof.
  move=>A.
  elim=>[|n IH] t i; first inv_fin i.
  destruct n.
  - inv_fin i => [|i]; last inv_fin i.
    inv_triangle t => t l /=.
    inv_fin_list l => a l /=.
    inv_fin_list l => b l /=.
    inv_fin_list l.
    inv_triangle t => t l' //=.
  - inv_fin i => [|i].
    + inv_triangle t => t l /=.
      specialize (IH t 0%fin).
      inv_fin_list l => a l /=.
      inv_fin_list l => b l /=.
      inv_triangle t => t l' IH //=.
    + #[local] Opaque triangle_remove_bottom triangle_remove_top fin_list_get triangle_top.
      remember (S n) as k.
      simpl.
      rewrite triangle_remove_top_bottom IH.
      subst k.
      setoid_rewrite fin_list_liat_cons_S at 2.
      f_equal.
      rewrite triangle_top_remove_bottom //.
Qed.

Lemma triangle_column_top :
  ∀ {A : Type} {n : nat} (t : triangle A (S n)) (i : fin n),
  triangle_column (triangle_remove_top t) i =
  fin_list_tail (triangle_column t (FS i)).
Proof. reflexivity. Qed.

Lemma triangle_get_remove_top :
  ∀ {A : Type} {n : nat} (t : triangle A (S n)) (i : fin n) (j : fin (S i)),
  triangle_get t (FS i) (FS j) =
  triangle_get (triangle_remove_top t) i j.
Proof. reflexivity. Qed.

Lemma triangle_get_remove_bottom :
  ∀ {A : Type} {n : nat} (t : triangle A (S n)) (i : fin n) (j : fin (S i)),
  triangle_get t (FS i) (fin_S_inj j) =
  triangle_get (triangle_remove_bottom t) i j.
Proof.
  move=>A [|n] t i j; first inv_fin i.
  unfold triangle_get.
  rewrite triangle_column_bottom fin_list_get_inj //.
Qed.

#[global] Opaque
  triangle_top
  triangle_bottom
  triangle_remove_top
  triangle_remove_bottom
  triangle_glue_top
  triangle_glue_bottom.

Fixpoint fin_list_const {n : nat} {A : Type} (a : A) : fin_list A n :=
  match n as n0 return fin_list A n0 with
  | 0 => fin_nil
  | S m => fin_cons a (fin_list_const a)
  end.

Fixpoint trig_const {n : nat} {A : Type} (a : A) : triangle A n :=
  match n as n0 return triangle A n0 with
  | 0 => trig_nil
  | S m => trig_snoc (trig_const a) (fin_list_const a)
  end.

Lemma fin_list_const_cons_snoc : ∀ {n : nat} {A : Type} (a : A), @fin_list_snoc A n (fin_list_const a) a = fin_cons a (fin_list_const a).
Proof.
  elim=>[|n IH] A a //=.
  rewrite -{2}IH //.
Qed.

Lemma fin_list_const_head : ∀ {n : nat} {A : Type} (a : A), @fin_list_head A n (fin_list_const a) = a.
Proof. reflexivity. Qed.
 
Lemma fin_list_const_last : ∀ {n : nat} {A : Type} (a : A), @fin_list_last A n (fin_list_const a) = a.
Proof.
  elim=>[//|n IH /=] A a.
  rewrite fin_list_last_cons_S IH //.
Qed.

Lemma fin_list_const_tail : ∀ {n : nat} {A : Type} (a : A), @fin_list_tail A n (fin_list_const a) = fin_list_const a.
Proof. reflexivity. Qed.
 
Lemma fin_list_const_liat : ∀ {n : nat} {A : Type} (a : A), @fin_list_liat A n (fin_list_const a) = fin_list_const a.
Proof.
  elim=>[//|n IH /=] A a.
  rewrite fin_list_liat_cons_S IH //.
Qed.

Lemma fin_list_const_get : ∀ {n : nat} {A : Type} (a : A) (i : fin n), @fin_list_get A n (fin_list_const a) i = a.
Proof.
  elim=>[|n IH] A a i /=; inv_fin i; first done.
  move=>i /=.
  rewrite -{3}(IH _ a i) //.
Qed.

Lemma trig_const_top : ∀ {n : nat} {A : Type} (a : A), @triangle_top A n (trig_const a) = fin_list_const a.
Proof.
  elim=>[|n IH] //= A a.
  cbv [triangle_top].
  simpl.
  cbv [triangle_top] in IH.
  rewrite IH.
  apply fin_list_const_cons_snoc.
Qed.

 Lemma trig_const_remove_top : ∀ {n : nat} {A : Type} (a : A), @triangle_remove_top A n (trig_const a) = trig_const a.
Proof.
  elim=>[|n IH] //= A a.
  cbv [triangle_remove_top].
  simpl.
  cbv [triangle_remove_top] in IH.
  rewrite IH //.
Qed.

Lemma trig_const_bottom : ∀ {n : nat} {A : Type} (a : A), @triangle_bottom A n (trig_const a) = fin_list_const a.
Proof.
  elim=>[|n IH] //= A a.
  cbv [triangle_bottom].
  simpl.
  cbv [triangle_bottom] in IH.
  rewrite IH fin_list_const_last fin_list_const_cons_snoc //.
Qed.

Lemma trig_const_remove_bottom : ∀ {n : nat} {A : Type} (a : A), @triangle_remove_bottom A n (trig_const a) = trig_const a.
Proof.
  elim=>[|n IH] //= A a.
  cbv [triangle_remove_bottom].
  simpl.
  cbv [triangle_remove_bottom] in IH.
  rewrite IH fin_list_const_liat //.
Qed.

Lemma trig_const_head : ∀ {n : nat} {A : Type} (a : A), @triangle_head A n (trig_const a) = trig_const a.
Proof. reflexivity. Qed.
  
Lemma trig_const_tail : ∀ {n : nat} {A : Type} (a : A), @triangle_tail A n (trig_const a) = fin_list_const a.
Proof. reflexivity. Qed.
 
