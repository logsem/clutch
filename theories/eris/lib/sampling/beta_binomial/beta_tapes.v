From clutch.eris Require Import eris.
From clutch.eris.lib.sampling.bernoulli Require Import interface.
From clutch.eris.lib.sampling Require Import utils.

Section BetaTapes.

  Context `{!bernoulli_spec bernoulli balloc}.
  
  (** A β_tape has a list at each pair of coordinates (k,i)
        for k the number of balls drawn so far and i the number
        of red balls seen while doing so.

        So a β_tape might look something like this
        (a star represents there being a list) :

       i\k 0 1 2 3 4 5
       0   * * * * * * 
       1     * * * * *
       2       * * * *
       3         * * *
       4           * *
       5             *

   **)

  Definition β_tape := triangle (list (fin 2)).
  
  Definition β_empty_list {n : nat} : fin_list (list (fin 2)) n := @fin_list_const n (list (fin 2)) [].
  Definition β_empty {n : nat} : β_tape n := @trig_const n (list (fin 2)) [].
  
  Definition tl_error {A : Type} (l : list A) : option (list A) :=
    match l with
    | [] => None
    | _::t => Some t
    end.

  Fixpoint liat_error {A : Type} (l : list A) : option (list A) :=
    match l with
    | [] => None
    | [_] => Some []
    | h::t => cons h <$> liat_error t
    end.

  Lemma liat_error_snoc : ∀ {A : Type} (l : list A) (a : A),
    liat_error (l ++ [a]) = Some l.
  Proof.
    move=>A.
    elim=>[//|h1 [|h2 t] IH] a //=.
    specialize (IH a).
    simpl in IH.
    rewrite IH //.
  Qed.

  Definition β_list_push_first {n : nat}
    (l : fin_list (list (fin 2)) (S n)) (v : fin 2) : fin_list (list (fin 2)) (S n)
    := fin_cons (v::fin_list_head l) (fin_list_tail l).

  Definition β_list_hsup_first {n : nat}
    (l : fin_list (list (fin 2)) (S n)) (v : fin 2) : fin_list (list (fin 2)) (S n)
    := fin_cons (fin_list_head l ++ [v]) (fin_list_tail l).

  Definition β_list_pop_first {n : nat}
    (l : fin_list (list (fin 2)) (S n))
    : option (fin_list (list (fin 2)) (S n))
    := hd' ← tl_error (fin_list_head l) ;
  Some (fin_cons hd' (fin_list_tail l)).

  Definition β_list_opo_first {n : nat}
    (l : fin_list (list (fin 2)) (S n))
    : option (fin_list (list (fin 2)) (S n))
    := hd' ← liat_error (fin_list_head l);
  Some (fin_cons hd' (fin_list_tail l)).

  Definition β_list_head_first {n : nat}
    (l : fin_list (list (fin 2)) (S n)) : option (fin 2) := 
    head (fin_list_head l)
  .

  Definition β_list_daeh_first {n : nat}
    (l : fin_list (list (fin 2)) (S n)) : option (fin 2) := 
    last (fin_list_head l)
  .
  
  Lemma β_list_push_pop_first {n : nat} :
    ∀ (l : fin_list (list (fin 2)) (S n))
      (v : fin 2),
    β_list_pop_first (β_list_push_first l v) = Some l.
  Proof.
    move=>l v.
    by inv_fin_list l.
  Qed.

  Lemma β_list_hsup_opo_first {n : nat} :
    ∀ (l : fin_list (list (fin 2)) (S n))
      (v : fin 2),
    β_list_opo_first (β_list_hsup_first l v) = Some l.
  Proof.
    move=>l v.
    inv_fin_list l => a l /=.
    rewrite /β_list_hsup_first /β_list_opo_first /= liat_error_snoc //.
  Qed.
  
  Lemma β_list_push_head_first {n : nat} :
    ∀ (l : fin_list (list (fin 2)) (S n))
      (v : fin 2),
    β_list_head_first (β_list_push_first l v) = Some v.
  Proof.
    move=>l v //.
  Qed.

  Lemma β_list_hsup_daeh_first {n : nat} :
    ∀ (l : fin_list (list (fin 2)) (S n))
      (v : fin 2),
    β_list_daeh_first (β_list_hsup_first l v) = Some v.
  Proof.
    move=>l v.
    inv_fin_list l => a l /=.
    rewrite /β_list_daeh_first fin_list_head_cons last_snoc //.
  Qed.

  Lemma β_list_head_first_top_bottom {n : nat} :
    ∀ (t : β_tape (S n)), β_list_head_first (triangle_top t) = β_list_head_first (triangle_bottom t).
  Proof.
    move=>t.
    unfold β_list_head_first.
    f_equal.
    apply triangle_top_bottom_first.
  Qed.

  Lemma β_list_daeh_first_top_bottom {n : nat} :
    ∀ (t : β_tape (S n)), β_list_daeh_first (triangle_top t) = β_list_daeh_first (triangle_bottom t).
  Proof.
    move=>t.
    unfold β_list_daeh_first.
    f_equal.
    apply triangle_top_bottom_first.
  Qed.
  
  Lemma β_list_push_first_fin_head {n : nat} :
    ∀ (l : fin_list (list (fin 2)) (S n))
      (v : fin 2),
    fin_list_head (β_list_push_first l v) = v::fin_list_head l.
  Proof.
    move=>l v //.
  Qed.
  
  Lemma β_list_push_first_fin_tail {n : nat} :
    ∀ (l : fin_list (list (fin 2)) (S n))
      (v : fin 2),
    fin_list_tail (β_list_push_first l v) = fin_list_tail l.
  Proof. reflexivity. Qed.

  
  Lemma β_list_hsup_first_fin_head {n : nat} :
    ∀ (l : fin_list (list (fin 2)) (S n))
      (v : fin 2),
    fin_list_head (β_list_hsup_first l v) = fin_list_head l ++ [v].
  Proof.
    move=>l v //.
  Qed.

  Lemma β_list_hsup_first_fin_tail {n : nat} :
    ∀ (l : fin_list (list (fin 2)) (S n))
      (v : fin 2),
    fin_list_tail (β_list_hsup_first l v) = fin_list_tail l.
  Proof.
    move=>l v //.
  Qed.

  Lemma β_list_push_hsup_empty {n : nat} :
    ∀ (i : fin 2), β_list_push_first (@β_empty_list (S n)) i = β_list_hsup_first (@β_empty_list (S n)) i.
  Proof. reflexivity. Qed.
  
  #[global] Opaque
    β_list_push_first
    β_list_pop_first
    β_list_head_first
    β_list_hsup_first
    β_list_opo_first
    β_list_daeh_first.

  Fixpoint fin_list_list_concat {A : Type} {n : nat} :
    fin_list (list A) n → fin_list (list A) n → fin_list (list A) n :=
    match n as n0 return
          fin_list (list A) n0 → fin_list (list A) n0 → fin_list (list A) n0
    with
    | 0 => λ _ _, fin_nil
    | S m => λ l1 l2, fin_cons (fin_list_head l1 ++ fin_list_head l2) (fin_list_list_concat (fin_list_tail l1) (fin_list_tail l2))
    end.

  Lemma fin_list_list_concat_assoc :
    ∀ (A : Type) (n : nat) (l1 l2 l3 : fin_list (list A) n),
    fin_list_list_concat (fin_list_list_concat l1 l2) l3 = fin_list_list_concat l1 (fin_list_list_concat l2 l3).
  Proof.
    move=>A.
    elim=>[//|n IH] l1 l2 l3.
    inv_fin_list l1=>h1 l1.
    inv_fin_list l2=>h2 l2.
    inv_fin_list l3=>h3 l3.
    rewrite /= app_assoc IH //.
  Qed.

  Lemma fin_list_list_concat_head :
    ∀ (A : Type) (n : nat) (l1 l2 : fin_list (list A) (S n)),
    fin_list_head (fin_list_list_concat l1 l2) = fin_list_head l1 ++ fin_list_head l2.
  Proof. reflexivity. Qed.

  Lemma fin_list_list_concat_snoc :
    ∀ (A : Type) (n : nat) (l1 l2 : fin_list (list A) n) (h1 h2 : list A),
    (fin_list_list_concat (fin_list_snoc l1 h1) (fin_list_snoc l2 h2)) =
    fin_list_snoc (fin_list_list_concat l1 l2) (h1 ++ h2).
  Proof.
    move=>A.
    elim=>[//|n IH] l1 l2 h1 h2.
    simpl.
    rewrite -fin_list_cons_snoc -IH //.
  Qed.

  Lemma fin_list_list_concat_last :
    ∀ (A : Type) (n : nat) (l1 l2 : fin_list (list A) (S n)),
    fin_list_last (fin_list_list_concat l1 l2) = fin_list_last l1 ++ fin_list_last l2.
  Proof.
    move=>A n l1 l2.
    rewrite {1}(fin_list_snoc_liat_last l1) {1}(fin_list_snoc_liat_last l2) fin_list_list_concat_snoc fin_list_last_snoc //.
  Qed.

  Lemma fin_list_list_concat_liat :
    ∀ (A : Type) (n : nat) (l1 l2 : fin_list (list A) (S n)),
    fin_list_liat (fin_list_list_concat l1 l2) = fin_list_list_concat (fin_list_liat l1) (fin_list_liat l2).
  Proof.
    move=>A n l1 l2.
    rewrite {1}(fin_list_snoc_liat_last l1) {1}(fin_list_snoc_liat_last l2) fin_list_list_concat_snoc fin_list_liat_snoc //.
  Qed.

  Lemma fin_list_list_concat_nil_l :
    ∀ (A : Type) (n : nat) (l : fin_list (list A) n),
    fin_list_list_concat (fin_list_const []) l = l.
  Proof.
    move=>A.
    elim=>[|n IH] l; inv_fin_list l=>// h l.
    rewrite /= IH //.
  Qed.

  Lemma fin_list_list_concat_nil_r :
    ∀ (A : Type) (n : nat) (l : fin_list (list A) n),
    fin_list_list_concat l (fin_list_const []) = l.
  Proof.
    move=>A.
    elim=>[|n IH] l; inv_fin_list l=>// h l.
    rewrite /= IH app_nil_r //.
  Qed.
  
  Lemma β_list_push_first_concat :
    ∀ (n : nat) (l : fin_list (list (fin 2)) (S n)) (i : fin 2),
    β_list_push_first l i = fin_list_list_concat (β_list_push_first β_empty_list i) l.
  Proof.
    move=>n l i.
    inv_fin_list l=>h l /=.
    rewrite fin_list_list_concat_nil_l //.
  Qed.

  Lemma β_list_hsup_first_concat :
    ∀ (n : nat) (l : fin_list (list (fin 2)) (S n)) (i : fin 2),
    β_list_hsup_first l i = fin_list_list_concat l (β_list_hsup_first β_empty_list i).
  Proof.
    move=>n l i.
    inv_fin_list l=>h l /=.
    rewrite fin_list_list_concat_nil_r //.
  Qed.
  
  Fixpoint triangle_list_concat {n : nat} : β_tape n → β_tape n → β_tape n :=
    match n as n0 return β_tape n0 → β_tape n0 → β_tape n0 with
    | 0 => λ _ _, trig_nil
    | S m => λ t1 t2,
               trig_snoc (triangle_list_concat
                            (triangle_head t1)
                            (triangle_head t2)
                 ) (fin_list_list_concat (triangle_tail t1) (triangle_tail t2))
                         
    end.

  #[local] Opaque fin_list_list_concat.
  
  Lemma triangle_list_concat_top :
    ∀ (n : nat) (t1 t2 : β_tape n),
    triangle_top (triangle_list_concat t1 t2) = fin_list_list_concat (triangle_top t1) (triangle_top t2).
  Proof.
    elim=>[//|n IH] t1 t2 /=.
    inv_triangle t1=>t1 l1.
    inv_triangle t2=>t2 l2.
    rewrite !triangle_top_split_snoc IH /= fin_list_list_concat_head fin_list_list_concat_snoc //.
  Qed.
  
  Lemma triangle_list_concat_remove_top :
    ∀ (n : nat) (t1 t2 : β_tape (S n)),
    triangle_remove_top (triangle_list_concat t1 t2) = triangle_list_concat (triangle_remove_top t1) (triangle_remove_top t2).
  Proof.
    elim=>[//|n IH] t1 t2 /=.
    specialize (IH (triangle_head t1) (triangle_head t2)).
    rewrite -IH //.
  Qed.

  Lemma triangle_list_concat_glue_top :
    ∀ (n : nat) (t1 t2 : β_tape n) (h1 h2 : fin_list (list (fin 2)) (S n)),
    triangle_glue_top (triangle_list_concat t1 t2) (fin_list_list_concat h1 h2) =
    triangle_list_concat (triangle_glue_top t1 h1) (triangle_glue_top t2 h2).
  Proof.
    move=>n t1 t2 h1 h2.
    rewrite
      (triangle_glue_remove_top (triangle_list_concat (triangle_glue_top _ _) _))
        triangle_list_concat_top triangle_list_concat_remove_top
        !triangle_remove_glue_top !triangle_top_glue //.
  Qed.

  Lemma triangle_list_concat_bottom :
    ∀ (n : nat) (t1 t2 : β_tape n),
    triangle_bottom (triangle_list_concat t1 t2) = fin_list_list_concat (triangle_bottom t1) (triangle_bottom t2).
  Proof.
    elim=>[//|n IH] t1 t2 /=.
    inv_triangle t1=>t1 l1.
    inv_triangle t2=>t2 l2.
    rewrite !triangle_bottom_split_snoc fin_list_list_concat_snoc fin_list_list_concat_last -IH //.
  Qed.
  
  Lemma triangle_list_concat_remove_bottom :
    ∀ (n : nat) (t1 t2 : β_tape (S n)),
    triangle_remove_bottom (triangle_list_concat t1 t2) = triangle_list_concat (triangle_remove_bottom t1) (triangle_remove_bottom t2).
  Proof.
    elim=>[//|n IH] t1 t2 /=.
    specialize (IH (triangle_head t1) (triangle_head t2)).
    rewrite -IH.
    cbv [triangle_remove_bottom].
    rewrite fin_list_list_concat_liat //.
  Qed.
  
  Lemma triangle_list_concat_glue_bottom :
    ∀ (n : nat) (t1 t2 : β_tape n) (h1 h2 : fin_list (list (fin 2)) (S n)),
    triangle_glue_bottom (triangle_list_concat t1 t2) (fin_list_list_concat h1 h2) =
    triangle_list_concat (triangle_glue_bottom t1 h1) (triangle_glue_bottom t2 h2).
  Proof.
    move=>n t1 t2 h1 h2.
    rewrite
      (triangle_glue_remove_bottom (triangle_list_concat (triangle_glue_bottom _ _) _))
        triangle_list_concat_bottom triangle_list_concat_remove_bottom
        !triangle_remove_glue_bottom !triangle_bottom_glue //.
  Qed.


  Lemma triangle_list_concat_assoc :
    ∀ (n : nat) (t1 t2 t3 : β_tape n),
    triangle_list_concat (triangle_list_concat t1 t2) t3 = triangle_list_concat t1 (triangle_list_concat t2 t3).
  Proof.
    elim=>[//|n IH] t1 t2 t3.
    inv_triangle t1=>t1 l1. 
    inv_triangle t2=>t2 l2. 
    inv_triangle t3=>t3 l3.
    rewrite /= !fin_list_list_concat_assoc IH //.
  Qed.

  Fixpoint β_push {n : nat} : β_tape n → fin_list (fin 2) n → β_tape n :=
    match n as n0 return β_tape n0 → fin_list (fin 2) n0 → β_tape n0 with
    | 0 => λ _ _, trig_nil
    | S m => λ t l,
               fin_S_inv (const (β_tape (S m)))
                 (triangle_glue_bottom
                    (β_push (triangle_remove_bottom t) (fin_list_tail l))
                    (β_list_push_first (triangle_bottom t) 0%fin)
                 )
                 (λ _,
                    triangle_glue_top
                      (β_push (triangle_remove_top t) (fin_list_tail l))
                      (β_list_push_first (triangle_top t) 1%fin)
                 )
                 (fin_list_head l)
    end.

  Lemma β_push_0_split :
    ∀ (n : nat) (t : β_tape (S n)) (l : fin_list (fin 2) n),
    β_push t (fin_cons 0%fin l) =
    triangle_glue_bottom
      (β_push (triangle_remove_bottom t) l)
      (β_list_push_first (triangle_bottom t) 0%fin)
  .
  Proof. reflexivity. Qed.

  Lemma β_push_1_split :
    ∀ (n : nat) (t : β_tape (S n)) (l : fin_list (fin 2) n),
    β_push t (fin_cons 1%fin l) =
    triangle_glue_top
      (β_push (triangle_remove_top t) l)
      (β_list_push_first (triangle_top t) 1%fin).
  Proof. reflexivity. Qed.

  
  Fixpoint β_hsup {n : nat} : β_tape n → fin_list (fin 2) n → β_tape n :=
    match n as n0 return β_tape n0 → fin_list (fin 2) n0 → β_tape n0 with
    | 0 => λ _ _, trig_nil
    | S m => λ t l,
               fin_S_inv (const (β_tape (S m)))
                 (triangle_glue_bottom
                    (β_hsup (triangle_remove_bottom t) (fin_list_tail l))
                    (β_list_hsup_first (triangle_bottom t) 0%fin)
                 )
                 (λ _,
                    triangle_glue_top
                      (β_hsup (triangle_remove_top t) (fin_list_tail l))
                      (β_list_hsup_first (triangle_top t) 1%fin)
                 )
                 (fin_list_head l)
    end.

  Lemma β_push_concat : ∀ (n : nat) (t : β_tape n) (l : fin_list (fin 2) n),
    β_push t l = triangle_list_concat (β_push β_empty l) t.
  Proof.
    elim=>[//|n IH] t l.
    inv_fin_list l=>i l.
    inv_fin i=>[|i].
    - rewrite /= IH β_list_push_first_concat triangle_list_concat_glue_bottom
              -triangle_glue_remove_bottom trig_const_bottom trig_const_remove_bottom //.
    - rewrite /= IH β_list_push_first_concat triangle_list_concat_glue_top
              -triangle_glue_remove_top trig_const_top trig_const_remove_top //.
  Qed.

  Lemma β_hsup_concat : ∀ (n : nat) (t : β_tape n) (l : fin_list (fin 2) n),
    β_hsup t l = triangle_list_concat t (β_hsup β_empty l).
  Proof.
    elim=>[//|n IH] t l.
    inv_fin_list l=>i l.
    inv_fin i=>[|i].
    - rewrite /= IH β_list_hsup_first_concat triangle_list_concat_glue_bottom
              -triangle_glue_remove_bottom trig_const_bottom trig_const_remove_bottom //.
    - rewrite /= IH β_list_hsup_first_concat triangle_list_concat_glue_top
              -triangle_glue_remove_top trig_const_top trig_const_remove_top //.
  Qed.

  Lemma β_push_hsup_empty : ∀ (n : nat) (i : fin_list (fin 2) n), β_push β_empty i = β_hsup β_empty i.
  Proof.
    elim=>[//|n IH] i.
    inv_fin_list i=>hi ti.
    inv_fin hi=>[|hi]=>/=.
    - rewrite !trig_const_remove_bottom trig_const_bottom IH //.
    - rewrite !trig_const_remove_top trig_const_top IH //.
  Qed.

  Lemma β_push_hsup :
    ∀ (n : nat) (τ : β_tape n) (lt lb : fin_list (fin 2) n),
    β_push (β_hsup τ lb) lt = β_hsup (β_push τ lt) lb.
  Proof.
    move=>n τ lt lb.
    rewrite (β_push_concat _ (β_hsup _ _)) (β_hsup_concat _ (β_push _ _))
      (β_push_concat _ τ) (β_hsup_concat _ τ) triangle_list_concat_assoc //.
  Qed.
  
  Fixpoint β_arbitrary {n : nat} : fin (S n) → fin_list (fin 2) n :=
    match n as n0 return fin (S n0) → fin_list (fin 2) n0 with
    | 0 => const fin_nil
    | S m => fin_S_inv (const (fin_list (fin 2) (S m)))
               (fin_cons 0%fin (β_arbitrary 0%fin))
               (λ j, fin_cons 1%fin (β_arbitrary j))
    end.
  
  Lemma β_push_length_first_top {n : nat} :
    ∀ (t : β_tape (S n))
      (v : fin_list (fin 2) (S n)),
    length (fin_list_head (triangle_top (β_push t v))) =
    S (length (fin_list_head (triangle_top t))).
  Proof.
    move=>t v.
    inv_fin_list v => i v /=.
    inv_fin i => [|i].
    - rewrite !triangle_top_bottom_first triangle_bottom_glue β_list_push_first_fin_head //.
    - rewrite triangle_top_glue β_list_push_first_fin_head //.
  Qed.
  
  Definition β_fold {n : nat} : list (fin_list (fin 2) n) → β_tape n :=
    foldr (flip β_push) β_empty.

  Lemma β_hsup_fold {n : nat} :
    ∀ (l : list (fin_list (fin 2) n)) (h : fin_list (fin 2) n),
    β_hsup (β_fold l) h = β_fold (l ++ [h]).
  Proof.
    elim=>[|hl tl IH] h /=.
    - rewrite β_push_hsup_empty //.
    - rewrite -β_push_hsup IH //.
  Qed.
  
  Definition β_encode {n : nat} : list (fin (S n)) → β_tape n :=
    β_fold ∘ fmap β_arbitrary.

  Definition β_first {n : nat} (t : β_tape (S n)) : option (fin 2) :=
    β_list_head_first (triangle_top t).

  Definition β_daeh_first {n : nat} (t : β_tape (S n)) : option (fin 2) :=
    β_list_daeh_first (triangle_top t).
  
  Fixpoint β_head {n : nat} : β_tape n → option (fin_list (fin 2) n) :=
    match n as n0 return β_tape n0 → option (fin_list (fin 2) n0) with
    | 0 => λ _, Some fin_nil
    | S m => λ t,
               v ← β_first t ;
  match v with
  | 0%fin => fin_cons 0%fin <$> β_head (triangle_remove_bottom t)
  | _ => fin_cons 1%fin <$> β_head (triangle_remove_top t)
  end
  end.

  Fixpoint β_daeh {n : nat} : β_tape n → option (fin_list (fin 2) n) :=
    match n as n0 return β_tape n0 → option (fin_list (fin 2) n0) with
    | 0 => λ _, Some fin_nil
    | S m => λ t,
               v ← β_daeh_first t ;
  match v with
  | 0%fin => fin_cons 0%fin <$> β_daeh (triangle_remove_bottom t)
  | _ => fin_cons 1%fin <$> β_daeh (triangle_remove_top t)
  end
  end.

  Fixpoint β_pop {n : nat} : β_tape n → option (β_tape n) :=
    match n as n0 return β_tape n0 → option (β_tape n0) with
    | 0 => λ _, Some β_empty
    | S m => λ t,
               v ← β_first t ;
  match v with
  | 0%fin =>
      l' ← β_list_pop_first (triangle_bottom t);
  t' ← β_pop $ triangle_remove_bottom t;
  Some (triangle_glue_bottom t' l')
       
| _ =>
    l' ← β_list_pop_first (triangle_top t);
  t' ← β_pop $ triangle_remove_top t;
  Some (triangle_glue_top t' l')
  end
  end.

  Fixpoint β_opo {n : nat} : β_tape n → option (β_tape n) :=
    match n as n0 return β_tape n0 → option (β_tape n0) with
    | 0 => λ _, Some β_empty
    | S m => λ t,
               v ← β_daeh_first t ;
  match v with
  | 0%fin =>
      l' ← β_list_opo_first (triangle_bottom t);
  t' ← β_opo $ triangle_remove_bottom t;
  Some (triangle_glue_bottom t' l')
       
| _ =>
    l' ← β_list_opo_first (triangle_top t);
  t' ← β_opo $ triangle_remove_top t;
  Some (triangle_glue_top t' l')
  end
  end.


  Definition β_split {n : nat} (t : β_tape n) : option (fin_list (fin 2) n * β_tape n) :=
    h ← β_head t ;
  t' ← β_pop t;
  Some (h, t').

  Definition β_tilps {n : nat} (t : β_tape n) : option (fin_list (fin 2) n * β_tape n) :=
    h ← β_daeh t ;
  t' ← β_opo t;
  Some (h, t').
  
  Fixpoint fin_list_fin_2_sum {n : nat} : fin_list (fin 2) n → fin (S n) :=
    match n as n0 return fin_list (fin 2) n0 → fin (S n0) with
    | 0 => const 0%fin
    | S m => λ l, fin_hsum (fin_list_head l) (fin_S_inj (fin_list_fin_2_sum (fin_list_tail l)))
    end.

  Lemma fin_list_fin_2_sum_0 : ∀ (l : fin_list (fin 2) 0), fin_list_fin_2_sum l = 0%fin.
  Proof. reflexivity. Qed.

  Lemma fin_list_fin_2_sum_S : ∀ (n : nat) (l : fin_list (fin 2) (S n)), fin_list_fin_2_sum l = fin_hsum (fin_list_head l) (fin_S_inj (fin_list_fin_2_sum (fin_list_tail l))).
  Proof. reflexivity. Qed.

  Lemma fin_list_fin_2_sum_0_const_0 : ∀ (n : nat) (l : fin_list (fin 2) n), fin_list_fin_2_sum l = 0%fin → l = fin_list_const 0%fin.
  Proof.
    elim=>[|n IH] l sum_l; inv_fin_list l=> // h t sum_h_t.
    inv_fin h=>[|h] /= sum_h_t.
    - rewrite (IH t) //.
      inv_fin (fin_list_fin_2_sum t) => [//|st] Sst_eq_0.
      discriminate.
    - rewrite fin_succ_inj in sum_h_t.
      inv_fin h=>[//|].
      move=>h.
      inv_fin h.
  Qed.

  Lemma fin_list_fin_2_sum_const_0_eq_0 : ∀ (n : nat), fin_list_fin_2_sum (@fin_list_const n _ 0%fin) = 0%fin.
  Proof.
    elim=>[|n /= ->] //.
  Qed.

  
  Lemma fin_list_fin_2_sum_const_1_eq_max : ∀ (n : nat), fin_list_fin_2_sum (@fin_list_const n _ 1%fin) = fin_max n.
  Proof.
    elim=>[//|n /= ->].
    apply fin_succ_inj. 
  Qed.

  Lemma sum_arbitrary : ∀ {n : nat} (i : fin (S n)), fin_list_fin_2_sum (β_arbitrary i) = i.
  Proof.
    elim=>[|n IH] i /=; full_inv_fin => /=; rewrite IH //=.
    rewrite fin_succ_inj //.
  Qed.

  #[global] Opaque β_arbitrary fin_list_fin_2_sum.
  
  Fixpoint β_decode_k {n : nat} (t : β_tape n) (k : nat) : option (list (fin (S n))) :=
    match k with
    | 0 => Some []
    | S k' => '(hd, t') ← β_split t ;
  tl ← β_decode_k t' k' ;
  Some ((fin_list_fin_2_sum hd)::tl)
  end.

  Definition β_decode {n : nat} : β_tape n → option (list (fin (S n))) :=
    match n as n0 return β_tape n0 → option (list (fin (S n0))) with
    | 0 => const (Some [])
    | S m => λ t, β_decode_k t (length $ fin_list_head $ triangle_top t)
    end.
  
  Lemma β_push_head :
    ∀ {n : nat} (t : β_tape n) (v : fin_list (fin 2) n),
    β_head (β_push t v) = Some v.
  Proof.
    elim=>[|n IH] t v; first by inv_fin_list v.
    inv_fin_list v => i v.
    inv_fin i => [|i].
    - simpl.
      unfold β_first.
      rewrite β_list_head_first_top_bottom triangle_bottom_glue β_list_push_head_first /= triangle_remove_glue_bottom IH //.
    - simpl.
      unfold β_first.
      rewrite triangle_top_glue β_list_push_head_first /= triangle_remove_glue_top IH //.
      inv_fin i => [//|i].
      inv_fin i.
  Qed.

  Lemma β_hsup_daeh :
    ∀ {n : nat} (t : β_tape n) (v : fin_list (fin 2) n),
    β_daeh (β_hsup t v) = Some v.
  Proof.
    elim=>[|n IH] t v; first by inv_fin_list v.
    inv_fin_list v => i v.
    inv_fin i => [|i].
    - simpl.
      unfold β_daeh_first.
      rewrite β_list_daeh_first_top_bottom triangle_bottom_glue β_list_hsup_daeh_first /= triangle_remove_glue_bottom IH //.
    - simpl.
      unfold β_daeh_first.
      rewrite triangle_top_glue β_list_hsup_daeh_first /= triangle_remove_glue_top IH //.
      inv_fin i => [//|i].
      inv_fin i.
  Qed.

  Lemma β_push_pop :
    ∀ {n : nat} (t : β_tape n) (v : fin_list (fin 2) n),
    β_pop (β_push t v) = Some t.
  Proof.
    elim=>[|n IH] t v.
    { inv_fin_list v. by inv_triangle t. } 
    inv_fin_list v => i v.
    inv_fin i => [|i].
    - simpl.
      unfold β_first.
      rewrite β_list_head_first_top_bottom triangle_bottom_glue β_list_push_head_first /= triangle_remove_glue_bottom IH β_list_push_pop_first /= -triangle_glue_remove_bottom //.
    - simpl.
      unfold β_first.
      rewrite triangle_top_glue β_list_push_head_first /= triangle_remove_glue_top IH β_list_push_pop_first /= -triangle_glue_remove_top //.
  Qed.

  Lemma β_hsup_opo :
    ∀ {n : nat} (t : β_tape n) (v : fin_list (fin 2) n),
    β_opo (β_hsup t v) = Some t.
  Proof.
    elim=>[|n IH] t v.
    { inv_fin_list v. by inv_triangle t. } 
    inv_fin_list v => i v.
    inv_fin i => [|i].
    - simpl.
      unfold β_daeh_first.
      rewrite β_list_daeh_first_top_bottom triangle_bottom_glue β_list_hsup_daeh_first /= triangle_remove_glue_bottom IH β_list_hsup_opo_first /= -triangle_glue_remove_bottom //.
    - simpl.
      unfold β_daeh_first.
      rewrite triangle_top_glue β_list_hsup_daeh_first /= triangle_remove_glue_top IH β_list_hsup_opo_first /= -triangle_glue_remove_top //.
  Qed.
  
  Lemma β_push_split :
    ∀ {n : nat} (t : β_tape n) (v : fin_list (fin 2) n),
    β_split (β_push t v) = Some (v, t).
  Proof.
    move=> n t v.
    unfold β_split.
    rewrite β_push_head /= β_push_pop //.
  Qed.

  Lemma β_hsup_tilps :
    ∀ {n : nat} (t : β_tape n) (v : fin_list (fin 2) n),
    β_tilps (β_hsup t v) = Some (v, t).
  Proof.
    move=> n t v.
    unfold β_tilps.
    rewrite β_hsup_daeh /= β_hsup_opo //.
  Qed.
  
  Lemma β_encode_decode :
    ∀ {n : nat} (l : list (fin (S (S n)))),
    β_decode (β_encode l) = Some l.
  Proof.
    move=>n.
    elim=>[|h t IH] /=.
    - rewrite trig_const_top //.
    - rewrite β_push_length_first_top /= β_push_split /=.
      unfold β_decode in IH.
      rewrite IH /=.
      do 2 f_equal.
      apply sum_arbitrary.
  Qed.

  Lemma β_hsup_head :
    ∀ (n : nat) (τ : β_tape (S n))
      (i : fin_list (fin 2) (S n)),
    triangle_head (β_hsup τ i) = β_hsup (triangle_head τ) (fin_list_liat i).
  Proof.
    elim=>[|n IH] τ i; first apply triangle_0_nil.
    inv_triangle τ=>τ l /=.
    inv_fin_list i=>hi ti /=.
    rewrite fin_list_liat_cons_S.
    inv_fin hi=>[|hi].
    - rewrite triangle_head_glue_bottom IH
        triangle_bottom_split_snoc fin_list_liat_cons_S
        fin_list_head_snoc fin_list_tail_snoc fin_list_liat_snoc //.
    - rewrite triangle_head_glue_top IH
        triangle_top_split_snoc fin_list_liat_cons_S
        fin_list_head_snoc fin_list_tail_snoc fin_list_liat_snoc //.
  Qed.

  Lemma fin_hsum_2_inj_inj : ∀ (n : nat) (a : fin 2) (b : fin n),
    fin_hsum a (fin_S_inj (fin_S_inj b)) =
    fin_S_inj (fin_hsum a (fin_S_inj b)).
  Proof.
    move=>n a b; inv_fin a; first done.
    move=>a /=.
    inv_fin a; last (move=>a; inv_fin a).
    rewrite !fin_succ_inj //.
  Qed.
  
  Lemma fin_list_fin_2_sum_last_liat :
    ∀ (n : nat) (l : fin_list (fin 2) (S n)),
    fin_list_fin_2_sum l = fin_hsum (fin_list_last l) (fin_S_inj (fin_list_fin_2_sum (fin_list_liat l))).
  Proof.
    elim=>[|n IH] l; inv_fin_list l=>k l; first inv_fin_list l=>//.
    rewrite fin_list_fin_2_sum_S IH fin_list_tail_cons
      fin_list_last_cons_S fin_list_head_cons
      fin_list_liat_cons_S fin_list_fin_2_sum_S
      fin_list_head_cons fin_list_tail_cons
      -!fin_hsum_2_inj_inj fin_hsum_comm //
    .
  Qed.
  
  Lemma β_hsup_tail :
    ∀ (n : nat) (τ : β_tape (S n))
      (i : fin_list (fin 2) (S n)),
    let tl := triangle_tail τ in
    let k := fin_list_fin_2_sum (fin_list_liat i) in
    triangle_tail (β_hsup τ i) = fin_list_set tl k (fin_list_get tl k ++ [fin_list_last i]).
  Proof.
    elim=>[|n IH] τ i tl k.
    { inv_triangle τ=>τ l tl.
      inv_triangle τ=>tl.
      simpl in tl.
      subst tl.
      inv_fin_list i=>k i0 k0.
      inv_fin_list i0=>k0.
      replace k0 with (0%fin : fin 1) by reflexivity.
      clear k0.
      inv_fin_list l=>h l /=.
      inv_fin k=>[|k] /=.
      - by inv_fin_list l.
      - inv_fin_list l.
        by inv_fin k=>[|k]; last inv_fin k.
    }
    inv_fin_list i=>k i0 k0.
    inv_fin k=>[|k] k0.
    #[local] Opaque fin_list_set fin_list_get.
    - rewrite triangle_tail_glue_bottom IH fin_list_tail_cons triangle_tail_remove_bottom.
      replace (fin_list_last (β_list_hsup_first (triangle_bottom τ) 0)) with (fin_list_last (triangle_bottom τ)); last first.
      {
        rewrite {1}(fin_list_cons_head_tail (triangle_bottom τ)) !fin_list_last_cons_S //.
      }
      rewrite /k0 !(fin_list_last_cons_S 0%fin i0) !fin_list_liat_cons_S !fin_list_fin_2_sum_S triangle_bottom_tail_last fin_list_set_inj fin_list_get_inj //.
    - inv_fin k; last (move=>k; inv_fin k); move=>k0.
      rewrite triangle_tail_glue_top IH fin_list_tail_cons triangle_tail_remove_top.
      replace (fin_list_last (β_list_hsup_first (triangle_top τ) 1)) with (fin_list_last (triangle_top τ)); last first.
      {
        rewrite {1}(fin_list_cons_head_tail (triangle_top τ)) !fin_list_last_cons_S //.
      }
      rewrite /k0 !(fin_list_last_cons_S 1%fin i0) !fin_list_liat_cons_S !fin_list_fin_2_sum_S triangle_top_last_tail_first /= fin_succ_inj //.
  Qed.

End BetaTapes.
