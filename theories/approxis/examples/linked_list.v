From clutch.approxis Require Import approxis map iterable_expression.

Section defs.
    
  Definition init_linked_list : val :=
    λ: <>, ref (init_list #()).
  
  Definition add_list : val :=
    λ: "l" "v", "l" <- cons_list !"l" "v".

  Variable elem_eq : val.

  Definition unfold_option1 {X Y} (f : X → Y) (x : option X) : option Y :=
    match x with
      | Some x' => Some (f x')
      | None => None
    end.

  Definition unfold_option2 {X Y} (f : X → X → Y) (x y : option X) : option Y :=
    match x, y with
      | Some x', Some y' => Some (f x' y')
      | _, _ => None
    end.

  Inductive vals_comparable : val → val → Prop :=
    | comp_lit : ∀ l l', vals_comparable (LitV l) (LitV l')
    | comp_pair : ∀ v1 v1' v2 v2', vals_comparable v1 v1' → vals_comparable v2 v2'
      → vals_comparable (PairV v1 v2) (PairV v1' v2')
    | comp_injr : ∀ v1 v1', vals_comparable v1 v1' → vals_comparable (InjRV v1) (InjRV v1')
    | comp_injl : ∀ v1 v1', vals_comparable v1 v1' → vals_comparable (InjLV v1) (InjLV v1')
  .

  Lemma vals_comparable_trans : ∀ v1 v2 v3,
    vals_comparable v1 v2 → vals_comparable v2 v3 → vals_comparable v1 v3.
  Proof. intros * H1 H2. generalize dependent v3.
    induction H1 as [l l'|v1 v1' v2 v2' Hv1 IHv1 Hv2 IHv2|v v' H IHv|v v' H IHv];
      intros v3 H2.
    - inversion H2. constructor.
    - inversion H2; subst.
      constructor.
      + apply IHv1. assumption.
      + apply IHv2. assumption.
    - inversion H2; subst.
      constructor. apply IHv. assumption.
    - inversion H2; subst.
      constructor. apply IHv. assumption.
  Qed.

  Lemma vals_comparable_sym : ∀ v1 v2, vals_comparable v1 v2 → vals_comparable v2 v1.
  Proof. intros v1 v2 H.
    induction H as [l l'|v1 v1' v2 v2' Hv1 IHv1 Hv2 IHv2|v v' H IHv|v v' H IHv];
      constructor; assumption.
  Qed.

  Fixpoint meta_elem_eq (x y : val) : bool := match x, y with
    | LitV l, LitV l' => bool_decide (x = y)
    | PairV v1 v2, PairV v1' v2' => (meta_elem_eq v1 v1') && (meta_elem_eq v2 v2') 
    | InjLV v, InjLV v' => meta_elem_eq v v'
    | InjRV v, InjRV v' => meta_elem_eq v v'
    (* nonsense if the vals aren't comparable *)
    | _, _ => false
  end.

  Lemma vals_comparable_refl (x y : val) (H : vals_comparable x y) : vals_comparable y y.
  Proof. induction H.
    - constructor.
    - constructor; assumption.
    - constructor; assumption.
    - constructor; assumption.
  Qed. 

  Lemma meta_elem_eq_iff_true (x y : val) (H : vals_comparable x y) :
    (eq x y) ↔ (meta_elem_eq x y = true).
  Proof. split; intros H1.
    - rewrite H1. apply vals_comparable_refl in H. clear H1 x.
      induction H as [l l' | v1 v1' v2 v2' IHv1 IHv1' IHv2 IHv2'
        | v v' IHv IHv' | v v' IHv IHv'].
      + simpl. apply bool_decide_eq_true. reflexivity.
      + simpl. rewrite IHv1' IHv2'. reflexivity.
      + simpl. assumption.
      + simpl; assumption.
    - induction H as [l l' | v1 v1' v2 v2' IHv1 IHv1' IHv2 IHv2'
        | v v' IHv IHv' | v v' IHv IHv'].
      + simpl in H1. apply bool_decide_eq_true in H1. assumption.
      + simpl in H1.
        apply andb_true_iff in H1 as [H1 H2].
        rewrite IHv1'; first (rewrite IHv2'; first reflexivity); assumption.
      + simpl in H1. rewrite IHv'; first reflexivity; assumption.
      + simpl in H1. rewrite IHv'; first reflexivity; assumption.
  Qed.

  Lemma meta_elem_eq_iff_false (x y : val) (H : vals_comparable x y) :
    (x ≠ y) ↔ (meta_elem_eq x y = false).
  Proof. split; intros H1.
    - apply not_true_iff_false. intros H2.
      apply meta_elem_eq_iff_true in H2; last assumption.
      apply H1; assumption.
    - intro H2. apply meta_elem_eq_iff_true in H2; last assumption.
      rewrite H1 in H2. discriminate H2.
  Qed.

  Definition comp_pair_fst {v1 v1' v2 v2' : val} (H : vals_comparable (PairV v1 v2) (PairV v1' v2')) : vals_comparable v1 v1' :=
    match H in vals_comparable (PairV v10 v20) (PairV v10' v20') 
    return vals_comparable v10 v10' with
    | comp_pair _ _ _ _ H1 _ => H1
    end.

  Definition comp_pair_snd {v1 v1' v2 v2' : val} (H : vals_comparable (PairV v1 v2) (PairV v1' v2')) : vals_comparable v2 v2' :=
    match H in vals_comparable (PairV v10 v20) (PairV v10' v20') 
    return vals_comparable v20 v20' with
    | comp_pair _ _ _ _ _ H2 => H2
    end.

  Definition comp_injl_inv {v1 v1' : val} (H : vals_comparable (InjLV v1) (InjLV v1')) : vals_comparable v1 v1' :=
    match H in vals_comparable (InjLV v10) (InjLV v10') 
    return vals_comparable v10 v10' with
    | comp_injl _ _ H1 => H1
    end.

  Definition comp_injr_inv {v2 v2' : val} (H : vals_comparable (InjRV v2) (InjRV v2')) : vals_comparable v2 v2' :=
    match H in vals_comparable (InjRV v20) (InjRV v20') 
    return vals_comparable v20 v20' with
    | comp_injr _ _ H2 => H2
    end.

  Definition comp_injl_injr {v1 v2 : val} (H : vals_comparable (InjLV v1) (InjRV v2)) : False :=
  match H in vals_comparable (InjLV v10) (InjRV v20) return False with
  end.

  Fixpoint meta_elem_eq_bool_prop (x y : val) (H : vals_comparable x y) : bool :=
  match  x as x0 , y as y0 return vals_comparable x0 y0 -> bool with 
    | LitV l, LitV l' => fun _ => bool_decide (x = y)
    | PairV v1 v2, PairV v1' v2' => fun H0 => meta_elem_eq_bool_prop v1 v1' (comp_pair_fst H0) && meta_elem_eq_bool_prop v2 v2' (comp_pair_snd H0)
    | InjLV v, InjLV v' => fun H0 => meta_elem_eq_bool_prop v v' (comp_injl_inv H0)
    | InjRV v, InjRV v' => fun H0 => meta_elem_eq_bool_prop v v' (comp_injr_inv H0)
    | InjLV v, InjRV v' => λ H0, False_rect _ (comp_injl_injr H0)
    | _, _ => fun _ => true
    end H.

  Definition elem_of_list : val :=
    rec: "elem_of" "h" "k" :=
          match: ! (rec_unfold "h") with
            NONE => #false
          | SOME "p" =>
              let: "kv" := Fst "p" in
              let: "next" := Snd "p" in
              if: elem_eq "kv" "k" then #true else ("elem_of") "next" "k"
          end.

  Definition elem_of_linked_list : val :=
    λ: "l" "x",
      elem_of_list !"l" "x".

  Section logrel.
  
    Context `{!approxisRGS Σ}.
    
    Definition refines_elem_eq_l_prop :=
      ∀ (x y : val) (H : vals_comparable x y) K e E A,
          refines E (fill K (Val #(meta_elem_eq x y))) e A
          ⊢ refines E (fill K (elem_eq x y)) e A.
    Definition refines_elem_eq_r_prop :=
      ∀ (x y : val) (H : vals_comparable x y) K e E A,
          refines E e (fill K (Val #(meta_elem_eq x y))) A
        ⊢ refines E e (fill K (elem_eq x y)) A.

    Hypothesis refines_elem_eq_l : refines_elem_eq_l_prop.
    Hypothesis refines_elem_eq_r : refines_elem_eq_r_prop.
    
    Context {X : Type}.
    Context (to_val : Inject X val).

    Fixpoint const_linked_list (l : loc) (ls : list X) : iProp Σ :=
      match ls with
        | [] => l ↦ NONEV
        | h :: t => ∃ (lt : loc), l ↦ SOMEV (inject h, #lt)%V ∗ const_linked_list lt t
      end.
    
    Fixpoint const_linked_slist (l : loc) (ls : list X) : iProp Σ :=
      match ls with
        | [] => l ↦ₛ NONEV
        | h :: t => ∃ (lt : loc), l ↦ₛ SOMEV (inject h, #lt)%V ∗ const_linked_slist lt t
      end.

    Definition linked_list (l : loc) (ls : list X) : iProp Σ :=
      ∃ (l' : loc), l ↦ #l' ∗ const_linked_list l' ls.

    Definition linked_slist (l : loc) (ls : list X) : iProp Σ :=
      ∃ (l' : loc), l ↦ₛ #l' ∗ const_linked_slist l' ls.

    Lemma refines_init_list_l : ∀ K e E A,
        (∀ (l : loc), linked_list l [] -∗ refines E (fill K (Val #l)) e A)
      ⊢ refines E (fill K (init_linked_list #())) e A.
    Proof with rel_pures_l.
      iIntros (K e E A) "H".
      rewrite /init_linked_list/init_list...
      rel_alloc_l lst' as "Hlst'".
      rel_alloc_l lst as "Hlst".
      rel_apply "H". iExists lst'. iFrame.
    Qed.
    
    Lemma refines_init_list_r : ∀ K e E A,
        (∀ l, linked_slist l [] -∗ refines E e (fill K (Val #l)) A)
      ⊢ refines E e (fill K (init_linked_list #())) A.
    Proof with rel_pures_r.
      iIntros (K e E A) "H".
      rewrite /init_linked_list/init_list...
      rel_alloc_r lst' as "Hlst'".
      rel_alloc_r lst as "Hlst".
      rel_apply "H". iExists lst'. iFrame.
    Qed.

    Lemma refines_add_list_l : ∀ K e E A (ll : loc) (t : list X) (h : X),
        (linked_list ll (h :: t)
        -∗ refines E (fill K (Val #())) e A)
      -∗ linked_list ll t
      -∗ refines E (fill K (add_list #ll (Val (inject h)))) e A.
    Proof with rel_pures_l.
      iIntros (K e E A ll t h) "H Hlist".
      rewrite /add_list/cons_list/linked_list...
      iDestruct "Hlist" as (l') "[Hll Hlist]"...
      rel_load_l... rel_alloc_l ll' as "Hll'"...
      rel_store_l. rel_apply "H". iFrame.
    Qed.

    Lemma refines_add_list_r : ∀ K e E A (ll : loc) (t : list X) (h : X),
        (linked_slist ll (h :: t)
        -∗ refines E e (fill K (Val #())) A)
      -∗ linked_slist ll t
      -∗ refines E e (fill K (add_list #ll (Val (inject h)))) A.
    Proof with rel_pures_r.
      iIntros (K e E A ll t h) "H Hlist".
      rewrite /add_list/cons_list/linked_list...
      iDestruct "Hlist" as (l') "[Hll Hlist]".
      rel_load_r... rel_alloc_r ll' as "Hll'"...
      rel_store_r. rel_apply "H". iFrame.
    Qed.

    Lemma refines_elem_of_const_list_l : ∀ K e E A l_list l v,
        (∀ (b : bool), const_linked_list l_list l
          -∗ (⌜b = true ↔ v ∈ l⌝ -∗ refines E (fill K (Val #b)) e A))
      -∗ const_linked_list l_list l
      -∗ ⌜Forall (λ x, vals_comparable (inject x) (inject v)) l⌝
      -∗ refines E (fill K (elem_of_list #l_list (Val (inject v)))) e A.
    Proof with rel_pures_l using X approxisRGS0 elem_eq refines_elem_eq_l to_val Σ.
      iIntros (K e E A l_list l v) "H Hlist %Hcomparable".
      iRevert "Hlist H". iRevert (l_list).
      iInduction l as [|h t] "IH"; iIntros (l_list) "Hlist H".
      - rewrite /elem_of_list/linked_list. simpl.
        rewrite /elem_of_linked_list/rec_unfold...
        rel_load_l...
        iPoseProof ("H" with "Hlist") as "H".
        rel_apply "H".
        iPureIntro. split; intros H; first discriminate H.
        exfalso. apply not_elem_of_nil in H. apply H.
      - rewrite /elem_of_list/linked_list.
        simpl. iDestruct "Hlist" as (lt) "[Hlt Htail]".
        rewrite /elem_of_linked_list/rec_unfold...
        rewrite /elem_of_linked_list;
        rel_load_l...
        rel_apply refines_elem_eq_l.
        { inversion Hcomparable. assumption. }
        destruct (meta_elem_eq (inject h) (inject v)) eqn:eq.
        + iAssert (∃ lt0 : loc, l_list ↦ InjRV (inject h, #lt0) ∗
            const_linked_list lt0 t)%I with "[Hlt Htail]" as "G".
          { iFrame. }
          iPoseProof ("H" with "G") as "H"...
          rel_apply "H".
          iPureIntro. apply meta_elem_eq_iff_true in eq.
          2: { inversion Hcomparable. assumption. }
          apply inject_inj in eq. rewrite eq.
          split; intros H; first constructor.
          reflexivity.
        + rel_pure_l. rel_apply ("IH" with "[] [Htail] [Hlt H]").
          * iPureIntro. inversion Hcomparable. assumption.
          * iAssumption.
          * iIntros (b) "G".
            iAssert (∃ lt0 : loc, l_list ↦ InjRV (inject h, #lt0) ∗
              const_linked_list lt0 t)%I with "[Hlt G]" as "H'".
            { iFrame. }
            iPoseProof ("H" with "H'") as "H". Unshelve. 2: exact b.
            iIntros "%H"; first iApply "H".
            iPureIntro.
            split; intros H'.
            -- apply H in H'. constructor. apply H'.
            -- apply H. inversion H'; subst.
              { apply meta_elem_eq_iff_false in eq.
                - exfalso. apply eq.
                  reflexivity.
                - inversion Hcomparable.
                  assumption. } 
              assumption.
    Qed.

    Lemma refines_elem_of_l : ∀ K e E A l_list l v,
        (∀ (b : bool), linked_list l_list l
          -∗ (⌜b = true ↔ v ∈ l⌝ -∗ refines E (fill K (Val #b)) e A))
      -∗ linked_list l_list l
      -∗ ⌜Forall (λ x, vals_comparable (inject x) (inject v)) l⌝
      -∗ refines E (fill K (elem_of_linked_list #l_list (Val (inject v)))) e A.
    Proof with rel_pures_l using X approxisRGS0 elem_eq refines_elem_eq_l to_val Σ.
      iIntros (K e E A ll l v) "H Hlist %Hcomparable".
      rewrite /elem_of_linked_list...
      iDestruct "Hlist" as (l_list) "[Hll Hlist]".
      rel_load_l.
      rel_apply (refines_elem_of_const_list_l with "[H Hll] [Hlist] []").
      - iIntros (b) "H1 Hin". iApply ("H" with "[-Hin]"); last iAssumption.
        iExists l_list. iFrame.
      - iAssumption.
      - iPureIntro; assumption.
    Qed.

    Lemma refines_elem_of_const_list_r : ∀ K e E A l_list l v,
        (∀ (b : bool), const_linked_slist l_list l
          -∗ (⌜b = true ↔ v ∈ l⌝ -∗ refines E e (fill K (Val #b)) A))
      -∗ const_linked_slist l_list l
      -∗ ⌜Forall (λ x, vals_comparable (inject x) (inject v)) l⌝
      -∗ refines E e (fill K (elem_of_list #l_list (Val (inject v)))) A.
    Proof with rel_pures_r using X approxisRGS0 elem_eq refines_elem_eq_r to_val Σ.
      iIntros (K e E A l_list l v) "H Hlist %Hcomparable".
      iRevert "Hlist H". iRevert (l_list).
      iInduction l as [|h t] "IH"; iIntros (l_list) "Hlist H".
      - rewrite /elem_of_list/linked_list. simpl.
        rewrite /elem_of_linked_list/rec_unfold...
        rel_load_r...
        iPoseProof ("H" with "Hlist") as "H".
        rel_apply "H".
        iPureIntro. split; intros H; first discriminate H.
        exfalso. apply not_elem_of_nil in H; assumption.
      - rewrite /elem_of_list/linked_list.
        simpl. iDestruct "Hlist" as (lt) "[Hlt Htail]".
        rewrite /elem_of_linked_list/rec_unfold...
        rewrite /elem_of_linked_list;
        rel_load_r...
        rel_apply refines_elem_eq_r.
        { inversion Hcomparable. assumption. }
        destruct (meta_elem_eq (inject h) (inject v)) eqn:eq.
        + iAssert (∃ lt0 : loc, l_list ↦ₛ InjRV (inject h, #lt0) ∗
            const_linked_slist lt0 t)%I with "[Hlt Htail]" as "G".
          { iFrame. }
          iPoseProof ("H" with "G") as "H"...
          rel_apply "H".
          iPureIntro. apply meta_elem_eq_iff_true in eq.
          2: { inversion Hcomparable. assumption. }
          apply inject_inj in eq. rewrite eq. split; intros H.
          * constructor.
          * reflexivity.
        + rel_pure_r. rel_apply ("IH" with "[] [Htail] [Hlt H]").
          * iPureIntro. inversion Hcomparable. assumption.
          * iAssumption.
          * iIntros (b) "G".
            iAssert (∃ lt0 : loc, l_list ↦ₛ InjRV (inject h, #lt0) ∗
              const_linked_slist lt0 t)%I with "[Hlt G]" as "H'".
            { iFrame. }
            iPoseProof ("H" with "H'") as "H".
            iIntros "%H"; first iApply "H".
            iPureIntro.
            split; intros H'.
            -- apply H in H'. constructor. apply H'.
            -- apply H. inversion H'; subst.
              { apply meta_elem_eq_iff_false in eq.
                - exfalso. apply eq.
                  reflexivity.
                - inversion Hcomparable.
                  assumption. } 
              assumption.
    Qed.

    Lemma refines_elem_of_r : ∀ K (e : expr) E A l_list l v,
        (∀ (b : bool), linked_slist l_list l
          -∗ (⌜b = true ↔ v ∈ l⌝ -∗ refines E e (fill K (Val #b)) A))
      -∗ linked_slist l_list l
      -∗ ⌜Forall (λ x, vals_comparable (inject x) (inject v)) l⌝
      -∗ refines E e (fill K (elem_of_linked_list #l_list (inject v))) A.
    Proof with rel_pures_r using X approxisRGS0 elem_eq refines_elem_eq_r to_val Σ.
      iIntros (K e E A ll l v) "H Hlist %Hcomparable".
      rewrite /elem_of_linked_list...
      iDestruct "Hlist" as (l_list) "[Hll Hlist]"...
      (* rel_load_r.
      rel_apply (refines_elem_of_const_list_r with "[H Hll] [Hlist] []").
      - iIntros "H1". iApply "H". iExists l_list. iFrame.
      - iAssumption.
      - iPureIntro; assumption.
    Qed. *)
    Admitted.

  End logrel.

End defs. 