From Coq Require Import Reals Psatz.
From stdpp Require Import functions gmap stringmap fin_sets.
From clutch.prelude Require Import stdpp_ext NNRbar fin uniform_list.
From clutch.prob Require Import distribution couplings couplings_app.
From clutch.common Require Import ectx_language.
From clutch.delay_prob_lang Require Import tactics notation urn_subst.
From clutch.delay_prob_lang Require Export lang.
From clutch.prob Require Import distribution couplings.
From iris.prelude Require Import options.
Set Default Proof Using "Type*".
(* This file contains some metatheory about the [delay_prob_lang] language *)

(* Adding a binder to a set of identifiers. *)
Local Definition set_binder_insert (x : binder) (X : stringset) : stringset :=
  match x with
  | BAnon => X
  | BNamed f => {[f]} ∪ X
  end.

(* Check if expression [e] is closed w.r.t. the set [X] of variable names,
   and that all the values in [e] are closed *)
Fixpoint is_closed_expr (X : stringset) (e : expr) : bool :=
  match e with
  | Val v => is_closed_val v
  | Var x => bool_decide (x ∈ X)
  | Rec f x e => is_closed_expr (set_binder_insert f (set_binder_insert x X)) e
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Load e |Rand e |DRand e=>
     is_closed_expr X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | AllocN e1 e2 | Store e1 e2 =>
     is_closed_expr X e1 && is_closed_expr X e2
  | If e0 e1 e2 | Case e0 e1 e2 =>
     is_closed_expr X e0 && is_closed_expr X e1 && is_closed_expr X e2
  end
with is_closed_val (v : val) : bool :=
  match v with
  | LitV _ => true
  | RecV f x e => is_closed_expr (set_binder_insert f (set_binder_insert x ∅)) e
  | PairV v1 v2 => is_closed_val v1 && is_closed_val v2
  | InjLV v | InjRV v => is_closed_val v
  end.

(** Parallel substitution *)
Fixpoint subst_map (vs : gmap string val) (e : expr)  : expr :=
  match e with
  | Val _ => e
  | Var y => if vs !! y is Some v then Val v else Var y
  | Rec f y e => Rec f y (subst_map (binder_delete y (binder_delete f vs)) e)
  | App e1 e2 => App (subst_map vs e1) (subst_map vs e2)
  | UnOp op e => UnOp op (subst_map vs e)
  | BinOp op e1 e2 => BinOp op (subst_map vs e1) (subst_map vs e2)
  | If e0 e1 e2 => If (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | Pair e1 e2 => Pair (subst_map vs e1) (subst_map vs e2)
  | Fst e => Fst (subst_map vs e)
  | Snd e => Snd (subst_map vs e)
  | InjL e => InjL (subst_map vs e)
  | InjR e => InjR (subst_map vs e)
  | Case e0 e1 e2 => Case (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | AllocN e1 e2 => AllocN (subst_map vs e1) (subst_map vs e2)
  | Load e => Load (subst_map vs e)
  | Store e1 e2 => Store (subst_map vs e1) (subst_map vs e2)
  | Rand e => Rand (subst_map vs e) 
  | DRand e => DRand (subst_map vs e) 
  end.

(* Properties *)
Local Instance set_unfold_elem_of_insert_binder x y X Q :
  SetUnfoldElemOf y X Q →
  SetUnfoldElemOf y (set_binder_insert x X) (Q ∨ BNamed y = x).
Proof. destruct 1; constructor; destruct x; set_solver. Qed.

Lemma is_closed_weaken X Y e : is_closed_expr X e → X ⊆ Y → is_closed_expr Y e.
Proof. revert X Y; induction e; naive_solver (eauto; set_solver). Qed.

Lemma is_closed_weaken_empty X e : is_closed_expr ∅ e → is_closed_expr X e.
Proof. intros. by apply is_closed_weaken with ∅, empty_subseteq. Qed.

Lemma is_closed_subst X e y v :
  is_closed_val v →
  is_closed_expr ({[y]} ∪ X) e →
  is_closed_expr X (subst y v e).
Proof.
  intros Hv. revert X.
  induction e=> X /= ?; destruct_and?; split_and?; simplify_option_eq;
    try match goal with
    | H : ¬(_ ∧ _) |- _ => apply not_and_l in H as [?%dec_stable|?%dec_stable]
    end; eauto using is_closed_weaken with set_solver.
Qed.
Lemma is_closed_subst' X e x v :
  is_closed_val v →
  is_closed_expr (set_binder_insert x X) e →
  is_closed_expr X (subst' x v e).
Proof. destruct x; eauto using is_closed_subst. Qed.

Lemma subst_is_closed X e x es : is_closed_expr X e → x ∉ X → subst x es e = e.
Proof.
  revert X. induction e=> X /=;
   rewrite ?bool_decide_spec ?andb_True=> ??;
   repeat case_decide; simplify_eq/=; f_equal; intuition eauto with set_solver.
Qed.

Lemma subst_is_closed_empty e x v : is_closed_expr ∅ e → subst x v e = e.
Proof. intros. apply subst_is_closed with (∅:stringset); set_solver. Qed.

Lemma subst_subst e x v v' :
  subst x v (subst x v' e) = subst x v' e.
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using subst_is_closed_empty with f_equal.
Qed.
Lemma subst_subst' e x v v' :
  subst' x v (subst' x v' e) = subst' x v' e.
Proof. destruct x; simpl; auto using subst_subst. Qed.

Lemma subst_subst_ne e x y v v' :
  x ≠ y → subst x v (subst y v' e) = subst y v' (subst x v e).
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using eq_sym, subst_is_closed_empty with f_equal.
Qed.
Lemma subst_subst_ne' e x y v v' :
  x ≠ y → subst' x v (subst' y v' e) = subst' y v' (subst' x v e).
Proof. destruct x, y; simpl; auto using subst_subst_ne with congruence. Qed.

Lemma subst_rec' f y e x v :
  x = f ∨ x = y ∨ x = BAnon →
  subst' x v (Rec f y e) = Rec f y e.
Proof. intros. destruct x; simplify_option_eq; naive_solver. Qed.
Lemma subst_rec_ne' f y e x v :
  (x ≠ f ∨ f = BAnon) → (x ≠ y ∨ y = BAnon) →
  subst' x v (Rec f y e) = Rec f y (subst' x v e).
Proof. intros. destruct x; simplify_option_eq; naive_solver. Qed.

Lemma bin_op_eval_closed op v1 v2 v' :
  is_closed_val v1 → is_closed_val v2 → bin_op_eval op v1 v2 = Some v' →
  is_closed_val v'.
Proof.
  rewrite /bin_op_eval. destruct op; simpl; repeat case_match; naive_solver.
Qed.

Lemma heap_closed_alloc σ l n w :
  (0 < n)%Z →
  is_closed_val w →
  map_Forall (λ _ v, is_closed_val v) (heap σ) →
  (∀ i : Z, (0 ≤ i)%Z → (i < n)%Z → heap σ !! (l +ₗ i) = None) →
  map_Forall (λ _ v, is_closed_val v)
             (heap_array l (replicate (Z.to_nat n) w) ∪ heap σ).
Proof.
  intros Hn Hw Hσ Hl.
  eapply (map_Forall_ind
            (λ k v, ((heap_array l (replicate (Z.to_nat n) w) ∪ heap σ)
                       !! k = Some v))).
  - apply map_Forall_empty.
  - intros m i x Hi Hix Hkwm Hm.
    apply map_Forall_insert_2; auto.
    apply lookup_union_Some in Hix; last first.
    { eapply heap_array_map_disjoint;
        rewrite replicate_length Z2Nat.id; auto with lia. }
    destruct Hix as [(?&?&?&[-> Hlt%inj_lt]%lookup_replicate_1)%heap_array_lookup|
                      [j Hj]%elem_of_map_to_list%elem_of_list_lookup_1].
    + simplify_eq/=. rewrite !Z2Nat.id in Hlt; eauto with lia.
    + apply map_Forall_to_list in Hσ.
      by eapply Forall_lookup in Hσ; eauto; simpl in *.
  - apply map_Forall_to_list, Forall_forall.
    intros [? ?]; apply elem_of_map_to_list.
Qed.

Lemma subst_map_empty e : subst_map ∅ e = e.
Proof.
  assert (∀ x, binder_delete x (∅:gmap _ val) = ∅) as Hdel.
  { intros [|x]; by rewrite /= ?delete_empty. }
  induction e; simplify_map_eq; rewrite ?Hdel; auto with f_equal.
Qed.
Lemma subst_map_insert x v vs e :
  subst_map (<[x:=v]>vs) e = subst x v (subst_map (delete x vs) e).
Proof.
  revert vs. induction e=> vs; simplify_map_eq; auto with f_equal.
  - match goal with
    | |- context [ <[?x:=_]> _ !! ?y ] =>
       destruct (decide (x = y)); simplify_map_eq=> //
    end. by case (vs !! _); simplify_option_eq.
  - destruct (decide _) as [[??]|[<-%dec_stable|[<-%dec_stable ?]]%not_and_l_alt].
    + rewrite !binder_delete_insert // !binder_delete_delete; eauto with f_equal.
    + by rewrite /= delete_insert_delete delete_idemp.
    + by rewrite /= binder_delete_insert // delete_insert_delete
        !binder_delete_delete delete_idemp.
Qed.
Lemma subst_map_singleton x v e :
  subst_map {[x:=v]} e = subst x v e.
Proof. by rewrite subst_map_insert delete_empty subst_map_empty. Qed.

Lemma subst_map_binder_insert b v vs e :
  subst_map (binder_insert b v vs) e =
  subst' b v (subst_map (binder_delete b vs) e).
Proof. destruct b; rewrite ?subst_map_insert //. Qed.
Lemma subst_map_binder_insert_empty b v e :
  subst_map (binder_insert b v ∅) e = subst' b v e.
Proof. by rewrite subst_map_binder_insert binder_delete_empty subst_map_empty. Qed.

Lemma subst_map_binder_insert_2 b1 v1 b2 v2 vs e :
  subst_map (binder_insert b1 v1 (binder_insert b2 v2 vs)) e =
  subst' b2 v2 (subst' b1 v1 (subst_map (binder_delete b2 (binder_delete b1 vs)) e)).
Proof.
  destruct b1 as [|s1], b2 as [|s2]=> /=; auto using subst_map_insert.
  rewrite subst_map_insert. destruct (decide (s1 = s2)) as [->|].
  - by rewrite delete_idemp subst_subst delete_insert_delete.
  - by rewrite delete_insert_ne // subst_map_insert subst_subst_ne.
Qed.
Lemma subst_map_binder_insert_2_empty b1 v1 b2 v2 e :
  subst_map (binder_insert b1 v1 (binder_insert b2 v2 ∅)) e =
  subst' b2 v2 (subst' b1 v1 e).
Proof.
  by rewrite subst_map_binder_insert_2 !binder_delete_empty subst_map_empty.
Qed.

Lemma subst_map_is_closed X e vs :
  is_closed_expr X e →
  (∀ x, x ∈ X → vs !! x = None) →
  subst_map vs e = e.
Proof.
  revert X vs. assert (∀ x x1 x2 X (vs : gmap string val),
    (∀ x, x ∈ X → vs !! x = None) →
    x ∈ set_binder_insert x2 (set_binder_insert x1 X) →
    binder_delete x1 (binder_delete x2 vs) !! x = None).
  { intros x x1 x2 X vs ??. rewrite !lookup_binder_delete_None. set_solver. }
  induction e=> X vs /= ? HX; repeat case_match; naive_solver eauto with f_equal.
Qed.

Lemma subst_map_is_closed_empty e vs : is_closed_expr ∅ e → subst_map vs e = e.
Proof. intros. apply subst_map_is_closed with (∅ : stringset); set_solver. Qed.



(** Lemma for resolving an urn. To be improved to allow partial resolvement *)  
Lemma urns_f_distr_split (m:gmap loc urn) u s (N:nat):
  m!!u=Some s ->
  size s = S N ->
  urns_f_distr m =
  dunifP N ≫= (λ n, (match (elements s)!!(fin_to_nat n) with
                     | Some y => dret (<[u:={[y]}]> m)
                     | None => dzero
                     end ) ≫= (λ m', urns_f_distr m')
    ).
Proof.
  intros Hsome Hsize.
  apply distr_ext.
  intros f.
  assert (s ≠ ∅) by (intros ?; set_solver). 
  destruct (decide (urns_f_valid m f)) as [H'|H'].
  - rewrite urns_f_distr_eval; last done.
    replace m with (<[u:=s]> (delete u m)) at 1; last first.
    { rewrite insert_delete_insert.
      by rewrite insert_id.
    }
    rewrite urns_subst_f_num_insert; [|done|apply lookup_delete].
    pose proof H' u as H''.
    rewrite Hsome in H''.
    case_match; last destruct!/=.
    destruct H'' as (u'&?&Helem).
    destruct!/=.
    rewrite -elem_of_elements in Helem.
    apply elem_of_list_lookup_1 in Helem.
    destruct Helem as [i Helem'].
    apply lookup_lt_Some in Helem' as Hlt.
    rewrite -length_elements_size_gset Hsize in Hlt.
    rewrite {1}/dbind{1}/dbind_pmf{1}/pmf.
    pose (a':= nat_to_fin Hlt).
    erewrite (SeriesC_ext _ (λ a, if bool_decide (a = a') then dunifP N a * _ else 0)); last first.
    { intros a.
      case_bool_decide as H1; first done.
      case_match eqn:Hsome'; last (rewrite dbind_dzero dzero_0; lra).
      rewrite dret_id_left'.
      rewrite urns_f_distr_eval'; first lra.
      intro Hcontra.
      pose proof Hcontra u as H2.
      case_match; simplify_eq.
      destruct H2 as (?&H2&?).
      rewrite lookup_insert in H2.
      simplify_eq.
      set_unfold; destruct!/=.
      apply H1.
      apply fin_to_nat_inj.
      eapply NoDup_lookup; try done.
      - apply NoDup_elements.
      - by rewrite fin_to_nat_to_fin. 
    }
    rewrite SeriesC_singleton_dependent.
    rewrite {1}/pmf{1}/dunifP/dunif.
    rewrite Hsize.
    rewrite fin_to_nat_to_fin.
    rewrite Helem'.
    rewrite dret_id_left'.
    rewrite urns_f_distr_eval; last first.
    + intros j. destruct (decide (u=j)).
      * subst. case_match; simplify_eq.
        eexists _.
        rewrite lookup_insert; split; first done.
        set_solver.
      * pose proof H' j.
        rewrite lookup_insert_ne; last done.
        case_match; destruct!/=; naive_solver.
    + rewrite -insert_delete_insert.
      rewrite urns_subst_f_num_insert.
      * rewrite size_singleton.
        rewrite !mult_INR. 
        rewrite INR_1. 
        rewrite !Rdiv_1_l.
        rewrite !Rinv_mult.
        lra.
      * set_solver.
      * apply lookup_delete.
  - rewrite urns_f_distr_eval'; last done.
    symmetry.
    destruct (pmf_pos (dunifP N
                         ≫= λ n : fin (S N),
                         match elements s !! (fin_to_nat n) with
                         | Some y => dret (<[u:={[y]}]> m)
                         | None => dzero
                         end ≫= λ m' : gmap loc urn, urns_f_distr m') f) as [Hcontra|]; last lra.
    apply Rlt_gt in Hcontra.
    inv_distr.
    case_match; inv_distr.
    exfalso.
    apply H'.
    intros u'.
    rename select (_ _ f > 0) into Hpos.
    rewrite urns_f_distr_pos in Hpos.
    pose proof Hpos u' as K.
    destruct (decide (u=u')).
    + subst.
      rewrite lookup_insert in K.
      case_match; destruct!/=.
      set_unfold; destruct!/=.
      eexists _; split; first done.
      rewrite -elem_of_elements.
      by eapply elem_of_list_lookup_2.
    + rewrite lookup_insert_ne in K; last done.
      naive_solver.
Qed.

(** Preservation lemma *)
Lemma head_step_urns_support_set_subset e σ e2 σ2:
  head_step_rel e σ e2 σ2 ->
  urns_support_set (urns σ) ⊆ urns_support_set (urns σ2).
Proof.
  intros H.
  inversion H; simplify_eq; try done; simpl.
  (* - rewrite urns_subst_f_to_urns_support. *)
  (*   by erewrite <-urns_f_valid_support. *)
  (* - rewrite urns_subst_f_to_urns_support. *)
  (*   by erewrite <-urns_f_valid_support. *)
  eapply urns_support_set_insert_subset.
  intros Hcontra.
  assert (0∈(list_to_set (seq 0 (Z.to_nat z +1))%nat : gset nat))%nat; last set_solver.
  rewrite elem_of_list_to_set.
  rewrite elem_of_seq. lia.
Qed. 
    
Lemma head_step_preserve e σ e2 σ2:
  is_well_constructed_expr e = true ->
  expr_support_set e ⊆ urns_support_set (urns σ) ->
  map_Forall (λ (_ : loc) (v : d_prob_lang.val), is_well_constructed_val v = true)
    (heap σ) ->
  map_Forall (λ (_ : loc) (v : d_prob_lang.val), val_support_set v ⊆ urns_support_set (urns σ))
    (heap σ) ->
  head_step_rel e σ e2 σ2 ->
  is_well_constructed_expr e2 = true
  ∧ expr_support_set e2 ⊆ urns_support_set (urns σ2)
    ∧ map_Forall (λ (_ : loc) (v : d_prob_lang.val), is_well_constructed_val v = true) (heap σ2)
      ∧ map_Forall
          (λ (_ : loc) (v : d_prob_lang.val), val_support_set v ⊆ urns_support_set (urns σ2))
          (heap σ2)
.
Proof.
  intros He1 He2 Hforall1 Hforall2 Hstep.
  inversion Hstep; simplify_eq; simpl; simpl in *; andb_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - repeat split; try done.
    + by repeat apply is_well_constructed_subst'.
    + etrans; first apply expr_support_set_subst'.
      rewrite union_subseteq.
      split; last set_solver.
      etrans; first apply expr_support_set_subst'.
      set_solver.
  - repeat split; try done.
    + by eapply is_well_constructed_un_op_eval.
    + by erewrite <-val_support_set_un_op.
  - repeat split; try done.
    + by eapply is_well_constructed_bin_op_eval.
    + by erewrite <-val_support_set_bin_op. 
  - repeat split; try done; set_solver.
  - repeat split; try done; set_solver.
  (* - repeat split; try done. *)
  (*   + rewrite urns_subst_f_to_urns_support. *)
  (*     erewrite <-urns_f_valid_support; last done. *)
  (*     set_solver. *)
  (*   + rewrite urns_subst_f_to_urns_support. *)
  (*     by erewrite <-urns_f_valid_support. *)
  (* - repeat split; try done. *)
  (*   + rewrite urns_subst_f_to_urns_support. *)
  (*     erewrite <-urns_f_valid_support; last done. *)
  (*     set_solver. *)
  (*   + rewrite urns_subst_f_to_urns_support. *)
  (*     by erewrite <-urns_f_valid_support. *)
  - repeat split; try done; set_solver.
  - repeat split; try done; set_solver.
  - repeat split; try done; set_solver.
  - repeat split; try done; set_solver.
  - repeat split; try done.
    + apply map_Forall_union_2; last done.
      intros ??.
      rewrite heap_array_lookup.
      intros (?&?&?&H).
      apply lookup_replicate in H.
      by destruct!/=. 
    + apply map_Forall_union_2; last done.
      intros ??.
      rewrite heap_array_lookup.
      intros (?&?&?&H).
      apply lookup_replicate in H.
      destruct!/=.
      set_solver.
  - repeat split; try done; first set_solver.
    rewrite map_Forall_lookup in Hforall2.
    naive_solver.
  - repeat split; try done.
    + by apply map_Forall_insert_2.
    + apply map_Forall_insert_2; last done.
      set_solver.
  - split!.
  - repeat split; try done.
    + set_unfold.
      intros. simplify_eq.
      rewrite lookup_insert.
      split; last naive_solver.
      intros Hcontra.
      simplify_eq.
      assert (0∈(list_to_set (seq 0 (Z.to_nat z + 1)) : gset _))%nat; last set_solver.
      rewrite elem_of_list_to_set elem_of_seq; lia.
    + eapply map_Forall_impl; first apply Hforall2.
      simpl.
      intros.
      etrans; last eapply urns_support_set_insert_subset; first done.
      assert (0∈(list_to_set (seq 0 (Z.to_nat z + 1)) : gset _))%nat; last set_solver.
      rewrite elem_of_list_to_set elem_of_seq; lia.
Qed. 

Lemma prim_step_preserve e σ e2 σ2:
  is_well_constructed_expr e = true ->
  expr_support_set e ⊆ urns_support_set (urns σ) ->
  map_Forall (λ (_ : loc) (v : d_prob_lang.val), is_well_constructed_val v = true)
    (heap σ) ->
  map_Forall (λ (_ : loc) (v : d_prob_lang.val), val_support_set v ⊆ urns_support_set (urns σ))
    (heap σ) ->
  (prim_step e σ (e2, σ2) > 0)%R ->
  is_well_constructed_expr e2 = true
  ∧ expr_support_set e2 ⊆ urns_support_set (urns σ2)
    ∧ map_Forall (λ (_ : loc) (v : d_prob_lang.val), is_well_constructed_val v = true) (heap σ2)
      ∧ map_Forall
          (λ (_ : loc) (v : d_prob_lang.val), val_support_set v ⊆ urns_support_set (urns σ2))
          (heap σ2).
Proof.
  rewrite prim_step_iff.
  intros He1 He2 Hforall1 Hforall2.
  intros (K&e1'&e2'&<-&<-&H).
  simpl in *.
  rewrite head_step_support_equiv_rel in H.
  rewrite !is_well_constructed_fill in He1 *.
  apply andb_prop in He1 as [He1 He1'].
  rewrite He1'.
  rewrite !support_set_fill in He2 *.
  apply head_step_preserve in H as H'; [|(done||set_solver)..].
  destruct H' as (H1&H2&H3&H4).
  repeat split.
  - by rewrite H1. 
  - rewrite union_subseteq; split; last done.
    etrans; last by eapply head_step_urns_support_set_subset.
    set_solver.
  - done.
  - done.
Qed. 

Local Open Scope R.

(** Removed lemmas on couplings*)

(** Some useful lemmas to reason about language properties  *)

(* Inductive head_step_rel : expr → state → expr → state → Prop := *)
(* | RecDS f x e σ : *)
(*   det_head_step_rel (Rec f x e) σ (Val $ RecV f x e) σ *)
(* | PairDS v1 v2 σ : *)
(*   det_head_step_rel (Pair (Val v1) (Val v2)) σ (Val $ PairV v1 v2) σ *)
(* | InjLDS v σ : *)
(*   det_head_step_rel (InjL $ Val v) σ (Val $ InjLV v) σ *)
(* | InjRDS v σ : *)
(*   det_head_step_rel (InjR $ Val v) σ (Val $ InjRV v) σ *)
(* | BetaDS f x e1 v2 e' σ : *)
(*   e' = subst' x v2 (subst' f (RecV f x e1) e1) → *)
(*   det_head_step_rel (App (Val $ RecV f x e1) (Val v2)) σ e' σ *)
(* | UnOpDS op v v' σ : *)
(*   un_op_eval op v = Some v' → *)
(*   det_head_step_rel (UnOp op (Val v)) σ (Val v') σ *)
(* | BinOpDS op v1 v2 v' σ : *)
(*   bin_op_eval op v1 v2 = Some v' → *)
(*   det_head_step_rel (BinOp op (Val v1) (Val v2)) σ (Val v') σ *)
(* | IfTrueDS bl e1 e2 σ : *)
(*   urn_subst_equal σ bl true -> *)
(*   det_head_step_rel (If (Val $ LitV $ bl) e1 e2) σ e1 σ *)
(* | IfFalseDS bl e1 e2 σ : *)
(*   urn_subst_equal σ bl false -> *)
(*   det_head_step_rel (If (Val $ LitV $ bl) e1 e2) σ e2 σ *)
(* | FstDS v1 v2 σ : *)
(*   det_head_step_rel (Fst (Val $ PairV v1 v2)) σ (Val v1) σ *)
(* | SndDS v1 v2 σ : *)
(*   det_head_step_rel (Snd (Val $ PairV v1 v2)) σ (Val v2) σ *)
(* | CaseLDS v e1 e2 σ : *)
(*   det_head_step_rel (Case (Val $ InjLV v) e1 e2) σ (App e1 (Val v)) σ *)
(* | CaseRDS v e1 e2 σ : *)
(*   det_head_step_rel (Case (Val $ InjRV v) e1 e2) σ (App e2 (Val v)) σ *)
(* | AllocNDS z N v σ l : *)
(*   l = fresh_loc σ.(heap) → *)
(*   N = Z.to_nat z → *)
(*   (0 < N)%nat -> *)
(*   det_head_step_rel (AllocN (Val (LitV (LitInt z))) (Val v)) σ *)
(*     (Val $ LitV $ LitLoc l) (state_upd_heap_N l N v σ) *)
(* | LoadDS l v σ : *)
(*   σ.(heap) !! l = Some v → *)
(*   det_head_step_rel (Load (Val $ LitV $ LitLoc l)) σ (of_val v) σ *)
(* | StoreDS l v w σ : *)
(*   σ.(heap) !! l = Some v → *)
(*   det_head_step_rel (Store (Val $ LitV $ LitLoc l) (Val w)) σ *)
(*     (Val $ LitV LitUnit) (state_upd_heap <[l:=w]> σ). *)

Inductive head_step_pred : expr → state → Prop :=
| RecHSP f x e σ :
  head_step_pred (Rec f x e) σ
| PairHSP v1 v2 σ :
  head_step_pred (Pair (Val v1) (Val v2)) σ
| InjLHSP v σ :
  head_step_pred (InjL $ Val v) σ
| InjRHSP v σ :
  head_step_pred (InjR $ Val v) σ
| BetaSP f x e1 v2 σ :
  head_step_pred (App (Val $ RecV f x e1) (Val v2)) σ
| UnOpHSP op v σ v' :
  un_op_eval op v = Some v' →
  head_step_pred (UnOp op (Val v)) σ
| BinOpHSP op v1 v2 σ v' :
  bin_op_eval op v1 v2 = Some v' →
  head_step_pred (BinOp op (Val v1) (Val v2)) σ
| IfTrueHSP bl e1 e2 σ :
  urn_subst_equal σ bl true ->
  head_step_pred (If (Val $ LitV $ bl) e1 e2) σ
| IfFalseHSP bl e1 e2 σ :
  urn_subst_equal σ bl false ->
  head_step_pred (If (Val $ LitV $ bl) e1 e2) σ
| FstHSP v1 v2 σ :
  head_step_pred (Fst (Val $ PairV v1 v2)) σ
| SndHSP v1 v2 σ :
  head_step_pred (Snd (Val $ PairV v1 v2)) σ
| CaseLHSP v e1 e2 σ :
  head_step_pred (Case (Val $ InjLV v) e1 e2) σ
| CaseRHSP v e1 e2 σ :
  head_step_pred (Case (Val $ InjRV v) e1 e2) σ
| AllocNHSP z N v σ l :
  l = fresh_loc σ.(heap) →
  N = Z.to_nat z →
  (0 < N)%nat ->
  head_step_pred (AllocN (Val (LitV (LitInt z))) (Val v)) σ
| LoadHSP l v σ :
  σ.(heap) !! l = Some v →
  head_step_pred (Load (Val $ LitV $ LitLoc l)) σ
| StoreHSP l v w σ :
  σ.(heap) !! l = Some v →
  head_step_pred (Store (Val $ LitV $ LitLoc l) (Val w)) σ
| RandHSP (N : nat) σ (z:Z) bl :
  urn_subst_equal σ bl z ->
  N = Z.to_nat z →
  head_step_pred (rand #bl) σ
| DRandHSP (N : nat) σ (z:Z) bl :
  urn_subst_equal σ bl z ->
  N = Z.to_nat z →
  head_step_pred (drand #bl) σ.

(* Definition is_det_head_step (e1 : expr) (σ1 : state)  : bool := *)
(*   match e1 with *)
(*   | Rec f x e => true *)
(*   | Pair (Val v1) (Val v2) => true *)
(*   | InjL (Val v) => true *)
(*   | InjR (Val v) => true *)
(*   | App (Val (RecV f x e1)) (Val v2) => true *)
(*   | UnOp op (Val v)  => bool_decide(is_Some(un_op_eval op v)) *)
(*   | BinOp op (Val v1) (Val v2) => bool_decide (is_Some(bin_op_eval op v1 v2)) *)
(*   | If (Val (LitV bl)) e1 e2 => bool_decide (urn_subst_equal σ1 bl true \/ urn_subst_equal σ1 bl false) *)
(*   | Fst (Val (PairV v1 v2)) => true *)
(*   | Snd (Val (PairV v1 v2)) => true *)
(*   | Case (Val (InjLV v)) e1 e2 => true *)
(*   | Case (Val (InjRV v)) e1 e2 => true *)
(*   | AllocN (Val (LitV (LitInt z))) (Val v) => bool_decide (0 < Z.to_nat z)%nat *)
(*   | Load (Val (LitV (LitLoc l)))  => *)
(*       bool_decide (is_Some (σ1.(heap) !! l)) *)
(*   | Store (Val (LitV (LitLoc l))) (Val w) => *)
(*       bool_decide (is_Some (σ1.(heap) !! l)) *)
(*   (* | Tick (Val (LitV (LitInt z))) => true *) *)
(*   | _ => false *)
(*   end. *)

(* Lemma det_step_eq_tapes e1 σ1 e2 σ2 : *)
(*   det_head_step_rel e1 σ1 e2 σ2 → σ1.(urns) = σ2.(urns). *)
(* Proof. inversion 1; auto. Qed. *)

(* Inductive prob_head_step_pred : expr -> state -> Prop := *)
(* | IfPSP bl e1 e2 σ: *)
(*   ¬ urn_subst_equal σ bl (LitBool true) ->  *)
(*   ¬ urn_subst_equal σ bl (LitBool false) -> *)
(*   base_lit_type_check bl = Some BLTBool -> *)
(*   base_lit_support_set bl ⊆ urns_support_set (σ.(urns)) -> *)
(*   prob_head_step_pred (If (Val $ LitV $ bl) e1 e2) σ *)
(* | RandPSP (N : nat) σ (z:Z) bl : *)
(*   urn_subst_equal σ bl z -> *)
(*   N = Z.to_nat z → *)
(*   prob_head_step_pred (rand #bl) σ *)
(* | DRandPSP (N : nat) σ (z:Z) bl : *)
(*   urn_subst_equal σ bl z -> *)
(*   N = Z.to_nat z → *)
(*   prob_head_step_pred (drand #bl) σ. *)

(* Definition head_step_pred e1 σ1 := *)
(*   det_head_step_pred e1 σ1 ∨ prob_head_step_pred e1 σ1. *)

(* Lemma det_step_is_unique e1 σ1 e2 σ2 e3 σ3 : *)
(*   det_head_step_rel e1 σ1 e2 σ2 → *)
(*   det_head_step_rel e1 σ1 e3 σ3 → *)
(*   e2 = e3 ∧ σ2 = σ3. *)
(* Proof. *)
(*   intros H1 H2. *)
(*   inversion H1; inversion H2; simplify_eq; auto. *)
(*   - exfalso. by eapply (urn_subst_equal_not_unique _ _ true false). *)
(*   - exfalso. by eapply (urn_subst_equal_not_unique _ _ true false). *)
(* Qed.  *)

(* Lemma det_step_pred_ex_rel e1 σ1 : *)
(*   det_head_step_pred e1 σ1 ↔ ∃ e2 σ2, det_head_step_rel e1 σ1 e2 σ2. *)
(* Proof. *)
(*   split. *)
(*   - intro H; inversion H; simplify_eq; eexists; eexists. *)
(*     9:{ by apply IfFalseDS. } *)
(*     all: econstructor; eauto. *)
(*   - intros (e2 & (σ2 & H)); inversion H. *)
(*     9:{ by apply IfFalseDSP. } *)
(*     all: econstructor; eauto. *)
(* Qed. *)

(* Local Ltac solve_step_det := *)
(*   rewrite /pmf /=; *)
(*     repeat (rewrite bool_decide_eq_true_2 // || case_match); *)
(*   try (lra || lia || done || naive_solver). *)

(* Local Ltac inv_det_head_step := *)
(*   repeat *)
(*     match goal with *)
(*     | H : to_val _ = Some _ |- _ => apply of_to_val in H *)
(*     | H : is_det_head_step _ _ = true |- _ => *)
(*         rewrite /is_det_head_step in H; *)
(*         repeat (case_match in H; simplify_eq) *)
(*     | H : is_Some _ |- _ => destruct H *)
(*     | H : bool_decide  _ = true |- _ => rewrite bool_decide_eq_true in H; destruct_and?; destruct_or? *)
(*     | _ => progress simplify_map_eq/= *)
(*     end. *)

(* Lemma is_det_head_step_true e1 σ1 : *)
(*   is_det_head_step e1 σ1 = true ↔ det_head_step_pred e1 σ1. *)
(* Proof. *)
(*   split; intro H. *)
(*   - destruct e1; inv_det_head_step. *)
(*     6:{ by apply IfFalseDSP. } *)
(*     all: by econstructor. *)
(*   - inversion H; solve_step_det. *)
(* Qed. *)

(* Lemma det_head_step_singleton e1 σ1 e2 σ2 : *)
(*   det_head_step_rel e1 σ1 e2 σ2 → head_step e1 σ1 = dret (e2, σ2). *)
(* Proof. *)
(*   intros Hdet. *)
(*   apply pmf_1_eq_dret. *)
(*   inversion Hdet; simplify_eq/=; try case_match; *)
(*     simplify_option_eq; rewrite ?dret_1_1 //. *)
(*   - by case_bool_decide. *)
(*   - case_bool_decide; last done. *)
(*     exfalso. by eapply (urn_subst_equal_not_unique _ _ true false). *)
(*   - rewrite bool_decide_eq_true_2; last done. rewrite dret_1_1//. *)
(* Qed. *)

Lemma val_not_head_step e1 σ1 :
  is_Some (to_val e1) → ¬ head_step_pred e1 σ1.
Proof.
  intros [] Hs; inversion Hs; simplify_eq.
Qed.

Lemma head_step_pred_ex_rel e1 σ1 :
  head_step_pred e1 σ1 ↔ ∃ e2 σ2, head_step_rel e1 σ1 e2 σ2.
Proof.
  split.
  - intros H; inversion H; simplify_eq; try by (do 2 eexists; (by econstructor)).
    Unshelve. all : apply 0%fin.
  (* - pose proof set_urns_f_nonempty (urns σ1) as Hnonempty. *)
    (* apply size_pos_elem_of in Hnonempty as [f Hnonempty]. *)
    (* rewrite elem_of_set_urns_f_valid in Hnonempty. *)
    (* rename select (base_lit_type_check _ = _) into H'. *)
    (* eapply urn_subst_exists in H'; last by erewrite <-urns_f_valid_support. *)
    (* destruct H' as [[][H1 ]]; apply urn_subst_is_simple in H1 as H4; simplify_eq. *)
    (* rename select (bool) into b. *)
    (* destruct b. *)
    (* + eexists _, _. *)
    (*   eapply IfTrueS'; try done. *)
    (*   by intros ? ->%urns_subst_f_to_urns_unique_valid. *)
    (* + eexists _, _. *)
    (*   eapply IfFalseS'; try done. *)
    (*   by intros ? ->%urns_subst_f_to_urns_unique_valid. *)
    (*   Unshelve. all : apply 0%fin. *)
  - intros (?&?& H). inversion H; simplify_eq; by econstructor.
Qed. 
(*     Unshelve. *)
(*     apply 0%fin. *)
(*     Qed *)
(*       (try by (right; econstructor)). *)
(*     + rename select (urn_subst_equal _ _ _) into H'. *)
(*       right; econstructor; try done. *)
(*       * apply urn_subst_equal_well_typed in H'. *)
(*         by destruct!/=. *)
(*       * apply urn_subst_equal_support in H'. *)
(*         rewrite urns_subst_f_to_urns_support in H'. *)
(*         by erewrite urns_f_valid_support. *)
(*     + rename select (urn_subst_equal _ _ _) into H'. *)
(*       right; econstructor; try done. *)
(*       * apply urn_subst_equal_well_typed in H'. *)
(*         by destruct!/=. *)
(*       * apply urn_subst_equal_support in H'. *)
(*         rewrite urns_subst_f_to_urns_support in H'. *)
(*         by erewrite urns_f_valid_support. *)
(* Qed. *)

Lemma not_head_step_pred_dzero e1 σ1:
  ¬ head_step_pred e1 σ1 ↔ head_step e1 σ1 = dzero.
Proof.
  split.
  - intro Hnstep.
    apply dzero_ext.
    intros (e2 & σ2).
    destruct (Rlt_le_dec 0 (head_step e1 σ1 (e2, σ2))) as [H1%Rgt_lt | H2]; last first.
    { pose proof (pmf_pos (head_step e1 σ1) (e2, σ2)). destruct H2; lra. }
    apply head_step_support_equiv_rel in H1.
    assert (∃ e2 σ2, head_step_rel e1 σ1 e2 σ2) as Hex; eauto.
    by apply head_step_pred_ex_rel in Hex.
  - intros Hhead (e2 & σ2 & Hstep)%head_step_pred_ex_rel.
    apply head_step_support_equiv_rel in Hstep.
    assert (head_step e1 σ1 (e2, σ2) = 0); [|lra].
    rewrite Hhead //.
Qed.

Lemma head_step_pred_or_dzero e1 σ1 :
  head_step_pred e1 σ1
  ∨ head_step e1 σ1 = dzero.
Proof.
  destruct (Rlt_le_dec 0 (SeriesC (head_step e1 σ1))) as [H1%Rlt_gt | [HZ | HZ]].
  - pose proof (SeriesC_gtz_ex (head_step e1 σ1) (pmf_pos (head_step e1 σ1)) H1) as [[e2 σ2] Hρ].
    pose proof (head_step_support_equiv_rel e1 e2 σ1 σ2) as [H3 H4].
    specialize (H3 Hρ).
    assert (head_step_pred e1 σ1); last auto. 
    apply head_step_pred_ex_rel; eauto.
  - by pose proof (pmf_SeriesC_ge_0 (head_step e1 σ1))
      as ?%Rle_not_lt.
  - apply SeriesC_zero_dzero in HZ. eauto.
Qed.

Lemma head_step_pred_head_reducible e1 σ1:
  head_step_pred e1 σ1 <-> head_reducible e1 σ1.
Proof.
  split.
  - intros.
    rewrite /head_reducible.
    destruct (decide (head_step e1 σ1 = dzero)) as [H'|H'].
    + rewrite -not_head_step_pred_dzero in H'. naive_solver.
    + apply not_dzero_gt_0 in H'.
      apply SeriesC_gtz_ex in H'; naive_solver.
  - intros.
    destruct (head_step_pred_or_dzero e1 σ1) as [H'|H']; first done.
    rewrite /head_reducible in H.
    simpl in H.
    rewrite H' in H. destruct!/=. inv_distr.
Qed. 

(** tapes specific *)
(* Lemma head_step_dzero_upd_tapes α e σ N zs z  : *)
(*   α ∈ dom σ.(tapes) → *)
(*   head_step e σ = dzero → *)
(*   head_step e (state_upd_tapes <[α:=(N; zs ++ [z]) : tape]> σ) = dzero. *)
(* Proof. *)
(*   intros Hdom Hz. *)
(*   destruct e; simpl in *; *)
(*     repeat case_match; done || inv_dzero; simplify_map_eq. *)
(*   (* TODO: [simplify_map_eq] should solve this? *) *)
(*   - destruct (decide (α = l1)). *)
(*     + simplify_eq. *)
(*       by apply not_elem_of_dom_2 in H5. *)
(*     + rewrite lookup_insert_ne // in H6. *)
(*       rewrite H5 in H6. done. *)
(*   - destruct (decide (α = l1)). *)
(*     + simplify_eq. *)
(*       by apply not_elem_of_dom_2 in H5. *)
(*     + rewrite lookup_insert_ne // in H6. *)
(*       rewrite H5 in H6. done. *)
(*   - destruct (decide (α = l1)). *)
(*     + simplify_eq. *)
(*       by apply not_elem_of_dom_2 in H5. *)
(*     + rewrite lookup_insert_ne // in H6. *)
(*       rewrite H5 in H6. done. *)
(* Qed. *)

(* Lemma det_head_step_upd_tapes N e1 σ1 e2 σ2 α z zs : *)
(*   det_head_step_rel e1 σ1 e2 σ2 → *)
(*   tapes σ1 !! α = Some (N; zs) → *)
(*   det_head_step_rel *)
(*     e1 (state_upd_tapes <[α := (N; zs ++ [z])]> σ1) *)
(*     e2 (state_upd_tapes <[α := (N; zs ++ [z])]> σ2). *)
(* Proof. *)
(*   inversion 1; try econstructor; eauto. *)
(*   (* Unsolved case *) *)
(*   intros. rewrite state_upd_tapes_heap. econstructor; eauto. *)
(* Qed. *)

(** * Lemmas about updating urns *)
Lemma upd_urn_some σ α ns :
  urns (state_upd_urns <[α:= ns]> σ) !! α = Some ns.
Proof.
  rewrite /state_upd_urns /=. rewrite lookup_insert //.
Qed.

Lemma upd_urn_some_trivial σ α bs:
  urns σ !! α = Some bs →
  state_upd_urns <[α:=urns σ !!! α]> σ = σ.
Proof.
  destruct σ. simpl.
  intros H.
  rewrite (lookup_total_correct _ _ _ H).
  f_equal.
  by apply insert_id.
Qed.

Lemma upd_diff_urn_comm σ α β bs bs':
  α ≠ β →
  state_upd_urns <[β:= bs]> (state_upd_urns <[α := bs']> σ) =
    state_upd_urns <[α:= bs']> (state_upd_urns <[β := bs]> σ).
Proof.
  intros. rewrite /state_upd_urns /=. rewrite insert_commute //.
Qed.

Lemma upd_diff_urn_tot σ α β bs:
  α ≠ β →
  urns σ !!! α = urns (state_upd_urns <[β:=bs]> σ) !!! α.
Proof. symmetry ; by rewrite lookup_total_insert_ne. Qed.

Lemma upd_urn_twice σ β bs bs' :
  state_upd_urns <[β:= bs]> (state_upd_urns <[β:= bs']> σ) = state_upd_urns <[β:= bs]> σ.
Proof. rewrite /state_upd_urns insert_insert //. Qed.

Lemma fresh_loc_upd_some σ α bs bs' :
  (urns σ) !! α = Some bs →
  fresh_loc (urns σ) = (fresh_loc (<[α:= bs']> (urns σ))).
Proof.
  intros Hα.
  apply fresh_loc_eq_dom.
  by rewrite dom_insert_lookup_L.
Qed.

Lemma elem_fresh_ne {V} (ls : gmap loc V) k v :
  ls !! k = Some v → fresh_loc ls ≠ k.
Proof.
  intros; assert (is_Some (ls !! k)) as Hk by auto.
  pose proof (fresh_loc_is_fresh ls).
  rewrite -elem_of_dom in Hk.
  set_solver.
Qed.

Lemma fresh_loc_upd_swap σ α bs bs' bs'' :
  (urns σ) !! α = Some bs →
  state_upd_urns <[fresh_loc (urns σ):=bs']> (state_upd_urns <[α:=bs'']> σ)
  = state_upd_urns <[α:=bs'']> (state_upd_urns <[fresh_loc (urns σ):=bs']> σ).
Proof.
  intros H.
  apply elem_fresh_ne in H.
  unfold state_upd_urns.
  by rewrite insert_commute.
Qed.

Lemma fresh_loc_lookup σ α bs bs' :
  (urns σ) !! α = Some bs →
  (urns (state_upd_urns <[fresh_loc (urns σ):=bs']> σ)) !! α = Some bs.
Proof.
  intros H.
  pose proof (elem_fresh_ne _ _ _ H).
  by rewrite lookup_insert_ne.
Qed.

(* Lemma prim_step_empty_tape σ α (z:Z) K N : *)
(*   (urns σ) !! α = Some (N; []) -> prim_step (fill K (rand(#lbl:α) #z)) σ = prim_step (fill K (rand #z)) σ. *)
(* Proof. *)
(*   intros H. *)
(*   rewrite !fill_dmap; [|done|done]. *)
(*   rewrite /dmap. *)
(*   f_equal. *)
(*   simpl. apply distr_ext; intros [e s]. *)
(*   erewrite !head_prim_step_eq; simpl; last first. *)
(*   (** type classes dont work? *) *)
(*   { destruct (decide (Z.to_nat z=N)) as [<-|?] eqn:Heqn. *)
(*     all: eexists (_, σ); eapply head_step_support_equiv_rel; *)
(*       eapply head_step_support_eq; simpl; last first. *)
(*     - rewrite H. rewrite bool_decide_eq_true_2; last lia. *)
(*       eapply dmap_unif_nonzero; last done. *)
(*       intros ???. simplify_eq. done. *)
(*     - apply Rinv_pos. pose proof pos_INR_S (Z.to_nat z). lra. *)
(*     - rewrite H. case_bool_decide as H0; first lia. *)
(*       eapply dmap_unif_nonzero; last done. *)
(*       intros ???. by simplify_eq. *)
(*     - apply Rinv_pos. pose proof pos_INR_S (Z.to_nat z). lra. *)
(*   } *)
(*   { eexists (_, σ); eapply head_step_support_equiv_rel; *)
(*       eapply head_step_support_eq; simpl; last first. *)
(*     - eapply dmap_unif_nonzero; last done. *)
(*       intros ???. simplify_eq. done. *)
(*     - apply Rinv_pos. pose proof pos_INR_S (Z.to_nat z). lra. *)
(*   } rewrite H. *)
(*   case_bool_decide; last done. *)
(*   subst. done. *)
(*   Unshelve. *)
(*   all: exact (0%fin). *)
(* Qed. *)
  

(** * remove drand 
 ** * Note that this function also checks whether everything is simple
      i.e. no thunks or urn labels.
 *)
From clutch.delay_prob_lang Require Export lang.

Fixpoint remove_drand_expr e:=
  match e with
  | Val v => v' ← remove_drand_val v; Some $ Val v'
  | Var x => Some $ Var x
  | Rec f x e => e' ← (remove_drand_expr e); Some $ Rec f x e'
  | App e1 e2 => e1' ← (remove_drand_expr e1); e2' ← (remove_drand_expr e2); Some $ App e1' e2'
  | UnOp op e => e' ← (remove_drand_expr e); Some $ UnOp op e'
  | BinOp op e1 e2 => e1' ← (remove_drand_expr e1); e2' ← (remove_drand_expr e2); Some $ BinOp op e1' e2'
  | If e0 e1 e2 => e0' ← (remove_drand_expr e0); e1' ← (remove_drand_expr e1); e2' ← (remove_drand_expr e2); Some $ If e0' e1' e2'
  | Pair e1 e2 => e1' ← (remove_drand_expr e1); e2' ← (remove_drand_expr e2); Some $ Pair e1' e2'
  | Fst e => e' ← (remove_drand_expr e); Some $ Fst e'
  | Snd e => e' ← (remove_drand_expr e); Some $ Snd e'
  | InjL e => e' ← (remove_drand_expr e); Some $ InjL e'
  | InjR e => e' ← (remove_drand_expr e); Some $ InjR e'
  | Case e0 e1 e2 => e0' ← (remove_drand_expr e0); e1' ← (remove_drand_expr e1); e2' ← (remove_drand_expr e2); Some $ Case e0' e1' e2'
  | AllocN e1 e2 => e1' ← (remove_drand_expr e1); e2' ← (remove_drand_expr e2); Some $ AllocN e1' e2'
  | Load e => e' ← (remove_drand_expr e); Some $ Load e'
  | Store e1 e2 => e1' ← (remove_drand_expr e1); e2' ← (remove_drand_expr e2); Some $ Store e1' e2'
  | Rand e => e' ← (remove_drand_expr e); Some $ Rand e'
  | DRand e => e' ← (remove_drand_expr e); Some $ Rand e'
  end
with remove_drand_val v : option val:= 
  match v with
  | LitV l => if is_simple_base_lit l then Some $ LitV l else None
  | RecV f x e => e' ← remove_drand_expr e; Some $ RecV f x e'
  | PairV v1 v2 => v1' ← (remove_drand_val v1); v2' ← (remove_drand_val v2); Some $ PairV v1' v2'
  | InjLV v => v' ← (remove_drand_val v); Some $ InjLV v'
  | InjRV v => v' ← (remove_drand_val v); Some $ InjRV v'
  end.

Lemma remove_drand_expr_urn_subst f e e':
  remove_drand_expr e = Some e' ->
  urn_subst_expr f e = Some e'.
Proof.
  revert e e'.
  apply (expr_mut (λ e, ∀ e', remove_drand_expr e = Some e' → urn_subst_expr f e = Some e' ) (λ v, ∀ v', remove_drand_val v = Some v' → urn_subst_val f v = Some v')); simpl; repeat setoid_rewrite bind_Some; intros; destruct!/=.
  19:{ case_match; last done.
       simplify_eq.
       rename select base_lit into bl.
       destruct bl; simplify_eq; naive_solver.
  }
  all: naive_solver.
Qed.   
  
