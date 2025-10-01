From Coq Require Import Reals Psatz.
From stdpp Require Import functions gmap stringmap fin_sets.
From clutch.prelude Require Import stdpp_ext NNRbar fin uniform_list.
From clutch.prob Require Import distribution couplings couplings_app.
From clutch.common Require Import ectx_language.
From clutch.prob_lang Require Import tactics notation.
From clutch.prob_lang Require Export lang.
From clutch.prob Require Import distribution couplings.
From iris.prelude Require Import options.
Set Default Proof Using "Type*".
(* This file contains some metatheory about the [prob_lang] language *)

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
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Load e =>
     is_closed_expr X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | AllocN e1 e2 | Store e1 e2 | Rand e1 e2 =>
     is_closed_expr X e1 && is_closed_expr X e2
  | If e0 e1 e2 | Case e0 e1 e2 =>
     is_closed_expr X e0 && is_closed_expr X e1 && is_closed_expr X e2
  | AllocTape e => is_closed_expr X e
  | Tick e => is_closed_expr X e
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
  | AllocTape e => AllocTape (subst_map vs e)
  | Rand e1 e2 => Rand (subst_map vs e1) (subst_map vs e2)
  | Tick e => Tick (subst_map vs e)
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
  rewrite /bin_op_eval /bin_op_eval_bool /bin_op_eval_int /bin_op_eval_loc;
    repeat case_match; by naive_solver.
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

Local Open Scope R.

Lemma iterM_state_step_unfold σ (N p:nat) α xs :
  σ.(tapes) !! α = Some (N%nat; xs) ->
  (iterM p (λ σ1', state_step σ1' α) σ) =
  dmap (λ v, state_upd_tapes <[α := (N%nat; xs ++ v)]> σ)
    (dunifv N p).
Proof.
  revert σ N α xs.
  induction p as [|p' IH].
  { (* base case *)
    intros. simpl.
    apply distr_ext.
    intros. rewrite /dret/dret_pmf{1}/pmf/=.
    rewrite dmap_unfold_pmf.

    (** Why doesnt this work?? *)
    (* rewrite (@SeriesC_subset _ _ _ (λ x, x= (nil:list (fin (S N)))) _ _). *)
    (* - rewrite (SeriesC_singleton_dependent nil). *)
    
    erewrite (SeriesC_ext ).
    - erewrite (SeriesC_singleton_dependent [] (λ a0:list (fin (S N)), dunifv N 0 a0 * (if bool_decide (a = state_upd_tapes <[α:=(N; xs ++ a0)]> σ) then 1 else 0))). 
      rewrite dunifv_pmf. simpl.
      case_bool_decide.
      + rewrite bool_decide_eq_true_2; [lra|]. rewrite app_nil_r.
        rewrite state_upd_tapes_no_change; done.
      + rewrite bool_decide_eq_false_2; [lra|]. rewrite app_nil_r.
        rewrite state_upd_tapes_no_change; done.
    - intros. simpl.
      symmetry.
      case_bool_decide; first done.
      rewrite dunifv_pmf.
      rewrite bool_decide_eq_false_2; first lra.
      intros ?%nil_length_inv. done.
  }
  (* inductive case *)
  intros σ N α xs Ht.
  replace (S p') with (p'+1)%nat; last lia.
  rewrite iterM_plus; simpl.
  erewrite IH; last done.
  erewrite dbind_ext_right; last first.
  { intros. apply dret_id_right. }
  apply distr_ext. intros σ'. rewrite dmap_unfold_pmf.
  replace (p'+1)%nat with (S p') by lia.
  assert (Decision (∃ v: list (fin (S N)), length v = S p' /\ σ' = state_upd_tapes <[α:=(N; xs ++ v)]> σ)) as Hdec.
  { (* can be improved *)
    apply make_decision. }
  destruct (decide (∃ v: list (fin (S N)), length v = S p' /\ σ' = state_upd_tapes <[α:=(N; xs ++ v)]> σ)) as [K|K].
  - (* σ' is reachable *)
    destruct K as [v [Hlen ->]].
    rewrite (SeriesC_subset (λ a, a = v)); last first.
    { intros a Ha.
      rewrite bool_decide_eq_false_2; first lra.
      move => /state_upd_tapes_same. intros L. simplify_eq.
    }
    rewrite SeriesC_singleton_dependent. rewrite bool_decide_eq_true_2; last done.
    rewrite dunifv_pmf. rewrite Rmult_1_r.
    remember (/ (S N ^ S p')%nat) as val eqn:Hval.
    rewrite /dbind/dbind_pmf{1}/pmf/=.
    rewrite (SeriesC_subset (λ a, a = state_upd_tapes <[α := (N; xs ++ take p' v)]> σ)).
    + rewrite SeriesC_singleton_dependent. erewrite state_step_unfold; last first.
      { simpl. rewrite lookup_insert. done. }
      rewrite !dmap_unfold_pmf.
      rewrite (SeriesC_subset (λ a, a = take p' v)); last first.
      { intros. rewrite bool_decide_eq_false_2; first lra.
        move => /state_upd_tapes_same. intros L. simplify_eq. 
      }
      rewrite SeriesC_singleton_dependent.
      rewrite bool_decide_eq_true_2; last done.
      rewrite dunifv_pmf.
      rewrite bool_decide_eq_true_2; last first.
      { rewrite firstn_length_le; lia. }
      assert (is_Some (last v)) as [x Hsome].
      { rewrite last_is_Some. intros ?. subst. done. }
      rewrite (SeriesC_subset (λ a, a = x)); last first.
      { intros a H'. rewrite bool_decide_eq_false_2; first lra.
        rewrite state_upd_tapes_twice. move => /state_upd_tapes_same.
        rewrite <-app_assoc. intros K.
        simplify_eq. apply H'.
        rewrite -K in Hsome.
        rewrite last_snoc in Hsome. by simplify_eq.
      }
      rewrite SeriesC_singleton_dependent.
      rewrite /dunifP dunif_pmf. rewrite bool_decide_eq_true_2; last rewrite state_upd_tapes_twice.
      * rewrite bool_decide_eq_true_2; last done.
        rewrite Hval.
        cut ( / INR (S N ^ p') * (/ INR (S N)) = / INR (S N ^ S p')); first lra.
        rewrite -Rinv_mult.
        f_equal. rewrite -mult_INR. f_equal. simpl. lia.
      * rewrite -app_assoc. repeat f_equal.
        rewrite <-(firstn_all v) at 1.
        rewrite Hlen. erewrite take_S_r; first done.
        rewrite -Hsome last_lookup.
        f_equal. rewrite Hlen. done.
    + (* prove that σ' is not an intermediate step*)
      intros σ'.
      intros Hσ.
      assert (dmap (λ v0, state_upd_tapes <[α:=(N; xs ++ v0)]> σ) (dunifv N p') σ' *  state_step σ' α (state_upd_tapes <[α:=(N; xs ++ v)]> σ) >= 0) as [H|H]; last done.
      { apply Rle_ge. apply Rmult_le_pos; auto. }
      exfalso.
      apply Rmult_pos_cases in H as [[H1 H2]|[? H]]; last first.
      { pose proof pmf_pos (state_step σ' α)  (state_upd_tapes <[α:=(N; xs ++ v)]> σ). lra. }
      rewrite dmap_pos in H1.
      destruct H1 as [v' [-> H1]].
      apply Hσ. repeat f_equal.
      erewrite state_step_unfold in H2; last first.
      { simpl. apply lookup_insert. }
      apply dmap_pos in H2.
      destruct H2 as [a [H2?]].
      rewrite state_upd_tapes_twice in H2.
      apply state_upd_tapes_same in H2. rewrite -app_assoc in H2. simplify_eq.
      rewrite take_app_length'; first done.
      rewrite app_length in Hlen. simpl in *; lia.
  - (* σ' is not reachable, i.e. both sides are zero *)
    rewrite SeriesC_0; last first.
    { intros x.
      assert (0<=dunifv N (S p') x) as [H|<-] by auto; last lra.
      apply Rlt_gt in H.
      rewrite -dunifv_pos in H.
      rewrite bool_decide_eq_false_2; [lra|naive_solver].
    }
    rewrite /dbind/dbind_pmf{1}/pmf/=.
    apply SeriesC_0.
    intros σ''.
    rewrite /dmap/dbind/dbind_pmf{1}/pmf/=.
    setoid_rewrite dunifv_pmf.
    assert (SeriesC
    (λ a : list (fin (S N)),
       (if bool_decide (length a = p') then / (S N ^ p')%nat else 0) *
         dret (state_upd_tapes <[α:=(N; xs ++ a)]> σ) σ'') * state_step σ'' α σ' >= 0) as [H|H]; last done.
    { apply Rle_ge. apply Rmult_le_pos; auto. apply SeriesC_ge_0'.
      intros. apply Rmult_le_pos; auto. case_bool_decide; try lra.
      rewrite -Rdiv_1_l. apply Rcomplements.Rdiv_le_0_compat; first lra.
      apply lt_0_INR.
      epose proof Nat.pow_le_mono_r (S N) 0 p' _ _ as H0; simpl in H0; lia.
      Unshelve.
      all: lia.
    }
    apply Rmult_pos_cases in H as [[H1 H2]|[? H]]; last first.
    { pose proof pmf_pos (state_step σ'' α) σ'. lra. }
    epose proof SeriesC_gtz_ex _ _ H1. simpl in *.
    destruct H as [v H].
    apply Rmult_pos_cases in H as [[? H]|[]]; last first.
    { epose proof pmf_pos (dret (state_upd_tapes <[α:=(N; xs ++ v)]> σ)) σ''. lra. }
    apply dret_pos in H; subst.
    case_bool_decide; last lra.
    erewrite state_step_unfold in H2; last first.
    { simpl. rewrite lookup_insert. done. }
    exfalso.
    apply K. rewrite dmap_pos in H2. destruct H2 as [x[-> H2]]. subst.
    setoid_rewrite state_upd_tapes_twice.
    rewrite -app_assoc.
    exists (v++[x]); rewrite app_length; simpl; split; first lia. done.
    Unshelve.
    simpl.
    intros. case_bool_decide; last real_solver.
    apply Rmult_le_pos; last auto.
    rewrite -Rdiv_1_l. apply Rcomplements.Rdiv_le_0_compat; first lra.
    apply lt_0_INR.
    epose proof Nat.pow_le_mono_r (S N) 0 p' _ _ as H0; simpl in H0; lia.
    Unshelve.
    all: lia.
Qed.

Lemma Rcoupl_state_state_exp N p M σ σₛ α αₛ xs zs
  (f:(list (fin (S N))) -> fin (S M))
  (Hinj: forall l1 l2, length l1 = p -> length l2 = p -> f l1 = f l2 -> l1 = l2):
  (S N ^ p = S M)%nat->
  σ.(tapes) !! α = Some (N%nat; xs) ->
  σₛ.(tapes) !! αₛ = Some (M%nat; zs) ->
  Rcoupl
    (iterM p (λ σ1', state_step σ1' α) σ)
    (state_step σₛ αₛ)
    (λ σ1' σ2', ∃ (xs':list(fin (S N))) (z:fin (S M)),
        length xs' = p /\
        σ1' = state_upd_tapes <[α := (N%nat; xs ++ xs')]> σ ∧
        σ2' = state_upd_tapes <[αₛ := (M%nat; zs ++ [z])]> σₛ /\
        f xs' = z
    ).
Proof.
  intros H Hσ Hσₛ.
  erewrite state_step_unfold; last done.
  erewrite iterM_state_step_unfold; last done.
  apply Rcoupl_dmap.
  exists (dmap (λ v, (v, f v)) (dunifv N p)).
  split.
  - split; apply distr_ext.
    + intros v. rewrite lmarg_pmf.
      rewrite (SeriesC_ext _
                 (λ b : fin (S M), if bool_decide (b=f v) then dmap (λ v0, (v0, f v0)) (dunifv N p) (v, b) else 0)).
      * rewrite SeriesC_singleton_dependent. rewrite dmap_unfold_pmf.
        rewrite (SeriesC_ext _
                   (λ a, if bool_decide (a = v) then dunifv N p a * (if bool_decide ((v, f v) = (a, f a)) then 1 else 0) else 0)).
        { rewrite SeriesC_singleton_dependent. rewrite bool_decide_eq_true_2; first lra.
          done. }
        intros.
        case_bool_decide; simplify_eq.
        -- rewrite bool_decide_eq_true_2; done.
        -- rewrite bool_decide_eq_false_2; first lra.
           intros ->. done.
      * intros. case_bool_decide; first done.
        rewrite dmap_unfold_pmf.
        setoid_rewrite bool_decide_eq_false_2.
        -- rewrite SeriesC_scal_r; lra.
        -- intros ?. simplify_eq.
    + intros a.
      rewrite rmarg_pmf.
      assert (∃ x, length x = p /\ f x = a) as [x [H1 H2]].
      {
        assert (Surj eq (λ x:vec(fin(S N)) p, f (vec_to_list x)) ) as K. 
        - apply finite_inj_surj; last first. 
          + rewrite vec_card !fin_card.
            done.
          + intros v1 v2 Hf.
            apply vec_to_list_inj2.
            apply Hinj; last done.
            * by rewrite vec_to_list_length.
            * by rewrite vec_to_list_length.
        - pose proof K a as [v K'].
          subst.
          exists (vec_to_list v). split; last done.
          apply vec_to_list_length.
      }
      rewrite (SeriesC_subset (λ x', x' = x)).
      * rewrite SeriesC_singleton_dependent. rewrite dmap_unfold_pmf.
        rewrite (SeriesC_subset (λ x', x' = x)).
        -- rewrite SeriesC_singleton_dependent. rewrite bool_decide_eq_true_2; last by subst.
           rewrite dunifv_pmf /dunifP dunif_pmf.
           rewrite bool_decide_eq_true_2; last done. rewrite H. lra.
        -- intros. subst. rewrite bool_decide_eq_false_2; first lra.
           naive_solver.
      * intros ? H0. subst. rewrite dmap_unfold_pmf.
        apply SeriesC_0. intros x0.
        assert (0<=dunifv N (length x) x0) as [H1|<-] by auto; last lra.
        apply Rlt_gt in H1. rewrite <-dunifv_pos in H1.
        rewrite bool_decide_eq_false_2; first lra.
        intros ?. simplify_eq.
        apply H0. by apply Hinj. 
  - intros []. rewrite dmap_pos.
    intros [?[? Hpos]]. simplify_eq.
    rewrite -dunifv_pos in Hpos.
    naive_solver.
Qed.

(** Some useful lemmas to reason about language properties  *)

Inductive det_head_step_rel : expr → state → expr → state → Prop :=
| RecDS f x e σ :
  det_head_step_rel (Rec f x e) σ (Val $ RecV f x e) σ
| PairDS v1 v2 σ :
  det_head_step_rel (Pair (Val v1) (Val v2)) σ (Val $ PairV v1 v2) σ
| InjLDS v σ :
  det_head_step_rel (InjL $ Val v) σ (Val $ InjLV v) σ
| InjRDS v σ :
  det_head_step_rel (InjR $ Val v) σ (Val $ InjRV v) σ
| BetaDS f x e1 v2 e' σ :
  e' = subst' x v2 (subst' f (RecV f x e1) e1) →
  det_head_step_rel (App (Val $ RecV f x e1) (Val v2)) σ e' σ
| UnOpDS op v v' σ :
  un_op_eval op v = Some v' →
  det_head_step_rel (UnOp op (Val v)) σ (Val v') σ
| BinOpDS op v1 v2 v' σ :
  bin_op_eval op v1 v2 = Some v' →
  det_head_step_rel (BinOp op (Val v1) (Val v2)) σ (Val v') σ
| IfTrueDS e1 e2 σ :
  det_head_step_rel (If (Val $ LitV $ LitBool true) e1 e2) σ e1 σ
| IfFalseDS e1 e2 σ :
  det_head_step_rel (If (Val $ LitV $ LitBool false) e1 e2) σ e2 σ
| FstDS v1 v2 σ :
  det_head_step_rel (Fst (Val $ PairV v1 v2)) σ (Val v1) σ
| SndDS v1 v2 σ :
  det_head_step_rel (Snd (Val $ PairV v1 v2)) σ (Val v2) σ
| CaseLDS v e1 e2 σ :
  det_head_step_rel (Case (Val $ InjLV v) e1 e2) σ (App e1 (Val v)) σ
| CaseRDS v e1 e2 σ :
  det_head_step_rel (Case (Val $ InjRV v) e1 e2) σ (App e2 (Val v)) σ
| AllocNDS z N v σ l :
  l = fresh_loc σ.(heap) →
  N = Z.to_nat z →
  (0 < N)%nat ->
  det_head_step_rel (AllocN (Val (LitV (LitInt z))) (Val v)) σ
    (Val $ LitV $ LitLoc l) (state_upd_heap_N l N v σ)
| LoadDS l v σ :
  σ.(heap) !! l = Some v →
  det_head_step_rel (Load (Val $ LitV $ LitLoc l)) σ (of_val v) σ
| StoreDS l v w σ :
  σ.(heap) !! l = Some v →
  det_head_step_rel (Store (Val $ LitV $ LitLoc l) (Val w)) σ
    (Val $ LitV LitUnit) (state_upd_heap <[l:=w]> σ)
| TickDS z σ :
  det_head_step_rel (Tick (Val $ LitV $ LitInt z)) σ (Val $ LitV $ LitUnit) σ.

Inductive det_head_step_pred : expr → state → Prop :=
| RecDSP f x e σ :
  det_head_step_pred (Rec f x e) σ
| PairDSP v1 v2 σ :
  det_head_step_pred (Pair (Val v1) (Val v2)) σ
| InjLDSP v σ :
  det_head_step_pred (InjL $ Val v) σ
| InjRDSP v σ :
  det_head_step_pred (InjR $ Val v) σ
| BetaDSP f x e1 v2 σ :
  det_head_step_pred (App (Val $ RecV f x e1) (Val v2)) σ
| UnOpDSP op v σ v' :
  un_op_eval op v = Some v' →
  det_head_step_pred (UnOp op (Val v)) σ
| BinOpDSP op v1 v2 σ v' :
  bin_op_eval op v1 v2 = Some v' →
  det_head_step_pred (BinOp op (Val v1) (Val v2)) σ
| IfTrueDSP e1 e2 σ :
  det_head_step_pred (If (Val $ LitV $ LitBool true) e1 e2) σ
| IfFalseDSP e1 e2 σ :
  det_head_step_pred (If (Val $ LitV $ LitBool false) e1 e2) σ
| FstDSP v1 v2 σ :
  det_head_step_pred (Fst (Val $ PairV v1 v2)) σ
| SndDSP v1 v2 σ :
  det_head_step_pred (Snd (Val $ PairV v1 v2)) σ
| CaseLDSP v e1 e2 σ :
  det_head_step_pred (Case (Val $ InjLV v) e1 e2) σ
| CaseRDSP v e1 e2 σ :
  det_head_step_pred (Case (Val $ InjRV v) e1 e2) σ
| AllocNDSP z N v σ l :
  l = fresh_loc σ.(heap) →
  N = Z.to_nat z →
  (0 < N)%nat ->
  det_head_step_pred (AllocN (Val (LitV (LitInt z))) (Val v)) σ
| LoadDSP l v σ :
  σ.(heap) !! l = Some v →
  det_head_step_pred (Load (Val $ LitV $ LitLoc l)) σ
| StoreDSP l v w σ :
  σ.(heap) !! l = Some v →
  det_head_step_pred (Store (Val $ LitV $ LitLoc l) (Val w)) σ
| TickDSP z σ :
  det_head_step_pred (Tick (Val $ LitV $ LitInt z)) σ.

Definition is_det_head_step (e1 : expr) (σ1 : state)  : bool :=
  match e1 with
  | Rec f x e => true
  | Pair (Val v1) (Val v2) => true
  | InjL (Val v) => true
  | InjR (Val v) => true
  | App (Val (RecV f x e1)) (Val v2) => true
  | UnOp op (Val v)  => bool_decide(is_Some(un_op_eval op v))
  | BinOp op (Val v1) (Val v2) => bool_decide (is_Some(bin_op_eval op v1 v2))
  | If (Val (LitV (LitBool true))) e1 e2 => true
  | If (Val (LitV (LitBool false))) e1 e2 => true
  | Fst (Val (PairV v1 v2)) => true
  | Snd (Val (PairV v1 v2)) => true
  | Case (Val (InjLV v)) e1 e2 => true
  | Case (Val (InjRV v)) e1 e2 => true
  | AllocN (Val (LitV (LitInt z))) (Val v) => bool_decide (0 < Z.to_nat z)%nat
  | Load (Val (LitV (LitLoc l)))  =>
      bool_decide (is_Some (σ1.(heap) !! l))
  | Store (Val (LitV (LitLoc l))) (Val w) =>
      bool_decide (is_Some (σ1.(heap) !! l))
  | Tick (Val (LitV (LitInt z))) => true
  | _ => false
  end.

Lemma det_step_eq_tapes e1 σ1 e2 σ2 :
  det_head_step_rel e1 σ1 e2 σ2 → σ1.(tapes) = σ2.(tapes).
Proof. inversion 1; auto. Qed.

Inductive prob_head_step_pred : expr -> state -> Prop :=
| AllocTapePSP σ N z :
  N = Z.to_nat z →
  prob_head_step_pred (alloc #z) σ
| RandTapePSP α σ N n ns z :
  N = Z.to_nat z →
  σ.(tapes) !! α = Some ((N; n :: ns) : tape) →
  prob_head_step_pred (rand(#lbl:α) #z) σ
| RandEmptyPSP N α σ z :
  N = Z.to_nat z →
  σ.(tapes) !! α = Some ((N; []) : tape) →
  prob_head_step_pred (rand(#lbl:α) #z) σ
| RandTapeOtherPSP N M α σ ns z :
  N ≠ M →
  M = Z.to_nat z →
  σ.(tapes) !! α = Some ((N; ns) : tape) →
  prob_head_step_pred (rand(#lbl:α) #z) σ
| RandNoTapePSP (N : nat) σ z :
  N = Z.to_nat z →
  prob_head_step_pred (rand #z) σ.

Definition head_step_pred e1 σ1 :=
  det_head_step_pred e1 σ1 ∨ prob_head_step_pred e1 σ1.

Lemma det_step_is_unique e1 σ1 e2 σ2 e3 σ3 :
  det_head_step_rel e1 σ1 e2 σ2 →
  det_head_step_rel e1 σ1 e3 σ3 →
  e2 = e3 ∧ σ2 = σ3.
Proof.
  intros H1 H2.
  inversion H1; inversion H2; simplify_eq; auto.
Qed.

Lemma det_step_pred_ex_rel e1 σ1 :
  det_head_step_pred e1 σ1 ↔ ∃ e2 σ2, det_head_step_rel e1 σ1 e2 σ2.
Proof.
  split.
  - intro H; inversion H; simplify_eq; eexists; eexists; econstructor; eauto.
  - intros (e2 & (σ2 & H)); inversion H ; econstructor; eauto.
Qed.

Local Ltac solve_step_det :=
  rewrite /pmf /=;
    repeat (rewrite bool_decide_eq_true_2 // || case_match);
  try (lra || lia || done).

Local Ltac inv_det_head_step :=
  repeat
    match goal with
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : is_det_head_step _ _ = true |- _ =>
        rewrite /is_det_head_step in H;
        repeat (case_match in H; simplify_eq)
    | H : is_Some _ |- _ => destruct H
    | H : bool_decide  _ = true |- _ => rewrite bool_decide_eq_true in H; destruct_and?
    | _ => progress simplify_map_eq/=
    end.

Lemma is_det_head_step_true e1 σ1 :
  is_det_head_step e1 σ1 = true ↔ det_head_step_pred e1 σ1.
Proof.
  split; intro H.
  - destruct e1; inv_det_head_step; by econstructor.
  - inversion H; solve_step_det.
Qed.

Lemma det_head_step_singleton e1 σ1 e2 σ2 :
  det_head_step_rel e1 σ1 e2 σ2 → head_step e1 σ1 = dret (e2, σ2).
Proof.
  intros Hdet.
  apply pmf_1_eq_dret.
  inversion Hdet; simplify_eq/=; try case_match;
    simplify_option_eq; rewrite ?dret_1_1 //.
Qed.

Lemma val_not_head_step e1 σ1 :
  is_Some (to_val e1) → ¬ head_step_pred e1 σ1.
Proof.
  intros [] [Hs | Hs]; inversion Hs; simplify_eq.
Qed.

Lemma head_step_pred_ex_rel e1 σ1 :
  head_step_pred e1 σ1 ↔ ∃ e2 σ2, head_step_rel e1 σ1 e2 σ2.
Proof.
  split.
  - intros [Hdet | Hdet];
      inversion Hdet; simplify_eq; do 2 eexists; try (by econstructor).
    Unshelve. all : apply 0%fin.
  - intros (?&?& H). inversion H; simplify_eq;
      (try by (left; econstructor));
      (try by (right; econstructor)).
    right. by eapply RandTapeOtherPSP; [|done|done].
Qed.

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

Lemma det_or_prob_or_dzero e1 σ1 :
  det_head_step_pred e1 σ1
  ∨ prob_head_step_pred e1 σ1
  ∨ head_step e1 σ1 = dzero.
Proof.
  destruct (Rlt_le_dec 0 (SeriesC (head_step e1 σ1))) as [H1%Rlt_gt | [HZ | HZ]].
  - pose proof (SeriesC_gtz_ex (head_step e1 σ1) (pmf_pos (head_step e1 σ1)) H1) as [[e2 σ2] Hρ].
    pose proof (head_step_support_equiv_rel e1 e2 σ1 σ2) as [H3 H4].
    specialize (H3 Hρ).
    assert (head_step_pred e1 σ1) as []; [|auto|auto].
    apply head_step_pred_ex_rel; eauto.
  - by pose proof (pmf_SeriesC_ge_0 (head_step e1 σ1))
      as ?%Rle_not_lt.
  - apply SeriesC_zero_dzero in HZ. eauto.
Qed.

Lemma head_step_dzero_upd_tapes α e σ N zs z  :
  α ∈ dom σ.(tapes) →
  head_step e σ = dzero →
  head_step e (state_upd_tapes <[α:=(N; zs ++ [z]) : tape]> σ) = dzero.
Proof.
  intros Hdom Hz.
  destruct e; simpl in *;
    repeat case_match; done || inv_dzero; simplify_map_eq.
  (* TODO: [simplify_map_eq] should solve this? *)
  - destruct (decide (α = l1)).
    + simplify_eq.
      by apply not_elem_of_dom_2 in H5.
    + rewrite lookup_insert_ne // in H6.
      rewrite H5 in H6. done.
  - destruct (decide (α = l1)).
    + simplify_eq.
      by apply not_elem_of_dom_2 in H5.
    + rewrite lookup_insert_ne // in H6.
      rewrite H5 in H6. done.
  - destruct (decide (α = l1)).
    + simplify_eq.
      by apply not_elem_of_dom_2 in H5.
    + rewrite lookup_insert_ne // in H6.
      rewrite H5 in H6. done.
Qed.

Lemma det_head_step_upd_tapes N e1 σ1 e2 σ2 α z zs :
  det_head_step_rel e1 σ1 e2 σ2 →
  tapes σ1 !! α = Some (N; zs) →
  det_head_step_rel
    e1 (state_upd_tapes <[α := (N; zs ++ [z])]> σ1)
    e2 (state_upd_tapes <[α := (N; zs ++ [z])]> σ2).
Proof.
  inversion 1; try econstructor; eauto.
  (* Unsolved case *)
  intros. rewrite state_upd_tapes_heap. econstructor; eauto.
Qed.

Lemma upd_tape_some σ α N n ns :
  tapes σ !! α = Some (N; ns) →
  tapes (state_upd_tapes <[α:= (N; ns ++ [n])]> σ) !! α = Some (N; ns ++ [n]).
Proof.
  intros H. rewrite /state_upd_tapes /=. rewrite lookup_insert //.
Qed.

Lemma upd_tape_some_trivial σ α bs:
  tapes σ !! α = Some bs →
  state_upd_tapes <[α:=tapes σ !!! α]> σ = σ.
Proof.
  destruct σ. simpl.
  intros H.
  rewrite (lookup_total_correct _ _ _ H).
  f_equal.
  by apply insert_id.
Qed.

Lemma upd_diff_tape_comm σ α β bs bs':
  α ≠ β →
  state_upd_tapes <[β:= bs]> (state_upd_tapes <[α := bs']> σ) =
    state_upd_tapes <[α:= bs']> (state_upd_tapes <[β := bs]> σ).
Proof.
  intros. rewrite /state_upd_tapes /=. rewrite insert_commute //.
Qed.

Lemma upd_diff_tape_tot σ α β bs:
  α ≠ β →
  tapes σ !!! α = tapes (state_upd_tapes <[β:=bs]> σ) !!! α.
Proof. symmetry ; by rewrite lookup_total_insert_ne. Qed.

Lemma upd_tape_twice σ β bs bs' :
  state_upd_tapes <[β:= bs]> (state_upd_tapes <[β:= bs']> σ) = state_upd_tapes <[β:= bs]> σ.
Proof. rewrite /state_upd_tapes insert_insert //. Qed.

Lemma fresh_loc_upd_some σ α bs bs' :
  (tapes σ) !! α = Some bs →
  fresh_loc (tapes σ) = (fresh_loc (<[α:= bs']> (tapes σ))).
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
  (tapes σ) !! α = Some bs →
  state_upd_tapes <[fresh_loc (tapes σ):=bs']> (state_upd_tapes <[α:=bs'']> σ)
  = state_upd_tapes <[α:=bs'']> (state_upd_tapes <[fresh_loc (tapes σ):=bs']> σ).
Proof.
  intros H.
  apply elem_fresh_ne in H.
  unfold state_upd_tapes.
  by rewrite insert_commute.
Qed.

Lemma fresh_loc_lookup σ α bs bs' :
  (tapes σ) !! α = Some bs →
  (tapes (state_upd_tapes <[fresh_loc (tapes σ):=bs']> σ)) !! α = Some bs.
Proof.
  intros H.
  pose proof (elem_fresh_ne _ _ _ H).
  by rewrite lookup_insert_ne.
Qed.

Lemma prim_step_empty_tape σ α (z:Z) K N :
  (tapes σ) !! α = Some (N; []) -> prim_step (fill K (rand(#lbl:α) #z)) σ = prim_step (fill K (rand #z)) σ.
Proof.
  intros H.
  rewrite !fill_dmap; [|done|done].
  rewrite /dmap.
  f_equal.
  simpl. apply distr_ext; intros [e s].
  erewrite !head_prim_step_eq; simpl; last first.
  (** type classes dont work? *)
  { destruct (decide (Z.to_nat z=N)) as [<-|?] eqn:Heqn.
    all: eexists (_, σ); eapply head_step_support_equiv_rel;
      eapply head_step_support_eq; simpl; last first.
    - rewrite H. rewrite bool_decide_eq_true_2; last lia.
      eapply dmap_unif_nonzero; last done.
      intros ???. simplify_eq. done.
    - apply Rinv_pos. pose proof pos_INR_S (Z.to_nat z). lra.
    - rewrite H. case_bool_decide as H0; first lia.
      eapply dmap_unif_nonzero; last done.
      intros ???. by simplify_eq.
    - apply Rinv_pos. pose proof pos_INR_S (Z.to_nat z). lra.
  }
  { eexists (_, σ); eapply head_step_support_equiv_rel;
      eapply head_step_support_eq; simpl; last first.
    - eapply dmap_unif_nonzero; last done.
      intros ???. simplify_eq. done.
    - apply Rinv_pos. pose proof pos_INR_S (Z.to_nat z). lra.
  } rewrite H.
  case_bool_decide; last done.
  subst. done.
  Unshelve.
  all: exact (0%fin).
Qed.
  
