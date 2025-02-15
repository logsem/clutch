(* TODO cleanup imports *)
Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp Require Import functions.
From mathcomp.analysis Require Import reals measure itv lebesgue_measure probability.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp fintype.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.common Require Export locations.
From clutch.meas_lang Require Import ectxi_language ectx_language.
From Coq Require Export Reals.
From clutch.prob.monad Require Export giry.
From mathcomp.analysis Require Export Rstruct.
From mathcomp Require Import classical_sets.
Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude types constructors shapes cover projections tapes.
Set Warnings "hiding-delimiting-key".

Local Open Scope classical_set_scope.

Set Default Proof Using "Type*".

Context `{R : realType}.

Global Instance gmap_lookup {T} : Lookup loc T (gmap loc T).
Proof. Admitted.

Section gmap_loc_measurable.
  Local Open Scope classical_set_scope.
  (** Measurable functions out of nat *)
  Context {d} {T : measurableType d}.

  HB.instance Definition _ := gen_eqMixin (gmap loc T).
  HB.instance Definition _ := gen_choiceMixin (gmap loc T).
  HB.instance Definition _ := isPointed.Build (gmap loc T) (inhabitant : gmap loc T).


  Definition loc_enum : nat -> loc. Admitted.
  Lemma loc_enum_surj : forall l, exists n, loc_enum n = l.
  Proof. Admitted.

  (* NOTE: that this is the preimage out of (option T), not T *)
  Definition gl_generators : set (set (gmap loc T)) :=
    (\bigcup_i (preimage_class setT (fun (f : gmap loc T) => lookup (loc_enum i) f) measurable)).

  Definition gl_measurable : set (set (gmap loc T)) := <<s gl_generators>>.

  Lemma gl_meas0 : gl_measurable set0.
  Proof. by apply sigma_algebra0. Qed.

  Lemma gl_measC X : (gl_measurable X) -> gl_measurable (~` X).
  Proof. by apply sigma_algebraC. Qed.

  Lemma gl_measU (F : sequences.sequence (set (gmap loc T))) : (forall i, gl_measurable (F i)) -> gl_measurable (\bigcup_i F i).
  Proof. by apply sigma_algebra_bigcup. Qed.

  HB.instance Definition _ :=
    @isMeasurable.Build (sigma_display gl_measurable) (gmap loc T) gl_measurable gl_meas0 gl_measC gl_measU.


  Lemma gl_eval_measurable (l : <<discr loc>>) : measurable_fun setT (lookup l : gmap loc T -> option T).
  Proof.
    intros _ Y HY.
    rewrite /gl_measurable.
    unfold lookup.
    suffices H : gl_generators (setT `&` gmap_lookup l @^-1` Y).
    { by apply ((@sub_gen_smallest _ _ gl_generators) _ H). }
    destruct (loc_enum_surj l) as [i Hi].
    exists i; [done|].
    rewrite /preimage_class//=.
    exists Y; [done|].
    by rewrite Hi setTI //=.
  Qed.
  Hint Resolve gl_eval_measurable : measlang.


  Lemma uncurry_loc_measurable {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
          (f : <<discr loc>> -> T1 -> T2) (Hf : forall i, measurable_fun setT (f i)) :
        measurable_fun setT (uncurry f).
   Proof using T d.
    intros _ Y HY.
    have -> : ((uncurry f) @^-1` Y) = \bigcup_i ((setX [set loc_enum i] ((f $ loc_enum i) @^-1` Y)) : set (<<discr loc>> * _)%type).
    { rewrite /uncurry/preimage/setX//=.
      apply /predeqP =>[[l ]] /=.
      split.
      { intros H.
        destruct (loc_enum_surj l) as [i Hi].
        exists i; [done|].
        by rewrite Hi //=. }
      { move=>[x ?]//=. by move=>[-> ?]//=. }
    }
    rewrite setTI.
    apply bigcup_measurable.
    intros i ?.
    apply measurableX.
    { by rewrite /measurable//=. }
    rewrite <-(setTI (preimage _ _)).
    by eapply (Hf _ _ Y HY).
    Unshelve. by apply @measurableT.
  Qed.


  (* The uncurry is measurable becuase nat is discrete and countable *)
  Definition gl_evalC : (<<discr loc>> * gmap loc T)%type -> option T := uncurry lookup.
  Lemma gl_evalC_measurable : measurable_fun setT gl_evalC.
  Proof. unfold gl_evalC. (* Typeclasses crap *) Admitted.
  Hint Resolve nf_evalC_measurable : measlang.


  Definition gl_update (l : <<discr loc>>) : (T * (gmap loc T))%type -> (gmap loc T) :=
    fun x => insert l x.1 x.2.

  Lemma gl_update_measurable (l : loc) : measurable_fun setT (gl_update l).
  Proof.
    eapply @measurability; [done|].
    rewrite //=/gl_update/subset/preimage_class//=.
    intro S.
    rewrite /nf_generators/preimage_class//=.
    move=> [S' [k _ +]].
    rewrite setTI//=; move=>[S'' HS'' +].
    rewrite setTI//=; move=><-<-//=.
    rewrite <-comp_preimage; rewrite /ssrfun.comp//=.
    destruct (loc_enum_surj l) as [i Hi].
    destruct (k =? i); rewrite //=.
    { have -> : ((λ x : T * gmap loc T, <[l:=x.1]> x.2 !! loc_enum k) @^-1` S'') =
                (setT `&` (ssrfun.comp Some fst) @^-1` S'').
      { rewrite /setI/preimage/cst//=.
        apply /predeqP =>[y] /=.
        split.
        { admit. }
        { admit. }
      }
      admit. }

    { have -> : ((λ x : T * gmap loc T, <[l:=x.1]> x.2 !! loc_enum k) @^-1` S'') =
               ((ssrfun.comp (gmap_lookup (loc_enum k)) snd) @^-1` S'').
      { rewrite /ssrfun.comp/preimage//=. admit. }
      rewrite <-(setTI (preimage _ _)).
      admit.
      (*
      by eapply (measurable_comp _ _ (nf_eval_measurable k) (measurable_snd) _ HS'').
      Unshelve.
      { by eapply @measurableT. }
      { by simpl. }
      { by eapply @measurableT. }
    }
      *)
  Admitted.
  Hint Resolve gl_update_measurable : measlang.

  Definition gl_updateC : (<<discr loc>> * (T * (gmap loc T)))%type -> (gmap loc T) := uncurry gl_update.
  Lemma gl_updateC_measurable : measurable_fun setT gl_updateC.
  Proof. Admitted. (*  by apply (@uncurry_nat_measurable _ _ _ _ gl_update), gl_update_measurable. Qed. *)
  Hint Resolve gl_updateC_measurable : measlang.

End gmap_loc_measurable.


(** The state: a [loc]-indexed heap of [val]s, and [loc]-indexed tapes, and [loc]-indexed utapes *)
Record state : Type := {
    state_v : ((gmap loc val) * (gmap loc btape) * (gmap loc (@utape R)))%type
}.

Definition prod_of_state (s : state) : ((gmap loc val) * (gmap loc btape) * (gmap loc (@utape R))) :=
  match s with {| state_v := x |} => x end.

Definition state_of_prod (v : (gmap loc val) * (gmap loc btape) * (gmap loc (@utape R))) : state :=
  {| state_v := v |}.

Lemma prod_of_state_of_state p : prod_of_state (state_of_prod p) = p.
Proof. by rewrite /prod_of_state/state_of_prod//. Qed.

Lemma state_of_prod_of_state s : state_of_prod (prod_of_state s) = s.
Proof. destruct s. by rewrite /prod_of_state/state_of_prod//. Qed.

HB.instance Definition _ := gen_eqMixin state.
HB.instance Definition _ := gen_choiceMixin state.
HB.instance Definition _ := isPointed.Build state (state_of_prod point).

Definition state_measurable : set (set state) :=
  flip image (flip image state_of_prod) measurable.

Lemma state_display : measure_display.
Proof. done. Qed.

Lemma state_meas0 : state_measurable set0.
Proof. Admitted.

Lemma state_measC X : (state_measurable X) -> state_measurable (~` X).
Proof. Admitted.

Lemma state_measU (F : sequences.sequence (set state)) : (forall i, state_measurable (F i)) -> state_measurable (\bigcup_i F i).
Proof. Admitted.

HB.instance Definition _ :=
  @isMeasurable.Build state_display state state_measurable state_meas0 state_measC state_measU.

Definition state_lift_fun {d} {T : measurableType d} f : state -> T := ssrfun.comp f prod_of_state.

Definition state_lift_set D : set state := image D state_of_prod.

Definition state_lift_meas {d} {T : measurableType d} (f : _ -> T) D (HD : measurable D) (H : measurable_fun D f) :
    measurable_fun (state_lift_set D) (state_lift_fun f).
Proof. Admitted.

Definition heap   : state -> gmap loc val := state_lift_fun $ ssrfun.comp fst fst.
Definition tapes  : state -> gmap loc btape := state_lift_fun $ ssrfun.comp snd fst.
Definition utapes : state -> gmap loc (@utape R) := state_lift_fun $ snd.


(** Operations on states *)

(*

Definition state_upd_heap (f : gmap loc val → gmap loc val) (σ : state) : state :=
  {| heap := f σ.(heap); tapes := σ.(tapes); utapes := σ.(utapes) |}.
Global Arguments state_upd_heap _ !_ /.

Definition state_upd_tapes (f : gmap loc btape → gmap loc btape) (σ : state) : state :=
  {| heap := σ.(heap); tapes := f σ.(tapes); utapes := σ.(utapes) |}.
Global Arguments state_upd_tapes _ !_ /.

Definition state_upd_utapes (f : gmap loc utape → gmap loc utape) (σ : state) : state :=
  {| heap := σ.(heap); tapes := σ.(tapes); utapes := f σ.(utapes) |}.
Global Arguments state_upd_utapes _ !_ /.

Lemma state_upd_tapes_twice σ l xs ys :
  state_upd_tapes <[ l := ys ]> (state_upd_tapes <[ l := xs ]> σ) = state_upd_tapes <[ l:= ys ]> σ.
Proof. rewrite /state_upd_tapes /=. f_equal. apply insert_insert. Qed.

Lemma state_upd_tapes_same σ σ' l xs ys :
  state_upd_tapes <[l:=ys]> σ = state_upd_tapes <[l:=xs]> σ' -> xs = ys.
Proof. rewrite /state_upd_tapes /=. intros K. simplify_eq.
       rewrite map_eq_iff in H.
       specialize (H l).
       rewrite !lookup_insert in H.
       by simplify_eq.
Qed.

Lemma state_upd_tapes_no_change σ l ys :
  tapes σ !! l = Some ys ->
  state_upd_tapes <[l := ys]> σ = σ .
Proof.
  destruct σ as [? t]. simpl.
  intros Ht.
  f_equal.
  apply insert_id. done.
Qed.

(*
Lemma state_upd_tapes_same' σ σ' l n xs (x y : stdpp.fin.fin (S n)) :
  state_upd_tapes <[l:=(fin (n; xs++[x]))]> σ = state_upd_tapes <[l:=(fin(n; xs++[y]))]> σ' -> x = y.
Proof. intros H. apply state_upd_tapes_same in H. by simplify_eq. Qed.

Lemma state_upd_tapes_neq' σ σ' l n xs (x y : stdpp.fin.fin (S n)) :
  x≠y -> state_upd_tapes <[l:=(fin(n; xs++[x]))]> σ ≠ state_upd_tapes <[l:=(fin(n; xs++[y]))]> σ'.
Proof. move => H /state_upd_tapes_same ?. simplify_eq. Qed.
*)

Fixpoint heap_array (l : loc) (vs : list val) : gmap loc val :=
  match vs with
  | [] => ∅
  | v :: vs' => {[l := v]} ∪ heap_array (l +ₗ 1) vs'
  end.

Lemma heap_array_singleton l v : heap_array l [v] = {[l := v]}.
Proof. by rewrite /heap_array right_id. Qed.

Lemma heap_array_app l vs1 vs2 : heap_array l (vs1 ++ vs2) = (heap_array l vs1) ∪ (heap_array (l +ₗ (length vs1)) vs2) .
Proof.
  revert l.
  induction vs1; intro l.
  - simpl.
    rewrite map_empty_union loc_add_0 //.
  - rewrite -app_comm_cons /= IHvs1.
    rewrite map_union_assoc.
    do 2 f_equiv.
    rewrite Nat2Z.inj_succ /=.
    rewrite /Z.succ
      Z.add_comm
      loc_add_assoc //.
Qed.

Lemma heap_array_lookup l vs v k :
  heap_array l vs !! k = Some v ↔
  ∃ j, (0 ≤ j)%Z ∧ k = l +ₗ j ∧ vs !! (Z.to_nat j) = Some v.
Proof.
  revert k l; induction vs as [|v' vs IH] => l' l /=.
  { rewrite lookup_empty. naive_solver lia. }
  rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
  - intros [[-> ?] | (Hl & j & ? & -> & ?)].
    { eexists 0. rewrite loc_add_0. naive_solver lia. }
    eexists (1 + j)%Z. rewrite loc_add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
  - intros (j & ? & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { rewrite loc_add_0; eauto. }
    right. split.
    { rewrite -{1}(loc_add_0 l). intros ?%(inj (loc_add _)); lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    eexists (j - 1)%Z. rewrite loc_add_assoc Z.add_sub_assoc Z.add_simpl_l.
    auto with lia.
Qed.

Lemma heap_array_map_disjoint (h : gmap loc val) (l : loc) (vs : list val) :
  (∀ i, (0 ≤ i)%Z → (i < length vs)%Z → h !! (l +ₗ i) = None) →
  (heap_array l vs) ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j&?&->&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
  move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
Qed.

Definition state_upd_heap_N (l : loc) (n : nat) (v : val) (σ : state) : state :=
  state_upd_heap (λ h, heap_array l (replicate n v) ∪ h) σ.

Lemma state_upd_heap_singleton l v σ :
  state_upd_heap_N l 1 v σ = state_upd_heap <[l:= v]> σ.
Proof.
  destruct σ as [h p]. rewrite /state_upd_heap_N /=. f_equiv.
  rewrite right_id insert_union_singleton_l. done.
Qed.

Lemma state_upd_tapes_heap σ l1 l2 xs m v :
  state_upd_tapes <[l2:=xs]> (state_upd_heap_N l1 m v σ) =
  state_upd_heap_N l1 m v (state_upd_tapes <[l2:=xs]> σ).
Proof.
  by rewrite /state_upd_tapes /state_upd_heap_N /=.
Qed.

Lemma heap_array_replicate_S_end l v n :
  heap_array l (replicate (S n) v) = heap_array l (replicate n v) ∪ {[l +ₗ n:= v]}.
Proof.
  induction n.
  - simpl.
    rewrite map_union_empty.
    rewrite map_empty_union.
    by rewrite loc_add_0.
  - rewrite replicate_S_end
     heap_array_app
     IHn /=.
    rewrite map_union_empty replicate_length //.
Qed.

Global Instance state_inhabited : Inhabited state :=
  populate {| heap := gmap_empty; tapes := gmap_empty; utapes := gmap_empty |}.
*)
