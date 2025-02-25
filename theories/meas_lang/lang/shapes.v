(* TODO: Clear imports *)
Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From stdpp Require Import binders gmap.
From mathcomp Require Import functions classical_sets.
From mathcomp.analysis Require Import reals measure lebesgue_measure.
From mathcomp Require Import boolp.
From clutch.prelude Require Export classical.
From clutch.meas_lang.lang Require Export prelude types.
Set Warnings "hiding-delimiting-key".

Local Open Scope classical_set_scope.

(** Shapes: Trees with Unit as leaves.
    Used to prove that functions in the expr algebra are measurable *)

Definition base_lit_shape : Type := @base_lit_pre () () () ().
Definition val_shape      : Type := @val_pre () () () ().
Definition expr_shape     : Type := @expr_pre () () () ().


(** Get the shape of an expression *)

Definition shape_base_lit {T1 T2 T3 T4} : @base_lit_pre T1 T2 T3 T4 -> base_lit_shape :=
 base_lit_pre_F (cst ()) (cst ()) (cst ()) (cst ()) (cst ()).

Definition shape_val {T1 T2 T3 T4} : @val_pre T1 T2 T3 T4 -> val_shape :=
 val_pre_F (cst ()) (cst ()) (cst ()) (cst ()) (cst ()).

Definition shape_expr {T1 T2 T3 T4} : @expr_pre T1 T2 T3 T4 -> expr_shape :=
 expr_pre_F (cst ()) (cst ()) (cst ()) (cst ()) (cst ()).


(** Get a generator for all expressions with a given shape *)

Definition gen_base_lit : base_lit_shape -> base_lit_S :=
 base_lit_pre_F (cst setT) (cst setT) (cst setT) (cst setT) (cst setT).

Definition gen_val : val_shape -> val_S :=
 val_pre_F (cst setT) (cst setT) (cst setT) (cst setT) (cst setT).

Definition gen_expr : expr_shape -> expr_S :=
 expr_pre_F (cst setT) (cst setT) (cst setT) (cst setT) (cst setT).


Lemma gen_base_lit_generator s : base_lit_ML (gen_base_lit s).
Proof.
  rewrite /base_lit_ML/gen_base_lit/base_lit_pre_F.
  destruct s; try done; by eapply @measurableT.
Qed.

(** gen-* are generators for their respective sigma algebras *)
Lemma gen_val_generator s : val_ML (gen_val s).
Proof.
  apply (val_pre_mut _ _ _ _ (fun s => expr_ML (gen_expr s)) (fun s => val_ML (gen_val s))).
  all: try by move=>*//=.
  by apply gen_base_lit_generator.
Qed.

Lemma gen_expr_generator s : expr_ML (gen_expr s).
Proof.
  apply (expr_pre_mut _ _ _ _ (fun s => expr_ML (gen_expr s)) (fun s => val_ML (gen_val s))).
  all: try by move=>*//=.
  by apply gen_base_lit_generator.
Qed.


(** The set of all expressions with a given shape is singly generated *)
Lemma base_lit_shape_cyl (s : base_lit_shape) : [set e | shape_base_lit e = s] = base_lit_ST (gen_base_lit s).
Proof.
  apply /predeqP =>b.
  destruct b; simpl.
  all: split; [ by move <-; rewrite //=; eexists _; eauto | ].
  all: move=> H.
  all: destruct s as [x|x| |x|x|x]; simpl in H.
  all: try done.
  all: try by destruct H as [? ?].
  all: by destruct x.
Qed.

Lemma expr_shape_cyl (s : expr_shape) : [set e | shape_expr e = s] = expr_ST (gen_expr s).
Proof.
  (*
  apply /predeqP =>b.
  have D1 : [set e | shape_expr e = s] b -> expr_ST (gen_expr s) b.
  { destruct b.
    all: move=> H.
    all: simpl in H.
    all: destruct s as [?|?|???|??|??|???|???|??|?|?|?|?|???|??|?|??|?|??| |?|?].
    all: rewrite /gen_expr/=.
    all: try done.
    all: admit.
  }
  have D2 : expr_ST (gen_expr s) b -> [set e | shape_expr e = s] b.
  { all: move=> H.
    all: destruct s as [?|?|???|??|??|???|???|??|?|?|?|?|???|??|?|??|?|??| |?|?].
    all: simpl in H.
    all: admit.
  }
  by split.
*)
Admitted.

Lemma val_shape_cyl (s : val_shape) : [set e | shape_val e = s] = val_ST (gen_val s).
Proof. Admitted.


(** Decompose the set of expressions into a countable union over expr_shape *)

Definition expr_shape_enum (n : nat) : expr_shape. Admitted.

Definition val_shape_enum (n : nat) : val_shape. Admitted.

Definition base_lit_shape_enum (n : nat) : base_lit_shape. Admitted.

(* I only need surjectivity to prove that I don't miss any trees, so I'll use a definition
   of surjectivity appropriate for that (not the HB one, it gives us nothing) *)

Lemma expr_shape_enum_surj (e : expr_shape) : exists n, expr_shape_enum n = e.
Proof. Admitted.

Lemma val_shape_enum_surj (e : val_shape) : exists n, val_shape_enum n = e.
Proof. Admitted.

Lemma base_lit_shape_enum_surj (e : base_lit_shape) : exists n, base_lit_shape_enum n = e.
Proof. Admitted.

Lemma binder_enum_surj (e : binder) : exists n, binder_enum n = e.
Proof. by eexists (Pos.to_nat (encode e)); rewrite /binder_enum Pos2Nat.id decode_encode //=. Qed.

Lemma un_op_enum_surj (e : un_op) : exists n, un_op_enum n = e.
Proof. destruct e; by [ exists 0 | exists 1 ]. Qed.

Lemma bin_op_enum_surj (e : bin_op) : exists n, bin_op_enum n = e.
Proof.
  destruct e; by [ exists 0 | exists 1 | exists 2 | exists 3 | exists 4 |
                   exists 5 | exists 6 | exists 7 | exists 8 | exists 9 |
                   exists 10 | exists 11 | exists 12 | exists 13].
Qed.

Definition base_lit_seq : sequences.sequence (set base_lit) :=
  fun n => shape_base_lit @^-1` [set base_lit_shape_enum n].

Definition expr_seq : sequences.sequence (set expr) :=
  fun n => shape_expr @^-1` [set expr_shape_enum n].

Definition val_seq : sequences.sequence (set val) :=
  fun n => shape_val @^-1` [set val_shape_enum n].

Lemma base_lit_shape_decompT : (\bigcup_n base_lit_seq n) = setT.
Proof.
  rewrite <- subTset => e He.
  case (base_lit_shape_enum_surj (shape_base_lit e)) as [n Hn].
  exists n; [done|].
  by rewrite /base_lit_seq Hn //=.
Qed.

Lemma expr_shape_decompT: (\bigcup_n expr_seq n) = setT.
Proof.
  rewrite <- subTset => e He.
  case (expr_shape_enum_surj (shape_expr e)) as [n Hn].
  exists n; [done|].
  by rewrite /expr_seq Hn //=.
Qed.

Lemma val_shape_decompT : (\bigcup_n val_seq n) = setT.
Proof.
  rewrite <- subTset => e He.
  case (val_shape_enum_surj (shape_val e)) as [n Hn].
  exists n; [done|].
  by rewrite /val_seq Hn //=.
Qed.


Lemma base_lit_shape_decomp S : (\bigcup_n (S `&` base_lit_seq n)) = S.
Proof. by rewrite <- setI_bigcupr, base_lit_shape_decompT, setIT. Qed.

Lemma expr_shape_decomp S : (\bigcup_n (S `&` expr_seq n)) = S.
Proof. by rewrite <- setI_bigcupr, expr_shape_decompT, setIT. Qed.

Lemma val_shape_decomp S : (\bigcup_n (S `&` val_seq n)) = S.
Proof. by rewrite <- setI_bigcupr, val_shape_decompT, setIT. Qed.

(*
Check @discr_generated_by_singletons binder.
Check @discr_generated_by_singletons un_op.
Check @discr_generated_by_singletons bin_op.
*)


(**  Lemma about discrete spaces

TODO: Refactor code to use discr_generated_by_singletons instead (7 total usages) then delete.
 *)

Definition binder_singletons : set (set <<discr binder>>) := fun S => exists b, S = [set b].
Definition un_op_singletons : set (set <<discr un_op>>) := fun S => exists b, S = [set b].
Definition bin_op_singletons : set (set <<discr bin_op>>) := fun S => exists b, S = [set b].

Lemma binder_generated_by_singletons : binder.-discr.-measurable = <<s binder_singletons >>.
Proof.
  apply /predeqP =>y //=.
  simpl in *.
  split.
  - move=> _.
    have ->: y = \bigcup_i ([set (binder_enum i)] `&` y).
    { rewrite /bigcup//=.
      apply /predeqP =>z /=.
      split.
      - move=> ?.
        destruct (binder_enum_surj z) as [i ?].
        by exists i.
      - by move=> [i ?][-> ?].
    }
    apply sigma_algebra_bigcup.
    move=> i.
    destruct (ExcludedMiddle (y (binder_enum i))).
    + apply sub_sigma_algebra.
      rewrite /binder_singletons/setI //=.
      exists (binder_enum i).
      apply /predeqP =>z /=.
      split.
      + by move=> [? ?].
      + by move=>->.
    + have -> : ([set binder_enum i] `&` y) = set0.
      { rewrite /setI//=.
      apply /predeqP =>z /=.
      split.
      + by move=>[-> ?].
      + by move=>?. }
      apply sigma_algebra0.
  - move=> _. by rewrite /measurable/=/discr_measurable/=.
Qed.

Lemma un_op_generated_by_singletons : un_op.-discr.-measurable = <<s un_op_singletons >>.
Proof.
  apply /predeqP =>y //=.
  simpl in *.
  split.
  - move=> _.
    have ->: y = \bigcup_i ([set (un_op_enum i)] `&` y).
    { rewrite /bigcup//=.
      apply /predeqP =>z /=.
      split.
      - move=> ?.
        destruct (un_op_enum_surj z) as [i ?].
        by exists i.
      - by move=> [i ?][-> ?].
    }
    apply sigma_algebra_bigcup.
    move=> i.
    destruct (ExcludedMiddle (y (un_op_enum i))).
    + apply sub_sigma_algebra.
      rewrite /binder_singletons/setI //=.
      exists (un_op_enum i).
      apply /predeqP =>z /=.
      split.
      + by move=> [? ?].
      + by move=>->.
    + have -> : ([set un_op_enum i] `&` y) = set0.
      { rewrite /setI//=.
      apply /predeqP =>z /=.
      split.
      + by move=>[-> ?].
      + by move=>?. }
      apply sigma_algebra0.
  - move=> _. by rewrite /measurable/=/discr_measurable/=.
Qed.

Lemma bin_op_generated_by_singletons : bin_op.-discr.-measurable = <<s bin_op_singletons >>.
Proof.
  apply /predeqP =>y //=.
  simpl in *.
  split.
  - move=> _.
    have ->: y = \bigcup_i ([set (bin_op_enum i)] `&` y).
    { rewrite /bigcup//=.
      apply /predeqP =>z /=.
      split.
      - move=> ?.
        destruct (bin_op_enum_surj z) as [i ?].
        by exists i.
      - by move=> [i ?][-> ?].
    }
    apply sigma_algebra_bigcup.
    move=> i.
    destruct (ExcludedMiddle (y (bin_op_enum i))).
    + apply sub_sigma_algebra.
      rewrite /binder_singletons/setI //=.
      exists (bin_op_enum i).
      apply /predeqP =>z /=.
      split.
      + by move=> [? ?].
      + by move=>->.
    + have -> : ([set bin_op_enum i] `&` y) = set0.
      { rewrite /setI//=.
      apply /predeqP =>z /=.
      split.
      + by move=>[-> ?].
      + by move=>?. }
      apply sigma_algebra0.
  - move=> _. by rewrite /measurable/=/discr_measurable/=.
Qed.
