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
From clutch.prob.monad Require Export laws extras.
From mathcomp.analysis Require Export Rstruct.
From mathcomp Require Import classical_sets.
Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude types shapes.
Set Warnings "hiding-delimiting-key".

Local Open Scope classical_set_scope.

(** Defines a measurable cover of the expr, val, and base_lit type, by constructor.

    cover of expr:     ecov
    cover of values:   vcov
    cover of base_lit: bcov

    For each constructor k, there is a set
        (e/v/b)cov_k : set (expr/val/base_lit)
     and a measurability proof
        (e/v/b)cov_k_meas  : measurable (e/v/b)cov_k
 *)

Definition ecov_val        : set expr     := [set e  | ∃ v,         e = ValC v].
Definition ecov_var        : set expr     := [set e  | ∃ s,         e = VarC s].
Definition ecov_rec        : set expr     := [set e  | ∃ f x b,     e = RecC f x b].
Definition ecov_app        : set expr     := [set e  | ∃ e1 e2,     e = AppC e1 e2].
Definition ecov_unop       : set expr     := [set e  | ∃ op x,      e = UnOpC op x].
Definition ecov_binop      : set expr     := [set e  | ∃ op e1 e2,  e = BinOpC op e1 e2].
Definition ecov_if         : set expr     := [set e  | ∃ e1 e2 e3,  e = IfC e1 e2 e3].
Definition ecov_pair       : set expr     := [set e  | ∃ e1 e2,     e = PairC e1 e2].
Definition ecov_fst        : set expr     := [set e  | ∃ x,         e = FstC x].
Definition ecov_snd        : set expr     := [set e  | ∃ x,         e = SndC x].
Definition ecov_injl       : set expr     := [set e  | ∃ x,         e = InjLC x].
Definition ecov_injr       : set expr     := [set e  | ∃ x,         e = InjRC x].
Definition ecov_case       : set expr     := [set e  | ∃ e1 e2 e3,  e = CaseC e1 e2 e3].
Definition ecov_alloc      : set expr     := [set e  | ∃ e1 e2,     e = AllocN e1 e2].
Definition ecov_load       : set expr     := [set e  | ∃ x,         e = LoadC x].
Definition ecov_store      : set expr     := [set e  | ∃ e1 e2,     e = StoreC e1 e2].
Definition ecov_alloctape  : set expr     := [set e  | ∃ x,         e = AllocTapeC x].
Definition ecov_rand       : set expr     := [set e  | ∃ e1 e2,     e = RandC e1 e2].
Definition ecov_allocutape : set expr     := [set e  |              e = AllocUTapeC].
Definition ecov_urand      : set expr     := [set e  | ∃ x,         e = URandC x].
Definition ecov_tick       : set expr     := [set e  | ∃ x,         e = TickC x].

Definition vcov_lit        : set val      := [set e  | ∃ v,         e = LitVC v].
Definition vcov_rec        : set val      := [set e  | ∃ f x e0,    e = RecVC f x e0].
Definition vcov_pair       : set val      := [set e  | ∃ v1 v2,     e = PairVC v1 v2].
Definition vcov_injlv      : set val      := [set e  | ∃ v,         e = InjLVC v].
Definition vcov_injrv      : set val      := [set e  | ∃ v,         e = InjRVC v].

Definition bcov_LitInt     : set base_lit := [set e  | ∃ v,         e = LitIntC  v].
Definition bcov_LitBool    : set base_lit := [set e  | ∃ v,         e = LitBoolC v].
Definition bcov_LitUnit    : set base_lit := [set e  |              e = LitUnitC  ].
Definition bcov_LitLoc     : set base_lit := [set e  | ∃ v,         e = LitLoc   v].
Definition bcov_LitLbl     : set base_lit := [set e  | ∃ v,         e = LitLbl   v].
Definition bcov_LitReal    : set base_lit := [set e  | ∃ v,         e = LitReal  v].

(* NOTE:
    I think that in principle we could have proven these by first showing a projection
    function is measurable, and then showing that it is the preimage of setT. However,
    for the indirect method we have to use (no restricted SA's) this does not work,
    because (measurable_fun Dom) requires we show Dom is measurable a priori.
 *)
(* Both will use the decomposition argument. *)
Lemma bcov_LitInt_meas  : measurable bcov_LitInt.
Proof.
  apply sub_sigma_algebra.
  rewrite /base_lit_cyl/=.
  exists (LitInt setT).
  { by rewrite /=/measurable/=/discr_meas/=. }
  rewrite /bcov_LitInt/=.
  apply /predeqP =>y /=.
  split.
  - by move=> [x??]; exists x.
  - by move=> [x?]; exists x.
Qed.
Hint Resolve bcov_LitInt_meas : measlang.

Lemma bcov_LitBool_meas : measurable bcov_LitBool.
Proof.
  apply sub_sigma_algebra.
  rewrite /base_lit_cyl/=.
  exists (LitBool setT).
  { by rewrite /=/measurable/=/discr_meas/=. }
  rewrite /bcov_LitBool/=.
  apply /predeqP =>y /=.
  split.
  - by move=> [x??]; exists x.
  - by move=> [x?]; exists x.
Qed.
Hint Resolve bcov_LitBool_meas : measlang.

Lemma bcov_LitUnit_meas : measurable bcov_LitUnit.
Proof.
  apply sub_sigma_algebra.
  rewrite /base_lit_cyl/=.
  exists (LitUnit).
  { by rewrite /=/measurable/=/discr_meas/=. }
  rewrite /bcov_LitUnit//=.
Qed.
Hint Resolve bcov_LitUnit_meas : measlang.

Lemma bcov_LitLoc_meas  : measurable bcov_LitLoc.
Proof.
  apply sub_sigma_algebra.
  rewrite /base_lit_cyl/=.
  exists (LitLoc setT).
  { by rewrite /=/measurable/=/discr_meas/=. }
  rewrite /bcov_LitLoc/=.
  apply /predeqP =>y /=.
  split.
  - by move=> [x??]; exists x.
  - by move=> [x?]; exists x.
Qed.
Hint Resolve bcov_LitLoc_meas : measlang.

Lemma bcov_LitLbl_meas  : measurable bcov_LitLbl.
Proof.
  apply sub_sigma_algebra.
  rewrite /base_lit_cyl/=.
  exists (LitLbl setT).
  { by rewrite /=/measurable/=/discr_meas/=. }
  rewrite /bcov_LitLbl/=.
  apply /predeqP =>y /=.
  split.
  - by move=> [x??]; exists x.
  - by move=> [x?]; exists x.
Qed.
Hint Resolve bcov_LitLbl_meas : measlang.

Lemma bcov_LitReal_meas : measurable bcov_LitReal.
Proof.
  apply sub_sigma_algebra.
  rewrite /base_lit_cyl/=.
  exists (LitReal setT).
  { by rewrite /=/measurable/=/measurableR/=. }
  rewrite /bcov_LitReal/=.
  apply /predeqP =>y /=.
  split.
  - by move=> [x??]; exists x.
  - by move=> [x?]; exists x.
Qed.

Arguments eq_measurable {_} {_} _ {_}.
Lemma ecov_val_meas : measurable ecov_val.
Proof.
  rewrite /ecov_val.
  eapply (eq_measurable (\bigcup_n [set ValC v | v in (val_seq n)])); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [v ->].
      destruct (val_shape_enum_surj (shape_val v)) as [? ?].
      eexists _; [done|].
      eexists _; [|done].
      by rewrite //=.
    - move=> [? _] [x ?] <-.
      by eexists _.
  }
  apply bigcup_measurable.
  move=> k _.
  apply sub_sigma_algebra.
  exists (Val (gen_val (val_shape_enum k))); [ by apply gen_val_generator |].
  by rewrite /val_seq/preimage //= (val_shape_cyl _).
Qed.
Hint Resolve ecov_val_meas : measlang.

Lemma ecov_var_meas        : measurable ecov_var.
Proof.
  rewrite /ecov_var.
  eapply (eq_measurable (\bigcup_n [set VarC (binder_enum n)])); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [v ->].
      destruct (binder_enum_surj v) as [? <-].
      eexists _; [done|].
      by rewrite //=.
    - move=> [? _] ->.
      by eexists _.
  }
  apply bigcup_measurable.
  move=> k _.
  apply sub_sigma_algebra.
  exists (Var (binder_enum k)); [by rewrite //= |].
  by rewrite /val_seq/preimage //= (val_shape_cyl _).
Qed.
Hint Resolve ecov_var_meas : measlang.

Lemma ecov_rec_meas        : measurable ecov_rec.
Proof.
  rewrite /ecov_rec.
  eapply (eq_measurable (\bigcup_i \bigcup_j \bigcup_k
                           [set (RecC (binder_enum j) (binder_enum k) e) | e in (expr_seq i)])); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [f][x][e]->.
      destruct (binder_enum_surj f) as [? ?].
      destruct (binder_enum_surj x) as [? ?].
      destruct (expr_shape_enum_surj (shape_expr e)) as [?].
      eexists _; [done|].
      eexists _; [done|].
      eexists _; [done|].
      exists e; [ by rewrite //= |].
      f_equal; done.
    - move=> [??][??][??][??<-].
      eexists _.
      eexists _.
      eexists _.
      done.
  }
  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply bigcup_measurable; move=> k _.
  apply sub_sigma_algebra.
  eexists (Rec (binder_enum j) (binder_enum k) (gen_expr (expr_shape_enum i))); [ by apply gen_expr_generator |].
  by rewrite /expr_seq/preimage //= (expr_shape_cyl _).
Qed.
Hint Resolve ecov_rec_meas : measlang.

Lemma ecov_app_meas        : measurable ecov_app.
Proof.
  rewrite /ecov_app.
  eapply (eq_measurable (\bigcup_i \bigcup_j
                           [set (AppC e1 e2) | e1 in (expr_seq i) & e2 in (expr_seq j)])); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [e1][e2]->.
      destruct (expr_shape_enum_surj (shape_expr e1)) as [?].
      destruct (expr_shape_enum_surj (shape_expr e2)) as [?].
      eexists _; [done|].
      eexists _; [done|].
      eexists e1; [ by rewrite //= |].
      eexists e2; [ by rewrite //= |].
      f_equal; done.
    - move=> [??][??][??][??]<-.
      eexists _.
      eexists _.
      done.
  }
  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (App  (gen_expr (expr_shape_enum i)) (gen_expr (expr_shape_enum j))).
  { rewrite //=. split; by apply gen_expr_generator. }
  by rewrite /expr_seq/preimage //= (expr_shape_cyl _) (expr_shape_cyl _).
Qed.
Hint Resolve ecov_app_meas : measlang.

Lemma ecov_unop_meas       : measurable ecov_unop.
Proof.
  rewrite /ecov_unop.
  eapply (eq_measurable (\bigcup_i \bigcup_j
                           [set (UnOpC (un_op_enum i) e) | e in (expr_seq j)])); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [op][e]->.
      destruct (un_op_enum_surj op) as [? ?].
      destruct (expr_shape_enum_surj (shape_expr e)) as [?].
      eexists _; [done|].
      eexists _; [done|].
      exists e; [ by rewrite //= |].
      f_equal; done.
    - move=> [??][??][??<-].
      eexists _.
      eexists _.
      done.
  }
  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (UnOp (un_op_enum i) (gen_expr (expr_shape_enum j))).
  { rewrite //=. by apply gen_expr_generator. }
  by rewrite /expr_seq/preimage //= (expr_shape_cyl _).
Qed.
Hint Resolve ecov_unop_meas : measlang.

Lemma ecov_binop_meas      : measurable ecov_binop.
Proof.
  eapply (eq_measurable (\bigcup_i \bigcup_j \bigcup_k
                           [set (BinOpC (bin_op_enum i) e1 e2) | e1 in (expr_seq j) & e2 in (expr_seq k) ])); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [op][e1][e2]->.
      destruct (bin_op_enum_surj op) as [? ?].
      destruct (expr_shape_enum_surj (shape_expr e1)) as [?].
      destruct (expr_shape_enum_surj (shape_expr e2)) as [?].
      eexists _; [done|].
      eexists _; [done|].
      eexists _; [done|].
      exists e1; [ by rewrite //= |].
      exists e2; [ by rewrite //= |].
      f_equal; done.
    - move=> [??][??][??][?]?[?]?<-.
      eexists _.
      eexists _.
      eexists _.
      done.
  }
  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply bigcup_measurable; move=> k _.
  apply sub_sigma_algebra.
  eexists (BinOp (bin_op_enum i) (gen_expr (expr_shape_enum j)) (gen_expr (expr_shape_enum k))).
  { rewrite //=. split; by apply gen_expr_generator. }
  by rewrite /expr_seq/preimage //= (expr_shape_cyl _) (expr_shape_cyl _).
Qed.
Hint Resolve ecov_binop_meas : measlang.

Lemma ecov_if_meas         : measurable ecov_if.
Proof.
  eapply (eq_measurable (\bigcup_i \bigcup_j \bigcup_k (image3 (expr_seq i) (expr_seq j) (expr_seq k) IfC))); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [e0][e1][e2]->.
      destruct (expr_shape_enum_surj (shape_expr e0)) as [?].
      destruct (expr_shape_enum_surj (shape_expr e1)) as [?].
      destruct (expr_shape_enum_surj (shape_expr e2)) as [?].
      eexists _; [done|].
      eexists _; [done|].
      eexists _; [done|].
      exists e0; [ by rewrite //= |].
      exists e1; [ by rewrite //= |].
      exists e2; [ by rewrite //= |].
      f_equal; done.
    - rewrite /image3//=.
      move=> [??][??][??][??][??][??]<-.
      eexists _.
      eexists _.
      eexists _.
      done.
  }
  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply bigcup_measurable; move=> k _.
  apply sub_sigma_algebra.
  eexists (If (gen_expr (expr_shape_enum i)) (gen_expr (expr_shape_enum j)) (gen_expr (expr_shape_enum k))).
  { rewrite //=. split; last split. all: by apply gen_expr_generator. }
  rewrite /expr_seq/preimage//=.
  rewrite <-(expr_shape_cyl _).
  rewrite <-(expr_shape_cyl _).
  rewrite <-(expr_shape_cyl _).
  done.
Qed.
Hint Resolve ecov_if_meas : measlang.

Lemma ecov_pair_meas       : measurable ecov_pair.
Proof.
  eapply (eq_measurable (\bigcup_i \bigcup_j (image2 (expr_seq i) (expr_seq j) PairC))); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [e0][e1]->.
      destruct (expr_shape_enum_surj (shape_expr e0)) as [?].
      destruct (expr_shape_enum_surj (shape_expr e1)) as [?].
      eexists _; [done|].
      eexists _; [done|].
      exists e0; [ by rewrite //= |].
      exists e1; [ by rewrite //= |].
      f_equal; done.
    - rewrite /image2//=.
      move=> [??][??][??][??]<-.
      eexists _.
      eexists _.
      done.
  }
  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (Pair (gen_expr (expr_shape_enum i)) (gen_expr (expr_shape_enum j))).
  { rewrite //=. split. all: by apply gen_expr_generator. }
  by rewrite /expr_seq/preimage //= (expr_shape_cyl _) (expr_shape_cyl _).
Qed.
Hint Resolve ecov_pair_meas : measlang.

Lemma ecov_fst_meas        : measurable ecov_fst.
Proof.
  rewrite /ecov_fst.
  eapply (eq_measurable (\bigcup_n [set FstC v | v in (expr_seq n)])); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [v ->].
      destruct (expr_shape_enum_surj (shape_expr v)) as [? ?].
      eexists _; [done|].
      eexists _; [|done].
      by rewrite //=.
    - move=> [? _] [x ?] <-.
      by eexists _.
  }
  apply bigcup_measurable.
  move=> k _.
  apply sub_sigma_algebra.
  exists (Fst (gen_expr (expr_shape_enum k))); [ by apply gen_expr_generator |].
  by rewrite /expr_seq/preimage //= (expr_shape_cyl _).
Qed.
Hint Resolve ecov_fst_meas : measlang.

Lemma ecov_snd_meas        : measurable ecov_snd.
Proof.
  rewrite /ecov_snd.
  eapply (eq_measurable (\bigcup_n [set SndC v | v in (expr_seq n)])); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [v ->].
      destruct (expr_shape_enum_surj (shape_expr v)) as [? ?].
      eexists _; [done|].
      eexists _; [|done].
      by rewrite //=.
    - move=> [? _] [x ?] <-.
      by eexists _.
  }
  apply bigcup_measurable.
  move=> k _.
  apply sub_sigma_algebra.
  exists (Snd (gen_expr (expr_shape_enum k))); [ by apply gen_expr_generator |].
  by rewrite /expr_seq/preimage //= (expr_shape_cyl _).
Qed.
Hint Resolve ecov_snd_meas : measlang.

Lemma ecov_injl_meas       : measurable ecov_injl.
Proof.
  rewrite /ecov_injl.
  eapply (eq_measurable (\bigcup_n [set InjLC v | v in (expr_seq n)])); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [v ->].
      destruct (expr_shape_enum_surj (shape_expr v)) as [? ?].
      eexists _; [done|].
      eexists _; [|done].
      by rewrite //=.
    - move=> [? _] [x ?] <-.
      by eexists _.
  }
  apply bigcup_measurable.
  move=> k _.
  apply sub_sigma_algebra.
  exists (InjL (gen_expr (expr_shape_enum k))); [ by apply gen_expr_generator |].
  by rewrite /expr_seq/preimage //= (expr_shape_cyl _).
Qed.
Hint Resolve ecov_injl_meas : measlang.

Lemma ecov_injr_meas       : measurable ecov_injr.
Proof.
  rewrite /ecov_injr.
  eapply (eq_measurable (\bigcup_n [set InjRC v | v in (expr_seq n)])); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [v ->].
      destruct (expr_shape_enum_surj (shape_expr v)) as [? ?].
      eexists _; [done|].
      eexists _; [|done].
      by rewrite //=.
    - move=> [? _] [x ?] <-.
      by eexists _.
  }
  apply bigcup_measurable.
  move=> k _.
  apply sub_sigma_algebra.
  exists (InjR (gen_expr (expr_shape_enum k))); [ by apply gen_expr_generator |].
  by rewrite /expr_seq/preimage //= (expr_shape_cyl _).
Qed.
Hint Resolve ecov_injr_meas : measlang.

Lemma ecov_case_meas         : measurable ecov_case.
Proof.
  eapply (eq_measurable (\bigcup_i \bigcup_j \bigcup_k (image3 (expr_seq i) (expr_seq j) (expr_seq k) CaseC))); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [e0][e1][e2]->.
      destruct (expr_shape_enum_surj (shape_expr e0)) as [?].
      destruct (expr_shape_enum_surj (shape_expr e1)) as [?].
      destruct (expr_shape_enum_surj (shape_expr e2)) as [?].
      eexists _; [done|].
      eexists _; [done|].
      eexists _; [done|].
      exists e0; [ by rewrite //= |].
      exists e1; [ by rewrite //= |].
      exists e2; [ by rewrite //= |].
      f_equal; done.
    - rewrite /image3//=.
      move=> [??][??][??][??][??][??]<-.
      eexists _.
      eexists _.
      eexists _.
      done.
  }
  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply bigcup_measurable; move=> k _.
  apply sub_sigma_algebra.
  eexists (Case (gen_expr (expr_shape_enum i)) (gen_expr (expr_shape_enum j)) (gen_expr (expr_shape_enum k))).
  { rewrite //=. split; last split. all: by apply gen_expr_generator. }
  rewrite /expr_seq/preimage//=.
  rewrite <-(expr_shape_cyl _).
  rewrite <-(expr_shape_cyl _).
  rewrite <-(expr_shape_cyl _).
  done.
Qed.
Hint Resolve ecov_case_meas : measlang.

Lemma ecov_alloc_meas      : measurable ecov_alloc.
Proof.
  eapply (eq_measurable (\bigcup_i \bigcup_j (image2 (expr_seq i) (expr_seq j) AllocNC))); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [e0][e1]->.
      destruct (expr_shape_enum_surj (shape_expr e0)) as [?].
      destruct (expr_shape_enum_surj (shape_expr e1)) as [?].
      eexists _; [done|].
      eexists _; [done|].
      exists e0; [ by rewrite //= |].
      exists e1; [ by rewrite //= |].
      f_equal; done.
    - rewrite /image2//=.
      move=> [??][??][??][??]<-.
      eexists _.
      eexists _.
      done.
  }
  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (AllocN (gen_expr (expr_shape_enum i)) (gen_expr (expr_shape_enum j))).
  { rewrite //=. split. all: by apply gen_expr_generator. }
  by rewrite /expr_seq/preimage //= (expr_shape_cyl _) (expr_shape_cyl _).
Qed.
Hint Resolve ecov_alloc_meas : measlang.

Lemma ecov_load_meas       : measurable ecov_load.
Proof.
  rewrite /ecov_load.
  eapply (eq_measurable (\bigcup_n [set LoadC v | v in (expr_seq n)])); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [v ->].
      destruct (expr_shape_enum_surj (shape_expr v)) as [? ?].
      eexists _; [done|].
      eexists _; [|done].
      by rewrite //=.
    - move=> [? _] [x ?] <-.
      by eexists _.
  }
  apply bigcup_measurable.
  move=> k _.
  apply sub_sigma_algebra.
  exists (Load (gen_expr (expr_shape_enum k))); [ by apply gen_expr_generator |].
  by rewrite /expr_seq/preimage //= (expr_shape_cyl _).
Qed.
Hint Resolve ecov_load_meas : measlang.

Lemma ecov_store_meas      : measurable ecov_store.
Proof.
  eapply (eq_measurable (\bigcup_i \bigcup_j (image2 (expr_seq i) (expr_seq j) StoreC))); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [e0][e1]->.
      destruct (expr_shape_enum_surj (shape_expr e0)) as [?].
      destruct (expr_shape_enum_surj (shape_expr e1)) as [?].
      eexists _; [done|].
      eexists _; [done|].
      exists e0; [ by rewrite //= |].
      exists e1; [ by rewrite //= |].
      f_equal; done.
    - rewrite /image2//=.
      move=> [??][??][??][??]<-.
      eexists _.
      eexists _.
      done.
  }
  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (Store (gen_expr (expr_shape_enum i)) (gen_expr (expr_shape_enum j))).
  { rewrite //=. split. all: by apply gen_expr_generator. }
  by rewrite /expr_seq/preimage //= (expr_shape_cyl _) (expr_shape_cyl _).
Qed.
Hint Resolve ecov_store_meas : measlang.

Lemma ecov_alloctape_meas  : measurable ecov_alloctape.
Proof.
  eapply (eq_measurable (\bigcup_n [set AllocTapeC v | v in (expr_seq n)])); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [v ->].
      destruct (expr_shape_enum_surj (shape_expr v)) as [? ?].
      eexists _; [done|].
      eexists _; [|done].
      by rewrite //=.
    - move=> [? _] [x ?] <-.
      by eexists _.
  }
  apply bigcup_measurable.
  move=> k _.
  apply sub_sigma_algebra.
  exists (AllocTape (gen_expr (expr_shape_enum k))); [ by apply gen_expr_generator |].
  by rewrite /expr_seq/preimage //= (expr_shape_cyl _).
Qed.
Hint Resolve ecov_alloctape_meas : measlang.

Lemma ecov_rand_meas       : measurable ecov_rand.
Proof.
  eapply (eq_measurable (\bigcup_i \bigcup_j (image2 (expr_seq i) (expr_seq j) RandC))); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [e0][e1]->.
      destruct (expr_shape_enum_surj (shape_expr e0)) as [?].
      destruct (expr_shape_enum_surj (shape_expr e1)) as [?].
      eexists _; [done|].
      eexists _; [done|].
      exists e0; [ by rewrite //= |].
      exists e1; [ by rewrite //= |].
      f_equal; done.
    - rewrite /image2//=.
      move=> [??][??][??][??]<-.
      eexists _.
      eexists _.
      done.
  }
  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (Rand (gen_expr (expr_shape_enum i)) (gen_expr (expr_shape_enum j))).
  { rewrite //=. split. all: by apply gen_expr_generator. }
  by rewrite /expr_seq/preimage //= (expr_shape_cyl _) (expr_shape_cyl _).
Qed.
Hint Resolve ecov_rand_meas : measlang.

Lemma ecov_allocutape_meas : measurable ecov_allocutape.
Proof.
  apply sub_sigma_algebra.
  rewrite /ecov_allocutape /expr_cyl //=.
  exists AllocUTape; by rewrite //=.
Qed.
Hint Resolve ecov_allocutape_meas : measlang.

Lemma ecov_urand_meas : measurable ecov_urand.
Proof.
  rewrite /ecov_urand.
  eapply (eq_measurable (\bigcup_n [set URandC v | v in (expr_seq n)])); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [v ->].
      destruct (expr_shape_enum_surj (shape_expr v)) as [? ?].
      eexists _; [done|].
      eexists _; [|done].
      by rewrite //=.
    - move=> [? _] [x ?] <-.
      by eexists _.
  }
  apply bigcup_measurable.
  move=> k _.
  apply sub_sigma_algebra.
  exists (URand (gen_expr (expr_shape_enum k))); [ by apply gen_expr_generator |].
  by rewrite /expr_seq/preimage //= (expr_shape_cyl _).
Qed.
Hint Resolve ecov_urand_meas : measlang.

Lemma ecov_tick_meas       : measurable ecov_tick.
Proof.
  rewrite /ecov_urand.
  eapply (eq_measurable (\bigcup_n [set TickC v | v in (expr_seq n)])); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [v ->].
      destruct (expr_shape_enum_surj (shape_expr v)) as [? ?].
      eexists _; [done|].
      eexists _; [|done].
      by rewrite //=.
    - move=> [? _] [x ?] <-.
      by eexists _.
  }
  apply bigcup_measurable.
  move=> k _.
  apply sub_sigma_algebra.
  exists (Tick (gen_expr (expr_shape_enum k))); [ by apply gen_expr_generator |].
  by rewrite /expr_seq/preimage //= (expr_shape_cyl _).
Qed.
Hint Resolve ecov_tick_meas : measlang.

Lemma vcov_lit_meas : measurable vcov_lit.
Proof.
  rewrite /vcov_lit.
  eapply (eq_measurable (\bigcup_n [set LitVC v | v in (base_lit_seq n)])); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [v ->].
      destruct (base_lit_shape_enum_surj (shape_base_lit v)) as [? ?].
      eexists _; [done|].
      eexists _; [|done].
      by rewrite //=.
    - move=> [? _] [x ?] <-.
      by eexists _.
  }
  apply bigcup_measurable.
  move=> k _.
  apply sub_sigma_algebra.
  exists (LitV (gen_base_lit (base_lit_shape_enum k))); [ by apply gen_base_lit_generator |].
  by rewrite /base_lit_seq/preimage //= (base_lit_shape_cyl _).
Qed.
Hint Resolve vcov_lit_meas : measlang.

Lemma vcov_rec_meas        : measurable vcov_rec.
Proof.
  eapply (eq_measurable (\bigcup_i \bigcup_j \bigcup_k
                           [set (RecVC (binder_enum j) (binder_enum k) e) | e in (expr_seq i)])); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [f][x][e]->.
      destruct (binder_enum_surj f) as [? ?].
      destruct (binder_enum_surj x) as [? ?].
      destruct (expr_shape_enum_surj (shape_expr e)) as [?].
      eexists _; [done|].
      eexists _; [done|].
      eexists _; [done|].
      exists e; [ by rewrite //= |].
      f_equal; done.
    - move=> [??][??][??][??<-].
      eexists _.
      eexists _.
      eexists _.
      done.
  }
  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply bigcup_measurable; move=> k _.
  apply sub_sigma_algebra.
  eexists (RecV (binder_enum j) (binder_enum k) (gen_expr (expr_shape_enum i))); [ by apply gen_expr_generator |].
  by rewrite /expr_seq/preimage //= (expr_shape_cyl _).
Qed.
Hint Resolve vcov_rec_meas : measlang.

Lemma vcov_pair_meas       : measurable vcov_pair.
Proof.
  eapply (eq_measurable (\bigcup_i \bigcup_j (image2 (val_seq i) (val_seq j) PairVC))); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [e0][e1]->.
      destruct (val_shape_enum_surj (shape_val e0)) as [?].
      destruct (val_shape_enum_surj (shape_val e1)) as [?].
      eexists _; [done|].
      eexists _; [done|].
      exists e0; [ by rewrite //= |].
      exists e1; [ by rewrite //= |].
      f_equal; done.
    - rewrite /image2//=.
      move=> [??][??][??][??]<-.
      eexists _.
      eexists _.
      done.
  }
  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (PairV (gen_val (val_shape_enum i)) (gen_val (val_shape_enum j))).
  { rewrite //=. split. all: by apply gen_val_generator. }
  by rewrite /val_seq/preimage //= (val_shape_cyl _) (val_shape_cyl _).
Qed.
Hint Resolve vcov_pair_meas : measlang.

Lemma vcov_injlv_meas      : measurable vcov_injlv.
Proof.
  rewrite /vcov_injlv.
  eapply (eq_measurable (\bigcup_n [set InjLVC v | v in (val_seq n)])); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [v ->].
      destruct (val_shape_enum_surj (shape_val v)) as [? ?].
      eexists _; [done|].
      eexists _; [|done].
      by rewrite //=.
    - move=> [? _] [x ?] <-.
      by eexists _.
  }
  apply bigcup_measurable.
  move=> k _.
  apply sub_sigma_algebra.
  exists (InjLV (gen_val (val_shape_enum k))); [ by apply gen_val_generator |].
  by rewrite /val_seq/preimage //= (val_shape_cyl _).
Qed.
Hint Resolve vcov_injlv_meas : measlang.

Lemma vcov_injrv_meas      : measurable vcov_injrv.
Proof.
  eapply (eq_measurable (\bigcup_n [set InjRVC v | v in (val_seq n)])); last first.
  { rewrite /bigcup/=.
    apply /predeqP =>y /=.
    split.
    - move=> [v ->].
      destruct (val_shape_enum_surj (shape_val v)) as [? ?].
      eexists _; [done|].
      eexists _; [|done].
      by rewrite //=.
    - move=> [? _] [x ?] <-.
      by eexists _.
  }
  apply bigcup_measurable.
  move=> k _.
  apply sub_sigma_algebra.
  exists (InjRV (gen_val (val_shape_enum k))); [ by apply gen_val_generator |].
  by rewrite /val_seq/preimage //= (val_shape_cyl _).
Qed.
Hint Resolve vcov_injrv_meas : measlang.


