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
From clutch.meas_lang.lang Require Export prelude types shapes constructors.
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


Definition ecov_val        := range ValU.
Definition ecov_var        := range VarU.
Definition ecov_rec        := range RecU.
Definition ecov_app        := range AppU.
Definition ecov_unop       := range UnOpU.
Definition ecov_binop      := range BinOpU.
Definition ecov_if         := range IfU.
Definition ecov_pair       := range PairU.
Definition ecov_fst        := range FstU.
Definition ecov_snd        := range SndU.
Definition ecov_injl       := range InjLU.
Definition ecov_injr       := range InjRU.
Definition ecov_case       := range CaseU.
Definition ecov_alloc      := range AllocU.
Definition ecov_load       := range LoadU.
Definition ecov_store      := range StoreU.
Definition ecov_alloctape  := range AllocTapeU.
Definition ecov_rand       := range RandU.
Definition ecov_allocutape := [set AllocUTapeU].
Definition ecov_urand      := range UrandU.
Definition ecov_tick       := range TickU.

Definition vcov_lit        := range LitVU.
Definition vcov_rec        := range RecVU.
Definition vcov_pair       := range PairVU.
Definition vcov_injlv      := range InjLVU.
Definition vcov_injrv      := range InjRVU.

Definition bcov_LitInt      := range LitIntU.
Definition bcov_LitBool     := range LitBoolU.
Definition bcov_LitUnit     := [set  LitUnitC].
Definition bcov_LitLoc      := range LitLocU.
Definition bcov_LitLbl      := range LitLblU.
Definition bcov_LitReal     := range LitRealU.

(* Both will use the decomposition argument. *)
Lemma bcov_LitInt_meas_set  : measurable bcov_LitInt.
Proof.
  apply sub_sigma_algebra.
  rewrite /base_lit_cyl/=.
  exists (LitInt setT).
  { by rewrite /=/measurable/=/discr_measurable/=. }
  rewrite /bcov_LitInt/=.
  apply /predeqP =>y /=.
  split.
  - by move=> [x??]; exists x.
  - by move=> [x?]; exists x.
Qed.
Hint Resolve bcov_LitInt_meas_set : measlang.

Lemma bcov_LitBool_meas_set : measurable bcov_LitBool.
Proof.
  apply sub_sigma_algebra.
  rewrite /base_lit_cyl/=.
  exists (LitBool setT).
  { by rewrite /=/measurable/=/discr_measurable/=. }
  rewrite /bcov_LitBool/=.
  apply /predeqP =>y /=.
  split.
  - by move=> [x??]; exists x.
  - by move=> [x?]; exists x.
Qed.
Hint Resolve bcov_LitBool_meas_set : measlang.

Lemma bcov_LitUnit_meas_set : measurable bcov_LitUnit.
Proof.
  apply sub_sigma_algebra.
  rewrite /base_lit_cyl/=.
  exists (LitUnit).
  { by rewrite /=/measurable/=/discr_measurable/=. }
  rewrite /bcov_LitUnit//=.
Qed.
Hint Resolve bcov_LitUnit_meas_set : measlang.

Lemma bcov_LitLoc_meas_set  : measurable bcov_LitLoc.
Proof.
  apply sub_sigma_algebra.
  rewrite /base_lit_cyl/=.
  exists (LitLoc setT).
  { by rewrite /=/measurable/=/discr_measurable/=. }
  rewrite /bcov_LitLoc/=.
  apply /predeqP =>y /=.
  split.
  - by move=> [x??]; exists x.
  - by move=> [x?]; exists x.
Qed.
Hint Resolve bcov_LitLoc_meas_set : measlang.

Lemma bcov_LitLbl_meas_set  : measurable bcov_LitLbl.
Proof.
  apply sub_sigma_algebra.
  rewrite /base_lit_cyl/=.
  exists (LitLbl setT).
  { by rewrite /=/measurable/=/discr_measurable/=. }
  rewrite /bcov_LitLbl/=.
  apply /predeqP =>y /=.
  split.
  - by move=> [x??]; exists x.
  - by move=> [x?]; exists x.
Qed.
Hint Resolve bcov_LitLbl_meas_set : measlang.

Lemma bcov_LitReal_meas_set : measurable bcov_LitReal.
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
Hint Resolve bcov_LitReal_meas_set : measlang.

Arguments eq_measurable {_} {_} _ {_}.
Lemma ecov_val_meas_set : measurable ecov_val.
Proof.
  have -> : ecov_val = [set e  | ∃ v, e = ValC v].
  { apply /predeqP =>y //=; rewrite /ecov_val//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
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
Hint Resolve ecov_val_meas_set : measlang.

Lemma ecov_var_meas_set        : measurable ecov_var.
Proof.
  have -> : ecov_var = [set e  | ∃ s, e = VarC s].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
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
Hint Resolve ecov_var_meas_set : measlang.

Lemma ecov_rec_meas_set        : measurable ecov_rec.
Proof.
  have -> : ecov_rec =  [set e  | ∃ f x b, e = RecC f x b].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
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
Hint Resolve ecov_rec_meas_set : measlang.

Lemma ecov_app_meas_set        : measurable ecov_app.
Proof.
  have -> : ecov_app = [set e  | ∃ e1 e2, e = AppC e1 e2].
  { apply /predeqP =>y //=; rewrite /ecov_app//=; split.
    - by move=> [[??]?]<-; eexists _; eexists _.
    - by move=> [a[b->]]; eexists (a, b). }
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
Hint Resolve ecov_app_meas_set : measlang.

Lemma ecov_unop_meas_set       : measurable ecov_unop.
Proof.
  have -> : ecov_unop = [set e  | ∃ op x, e = UnOpC op x].
  { apply /predeqP =>y //=; rewrite /ecov_app//=; split.
    - by move=> [[??]?]<-; eexists _; eexists _.
    - by move=> [a[b->]]; eexists (a, b). }
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
Hint Resolve ecov_unop_meas_set : measlang.

Lemma ecov_binop_meas_set      : measurable ecov_binop.
Proof.
  have -> : ecov_binop = [set e  | ∃ op e1 e2, e = BinOpC op e1 e2].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
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
Hint Resolve ecov_binop_meas_set : measlang.

Lemma ecov_if_meas_set         : measurable ecov_if.
Proof.
  have -> : ecov_if = [set e  | ∃ e1 e2 e3, e = IfC e1 e2 e3].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
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
Hint Resolve ecov_if_meas_set : measlang.

Lemma ecov_pair_meas_set       : measurable ecov_pair.
Proof.
  have -> : ecov_pair = [set e  | ∃ e1 e2, e = PairC e1 e2].
  { apply /predeqP =>y //=; rewrite /ecov_app//=; split.
    - by move=> [[??]?]<-; eexists _; eexists _.
    - by move=> [a[b->]]; eexists (a, b). }
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
Hint Resolve ecov_pair_meas_set : measlang.

Lemma ecov_fst_meas_set        : measurable ecov_fst.
Proof.
  have -> : ecov_fst = [set e  | ∃ x, e = FstC x].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
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
Hint Resolve ecov_fst_meas_set : measlang.

Lemma ecov_snd_meas_set        : measurable ecov_snd.
Proof.
  have -> : ecov_snd = [set e  | ∃ x, e = SndC x].
  { apply /predeqP =>y //=; rewrite /ecov_snd//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
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
Hint Resolve ecov_snd_meas_set : measlang.

Lemma ecov_injl_meas_set       : measurable ecov_injl.
Proof.
  have -> : ecov_injl = [set e  | ∃ x, e = InjLC x].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
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
Hint Resolve ecov_injl_meas_set : measlang.

Lemma ecov_injr_meas_set       : measurable ecov_injr.
Proof.
  have -> : ecov_injr = [set e  | ∃ x, e = InjRC x].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
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
Hint Resolve ecov_injr_meas_set : measlang.

Lemma ecov_case_meas_set         : measurable ecov_case.
Proof.
  have -> : ecov_case = [set e  | ∃ e1 e2 e3, e = CaseC e1 e2 e3].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
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
Hint Resolve ecov_case_meas_set : measlang.

Lemma ecov_alloc_meas_set      : measurable ecov_alloc.
Proof.
  have -> : ecov_alloc = [set e  | ∃ x, e = AllocC x].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  (*
  eapply (eq_measurable (\bigcup_i \bigcup_j (image2 (expr_seq i) (expr_seq j) AllocC))); last first.
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
  *)
Admitted.
Hint Resolve ecov_alloc_meas_set : measlang.

Lemma ecov_load_meas_set       : measurable ecov_load.
Proof.
  have -> : ecov_load = [set e  | ∃ x, e = LoadC x].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
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
Hint Resolve ecov_load_meas_set : measlang.

Lemma ecov_store_meas_set      : measurable ecov_store.
Proof.
  have -> : ecov_store = [set e  | ∃ e1 e2, e = StoreC e1 e2].
  { apply /predeqP =>y //=; rewrite /ecov_app//=; split.
    - by move=> [[??]?]<-; eexists _; eexists _.
    - by move=> [a[b->]]; eexists (a, b). }
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
Hint Resolve ecov_store_meas_set : measlang.

Lemma ecov_alloctape_meas_set  : measurable ecov_alloctape.
Proof.
  have -> : ecov_alloctape = [set e  | ∃ x, e = AllocTapeC x].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
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
Hint Resolve ecov_alloctape_meas_set : measlang.

Lemma ecov_rand_meas_set       : measurable ecov_rand.
Proof.
  have -> : ecov_rand = [set e  | ∃ e1 e2, e = RandC e1 e2].
  { apply /predeqP =>y //=; rewrite /ecov_app//=; split.
    - by move=> [[??]?]<-; eexists _; eexists _.
    - by move=> [a[b->]]; eexists (a, b). }
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
Hint Resolve ecov_rand_meas_set : measlang.

Lemma ecov_allocutape_meas_set : measurable ecov_allocutape.
Proof.
  apply sub_sigma_algebra.
  rewrite /ecov_allocutape /expr_cyl //=.
  exists AllocUTape; by rewrite //=.
Qed.
Hint Resolve ecov_allocutape_meas_set : measlang.

Lemma ecov_urand_meas_set : measurable ecov_urand.
Proof.
  have -> : ecov_urand = [set e  | ∃ x, e = UrandU x].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
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
Hint Resolve ecov_urand_meas_set : measlang.

Lemma ecov_tick_meas_set       : measurable ecov_tick.
Proof.
  have -> : ecov_tick = [set e  | ∃ x, e = TickC x].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
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
Hint Resolve ecov_tick_meas_set : measlang.

Lemma vcov_lit_meas_set : measurable vcov_lit.
Proof.
  have -> : vcov_lit = [set e  | ∃ x, e = LitVC x].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
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
Hint Resolve vcov_lit_meas_set : measlang.

Lemma vcov_rec_meas_set        : measurable vcov_rec.
Proof.
  have -> : vcov_rec =  [set e  | ∃ f x b, e = RecVC f x b].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
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
Hint Resolve vcov_rec_meas_set : measlang.

Lemma vcov_pair_meas_set       : measurable vcov_pair.
Proof.
  have -> : vcov_pair = [set e  | ∃ e1 e2, e = PairVC e1 e2].
  { apply /predeqP =>y //=; rewrite /ecov_app//=; split.
    - by move=> [[??]?]<-; eexists _; eexists _.
    - by move=> [a[b->]]; eexists (a, b). }
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
Hint Resolve vcov_pair_meas_set : measlang.

Lemma vcov_injlv_meas_set      : measurable vcov_injlv.
Proof.
  have -> : vcov_injlv = [set e  | ∃ x, e = InjLVU x].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
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
Hint Resolve vcov_injlv_meas_set : measlang.

Lemma vcov_injrv_meas_set      : measurable vcov_injrv.
Proof.
  have -> : vcov_injrv = [set e  | ∃ x, e = InjRVU x].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
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
Hint Resolve vcov_injrv_meas_set : measlang.
