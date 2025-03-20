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
From clutch.meas_lang.lang Require Export prelude types shapes cover.
Set Warnings "hiding-delimiting-key".

Local Open Scope classical_set_scope.


(** Projections:
      Each field (x : T) of each constructor k for type (T') has a projection function
        𝜋_k_x : T' -> T
      and a measurability lemma from the appropriate cover set S
        𝜋_k_x_meas : measurable_fun S 𝜋_k_x

      For each constructor k, there is also an "uncurried form"
        𝜋_kU : T' -> (... * ... * ...)%type
      which packages all the projections into one product type. The corresponding
      measurability proof is
        𝜋_kU_meas : measurable_fun S 𝜋_k_x
*)


(** Projection functions *)
Definition 𝜋_LitInt_z  (b : base_lit) : <<discr Z>> := match b with | LitInt  v => v | _ => point end.
Definition 𝜋_LitBool_b (b : base_lit) : <<discr bool>> := match b with | LitBool v => v | _ => point end.
Definition 𝜋_LitLoc_l  (b : base_lit) : <<discr loc>> := match b with | LitLoc  v => v | _ => point end.
Definition 𝜋_LitLbl_l  (b : base_lit) : <<discr loc>> := match b with | LitLbl  v => v | _ => point end.
Definition 𝜋_LitReal_r (b : base_lit) : ((R : realType) : measurableType _):= match b with | LitReal v => v | _ => point end.

Definition 𝜋_LitV_v    (v : val)      : base_lit         := match v with | LitV v => v | _ => point end.
Definition 𝜋_RecV_f    (v : val)      : <<discr binder>> := match v with | RecV f _ _ => f | _ => point end.
Definition 𝜋_RecV_x    (v : val)      : <<discr binder>> := match v with | RecV _ x _ => x | _ => point end.
Definition 𝜋_RecV_e    (v : val)      : expr             := match v with | RecV _ _ e => e | _ => point end.
Definition 𝜋_PairV_l   (v : val)      : val              := match v with | PairV r _ => r | _ => point end.
Definition 𝜋_PairV_r   (v : val)      : val              := match v with | PairV _ r => r | _ => point end.
Definition 𝜋_InjLV_v   (v : val)      : val              := match v with | InjLV r => r | _ => point end.
Definition 𝜋_InjRV_v   (v : val)      : val              := match v with | InjRV r => r | _ => point end.


Definition 𝜋_Val_v        (e : expr)     : val              := match e with | Val r => r | _ => point end.
Definition 𝜋_Var_v        (e : expr)     : <<discr binder>> := match e with | Var x => x | _ => point end.
Definition 𝜋_Rec_f        (e : expr)     : <<discr binder>> := match e with | Rec f _ _ => f | _ => point end.
Definition 𝜋_Rec_x        (e : expr)     : <<discr binder>> := match e with | Rec _ x _ => x | _ => point end.
Definition 𝜋_Rec_e        (e : expr)     : expr             := match e with | Rec _ _ e => e | _ => point end.
Definition 𝜋_UnOp_op      (e : expr)     : <<discr un_op>>  := match e with | UnOp op _ => op | _ => point end.
Definition 𝜋_UnOp_e       (e : expr)     : expr             := match e with | UnOp _  e => e | _ => point end.
Definition 𝜋_BinOp_op     (e : expr)     : <<discr bin_op>> := match e with | BinOp op _ _ => op | _ => point end.
Definition 𝜋_BinOp_l      (e : expr)     : expr             := match e with | BinOp _  e _ => e | _ => point end.
Definition 𝜋_BinOp_r      (e : expr)     : expr             := match e with | BinOp _  _ e => e | _ => point end.
Definition 𝜋_App_l        (e : expr)     : expr             := match e with | App e _ => e | _ => point end.
Definition 𝜋_App_r        (e : expr)     : expr             := match e with | App _ e => e | _ => point end.
Definition 𝜋_If_c         (e : expr)     : expr             := match e with | If e _ _ => e | _ => point end.
Definition 𝜋_If_l         (e : expr)     : expr             := match e with | If _ e _ => e | _ => point end.
Definition 𝜋_If_r         (e : expr)     : expr             := match e with | If _ _ e => e | _ => point end.
Definition 𝜋_Pair_l       (e : expr)     : expr             := match e with | Pair e _ => e | _ => point end.
Definition 𝜋_Pair_r       (e : expr)     : expr             := match e with | Pair _ e => e | _ => point end.
Definition 𝜋_Fst_e        (e : expr)     : expr             := match e with | Fst e => e | _ => point end.
Definition 𝜋_Snd_e        (e : expr)     : expr             := match e with | Snd e => e | _ => point end.
Definition 𝜋_InjL_e       (e : expr)     : expr             := match e with | InjL e => e | _ => point end.
Definition 𝜋_InjR_e       (e : expr)     : expr             := match e with | InjR e => e | _ => point end.
Definition 𝜋_Case_c       (e : expr)     : expr             := match e with | Case e _ _ => e | _ => point end.
Definition 𝜋_Case_l       (e : expr)     : expr             := match e with | Case _ e _ => e | _ => point end.
Definition 𝜋_Case_r       (e : expr)     : expr             := match e with | Case _ _ e => e | _ => point end.
Definition 𝜋_Alloc_e      (e : expr)     : expr             := match e with | Alloc e => e | _ => point end.
Definition 𝜋_Load_e       (e : expr)     : expr             := match e with | Load e => e | _ => point end.
Definition 𝜋_Store_l      (e : expr)     : expr             := match e with | Store e _ => e | _ => point end.
Definition 𝜋_Store_e      (e : expr)     : expr             := match e with | Store _ e => e | _ => point end.
Definition 𝜋_AllocTape_e  (e : expr)     : expr             := match e with | AllocTape e => e | _ => point end.
Definition 𝜋_Rand_t       (e : expr)     : expr             := match e with | Rand e _ => e | _ => point end.
Definition 𝜋_Rand_N       (e : expr)     : expr             := match e with | Rand _ e => e | _ => point end.
Definition 𝜋_URand_e      (e : expr)     : expr             := match e with | URand e => e | _ => point end.
Definition 𝜋_Tick_e       (e : expr)     : expr             := match e with | Tick e => e | _ => point end.


(** Uncurred projections *)
Definition 𝜋_LitIntU    := 𝜋_LitInt_z.
Definition 𝜋_LitBoolU   := 𝜋_LitBool_b.
Definition 𝜋_LitLocU    := 𝜋_LitLoc_l.
Definition 𝜋_LitLblU    := 𝜋_LitLbl_l.
Definition 𝜋_LitRealU   := 𝜋_LitReal_r.

Definition 𝜋_LitVU      := 𝜋_LitV_v.
Definition 𝜋_RecVU      := 𝜋_RecV_f        △ 𝜋_RecV_x    △ 𝜋_RecV_e.
Definition 𝜋_PairVU     := 𝜋_PairV_l       △ 𝜋_PairV_r.
Definition 𝜋_InjLVU     := 𝜋_InjLV_v.
Definition 𝜋_InjRVU     := 𝜋_InjRV_v.

Definition 𝜋_ValU       := 𝜋_Val_v.
Definition 𝜋_VarU       := 𝜋_Var_v.
Definition 𝜋_RecU       := 𝜋_Rec_f         △ 𝜋_Rec_x     △ 𝜋_Rec_e.
Definition 𝜋_UnOpU      := 𝜋_UnOp_op       △ 𝜋_UnOp_e.
Definition 𝜋_BinOpU     := 𝜋_BinOp_op      △ 𝜋_BinOp_l   △ 𝜋_BinOp_r.
Definition 𝜋_AppU       := 𝜋_App_l         △ 𝜋_App_r.
Definition 𝜋_IfU        := 𝜋_If_c          △ 𝜋_If_l      △ 𝜋_If_r.
Definition 𝜋_PairU      := 𝜋_Pair_l        △ 𝜋_Pair_r.
Definition 𝜋_FstU       := 𝜋_Fst_e.
Definition 𝜋_SndU       := 𝜋_Snd_e.
Definition 𝜋_InjLU      := 𝜋_InjL_e.
Definition 𝜋_InjRU      := 𝜋_InjR_e.
Definition 𝜋_CaseU      := 𝜋_Case_c        △ 𝜋_Case_l    △ 𝜋_Case_r.
Definition 𝜋_AllocU     := 𝜋_Alloc_e.
Definition 𝜋_LoadU      := 𝜋_Load_e.
Definition 𝜋_StoreU     := 𝜋_Store_l       △ 𝜋_Store_e.
Definition 𝜋_AllocTapeU := 𝜋_AllocTape_e.
Definition 𝜋_RandU      := 𝜋_Rand_t        △ 𝜋_Rand_N.
Definition 𝜋_URandU     := 𝜋_URand_e.
Definition 𝜋_TickU      := 𝜋_Tick_e.


(** Primitive Projection functions measurability *)
Lemma 𝜋_LitInt_z_meas  : measurable_fun bcov_LitInt 𝜋_LitInt_z.
Proof.
  have -> : bcov_LitInt = [set e  | ∃ v, e = LitIntU v].
  { apply /predeqP =>y //=; rewrite /ecov_val//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  intros _H S HS.
  apply sub_sigma_algebra.
  exists (LitInt S).
  { by rewrite /base_lit_ML. }
  rewrite /bcov_LitInt/preimage/setI/𝜋_LitInt_z/=.
  apply /predeqP =>y /=.
  split.
  - move=> [x Hs <-].
    split; [|done].
    by exists x.
  - move=> [[z ->]] /= ?.
    exists z; done.
Qed.
Hint Resolve 𝜋_LitInt_z_meas : measlang.
Hint Resolve 𝜋_LitInt_z_meas : mf_fun.

Lemma 𝜋_LitBool_b_meas : measurable_fun bcov_LitBool 𝜋_LitBool_b.
Proof.
  have -> : bcov_LitBool = [set e  | ∃ v, e = LitBoolU v].
  { apply /predeqP =>y //=; rewrite /ecov_val//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  intros _H S HS.
  apply sub_sigma_algebra.
  exists (LitBool S).
  { by rewrite /base_lit_ML. }
  rewrite /bcov_LitInt/preimage/setI/𝜋_LitInt_z/=.
  apply /predeqP =>y /=.
  split.
  - move=> [x Hs <-].
    split; [|done].
    by exists x.
  - move=> [[z ->]] /= ?.
    exists z; done.
Qed.
Hint Resolve 𝜋_LitBool_b_meas : measlang.
Hint Resolve 𝜋_LitBool_b_meas : mf_fun.

Lemma 𝜋_LitLoc_l_meas  : measurable_fun bcov_LitLoc 𝜋_LitLoc_l.
Proof.
  have -> : bcov_LitLoc = [set e  | ∃ v, e = LitLocU v].
  { apply /predeqP =>y //=; rewrite /ecov_val//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  intros _H S HS.
  apply sub_sigma_algebra.
  exists (LitLoc S).
  { by rewrite /base_lit_ML. }
  rewrite /bcov_LitInt/preimage/setI/𝜋_LitInt_z/=.
  apply /predeqP =>y /=.
  split.
  - move=> [x Hs <-].
    split; [|done].
    by exists x.
  - move=> [[z ->]] /= ?.
    exists z; done.
Qed.
Hint Resolve 𝜋_LitLoc_l_meas : measlang.
Hint Resolve 𝜋_LitLoc_l_meas : mf_fun.

Lemma 𝜋_LitLbl_l_meas  : measurable_fun bcov_LitLbl 𝜋_LitLbl_l.
Proof.
  have -> : bcov_LitLbl = [set e  | ∃ v, e = LitLblU v].
  { apply /predeqP =>y //=; rewrite /ecov_val//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  intros _H S HS.
  apply sub_sigma_algebra.
  exists (LitLbl S).
  { by rewrite /base_lit_ML. }
  rewrite /bcov_LitInt/preimage/setI/𝜋_LitInt_z/=.
  apply /predeqP =>y /=.
  split.
  - move=> [x Hs <-].
    split; [|done].
    by exists x.
  - move=> [[z ->]] /= ?.
    exists z; done.
Qed.
Hint Resolve 𝜋_LitLbl_l_meas : measlang.
Hint Resolve 𝜋_LitLbl_l_meas : mf_fun.

Lemma 𝜋_LitReal_r_meas : measurable_fun bcov_LitReal 𝜋_LitReal_r.
Proof.
  have -> : bcov_LitReal = [set e  | ∃ v, e = LitRealU v].
  { apply /predeqP =>y //=; rewrite /ecov_val//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  intros _H S HS.
  apply sub_sigma_algebra.
  exists (LitReal S).
  { by rewrite /base_lit_ML. }
  rewrite /bcov_LitInt/preimage/setI/𝜋_LitInt_z/=.
  apply /predeqP =>y /=.
  split.
  - move=> [x Hs <-].
    split; [|done].
    by exists x.
  - move=> [[z ->]] /= ?.
    exists z; done.
Qed.
Hint Resolve 𝜋_LitReal_r_meas : measlang.
Hint Resolve 𝜋_LitReal_r_meas : mf_fun.


Lemma 𝜋_LitV_v_meas    : measurable_fun vcov_lit   𝜋_LitV_v.
Proof.
  have -> : vcov_lit = [set e  | ∃ v, e = LitVU v].
  { apply /predeqP =>y //=; rewrite /ecov_val//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  into_gen_measurable; move=> S.                       (* codomain is generated SA *)
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.    (* Separate S into union of preimages *)
  move=> [SB + ->].                                    (* Destruct facts about S *)
  move=> [C ? <-].

  apply sub_sigma_algebra.                             (* Preimage is a generator *)
  eexists (LitV C). { simpl. assumption. }

  apply /predeqP =>y /=.
  split.
  - move=> [z ? <-].
    rewrite /𝜋_LitV_v/=.
    split; [by exists z|done].
  - move=> [[z ->]]; rewrite /𝜋_LitV_v/=; move=> ?.
    exists z; [done|done].
Qed.
Hint Resolve 𝜋_LitV_v_meas : measlang.
Hint Resolve 𝜋_LitV_v_meas : mf_fun.

Lemma 𝜋_RecV_f_meas    : measurable_fun vcov_rec   𝜋_RecV_f.
Proof.
  have -> : vcov_rec =  [set e  | ∃ f x b, e = RecVC f x b].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
  eapply (measurability binder_generated_by_singletons).
  move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [b ->].

  rewrite /ecov_rec.
  rewrite /preimage/=/setI//=.

  (* Simplify the projection preimage *)
  apply (eq_measurable [set x | (∃ (x0 : <<discr binder >>) (b0 : expr_pre), x = RecVC b x0 b0)]); last first.
  { apply /predeqP =>y /=.
    split.
    - move=> [[?[?[?->]]]<-] //=.
      by eexists _; eexists _.
    - move=> [? [? ->]].
      split; [|done].
      by eexists _; eexists _; eexists _.
  }

  (* Split into countable union *)
  apply (eq_measurable (\bigcup_i \bigcup_j
                          [set (RecVC b (binder_enum i) b0) |
                            b0 in (expr_ST (gen_expr (expr_shape_enum j)) )])); last first.
  { rewrite /bigcup//=.
    apply /predeqP =>y /=.
    split.
    - move=> [x[e->]].
      destruct (binder_enum_surj x) as [i Hi].
      destruct (expr_shape_enum_surj (shape_expr e)) as [j Hj].
      exists i; [done|].
      exists j; [done|].
      exists e.
      + by rewrite -expr_shape_cyl //=.
      + by rewrite -Hi.
    - move=> [??][??][??]<-.
      by eexists _; eexists _.
  }
  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (RecV b (binder_enum i) (gen_expr (expr_shape_enum j))).
  { by apply gen_expr_generator. }
  apply /predeqP =>y //=.
Qed.
Hint Resolve 𝜋_RecV_f_meas : measlang.
Hint Resolve 𝜋_RecV_f_meas : mf_fun.

Lemma 𝜋_RecV_x_meas    : measurable_fun vcov_rec   𝜋_RecV_x.
Proof.
  have -> : vcov_rec =  [set e  | ∃ f x b, e = RecVC f x b].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
  eapply (measurability binder_generated_by_singletons).
  move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [b ->].

  rewrite /ecov_rec.
  rewrite /preimage/=/setI//=.

  (* Simplify the projection preimage *)
  apply (eq_measurable [set x | (∃ (x0 : <<discr binder >>) (b0 : expr_pre), x = RecVC x0 b b0)]); last first.
  { apply /predeqP =>y /=.
    split.
    - move=> [[?[?[?->]]]<-] //=.
      by eexists _; eexists _.
    - move=> [? [? ->]].
      split; [|done].
      by eexists _; eexists _; eexists _.
  }

  (* Split into countable union *)
  apply (eq_measurable (\bigcup_i \bigcup_j
                          [set (RecVC (binder_enum i) b b0) |
                            b0 in (expr_ST (gen_expr (expr_shape_enum j)) )])); last first.
  { rewrite /bigcup//=.
    apply /predeqP =>y /=.
    split.
    - move=> [x[e->]].
      destruct (binder_enum_surj x) as [i Hi].
      destruct (expr_shape_enum_surj (shape_expr e)) as [j Hj].
      exists i; [done|].
      exists j; [done|].
      exists e.
      + by rewrite -expr_shape_cyl //=.
      + by rewrite -Hi.
    - move=> [??][??][??]<-.
      by eexists _; eexists _.
  }
  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (RecV (binder_enum i) b (gen_expr (expr_shape_enum j))).
  { by apply gen_expr_generator. }
  apply /predeqP =>y //=.
Qed.
Hint Resolve 𝜋_RecV_x_meas : measlang.
Hint Resolve 𝜋_RecV_x_meas : mf_fun.

Lemma 𝜋_RecV_e_meas    : measurable_fun vcov_rec   𝜋_RecV_e.
Proof.
  have -> : vcov_rec =  [set e  | ∃ f x b, e = RecVC f x b].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  eapply (eq_measurable
            (\bigcup_i \bigcup_j [set x | (∃ e0, x = RecVC (binder_enum i) (binder_enum j) e0 /\
                                           expr_ST C (𝜋_RecV_e x))])); last first.
  { apply /predeqP =>y /=.
    split.
    - rewrite /vcov_rec//=.
      move=> [[f[x[e->]]]+]; rewrite //=; move=> ?.
      rewrite /bigcup//=.
      destruct (binder_enum_surj f) as [i <-].
      destruct (binder_enum_surj x) as [j <-].
      eexists i; [done|].
      eexists j; [done|].
      eexists e.
      split; [|done].
      by f_equal.
    - rewrite /bigcup//=.
      move=> [i?][j?][e[-> +]]; rewrite //=; move=>?.
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (RecV (binder_enum i) (binder_enum j) C).
  { by simpl. }

  apply /predeqP =>y /=.
  split.
  - move=> [e?]<-.
    eexists e; simpl.
    split; [|by simpl].
    by f_equal.
  - move=> [?[->?]].
    eexists _; [done|].
    by f_equal.
Qed.
Hint Resolve 𝜋_RecV_e_meas : measlang.
Hint Resolve 𝜋_RecV_e_meas : mf_fun.


Lemma 𝜋_PairV_l_meas : measurable_fun vcov_pair  𝜋_PairV_l.
Proof.
  have -> : vcov_pair = [set e  | ∃ e1 e2, e = PairVC e1 e2].
  { apply /predeqP =>y //=; rewrite /ecov_app//=; split.
    - by move=> [[??]?]<-; eexists _; eexists _.
    - by move=> [a[b->]]; eexists (a, b). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  rewrite /vcov_pair/setI/=.
  eapply (eq_measurable
            (\bigcup_n [set x | (∃ v1 v2 : val_pre, x = PairVC v1 v2 /\
                                           (val_ST (gen_val (val_shape_enum n)) v2)) ∧
                                val_ST C (𝜋_PairV_l x)])); last first.
  { apply /predeqP =>y /=.
    split.
    - move=> [[? [z ->]] +]; simpl; move=> ?.
      destruct (val_shape_enum_surj (shape_val z)).
      eexists _; [done|].
      split; [|done].
      eexists _; eexists _; split; [done|].
      by rewrite -val_shape_cyl.
    - move=> [? _ [[? [? [-> ?]]] +]]; simpl; move=> ?.
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> k _.
  apply sub_sigma_algebra.
  eexists (PairV C (gen_val (val_shape_enum k))).
  { split; [done|]. by apply gen_val_generator. }

  apply /predeqP =>y /=.
  split.
  - move=> [? ? [ ? ? <-]].
    split.
    + by eexists _; eexists _; eauto.
    + by simpl.
  - move=> [[? [? [-> ?]]] +]; simpl; move=> ?.
    eexists _; [done|].
    eexists _; [done|].
    done.
Qed.
Hint Resolve 𝜋_PairV_l_meas : measlang.
Hint Resolve 𝜋_PairV_l_meas : mf_fun.

Lemma 𝜋_PairV_r_meas   : measurable_fun vcov_pair  𝜋_PairV_r.
Proof.
  have -> : vcov_pair = [set e  | ∃ e1 e2, e = PairVC e1 e2].
  { apply /predeqP =>y //=; rewrite /ecov_app//=; split.
    - by move=> [[??]?]<-; eexists _; eexists _.
    - by move=> [a[b->]]; eexists (a, b). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  rewrite /vcov_pair/setI/=.
  eapply (eq_measurable
            (\bigcup_n [set x | (∃ v1 v2 : val_pre, x = PairVC v1 v2 /\
                                           (val_ST (gen_val (val_shape_enum n)) v1)) ∧
                                val_ST C (𝜋_PairV_r x)])); last first.
  { apply /predeqP =>y /=.
    split.
    - move=> [[z [? ->]] +] //=; move=> ?.
      destruct (val_shape_enum_surj (shape_val z)).
      eexists _; [done|].
      split; [|done].
      eexists _; eexists _; split; [done|].
      by rewrite -val_shape_cyl.
    - move=> [? _ [[? [? [-> ?]]] +]]; simpl; move=> ?.
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> k _.
  apply sub_sigma_algebra.
  eexists (PairV (gen_val (val_shape_enum k)) C).
  { split; [|done]. by apply gen_val_generator. }

  apply /predeqP =>y /=.
  split.
  - move=> [? ? [ ? ? <-]].
    split.
    + by eexists _; eexists _; eauto.
    + by simpl.
  - move=> [[? [? [-> ?]]] +]; simpl; move=> ?.
    eexists _; [done|].
    eexists _; [done|].
    done.
Qed.
Hint Resolve 𝜋_PairV_r_meas : measlang.
Hint Resolve 𝜋_PairV_r_meas : mf_fun.


Lemma 𝜋_InjLV_v_meas   : measurable_fun vcov_injlv 𝜋_InjLV_v.
Proof.
  have -> : vcov_injlv = [set e  | ∃ x, e = InjLVU x].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].

  apply sub_sigma_algebra.
  eexists (InjLV C). { simpl. assumption. }

  apply /predeqP =>y /=.
  split.
  - move=> [z ? <-].
    rewrite //=.
    split; [by exists z|done].
  - move=> [[z ->]] //=; move=> ?.
    exists z; [done|done].
Qed.
Hint Resolve 𝜋_InjLV_v_meas : measlang.
Hint Resolve 𝜋_InjLV_v_meas : mf_fun.

Lemma 𝜋_InjRV_v_meas   : measurable_fun vcov_injrv 𝜋_InjRV_v.
Proof.
  have -> : vcov_injrv = [set e  | ∃ x, e = InjRVU x].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].

  apply sub_sigma_algebra.
  eexists (InjRV C). { simpl. assumption. }

  apply /predeqP =>y /=.
  split.
  - move=> [? z <-].
    rewrite //=.
    split; [by eexists _|done].
  - move=> [[z ->]] //=; move=> ?.
    exists z; [done|done].
Qed.
Hint Resolve 𝜋_InjRV_v_meas : measlang.
Hint Resolve 𝜋_InjRV_v_meas : mf_fun.



Lemma 𝜋_Val_v_meas         : measurable_fun ecov_val 𝜋_Val_v.
Proof.
  have -> : ecov_val = [set e  | ∃ v, e = ValC v].
  { apply /predeqP =>y //=; rewrite /ecov_val//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].

  apply sub_sigma_algebra.
  eexists (Val C). { simpl. assumption. }

  apply /predeqP =>y /=.
  split.
  - move=> [? z <-].
    rewrite //=.
    split; [by eexists _|done].
  - move=> [[z ->]] //=; move=> ?.
    exists z; [done|done].
Qed.
Hint Resolve 𝜋_Val_v_meas : measlang.
Hint Resolve 𝜋_Val_v_meas : mf_fun.


Lemma 𝜋_Var_v_meas         : measurable_fun ecov_var 𝜋_Var_v.
Proof.
  have -> : ecov_var = [set e  | ∃ x, e = VarU x].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  (** Instead of having spaces of binders (bad, would require major rework)
      we use the fact that the measure space of binders is generated
      by points *)
  eapply (measurability binder_generated_by_singletons).
  move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [b ->].

  rewrite /ecov_var.
  rewrite /preimage/=/setI//=.
  apply (eq_measurable [set VarC b]); last first.
  { apply /predeqP =>y /=.
    split.
    - by move=> [[? ->] <-] //=.
    - move=>-> //=.
      split; [|done].
      by exists b.
  }
  apply sub_sigma_algebra.
  eexists (Var b); by rewrite //=.
Qed.
Hint Resolve 𝜋_Var_v_meas : measlang.
Hint Resolve 𝜋_Var_v_meas : mf_fun.

Lemma 𝜋_Rec_f_meas         : measurable_fun ecov_rec 𝜋_Rec_f.
Proof.
  have -> : ecov_rec =  [set e  | ∃ f x b, e = RecC f x b].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
  eapply (measurability binder_generated_by_singletons).
  move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [b ->].

  rewrite /ecov_rec.
  rewrite /preimage/=/setI//=.

  (* Simplify the projection preimage *)
  apply (eq_measurable [set x | (∃ (x0 : <<discr binder >>) (b0 : expr_pre), x = RecC b x0 b0)]); last first.
  { apply /predeqP =>y /=.
    split.
    - move=> [[?[?[?->]]]<-] //=.
      by eexists _; eexists _.
    - move=> [? [? ->]].
      split; [|done].
      by eexists _; eexists _; eexists _.
  }

  (* Split into countable union *)
  apply (eq_measurable (\bigcup_i \bigcup_j
                          [set (RecC b (binder_enum i) b0) |
                            b0 in (expr_ST (gen_expr (expr_shape_enum j)) )])); last first.
  { rewrite /bigcup//=.
    apply /predeqP =>y /=.
    split.
    - move=> [x[e->]].
      destruct (binder_enum_surj x) as [i Hi].
      destruct (expr_shape_enum_surj (shape_expr e)) as [j Hj].
      exists i; [done|].
      exists j; [done|].
      exists e.
      + by rewrite -expr_shape_cyl //=.
      + by rewrite -Hi.
    - move=> [??][??][??]<-.
      by eexists _; eexists _.
  }
  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (Rec b (binder_enum i) (gen_expr (expr_shape_enum j))).
  { by apply gen_expr_generator. }
  apply /predeqP =>y //=.
Qed.
Hint Resolve 𝜋_Rec_f_meas : measlang.
Hint Resolve 𝜋_Rec_f_meas : mf_fun.

Lemma 𝜋_Rec_x_meas         : measurable_fun ecov_rec 𝜋_Rec_x.
Proof.
  have -> : ecov_rec =  [set e  | ∃ f x b, e = RecC f x b].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
  eapply (measurability binder_generated_by_singletons).
  move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [b ->].

  rewrite /ecov_rec.
  rewrite /preimage/=/setI//=.

  (* Simplify the projection preimage *)
  apply (eq_measurable [set x | (∃ (x0 : <<discr binder >>) (b0 : expr_pre), x = RecC x0 b b0)]); last first.
  { apply /predeqP =>y /=.
    split.
    - move=> [[?[?[?->]]]<-] //=.
      by eexists _; eexists _.
    - move=> [? [? ->]].
      split; [|done].
      by eexists _; eexists _; eexists _.
  }

  (* Split into countable union *)
  apply (eq_measurable (\bigcup_i \bigcup_j
                          [set (RecC (binder_enum i) b b0) |
                            b0 in (expr_ST (gen_expr (expr_shape_enum j)) )])); last first.
  { rewrite /bigcup//=.
    apply /predeqP =>y /=.
    split.
    - move=> [x[e->]].
      destruct (binder_enum_surj x) as [i Hi].
      destruct (expr_shape_enum_surj (shape_expr e)) as [j Hj].
      exists i; [done|].
      exists j; [done|].
      exists e.
      + by rewrite -expr_shape_cyl //=.
      + by rewrite -Hi.
    - move=> [??][??][??]<-.
      by eexists _; eexists _.
  }
  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (Rec (binder_enum i) b (gen_expr (expr_shape_enum j))).
  { by apply gen_expr_generator. }
  apply /predeqP =>y //=.
Qed.
Hint Resolve 𝜋_Rec_x_meas : measlang.
Hint Resolve 𝜋_Rec_x_meas : mf_fun.


Lemma 𝜋_Rec_e_meas         : measurable_fun ecov_rec 𝜋_Rec_e.
Proof.
  have -> : ecov_rec =  [set e  | ∃ f x b, e = RecC f x b].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  eapply (eq_measurable
            (\bigcup_i \bigcup_j [set x | (∃ e0, x = RecC (binder_enum i) (binder_enum j) e0 /\
                                           expr_ST C (𝜋_Rec_e x))])); last first.
  { apply /predeqP =>y /=.
    split.
    - rewrite /vcov_rec//=.
      move=> [[f[x[e->]]]+]; rewrite //=; move=> ?.
      rewrite /bigcup//=.
      destruct (binder_enum_surj f) as [i <-].
      destruct (binder_enum_surj x) as [j <-].
      eexists i; [done|].
      eexists j; [done|].
      eexists e.
      split; [|done].
      by f_equal.
    - rewrite /bigcup//=.
      move=> [i?][j?][e[-> +]]; rewrite //=; move=>?.
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (Rec (binder_enum i) (binder_enum j) C).
  { by simpl. }

  apply /predeqP =>y /=.
  split.
  - move=> [e?]<-.
    eexists e; simpl.
    split; [|by simpl].
    by f_equal.
  - move=> [?[->?]].
    eexists _; [done|].
    by f_equal.
Qed.
Hint Resolve 𝜋_Rec_e_meas : measlang.
Hint Resolve 𝜋_Rec_e_meas : mf_fun.

Lemma 𝜋_App_l_meas         : measurable_fun ecov_app 𝜋_App_l.
Proof.
  have -> : ecov_app = [set e  | ∃ e1 e2, e = AppC e1 e2].
  { apply /predeqP =>y //=; rewrite /ecov_app//=; split.
    - by move=> [[??]?]<-; eexists _; eexists _.
    - by move=> [a[b->]]; eexists (a, b). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  rewrite /ecov_app/setI/=.
  eapply (eq_measurable
            (\bigcup_n [set x | (∃ e1 e2 : expr_pre, x = AppC e1 e2 /\
                                           (expr_ST (gen_expr (expr_shape_enum n)) e2)) ∧
                                expr_ST C (𝜋_App_l x)])); last first.
  { apply /predeqP =>y /=.
    split.
    - move=> [[? [z ->]] +]; simpl; move=> ?.
      destruct (expr_shape_enum_surj (shape_expr z)).
      eexists _; [done|].
      split; [|done].
      eexists _; eexists _; split; [done|].
      by rewrite -expr_shape_cyl.
    - move=> [? _ [[? [? [-> ?]]] +]]; simpl; move=> ?.
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> k _.
  apply sub_sigma_algebra.
  eexists (App C (gen_expr (expr_shape_enum k))).
  { split; [done|]. by apply gen_expr_generator. }

  apply /predeqP =>y /=.
  split.
  - move=> [? ? [ ? ? <-]].
    split.
    + by eexists _; eexists _; eauto.
    + by simpl.
  - move=> [[? [? [-> ?]]] +]; simpl; move=> ?.
    eexists _; [done|].
    eexists _; [done|].
    done.
Qed.
Hint Resolve 𝜋_App_l_meas : measlang.
Hint Resolve 𝜋_App_l_meas : mf_fun.

Lemma 𝜋_App_r_meas         : measurable_fun ecov_app 𝜋_App_r.
Proof.
  have -> : ecov_app = [set e  | ∃ e1 e2, e = AppC e1 e2].
  { apply /predeqP =>y //=; rewrite /ecov_app//=; split.
    - by move=> [[??]?]<-; eexists _; eexists _.
    - by move=> [a[b->]]; eexists (a, b). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  rewrite /ecov_app/setI/=.
  eapply (eq_measurable
            (\bigcup_n [set x | (∃ e1 e2 : expr_pre, x = AppC e1 e2 /\
                                           (expr_ST (gen_expr (expr_shape_enum n)) e1)) ∧
                                expr_ST C (𝜋_App_r x)])); last first.
  { apply /predeqP =>y /=.
    split.
    - move=> [[z [? ->]] +]; simpl; move=> ?.
      destruct (expr_shape_enum_surj (shape_expr z)).
      eexists _; [done|].
      split; [|done].
      eexists _; eexists _; split; [done|].
      by rewrite -expr_shape_cyl.
    - move=> [? _ [[? [? [-> ?]]] +]]; simpl; move=> ?.
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> k _.
  apply sub_sigma_algebra.
  eexists (App (gen_expr (expr_shape_enum k)) C).
  { split; [|done]. by apply gen_expr_generator. }

  apply /predeqP =>y /=.
  split.
  - move=> [? ? [ ? ? <-]].
    split.
    + by eexists _; eexists _; eauto.
    + by simpl.
  - move=> [[? [? [-> ?]]] +]; simpl; move=> ?.
    eexists _; [done|].
    eexists _; [done|].
    done.
Qed.
Hint Resolve 𝜋_App_r_meas : measlang.
Hint Resolve 𝜋_App_r_meas : mf_fun.


Lemma 𝜋_UnOp_op_meas       : measurable_fun ecov_unop 𝜋_UnOp_op.
Proof.
  have -> : ecov_unop = [set e  | ∃ e1 e2, e = UnOpC e1 e2].
  { apply /predeqP =>y //=; rewrite /ecov_app//=; split.
    - by move=> [[??]?]<-; eexists _; eexists _.
    - by move=> [a[b->]]; eexists (a, b). }
  rewrite //=.
  eapply (measurability un_op_generated_by_singletons).
  move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [b ->].

  rewrite /ecov_binop.
  rewrite /preimage/=/setI//=.

  (* Simplify the projection preimage *)
  apply (eq_measurable [set x | (∃ (x0 : expr_pre), x = UnOpC b x0)]); last first.
  { apply /predeqP =>y /=.
    split.
    - move=> [[?[?->]]<-] //=.
      by eexists _.
    - move=> [? ->].
      split; [|done].
      by eexists _; eexists _.
  }

  (* Split into countable union *)
  apply (eq_measurable (\bigcup_i
                          [set (UnOpC b b0) |
                            b0 in (expr_ST (gen_expr (expr_shape_enum i)))])); last first.
  { rewrite /bigcup//=.
    apply /predeqP =>y /=.
    split.
    - move=> [e0->].
      destruct (expr_shape_enum_surj (shape_expr e0)) as [i Hi].
      exists i; [done|].
      eexists _; [by rewrite -expr_shape_cyl //=|].
      done.
    - move=> [??][??]<-.
      by eexists _.
  }
  apply bigcup_measurable; move=> i _.
  apply sub_sigma_algebra.
  eexists (UnOp b (gen_expr (expr_shape_enum i))).
  { by apply gen_expr_generator. }
  apply /predeqP =>y //=.
Qed.
Hint Resolve 𝜋_UnOp_op_meas : measlang.
Hint Resolve 𝜋_UnOp_op_meas : mf_fun.

Lemma 𝜋_UnOp_e_meas        : measurable_fun ecov_unop 𝜋_UnOp_e.
Proof.
  have -> : ecov_unop = [set e  | ∃ e1 e2, e = UnOpC e1 e2].
  { apply /predeqP =>y //=; rewrite /ecov_app//=; split.
    - by move=> [[??]?]<-; eexists _; eexists _.
    - by move=> [a[b->]]; eexists (a, b). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  eapply (eq_measurable
            (\bigcup_i [set x | (∃ e0, x = UnOpC (un_op_enum i) e0 /\
                                           expr_ST C (𝜋_UnOp_e x))])); last first.
  { apply /predeqP =>y /=.
    split.
    - rewrite /ecov_unop//=.
      move=> [[op[e->]]+]; rewrite //=; move=> ?.
      rewrite /bigcup//=.
      destruct (un_op_enum_surj op) as [i <-].
      eexists i; [done|].
      eexists e.
      split; [|done].
      by f_equal.
    - rewrite /bigcup//=.
      move=> [i?][e[-> +]]; rewrite //=; move=>?.
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> i _.
  apply sub_sigma_algebra.
  eexists (UnOp (un_op_enum i) C).
  { by simpl. }

  apply /predeqP =>y /=.
  split.
  - move=> [e?]<-.
    eexists e; simpl.
    split; [|by simpl].
    by f_equal.
  - move=> [?[->?]].
    eexists _; [done|].
    by f_equal.
Qed.
Hint Resolve 𝜋_UnOp_e_meas : measlang.
Hint Resolve 𝜋_UnOp_e_meas : mf_fun.

Lemma 𝜋_BinOp_op_meas      : measurable_fun ecov_binop 𝜋_BinOp_op.
Proof.
  have -> : ecov_binop =  [set e  | ∃ f x b, e = BinOpC f x b].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
  rewrite //=.
  eapply (measurability bin_op_generated_by_singletons).
  move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [b ->].

  rewrite /ecov_binop.
  rewrite /preimage/=/setI//=.

  (* Simplify the projection preimage *)
  apply (eq_measurable [set x | (∃ (x0 b0 : expr_pre), x = BinOpC b x0 b0)]); last first.
  { apply /predeqP =>y /=.
    split.
    - move=> [[?[?[?->]]]<-] //=.
      by eexists _; eexists _.
    - move=> [? [? ->]].
      split; [|done].
      by eexists _; eexists _; eexists _.
  }

  (* Split into countable union *)
  apply (eq_measurable (\bigcup_i \bigcup_j
                          [set (BinOpC b b0 b1) |
                            b0 in (expr_ST (gen_expr (expr_shape_enum i))) &
                                     b1 in (expr_ST (gen_expr (expr_shape_enum j)) )])); last first.
  { rewrite /bigcup//=.
    apply /predeqP =>y /=.
    split.
    - move=> [e0[e1->]].
      destruct (expr_shape_enum_surj (shape_expr e0)) as [i Hi].
      destruct (expr_shape_enum_surj (shape_expr e1)) as [j Hj].
      exists i; [done|].
      exists j; [done|].
      eexists _; [by rewrite -expr_shape_cyl //=|].
      eexists _; [by rewrite -expr_shape_cyl //=|].
      done.
    - move=> [??][??][??][??]<-.
      by eexists _; eexists _.
  }
  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (BinOp b (gen_expr (expr_shape_enum i)) (gen_expr (expr_shape_enum j))).
  { split; by apply gen_expr_generator. }
  apply /predeqP =>y //=.
Qed.
Hint Resolve 𝜋_BinOp_op_meas : measlang.
Hint Resolve 𝜋_BinOp_op_meas : mf_fun.

Lemma 𝜋_BinOp_l_meas       : measurable_fun ecov_binop 𝜋_BinOp_l.
Proof.
  have -> : ecov_binop =  [set e  | ∃ f x b, e = BinOpC f x b].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  eapply (eq_measurable
            (\bigcup_i \bigcup_j [set x | (∃ e0 e2, x = BinOpC (bin_op_enum i) e0 e2 /\
                                                    (expr_ST (gen_expr (expr_shape_enum j)) e2) /\
                                                    (expr_ST C (𝜋_BinOp_l x)))])); last first.
  { apply /predeqP =>y /=.
    split.
    - rewrite /ecov_binop//=.
      move=> [[op[e1[e2->]]]+]; rewrite //=; move=> ?.
      rewrite /bigcup//=.
      destruct (bin_op_enum_surj op) as [i <-].
      destruct (expr_shape_enum_surj (shape_expr e2)) as [j Hj].
      eexists i; [done|].
      eexists j; [done|].
      eexists _.
      eexists _.
      split; [done|].
      split; [|done].
      by rewrite Hj -expr_shape_cyl //=.
    - rewrite /bigcup//=.
      move=> [i?][j?][e1][e2][-> +]. rewrite //=. move=>[??].
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (BinOp (bin_op_enum i) C (gen_expr (expr_shape_enum j))).
  { simpl; split; [done|]. by apply gen_expr_generator. }

  apply /predeqP =>y /=.
  split.
  - move=> [a?][b?]<-.
    eexists _; eexists b.
    split; [done|].
    split; [done|].
    by simpl.
  - move=> [? [? [-> [??]]]].
    eexists _; [done|].
    eexists _; [done|].
    by f_equal.
Qed.
Hint Resolve 𝜋_BinOp_l_meas : measlang.
Hint Resolve 𝜋_BinOp_l_meas : mf_fun.


Lemma 𝜋_BinOp_r_meas       : measurable_fun ecov_binop 𝜋_BinOp_r.
Proof.
  have -> : ecov_binop =  [set e  | ∃ f x b, e = BinOpC f x b].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  eapply (eq_measurable
            (\bigcup_i \bigcup_j [set x | (∃ e0 e2, x = BinOpC (bin_op_enum i) e0 e2 /\
                                                    (expr_ST (gen_expr (expr_shape_enum j)) e0) /\
                                                    (expr_ST C (𝜋_BinOp_r x)))])); last first.
  { apply /predeqP =>y /=.
    split.
    - rewrite /ecov_binop//=.
      move=> [[op[e1[e2->]]]+]; rewrite //=; move=> ?.
      rewrite /bigcup//=.
      destruct (bin_op_enum_surj op) as [i <-].
      destruct (expr_shape_enum_surj (shape_expr e1)) as [j Hj].
      eexists i; [done|].
      eexists j; [done|].
      eexists _.
      eexists _.
      split; [done|].
      split; [|done].
      by rewrite Hj -expr_shape_cyl //=.
    - rewrite /bigcup//=.
      move=> [i?][j?][e1][e2][-> +]. rewrite //=. move=>[??].
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (BinOp (bin_op_enum i) (gen_expr (expr_shape_enum j)) C).
  { simpl; split; [|done]. by apply gen_expr_generator. }

  apply /predeqP =>y /=.
  split.
  - move=> [a?][b?]<-.
    eexists _; eexists b.
    split; [done|].
    split; [done|].
    by simpl.
  - move=> [? [? [-> [??]]]].
    eexists _; [done|].
    eexists _; [done|].
    by f_equal.
Qed.
Hint Resolve 𝜋_BinOp_r_meas : measlang.
Hint Resolve 𝜋_BinOp_r_meas : mf_fun.

Lemma 𝜋_If_c_meas          : measurable_fun ecov_if 𝜋_If_c.
Proof.
  have -> : ecov_if =  [set e  | ∃ f x b, e = IfC f x b].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  rewrite /ecov_if/setI/=.
  eapply (eq_measurable
            (\bigcup_i \bigcup_j
               [set x | (∃ e1 e2 e3 : expr_pre,
                                    x = IfC e1 e2 e3 /\
                                    (expr_ST (gen_expr (expr_shape_enum i)) e2) ∧
                                    (expr_ST (gen_expr (expr_shape_enum j)) e3) ∧
                                    expr_ST C (𝜋_If_c x))])); last first.
  { apply /predeqP =>y /=.
    split.
    - move=>//=[+ Hm].
      move=>[e1][e2][e3]Hy.
      rewrite Hy//= in Hm; rewrite Hy.
      destruct (expr_shape_enum_surj (shape_expr e2)) as [i Hi].
      destruct (expr_shape_enum_surj (shape_expr e3)) as [j Hj].
      rewrite /bigcup//=.
      eexists i; [done|].
      eexists j; [done|].
      eexists _; eexists _; eexists _; split; [done|].
      by rewrite Hi Hj -expr_shape_cyl -expr_shape_cyl //=.
    - rewrite /bigcup//=.
      move=> [i?][j?][e1[e2[e3[->[?[??]]]]]].
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (If C (gen_expr (expr_shape_enum i)) (gen_expr (expr_shape_enum j))).
  { split; last split.
    - done.
    - by apply gen_expr_generator.
    - by apply gen_expr_generator.
  }

  apply /predeqP =>y /=.
  split; rewrite /image3//=.
  - move=> [x?][w?][z?]<-.
    eexists x; eexists w; eexists z.
    split; [done|].
    split; [done|].
    split; [done|].
    by rewrite //=.
  - move=> [?[?[?[->[?[??]]]]]] //=.
    eexists _; [done|].
    eexists _; [done|].
    eexists _; [done|].
    by rewrite //=.
Qed.
Hint Resolve 𝜋_If_c_meas : measlang.
Hint Resolve 𝜋_If_c_meas : mf_fun.

Lemma 𝜋_If_l_meas          : measurable_fun ecov_if 𝜋_If_l.
Proof.
  have -> : ecov_if =  [set e  | ∃ f x b, e = IfC f x b].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  rewrite /ecov_if/setI/=.
  eapply (eq_measurable
            (\bigcup_i \bigcup_j
               [set x | (∃ e1 e2 e3 : expr_pre,
                                    x = IfC e1 e2 e3 /\
                                    (expr_ST (gen_expr (expr_shape_enum i)) e1) ∧
                                    (expr_ST (gen_expr (expr_shape_enum j)) e3) ∧
                                    expr_ST C (𝜋_If_l x))])); last first.
  { apply /predeqP =>y /=.
    split.
    - move=>//=[+ Hm].
      move=>[e1][e2][e3]Hy.
      rewrite Hy//= in Hm; rewrite Hy.
      destruct (expr_shape_enum_surj (shape_expr e1)) as [i Hi].
      destruct (expr_shape_enum_surj (shape_expr e3)) as [j Hj].
      rewrite /bigcup//=.
      eexists i; [done|].
      eexists j; [done|].
      eexists _; eexists _; eexists _; split; [done|].
      by rewrite Hi Hj -expr_shape_cyl -expr_shape_cyl //=.
    - rewrite /bigcup//=.
      move=> [i?][j?][e1[e2[e3[->[?[??]]]]]].
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (If (gen_expr (expr_shape_enum i)) C (gen_expr (expr_shape_enum j))).
  { split; last split.
    - by apply gen_expr_generator.
    - done.
    - by apply gen_expr_generator.
  }

  apply /predeqP =>y /=.
  split; rewrite /image3//=.
  - move=> [x?][w?][z?]<-.
    eexists x; eexists w; eexists z.
    split; [done|].
    split; [done|].
    split; [done|].
    by rewrite //=.
  - move=> [?[?[?[->[?[??]]]]]] //=.
    eexists _; [done|].
    eexists _; [done|].
    eexists _; [done|].
    by rewrite //=.
Qed.
Hint Resolve 𝜋_If_l_meas : measlang.
Hint Resolve 𝜋_If_l_meas : mf_fun.

Lemma 𝜋_If_r_meas          : measurable_fun ecov_if 𝜋_If_r.
Proof.
  have -> : ecov_if =  [set e  | ∃ f x b, e = IfC f x b].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  rewrite /ecov_if/setI/=.
  eapply (eq_measurable
            (\bigcup_i \bigcup_j
               [set x | (∃ e1 e2 e3 : expr_pre,
                                    x = IfC e1 e2 e3 /\
                                    (expr_ST (gen_expr (expr_shape_enum i)) e1) ∧
                                    (expr_ST (gen_expr (expr_shape_enum j)) e2) ∧
                                    expr_ST C (𝜋_If_r x))])); last first.
  { apply /predeqP =>y /=.
    split.
    - move=>//=[+ Hm].
      move=>[e1][e2][e3]Hy.
      rewrite Hy//= in Hm; rewrite Hy.
      destruct (expr_shape_enum_surj (shape_expr e1)) as [i Hi].
      destruct (expr_shape_enum_surj (shape_expr e2)) as [j Hj].
      rewrite /bigcup//=.
      eexists i; [done|].
      eexists j; [done|].
      eexists _; eexists _; eexists _; split; [done|].
      by rewrite Hi Hj -expr_shape_cyl -expr_shape_cyl //=.
    - rewrite /bigcup//=.
      move=> [i?][j?][e1[e2[e3[->[?[??]]]]]].
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (If (gen_expr (expr_shape_enum i)) (gen_expr (expr_shape_enum j)) C).
  { split; last split.
    - by apply gen_expr_generator.
    - by apply gen_expr_generator.
    - done.
  }

  apply /predeqP =>y /=.
  split; rewrite /image3//=.
  - move=> [x?][w?][z?]<-.
    eexists x; eexists w; eexists z.
    split; [done|].
    split; [done|].
    split; [done|].
    by rewrite //=.
  - move=> [?[?[?[->[?[??]]]]]] //=.
    eexists _; [done|].
    eexists _; [done|].
    eexists _; [done|].
    by rewrite //=.
Qed.
Hint Resolve 𝜋_If_r_meas : measlang.
Hint Resolve 𝜋_If_r_meas : mf_fun.

Lemma 𝜋_Pair_l_meas        : measurable_fun ecov_pair 𝜋_Pair_l.
Proof.
  have -> : ecov_pair = [set e  | ∃ e1 e2, e = PairC e1 e2].
  { apply /predeqP =>y //=; rewrite /ecov_app//=; split.
    - by move=> [[??]?]<-; eexists _; eexists _.
    - by move=> [a[b->]]; eexists (a, b). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  rewrite /ecov_pair/setI/=.
  eapply (eq_measurable
            (\bigcup_n [set x | (∃ e1 e2 : expr_pre, x = PairC e1 e2 /\
                                           (expr_ST (gen_expr (expr_shape_enum n)) e2)) ∧
                                expr_ST C (𝜋_Pair_l x)])); last first.
  { apply /predeqP =>y /=.
    split.
    - move=> [[? [z ->]] +]; simpl; move=> ?.
      destruct (expr_shape_enum_surj (shape_expr z)).
      eexists _; [done|].
      split; [|done].
      eexists _; eexists _; split; [done|].
      by rewrite -expr_shape_cyl.
    - move=> [? _ [[? [? [-> ?]]] +]]; simpl; move=> ?.
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> k _.
  apply sub_sigma_algebra.
  eexists (Pair C (gen_expr (expr_shape_enum k))).
  { split; [done|]. by apply gen_expr_generator. }

  apply /predeqP =>y /=.
  split.
  - move=> [? ? [ ? ? <-]].
    split.
    + by eexists _; eexists _; eauto.
    + by simpl.
  - move=> [[? [? [-> ?]]] +]; simpl; move=> ?.
    eexists _; [done|].
    eexists _; [done|].
    done.
Qed.
Hint Resolve 𝜋_Pair_l_meas : measlang.
Hint Resolve 𝜋_Pair_l_meas : mf_fun.

Lemma 𝜋_Pair_r_meas        : measurable_fun ecov_pair 𝜋_Pair_r.
Proof.
  have -> : ecov_pair = [set e  | ∃ e1 e2, e = PairC e1 e2].
  { apply /predeqP =>y //=; rewrite /ecov_app//=; split.
    - by move=> [[??]?]<-; eexists _; eexists _.
    - by move=> [a[b->]]; eexists (a, b). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  rewrite /ecov_pair/setI/=.
  eapply (eq_measurable
            (\bigcup_n [set x | (∃ e1 e2 : expr_pre, x = PairC e1 e2 /\
                                           (expr_ST (gen_expr (expr_shape_enum n)) e1)) ∧
                                expr_ST C (𝜋_Pair_r x)])); last first.
  { apply /predeqP =>y /=.
    split.
    - move=> [[z [? ->]] +]; simpl; move=> ?.
      destruct (expr_shape_enum_surj (shape_expr z)).
      eexists _; [done|].
      split; [|done].
      eexists _; eexists _; split; [done|].
      by rewrite -expr_shape_cyl.
    - move=> [? _ [[? [? [-> ?]]] +]]; simpl; move=> ?.
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> k _.
  apply sub_sigma_algebra.
  eexists (Pair (gen_expr (expr_shape_enum k)) C).
  { split; [|done]. by apply gen_expr_generator. }

  apply /predeqP =>y /=.
  split.
  - move=> [? ? [ ? ? <-]].
    split.
    + by eexists _; eexists _; eauto.
    + by simpl.
  - move=> [[? [? [-> ?]]] +]; simpl; move=> ?.
    eexists _; [done|].
    eexists _; [done|].
    done.
Qed.
Hint Resolve 𝜋_Pair_r_meas : measlang.
Hint Resolve 𝜋_Pair_r_meas : mf_fun.

Lemma 𝜋_Fst_e_meas         : measurable_fun ecov_fst 𝜋_Fst_e.
Proof.
  have -> : ecov_fst = [set e  | ∃ v, e = FstC v].
  { apply /predeqP =>y //=; rewrite /ecov_val//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].

  apply sub_sigma_algebra.
  eexists (Fst C). { simpl. assumption. }

  apply /predeqP =>y /=.
  split.
  - move=> [? z <-].
    rewrite //=.
    split; [by eexists _|done].
  - move=> [[z ->]] //=; move=> ?.
    exists z; [done|done].
Qed.
Hint Resolve 𝜋_Fst_e_meas : measlang.
Hint Resolve 𝜋_Fst_e_meas : mf_fun.

Lemma 𝜋_Snd_e_meas         : measurable_fun ecov_snd 𝜋_Snd_e.
Proof.
  have -> : ecov_snd = [set e  | ∃ v, e = SndC v].
  { apply /predeqP =>y //=; rewrite /ecov_val//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].

  apply sub_sigma_algebra.
  eexists (Snd C). { simpl. assumption. }

  apply /predeqP =>y /=.
  split.
  - move=> [? z <-].
    rewrite //=.
    split; [by eexists _|done].
  - move=> [[z ->]] //=; move=> ?.
    exists z; [done|done].
Qed.
Hint Resolve 𝜋_Snd_e_meas : measlang.
Hint Resolve 𝜋_Snd_e_meas : mf_fun.

Lemma 𝜋_InjL_e_meas        : measurable_fun ecov_injl 𝜋_InjL_e.
Proof.
  have -> : ecov_injl = [set e  | ∃ v, e = InjLC v].
  { apply /predeqP =>y //=; rewrite /ecov_val//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].

  apply sub_sigma_algebra.
  eexists (InjL C). { simpl. assumption. }

  apply /predeqP =>y /=.
  split.
  - move=> [? z <-].
    rewrite //=.
    split; [by eexists _|done].
  - move=> [[z ->]] //=; move=> ?.
    exists z; [done|done].
Qed.
Hint Resolve 𝜋_InjL_e_meas : measlang.
Hint Resolve 𝜋_InjL_e_meas : mf_fun.

Lemma 𝜋_InjR_e_meas        : measurable_fun ecov_injr 𝜋_InjR_e.
Proof.
  have -> : ecov_injr = [set e  | ∃ v, e = InjRC v].
  { apply /predeqP =>y //=; rewrite /ecov_val//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].

  apply sub_sigma_algebra.
  eexists (InjR C). { simpl. assumption. }

  apply /predeqP =>y /=.
  split.
  - move=> [? z <-].
    rewrite //=.
    split; [by eexists _|done].
  - move=> [[z ->]] //=; move=> ?.
    exists z; [done|done].
Qed.
Hint Resolve 𝜋_InjR_e_meas : measlang.
Hint Resolve 𝜋_InjR_e_meas : mf_fun.

Lemma 𝜋_Case_c_meas          : measurable_fun ecov_case 𝜋_Case_c.
Proof.
  have -> : ecov_case =  [set e  | ∃ f x b, e = CaseC f x b].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  rewrite /ecov_case/setI/=.
  eapply (eq_measurable
            (\bigcup_i \bigcup_j
               [set x | (∃ e1 e2 e3 : expr_pre,
                                    x = CaseC e1 e2 e3 /\
                                    (expr_ST (gen_expr (expr_shape_enum i)) e2) ∧
                                    (expr_ST (gen_expr (expr_shape_enum j)) e3) ∧
                                    expr_ST C (𝜋_Case_c x))])); last first.
  { apply /predeqP =>y /=.
    split.
    - move=>//=[+ Hm].
      move=>[e1][e2][e3]Hy.
      rewrite Hy//= in Hm; rewrite Hy.
      destruct (expr_shape_enum_surj (shape_expr e2)) as [i Hi].
      destruct (expr_shape_enum_surj (shape_expr e3)) as [j Hj].
      rewrite /bigcup//=.
      eexists i; [done|].
      eexists j; [done|].
      eexists _; eexists _; eexists _; split; [done|].
      by rewrite Hi Hj -expr_shape_cyl -expr_shape_cyl //=.
    - rewrite /bigcup//=.
      move=> [i?][j?][e1[e2[e3[->[?[??]]]]]].
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (Case C (gen_expr (expr_shape_enum i)) (gen_expr (expr_shape_enum j))).
  { split; last split.
    - done.
    - by apply gen_expr_generator.
    - by apply gen_expr_generator.
  }

  apply /predeqP =>y /=.
  split; rewrite /image3//=.
  - move=> [x?][w?][z?]<-.
    eexists x; eexists w; eexists z.
    split; [done|].
    split; [done|].
    split; [done|].
    by rewrite //=.
  - move=> [?[?[?[->[?[??]]]]]] //=.
    eexists _; [done|].
    eexists _; [done|].
    eexists _; [done|].
    by rewrite //=.
Qed.
Hint Resolve 𝜋_Case_c_meas : measlang.
Hint Resolve 𝜋_Case_c_meas : mf_fun.

Lemma 𝜋_Case_l_meas          : measurable_fun ecov_case 𝜋_Case_l.
Proof.
  have -> : ecov_case =  [set e  | ∃ f x b, e = CaseC f x b].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  rewrite /ecov_if/setI/=.
  eapply (eq_measurable
            (\bigcup_i \bigcup_j
               [set x | (∃ e1 e2 e3 : expr_pre,
                                    x = CaseC e1 e2 e3 /\
                                    (expr_ST (gen_expr (expr_shape_enum i)) e1) ∧
                                    (expr_ST (gen_expr (expr_shape_enum j)) e3) ∧
                                    expr_ST C (𝜋_Case_l x))])); last first.
  { apply /predeqP =>y /=.
    split.
    - move=>//=[+ Hm].
      move=>[e1][e2][e3]Hy.
      rewrite Hy//= in Hm; rewrite Hy.
      destruct (expr_shape_enum_surj (shape_expr e1)) as [i Hi].
      destruct (expr_shape_enum_surj (shape_expr e3)) as [j Hj].
      rewrite /bigcup//=.
      eexists i; [done|].
      eexists j; [done|].
      eexists _; eexists _; eexists _; split; [done|].
      by rewrite Hi Hj -expr_shape_cyl -expr_shape_cyl //=.
    - rewrite /bigcup//=.
      move=> [i?][j?][e1[e2[e3[->[?[??]]]]]].
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (Case (gen_expr (expr_shape_enum i)) C (gen_expr (expr_shape_enum j))).
  { split; last split.
    - by apply gen_expr_generator.
    - done.
    - by apply gen_expr_generator.
  }

  apply /predeqP =>y /=.
  split; rewrite /image3//=.
  - move=> [x?][w?][z?]<-.
    eexists x; eexists w; eexists z.
    split; [done|].
    split; [done|].
    split; [done|].
    by rewrite //=.
  - move=> [?[?[?[->[?[??]]]]]] //=.
    eexists _; [done|].
    eexists _; [done|].
    eexists _; [done|].
    by rewrite //=.
Qed.
Hint Resolve 𝜋_Case_l_meas : measlang.
Hint Resolve 𝜋_Case_l_meas : mf_fun.

Lemma 𝜋_Case_r_meas          : measurable_fun ecov_case 𝜋_Case_r.
Proof.
  have -> : ecov_case =  [set e  | ∃ f x b, e = CaseC f x b].
  { apply /predeqP =>y //=; rewrite /ecov_rec//=; split.
    - by move=> [[[??]?]?]<-; eexists _; eexists _; eexists _.
    - by move=> [a[b[c->]]]; eexists (a, b, c). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  rewrite /ecov_case/setI/=.
  eapply (eq_measurable
            (\bigcup_i \bigcup_j
               [set x | (∃ e1 e2 e3 : expr_pre,
                                    x = CaseC e1 e2 e3 /\
                                    (expr_ST (gen_expr (expr_shape_enum i)) e1) ∧
                                    (expr_ST (gen_expr (expr_shape_enum j)) e2) ∧
                                    expr_ST C (𝜋_Case_r x))])); last first.
  { apply /predeqP =>y /=.
    split.
    - move=>//=[+ Hm].
      move=>[e1][e2][e3]Hy.
      rewrite Hy//= in Hm; rewrite Hy.
      destruct (expr_shape_enum_surj (shape_expr e1)) as [i Hi].
      destruct (expr_shape_enum_surj (shape_expr e2)) as [j Hj].
      rewrite /bigcup//=.
      eexists i; [done|].
      eexists j; [done|].
      eexists _; eexists _; eexists _; split; [done|].
      by rewrite Hi Hj -expr_shape_cyl -expr_shape_cyl //=.
    - rewrite /bigcup//=.
      move=> [i?][j?][e1[e2[e3[->[?[??]]]]]].
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> i _.
  apply bigcup_measurable; move=> j _.
  apply sub_sigma_algebra.
  eexists (Case (gen_expr (expr_shape_enum i)) (gen_expr (expr_shape_enum j)) C).
  { split; last split.
    - by apply gen_expr_generator.
    - by apply gen_expr_generator.
    - done.
  }

  apply /predeqP =>y /=.
  split; rewrite /image3//=.
  - move=> [x?][w?][z?]<-.
    eexists x; eexists w; eexists z.
    split; [done|].
    split; [done|].
    split; [done|].
    by rewrite //=.
  - move=> [?[?[?[->[?[??]]]]]] //=.
    eexists _; [done|].
    eexists _; [done|].
    eexists _; [done|].
    by rewrite //=.
Qed.
Hint Resolve 𝜋_Case_r_meas : measlang.
Hint Resolve 𝜋_Case_r_meas : mf_fun.

Lemma 𝜋_Alloc_e_meas      : measurable_fun ecov_alloc 𝜋_Alloc_e.
Proof.
  have -> : ecov_alloc = [set e  | ∃ x, e = AllocU x].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  apply sub_sigma_algebra.
  eexists (Alloc C). { simpl. assumption. }
  apply /predeqP =>y /=.
  split.
  - move=> [? z <-].
    rewrite //=.
    split; [by eexists _|done].
  - move=> [[z ->]] //=; move=> ?.
    exists z; [done|done].
Qed.
Hint Resolve 𝜋_Alloc_e_meas : measlang.
Hint Resolve 𝜋_Alloc_e_meas : mf_fun.

Lemma 𝜋_Load_e_meas        : measurable_fun ecov_load 𝜋_Load_e.
Proof.
  have -> : ecov_load = [set e  | ∃ x, e = LoadU x].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].

  apply sub_sigma_algebra.
  eexists (Load C). { simpl. assumption. }

  apply /predeqP =>y /=.
  split.
  - move=> [? z <-].
    rewrite //=.
    split; [by eexists _|done].
  - move=> [[z ->]] //=; move=> ?.
    exists z; [done|done].
Qed.
Hint Resolve 𝜋_Load_e_meas : measlang.
Hint Resolve 𝜋_Load_e_meas : mf_fun.

Lemma 𝜋_Store_l_meas       : measurable_fun ecov_store 𝜋_Store_l.
Proof.
  have -> : ecov_store = [set e  | ∃ e1 e2, e = StoreC e1 e2].
  { apply /predeqP =>y //=; rewrite /ecov_app//=; split.
    - by move=> [[??]?]<-; eexists _; eexists _.
    - by move=> [a[b->]]; eexists (a, b). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  rewrite /ecov_store/setI/=.
  eapply (eq_measurable
            (\bigcup_n [set x | (∃ e1 e2 : expr_pre, x = StoreC e1 e2 /\
                                           (expr_ST (gen_expr (expr_shape_enum n)) e2)) ∧
                                expr_ST C (𝜋_Store_l x)])); last first.
  { apply /predeqP =>y /=.
    split.
    - move=> [[? [z ->]] +]; simpl; move=> ?.
      destruct (expr_shape_enum_surj (shape_expr z)).
      eexists _; [done|].
      split; [|done].
      eexists _; eexists _; split; [done|].
      by rewrite -expr_shape_cyl.
    - move=> [? _ [[? [? [-> ?]]] +]]; simpl; move=> ?.
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> k _.
  apply sub_sigma_algebra.
  eexists (Store C (gen_expr (expr_shape_enum k))).
  { split; [done|]. by apply gen_expr_generator. }

  apply /predeqP =>y /=.
  split.
  - move=> [? ? [ ? ? <-]].
    split.
    + by eexists _; eexists _; eauto.
    + by simpl.
  - move=> [[? [? [-> ?]]] +]; simpl; move=> ?.
    eexists _; [done|].
    eexists _; [done|].
    done.
Qed.
Hint Resolve 𝜋_Store_l_meas : measlang.
Hint Resolve 𝜋_Store_l_meas : mf_fun.

Lemma 𝜋_Store_e_meas       : measurable_fun ecov_store 𝜋_Store_e.
Proof.
  have -> : ecov_store = [set e  | ∃ e1 e2, e = StoreC e1 e2].
  { apply /predeqP =>y //=; rewrite /ecov_app//=; split.
    - by move=> [[??]?]<-; eexists _; eexists _.
    - by move=> [a[b->]]; eexists (a, b). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  rewrite /ecov_store/setI/=.
  eapply (eq_measurable
            (\bigcup_n [set x | (∃ e1 e2 : expr_pre, x = StoreC e1 e2 /\
                                           (expr_ST (gen_expr (expr_shape_enum n)) e1)) ∧
                                expr_ST C (𝜋_Store_e x)])); last first.
  { apply /predeqP =>y /=.
    split.
    - move=> [[z [? ->]] +]; simpl; move=> ?.
      destruct (expr_shape_enum_surj (shape_expr z)).
      eexists _; [done|].
      split; [|done].
      eexists _; eexists _; split; [done|].
      by rewrite -expr_shape_cyl.
    - move=> [? _ [[? [? [-> ?]]] +]]; simpl; move=> ?.
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> k _.
  apply sub_sigma_algebra.
  eexists (Store (gen_expr (expr_shape_enum k)) C).
  { split; [|done]. by apply gen_expr_generator. }

  apply /predeqP =>y /=.
  split.
  - move=> [? ? [ ? ? <-]].
    split.
    + by eexists _; eexists _; eauto.
    + by simpl.
  - move=> [[? [? [-> ?]]] +]; simpl; move=> ?.
    eexists _; [done|].
    eexists _; [done|].
    done.
Qed.
Hint Resolve 𝜋_Store_e_meas : measlang.
Hint Resolve 𝜋_Store_e_meas : mf_fun.

Lemma 𝜋_AllocTape_e_meas   : measurable_fun ecov_alloctape 𝜋_AllocTape_e.
Proof.
  have -> : ecov_alloctape = [set e  | ∃ x, e = AllocTapeU x].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].

  apply sub_sigma_algebra.
  eexists (AllocTape C). { simpl. assumption. }

  apply /predeqP =>y /=.
  split.
  - move=> [? z <-].
    rewrite //=.
    split; [by eexists _|done].
  - move=> [[z ->]] //=; move=> ?.
    exists z; [done|done].
Qed.
Hint Resolve 𝜋_AllocTape_e_meas : measlang.
Hint Resolve 𝜋_AllocTape_e_meas : mf_fun.


Lemma 𝜋_Rand_t_meas        : measurable_fun ecov_rand 𝜋_Rand_t.
Proof.
  have -> : ecov_rand = [set e  | ∃ e1 e2, e = RandC e1 e2].
  { apply /predeqP =>y //=; rewrite /ecov_app//=; split.
    - by move=> [[??]?]<-; eexists _; eexists _.
    - by move=> [a[b->]]; eexists (a, b). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  rewrite /ecov_pair/setI/=.
  eapply (eq_measurable
            (\bigcup_n [set x | (∃ e1 e2 : expr_pre, x = RandC e1 e2 /\
                                           (expr_ST (gen_expr (expr_shape_enum n)) e2)) ∧
                                expr_ST C (𝜋_Rand_t x)])); last first.
  { apply /predeqP =>y /=.
    split.
    - move=> [[? [z ->]] +]; simpl; move=> ?.
      destruct (expr_shape_enum_surj (shape_expr z)).
      eexists _; [done|].
      split; [|done].
      eexists _; eexists _; split; [done|].
      by rewrite -expr_shape_cyl.
    - move=> [? _ [[? [? [-> ?]]] +]]; simpl; move=> ?.
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> k _.
  apply sub_sigma_algebra.
  eexists (Rand C (gen_expr (expr_shape_enum k))).
  { split; [done|]. by apply gen_expr_generator. }

  apply /predeqP =>y /=.
  split.
  - move=> [? ? [ ? ? <-]].
    split.
    + by eexists _; eexists _; eauto.
    + by simpl.
  - move=> [[? [? [-> ?]]] +]; simpl; move=> ?.
    eexists _; [done|].
    eexists _; [done|].
    done.
Qed.
Hint Resolve 𝜋_Rand_t_meas : measlang.
Hint Resolve 𝜋_Rand_t_meas : mf_fun.


Lemma 𝜋_Rand_N_meas        : measurable_fun ecov_rand 𝜋_Rand_N.
Proof.
  have -> : ecov_rand = [set e  | ∃ e1 e2, e = RandC e1 e2].
  { apply /predeqP =>y //=; rewrite /ecov_app//=; split.
    - by move=> [[??]?]<-; eexists _; eexists _.
    - by move=> [a[b->]]; eexists (a, b). }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].
  rewrite /ecov_pair/setI/=.
  eapply (eq_measurable
            (\bigcup_n [set x | (∃ e1 e2 : expr_pre, x = RandC e1 e2 /\
                                           (expr_ST (gen_expr (expr_shape_enum n)) e1)) ∧
                                expr_ST C (𝜋_Rand_N x)])); last first.
  { apply /predeqP =>y /=.
    split.
    - move=> [[z [? ->]] +]; simpl; move=> ?.
      destruct (expr_shape_enum_surj (shape_expr z)).
      eexists _; [done|].
      split; [|done].
      eexists _; eexists _; split; [done|].
      by rewrite -expr_shape_cyl.
    - move=> [? _ [[? [? [-> ?]]] +]]; simpl; move=> ?.
      split; [|done].
      by eexists _; eexists _; eauto.
  }

  apply bigcup_measurable; move=> k _.
  apply sub_sigma_algebra.
  eexists (Rand (gen_expr (expr_shape_enum k)) C).
  { split; [|done]. by apply gen_expr_generator. }

  apply /predeqP =>y /=.
  split.
  - move=> [? ? [ ? ? <-]].
    split.
    + by eexists _; eexists _; eauto.
    + by simpl.
  - move=> [[? [? [-> ?]]] +]; simpl; move=> ?.
    eexists _; [done|].
    eexists _; [done|].
    done.
Qed.
Hint Resolve 𝜋_Rand_N_meas : measlang.
Hint Resolve 𝜋_Rand_N_meas : mf_fun.

Lemma 𝜋_URand_e_meas       : measurable_fun ecov_urand 𝜋_URand_e.
Proof.
  have -> : ecov_urand = [set e  | ∃ x, e = URand x].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].

  apply sub_sigma_algebra.
  eexists (URand C). { simpl. assumption. }

  apply /predeqP =>y /=.
  split.
  - move=> [? z <-].
    rewrite //=.
    split; [by eexists _|done].
  - move=> [[z ->]] //=; move=> ?.
    exists z; [done|done].
Qed.
Hint Resolve 𝜋_URand_e_meas : measlang.
Hint Resolve 𝜋_URand_e_meas : mf_fun.

Lemma 𝜋_Tick_e_meas        : measurable_fun ecov_tick 𝜋_Tick_e.
Proof.
  have -> : ecov_tick = [set e  | ∃ x, e = TickU x].
  { apply /predeqP =>y //=; rewrite /ecov_var//=; split.
    - move=> [??]<-; by eexists _.
    - move=> [?->]; by eexists _. }
  into_gen_measurable; move=> S.
  rewrite /preimage_class -bigcup_imset1 /bigcup/=.
  move=> [SB + ->].
  move=> [C ? <-].

  apply sub_sigma_algebra.
  eexists (Tick C). { simpl. assumption. }

  apply /predeqP =>y /=.
  split.
  - move=> [? z <-].
    rewrite //=.
    split; [by eexists _|done].
  - move=> [[z ->]] //=; move=> ?.
    exists z; [done|done].
Qed.
Hint Resolve 𝜋_Tick_e_meas : measlang.
Hint Resolve 𝜋_Tick_e_meas : mf_fun.





(**  Uncurried projection functions are measurable *)

(* NOTE (e)apply gets stuck when I don't specialze these lemmas *)

Definition measurable_fun_prod'_expr :=
  (fun {d1 d2 : measure_display} => (@measurable_fun_prod' _ d1 d2 expr)).
Definition measurable_fun_prod'_val  :=
  (fun {d1 d2 : measure_display} => (@measurable_fun_prod' _ d1 d2 val)).
Definition measurable_fun_prod'_base_lit  :=
  (fun {d1 d2 : measure_display} => (@measurable_fun_prod' _ d1 d2 val)).

Ltac solve_packaged_meas :=
  repeat
    (try (apply measurable_fun_prod'_expr; try (by eauto with measlang));
     try (apply measurable_fun_prod'_val;  try (by eauto with measlang));
     try (apply measurable_fun_prod'_base_lit;  try (by eauto with measlang));
     try (by eauto with measlang)).


Definition 𝜋_LitIntU_meas : measurable_fun bcov_LitInt 𝜋_LitIntU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_LitIntU_meas : measlang.
Hint Resolve 𝜋_LitIntU_meas : mf_fun.

Definition 𝜋_LitBoolU_meas : measurable_fun bcov_LitBool 𝜋_LitBoolU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_LitBoolU_meas : measlang.
Hint Resolve 𝜋_LitBoolU_meas : mf_fun.

Definition 𝜋_LitLocU_meas : measurable_fun bcov_LitLoc 𝜋_LitLocU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_LitLocU_meas : measlang.
Hint Resolve 𝜋_LitLocU_meas : mf_fun.

Definition 𝜋_LitLblU_meas : measurable_fun bcov_LitLbl 𝜋_LitLblU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_LitLblU_meas : measlang.
Hint Resolve 𝜋_LitLblU_meas : mf_fun.

Definition 𝜋_LitRealU_meas : measurable_fun bcov_LitReal 𝜋_LitRealU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_LitRealU_meas : measlang.
Hint Resolve 𝜋_LitRealU_meas : mf_fun.

Definition 𝜋_LitVU_meas : measurable_fun vcov_lit 𝜋_LitVU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_LitVU_meas : measlang.
Hint Resolve 𝜋_LitVU_meas : mf_fun.

Definition 𝜋_RecVU_meas : measurable_fun vcov_rec 𝜋_RecVU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_RecVU_meas : measlang.
Hint Resolve 𝜋_RecVU_meas : mf_fun.

Definition 𝜋_PairVU_meas : measurable_fun vcov_pair 𝜋_PairVU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_PairVU_meas : measlang.
Hint Resolve 𝜋_PairVU_meas : mf_fun.

Definition 𝜋_InjLVU_meas : measurable_fun vcov_injlv 𝜋_InjLVU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_InjLVU_meas : measlang.
Hint Resolve 𝜋_InjLVU_meas : mf_fun.

Definition 𝜋_InjRVU_meas : measurable_fun vcov_injrv 𝜋_InjRVU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_InjRVU_meas : measlang.
Hint Resolve 𝜋_InjRVU_meas : mf_fun.

Definition 𝜋_ValU_meas : measurable_fun ecov_val 𝜋_ValU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_ValU_meas : measlang.
Hint Resolve 𝜋_ValU_meas : mf_fun.

Definition 𝜋_VarU_meas : measurable_fun ecov_var 𝜋_VarU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_VarU_meas : measlang.
Hint Resolve 𝜋_VarU_meas : mf_fun.

Definition 𝜋_RecU_meas : measurable_fun ecov_rec 𝜋_RecU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_RecU_meas : measlang.
Hint Resolve 𝜋_RecU_meas : mf_fun.

Definition 𝜋_UnOpU_meas : measurable_fun ecov_unop 𝜋_UnOpU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_UnOpU_meas : measlang.
Hint Resolve 𝜋_UnOpU_meas : mf_fun.

Definition 𝜋_BinOpU_meas : measurable_fun ecov_binop 𝜋_BinOpU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_BinOpU_meas : measlang.
Hint Resolve 𝜋_BinOpU_meas : mf_fun.

Definition 𝜋_AppU_meas : measurable_fun ecov_app 𝜋_AppU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_AppU_meas : measlang.
Hint Resolve 𝜋_AppU_meas : mf_fun.

Definition 𝜋_IfU_meas : measurable_fun ecov_if 𝜋_IfU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_IfU_meas : measlang.
Hint Resolve 𝜋_IfU_meas : mf_fun.

Definition 𝜋_PairU_meas : measurable_fun ecov_pair 𝜋_PairU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_PairU_meas : measlang.
Hint Resolve 𝜋_PairU_meas : mf_fun.

Definition 𝜋_FstU_meas : measurable_fun ecov_fst 𝜋_FstU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_FstU_meas : mf_fun.

Definition 𝜋_SndU_meas : measurable_fun ecov_snd 𝜋_SndU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_SndU_meas : mf_fun.

Definition 𝜋_InjLU_meas : measurable_fun ecov_injl 𝜋_InjLU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_InjLU_meas : measlang.
Hint Resolve 𝜋_InjLU_meas : mf_fun.

Definition 𝜋_InjRU_meas : measurable_fun ecov_injr 𝜋_InjRU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_InjRU_meas : measlang.
Hint Resolve 𝜋_InjRU_meas : mf_fun.

Definition 𝜋_CaseU_meas : measurable_fun ecov_case 𝜋_CaseU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_CaseU_meas : measlang.
Hint Resolve 𝜋_CaseU_meas : mf_fun.

Definition 𝜋_AllocU_meas : measurable_fun ecov_alloc 𝜋_AllocU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_AllocU_meas : measlang.
Hint Resolve 𝜋_AllocU_meas : mf_fun.

Definition 𝜋_LoadU_meas : measurable_fun ecov_load 𝜋_LoadU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_LoadU_meas : measlang.
Hint Resolve 𝜋_LoadU_meas : mf_fun.

Definition 𝜋_StoreU_meas : measurable_fun ecov_store 𝜋_StoreU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_StoreU_meas : measlang.
Hint Resolve 𝜋_StoreU_meas : mf_fun.

Definition 𝜋_AllocTapeU_meas : measurable_fun ecov_alloctape 𝜋_AllocTapeU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_StoreU_meas : measlang.
Hint Resolve 𝜋_StoreU_meas : mf_fun.

Definition 𝜋_RandU_meas : measurable_fun ecov_rand 𝜋_RandU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_RandU_meas : measlang.
Hint Resolve 𝜋_RandU_meas : mf_fun.

Definition 𝜋_URandU_meas : measurable_fun ecov_urand 𝜋_URandU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_URandU_meas : measlang.
Hint Resolve 𝜋_URandU_meas : mf_fun.

Definition 𝜋_Tick_meas : measurable_fun ecov_tick 𝜋_TickU.
Proof. by solve_packaged_meas. Qed.
Hint Resolve 𝜋_Tick_meas : measlang.
Hint Resolve 𝜋_Tick_meas : mf_fun.



Lemma 𝜋_LitV_v_sub S : [set 𝜋_LitV_v x | x in vcov_lit `&` 𝜋_LitV_v @^-1` S] `<=` S.
Proof.
  rewrite /subset//=.
  move=>?.
  move=>[+]; move=>?.
  move=>[+]; move=>[? _].
  move=><-//=.
  by move=>?<-//.
Qed.
Hint Resolve 𝜋_LitV_v_sub : projection_subs.

Lemma 𝜋_Pair_l_sub S1 S2 : [set 𝜋_Pair_l x | x in ecov_pair `&` 𝜋_PairU @^-1` (S1 `*` S2)] `<=` S1.
Proof.
  rewrite /preimage/ecov_pair/subset//=.
  move=> t [++].
  move=> x [++].
  move=> [[??]?<-].
  rewrite /𝜋_Pair_l/𝜋_Pair_r/=.
  by intros [??]?; simplify_eq.
Qed.
Hint Resolve 𝜋_Pair_l_sub : projection_subs.

Lemma 𝜋_Pair_r_sub S1 S2 : [set 𝜋_Pair_r x | x in ecov_pair `&` 𝜋_PairU @^-1` (S1 `*` S2)] `<=` S2.
Proof.
  rewrite /preimage/ecov_pair/subset//=.
  move=> t [++].
  move=> x [++].
  move=> [[??]?<-].
  rewrite /𝜋_Pair_l/𝜋_Pair_r/=.
  by intros [??]?; simplify_eq.
Qed.
Hint Resolve 𝜋_Pair_r_sub : projection_subs.
