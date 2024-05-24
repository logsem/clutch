From clutch.prelude Require Import base.
From clutch.prob_lang Require Import notation lang.
From clutch.ctx_logic Require Import weakestpre model.
From clutch.typing Require Import types.
From clutch Require Import clutch.

From mathcomp Require Import solvable.cyclic choice eqtype finset fintype seq
  ssrbool ssreflect zmodp.
From mathcomp Require ssralg.
Import fingroup.
Set Bullet Behavior "Strict Subproofs".

Local Open Scope group_scope.
Import fingroup.fingroup.
Local Notation "'cval'" := (prob_lang.val).

Class val_group :=
  Val_group { vgG : finGroupType
            ; vgval : vgG → cval
            ; vgval_inj : Inj eq eq vgval }.

(* Both of the below seem necessary since there is a subtle difference in the
   domain type DOM, despite the two being convertible. *)
#[warning="-uniform-inheritance"] Coercion vgval_as {vg : val_group}
  (x : FinGroup.arg_sort (FinGroup.base vgG)) : cval := vgval x.
#[warning="-uniform-inheritance"] Coercion vgval_s {vg : val_group}
  (x : FinGroup.sort (FinGroup.base vgG)) : cval := vgval x.

Class clutch_group_struct :=
  Clutch_group_struct
    { vunit : cval
    ; vinv : cval
    ; vmult : cval
    ; int_of_vg : cval
    ; vg_of_int : cval
    ; τG : type
    ; vunit_typed : val_typed vunit τG
    ; vinv_typed : val_typed vinv (τG → τG)%ty
    ; vmult_typed : val_typed vmult (τG → τG → τG)%ty
    ; int_of_vg_typed : val_typed int_of_vg (τG → TInt)%ty
    ; vg_of_int_typed : val_typed vg_of_int (TInt → () + τG)%ty
    }.

(* In some cases (Zpˣ), we might want to use exponentiation to define
   inversion, so we expose a bare version parametrised by only the unit and
   multiplication instead of the whole group structure. *)
Definition vexp' (vunit : cval) (vmult : cval) : cval := λ:"a", rec: "vexp" "n" :=
    if: "n" ≤ #0 then vunit else let: "x" := "vexp" ("n" - #1) in vmult "a" "x".

Definition vexp `{!clutch_group_struct} : cval := vexp' vunit vmult.

Definition lrel_G `{clutchRGS Σ} {vg : val_group} : lrel Σ
  := LRel (λ w1 w2, ∃ a : vgG, ⌜ w1 = a ∧ w2 = a ⌝)%I.

Class clutch_group `{clutchRGS Σ} {vg : val_group} {cg : clutch_group_struct} :=
  Clutch_group
    { int_of_vg_lrel_G : ⊢ (lrel_G → lrel_int)%lrel int_of_vg int_of_vg
    ; vg_of_int_lrel_G : ⊢ (lrel_int → (() + lrel_G))%lrel vg_of_int vg_of_int
    ; τG_subtype v1 v2 Δ : lrel_G v1 v2 ⊢ interp τG Δ v1 v2
    ; is_unit : vunit = 1
    ; is_inv (x : vgG) : ⊢ WP vinv x {{ λ (v : cval), ⌜v = x^-1⌝ }}
    ; is_spec_inv (x : vgG) K :
      ⤇ fill K (vinv x) ⊢ spec_update ⊤ (⤇ fill K (x^-1))
    ; is_mult (x y : vgG) : ⊢ WP vmult x y {{ λ (v : cval), ⌜v = (x * y)%g⌝ }}
    ; is_spec_mult (x y : vgG) K :
      ⤇ fill K (vmult x y) ⊢ spec_update ⊤ (⤇ fill K (x * y)%g)
    }.

Definition vexp_typed `{!clutch_group_struct} :
  val_typed vexp (τG → TInt → τG)%ty.
Proof. unfold vexp, vexp' ; tychk ; auto using vunit_typed, vmult_typed. Qed.

#[export] Hint Extern 0 (val_typed vunit τG) => apply vunit_typed : core.
#[export] Hint Extern 0 (val_typed vmult _) => apply vmult_typed : core.
#[export] Hint Extern 0 (val_typed vexp _) => apply vexp_typed : core.
#[export] Hint Extern 0 (val_typed int_of_vg _) => apply int_of_vg_typed : core.
#[export] Hint Extern 0 (val_typed vg_of_int _) => apply vg_of_int_typed : core.

Definition vg_of_cg := λ {Σ HΣ} vg cg (G : @clutch_group Σ HΣ vg cg), vg.
Coercion vg_of_cg : clutch_group >-> val_group.

(* vg is generated by g. We further include the assumption that vg is
   nontrivial, i.e. of size at least 2, since this allows us to work with
   mathcomp's 'Z_p type of integers modulo p (taking p := #[g]). *)
Class clutch_group_generator {vg : val_group} :=
  Clutch_group_generator
    { g : vgG
    ; n'' : nat
    ; g_nontriv : #[g] = S (S n'')
    ; g_generator : generator [set: vgG] g
    }.

Set Default Proof Using "Type*".

Section facts.

Context `{!clutchRGS Σ}.

Context {vg : val_group}.
Context {cg : clutch_group_struct}.
Context {G : clutch_group (vg:=vg) (cg:=cg)}.
Context {cgg : @clutch_group_generator vg}.

Lemma refines_inv_l E K A (a : vgG) t :
  (refines E (ectxi_language.fill K (Val (a^-1)%g)) t A)
    ⊢ refines E (ectxi_language.fill K (vinv a)) t A.
Proof.
  iIntros "H". rel_apply_l refines_wp_l.
  iApply (wp_frame_wand with "H"). iApply (wp_mono $! (is_inv a)).
  by iIntros ; subst.
Qed.

Lemma refines_inv_r E K A (a : vgG) t :
  (refines E t (ectxi_language.fill K (Val (a^-1)%g)) A)
    ⊢ refines E t (ectxi_language.fill K (vinv a)) A.
Proof.
  iIntros "H". rel_apply_r refines_steps_r => //.
  iIntros (?). iApply is_spec_inv.
Qed.

Lemma refines_mult_l E K A (a b : vgG) t :
  (refines E (ectxi_language.fill K (Val (a * b)%g)) t A)
    ⊢ refines E (ectxi_language.fill K (vmult a b)) t A.
Proof.
  iIntros "H". rel_apply_l refines_wp_l.
  iApply (wp_frame_wand with "H"). iApply (wp_mono $! (is_mult a b)).
  by iIntros ; subst.
Qed.

Lemma refines_mult_r E K A (a b : vgG) t :
  (refines E t (ectxi_language.fill K (Val (a * b)%g)) A)
    ⊢ refines E t (ectxi_language.fill K (vmult a b)) A.
Proof.
  iIntros "H". rel_apply_r refines_steps_r => //.
  iIntros (?). iApply is_spec_mult.
Qed.

Fact is_exp (b : vgG) (x : nat) :
  {{{ True }}} vexp b #x {{{ v, RET (v : cval); ⌜v = (b ^+ x)%g⌝ }}}.
Proof.
  unfold vexp, vexp'. iIntros (? _) "hlog".
  wp_pure. wp_pure.
  iInduction x as [|x] "IH" forall (Φ).
  - wp_pures.
    rewrite is_unit.
    iApply ("hlog").
    by rewrite expg0.
  - do 4 wp_pure.
    wp_bind ((rec: _ _ := _)%V _).
    replace (S x - 1)%Z with (Z.of_nat x) by lia.
    iApply "IH".
    iIntros. wp_pures.
    iApply (wp_frame_wand with "hlog"). iApply (wp_mono $! (is_mult b v)).
    iIntros (??) "hlog" ; subst. iApply "hlog".
    by rewrite expgS.
Qed.

Fact is_spec_exp (b : vgG) (x : nat) K :
  ⤇ fill K (vexp b #x) ⊢ spec_update ⊤ (⤇ fill K (b ^+ x)%g).
Proof.
  unfold vexp, vexp'. iIntros "hlog".
  tp_pure. tp_pure.
  iInduction x as [|x] "IH" forall (K).
  - tp_pures. rewrite is_unit.
    by iModIntro.  
  - do 4 tp_pure.
    tp_bind ((rec: _ _ := _)%V _).
    replace (S x - 1)%Z with (Z.of_nat x) by lia.
    iSpecialize ("IH" with "hlog").
    iMod "IH" as "IH /=".
    tp_pures.
    rewrite is_spec_mult.
    by rewrite expgS.
Qed.

Lemma refines_exp_l E K A (b : vgG) (p : nat) t :
  (refines E (ectxi_language.fill K (Val (b ^+ p)%g)) t A)
    ⊢ refines E (ectxi_language.fill K (vexp b #p)) t A.
Proof.
  iIntros "H". rel_apply_l refines_wp_l.
  iApply (is_exp b p) => //. iModIntro ; iIntros (v) "->" => //.
Qed.

Lemma refines_exp_r E K A (b : vgG) (p : nat) t :
  (refines E t (ectxi_language.fill K (Val (b ^+ p)%g)) A)
    ⊢ refines E t (ectxi_language.fill K (vexp b #p)) A.
Proof.
  iIntros "H". rel_apply_r refines_steps_r => //.
  iIntros (?). iApply (is_spec_exp b).
Qed.

Lemma log_g
  : ∀ v : vgG, ∃ k : fin (S (S n'')), (v = g^+k)%g.
Proof using.
  pose proof g_nontriv.
  pose proof g_generator.
  unfold generator in *.
  intros v ; destruct (@cyclePmin vgG g v).
  2: {
    assert (hx : x < #[g]%g) by by apply /ssrnat.leP.
    rewrite g_nontriv in hx.
    exists (nat_to_fin hx).
    symmetry. rewrite e. f_equal.
    rewrite fin_to_nat_to_fin.
    reflexivity.
  }
  assert ([set: vgG] = cycle g)%g as <-.
  2: apply in_setT.
  by destruct (@eqtype.eqP _ [set: vgG] (cycle g)).
Qed.

End facts.

(* fast tactics to simplify inversion *)
Tactic Notation "rel_inv_l" :=
  lazymatch goal with
  | |- environments.envs_entails _ (refines _ ?e _ _) =>
      match e with
      | context[App (Val vinv) (Val ?a)] =>
          rel_apply_l (refines_inv_l _ _ _ a _) => //
      | _ => fail "rel_inv_l: no vinv / group element found"
      end
  | _ => fail "rel_inv_l: not proving a refinement"
  end.

Tactic Notation "rel_inv_r" :=
  lazymatch goal with
  | |- environments.envs_entails _ (refines _ _ ?e _) =>
      match e with
      | context[App (Val vinv) (Val ?a)] =>
          rel_apply_r (refines_inv_r _ _ _ a _) => //
      | _ => fail "rel_inv_r: no vinv / group element found"
      end
  | _ => fail "rel_inv_r: not proving a refinement"
  end.

(* fast tactics to simplify multiplications *)
Tactic Notation "rel_mult_l" :=
  lazymatch goal with
  | |- environments.envs_entails _ (refines _ ?e _ _) =>
      match e with
      | context[App (App (Val vmult) (Val ?a)) (Val ?b)] =>
          rel_apply_l (refines_mult_l _ _ _ a b _) => //
      | _ => fail "rel_mult_l: no vmult / v1 / v2 found"
      end
  | _ => fail "rel_mult_l: not proving a refinement"
  end.

Tactic Notation "rel_mult_r" :=
  lazymatch goal with
  | |- environments.envs_entails _ (refines _ _ ?e _) =>
      match e with
      | context[App (App (Val vmult) (Val ?a)) (Val ?b)] =>
          rel_apply_r (refines_mult_r _ _ _ a b _) => //
      | _ => fail "rel_mult_r: no vmult / v1 / v2 found"
      end
  | _ => fail "rel_mult_r: not proving a refinement"
  end.

(* fast tactics to simplify exponentials *)
Tactic Notation "rel_exp_l" :=
  lazymatch goal with
  | |- environments.envs_entails _ (refines _ ?e _ _) =>
      match e with
      | context[App (App (Val vexp) (Val ?b)) (Val #(LitInt (Z.of_nat ?p)))] =>
          rel_apply_l (refines_exp_l _ _ _ b p _) => //
      | _ => fail "rel_exp_l: no vexp / base / exponent found"
      end
  | _ => fail "rel_exp_l: not proving a refinement"
  end.

Tactic Notation "rel_exp_r" :=
  lazymatch goal with
  | |- environments.envs_entails _ (refines _ _ ?e _) =>
      match e with
      | context[App (App (Val vexp) (Val ?b)) (Val #(LitInt (Z.of_nat ?p)))] =>
          rel_apply_r (refines_exp_r _ _ _ b p _) => //
      | _ => fail "rel_exp_r: no vexp / base / exponent found"
      end
  | _ => fail "rel_exp_r: not proving a refinement"
  end.

Module valgroup_tactics.

  Ltac rel_pures :=
    iStartProof ;
    repeat (iredpuresr ; try first [rel_exp_r | rel_mult_r | rel_inv_r]) ;
    repeat (iredpuresl ; try first [rel_exp_l | rel_mult_l | rel_inv_l]).

  (* TODO: make this into a general purpose tactic for solving log. rel.s at base
   type, and add a clause to use a hint database to which local solutions such
   as τG_subtype can be added. *)
  Ltac rel_vals' :=
    lazymatch goal with
    | |- environments.envs_entails _ (_ (InjRV _) (InjRV _)) =>
        iExists _,_ ; iRight ; iSplit ; [eauto|iSplit ; eauto]
    | |- environments.envs_entails _ (_ (InjLV _) (InjLV _)) =>
        iExists _,_ ; iLeft ; iSplit ; [eauto|iSplit ; eauto]
    | |- environments.envs_entails _ (_ (_ , _)%V (_ , _)%V) =>
        iExists _,_,_,_ ; iSplit ; [eauto|iSplit ; [eauto | iSplit]]
    | |- environments.envs_entails _ (_ (_ (interp τG) _) _ _) =>
        iApply τG_subtype ; eauto
    | _ => fail "rel_vals: case not covered"
    end.
  Ltac rel_vals := rel_values ; repeat iModIntro ; repeat (rel_vals' ; eauto).

End valgroup_tactics.

Module valgroup_notation.

  Notation "e1 · e2" := (vmult e1 e2) (at level 40) : expr_scope.
  Notation "e ^-1" := (vinv e) : expr_scope.
  Notation "e1 ^ e2" := (vexp e1 e2) : expr_scope.
  Notation "e1 ^- e2" := (e1 ^ e2)^-1%E : expr_scope.

End valgroup_notation.
