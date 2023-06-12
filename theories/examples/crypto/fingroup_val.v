From clutch.prelude Require Import base.
From clutch.program_logic Require Import weakestpre.
From clutch.prob_lang Require Import notation lang.
From clutch.rel_logic Require Import model spec_ra.
From clutch.typing Require Import types.
From clutch.examples.crypto Require Import mc_val_instances.
From clutch Require Import clutch.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import solvable.cyclic choice eqtype finset fintype seq
  ssrbool ssreflect zmodp.
From mathcomp Require ssralg.
Import fingroup.
Set Warnings "notation-overridden,ambiguous-paths".
Set Bullet Behavior "Strict Subproofs".

From deriving Require Import deriving.
From deriving Require Import instances.

Local Open Scope group_scope.
Import fingroup.fingroup.
Import prob_lang.

Section val_group.
  (* A decidable predicate on values. *)
  Variable P : {pred val}.
  (* The subtype of values satisfying P. *)
  Definition vt := sig_subType P.
  (* An enumeration of [vt]... *)
  Variable e : seq vt.
  (* ...in which every element of [vt] appears exactly once. *)
  Variable h_enum : Finite.axiom e.

  Definition vt_finMixin := FinMixin h_enum.
  Canonical vt_finType := Eval hnf in FinType vt vt_finMixin.
  (* Not sure why it doesn't find the finType instance vt_finType. *)
  (* Fail Check [finType of vt]. *)

  Canonical vt_subFinType : subFinType P :=
    Eval hnf in SubFinType (T:=val_choiceType) (subFin_sort:=vt) vt_finMixin.

  (* Now it works. Oh well. *)
  (* Check [finType of vt]. *)

  (* Check {set vt}. *)
  (* Check (@FinGroup.PackBase vt). *)
  (* Check (@FinGroup.mixin_of vt). *)
  (* Check phant (@sub_sort val (fun x : val => P x) vt). *)
  (* Check phant (FinGroup.arg_sort (FinGroup.base _)). *)
  (* Let's spell out the details of assuming we have a group structure. *)
  (* Variable vt_finGroupMixin : FinGroup.mixin_of vt. *)

  Variables (one : vt) (mul : vt -> vt -> vt) (inv : vt -> vt).

  Hypothesis mulA : ssrfun.associative mul.
  Hypothesis mul1 : ssrfun.left_id one mul.
  Hypothesis mulV : ssrfun.left_inverse one inv mul.

  Canonical vg_BaseFinGroupType := BaseFinGroupType _ (FinGroup.Mixin mulA mul1 mulV).
  Canonical vg_finGroup : finGroupType := FinGroupType mulV.

  (* Canonical vg := Eval hnf in BaseFinGroupType _ vt_finGroupMixin. *)
End val_group.

Class val_group :=
  Val_group { P : {pred val}
            ; val_group_enum : seq (vt P)
            ; val_group_finite_axiom : Finite.axiom val_group_enum
            ; vgone : vt P
            ; vgmul : vt P -> vt P -> vt P
            ; vginv : vt P -> vt P
            ; val_group_associative : ssrfun.associative vgmul
            ; val_group_left_id : ssrfun.left_id vgone vgmul
            ; val_group_left_inverse : ssrfun.left_inverse vgone vginv vgmul
    }.

Coercion mk_vg (vg : val_group) : finGroupType :=
  vg_finGroup _ _ (@val_group_finite_axiom vg) _ _ _
    (@val_group_associative vg) (@val_group_left_id vg) (@val_group_left_inverse vg).

(* While this commented-out declaration does not trigger a "nonuniform
   inheritance" warning, it unfortunately seems useless, i.e. it does not
   coerce from val_group to val. *)
(* Definition vgval := λ {vg : val_group} (x : vg), `x : val.
   Coercion vgval : val_group >-> Funclass. *)

(* Both of the below seem necessary since there is a subtle difference in the
   domain type DOM, despite DOM being to {x : val | P x} in both cases. *)
#[nonuniform] Coercion vgval_as {vg : val_group}
  (x : FinGroup.arg_sort (FinGroup.base (mk_vg vg))) : val := `x.
#[nonuniform] Coercion vgval_s {vg : val_group}
  (x : FinGroup.sort (FinGroup.base (mk_vg vg))) : val := `x.

Class clutch_group_struct :=
  Clutch_group_struct
    { vunit : val
    ; vinv : val
    ; vmult : val
    ; vexp : val
    ; τG : type
    ; vmult_typed : val_typed vmult (τG → τG → τG)%ty
    ; vexp_typed : val_typed vexp (τG → TInt → τG)%ty
    }.

(* Could push `{clutchRGS Σ} down to the Iris propositions, or move the
   syntactic typing info into the clutch_group_struct. *)
Class clutch_group `{clutchRGS Σ} {vg : val_group} {cg : clutch_group_struct} :=
  Clutch_group
    { τG_closed : forall Δ, interp.interp τG Δ = interp.interp τG []
    ; vall_typed : (∀ (x : vg), ⊢ᵥ x : τG)%ty
    ; vg_log_rel v1 v2 : (⊢ (interp.interp τG [] v1 v2) -∗ ⌜ P v1 /\ P v2 ⌝)%I
    ; is_unit : vunit = 1
    ; is_inv (x : vg) : {{{ True }}} vinv x {{{ v, RET (v : val); ⌜v = x^-1⌝ }}}
    ; is_spec_inv (x : vg) K :
      refines_right K (vinv x) ={⊤}=∗ refines_right K (x^-1)
    ; is_mult (x y : vg) : {{{ True }}} vmult x y {{{ v, RET (v : val); ⌜v = (x * y)%g⌝ }}}
    ; is_spec_mult (x y : vg) K :
      refines_right K (vmult x y) ={⊤}=∗ refines_right K (x * y)
    ; is_exp (b : vg) (x : nat) : {{{ True }}} vexp b #x {{{ v, RET (v : val); ⌜v = b ^+ x⌝ }}}
    ; is_spec_exp (b : vg) (x : nat) K :
      refines_right K (vexp b #x) ={⊤}=∗ refines_right K (b ^+ x)
    }.

#[export] Hint Extern 0 (val_typed _ τG) => apply vall_typed : core.

Definition vg_of_cg := λ {Σ HΣ} vg cg (G : @clutch_group Σ HΣ vg cg), vg.
Coercion vg_of_cg : clutch_group >-> val_group.

(* vg is generated by g. We further include the assumption that vg is
   nontrivial, i.e. of size at least 2, since this allows us to work with
   mathcomp's 'Z_p type of integers modulo p (taking p := #[g]). *)
Class clutch_group_generator {vg : val_group} :=
  Clutch_group_generator
    { g : vg
    ; n'' : nat
    ; g_nontriv : #[g] = S (S n'')
    ; g_generator : generator [set: vg] g
    }.

Set Default Proof Using "Type*".

Section facts.

Context `{!clutchRGS Σ}.

Context {vg : val_group}.
Context {cg : clutch_group_struct}.
Context {G : clutch_group (vg:=vg) (cg:=cg)}.
Context {cgg : @clutch_group_generator vg}.

#[local] Notation T := (interp.interp τG []).

Fact mult_typed : ∀ Γ, Γ ⊢ₜ vmult : (τG → τG → τG)%ty.
Proof. intros. constructor. apply vmult_typed. Qed.

Lemma refines_mult_l E K A (a b : G) t :
  (refines E (ectxi_language.fill K (Val (a * b)%g)) t A)
    ⊢ refines E (ectxi_language.fill K (vmult a b)) t A.
Proof.
  iIntros "H".
  rel_apply_l refines_wp_l.
  iApply (is_mult a b) => //.
  iModIntro ; iIntros (v) "->" => //.
Qed.

Lemma refines_exp_l E K A (b : G) (p : nat) t :
  (refines E (ectxi_language.fill K (Val (b ^+ p)%g)) t A)
    ⊢ refines E (ectxi_language.fill K (vexp b #p)) t A.
Proof.
  iIntros "H".
  rel_apply_l refines_wp_l.
  iApply (is_exp b p) => //.
  iModIntro ; iIntros (v) "->" => //.
Qed.

Lemma refines_exp_r E K A (b : G) (p : nat) t :
  (refines E t (ectxi_language.fill K (Val (b ^+ p)%g)) A)
    ⊢ refines E t (ectxi_language.fill K (vexp b #p)) A.
Proof.
  iIntros "H".
  rel_apply_r refines_steps_r => //.
  iIntros (?).
  iApply (is_spec_exp b).
Qed.

Lemma log_g
  : ∀ v : vg, ∃ k : fin (S (S n'')), (v = g^+k)%g.
Proof using.
  pose proof g_nontriv.
  pose proof g_generator.
  unfold generator in *.
  intros v ; destruct (@cyclePmin vg g v).
  2: {
    assert (hx : x < #[g]%g) by by apply /ssrnat.leP.
    rewrite g_nontriv in hx.
    exists (nat_to_fin hx).
    symmetry. rewrite e. f_equal.
    rewrite fin_to_nat_to_fin.
    reflexivity.
  }
  assert ([set: vg] = cycle g)%g as <-.
  2: apply in_setT.
  by destruct (@eqtype.eqP _ [set: vg] (cycle g)).
Qed.

End facts.

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
