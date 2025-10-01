From stdpp                         Require Import tactics.

From iris.proofmode  Require Export base tactics classes.
From iris.proofmode Require Import proofmode.
From clutch.approxis Require Import app_weakestpre.
From clutch.common Require Import language ectxi_language locations.
From clutch.base_logic Require Export spec_update.
From clutch.prob Require Export couplings_app distribution.
From iris.base_logic Require Export na_invariants ghost_map.
From clutch.prob_eff_lang          Require Import wp_tactics weakestpre shallow_handler typed_lang spec_ra
                                                  iEff spec_rules primitive_laws lang class_instances
                                                  spec_tactics.
From clutch.prob_eff_lang.named_effects Require Import labeled_effects.
Import uPred.

Set Default Proof Using "Type".


(** * Semantic Intepretation of Pure Types. *)

(* Pure types are elements from the inductive set [ty] (defined in the file
   [typed_lang.v]). A pure type is interpreted in the model as a persistent
   relation on values, that is, a relation [R : val → val → iProp Σ] such that
   [R v₁ v₂] is persistent for any values [v₁] and [v₂].
   We define [valRel] as the set of such relations.
*)

Record valRel Σ := ValRel {
  valRel_car :> val → val → iProp Σ;
  valRel_persistent v₁ v₂ : Persistent (valRel_car v₁ v₂)
}.
Arguments ValRel {_} _%I {_}.
Arguments valRel_car {_} _ _ _ : simpl never.
Declare Scope valRel_scope.
Bind Scope valRel_scope with valRel.
Delimit Scope valRel_scope with valRel.
Existing Instance valRel_persistent.

Section valRel_ofe.
  Context `{Σ : gFunctors}.
  Instance valRel_equiv : Equiv (valRel Σ) := λ   A B, ∀ v₁ v₂, A v₁ v₂ ≡     B v₁ v₂.
  Instance valRel_dist  : Dist  (valRel Σ) := λ n A B, ∀ v₁ v₂, A v₁ v₂ ≡{n}≡ B v₁ v₂.
  Lemma valRel_ofe_mixin : OfeMixin (valRel Σ).
  Proof. by apply (iso_ofe_mixin (valRel_car : valRel Σ → (val -d> val -d> iPropO Σ))). Qed.
  Canonical Structure valRelO := Ofe (valRel Σ) valRel_ofe_mixin.
  Global Instance valRel_cofe : Cofe valRelO.
  Proof.
    apply (iso_cofe_subtype' (λ A : val -d> val -d> iPropO Σ,
      ∀ v₁ v₂, Persistent (A v₁ v₂)) (@ValRel _) valRel_car)=>//.
    - apply _.
    - apply limit_preserving_forall=> w1.
      apply limit_preserving_forall=> w2.
      apply bi.limit_preserving_Persistent.
      intros n P Q HPQ. apply (HPQ w1 w2).
  Qed.
  Global Instance valRel_inhabited : Inhabited (valRel Σ) := populate (ValRel inhabitant).
  Global Instance valRel_car_ne n : Proper (dist n ==> (=) ==> (=) ==> dist n) valRel_car.
  Proof. by intros A A' ? v₁ v₂ <- ? ? <-. Qed.
  Global Instance valRel_car_proper : Proper ((≡) ==> (=) ==> (=) ==> (≡)) valRel_car.
  Proof.
    intros ??? ??-> ??->. apply equiv_dist=>n.
    by apply valRel_car_ne; first apply equiv_dist.
  Qed.
End valRel_ofe.

Arguments valRelO : clear implicits.


(** * Semantic Intepretation of Effect Types. *)

(* Effect types are elements from the inductive set [eff_ty] (also defined in
   the file [typed_lang.v]). There are two interpretations of effect types in
   the model. Indeed, an effect type is interpreted as a function of one of
   the following types:

     [(valRel → exprRel) → valRel → exprRel]

   and

     [(valRel → exprRel) → valRel → ectxRel]

   where [exprRel] is a relation on expressions and [ectxRel] is a relation
   on evaluation contexts.

   The type [valRel → exprRel] is related with the interpretation of *effect
   signatures*, i.e., the type annotations of the form [<α₁;α₂>] accompanying
   effect types.
*)

(* TODO: Improve the previous comment. *)

Record exprRel Σ := ExprRel {
  exprRel_car :> expr -d> expr -d> iPropO Σ;
}.
Arguments ExprRel {_} _%I.
Arguments exprRel_car {_} _ _%E _%E : simpl never.
Declare Scope exprRel_scope.
Bind Scope exprRel_scope with exprRel.
Delimit Scope exprRel_scope with exprRel.

Section exprRel_ofe.
  Context `{Σ : gFunctors}.
  Instance exprRel_equiv : Equiv (exprRel Σ) := λ A B,
    ∀ e₁ e₂, exprRel_car A e₁ e₂ ≡     exprRel_car B e₁ e₂.
  Instance exprRel_dist : Dist (exprRel Σ) := λ n A B,
    ∀ e₁ e₂, exprRel_car A e₁ e₂ ≡{n}≡ exprRel_car B e₁ e₂.
  Lemma exprRel_ofe_mixin : OfeMixin (exprRel Σ).
  Proof. by apply (iso_ofe_mixin (exprRel_car : exprRel Σ → (expr -d> expr -d> iPropO Σ))). Qed.
  Canonical Structure exprRelO := Ofe (exprRel Σ) exprRel_ofe_mixin.
  Global Instance exprRel_cofe : Cofe exprRelO.
  Proof. by apply (iso_cofe ExprRel exprRel_car). Qed.
  Global Instance exprRel_inhabited : Inhabited (exprRel Σ) := populate (ExprRel inhabitant).
  Global Instance exprRel_car_ne n : Proper (dist n ==> (=) ==> (=) ==> dist n) exprRel_car.
  Proof. by intros A A' ? e₁ e₂ <- ? ? <-. Qed.
  Global Instance exprRel_car_proper : Proper ((≡) ==> (=) ==> (=) ==> (≡)) exprRel_car.
  Proof.
    intros ??? ??-> ??->. apply equiv_dist=>n.
    by apply exprRel_car_ne; first apply equiv_dist.
  Qed.
End exprRel_ofe.

Arguments exprRelO : clear implicits.

Global Instance ExprRel_ne {Σ} : NonExpansive (ExprRel (Σ:=Σ)).
Proof. by intros ???. Qed.
Global Instance ExprRel_proper {Σ} : Proper ((≡) ==> (≡)) (ExprRel (Σ:=Σ)).
Proof. by intros ???. Qed.


Record ectxRel Σ := EctxRel {
  ectxRel_car :> ectx -d> ectx -d> iPropO Σ;
}.
Arguments EctxRel {_} _%I.
Arguments ectxRel_car {_} _ _%E _%E : simpl never.
Declare Scope ectxRel_scope.
Bind Scope ectxRel_scope with ectxRel.
Delimit Scope ectxRel_scope with ectxRel.

Section ectxRel_ofe.
  Context `{Σ : gFunctors}.
  Instance ectxRel_equiv : Equiv (ectxRel Σ) := λ A B,
    ∀ K₁ K₂, ectxRel_car A K₁ K₂ ≡     ectxRel_car B K₁ K₂.
  Instance ectxRel_dist : Dist (ectxRel Σ) := λ n A B,
    ∀ K₁ K₂, ectxRel_car A K₁ K₂ ≡{n}≡ ectxRel_car B K₁ K₂.
  Lemma ectxRel_ofe_mixin : OfeMixin (ectxRel Σ).
  Proof. by apply (iso_ofe_mixin (ectxRel_car : ectxRel Σ → (ectx -d> ectx -d> iPropO Σ))). Qed.
  Canonical Structure ectxRelO := Ofe (ectxRel Σ) ectxRel_ofe_mixin.
  Global Instance ectxRel_cofe : Cofe ectxRelO.
  Proof. by apply (iso_cofe EctxRel ectxRel_car). Qed.
  Global Instance ectxRel_inhabited : Inhabited (ectxRel Σ) := populate (EctxRel inhabitant).
  Global Instance ectxRel_car_ne n : Proper (dist n ==> (=) ==> (=) ==> dist n) ectxRel_car.
  Proof. by intros A A' ? w1 w2 <- ? ? <-. Qed.
  Global Instance ectxRel_car_proper : Proper ((≡) ==> (=) ==> (=) ==> (≡)) ectxRel_car.
  Proof.
    intros ??? ??-> ??->. apply equiv_dist=>n.
    by apply ectxRel_car_ne; first apply equiv_dist.
  Qed.
End ectxRel_ofe.

Arguments ectxRelO : clear implicits.

Global Instance EctxRelK_ne {Σ} : NonExpansive (EctxRel (Σ:=Σ)).
Proof. by intros ???. Qed.
Global Instance EctxRel_proper {Σ} : Proper ((≡) ==> (≡)) (EctxRel (Σ:=Σ)).
Proof. by intros ???. Qed.

(** Notations. *)

Notation "e₁ '<<{' R '}<<' e₂" := (exprRel_car R e₁ e₂) (at level 70).

Definition logN : namespace := nroot .@ "logN".

Class probeffRGS Σ := ProbeffRGS {
                        probeffRGS_probeffGS :: probeffGS Σ;
                        probeffRGS_na_invG :: na_invG Σ;
                        probeffRGS_nais : na_inv_pool_name;
                      }.


Section lrel_ectx_and_expr.
  Context `{!probeffRGS Σ}.

  (* Observational refinement. *)
  Definition obs_refines_def : exprRel Σ := ExprRel (λ e e',
                                                       (∀ ε, ⤇ e' -∗
                                                             ↯ ε -∗
                                                             ⌜ (0 < ε)%R ⌝ -∗
                                                             EWP e @ ⊤ <| iEff_bottom |> {{ _, ∃ v', ⤇ (of_val v')
                                                                                                     ∗ ↯ ε
                                                                                                     ∗ ⌜ (0 < ε)%R ⌝ }}))%I.
  Definition obs_refines_aux : seal obs_refines_def. Proof. by eexists. Qed.
  Definition obs_refines := unseal obs_refines_aux.
  Definition obs_refines_eq : obs_refines = obs_refines_def :=
    seal_eq obs_refines_aux.

  Definition ectx_refines : ((valRelO Σ -d> exprRelO Σ) -d> valRel Σ -d> ectxRelO Σ) := λ E A,
    EctxRel (λ K K',
               (∀ (v v' : val), A v v'          -∗ (fill K (Val v)) <<{obs_refines}<< (fill K' (Val v')))
               ∧
               (∀ (e e' : expr), e <<{ E A }<< e' -∗ (fill K e) <<{obs_refines}<< (fill K' e')))%I.
  Global Instance ectx_refines_ne n : Proper ((dist n) ==> (dist n) ==> (dist n)) ectx_refines.
  Proof. intros ????????. 
         (* intros ????????. by solve_proper. Qed. *) Admitted.
  Global Instance ectx_refines_proper : Proper ((≡) ==> (≡) ==> (≡)) ectx_refines.
  Proof. intros ????????.  (* by solve_proper. Qed. *) Admitted.

  Definition expr_refines : ((valRelO Σ -d> exprRelO Σ) -d> valRel Σ -d> exprRelO Σ) := λ E A,
    ExprRel (λ e e',
      ∀ (K K' : ectx),
        ectxRel_car (ectx_refines E A) K K' -∗
          (fill K e) <<{obs_refines}<< (fill K' e'))%I.
  Global Instance expr_refines_ne n : Proper ((dist n) ==> (dist n) ==> (dist n)) expr_refines.
  Proof. intros ????????. by solve_proper. Qed. 
  Global Instance expr_refines_proper : Proper ((≡) ==> (≡) ==> (≡)) expr_refines.
  Proof. intros ????????. by solve_proper. Qed.

  Definition sig_type Σ : Type := (loc * loc) * (valRel Σ * valRel Σ).

                                          (* TODO: Consider changing list to map *)
  (* Effect relation. *)
  Program Definition eff_refines_pre :
    ((list (sig_type Σ)) -d> (list (sig_type Σ)) -d> (valRelO Σ -n> exprRelO Σ)) →
    ((list (sig_type Σ)) -d> (list (sig_type Σ)) -d> (valRelO Σ -n> exprRelO Σ)) := λ eff_refines ρ' ρ, λne A,
     ExprRel (λ e e',
                ∃ (l1' l2' : loc) v v' N N',
                  ⌜ e = Eff (#l1', v) N ⌝ ∗ ⌜ e' = Eff (#l2', v') N' ⌝ ∗
                  ⌜ NeutralEctx N ⌝ ∗ ⌜ NeutralEctx N' ⌝ ∗
                  match ρ' with
                  | [] => False
                  | ((l1, l2), (A1, A2)) :: ρ'' =>
                ⌜ l1 = l1' ⌝ ∗ ⌜ l2 = l2' ⌝ ∗
                A1 v v' ∗
                □(∀ w w', A2 w w' -∗ ▷( fill N w <<{ expr_refines (eff_refines ρ ρ) A }<< fill N' w'))
                ∨
                  ▷(e <<{eff_refines ρ'' ρ A}<< e')
              end)%I.
  Next Obligation. intros ???????. repeat f_equiv. intros ??. simpl. destruct ρ' as [| ((l1, l2), ( A1, A2)) ρ'']; solve_proper.  Qed.
  Local Instance eff_refines_pre_contractive : Contractive eff_refines_pre.
  Proof.
    rewrite /eff_refines_pre=> n eff_ref eff_refines' Heff ρ' ρ A. simpl.
    apply ExprRel_ne=>??.
    induction ρ' as [| ((l1,l2), (A1, A2)) ρ'']; eauto.
    do 17f_equiv; [| f_contractive; solve_proper].
    do 9f_equiv. f_contractive. do 2f_equiv. apply Heff.
  Qed.
  Definition eff_refines_def := fixpoint eff_refines_pre.
  Definition eff_refines_aux : seal eff_refines_def. Proof. by eexists. Qed.
  Definition eff_refines := eff_refines_aux.(unseal).
  Definition eff_refines_eq : eff_refines = eff_refines_def := eff_refines_aux.(seal_eq).
  Global Lemma eff_refines_unfold A1 A2 A :
    (eff_refines A1 A2 A) ≡ (eff_refines_pre eff_refines A1 A2 A).
  Proof.
    rewrite eff_refines_eq /eff_refines_def.
    apply (fixpoint_unfold eff_refines_pre).
  Qed.
  Global Instance eff_refines_ne n :
    Proper ((Forall2 (dist n)) ==> (Forall2 (dist n)) ==> (dist n)) eff_refines.
  Proof.
    induction (lt_wf n) as [n _ IH]=> ρ1' ρ2' Hρ' ρ1 ρ2 Hρ A.
    rewrite !eff_refines_unfold /eff_refines_pre.
    simpl. repeat f_equiv. intros ??.
    destruct ρ1' as [| ((l1, l2), (A1, A1')) ρ1''];
      destruct ρ2' as [| ((l1', l2'), (A2, A2')) ρ2'']; eauto;
    inversion Hρ';
    inversion H2;
    inversion H6;
      simpl in *.
    simplify_eq.
    inversion H5.
    simpl in *.
    do 17 f_equiv.
    2 : { f_contractive. apply IH; eauto; eapply Forall2_impl; try done; intros ??; eauto using dist_lt. }
    f_equiv; [by rewrite H|].
    f_equiv; [by rewrite H0|].
    do 2 f_equiv; [done|].
    do 5 f_equiv; [done|].
    f_contractive. do 2 f_equiv.
    apply IH; try lia;  eapply Forall2_impl; try done; intros ??; eauto using dist_lt.
  Qed.
  (* TODO: clean up this proof *)
  Global Instance eff_refines_proper :
    Proper (Forall2 (≡) ==> Forall2 (≡) ==> (≡)) eff_refines.
  Proof.
    intros ρ1' ρ2' Hρ' ρ1 ρ2 Hρ A.
    apply equiv_dist=>n. apply eff_refines_ne; apply list_equiv_Forall2. 
    1 : { apply list_equiv_Forall2. generalize dependent ρ2'. induction ρ1'; intros ρ2' Hρ'; destruct ρ2'; eauto.
          - by apply Forall2_nil_cons_inv in Hρ'.
          - by apply Forall2_cons_nil_inv in Hρ'.
          - destruct a as [l1' (A1, A2)]. destruct s as [l2' (A1', A2')]. inversion Hρ'. simplify_eq. constructor.
            1 : { constructor; simpl; inversion H2; try done. simpl in *.
                  inversion H0. constructor.
                  + rewrite H1. done.
                  + rewrite H3. done. }
            apply IHρ1'. done. }
    apply list_equiv_Forall2. generalize dependent ρ2. induction ρ1; intros ρ2 Hρ; destruct ρ2; eauto.
          - by apply Forall2_nil_cons_inv in Hρ.
          - by apply Forall2_cons_nil_inv in Hρ.
          - destruct a as [l1' (A1, A2)]. destruct s as [l2' (A1', A2')]. inversion Hρ. simplify_eq. constructor.
            1 : { constructor; simpl; inversion H2; try done. simpl in *.
                  inversion H0. constructor.
                  + rewrite H1. done.
                  + rewrite H3. done. }
            apply IHρ1. done.
  Qed.

End lrel_ectx_and_expr.


(** * Value Relations. *)

Section semtypes.
  Context `{!probeffRGS Σ}.

  Implicit Types e : expr.
  Implicit Types E : coPset.
  Implicit Types A B : valRel Σ.

  Definition valRel_unit : valRel Σ := ValRel (λ w1 w2, ⌜ w1 = #() ∧ w2 = #() ⌝%I).
  Definition valRel_bool : valRel Σ := ValRel (λ w1 w2, ∃ b : bool, ⌜ w1 = #b ∧ w2 = #b ⌝)%I.
  Definition valRel_int : valRel Σ := ValRel (λ w1 w2, ∃ n : Z, ⌜ w1 = #n ∧ w2 = #n ⌝)%I.
  Definition valRel_nat : valRel Σ := ValRel (λ w1 w2, ∃ n : nat, ⌜ w1 = #n ∧ w2 = #n ⌝)%I.
  Definition valRel_bot : valRel Σ := ValRel (λ w1 w2, False%I).
  Definition valRel_arrow (A : valRel Σ) (B : exprRel Σ) : valRel Σ :=
    ValRel (λ w1 w2, □ ∀ v1 v2, A v1 v2 -∗ (App w1 v1) <<{B}<< (App w2 v2))%I.
  Definition valRel_ref (A : valRel Σ) : valRel Σ := ValRel (λ w1 w2,
    ∃ l1 l2: loc, ⌜w1 = #l1⌝ ∧ ⌜w2 = #l2⌝ ∧
                  inv (logN .@ "ref" .@ (l1,l2)) (∃ v1 v2, l1 ↦ v1 ∗ l2 ↦ₛ v2 ∗ A v1 v2))%I.
  Definition valRel_tape : valRel Σ := ValRel (λ w1 w2,
    ∃ (α1 α2 : loc) (N: nat), ⌜w1 = #lbl:α1⌝ ∧ ⌜w2 = #lbl:α2⌝ ∧
      inv (logN .@ (α1, α2)) (α1 ↪ (N; []) ∗ α2 ↪ₛ (N; [])))%I.
  
  Definition valRel_prod (A B : valRel Σ) : valRel Σ := ValRel (λ w1 w2,
    ∃ v1 v2 v1' v2', ⌜w1 = (v1,v1')%V⌝ ∧ ⌜w2 = (v2,v2')%V⌝ ∧
        A v1 v2 ∗ B v1' v2')%I.
  Definition valRel_sum (A B : valRel Σ) : valRel Σ := ValRel (λ w1 w2,
    ∃ v1 v2, (⌜w1 = InjLV v1⌝ ∧ ⌜w2 = InjLV v2⌝ ∧ A v1 v2)
          ∨  (⌜w1 = InjRV v1⌝ ∧ ⌜w2 = InjRV v2⌝ ∧ B v1 v2))%I.
  Definition valRel_rec_pre (C : valRelO Σ -n> valRelO Σ) (rec : valRel Σ) : valRel Σ :=
    ValRel (λ w1 w2, ▷ C rec w1 w2)%I.
  Instance valRel_rec_pre_contractive C : Contractive (valRel_rec_pre C).
  Proof.
    intros n. intros P Q HPQ.
    unfold valRel_rec_pre. intros w1 w2. rewrite {1 4}/valRel_car /=.
    f_contractive. f_equiv. by apply C.
  Qed.
  Definition valRel_rec (C : valRelO Σ -n> valRelO Σ) : valRel Σ := fixpoint (valRel_rec_pre C).
  Definition valRel_exists (C : valRel Σ → valRel Σ) : valRel Σ := ValRel (λ w1 w2, ∃ A, C A w1 w2)%I.
  Definition valRel_forall {A : ofe} (C : A → valRel Σ) : valRel Σ := ValRel (λ w1 w2,
    ∀ (R : A),
      let B : exprRel Σ := expr_refines (eff_refines [] []) (C R) in
      (valRel_arrow valRel_unit B w1 w2))%I.
  Definition valRel_true : valRel Σ := ValRel (λ w1 w2, True)%I.

  (** The valRel constructors are non-expansive *)
  Global Instance valRel_prod_ne n : Proper (dist n ==> dist n ==> dist n) valRel_prod.
  Proof. solve_proper. Qed.
  Global Instance valRel_sum_ne n : Proper (dist n ==> dist n ==> dist n) valRel_sum.
  Proof. solve_proper. Qed.
  Global Instance valRel_arrow_ne n : Proper (dist n ==> dist n ==> dist n) valRel_arrow.
  Proof. solve_proper. Qed.
  Global Instance valRel_ref_ne n : Proper (dist n ==> dist n) valRel_ref.
  Proof. solve_proper. Qed.
  Global Instance valRel_tape_ne n : Proper (dist n ==> dist n ==> dist n) valRel_tape.
  Proof. solve_proper. Qed.
  Global Instance valRel_arrow_proper : Proper ((≡) ==> (≡) ==> (≡)) valRel_arrow.
  Proof. solve_proper. Qed.
  Global Instance valRel_ref_proper : Proper ((≡) ==> (≡)) valRel_ref.
  Proof. solve_proper. Qed.
  Global Instance valRel_tape_proper : Proper ((≡) ==> (≡) ==> (≡)) valRel_tape.
  Proof. solve_proper. Qed.
  Global Instance valRel_rec_ne n : Proper (dist n ==> dist n)
       (valRel_rec : (valRelO Σ -n> valRelO Σ) -> valRelO Σ).
  Proof.
    intros F F' HF.
    unfold valRel_rec, valRel_car.
    apply fixpoint_ne=> X w1 w2.
    unfold valRel_rec_pre, valRel_car. cbn.
    f_equiv.
    apply valRel_car_ne; eauto.
  Qed.
  Lemma valRel_rec_unfold (C : valRelO Σ -n> valRelO Σ) : valRel_rec C ≡ valRel_rec_pre C (valRel_rec C).
  Proof. apply fixpoint_unfold. Qed.

  Global Instance valRel_forall_ne {A : ofe} n :
    Proper (((=) ==> (dist n)) ==> (dist n)) (@valRel_forall A).
  Proof. 
    intros ?????. apply bi.forall_ne=>?. simpl.
    apply valRel_arrow_ne; [done|].
    apply expr_refines_ne; [done|].
    by apply H.
  Qed.
  Global Instance valRel_forall_proper {A : ofe} :
    Proper (((=) ==> (≡)) ==> (≡)) (@valRel_forall A).
  Proof.
    intros ?????. apply bi.forall_proper=>?. simpl.
    apply valRel_arrow_proper; [done|].
    apply expr_refines_proper; [done|].
    by apply H.
  Qed.
End semtypes.

(** Nice notations *)
Notation "()" := valRel_unit : valRel_scope.
Notation "⊥" := valRel_bot : valRel_scope.
Notation "'Int'" := valRel_int : valRel_scope.
Notation "'Nat'" := valRel_nat : valRel_scope.
Infix "→" := valRel_arrow : valRel_scope.
Infix "*" := valRel_prod : valRel_scope.
Infix "+" := valRel_sum : valRel_scope.
Notation "'ref' A" := (valRel_ref A) : valRel_scope.
Notation "∃ A1 .. An , C" :=
  (valRel_exists (λ A1, .. (valRel_exists (λ An, C%valRel)) ..)) : valRel_scope.
Notation "∀ A1 .. An , C" :=
  (valRel_forall (λ A1, .. (valRel_forall (λ An, C%valRel)) ..)) : valRel_scope.
Notation noEffs := (eff_refines [] [])%valRel.

Arguments expr_refines {_ _} _%_valRel _%_valRel.
Arguments eff_refines {_ _} _%_valRel _%_valRel.


(** * Properties of Semantic Types. *)

Section semtypes_properties.
  Context `{!probeffRGS Σ}.

  (* The reference type relation is functional and injective.
     Thanks to Amin. *)
  Lemma interp_ref_funct E (A : valRel Σ) (l l1 l2 : loc) :
    ↑logN ⊆ E →
    (ref A)%valRel #l #l1 ∗ (ref A)%valRel #l #l2
    ={E}=∗ ⌜l1 = l2⌝.
  Proof.
    iIntros (?) "[Hl1 Hl2] /=".
    iDestruct "Hl1" as (l' l1') "[% [% #Hl1]]". simplify_eq.
    iDestruct "Hl2" as (l l2') "[% [% #Hl2]]". simplify_eq.
    destruct (decide (l1' = l2')) as [->|?]; eauto.
    iInv (logN.@"ref".@(l, l1')) as (? ?) "[>Hl ?]" "Hcl".
    iInv (logN.@"ref".@(l, l2')) as (? ?) "[>Hl' ?]" "Hcl'".
    simpl. iExFalso.
    iDestruct (ghost_map.ghost_map_elem_valid_2 with "Hl Hl'") as %[Hfoo _].
    compute in Hfoo. eauto.
  Qed.

  Lemma interp_ref_inj E (A : valRel Σ) (l l1 l2 : loc) :
    ↑logN ⊆ E →
    (ref A)%valRel #l1 #l ∗ (ref A)%valRel #l2 #l
    ={E}=∗ ⌜l1 = l2⌝.
  Proof.
    iIntros (?) "[Hl1 Hl2] /=".
    iDestruct "Hl1" as (l1' l') "[% [% #Hl1]]". simplify_eq.
    iDestruct "Hl2" as (l2' l) "[% [% #Hl2]]". simplify_eq.
    destruct (decide (l1' = l2')) as [->|?]; eauto.
    iInv (logN.@"ref".@(l1', l)) as (? ?) "(? & >Hl & ?)" "Hcl".
    iInv (logN.@"ref".@(l2', l)) as (? ?) "(? & >Hl' & ?)" "Hcl'".
    simpl. iExFalso.
    iDestruct (ghost_map_elem_valid_2 with "Hl Hl'") as %(Hfoo & _).
    compute in Hfoo. eauto.
  Qed.

End semtypes_properties.


(** * Monadic Rules. *)

Section monadic.
  Context `{probeffRGS Σ}.

  (* Bind rule for effectful expressions. *)
  Lemma refines_bind K K' E A F B e e' :
    e <<{ expr_refines E A }<< e' -∗

     ((∀ (v v' : val),
         A v v' -∗
           (fill K v) <<{ expr_refines F B }<< (fill K' v')) ∧

      (∀ (s s' : expr),
         s <<{ E A }<< s' -∗
           (fill K s) <<{ expr_refines F B }<< (fill K' s'))) -∗

        (fill K e) <<{ expr_refines F B }<< (fill K' e').
  Proof.
    iIntros "He H".
    iIntros (K1 K2) "HK12".
    rewrite -!fill_app.
    iApply "He".
    iSplit.
    - iDestruct "H" as "[HKval _]".
      iIntros (v v') "HA". rewrite !fill_app.
      iSpecialize ("HKval" with "HA").
      by iApply "HKval".
    - iDestruct "H" as "[_ HKeff]".
      iIntros (s s') "HE". rewrite !fill_app.
      iSpecialize ("HKeff" with "HE").
      by iApply "HKeff".
  Qed.

  (* Bind rule for pure expressions. *)
  Lemma refines_pure_bind K K' A F B e e' :
    e <<{ expr_refines (eff_refines [] []) A }<< e' -∗

      (∀ (v v' : val),
         A v v' -∗
           (fill K v) <<{ expr_refines F B }<< (fill K' v')) -∗

        (fill K e) <<{ expr_refines F B }<< (fill K' e').
  Proof.
    iIntros "He HKval".
    iIntros (K1 K2) "HK12".
    rewrite -!fill_app.
    iApply "He".
    iSplit.
    - iIntros (v v') "HA". rewrite !fill_app.
      iSpecialize ("HKval" with "HA").
      by iApply "HKval".
    - iIntros (s s') "H". rewrite eff_refines_unfold. iDestruct "H" as (??????????) "contra". done.
  Qed.

  (* Bind rule for pure expressions under an evaluation context item. *)
  Lemma Ectxi_refines_pure_bind K K' A F B e e' :
    e <<{ expr_refines (eff_refines [] []) A }<< e' -∗

      (∀ (v v' : val),
         A v v' -∗
           (fill_item K v) <<{ expr_refines F B }<< (fill_item K' v')) -∗

        (fill_item K e) <<{ expr_refines F B }<< (fill_item K' e').
  Proof.
    iIntros "He HKval".
    by iApply (refines_pure_bind [K]
                                 [K'] with "He").
  Qed.

  (* Return rule. *)
  Lemma refines_ret e₁ e₂ v₁ v₂ E (A : valRel Σ) :
    IntoVal e₁ v₁ →
    IntoVal e₂ v₂ →
    A v₁ v₂ -∗ e₁ <<{ expr_refines E A }<< e₂.
  Proof.
    iIntros (<-<-) "HA". iIntros (K K') "HK".
    iDestruct "HK" as "[HK _]". by iApply "HK".
  Qed.

  (* Effect rule. *)
  Lemma refines_eff e₁ e₂ (E : valRelO Σ -n> exprRelO Σ) A :
    e₁ <<{ E A }<< e₂ -∗ e₁ <<{ expr_refines E A }<< e₂.
  Proof. iIntros "HE" (K K') "HK". by iApply "HK". Qed.

  (* TODO: reformulate to the new definition of row-types *)
  (* Lemma eff_refines_intro (A1 A2 B : valRel Σ) v v' N N' e e' :
       e = of_eff v N → e' = of_eff v' N' →
         NeutralEctx N → NeutralEctx N' →
           A1 v v' -∗
             □ (∀ (w w' : val),
                  A2 w w' -∗
                    ▷ ((fill N  w ) <<{ expr_refines (eff_refines A1 A2) B }<<
                       (fill N' w'))) -∗
           e <<{ eff_refines A1 A2 B }<< e'.
     Proof.
       intros -> -> ??. rewrite eff_refines_unfold.
       iIntros "HA #HN". iExists v, v', N, N'.
       do 2 (iSplit; [iPureIntro; apply _|]). by auto.
     Qed. *)

End monadic.



(** * Rules. *)

Section pure_reduction.
  Context `{probeffRGS Σ}.

  (** One-step reduction. *)

  (* Observational refinement - implementation side. *)
  Lemma obs_refines_pure_l e₁ e₁' e₂ :
    pure_prim_step e₁ e₁' →
      ▷ (e₁' <<{ obs_refines }<< e₂) ⊢ e₁ <<{ obs_refines }<< e₂.
  Proof.
    iIntros (Hstep) "He". rewrite obs_refines_eq.
    iIntros (ε) "Hj". iIntros "Herr". iIntros (Hpos).
    iApply ewp_pure_step'. { by apply Hstep. }
    iNext. by iApply ("He" with "[$] [$]").
  Qed.

  (* Observational refinement - specification side. *)
  Lemma obs_refines_pure_r e1 e2 e2' :
    TCEq (to_eff e1) None →
      pure_prim_step e2 e2' →
        e1 <<{ obs_refines }<< e2' ⊢ e1 <<{ obs_refines }<< e2.
  Proof.
    iIntros (Heff (Hsafe&Hdet)) "He". rewrite obs_refines_eq.
    iIntros (ε) "Hj". iIntros "Herr". iIntros (Hpos).
    iApply spec_update_ewp.
    iMod (step_pure ⊤ [] with "Hj") as "Hj"; [ apply I| | ].
    { intros _. apply nsteps_once. split; eauto. }
    iModIntro.
    by iApply ("He" with "[$] [$]"). 
  Qed.

  (* Expression relation - implementation side. *)
  Lemma refines_pure_l e₁ e₁' e₂ E A :
    pure_prim_step e₁ e₁' →
      ▷ (e₁' <<{ expr_refines E A }<< e₂) ⊢ e₁ <<{ expr_refines E A }<< e₂.
  Proof.
    iIntros (Hstep) "He". iIntros (K1 K2) "HK".
    iApply obs_refines_pure_l. { by apply pure_prim_step_fill, Hstep. }
    iNext. by iApply "He".
  Qed.

  (* Expression relation - specification side. *)
  Lemma refines_pure_r e₁ e₂ e₂' E A :
    TCEq (to_eff e₁) None →
      pure_prim_step e₂ e₂' →
        e₁ <<{ expr_refines E A }<< e₂' ⊢ e₁ <<{ expr_refines E A }<< e₂.
  Proof.
    iIntros (Heff Hstep) "He". iIntros (K1 K2) "HK".
    iApply obs_refines_pure_r.
    { rewrite fill_not_eff; [done|]. by rewrite Heff. }
    { by apply pure_prim_step_fill, Hstep. }
    { by iApply "He". }
  Qed.


  (** Multiple steps reduction. *)

  (* Observational refinement - implementation side. *)
  Lemma obs_refines_pure_l' e₁ e₁' e₂ :
    tc pure_prim_step e₁ e₁' →
      ▷ (e₁' <<{ obs_refines }<< e₂) ⊢ e₁ <<{ obs_refines }<< e₂.
  Proof.
    iIntros (Hstep) "He". rewrite obs_refines_eq.
    iIntros (ε) "Hj". iIntros "Herr". iIntros (Hpos).
    iApply ewp_pure_steps'. { by apply Hstep. }
    iNext. by iApply ("He" with "[$][$]").
  Qed.

  (* TODO: Find better name for this lemma. *)
  Lemma obs_refines_rtc_pure_l e₁ e₁' e₂ :
    rtc pure_prim_step e₁ e₁' →
      (e₁' <<{ obs_refines }<< e₂) ⊢ e₁ <<{ obs_refines }<< e₂.
  Proof.
    induction 1; [done|].
    iIntros "H". iApply obs_refines_pure_l; [done|].
    by iApply IHrtc.
  Qed.

  (* Observational refinement - specification side. *)
  Lemma obs_refines_pure_r'  e₁ e₂ e₂' :
    TCEq (to_eff e₁) None →
      tc pure_prim_step e₂ e₂' →
        e₁ <<{ obs_refines }<< e₂' ⊢ e₁ <<{ obs_refines }<< e₂.
  Proof.
    intros He. induction 1.
    - by iApply obs_refines_pure_r.
    - iIntros "H".
      iPoseProof (IHtc with "H") as "IH".
      by iApply (obs_refines_pure_r with "IH").
  Qed.

  (* Expression relation - implementation side. *)
  Lemma refines_pure_l'  e₁ e₁' e₂ E A :
    tc pure_prim_step e₁ e₁' →
      ▷ (e₁' <<{ expr_refines E A }<< e₂) ⊢ e₁ <<{ expr_refines E A }<< e₂.
  Proof.
    induction 1.
    - by iApply refines_pure_l.
    - iIntros "H".
      iPoseProof (IHtc with "H") as "IH".
      by iApply (refines_pure_l with "IH").
  Qed.

  (* TODO: Find better name for this lemma. *)
  Lemma refines_rtc_pure_l e₁ e₁' e₂ E A :
    rtc pure_prim_step e₁ e₁' →
      (e₁' <<{ expr_refines E A }<< e₂) ⊢ e₁ <<{ expr_refines E A }<< e₂.
  Proof.
    induction 1; [done|].
    iIntros "H". iApply refines_pure_l; [done|].
    by iApply IHrtc.
  Qed.

  (* Expression relation - specification side. *)
  Lemma refines_pure_r'  e₁ e₂ e₂' E A :
    TCEq (to_eff e₁) None →
      tc pure_prim_step e₂ e₂' →
        e₁ <<{ expr_refines E A }<< e₂' ⊢ e₁ <<{ expr_refines E A }<< e₂.
  Proof.
    intros He. induction 1.
    - by iApply refines_pure_r.
    - iIntros "H".
      iPoseProof (IHtc with "H") as "IH".
      by iApply (refines_pure_r with "IH").
  Qed.

End pure_reduction.


Section stateful_reduction.
  Context `{probeffRGS Σ}.

  (* A helper lemma for proving the stateful reductions for the RHS below *)
  Lemma refines_step_r E K' e1 e2 A :
    (∀ k, ⤇ fill k e2 -∗
         spec_update ⊤ (∃ v, ⤇ fill k (of_val v) ∗
                              e1 <<{ expr_refines E A }<< fill K' (of_val v) ))
    ⊢ e1 <<{ expr_refines E A }<< fill K' e2.
  Proof.
    iIntros "He" (K1 K2) "HKK".
    rewrite obs_refines_eq -fill_app.
    iIntros (ε) "Hj". iIntros "Herr". iIntros (Hpos).
    iApply spec_update_ewp.
    iMod ("He" with "Hj") as (v) "[Hs He]".
    iModIntro.
    rewrite fill_app.
    iSpecialize ("He" with "HKK"). 
    rewrite obs_refines_eq.
    by iApply ("He" with "[$][$]").
  Qed.

  Lemma refines_alloc_l K (v : val) (e : expr) E A :
    ▷ (∀ (l : loc), l ↦ v -∗ (fill K #l) <<{ expr_refines E A }<< e) -∗
      (fill K (Alloc v)) <<{ expr_refines E A }<< e.
  Proof.
    iIntros "He" (K1 K2) "HKK'".
    rewrite obs_refines_eq -fill_app.
    iIntros (ε) "Hj". iIntros "Herr". iIntros (Hpos).
    iApply (ewp_pure_bind (K ++ K1)); [done|].
    iApply ewp_alloc. iNext. iIntros (l) "Hl".
    rewrite fill_app.
    iSpecialize ("He" $! l with "Hl").
    iSpecialize ("He" $! K1 K2 with "HKK'").
    rewrite obs_refines_eq.
    by iApply ("He" with "[$][$]").
  Qed.

  Lemma refines_alloc_r K (v : val) (e : expr) E A :
    TCEq (to_eff e) None →
      (∀ (l : loc), l ↦ₛ v -∗ e <<{ expr_refines E A }<< (fill K #l)) -∗
        e <<{ expr_refines E A }<< (fill K (Alloc v)).
  Proof.
    iIntros (Heff) "He".
    iIntros (K1 K2) "HKK'".
    rewrite obs_refines_eq -fill_app.
    iIntros (ε) "Hj". iIntros "Herr". iIntros (Hpos).
    iApply spec_update_ewp.
    tp_alloc as l "Hl".
    iModIntro.
    iSpecialize ("He" $! l with "Hl").
    iSpecialize ("He" $! K1 K2 with "HKK'").
    rewrite obs_refines_eq.
    by iApply ("He" with "[$][$]").
  Qed.

  Lemma refines_load_l K (l : loc) (v : val) (e : expr) E A :
    ▷ l ↦ v -∗
      ▷ (l ↦ v -∗ (fill K v) <<{ expr_refines E A }<< e) -∗
    (fill K (Load #l)) <<{ expr_refines E A }<< e.
  Proof.
    iIntros "Hl He".
    iIntros (K1 K2) "HKK'".
    rewrite obs_refines_eq -fill_app.
    iIntros (ε) "Hj". iIntros "Herr". iIntros (Hpos). 
    iApply ewp_pure_bind; [done|]. 
    iApply (ewp_load with "Hl"). iNext. iIntros "Hl".
    iSpecialize ("He" with "Hl HKK'").
    rewrite obs_refines_eq fill_app.
    by iApply ("He" with "[$][$]").
  Qed.

  Lemma refines_load_r K (l : loc) (v : val) (e : expr) E A :
    TCEq (to_eff e) None →
      l ↦ₛ v -∗
        (l ↦ₛ v -∗ e <<{ expr_refines E A }<< (fill K v)) -∗
    e <<{ expr_refines E A }<< (fill K (Load #l)).
  Proof.
    iIntros (Heff) "Hl He".
    iIntros (K1 K2) "HKK'".
    rewrite obs_refines_eq -fill_app.
    iIntros (ε) "Hj". iIntros "Herr". iIntros (Hpos).
    iApply spec_update_ewp.
    iMod (step_load with "[$]") as "(Hj&Hl)".
    iModIntro.
    iSpecialize ("He" with "Hl HKK'").
    rewrite obs_refines_eq fill_app.
    by iApply ("He" with "[$][$]").
  Qed.


  Lemma refines_store_l K (l : loc) (v w : val) (e : expr) E A :
    ▷ l ↦ v -∗
      ▷ (l ↦ w -∗ (fill K #()) <<{ expr_refines E A }<< e) -∗
    (fill K (#l <- w)) <<{ expr_refines E A }<< e.
  Proof.
    iIntros "Hl He" (K1 K2) "HKK'".
    rewrite obs_refines_eq -fill_app. 
    iIntros (ε) "Hj". iIntros "Herr". iIntros (Hpos). 
    ewp_store.
    iSpecialize ("He" with "Hl").
    iSpecialize ("He" $! K1 K2 with "HKK'").
    rewrite obs_refines_eq fill_app.
    by iApply ("He" with "[$][$]").
  Qed.

  Lemma refines_store_r K (l : loc) (v w : val) (e : expr) E A :
    TCEq (to_eff e) None →
      l ↦ₛ v -∗
        (l ↦ₛ w -∗ (e <<{ expr_refines E A }<< (fill K #()))) -∗
    e <<{ expr_refines E A }<< (fill K (#l <- w)).
  Proof.
    iIntros (Heff) "Hl He".
    iIntros (K1 K2) "HKK'".
    rewrite obs_refines_eq -fill_app.
    iIntros (ε) "Hj". iIntros "Herr". iIntros (Hpos).
    iApply spec_update_ewp.
    iMod (step_store with "[$]") as "(Hj&Hl)".
    iModIntro.
    iSpecialize ("He" with "Hl").
    iSpecialize ("He" $! K1 K2 with "HKK'").
    rewrite obs_refines_eq fill_app.
    by iApply ("He" with "[$][$]").
  Qed.

End stateful_reduction.


(** * Tactics. *)

Module tactics.

  Ltac reshape_expr e tac :=
    let rec go K e :=
      match e with
      | Do ?e                 => add_item DoCtx K e
      | TryWith ?e ?e1 ?e2    => add_item (TryWithCtx e1 e2) K e
      | App ?e (Val ?v)       => add_item (AppLCtx v) K e
      | App ?e1 ?e2           => add_item (AppRCtx e1) K e2
      | UnOp ?op ?e           => add_item (UnOpCtx op) K e
      | BinOp ?op ?e (Val ?v) => add_item (BinOpLCtx op v) K e
      | BinOp ?op ?e1 ?e2     => add_item (BinOpRCtx op e1) K e2
      | If ?e0 ?e1 ?e2        => add_item (IfCtx e1 e2) K e0
      | Pair ?e (Val ?v)      => add_item (PairLCtx v) K e
      | Pair ?e1 ?e2          => add_item (PairRCtx e1) K e2
      | Fst ?e                => add_item FstCtx K e
      | Snd ?e                => add_item SndCtx K e
      | InjL ?e               => add_item InjLCtx K e
      | InjR ?e               => add_item InjRCtx K e
      | Case ?e0 ?e1 ?e2      => add_item (CaseCtx e1 e2) K e0
      | AllocN ?e (Val ?v)    => add_item (AllocNLCtx v) K e
      | AllocN ?e1 ?e2        => add_item (AllocNRCtx e1) K e2
      | Load ?e               => add_item LoadCtx K e
      | Store ?e (Val ?v)     => add_item (StoreLCtx v) K e
      | Store ?e1 ?e2         => add_item (StoreRCtx e1) K e2
      | AllocTape ?e          => add_item (AllocTapeCtx) K e
      | Rand ?e (Val ?v)      => add_item (RandLCtx v) K e
      | Rand ?e1 ?e2          => add_item (RandRCtx e1) K e2
      | Tick ?e               => add_item (TickCtx) K e

      | Val _                 => tac K e
      | Eff _ _               => tac K e
      | Var _                 => tac K e
      | Rec _ _ _             => tac K e
      | _                     => tac K e
    end
    with add_item Ki K e := go (Ki :: K) e
    in go ([] : ectx) e.

  (* Apply a [pure_prim_step] lemma according to the current goal. *)
  Ltac apply_pure_prim_step e :=
    match e with
    | Do (Val _)                      => apply pure_prim_step_do
    | TryWith (Val _) _ _             => apply pure_prim_step_try_with_val
    | TryWith (Eff _ _) _ _           => apply pure_prim_step_try_with_eff
    | Rec _ _ _                       => apply pure_prim_step_rec
    | App (Val (RecV _ _ _)) (Val _)  => apply pure_prim_step_beta
    | App (Val (Cont _)) (Val _)      => apply pure_prim_step_cont
    | UnOp _ _                        => apply pure_prim_step_unop
    | BinOp _ _ _                     => apply pure_prim_step_binop
    | If (Val (LitV (LitBool _))) _ _ => apply pure_prim_step_if
    | Pair (Val _) (Val _)            => apply pure_prim_step_pair
    | Fst (Val (PairV _ _))           => apply pure_prim_step_Fst
    | Snd (Val (PairV _ _))           => apply pure_prim_step_Snd
    | InjL (Val _)                    => apply pure_prim_step_InjL
    | InjR (Val _)                    => apply pure_prim_step_InjR
    | Case (Val (InjLV _)) _ _        => apply pure_prim_step_case_InjL
    | Case (Val (InjRV _)) _ _        => apply pure_prim_step_case_InjR
    end.

  (* It tries either to solve a goal of the form [tc pure_prim_step e e'] by
     finding an one-step reduction from [e] to [e'] or to simplify it by
     finding an one-step reduction from [e] to some expression.
   *)
  Ltac apply_tc_pure_prim_step e :=
    let tac K e :=
      match e with
      | Eff _ _ =>
         match K with
         | ?Ki :: ?K =>
             match Ki with
             | TryWithCtx _ _ =>  apply pure_prim_step_try_with_eff
             | _ =>
                 apply (pure_prim_step_fill K);
                 apply (pure_prim_step_eff Ki)
             end
         | _ => idtac
         end
      | _ => 
         apply (pure_prim_step_fill K);
         apply_pure_prim_step e
      end
    in
  
    let try_tc_once :=
      apply tc_once; reshape_expr e tac; fail
    in
  
    let try_tc_l := (
      let x := fresh "x" in
      evar (x : expr);
      let e' := eval unfold x in x in
      clear x;
      apply (tc_l _ _ e');  [reshape_expr e tac|];
      simpl
    )
    in
  
    try_tc_once || try_tc_l.
  
  Ltac solve_pure_steps :=
    repeat (
      match goal with
      | [ |- tc pure_prim_step ?e _ ] => apply_tc_pure_prim_step e
      end
      ).


  Goal ∀ y N (h r : val),
    tc pure_prim_step
      (TryWith (Eff y N) (λ: "v" "k", h "v" (λ: "w", deep_try_with (λ: <>, "k" "w") h r)) r)
      (h y (λ: "w", DeepTryWith ((Cont N ) "w") h  r )%V).
  Proof. intros y N h r. solve_pure_steps. Qed.
  
  Goal ∀ e (h r : val),
    tc pure_prim_step
      (deep_try_with (λ: <>, e)%E h r)
      (TryWith ((λ: <>, e)%V #())
               (λ: "v" "k", h  "v" (λ: "w", DeepTryWith ("k" "w")%E h  r)) r).
  Proof. intros e h r. unfold deep_try_with. by solve_pure_steps. Qed. 
 End tactics.



(** * Compatibility Lemmas. *)

Class Compatible `{probeffRGS Σ} (E : valRelO Σ -n> exprRelO Σ) :=
  compatible :
    ⊢ (∀ (A B : valRel Σ) (e e' : expr) (v v' : val),
        (A → (expr_refines E B))%valRel v v' -∗
          e <<{ E A }<< e' -∗
            (bind' e v) <<{ expr_refines E B }<< (bind' e' v')).

Record semEffSig Σ `{probeffRGS Σ} := SemEffSig {
  semEffSig_car :> (valRelO Σ -n> exprRelO Σ);
  semEffSig_compatible : Compatible semEffSig_car
}.
Arguments SemEffSig {_} {_} _%I {_}.
Arguments semEffSig_car {_} {_} _ : simpl never.
Declare Scope semEffSig_scope.
Bind Scope semEffSig_scope with semEffSig.
Delimit Scope semEffSig_scope with semEffSig.
Existing Instance semEffSig_compatible.

Section semEffSig_ofe.
  Context `{probeffRGS Σ}.
  Instance semEffSig_equiv : Equiv (semEffSig Σ) := λ E F, ∀ A e₁ e₂,
    (e₁ <<{ semEffSig_car E A }<< e₂) ≡ (e₁ <<{ semEffSig_car F A }<< e₂).
  Instance semEffSig_dist : Dist (semEffSig Σ) := λ n E F, ∀ A e₁ e₂,
    (e₁ <<{ semEffSig_car E A }<< e₂) ≡{n}≡ (e₁ <<{ semEffSig_car F A }<< e₂).
  Lemma semEffSig_ofe_mixin : OfeMixin (semEffSig Σ).
  Proof. by apply (iso_ofe_mixin (semEffSig_car : semEffSig Σ → _)). Qed.
  Canonical Structure semEffSigO := Ofe (semEffSig Σ) semEffSig_ofe_mixin.
  Global Instance semEffSig_cofe : Cofe semEffSigO.
  Proof.
    apply (iso_cofe_subtype' (λ E : valRelO Σ -n> exprRelO Σ,
      Compatible E) (@SemEffSig _ _) semEffSig_car)=>//.
    - apply _.
    - apply bi.limit_preserving_entails; [done|]; solve_proper.
  Qed.
  Global Instance semEffSig_car_ne n : Proper (dist n ==> dist n) semEffSig_car.
  Proof. solve_proper. Qed.
  Global Instance semEffSig_car_proper : Proper ((≡) ==> (≡)) semEffSig_car.
  Proof. solve_proper. Qed.
End semEffSig_ofe.

Arguments semEffSigO : clear implicits.


Section compatibility.
  Context `{probeffRGS Σ}.

  (* Auxiliar lemma. *)
  Lemma refines_app e1 e2 e1' e2' A E B :
    let C := expr_refines E B in

    e1 <<{ expr_refines noEffs (A → C) }<< e1' -∗
      e2 <<{ expr_refines noEffs A }<< e2' -∗
        (App e1 e2) <<{ C }<< (App e1' e2').
  Proof.
    simpl.
    iIntros "He1 He2".
    iApply (Ectxi_refines_pure_bind (AppRCtx _) (AppRCtx _) with "He2").
    iIntros (v2 v2') "Hv2".
    iApply (Ectxi_refines_pure_bind (AppLCtx _) (AppLCtx _) with "He1").
    iIntros (v1 v1') "Hv1". simpl.
    by iApply "Hv1".
  Qed.

  (* Recursive functions values -- corresponding to the rule [RecV_typed]. *)
  Lemma refines_recV f x e e' A E B :
    □ (∀ (v v' w w' : val),
         (A → (expr_refines E B))%valRel v v' -∗
           A w w' -∗
             (subst' x w  (subst' f v  e )) <<{ expr_refines E B }<<
             (subst' x w' (subst' f v' e'))) -∗
        (A → (expr_refines E B))%valRel (RecV f x e)
                                        (RecV f x e').
  Proof.
    iIntros "#He".
    iLöb as "IH".
    iIntros (v v') "!# #Hv".
    iApply refines_pure_r; [by apply pure_prim_step_beta|].
    iApply refines_pure_l; [by apply pure_prim_step_beta|].
    iNext.
    by iApply "He".
  Qed.

  (* Recursive functions -- corresponding to the rule [Rec_typed]. *)
  Lemma refines_rec f x e e' A E B :
    let C := expr_refines E B in

    □ (∀ (v v' w w' : val),
         (A → (expr_refines E B))%valRel v v' -∗
           A w w' -∗
             (subst' x w  (subst' f v  e )) <<{ C }<<
             (subst' x w' (subst' f v' e'))) -∗

         (rec: f x := e)%E <<{ expr_refines noEffs (A → C) }<<
         (rec: f x := e').
  Proof.
    simpl.
    iIntros "#He".
    iApply refines_pure_l; [by apply pure_prim_step_rec|].
    iApply refines_pure_r; [by apply pure_prim_step_rec|].
    iNext.
    iApply refines_ret; try done.
    by iApply refines_recV.
  Qed.

  (* Reference allocation -- corresponding to the rule [Alloc_typed]. *)
  Lemma refines_alloc e e' A :
    e <<{ expr_refines noEffs A }<< e' -∗
      (Alloc e) <<{ expr_refines noEffs (ref A) }<< (Alloc e').
  Proof.
    iIntros "He".
    iApply (Ectxi_refines_pure_bind (AllocNRCtx _) (AllocNRCtx _) with "He").
    iIntros (v v') "#HA". simpl.
    iApply (refines_alloc_l []). iNext. iIntros (l) "Hl".
    iApply (refines_alloc_r []). iIntros (l') "Hl'".
    iIntros (K K') "HKK'". rewrite obs_refines_eq.
    iIntros (ε) "Hj". iIntros "Herr". iIntros (Hpos).
    iApply fupd_ewp.
    iMod (inv_alloc (logN .@ "ref" .@ (l,l')) _
      (∃ v v', l ↦ v ∗ l' ↦ₛ v' ∗ A v v')%I with "[Hl Hl']") as "#Hinv".
    { iNext. iExists v, v'. by iFrame. }
    iDestruct "HKK'" as "[Hval _]".
    iSpecialize ("Hval" $! #l #l' with "[]"); [by iExists l, l'; auto|].
    rewrite obs_refines_eq.
    by iApply ("Hval" with "[$][$]").
  Qed.

  (* Read instruction -- corresponding to the rule [Load_typed]. *)
  Lemma refines_load e e' A :
    e <<{ expr_refines noEffs (ref A) }<< e' -∗
      (Load e) <<{ expr_refines noEffs A }<< (Load e').
  Proof.
    iIntros "He".
    iApply (Ectxi_refines_pure_bind LoadCtx LoadCtx with "He").
    iIntros (v v') "#HA". simpl.
    iIntros (K K') "HKK'". rewrite obs_refines_eq.
    iIntros (ε) "Hj". iIntros "Herr". iIntros (Hpos).
    iApply (ewp_pure_bind K); [done|].
    iDestruct "HA" as (l l') "(->&->&#Hinv)".
    set E := logN.@"ref".@(l,l').
    iApply (ewp_atomic _ (⊤ ∖ ↑E)).
    iInv E as (w w') "[>Hl [>Hl' #Hw]]" "Hclose"; simpl.
    iModIntro.
    iApply spec_update_ewp.
    tp_load. iModIntro.
    iApply (ewp_load with "Hl").
    iModIntro. 
    iIntros "Hl".
    iMod ("Hclose" with "[Hl Hl']") as "_".
    { iNext. iExists _, _. by iFrame. }
    iModIntro.    
    iDestruct "HKK'" as "[Hval _]". rewrite obs_refines_eq.
    by iApply ("Hval" with "Hw Hj Herr").
  Qed.

  (* Write instruction -- corresponding to the rule [Store_typed]. *)
  Lemma refines_store e₁ e₂ e₁' e₂' A :
    e₁ <<{ expr_refines noEffs (ref A) }<< e₁' -∗
      e₂ <<{ expr_refines noEffs A }<< e₂' -∗
        (e₁ <- e₂)%E <<{ expr_refines noEffs () }<< (e₁' <-  e₂')%E.
  Proof.
    iIntros "He₁ He₂".
    iApply (Ectxi_refines_pure_bind (StoreRCtx _) (StoreRCtx _) with "He₂").
    iIntros (w w') "#HA". simpl.
    iApply (Ectxi_refines_pure_bind (StoreLCtx _) (StoreLCtx _) with "He₁").
    iIntros (_l _l') "H". iDestruct "H" as (l l') "(->&->&#Hinv)". simpl.
    iIntros (K K') "HKK'". rewrite obs_refines_eq.
    iIntros (ε) "Hj". iIntros "Herr". iIntros (Hpos).
    iApply (ewp_pure_bind K); [done|].
    set E := logN.@"ref".@(l,l').
    iApply (ewp_atomic _ (⊤ ∖ ↑E)).
    iInv E as (v v') "[>Hl [>Hl' #Hw]]" "Hclose"; iModIntro; simpl.
    tp_store. ewp_store. simpl.
    ewp_value_head.
    iMod ("Hclose" with "[Hl Hl']") as "_".
    { by iExists w, w'; iFrame. }
    iDestruct "HKK'" as "[Hval _]". rewrite obs_refines_eq.
    by iApply ("Hval" with "[] Hj Herr").
  Qed. 

  (* Bind -- corresponding to the rule [Bind_typed]. *)
  Lemma refines_bind' e₁ e₂ e₁' e₂' A E `{Compatible Σ E} B :
    e₁ <<{ expr_refines E A }<< e₁' -∗
      e₂ <<{ expr_refines noEffs (A → (expr_refines E B)) }<< e₂' -∗
        (bind' e₁ e₂) <<{ expr_refines E B }<< (bind' e₁' e₂').
  Proof.
    iIntros "He1 He2".
    iApply (Ectxi_refines_pure_bind (AppRCtx _) (AppRCtx _) with "He2").
    iIntros (w w') "#HB //=".
    set K  := ([AppRCtx bind'; AppLCtx w]).
    set K' := ([AppRCtx bind'; AppLCtx w']).
    iApply (refines_bind K K' with "He1").
    iSplit.
    { iIntros (v v') "#HA //=".
      iApply (refines_pure_r' _ _ (w' v')%E);[
      unfold bind'; by tactics.solve_pure_steps|].
      iApply (refines_pure_l' _ (w v)%E);[
      unfold bind'; by tactics.solve_pure_steps|].
      iNext. simpl. by iApply "HB".
    }
    { iIntros (s s') "HE //=".
      by iApply (compatible with "[] [HE]"); [|iApply "HE"].
    }
  Qed.

    
  (* Return -- corresponding to the rule [Return_typed]. *)
  Lemma refines_return' e₁ e₁' E A :
    e₁ <<{ expr_refines noEffs A }<< e₁' -∗
      (Ret e₁) <<{ expr_refines E A }<< (Ret e₁').
  Proof.
    iIntros "He".
    iApply (refines_pure_bind [] [] with "He").
    iIntros (v v') "HA". by iApply refines_ret.
  Qed.

  (* TODO: Generalize arbitrary rows  *)
  Lemma refines_perform l1 l2 e1 e2 A1 A2 :
    e1 <<{ expr_refines (eff_refines [((l1,l2), (A1, A2))] [((l1, l2), (A1, A2))]) A1 }<< e2 -∗
      (perform #l1 e1) <<{ expr_refines (eff_refines [((l1,l2), (A1, A2))] [((l1, l2), (A1, A2))]) A2 }<< (perform #l2 e2).
  Proof.
    iIntros "He".
    unfold perform.
    iApply (refines_bind [AppRCtx _] [AppRCtx _] with "[$He]").
    iLöb as "IH".
    iSplit.
    - iClear "IH".
      iIntros (v1 v2) "#Hvv". simpl.
      iApply (refines_pure_r' _ _ (Eff (#l2, v2) [])%E); [by tactics.solve_pure_steps|].
      iApply (refines_pure_l' _ (Eff (#l1, v1) [])%E); [by tactics.solve_pure_steps|].
      iModIntro.
      iApply refines_eff.
      rewrite eff_refines_unfold.
      iExists l1, l2, v1, v2, [], [].
      repeat (try (iSplit; [iPureIntro; (apply _ || done)|])).
      iLeft.
      repeat (try (iSplit; [iPureIntro; (apply _ || done)|])).
      iFrame "Hvv". iIntros "!#" (w w') "#Hw". iNext. simpl.
      iIntros (K K') "HK". 
      iDestruct "HK" as "[HK _]".
      by iApply ("HK" with "Hw").
    - iIntros (s s') "Heff". simpl.
      rewrite {2} eff_refines_unfold.
      iDestruct "Heff" as (l1' l2' v1 v2 N1 N2)  "(-> & -> & %HN1 & %HN2 & [(<- & <- & #Hvv & #Hcont) | H])". 
      + iApply (refines_pure_r' _ _ (Eff (#l2, v2) _)); [by tactics.solve_pure_steps|].
        iApply (refines_pure_l' _ (Eff (#l1, v1) _)); [by tactics.solve_pure_steps|].
        iModIntro.
        iApply refines_eff. 
        rewrite (eff_refines_unfold _ _ A2).
        iExists l1, l2, v1, v2, (N1 ++ [AppRCtx ((λ: "l" "v", do:("l", "v"))%V #l1)]), (N2 ++ [AppRCtx ((λ: "l" "v", do:("l", "v"))%V #l2)]).
        repeat (try (iSplit; [iPureIntro; (apply _ || done)|])).
        iSplit. { iPureIntro. apply ectx_app_neutral; [done|]. apply ConsCtx_neutral; [apply AppRCtx_neutral|apply EmptyCtx_neutral].}
        iSplit. { iPureIntro. apply ectx_app_neutral; [done|]. apply ConsCtx_neutral; [apply AppRCtx_neutral|apply EmptyCtx_neutral].}
        iLeft.
        repeat (try (iSplit; [iPureIntro; (apply _ || done)|])).
        iFrame "Hvv".
        iModIntro.
        iIntros (w1 w2) "Hww".
        iDestruct ("Hcont" with "Hww") as "Hfill". iNext.
        do 2rewrite fill_app.
        iApply (refines_bind with "[$Hfill]"). simpl.
        iApply "IH".
      + iClear "IH".
        iApply refines_pure_l'; [ by tactics.solve_pure_steps|]. iModIntro. iExFalso.
        rewrite eff_refines_unfold. 
        iDestruct "H" as (??????????) "$".
  Qed.

  Lemma refines_perform_general l1 l2 e1 e2 A1 A2 (ρ ρ' : list (sig_type Σ)) :
    (((l1,l2), (A1, A2)) : sig_type Σ) ∈ ρ →
    e1 <<{ expr_refines (eff_refines ρ' ρ') A1 }<< e2 -∗
    (perform #l1 e1) <<{ expr_refines (eff_refines ρ ρ') A2}<< (perform #l2 e2).
  Proof.
    iIntros (Hin) "He".
    unfold perform.
    iApply (refines_bind [AppRCtx _] [AppRCtx _] with "[$He]").
    iLöb as "IH".
    iSplit.
    - iClear "IH".
      iIntros (v1 v2) "#Hvv". simpl.
      iApply (refines_pure_r' _ _ (Eff (#l2, v2) [])%E); [by tactics.solve_pure_steps|].
      iApply (refines_pure_l' _ (Eff (#l1, v1) [])%E); [by tactics.solve_pure_steps|].
      iModIntro.
      iApply refines_eff.
      rewrite eff_refines_unfold.
      iExists l1, l2, v1, v2, [], [].
      repeat (try (iSplit; [iPureIntro; (apply _ || done)|])).
      induction Hin as [((l1',l2'), (A1', A2')) ρ'' Hin' | IH ].
      { iLeft. admit. }
      


      iInduction ρ as (IH).
      iLeft.
      repeat (try (iSplit; [iPureIntro; (apply _ || done)|])).
      iFrame "Hvv". iIntros "!#" (w w') "#Hw". iNext. simpl.
      iIntros (K K') "HK". 
      iDestruct "HK" as "[HK _]".
      by iApply ("HK" with "Hw").

  (* Effect abstraction -- corresponding to the rule [TLam_typed]. *)
  Lemma refines_tlam e e' (C : semEffSig Σ → valRel Σ) :
    □ (∀ (R : semEffSig Σ),
         e <<{ expr_refines noEffs (C R) }<< e') -∗
     (Λ: e)%E <<{ expr_refines noEffs (∀ R, C R)%valRel }<< (Λ: e')%E.
  Proof.
    iIntros "#Hee'".
    iApply refines_pure_r; [apply pure_prim_step_rec|].
    iApply refines_pure_l; [apply pure_prim_step_rec|].
    iNext. iApply refines_ret.
    iIntros (R) "!#". iIntros (v1 v2) "[-> ->]".
    iApply refines_pure_r; [apply pure_prim_step_beta|].
    iApply refines_pure_l; [apply pure_prim_step_beta|].
    iNext. simpl. by iApply "Hee'".
  Qed.

  Lemma refines_tlamV e e' (C : semEffSig Σ → valRel Σ) :
    □ (∀ (R : semEffSig Σ),
         e <<{ expr_refines noEffs (C R) }<< e') -∗
    (∀ R, C R)%valRel (Λ: e)%V (Λ: e')%V.
  Proof.
    iIntros "#Hee'" (R) "!#". iIntros (??) "[-> ->]".
    iApply refines_pure_r; [apply pure_prim_step_beta|].
    iApply refines_pure_l; [apply pure_prim_step_beta|].
    by iApply "Hee'".
  Qed.

  (* Effect application -- corresponding to the rule [TApp_typed]. *)
  Lemma refines_tapp e e' (C : semEffSig Σ → valRel Σ) (R : semEffSig Σ) :
   e <<{ expr_refines noEffs (∀ R, C R)%valRel }<< e' -∗
     (e <_>) <<{ expr_refines noEffs (C R) }<< (e' <_>).
  Proof.
    iIntros "Hee'".
    set Ki := AppLCtx #().
    iApply (Ectxi_refines_pure_bind Ki Ki  with "Hee'").
    iIntros (v v') "Hvv'". by iApply "Hvv'".
  Qed.

  (* Shallow handler -- no corresponding typing rule :( *)
  Lemma refines_try_with e e' h h' r r' A1 A2 A F B :
    let E := eff_refines A1 A2 in
    let A' := expr_refines E A in
    let B' := expr_refines F B in

    e <<{ A' }<< e' -∗

      (h <<{ expr_refines noEffs (A1 → (expr_refines noEffs ((A2 → A') → B'))) }<< h' ∧

       r <<{ expr_refines noEffs (A → B') }<< r') -∗

         (TryWith e  h  r) <<{ B' }<< (TryWith e' h' r').

  Proof.
    set K  := [TryWithCtx h  r ].
    set K' := [TryWithCtx h' r'].
    simpl.
    iIntros "He Hhr".
    iApply (refines_bind K K' with "He"); iSplit.
    { iDestruct "Hhr" as "[_ Hr]".
      iIntros (v v') "#HAv". unfold K, K'. simpl.
      iApply refines_pure_l; [by apply pure_prim_step_try_with_val|].
      iApply refines_pure_r; [by apply pure_prim_step_try_with_val|].
      iNext.
      iApply (Ectxi_refines_pure_bind (AppLCtx _) (AppLCtx _) with "Hr").
      iIntros (rv rv') "#Hrv".
      by iApply "Hrv".
    }
    { iDestruct "Hhr" as "[Hh _]".
      iIntros (s s'). rewrite eff_refines_unfold.
      iIntros "H".
      iDestruct "H" as (y y' N N') "(%&%&->&->&#HA1&#HN)". unfold K, K'. simpl.
      iApply refines_pure_l; [by apply pure_prim_step_try_with_eff|].
      iApply refines_pure_r; [by apply pure_prim_step_try_with_eff|].
      iNext.
      iApply (refines_app with "[Hh]").
      { iApply (refines_app with "Hh"). by iApply refines_ret. }
      iApply refines_ret; try done.
      iIntros (w w') "!# HA2".
      iSpecialize ("HN" with "HA2").
      iApply refines_pure_l; [by apply pure_prim_step_cont|].
      iApply refines_pure_r; [by rewrite fill_not_eff|
                              by apply pure_prim_step_cont|].
      by iApply "HN".
    }
  Qed.

  (* Deep handler -- corresponding to the rule [Deep_try_with_typed]. *)
  Lemma refines_deep_try_with e e' h h' r r' A1 A2 A F B :
    let E := eff_refines A1 A2 in
    let A' := expr_refines E A in
    let B' := expr_refines F B in

    e <<{ A' }<< e' -∗

       h <<{ expr_refines noEffs (A1 → (expr_refines noEffs ((A2 → B') → B'))) }<< h' -∗

       r <<{ expr_refines noEffs (A → B') }<< r' -∗

         (DeepTryWith e  h  r) <<{ B' }<< (DeepTryWith e' h' r').

  Proof.
    simpl.
    iIntros "He Hh Hr".
    iApply (Ectxi_refines_pure_bind (AppRCtx _) (AppRCtx _) with "Hr").
    iIntros (rv rv') "#Hrv".
    iApply (refines_pure_bind ([AppRCtx _; AppLCtx _]) ([AppRCtx _; AppLCtx _]) with "Hh").
    iIntros (hv hv') "#Hhv". simpl.
    iLöb as "IH" forall (e e').
    iApply (refines_pure_l' _ (TryWith e _ _)).
    { unfold deep_try_with. by tactics.solve_pure_steps. }
    iApply (refines_pure_r' _ _ (TryWith e' _ _ )).
    { unfold deep_try_with. by tactics.solve_pure_steps. }
    iNext.
    iApply (refines_try_with with "He"); iSplit; [|by iApply refines_ret].
    iApply refines_rec.
    iIntros "!#" (v v' y y') "_ #Hy". simpl. clear v v'.
    iApply refines_rec.
    iIntros "!#" (v v' k k') "_ #Hk". simpl. clear v v'.
    iApply refines_app; [by iApply "Hhv"|].
    iApply refines_rec.
    iIntros "!#" (v v' w w') "_ #Hw". simpl. clear v v'.
    iApply "IH". by iApply "Hk".
  Qed.

    
End compatibility.


Section eff_refines.
  Context `{probeffRGS Σ}.

  Global Instance eff_refines_compatible A1 A2 : Compatible (eff_refines A1 A2).
  Proof.
    rewrite /Compatible.
    iIntros (A B s s' v v') "#Hvv' Hee'".
    rewrite (eff_refines_unfold _ _ A).
    iLöb as "IH" forall (s s').
    iDestruct "Hee'" as (y y' N N') "(% & % & -> & -> & #HA1 & #HN)".
    iApply (refines_pure_r' _ _ (Eff y' _)).
    { unfold bind'. by tactics.solve_pure_steps. }
    iApply (refines_pure_l' _ (Eff y _)).
    { unfold bind'. by tactics.solve_pure_steps. }
    iNext.
    iApply refines_eff.
    set K  := ((N ++ [AppRCtx bind']) ++ [AppLCtx v]).
    set K' := ((N' ++ [AppRCtx bind'])++ [AppLCtx v']).
    iApply (eff_refines_intro _ _ _ _ _ K K' with "HA1"); [done|done| | |].
    { repeat (apply ectx_app_neutral); eauto; apply ConsCtx_neutral; try apply EmptyCtx_neutral; eauto using AppRCtx_neutral, AppLCtx_neutral. }
    { repeat (apply ectx_app_neutral); eauto; apply ConsCtx_neutral; try apply EmptyCtx_neutral; eauto using AppRCtx_neutral, AppLCtx_neutral. }
    iModIntro. iIntros (w w') "HA2".
    unfold K, K'. iSpecialize ("HN" with "HA2"). iNext. simpl.
    clear K K'.
    set K  := ([AppRCtx bind'; AppLCtx v]).
    set K' := ([AppRCtx bind'; AppLCtx v']).
    do 2rewrite -app_assoc. rewrite -fill_app_ctx. rewrite -(fill_app_ctx _ N').
    iApply (refines_bind K K' with "HN"); iSplit.
    { clear w w'.
      iIntros (w w') "#HA //=".
      iApply (refines_pure_r' _ _ (v' w')%E);[
      unfold bind'; by tactics.solve_pure_steps|].
      iApply (refines_pure_l' _ (v w)%E);[
      unfold bind'; by tactics.solve_pure_steps|].
      iNext. simpl. by iApply "Hvv'".
    }
    { iIntros (s s') "Hs".
      rewrite (eff_refines_unfold _ _ A).
      by iApply "IH".
    }
  Qed.

  Definition eff_refines' (A1 A2 : valRel Σ) : semEffSig Σ :=
    SemEffSig (eff_refines A1 A2).

  Global Instance eff_refines_ne' n :
    Proper ((dist n) ==> (dist n) ==> (dist n)) eff_refines'.
  Proof.
    intros A1 A1' HA1 A2 A2' HA2.
    unfold eff_refines'.
    intros A e1 e2. rewrite {1 2}/semEffSig_car /=.
    by solve_proper.
  Qed.
  Global Instance eff_refines_proper' :
    Proper ((≡) ==> (≡) ==> (≡)) eff_refines'.
  Proof.
    intros ??? ???. apply equiv_dist=>n.
    by apply eff_refines_ne'; try apply equiv_dist.
  Qed.
p  Global Instance semEffSigRel_inhabited : Inhabited (semEffSig Σ) :=
    populate (eff_refines' ()%valRel ()%valRel).

End eff_refines.
