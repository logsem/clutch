From iris.proofmode Require Import base proofmode environments.
From clutch.prob_eff_lang.probblaze Require Import logic sem_sig sem_row sem_types sem_def syntax mode.
From clutch.prob_eff_lang.probblaze.typing Require Import types interp interp_simp.

(** * Bridge from syntactic mirrors to semantic interface types
      (PLAN.md, Stage E)

    [sem_ty_le_struct] proves goals [⊢ τsem ≤ₜ interp._ty η μ δ T ξ] where
    [T] is a syntactic mirror of the semantic type [τsem], by structural
    decomposition with [ty_le_row_forall], [ty_le_type_forall],
    [ty_le_mode_forall], [ty_le_exists], [ty_le_arr], [ty_le_prod],
    [ty_le_sum], [ty_le_ref] and [ty_le_mbang_comp].

    - The structure is read off whichever side is a semantic type former
      after [interp_simp]; the interpretation side always is one, the other
      side may be a folded definition ([τ_CHAN], [τ__F …], [sem_ty_option
      …]), which unification unfolds when a rule is applied.  So the
      semantic interface type need not be unfolded by hand; the syntactic
      mirror ([T_SCHAN] …) is unfolded by the tactic ([interp_unfold_head]).
    - Rows are closed by [row_le_refl], modes by [mode_le_refl],
      [mode_le_MS] or [mode_le_OS] (all up to conversion).
    - A leaf (no rule applies) is closed by [ty_le_refl] (up to
      conversion) or by the user tactic [leaf]: [sem_ty_le_struct using
      leaf] runs [leaf] first on the goal [A ≤ₜ B] and then on the pointwise
      goal [A v1 v2 -∗ B v1 v2] obtained by [iIntros (??) "!#"], so lemmas
      in the style of [τG_subtype] ([sem_ty_group v1 v2 ⊢ interp._ty …
      τG ξ v1 v2]) are used as [iApply τG_subtype].
    - Leaves that nothing closes, rows and modes that are not closed by
      reflexivity, are left to the user, in this order, as [≤ₜ], [≤ᵣ] and
      [≤ₘ] goals. *)

(** ** Unfolding the head of a syntactic mirror *)

(** Replace each [interp._ty _ _ _ T _] whose [T] is not headed by a
    constructor (a [Definition] such as [T_SCHAN]) by its head normal
    form.  Leaves such as [τG] (a projection of a section variable) do not
    reduce and are kept. *)
Ltac interp_unfold_head :=
  repeat match goal with
  | |- context [interp._ty _ _ _ ?T] =>
      lazymatch T with
      | TBot => fail | TTop => fail | TUnit => fail | TBool => fail
      | TInt => fail | TNat => fail | TTape => fail
      | TRef _ => fail | TRefC _ => fail | TProd _ _ => fail
      | TSum _ _ => fail | TBang _ _ => fail | TArrow _ _ _ => fail
      | TForallM _ => fail | TForallR _ => fail | TForallT _ => fail
      | TExists _ => fail | TRec _ => fail | TVar _ => fail
      | _ => let T' := eval hnf in T in
             assert_fails (constr_eq T T');
             change T with T'
      end
  end.

(** [iApply] postpones unification constraints to the end of the sentence,
    where a failure is no longer caught by [first]/[try]/[match]; force them
    at once so that a rule that does not fit fails where it is tried. *)
Ltac sem_iapply lem := iApply lem; solve_constraints.

(** ** Rows and modes *)
Ltac sem_row_le_struct :=
  interp_simp; try (sem_iapply row_le_refl; done).

Ltac sem_mode_le_struct :=
  interp_simp;
  first [ sem_iapply mode_le_refl | sem_iapply mode_le_MS | sem_iapply mode_le_OS | idtac ].

(** ** Leaves *)
Ltac sem_ty_le_leaf leaf :=
  first [ sem_iapply ty_le_refl
        | lazymatch goal with |- envs_entails _ (ty_le ⊥ _) => sem_iapply ty_le_bot end
        | solve [leaf]
        | solve [iIntros (??) "!#"; leaf]
        | idtac ].

(** ** The structural recursion *)
Ltac sem_ty_le_go leaf :=
  interp_simp; cbv beta;
  match goal with
  | |- envs_entails _ (ty_le ?A ?A) => sem_iapply ty_le_refl
  (* binders *)
  | |- envs_entails _ (ty_le _ (sem_ty_row_forall _)) => sem_ty_le_rforall leaf
  | |- envs_entails _ (ty_le (sem_ty_row_forall _) _) => sem_ty_le_rforall leaf
  | |- envs_entails _ (ty_le _ (sem_ty_type_forall _)) => sem_ty_le_tforall leaf
  | |- envs_entails _ (ty_le (sem_ty_type_forall _) _) => sem_ty_le_tforall leaf
  | |- envs_entails _ (ty_le _ (sem_ty_mode_forall _)) => sem_ty_le_mforall leaf
  | |- envs_entails _ (ty_le (sem_ty_mode_forall _) _) => sem_ty_le_mforall leaf
  | |- envs_entails _ (ty_le _ (sem_ty_exists _)) => sem_ty_le_exists leaf
  | |- envs_entails _ (ty_le (sem_ty_exists _) _) => sem_ty_le_exists leaf
  (* modalities *)
  | |- envs_entails _ (ty_le _ (sem_ty_mbang _ _)) => sem_ty_le_mbang leaf
  | |- envs_entails _ (ty_le (sem_ty_mbang _ _) _) => sem_ty_le_mbang leaf
  (* type formers *)
  | |- envs_entails _ (ty_le _ (sem_ty_arr _ _ _)) => sem_ty_le_arr leaf
  | |- envs_entails _ (ty_le (sem_ty_arr _ _ _) _) => sem_ty_le_arr leaf
  | |- envs_entails _ (ty_le _ (sem_ty_prod _ _)) => sem_ty_le_prod leaf
  | |- envs_entails _ (ty_le (sem_ty_prod _ _) _) => sem_ty_le_prod leaf
  | |- envs_entails _ (ty_le _ (sem_ty_sum _ _)) => sem_ty_le_sum leaf
  | |- envs_entails _ (ty_le (sem_ty_sum _ _) _) => sem_ty_le_sum leaf
  | |- envs_entails _ (ty_le _ (sem_ty_ref _)) => sem_ty_le_ref leaf
  | |- envs_entails _ (ty_le (sem_ty_ref _) _) => sem_ty_le_ref leaf
  (* leaves *)
  | |- envs_entails _ (ty_le _ _) => sem_ty_le_leaf leaf
  | |- _ => idtac
  end
with sem_ty_le_rforall leaf :=
  sem_iapply ty_le_row_forall; iIntros (?); sem_ty_le_go leaf
with sem_ty_le_tforall leaf :=
  sem_iapply ty_le_type_forall; iIntros (?); sem_ty_le_go leaf
with sem_ty_le_mforall leaf :=
  sem_iapply ty_le_mode_forall; iIntros (?); sem_ty_le_go leaf
with sem_ty_le_exists leaf :=
  sem_iapply ty_le_exists; iIntros (?); sem_ty_le_go leaf
with sem_ty_le_mbang leaf :=
  sem_iapply ty_le_mbang_comp; [sem_mode_le_struct | sem_ty_le_go leaf]
with sem_ty_le_arr leaf :=
  sem_iapply ty_le_arr; [sem_row_le_struct | sem_ty_le_go leaf | sem_ty_le_go leaf]
with sem_ty_le_prod leaf :=
  sem_iapply ty_le_prod; [sem_ty_le_go leaf | sem_ty_le_go leaf]
with sem_ty_le_sum leaf :=
  sem_iapply ty_le_sum; [sem_ty_le_go leaf | sem_ty_le_go leaf]
with sem_ty_le_ref leaf :=
  sem_iapply ty_le_ref; sem_ty_le_go leaf.

Tactic Notation "sem_ty_le_struct" "using" tactic3(leaf) :=
  iStartProof; interp_unfold_head; sem_ty_le_go ltac:(leaf).
Tactic Notation "sem_ty_le_struct" :=
  sem_ty_le_struct using fail.

(** ** Smoke tests *)
Section tests.
  Context `{!probblazeRGS Σ}.

  Local Definition T_test : type :=
    (∀R: ((ℕ -{ RVar 0%nat }-> ()) * (() -{ RVar 0%nat }-> (() + ℤ)))
           -{ RVar 0%nat }-∘ ())%ty.

  Local Definition τ_test : sem_ty Σ :=
    (∀ᵣ θ, ((sem_ty_nat -{ θ }-> 𝟙) × (𝟙 -{ θ }-> Option ℤ)) -{ θ }-∘ 𝟙)%T.

  Goal ∀ η μ δ ξ, ⊢ τ_test ≤ₜ interp._ty η μ δ T_test ξ.
  Proof. intros. sem_ty_le_struct. Qed.

  (* The other direction: every rule is symmetric. *)
  Goal ∀ η μ δ ξ, ⊢ interp._ty η μ δ T_test ξ ≤ₜ τ_test.
  Proof. intros. sem_ty_le_struct. Qed.

  (* A leaf closed by a pointwise user lemma, as with [τG_subtype]. *)
  Goal ∀ η μ δ ξ (τ : sem_ty Σ) (T : type),
    (∀ v1 v2 ξ', τ v1 v2 ⊢ interp._ty η μ δ T ξ' v1 v2) →
    ⊢ (∀ᵣ θ, 𝟙 -{ θ }-> Option τ)%T ≤ₜ interp._ty η μ δ (∀R: () -{ RVar 0%nat }-> (() + T))%ty ξ.
  Proof. intros η μ δ ξ τ T H. sem_ty_le_struct using (iApply H). Qed.
End tests.
