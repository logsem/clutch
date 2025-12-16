(* sem_types.v *)

(* This file contains the definition of semantic types *)

From iris.proofmode Require Import base tactics.
From iris.algebra Require Import ofe list.
From iris.base_logic Require Export iprop upred invariants.

(* Local imports *)
From clutch.prob_eff_lang.probblaze Require Import logic notation sem_def mode sem_sig sem_row.

(* Base types. *)
Definition sem_ty_bot {Σ} : sem_ty Σ := (λ v1 v2, False)%I.

Global Instance sem_ty_bot_instance {Σ} : Bottom (sem_ty Σ) := sem_ty_bot. 

Definition sem_ty_unit {Σ} : sem_ty Σ := (λ v1 v2, ⌜ v1 = #()%V ∧ v2 = #()%V ⌝ )%I.
Definition sem_ty_bool {Σ} : sem_ty Σ := (λ v1 v2, ∃ b : bool, ⌜ v1 = #b ∧ v2 = #b ⌝)%I.
Definition sem_ty_nat {Σ} : sem_ty Σ := (λ v1 v2, ∃ n : nat, ⌜ v1 = #n ∧ v2 = #n ⌝)%I.
Definition sem_ty_int {Σ} : sem_ty Σ := (λ v1 v2, ∃ n : Z, ⌜ v1 = #n ∧ v2 = #n ⌝)%I.
Definition sem_ty_top {Σ} : sem_ty Σ := (λ v1 v2, True)%I.

Global Instance sem_ty_top_instance {Σ} : Top (sem_ty Σ) := sem_ty_top. 
Global Instance sem_ty_inhabited {Σ} : Inhabited (sem_ty Σ) := populate sem_ty_top. 

Definition sem_ty_mbang {Σ} (m : mode) (τ : sem_ty Σ) : sem_ty Σ := (λ v1 v2, □? m (τ v1 v2))%I.

Definition logN : namespace := nroot .@ "logN".
(* Both tapes are empty and are sampled from the same distribution *)
Definition sem_ty_tape `{probblazeGS Σ} : sem_ty Σ :=
  (λ w1 w2,
     ∃ (α1 α2 : loc) (N: nat), ⌜w1 = #lbl:α1⌝ ∧ ⌜w2 = #lbl:α2⌝ ∧
                               inv (logN .@ (α1, α2)) (α1 ↪ (N; []) ∗ α2 ↪ₛ (N; [])))%I.

(* Copyable Reference Type *)
Definition tyN := nroot .@ "ty".
Definition sem_ty_ref_cpy `{!probblazeGS Σ} (τ : sem_ty Σ): sem_ty Σ := 
  (λ v1 v2, ∃ l1 l2 : loc, ⌜ v1 = #l1 ⌝ ∗ ⌜ v2 = #l2 ⌝ ∗ inv (tyN .@ (l1,l2)) (∃ w1 w2, l1 ↦ w1 ∗ l2 ↦ₛ w2 ∗ τ w1 w2))%I.

(* Substructural Reference Type *)
Definition sem_ty_ref `{!probblazeGS Σ} (τ : sem_ty Σ): sem_ty Σ := 
  (λ v1 v2, ∃ l1 l2 : loc, ⌜ v1 = #l1 ⌝ ∗ ⌜ v2 = #l2 ⌝ ∗ (∃ w1 w2, l1 ↦ w1 ∗ l2 ↦ₛ w2 ∗ τ w1 w2))%I.

(* Product type. *)
Definition sem_ty_prod {Σ} (τ κ : sem_ty Σ) : sem_ty Σ := 
  (λ v1 v2, ∃ w1 w1' w2 w2', ⌜v1 = (w1, w2)%V⌝ ∗ ⌜ v2 = (w1', w2')%V ⌝ ∗ τ w1 w1' ∗ κ w2 w2')%I.

(* Sum type. *)
Definition sem_ty_sum {Σ} (τ κ : sem_ty Σ) : sem_ty Σ :=
  (λ v1 v2, ∃ w1 w2, (⌜v1 = InjLV w1%V⌝ ∗ ⌜v2 = InjLV w2%V⌝ ∗ τ w1 w2) ∨(⌜v1 = InjRV w1%V⌝ ∗ ⌜v2 = InjRV w2%V⌝ ∗ κ w1 w2))%I.

(* Arrow type. *)
Definition sem_ty_arr `{probblazeRGS Σ} 
  (ρ : sem_row Σ)
  (τ : sem_ty Σ)
  (κ : sem_ty Σ) : sem_ty Σ :=
  (λ (v1 v2 : val),
    ∀ (w1 w2 : val),
      τ w1 w2 -∗ BREL (v1 w1) ≤ (v2 w2) <| ρ |> {{ (λ u1 u2, κ u1 u2) }})%I.

(* Polymorphic type. *)
Definition sem_ty_type_forall {Σ} 
  (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ := (λ v1 v2, ∀ τ, C τ v1 v2)%I.

(* Polymorphic effect type. *)
Definition sem_ty_row_forall {Σ} 
  (A : sem_row Σ → sem_ty Σ) : sem_ty Σ := (λ v1 v2, ∀ θ, A θ v1 v2)%I.

(* Polymorphic mode type. *)
Definition sem_ty_mode_forall {Σ} 
  (C : mode → sem_ty Σ) : sem_ty Σ := (λ v1 v2, ∀ m, C m v1 v2)%I.

(* Existential type. *)
Definition sem_ty_exists `{probblazeGS Σ} 
  (C : sem_ty Σ → sem_ty Σ) : sem_ty Σ := (λ v1 v2, ∃ τ, C τ v1 v2)%I.

(** Recursive types *)
Definition sem_ty_rec_pre {Σ} (C : sem_ty Σ → sem_ty Σ)
  (rec : sem_ty Σ) : sem_ty Σ := (λ v1 v2, ▷ (∃ rec', rec ≡ rec' ∧ C rec' v1 v2))%I.
Global Instance sem_ty_rec_pre_contractive {Σ} (C : sem_ty Σ → sem_ty Σ) :
  Contractive (sem_ty_rec_pre C).
Proof. solve_contractive. Qed.
Definition sem_ty_rec {Σ} (C : sem_ty Σ -d> sem_ty Σ) : sem_ty Σ :=
  fixpoint (sem_ty_rec_pre C).

(* TODO: figure out the last part of the proof *)
Lemma sem_ty_rec_unfold {Σ} (C : sem_ty Σ → sem_ty Σ) `{!NonExpansive C} v1 v2 :
  (sem_ty_rec C)%T v1 v2 ⊣⊢ ▷ C (sem_ty_rec C)%T v1 v2. 
Proof.
  rewrite {1}/sem_ty_rec.
  assert (fixpoint (sem_ty_rec_pre C) v1 v2 ≡ sem_ty_rec_pre C (fixpoint (sem_ty_rec_pre C)) v1 v2).
  { do 2 apply non_dep_fun_equiv. apply fixpoint_unfold. }
  rewrite H. iSplit.
  - iIntros "(%rec' & #Hrec & HC) !>".
      rewrite /sem_ty_rec.
      iAssert (C rec' ≡ C (fixpoint (sem_ty_rec_pre C)))%I as "#H".
      { by iRewrite "Hrec". }
      rewrite !discrete_fun_equivI. (* iRewrite - ("H" $! v1). *) admit.
  - iIntros "HC //=". iNext. iExists (sem_ty_rec C).
    by iFrame. 
Admitted.

Notation "'𝟙'" := sem_ty_unit : sem_ty_scope.
Notation "'𝔹'" := (sem_ty_bool) : sem_ty_scope.
Notation "'ℤ'" := (sem_ty_int) : sem_ty_scope.
Notation "![ m ] τ" := (sem_ty_mbang m τ) (at level 10) : sem_ty_scope.
Notation "! τ" := (sem_ty_mbang MS τ) (at level 9, τ at level 9) : sem_ty_scope.

Notation "τ '×' κ" := (sem_ty_prod τ%T κ%T) (at level 120) : sem_ty_scope.
Infix "+" := (sem_ty_sum) : sem_ty_scope.

Notation "'Ref' τ" := (sem_ty_ref τ%T) 
  (at level 50) : sem_ty_scope.

Notation "'Refᶜ' τ" := (sem_ty_ref_cpy τ%T) 
  (at level 50) : sem_ty_scope.

Notation "'∀ₜ' α , C " := (sem_ty_type_forall (λ α, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∀ᵣ' θ , C " := (sem_ty_row_forall (λ θ, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∀ₘ' ν , C " := (sem_ty_mode_forall (λ ν, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'∃ₜ' α , C " := (sem_ty_exists (λ α, C%T)) 
  (at level 180) : sem_ty_scope.

Notation "'μₜ' α , C " := (sem_ty_rec (λ α, C%T))
  (at level 180) : sem_ty_scope.

Notation "τ ⊸ κ" := (sem_ty_arr ⟨⟩%R τ%T κ%T)
  (at level 99, κ at level 200) : sem_ty_scope.

Notation "τ '-{' ρ '}-∘' κ" := (sem_ty_arr ρ%R τ%T κ%T)
  (at level 100, ρ, κ at level 200) : sem_ty_scope.

Notation "τ '-{' ρ '}-[' m ']->' κ" := (sem_ty_mbang m (sem_ty_arr ρ%R τ%T κ%T))%T
  (at level 100, m, ρ, κ at level 200) : sem_ty_scope.

Notation "τ '-[' m ']->' κ" := (sem_ty_mbang m (sem_ty_arr ⟨⟩%R τ%T κ%T))%T
  (at level 100, m, κ at level 200) : sem_ty_scope.

Notation "τ '-{' ρ '}->' κ" := (sem_ty_mbang MS (sem_ty_arr ρ%R τ%T κ%T))
  (at level 100, ρ, κ at level 200) : sem_ty_scope.

Notation "τ → κ" := (sem_ty_mbang MS (sem_ty_arr ⟨⟩%R τ%T κ%T))
  (at level 99, κ at level 200) : sem_ty_scope.

(* Derived Types *)
Definition ListF {Σ} (τ : sem_ty Σ) := (λ α, 𝟙 + (τ × α))%T.

(* List type. *)
Definition sem_ty_list {Σ} (τ : sem_ty Σ) : sem_ty Σ := 
    sem_ty_rec (ListF τ).

Notation "'List' τ" := (sem_ty_list τ%T) 
  (at level 50) : sem_ty_scope.

(* List type. *)
Definition sem_ty_option {Σ} (τ : sem_ty Σ) : sem_ty Σ := (𝟙 + τ)%T.

Notation "'Option' τ" := (sem_ty_option τ%T) 
  (at level 50) : sem_ty_scope.

(**  Prove that type formers are non-expansive and respect setoid equality. *)
Section types_properties.
  Context `{probblazeRGS Σ}.

  Implicit Types σ : sem_sig Σ.

  Ltac solve_non_expansive :=
    repeat intros ?;
    unfold sem_ty_unit, sem_ty_int, sem_ty_bool, sem_ty_mbang,
           sem_ty_prod, sem_ty_sum, sem_ty_arr,
           sem_ty_ref, sem_ty_ref_cpy, 
           sem_ty_rec, sem_ty_list, sem_ty_type_forall, sem_ty_exists;
    repeat ( done || apply non_dep_fun_dist || intros ? || f_equiv).

  Global Instance sem_ty_mbang_ne m : NonExpansive (@sem_ty_mbang Σ m).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_prod_ne : NonExpansive2 (@sem_ty_prod Σ).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_sum_ne : NonExpansive2 (@sem_ty_sum Σ).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_arr_ne : NonExpansive3 sem_ty_arr.
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_ref_ne : NonExpansive (@sem_ty_ref Σ _).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_ref_cpy_ne : NonExpansive (@sem_ty_ref_cpy Σ _).
  Proof. solve_non_expansive. Qed.

  Global Instance sem_ty_type_forall_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@sem_ty_type_forall Σ).
  Proof.
    intros ?????. unfold sem_ty_type_forall; repeat f_equiv. 
    by do 3apply non_dep_fun_dist.
  Qed.

  Global Instance sem_ty_type_forall_row_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@sem_ty_row_forall Σ).
  Proof.
    intros ?????. unfold sem_ty_row_forall; repeat f_equiv.
    by do 2 apply non_dep_fun_dist.
  Qed.

  Global Instance sem_ty_type_forall_mode_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@sem_ty_mode_forall Σ).
  Proof.
    intros ?????. unfold sem_ty_mode_forall; repeat f_equiv. 
    by do 2 apply non_dep_fun_dist.
  Qed.

  Global Instance sem_ty_exist_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) sem_ty_exists.
  Proof. 
    intros ?????. unfold sem_ty_exists; repeat f_equiv. 
    by do 2 apply non_dep_fun_dist. 
  Qed.

  Global Instance sem_ty_rec_ne :
    NonExpansive (@sem_ty_rec Σ).
  Proof.
    intros ????. unfold sem_ty_rec. apply fixpoint_ne.
    intros ???. unfold sem_ty_rec_pre. do 4 f_equiv. 
    by do 3 apply non_dep_fun_dist.
  Qed.

  Global Instance sem_ty_listF_ne τ : NonExpansive (@ListF Σ τ).
  Proof. intros ?????. rewrite /ListF. 
         apply non_dep_fun_dist. by repeat f_equiv.
  Qed.

  Global Instance sem_ty_listF_ne_2 : NonExpansive2 (@ListF Σ).
  Proof. intros ???????. unfold ListF; by repeat f_equiv. Qed.

  Global Instance sem_ty_list_ne : NonExpansive (@sem_ty_list Σ).
  Proof. intros ?????. unfold sem_ty_list. 
         apply non_dep_fun_dist. f_equiv. 
         rewrite /ListF. intros ?. by repeat f_equiv.
  Qed.
  
  Global Instance sem_ty_mbang_proper m : Proper ((≡) ==> (≡)) (@sem_ty_mbang Σ m).
  (* Proof. solve_non_expansive. Qed. *)
  Admitted.

  Global Instance sem_ty_prod_proper : Proper ((≡) ==> (≡) ==> (≡)) (@sem_ty_prod Σ).
  (* Proof. solve_non_expansive. Qed. *)
  Admitted.

  Global Instance sem_ty_sum_proper : Proper ((≡) ==> (≡) ==> (≡)) (@sem_ty_sum Σ).
  (* Proof. solve_non_expansive. Qed. *)
  Admitted.

  Global Instance sem_ty_arr_proper : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) sem_ty_arr.
  (* Proof. solve_non_expansive. Qed. *)
  Admitted.

  Global Instance sem_ty_ref_proper : Proper ((≡) ==> (≡)) (@sem_ty_ref Σ _).
  (* Proof. intros ????. unfold sem_ty_ref; by repeat f_equiv. Qed. *)
  Admitted.

  Global Instance sem_ty_ref_cpy_proper : Proper ((≡) ==> (≡)) (@sem_ty_ref_cpy Σ _).
  (* Proof. intros ????. unfold sem_ty_ref_cpy; by repeat f_equiv. Qed. *)
  Admitted.

  Global Instance sem_ty_type_forall_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@sem_ty_type_forall Σ).
  Proof. 
    intros ?????. unfold sem_ty_type_forall; repeat f_equiv. 
    by do 3 apply non_dep_fun_equiv. 
  Qed.

  Global Instance sem_ty_row_forall_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@sem_ty_row_forall Σ).
  Proof. 
    intros ?????. unfold sem_ty_row_forall; repeat f_equiv. 
    by do 3 apply non_dep_fun_equiv. 
  Qed.

  Global Instance sem_ty_mode_forall_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@sem_ty_mode_forall Σ).
  Proof. 
    intros ?????. unfold sem_ty_mode_forall; repeat f_equiv. 
    by do 3 apply non_dep_fun_equiv. 
  Qed.

  Global Instance sem_ty_exist_proper :
    Proper (pointwise_relation _ (≡) ==>(≡)) sem_ty_exists.
  Proof. 
    intros ?????. unfold sem_ty_exists; repeat f_equiv.
    by do 3 apply non_dep_fun_equiv.
  Qed.

  Global Instance sem_ty_rec_proper :
    Proper (pointwise_relation _ (≡) ==>(≡)) (@sem_ty_rec Σ).
  Proof.
    intros C1 C2 HA. apply equiv_dist=> n.
    apply sem_ty_rec_ne=> A. by apply equiv_dist.
  Qed.

  Global Instance sem_ty_mbang_persistent τ :
    (∀ v1 v2, Persistent (@sem_ty_mbang Σ MS τ v1 v2)).
  Proof. unfold sem_ty_mbang. simpl. apply _. Qed.

  Global Instance sem_ty_type_forall_type_persistent (C : sem_ty Σ → sem_ty Σ) v1 v2 :
    (∀ τ w1 w2, Persistent (C τ w1 w2)) →
    Persistent ((sem_ty_type_forall C) v1 v2). 
  Proof. unfold sem_ty_type_forall. simpl. apply _. Qed.

  Global Instance sem_ty_row_forall_persistent (C : sem_row Σ → sem_ty Σ) v1 v2 :
    (∀ τ w1 w2, Persistent (C τ w1 w2)) →
    Persistent ((sem_ty_row_forall C) v1 v2).
  Proof. unfold sem_ty_row_forall. simpl. apply _. Qed.

  Global Instance sem_ty_mode_forall_persistent (C : mode → sem_ty Σ) v1 v2 :
    (∀ τ w1 w2, Persistent (C τ w1 w2)) →
    Persistent ((sem_ty_mode_forall C) v1 v2).
  Proof. unfold sem_ty_mode_forall. simpl. apply _. Qed.

End types_properties.

Section multi_types.
  
  Context `{probblazeRGS Σ}.

  Implicit Types τ κ : sem_ty Σ.
  
  Class MultiT {Σ} (τ : sem_ty Σ) := {
    multi_ty : ⊢ (τ%T ≤ₜ ![MS] τ%T)
  }.

  Global Arguments MultiT _ _%_T.

  Global Instance multi_ty_persistent (τ : sem_ty Σ) `{! MultiT τ} :
    ∀ v1 v2, Persistent (τ v1 v2).
  Proof. 
    intros ??. inv MultiT0. 
    rewrite /ty_le /tc_opaque /sem_ty_mbang /= in multi_ty0.
    rewrite /Persistent. 
    iIntros "Hτ.". iDestruct (multi_ty0 with "Hτ.") as "#Hτ".
    by iModIntro.
  Qed.

End multi_types.

Section sub_typing.

  Context `{!probblazeRGS Σ}.

  Implicit Types τ κ : sem_ty Σ.

  Lemma ty_le_refl (τ : sem_ty Σ) : ⊢ τ ≤ₜ τ.
  Proof. iIntros "!# % % $". Qed.

  Lemma ty_le_trans (τ₁ τ₂ τ₃ : sem_ty Σ) :
    τ₁ ≤ₜ τ₂ -∗
    τ₂ ≤ₜ τ₃ -∗
    τ₁ ≤ₜ τ₃.
  Proof. 
    iIntros "#Hτ₁₂ #Hτ₂₃ !# %v1 %v2 Hτ₁". 
    iApply "Hτ₂₃". by iApply "Hτ₁₂".
  Qed.

  Lemma ty_le_bot (τ : sem_ty Σ) :
    ⊢ ⊥ ≤ₜ τ.
  Proof. iIntros "% % !# []". Qed.

  (* Lemma ty_le_arr (τ₁ κ₁ τ₂ κ₂ : sem_ty Σ) (ρ ρ' : sem_row Σ) :
       ρ ≤ᵣ ρ' -∗
       τ₂ ≤ₜ τ₁ -∗
       κ₁ ≤ₜ κ₂ -∗
       (τ₁ -{ ρ }-∘ κ₁) ≤ₜ (τ₂ -{ ρ' }-∘ κ₂).
     Proof.
       iIntros "#Hρ  #Hτ₂₁ #Hκ₁₂ !# %v1 %v2 Hτκ₁". 
       rewrite /sem_ty_arr /=. iIntros "% % Hτ₂".
       iApply (ewpw_sub with "Hρ").
       iApply (ewpw_mono with "[Hτκ₁ Hτ₂]").
       { iApply ("Hτκ₁" with "[Hτ₂]"); by iApply "Hτ₂₁". }
       iIntros "!# % Hκ !>". by iApply "Hκ₁₂".
     Qed. *)
