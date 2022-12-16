(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Logical relation is sound w.r.t. the contextual refinement. *)
From iris.proofmode Require Import proofmode.
From self.logrel Require Export model adequacy.
From self.typing Require Export contextual_refinement.

(* Observable types are, at the moment, exactly the unboxed types
   which support direct equality tests. *)
Definition ObsType : type → Prop := λ τ, EqType τ ∧ UnboxedType τ.

(* Lemma logrel_adequate Σ `{relocPreG Σ} *)
(*    e e' τ (σ : state) : *)
(*   (∀ `{relocG Σ} Δ, ⊢ {⊤;Δ;∅} ⊨ e ≤log≤ e' : τ) → *)
(*   adequate NotStuck e σ (λ v _, ∃ thp' h v', rtc erased_step ([e'], σ) (of_val v' :: thp', h) *)
(*     ∧ (EqType τ → v = v')). *)
(* Proof. *)
(*   intros Hlog. *)
(*   set (A := λ (HΣ : relocG Σ), interp τ []). *)
(*   eapply (refines_adequate Σ A); last first. *)
(*   - intros HΣ. specialize (Hlog HΣ []). *)
(*     revert Hlog. unfold A, bin_log_related. *)
(*     rewrite !fmap_empty. intros Hvs. *)
(*     iPoseProof Hvs as "H". iSpecialize ("H" $! ∅ with "[]"). *)
(*     { iApply env_ltyped2_empty. } *)
(*     by rewrite !fmap_empty !subst_map_empty. *)
(*   - intros HΣ v v'. unfold A. iIntros "Hvv". *)
(*     iIntros (Hτ). by iApply (eq_type_sound with "Hvv"). *)
(* Qed. *)

(* Theorem logrel_typesafety Σ `{relocPreG Σ} e e' τ thp σ σ' : *)
(*   (∀ `{relocG Σ} Δ, ⊢ {⊤;Δ;∅} ⊨ e ≤log≤ e : τ) → *)
(*   rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp → *)
(*   not_stuck e' σ'. *)
(* Proof. *)
(*   intros Hlog ??. *)
(*   cut (adequate NotStuck e σ (λ v _, ∃ thp' h v', rtc erased_step ([e], σ) (of_val v' :: thp', h) ∧ (EqType τ → v = v'))); first (intros [_ ?]; eauto). *)
(*   eapply logrel_adequate; eauto. *)
(* Qed. *)

(* Theorem F_mu_ref_conc_typesfety e e' τ σ thp σ' : *)
(*   ∅ ⊢ₜ e : τ → *)
(*   rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp → *)
(*   is_Some (to_val e') ∨ reducible e' σ'. *)
(* Proof. *)
(*   intros. *)
(*   eapply (logrel_typesafety relocΣ); eauto. *)
(*   intros. by apply fundamental. *)
(* Qed. *)

(* Lemma logrel_simul Σ `{relocPreG Σ} *)
(*   e e' τ v thp hp σ : *)
(*   (∀ `{relocG Σ} Δ, ⊢ {⊤;Δ;∅} ⊨ e ≤log≤ e' : τ) → *)
(*   rtc erased_step ([e], σ) (of_val v :: thp, hp) → *)
(*   (∃ thp' hp' v', rtc erased_step ([e'], σ) (of_val v' :: thp', hp') ∧ (ObsType τ → v = v')). *)
(* Proof. *)
(*   intros Hlog Hsteps. *)
(*   cut (adequate NotStuck e σ (λ v _, ∃ thp' h v', rtc erased_step ([e'], σ) (of_val v' :: thp', h) ∧ (EqType τ → v = v'))). *)
(*   { unfold ObsType. destruct 1; naive_solver. } *)
(*   eapply logrel_adequate; eauto. *)
(* Qed. *)

(* Theorem refines_coupling' Σ `{prelogrelGpreS Σ} *)
(*   (A : ∀ `{prelogrelGS Σ}, lrel Σ) (φ : val → val → Prop) e e' σ σ' n : *)
(*   (∀ `{prelogrelGS Σ}, ∀ v v', A v v' -∗ ⌜φ v v'⌝) → *)
(*   (∀ `{prelogrelGS Σ}, ⊢ REL e << e' : A) → *)
(*   refRcoupl (prim_exec n (e, σ)) (lim_prim_exec (e', σ')) (coupl_rel φ). *)

Lemma refines_sound_open Σ `{!prelogrelGpreS Σ} Γ e e' τ :
  (∀ `{prelogrelGS Σ} Δ, ⊢ {⊤;Δ;Γ} ⊨ e ≤log≤ e' : τ) →
  Γ ⊨ e ≤ctx≤ e' : τ.
Proof.
  intros Hlog K σ₀ b Htyped.
  assert (ObsType TBool).
  { repeat econstructor; eauto. }
  cut (∀ n, (dmap fst (prim_exec n (fill_ctx K e, σ₀)) #b <=
               dmap fst (lim_prim_exec (fill_ctx K e', σ₀)) #b)%R).
  { intros Hn. eapply distr_le_dmap_1.
    intros ρ. eapply lim_prim_exec_continous.
    intros n.
    (* Seems like we need continuity of [lmarg] to make this work *)
    admit. }
  intros n.
  (* should be [refines_coupling] when we merge with Alejandro's branch *)
  admit.
  (* cut (∃ thp' hp' v', rtc erased_step ([fill_ctx K e'], σ₀) (of_val v' :: thp', hp') ∧ (ObsType TBool  → #b = v')). *)
  (* { naive_solver. } *)
  (* eapply (logrel_simul Σ); last by apply Hstep. *)
  (* iIntros (? ?). *)
  (* iApply (bin_log_related_under_typed_ctx with "[]"); eauto. *)
  (* iModIntro. iIntros (?). iApply Hlog. *)
  Admitted.

Lemma refines_sound Σ `{Hpre : !prelogrelGpreS Σ} (e e': expr) τ :
  (∀ `{prelogrelGS Σ} Δ, ⊢ REL e << e' : (interp τ Δ)) →
  ∅ ⊨ e ≤ctx≤ e' : τ.
Proof.
  intros Hlog. eapply (refines_sound_open Σ).
  iIntros (? Δ vs).
  rewrite fmap_empty env_ltyped2_empty_inv.
  iIntros (->).
  rewrite !fmap_empty !subst_map_empty.
  iApply Hlog.
Qed.
