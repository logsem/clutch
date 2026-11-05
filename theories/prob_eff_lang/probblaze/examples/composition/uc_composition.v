(* A UC composition theorem for the composition operators of [comp_operators].

   A protocol [π] realises an ideal functionality [F] in the [H]-hybrid
   world with simulator [S] if  H ∘f π ≈ S ∘f F,  and a protocol [ρ]
   realises [Iρ] in the [F]-hybrid world (its other subroutines collected in
   the side functionality [A₀]) if  (F ||ᵣ A₀) ∘f ρ ≈ Iρ.  Then

       ((H ∘f π) ||ᵣ A₀) ∘f ρ   ≈   S ∘F Iρ

   with the composed simulator obtained by nesting [S] around [Iρ], and the
   advantage of an environment [A] against the composed system is bounded by
   the advantages of [A ∘ (λ x. (x ||ᵣ A₀) ∘f ρ)] against π's realisation
   and of [A ∘ (λ x. S ∘F x)] against ρ's realisation.

   The proof has two ingredients:

   - congruence: an environment that observes [e] only through an evaluation
     context [K] has the same output distribution as the environment
     [λ v. A (fill K v)] run against [e] directly ([advantage_reduction_ctx],
     a purely operational fact about [lim_exec]), and [λ v. A (fill K v)]
     is a well-typed environment when the context is ([ctx_adv_typed]);

   - the simulator bookkeeping: the associativity lemmas of [comp_operators]
     move [S] out past [A₀] and [ρ].

   Only the components that occur in the two contexts ([S], [F], [A₀], [ρ])
   need to be typed; nothing is assumed about [H ∘f π] or [Iρ] beyond the two
   advantage bounds. *)

From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From Coquelicot Require Import Rbar Lim_seq.
From clutch.prelude Require Import Series_ext.
From clutch.prob Require Import distribution markov.
From clutch.common Require Import language exec.
From clutch.prob_eff_lang.probblaze Require Import comp_operators primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory semantics adequacy.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze Require Import advantage.
From Stdlib Require Import Reals Psatz Classical.

#[local] Open Scope R_scope.
#[local] Set Default Proof Using "All".

(* ------------------------------------------------------------------ *)
(* Semantic typing of the composition operators themselves.           *)
(* (Copies of [func_comp_val_typed] from [dhke_typing],               *)
(* [right_comp_val_typed] from [new_composition_typing] and            *)
(* [functionality_comp_val_typed] from [ske_composition_typing], so    *)
(* that this file does not depend on any example.)                     *)
(* ------------------------------------------------------------------ *)

Section operator_typing.
  Context `{!probblazeRGS Σ}.
  Import typed_hint_modes.

  (* [func_comp] hands [F] the client [λ r, G f r]: the application [G f] is
     delayed behind an η-expansion.  [eta_ty τ] says that this delay preserves
     [τ].  It holds for one-shot arrows and is closed under [∀ᵣ], which covers
     the client types of [τ__F] and [τ__f]. *)
  Definition eta_ty (τ : sem_ty Σ) : iProp Σ :=
    ∀ g1 g2 x1 x2 : val,
      BREL g1 x1 ≤ g2 x2 <| [] |> {{ τ }} -∗ τ (λ: "r", g1 x1 "r")%V (λ: "r", g2 x2 "r")%V.

  Lemma eta_ty_arr ρ τ κ : ⊢ eta_ty (τ -{ ρ }-∘ κ).
  Proof.
    iIntros (g1 g2 x1 x2) "Hg". rewrite /sem_ty_arr /=.
    iIntros (w1 w2) "Hw". brel_pures_l; brel_pures_r.
    iApply (brel_bind [AppLCtx _] [AppLCtx _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS _ _ [] [] with "[] Hg"); first iApply to_iThy_le_refl.
    simpl. iIntros (v1 v2) "Hv". by iApply "Hv".
  Qed.

  Lemma eta_ty_row_forall (C : sem_row Σ → sem_ty Σ) :
    (∀ θ, ⊢ eta_ty (C θ)) → ⊢ eta_ty (∀ᵣ θ, C θ).
  Proof.
    intros HC. iIntros (g1 g2 x1 x2) "Hg". rewrite /sem_ty_row_forall /=. iIntros (θ).
    iApply HC. iApply (brel_wand with "Hg"). iIntros "!# % % H". iApply "H".
  Qed.

  Lemma eta_ty_τf (τ1 τ2 : sem_row Σ → sem_ty Σ) θ : ⊢ eta_ty (τ__f θ τ1 τ2).
  Proof. apply eta_ty_row_forall => θ1. apply eta_ty_row_forall => θ2. apply eta_ty_arr. Qed.

  Lemma sem_oval_typed_eta (g x : string) τ M :
    g ≠ "r" → x ≠ "r" → (⊢ eta_ty M) →
    ⊢ sem_oval_typed [(x, τ); (g, τ ⊸ M)] (λ: "r", g x "r") (λ: "r", g x "r") M.
  Proof.
    iIntros (Hg Hx HM) "!# %vs HΓ /=".
    rewrite !env_sem_typed_cons env_sem_typed_empty.
    iDestruct "HΓ" as "([%x1 [%x2 [%Hvx Hx]]] & [%g1 [%g2 [%Hvg Hg]]] & _)".
    simplify_map_eq. rewrite /pure_weakestpre.prel /=. iExists _, _, 1%nat, 1%nat.
    iSplit; first (iPureIntro; repeat split; by apply pure_recc).
    iApply HM. by iApply "Hg".
  Qed.

  Lemma func_comp_val_typed (T1 M T4 : sem_row Σ → sem_ty Σ) :
    (∀ θ, ⊢ eta_ty (M θ)) →
    ⊢ ⊨ᵥ func_comp ≤ func_comp :
      ((∀ᵣ θ, M θ ⊸ T4 θ) ⊸ (∀ᵣ θ, T1 θ ⊸ M θ) ⊸ (∀ᵣ θ, T1 θ ⊸ T4 θ))%T.
  Proof.
    intros HM.
    iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
    iApply sem_typed_closure; first done.
    iApply (sem_typed_oval _ [_]). iApplyT sem_oval_typed_afun.
    iApply (sem_typed_oval _ [_; _]). iApply sem_typed_RLam. iIntros (θ).
    iApplyT sem_oval_typed_afun. simpl.
    iApplyT sem_typed_app_fun_nil; first iApply row_le_refl.
    - iApplyT (sem_typed_sub_env _ [("f", T1 θ); ("G", T1 θ ⊸ M θ); ("F", _)]).
      { iApply env_le_cons; last iApply ty_le_refl.
        iApply env_le_cons; [iApply env_le_refl|iApply ty_le_row_forall_inst]. }
      iApply (sem_typed_oval _ [("f", _); ("G", _)] [("F", _)]).
      iApply sem_oval_typed_eta; [done|done|apply HM].
    - iApplyT sem_typed_sub_ty; last typed_var. iApply ty_le_row_forall_inst.
      Unshelve. all: solve_typed_side.
  Qed.

  Lemma parallel_comp_val_typed (τ1 τ1' τ2 τ2' : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ parallel_composition ≤ parallel_composition :
      (τ__F τ2 τ2' ⊸ τ__F τ1 τ1' ⊸ ∀ᵣ θ, τ__f θ τ1' τ2' ⊸ τ__f θ τ1 τ2)%T.
  Proof.
    iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
    iApply sem_typed_closure; first done.
    iApply (sem_typed_oval _ [_]). iApplyT sem_oval_typed_afun.
    iApply (sem_typed_oval _ [_; _]). iApply sem_typed_RLam. iIntros (θ).
    iApplyT sem_oval_typed_afun.
    iApply (sem_typed_oval _ [_; _; _]). iApply sem_typed_RLam. iIntros (θ1).
    iApply sem_typed_RLam. iIntros (θ2).
    iApplyT sem_oval_typed_afun. simpl.
    iApplyT sem_typed_pair_elim; first typed_var.
    iApplyT sem_typed_app_fun_nil.
    2: typed_var.
    2: { iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApply (sem_typed_oval _ [_; _; _])|].
         2: { iApplyT sem_typed_sub_ty; last typed_var.
              iApply ty_le_trans; first iApply (ty_le_row_forall_inst _ (sem_row_union (¡ θ1) θ)).
              iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|iApply ty_le_row_forall_inst]. }
         iApply sem_typed_RLam. iIntros (θh). iApplyT sem_oval_typed_afun. simpl.
         iApplyT sem_typed_app_fun_nil.
         2: typed_var.
         2: { iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApply (sem_typed_oval _ [_; _])|].
              2: { iApplyT sem_typed_sub_ty; last typed_var.
                   iApply ty_le_trans; first iApply (ty_le_row_forall_inst _ (sem_row_union (¡ θh) θ)).
                   iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|iApply ty_le_row_forall_inst]. }
              iApply sem_typed_RLam. iIntros (θh2). iApplyT sem_oval_typed_afun. simpl.
              iApplyT sem_typed_app_fun_nil.
              2: { iApply sem_typed_sub_nil. iApplyT sem_typed_pair; typed_var. }
              2: { iApplyT sem_typed_sub_ty; last typed_var.
                   iApply ty_le_trans; first iApply ty_le_row_forall_inst. iApply ty_le_row_forall_inst. }
              iApply row_le_refl. }
         row_le_submseteq. }
    row_le_submseteq.
    Unshelve. all: solve_typed_side.
  Qed.

  Lemma functionality_comp_val_typed (τ1' τ1 τF τ2 : sem_row Σ → sem_ty Σ) :
    ⊢ ⊨ᵥ functionality_composition ≤ functionality_composition :
      (τ__F τ2 τF ⊸ (∀ᵣ θ, τ1' θ ⊸ τ__f θ τ1 τF) ⊸ ∀ᵣ θ, τ1' θ ⊸ τ__f θ τ1 τ2)%T.
  Proof.
    iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
    iApply sem_typed_closure; first done.
    iApply (sem_typed_oval _ [_]). iApplyT sem_oval_typed_afun.
    iApply (sem_typed_oval _ [_; _]). iApply sem_typed_RLam. iIntros (θ).
    iApplyT sem_oval_typed_afun.
    iApply (sem_typed_oval _ [_; _; _]). iApply sem_typed_RLam. iIntros (θ1).
    iApply sem_typed_RLam. iIntros (θ2).
    iApplyT sem_oval_typed_afun. simpl.
    iApplyT sem_typed_pair_elim; first typed_var.
    iApplyT sem_typed_app_fun_nil.
    2: typed_var.
    2: { iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApply (sem_typed_oval _ [_; _; _])|].
         2: { iApplyT sem_typed_sub_ty; last typed_var.
              iApply ty_le_trans; first iApply (ty_le_row_forall_inst _ (sem_row_union (¡ θ1) θ)).
              iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|iApply ty_le_row_forall_inst]. }
         iApply sem_typed_RLam. iIntros (θF). iApplyT sem_oval_typed_afun. simpl.
         iApplyT sem_typed_app_fun_nil.
         2: { iApply sem_typed_sub_nil. iApplyT sem_typed_pair; typed_var. }
         2: { iApplyT sem_typed_sub_ty; last first.
              { iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|typed_var|].
                iApplyT sem_typed_sub_ty; last typed_var. iApply ty_le_row_forall_inst. }
              rewrite /τ__f. iApply ty_le_trans; first iApply (ty_le_row_forall_inst _ θ1).
              iApply (ty_le_row_forall_inst _ θF). }
         row_le_submseteq. }
    row_le_submseteq.
    Unshelve. all: solve_typed_side.
  Qed.


  (* The hybrid-world context [λ x. (x ||ᵣ A₀) ∘f ρ], as an open term in [x]. *)
  Lemma ctx_hybrid_typed (A₀ ρ : expr) (τc τJ1 τJ2 τA τH : sem_row Σ → sem_ty Σ) :
    ⊢ sem_typed [] A₀ A₀ ⊥ (τ__F τA τJ1) [] -∗
      sem_typed [] ρ ρ ⊥ (∀ᵣ θ, τc θ ⊸ τ__f θ τJ1 τJ2)%T [] -∗
      sem_typed [("v", τ__F τH τJ2)] (("v" ||ᵣ A₀) ∘f ρ) (("v" ||ᵣ A₀) ∘f ρ) ⊥
        (∀ᵣ θ, τc θ ⊸ τ__f θ τA τH)%T [].
  Proof.
    iIntros "#HA₀ #Hρ".
    iApplyT sem_typed_app_nil; last first.
    { iApply (sem_typed_frame_env_gen _ [_]). iApply "Hρ". }
    iApplyT sem_typed_app_nil; last first.
    - iApplyT sem_typed_app_nil; last first.
      { iApply (sem_typed_frame_env_gen _ [_]). iApply "HA₀". }
      iApplyT sem_typed_app_nil; last typed_var.
      iApply sem_typed_val. iApply parallel_comp_val_typed.
    - iApply sem_typed_val. iApply func_comp_val_typed. intros θ. apply eta_ty_τf.
    Unshelve. all: solve_typed_side.
  Qed.

  (* The simulator context [λ x. S ∘F x], as an open term in [x]. *)
  Lemma ctx_sim_typed (S : expr) (τc τA τF τH : sem_row Σ → sem_ty Σ) :
    ⊢ sem_typed [] S S ⊥ (τ__F τH τF) [] -∗
      sem_typed [("v", (∀ᵣ θ, τc θ ⊸ τ__f θ τA τF)%T)] (S ∘F "v") (S ∘F "v") ⊥
        (∀ᵣ θ, τc θ ⊸ τ__f θ τA τH)%T [].
  Proof.
    iIntros "#HS".
    iApplyT sem_typed_app_nil; last typed_var.
    iApplyT sem_typed_app_nil; last iApply "HS".
    iApply sem_typed_val. iApply functionality_comp_val_typed.
    Unshelve. all: solve_typed_side.
  Qed.

  (* The shapes in which [functionality_comp_func_comp_assoc] wants a
     simulator [S'] over a one-port functionality and that functionality [G]:
     [S']'s output row in the other order, and [G]'s port quantifier outside
     the arrow.  Both are subtyping. *)
  Lemma sem_typed_sim_assoc_shape (S' : expr) (τG τA τF : sem_row Σ → sem_ty Σ) :
    ⊢ sem_typed [] S' S' ⊥ (∀ᵣ θ, (∀ᵣ θJ, τG θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙) ⊸ τ__f θ τA τF)%T [] -∗
      sem_typed [] S' S' ⊥ (∀ᵣ θ, (∀ᵣ θJ, τG θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙) ⊸
          ∀ᵣ θ1, ∀ᵣ θ2, (τA θ1 × τF θ2) -{ sem_row_union (¡θ2) (sem_row_union (¡θ1) θ) }-∘ 𝟙)%T [].
  Proof.
    iIntros "#HS'". iApply sem_typed_sub_ty; last iApply "HS'".
    iApply ty_le_row_forall; iIntros (θ).
    iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|].
    rewrite /τ__f. iApply ty_le_row_forall; iIntros (θ1). iApply ty_le_row_forall; iIntros (θ2).
    iApply ty_le_arr; [row_le_submseteq|iApply ty_le_refl|iApply ty_le_refl].
  Qed.

  Lemma sem_typed_fun_assoc_shape (G : expr) (τc τG : sem_row Σ → sem_ty Σ) :
    ⊢ sem_typed [] G G ⊥ (∀ᵣ θ, τc θ ⊸ ∀ᵣ θJ, τG θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙)%T [] -∗
      sem_typed [] G G ⊥ (∀ᵣ θ, ∀ᵣ θJ, τc θ ⊸ τG θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙)%T [].
  Proof.
    iIntros "#HG". iApply sem_typed_sub_ty; last iApply "HG".
    iApply ty_le_row_forall; iIntros (θ).
    iIntros "!# %v1 %v2 H %θJ".
    iDestruct (ty_le_arr with "[] [] []") as "Hle";
      [iApply row_le_refl|iApply ty_le_refl|iApply (ty_le_row_forall_inst _ θJ)|].
    iApply ("Hle" with "H").
  Qed.

  (* An environment composed with a typed context is a typed environment. *)
  Lemma ctx_adv_typed (A : val) (K : ectx) (α β : sem_ty Σ) :
    ⊢ sem_val_typed A A (β → 𝔹)%T -∗
      sem_typed [("v", α)] (fill K "v") (fill K "v") ⊥ β [] -∗
      sem_val_typed (λ: "v", A (fill K "v"))%V (λ: "v", A (fill K "v"))%V (α → 𝔹)%T.
  Proof.
    iIntros "#HA #Hbody".
    iApply (sem_typed_closure _ _ _ BAnon "v" _ _ MS); first done. simpl.
    iApply sem_typed_app_nil; last iApply "Hbody".
    iApply sem_typed_val. iApply sem_val_typed_sub; last iApply "HA". iApply ty_le_mbang_elim.
  Qed.

End operator_typing.

(* ------------------------------------------------------------------ *)
(* Closedness helpers.                                                 *)
(* ------------------------------------------------------------------ *)

Lemma closed_app (e1 e2 : expr) :
  is_closed_expr ∅ e1 → is_closed_expr ∅ e2 → is_closed_expr ∅ (e1 e2).
Proof. intros H1 H2. simpl. apply andb_prop_intro. by split. Qed.

Lemma closed_app_inv (e1 e2 : expr) :
  is_closed_expr ∅ (e1 e2) → is_closed_expr ∅ e1 ∧ is_closed_expr ∅ e2.
Proof. simpl. by intros [? ?]%andb_prop_elim. Qed.

Lemma func_comp_closed : is_closed_expr ∅ func_comp.
Proof. is_closed. Qed.
Lemma parallel_composition_closed : is_closed_expr ∅ parallel_composition.
Proof. is_closed. Qed.
Lemma functionality_composition_closed : is_closed_expr ∅ functionality_composition.
Proof. is_closed. Qed.

Lemma closed_func_comp (e1 e2 : expr) :
  is_closed_expr ∅ e1 → is_closed_expr ∅ e2 → is_closed_expr ∅ (e1 ∘f e2).
Proof. intros. apply closed_app; [apply closed_app; [apply func_comp_closed|done]|done]. Qed.
Lemma closed_parallel (e1 e2 : expr) :
  is_closed_expr ∅ e1 → is_closed_expr ∅ e2 → is_closed_expr ∅ (e1 ||ᵣ e2).
Proof. intros. apply closed_app; [apply closed_app; [apply parallel_composition_closed|done]|done]. Qed.
Lemma closed_functionality (e1 e2 : expr) :
  is_closed_expr ∅ e1 → is_closed_expr ∅ e2 → is_closed_expr ∅ (e1 ∘F e2).
Proof. intros. apply closed_app; [apply closed_app; [apply functionality_composition_closed|done]|done]. Qed.

(* ------------------------------------------------------------------ *)
(* Execution under a handler-free evaluation context.                  *)
(*                                                                     *)
(* An evaluation context without handler frames cannot catch effects   *)
(* raised by the expression it surrounds, so it is a language context  *)
(* in the sense of [LanguageCtx], and [lim_exec_val_context_bind]      *)
(* applies: running [fill K e] is running [e] and then [K] on its      *)
(* result.                                                             *)
(* ------------------------------------------------------------------ *)

Section exec_ctx.

  Lemma prim_step_uncaught e σ :
    uncaught_eff e ≠ None → prim_step e σ = dzero.
  Proof.
    intros Hu. apply distr_ext => ρ. rewrite dzero_0.
    destruct ρ as [e' σ'].
    destruct (Rgt_dec (prim_step e σ (e', σ')) 0) as [Hgt|Hngt].
    - by apply prim_step_uncaught_eff in Hgt.
    - pose proof (pmf_pos (prim_step e σ) (e', σ')). lra.
  Qed.

  Lemma fill_ctx_no_handler (K : ectx) :
    ectx_labels K = [] → LanguageCtx (fill K).
  Proof.
    intros HK. split.
    - apply fill_not_val.
    - apply _.
    - intros e1 σ1 Hv. simpl.
      destruct (uncaught_eff e1) as [((l, v), k)|] eqn:Hu.
      + rewrite (prim_step_uncaught e1); [|by rewrite Hu].
        rewrite (prim_step_uncaught (fill K e1)); [by rewrite dmap_dzero|].
        rewrite /uncaught_eff in Hu *.
        destruct (to_eff e1) as [((l', v'), k')|] eqn:He; [|done].
        erewrite to_eff_fill; [|done].
        destruct (decide (l' ∉ ectx_labels k')); [|done].
        rewrite ectx_labels_app HK /=. by destruct (decide (l' ∉ ectx_labels k')).
      + by apply fill_dmap_uncaught'.
  Qed.

  (* Only final configurations carry mass in [lim_exec_cfg]. *)
  Lemma exec_cfg_val n (ρ : cfg blaze_prob_lang) e' σ' :
    exec_cfg n ρ (e', σ') > 0 → is_Some (to_val e').
  Proof.
    revert ρ. induction n as [|n IH]; intros [e σ]; simpl; destruct (to_val e) eqn:He.
    - intros Hpos%dret_pos. simplify_eq. by eauto.
    - rewrite dzero_0. lra.
    - intros Hpos%dret_pos. simplify_eq. by eauto.
    - intros ([e1 σ1] & H1 & H2)%dbind_pos. by eapply IH.
  Qed.

  Lemma lim_exec_cfg_val (ρ : cfg blaze_prob_lang) e' σ' :
    lim_exec_cfg ρ (e', σ') > 0 → is_Some (to_val e').
  Proof.
    rewrite /lim_exec_cfg lim_distr_pmf. intros Hpos.
    destruct (classic (∃ n, exec_cfg n ρ (e', σ') > 0)) as [[n Hn]|Hno]; [by eapply exec_cfg_val|].
    exfalso.
    assert (∀ n, exec_cfg n ρ (e', σ') = 0) as H0.
    { intros n. pose proof (pmf_pos (exec_cfg n ρ) (e', σ')).
      destruct (Rle_lt_or_eq_dec _ _ H) as [Hlt|Heq]; [|done].
      exfalso. apply Hno. by exists n. }
    erewrite Sup_seq_ext in Hpos; [|intros n; rewrite H0; done].
    rewrite sup_seq_const in Hpos. lra.
  Qed.

  (* The Markov-chain [lim_exec] used by [advantage] agrees with [lim_exec_val]. *)
  Lemma lim_exec_lim_exec_val (ρ : cfg blaze_prob_lang) :
    lim_exec ρ = lim_exec_val ρ.
  Proof.
    apply distr_ext => v. rewrite lim_exec_unfold lim_exec_val_rw. f_equal.
  Qed.

  Lemma lim_exec_val_pure_step (e e' : expr) σ :
    PureExec True 1 e e' → to_val e = None →
    lim_exec_val (e, σ) = lim_exec_val (e', σ).
  Proof.
    intros Hp Hv. apply nsteps_once_inv in Hp; [|done].
    rewrite lim_exec_val_prim_step prim_step_or_val_no_val //.
    rewrite (pmf_1_eq_dret _ _ (pure_step_det _ _ Hp σ)) dret_id_left' //.
  Qed.

  (* Running [A (fill K e)] is running [(λ v. A (fill K v)) e]. *)
  Lemma lim_exec_ctx_adv (A : val) (K : ectx) (e0 : expr) σ (w : val) :
    ectx_labels K = [] →
    (∀ v : val, val_subst "v" v (fill K "v") = fill K v) →
    lim_exec (A (fill K e0), σ) w = lim_exec ((λ: "v", A (fill K "v"))%V e0, σ) w.
  Proof.
    intros HK Hvs. rewrite !lim_exec_lim_exec_val.
    change (A (fill K e0))%E with (fill (AppRCtx A :: K) e0).
    change ((λ: "v", A (fill K "v"))%V e0)%E with (fill [AppRCtx (λ: "v", A (fill K "v"))%V] e0).
    assert (ectx_labels (AppRCtx A :: K) = []) as HK' by by rewrite ectx_labels_cons HK.
    rewrite (@lim_exec_val_context_bind _ _ (fill_ctx_no_handler _ HK')).
    rewrite (@lim_exec_val_context_bind _ _ (fill_ctx_no_handler [AppRCtx _] eq_refl)).
    erewrite dbind_ext_right_strong; [done|].
    intros [e' σ'] Hpos.
    destruct (lim_exec_cfg_val _ _ _ Hpos) as [v Hv]. apply of_to_val in Hv. subst e'. simpl.
    pose proof (pure_beta BAnon "v" (A (fill K "v")) (RecV BAnon "v" (A (fill K "v"))) v) as Hb.
    simpl in Hb. rewrite Hvs in Hb.
    by rewrite (lim_exec_val_pure_step _ _ _ Hb).
  Qed.

End exec_ctx.

(* ------------------------------------------------------------------ *)
(* Advantage under an evaluation context.                              *)
(* ------------------------------------------------------------------ *)

Section advantage_ctx.
  Context `{!probblazeRGpreS Σ}.

  (* If the environment [A] observes [e] only through a handler-free
     context [K], its advantage against [fill K e] vs [fill K e'] is that of
     the environment [λ v. A (fill K v)] against [e] vs [e'].  No typing of
     [e] or [e'] is needed. *)
  Lemma advantage_reduction_ctx (A : val) (K : ectx) (e e' : expr) (b : bool) :
    ectx_labels K = [] →
    (∀ (vs : gmap string val) (w : val), vs !! "v" = Some w →
        subst_map vs (fill K "v") = fill K w) →
    advantage A (fill K e) (fill K e') #b <= advantage (λ: "v", A (fill K "v"))%V e e' #b.
  Proof.
    intros HK Hsubst.
    assert (∀ w : val, val_subst "v" w (fill K "v") = fill K w) as Hvs.
    { intros w. rewrite -(subst_map_empty (fill K "v")) -(delete_empty "v") -subst_map_insert.
      apply Hsubst. apply lookup_insert_eq. }
    apply advantage_uniform => σ.
    etrans; last by apply (advantage_ub _ _ _ _ σ).
    right. unfold pr_dist.
    by rewrite !(lim_exec_ctx_adv A K _ σ _ HK Hvs).
  Qed.

  (* A perfect (two-sided) relation gives zero advantage. *)
  Lemma advantage_zero (A : val) (e e' : expr) (b : bool) (τ : ∀ `{probblazeRGS Σ}, sem_ty Σ) :
    (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (τ → 𝔹)%T) →
    (∀ `{probblazeRGS Σ}, ⊢ sem_typed [] e e' ⊥ τ []) →
    (∀ `{probblazeRGS Σ}, ⊢ sem_typed [] e' e ⊥ τ []) →
    advantage A e e' #b <= 0.
  Proof. intros. right. by eapply sem_typed_advantage. Qed.

End advantage_ctx.

(* ------------------------------------------------------------------ *)
(* The UC composition theorem.                                         *)
(* ------------------------------------------------------------------ *)

Section uc_composition.
  Context `{!probblazeRGpreS Σ}.

  (* The two contexts through which the environment observes the two
     realisations. *)
  Definition hybrid_ctx (A₀ ρ : val) : ectx :=
    [AppLCtx ρ; AppRCtx func_comp; AppLCtx A₀; AppRCtx parallel_composition].
  Definition sim_ctx (S : expr) : ectx :=
    [AppRCtx (functionality_composition S)].

  (* Interface types (all indexed by a row):
       τc  : the client interface of ρ
       τJ1 : what ρ needs from A₀;  τJ2 : what ρ needs from F (and from H ∘f π)
       τA  : A₀'s environment ports
       τF  : F's environment ports
       τH  : the environment ports of H ∘f π (and of the simulator S)
       τG  : the environment port of G, handled by the simulator S'       *)
  Theorem uc_composition
      (Rπ S F S' G : expr) (A₀ ρ : val) (b : bool) (ε_π ε_ρ : val → R)
      (τc τJ1 τJ2 τA τF τH τG : ∀ `{probblazeRGS Σ}, sem_row Σ → sem_ty Σ) :
    (* the components that act as contexts or get rearranged: closed and well typed *)
    is_closed_expr ∅ S → is_closed_expr ∅ F → is_closed_expr ∅ A₀ → is_closed_expr ∅ ρ →
    is_closed_expr ∅ S' → is_closed_expr ∅ G →
    (∀ `{probblazeRGS Σ}, ⊢ sem_typed [] S S ⊥ (τ__F τH τF) []) →
    (∀ `{probblazeRGS Σ}, ⊢ sem_typed [] F F ⊥ (τ__F τF τJ2) []) →
    (∀ `{probblazeRGS Σ}, ⊢ sem_typed [] A₀ A₀ ⊥ (τ__F τA τJ1) []) →
    (∀ `{probblazeRGS Σ}, ⊢ sem_typed [] ρ ρ ⊥ (∀ᵣ θ, τc θ ⊸ τ__f θ τJ1 τJ2)%T []) →
    (∀ `{probblazeRGS Σ}, ⊢ sem_typed [] S' S' ⊥
        (∀ᵣ θ, (∀ᵣ θJ, τG θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙) ⊸ τ__f θ τA τF)%T []) →
    (∀ `{probblazeRGS Σ}, ⊢ sem_typed [] G G ⊥
        (∀ᵣ θ, τc θ ⊸ ∀ᵣ θJ, τG θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙)%T []) →
    (* π realises F in the H-hybrid world with simulator S *)
    (∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (τ__F τH τJ2 → 𝔹)%T) →
       advantage A Rπ (S ∘f F) #b <= ε_π A) →
    (* ρ realises G in the (F, A₀)-hybrid world with simulator S' *)
    (∀ A : val, (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A ((∀ᵣ θ, τc θ ⊸ τ__f θ τA τF) → 𝔹)%T) →
       advantage A ((F ||ᵣ A₀) ∘f ρ) (S' ∘f G) #b <= ε_ρ A) →
    (* the composed protocol realises G with the composed simulator S ∘F S' *)
    ∀ A : val,
      (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A ((∀ᵣ θ, τc θ ⊸ τ__f θ τA τH) → 𝔹)%T) →
      advantage A ((Rπ ||ᵣ A₀) ∘f ρ) ((S ∘F S') ∘f G) #b
        <= ε_π (λ: "v", A (("v" ||ᵣ A₀) ∘f ρ))%V + ε_ρ (λ: "v", A (S ∘F "v"))%V.
  Proof.
    intros HSc HFc HA₀c Hρc HS'c HGc HS HF HA₀ Hρ HS' HG Hπ Hρ' A HA.
    (* The type of the composed systems. *)
    set (β := λ H : probblazeRGS Σ, (∀ᵣ θ, τc H θ ⊸ τ__f θ (τA H) (τH H))%T).
    assert (is_closed_expr ∅ ((S ∘f F) ||ᵣ A₀)) as HSFA
      by (apply closed_parallel; [by apply closed_func_comp|done]).
    assert (is_closed_expr ∅ (S ∘F (F ||ᵣ A₀))) as HSFA'
      by (apply closed_functionality; [done|by apply closed_parallel]).
    assert (is_closed_expr ∅ (F ||ᵣ A₀)) as HFA by by apply closed_parallel.
    (* The chain of hybrids:
         (Rπ ||ᵣ A₀) ∘f ρ
       ≤ ((S ∘f F) ||ᵣ A₀) ∘f ρ          [Hπ, through the hybrid context]
       ≃ (S ∘F (F ||ᵣ A₀)) ∘f ρ          [associativity]
       ≃ S ∘F ((F ||ᵣ A₀) ∘f ρ)          [associativity]
       ≤ S ∘F (S' ∘f G)                  [Hρ', through the simulator context]
       ≃ (S ∘F S') ∘f G                  [associativity]                        *)
    eapply (advantage_triangle _ _ (((S ∘f F) ||ᵣ A₀) ∘f ρ)); first last.
    { reflexivity. }
    - (* the simulator side *)
      eapply (advantage_triangle _ _ ((S ∘F (F ||ᵣ A₀)) ∘f ρ) _ _ 0); first last.
      { rewrite Rplus_0_l. reflexivity. }
      2: { apply (advantage_zero _ _ _ _ β); [exact HA| |]; intros HRGS.
           - iApply func_comp_left; [done|done|done|done| |iApply Hρ].
             iApply func_comp_parallel_comp_assoc; [done|done|done|iApply HS|iApply HF|iApply HA₀].
           - iApply func_comp_left; [done|done|done|done| |iApply Hρ].
             iApply func_comp_parallel_comp_assoc_rev; [done|done|done|iApply HS|iApply HF|iApply HA₀]. }
      eapply (advantage_triangle _ _ (S ∘F ((F ||ᵣ A₀) ∘f ρ)) _ _ 0); first last.
      { rewrite Rplus_0_l. reflexivity. }
      2: { apply (advantage_zero _ _ _ _ β); [exact HA| |]; intros HRGS.
           - iApply (functionality_comp_func_comp_assoc_gen _ _ _ _ _ _ (λ θ1 θ2, (τJ1 HRGS θ1 × τJ2 HRGS θ2)%T));
               [done|done|done|iApply HS| |iApply Hρ].
             iApply parallel_comp_right; [done|done|done|done|iApply HF|iApply HA₀].
           - iApply (functionality_comp_func_comp_assoc_gen_rev _ _ _ _ _ _ (λ θ1 θ2, (τJ1 HRGS θ1 × τJ2 HRGS θ2)%T));
               [done|done|done|iApply HS| |iApply Hρ].
             iApply parallel_comp_right; [done|done|done|done|iApply HF|iApply HA₀]. }
      eapply (advantage_triangle _ _ (S ∘F (S' ∘f G)) _ _ _ 0); first last.
      { rewrite Rplus_0_r. reflexivity. }
      1: { apply (advantage_zero _ _ _ _ β); [exact HA| |]; intros HRGS.
           - iApply (functionality_comp_func_comp_assoc_rev _ _ _ _ _ _ (τG HRGS));
               [done|done|done|iApply HS
               |iApply sem_typed_sim_assoc_shape; iApply HS'
               |iApply sem_typed_fun_assoc_shape; iApply HG].
           - iApply (functionality_comp_func_comp_assoc _ _ _ _ _ _ (τG HRGS));
               [done|done|done|iApply HS
               |iApply sem_typed_sim_assoc_shape; iApply HS'
               |iApply sem_typed_fun_assoc_shape; iApply HG]. }
      change (S ∘F ((F ||ᵣ A₀) ∘f ρ))%E with (fill (sim_ctx S) ((F ||ᵣ A₀) ∘f ρ)).
      change (S ∘F (S' ∘f G))%E with (fill (sim_ctx S) (S' ∘f G)).
      change (S ∘F "v")%E with (fill (sim_ctx S) "v").
      etrans; first apply advantage_reduction_ctx.
      { done. }
      { intros vs w Hw. simpl. by rewrite Hw (subst_map_is_closed_empty S). }
      apply Hρ'. intros HRGS.
      iApply ctx_adv_typed; first iApply HA. iApply ctx_sim_typed. iApply HS.
    - (* the protocol side *)
      change ((Rπ ||ᵣ A₀) ∘f ρ)%E with (fill (hybrid_ctx A₀ ρ) Rπ).
      change (((S ∘f F) ||ᵣ A₀) ∘f ρ)%E with (fill (hybrid_ctx A₀ ρ) (S ∘f F)).
      change (("v" ||ᵣ A₀) ∘f ρ)%E with (fill (hybrid_ctx A₀ ρ) "v").
      etrans; first apply advantage_reduction_ctx.
      { done. }
      { intros vs w Hw. simpl. by rewrite Hw. }
      apply Hπ. intros HRGS.
      iApply ctx_adv_typed; first iApply HA. iApply ctx_hybrid_typed; [iApply HA₀|iApply Hρ].
  Qed.


End uc_composition.


