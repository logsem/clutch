(* Advantage under an evaluation context, and perfect steps.

   - [advantage_reduction_ctx]: an environment [A] that observes [e] only
     through a handler-free evaluation context [K] has the same output
     distribution as the environment [λ v. A (fill K v)] run against [e]
     directly.  Purely operational: nothing is assumed about [e].
   - [ctx_adv_typed]: [λ v. A (fill K v)] is a well-typed environment when
     the context is.
   - [advantage_zero]: a two-sided semantic relation gives zero advantage. *)

From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From Coquelicot Require Import Rbar Lim_seq.
From clutch.prelude Require Import Series_ext.
From clutch.prob Require Import distribution markov.
From clutch.common Require Import language exec.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode logic.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory semantics adequacy.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From Stdlib Require Import Reals Psatz Classical.

#[local] Open Scope R_scope.
#[local] Set Default Proof Using "All".

Section ctx_adv_typed.
  Context `{!probblazeRGS Σ}.

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

  (* Pure steps on either side, under a context. *)
  Lemma brel_rtc_pure_l K e e' e2 E L R :
    rtc pure_step e e' →
    BREL fill K e' ≤ e2 @ E <|L|> {{R}} ⊢ BREL fill K e ≤ e2 @ E <|L|> {{R}}.
  Proof.
    induction 1 as [|x y z Hxy _ IH]; first done.
    iIntros "H". iApply (brel_pure_step_later _ _ _ _ True 1).
    { intros _. apply nsteps_once. by apply logic.pure_step_ctx. }
    { done. }
    iNext. by iApply IH.
  Qed.

  Lemma brel_rtc_pure_r K e1 e e' E L R :
    rtc pure_step e e' →
    BREL e1 ≤ fill K e' @ E <|L|> {{R}} ⊢ BREL e1 ≤ fill K e @ E <|L|> {{R}}.
  Proof.
    induction 1 as [|x y z Hxy _ IH]; first done.
    iIntros "H". iApply (brel_pure_step_r _ _ _ _ True 1).
    { intros _. apply nsteps_once. by apply logic.pure_step_ctx. }
    { done. }
    by iApply IH.
  Qed.

End ctx_adv_typed.

(* Calling a factory literal is one pure step. *)
Lemma thunk_call_pure (e : expr) : rtc pure_step ((λ: <>, e)%V #()%V) e.
Proof.
  pose proof (pure_beta BAnon BAnon e (RecV BAnon BAnon e) #()%V) as Hp. simpl in Hp.
  apply rtc_once, nsteps_once_inv, Hp. done.
Qed.

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

  (* Pure steps under [A (fill K ·)] do not change the output distribution. *)
  Lemma lim_exec_rtc_pure (e e' : expr) σ :
    rtc pure_step e e' → lim_exec_val (e, σ) = lim_exec_val (e', σ).
  Proof.
    induction 1 as [|x y z Hxy _ IH]; first done.
    rewrite -IH. apply lim_exec_val_pure_step.
    - intros _. by apply nsteps_once.
    - eapply (val_stuck x σ (y, σ)). rewrite (pure_step_det _ _ Hxy σ). lra.
  Qed.

  Lemma lim_exec_pure_ctx (A : val) (K : ectx) (e e' : expr) σ (w : val) :
    ectx_labels K = [] → rtc pure_step e e' →
    lim_exec (A (fill K e), σ) w = lim_exec (A (fill K e'), σ) w.
  Proof.
    intros HK H. rewrite !lim_exec_lim_exec_val.
    change (A (fill K e))%E with (fill (AppRCtx A :: K) e).
    change (A (fill K e'))%E with (fill (AppRCtx A :: K) e').
    assert (ectx_labels (AppRCtx A :: K) = []) as HK' by by rewrite ectx_labels_cons HK.
    pose proof (fill_ctx_no_handler _ HK') as Hctx.
    rewrite (lim_exec_rtc_pure (fill (AppRCtx A :: K) e) (fill (AppRCtx A :: K) e')); first done.
    apply (rtc_congruence (R := pure_step) (fill (AppRCtx A :: K)) pure_step); [intros ? ? ?; by apply (@language.pure_step_ctx _ _ Hctx)|done].
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

  (* The advantage is invariant under pure steps of the systems, under a
     context. *)
  Lemma advantage_pure_l (A : val) (K : ectx) (e e' X : expr) (b : bool) :
    ectx_labels K = [] → rtc pure_step e e' →
    advantage A (fill K e) X #b <= advantage A (fill K e') X #b.
  Proof.
    intros HK H. apply advantage_uniform => σ.
    etrans; last by apply (advantage_ub _ _ _ _ σ).
    right. unfold pr_dist. by rewrite !(lim_exec_pure_ctx A K e e' σ _ HK H).
  Qed.

  Lemma advantage_pure_r (A : val) (K : ectx) (X e e' : expr) (b : bool) :
    ectx_labels K = [] → rtc pure_step e e' →
    advantage A X (fill K e) #b <= advantage A X (fill K e') #b.
  Proof.
    intros HK H. apply advantage_uniform => σ.
    etrans; last by apply (advantage_ub _ _ _ _ σ).
    right. unfold pr_dist. by rewrite !(lim_exec_pure_ctx A K e e' σ _ HK H).
  Qed.

  Lemma advantage_pure_l_rev (A : val) (K : ectx) (e e' X : expr) (b : bool) :
    ectx_labels K = [] → rtc pure_step e e' →
    advantage A (fill K e') X #b <= advantage A (fill K e) X #b.
  Proof.
    intros HK H. apply advantage_uniform => σ.
    etrans; last by apply (advantage_ub _ _ _ _ σ).
    right. unfold pr_dist. by rewrite !(lim_exec_pure_ctx A K e e' σ _ HK H).
  Qed.

  Lemma advantage_pure_r_rev (A : val) (K : ectx) (X e e' : expr) (b : bool) :
    ectx_labels K = [] → rtc pure_step e e' →
    advantage A X (fill K e') #b <= advantage A X (fill K e) #b.
  Proof.
    intros HK H. apply advantage_uniform => σ.
    etrans; last by apply (advantage_ub _ _ _ _ σ).
    right. unfold pr_dist. by rewrite !(lim_exec_pure_ctx A K e e' σ _ HK H).
  Qed.

End advantage_ctx.
