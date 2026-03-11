(** * Completeness prelims for concurrent probabilistic languages

    Thread pool ghost state, safety, and multi-step relation used by
    the abstract completeness framework in [coneris_completeness.v].

    Analogous to [iris-completeness/completeness_prelims.v] but adapted
    for clutch's [conLanguage] (probabilistic, no observations).
*)

From Stdlib Require Export Reals.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic Require Export invariants lib.ghost_map lib.cancelable_invariants.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.

From clutch.common Require Export con_language.
From clutch.prob Require Export distribution.

Local Open Scope R.

Class coneristpinvGS (Σ : gFunctors) (Λ : conLanguage) := ConeristpInvGS {
  coneristpinvGS_ghost_mapG :: ghost_mapG Σ nat Λ.(expr);
  coneristpinvGS_tp_name : gname;
}.

Definition con_is_thread `{coneristpinvGS Σ Λ} (n : nat) (dq : dfrac) (e : Λ.(expr)) : iProp Σ :=
  n ↪[coneristpinvGS_tp_name]{dq} e.

Notation "n '↪cthread' dq e" := (con_is_thread n dq e)
  (at level 20, dq custom dfrac at level 1,
   format "n  '↪cthread' dq  e") : bi_scope.

Section coneristpinv.
Context `{!coneristpinvGS Σ Λ}.

Definition con_tp_inv (C : list Λ.(expr)) : iProp Σ :=
  ∃ (m : gmap nat Λ.(expr)),
    ⌜∀ n, m !! n = C !! n⌝ ∗
    ghost_map_auth coneristpinvGS_tp_name 1 m.

Definition con_tp_inv_ini : iProp Σ :=
  ghost_map_auth coneristpinvGS_tp_name 1 ∅.

Lemma con_tp_inv_lookup C n e dq :
  con_tp_inv C -∗ n ↪cthread{dq} e -∗ ⌜C !! n = Some e⌝.
Proof.
  iIntros "(%m&%Heq&Hm) Hn".
  iPoseProof (ghost_map_lookup with "Hm Hn") as "%HH".
  iPureIntro. rewrite -Heq. done.
Qed.

Lemma con_tp_inv_update C n e1 e2 :
  con_tp_inv C -∗ n ↪cthread e1 ==∗ con_tp_inv (<[n := e2]> C) ∗ n ↪cthread e2.
Proof.
  iIntros "Htp Hn".
    iPoseProof (con_tp_inv_lookup with "Htp Hn") as "%Hlu".
    iDestruct "Htp" as "(%m&%Hm&Hm)".
    iMod (ghost_map_update e2 with "Hm Hn") as "(Hm&$)".
    iModIntro. iExists _. iFrame "Hm".
    iPureIntro.
    intros n'. destruct (decide (n = n')) as [->|Hne].
    - rewrite lookup_insert list_lookup_insert //.
      eapply lookup_lt_is_Some. by eexists.
    - rewrite list_lookup_insert_ne // lookup_insert_ne //.
Qed.

Lemma con_tp_inv_new_threads C efs :
  con_tp_inv C ==∗
  con_tp_inv (C ++ efs) ∗ [∗ list] k↦e ∈ efs, (length C + k) ↪cthread e.
Proof.
  Search map_seq.
  iIntros "(%m&%Hm&Hm)".
  iMod (ghost_map_insert_big (map_seq (length C) efs)  with "Hm") as "(Hm&Hefs)".
  - eapply map_disjoint_spec. intros n e1 e2 (Hlen&Hluefs)%lookup_map_seq_Some Hl2.
    rewrite Hm in Hl2. eapply lookup_lt_Some in Hl2. lia.
  - 
Admitted.

Lemma con_tp_inv_set C :
  con_tp_inv_ini ==∗ con_tp_inv C ∗ [∗ list] n↦e ∈ C, n ↪cthread e.
Proof.
  iIntros "Hauth".
  iMod (con_tp_inv_new_threads [] C with "[Hauth]") as "[Hauth Hfrags]".
  { rewrite /con_tp_inv. simpl. iFrame. iPureIntro.
    intros ?. rewrite lookup_empty lookup_nil //. }
  simpl. iModIntro. iFrame.
Qed.

End coneristpinv.

Lemma con_tp_inv_alloc `{!ghost_mapG Σ nat Λ.(expr)} :
  ⊢ |==> ∃ γ, let H := ConeristpInvGS Σ Λ _ γ in con_tp_inv_ini.
Proof.
  iMod (ghost_map_alloc_empty) as (γ) "$". done.
Qed.

Inductive con_prim_steps {Λ : conLanguage} :
    Λ.(expr) → Λ.(state) → Λ.(expr) → Λ.(state) → list Λ.(expr) → Prop :=
  | con_prim_steps_once e1 σ1 e2 efs :
      pure_step e1 e2 →
      con_prim_steps e1 σ1 e2 σ1 efs.

From clutch.con_prob_lang Require Import lang.

Section NoAlloc.

Fixpoint no_allocN_expr (e : expr) : Prop :=
  match e with
  | AllocN _ _ => False
  | Val v => no_allocN_val v
  | Var _ => True
  | Rec _ _ e => no_allocN_expr e
  | App e1 e2 => no_allocN_expr e1 ∧ no_allocN_expr e2
  | UnOp _ e => no_allocN_expr e
  | BinOp _ e1 e2 => no_allocN_expr e1 ∧ no_allocN_expr e2
  | If e0 e1 e2 => no_allocN_expr e0 ∧ no_allocN_expr e1 ∧ no_allocN_expr e2
  | Pair e1 e2 => no_allocN_expr e1 ∧ no_allocN_expr e2
  | Fst e | Snd e | InjL e | InjR e => no_allocN_expr e
  | Case e0 e1 e2 => no_allocN_expr e0 ∧ no_allocN_expr e1 ∧ no_allocN_expr e2
  | Load e => no_allocN_expr e
  | Store e1 e2 => no_allocN_expr e1 ∧ no_allocN_expr e2
  | AllocTape e => False
  | Rand e1 e2 => no_allocN_expr e1 ∧ no_allocN_expr e2
  | Tick e => no_allocN_expr e
  | Fork e => no_allocN_expr e
  | CmpXchg e0 e1 e2 => no_allocN_expr e0 ∧ no_allocN_expr e1 ∧ no_allocN_expr e2
  | Xchg e1 e2 => no_allocN_expr e1 ∧ no_allocN_expr e2
  | FAA e1 e2 => no_allocN_expr e1 ∧ no_allocN_expr e2
  end
with no_allocN_val (v : val) : Prop :=
  match v with
  | LitV _ => True
  | RecV _ _ e => no_allocN_expr e
  | PairV v1 v2 => no_allocN_val v1 ∧ no_allocN_val v2
  | InjLV v => no_allocN_val v
  | InjRV v => no_allocN_val v
  end.

Lemma no_allocN_fill_item_inv (Ki : ectx_item) (e : expr) :
  no_allocN_expr (fill_item Ki e) → no_allocN_expr e.
Proof. destruct Ki; simpl; tauto. Qed.

Lemma no_allocN_fill_inv (K : ectx con_prob_ectx_lang) (e : expr) :
  no_allocN_expr (fill K e) → no_allocN_expr e.
Proof.
  revert e. induction K as [|Ki K IH] using rev_ind; [done|].
  intros e H. rewrite /fill foldl_app /= in H.
  apply no_allocN_fill_item_inv in H. apply IH in H. done.
Qed.

Lemma no_allocN_fill_item_compat (Ki : ectx_item) (e1 e2 : expr) :
  no_allocN_expr (fill_item Ki e1) → no_allocN_expr e2 →
  no_allocN_expr (fill_item Ki e2).
Proof. destruct Ki; simpl; tauto. Qed.

Lemma no_allocN_fill_compat (K : ectx con_prob_ectx_lang) (e1 e2 : expr) :
  no_allocN_expr (fill K e1) → no_allocN_expr e2 →
  no_allocN_expr (fill K e2).
Proof.
  revert e1 e2. 
  rewrite /fill /=. 
  induction K as [|Ki K IH] using rev_ind; [done|].
  setoid_rewrite foldl_app => /=.
  intros e1 e2 H Hna.
  eapply no_allocN_fill_item_compat; eauto.
  eapply IH; eauto.
  by eapply no_allocN_fill_item_inv.
Qed.

Lemma no_allocN_Forall_insert (C : list expr) n e_old e_new :
  Forall no_allocN_expr C →
  C !! n = Some e_old →
  no_allocN_expr e_new →
  Forall no_allocN_expr (<[n := e_new]> C).
Proof.
  intros Hfa Hn Hnew.
  apply Forall_forall. intros e He.
  apply elem_of_list_lookup in He as [i Hi].
  destruct (decide (i = n)) as [->|Hne].
  - rewrite list_lookup_insert in Hi; [|by eapply lookup_lt_Some].
    by simplify_eq.
  - rewrite list_lookup_insert_ne in Hi; [|done].
    eapply Forall_lookup; done.
Qed.

Lemma no_allocN_Forall_app (C1 C2 : list expr) :
  Forall no_allocN_expr C1 → Forall no_allocN_expr C2 →
  Forall no_allocN_expr (C1 ++ C2).
Proof. intros. by apply Forall_app. Qed.

Lemma no_allocN_subst (x : string) (v : val) (e : expr) :
  no_allocN_val v → no_allocN_expr e → no_allocN_expr (subst x v e).
Proof.
  intros Hv. induction e; simpl in *; try tauto.
  - case_decide; intros; [exact Hv | done].
  - case_decide; tauto.
Qed.

Lemma no_allocN_subst' (bx : binder) (v : val) (e : expr) :
  no_allocN_val v → no_allocN_expr e → no_allocN_expr (subst' bx v e).
Proof. destruct bx; simpl; [done | apply no_allocN_subst]. Qed.

Lemma no_allocN_head_step_val (e1 : expr) (v2 : val) (σ : state)
    (HnoallocH : map_Forall (λ _ v, no_allocN_val v) σ.(heap)) :
  no_allocN_expr e1 →
  head_step_rel e1 σ (of_val v2) σ [] →
  no_allocN_val v2.
Proof.
Admitted.

End NoAlloc.