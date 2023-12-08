From Coq Require Import Reals Psatz.
From iris.base_logic.lib Require Import na_invariants.
From clutch.prob_lang Require Import lang notation.
From clutch.tpref_logic Require Import weakestpre spec primitive_laws proofmode adequacy.
From clutch.prob Require Import distribution markov.
From clutch.tpref_logic.examples.lib Require Import list.

Section galton_watson_process.
  Context (μ : distr nat).

  Definition gwp_step (n : nat) : distr nat :=
    if n is S n then m ← μ; dret (n + m)%nat else dzero.

  Definition gwp_to_final (n : nat) : option nat :=
    if n is 0 then Some 0%nat else None.

  Definition gwp_mixin : MarkovMixin gwp_step gwp_to_final.
  Proof. constructor. by intros [] [] []; simplify_eq=>/=. Qed.

  Canonical Structure gwp : markov := Markov _ _ gwp_mixin.

End galton_watson_process.

(** * Task loop  *)
Definition add_task := queue_add.
Definition run : val :=
  rec: "run" "q" :=
    match: queue_take "q" with
    | NONE => #()
    | SOME "f" =>
        "f" #();;
        "run" "q"
    end.

(** * Galton-Watson tree *)
Definition sample_node : val :=
  rec: "sample_node" "child_dist" "r" "q" <> :=
    let: "num_children" := "child_dist" #() in
    let: "l" := list_init "num_children"
      (λ: <>, let: "r" := ref (list_create #()) in
              add_task ("sample_node" "child_dist" "r" "q") "q";;
             "r") in
    "r" <- "l".

Definition gen_tree : val :=
  λ: "child_dist",
    let: "rinit" := ref (list_create #()) in
    let: "q" := queue_create #() in
    queue_add (sample_node "child_dist" "rinit" "q") "q";;
    run "q";;
    ! "rinit".

Section task_loop_spec.
  Context `{tprG (gwp μ) Σ} (N : nat).

  Definition task_spec (f q : val) (queue : nat → val → iProp Σ) (α : loc) : iProp Σ :=
    tc_opaque (▷ ∀ n m E, ⟨⟨⟨ queue n q ∗ α ↪ (N; [m]) ⟩⟩⟩ f #() @ E ⟨⟨⟨ RET #(); queue (n + m)%nat q ⟩⟩⟩)%I.

  Definition queue_pre (queue : natO -d> valO -d> iPropO Σ) : natO -d> valO -d> iPropO Σ :=
    (λ n q, is_queue q n (λ f, ∃ α, α ↪ (N; []) ∗ task_spec f q queue α))%I.

  #[local] Instance queue_pre_contractive : Contractive queue_pre.
  Proof.
    rewrite /queue_pre => n ?????. rewrite /is_queue /is_listP /task_spec /tc_opaque.
    do 16 f_equiv. f_contractive; repeat f_equiv.
  Qed.

  Definition queue : nat → val → iProp Σ := fixpoint queue_pre.

  Lemma queue_unfold n q :
    queue n q ⊣⊢ queue_pre queue n q.
  Proof. apply (fixpoint_unfold queue_pre). Qed.

  Lemma wp_run n q E :
    Rcoupl (dunifP N) μ (λ n m, fin_to_nat n = m) →
    ⟨⟨⟨ queue n q ∗ specF n ⟩⟩⟩
      run q @ E
    ⟨⟨⟨ m, RET #(); queue m q ∗ specF m ⟩⟩⟩.
  Proof.
    iIntros (Hcpl Ψ) "[Hq Hspec] HΨ".
    iLöb as "IH" forall (n).
    wp_rec.
    iEval (rewrite queue_unfold /queue_pre) in "Hq".
    destruct n.
    - wp_apply (wp_queue_take_0 with "Hq").
      iIntros "Hq". wp_pures.
      iApply "HΨ". iModIntro.
      iFrame. by iApply queue_unfold.
    - wp_apply (wp_queue_take_Sn with "Hq").
      iIntros (f) "[Hq (%α & Hα & Hf)]".
      wp_pures.
      iApply (rwp_couple_tape _ (λ m s, s = n + m)%nat); [|iFrame].
      { iIntros (σ Hσ).
        rewrite /state_step /=.
        rewrite bool_decide_eq_true_2; [|by eapply elem_of_dom_2].
        rewrite lookup_total_alt Hσ /=.
        eapply Rcoupl_dbind; [|apply Hcpl].
        intros n1 n2 <-.
        apply Rcoupl_dret; eauto. }
      rewrite {2}/task_spec /tc_opaque.
      iIntros "!>" (m ? ->) "Hspec Hα /=".
      wp_pures.
      wp_apply ("Hf" with "[$Hα Hq]").
      { iEval (rewrite queue_unfold). iFrame.  }
      iIntros "Hq".
      wp_pures.
      wp_apply ("IH" with "Hq Hspec HΨ").
  Qed.

End task_loop_spec.
