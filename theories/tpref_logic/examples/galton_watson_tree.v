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
  rec: "run_loop" "q" :=
    match: queue_take "q" with
    | NONE => #()
    | SOME "f" =>
        "f" #();;
        "run_loop" "q"
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
  Context `{tprG (gwp μ) Σ}.
  Context `{na_invG Σ}.

  Context (p : na_inv_pool_name) (N : namespace).

  Definition queue_pred (f : val) : iProp Σ :=
    ∀ (P : iProp Σ), ⟨⟨⟨ ▷ P ⟩⟩⟩ f #() ⟨⟨⟨ RET #(); P ⟩⟩⟩.

  Definition queue (q : val) : iProp Σ :=
    na_inv p N (∃ n, specF n ∗ is_queue q n queue_pred)%I.

  Lemma wp_add_task q f E F :
    ↑N ⊆ E →
    ↑N ⊆ F →
    ⟨⟨⟨ queue q ∗ queue_pred f ∗ na_own p F ⟩⟩⟩
      add_task f q @ E
    ⟨⟨⟨ RET #(); na_own p F ⟩⟩⟩.
  Proof.
    iIntros (?? Ψ) "(Hq & #Hf & Hp) HΨ".
    iMod (na_inv_acc with "Hq Hp") as "((%n & >Hspec & Hq) & Hp & Hclose)"; [done|done|].
  Admitted.


  Lemma wp_run_loop n q E :
    ⟨⟨⟨ is_queue q n queue_pred ∗ specF n ⟩⟩⟩
      run q @ E
    ⟨⟨⟨ m, RET #(); is_queue q m queue_pred ∗ specF m ⟩⟩⟩.
  Proof. Admitted.

End task_loop_spec.
