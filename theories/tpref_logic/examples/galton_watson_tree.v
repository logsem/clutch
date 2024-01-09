From Coq Require Import Reals Psatz.
From iris.base_logic.lib Require Import na_invariants.
From clutch.prob_lang Require Import lang notation.
From clutch.tpref_logic Require Import seq_weakestpre spec primitive_laws proofmode adequacy.
From clutch.prob Require Import distribution markov.
From clutch.tpref_logic.examples.lib Require Import list.
Set Default Proof Using "Type*".

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
    add_task (sample_node "child_dist" "rinit" "q") "q";;
    run "q";;
    ! "rinit".

Section task_loop_spec.
  Context `{tprG (gwp μ) Σ, seqG Σ}.
  Context (M : nat) (α : loc) (N : namespace).

  Definition task_spec (f q : val) (queue : valO -d> natO -d> iPropO Σ) : iPropO Σ :=
    tc_opaque (▷ (∀ n m, queue q n -∗ α ↪ (M; [m]) -∗ SEQ f #() {{ _, queue q (n + m)%nat ∗ α ↪ (M; []) }}))%I.

  #[local] Instance queue_pre_contractive f q : Contractive (task_spec f q).
  Proof. rewrite /task_spec /tc_opaque /seq_weakestpre.seq => n ???. f_contractive. repeat f_equiv. Qed.

  Definition task_queue : val → nat → iProp Σ := queue task_spec.

  Lemma wp_run n q :
    Rcoupl (dunifP M) μ (λ n m, fin_to_nat n = m) →
    task_queue q n ∗ specF n ∗ α ↪ (M; [])
    ⊢ SEQ run q {{ _, ∃ m, task_queue q m ∗ specF m ∗ α ↪ (M; []) }}.
  Proof.
    iIntros (Hcpl) "(Hq & Hspec & Hα) Hna".
    iLöb as "IH" forall (n).
    wp_rec.
    destruct n.
    - wp_apply (wp_queue_take_0 with "Hq").
      iIntros "Hq". wp_pures.
      iModIntro. iFrame. iExists _. iFrame.
    - wp_apply (wp_queue_take_Sn with "Hq").
      iIntros (f) "[Hq Hf]".
      wp_pures.
      iApply (rwp_couple_tape _ (λ m s, s = n + m)%nat); [|iFrame "Hspec Hα"].
      (* Notice how the model step in the preceding line introduces a later in the goal. *)
      { iIntros (σ Hσ).
        rewrite /state_step /=.
        rewrite bool_decide_eq_true_2; [|by eapply elem_of_dom_2].
        rewrite lookup_total_alt Hσ /=.
        eapply Rcoupl_dbind; [|apply Hcpl].
        intros n1 n2 <-.
        apply Rcoupl_dret; eauto. }
      rewrite {2}/task_spec /tc_opaque.
      iIntros "!>" (m ? ->) "Hspec Hα /=".
      (* Notice how the above line strips a later from the goal and the Loeb induction hyptothesis. *)
      iSpecialize ("Hf" with "Hq Hα Hna").
      wp_apply (rwp_wand with "Hf").
      iIntros (v) "(Hna & Hq & Hα)".
      wp_pures.
      wp_apply ("IH" with "Hq Hspec Hα Hna").
  Qed.

  Definition child_dist_spec (child_dist : val) : iProp Σ :=
    ∀ m, ⟨⟨⟨ α ↪ (M; [m]) ⟩⟩⟩ child_dist #() ⟨⟨⟨ RET #m; α ↪ (M; []) ⟩⟩⟩.

  Lemma wp_sample_node child_dist r (q : val) :
    seq_inv N (∃ xs l, r ↦ l ∗ is_list l xs) ∗
    child_dist_spec child_dist
    ⊢ SEQ sample_node child_dist #r q {{ f, task_spec f q task_queue }}.
  Proof.
    iIntros "(#Hr & #Hc) Hna".
    iLöb as "IH" forall (r) "Hr".
    wp_rec. wp_pures.
    iModIntro. iFrame.
    iIntros "!> %n %m Hq Hα Hna".
    (* Notice how the above line strips later from the goal and the Loeb IH since task_spec has a later in front *)
    wp_pures.
    wp_apply ("Hc" with "Hα"); iIntros "Hα".
    wp_pures.
    wp_apply (wp_listP_init (λ _, True)%I (λ m, task_queue q (n + m) ∗ na_own seqG_name ⊤)%I with "[Hq Hna]").
    { rewrite Nat.add_0_r. iFrame.
      iIntros (s Ψ') "!# [Hq Hna] HΨ'".
      wp_pures.
      wp_apply wp_list_create; [done|].
      iIntros (v) "Hv".
      wp_alloc l as "Hl".
      wp_pures.
      iMod (na_inv_alloc _ _ N (∃ xs v, l ↦ v ∗ is_list v xs)%I with "[Hv Hl]") as "#Hl".
      { iModIntro. iExists _, _. iFrame. }
      iSpecialize ("IH" with "Hna Hl").
      wp_apply (rwp_wand with "IH").
      iIntros (f) "[Hna Hf]".
      wp_apply (wp_queue_add with "[$Hq $Hf]").
      iIntros "Hq".
      wp_pures.
      iModIntro. iApply "HΨ'".
      rewrite plus_n_Sm.
      iFrame. }
    iIntros (l xs) "(Hl & [Hq Hna] & %)".
    wp_pures.
    iMod (na_inv_acc with "Hr Hna") as "(>(%&%& Hr' & Hxs) & Hna & Hclose)"; [set_solver| |].
    { set_solver. }
    wp_store.
    iMod ("Hclose" with "[Hr' Hl $Hna]").
    { iModIntro. iExists _, _. iFrame. iDestruct "Hl" as "[$ ?]". }
    by iFrame.
  Qed.

  Lemma wp_gen_tree child_dist :
    Rcoupl (dunifP M) μ (λ n m, fin_to_nat n = m) →
    child_dist_spec child_dist ∗ specF 1%nat ∗ α ↪ (M; [])
    ⊢ SEQ gen_tree child_dist {{ _, True }}.
  Proof using N.
    iIntros (?) "(#Hc & Hspec & Hα) Hna".
    wp_rec.
    wp_apply wp_list_create; [done|].
    iIntros (l) "Hl".
    wp_alloc r as "Hr".
    wp_pures.
    wp_apply (wp_queue_create task_spec); [done|].
    iIntros (q) "Hq".
    wp_pures.
    iMod (na_inv_alloc _ _ N (∃ xs l, r ↦ l ∗ is_list l xs)%I with "[Hr Hl]") as "#Hl".
    { iModIntro. iExists _, _. iFrame. }
    iPoseProof (wp_sample_node with "[$Hl $Hc] Hna") as "H".
    wp_apply (rwp_wand with "H").
    iIntros (f) "[Hna Hf]".
    wp_apply (wp_queue_add with "[$Hq $Hf]").
    iIntros "Hq".
    wp_pures.
    iPoseProof (wp_run with "[$Hq $Hspec $Hα] Hna") as "H"; [done|].
    wp_apply (rwp_wand with "H").
    iIntros (?) "[Hna (% & Hq & Hspec & Hα)]".
    wp_pures.
    iMod (na_inv_acc with "Hl Hna") as "(>(%&%& Hr' & Hxs) & Hna & Hclose)"; [set_solver| |].
    { set_solver. }
    wp_load.
    iMod ("Hclose" with "[Hr' Hxs $Hna]").
    { iModIntro. iExists _, _. iFrame. }
    by iFrame.
  Qed.

End task_loop_spec.

Definition gen_tree_unif3 : val :=
  λ: <>,
    let: "α" := alloc #3 in
    let: "child_dist" := λ: <>, rand("α") #3 in
    gen_tree "child_dist".

Definition dunif3 := dmap fin_to_nat (dunifP 3).

Section unif_3.
  Context `{tprG (gwp dunif3) Σ, seqG Σ}.

  Lemma wp_gen_tree_unif3 :
    specF 1%nat ⊢ SEQ gen_tree_unif3 #() {{ _, True }}.
  Proof.
    iIntros "Hspec Hna". wp_rec.
    wp_apply rwp_alloc_tape; [done|].
    iIntros (α) "Hα".
    wp_pures.
    wp_apply (wp_gen_tree 3 _ nroot with "[$Hα $Hspec] Hna").
    { rewrite -(dret_id_right (dunifP 3)) /dunif3 /dmap.
      eapply Rcoupl_dbind; [|eapply Rcoupl_eq].
      intros n m ->. by apply Rcoupl_dret. }
    iIntros (n) "!#"; iIntros (Ψ) "Hα HΨ".
    wp_pures.
    by wp_apply (rwp_rand_tape with "Hα").
  Qed.

End unif_3.
