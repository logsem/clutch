From clutch.prob Require Import distribution markov.
From clutch.prob_lang Require Import lang notation.
From clutch.tpref_logic Require Import weakestpre spec primitive_laws proofmode.

(** * Linked list  *)
Definition list_create : val :=
  λ: <>, NONEV.

Definition list_cons : val :=
  λ: "v" "l", SOME (ref ("v", "l")).

Definition list_init : val :=
  rec: "list_init" "n" "f" :=
    if: "n" = #0 then list_create #()
    else list_cons ("f" ("n" - #1)) ("list_init" ("n" - #1) "f").

Section list.
  Context `{!tprG δ Σ}.

  Fixpoint is_list (v : val) (xs : list val) : iProp Σ :=
    match xs with
    | [] => ⌜v = NONEV⌝
    | x :: xs =>
        ∃ (l : loc) (v' : val), ⌜v = SOMEV #l⌝ ∗ l ↦ (x, v')%V ∗ is_list v' xs
    end.

  #[global] Instance timeless_is_list l vs :
    Timeless (is_list l vs).
  Proof. revert l. induction vs as [|?] => l /=; apply _. Qed.

  Lemma wp_list_create E :
    ⟨⟨⟨ True ⟩⟩⟩
      list_create #() @ E
    ⟨⟨⟨ (l : val), RET l; is_list l [] ⟩⟩⟩.
  Proof.
    iIntros (Φ) "_ HΦ". wp_rec. iModIntro. iApply "HΦ". eauto.
  Qed.

  Lemma wp_list_cons v x xs E :
    ⟨⟨⟨ is_list v xs ⟩⟩⟩
      list_cons x v @ E
    ⟨⟨⟨ w, RET w; is_list w (x :: xs) ⟩⟩⟩.
  Proof.
    iIntros (Φ) "Hv HΦ".
    wp_rec. wp_pures. wp_alloc r as "Hr". wp_pures.
    iModIntro. iApply "HΦ". simpl. eauto.
    iExists _, _. by iFrame.
  Qed.

  Definition is_listP v xs P : iProp Σ := is_list v xs ∗ [∗ list] x ∈ xs, P x.

  Lemma wp_listP_create P E :
    ⟨⟨⟨ True ⟩⟩⟩
      list_create #() @ E
    ⟨⟨⟨ (l : val), RET l; is_listP l [] P ⟩⟩⟩.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_apply wp_list_create; [done|].
    iIntros (??).
    iApply "HΦ".
    by iSplit.
  Qed.

  Lemma wp_listP_cons v x xs E P :
    ⟨⟨⟨ is_listP v xs P ∗ P x ⟩⟩⟩
      list_cons x v @ E
    ⟨⟨⟨ w, RET w; is_listP w (x :: xs) P ⟩⟩⟩.
  Proof.
    iIntros (Φ) "[[Hv HPs] HP] HΦ".
    wp_apply (wp_list_cons with "Hv").
    iIntros (w) "Hw". iApply "HΦ". iFrame.
  Qed.

  Lemma wp_listP_init P Q (n : nat) (f : val) E :
    ⟨⟨⟨ Q 0 ∗
       ∀ (m : nat), ⟨⟨⟨ Q m ⟩⟩⟩ f #m @ E ⟨⟨⟨ v, RET v; P v ∗ Q (S m) ⟩⟩⟩ ⟩⟩⟩
      list_init #n f @ E
    ⟨⟨⟨ (l : val) (xs : list val), RET l; is_listP l xs P ∗ Q n ∗ ⌜length xs = n⌝ ⟩⟩⟩.
  Proof.
    iIntros (Ψ) "[HQ #Hf] HΨ".
    iInduction (n) as [|n] "IH" forall (Ψ).
    - wp_rec; wp_pures. wp_apply (wp_listP_create P); [done|].
      iIntros (l) "Hl". iApply "HΨ". by iFrame.
    - wp_rec; wp_pures.
      replace #(S n - 1) with #n; [|do 2 f_equal; lia].
      wp_apply ("IH" with "HQ").
      iIntros (v xs) "(Hx & HQ & <-)".
      wp_pures.
      replace #(S (length xs) - 1) with #(length xs); [|do 2 f_equal; lia].
      wp_apply ("Hf" with "HQ").
      iIntros (x) "[HP HQ]".
      wp_apply (wp_listP_cons with "[$Hx $HP]").
      iIntros (w) "Hw".
      iApply "HΨ". by iFrame.
  Qed.

End list.

Definition opt_to_val (ov : option val) :=
  match ov with
  | Some v => SOMEV v
  | None => NONEV
  end.

(** * Queue implemented using a linked list  *)
Definition queue_create : val :=
  λ: <>, ref (list_create #()).

Definition queue_add : val :=
  λ: "v" "q", "q" <- list_cons "v" !"q".

Definition queue_take : val :=
  λ: "q",
    let:m "v" := !"q" in
    let, ("x", "l") := ! "v" in
    "q" <- "l";;
    SOME "x".

Section queue.
  Context `{!tprG δ Σ}.

  Definition is_queue (q : val) (n : nat) (Q : val → iProp Σ) : iProp Σ :=
    ∃ (l : loc) (v : val) (xs : list val), ⌜q = #l⌝ ∗ ⌜length xs = n⌝ ∗ l ↦ v ∗ is_listP v xs Q.

  Implicit Type P : val → val → (valO -d> natO -d> iProp Σ) -d> iProp Σ.

  Definition queue_pre P (queue : valO -d> natO -d> iPropO Σ) : valO -d> natO -d> iPropO Σ :=
    (λ q n, is_queue q n (λ f, P f q queue))%I.

  #[local] Instance queue_pre_contractive `{∀ n q, Contractive (P n q)} :
    Contractive (queue_pre P).
  Proof.
    rewrite /queue_pre => n ?????. rewrite /is_queue /is_listP.
    do 13 f_equiv. by f_contractive.
  Qed.

  Definition queue P `{∀ n q, Contractive (P n q)} : val → nat → iProp Σ := fixpoint (queue_pre P).

  Lemma queue_unfold P `{∀ n q, Contractive (P n q)} n q :
    queue P q n ⊣⊢ queue_pre P (queue P) q n.
  Proof. apply (fixpoint_unfold (queue_pre _)). Qed.

  Lemma wp_queue_create P `{∀ n q, Contractive (P n q)} E :
    ⟨⟨⟨ True ⟩⟩⟩
      queue_create #() @ E
    ⟨⟨⟨ q, RET q; queue P q 0 ⟩⟩⟩.
  Proof.
    iIntros (Φ) "_ HΦ". wp_rec.
    wp_rec.
    wp_alloc l as "Hl".
    iModIntro. iApply "HΦ".
    rewrite queue_unfold.
    iExists _, _, [].
    iFrame. rewrite /is_listP; eauto.
  Qed.

  Lemma wp_queue_add q x n P `{∀ n q, Contractive (P n q)} E :
    ⟨⟨⟨ queue P q n ∗ P x q (queue P) ⟩⟩⟩
      queue_add x q @ E
    ⟨⟨⟨ RET #(); queue P q (S n) ⟩⟩⟩.
  Proof.
    iIntros (Φ) "[Hq HP] HΦ".
    wp_rec. wp_pures.
    rewrite queue_unfold.
    iDestruct "Hq" as "(%l & %v & %xs & -> & %Hlen & Hl & H)".
    wp_load.
    wp_apply (wp_listP_cons with "[$H $HP]").
    iIntros (w) "Hw".
    wp_store.
    iModIntro. iApply "HΦ".
    rewrite queue_unfold.
    iExists _, _, _. iFrame.
    rewrite -Hlen //.
  Qed.

  Lemma wp_queue_take q n P `{∀ n q, Contractive (P n q)} E :
    ⟨⟨⟨ queue P q n ⟩⟩⟩
      queue_take q @ E
    ⟨⟨⟨ v, RET v; queue P q (n - 1) ∗
         ((⌜v = NONEV⌝ ∗ ⌜n = 0⌝) ∨ (∃ x m, ⌜v = SOMEV x⌝ ∗ ⌜n = S m⌝ ∗ P x q (queue P))) ⟩⟩⟩.
  Proof.
    iIntros (Φ) "Hq HΦ". wp_rec.
    rewrite queue_unfold.
    iDestruct "Hq" as "(%l & %v & %xs & -> & %Hlen & Hl & H)".
    wp_load.
    destruct xs; iSimpl in "H".
    - iDestruct "H" as "[-> Hv]".
      wp_pures.
      iModIntro. iApply "HΦ".
      iSplitL; [|eauto].
      rewrite queue_unfold.
      iExists _, _, _. iFrame.
      rewrite -Hlen //.
    - iDestruct "H" as "[H HPs] /=".
      iDestruct "H" as (l' v') "(-> & Hl' & Hxs)". wp_pures.
      wp_load. wp_pures.
      wp_store. wp_pures.
      iModIntro. iApply "HΦ".
      iDestruct "HPs" as "[HP HPs]".
      iSplitR "HP"; [|iRight; eauto].
      rewrite queue_unfold.
      iExists _, _, _. iFrame.
      rewrite -Hlen /= Nat.sub_0_r //.
  Qed.

  Lemma wp_queue_take_Sn P `{∀ n q, Contractive (P n q)} q n E :
    ⟨⟨⟨ queue P q (S n) ⟩⟩⟩
      queue_take q @ E
    ⟨⟨⟨ x, RET (SOMEV x); queue P q n ∗ P x q (queue P) ⟩⟩⟩.
  Proof.
    iIntros (Ψ) "Hq HΨ".
    iApply (wp_queue_take with "Hq").
    iIntros (v) "(Hq & [[% %] | (% & % & -> & _ & HP)])"; [done|].
    rewrite /= Nat.sub_0_r.
    iApply "HΨ". iFrame.
  Qed.

  Lemma wp_queue_take_0 P `{∀ n q, Contractive (P n q)} q E :
    ⟨⟨⟨ queue P q 0 ⟩⟩⟩
      queue_take q @ E
    ⟨⟨⟨ RET NONEV; queue P q 0 ⟩⟩⟩.
  Proof.
    iIntros (Ψ) "Hq HΨ".
    iApply (wp_queue_take with "Hq").
    iIntros (v) "(Hq & [[-> %] | (% & % & _ & % & _)])"; [|done].
    iApply "HΨ". iFrame.
  Qed.

End queue.
