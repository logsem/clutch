From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt.
From clutch.eris Require Import infinite_tape.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Section lazy_real.

  (** Program *)
 Definition get_chunk : val :=
    λ: "α" "chnk",
      match: !"chnk" with
      | NONE =>
          let: "b" := rand("α") #1 in
          let: "next" := ref NONEV in
          let: "val" := ("b", "next") in
          "chnk" <- SOME "val";;
          "val"
      | SOME "val" => "val"
      end.

  Definition cmpZ : val :=
    λ: "z1" "z2",
      if: "z1" < "z2" then #(-1)
      else
        if: "z2" < "z1" then #1
        else #0.

  Definition cmp_list : val :=
    rec: "cmp_list" "α1" "cl1" "α2" "cl2" :=
      let: "c1n" := get_chunk "α1" "cl1" in
      let: "c2n" := get_chunk "α2" "cl2" in
      let: "res" := cmpZ (Fst "c1n") (Fst "c2n") in
      if: "res" = #0 then
        "cmp_list" "α1" (Snd "c1n") "α2" (Snd "c2n")
      else
        "res".

  Definition init : val :=
    λ: <>,
      let: "hd" := ref NONEV in
      let: "α" := alloc #1 in
      ("α", "hd").

  Definition cmp : val :=
    λ: "lz1" "lz2",
      (* We short-circuit if the two locations are physically equal to avoid forcing sampling *)
      if: Snd "lz1" = Snd "lz2" then
        #0
      else
        cmp_list (Fst "lz1") (Snd "lz1") (Fst "lz2") (Snd "lz2").

  Context `{!erisGS Σ}.

  Definition comparison2z c : Z :=
    match c with
    | Eq => 0
    | Lt => -1
    | Gt => 1
    end.

  Lemma comparison2z_lt (z1 z2 : Z) :
    (z1 < z2)%Z →
    comparison2z (Z.compare z1 z2) = (-1)%Z.
  Proof.
    rewrite /comparison2z.
    case_match eqn:Heq;
      rewrite ?Z.compare_eq_iff ?Z.compare_gt_iff in Heq; lia.
  Qed.

  Lemma comparison2z_eq (z1 z2 : Z) :
    (z1 = z2)%Z →
    comparison2z (Z.compare z1 z2) = 0%Z.
  Proof.
    rewrite /comparison2z.
    case_match eqn:Heq;
      rewrite ?Z.compare_lt_iff ?Z.compare_gt_iff in Heq; lia.
  Qed.

  Lemma comparison2z_gt (z1 z2 : Z) :
    (z1 > z2)%Z →
    comparison2z (Z.compare z1 z2) = 1%Z.
  Proof.
    rewrite /comparison2z.
    case_match eqn:Heq;
      rewrite ?Z.compare_eq_iff ?Z.compare_lt_iff in Heq; lia.
  Qed.

  Lemma wp_cmpZ (z1 z2 : Z) E :
    ⟨⟨⟨ True ⟩⟩⟩
      cmpZ #z1 #z2 @ E
    ⟨⟨⟨ RET #(comparison2z (Z.compare z1 z2)); True%I ⟩⟩⟩.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /cmpZ.
    destruct (Z.compare_spec z1 z2).
    - wp_pures; case_bool_decide; [lia|].
      wp_pures; case_bool_decide; [lia|].
      wp_pures. iApply "HΦ"; eauto.
    - wp_pures; case_bool_decide; [|lia].
      wp_pures. iApply "HΦ"; eauto.
    - wp_pures; case_bool_decide; [lia|].
      wp_pures; case_bool_decide; [|lia].
      wp_pures. iApply "HΦ"; eauto.
  Qed.

  Fixpoint chunk_list (l : loc) (zs : list (fin 2)) : iProp Σ :=
    match zs with
    | [] => l ↦ NONEV
    | z :: zs =>
        ∃ l' : loc, l ↦ SOMEV (#z, #l') ∗ chunk_list l' zs
  end.

  Definition chunk_and_tape_seq α l (f: nat → (fin 2)) : iProp Σ :=
    ∃ zs f', ⌜f = append_bin_seq zs f' ⌝∗ chunk_list l zs ∗ infinite_tape α f'.

  Definition lazy_real (v : val) (r : R) : iProp Σ :=
    ∃ (l : loc) (α : loc) (f : nat → (fin 2)),
      ⌜v = (#lbl:α, #l)%V⌝ ∗
      ⌜ r = seq_bin_to_R f ⌝ ∗
      chunk_and_tape_seq α l f.

  Lemma chunk_list_hd_acc l zs :
    chunk_list l zs -∗
    (∃ v, l ↦ v ∗ (l ↦ v -∗ chunk_list l zs)).
  Proof.
    destruct zs.
    - simpl. iIntros. iExists _. iFrame. eauto.
    - simpl. iIntros "(%&H1&H2)". iExists _. iFrame.
      iIntros "H". iExists _. iFrame.
  Qed.

  Lemma chunk_and_tape_list_ne (l1 l2 α1 α2 : loc) f1 f2 :
    chunk_and_tape_seq α1 l1 f1 -∗ chunk_and_tape_seq α2 l2 f2 -∗ ⌜l1 ≠ l2⌝.
  Proof.
    iIntros "(% & % & _ & Hl1 & _) (% & % & _ & Hl2 & _)".
    iDestruct (chunk_list_hd_acc with "Hl1") as (?) "[Hl1 _]".
    iDestruct (chunk_list_hd_acc with "Hl2") as (?) "[Hl2 _]".
    iApply (ghost_map_elem_ne with "Hl1 Hl2").
  Qed.

  Lemma chunk_and_tape_list_cons_chunk (l l' : loc) (z : fin _) (f : nat → (fin 2)) α :
    l ↦ SOMEV (#z, #l') -∗
    chunk_and_tape_seq α l' f -∗
    chunk_and_tape_seq α l (cons_bin_seq z f).
  Proof.
    iIntros "Hl Htape". iDestruct "Htape" as (zs1 zs2 Heq) "(Hchunks&Hlist)".
    iExists (z :: zs1), zs2.
    iSplit.
    { rewrite Heq /=//. }
    iSplitL "Hl Hchunks".
    { rewrite /=. iExists l'. iFrame. }
    iFrame.
  Qed.

  (*
  Lemma rwp_get_chunk α l E :
    ⟨⟨⟨ chunk_and_tape_seq α l f ⟩⟩⟩
      get_chunk #lbl:α #l @ E
    ⟨⟨⟨ (z : fin 2) (l' : loc), RET (#z, #l');
        chunk_and_tape_list α l' [] ∗
        (∀ zs, chunk_and_tape_list α l' zs -∗ chunk_and_tape_list α l (z :: zs)) ⟩⟩⟩.
  Proof.
    iIntros (Ψ) "(%zs1 & %zs2 & %Heq & Hl & Hα) HΨ".
    rewrite /get_chunk.
    symmetry in Heq. apply app_nil in Heq as [-> ->].
    wp_pures.
    wp_load. wp_pures.
    wp_apply (rwp_rand_tape_empty with "Hα").
    iIntros (n) "Hα". wp_pures. wp_alloc l' as "Hl'". wp_pures. wp_store.
    iModIntro. iApply "HΨ".
    iSplitR "Hl".
    { iExists [], []. iSplit; [done|]. iFrame. }
    { iIntros (?) "Htail". iApply (chunk_and_tape_list_cons_chunk with "Hl Htail"). }
  Qed.
   *)

  Lemma wp_get_chunk_cons z f α l E :
    ⟨⟨⟨ chunk_and_tape_seq α l (cons_bin_seq z f) ⟩⟩⟩
      get_chunk #lbl:α #l @ E
    ⟨⟨⟨ l', RET (#z, #l');
        chunk_and_tape_seq α l' f ∗
       (∀ f, chunk_and_tape_seq α l' f -∗ chunk_and_tape_seq α l (cons_bin_seq z f)) ⟩⟩⟩.
  Proof.
    iIntros (Ψ) "(%zs1 & %zs2 & %Heq & Hl & Hα) HΨ".
    rewrite /get_chunk.
    wp_pures.
    destruct zs1 as [| z' zs1'].
    - wp_load. wp_pures.
      rewrite /= in Heq.
      assert (zs2 = cons_bin_seq z f) as ->.
      { rewrite Heq. eauto. }
      wp_apply (wp_rand_infinite_tape_cons with "Hα").
      iIntros "Hα".
      wp_pures. wp_alloc l' as "Hl'". wp_pures. wp_store.
      iModIntro. iApply "HΨ". iSplitR "Hl".
      { iExists [], f. iSplit; [done|]. iFrame. }
      { iIntros (?) "Htail". iApply (chunk_and_tape_list_cons_chunk with "[$] [$]"). }
    - rewrite /=. iDestruct "Hl" as "(%l' & Hl & Hl')".
      wp_load. wp_pures.
      assert (z = z').
      { cut (cons_bin_seq z f O = append_bin_seq (z' :: zs1') zs2 O); first done.
        rewrite Heq //=. }
      subst.
      iModIntro. iApply "HΨ".
      iSplitR "Hl".
      { iExists _, _. iFrame. apply cons_bin_seq_inv in Heq as (Heq1&Heq2). auto. }
      { iIntros (?) "Htail". iApply (chunk_and_tape_list_cons_chunk with "[$] [$]"). }
  Qed.

  Lemma wp_cmp_list α1 α2 l1 l2 E zs1 zs2 :
    ⟨⟨⟨ chunk_and_tape_seq α1 l1 zs1 ∗
        chunk_and_tape_seq α2 l2 zs2 ⟩⟩⟩
      cmp_list #lbl:α1 #l1 #lbl:α2 #l2 @ E
    ⟨⟨⟨ (z : Z), RET #z;
        (⌜ z = (-1)%Z ∧ (seq_bin_to_R zs1 <= seq_bin_to_R zs2)%R ⌝ ∨
         ⌜ z = 1%Z  ∧ (seq_bin_to_R zs2 <= seq_bin_to_R zs2)%R ⌝) ∗
        chunk_and_tape_seq α1 l1 zs1 ∗
        chunk_and_tape_seq α2 l2 zs2
         ⟩⟩⟩.
  Proof.
  Abort.
  (*
    iIntros (?).
    iInduction zs1 as [|z1 zs1] "IH" forall (l1 l2 zs2 b).
    - iInduction zs2 as [|z2 zs2] "IH" forall (l1 l2 b).
      + iIntros (Ψ) "(Hspec & Hl1 & Hl2) HΨ".
        destruct N; [lia|].
        wp_apply (rwp_cmp_list_nil_nil with "[$Hspec $Hl1 $Hl2]").
        iIntros (b' z1 z2 zs) "(Hspec & % & Hl1 & Hl2)".
        iApply ("HΨ").
        iFrame. iSplit.
        { iPureIntro. apply prefix_nil. }
        iSplit.
        { iPureIntro. apply prefix_nil. }
        iSplit; [done|].
        iPureIntro. lia.
      + iIntros (Ψ) " (Hspec & Hl1 & Hl2) HΨ".
        rewrite {2}/cmp_list. wp_pures.
        wp_apply (rwp_get_chunk_nil with "Hl1").
        iIntros (z1 l1') "(Hl1' & Hl1)". wp_pures.
        wp_apply (rwp_get_chunk_cons with "Hl2").
        iIntros (l2') "[Hl2' Hl2]".
        wp_pures.
        wp_apply wp_cmpZ; [done|]; iIntros "_".
        wp_pures.
        destruct (Z.compare_spec z1 z2)
          as [? | Hl | Hgt]; simplify_eq=>/=.
        * do 3 wp_pure _.
          wp_apply ("IH" with "[$Hspec $Hl1' $Hl2']").
          iIntros (???????)  "(Hl1' & Hl2' & % & % & Hspec)".
          iSpecialize ("Hl1" with "Hl1'").
          iSpecialize ("Hl2" with "Hl2'").
          rewrite 2!app_comm_cons.
          iApply "HΨ". iFrame.
          iSplit; [iPureIntro; apply prefix_nil|].
          iPureIntro. by apply prefix_cons.
        * wp_pures.
          iSpecialize ("Hl1" with "Hl1'").
          iSpecialize ("Hl2" with "Hl2'").
          iModIntro.
          iSpecialize ("HΨ" $! _ _ z1 z2 [] [] zs2).
          rewrite comparison2z_lt //.
          iApply "HΨ".
          iFrame.
          iSplit; [iPureIntro; apply prefix_nil|].
          iSplit; [done|].
          iSplit; [|iPureIntro; lia].
          iPureIntro. intros ->; lia.
        * wp_pures.
          iSpecialize ("Hl1" with "Hl1'").
          iSpecialize ("Hl2" with "Hl2'").
          iModIntro.
          iSpecialize ("HΨ" $! _ _ z1 z2 [] [] zs2).
          rewrite comparison2z_gt; [|lia].
          iApply "HΨ".
          iFrame. iPureIntro.
          split; [apply prefix_nil|].
          split; [done|].
          split; [|lia]. intros ->; lia.
    - destruct zs2 as [|z2 zs2].
      + iIntros (Ψ) "(Hspec & Hl1 & Hl2) HΨ".
        rewrite {2}/cmp_list. wp_pures.
        wp_apply (rwp_get_chunk_cons with "Hl1").
        iIntros (l1') "(Hl1' & Hl1)". wp_pures.
        wp_apply (rwp_get_chunk_nil with "Hl2").
        iIntros (z2 l2') "[Hl2' Hl2]".
        wp_pures.
        wp_apply wp_cmpZ; [done|]; iIntros "_".
        wp_pures.
        destruct (Z.compare_spec z1 z2)
          as [? | Hlt | Hgt]; simplify_eq=>/=.
        * do 3 wp_pure _.
          wp_apply ("IH" with "[$Hspec $Hl1' $Hl2']").
          iIntros (???????)  "(Hl1' & Hl2' & % & % & Hspec)".
          iSpecialize ("Hl1" with "Hl1'").
          iSpecialize ("Hl2" with "Hl2'").
          rewrite 2!app_comm_cons.
          iApply "HΨ". iFrame.
          iPureIntro.
          split; [by apply prefix_cons|].
          apply prefix_nil.
        * wp_pures.
          iSpecialize ("Hl1" with "Hl1'").
          iSpecialize ("Hl2" with "Hl2'").
          iModIntro.
          iSpecialize ("HΨ" $! _ _ z1 z2 [] zs1 []).
          rewrite comparison2z_lt //.
          iApply "HΨ".
          iFrame. iPureIntro.
          split; [done|].
          split; [apply prefix_nil|].
          split; [|lia]. intros ->; lia.
        * wp_pures.
          iSpecialize ("Hl1" with "Hl1'").
          iSpecialize ("Hl2" with "Hl2'").
          iModIntro.
          iSpecialize ("HΨ" $! _ _ z1 z2 [] zs1 []).
          rewrite comparison2z_gt; [|lia].
          iApply "HΨ".
          iFrame. iPureIntro.
          split; [done|].
          split; [apply prefix_nil|].
          split; [|lia]. intros ->; lia.
      + iIntros (Ψ) "(Hspec & Hl1 & Hl2) HΨ".
        rewrite {2}/cmp_list. wp_pures.
        wp_apply (rwp_get_chunk_cons with "Hl1").
        iIntros (l1') "(Hl1' & Hl1)". wp_pures.
        wp_apply (rwp_get_chunk_cons with "Hl2").
        iIntros (l2') "[Hl2' Hl2]".
        wp_pures.
        wp_apply wp_cmpZ; [done|]; iIntros "_".
        wp_pures.
        destruct (Z.compare_spec z1 z2)
          as [? | Hlt | Hgt]; simplify_eq=>/=.
        * do 3 wp_pure _.
          wp_apply ("IH" with "[$Hspec $Hl1' $Hl2']").
          iIntros (???????)  "(Hl1' & Hl2' & % & % & Hspec)".
          iSpecialize ("Hl1" with "Hl1'").
          iSpecialize ("Hl2" with "Hl2'").
          rewrite 2!app_comm_cons.
          iApply "HΨ". iFrame.
          iPureIntro.
          split; by apply prefix_cons.
        * wp_pures.
          iSpecialize ("Hl1" with "Hl1'").
          iSpecialize ("Hl2" with "Hl2'").
          iModIntro.
          iSpecialize ("HΨ" $! _ _ z1 z2 [] zs1 zs2).
          rewrite comparison2z_lt //.
          iApply "HΨ".
          iFrame. iPureIntro.
          split; [done|]. split; [done|]. split; [|lia]. intros ->; lia.
        * wp_pures.
          iSpecialize ("Hl1" with "Hl1'").
          iSpecialize ("Hl2" with "Hl2'").
          iModIntro.
          iSpecialize ("HΨ" $! _ _ z1 z2 [] zs1 zs2).
          rewrite comparison2z_gt; [|lia].
          iApply "HΨ".
          iFrame. iPureIntro.
          split; [done|]. split; [done|]. split; [|lia]. intros ->; lia.
  Qed.

  Lemma rwp_init E :
    ⟨⟨⟨ True ⟩⟩⟩
      init #() @ E
    ⟨⟨⟨ v, RET v; lazy_no [] v ⟩⟩⟩.
  Proof.
    iIntros (Ψ) "_ HΨ".
    wp_rec.
    wp_alloc l as "Hl".
    wp_pures.
    wp_apply rwp_alloc_tape; [done|].
    iIntros (α) "Hα".
    wp_pures.
    iModIntro.
    iApply "HΨ".
    iExists _, _. iSplit; [done|].
    iExists [], []. by iFrame.
  Qed.

  Definition cmps (N : nat) : iProp Σ := ∃ b M, specF (b, b, M) ∗ ⌜M ≥ N⌝.

  Lemma rwp_cmp E v1 v2 zs1 zs2 N :
    (N > 0)%nat →
    ⟨⟨⟨ lazy_no zs1 v1 ∗ lazy_no zs2 v2 ∗ cmps N ⟩⟩⟩
      cmp v1 v2 @ E
    ⟨⟨⟨ (z : Z) zs1' zs2', RET #z;
        lazy_no (zs1 ++ zs1') v1 ∗ lazy_no (zs2 ++ zs2') v2 ∗ cmps (N - 1) ⟩⟩⟩.
  Proof.
    iIntros (? Ψ) "((%l1 & %α1 & -> & Hl1) & (%l2 & %α2 & -> & Hl2) & (% & % & Hcmps & %)) HΨ".
    wp_rec. wp_pures.
    iDestruct (chunk_and_tape_list_ne with "Hl1 Hl2") as %?.
    rewrite bool_decide_eq_false_2; [|by intros [=]].
    wp_pures.
    destruct M; [lia|].
    wp_apply (rwp_cmp_list with "[$Hcmps $Hl1 $Hl2]"); [lia|].
    iIntros (???????) "(Hl1 & Hl2 & [%zs1'' ->] & [%zs2'' ->] & % & Hs & %)".
    iApply "HΨ".
    iSplitL "Hl1".
    { iExists _, _. by iFrame. }
    iSplitL "Hl2".
    { iExists _, _. by iFrame. }
    iFrame. eauto with lia.
  Qed.
   *)

End lazy_real.
