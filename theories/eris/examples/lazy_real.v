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

  Definition lazy_real_uninit (v : val) : iProp Σ :=
    ∃ (l : loc) (α : loc),
      ⌜v = (#lbl:α, #l)%V⌝ ∗
      chunk_list l [] ∗
      α ↪ (1%nat; []).

  Lemma chunk_list_hd_acc l zs :
    chunk_list l zs -∗
    (∃ v, l ↦ v ∗ (l ↦ v -∗ chunk_list l zs)).
  Proof.
    destruct zs.
    - simpl. iIntros. iExists _. iFrame. eauto.
    - simpl. iIntros "(%&H1&H2)". iExists _. iFrame.
      iIntros "H". iExists _. iFrame.
  Qed.

  Lemma chunk_and_tape_seq_ne (l1 l2 α1 α2 : loc) f1 f2 :
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

  Lemma bin_ltZ_inv (z1 z2 : fin 2) :
    (z1 < z2)%Z → fin_to_nat z1 = O /\ fin_to_nat z2 = 1%nat.
  Proof.
    intros Hlt.
    destruct (bin_fin_to_nat_cases z1);
    destruct (bin_fin_to_nat_cases z2); try lia.
  Qed.

  (* Note the postcondition uses <= instead of <, because one can have the situation where
     zs1 = 0.011111 (recall: using binary notation)
     zs2 = 0.10
     These are both equal to 0.5, but cmp_list will return -1. *)

  Lemma wp_cmp_list α1 α2 l1 l2 E zs1 zs2 :
    ⟨⟨⟨ chunk_and_tape_seq α1 l1 zs1 ∗
        chunk_and_tape_seq α2 l2 zs2 ⟩⟩⟩
      cmp_list #lbl:α1 #l1 #lbl:α2 #l2 @ E
    ⟨⟨⟨ (z : Z), RET #z;
        (⌜ z = (-1)%Z ∧ (seq_bin_to_R zs1 <= seq_bin_to_R zs2)%R ⌝ ∨
         ⌜ z = 1%Z    ∧ (seq_bin_to_R zs2 <= seq_bin_to_R zs1)%R ⌝) ∗
        chunk_and_tape_seq α1 l1 zs1 ∗
        chunk_and_tape_seq α2 l2 zs2
         ⟩⟩⟩.
  Proof.
    iLöb as "IH" forall (l1 zs1 l2 zs2).
    iIntros (Φ) "(Hzs1&Hzs2) HΦ".
    wp_rec.
    wp_pures.
    destruct (bin_seq_hd zs1) as (z1&zs1'&->).
    destruct (bin_seq_hd zs2) as (z2&zs2'&->).
    wp_apply (wp_get_chunk_cons with "Hzs1").
    iIntros (l1') "(Hzs1'&Hclo1')".
    wp_pures.
    wp_apply (wp_get_chunk_cons with "Hzs2").
    iIntros (l2') "(Hzs2'&Hclo2')".
    wp_pures.
    wp_apply wp_cmpZ; [done|]; iIntros "_".
    wp_pures.
    destruct (Z.compare_spec z1 z2)
      as [? | Hl | Hgt]; simplify_eq=>/=.
    {
      wp_pures.
      wp_apply ("IH" with "[$Hzs1' $Hzs2']").
      iIntros (z) "(%Hcases&Hzs1'&Hzs2')".
      iDestruct ("Hclo1'" with "[$]") as "Hzs1".
      iDestruct ("Hclo2'" with "[$]") as "Hzs2".
      iApply "HΦ".
      iFrame.
      iPureIntro.
      destruct Hcases as [(->&Hle)|(->&Hle)].
      { left; split; auto. rewrite ?seq_bin_to_R_cons. nra. }
      { right; split; auto. rewrite ?seq_bin_to_R_cons. nra. }
    }
    {
      wp_pures.
      iDestruct ("Hclo1'" with "[$]") as "Hzs1".
      iDestruct ("Hclo2'" with "[$]") as "Hzs2".
      iApply "HΦ".
      iFrame.
      iModIntro. iPureIntro; left; split; auto.
      rewrite ?seq_bin_to_R_cons.
      destruct (bin_ltZ_inv z1 z2) as (->&->); first done.
      simpl.
      specialize (seq_bin_to_R_range zs1').
      specialize (seq_bin_to_R_range zs2').
      intros; nra.
    }
    {
      wp_pures.
      iDestruct ("Hclo1'" with "[$]") as "Hzs1".
      iDestruct ("Hclo2'" with "[$]") as "Hzs2".
      iApply "HΦ".
      iFrame.
      iModIntro. iPureIntro; right; split; auto.
      rewrite ?seq_bin_to_R_cons.
      destruct (bin_ltZ_inv z2 z1) as (->&->); first done.
      simpl.
      specialize (seq_bin_to_R_range zs1').
      specialize (seq_bin_to_R_range zs2').
      intros; nra.
    }
  Qed.

  Lemma wp_init E :
    ⟨⟨⟨ True ⟩⟩⟩
      init #() @ E
    ⟨⟨⟨ v, RET v; lazy_real_uninit v ⟩⟩⟩.
  Proof.
    iIntros (Ψ) "_ HΨ".
    wp_rec.
    wp_alloc l as "Hl".
    wp_pures.
    wp_apply wp_alloc_tape; [done|].
    iIntros (α) "Hα".
    wp_pures.
    iModIntro.
    iApply "HΨ".
    iExists _, _. iSplit; [done|].
    iFrame.
  Qed.

  Import Hierarchy.

  Lemma wp_lazy_real_presample_adv_comp E e v Φ (ε1 : R) (ε2 : R -> R) :
    to_val e = None →
    (forall r, (0 <= ε2 r)%R) ->
    is_RInt ε2 0 1 ε1 →
    lazy_real_uninit v ∗
      ↯ ε1 ∗
      (∀ r : R, ↯ (ε2 r) ∗ lazy_real v r -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hnonval Hle HRint) "(Hv&Hε&Hwp)".
    iDestruct "Hv" as (l α) "(->&Hchunk&Htape)".
    wp_apply (wp_presample_unif_adv_comp _ _ _ _ ε1 ε2 with "[-]"); try auto.
    iFrame "∗".
    iIntros (r) "(Herr&Htape)".
    iDestruct "Htape" as (f) "(Htape&%Hr)".
    iApply "Hwp".
    iFrame.
    iExists _.
    iPureIntro. split_and!; eauto.
  Qed.

  Lemma wp_cmp E v1 v2 r1 r2 :
    ⟨⟨⟨ lazy_real v1 r1 ∗ lazy_real v2 r2 ⟩⟩⟩
      cmp v1 v2 @ E
    ⟨⟨⟨ (z : Z) , RET #z;
        lazy_real v1 r1 ∗ lazy_real v2 r2 ∗
        (⌜ z = (-1)%Z ∧ r1 <= r2 ⌝ ∨
         ⌜ z = 1%Z ∧ r2 <= r1 ⌝) ⟩⟩⟩.
  Proof.
    iIntros (Φ) "(Hr1&Hr2) HΦ".
    wp_rec. wp_pures.
    iDestruct "Hr1" as (l1 α1 f1 -> ->) "Hr1".
    iDestruct "Hr2" as (l2 α2 f2 -> ->) "Hr2".
    wp_pures.
    iDestruct (chunk_and_tape_seq_ne with "Hr1 Hr2") as %?.
    rewrite bool_decide_eq_false_2; [|by intros [=]].
    wp_pures.
    wp_apply (wp_cmp_list with "[$Hr1 $Hr2]").
    iIntros (z)  "(Hcases&Hr1&Hr2)".
    iApply "HΦ".
    iSplitL "Hr1".
    { iExists _, _, _. iFrame. eauto. }
    iSplitL "Hr2".
    { iExists _, _, _. iFrame. eauto. }
    auto.
  Qed.

End lazy_real.
