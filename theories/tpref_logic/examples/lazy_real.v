From Coq Require Import Reals Psatz.
From clutch.prob_lang Require Import lang notation metatheory.
From clutch.tpref_logic Require Import weakestpre spec primitive_laws proofmode adequacy spec.
From clutch.prob Require Import distribution markov.
From clutch.tpref_logic.examples Require Import flip.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Section lazy_real.
  (* Context (CHUNCK_SIZE : nat). *)

  #[global] Existing Instance finite_countable | 0.

  Definition mstep (bs : bool * bool) :=
    let '(b1, b2) := bs in
    if bool_decide (b1 ≠ b2) then dzero else dprod fair_coin fair_coin.

  Definition mto_final (bs : bool * bool) : option (bool * bool) :=
    let '(b1, b2) := bs in
    if bool_decide (b1 ≠ b2) then Some (b1, b2) else None.

  Definition two_coins_mixin : MarkovMixin mstep mto_final.
  Proof.
    constructor.
    move=> [? ?] =>/= [[[? ?] ?] [? ?]].
    case_bool_decide as Heq; simplify_eq=>//.
  Qed.

  Definition two_coins : markov := Markov _ _ two_coins_mixin.

  #[global] Program Instance two_coins_rsm :
    rsm (δ := two_coins) (λ '(b1, b2), if bool_decide (b1 ≠ b2) then 0 else 2) 1.
  Next Obligation. intro a; simpl; real_solver. Qed.
  Next Obligation. real_solver. Qed.
  Next Obligation.
    move=> /= [b1 b2] Hf. rewrite /= /mstep.
    case_bool_decide as Heq; simpl in *.
    - exfalso; apply Hf. apply to_final_Some.
      eexists. rewrite /= /mto_final /=.
      rewrite bool_decide_eq_true_2 //.
    - rewrite dprod_mass fair_coin_mass. lra.
  Qed.
  Next Obligation.
    move=> [b1 b2] /= H.
    apply to_final_Some.
    eexists. rewrite /= /mto_final /=.
    case_bool_decide; [done|]. lra.
  Qed.
  Next Obligation.
   move=> [b1 b2] H /=.
   eapply (ex_seriesC_le _ (λ a, mstep (b1, b2) a * 2)); [|by eapply ex_seriesC_scal_r].
   move=> [b1' b2'] /=. real_solver.
  Qed.
  Next Obligation.
    move=> [b1 b2] /= H.
    case_bool_decide as Heq.
    - exfalso. apply H. apply to_final_Some.
      eexists. rewrite /= /mto_final /=.
      rewrite /= bool_decide_eq_true_2 //.
    - subst. rewrite /Expval /mstep /=.
      trans (1 + 1); [|lra].
      apply Rplus_le_compat_r.
      rewrite fubini_pos_seriesC_prod_lr.
      + rewrite !SeriesC_bool !dprod_pmf !fair_coin_pmf. real_solver.
      + real_solver.
      + apply ex_seriesC_prod; eauto using ex_seriesC_finite.
        intros ??.
        pose proof (pmf_pos (dprod fair_coin fair_coin) (a, b)).
        case_match; lra.
  Qed.

  Lemma two_coins_terminates (bs : mstate two_coins)  :
    SeriesC (lim_exec bs) = 1.
  Proof. apply (rsm_term_limexec bs). Qed.

  Definition model := iter_markov two_coins (true, true).

  Lemma iter_two_coins_terminates n :
    SeriesC (lim_exec (δ := model) ((true, true), n)) = 1.
  Proof.
    apply: iter_markov_terminates.
    apply two_coins_terminates.
  Qed.

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

  Context `{tprG model Σ}.

  Lemma two_coins_final b1 b2 :
    is_final ((b1, b2) : mstate two_coins) ↔ b1 ≠ b2.
  Proof.
    split.
    - intros [? Hf] ->. simpl in *. by case_bool_decide.
    - intros ?. eexists. simpl. rewrite bool_decide_eq_true_2//.
  Qed.

  Lemma two_coins_not_final b1 b2 :
    ¬ is_final ((b1, b2) : mstate two_coins) ↔ b1 = b2.
  Proof.
    split.
    - intros ?%to_final_None_1.
      simpl in *. by case_bool_decide.
    - by intros -> ?%two_coins_final.
  Qed.

  Lemma spec_restart E b1 b2 N :
    b1 ≠ b2 →
    specF (b1, b2, S N) -∗ spec_update 1 E (specF (true, true, N)).
  Proof.
    iIntros (?) "Hspec". iIntros (s) "Hs".
    iDestruct (spec_auth_agree with "Hs Hspec") as %->.
    iExists (true, true, N).
    iMod (spec_auth_update with "Hs Hspec") as "[$ $]".
    iModIntro. iPureIntro.
    rewrite stepN_Sn /=.
    rewrite bool_decide_eq_true_2 //.
    rewrite dret_id_left /=.
    by apply dret_1.
  Qed.

  Lemma rwp_coupl_two_tapes ns1 ns2 α1 α2 N (e : expr) E (Φ : val → iProp Σ) b :
    TCEq (to_val e) None →
    α1 ↪ (1%nat; ns1) ∗
    α2 ↪ (1%nat; ns2) ∗
    specF (b, b, S N) ∗
    ▷ (∀ b1' b2', specF (b1', b2', S N) -∗
                α1 ↪ (1%nat; ns1 ++ [bool_to_fin b1']) -∗
                α2 ↪ (1%nat; ns2 ++ [bool_to_fin b2']) -∗
                WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hv) "(Hα1 & Hα2 & Hspec & Hcnt)".
    iApply (rwp_couple_two_tapes (δ := model) _ _
              (λ '(n1, n2) '(b1, b2, N'),
                N' = S N ∧ n1 = bool_to_fin b1 ∧ n2 = bool_to_fin b2)
               with "[$Hα1 $Hα2 $Hspec Hcnt]").
    { intros ???? => /=.
      rewrite bool_decide_eq_false_2; [|auto].
      rewrite -(dret_id_right (state_step _ _ ≫= _)).
      eapply Rcoupl_dbind; [|by apply state_steps_fair_coins_coupl].
      intros [] [b1' b2']  [= -> ->] =>/=.
      eapply Rcoupl_dret=>/=. eauto 6. }
    iIntros "!>" (?? [[b1' b2'] N'] (-> & -> & ->)) "Hf1 Hα1 Hα2".
    iApply ("Hcnt" with "Hf1 Hα1 Hα2").
  Qed.

  Definition comparison2z c : Z :=
    match c with
    | Eq => 0
    | Lt => -1
    | Gt => 1
    end.

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

  Definition chunk_and_tape_list α l zs : iProp Σ :=
    ∃ zs1 zs2, ⌜zs = zs1 ++ zs2⌝ ∗ chunk_list l zs1 ∗ α ↪ (1%nat; zs2).

  Definition lazy_no (zs : list _) (v : val) : iProp Σ :=
    ∃ (l : loc) (α : loc),
      ⌜v = (#lbl:α, #l)%V⌝ ∗
      chunk_and_tape_list α l zs.

  Lemma chunk_list_hd_acc l zs :
    chunk_list l zs -∗
    (∃ v, l ↦ v ∗ (l ↦ v -∗ chunk_list l zs)).
  Proof.
    destruct zs.
    - simpl. iIntros. iExists _. iFrame. eauto.
    - simpl. iIntros "(%&H1&H2)". iExists _. iFrame.
      iIntros "H". iExists _. iFrame.
  Qed.

  Lemma chunk_and_tape_list_ne (l1 l2 α1 α2 : loc) zs1 zs2 :
    chunk_and_tape_list α1 l1 zs1 -∗ chunk_and_tape_list α2 l2 zs2 -∗ ⌜l1 ≠ l2⌝.
  Proof.
    iIntros "(% & % & _ & Hl1 & _) (% & % & _ & Hl2 & _)".
    iDestruct (chunk_list_hd_acc with "Hl1") as (?) "[Hl1 _]".
    iDestruct (chunk_list_hd_acc with "Hl2") as (?) "[Hl2 _]".
    iApply (ghost_map_elem_ne with "Hl1 Hl2").
  Qed.

  Lemma chunk_and_tape_list_cons_chunk (l l' : loc) (z : fin _) zs α :
    l ↦ SOMEV (#z, #l') -∗
    chunk_and_tape_list α l' zs -∗
    chunk_and_tape_list α l (z :: zs).
  Proof.
    iIntros "Hl Htape". iDestruct "Htape" as (zs1 zs2 Heq) "(Hchunks&Hlist)".
    iExists (z :: zs1), zs2.
    iSplit.
    { rewrite Heq /=//. }
    iSplitL "Hl Hchunks".
    { rewrite /=. iExists l'. iFrame. }
    iFrame.
  Qed.

  Lemma rwp_get_chunk_nil α l E :
    ⟨⟨⟨ chunk_and_tape_list α l [] ⟩⟩⟩
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

  Lemma rwp_get_chunk_cons z zs α l E :
    ⟨⟨⟨ chunk_and_tape_list α l (z :: zs) ⟩⟩⟩
      get_chunk #lbl:α #l @ E
    ⟨⟨⟨ l', RET (#z, #l');
        chunk_and_tape_list α l' zs ∗
       (∀ zs, chunk_and_tape_list α l' zs -∗ chunk_and_tape_list α l (z :: zs)) ⟩⟩⟩.
  Proof.
    iIntros (Ψ) "(%zs1 & %zs2 & %Heq & Hl & Hα) HΨ".
    rewrite /get_chunk.
    wp_pures.
    destruct zs1 as [| z' zs1'].
    - wp_load. wp_pures.
      rewrite /= in Heq. rewrite -Heq.
      (* TODO: tactic *)
      wp_apply (rwp_rand_tape with "Hα").
      iIntros "Hα".
      wp_pures. wp_alloc l' as "Hl'". wp_pures. wp_store.
      iModIntro. iApply "HΨ". iSplitR "Hl".
      { iExists [], zs. iSplit; [done|]. iFrame. }
      { iIntros (?) "Htail". iApply (chunk_and_tape_list_cons_chunk with "[$] [$]"). }
    - rewrite /=. iDestruct "Hl" as "(%l' & Hl & Hl')".
      wp_load. wp_pures. inversion Heq; subst.
      iModIntro. iApply "HΨ".
      iSplitR "Hl".
      { iExists _, _. by iFrame. }
      { iIntros (?) "Htail". iApply (chunk_and_tape_list_cons_chunk with "[$] [$]"). }
  Qed.

  Lemma rwp_couple_chunk_and_tape_list α1 α2 l1 l2 zs1 zs2 N (e : expr) E (Φ : val → iProp Σ) b  :
    TCEq (to_val e) None →
    chunk_and_tape_list α1 l1 zs1 ∗
    chunk_and_tape_list α2 l2 zs2 ∗
    specF (b, b, S N) ∗
    ▷ (∀ b1' b2', specF (b1', b2', S N) -∗
                chunk_and_tape_list α1 l1 (zs1 ++ [bool_to_fin b1']) -∗
                chunk_and_tape_list α2 l2 (zs2 ++ [bool_to_fin b2']) -∗
                WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (?) "((% & % & % & Hl1 & Hα1) & (% & % & % & Hl2 & Hα2) & Hspec & Hcnt)".
    iApply rwp_coupl_two_tapes.
    iFrame "Hα1 Hα2 Hspec".
    iIntros "!>" (b1' b2') "Hspec Hα1 Hα2".
    iApply ("Hcnt" with "Hspec [Hl1 Hα1] [Hl2 Hα2]").
    { iExists _, _. iFrame. subst. rewrite app_assoc //. }
    { iExists _, _. iFrame. subst. rewrite app_assoc //. }
  Qed.

  Lemma rwp_cmp_list_nil_nil N α1 α2 l1 l2 E b :
    ⟨⟨⟨ specF (b, b, S N) ∗ chunk_and_tape_list α1 l1 [] ∗ chunk_and_tape_list α2 l2 [] ⟩⟩⟩
      cmp_list #lbl:α1 #l1 #lbl:α2 #l2 @ E
    ⟨⟨⟨ (z : Z) (b' : bool) (z1 z2 : fin _) (zs : list (fin _)), RET #z;
        specF (b', b', N) ∗
          ⌜z1 ≠ z2⌝ ∗
          chunk_and_tape_list α1 l1 (zs ++ [z1]) ∗
          chunk_and_tape_list α2 l2 (zs ++ [z2]) ⟩⟩⟩.
  Proof.
    iLöb as "IH" forall (l1 l2 b).
    iIntros (Ψ) "(Hspec & Hl1 & Hl2) HΨ".
    wp_rec. wp_pures.
    wp_apply (rwp_couple_chunk_and_tape_list α1).
    iFrame.
    iIntros "!>" (b1' b2') "Hspec Hl1 Hl2 /=".
    wp_apply (rwp_get_chunk_cons with "Hl1").
    iIntros (l1') "(Hl1' & Hl1)".
    wp_pures.
    wp_apply (rwp_get_chunk_cons with "Hl2").
    iIntros (l2') "(Hl2' & Hl2)".
    wp_pures.
    wp_apply wp_cmpZ; [done|]; iIntros "_".
    destruct (Z.compare_spec (bool_to_fin b1') (bool_to_fin b2'))
      as [? | Hlt%Z.lt_neq | Hgt%Z.lt_neq]; simplify_eq=>/=.
   - wp_pures.
     wp_apply ("IH" with "[$Hspec $Hl1' $Hl2']").
     iIntros (?????) "(?&?& Hl1' & Hl2')".
     iSpecialize ("Hl1" with "Hl1'").
     iSpecialize ("Hl2" with "Hl2'").
     rewrite 2!app_comm_cons. iApply ("HΨ" with "[$]").
   - wp_apply rwp_spec_steps'.
     assert (b1' ≠ b2') by (intros ->; eauto).
     iSplitR "Hspec"; [|by iApply (spec_restart with "Hspec")].
     iIntros "Hspec !>".
     wp_pures.
     iSpecialize ("Hl1" with "Hl1'").
     iSpecialize ("Hl2" with "Hl2'").
     iApply ("HΨ" $! _ _ _ _ []). iFrame.
     iModIntro. iPureIntro. by intros ?%(inj _).
   - wp_apply rwp_spec_steps'.
     assert (b1' ≠ b2') by (intros ->; eauto).
     iSplitR "Hspec"; [|by iApply (spec_restart with "Hspec")].
     iIntros "Hspec !>".
     wp_pures.
     iSpecialize ("Hl1" with "Hl1'").
     iSpecialize ("Hl2" with "Hl2'").
     iApply ("HΨ" $! _ _ _ _ []). iFrame.
     iModIntro. iPureIntro. by intros ?%(inj _).
  Qed.

  Lemma rwp_cmp_list N α1 α2 l1 l2 E zs1 zs2 b :
    (N > 0)%nat →
    ⟨⟨⟨ specF (b, b, N) ∗
        chunk_and_tape_list α1 l1 zs1 ∗
        chunk_and_tape_list α2 l2 zs2 ⟩⟩⟩
      cmp_list #lbl:α1 #l1 #lbl:α2 #l2 @ E
    ⟨⟨⟨ (z : Z) (M : nat) (b' : bool) (z1 z2 : fin _) (zs zs1' zs2' : list (fin _)), RET #z;
        chunk_and_tape_list α1 l1 (zs ++ [z1] ++ zs1') ∗
        chunk_and_tape_list α2 l2 (zs ++ [z2] ++ zs2') ∗
        ⌜z1 ≠ z2⌝ ∗
        specF (b', b', M) ∗
        ⌜(N - 1 ≤ M ≤ N)%nat⌝ ⟩⟩⟩.
  Proof.
    iIntros (?).
    iInduction zs1 as [|z1 zs1] "IH" forall (l1 l2 zs2 b).
    - iInduction zs2 as [|z2 zs2] "IH" forall (l1 l2 b).
      + iIntros (Ψ) "(Hspec & Hl1 & Hl2) HΨ".
        destruct N; [lia|].
        wp_apply (rwp_cmp_list_nil_nil with "[$Hspec $Hl1 $Hl2]").
        iIntros (z b' z1 z2 zs) "(Hspec & % & Hl1 & Hl2)".
        iApply ("HΨ").
        iFrame. iSplit; [done|].
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
          as [? | Hlt%Z.lt_neq | Hgt%Z.lt_neq]; simplify_eq=>/=.
        * do 3 wp_pure _.
          wp_apply ("IH" with "[$Hspec $Hl1' $Hl2']").
          iIntros (????????)  "(Hl1' & Hl2' & % & Hspec)".
          iSpecialize ("Hl1" with "Hl1'").
          iSpecialize ("Hl2" with "Hl2'").
          rewrite 2!app_comm_cons.
          iApply "HΨ". by iFrame.
        * wp_pures.
          iSpecialize ("Hl1" with "Hl1'").
          iSpecialize ("Hl2" with "Hl2'").
          iModIntro.
          iApply ("HΨ" $! _ _ _ z1 z2 [] [] zs2).
          iFrame. iSplit; [|iPureIntro; lia].
          iPureIntro. by intros ->.
        * wp_pures.
          iSpecialize ("Hl1" with "Hl1'").
          iSpecialize ("Hl2" with "Hl2'").
          iModIntro.
          iApply ("HΨ" $! _ _ _ z1 z2 [] [] zs2).
          iFrame. iPureIntro. split; [|lia]. by intros ->.
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
          as [? | Hlt%Z.lt_neq | Hgt%Z.lt_neq]; simplify_eq=>/=.
        * do 3 wp_pure _.
          wp_apply ("IH" with "[$Hspec $Hl1' $Hl2']").
          iIntros (????????)  "(Hl1' & Hl2' & % & Hspec)".
          iSpecialize ("Hl1" with "Hl1'").
          iSpecialize ("Hl2" with "Hl2'").
          rewrite 2!app_comm_cons.
          iApply "HΨ". by iFrame.
        * wp_pures.
          iSpecialize ("Hl1" with "Hl1'").
          iSpecialize ("Hl2" with "Hl2'").
          iModIntro.
          iApply ("HΨ" $! _ _ _ z1 z2 [] zs1 []).
          iFrame. iPureIntro. split; [|lia]. by intros ->.
        * wp_pures.
          iSpecialize ("Hl1" with "Hl1'").
          iSpecialize ("Hl2" with "Hl2'").
          iModIntro.
          iApply ("HΨ" $! _ _ _ z1 z2 [] zs1 []).
          iFrame. iPureIntro. split; [|lia]. by intros ->.
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
          as [? | Hlt%Z.lt_neq | Hgt%Z.lt_neq]; simplify_eq=>/=.
        * do 3 wp_pure _.
          wp_apply ("IH" with "[$Hspec $Hl1' $Hl2']").
          iIntros (????????)  "(Hl1' & Hl2' & % & Hspec)".
          iSpecialize ("Hl1" with "Hl1'").
          iSpecialize ("Hl2" with "Hl2'").
          rewrite 2!app_comm_cons.
          iApply "HΨ". by iFrame.
        * wp_pures.
          iSpecialize ("Hl1" with "Hl1'").
          iSpecialize ("Hl2" with "Hl2'").
          iModIntro.
          iApply ("HΨ" $! _ _ _ z1 z2 [] zs1 zs2).
          iFrame. iPureIntro. split; [|lia]. by intros ->.
        * wp_pures.
          iSpecialize ("Hl1" with "Hl1'").
          iSpecialize ("Hl2" with "Hl2'").
          iModIntro.
          iApply ("HΨ" $! _ _ _ z1 z2 [] zs1 zs2).
          iFrame. iPureIntro. split; [|lia]. by intros ->.
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
        lazy_no zs1' v1 ∗ lazy_no zs2' v2 ∗ cmps (N - 1) ⟩⟩⟩.
  Proof.
    iIntros (? Ψ) "((%l1 & %α1 & -> & Hl1) & (%l2 & %α2 & -> & Hl2) & (% & % & Hcmps & %)) HΨ".
    wp_rec. wp_pures.
    iDestruct (chunk_and_tape_list_ne with "Hl1 Hl2") as %?.
    rewrite bool_decide_eq_false_2; [|by intros [=]].
    wp_pures.
    destruct M; [lia|].
    wp_apply (rwp_cmp_list with "[$Hcmps $Hl1 $Hl2]"); [lia|].
    iIntros (????????) "(Hl1 & Hl2 & % & Hs & %)".
    iApply "HΨ".
    iSplitL "Hl1".
    { iExists _, _. by iFrame. }
    iSplitL "Hl2".
    { iExists _, _. by iFrame. }
    iFrame. iExists _, _. eauto with lia.
  Qed.

End lazy_real.

Definition cmp_three_numbers : expr :=
  let: "r1" := init #() in
  let: "r2" := init #() in
  let: "r3" := init #() in
  cmp "r1" "r2";;
  cmp "r2" "r3";;
  #().

Section client.
  Context `{!tprG model Σ}.

  Lemma rwp_cmp_three_numbers :
    ⟨⟨⟨ cmps 2 ⟩⟩⟩
      cmp_three_numbers
    ⟨⟨⟨ RET #(); True ⟩⟩⟩.
  Proof.
    iIntros (Ψ) "Hcmps HΨ".
    rewrite /cmp_three_numbers.
    wp_apply rwp_init; [done|].
    iIntros (r1) "Hr1"; wp_pures.
    wp_apply rwp_init; [done|].
    iIntros (r2) "Hr2"; wp_pures.
    wp_apply rwp_init; [done|].
    iIntros (r3) "Hr3"; wp_pures.
    wp_apply (rwp_cmp with "[$Hr1 $Hr2 $Hcmps]"); [lia|].
    iIntros (c1 ? ?) "(Hr1 & Hr2 & Hcmps)"; wp_pures.
    wp_apply (rwp_cmp with "[$Hr2 $Hr3 $Hcmps]"); [lia|].
    iIntros (c2 ? ?) "(Hr2 & Hr3 & Hcmps)"; wp_pures.
    iModIntro.
    by iApply "HΨ".
  Qed.

End client.

Notation σ₀ := {| heap := ∅; tapes := ∅ |}.
Notation almost_surely_terminates ρ := (SeriesC (lim_exec ρ) = 1%R).

Theorem lazy_real_terminates :
  almost_surely_terminates (cmp_three_numbers, σ₀).
Proof.
  eapply Rle_antisym; [done|].
  transitivity (SeriesC (lim_exec ((true, true, 2%nat) : mstate model))).
  { by rewrite iter_two_coins_terminates. }
  eapply (wp_refRcoupl_mass (δ := model) (tprΣ model)).
  iIntros (?) "Ha".
  wp_apply (rwp_cmp_three_numbers with "[Ha]"); [|done].
  iExists _, _. eauto with lia.
Qed.
