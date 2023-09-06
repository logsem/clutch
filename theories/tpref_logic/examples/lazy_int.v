From Coq Require Import Reals Psatz.
From clutch.prob_lang Require Import lang notation metatheory.
From clutch.tpref_logic Require Import weakestpre spec primitive_laws proofmode.
From clutch.prob Require Import distribution markov.
From clutch.tpref_logic.examples Require Import flip.
#[local] Open Scope R.

Section lazy_int.
  (* Context (CHUNCK_SIZE : nat). *)

  Definition mstep (bs : bool * bool) : distr (bool * bool) :=
    let '(b1, b2) := bs in
    if bool_decide (b1 ≠ b2) then
      dzero
    else
      dprod fair_coin fair_coin.

  Definition mto_final (bs : bool * bool) : option (bool * bool) :=
    let '(b1, b2) := bs in
    if bool_decide (b1 ≠ b2) then Some (b1, b2) else None.

  Definition random_walks_mixin : MarkovMixin mstep mto_final.
  Proof.
    constructor.
    move=> [? ?]=>/= [[[? ?] ?] [? ?]].
    case_bool_decide; simplify_eq=>//.
  Qed.

  Canonical Structure random_walks : markov := Markov _ _ random_walks_mixin.

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

  Definition sample_lazy_no : val :=
    λ: <>,
      let: "hd" := ref NONEV in
      let: "α" := alloc #1 in
      ("α", "hd").

  Definition cmp_lazy_no : val :=
    λ: "lz1" "lz2",
      (* We short-circuit if the two locations are physically equal to avoid forcing sampling *)
      if: Snd "lz1" = Snd "lz2" then
        #0
      else
        cmp_list (Fst "lz1") (Snd "lz1") (Fst "lz2") (Snd "lz2").


  Context `{tprG random_walks Σ}.

  (* TODO: why is this neccesary?!?! *)
  Definition foo : specG _ _ := (@tprG_specG _ _ _).
  Existing Instance foo.
  
  Lemma rwp_coupl_two_tapes ns1 ns2 α1 α2 (e : expr) E (Φ : val → iProp Σ) (b : bool) :
    TCEq (to_val e) None →
    α1 ↪ (1%nat; ns1) ∗
    α2 ↪ (1%nat; ns2) ∗
    specF (b, b) ∗
    ▷ (∀ b1 b2, specF (b1, b2) -∗
                α1 ↪ (1%nat; ns1 ++ [bool_to_fin b1]) -∗
                α2 ↪ (1%nat; ns2 ++ [bool_to_fin b2]) -∗
                WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hv) "(Hα1 & Hα2 & Hspec & Hcnt)".
    iApply (rwp_couple_two_tapes (δ := random_walks) _ _
              (λ '(n1, n2) '(b1, b2), n1 = bool_to_fin b1 ∧ n2 = bool_to_fin b2)
             with "[$Hα1 $Hα2 $Hspec Hcnt]").
    { rewrite Hv //. }
    { intros ???? => /=.
      rewrite bool_decide_eq_false_2; auto.
      eapply Rcoupl_mono; [by apply state_steps_fair_coins_coupl|].
      intros [] [b1 b2] [= -> ->] =>/=. eauto. }
    iIntros "!>" (?? [b1 b2] [-> ->]) "Hf1 Hα1 Hα2".
    iApply ("Hcnt" with "Hf1 Hα1 Hα2").
  Qed.

  Definition comparison2z c : Z :=
    match c with
    | Eq => 0
    | Lt => -1
    | Gt => 1
    end.

  Lemma wp_cmp_Z (z1 z2 : Z) E :
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
  
  Lemma rwp_get_chunk_cons z zs α l E :
    ⟨⟨⟨ chunk_and_tape_list α l (z :: zs) ⟩⟩⟩
      get_chunk #lbl:α #l @ E
    ⟨⟨⟨ l', RET (#z, #l');
        chunk_and_tape_list α l' zs ∗
       (chunk_and_tape_list α l' zs -∗ chunk_and_tape_list α l (z :: zs)) ⟩⟩⟩.
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
      { iIntros "Htail". iApply (chunk_and_tape_list_cons_chunk with "[$] [$]"). }
    - rewrite /=. iDestruct "Hl" as "(%l' & Hl & Hl')".
      wp_load. wp_pures. inversion Heq; subst.
      iModIntro. iApply "HΨ".
      iSplitR "Hl".
      { iExists _, _. by iFrame. }
      { iIntros "Htail". iApply (chunk_and_tape_list_cons_chunk with "[$] [$]"). }
  Qed.

  Lemma rwp_couple_chunk_and_tape_list α1 α2 l1 l2 zs1 zs2 (e : expr) E (Φ : val → iProp Σ) b :
    TCEq (to_val e) None →
    chunk_and_tape_list α1 l1 zs1 ∗
    chunk_and_tape_list α2 l2 zs2 ∗
    specF (b, b) ∗
    ▷ (∀ b1 b2, specF (b1, b2) -∗
                chunk_and_tape_list α1 l1 (zs1 ++ [bool_to_fin b1]) -∗                                  
                chunk_and_tape_list α2 l2 (zs2 ++ [bool_to_fin b2]) -∗                                  
                WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (?) "((% & % & % & Hl1 & Hα1) & (% & % & % & Hl2 & Hα2) & Hspec & Hcnt)".
    iApply rwp_coupl_two_tapes.
    iFrame "Hα1 Hα2 Hspec". 
    iIntros "!>" (b1 b2) "Hspec Hα1 Hα2".
    iApply ("Hcnt" with "Hspec [Hl1 Hα1] [Hl2 Hα2]").
    { iExists _, _. iFrame. subst. rewrite app_assoc //. }
    { iExists _, _. iFrame. subst. rewrite app_assoc //. }    
  Qed.
  
  Lemma rwp_cmp_list α1 α2 l1 l2 E b :
    ⟨⟨⟨ specF (b, b) ∗ chunk_and_tape_list α1 l1 [] ∗ chunk_and_tape_list α2 l2 [] ⟩⟩⟩
      cmp_list #lbl:α1 #l1 #lbl:α2 #l2 @ E
    ⟨⟨⟨ (z : Z) (b1 b2 : bool), RET #z;
        specF (b1, b2) ∗ ⌜b1 ≠ b2⌝
        (* ⌜ z = comparison2z (digit_list_cmp zs1 zs2) ⌝ ∗ *)
        (* chunk_and_tape_list α1 l1 zs1 ∗ chunk_and_tape_list α2 l2 zs2 *) ⟩⟩⟩.
  Proof.
    iLöb as "IH" forall (b l1 l2).    
    iIntros (Ψ) "(Hspec & Hl1 & Hl2) HΨ".
    wp_rec. wp_pures. 
    iApply (rwp_couple_chunk_and_tape_list α1).
    iFrame.
    iIntros "!>" (b1 b2) "Hspec Hl1 Hl2".
    rewrite /=.
    wp_apply (rwp_get_chunk_cons with "Hl1").
    iIntros (l1') "(Hl1' & Hl1)".
    wp_pures.
    wp_apply (rwp_get_chunk_cons with "Hl2").
    iIntros (l2') "(Hl2' & Hl2)".
    wp_pures.
    wp_apply wp_cmp_Z; [done|]; iIntros "_".
    destruct (Z.compare_spec (bool_to_fin b1) (bool_to_fin b2))
      as [? | Hlt%Z.lt_neq | Hgt%Z.lt_neq] => /=; simplify_eq.
   - wp_pures. by iApply ("IH" with "[$Hspec $Hl1' $Hl2']"). 
   - wp_pures. iApply "HΨ". iFrame. iModIntro. iPureIntro. by intros ->.       
   - wp_pures. iApply "HΨ". iFrame. iModIntro. iPureIntro. by intros ->.
  Qed. 
                          
End lazy_int.
