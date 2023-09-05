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
    λ: "chnk",
      match: !"chnk" with
      | NONE =>
          let: "b" := rand #1 in
          let: "next"  := ref NONEV in
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
    rec: "cmp_list" "cl1" "cl2" :=
      let: "c1n" := get_chunk "cl1" in
      let: "c2n" := get_chunk "cl2" in
      let: "res" := cmpZ (Fst "c1n") (Fst "c2n") in
      if: "res" = #0 then
        "cmp_list" (Snd "c1n") (Snd "c2n")
      else
        "res".

  Definition sample_lazy_no : val :=
    λ: <>,
      let: "hd" := ref NONEV in
      "hd".

  Definition cmp_lazy_no : val :=
    λ: "lz1" "lz2",
      (* We short-circuit if the two locations are physically equal to avoid forcing sampling *)
      if: "lz1" = "lz2" then
        #0
      else
        cmp_list "lz1" "lz2".


  Context `{tprG random_walks Σ}.

  (* TODO: why is this neccesary?!?! *)
  Definition foo : specG _ _ := (@tprG_specG _ _ _).
  Existing Instance foo.

  Lemma rwp_coupl_two_tapes ns1 ns2 α1 α2 (e : expr) E (Φ : val → iProp Σ) (b : bool) :
    to_val e = None →
    α1 ↪ (1%nat; ns1) ∗
    α2 ↪ (1%nat; ns2) ∗
    specF (b, b) ∗
    ▷ (∀ b1 b2, specF (b1, b2) -∗
                α1 ↪ (1%nat; ns1 ++ [bool_to_fin b1]) -∗
                α2 ↪ (1%nat; ns2 ++ [bool_to_fin b2]) -∗
                WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (?) "(Hα1 & Hα2 & Hspec & Hcnt)".
    iApply (rwp_couple_two_tapes (δ := random_walks) _ _
              (λ '(n1, n2) '(b1, b2), n1 = bool_to_fin b1 ∧ n2 = bool_to_fin b2)
             with "[$Hα1 $Hα2 $Hspec Hcnt]"); [done| |].
    { intros ???? => /=.
      rewrite bool_decide_eq_false_2; auto.
      eapply Rcoupl_mono; [by apply state_steps_fair_coins_coupl|].
      intros [] [b1 b2] [= -> ->] =>/=. eauto. }
    iIntros "!>" (?? [b1 b2] [-> ->]) "Hf1 Hα1 Hα2".
    iApply ("Hcnt" with "Hf1 Hα1 Hα2").
  Qed.

  Fixpoint chunk_list (l : loc) (zs : list Z) : iProp Σ :=
    match zs with
    | [] => l ↦ NONEV
    | z :: zs =>
        ∃ l' : loc, l ↦ SOMEV (#z, #l') ∗ chunk_list l' zs
  end.

  Definition lazy_no (v : val) : iProp Σ :=
    ∃ (l : loc) (zs : list Z), ⌜v = #l⌝ ∧ chunk_list l zs .

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

End lazy_int.
