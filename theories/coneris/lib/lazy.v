(** * Library for lazy sampling *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import
  coq_tactics ltac_tactics sel_patterns environments reduction proofmode.
From coneris.coneris Require Import coneris lib.conversion par spawn lib.flip.

Set Default Proof Using "Type*".

Section defs.


  Context `{!conerisGS Σ}.

  (** A lazy rand *)
  Definition new_lazyrand : expr :=
    λ: "N",
      (ref NONEV, "N").

  Definition read_lazyrand : expr :=
    λ: "c",
      let, ("r", "N") := "c" in
      match: !"r" with
      | NONE => let: "n" := rand "N" in
               "r" <- SOME "n" ;;
               "n"
      | SOME "n" => "n"
      end.

  Definition is_lazyrand (v : val) (N : nat) (n : option nat) : iProp Σ :=
    ∃ (l : loc), ⌜ v = (#l, #N)%V ⌝ ∗
                         ( match n with
                           | None => l ↦ NONEV
                           | Some m => l ↦ SOMEV #m
                           end ).

  Lemma new_lazyrand_spec (N : nat) :
    {{{ True }}} new_lazyrand #N {{{ v, RET v; is_lazyrand v N None }}}.
  Proof.
    iIntros (Φ) "? HΦ".
    rewrite /new_lazyrand.
    wp_pures.
    wp_alloc l as "Hl".
    wp_pures.
    iModIntro.
    iApply "HΦ".
    rewrite /is_lazyrand.
    iExists l.
    iFrame.
    iPureIntro.
    done.
  Qed.


  Lemma read_lazyrand_old_spec (v : val) (N m : nat) :
    {{{ is_lazyrand v N (Some m) }}} read_lazyrand v {{{ n, RET n; ⌜ n = #m ⌝ ∗ is_lazyrand v N (Some m) }}}.
  Proof.
    rewrite /read_lazyrand /is_lazyrand.
    iIntros (Φ) "Hv HΦ".
    iDestruct "Hv" as (l) "[-> Hl]".
    wp_pures.
    wp_load.
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame.
    done.
  Qed.


  Lemma read_lazyrand_fresh_spec (v : val) (N : nat) (ε : nonnegreal) (F : fin (S N) -> nonnegreal) :
    SeriesC (λ n : fin (S N), (1 / S N * F n)%R) = ε ->
    {{{ is_lazyrand v N (None) ∗ ↯ ε }}}
      read_lazyrand v
    {{{ (n : fin (S N)), RET #n; ∃ m : nat , ⌜ fin_to_nat n = m ⌝ ∗ is_lazyrand v N (Some m) ∗ ↯ (F n) }}}.
  Proof.
    rewrite /read_lazyrand /is_lazyrand.
    iIntros (Hf Φ) "(Hv & Herr) HΦ".
    iDestruct "Hv" as (l) "[-> Hl]".
    wp_pures.
    wp_load.
    wp_pures.
    wp_apply (wp_couple_rand_adv_comp1 N _ _ ε F with "Herr"); [naive_solver|auto|].
    iIntros (n) "Herr".
    wp_pures.
    wp_store.
    iModIntro.
    iApply "HΦ".
    iExists (fin_to_nat n).
    iFrame.
    done.
  Qed.

End defs.


Section applications.


  Context `{!conerisGS Σ, !spawnG Σ}.

  Definition foo : expr :=
    let: "r" := ref #0 in
    ( let: "x" := new_lazyrand #1 in
      let: "y" := !"r" in
      if: (read_lazyrand "x" ≠ "y") then  #() else #() #() )
      |||
      ( "r" <- #1).


  Definition foo_inv (l:loc) : iProp Σ :=
    l ↦ #0 ∨ l ↦ #1.

  Lemma foo_spec :
    {{{ ↯ (1/2) }}}
      foo
      {{{ v, RET v; True }}}.
  Proof.
    rewrite /foo.
    iIntros (Φ) "Herr HΦ".
    wp_alloc r as "Hr".
    do 2 wp_pures.
    iMod (inv_alloc nroot _ (foo_inv r) with "[Hr]") as "#I".
    { iModIntro. by iLeft. }
    rewrite -/new_lazyrand.
    wp_apply (wp_par (λ _, ⊤) (λ _, ⊤) with "[Herr][]").
    - wp_apply (new_lazyrand_spec 1); auto.
      iIntros (v) "Hv".
      wp_pures.
      wp_bind (Load _).
      iInv "I" as "[Hr0 | Hr1]" "Hclose".
      + wp_load.
        iMod ("Hclose" with "[Hr0]") as "_"; first by iLeft.
        iModIntro.
        do 2 wp_pure.
        rewrite -/read_lazyrand.
        wp_bind (read_lazyrand _).
        wp_apply (read_lazyrand_fresh_spec v 1 nnreal_half
                                           (λ x, if fin_to_nat x =? 0%nat then nnreal_one else nnreal_zero)
                   with "[Herr Hv]"); [|iFrame|].
        { rewrite SeriesC_finite_foldr/=.
          lra.
        }
        iIntros (n).
        repeat (inv_fin n; try intros n); last first.
        * iIntros. by wp_pures.
        * iIntros "(%&<-&?&?)".
          simpl. by iDestruct (ec_contradict with "[$]") as "[]".
      + wp_load.
        iMod ("Hclose" with "[Hr1]") as "_"; first by iRight.
        iModIntro.
        do 2 wp_pure.
        rewrite -/read_lazyrand.
        wp_bind (read_lazyrand _).
        wp_apply (read_lazyrand_fresh_spec v 1 nnreal_half
                                           (λ x, if fin_to_nat x =? 1%nat then nnreal_one else nnreal_zero)
                   with "[Herr Hv]"); [|iFrame|].
        { rewrite SeriesC_finite_foldr/=.
          lra.
        }
        iIntros (n).
        repeat (inv_fin n; try intros n); last first.
        * iIntros "(%&<-&?&?)".
          simpl. by iDestruct (ec_contradict with "[$]") as "[]".
        * iIntros. by wp_pures.
    - iInv "I" as "[Hr | Hr]" "Hclose".
      + wp_store.
        iMod ("Hclose" with "[Hr]") as "_"; first by iRight.
        done.
      + wp_store.
        iMod ("Hclose" with "[Hr]") as "_"; first by iRight.
        done.
    - iIntros (??) "? !>".
      by iApply "HΦ".
  Qed.


End applications.

