From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real indicators real_decr_trial.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Section pmf.

   Definition BNEHalf_μ (b : bool) : R :=
     match b with
     | true => exp (-1/2)%R
     | false => 1 - exp (-1/2)%R
     end.

End pmf.

Section credits.
  Import Hierarchy.

End credits.


Section program.
  Context `{!erisGS Σ}.

  (* A lazy real is less than or equal to one half, ie. the first bit is zero. *)
  Definition LeHalf : val :=
    λ: "x",
      let: "c1n" := get_chunk (Fst "x") (Snd "x") in
      let: "res" := cmpZ (Fst "c1n") #1 in
      (* First bit is 0: res is -1, number is at most 1/2, return #true
         First bit is 1: res is 0, number is at least 1/2, return #false *)
      "res" = #0.

  Definition LeHalf_spec (r : R) : bool := bool_decide (Rle r (0.5)%R).

  Theorem wp_LeHalf E v r :
    lazy_real v r -∗ WP LeHalf v @ E {{ vb, ⌜vb = #(LeHalf_spec r) ⌝ ∗ lazy_real v r }}.
  Proof.
    iIntros "Hr".
    iDestruct "Hr" as (l α f -> ->) "Hr".
    iDestruct "Hr" as (zs f') "(%Hf & Hc & Hα)".
    rewrite /LeHalf /get_chunk; wp_pures.
    destruct zs as [|z zs].
    { rewrite /chunk_list//=.
      wp_apply (wp_load with "Hc").
      iIntros "Hc".
      wp_pures.
      wp_apply (wp_rand_infinite_tape with "Hα").
      iIntros "Hα".
      wp_pures.
      wp_apply (wp_alloc with "[//]").
      iIntros (ℓ) "Hℓ".
      wp_pures.
      wp_apply (wp_store with "[Hc]"); first iFrame.
      iIntros "Hc'".
      wp_pures.
      wp_apply (wp_cmpZ with "[//]").
      iIntros "_".
      wp_pures.
      iModIntro.
      iSplit.
      { iPureIntro; simpl; f_equal.
        rewrite Hf /append_bin_seq /LeHalf_spec //=.
        replace (λ n : nat, f' n) with f' by done.
        (* The terms seq_bin_to_R_leading0 seq_bin_to_R_leading1 should do the trick, but there is
           dependent types trouble in destructing f' 0 *)
        admit.
      }
      iExists l, α, f.
      iSplitR; first done.
      iSplitR; first done.
      iExists [f' 0%nat], (λ n : nat, f' (S n)).
      iFrame.
      iPureIntro.
      rewrite Hf /append_bin_seq//=.
      apply functional_extensionality; by intros [|].
    }
    { rewrite /chunk_list.
      iDestruct "Hc" as (l') "(Hc & Hlist)".
      wp_apply (wp_load with "Hc").
      iIntros "Hc".
      wp_pures.
      wp_apply (wp_cmpZ with "[//]").
      iIntros "_".
      wp_pures.
      iModIntro.
      iSplit.
      { iPureIntro; simpl; f_equal.
        (* Similar to above. *)
        admit. }
      { iExists l, α, f.
        iSplitR; first done.
        iSplitR; first done.
        unfold chunk_and_tape_seq.
        iExists (z::zs), f'.
        iFrame.
        done.
    }
  Admitted.





End program.
