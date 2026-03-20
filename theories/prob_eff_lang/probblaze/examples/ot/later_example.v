From clutch.prob_eff_lang.probblaze Require Export notation.
From iris.proofmode Require Import base proofmode classes.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra 
  class_instances definition sem_types.

Section proof.
  Context `{!probblazeRGS Σ}.
  Context {op : label}.

  Program Definition X : iThy Σ := (λ e1 e2, λne Q,
                                      ⌜ e1 = do: op #()%V ⌝%E ∗
                                      ⌜ e2 = do: op #()%V ⌝%E ∗
                                      ▷ Q #()%V #()%V)%I.
  Next Obligation. solve_proper. Qed.
  Definition L := [([op],[op], X)].
  
  Lemma later_example e1 e2 :
    BREL e1 ≤ e2 <| L |> {{ (λ v1 v2, True) }} -∗
    BREL e1 ≤ handle: e2 with effect op "x", "k" as multi => "k" (do: op #()%V) | return "y" => "y" end <| L |> {{ (λ v1 v2, True) }}.
  Proof.
    iIntros "H".
    assert (L = L ++ to_iThyIfMono OS []) as -> by done.
    iApply (brel_exhaustion' OS _ _ [] [_] with "H"); [set_solver|done|].
    iSplit.
    - iIntros (v1 v2) "H". by brel_pures_r.
    - iIntros (???????) "(-> & -> & HQ) Hkont".
      brel_pures_r; [apply neutral_ectx; set_solver|].
      iApply (brel_introduction' with "[HQ Hkont]"); [apply list_elem_of_here|].
      iExists _,_,_,[AppRCtx _],(λ s1 s2, ∃ v1 v2, ⌜ s1 = Val v1 ⌝ ∗ ⌜ s2 = Val v2 ⌝ ∗ Q v1 v2 ∗ ∀ s1' s2' : expr, Q s1' s2' -∗ brel ⊤ (fill k1' s1') (fill k2' s2') [([op], [op], X)] (λ _ _ : val, True))%I.
      repeat (iSplit; [done|]).
      iSplit; [iPureIntro;apply AppRCtx_NeutralEctx;apply NeutralEctx_nil|].
      iSplit.
      { repeat (iSplit; [done|]). iModIntro. by iFrame. }
      iIntros (??) "!# (%&%&->&->&HQ&Hkont)".
      brel_pures_r. by iApply "Hkont".
  Qed. 

  Program Definition Y : iThy Σ := (λ e1 e2, λne Q,
                                      ⌜ e1 = do: op #()%V ⌝%E ∗
                                      ⌜ e2 = do: op #()%V ⌝%E ∗
                                      Q #()%V #()%V)%I.
  Next Obligation. solve_proper. Qed.
  Definition M := [([op],[op], Y)].

  Lemma later_example_introduction' e1 e2 :
    BREL e1 ≤ e2 <| M |> {{ (λ v1 v2, True) }} -∗
    BREL e1 ≤ handle: e2 with effect op "x", "k" as multi => "k" (do: op #()%V) | return "y" => "y" end <| M |> {{ (λ v1 v2, True) }}.
  Proof.
    iIntros "H".
    assert (M = M ++ to_iThyIfMono OS []) as -> by done.
    iApply (brel_exhaustion' OS _ _ [] [_] with "H"); [set_solver|done|].
    iSplit.
    - iIntros (v1 v2) "H". by brel_pures_r.
    - iIntros (???????) "(-> & -> & HQ) Hkont".
      brel_pures_r; [apply neutral_ectx; set_solver|].
      iApply (brel_introduction' with "[HQ Hkont]"); [apply list_elem_of_here|].
      iExists _,_,_,[AppRCtx _],(λ s1 s2, ∃ v1 v2, ⌜ s1 = Val v1 ⌝ ∗ ⌜ s2 = Val v2 ⌝ ∗ Q v1 v2 ∗ ▷ ∀ s1' s2' : expr, Q s1' s2' -∗ brel ⊤ (fill k1' s1') (fill k2' s2') [([op], [op], Y)] (λ _ _ : val, True))%I.
      repeat (iSplit; [done|]).
      iSplit; [iPureIntro;apply AppRCtx_NeutralEctx;apply NeutralEctx_nil|].
      iSplit.
      { repeat (iSplit; [done|]). by iFrame. }
      iIntros (??) "!# (%&%&->&->&HQ&Hkont)".
      brel_pures_r.
  Admitted. 

End proof.
