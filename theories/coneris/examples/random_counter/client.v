From iris.algebra Require Import excl_auth cmra.
From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris par spawn.
From clutch.coneris.examples Require Import random_counter.random_counter.

Local Open Scope Z.

Set Default Proof Using "Type*".
Section lemmas.
  Context `{!inG Σ (excl_authR (option natO))}.

  (* Helpful lemmas *)
  Lemma ghost_var_alloc b :
    ⊢ |==> ∃ γ, own γ (●E b) ∗ own γ (◯E b).
  Proof.
    iMod (own_alloc (●E b ⋅ ◯E b)) as (γ) "[??]".
    - by apply excl_auth_valid.
    - by eauto with iFrame.
  Qed.

  Lemma ghost_var_agree γ b c :
    own γ (●E b) -∗ own γ (◯E c) -∗ ⌜ b = c ⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    by iCombine "Hγ● Hγ◯" gives %->%excl_auth_agree_L.
  Qed.

  Lemma ghost_var_update γ b' b c :
    own γ (●E b) -∗ own γ (◯E c) ==∗ own γ (●E b') ∗ own γ (◯E b').
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E b' ⋅ ◯E b') with "Hγ● Hγ◯") as "[$$]".
    { by apply excl_auth_update. }
    done.
  Qed.
End lemmas.

Section lemmas'.
  Context `{!inG Σ (excl_authR (boolO))}.

  (* Helpful lemmas *)
  Lemma ghost_var_alloc' b :
    ⊢ |==> ∃ γ, own γ (●E b) ∗ own γ (◯E b).
  Proof.
    iMod (own_alloc (●E b ⋅ ◯E b)) as (γ) "[??]".
    - by apply excl_auth_valid.
    - by eauto with iFrame.
  Qed.

  Lemma ghost_var_agree' γ b c :
    own γ (●E b) -∗ own γ (◯E c) -∗ ⌜ b = c ⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    by iCombine "Hγ● Hγ◯" gives %->%excl_auth_agree_L.
  Qed.

  Lemma ghost_var_update' γ b' b c :
    own γ (●E b) -∗ own γ (◯E c) ==∗ own γ (●E b') ∗ own γ (◯E b').
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E b' ⋅ ◯E b') with "Hγ● Hγ◯") as "[$$]".
    { by apply excl_auth_update. }
    done.
  Qed.
End lemmas'.

Section client.
  Context `{rc:random_counter} {L: counterG Σ}.
  Definition con_prog : expr :=
    let: "c" := new_counter #() in
    ((let: "lbl" := allocate_tape #() in
     incr_counter_tape "c" "lbl") |||
    let: "lbl" := allocate_tape #() in
    incr_counter_tape "c" "lbl"
    ) ;;
    read_counter "c"
  .

  Definition counter_nroot:=nroot.@"counter".

  Context `{!spawnG Σ, !inG Σ (excl_authR (option natO)), !inG Σ (excl_authR (boolO))}.
  Lemma con_prog_spec:
    {{{ ↯ (1/16) }}}
      con_prog
      {{{ (n:nat), RET #n; ⌜(0<n)%nat⌝ }}}.
  Proof.
    iIntros (Φ) "Hε HΦ".
    rewrite /con_prog.
    wp_apply (new_counter_spec _ counter_nroot with "[//]") as (c) "(%γ & #Hcounter & Hfrag)".
    replace (1)%Qp with (1/2+1/2)%Qp; last compute_done.
    replace 0%nat with (0+0)%nat by lia.
    rewrite -counter_content_frag_combine.
    iDestruct "Hfrag" as "[Hfrag1 Hfrag2]".
    wp_pures.
  Admitted.
  
End client.
