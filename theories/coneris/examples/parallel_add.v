From iris.algebra Require Import excl_auth.
From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris par spawn lib.flip.

Local Open Scope Z.

Set Default Proof Using "Type*".

Section lemmas.
  Context `{!inG Σ (excl_authR boolO)}.

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
    by iCombine "Hγ● Hγ◯" gives %<-%excl_auth_agree_L.
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

Section simple_parallel_add.
Definition simple_parallel_add : expr :=
  let: "r" := ref #0 in
  ( if: #0 < rand #2 then FAA "r" #1 else #())
  |||
  (if: #0 < rand #2 then FAA "r" #1 else #())
  ;;
  !"r".

(* Simple spec, where the error is directly distributed *)
Context `{!conerisGS Σ, !spawnG Σ, !inG Σ (excl_authR boolO)}.

Definition simple_parallel_add_inv (l:loc) (γ1 γ2 : gname) : iProp Σ :=
  ∃ (b1 b2 : bool) (z : Z),
      own γ1 (●E b1) ∗ own γ2 (●E b2) ∗ l ↦ #z ∗
      ⌜(z = bool_to_Z b1 + bool_to_Z b2)%Z⌝.


Lemma simple_parallel_add_spec:
  {{{ ↯ (2/3) }}}
    simple_parallel_add
    {{{ (z:Z), RET #z; ⌜(z=2)⌝ }}}.
Proof.
  iIntros (Φ) "Herr HΦ".
  rewrite /simple_parallel_add.
  wp_alloc l as "Hl".
  wp_pures.
  iMod (ghost_var_alloc false) as (γ1) "[Hγ1● Hγ1◯]".
  iMod (ghost_var_alloc false) as (γ2) "[Hγ2● Hγ2◯]".
  iMod (inv_alloc nroot _ (simple_parallel_add_inv l γ1 γ2) with "[Hl Hγ1● Hγ2●]") as "#I".
  { iModIntro. iExists _, _, _. iFrame. iPureIntro. simpl. lia. }
  replace (2/3)%R with (/3 + /3)%R by lra.
  iDestruct (ec_split with "[$]") as "[Herr1 Herr2]"; [lra|lra|].
  wp_apply (wp_par (λ _, own γ1 (◯E true))%I (λ _, own γ2 (◯E true))%I
             with "[Herr1 Hγ1◯][Herr2 Hγ2◯]").
  { wp_apply (wp_rand_err_nat _ _ 0%nat).
    replace (INR (Z.to_nat 2) + 1)%R with 3%R; [iFrame|simpl; lra].
    iIntros (??).
    wp_pures.
    rewrite bool_decide_eq_true_2; last lia.
    wp_pures.
    iInv "I" as (???) ">(Hγ1● & Hγ2● & Hl & %)" "Hclose".
    iDestruct (ghost_var_agree with "[$Hγ1●][$]") as "->".
    wp_faa.
    iMod (ghost_var_update _ true with "[$Hγ1●][$]") as "[Hγ1● Hγ1◯]".
    iMod ("Hclose" with "[Hγ1● Hγ2● Hl]"); last done.
    iModIntro. iExists _, _, _. iFrame.
    iPureIntro. simpl in *. lia.
  }
  { wp_apply (wp_rand_err_nat _ _ 0%nat).
    replace (INR (Z.to_nat 2) + 1)%R with 3%R; [iFrame|simpl; lra].
    iIntros (??).
    wp_pures.
    rewrite bool_decide_eq_true_2; last lia.
    wp_pures.
    iInv "I" as (???) ">(Hγ1● & Hγ2● & Hl & %)" "Hclose".
    iDestruct (ghost_var_agree with "[$Hγ2●][$]") as "->".
    wp_faa.
    iMod (ghost_var_update _ true with "[$Hγ2●][$]") as "[Hγ2● Hγ2◯]".
    iMod ("Hclose" with "[Hγ1● Hγ2● Hl]"); last done.
    iModIntro. iExists _, _, _. iFrame.
    iPureIntro. simpl in *. lia.
  }
  iIntros (??) "[??]".
  iNext. wp_pures.
  iInv "I" as (???) ">(Hγ1● & Hγ2● & Hl & %)" "Hclose".
  iDestruct (ghost_var_agree with "[$Hγ1●][$]") as "->".
  iDestruct (ghost_var_agree with "[$Hγ2●][$]") as "->".
  simpl in *. subst. wp_load.
  iMod ("Hclose" with "[Hγ1● Hγ2● Hl]").
  - iNext. by iFrame.
  - iApply "HΦ". iPureIntro. lia.
Qed. 

End simple_parallel_add.

Section parallel_add.
  
Definition parallel_add : expr :=
  let: "r" := ref #0 in
  ( if: flip then FAA "r" #1 else #())
  |||
  (if: flip then FAA "r" #1 else #())
  ;;
  !"r".

End parallel_add.

