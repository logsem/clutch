From iris.algebra Require Import excl_auth.
From clutch.coneris Require Import coneris par spawn con_hash_interface3.
  
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

Section race.
  Variables val_size max_hash_size:nat.
  Variable Hpos: (0<max_hash_size)%nat.
  Context `{!conerisGS Σ, !spawnG Σ, c:con_hash3 Σ val_size max_hash_size Hpos, !inG Σ (excl_authR boolO) }.
  
  Definition race_prog : expr :=
  let: "h" := init_hash3 #() in
  ( "h" #0 (allocate_tape3 #()))
  |||
  ("h" #0 (allocate_tape3 #())).

  Local Opaque amortized_error.
  Lemma race_prog_spec:
  {{{ ↯ (amortized_error val_size max_hash_size Hpos) }}}
    race_prog
    {{{ (z:Z), RET (#z,#z)%Z; True }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    rewrite /race_prog.
    iMod (ghost_var_alloc false) as (γ) "[Hauth Hfrag]".
    wp_apply (con_hash_init3 (nroot.@"1") (λ _ _, ⌜True⌝)%I  (λ m,if bool_decide (m!!0=None) then own γ (◯E false) else own γ (◯E true))%I  with "[Hfrag]" ).
    { iSplit; first done. rewrite bool_decide_eq_true_2; first iFrame.
      by rewrite lookup_empty.
    }
    iIntros (f) "(%&%&%&%&%&%&%&%γ_token&%&#Hinv1&Htoken)".
    iMod (inv_alloc (nroot.@"inv") _ (own γ (●E false) ∗ hash_token3 max_hash_size γ_token ∗ ↯ (amortized_error val_size max_hash_size Hpos)∨ own γ (●E true))%I with "[Herr Hauth Htoken]") as "#Hinv2".
    { iLeft. iFrame. }
    wp_pures.
    wp_apply (wp_par (λ res, ∃ (res':nat), ⌜#res' = res⌝ ∗ hash_frag3 0 res' _ _ _ )%I
                (λ res, ∃ (res':nat), ⌜#res' = res⌝ ∗ hash_frag3 0 res' _ _ _)%I with "[][]").
    - wp_apply (con_hash_alloc_tape3  _ _ _ _ _ _ _ _ _ _ _ _ _ (λ _, ⌜True⌝)%I).
      { iSplit; first done.
        iIntros. iModIntro. by iSplit.
      }
      iIntros (α) "[Ht _]".
      replace 0%Z with (Z.of_nat 0%nat) by done.
      wp_apply (con_hash_spec3 _ _ _ _ _ _ _ _ _ _ _ _ _ (λ res,  hash_frag3 0 res _ _ _ )%I (λ res _, hash_frag3 0 res _ _ _ )%I with "[Ht]"); first iSplit; first done.
      + simpl.
        iIntros (? ?) "Hfrag _ Htauth Hhauth".
        case_bool_decide as H.
        * iApply (state_update_inv_acc with "[][-]"); [|iExact "Hinv2" |].
          { apply subseteq_difference_r; last done.
            apply ndot_preserve_disjoint_r.
            by apply ndot_ne_disjoint. }
          iIntros ">[(Hauth & Htoken &Herr) | Hauth]"; last by iDestruct (ghost_var_agree with "[$][$]") as "%".
          rewrite H.
          iMod (hash_tape_presample with "[//][$][$][$][Htoken]") as "(%&?&?&?)".
          -- repeat apply subseteq_difference_r; last done.
             ++ by apply ndot_preserve_disjoint_l, ndot_ne_disjoint.
             ++ by apply ndot_ne_disjoint.
          -- repeat apply subseteq_difference_r; last done.
             ++ by apply ndot_preserve_disjoint_l, ndot_ne_disjoint.
             ++ by apply ndot_ne_disjoint.
          -- destruct max_hash_size as [|n]; first lia.
             iAssert (hash_token3 (n) γ_token ∗ hash_token3 (1) γ_token)%I with "[Htoken]" as "[_ $]".
             rewrite -hash_token_split. replace (n+1)%nat with (S n) by lia. iFrame.
          -- simpl. iDestruct (hash_tape_auth_frag_agree with "[$][$]") as "%".
             iFrame. iMod (ghost_var_update _ true with "[$][$]") as "[??]". iFrame. iModIntro.
             iIntros.
             rewrite bool_decide_eq_false_2; last first.
             { by rewrite lookup_insert. }
             iMod (hash_auth_insert with "[$][$]"); first done.
             iDestruct (hash_auth_duplicate with "[$]") as "#?".
             { by apply lookup_insert. }
             iFrame. done.
        * iModIntro. case_match; last done.
          iDestruct (hash_auth_duplicate with "[$]") as "#?"; first done.
          by iFrame.
      + iIntros (?) "[?|(%&?)]"; by iFrame.
    - wp_apply (con_hash_alloc_tape3  _ _ _ _ _ _ _ _ _ _ _ _ _ (λ _, ⌜True⌝)%I).
      { iSplit; first done.
        iIntros. iModIntro. by iSplit.
      }
      iIntros (α) "[Ht _]".
      replace 0%Z with (Z.of_nat 0%nat) by done.
      wp_apply (con_hash_spec3 _ _ _ _ _ _ _ _ _ _ _ _ _ (λ res,  hash_frag3 0 res _ _ _ )%I (λ res _, hash_frag3 0 res _ _ _ )%I with "[Ht]"); first iSplit; first done.
      + simpl.
        iIntros (? ?) "Hfrag _ Htauth Hhauth".
        case_bool_decide as H.
        * iApply (state_update_inv_acc with "[][-]"); [|iExact "Hinv2" |].
          { apply subseteq_difference_r; last done.
            apply ndot_preserve_disjoint_r.
            by apply ndot_ne_disjoint. }
          iIntros ">[(Hauth & Htoken &Herr) | Hauth]"; last by iDestruct (ghost_var_agree with "[$][$]") as "%".
          rewrite H.
          iMod (hash_tape_presample with "[//][$][$][$][Htoken]") as "(%&?&?&?)".
          -- repeat apply subseteq_difference_r; last done.
             ++ by apply ndot_preserve_disjoint_l, ndot_ne_disjoint.
             ++ by apply ndot_ne_disjoint.
          -- repeat apply subseteq_difference_r; last done.
             ++ by apply ndot_preserve_disjoint_l, ndot_ne_disjoint.
             ++ by apply ndot_ne_disjoint.
          -- destruct max_hash_size as [|n]; first lia.
             iAssert (hash_token3 (n) γ_token ∗ hash_token3 (1) γ_token)%I with "[Htoken]" as "[_ $]".
             rewrite -hash_token_split. replace (n+1)%nat with (S n) by lia. iFrame.
          -- simpl. iDestruct (hash_tape_auth_frag_agree with "[$][$]") as "%".
             iFrame. iMod (ghost_var_update _ true with "[$][$]") as "[??]". iFrame. iModIntro.
             iIntros.
             rewrite bool_decide_eq_false_2; last first.
             { by rewrite lookup_insert. }
             iMod (hash_auth_insert with "[$][$]"); first done.
             iDestruct (hash_auth_duplicate with "[$]") as "#?".
             { by apply lookup_insert. }
             iFrame. done.
        * iModIntro. case_match; last done.
          iDestruct (hash_auth_duplicate with "[$]") as "#?"; first done.
          by iFrame.
      + iIntros (?) "[?|(%&?)]"; by iFrame.
    - iIntros (??) "[(%res&<-&?)(%res'&<-&?)]".
      iDestruct (hash_frag_frag_agree with "[$][$]") as "%K".
      replace (res) with (res'); last naive_solver.
      by iApply "HΦ".
  Qed.
      
End race.
