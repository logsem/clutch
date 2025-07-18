From clutch.foxtrot Require Import foxtrot par spawn.

Section encr.
  Variable N:nat.
  
  Definition encr_prog : expr :=
    let: "x" := ref #0 in 
    ((let: "msg":=rand #N in
     FAA "x" "msg")
       |||
       (let: "key":=rand #N in
       FAA "x" "key")
    ) ;;
    !"x" `rem` #(N+1).


  Definition encr_prog' : expr :=
    let: "x" := ref #0 in
    let: "α" := alloc #N in
    let: "α'" := alloc #N in
    ((let: "msg":=rand("α") #N in
     FAA "x" "msg")
       |||
       (let: "key":=rand("α'") #N in
       FAA "x" "key")
    ) ;;
    !"x" `rem` #(N+1).

  Definition rand_prog : expr := rand #N.

  
  Definition coupling_f (n:nat) (_:n<=N) := (λ (x:nat), if bool_decide (x<=N)%nat then (x+n) `mod` (N+1) else x).

  Instance coupling_f_Bij n Hn: Bij (coupling_f n Hn).
  Proof.
    split.
    - intros x y. rewrite /coupling_f.
      case_bool_decide as H1; case_bool_decide as H2; try lia; intros Heq; subst.
      + apply (f_equal Z.of_nat) in Heq.
        rewrite !Nat2Z.inj_mod in Heq.
        rewrite -Z.sub_move_0_r in Heq.
        assert ((((x + n)%nat `mod` (N + 1)%nat - (y + n)%nat `mod` (N + 1)%nat)`mod` (N+1)%nat)%Z = 0%Z) as Heq'.
        { rewrite Z.mod_small; lia. }
        rewrite -Zminus_mod in Heq'.
        assert (((x + n)%nat - (y + n)%nat)%Z = (Z.of_nat x - Z.of_nat y))%Z as Hrewrite by lia.
        rewrite Hrewrite in Heq'.
        rewrite Z.mod_divide in Heq'; last lia.
        assert (-N<=x-y<=N)%Z as Hineq by lia.
        destruct Heq' as [x' Heq'].
        rewrite Heq' in Hineq.
        destruct (Z.le_gt_cases 0%Z x') as [H'|H'].
        * apply Zle_lt_or_eq in H'. destruct H' as [H'|H']; last lia.
          assert ((N + 1)%nat<=x' * (N + 1)%nat)%Z; try lia.
          rewrite -{1}(Z.mul_1_l (_+_)%nat).
          apply Z.mul_le_mono_nonneg_r; lia.
        * assert (x' * (N + 1)%nat<=- (N + 1)%nat)%Z; try lia.
          rewrite -{2}(Z.mul_1_l (_+_)%nat).
          rewrite -Z.mul_opp_l.
          apply Z.mul_le_mono_nonneg_r; lia.
      + exfalso.
        apply H2.
        unshelve epose proof Nat.mod_upper_bound (x+n) (N+1) _; lia.
      + exfalso.
        apply H1.
        unshelve epose proof Nat.mod_upper_bound (y+n) (N+1) _; lia.
    - intros x.
      destruct (decide (x<=N)); rewrite /coupling_f.
      + eexists ((x+(N+1)-n)`mod`(N+1)).
        rewrite bool_decide_eq_true_2; last first.
        { unshelve epose proof Nat.mod_upper_bound (x+(N+1)-n) (N+1) _; lia. }
        rewrite Nat.Div0.add_mod_idemp_l.
        replace (_+_-_+_) with (x+(N+1)) by lia.
        replace (N+1) with (1*(N+1)) at 1 by lia.
        rewrite Nat.Div0.mod_add.
        rewrite Nat.mod_small; lia.
      + exists x. rewrite bool_decide_eq_false_2; lia.
  Qed.

  (* Definition coupling_f' n Hn := f_inv (coupling_f n Hn). *)

  Section proof.
    Context `{!foxtrotRGS Σ, !spawnG Σ}.
    
    Lemma wp_encr_prog_encr_prog' K j:
    {{{ j ⤇ fill K encr_prog' }}}
      encr_prog
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ lrel_nat v v' }}}.
    Proof.
    Admitted.

    Lemma wp_encr_prog'_rand_prog K j:
    {{{ j ⤇ fill K rand_prog }}}
      encr_prog'
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ lrel_nat v v' }}}.
    Proof.
    Admitted. 
  End proof.
  
  Section proof'.
    Context `{!foxtrotRGS Σ}.

    Lemma wp_rand_prog_encr_prog K j:
    {{{ j ⤇ fill K encr_prog }}}
      rand_prog
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ lrel_nat v v' }}}.
    Proof.
      iIntros (Φ) "Hspec HΦ".
      rewrite /encr_prog /rand_prog/=.
      iApply wp_pupd.
      tp_alloc j as l "Hl".
      do 2 tp_pure j.
      tp_bind j (_ ||| _)%E.
      iMod (tp_par with "[$]") as "(%j1&%j2&%K1&%K2&Hspec1&Hspec2&Hcont)".
      tp_bind j1 (rand _)%E.
      iMod (pupd_rand with "[$]") as "(%n&Hspec1&%Hn)".
      simpl.
      tp_pures j1.
      tp_faa j1.
      replace (0+Z.of_nat n)%Z with (Z.of_nat n) by lia.
      tp_bind j2 (rand _)%E.
      unshelve wp_apply (wp_couple_rand_rand' _ (coupling_f n Hn) with "[$]").
      - intros n' Hn'. rewrite /coupling_f.
        rewrite bool_decide_eq_true_2; last lia.
        epose proof Nat.mod_upper_bound (n'+n) (N+1) _; lia.
      - iIntros (n') "(%Hn'&Hspec2)".
        rewrite /coupling_f.
        simpl.
        tp_pures j2.
        tp_faa j2.
        iMod ("Hcont" with "[$]") as "Hspec".
        tp_pures j.
        tp_load j.
        tp_pures j.
        iModIntro.
        rewrite bool_decide_eq_true_2; last done.
        iApply "HΦ".
        iFrame.
        iExists _; iPureIntro; split; first done.
        do 2 f_equal.
        rewrite -Nat2Z.inj_add.
        rewrite Z.rem_mod_nonneg; try lia.
        rewrite Nat2Z.inj_mod.
        f_equal; lia.
        Unshelve. lia.
    Qed. 
  End proof'.



  Lemma encr_prog_refines_rand_prog :
    ∅ ⊨ encr_prog ≤ctx≤ rand_prog : TNat.
  Proof.
    eapply ctx_refines_transitive with encr_prog';
      apply (refines_sound (#[spawnΣ; foxtrotRΣ])); rewrite /interp/=.
    - iIntros. unfold_rel.
      iIntros (K j) "Hspec".
      wp_apply (wp_encr_prog_encr_prog' with "[$]").
      iIntros (v) "(%&?&?)". iFrame. 
    - iIntros. unfold_rel.
      iIntros (K j) "Hspec".
      wp_apply (wp_encr_prog'_rand_prog with "[$]").
      iIntros (v) "(%&?&?)". iFrame.
  Qed. 

  Lemma rand_prog_refines_encr_prog :
    ∅ ⊨ rand_prog ≤ctx≤ encr_prog : TNat.
  Proof.
    apply (refines_sound (foxtrotRΣ)).
    iIntros. unfold_rel.
    iIntros (K j) "Hspec".
    wp_apply (wp_rand_prog_encr_prog with "[$]").
    iIntros (v) "(%&?&?)". iFrame.
  Qed. 

  Lemma encr_prog_eq_rand_prog :
    ∅ ⊨ encr_prog =ctx= rand_prog : TNat.
  Proof.
    split; [apply encr_prog_refines_rand_prog|apply rand_prog_refines_encr_prog].
  Qed. 

End encr.
