From iris.base_logic.lib Require Import ghost_var.
From clutch.foxtrot Require Import foxtrot par spawn sampler.

(* Similar to the one-time pad in encryption.v, but now the message is produced
   by unknown code *)
Section encr.
  Variable N:nat.
  
  Definition coupling_f (n:nat) (_:n<=N) := (λ (x:nat), if bool_decide (x<=N)%nat then (x+n) `mod` (N+1) else x).

  Lemma coupling_f_Bij n Hn: Bij (coupling_f n Hn).
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
 
  Variable f:val.
  
  Definition encr_prog : expr :=
    let: "x" := ref #0 in 
    ((let: "msg":=f #() in
     FAA "x" "msg")
       |||
       (let: "key":=rand #N in
       FAA "x" "key")
    ) ;;
    !"x" `rem` #(N+1).

  Definition rand_prog : expr := rand #N.

  
  Context `{Hsample: !sample_spec N f}.
  
  (* Definition coupling_f' n Hn := f_inv (coupling_f n Hn). *)

  Section proof.
    Context `{!foxtrotRGS Σ, Hspawn: !spawnG Σ, Hghost : !ghost_varG Σ bool}.
             
    Definition encr_prog' : expr :=
      let: "x" := ref #0 in
      let: "α" := sample_allocate_tape #() in
      let: "α'" := alloc #N in
      ((let: "msg":=sample_with_tape "α" in
        FAA "x" "msg")
         |||
         (let: "key":=rand("α'") #N in
          FAA "x" "key")
      ) ;;
      !"x" `rem` #(N+1).

    
    Lemma wp_encr_prog_encr_prog' K j:
    {{{ j ⤇ fill K encr_prog' }}}
      encr_prog
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ lrel_nat v v' }}}.
    Proof using Hspawn.
      iIntros (Φ) "Hspec HΦ".
      rewrite /encr_prog/encr_prog'.
      tp_alloc j as l' "Hl'".
      wp_alloc l as "Hl".
      tp_pures j.
      wp_pures.
      tp_bind j (sample_allocate_tape _).
      iMod (sample_allocate_tape_spec' with "[$]") as "(%α&Hα&Hspec)".
      simpl.
      tp_pures j.
      tp_allocnattape j α' as "Hα'".
      do 2 tp_pure j.
      tp_bind j (_|||_)%E.
      iMod (tp_par with "[$]") as "(%j1&%j2&%K1&%K2&Hspec1&Hspec2&Hcont)".
      iMod (inv_alloc nroot _ (∃ (n:nat), l↦ #n ∗ l'↦ₛ#n)%I with "[Hl Hl']") as "#Hinv".
      { replace 0%Z with (Z.of_nat 0) by lia. iFrame. }
      wp_apply (wp_par (λ _, ∃ (v1:val), j1 ⤇ fill K1 v1)%I (λ _, ∃ (v2:val), j2 ⤇ fill K2 v2)%I%I with "[Hα Hspec1][Hα' Hspec2]").
      - tp_bind j1 (sample_with_tape α)%E.
        wp_apply (sample_tape_spec_couple' with "[$]"). 
        iIntros (?) "[_ Hspec1]".
        simpl.
        tp_pures j1. wp_pures.
        iInv "Hinv" as "(%&>H&>H')" "Hclose".
        tp_faa j1.
        wp_faa.
        rewrite -Nat2Z.inj_add.
        iMod ("Hclose" with "[$]"). by iFrame. 
      - tp_bind j2 (rand(#lbl:α') _)%E.
        wp_apply (wp_couple_rand_rand_lbl with "[$]"); first naive_solver.
        iIntros (?) "(_&Hspec2&%)".
        simpl.
        tp_pures j2. wp_pures.
        iInv "Hinv" as "(%&>H&>H')" "Hclose".
        tp_faa j2.
        wp_faa.
        rewrite -Nat2Z.inj_add.
        iMod ("Hclose" with "[$]"). by iFrame. 
      - iIntros (??) " [(%&Hspec1) (%&Hspec2)]".
        iNext.
        wp_pures.
        iMod ("Hcont" with "[$]") as "Hspec".
        simpl. tp_pures j.
        wp_bind (! _)%E.
        tp_bind j (! _)%E.
        iInv "Hinv" as ">(%&?&?)" "Hclose".
        tp_load j.
        wp_load.
        iMod ("Hclose" with "[$]") as "_".
        iModIntro.
        tp_pures j.
        wp_pures.
        iModIntro.
        iApply "HΦ".
        iFrame.
        iExists _. iPureIntro.
        rewrite Z.rem_mod_nonneg; try lia.
        replace (Z.of_nat N + 1)%Z with (Z.of_nat (S N)) by lia.
        rewrite -Nat2Z.inj_mod; naive_solver.
    Qed. 

    Lemma wp_encr_prog'_rand_prog K j:
    {{{ j ⤇ fill K rand_prog }}}
      encr_prog'
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ lrel_nat v v' }}}.
    Proof using Hspawn Hghost.
      iIntros (Φ) "Hspec HΦ".
      rewrite /encr_prog'/rand_prog.
      wp_alloc l as "Hl".
      wp_pures.
      wp_apply (sample_allocate_tape_spec with "[//]") as (α) "Hα".
      wp_pures.
      wp_alloctape α' as "Hα'".
      wp_pures.
      iMod (sample_tape_presample with "[$Hα]") as "(%n&Hα)". simpl.
      pose proof fin_to_nat_lt n as K1.
      assert (n<=N)%nat as K2 by lia.
      iMod (pupd_couple_tape_rand _ (coupling_f n K2) with "[$Hα'][$]") as "(%n'&Hα'&Hspec&%)".
      { intros n' Hn'. rewrite /coupling_f.
        rewrite bool_decide_eq_true_2; last lia.
        epose proof Nat.mod_upper_bound (n'+n) (N+1) _; lia. }
      simpl.
      rewrite /coupling_f. rewrite bool_decide_eq_true_2; last done.
      iMod (ghost_var_alloc false) as "(%γ1 & [Hγ1 Hγ1'])".
      iMod (ghost_var_alloc false) as "(%γ2 & [Hγ2 Hγ2'])".
      iMod (inv_alloc nroot _ (∃ (b1 b2:bool), ghost_var γ1 (1/2) b1 ∗ ghost_var γ2 (1/2) b2 ∗ l ↦ # ((if b1 then n else 0)+(if b2 then n' else 0)))%I with "[$]") as "#Hinv".
      wp_apply (wp_par (λ _, ghost_var γ1 (1/2) true)(λ _, ghost_var γ2 (1/2) true) with "[Hα Hγ1][Hα' Hγ2]").
      - wp_apply (sample_tape_spec_some with "[$]") as "_".
        wp_pures.
        iInv "Hinv" as ">(%&%&?&?&Hl)" "Hclose".
        iDestruct (ghost_var_agree with "[$Hγ1][$]") as "<-".
        wp_faa.
        iMod (ghost_var_update_halves true with "[$Hγ1][$]") as "[??]".
        iFrame.
        iMod ("Hclose" with "[-]"); last done.
        iFrame.
        iNext.
        replace (Z.of_nat n + (if b2 then Z.of_nat n' else 0))%Z with (0 + (if b2 then Z.of_nat n' else 0) + Z.of_nat n)%Z by lia. iFrame.
      - wp_apply (wp_rand_tape with "[$]").
        iIntros "(_&%)".
        wp_pures.
        iInv "Hinv" as ">(%&%&?&?&Hl)" "Hclose".
        iDestruct (ghost_var_agree with "[$Hγ2][$]") as "<-".
        wp_faa.
        iMod (ghost_var_update_halves true with "[$Hγ2][$]") as "[??]".
        iFrame.
        iMod ("Hclose" with "[-]"); last done.
        iFrame.
        iNext.
        replace ((if b1 then Z.of_nat n else 0) + Z.of_nat n')%Z with ((if b1 then Z.of_nat n else 0) + 0 + Z.of_nat n')%Z by lia. iFrame.
      - iIntros (??) "[Hγ1 Hγ2]". iNext.
        wp_pures.
        wp_bind (! _)%E.
        iInv "Hinv" as ">(%&%&?&?&Hl)" "Hclose".
        iDestruct (ghost_var_agree with "[$Hγ1][$]") as "<-".
        iDestruct (ghost_var_agree with "[$Hγ2][$]") as "<-".
        wp_load.
        iMod ("Hclose" with "[$Hγ1 $Hγ2 $Hl]").
        iModIntro.
        wp_pures.
        rewrite Z.add_comm.
        iApply "HΦ".
        iFrame.
        iModIntro. iPureIntro. simpl.
        rewrite Z.rem_mod_nonneg; try lia.
        eexists _.
        split; last done.
        rewrite !Nat2Z.inj_mod.
        repeat f_equal; lia.
        Unshelve.
        + apply coupling_f_Bij.
        + lia.
    Qed.
    
  End proof.
  
  Section proof'.
    Context `{!foxtrotRGS Σ}.

    Lemma wp_rand_prog_encr_prog K j:
    {{{ j ⤇ fill K encr_prog }}}
      rand_prog
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ lrel_nat v v' }}}.
    Proof using Hsample.
      iIntros (Φ) "Hspec HΦ".
      rewrite /encr_prog /rand_prog/=.
      iApply wp_pupd.
      tp_alloc j as l "Hl".
      do 2 tp_pure j.
      tp_bind j (_ ||| _)%E.
      iMod (tp_par with "[$]") as "(%j1&%j2&%K1&%K2&Hspec1&Hspec2&Hcont)".
      tp_bind j1 (f #())%E.
      iMod (sample_without_tape_spec' with "[$]") as "(%n&Hspec1)".
      pose proof fin_to_nat_lt n.
      simpl.
      tp_pures j1.
      tp_faa j1.
      replace (0+Z.of_nat n)%Z with (Z.of_nat n) by lia.
      tp_bind j2 (rand _)%E.
      assert (n<=N)%nat as Hn by lia.
      unshelve wp_apply (wp_couple_rand_rand' _ (coupling_f n Hn) with "[$]").
      - apply coupling_f_Bij.
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
  Proof using Hsample.
    eapply ctx_refines_transitive with encr_prog';
      apply (refines_sound (#[spawnΣ; foxtrotRΣ; ghost_varΣ bool])); rewrite /interp/=.
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
  Proof using Hsample.
    apply (refines_sound (foxtrotRΣ)).
    iIntros. unfold_rel.
    iIntros (K j) "Hspec".
    wp_apply (wp_rand_prog_encr_prog with "[$]").
    iIntros (v) "(%&?&?)". iFrame.
  Qed. 

  Lemma encr_prog_eq_rand_prog :
    ∅ ⊨ encr_prog =ctx= rand_prog : TNat.
  Proof using Hsample.
    split; [apply encr_prog_refines_rand_prog|apply rand_prog_refines_encr_prog].
  Qed. 

End encr.
