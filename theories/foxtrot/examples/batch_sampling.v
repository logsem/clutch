From clutch.foxtrot Require Import foxtrot par spawn.

Section batch.
  Variable N M:nat.
  Definition batch_prog :val:=
    λ: "_", 
    let, ("x", "y") := ((rand #N) ||| rand #M) in
    "x" * (#(M+1)) + "y".

  
  Definition batch_prog' : val :=
    λ: "_",
    let: "α" := alloc #N in
    let: "α'" := alloc #M in
    let, ("x", "y") := ((rand("α") #N) ||| rand("α'") #M) in
    "x" * (#(M+1)) + "y".


  Definition rand_prog : val := λ: "_", rand #((S N) * (S M)-1).

  Definition coupling_f n m:= n*(S M) +m.

  Lemma coupling_f_cond1 n m:n < S N → m < S M → coupling_f n m < S N * S M.
  Proof.
    intros. rewrite /coupling_f. assert (n* S M + m< N * S M+ S M); last lia.
    apply Nat.add_le_lt_mono; last lia.
    apply Nat.mul_le_mono_r. lia.
  Qed. 

  Lemma coupling_f_cond2 n n' m m': n < S N → n' < S N → m < S M → m' < S M → coupling_f n m = coupling_f n' m' → n = n' ∧ m = m'.
  Proof.
    rewrite /coupling_f.
    intros ? ? ? ? H'.
    apply Nat.mul_split_l in H'; lia.
  Qed. 

  Lemma coupling_f_cond3 x: x < S N * S M → ∃ n m : nat, n < S N ∧ m < S M ∧ coupling_f n m = x.
  Proof.
    intros Hx.
    rewrite /coupling_f.
    erewrite (Nat.div_mod x (S M)); last lia.
    eexists _, _; repeat split; last first.
    - f_equal. by rewrite Nat.mul_comm.
    - apply Nat.mod_upper_bound. lia.
    - apply Nat.Div0.div_lt_upper_bound. lia.
  Qed. 
  
  Section proof.
    Context `{!foxtrotRGS Σ, Hspawn: !spawnG Σ}.
    
    Lemma wp_batch_prog_batch_prog' K j:
    {{{ j ⤇ fill K (batch_prog' #()) }}}
      batch_prog #()
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ lrel_nat v v' }}}.
    Proof using Hspawn.
      iIntros (Φ) "Hspec HΦ".
      rewrite /batch_prog'/batch_prog.
      wp_pures.
      tp_pures j.
      tp_allocnattape j α as "Hα".
      tp_pures j.
      tp_allocnattape j α' as "Hα'".
      do 2 tp_pure j.
      tp_bind j (_|||_)%E.
      iMod (tp_par with "[$]") as "(%j1 & %j2 & %K1 & %K2 & Hspec1 & Hspec2 & Hcont)".
      wp_apply (wp_par (λ x, ∃ (n:nat), ⌜x = # n⌝ ∗ j1 ⤇ fill K1 (#n))%I (λ x, ∃ (m:nat), ⌜x = # m⌝ ∗ j2 ⤇ fill K2 (#m))%I with "[Hα Hspec1][Hα' Hspec2]").
      - wp_apply (wp_couple_rand_rand_lbl with "[$]"); first done.
        iIntros (?) "(?&?&%)".
        by iFrame.
      - wp_apply (wp_couple_rand_rand_lbl with "[$]"); first done.
        iIntros (?) "(?&?&%)".
        by iFrame.
      - iIntros (??) "[(%n&%&?)(%m&%&?)]".
        subst.
        iNext.
        iMod ("Hcont" with "[$]") as "Hspec".
        simpl.
        tp_pures j.
        wp_pures.
        iApply "HΦ".
        iFrame.
        iPureIntro.
        simpl.
        eexists (n*(M+1)+m); split; repeat f_equal; lia.
    Qed.
    
    Lemma wp_batch_prog'_rand_prog K j:
    {{{ j ⤇ fill K (rand_prog #()) }}}
      batch_prog' #()
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ lrel_nat v v' }}}.
    Proof using Hspawn.
      iIntros (Φ) "Hspec HΦ".
      rewrite /batch_prog'/rand_prog.
      wp_pures.
      wp_alloctape α as "Hα".
      wp_pures.
      wp_alloctape α' as "Hα'".
      wp_pures.
      tp_pures j.
      iMod (pupd_couple_two_tapes_rand _ _ coupling_f with "[$Hα][$][$]") as "(%n&%m&Hα&Hα'&Hspec &%&%)".
      - rewrite TCEq_eq. by erewrite Nat2Z.id.
      - rewrite TCEq_eq. by erewrite Nat2Z.id.
      - lia.
      - apply coupling_f_cond1.
      - apply coupling_f_cond2.
      - apply coupling_f_cond3.
      - simpl. rewrite /coupling_f.
        wp_apply (wp_par (λ x, ⌜x=#n⌝)%I(λ x, ⌜x=#m⌝)%I with "[Hα][Hα']").
        + by wp_randtape as "%".
        + by wp_randtape as "%".
        + iIntros (??) "[-> ->]".
          iNext. wp_pures.
          iApply "HΦ".
          iFrame.
          iPureIntro.
          simpl. eexists _.
          split; last done.
          repeat f_equal; lia.
    Qed.
  End proof.
  
  Section proof'.
    Context `{!foxtrotRGS Σ}.

    Lemma wp_rand_prog_batch_prog K j:
    {{{ j ⤇ fill K (batch_prog #()) }}}
      rand_prog #()
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ lrel_nat v v' }}}.
    Proof.
      iIntros (Φ) "Hspec HΦ".
      rewrite /batch_prog/rand_prog.
      wp_pures.
      tp_pure j.
      iApply wp_pupd.
      tp_bind j (_|||_)%E.
      iMod (tp_par with "[$]") as "(%j1&%j2&%K1&%K2&Hspec1&Hspec2&Hcont)".
      wp_apply (wp_couple_rand_two_rands with "[$Hspec1 $Hspec2]").
      - rewrite TCEq_eq. by erewrite Nat2Z.id.
      - rewrite TCEq_eq. by erewrite Nat2Z.id.
      - lia.
      - apply coupling_f_cond1.
      - apply coupling_f_cond2.
      - apply coupling_f_cond3.
      - iIntros (?) "(%n&%m&%&%&%&Hspec1&Hspec2)".
        subst.
        iMod ("Hcont" with "[$]") as "Hspec".
        simpl. tp_pures j.
        rewrite /coupling_f.
        iApply "HΦ".
        iFrame.
        iPureIntro.
        simpl.
        eexists _; split; first done.
        repeat f_equal; lia.
    Qed.
  End proof'.

  Lemma batch_prog_refines_rand_prog :
    ∅ ⊨ batch_prog ≤ctx≤ rand_prog : (TUnit → TNat).
  Proof.
    eapply ctx_refines_transitive with batch_prog';
      apply (refines_sound (#[spawnΣ; foxtrotRΣ])); rewrite /interp/=.
    - iIntros. unfold_rel.
      iIntros (K j) "Hspec".
      wp_pures.
      iFrame.
      iModIntro.
      iModIntro.
      iIntros (??[->->]).
      unfold_rel.
      clear K j.
      iIntros (K j) "Hspec".
      wp_apply (wp_batch_prog_batch_prog' with "[$]").
      iIntros (v) "(%&?&?)". iFrame. 
    - iIntros. unfold_rel.
      iIntros (K j) "Hspec".
      wp_pures.
      iFrame.
      iModIntro.
      iIntros (??[->->]).
      unfold_rel.
      iModIntro.
      clear K j.
      iIntros (K j) "Hspec". 
      wp_apply (wp_batch_prog'_rand_prog with "[$]").
      iIntros (v) "(%&?&?)". iFrame.
  Qed. 

  Lemma rand_prog_refines_batch_prog :
    ∅ ⊨ rand_prog ≤ctx≤ batch_prog : (TUnit →TNat).
  Proof.
    apply (refines_sound (foxtrotRΣ)).
    iIntros. unfold_rel.
    iIntros (K j) "Hspec".
    wp_pures.
    iFrame.
    iModIntro.
    iIntros (??[->->]).
    unfold_rel.
    iModIntro.
    clear K j.
    iIntros (K j) "Hspec". 
    wp_apply (wp_rand_prog_batch_prog with "[$]").
    iIntros (v) "(%&?&?)". iFrame.
  Qed. 

  Lemma batch_prog_eq_rand_prog :
    ∅ ⊨ batch_prog =ctx= rand_prog : (TUnit →TNat).
  Proof.
    split; [apply batch_prog_refines_rand_prog|apply rand_prog_refines_batch_prog].
  Qed. 

  
End batch.
