From clutch.foxtrot Require Import foxtrot par spawn batch_sampling.
  
(** * Sequential version of the batch sampler*)
Section batch.
  Variable N M:nat.
  Definition seq_batch_prog : val :=
    λ: "_",
    let: "x" := (rand #N)  in
    let: "y" := (rand #M) in 
    "x" * (#(M+1)) + "y".

  Definition seq_batch_prog' : val :=
    λ: "_",
    let: "α" := alloc #N in
    let: "α'" := alloc #M in
    let: "x" := (rand("α") #N)  in
    let: "y" := (rand("α'") #M) in 
    "x" * (#(M+1)) + "y".
  
  Definition rand_prog : val := λ: "_", rand #((S N) * (S M)-1).
  
  Section proof.
    Context `{!foxtrotRGS Σ}.
    
    Lemma wp_seq_batch_prog_seq_batch_prog' K j:
    {{{ j ⤇ fill K (seq_batch_prog' #()) }}}
      seq_batch_prog #()
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ lrel_nat v v' }}}.
    Proof.
      iIntros (Φ) "Hspec HΦ".
      rewrite /seq_batch_prog'/seq_batch_prog.
      wp_pures.
      tp_pures j.
      tp_allocnattape j α as "Hα".
      tp_pures j.
      tp_allocnattape j α' as "Hα'".
      tp_pures j.
      tp_bind j (rand(_) _)%E.
      wp_apply (wp_couple_rand_rand_lbl with "[$Hspec $Hα]"); first done.
      iIntros (n) "(?&Hspec&%)".
      wp_pures.
      simpl.
      tp_pures j.
      tp_bind j (rand(_) _)%E.
      wp_apply (wp_couple_rand_rand_lbl with "[$Hspec $Hα']"); first done.
      iIntros (m) "(?&Hspec&%)".
      simpl.
      tp_pures j.
      wp_pures.
      iApply "HΦ". iFrame.
      iPureIntro.
      simpl.
      eexists (n*(M+1)+m); split; repeat f_equal; lia.
    Qed.
    
    Lemma wp_seq_batch_prog'_rand_prog K j:
    {{{ j ⤇ fill K (rand_prog #()) }}}
      seq_batch_prog' #()
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ lrel_nat v v' }}}.
    Proof.
      iIntros (Φ) "Hspec HΦ".
      rewrite /seq_batch_prog'/rand_prog.
      wp_pures.
      wp_alloctape α as "Hα".
      wp_pures.
      wp_alloctape α' as "Hα'".
      wp_pures.
      tp_pures j.
      iMod (pupd_couple_two_tapes_rand _ _ (coupling_f M) with "[$Hα][$][$]") as "(%n&%m&Hα&Hα'&Hspec &%&%)".
      - rewrite TCEq_eq. by erewrite Nat2Z.id.
      - rewrite TCEq_eq. by erewrite Nat2Z.id.
      - lia.
      - apply coupling_f_cond1.
      - apply coupling_f_cond2.
      - apply coupling_f_cond3.
      - simpl. rewrite /coupling_f.
        wp_randtape as "%".
        wp_pures.
        wp_randtape as "%".
        wp_pures.
        iApply "HΦ".
        iFrame.
        iPureIntro.
        simpl. eexists _.
        split; last done.
        repeat f_equal; lia.
    Qed.
  End proof.
  
  Section proof'.
    Context `{!foxtrotRGS Σ, Hspawn: !spawnG Σ}.

    Lemma wp_batch_prog'_seq_batch_prog K j:
    {{{ j ⤇ fill K (seq_batch_prog #()) }}}
      batch_prog' N M #()
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ lrel_nat v v' }}}.
    Proof using Hspawn.
      iIntros (Φ) "Hspec HΦ".
      rewrite /seq_batch_prog/batch_prog'.
      wp_pures.
      wp_alloctape α as "Hα".
      wp_pures.
      wp_alloctape α' as "Hα'".
      wp_pures.
      tp_pures j.
      tp_bind j (rand _)%E.
      iMod (pupd_couple_tape_rand with "[$Hα][$]") as "(%n&Hα&Hspec&%)"; first naive_solver.
      simpl.
      tp_pures j.
      tp_bind j (rand _)%E.
      iMod (pupd_couple_tape_rand with "[$Hα'][$]") as "(%m&Hα'&Hspec&%)"; first naive_solver.
      simpl.
      tp_pures j.
      wp_apply (wp_par (λ x, ⌜x=#n⌝)%I (λ y, ⌜y=#m⌝)%I%I with "[Hα][Hα']").
      - by wp_randtape.
      - by wp_randtape.
      - iIntros (??[->->]).
        iNext.
        wp_pures.
        iApply "HΦ".
        iFrame.
        iPureIntro. simpl.
        eexists (n*(M+1)+m); split; repeat f_equal; lia.
    Qed.
  End proof'.

  Lemma seq_batch_prog_refines_rand_prog :
    ∅ ⊨ seq_batch_prog ≤ctx≤ rand_prog : (TUnit → TNat).
  Proof.
    eapply ctx_refines_transitive with seq_batch_prog';
      apply (refines_sound (#[foxtrotRΣ])); rewrite /interp/=.
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
      wp_apply (wp_seq_batch_prog_seq_batch_prog' with "[$]").
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
      wp_apply (wp_seq_batch_prog'_rand_prog with "[$]").
      iIntros (v) "(%&?&?)". iFrame.
  Qed. 

  Lemma rand_prog_refines_seq_batch_prog :
    ∅ ⊨ rand_prog ≤ctx≤ seq_batch_prog : (TUnit →TNat).
  Proof.
    eapply ctx_refines_transitive with (batch_prog N M); first apply rand_prog_refines_batch_prog.
    eapply ctx_refines_transitive with (batch_prog' N M).
    - apply (refines_sound (#[spawnΣ; foxtrotRΣ])).
      iIntros.
      unfold_rel.
      iIntros (K j) "Hspec".
      wp_pures.
      iFrame.
      iModIntro.
      iIntros (??[->->]).
      unfold_rel.
      iModIntro.
      clear K j.
      iIntros (K j) "Hspec".
      iApply (wp_batch_prog_batch_prog' with "[$]").
      iNext.
      by iIntros.
    - apply (refines_sound (#[spawnΣ; foxtrotRΣ])).
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
      wp_apply (wp_batch_prog'_seq_batch_prog with "[$]").
      by iIntros.
  Qed. 

  Lemma seq_batch_prog_eq_rand_prog :
    ∅ ⊨ seq_batch_prog =ctx= rand_prog : (TUnit → TNat).
  Proof.
    split; [apply seq_batch_prog_refines_rand_prog|apply rand_prog_refines_seq_batch_prog].
  Qed. 
  
End batch.
