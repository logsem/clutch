From clutch.foxtrot Require Import foxtrot.

Set Default Proof Using "Type*".

Section rejection_sampler.
  Variable (N M : nat).
  Context (Hineq : (M < N)%nat).

  Local Lemma NM1: (1 < (S N / (S N - S M)))%R.
  Proof.
    rewrite !S_INR.
    apply lt_INR in Hineq.
    apply Rcomplements.Rlt_div_r; [lra|].
    rewrite Rmult_1_l.
    pose proof pos_INR M. lra.
  Qed.
  Local Hint Resolve NM1:core.

  Local Lemma NMpos : (0 < (S N / (S N - S M)))%R.
  Proof. pose proof NM1; lra. Qed.

  Local Hint Resolve NMpos:core.

  Definition rejection_sampler_prog: val :=
    rec: "f" "_" :=
      let: "x" := rand #N in
      if: ("x" ≤ #M) then "x"
      else "f" #().

  Definition rand_prog: val :=
    λ: "_", rand #M.

  
  Definition rand_prog': val :=
    λ: "_", let: "x" := alloc #M in rand("x") #M.
  
  Section proof.
    Context `{!foxtrotRGS Σ}.
    
    Lemma wp_rejection_sampler_prog_rand_prog K j:
    {{{ j ⤇ fill K (rand_prog #()) }}}
      (rejection_sampler_prog #())
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ lrel_nat v v' }}}.
    Proof.
      iIntros (Φ) "Hspec HΦ".
      rewrite /rand_prog.
      tp_pures j.
      iLöb as "IH" forall "Hspec HΦ".
      rewrite /rejection_sampler_prog/rand_prog.
      wp_pures.
      wp_apply (wp_couple_fragmented_rand_rand_inj id with "[$]") as (?) "[% [H|H]]".
      - lia.
      - intros. simpl. lia.
      - iDestruct ("H") as "(%&%&%&Hspec)".
        simpl in *.
        wp_pures.
        rewrite bool_decide_eq_true_2; last lia.
        wp_pures.
        iApply "HΦ". iFrame. subst. by iExists _.
      - simpl.
        iDestruct "H" as "(%Hfalse&Hspec)".
        wp_pures.
        rewrite bool_decide_eq_false_2; last first. 
        { intro H'. apply Hfalse. eexists _; split; last done. lia. }
        wp_pure.
        iApply ("IH" with "[$]").
        iApply "HΦ".
    Qed. 
  End proof.
  
  Section proof'.
    Context `{!foxtrotRGS Σ}.

    Lemma wp_rand_prog_rand_prog' K j:
    {{{ j ⤇ fill K (rand_prog' #()) }}}
      rand_prog #()
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ lrel_nat v v' }}}.
    Proof.
      iIntros (Φ) "Hspec HΦ".
      rewrite /rand_prog/rand_prog'.
      tp_pures j.
      wp_pures.
      tp_allocnattape j α as "Hα".
      tp_pures j.
      wp_apply (wp_couple_rand_rand_lbl with "[$]"); first done.
      iIntros (?) "(?&?&%)".
      iApply "HΦ".
      iFrame.
      iPureIntro. naive_solver.
    Qed. 

    Local Opaque INR.
    
    Lemma wp_rand_prog'_rejection_sampler_prog K j:
    {{{ j ⤇ fill K (rejection_sampler_prog #()) }}}
      rand_prog' #()
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ lrel_nat v v' }}}.
    Proof.
      iIntros (Φ) "Hspec HΦ".
      rewrite /rejection_sampler_prog/rand_prog'.
      wp_pures.
      wp_alloctape α as "Hα".
      wp_pures.
      iMod (pupd_epsilon_err) as "(%&%&Hε)".
      iRevert "Hspec HΦ Hα".
      iApply (ec_ind_simpl _ ((S N / (S N - S M))) with "[][$]"); [lra|apply NM1|].
      iModIntro.
      iIntros "[Hind Herr] Hspec HΦ Hα".
      tp_pures j.
      tp_bind j (rand _)%E.
      iMod (pupd_couple_fragmented_tape_rand_inj_rev' (λ x,x) with "[$][$][$]") as "(%&%&Hspec&[H|H])".
      - lra.
      - done.
      - intros. lia.
      - iDestruct "H" as "(%&%&%&Hα)".
        subst.
        simpl.
        tp_pures j.
        rewrite bool_decide_eq_true_2; last lia.
        tp_pures j.
        wp_randtape.
        simpl.
        iApply "HΦ". iFrame. by iExists _.
      - iDestruct ("H") as "(%Hfalse&Hα&Herr)".
        simpl.
        tp_pures j.
        rewrite bool_decide_eq_false_2; last first.
        { intro H'. apply Hfalse. eexists _; split; last done. lia. }
        tp_pure j.
        iApply ("Hind" with "[$][$][$][$]").
    Qed. 
    
  End proof'.

  Lemma rejection_sampler_prog_refines_rand_prog :
    ∅ ⊨ rejection_sampler_prog ≤ctx≤ rand_prog : (TUnit→TNat).
  Proof.
    apply (refines_sound (#[foxtrotRΣ])); rewrite /interp/=.
    iIntros. unfold_rel.
    iIntros (K j) "Hspec".
    wp_pures.
    iFrame. iModIntro.
    iModIntro. 
    iIntros (??) "[->->]".
    unfold_rel.
    clear -Hineq.
    iIntros (K j) "Hspec".
    wp_apply (wp_rejection_sampler_prog_rand_prog with "[$]").
    iIntros (v) "(%&?&?)". iFrame.
  Qed.

  Lemma rand_prog_refines_rejection_sampler_prog :
    ∅ ⊨ rand_prog ≤ctx≤ rejection_sampler_prog : (TUnit→TNat).
  Proof.
    eapply ctx_refines_transitive with rand_prog';
    apply (refines_sound (foxtrotRΣ)).
    - iIntros. unfold_rel.
      iIntros (K j) "Hspec".
      wp_pures.
      iFrame. iModIntro.
      iModIntro. 
      iIntros (??) "[->->]".
      unfold_rel.
      clear -Hineq.
      iIntros (K j) "Hspec".
      wp_apply (wp_rand_prog_rand_prog' with "[$]").
      iIntros (v) "(%&?&?)". iFrame. 
    - iIntros. unfold_rel.
      iIntros (K j) "Hspec".
      wp_pures.
      iFrame. iModIntro.
      iModIntro. 
      iIntros (??) "[->->]".
      unfold_rel.
      clear -Hineq.
      iIntros (K j) "Hspec".
      wp_apply (wp_rand_prog'_rejection_sampler_prog with "[$]").
      iIntros (v) "(%&?&?)". iFrame. 
  Qed.

  Lemma rejection_sampler_prog_eq_rand_prog :
    ∅ ⊨ rejection_sampler_prog =ctx= rand_prog : (TUnit→TNat).
  Proof.
    split; [apply rejection_sampler_prog_refines_rand_prog|apply rand_prog_refines_rejection_sampler_prog].
  Qed. 

End rejection_sampler. 


 
