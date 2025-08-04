(** von Neumann Trick *)
From clutch.foxtrot Require Import foxtrot lib.conversion lib.min lib.par lib.spawn.

Set Default Proof Using "Type*".

Definition flipL : val := λ: "e", int_to_bool (rand("e") #1%nat).
Definition flip : expr := (flipL #()).

Section von_neumann.
  Variable (N : nat).

  Definition von_neumann_prog: val :=
    λ: "ad",
      let: "l" := ref #0 in
      Fork ("ad" "l") ;;
      (rec: "f" "_" :=
         let: "bias" := min_prog (! "l") #N in
         let: "x" := rand #(S N) in
         let: "y" := rand #(S N) in
         if: "x" = "y" then "f" #() else "x"
      ).

  Definition von_neumann_prog': val :=
    λ: "ad",
      let: "l" := ref #0 in
      Fork ("ad" "l") ;;
      (rec: "f" "_" :=
         let: "bias" := min_prog (! "l") #N in
         let: "α" := alloc #(S N)in
         let: "β" := alloc #(S N) in
         let: "x" := rand("α") #(S N) in
         let: "y" := rand("β") #(S N) in
         if: "x" = "y" then "f" #() else "x"
      ).

  Definition von_neumann_con_prog: val :=
    λ: "ad",
      let: "l" := ref #0 in
      Fork ("ad" "l") ;;
      (rec: "f" "_" :=
         let: "bias" := min_prog (! "l") #N in
         let: "α" := alloc #(S N)in
         let: "β" := alloc #(S N) in
         let, ("x", "y") := ((rand("α") #(S N)) ||| rand("β") #(S N)) in
         if: "x" = "y" then "f" #() else "x"
      ).

  Definition rand_prog: val :=
    λ: "_" "_", flip.
  
  Definition rand_prog': val :=
    λ: "_" "_", let: "x" := alloc #1 in flipL "x" .
  
  Section proof.
    Context `{!foxtrotRGS Σ}.

    
    Lemma wp_von_neumann_prog_von_neumann_prog' K j:
    {{{ j ⤇ fill K (Val von_neumann_prog') }}}
      (Val von_neumann_prog)
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ ((ref lrel_nat → ()) → () → lrel_bool)%lrel v v' }}}.
    Proof.
    Admitted. 
    
    Lemma wp_von_neumann_prog'_rand_prog K j:
    {{{ j ⤇ fill K (Val rand_prog) }}}
      (Val von_neumann_prog')
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ ((ref lrel_nat → ()) → () → lrel_bool)%lrel v v' }}}.
    Proof.
    Admitted. 
    (*   iIntros (Φ) "Hspec HΦ". *)
    (*   rewrite /rand_prog. *)
    (*   tp_pures j. *)
    (*   iLöb as "IH" forall "Hspec HΦ". *)
    (*   rewrite /von_neumann_prog/rand_prog. *)
    (*   wp_pures. *)
    (*   wp_apply (wp_couple_fragmented_rand_rand_inj id with "[$]") as (?) "[% [H|H]]". *)
    (*   - lia. *)
    (*   - intros. simpl. lia. *)
    (*   - iDestruct ("H") as "(%&%&%&Hspec)". *)
    (*     simpl in *. *)
    (*     wp_pures. *)
    (*     rewrite bool_decide_eq_true_2; last lia. *)
    (*     wp_pures. *)
    (*     iApply "HΦ". iFrame. subst. by iExists _. *)
    (*   - simpl. *)
    (*     iDestruct "H" as "(%Hfalse&Hspec)". *)
    (*     wp_pures. *)
    (*     rewrite bool_decide_eq_false_2; last first.  *)
    (*     { intro H'. apply Hfalse. eexists _; split; last done. lia. } *)
    (*     wp_pure. *)
    (*     iApply ("IH" with "[$]"). *)
    (*     iApply "HΦ". *)
    (* Qed.  *)
  End proof.
  
  Section proof'.
    Context `{!foxtrotRGS Σ, !spawnG Σ}.

    Lemma wp_rand_prog_rand_prog' K j:
    {{{ j ⤇ fill K (Val rand_prog') }}}
      (Val rand_prog)
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ ((ref lrel_nat → ()) → () → lrel_bool)%lrel v v' }}}.
    Proof.
    Admitted. 
    (*   iIntros (Φ) "Hspec HΦ". *)
    (*   rewrite /rand_prog/rand_prog'. *)
    (*   tp_pures j. *)
    (*   wp_pures. *)
    (*   tp_allocnattape j α as "Hα". *)
    (*   tp_pures j. *)
    (*   wp_apply (wp_couple_rand_rand_lbl with "[$]"); first done. *)
    (*   iIntros (?) "(?&?&%)". *)
    (*   iApply "HΦ". *)
    (*   iFrame. *)
    (*   iPureIntro. naive_solver. *)
    (* Qed.  *)

    Local Opaque INR.

    
    Lemma wp_rand_prog'_von_neumann_con_prog K j:
    {{{ j ⤇ fill K (Val von_neumann_con_prog) }}}
      (Val rand_prog')
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ ((ref lrel_nat → ()) → () → lrel_bool)%lrel v v' }}}.
    Proof.
    Admitted. 
    
    Lemma wp_von_neumann_con_prog_von_neumann_prog K j:
    {{{ j ⤇ fill K (Val von_neumann_prog) }}}
      (Val von_neumann_con_prog)
      {{{ v, RET v; ∃ v' : val, j ⤇ fill K v' ∗ ((ref lrel_nat → ()) → () → lrel_bool)%lrel v v' }}}.
    Proof.
    Admitted. 
    (*   iIntros (Φ) "Hspec HΦ". *)
    (*   rewrite /von_neumann_prog/rand_prog'. *)
    (*   wp_pures. *)
    (*   wp_alloctape α as "Hα". *)
    (*   wp_pures. *)
    (*   iMod (pupd_epsilon_err) as "(%&%&Hε)". *)
    (*   iRevert "Hspec HΦ Hα". *)
    (*   iApply (ec_ind_simpl _ ((S N / (S N - S M))) with "[][$]"); [lra|apply NM1|]. *)
    (*   iModIntro. *)
    (*   iIntros "[Hind Herr] Hspec HΦ Hα". *)
    (*   tp_pures j. *)
    (*   tp_bind j (rand _)%E. *)
    (*   iMod (pupd_couple_fragmented_tape_rand_inj_rev' (λ x,x) with "[$][$][$]") as "(%&%&Hspec&[H|H])". *)
    (*   - lra. *)
    (*   - done. *)
    (*   - intros. lia. *)
    (*   - iDestruct "H" as "(%&%&%&Hα)". *)
    (*     subst. *)
    (*     simpl. *)
    (*     tp_pures j. *)
    (*     rewrite bool_decide_eq_true_2; last lia. *)
    (*     tp_pures j. *)
    (*     wp_randtape. *)
    (*     simpl. *)
    (*     iApply "HΦ". iFrame. by iExists _. *)
    (*   - iDestruct ("H") as "(%Hfalse&Hα&Herr)". *)
    (*     simpl. *)
    (*     tp_pures j. *)
    (*     rewrite bool_decide_eq_false_2; last first. *)
    (*     { intro H'. apply Hfalse. eexists _; split; last done. lia. } *)
    (*     tp_pure j. *)
    (*     iApply ("Hind" with "[$][$][$][$]"). *)
    (* Qed.  *)
    
  End proof'.

  Lemma von_neumann_prog_refines_rand_prog :
    ∅ ⊨ von_neumann_prog ≤ctx≤ rand_prog : ((TRef TNat → TUnit) → TUnit →TBool).
  Proof.
    eapply ctx_refines_transitive with von_neumann_prog';
    apply (refines_sound (#[foxtrotRΣ])); rewrite /interp/=;
    iIntros; unfold_rel;
      iIntros (K j) "Hspec".
    - wp_apply (wp_von_neumann_prog_von_neumann_prog' with "[$]"); by iIntros.
    - wp_apply (wp_von_neumann_prog'_rand_prog with "[$]"); by iIntros.
  Qed. 

  Lemma rand_prog_refines_von_neumann_prog :
    ∅ ⊨ rand_prog ≤ctx≤ von_neumann_prog : ((TRef TNat → TUnit) → TUnit →TBool).
  Proof.
    eapply ctx_refines_transitive with rand_prog'; last eapply ctx_refines_transitive with von_neumann_con_prog;
      apply (refines_sound (#[spawnΣ; foxtrotRΣ])); iIntros; unfold_rel; iIntros (K j) "spec"; simpl.
    - wp_apply (wp_rand_prog_rand_prog' with "[$]"); by iIntros.
    - wp_apply (wp_rand_prog'_von_neumann_con_prog with "[$]"); by iIntros.
    - wp_apply (wp_von_neumann_con_prog_von_neumann_prog with "[$]"); by iIntros.
  Qed.
  
  Lemma von_neumann_prog_eq_rand_prog :
    ∅ ⊨ von_neumann_prog =ctx= rand_prog : ((TRef TNat → TUnit) → TUnit →TBool).
  Proof.
    split; [apply von_neumann_prog_refines_rand_prog|apply rand_prog_refines_von_neumann_prog].
  Qed. 

End von_neumann. 


 

