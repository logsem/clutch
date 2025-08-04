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
         let: "x" := (rand #(S N)) ≤ "bias" in
         let: "y" := (rand #(S N)) ≤ "bias" in
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
         let: "x" := (rand("α") #(S N)) ≤ "bias" in
         let: "y" := (rand("β") #(S N)) ≤ "bias" in
         if: "x" = "y" then "f" #() else "x"
      ).

  Definition von_neumann_con_prog: val :=
    λ: "ad",
      let: "l" := ref #0 in
      Fork ("ad" "l") ;;
      (rec: "f" "_" :=
         let: "bias" := min_prog (! "l") #N in
         let, ("x", "y") := (((rand #(S N))≤ "bias") ||| ((rand #(S N))≤ "bias")) in
         if: "x" = "y" then "f" #() else "x"
      ).
  
  Definition von_neumann_con_prog': val :=
    λ: "ad",
      let: "l" := ref #0 in
      Fork ("ad" "l") ;;
      (rec: "f" "_" :=
         let: "bias" := min_prog (! "l") #N in
         let: "α" := alloc #(S N)in
         let: "β" := alloc #(S N) in
         let, ("x", "y") := (((rand("α") #(S N))≤ "bias") ||| ((rand("β") #(S N))≤ "bias")) in
         if: "x" = "y" then "f" #() else "x"
      ).

  Definition rand_prog: val :=
    λ: "_" "_", flip.
  
  Definition rand_prog': val :=
    λ: "_" "_", let: "x" := alloc #1 in flipL "x" .
  
  Section proof.
    Context `{!foxtrotRGS Σ}.

    
    Lemma wp_von_neumann_prog_von_neumann_prog' K j:
     j ⤇ fill K (Val von_neumann_prog') -∗
     WP (Val von_neumann_prog)
      {{ v, ∃ v' : val, j ⤇ fill K v' ∗ ((ref lrel_nat → ()) → () → lrel_bool)%lrel v v' }}.
    Proof.
      iIntros "Hspec".
      rewrite /von_neumann_prog'.
      rewrite /von_neumann_prog.
      wp_pures.
      iModIntro.
      iFrame.
      iModIntro.
      iIntros (??) "#Hinv".
      unfold_rel.
      clear.
      iIntros (K j) "Hspec".
      wp_pures. tp_pures j.
      wp_alloc l as "Hl".
      tp_alloc j as l' "Hl'".
      wp_pures. tp_pures j.
      iMod (inv_alloc _ _ ((∃ v0 v3 : val, l ↦ v0 ∗ l' ↦ₛ v3 ∗ lrel_nat v0 v3))%I with "[Hl Hl']") as "#Hinv'".
      { iFrame. iNext. iExists 0; iPureIntro; split; f_equal. }
      tp_bind j (Fork _).
      iMod (pupd_fork with "[$]") as "[Hspec [%j' Hspec']]".
      wp_apply (wp_fork with "[Hspec']").
      { iNext.
        iApply (wp_wand with "[Hspec']"); first (iApply ("Hinv" with "[][Hspec']")).
        - iExists _, _. by repeat iSplit. 
        - by erewrite fill_empty.
        - by iIntros.
      }
      simpl.
      tp_pures j.
      wp_pures.
      iFrame.
      iModIntro.
      iModIntro. 
      iIntros (??) "[-> ->]".
      unfold_rel.
      clear.
      iIntros (K j) "Hspec".
      iLöb as "IH".
      wp_pures.
      tp_pures j.
      wp_bind (! _)%E.
      iInv "Hinv'" as ">(%&%&?&?&[%[-> ->]])" "Hclose".
      tp_load j.
      wp_load.
      iMod ("Hclose" with "[-Hspec]").
      { iFrame. by iExists _. }
      iModIntro.
      wp_apply (wp_min_prog); first done.
      tp_bind j (min_prog _ _)%E.
      iMod (spec_min_prog with "[$]") as "Hspec".
      iIntros (? ->).
      simpl.
      wp_pures.
      tp_pures j.
      tp_allocnattape j α as "Hα".
      tp_pures j.
      tp_allocnattape j β as "Hβ".
      tp_pures j.
      tp_bind j (rand(_) _)%E.
      wp_apply (wp_couple_rand_rand_lbl with "[$Hα $Hspec]"); first naive_solver.
      iIntros (?) "(?&Hspec&%)".
      simpl.
      wp_pures. tp_pures j.
      tp_bind j (rand(_) _)%E.
      wp_apply (wp_couple_rand_rand_lbl with "[$Hβ $Hspec]"); first naive_solver.
      iIntros (?) "(?&Hspec&%)".
      simpl.
      tp_pures j; first solve_vals_compare_safe.
      wp_pures.
      case_bool_decide.
      - tp_pure j. wp_pure. by iApply "IH".
      - tp_pures j. wp_pure. iFrame.
        by iExists _.
    Qed. 
    
    Lemma wp_von_neumann_prog'_rand_prog K j:
     j ⤇ fill K (Val rand_prog) -∗
     WP (Val von_neumann_prog')
      {{ v, ∃ v' : val, j ⤇ fill K v' ∗ ((ref lrel_nat → ()) → () → lrel_bool)%lrel v v' }}.
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
    Context `{!foxtrotRGS Σ, Hspawn: !spawnG Σ}.

    Lemma wp_rand_prog_rand_prog' K j:
     j ⤇ fill K (Val rand_prog') -∗
     WP (Val rand_prog)
      {{ v, ∃ v' : val, j ⤇ fill K v' ∗ ((ref lrel_nat → ()) → () → lrel_bool)%lrel v v' }}.
    Proof.
      iIntros "Hspec".
      rewrite /rand_prog'.
      rewrite /rand_prog.
      wp_pures.
      iModIntro.
      iFrame.
      iModIntro.
      iIntros (??) "#Hinv".
      unfold_rel.
      clear.
      iIntros (K j) "Hspec".
      tp_pures j.
      wp_pures. 
      iFrame.
      iModIntro.
      iModIntro. 
      iIntros (??) "[-> ->]".
      unfold_rel.
      clear.
      iIntros (K j) "Hspec".
      wp_pures.
      tp_pures j.
      tp_allocnattape j α as "Hα".
      tp_pures j.
      rewrite /flipL.
      tp_pures j.
      tp_bind j (rand(_) _)%E.
      wp_pures.
      wp_apply (wp_couple_rand_rand_lbl with "[$Hα $Hspec]"); first naive_solver.
      iIntros (?) "(?&Hspec&%)".
      simpl.
      iMod (spec_int_to_bool with "[$]").
      wp_apply (wp_int_to_bool); first done.
      iIntros. iFrame.
      by iExists _.
    Qed.


    
    Local Opaque INR.

    
    Lemma wp_rand_prog'_von_neumann_con_prog K j:
      j ⤇ fill K (Val von_neumann_con_prog) -∗
      WP (Val rand_prog')
      {{ v, ∃ v' : val, j ⤇ fill K v' ∗ ((ref lrel_nat → ()) → () → lrel_bool)%lrel v v' }}.
    Proof.
    Admitted. 

    Lemma wp_von_neumann_con_prog_von_neumann_con_prog' K j:
      j ⤇ fill K (Val von_neumann_con_prog') -∗
      WP (Val von_neumann_con_prog)
        {{ v, ∃ v' : val, j ⤇ fill K v' ∗ ((ref lrel_nat → ()) → () → lrel_bool)%lrel v v' }}.
    Proof.
    Admitted. 
    
    Lemma wp_von_neumann_con_prog'_von_neumann_prog K j:
      j ⤇ fill K (Val von_neumann_prog) -∗
      WP (Val von_neumann_con_prog')
        {{ v, ∃ v' : val, j ⤇ fill K v' ∗ ((ref lrel_nat → ()) → () → lrel_bool)%lrel v v' }}.
    Proof.
      iIntros "Hspec".
      rewrite /von_neumann_con_prog'.
      rewrite /von_neumann_prog.
      wp_pures.
      iModIntro.
      iFrame.
      iModIntro.
      iIntros (??) "#Hinv".
      unfold_rel.
      clear -Hspawn.
      iIntros (K j) "Hspec".
      wp_pures. tp_pures j.
      wp_alloc l as "Hl".
      tp_alloc j as l' "Hl'".
      wp_pures. tp_pures j.
      iMod (inv_alloc _ _ ((∃ v0 v3 : val, l ↦ v0 ∗ l' ↦ₛ v3 ∗ lrel_nat v0 v3))%I with "[Hl Hl']") as "#Hinv'".
      { iFrame. iNext. iExists 0; iPureIntro; split; f_equal. }
      tp_bind j (Fork _).
      iMod (pupd_fork with "[$]") as "[Hspec [%j' Hspec']]".
      wp_apply (wp_fork with "[Hspec']").
      { iNext.
        iApply (wp_wand with "[Hspec']"); first (iApply ("Hinv" with "[][Hspec']")).
        - iExists _, _. by repeat iSplit. 
        - by erewrite fill_empty.
        - by iIntros.
      }
      simpl.
      tp_pures j.
      wp_pures.
      iFrame.
      iModIntro.
      iModIntro. 
      iIntros (??) "[-> ->]".
      unfold_rel.
      clear -Hspawn.
      iIntros (K j) "Hspec".
      iLöb as "IH".
      wp_pures.
      tp_pures j.
      wp_bind (! _)%E.
      iInv "Hinv'" as ">(%&%&?&?&[%[-> ->]])" "Hclose".
      tp_load j.
      wp_load.
      iMod ("Hclose" with "[-Hspec]").
      { iFrame. by iExists _. }
      iModIntro.
      wp_apply (wp_min_prog); first done.
      tp_bind j (min_prog _ _)%E.
      iMod (spec_min_prog with "[$]") as "Hspec".
      iIntros (? ->).
      simpl.
      wp_pures.
      tp_pures j.
      wp_alloctape α as "Hα".
      wp_pures.
      wp_alloctape β as "Hβ".
      wp_pures.
      tp_bind j (rand _)%E.
      iMod (pupd_couple_tape_rand with "[$Hα][$]") as "(%x&Hα&Hspec&%)"; first naive_solver.
      simpl.
      tp_pures j.
      tp_bind j (rand _)%E.
      iMod (pupd_couple_tape_rand with "[$Hβ][$]") as "(%y&Hβ&Hspec&%)"; first naive_solver.
      simpl.
      tp_pures j; first solve_vals_compare_safe.
      wp_apply (wp_par (λ v, ⌜v=#(bool_decide (x ≤ n `min` N))⌝)%I (λ v, ⌜v=#(bool_decide (y ≤ n `min` N))⌝)%I with "[Hα][Hβ]"); [wp_randtape; by wp_pures..|].
      iIntros (??)"[->->]".
      iNext.
      wp_pures.
      case_bool_decide.
      - tp_pure j. wp_pure. by iApply "IH".
      - tp_pures j. wp_pure. iFrame.
        by iExists _.
    Qed.
    
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
    eapply ctx_refines_transitive with rand_prog'; last eapply ctx_refines_transitive with von_neumann_con_prog; last eapply ctx_refines_transitive with von_neumann_con_prog';
      apply (refines_sound (#[spawnΣ; foxtrotRΣ])); iIntros; unfold_rel; iIntros (K j) "spec"; simpl.
    - wp_apply (wp_rand_prog_rand_prog' with "[$]"); by iIntros.
    - wp_apply (wp_rand_prog'_von_neumann_con_prog with "[$]"); by iIntros.
    - wp_apply (wp_von_neumann_con_prog_von_neumann_con_prog' with "[$]"); by iIntros.
    - wp_apply (wp_von_neumann_con_prog'_von_neumann_prog with "[$]"); by iIntros.
  Qed.
  
  Lemma von_neumann_prog_eq_rand_prog :
    ∅ ⊨ von_neumann_prog =ctx= rand_prog : ((TRef TNat → TUnit) → TUnit →TBool).
  Proof.
    split; [apply von_neumann_prog_refines_rand_prog|apply rand_prog_refines_von_neumann_prog].
  Qed. 

End von_neumann. 


 

