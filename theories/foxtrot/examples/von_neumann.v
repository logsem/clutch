(** von Neumann Trick *)
From clutch.foxtrot Require Import foxtrot lib.conversion lib.min lib.par lib.spawn.

Set Default Proof Using "Type*".

Definition flipL : val := λ: "e", int_to_bool (rand("e") #1%nat).
Definition flip : expr := (flipL #()).

Section von_neumann.
  Variable (N : nat).
  Variable (ad : val).
  Definition Htyped:= ∅ ⊢ₜ ad : (TRef TNat → TUnit).

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
    λ:"_" "_", flip.
  
  Definition rand_prog': val :=
    λ: "_" "_", let: "x" := alloc #1 in flipL "x" .
  
  Section proof.
    Context `{!foxtrotRGS Σ}.
    
    Lemma wp_von_neumann_prog_von_neumann_prog' K j :
      Htyped->
     j ⤇ fill K (von_neumann_prog' ad) -∗
     WP (von_neumann_prog ad)
      {{ v, ∃ v' : val, j ⤇ fill K v' ∗ ( () → lrel_bool)%lrel v v' }}.
    Proof.
      iIntros (Ht) "Hspec".
      rewrite /von_neumann_prog'.
      rewrite /von_neumann_prog.
      iPoseProof (binary_fundamental.refines_typed _ [] _ Ht) as "H".
      unfold_rel.
      wp_pures. tp_pures j.
      wp_alloc l as "Hl".
      wp_pures.
      tp_alloc j as l' "Hl'".
      tp_pures j.
      iMod (inv_alloc _ _ ((∃ v0 v3 : val, l ↦ v0 ∗ l' ↦ₛ v3 ∗ lrel_nat v0 v3))%I with "[Hl Hl']") as "#Hinv'"; first (iFrame; by iExists 0).
      tp_bind j (Fork _).
      iMod (pupd_fork with "[$]") as "[Hspec [%j' Hspec']]".
      wp_apply (wp_fork with "[Hspec']").
      { iNext.
        wp_bind (Val ad).
        tp_bind j' (Val ad).
        iApply (wp_wand with "[Hspec']").
        - by iApply "H".
        - simpl.
          iIntros (?) "(%&Hspec&#Hrel)".
          unfold_rel.
          rewrite -(fill_empty (App _ #l'))%E.
          iApply (wp_wand with "[-]").
          + iApply "Hrel"; last done. iExists _, _. by repeat iSplit.
          +  by iIntros.
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
      Htyped->
     j ⤇ fill K (Val rand_prog ad) -∗
     WP (Val von_neumann_prog' ad)
      {{ v, ∃ v' : val, j ⤇ fill K v' ∗ (() → lrel_bool)%lrel v v' }}.
    Proof.
      iIntros (Ht) "Hspec".
      rewrite /von_neumann_prog'.
      rewrite /rand_prog.
      wp_pures. tp_pures j.
      wp_alloc l as "Hl".
      wp_pures.
      iMod (inv_alloc _ _ _ with "[Hl]") as "#Hinv"; first shelve.
      wp_apply (wp_fork).
      { iPoseProof (typed_safe _ [] _ Ht) as "H'".
        wp_bind (Val ad).
        iApply (wp_wand); first done.
        simpl.
        iIntros (?) "#H".
        rewrite unary_model.refines_eq.
        rewrite /unary_model.refines_def.
        iApply wp_wand.
        - iApply "H". iExists _; by repeat iSplit.
        - by iIntros. }
      Unshelve.
      2:{ iFrame. by iExists 0. }
      wp_pures.
      iFrame.
      iModIntro.
      iModIntro.
      iIntros (??) "[->->]".
      unfold_rel.
      clear.
      iIntros (K j) "Hspec".
      tp_pures j.
      rewrite /flipL.
      tp_pures j.
      iLöb as "IH".
      wp_pures.
      wp_bind (! _)%E.
      iInv "Hinv" as ">(%&Hl&[% ->])" "Hclose".
      wp_load.
      iMod ("Hclose" with "[$Hl]") as "_"; first by iExists _.
      iModIntro.
      wp_apply wp_min_prog; first done.
      iIntros (?) "->".
      wp_pures.
      wp_alloctape α as "Hα".
      wp_pures.
      wp_alloctape β as "Hβ".
      wp_pures.
    Admitted. 
      
  End proof.
  
  Section proof'.
    Context `{!foxtrotRGS Σ, Hspawn: !spawnG Σ}.

    Lemma wp_rand_prog_rand_prog' K j:
      Htyped->
     j ⤇ fill K (Val rand_prog' ad) -∗
     WP (Val rand_prog ad)
      {{ v, ∃ v' : val, j ⤇ fill K v' ∗ (() → lrel_bool)%lrel v v' }}.
    Proof.
      iIntros (Ht) "Hspec".
      rewrite /rand_prog'.
      rewrite /rand_prog.
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
      Htyped->
      j ⤇ fill K (Val von_neumann_con_prog ad) -∗
      WP (Val rand_prog' ad)
      {{ v, ∃ v' : val, j ⤇ fill K v' ∗ (() → lrel_bool)%lrel v v' }}.
    Proof.
      iIntros (Ht) "Hspec".
      rewrite /rand_prog'.
      rewrite /von_neumann_con_prog.
      tp_pures j.
      tp_alloc j as l "Hl".
      tp_pures j.
      tp_bind j (Fork _).
      iMod (pupd_fork with "[$]") as "[Hspec _]".
      simpl.
      tp_pures j.
      iMod (inv_alloc _ _ (l↦ₛ#0)%I with "[$]") as "#Hinv'".
      wp_pures.
      iFrame.
      iModIntro.
      iModIntro.
      iIntros (??) "[-> ->]".
      unfold_rel.
      clear K j.
      iIntros (K j) "Hspec".
      wp_pures.
      wp_alloctape α as "Hα".
      wp_pures.
      rewrite /flipL.
      wp_pures.
      iMod (pupd_epsilon_err) as "(%&%&Herr)".
      iRevert "Hspec Hα".
      iApply (ec_ind_simpl _ _ with "[][$]"); first done.
      { admit. }
      iModIntro.
      iIntros "[Hind Herr] Hspec Hα".
      tp_pures j.
      iApply pupd_wp.
      iInv "Hinv'" as ">?" "Hclose".
      tp_load j.
      iMod ("Hclose" with "[$]") as "_".
      iModIntro.
      tp_bind j (min_prog _ _)%E.
      iMod (spec_min_prog with "[$]") as "Hspec".
      simpl.
      rewrite Z.min_l; last lia.
      do 2 tp_pure j.
      tp_bind j (_|||_)%E.
      iMod (tp_par with "[$]") as "(%j1&%j2&%K1&%K2&Hspec1&Hspec2&Hcont)".
      tp_bind j1 (rand _)%E.
      tp_bind j2 (rand _)%E.
      (* error amplification *)
    Admitted.
      
    Lemma wp_von_neumann_con_prog_von_neumann_con_prog' K j:
      Htyped ->
      j ⤇ fill K (Val von_neumann_con_prog' ad) -∗
      WP (Val von_neumann_con_prog ad)
        {{ v, ∃ v' : val, j ⤇ fill K v' ∗ (() → lrel_bool)%lrel v v' }}.
    Proof.
      iIntros (Ht) "Hspec".
      rewrite /von_neumann_con_prog'.
      rewrite /von_neumann_con_prog.
      iPoseProof (binary_fundamental.refines_typed _ [] _ Ht) as "H".
      unfold_rel.
      wp_pures.
      tp_pures j.
      wp_alloc l as "Hl".
      tp_alloc j as l' "Hl'".
      wp_pures. tp_pures j.
      iMod (inv_alloc _ _ ((∃ v0 v3 : val, l ↦ v0 ∗ l' ↦ₛ v3 ∗ lrel_nat v0 v3))%I with "[Hl Hl']") as "#Hinv'".
      { iFrame. iNext. iExists 0; iPureIntro; split; f_equal. }
      tp_bind j (Fork _).
      iMod (pupd_fork with "[$]") as "[Hspec [%j' Hspec']]".
      wp_apply (wp_fork with "[Hspec']").
      { iNext.
        wp_bind (Val ad).
        tp_bind j' (Val ad).
        iApply (wp_wand with "[Hspec']").
        - by iApply "H".
        - simpl.
          iIntros (?) "(%&Hspec&#Hrel)".
          unfold_rel.
          rewrite -(fill_empty (App _ #l'))%E.
          iApply (wp_wand with "[-]").
          + iApply "Hrel"; last done. iExists _, _. by repeat iSplit.
          +  by iIntros. 
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
      tp_allocnattape j α as "Hα".
      tp_pures j.
      tp_allocnattape j β as "Hβ".
      do 2 tp_pure j.
      tp_bind j (_|||_)%E.
      iMod (tp_par with "[$]") as "(%j1&%j2&%K1&%K2&Hspec1&Hspec2&Hcont)".
      wp_apply (wp_par (λ v, ∃ (b:bool), ⌜v=#b⌝ ∗ j1 ⤇ fill K1 v)%I (λ v, ∃ (b:bool), ⌜v=#b⌝ ∗ j2 ⤇ fill K2 v)%I with "[Hα Hspec1][Hβ Hspec2]").
      - tp_bind j1 (rand(_) _)%E.
        wp_apply (wp_couple_rand_rand_lbl with "[$Hα $Hspec1]"); first naive_solver.
        iIntros (?) "(?&Hspec1&%)".
        simpl.
        tp_pures j1.
        wp_pures.
        iFrame.
        by iExists _.
      - tp_bind j2 (rand(_) _)%E.
        wp_apply (wp_couple_rand_rand_lbl with "[$Hβ $Hspec2]"); first naive_solver.
        iIntros (?) "(?&Hspec2&%)".
        simpl.
        tp_pures j2.
        wp_pures.
        iFrame.
        by iExists _.
      - iIntros (??) "[(%&->&Hspec1) (%&->&Hspec2)]".
        iNext.
        iMod ("Hcont" with "[$]").
        simpl.
        tp_pures j; first solve_vals_compare_safe.
        wp_pures.
        case_bool_decide.
        + tp_pure j. wp_pure. by iApply "IH".
        + tp_pures j. wp_pure. iFrame.
          by iExists _.
    Qed.
    
    Lemma wp_von_neumann_con_prog'_von_neumann_prog K j:
      Htyped ->
      j ⤇ fill K (Val von_neumann_prog ad) -∗
      WP (Val von_neumann_con_prog' ad)
        {{ v, ∃ v' : val, j ⤇ fill K v' ∗ (() → lrel_bool)%lrel v v' }}.
    Proof.
      iIntros (Ht) "Hspec".
      rewrite /von_neumann_con_prog'.
      rewrite /von_neumann_prog.
      iPoseProof (binary_fundamental.refines_typed _ [] _ Ht) as "H".
      unfold_rel.
      wp_pures.
      tp_pures j.
      wp_alloc l as "Hl".
      tp_alloc j as l' "Hl'".
      wp_pures. tp_pures j.
      iMod (inv_alloc _ _ ((∃ v0 v3 : val, l ↦ v0 ∗ l' ↦ₛ v3 ∗ lrel_nat v0 v3))%I with "[Hl Hl']") as "#Hinv'".
      { iFrame. iNext. iExists 0; iPureIntro; split; f_equal. }
      tp_bind j (Fork _).
      iMod (pupd_fork with "[$]") as "[Hspec [%j' Hspec']]".
      wp_apply (wp_fork with "[Hspec']").
      { iNext.
        wp_bind (Val ad).
        tp_bind j' (Val ad).
        iApply (wp_wand with "[Hspec']").
        - by iApply "H".
        - simpl.
          iIntros (?) "(%&Hspec&#Hrel)".
          unfold_rel.
          rewrite -(fill_empty (App _ #l'))%E.
          iApply (wp_wand with "[-]").
          + iApply "Hrel"; last done. iExists _, _. by repeat iSplit.
          +  by iIntros. 
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
    Htyped ->
    ∅ ⊨ von_neumann_prog ad ≤ctx≤ rand_prog ad : (TUnit →TBool).
  Proof.
    intros Ht.
    eapply ctx_refines_transitive with (von_neumann_prog' ad);
    apply (refines_sound (#[foxtrotRΣ])); rewrite /interp/=;
    iIntros; unfold_rel;
      iIntros (K j) "Hspec".
    - by wp_apply (wp_von_neumann_prog_von_neumann_prog' with "[$]").
    - (** this one needs stronger logical relations! *)
      by wp_apply (wp_von_neumann_prog'_rand_prog with "[$]").
  Qed.

  Lemma rand_prog_refines_von_neumann_prog :
    Htyped ->
    ∅ ⊨ rand_prog ad ≤ctx≤ von_neumann_prog ad : (TUnit →TBool).
  Proof.
    intros Ht.
    eapply ctx_refines_transitive with (rand_prog' ad); last eapply ctx_refines_transitive with (von_neumann_con_prog ad); last eapply ctx_refines_transitive with (von_neumann_con_prog' ad);
      apply (refines_sound (#[spawnΣ; foxtrotRΣ])); iIntros; unfold_rel; iIntros (K j) "spec"; simpl.
    - by wp_apply (wp_rand_prog_rand_prog' with "[$]").
    - by wp_apply (wp_rand_prog'_von_neumann_con_prog with "[$]").
    - by wp_apply (wp_von_neumann_con_prog_von_neumann_con_prog' with "[$]").
    - by wp_apply (wp_von_neumann_con_prog'_von_neumann_prog with "[$]").
  Qed.
  
  Lemma von_neumann_prog_eq_rand_prog :
    Htyped ->
    ∅ ⊨ von_neumann_prog ad =ctx= rand_prog ad : (TUnit →TBool).
  Proof.
    intros.
    split; by [apply von_neumann_prog_refines_rand_prog|apply rand_prog_refines_von_neumann_prog].
  Qed.

End von_neumann.


 

