From clutch Require Export clutch.
From iris.base_logic.lib Require Export gen_heap.
Set Default Proof Using "Type*".

(** Proof of Privacy Equation in clutch *)
(*  https://dl.acm.org/doi/10.1145/3434292 *)
(*  https://homepages.inf.ed.ac.uk/stark/obspho-mfcs.pdf *)

Section privacy_eq.
  Context `{!clutchRGS Σ}.

  Definition cmp_fresh : expr := 
    let: "n" := ref #() in
    λ: "x" (* ideally it would be typed ν, but now it's just `unit ref` *), "x" = "n".

  Definition cmp_fresh' : expr :=
    λ: "x", let: "n" := ref #() in "x" = "n".

  Definition f : expr :=
    λ: "x", #false.
  
  Lemma fresh'_cmp_f_rel : 
    ⊢ REL f << cmp_fresh' : ref lrel_unit → lrel_bool.
  Proof.
    unfold cmp_fresh', f.
    rel_pure_l. rel_pure_r.
    iApply refines_arrow_val.
    iIntros (??) "!> #(%l1 & %l2 & -> & -> & H)".
    rel_pure_l. rel_pure_r.
    rel_alloc_r yl as "Hy".
    do 2 rel_pure_r.
    rel_binop_r.
    case_bool_decide.
    - iApply fupd_refines.
      iInv "H" as (??) ">(_ & h & _)".
      simplify_eq.
      by iDestruct (ghost_map_elem_ne with "Hy h") as "%Hneq".
    - rel_values.
  Qed.

  Lemma cmp_fresh'_f_rel : 
    ⊢ REL cmp_fresh' << f : ref lrel_unit → lrel_bool.
  Proof.
    unfold cmp_fresh', f.
    rel_pure_r.
    rel_pure_l.
    iApply refines_arrow_val.
    iIntros (??) "!> #(%l1 & %l2 & -> & -> & H)".
    rel_alloc_l xl as "Hx".
    do 2 rel_pure_l.
    rel_pure_r.
    rel_pure_l.
    case_bool_decide.
    - iApply fupd_refines.
      iInv "H" as (??) ">(h & _)".
      simplify_eq.
      by iDestruct (ghost_map_elem_ne with "Hx h") as "%Hneq".
    - rel_values.
  Qed.

  Definition freshN := nroot.@"fresh".

  Lemma cmp_fresh_f_rel : 
    ⊢ REL cmp_fresh << f : ref lrel_unit → lrel_bool.
  Proof.
    unfold cmp_fresh, f.
    rel_alloc_l n as "Hn".
    do 2 rel_pures_l.
    rel_pures_r.
    iMod (inv_alloc freshN _ (n ↦ #())%I with "[Hn]") as "#Hinv"; first done.
    iApply refines_arrow_val.
    (* The □ here let's us no longer having access to `n ↦ₛ #()`, 
       so we need to allocate invariant before *)
    iIntros (??) "!> #(%l1 & %l2 & -> & -> & H)".
    rel_pures_l.
    rel_pures_r.
    case_bool_decide.
    - iApply fupd_refines.
      iInv "H" as (??) ">(h & _)".
      iInv "Hinv" as ">Hn".
      simplify_eq.
      by iDestruct (ghost_map_elem_ne with "Hn h") as "%Hneq".
    - rel_values.
  Qed.

  Lemma f_cmp_fresh_rel : 
    ⊢ REL f << cmp_fresh : ref lrel_unit → lrel_bool.
  Proof.
    unfold cmp_fresh, f.
    rel_alloc_r n as "Hn".
    do 2 rel_pures_r.
    rel_pures_l.
    set (P := (n ↦ₛ #())%I).
    iMod (inv_alloc freshN _ P with "[Hn]") as "#Hinv"; first done.
    iApply refines_arrow_val.
    iIntros (??) "!> #(%l1 & %l2 & -> & -> & H)".
    rel_pures_l.
    rel_pures_r.
    case_bool_decide.
    - iApply fupd_refines.
      iInv "H" as (??) ">(_ & h & _)".
      unfold P.
      iInv "Hinv" as ">Hn".
      simplify_eq.
      by iDestruct (ghost_map_elem_ne with "Hn h") as "%Hneq".
    - rel_values.
  Qed.

End privacy_eq.

Theorem cmp_fresh'_f_refinement :
  ∅ ⊨ cmp_fresh' ≤ctx≤ f : ref TUnit → TBool.
Proof.
  eapply (refines_sound clutchRΣ). intros.
  simpl.
  apply cmp_fresh'_f_rel.
Qed.

Theorem f_cmp_fresh'_refinement :
  ∅ ⊨ f ≤ctx≤ cmp_fresh' : ref TUnit → TBool.
Proof.
  eapply (refines_sound clutchRΣ). intros.
  simpl.
  apply fresh'_cmp_f_rel.
Qed.

Theorem cmp_fresh'_f_equivalence :
  ∅ ⊨ cmp_fresh' =ctx= f : ref TUnit → TBool.
Proof.
  unfold ctx_equiv.
  split.
  - apply cmp_fresh'_f_refinement.
  - apply f_cmp_fresh'_refinement.
Qed.

Theorem cmp_fresh_f_refinement :
  ∅ ⊨ cmp_fresh ≤ctx≤ f : ref TUnit → TBool.
Proof.
  eapply (refines_sound clutchRΣ). intros.
  simpl.
  apply cmp_fresh_f_rel.
Qed.

Theorem f_cmp_fresh_refinement :
  ∅ ⊨ f ≤ctx≤ cmp_fresh : ref TUnit → TBool.
Proof.
  eapply (refines_sound clutchRΣ). intros.
  simpl.
  apply f_cmp_fresh_rel.
Qed.

Theorem cmp_fresh_f_equivalence :
  ∅ ⊨ cmp_fresh =ctx= f : ref TUnit → TBool.
Proof.
  unfold ctx_equiv.
  split.
  - apply cmp_fresh_f_refinement.
  - apply f_cmp_fresh_refinement.
Qed.
