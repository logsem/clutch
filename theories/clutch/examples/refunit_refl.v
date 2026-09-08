From clutch Require Export clutch.
Set Default Proof Using "Type*".

Section fresh_refl.
  Context `{!clutchRGS Σ}.

  Definition fresh_name : expr := 
    ref #().

  Lemma fresh_name_log_reflexivity :
    ⊢ REL fresh_name << fresh_name : lrel_ref lrel_unit.
  Proof.
    unfold fresh_name.
    rel_alloc_l xl as "Hx".
    rel_alloc_r yl as "Hy".
    rel_values.
    rewrite /lrel_ref /lrel_unit.
    unfold lrel_car.
    iExists xl, yl. repeat (iSplitR; auto).
    iApply inv_alloc.
    iNext.
    iExists #(), #().
    by iFrame.
  Qed.
End fresh_refl.

Lemma fresh_name_ctx_ref :
  ∅ ⊨ fresh_name ≤ctx≤ fresh_name : TRef TUnit.
Proof.
  unfold fresh_name.
  apply ctx_refines_reflexive.
Qed.

Lemma fresh_name_ctx_eq :
  ∅ ⊨ fresh_name =ctx= fresh_name : TRef TUnit.
Proof.
  unfold ctx_equiv.
  auto using fresh_name_ctx_ref.
Qed.

Lemma fresh_name_ctx_ref_alt :
  ∅ ⊨ fresh_name ≤ctx≤ fresh_name : TRef TUnit.
Proof.
  eapply (refines_sound clutchRΣ). intros.
  (* TODO: only simpl works here... *)
  simpl. 
  apply: fresh_name_log_reflexivity.
Qed.
