From clutch Require Export clutch lib.flip.
Set Default Proof Using "Type*".

Section proofs.
  Context `{!clutchRGS Σ}.

  Definition idrecN := nroot.@"idrec".

  (* Warmup: λx.x refines the function that recurses once before returning its
     argument. Nothing probabilistic, just recursion and state. *)
  Lemma id_rec_det : ⊢ REL
                   (λ: "x", "x")
                   <<
                   (let: "c" := ref #0 in
                    (rec: "f" "x" := if: !"c" = #1 then "x" else "c" <- #1 ;; "f" "x"))
      : (lrel_bool → lrel_bool).
  Proof with try rel_pures_l ; try rel_pures_r.
    rel_alloc_r c as "c"...
    set (P := (REL (λ: "x", "x")%V
                 <<
                 (rec: "f" "x" := if: ! #c = #1 then "x" else #c <- #1;; "f" "x")%V :
                lrel_bool → lrel_bool)).
    iApply (refines_na_alloc (c ↦ₛ #0 ∨ ((c ↦ₛ #1) ∗ P)) idrecN).
    iSplitL ; iFrame.
    iIntros "#Hinv".
    iApply refines_arrow_val.
    iIntros "!#" (??) "#(%b&->&->)".
    iRevert (b).
    iLöb as "HH".
    iIntros (b).
    rel_rec_r.
    iApply (refines_na_inv with "[$Hinv]") ; [done|].
    iIntros "[HHH Hclose]".
    rel_pure_l.
    iDestruct "HHH" as "[c0 | c1]".
    - (* First call: Set the counter and unfold the rec. def. once more. *)
      rel_load_r. subst. rel_pures_r. rel_store_r. do 2 rel_pure_r.
      rel_pures_r. rel_load_r...
      iApply (refines_na_close with "[- $Hclose]") ; iSplitL.
      {
        iNext. iRight. iSplitL ; iFrame.
        unfold P.
        iApply refines_arrow_val.
        iIntros "!#" (??) "#(%b'&->&->)".
        iApply "HH".
      }
      rel_values.
    - (* Not first call: Actually act like the identity. *)
      subst...
      iDestruct "c1" as "(c1 & p)".
      rel_load_r...
      iApply (refines_na_close with "[- $Hclose]") ;
        iSplitL. { iRight. iFrame. }
      rel_values.
  Qed.

  Lemma rec_id :
    ⊢ REL
      let: "α" := allocB in
       (rec: "f" "x" := if: flipL "α" then "x" else "f" "x")
    <<
       (λ: "x", "x")
    : (lrel_bool → lrel_bool).
  Proof with try rel_pures_l ; try rel_pures_r.
    rel_alloctape_l α as "α"...
    iApply (refines_na_alloc (α ↪B []) idrecN) ; iFrame.
    iIntros "#Hinv".
    iApply refines_arrow_val.
    iIntros "!#" (??) "#(%b&->&->)".
    iLöb as "HH".
    rel_rec_l.
    iApply (refines_na_inv with "[$Hinv]") ; [done|].
    iIntros "[> α Hclose]".
    rel_apply_l refines_flipL_empty_l ; iFrame.
    iIntros ([]) "α".
    1: iApply (refines_na_close with "[- $Hclose]") ; iFrame... 1: rel_values.
    rel_pure_l.
    iApply (refines_na_close with "[- $Hclose]") ; iFrame.
    iApply "HH".
  Qed.

  Lemma id_rec :
    ⊢ REL
       (λ: "x", "x")
    <<
      (let: "c" := ref #0 in
       (rec: "f" "x" := if: !"c" = #1 then "x" else "c" <- #1 ;; "f" "x"))
    : (lrel_bool → lrel_bool).
  Proof with try rel_pures_l ; try rel_pures_r.
    rel_alloc_r c as "c"...
    iApply (refines_na_alloc (∃ n, c ↦ₛ #n ∗ ⌜(n = 0 ∨ n = 1)⌝) idrecN).
    iSplitL ; [iExists _ ; iFrame ; eauto|].
    iIntros "#Hinv".
    iApply refines_arrow_val.
    iIntros "!#" (??) "#(%b&->&->)".
    iLöb as "HH".
    rel_rec_r.
    iApply (refines_na_inv with "[$Hinv]") ; [done|].
    iIntros "[>[%b' [c %hb']] Hclose]".
    rel_load_r.
    destruct hb'.
    - subst. rel_pures_r. rel_store_r. do 2 rel_pure_r.
      iApply (refines_na_close with "[- $Hclose]") ;
        iSplitL ; [iExists _ ; iFrame ; eauto|].
      rel_pure_l.
      (* Not clear how to proceed, so we *)
      give_up.
    - subst... iApply (refines_na_close with "[- $Hclose]") ;
        iSplitL ; [iExists _ ; iFrame ; eauto|].
      rel_values.
  Abort.

End proofs.
