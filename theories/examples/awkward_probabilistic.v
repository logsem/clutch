(*
An example in Sec. 6 of https://cs.au.dk/~birke/papers/step-probability-conf.pdf

Maybe this is another example, relying on local state encapsulation
  tau = (1 - > 1) -> 1
  e1 = let x = ref (flip ()) in \f. f(); !x
  e2 = \f. f(); flip()
show e1 related to e2 at tau.

Or how about a variant of the above, but where e1 is let x = ref (flip ()) in \f. (x := negate (!x); f(); !x). ?

NB: e1 and e2 are equivalent only if executed only once. We prove the
equivalence by adding a guard that returns `NONE` after the first invocation.
*)

From clutch Require Export clutch lib.flip. 
From clutch.examples Require Export one_time_pad.

Set Default Proof Using "Type*".

Section proofs.
  Context `{!clutchRGS Σ}.

  Definition awkwardN := nroot.@"awkward".

  Lemma refinement_prob :
    ⊢ REL
      (let: "α" := allocB in
       let: "callable" := ref #true in
       (λ: "f", if: ! "callable" then "callable" <- #false ;; "f" #() ;; SOME (flipL "α") else NONE))
    <<
      (let: "x" := ref flip in
       let: "callable" := ref #true in
       (λ: "f", if: ! "callable" then "callable" <- #false ;; "f" #() ;; SOME (!"x") else NONE))
    : (() → ()) → lrel_sum lrel_unit lrel_bool.
  Proof with try rel_pures_l ; try rel_pures_r.
    rel_allocBtape_l α as "α".
    rel_apply_r (refines_couple_tape_flip with "[$α]"); [done|].
    iIntros (b) "Hα /="...
    rel_alloc_r x as "Hx"...
    rel_alloc_l cl as "Hcl"...
    rel_alloc_r cr as "Hcr"...
    set (P := ((x ↦ₛ #b ∗ α ↪B [b] ∗ cl ↦ #true ∗ cr ↦ₛ #true ∨ cl ↦ #false ∗ cr ↦ₛ #false))%I).
    iApply (refines_na_alloc P awkwardN).
    iSplitL ; [ iFrame ; iLeft ; iFrame |].
    iIntros "#Hinv".
    iApply refines_arrow_val.
    iIntros "!#" (f1 f2) "#Hf"...
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "(>[(Hx & Hα & Hcl & Hcr) | (Hx & Hcr)] & Hclose)".
    - rel_load_l... rel_store_l...
      rel_load_r... rel_store_r...
      iApply (refines_na_close with "[-$Hclose]"). iSplitR "Hα Hx".
      { iModIntro. iFrame. iRight. iFrame. }
      iApply (refines_seq with "[Hf]") => // ; [by iApply "Hf"|].
      rel_load_r. rel_flipL_l...
      rel_values. iModIntro.
      unfold lrel_sum, lrel_car.
      do 2 iExists (#b). simpl. iRight. auto.
    - rel_load_l... rel_load_r...
      iApply (refines_na_close with "[-$Hclose]"). iSplitL.
      { iModIntro. iFrame. iRight; by iFrame. }
      rel_values.
      rewrite /lrel_sum/lrel_car/=.
      iModIntro. do 2 iExists _. iLeft. eauto.
  Qed.

  (* Simplified warm-up for the next series of examples. *)
  (* If the reference to `x` is local to the rhs closure, we never need to
     transfer its ownership into an invariant, and `f` cannot interfere with
     it, so we can couple with `x`. *)
  Lemma refinement_prob_resample_local_ref :
    ⊢ REL
      (λ: "f", let: "α" := allocB in
               "f" #() ;;
               flipL "α")
    <<
      (λ: "f", let: "β" := allocB in
               let: "b" := flipL "β" in
               let: "x" := ref "b" in
               "f" #() ;;
               !"x" )
    : (() → ()) → lrel_bool.
  Proof with try rel_pures_l ; try rel_pures_r.
    simpl...
    iApply refines_arrow_val.
    iIntros "!#" (f1 f2) "#Hf"...
    rel_allocBtape_l α as "α"...
    rel_allocBtape_r β as "β"...
    iApply refines_couple_bool_tape_tape ; auto ; iFrame ;
      iIntros (b) "(β & α)" => /=.
    rel_flipL_r...
    rel_alloc_r x as "Hx"...
    iApply (refines_seq with "[Hf]") => // ; [iApply "Hf" => //|].
    rel_flipL_l.
    rel_load_r.
    rel_values.
  Qed.

  (* The following is an example of a contextual equivalence we expect to hold
     but cannot currently prove conveniently using our relational logic. The
     issue is that we cannot determine, ahead of time, which flip to couple
     with in the rhs.

     One is tempted to argue that it should be sufficient to find a coupling
     the for any given call to the lhs and rhs closures, and couple `α` and `γ`
     by presampling a new bit `xor b b'` to `α` and `b'` to `γ`.

     But even though `x` is local to the rhs, we cannot argue the coupling of
     `α` and `γ` will be propagated past `f`. The reason is that `f` may be
     instantiated with the a function calling the rhs, which would sample a new
     bit to `γ` and modify `x`. Of course this shouldn't matter since for any
     value of `x`, there exists a coupling (via `xor !x`), but we cannot
     exploit this observation in the formal argument. *)

  Definition call_flip :=
    (λ: "f", let: "α" := allocB in
             "f" #() ;; flipL "α")%E.

  Definition store_xor :=
    (let: "x" := ref #false in
     (λ: "f", let: "β" := allocB in
              let: "b" := flipL "β" in
              let: "γ" := allocB in
              let: "b'" := flipL "γ" in
              "x" <- "b" ;;
              "f" #() ;;
              xor (! "x") "b'" ))%E.

  Definition store_xor_late :=
    (let: "x" := ref #false in
     (λ: "f", let: "β" := allocB in
              let: "b" := flipL "β" in
              let: "γ" := allocB in
              "x" <- "b" ;;
              "f" #() ;;
              let: "b'" := flipL "γ" in
              xor (! "x") "b'" ))%E.

  Definition store_ignore :=
    (let: "x" := ref #false in
     (λ: "f", let: "β" := allocB in
              let: "b" := flipL "β" in
              let: "γ" := allocB in
              "x" <- "b" ;;
              "f" #() ;;
              let: "b'" := flipL "γ" in
              "b'" ))%E.

  (* If we try to do the proof directly with our bare hands we get stuck. *)
  Lemma refinement_prob_resample :
    ⊢ REL call_flip << store_xor : (() → ()) → (lrel_bool).
  Proof with try rel_pures_l ; try rel_pures_r ; try foldxor.
    rewrite /call_flip /store_xor... rel_alloc_r x as "Hx"...
    iApply (refines_na_alloc (∃ b : bool, x ↦ₛ #b) awkwardN).
    iSplitL ; [ iExists _ ; iFrame |].
    iIntros "#Hinv".
    iApply refines_arrow_val.
    iIntros "!#" (f1 f2) "#Hf".
    rel_allocBtape_r β as "β"...
    rel_allocBtape_l α as "α"...
    iApply (refines_na_inv with "[-$Hinv]") ; [done|].
    iIntros "(>(%old_b & xb ) & Hclose)".
    rel_apply_r refines_flipL_empty_r => // ; iFrame. iIntros "%b β"...
    rel_allocBtape_r γ as "γ"...
    (* Now we lose. If we had prophecies, we could couple α and γ with the
    bijection (xor !x) at the time when the read from x occurs. Instead, we can
    try to couple with the current contents of x, i.e. b. But we can't hope
    that this will be preserved, so we'll get stuck later on. *)
    rel_apply_r (refines_couple_bool_tape_tape (xor_sem b) _ _ _ _ α γ ) => // ; iFrame.
    iIntros (b'') "(γ & α)" => /=.
    rewrite -{2}(cancel (xor_sem b) (xor_sem b) b''). set (b' := (xor_sem b b'')).
    rel_flipL_r... rel_store_r...
    iApply (refines_na_close with "[-$Hclose]") ; iSplitL "xb" ; [ by iExists _ |].
    iApply (refines_seq with "[Hf]") ; [by iApply "Hf"|].
    rel_flipL_l.
    iApply (refines_na_inv with "[-$Hinv]"); [done|].
    iIntros "(>(%not_necessarily_b & xb ) & Hclose)".
    unfold xor ; rel_load_r...
    iApply (refines_na_close with "[-$Hclose]") ; iSplitL "xb" ; [ by iExists _ |].
    unshelve rel_apply_r (refines_steps_r $! (xor_tp _ _ _ _)) ; [easy|iModIntro].
    (* We do not know this, in fact it may well be false (i.e. read this as `assert False`). *)
    assert (b = not_necessarily_b) as <- by admit.
    rewrite /b'. rewrite cancel.
    rel_values.
  Abort.

  (* Instead of directly trying to link the flip in call_flip with the one in
  store_xor via `(xor !x)`, we prove that the flip on `γ` can be delayed after
  the call to `f`. This will allow us to pick a coupling depending on the value
  of `x` *after* the call to `f` in the next refinement. *)
  Lemma store_xor_late_store_xor :
    ⊢ REL store_xor_late << store_xor : (() → ()) → (lrel_bool).
  Proof with try rel_pures_l ; try rel_pures_r ; try foldxor.
    rewrite /store_xor /store_xor_late...
    rel_alloc_l x as "x"... rel_alloc_r x' as "x'"...
    iApply (refines_na_alloc (∃ b b' : bool, x ↦ #b ∗ x' ↦ₛ #b' ∗ ⌜b = b'⌝) awkwardN).
    iSplitL ; [ iExists _,_ ; iFrame ; done |].
    iIntros "#Hinv".
    iApply refines_arrow_val.
    iIntros "!#" (f1 f2) "#Hf".
    rel_allocBtape_l α as "α"...
    rel_allocBtape_r β as "β"...
    iApply (refines_na_inv with "[-$Hinv]") ; [done|].
    iIntros "(>(%old_b & %old_b' & xb & xb' & <-) & Hclose)".
    iApply refines_couple_bool_tape_tape => // ; iFrame ; iIntros (b) "(β & α)" => /=.
    rel_flipL_l ; rel_flipL_r...
    rel_allocBtape_l γ as "γ"...
    rel_allocBtape_r γ' as "γ'"...
    rel_store_l...
    rel_apply (refines_couple_bool_tape_tape _ _ _ _ _ γ γ' ) => // ; iFrame ; iIntros (b') "(γ' & γ)" => /=.
    rel_flipL_r...
    rel_store_r...
    iApply (refines_na_close with "[-$Hclose]") ; iSplitL "xb xb'" ; [ iExists _, _ ; iFrame ; done |].
    iApply (refines_seq with "[Hf]") ; [by iApply "Hf"|].
    rel_flipL_l...
    iApply (refines_na_inv with "[-$Hinv]"); [done|].
    iIntros "(>(%not_necessarily_b & %not_necessarily_b' & xb & xb' & <-) & Hclose)".
    unfold xor ; rel_load_r ; rel_load_l...
    iApply (refines_na_close with "[-$Hclose]") ; iSplitL "xb xb'" ; [ iExists _, _ ; iFrame ; done |].
    unshelve rel_apply_r (refines_steps_r $! (xor_tp _ _ _ _)) ; [easy|iModIntro].
    rel_apply_l (refines_wp_l).
    wp_apply wp_mono.
    2: wp_apply xor_wp.
    iIntros (v) "->".
    rel_values.
  Qed.

  Lemma store_ignore_store_xor_late :
    ⊢ REL store_ignore << store_xor_late : (() → ()) → (lrel_bool).
  Proof with try rel_pures_l ; try rel_pures_r ; try foldxor.
    rewrite /store_xor_late /store_ignore...
    rel_alloc_l x as "x"... rel_alloc_r x' as "x'"...
    iApply (refines_na_alloc (∃ b b' : bool, x ↦ #b ∗ x' ↦ₛ #b' ∗ ⌜b = b'⌝) awkwardN).
    iSplitL ; [ iExists _,_ ; iFrame ; done |].
    iIntros "#Hinv".
    iApply refines_arrow_val.
    iIntros "!#" (f1 f2) "#Hf".
    rel_allocBtape_l α as "α"...
    rel_allocBtape_r β as "β"...
    iApply (refines_na_inv with "[-$Hinv]") ; [done|].
    iIntros "(>(%old_b & %old_b' & xb & xb' & <-) & Hclose)".
    iApply refines_couple_bool_tape_tape => // ; iFrame ; iIntros (b) "(β & α)" => /=.
    rel_flipL_l ; rel_flipL_r...
    rel_allocBtape_l γ as "γ"...
    rel_allocBtape_r γ' as "γ'"...
    rel_store_r...
    rel_store_l...
    iApply (refines_na_close with "[-$Hclose]") ; iSplitL "xb xb'" ; [ iExists _, _ ; iFrame ; done |].
    iApply (refines_seq with "[Hf]") ; [by iApply "Hf"|].
    iApply (refines_na_inv with "[-$Hinv]"); [done|].
    iIntros "(>(%not_necessarily_b & %not_necessarily_b' & xb & xb' & <-) & Hclose)".
    rel_apply (refines_couple_bool_tape_tape (xor_sem not_necessarily_b) _ _ _ _ γ γ' )
              => // ; iFrame ; iIntros (b') "(γ' & γ)" => /=.
    rel_flipL_l ; rel_flipL_r...
    unfold xor ; rel_load_r...
    iApply (refines_na_close with "[-$Hclose]") ; iSplitL "xb xb'" ; [ iExists _, _ ; iFrame ; done |].
    unshelve rel_apply_r (refines_steps_r $! (xor_tp _ _ _ _)) ; [easy|iModIntro].
    rewrite cancel.
    rel_values.
  Qed.

  Lemma call_flip_store_ignore :
    ⊢ REL call_flip << store_ignore : (() → ()) → (lrel_bool).
  Proof with try rel_pures_l ; try rel_pures_r ; try foldxor.
    rewrite /store_ignore /call_flip...
    rel_alloc_r x as "x"...
    iApply (refines_na_alloc (∃ b : bool, x ↦ₛ #b) awkwardN).
    iSplitL ; [ iExists _ ; iFrame ; done |].
    iIntros "#Hinv".
    iApply refines_arrow_val.
    iIntros "!#" (f1 f2) "#Hf".
    rel_allocBtape_r α as "α"...
    rel_allocBtape_l β as "β"...
    iApply (refines_na_inv with "[-$Hinv]") ; [done|].
    iIntros "(>(%old_b & xb) & Hclose)".
    rel_apply_r refines_flipL_empty_r => // ; iFrame ; iIntros "%b α"...
    rel_allocBtape_r γ as "γ"...
    rel_store_r...
    iApply (refines_na_close with "[-$Hclose]") ; iSplitL "xb" ; [ iExists _ ; iFrame ; done |].
    iApply (refines_seq with "[Hf]") ; [by iApply "Hf"|].
    iApply (refines_na_inv with "[-$Hinv]"); [done|].
    iIntros "(>(%not_necessarily_b & xb) & Hclose)".
    rel_apply refines_couple_bool_tape_tape => // ; iFrame ; iIntros (b') "(β & γ)" => /=.
    rel_flipL_r ; rel_flipL_l...
    iApply (refines_na_close with "[-$Hclose]") ; iSplitL "xb" ; [ iExists _ ; iFrame ; done |].
    rel_values.
  Qed.

  (* The opposite direction of the last three refinements. The proofs are
  essentially the same. *)
  Lemma store_xor_store_xor_late :
    ⊢ REL store_xor << store_xor_late : (() → ()) → (lrel_bool).
  Proof with try rel_pures_l ; try rel_pures_r ; try foldxor.
    rewrite /store_xor /store_xor_late...
    rel_alloc_l x as "x"... rel_alloc_r x' as "x'"...
    iApply (refines_na_alloc (∃ b b' : bool, x ↦ #b ∗ x' ↦ₛ #b' ∗ ⌜b = b'⌝) awkwardN).
    iSplitL ; [ iExists _,_ ; iFrame ; done |].
    iIntros "#Hinv".
    iApply refines_arrow_val.
    iIntros "!#" (f1 f2) "#Hf".
    rel_allocBtape_l α as "α"...
    rel_allocBtape_r β as "β"...
    iApply (refines_na_inv with "[-$Hinv]") ; [done|].
    iIntros "(>(%old_b & %old_b' & xb & xb' & <-) & Hclose)".
    iApply refines_couple_bool_tape_tape => // ; iFrame ; iIntros (b) "(β & α)" => /=.
    rel_flipL_l ; rel_flipL_r...
    rel_allocBtape_l γ as "γ"...
    rel_allocBtape_r γ' as "γ'"...
    rel_store_r...
    rel_apply (refines_couple_bool_tape_tape _ _ _ _ _ γ γ' ) => // ; iFrame ; iIntros (b') "(γ' & γ)" => /=.
    rel_flipL_l...
    rel_store_l...
    iApply (refines_na_close with "[-$Hclose]") ; iSplitL "xb xb'" ; [ iExists _, _ ; iFrame ; done |].
    iApply (refines_seq with "[Hf]") ; [by iApply "Hf"|].
    rel_flipL_r...
    iApply (refines_na_inv with "[-$Hinv]"); [done|].
    iIntros "(>(%not_necessarily_b & %not_necessarily_b' & xb & xb' & <-) & Hclose)".
    unfold xor ; rel_load_r ; rel_load_l...
    iApply (refines_na_close with "[-$Hclose]") ; iSplitL "xb xb'" ; [ iExists _, _ ; iFrame ; done |].
    unshelve rel_apply_r (refines_steps_r $! (xor_tp _ _ _ _)) ; [easy|iModIntro].
    rel_apply_l (refines_wp_l).
    wp_apply wp_mono.
    2: wp_apply xor_wp.
    iIntros (v) "->".
    rel_values.
  Qed.

  Lemma store_xor_late_store_ignore :
    ⊢ REL store_xor_late << store_ignore : (() → ()) → (lrel_bool).
  Proof with try rel_pures_l ; try rel_pures_r ; try foldxor.
    rewrite /store_xor_late /store_ignore...
    rel_alloc_l x as "x"... rel_alloc_r x' as "x'"...
    iApply (refines_na_alloc (∃ b b' : bool, x ↦ #b ∗ x' ↦ₛ #b' ∗ ⌜b = b'⌝) awkwardN).
    iSplitL ; [ iExists _,_ ; iFrame ; done |].
    iIntros "#Hinv".
    iApply refines_arrow_val.
    iIntros "!#" (f1 f2) "#Hf".
    rel_allocBtape_l α as "α"...
    rel_allocBtape_r β as "β"...
    iApply (refines_na_inv with "[-$Hinv]") ; [done|].
    iIntros "(>(%old_b & %old_b' & xb & xb' & <-) & Hclose)".
    iApply refines_couple_bool_tape_tape => // ; iFrame ; iIntros (b) "(β & α)" => /=.
    rel_flipL_l ; rel_flipL_r...
    rel_allocBtape_l γ as "γ"...
    rel_allocBtape_r γ' as "γ'"...
    rel_store_r...
    rel_store_l...
    iApply (refines_na_close with "[-$Hclose]") ; iSplitL "xb xb'" ; [ iExists _, _ ; iFrame ; done |].
    iApply (refines_seq with "[Hf]") ; [by iApply "Hf"|].
    iApply (refines_na_inv with "[-$Hinv]"); [done|].
    iIntros "(>(%not_necessarily_b & %not_necessarily_b' & xb & xb' & <-) & Hclose)".
    rel_apply (refines_couple_bool_tape_tape (xor_sem not_necessarily_b) _ _ _ _ γ γ' )
              => // ; iFrame ; iIntros (b') "(γ' & γ)" => /=.
    rel_flipL_l ; rel_flipL_r...
    unfold xor ; rel_load_l...
    iApply (refines_na_close with "[-$Hclose]") ; iSplitL "xb xb'" ; [ iExists _, _ ; iFrame ; done |].
    rel_apply_l (refines_wp_l).
    wp_apply wp_mono.
    2: wp_apply xor_wp.
    iIntros (v) "->".
    rel_values.
  Qed.

  Lemma store_ignore_call_flip :
    ⊢ REL store_ignore << call_flip : (() → ()) → (lrel_bool).
  Proof with try rel_pures_l ; try rel_pures_r ; try foldxor.
    rewrite /store_ignore /call_flip...
    rel_alloc_l x as "x"...
    iApply (refines_na_alloc (∃ b : bool, x ↦ #b) awkwardN).
    iSplitL ; [ iExists _ ; iFrame ; done |].
    iIntros "#Hinv".
    iApply refines_arrow_val.
    iIntros "!#" (f1 f2) "#Hf".
    rel_allocBtape_l α as "α"...
    rel_allocBtape_r β as "β"...
    iApply (refines_na_inv with "[-$Hinv]") ; [done|].
    iIntros "(>(%old_b & xb) & Hclose)".
    rel_apply_l refines_flipL_empty_l => // ; iFrame ; iIntros "%b α"...
    rel_allocBtape_l γ as "γ"...
    rel_store_l...
    iApply (refines_na_close with "[-$Hclose]") ; iSplitL "xb" ; [ iExists _ ; iFrame ; done |].
    iApply (refines_seq with "[Hf]") ; [by iApply "Hf"|].
    iApply (refines_na_inv with "[-$Hinv]"); [done|].
    iIntros "(>(%not_necessarily_b & xb) & Hclose)".
    rel_apply refines_couple_bool_tape_tape => // ; iFrame ; iIntros (b') "(β & γ)" => /=.
    rel_flipL_l ; rel_flipL_r...
    iApply (refines_na_close with "[-$Hclose]") ; iSplitL "xb" ; [ iExists _ ; iFrame ; done |].
    rel_values.
  Qed.

End proofs.

Theorem store_xor_call_flip_refinement :
  ∅ ⊨ store_xor ≤ctx≤ call_flip : (() → ()) → TBool.
Proof.
  eapply ctx_refines_transitive.
  - eapply (refines_sound clutchRΣ).
    intros. apply: store_xor_store_xor_late.
  - eapply ctx_refines_transitive.
    + eapply (refines_sound clutchRΣ).
      intros. apply: store_xor_late_store_ignore.
    + eapply (refines_sound clutchRΣ).
      intros. apply: store_ignore_call_flip.
Qed.

Theorem call_flip_store_xor_refinement :
  ∅ ⊨ call_flip ≤ctx≤ store_xor : (() → ()) → TBool.
Proof.
  eapply ctx_refines_transitive.
  - eapply (refines_sound clutchRΣ).
    intros. apply: call_flip_store_ignore.
  - eapply ctx_refines_transitive.
    + eapply (refines_sound clutchRΣ).
      intros. apply: store_ignore_store_xor_late.
    + eapply (refines_sound clutchRΣ).
      intros. apply: store_xor_late_store_xor.
Qed.
