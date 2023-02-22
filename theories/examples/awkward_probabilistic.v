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

From stdpp Require Import namespaces.
From self.program_logic Require Import weakestpre.
From self.prob_lang Require Import lang notation spec_ra spec_tactics proofmode primitive_laws.
From self.logrel Require Import model rel_rules rel_tactics compatibility.
From self.examples Require Import one_time_pad.
From self.prelude Require Import base.
Set Default Proof Using "Type*".

Section proofs.
  Context `{!prelogrelGS Σ}.

  Definition awkwardN := nroot.@"awkward".

  Lemma refinement_prob :
    ⊢ REL
      (let: "α" := AllocTape in
       let: "callable" := ref #true in
       (λ: "f", if: ! "callable" then "callable" <- #false ;; "f" #() ;; SOME (flip "α") else NONE))
    <<
      (let: "x" := ref (flip #()) in
       let: "callable" := ref #true in
       (λ: "f", if: ! "callable" then "callable" <- #false ;; "f" #() ;; SOME (!"x") else NONE))
    : (() → ()) → lrel_sum lrel_unit lrel_bool.
  Proof with try rel_pures_l ; try rel_pures_r.
    rel_alloctape_l α as "α".
    rel_apply_r (refines_couple_tape_flip with "[$α]"); [done|].
    iIntros (b) "Hα /="...
    rel_alloc_r x as "Hx"...
    rel_alloc_l cl as "Hcl"...
    rel_alloc_r cr as "Hcr"...
    set (P := ((x ↦ₛ #b ∗ α ↪ [b] ∗ cl ↦ #true ∗ cr ↦ₛ #true ∨ cl ↦ #false ∗ cr ↦ₛ #false))%I).
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
      rel_load_r. rel_flip_l...
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
  Lemma refinement_prob_resample :
    ⊢ REL
      (λ: "f", let: "α" := alloc in
               "f" #() ;; flip "α")
    <<
      (let: "x" := ref #false in
       (λ: "f", let: "β" := alloc in
                let: "b" := flip "β" in
                let: "γ" := alloc in
                let: "b'" := flip "γ" in
                "x" <- "b" ;;
                "f" #() ;;
                xor (! "x") "b'" ))
    : (() → ()) → (lrel_bool).
  Proof with try rel_pures_l ; try rel_pures_r ; try foldxor.
    rel_pures_r. rel_alloc_r x as "Hx"...
    iApply (refines_na_alloc (∃ b : bool, x ↦ₛ #b) awkwardN).
    iSplitL ; [ iExists _ ; iFrame |].
    iIntros "#Hinv".
    iApply refines_arrow_val.
    iIntros "!#" (f1 f2) "#Hf".
    rel_alloctape_r β as "β"...
    rel_alloctape_l α as "α"...
    iApply (refines_na_inv with "[-$Hinv]") ; [done|].
    iIntros "(>(%old_b & xb ) & Hclose)".
    rel_apply_r refines_flip_empty_r => // ; iFrame. iIntros "%b β"...
    rel_alloctape_r γ as "γ"...
    (* Now we lose. If we had prophecies, we could couple α and γ with the
    bijection (xor !x) at the time when the read from x occurs. Instead, we can
    try to couple with the current contents of x, i.e. b. But we can't hope
    that this will be preserved, so we'll get stuck later on. *)
    rel_apply_r (refines_couple_tapes (xor_sem b) _ _ _ _ α γ ) => // ; iFrame.
    iIntros (b'') "(γ & α)" => /=.
    rewrite -{2}(cancel (xor_sem b) (xor_sem b) b''). set (b' := (xor_sem b b'')).
    rel_flip_r... rel_store_r...
    iApply (refines_na_close with "[-$Hclose]") ; iSplitL "xb" ; [ by iExists _ |].
    iApply (refines_seq with "[Hf]") ; [by iApply "Hf"|].
    rel_flip_l.
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

  (* We can isolate the problem by trying to go via this intermediate lhs
  program where the xor is removed, and we'll get stuck in the same way. *)
  Lemma refinement_prob_resample :
    ⊢ REL
      (let: "x" := ref #false in
       (λ: "f", let: "β" := alloc in
                let: "b" := flip "β" in
                let: "γ" := alloc in
                "x" <- "b" ;;
                "f" #() ;;
                let: "b'" := flip "γ" in
                "b'" ))
    <<
      (let: "x" := ref #false in
       (λ: "f", let: "β" := alloc in
                let: "b" := flip "β" in
                let: "γ" := alloc in
                let: "b'" := flip "γ" in
                "x" <- "b" ;;
                "f" #() ;;
                xor (! "x") "b'" ))
    : (() → ()) → (lrel_bool).
  Proof with try rel_pures_l ; try rel_pures_r ; try foldxor.
    rel_pures_r. rel_alloc_r x as "Hx"...
    rel_alloc_l x' as "Hx'"...
    iApply (refines_na_alloc (∃ b' b : bool, x' ↦ #b' ∗ x ↦ₛ #b)%I awkwardN) ;
      iSplitL ; [ do 2 iExists _ ; iFrame |].
    iIntros "#Hinv".
    iApply refines_arrow_val.
    iIntros "!#" (f1 f2) "#Hf".
    rel_alloctape_r β as "β". rel_alloctape_l β' as "β'"...
    iApply (refines_na_inv with "[-$Hinv]"); [done|].
    iIntros "(>(%_b' & %_b & xb' & xb) & Hclose)".
    rel_apply_r refines_flip_empty_r => // ; iFrame. iIntros "%b β"...
    rel_apply_l refines_flip_empty_l => // ; iFrame. iIntros "%b' β'"...
    rel_alloctape_r γ as "γ".
    rel_alloctape_l γ' as "γ'"... rel_store_l...
    (* We're about to get stuck in the same way as before; we just don't know
    what `x` is going to be after we call f2. We can couple γ' with `xor b` but
    that won't be good enough later. *)
    rel_apply_r (refines_couple_tapes (xor_sem b)) => //. iFrame.
    iIntros (xor_of_b_and_of_b') "(γ & α)".
    rel_flip_r... rel_store_r...
    iApply (refines_na_close with "[-$Hclose]") ; iSplitL "xb xb'" ; [ do 2 iExists _ ; iFrame|].
    iApply (refines_seq with "[Hf]"); auto ; [iApply "Hf" => //|].
    iApply (refines_na_inv with "[-$Hinv]"); [done|] ;
      iIntros "(>(%b'' & %not_necessarily_b & xb'' & xb ) & Hclose)".
    rel_flip_l...
    unfold xor ; rel_load_r...
    iApply (refines_na_close with "[-$Hclose]") ; iSplitL "xb xb''" ; [do 2 iExists _ ; iFrame|].
    unshelve rel_apply_r (refines_steps_r $! (xor_tp _ _ _ _)) ; [easy|iModIntro].
    (* We do not know this, in fact it may well be false (i.e. read this as `assert False`). *)
    assert (b = not_necessarily_b) as <- by admit.
    rewrite /b'. rewrite cancel.
    rel_values.
Abort.

  (* Perform the lhs flip before calling `f`. Doesn't help, same problem. *)
  Lemma refinement_prob_resample :
    ⊢ REL
      (let: "x" := ref #false in
       (λ: "f", let: "β" := alloc in
                let: "b" := flip "β" in
                let: "γ" := alloc in
                "x" <- "b" ;;
                let: "b'" := flip "γ" in
                "f" #() ;;
                "b'" ))
    <<
      (let: "x" := ref #false in
       (λ: "f", let: "β" := alloc in
                let: "b" := flip "β" in
                let: "γ" := alloc in
                let: "b'" := flip "γ" in
                "x" <- "b" ;;
                "f" #() ;;
                let: "vx" := ! "x" in
                xor "vx" "b'" ))
    : (() → ()) → (lrel_bool).
  Proof with try rel_pures_l ; try rel_pures_r ; try foldxor.
    #[local] Ltac rel_pures_r := rel_tactics.rel_pures_r ; try foldxor.
    rel_alloc_r x as "Hx"...
    rel_alloc_l x' as "Hx'"...
    iApply (refines_na_alloc (∃ b' b : bool, x' ↦ #b' ∗ x ↦ₛ #b)%I awkwardN).
    iSplitL ; [ do 2 iExists _ ; iFrame |].
    iIntros "#Hinv".
    iApply refines_arrow_val.
    iIntros "!#" (f1 f2) "#Hf".
    rel_alloctape_r β as "β"...
    rel_alloctape_l β' as "β'"...
    iApply (refines_na_inv with "[-$Hinv]"); [done|].
    iIntros "(>(%_b' & %_b & xb' & xb) & Hclose)".
    rel_apply_r refines_flip_empty_r => // ; iFrame. iIntros "%b β"...
    rel_apply_l refines_flip_empty_l => // ; iFrame. iIntros "%b' β'"...
    rel_alloctape_r γ as "γ"... rel_alloctape_l γ' as "γ'"...
    rel_store_l...
    (* We're about to get stuck in the same way as before; we just don't know
    what `x` is going to be after we call f2. We can couple γ' with `xor b` but
    that won't be good enough later. *)
    rel_apply_r (refines_couple_tapes (xor_sem b) _ _ _ _ γ' γ) => // ; iFrame.
    iIntros (xor_of_not_necessarily_b_and_of_b') "(γ & α)".
    rel_flip_l... rel_flip_r...
    rel_store_r...
    iApply (refines_na_close with "[-$Hclose]") ; iSplitL "xb xb'".
    1: iModIntro ; do 2 iExists _ ; iFrame.
    iApply (refines_seq with "[Hf]") ; first by iApply "Hf".
    iApply (refines_na_inv with "[-$Hinv]"); [done|].
    iIntros "(>(%b'' & %not_necessarily_b & xb'' & xb ) & Hclose)".
    rel_load_r...
    iApply (refines_na_close with "[-$Hclose]") ; iSplitL "xb xb''".
    1: iModIntro ; do 2 iExists _ ; iFrame.
    unshelve rel_apply_r (refines_steps_r $! (xor_tp _ _ _ _)) ; [easy|iModIntro].
    (* We do not know this, in fact it may well be false (i.e. read this as `assert False`). *)
    assert (b = not_necessarily_b) as <- by admit.
    rewrite /b'. rewrite cancel.
    rel_values.
  Abort.

  (* This refinement does not actually hold since calling the rhs with an f
  that invokes the rhs itselve allows to observe the identical return value of
  two consecutive calls while the lhs always samples. *)
  Lemma refinement_prob_resample_let :
    ⊢ REL
      (λ: "f", let: "α" := alloc in
               let: "v" := flip #() in
               "f" #() ;;
               SOME "v"
      )
    <<
      (let: "x" := ref NONE in
       (λ: "f", let: "β" := alloc in
                let: "b" := flip #() in
                "x" <- SOME "b" ;;
                "f" #() ;;
                !"x" ))
    : (() → ()) → (lrel_sum lrel_unit lrel_bool).
  Proof with try rel_pures_l ; try rel_pures_r.
    rel_pures_r. rel_alloc_r x as "Hx"...
    set (P := (x ↦ₛ NONEV ∨ ∃ (b : bool), (x ↦ₛ SOMEV #b))%I).
    iApply (refines_na_alloc P awkwardN).
    iSplitL ; [ try iExists _ ; try iLeft ; iFrame |].
    iIntros "#Hinv".
    iApply refines_arrow_val.
    iIntros "!#" (f1 f2) "#Hf".
    rel_alloctape_r β as "β"...
    rel_alloctape_l α as "α"...
    rel_apply refines_couple_flips_lr.
    iIntros (b')...
    iApply (refines_na_inv with "[-$Hinv]"); [done|].
    unfold P.
    iIntros "(> [b | (%b & b )] & Hclose)".
    - rel_store_r...
      (* `x` points to `b`, but calling `f2` may not preserve this. *)
      iApply (refines_na_close with "[-$Hclose]") ; iSplitL "b".
      { iModIntro. iRight. iExists _. iFrame. }
      iApply (refines_seq with "[Hf]"); auto. 1: iApply "Hf" => //.
      iApply (refines_na_inv with "[-$Hinv]"); [done|].
      iIntros "(> [b | (%b & b )] & Hclose)".
      + rel_load_r. give_up.    (* x ↦ₛ NONE should be impossible *)
      + rel_load_r. give_up.    (* We know nothing about the relation between b, b'. *)
    - rel_store_r...
      give_up.
Abort.


  (* If the reference to `x` is local to the rhs closure, we never need to
     transfer its ownership into an invariant, and `f` cannot interfere with
     it, so we can couple with `x`. *)
  Lemma refinement_prob_resample_local_ref :
    ⊢ REL
      (λ: "f", let: "α" := alloc in
               "f" #() ;;
               flip "α")
    <<
      (λ: "f", let: "β" := alloc in
               let: "b" := flip "β" in
               let: "x" := ref "b" in
               "f" #() ;;
               !"x" )
    : (() → ()) → lrel_bool.
  Proof with try rel_pures_l ; try rel_pures_r.
    rel_pures_r...
    iApply refines_arrow_val.
    iIntros "!#" (f1 f2) "#Hf"...
    rel_alloctape_l α as "α"...
    rel_alloctape_r β as "β"...
    iApply refines_couple_tapes_eq ; auto ; iFrame ;
      iIntros (b) "(β & α)" => /=.
    rel_flip_r...
    rel_alloc_r x as "Hx"...
    iApply (refines_seq with "[Hf]") => //. 1: iApply "Hf" => //.
    rel_flip_l.
    rel_load_r.
    rel_values.
  Qed.

End proofs.
