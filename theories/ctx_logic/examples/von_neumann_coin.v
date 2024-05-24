(* A zoo of variants of Von Neumann's construction of a fair coin from a biased coin. *)
From clutch Require Export clutch lib.flip.
Set Default Proof Using "Type*".

Section proofs.
  Context `{!clutchRGS Σ}.

  Definition coinN := nroot.@"coin".

  (* Biased coin toss: t4 = { true ⟼ 1/4, false ⟼ 3/4 } *)
  Definition t4 :=
    (λ:<>,
      let: "b0" := flip in
      let: "b1" := flip in
      if: "b1" then "b0" else #false)%V.

  (* Von Neumann coin. *)
  Definition vnc (t : expr) :=
    (rec: "f" <> :=
      let: "x" := t #() in
      let: "y" := t #() in
      if: "x" = "y" then "f" #() else "x")%V.

  (* A variant that diverges instead of recursing. Can be used in simple
  situations to prove a left-refinement because our judgement allows discarding
  mass on the left. *)
  Definition vnc_div (t : expr) :=
    (λ:<>,
      let: "x" := t #() in
      let: "y" := t #() in
      if: "x" = "y" then (rec: "f" <> := "f" #()) #() else "x")%V.

  (* We can't show this refinement since the lhs needs to couple a combination
  of flips with a single flip on the rhs and since we may need to recurse an
  unbounded number of times. *)
  Goal ⊢ REL (vnc t4) << (λ:<>, flip) : lrel_unit → lrel_bool.
  Proof.
    rewrite /vnc.
    rel_pures_r. rel_pures_l.
    iApply refines_arrow_val.
    iIntros "!#" (??) "#[-> ->]".
    rel_pures_r. rel_pures_l.
    set (vnc4 := vnc t4).
    unfold vnc in vnc4.
    fold vnc4.
    unfold t4. rel_pures_l.
  Abort.

  (* A simpler coin toss: t2 = { true ⟼ 1/2, false ⟼ 1/2 } *)
  Definition t2 := (λ:<>, flip)%V.

  (* Still can't prove the refinement since we don't know how to recurse. *)
  Goal ⊢ REL (vnc t2) << (λ:<>, flip) : lrel_unit → lrel_bool.
  Proof.
    iLöb as "HH".
    rewrite /vnc.
    rel_pures_r. rel_pures_l.

    iApply refines_arrow_val.
    iIntros "!#" (??) "#[-> ->]".
    rel_rec_l.
    rel_pures_r. rel_pures_l.
    set (vnc2 := vnc t2) ; unfold vnc in vnc2 ; fold vnc2.
    unfold t2. rel_pures_l.

    rel_apply refines_couple_flip_flip.
    iIntros (b) "!>".
    rel_pures_l.
    rel_apply refines_flip_l.
    iIntros "!>" (b').
    rel_pures_l.
    case_bool_decide ; rel_pures_l.
    - admit.
    - rel_values.
  Abort.

  (* We can prove the refinement in case we diverge instead. *)
  Goal ⊢ REL (vnc_div t2) << (λ:<>, flip) : lrel_unit → lrel_bool.
  Proof.
    rewrite /vnc_div.
    rel_pures_r. rel_pures_l.
    iApply refines_arrow_val.
    iIntros "!#" (??) "#[-> ->]".
    rel_rec_l.
    rel_pures_r. rel_pures_l.
    set (vnc2 := vnc_div t2) ; unfold vnc_div in vnc2 ; fold vnc2.
    unfold t2. rel_pures_l.
    rel_apply refines_couple_flip_flip.
    iIntros (b) "!>".
    rel_pures_l.
    rel_apply refines_flip_l.
    iIntros "!>" (b').
    rel_pures_l.
    case_bool_decide ; rel_pures_l.
    - iLöb as "H".
      rel_rec_l.
      iExact "H".
    - rel_values.
  Qed.

  (* We can construct a refinement coupling of vnc_div t4 and flip by
     discarding weight of the recursive calls.

     The biased coin t4 is represented by the following tree, where left
     sub-branches correspond to the label evaluating to true (1) and right
     branches correspond to false (0). *)
(*   b0
    / \
   b1  b1
  / \ / \
 1  0 0 0  *)
  (* The vnc_div t4 program executes this tree twice and returns 1 if the two
     results differ, and diverges otherwise. *)

(*
                                /---------- b0 ----------\
                               b1                        b1
                           ___/  \___                ___/  \___
                          /          \              /          \
x = 1st run of t4:       1            0            0            0
                         |            |            |            |
                        b2           b2           b2           b2
                        / \          / \          / \          / \
                      b3   b3      b3   b3      b3   b3      b3   b3
                     / \   / \    / \   / \    / \   / \    / \   / \
y = 2nd run of t4:  1  0  0  0   1  0  0  0   1  0  0  0   1  0  0  0
                    |  |  |  |   |  |  |  |   |  |  |  |   |  |  |  |
x = y ?             y  n  n  n   n  y  y  y   n  y  y  y   n  y  y  y
                    |  |  |  |   |  |  |  |   |  |  |  |   |  |  |  |
vnc_div t4:         ⊥  1  1  1   0  ⊥  ⊥  ⊥   0  ⊥  ⊥  ⊥   0  ⊥  ⊥  ⊥

   *)
  Goal ⊢ REL (vnc_div t4) << (λ:<>, flip) : lrel_unit → lrel_bool.
  Proof with try rel_pures_r ; try rel_pures_l.
    rewrite /vnc_div...
    iApply refines_arrow_val.
    iIntros "!#" (??) "#[-> ->]".
    rel_pure_l.
    set (Ω := ((rec: "f" <> := "f" #()) #())%E).
    unfold t4...
    (* Case on the first lhs flip, don't couple anything. *)
    rel_apply_l refines_flip_l ; iIntros "!>" (b0) ; destruct b0 eqn:hb0...
    - rel_apply (refines_couple_flip_flip) ; iIntros "!>" (b1) ; destruct b1 eqn:hb1...
      + rel_apply_l refines_flip_l ; iIntros "!>" (b2) ; destruct b2 eqn:hb2...
        * rel_apply_l refines_flip_l ; iIntros "!>" (b3) ; destruct b3 eqn:hb3...
          -- iLöb as "H".
             rel_rec_l.
             iExact "H".
          -- rel_values.
        * rel_apply_l refines_flip_l ; iIntros "!>" (b3) ; destruct b3 eqn:hb3...
          all: rel_values.
      + rel_apply_l refines_flip_l ; iIntros "!>" (b2) ; destruct b2 eqn:hb2...
        * rel_apply_l refines_flip_l ; iIntros "!>" (b3) ; destruct b3 eqn:hb3...
          -- rel_values.
          -- iLöb as "H".
             rel_rec_l.
             iExact "H".
        * rel_apply_l refines_flip_l ; iIntros "!>" (b3) ; destruct b3 eqn:hb3...
          all: iLöb as "H" ; rel_rec_l ; iExact "H".
    - rel_apply_l refines_flip_l ; iIntros "!>" (b1) ; destruct b1 eqn:hb1...
      all: rel_apply_l refines_flip_l ; iIntros "!>" (b2) ; destruct b2 eqn:hb2...
      all: rel_apply (refines_couple_flip_flip negb) ; iIntros "!>" (b3) ; destruct b3 eqn:hb3...
      1,5: rel_values.
      all: iLöb as "H" ; rel_rec_l ; iExact "H".
  Qed.

  (* A similar problem: no single flip on the left behaves like the rhs. But we
  can pick our coupling after evaluating the first flip! *)
  Goal ⊢ REL flip = flip << flip : lrel_bool.
  Proof.
    rel_apply refines_flip_l.
    iIntros "!>" (b).
    rel_apply (refines_couple_flip_flip (if b then Datatypes.id else negb)).
    iIntros "!>" (b').
    destruct b, b' => /=.
    all: rel_pures_l.
    all: rel_values.
    Unshelve. destruct b ; apply _.
  Qed.

  (* We can also show this refinement where the result on the left only
  depends on the outcome of one flip. *)
  Goal ⊢ REL (let: "b" := flip in if: "b" = flip then "b" else "b") << flip : lrel_bool.
  Proof.
    rel_apply refines_couple_flip_flip.
    iIntros "!>" (b).
    rel_pures_l.
    rel_apply_l refines_flip_l.
    iIntros "!>" (b').
    rel_pures_l.
    case_bool_decide ; rel_pures_l.
    all: rel_values.
  Qed.

  (* We can even flip separately in each branch. *)
  Goal ⊢ REL if: flip then flip else flip << flip : lrel_bool.
  Proof.
    rel_apply_l refines_flip_l ; iIntros "!>" (b).
    destruct b ; rel_pures_l; rel_apply refines_couple_flip_flip;
      iIntros (?); rel_values. 
  Qed.

  (* A form of extensionality. *)
  Goal forall e τ Γ,
      ∅ ⊢ₜ e : τ →
      ⊢ REL if: flip then e else e << e : interp τ Γ.
  Proof.
    intros.
    rel_apply_l refines_flip_l ; iIntros (b').
    destruct b' ; iModIntro ; rel_pures_l.
    all: rel_apply_l refines_typed.
    all: assumption.
  Qed.

End proofs.
