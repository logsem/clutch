From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From self Require Import spec_rules rel_rules rel_tactics notation types proofmode model spec_tactics.

Notation "'match:' e0 'with' | 'NONE' => e1 | 'SOME' x => e2 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing) : expr_scope.
Notation "'match:' e0 'with' | 'SOME' x => e2 | 'NONE' => e1 'end'" :=
  (Match e0 BAnon e1 x%binder e2)
  (e0, e1, x, e2 at level 200, only parsing) : expr_scope.

Definition lazy α : expr :=
  let:"s" := ref NONE in
  (λ:"_u", match: !"s" with
           | NONE => let: "b" := flip #lbl:α in
                     "s" <- SOME "b" ;;
                     "b"
           | SOME "b" => "b" end).

Definition eager α : expr :=
  let:"b" := flip #lbl:α in
  (λ:"_u", "b").


Section proofs.
  Context `{!prelocGS Σ}.

  Definition coinN := nroot.@"coins".

  (* Warmup: the flips have already been resolved. *)
  Lemma lazy_eager_refinement α b bs :
    (* TODO: should instead assume that REL α << αₛ : lrel_tape *)
    α ↪ₛ (b::bs) ∗ α ↪ (b::bs)
    -∗ REL lazy α << eager α : lrel_unit → lrel_bool.
  Proof.
    iIntros "[Hαs Hα]".
    rewrite /lazy /eager.
    rel_alloc_l l as "Hl".
    do 2 rel_pure_l.

    rel_bind_r (Flip _).
    rewrite refines_eq /refines_def.
    iIntros (K) "HCs".
    rewrite {1} /refines_right.
    rewrite -fill_app.
    iPoseProof ((step_flip _ _ α) with "[Hαs HCs]") as "> (Hs & Hb & Hαs)" ; auto.
    { now iFrame. }
    (* iModIntro. *)
    rewrite fill_app.
    fold refines_right.
    iAssert (spec_ctx ∗ ⤇ fill K (fill [AppRCtx (λ: "b" "_u", "b")] #b))%I with "[Hs Hb]" as "HH"
    ; [iFrame|].
    replace (spec_ctx ∗ ⤇ fill K (fill [AppRCtx (λ: "b" "_u", "b")] #b))%I with
      (refines_right K (fill [AppRCtx (λ: "b" "_u", "b")] #b)) by reflexivity.
    iRevert (K) "HH".
    rewrite -/refines_def.

    (* TODO: move to rel_tactics *)
    replace (∀ a : list (ectxi_language.ectx_item prob_ectxi_lang),
                refines_right a (fill [AppRCtx (λ: "b" "_u", "b")] #b) ={⊤}=∗
                                                                          WP λ: "_u",
               match: ! #l with
                 InjL <> => let: "b" := flip #lbl:α in #l <- InjR "b";; "b"
               | InjR "b" => "b"
               end
                 {{ v, ∃ v' : val, refines_right a v' ∗ (() → lrel_bool)%lrel v v' }}
            )%I
      with
      (REL
         λ: "_u",
        match: ! #l with
          InjL <> => let: "b" := flip #lbl:α in #l <- InjR "b";; "b"
        | InjR "b" => "b"
        end
          << (fill [AppRCtx (λ: "b" "_u", "b")] #b)
        : () → lrel_bool)%I.
    2:{ rewrite refines_eq /refines_def ; reflexivity. }
    simpl.

    rel_pure_l.
    do 3 rel_pure_r.

    iMod (invariants.inv_alloc coinN _

                    (l ↦ NONEV ∗ α ↪ (b::bs) ∨ l ↦ SOMEV #b)%I

           (* (∃ (b : bool), *)
           (*     is_locked_r lk false *)
           (*       ∗ ce ↦ #b *)
           (*       ∗ (cl ↦ₛ NONEV ∨ cl ↦ₛ SOMEV #b) *)
           (* )%I *)
            with "[-]") as "#Hinv".
    { iNext. iLeft. iFrame. }

    iApply refines_arrow.
    (* rel_arrow. *)
    iIntros (v1 v2) "!> _".

    rel_pure_r.

    (* iInv coinN as "HHH" "Hclose". *)

    (* rel_pure_l doesn't give us a ▷ in the goal, this does. *)
    rel_pure_l.
    rel_load_l_atomic.
    iInv coinN as "> [[H G] | H]" "Hclose"; first last.

    (* The second branch of lazy, amounting to #b << #b : bool. *)
    - iModIntro. iExists _.
      iFrame.
      iNext.
      iIntros "Hl".
      rel_pures_l.
      rel_values.
      iMod ("Hclose" with "[Hl]").
      + eauto.
      + eauto.
    - iModIntro.
      iExists _.
      iFrame.
      iNext.
      iIntros "Hl".
      rel_pures_l.
      rel_bind_l (Flip _).

      (* Should be [iApply refines_wp_l], but that one only seems to work with the top mask.
         Let's replay that proof and see where it gets stuck. *)
      rewrite refines_eq /refines_def.
      iIntros (j) "Hs /=".

      iMod ("Hclose" with "[Hl]").


      iMod wp_flip.


    iModIntro. iApply wp_bind.
    iApply (wp_wand with "He").
    iIntros (v) "Hv".
    by iMod ("Hv" with "Hs").

    iApply refines_wp_l.

    iApply wp_flip.

    rel_load_l.



  iStartProof;
  rel_reshape_cont_l

    ltac:(fun K e' =>
      (* unify e' ef; *)
      (* (iApply refines_pure_l || idtac "nope") ; *)
      eapply (tac_rel_pure_l K e');
      [reflexivity                  (** e = fill K e' *)
      |iSolveTC                     (** PureClosed ϕ e' e2 *)
      | .. ]);
      [try prob_lang.proofmode.solve_vals_compare_safe                (** φ *)
      |
        (* first [left; split; reflexivity              (** Here we decide if the mask E is ⊤ *) *)
        (*      | right; reflexivity]                  (**    (m = n ∧ E = ⊤) ∨ (m = 0) *) *)
        ..
      |iSolveTC                                     (** IntoLaters *)
      |simpl; reflexivity           (** eres = fill K e2 *)
      |rel_finish                   (** new goal *)]
  (* || fail "rel_pure_l: cannot find the reduct" *).

Unshelve.


    rel_bind_l (_ _). iApply refines_pure_l ; auto ; simpl.

    rel_pure_l.


    rel_pure_l ; rel_pure_r ; clear v1 v2.

    iInv coinN as "HHH" "Hclose".

    rel_load_l.

    rel_load_l_atomic.

    iModIntro.
    iExists _.
    iApply bi.later_sep_1.
    iNext.
    iDestruct "HHH" as "[[ Hl Hα ] | Hl ]".
    - iFrame.
      iIntros "Hl".
      repeat rel_pure_l.
      admit.
    - iIntros.
