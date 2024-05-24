From stdpp Require Import sorting.
From clutch.common Require Import inject.
From clutch.eris Require Import eris.
From clutch.eris.lib Require Import list.
Set Default Proof Using "Type*".

Section in_place_quicksort.

  Import list.

  Local Notation sorted := (StronglySorted Nat.le).

  Context `{!erisGS Σ}.

  Definition swap :=
    (λ: "arr" "a" "b",
        let: "tmp" := !("arr" +ₗ "a") in
        "a" <- !("arr" +ₗ "b") ;;
        "b" <- "tmp")%V.

  Definition swapped `{T: Type} `{!Inhabited T} (a b : nat) A : list T
    := <[a := (A !!! b)]> $ <[b := (A !!! a)]> A.

  Lemma swap_spec arr (A : list val) (a b : nat) :
    ⊢ {{{ (arr ↦∗ A) ∗ ⌜(a < (length A))%nat⌝ ∗ ⌜(b < (length A))%nat⌝ }}}
        swap #arr #a #b
      {{{ v, RET v; ((arr ↦∗ (swapped a b A)))}}}.
  Proof. Admitted.

  Definition prefix_parted_l (A : list nat) (len_left pivot_v: nat) : Prop
    := Forall (fun v => (v <= pivot_v)%nat) (take len_left A).

  Definition prefix_parted_r (A : list nat) (len_left next pivot_v: nat) : Prop
    := Forall (fun v => (v > pivot_v)%nat) (drop len_left (take next A)).

  Definition prefix_sorted (A : list nat) (len_left next pivot_v: nat) : Prop
    := prefix_parted_l A len_left pivot_v /\ prefix_parted_r A len_left next pivot_v.

  Definition in_place_pivot
    := (λ: "arr" "len" "pivot",
          (* Swap pivot with the last element *)
          swap "arr" "pivot" ("len" - #1) ;;
          let: "pivot_v" := !("arr" +ₗ ("len" - #1)) in

          let: "len_left" := ref #0 in
          (* rec inv.
                len_left < next <= len - 1
                for all 0 <= i < len_left, (arr[i] <= pivot)
                for all len_left <= i < next, (arr[i] > pivot)
                ⇒ if (next = len - 1), array is of the form [less than pivot, greater than pivot, pivot]
          *)
          (rec: "swap_next" "next" :=
             if: ("next" = ("len" - #1))
                then #()
                else (
                    if: (!("arr" +ₗ "next") ≤ "pivot_v")
                      then
                        (* next belongs in the left list *)
                        swap "arr" "next" "len_left" ;;
                        "len_left" <- !("len_left" + #1) ;;
                        "swap_next" ("next" + #1)
                      else
                        "swap_next" ("next" + #1)))
          #0 ;;

          (* Swap pivot back into the right spot*)
          swap "arr" !("len_left") ("len" - #1) ;;
          "len_left")%V.

  Definition pivot_correct (A : list nat) pivot len_left : Prop :=
    prefix_parted_l A len_left (A !!! pivot) /\
    prefix_parted_r A (S len_left) (length A) (A !!! pivot).

  Definition refl_values A : list val := fmap (fun (n: nat) => #n) A.


  Lemma in_place_pivot_spec (A : list nat) arr (pivot : nat) :
    ⊢ (arr ↦∗ (refl_values A)) -∗
      WP (in_place_pivot #arr #(length A) #pivot)
        {{λ len_left_v, ∃ R (len_left : nat),
              arr ↦∗ (refl_values R) ∗
              ⌜len_left_v = #len_left⌝ ∗
              ⌜pivot_correct R pivot len_left⌝ }}.
  Proof. Admitted.


  Definition quicksort :=
    (rec: "quicksort" "arr" "len" :=
       if: ("len" = #0)%E
        then #()
        else
          let: "pivot" := rand "len" in
          let: "len_left" := in_place_pivot "arr" "len" "pivot" in
          let: "left" := "arr" in
          let: "right" := (#1 + "len_left") in
          let: "len_right" := ("len" - "right" + #1) in
          "quicksort" "left" "len_left" ;;
          "quicksort" "right" "len_right")%V.

  Lemma quicksort_spec arr (A : list nat) :
    ⊢ {{{ (arr ↦∗ (refl_values A)) }}}
        quicksort #arr #(length A)
      {{{ v, RET v; ∃ A1, ((arr ↦∗ refl_values A1 ∗ ⌜(sorted A1)⌝))}}}.
  Proof.
    iLöb as "IH" forall (A arr).
    iIntros (Φ) "!> Harr HΦ".
    rewrite /quicksort.
    wp_pures.
    case_bool_decide as Hdec.
    - (* Base case *)
      wp_pures.
      iApply "HΦ"; iModIntro; iExists _; iFrame.
      iPureIntro.
      inversion Hdec as [Hdec1].
      rewrite -Nat2Z.inj_0 in Hdec1.
      apply Nat2Z.inj in Hdec1.
      rewrite (nil_length_inv A); eauto.
      apply SSorted_nil.
    - (* Inductive case *)
      wp_pures.

      (* CREDIT ACCOUNTING: Advanced composition on the rank of (rand #(length A)) in A *)
      wp_apply wp_rand; eauto.
      iIntros (s) "_".

      (* Step through the in-place pivot *)
      (* this is a total mess *)
      wp_pures.
      wp_bind (in_place_pivot _ _ _)%E.
      iApply (ub_wp_mono); last first.
      { iApply ub_wp_frame_r; iSplitL; last iApply "IH".
        iApply ub_wp_frame_r; iSplitR "HΦ"; last iApply "HΦ".
        wp_apply (in_place_pivot_spec with "Harr"). }
      iIntros (len_left) "[[[%R [%len_left_nat [Harr [-> %Hcorrect]]]] HΦ] #IH]".

      (* Prepare inductive calls *)
      do 11 wp_pure.

      (* Manually split the permission to Harr *)
      assert (Hspec_improvement : exists RL RR vp, R = RL ++ ([vp] ++ RR) /\ (length RL = len_left_nat)%R) by admit.
      destruct (Hspec_improvement) as [RL [RR [vp [-> HRLL]]]].
      iAssert (arr ↦∗ (refl_values RL) ∗
               (arr +ₗ (length RL)) ↦∗ (refl_values [vp]) ∗
               (arr +ₗ (length RL + 1)) ↦∗ (refl_values RR))%I
        with "[Harr]" as "(HarrL & HarrP & HarrR)".
      {
        admit.
      }
      wp_bind (((RecV _ _ _) _) _)%E.
      iApply (ub_wp_mono with "[HarrL HarrP HarrR]"); last first.
      { iSpecialize ("IH" $! (take len_left_nat A) arr).
        replace (length (take len_left_nat A)) with len_left_nat; last first.
        { (* Probably doable *) admit. }
        iApply ("IH" with "[HarrL]"); last iFrame.
        {  (* idk *) admit. }
        iNext.
        iIntros (?) "H".
        iAssert ((∃ A1 : list nat, arr ↦∗ refl_values A1 ∗ ⌜sorted A1⌝) ∗ ((arr +ₗ (length RL + 1)) ↦∗ refl_values RR) ∗  ((arr +ₗ length RL) ↦∗ refl_values [vp]))%I with "[$]" as "X".
        iApply "X".
      }

      iIntros (v) "(A & HarrP & HarrR)".
      do 2 wp_pure.


      wp_bind (((RecV _ _ _) _) _)%E.
      iApply (ub_wp_mono with "[A HarrP HarrR]"); last first.
      { admit.
      }

  Admitted.


End in_place_quicksort.
