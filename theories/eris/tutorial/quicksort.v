(* We prove functional correctness of randomised quicksort. *)

From stdpp Require Import sorting.
From clutch.common Require Import inject.
From clutch.eris Require Import eris.
From clutch.eris.lib Require Import list.
Set Default Proof Using "Type*".

Section quicksort.

  Context `{!erisGS Σ}.

  Definition partition : expr :=
    let: "negb" := λ:"b", if: "b" then #false else #true in
    λ:"l" "e",
      let: "f" := (λ:"x", "e" < "x") in
      (list_filter (λ:"x", "negb" ("f" "x") ) "l",
        list_filter "f" "l").

  Definition qs : val :=
    rec: "qs" "l" :=
      let: "n" := list_length "l" in
      if: "n" <= #1 then "l" else
        let: "ip" := rand ("n" - #1) in
        let, ("p", "r") := list_remove_nth_unsafe "l" "ip" in
        let, ("le", "gt") := partition "r" "p" in
        let, ("les", "gts") := ("qs" "le", "qs" "gt") in
        list_append "les" (list_cons "p"  "gts").


  Lemma filter_split_perm {A} (l : list A) f :
    l ≡ₚ List.filter f l ++ List.filter (fun x=>negb (f x)) l.
  Proof.
    induction l as [|a l IHl] => // /=.
    destruct (f a) => /= ; rewrite -?Permutation_middle -IHl //.
  Qed.

  Lemma Partition (xs : list Z) l (e : Z) :
    {{{ ⌜is_list xs l⌝ }}}
      partition l (Val #e)
    {{{ le gt, RET (le, gt);
        ∃ xsle xsgt : list Z,
          ⌜is_list xsle le ∧ is_list xsgt gt
          ∧ app xsle xsgt ≡ₚ xs ⌝
          ∧ ⌜ ∀ x, In x xsle → (x ≤ e)%Z ⌝
                   ∧ ⌜ ∀ x, In x xsgt → (e < x)%Z ⌝
    }}}.
  Proof.
    iIntros (φ Lxs) "hφ".
    rewrite /partition. subst.
    wp_pures.
    wp_bind (list_filter _ _).
    iApply (wp_list_filter _ (λ x, bool_decide (e < x)%Z)).
    { iSplit => //. iIntros (x ψ) "_ !> hψ".
      simpl. wp_pures. iApply "hψ". eauto. }
    iIntros "!>" (gt egt). wp_pures.
    wp_bind (list_filter _ _).
    iApply (wp_list_filter _ (λ x, negb $ bool_decide (e < x)%Z)).
    { iSplit => //. iIntros (x ψ) "_ !> hψ".
      simpl. wp_pures.
      case_bool_decide ; wp_pures ; by iApply "hψ". }
    iIntros "!>" (le ele).
    wp_pures. iApply "hφ". iPureIntro.
    set (xs_gt := (List.filter (λ x : Z, bool_decide (e < x)%Z) xs)) in *.
    set (xs_le := (List.filter (λ x : Z, negb $ bool_decide (e < x)%Z) xs)) in *.
    exists xs_le, xs_gt. intuition auto.
    2:{ epose proof (filter_In _ x xs) as [h _]. destruct (h H) as [_ hle].
        destruct (bool_decide (e < x)%Z) eqn:hlt => //.
        apply bool_decide_eq_false in hlt.
        apply Z.nlt_ge. done.
    }
    2:{ epose proof (filter_In _ x xs) as [h _]. destruct (h H) as [_ hgt].
        by apply bool_decide_eq_true in hgt.
    }
    epose proof (filter_split_perm xs _) as xs_split.
    symmetry. subst xs_le xs_gt.
    rewrite Permutation_app_comm. apply xs_split.
  Qed.

  Local Notation sorted := (StronglySorted Z.le).

  Fact sorted_append pre post p :
    sorted pre → sorted post →
    (∀ x, In x pre → (x <= p)%Z) → (∀ x, In x post → (p < x)%Z) →
    sorted (pre ++ p :: post).
  Proof.
    intros Spre Spost ppre ppost.
    induction pre => /=.
    - apply SSorted_cons, List.Forall_forall => // ; intros.
      by apply Z.lt_le_incl, ppost.
    - apply SSorted_cons, List.Forall_forall => // ; [| clear IHpre].
      { apply IHpre.
        * apply StronglySorted_inv in Spre. by destruct Spre.
        * intros. apply ppre. set_solver. }
      intros x xppp.
      destruct (in_app_or _ _ _ xppp) as [x_pre | x_post] ; clear xppp.
      + apply StronglySorted_inv in Spre. destruct Spre.
        by apply (List.Forall_forall _ pre).
      + assert (a ≤ p)%Z as ap by (apply ppre ; constructor => //).
        assert (∀ z, In z (p::post) -> (p ≤ z)%Z) as ppost' ; last first.
        { etrans => //. apply ppost' => //. }
        intros z hz.
        destruct (in_inv hz) as [-> | zpost] => //.
        apply Z.lt_le_incl, ppost => //.
  Qed.

  Lemma qs_sorted : ∀ (xs : list Z) (l : val),
    {{{ ⌜is_list xs l⌝ }}}
      qs l
    {{{ v, RET v; ∃ xs', ⌜ is_list xs' v ∧ xs' ≡ₚ xs ∧ sorted xs' ⌝ }}}.
  Proof.
    iLöb as "Hqs". iIntros (xs l φ hl) "hφ".
    unfold qs at 2. wp_pures. fold qs.
    wp_bind (list_length _). iApply (wp_list_length $! hl).
    iIntros "!>" (n) "->". wp_pures.
    case_bool_decide as hn ; wp_pures.
    (* A list of length ≤ 1 is already sorted. *)
    { iApply "hφ". iExists xs. iPureIntro. intuition auto.
      destruct xs as [|x xs]; [|destruct xs as [|y zs]].
      - constructor.            (* [] is sorted. *)
      - do 2 constructor.       (* [x] is sorted. *)
      - cbn in hn. lia.         (* If len xs ≤ 1 then xs can't be x::y::zs. *)
    }
    (* pick a pivot index at random *)
    wp_apply wp_rand. 1: auto. iIntros (ip) "_". wp_pures.
    (* pop the pivot from xs *)
    wp_apply (wp_remove_nth_unsafe _ xs l ip).
    { iPureIntro. split => //. apply (Nat.lt_le_trans _ _ _ (fin_to_nat_lt ip)).
      destruct xs => /= ; simpl in hn ; lia. }
    iIntros (pr_opt (p & r & pre & post & hpart & hpos & hpr & hr)).
    rewrite hpr.
    repeat (wp_pure ; unfold partition ; progress fold partition).
    (* partition xs \ p into smaller and larger elements *)
    wp_apply Partition => //.
    iIntros (le gt (xsle & xsgt & (hle & hgt & hperm) & ple & pgt)). wp_pures.
    (* sort xs_gt *)
    wp_apply "Hqs" => //. iIntros (gts (xs_gt_s & Lgts & Pgts & Sgts)).
    (* sort xs_le *)
    wp_apply "Hqs" => //. iIntros (les (xs_le_s & Lles & Ples & Sles)). wp_pures.
    (* re-assemble the sorted results *)
    replace (#p) with (inject p) by auto.
    wp_apply wp_list_cons => //. iIntros (p_xs_gt_s h_p_xs_gt).
    iApply wp_list_append => //. iIntros "!>" (xs_le_p_gt_s L).
    iApply "hφ".
    iExists (xs_le_s ++ p :: xs_gt_s). iPureIntro. repeat split => //.
    - clear -Ples Pgts hperm hpart.
      rewrite Pgts Ples. rewrite -Permutation_middle.
      rewrite hperm. rewrite Permutation_middle. rewrite -hpart. done.
    - clear -Sles Sgts ple pgt Ples Pgts. apply sorted_append => // ; intros.
      + apply ple. eapply Permutation_in => //.
      + apply pgt. eapply Permutation_in => //.
  Qed.

End quicksort.
