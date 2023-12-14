(* We prove functional correctness of randomised quicksort. Since this is a
   unary property, we work in the UB logic, which has the appropriate adequacy
   theorem. *)

From stdpp Require Import sorting.
From clutch.lib Require Import utils.
From clutch.ub_logic Require Import ub_clutch lib.list.
Set Default Proof Using "Type*".

Section quicksort.

  Import list.

  Context `{!ub_clutchGS Σ}.

  Definition list_remove_nth_unsafe : val :=
    λ:"l" "n",
    match: list_remove_nth "l" "n" with
    | NONE => #()
    | SOME "v" => "v"
    end.

  Definition partition : expr :=
    let: "negb" := λ:"b", if: "b" then #false else #true in
    λ:"l" "e",
      let: "f" := (λ:"x", "e" < "x") in
      (list_filter (λ:"x", "negb" ("f" "x") ) "l",
        list_filter "f" "l").

  Definition qs : val :=
    rec: "qs" "l" :=
      let: "n" := list_length "l" in
      if: "n" < #1 then "l" else
        let: "ip" := rand ("n" - #1) from #() in
        let, ("p", "r") := list_remove_nth_unsafe "l" "ip" in
        let, ("le", "gt") := partition "r" "p" in
        let, ("les", "gts") := ("qs" "le", "qs" "gt") in
        list_append "les" (list_cons "p" "gts").


  Lemma wp_remove_nth_unsafe {A} [_ : Inject A val] E (l : list A) (lv : val) (i : nat) :
    {{{ ⌜ is_list l lv /\ i < length l ⌝ }}}
      list_remove_nth_unsafe lv #i @ E
    {{{ v, RET v;
        ∃ e lv' l1 l2,
          ⌜ l = l1 ++ e :: l2 ∧
          length l1 = i /\
          v = ((inject e), lv')%V ∧
          is_list (l1 ++ l2) lv' ⌝ }}}.
  Proof.
    iIntros (φ (llv & il)) "hφ".
    rewrite /list_remove_nth_unsafe. wp_pures.
    wp_apply wp_remove_nth => //.
    iIntros (?(?&?&?&?&?&?&?&?)) ; subst. wp_pures.
    iApply "hφ". iModIntro. iExists _,_,_,_. intuition eauto.
  Qed.

  Lemma filter_split_perm {A} (l : list A) f :
    l ≡ₚ List.filter f l ++ List.filter (fun x=>negb (f x)) l.
  Proof.
    induction l as [|a l IHl] => // /=.
    destruct (f a) => /= ; rewrite -?Permutation_middle -IHl //.
  Qed.

  Lemma Partition (xs : list Z) l (e : Z) e' :
    e' = Val #e ->
    {{{ ⌜is_list xs l⌝ }}}
      partition l e'
    {{{ le gt, RET (le, gt);
        ∃ xsle xsgt : list Z,
          ⌜is_list xsle le ∧ is_list xsgt gt
          ∧ app xsle xsgt ≡ₚ xs ⌝
          ∧ ⌜ ∀ x, In x xsle → (x ≤ e)%Z ⌝
                   ∧ ⌜ ∀ x, In x xsgt → (e < x)%Z ⌝
    }}}.
  Proof.
    iIntros (-> φ Lxs) "hφ".
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
  Proof with wp_pures.
    iLöb as "Hqs". iIntros (xs l φ hl) "hφ".
    rewrite {2}/qs... rewrite -/qs.
    wp_bind (list_length _). iApply (wp_list_length $! hl).
    iIntros "!>" (n) "->"...
    case_bool_decide as hn...
    (* an empty or singleton list is already sorted. *)
    { iApply "hφ". iExists xs. iPureIntro. intuition auto.
      destruct xs => //. 1: constructor. destruct xs => //. simpl in hn. lia. }
    (* pick a pivot index at random *)
    wp_apply wp_rand => //. iIntros (ip) "_"...
    (* pop the pivot from xs *)
    wp_apply (wp_remove_nth_unsafe _ xs l ip).
    { iPureIntro. split => //. apply (Nat.lt_le_trans _ _ _ (fin_to_nat_lt ip)).
      destruct xs => /= ; simpl in hn ; lia. }
    iIntros (pr_opt (p & r & pre & post & hpart & hpos & hpr & hr)).
    rewrite hpr. repeat (wp_pure ; unfold partition ; progress fold partition).
    (* partition xs \ p into smaller and larger elements *)
    wp_apply Partition => //.
    iIntros (le gt (xsle & xsgt & (hle & hgt & hperm) & ple & pgt))...
    (* sort xs_gt *)
    wp_apply "Hqs" => //. iIntros (gts (xs_gt_s & Lgts & Pgts & Sgts)).
    (* sort xs_le *)
    wp_apply "Hqs" => //. iIntros (les (xs_le_s & Lles & Ples & Sles))...
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
