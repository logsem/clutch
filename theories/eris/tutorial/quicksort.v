(** We prove functional correctness of randomised quicksort. *)

From stdpp Require Import sorting.
From clutch.common Require Import inject.
From clutch.eris Require Import eris.
From clutch.eris.lib Require Import list.
Set Default Proof Using "Type*".

Local Notation sorted := (StronglySorted Z.le).

Section quicksort.

  Context `{!erisGS Σ}.

  (** We define two recursive functions on list:
      - [partition l e] splits [l] into elements smaller than or larger than [e]
      - [qs l] sorts [l], using [partition] as sub-procedure xx *)
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

  (** Auxiliary lemmas about sorting, partitioning, and permutations. *)
  Lemma filter_split_perm {A} (l : list A) f :
    l ≡ₚ List.filter f l ++ List.filter (fun x=>negb (f x)) l.
  Proof.
    induction l as [|a l IHl] => // /=.
    destruct (f a) => /= ; rewrite -?Permutation_middle -IHl //.
  Qed.

  Fact sorted_append pre post p :
    sorted pre → sorted post →
    (∀ x, In x pre → (x <= p)%Z) → (∀ x, In x post → (p < x)%Z) →
    sorted (pre ++ p :: post).
  Proof.
    intros Spre Spost ppre ppost. apply StronglySorted_app. repeat split ; auto.
    - intros x1 x2 x1pre x2post. trans p.
      + apply ppre, elem_of_list_In ; auto.
      + apply elem_of_list_In in x2post.
        destruct (in_inv x2post) as [-> | zpost] => //.
        apply Z.lt_le_incl, ppost => //.
    - apply SSorted_cons, List.Forall_forall => // ; intros.
      apply Z.lt_le_incl, ppost. assumption.
  Qed.

  (** This specification formalizes the intuition for [partition]. This is just
      standard separation logic reasoning, the probabilistic part of Eris does
      not interfere. xx *)
  Lemma Partition (xs : list Z) (l_xs : val) (e : Z) :
    {{{ ⌜is_list xs l_xs⌝ }}}
      partition l_xs (Val #e)
    {{{ le gt, RET (le, gt);
        ∃ xsle xsgt : list Z,
          ⌜is_list xsle le ∧ is_list xsgt gt
          ∧ xsle ++ xsgt ≡ₚ xs ⌝
          ∧ ⌜ ∀ x, In x xsle → (x ≤ e)%Z ⌝
                   ∧ ⌜ ∀ x, In x xsgt → (e < x)%Z ⌝
    }}}.
  Proof.
    iIntros (post Lxs) "Hpost".
    unfold partition.
    wp_pures.
    (* filter the xs greater than e *)
    wp_apply (wp_list_filter xs (λ x, bool_decide (e < x)%Z)).
    { iSplit ; auto. iIntros (x ψ) "_ !> hψ".
      simpl. wp_pures. iApply "hψ". done. }
    iIntros (l_xs_gt H_xs_gt). wp_pures.
    (* filter the xs smaller/equal to e *)
    wp_apply (wp_list_filter _ (λ x, negb $ bool_decide (e < x)%Z)).
    { iSplit => //. iIntros (x ψ) "_ !> hψ".
      simpl. wp_pures.
      case_bool_decide ; wp_pures ; by iApply "hψ". }
    iIntros (l_xs_le H_xs_le).
    (* prove the postcondition from the facts we know about xs_le and xs_gt *)
    wp_pures. iApply "Hpost". iPureIntro.
    set (xs_gt := (List.filter (λ x : Z, bool_decide (e < x)%Z) xs)) in *.
    set (xs_le := (List.filter (λ x : Z, negb $ bool_decide (e < x)%Z) xs)) in *.
    exists xs_le, xs_gt.
    repeat split ; auto.
    (* the result is a permutation of the input *)
    - rewrite Permutation_app_comm. rewrite -filter_split_perm. reflexivity.
    (* xs_le are indeed smaller than e *)
    - intros x H. epose proof (filter_In _ x xs) as [h _]. destruct (h H) as [_ hle].
      destruct (bool_decide (e < x)%Z) eqn:hlt => //.
      apply bool_decide_eq_false in hlt.
      apply Z.nlt_ge. done.
    (* xs_gt are indeed larger than e *)
    - intros x H. epose proof (filter_In _ x xs) as [h _]. destruct (h H) as [_ hgt].
      by apply bool_decide_eq_true in hgt.
  Qed.

  (** We can prove that [qs] indeed sorts. *)
  Lemma qs_sorted : ∀ (xs : list Z) (l : val),
    {{{ ⌜is_list xs l⌝ }}}
      qs l
    {{{ v, RET v; ∃ xs', ⌜ is_list xs' v ∧ xs' ≡ₚ xs ∧ sorted xs' ⌝ }}}.
  Proof.
    (** Set up the recursion. xx *)
    iLöb as "Hqs". iIntros (xs l φ hl) "hφ".
    unfold qs at 2. wp_pures. fold qs.
    wp_bind (list_length _). iApply (wp_list_length $! hl).
    iIntros "!>" (n) "->". wp_pures.
    (** The definition of quicksort cases on the length of [l]. xx *)
    case_bool_decide as hn ; wp_pures.
    { (** A list of length ≤ 1 is already sorted. xx **)
      iApply "hφ". iExists xs. iPureIntro. intuition auto.
      destruct xs as [|x xs]; [|destruct xs as [|y zs]].
      - constructor.            (* [] is sorted. *)
      - do 2 constructor.       (* [x] is sorted. *)
      - simpl in hn. lia.       (* If len xs ≤ 1 then xs can't be x::y::zs. *)
    }
    (** Otherwise, we pick a pivot index [ip] at random xx *)
    wp_apply wp_rand ; [done|]. iIntros (ip) "_". wp_pures.
    (** Next, we pop the pivot at index [ip] from [l] xx *)
    wp_apply (wp_remove_nth_unsafe _ xs l ip).
    { iPureIntro. split => //. apply (Nat.lt_le_trans _ _ _ (fin_to_nat_lt ip)).
      destruct xs => /= ; simpl in hn ; lia. }
    iIntros (pr_opt (p & r & pre & post & hpart & hpos & hpr & hr)).
    rewrite hpr.
    repeat (wp_pure ; unfold partition ; progress fold partition).
    (** We partition xs \ p into smaller and larger elements xx *)
    wp_apply Partition => //.
    iIntros (le gt (xs_le & xs_gt & (hle & hgt & hperm) & ple & pgt)). wp_pures.
    (** Recursive call: sort xs_gt xx *)
    wp_apply "Hqs" => //. iIntros (gts (xs_gt_sorted & Lgts & Pgts & Sgts)).
    (** Recursive call: sort xs_le *)
    wp_apply "Hqs" => //. iIntros (les (xs_le_sorted & Lles & Ples & Sles)). wp_pures.
    (** Finally, re-assemble the sorted results xx *)
    replace (#p) with (inject p) by auto.
    wp_apply wp_list_cons => //. iIntros (p_xs_gt_sorted h_p_xs_gt).
    iApply wp_list_append => //. iIntros "!>" (xs_le_p_gt_s L).
    iApply "hφ".
    (** The result is indeed sorted. xx *)
    iExists (xs_le_sorted ++ p :: xs_gt_sorted). iPureIntro. repeat split => //.
    - clear -Ples Pgts hperm hpart.
      rewrite Pgts Ples. rewrite -Permutation_middle.
      rewrite hperm. rewrite Permutation_middle. rewrite -hpart. reflexivity.
    - clear -Sles Sgts ple pgt Ples Pgts. apply sorted_append => // ; intros.
      + apply ple. eapply Permutation_in => //.
      + apply pgt. eapply Permutation_in => //.
  Qed.

End quicksort.
