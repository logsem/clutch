From clutch.prob_lang Require Import lang notation tactics metatheory.
From clutch.eris Require Export eris.
From clutch.eris.lib Require Export list.
From clutch.common Require Import inject.
Set Default Proof Using "Type*".

(*
Section lib_code.

  Context `{!erisGS Σ}.
  Context `[!Inject A val].

  Fixpoint is_list (l : list A) (v : val) :=
    match l with
    | [] => v = NONEV
    | a::l' => ∃ lv, v = SOMEV ((inject a), lv) ∧ is_list l' lv
  end.

  (** list library*)
  Definition list_nil := NONE.

  Notation "[ ]" := (list_nil) (format "[ ]") : expr_scope.

  Definition list_cons : val := λ: "elem" "list", SOME ("elem", "list").

  Infix "::" := list_cons (at level 60, right associativity) : expr_scope.

  Notation "[ x ]" := (list_cons x list_nil) (format "[ x ]") : expr_scope.

  Notation "[ x ; y ; .. ; z ]" := (list_cons x (list_cons y .. (list_cons z list_nil) ..)) : expr_scope.

  Definition list_nth : val :=
    rec: "list_nth" "l" "i" :=
      match: "l" with
        SOME "a" =>
          (if: "i" = #0
           then  SOME (Fst "a")
           else  "list_nth" (Snd "a") ("i" - #1))
      | NONE => NONE
      end.


  Definition list_tail : val :=
    λ: "l", match: "l" with
              SOME "a" => Snd "a"
            | NONE => NONE
            end.



  Definition list_update : val :=
    rec: "list_update" "l" "i" "v" :=
      match: "l" with
        SOME "a" =>
          (if: "i" = #0
           then  "v" :: list_tail "l"
           else  Fst "a" :: "list_update" (Snd "a") ("i" - #1) "v")
      | NONE => []
      end.

 
  Definition list_length : val :=
    rec: "list_length" "l" :=
      match: "l" with
        SOME "a" => #1 + ("list_length" (Snd "a"))
      | NONE => #0
      end.

  Definition list_swap: val :=
    λ: "l" "i" "j",
      let: "temp" := (match: list_nth "l" "j" with
                      |SOME "x" => "x"
                      |NONE => #()
                      end
                     )
      in
      let: "l'" := list_update "l" "j"
                     (match: list_nth "l" "i" with
                      |SOME "x" => "x"
                      |NONE => #()
                      end
                     )  in
      list_update "l'" "i" "temp".
 

  (** spec*)

  Lemma wp_list_cons a l lv E :
    {{{ ⌜is_list l lv⌝ }}}
      list_cons (inject a) lv @ E
      {{{ v, RET v; ⌜is_list (a::l) v⌝}}}.
  Proof.
    iIntros (Φ) "% HΦ". wp_lam. wp_pures.
    iApply "HΦ". iPureIntro; by eexists.
  Qed.

  Lemma wp_list_nth E (i: nat) l lv  :
    {{{ ⌜is_list l lv⌝ }}}
      list_nth (Val lv) #i @ E
      {{{ v, RET v; (⌜v = NONEV⌝ ∧ ⌜length l <= i⌝) ∨
                      ⌜∃ r, v = SOMEV (inject r) ∧ l!! i = Some r⌝ }}}.
  Proof.
    iIntros (Φ) "Ha HΦ".
    iInduction l as [|a l'] "IH" forall (i lv Φ);
      iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_rec; wp_let.
    - wp_match. wp_pures.
      iApply ("HΦ" $! (InjLV #())). iLeft. simpl. eauto with lia.
    - destruct Ha as [lv' [Hlv Hlcoh]]; subst.
      wp_match. wp_pures. case_bool_decide; wp_pures.
      + iApply "HΦ". iRight. simpl. iExists a. by destruct i.
      + destruct i; first done.
        assert ((S i - 1)%Z = i) as -> by lia.
        iApply ("IH" $! i lv' _  Hlcoh).
        iNext. iIntros (v [ (Hv & Hs) | Hps]); simpl.
        * iApply "HΦ"; try eauto with lia.
        * iApply "HΦ"; try eauto with lia.
  Qed.

  Lemma wp_list_nth_some E (i: nat) l lv  :
    {{{  ⌜is_list l lv ∧ i < length l⌝  }}}
      list_nth (Val lv) #i @ E
    {{{ v, RET v; ⌜∃ r, v = SOMEV (inject r) ∧  l!! i = Some r⌝ }}}.
  Proof.
    iIntros (Φ (Hcoh & Hi)) "HΦ".
    iApply (wp_list_nth $! Hcoh).
    iIntros (v [H | H]); first eauto with lia.
    by iApply "HΦ".
  Qed.

  Lemma wp_list_tail E lv l :
    {{{ ⌜is_list l lv⌝ }}}
      list_tail lv @ E
    {{{ v, RET v; ⌜is_list (tail l) v⌝}}}.
  Proof.
    iIntros (Φ a) "HΦ".
    wp_lam. destruct l; simpl in *; subst.
    - wp_match. wp_inj. by iApply "HΦ".
    - destruct a as [lv' [Hhead Htail]] eqn:Heq; subst.
      wp_match. wp_proj. by iApply "HΦ".
  Qed.

  Lemma wp_list_update E l lv a i:
    {{{ ⌜is_list l lv⌝ ∗ ⌜i<length l⌝ }}}
    list_update lv #i (inject a)@E
    {{{ v, RET v; ⌜is_list (<[i:=a]>l) v⌝}}}.
  Proof.
    iIntros (Φ) "[%Hv %Hlen] HΦ".
    iInduction l as [|x l'] "IH" forall (i a lv Hv Hlen Φ).
    { simpl in Hlen. lia. }
    rewrite /list_update. wp_pures.
    destruct Hv as [? [-> Hv]]. wp_pures.
    case_bool_decide as H.
    - wp_pures. wp_apply wp_list_tail.
      { iPureIntro. instantiate (1:=x::l'). naive_solver. }
       iIntros (v) "%". wp_apply wp_list_cons; first done.
      iIntros. iApply "HΦ". iPureIntro.
      assert (i=0) as ->.
      { inversion H. lia. } naive_solver.
    - rewrite -/list_update. wp_pures.
      assert (i≠0) by (intro; naive_solver).
      replace (_-_)%Z with (Z.of_nat (i-1)) by lia.
      wp_apply "IH"; [done|..].
      { iPureIntro. simpl in Hlen. lia. }
      iIntros. wp_pures. wp_apply wp_list_cons; first done.
      iIntros. iApply "HΦ".
      iPureIntro.
      replace (x::l') with ([x]++l') by done.
      replace i with (length ([x]) + (i-1)) by (simpl;lia).
      rewrite insert_app_r. naive_solver.
  Qed.

  Lemma wp_list_length E l lv :
    {{{ ⌜is_list l lv⌝ }}}
      list_length lv @ E
    {{{ v, RET #v; ⌜v = length l⌝ }}}.
  Proof.
    iIntros (Φ) "Ha HΦ".
    iInduction l as [|a l'] "IH" forall (lv Φ);
    iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_rec.
    - wp_match. iApply ("HΦ" $! 0%nat); done.
    - destruct Ha as [lv' [Hlv Hlcoh]]; subst.
      wp_match. wp_proj. wp_bind (list_length _).
      iApply ("IH" $! _ _ Hlcoh). iNext. iIntros; simpl.
      wp_op. iSpecialize ("HΦ" $! (1 + v)%nat).
      rewrite Nat2Z.inj_add. iApply "HΦ"; by auto.
  Qed.

  Lemma wp_list_swap E l lv i j:
    {{{ ⌜is_list l lv⌝ ∗ ⌜i<length l⌝ ∗ ⌜j<length l⌝ }}}
      list_swap lv #i #j@E
      {{{ lv', RET lv'; ∃ x y, ⌜l!!i= Some x⌝ ∗ ⌜l!!j=Some y⌝ ∗
                               ⌜is_list (<[i:=y]>(<[j:=x]>l)) lv'⌝ }}}.
  Proof.
    iIntros (Φ) "(%&%&%) HΦ".
    rewrite /list_swap.
    wp_pures.
    wp_apply wp_list_nth_some.
    { iPureIntro. split; first done. lia. }
    iIntros (?) "(%&->&%)".
    wp_pures.
    wp_apply wp_list_nth_some.
    { iPureIntro. done. }
    iIntros (?) "(%&->&%H')".
    wp_pures.
    wp_apply wp_list_update.
    { iPureIntro. split; first done. lia. }
    iIntros (lv' ?). wp_pures.
    wp_apply wp_list_update.
    { iPureIntro. split; first done. rewrite insert_length. lia. }
    iIntros (lv'' ?).
    iApply "HΦ".
    iExists _, _.
    by repeat iSplit.
  Qed.

End lib_code.
*)

Section fisher_yates.

  Context `{!erisGS Σ}.
  Context `[!Inject A val].

  (*
  Local Lemma Rlog_mult: ∀ x y : R, (0 < x)%R → (0 < y)%R → Rlog 2 (x * y) = (Rlog 2 x + Rlog 2 y)%R.
  Proof.
    intros x y Hx Hy.
    rewrite /Rlog.
    rewrite -Rdiv_plus_distr. f_equal.
    rewrite ln_mult; done.
  Qed.

  Local Lemma cost_rand (n:nat): cost (rand #n)%E= Rlog 2 (n+1). 
  Proof.
    simpl. f_equal.
    rewrite Zabs2Nat.id. case_match; simpl; lra.
  Qed.
  *)

  Definition fisher_yates_loop: val :=
    (rec: "loop" "l" "i" :=
                 if: "i" ≤ #0
                 then "l"
                 else let: "j" := rand ("i") in
                      let: "l'" := list_swap "l" "i" "j" in
                      "loop" "l'" ("i"-#1)
              ).

  Definition fisher_yates: val:=
    λ: "l", let: "i" := list_length "l" - #1 in
            fisher_yates_loop "l" "i".

  (*
  Lemma permutation_insert_delete `{Inject A val} (l : list A) (i : nat) (x : A) :
    i < length l ->
    <[i := x]> l ≡ₚ x :: delete i l.
  Proof.
    intros Hi.
    assert (delete i l = delete i (insert i x l)) as Haux.
    {
      revert i Hi.
      induction l;
        intros i Hi; auto.
      destruct i; simpl; auto.
      f_equal.
      apply IHl.
      simpl in Hi.
      lia.
    }
    rewrite Haux.
    etrans; last first.
    - apply delete_Permutation.
      by apply list_lookup_insert.
    - done.
  Qed.
  *)

  Lemma permutation_insert_swap {B : Type} (l : list B) (i j : nat) (x y : B) :
    l !! i = Some x ->
    l !! j = Some y ->
    l ≡ₚ (<[i := y]>(<[j := x]> l)).
  Proof.
    intros Hi Hj.
    pose proof (lookup_lt_Some _ _ _ Hi) as Hlen1.
    pose proof (lookup_lt_Some _ _ _ Hj) as Hlen2.
    erewrite <- (list_insert_id l j) at 1; eauto.
    erewrite <- (list_insert_id l i) at 1; eauto.
    clear Hi Hj.
    revert x y i j Hlen1 Hlen2.
    induction l; intros x y i j Hlen1 Hlen2; auto.
    destruct i as [|i']; destruct j as [|j']; auto.
    - simpl; auto.
      simpl in Hlen2.
      rewrite insert_take_drop; [|lia].
      rewrite insert_take_drop; [|lia].
      rewrite Permutation_middle.
      rewrite Permutation_middle.
      rewrite Permutation_swap //.
    - simpl; auto.
      simpl in Hlen1.
      rewrite insert_take_drop; [|lia].
      rewrite insert_take_drop; [|lia].
      rewrite Permutation_middle.
      rewrite Permutation_middle.
      rewrite Permutation_swap //.
    - simpl.
      simpl in Hlen1.
      simpl in Hlen2.
      rewrite IHl; auto; lia.
Qed.



  Lemma wp_fisher_yates_loop E l lav lv i:
    l ≡ₚ lav ->
      {{{ ⌜is_list l lv ⌝ ∗ ⌜i<length l⌝ ∗ ⌜ NoDup l ⌝ ∗
          (↯ (1/ fact (i+1)) ∨ ⌜drop (S i) l ≠ drop (S i) lav ⌝)  }}}
      fisher_yates_loop lv #i@E
      {{{ v, RET v; ∃ l', ⌜is_list l' v⌝ ∗ ⌜l' ≡ₚ l⌝ ∗ ⌜l' ≠ lav⌝ }}}.
  Proof.
    iIntros (Hperm Φ) "(%Hl&%Hlen&%Hdup&Herr) HΦ".
    iInduction i as [|i'] "IH" forall (l lav lv Φ Hperm Hl Hlen Hdup) "Herr HΦ"; rewrite /fisher_yates_loop; wp_pures.
    { iModIntro. iApply "HΦ".
      iDestruct "Herr" as "[Herr | %Hdiff]".
      - iDestruct (ec_contradict with "[Herr]") as "?"; auto.
        simpl; lra.
      - iExists l.
        iSplit; auto.
        iSplit; auto.
        iPureIntro.
        by intros ->.
    }
    iDestruct "Herr" as "[Herr | %Hdiff]".
    - set (j := list_find (λ y, bool_decide (lav !! i' = Some y)) l).
      assert (is_Some j) as [ [k a] Hk].
      {
        rewrite /j.
        epose proof (lookup_lt_is_Some_2 lav i' _) as [y Hy].
        eapply list_find_elem_of; last first.
        - by apply bool_decide_spec.
        - apply elem_of_list_lookup_2 in Hy.
          rewrite Hperm //.
      }
      wp_apply (wp_rand_err_amp_nat _ _ k); iFrame.
      iIntros (x) "(%Hnleq & [%Hneq | Herr])".
      + wp_pures.
        wp_apply wp_list_swap.
        { repeat iSplit; try done. iPureIntro.
          lia.
        }
      iIntros (lv') "(%&%&%H1&%H2&%)".
      do 3 wp_pure.
      replace (_-_)%Z with (Z.of_nat i'); last lia.
      wp_apply ("IH" $! (<[S i':=y]> (<[x:=x0]> l)) lav with "[][][][]").
      * iPureIntro.
        transitivity l; auto.
        symmetry.
        by apply permutation_insert_swap.
      * auto.
      * rewrite !insert_length. iPureIntro.
        lia.
      * iPureIntro.
        rewrite -(permutation_insert_swap l (S i') x x0 y H1 H2) //.
      * iRight. iPureIntro.
        admit.
      * iIntros (?) "(%&%&%&%)".
        iApply "HΦ".
        iExists l'. iPureIntro; split; first done. admit.
        (*
        etrans; first exact.
        rewrite Permutation_inj. split.
        { rewrite !insert_length. lia. }
        exists (λ x, if (bool_decide (x=fin_to_nat n)) then (S i')
                else if (bool_decide (x=S i')) then (fin_to_nat n)
                     else x
          ).
        split.
        + intros ??. repeat case_bool_decide; simpl; naive_solver.
        + intros. repeat case_bool_decide; subst.
          * destruct (decide (fin_to_nat n=S i')) as [Heq|Heq].
            -- rewrite Heq in H2. rewrite Heq. rewrite list_lookup_insert; first naive_solver.
               rewrite !insert_length. lia.
            -- rewrite list_lookup_insert_ne; last done. rewrite list_lookup_insert; first naive_solver.
               pose proof fin_to_nat_lt n. lia.
          * rewrite list_lookup_insert; first naive_solver.
            rewrite insert_length. lia.
          * repeat (rewrite list_lookup_insert_ne; last done). done.
          *)
      + wp_pures.
        wp_apply wp_list_swap.
        { repeat iSplit; try done. iPureIntro.
          lia.
        }
      iIntros (lv') "(%&%&%H1&%H2&%)".
      do 3 wp_pure.
      replace (_-_)%Z with (Z.of_nat i'); last lia.
      wp_apply ("IH" $! (<[S i':=y]> (<[x:=x0]> l)) lav with "[][][][][Herr]").
      * admit.
      * admit.
      * rewrite !insert_length. iPureIntro.
        admit.
      * admit.
      * iLeft.
        admit.
      * iIntros (?) "(%&%&%&%)".
        iApply "HΦ".
        iExists l'. iPureIntro; split; first done. admit.
    - wp_apply wp_rand; auto.
      iIntros (n) "?".
      wp_pures.
      wp_apply wp_list_swap.
      { repeat iSplit; try done. iPureIntro.
        pose proof fin_to_nat_lt n. lia. }
      iIntros (lv') "(%&%&%H1&%H2&%)".
      do 3 wp_pure.
      replace (_-_)%Z with (Z.of_nat i'); last lia.
      wp_apply ("IH" $! (<[S i':=y]> (<[fin_to_nat n:=x]> l)) lav with "[][][][]").
      * iPureIntro.
        rewrite -Hperm.
        rewrite (insert_take_drop _ n); [|admit].
        rewrite (insert_take_drop); [|admit].

        **
        auto.
        admit.
      * admit.
      * admit.
      * admit.
      * iRight.
        iPureIntro.
  Admitted.



  Lemma wp_fisher_yates E l lav lv:
    l ≡ₚ lav ->
    {{{ ⌜is_list l lv ⌝ ∗ ⌜NoDup l⌝ ∗ ↯ (1/ (fact (length l)))}}}
      fisher_yates lv @E
      {{{ v, RET v; ∃ l', ⌜is_list l' v⌝ ∗ ⌜l' ≡ₚ l⌝ ∗ ⌜l' ≠ lav⌝ }}}.
  Proof.
    iIntros (Hperm Φ) "[% [% Hx]] HΦ".
    rewrite /fisher_yates.
    wp_pures.
    wp_apply wp_list_length; first done.
    iIntros (? ->).
    wp_pures.
    destruct (decide (length l = 0)) as [->|].
    { rewrite /fisher_yates_loop. wp_pures.
      rewrite /= Rdiv_1_r.
      iDestruct (ec_contradict with "Hx") as "?"; auto.
      lra.
    }
    replace (_-_)%Z with (Z.of_nat (length l - 1)) by lia.
    wp_apply (wp_fisher_yates_loop with "[Hx]"); last done; auto.
    repeat iSplit; try done.
    { iPureIntro. lia. }
    iLeft.
    replace (length l - 1 + 1) with (length l) by lia.
    iFrame.
  Qed.



End fisher_yates.
