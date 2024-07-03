From clutch.common Require Import inject.
From clutch Require Import paris.

From clutch.paris.examples Require Export map.
Set Default Proof Using "Type*".

Section list_code.
Definition list_nil := NONE.

Notation "[ ]" := (list_nil) (format "[ ]") : expr_scope.

Definition list_cons : val := λ: "elem" "list", SOME ("elem", "list").

Infix "::" := list_cons (at level 60, right associativity) : expr_scope.

Notation "[ x ]" := (list_cons x list_nil) (format "[ x ]") : expr_scope.

Notation "[ x ; y ; .. ; z ]" := (list_cons x (list_cons y .. (list_cons z list_nil) ..)) : expr_scope.

Definition list_head : val :=
  λ: "l", match: "l" with
    SOME "a" => SOME (Fst "a")
  | NONE => NONE
  end.

Definition list_tail : val :=
  λ: "l", match: "l" with
    SOME "a" => Snd "a"
  | NONE => NONE
  end.

Definition list_fold_right : val :=
  rec: "list_fold_right" "handler" "l" "acc" :=
  match: "l" with
     SOME "c" =>
     let: "hd" := Fst "c" in
     let: "tl" := Snd "c" in
     "handler" "hd" ("list_fold_right" "handler" "tl" "acc")
  |  NONE => "acc"
  end.

Definition list_fold : val :=
  rec: "list_fold" "handler" "acc" "l" :=
  match: "l" with
    SOME "a" =>
    let: "f" := Fst "a" in
    let: "s" := Snd "a" in
    let: "acc" := "handler" "acc" "f" in
    "list_fold" "handler" "acc" "s"
  | NONE => "acc"
  end.

Definition list_iter : val :=
  rec: "list_iter" "handler" "l" :=
  match: "l" with
    SOME "a" =>
    let: "tail" := Snd "a" in
    "handler" (Fst "a");;
    "list_iter" "handler" "tail"
  | NONE => #()
  end.

Definition list_iteri_loop : val :=
  rec: "list_iteri_loop" "handler" "i" "l" :=
  match: "l" with
    SOME "a" =>
    let: "tail" := Snd "a" in
    "handler" "i" (Fst "a");;
    "list_iteri_loop" "handler" ("i" + #1) "tail"
  | NONE => #()
  end.

Definition list_iteri : val :=
  λ: "handler" "l", list_iteri_loop "handler" #0 "l".

Definition list_mapi_loop : val :=
  rec: "list_mapi_loop" "f" "k" "l" :=
  match: "l" with
    SOME "a" =>
    "f" "k" (Fst "a") :: "list_mapi_loop" "f" ("k" + #1) (Snd "a")
  | NONE => NONE
  end.

Definition list_mapi : val := λ: "f" "l", list_mapi_loop "f" #0 "l".

Definition list_map : val :=
  rec: "list_map" "f" "l" :=
  match: "l" with
    SOME "a" => "f" (Fst "a") :: "list_map" "f" (Snd "a")
  | NONE => NONE
  end.

Definition list_filter : val :=
  rec: "list_filter" "f" "l" :=
  match: "l" with
    SOME "a" =>
    let: "r" := "list_filter" "f" (Snd "a") in
    (if: "f" (Fst "a")
     then  Fst "a" :: "r"
     else  "r")
  | NONE => NONE
  end.

Definition list_length : val :=
  rec: "list_length" "l" :=
  match: "l" with
    SOME "a" => #1 + ("list_length" (Snd "a"))
  | NONE => #0
  end.

Definition list_nth : val :=
  rec: "list_nth" "l" "i" :=
  match: "l" with
    SOME "a" =>
    (if: "i" = #0
     then  SOME (Fst "a")
     else  "list_nth" (Snd "a") ("i" - #1))
  | NONE => NONE
  end.

Definition list_mem : val :=
  rec: "list_mem" "x" "l" :=
  match: "l" with
    SOME "a" =>
    let: "head" := Fst "a" in
    let: "tail" := Snd "a" in
    ("x" = "head") || ("list_mem" "x" "tail")
  | NONE => #false
  end.


Definition list_remove_nth : val :=
  rec: "list_remove_nth" "l" "i" :=
    match: "l" with
    SOME "a" =>
      let: "head" := Fst "a" in
      let: "tail" := Snd "a" in
      (if: "i" = #0
         then SOME ("head", "tail")
         else
           let: "r" := "list_remove_nth" "tail" ("i" - #1) in
           match: "r" with
             SOME "b" =>
             let: "head'" := Fst "b" in
             let: "tail'" := Snd "b" in
             SOME ("head'", ("head" :: "tail'"))
           | NONE => NONE
           end)
    | NONE => list_nil
    end.

Definition list_remove_nth_total : val :=
  rec: "list_remove_nth_total" "l" "i" :=
    match: "l" with
    SOME "a" =>
    (if: "i" = #0
     then  Snd "a"
     else  (Fst "a") :: ("list_remove_nth_total" (Snd "a") ("i" - #1)))
    | NONE => list_nil
    end.

Definition list_find_remove : val :=
  rec: "list_find_remove" "f" "l" :=
  match: "l" with
    SOME "a" =>
    let: "head" := Fst "a" in
    let: "tail" := Snd "a" in
    (if: "f" "head"
     then  SOME ("head", "tail")
     else
       let: "r" := "list_find_remove" "f" "tail" in
       match: "r" with
         SOME "b" =>
         let: "head'" := Fst "b" in
         let: "tail'" := Snd "b" in
         SOME ("head'", ("head" :: "tail'"))
       | NONE => NONE
       end)
  | NONE => NONE
  end.

Definition list_sub : val :=
  rec: "list_sub" "i" "l" :=
  (if: "i" ≤ #0
   then  []
   else
     match: "l" with
      SOME "a" => Fst "a" :: "list_sub" ("i" - #1) (Snd "a")
    | NONE => []
    end).

Definition list_rev_aux : val :=
  rec: "list_rev_aux" "l" "acc" :=
  match: "l" with
    NONE => "acc"
  | SOME "p" =>
      let: "h" := Fst "p" in
      let: "t" := Snd "p" in
      let: "acc'" := "h" :: "acc" in
      "list_rev_aux" "t" "acc'"
  end.

Definition list_rev : val := λ: "l", list_rev_aux "l" [].

Definition list_append : val :=
  rec: "list_append" "l" "r" :=
  match: "l" with
    NONE => "r"
  | SOME "p" =>
      let: "h" := Fst "p" in
      let: "t" := Snd "p" in
      "h" :: "list_append" "t" "r"
  end.

Definition list_is_empty : val :=
  λ: "l", match: "l" with
    NONE => #true
  | SOME "_p" => #false
  end.

Definition list_forall : val :=
  rec: "list_forall" "test" "l" :=
  match: "l" with
    NONE => #true
  | SOME "p" =>
      let: "h" := Fst "p" in
      let: "t" := Snd "p" in
      ("test" "h") && ("list_forall" "test" "t")
  end.

Definition list_make : val :=
  rec: "list_make" "len" "init" :=
  (if: "len" = #0
   then  []
   else  "init" :: "list_make" ("len" - #1) "init").

Definition list_init : val :=
  λ: "len" "f",
  letrec: "aux" "acc" "i" :=
    (if: "i" = "len"
     then  list_rev "acc"
     else  "aux" (("f" "i") :: "acc") ("i" + #1)) in
    "aux" [] #0.


Definition list_seq : val :=
  rec: "list_seq" "st" "ln" :=
    (if: "ln" ≤ #0
     then  list_nil
     else  list_cons "st" ("list_seq" ("st" + #1)  ("ln" - #1))).

Definition list_update : val :=
  rec: "list_update" "l" "i" "v" :=
  match: "l" with
    SOME "a" =>
    (if: "i" = #0
     then  "v" :: list_tail "l"
     else  Fst "a" :: "list_update" (Snd "a") ("i" - #1) "v")
  | NONE => []
  end.

Definition list_suf : val :=
  rec: "list_suf" "i" "l" :=
  (if: "i" = #0
   then  "l"
   else
     match: "l" with
      NONE => NONE
    | SOME "p" => "list_suf" ("i" - #1) (Snd "p")
    end).

Definition list_inf_ofs : val :=
  λ: "i" "ofs" "l",
  (if: "ofs" ≤ #0
   then  []
   else  list_sub "ofs" (list_suf "i" "l")).

Definition list_inf : val :=
  λ: "i" "j" "l", list_inf_ofs "i" (("j" - "i") + #1) "l".

Definition list_split : val :=
  rec: "list_split" "i" "l" :=
  (if: "i" ≤ #0
   then  ([], "l")
   else
     match: "l" with
      NONE => ([], [])
    | SOME "p" =>
        let: "x" := Fst "p" in
        let: "tl" := Snd "p" in
        let: "ps" := "list_split" ("i" - #1) "tl" in
        ("x" :: Fst "ps", Snd "ps")
    end).
End list_code.

Fixpoint inject_list `{!Inject A val} (xs : list A) :=
  match xs with
  | [] => NONEV
  | x :: xs' => SOMEV ((inject x), inject_list xs')
  end.

Global Program Instance Inject_list `{!Inject A val} : Inject (list A) val :=
  {| inject := inject_list |}.
Next Obligation.
  intros ? [] xs. induction xs as [|x xs IH]; simpl.
  - intros []; by inversion 1.
  - intros []; [by inversion 1|].
    inversion 1 as [H'].
    f_equal; [by apply (inj _)|].
    by apply IH.
Qed.

Section list_specs.

  Context `{!parisGS Σ}.
  Context `[!Inject A val].

  Fixpoint is_list (l : list A) (v : val) :=
    match l with
    | [] => v = NONEV
    | a::l' => ∃ lv, v = SOMEV ((inject a), lv) ∧ is_list l' lv
  end.

  Lemma is_list_inject xs v :
    is_list xs v ↔ v = (inject xs).
  Proof.
    revert v.
    induction xs as [|x xs IH]; [done|]. split.
    - destruct 1 as (? & -> & ?). simpl.
      do 2 f_equal. by apply IH.
    - intros ->. eexists. split; [done|]. by apply IH.
  Qed.

  Lemma wp_list_nil E :
    {{{ True }}}
      list_nil @ E
    {{{ v, RET v; ⌜is_list [] v⌝}}}.
  Proof. iIntros (Φ) "_ HΦ". wp_pures. by iApply "HΦ". Qed.

  Lemma wp_list_cons a l lv E :
    {{{ ⌜is_list l lv⌝ }}}
      list_cons (inject a) lv @ E
    {{{ v, RET v; ⌜is_list (a::l) v⌝}}}.
  Proof.
    iIntros (Φ) "% HΦ". wp_lam. wp_pures.
    iApply "HΦ". iPureIntro; by eexists.
  Qed.

  Lemma spec_list_cons E K (a : A) (l : list A) lv :
    ⌜ is_list l lv ⌝ -∗
    ⤇ fill K (list_cons (inject a) lv) -∗
    spec_update E (∃ v, ⤇ fill K (of_val v) ∗ ⌜is_list (a :: l) v⌝).
  Proof.
    iIntros "%Hlist Hspec".
    tp_lam. tp_pures.
    iModIntro.
    iExists _.
    iFrame.
    iPureIntro; by eexists.
  Qed.

  Lemma wp_list_singleton E a :
    {{{ True }}}
      list_cons (inject a) list_nil @ E
    {{{ v, RET v; ⌜is_list [a] v⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_pures.
    wp_apply (wp_list_cons _ []); [done|].
    iIntros (v' Hv').
    by iApply "HΦ".
  Qed.

  Lemma wp_list_head E lv l :
    {{{ ⌜is_list l lv⌝ }}}
      list_head lv @ E
    {{{ v, RET v;
        ⌜(l = [] ∧ v = NONEV) ∨ (∃ a l', l = a :: l' ∧ v = SOMEV (inject a))⌝ }}}.
  Proof.
    iIntros (Φ a) "HΦ".
    wp_lam. destruct l; simpl in *; subst.
    - wp_pures. iApply "HΦ". iPureIntro. by left.
    - destruct a as [lv' [Hhead Htail]] eqn:Heq; subst.
      wp_pures. iApply "HΦ". iPureIntro. right. eauto.
  Qed.


  Lemma spec_list_head E lv l K:
    is_list l lv ->
    ⤇ fill K (list_head lv) -∗
    spec_update E
    (∃ v, ⤇ fill K v∗
       ⌜(l = [] ∧ v = NONEV) ∨ (∃ a l', l = a :: l' ∧ v = SOMEV (inject a))⌝ ).
  Proof.
    iIntros (a) "Hspec".
    rewrite /list_head.
    tp_pures. destruct l; simpl in *; subst.
    - tp_pures. iApply spec_update_ret. iFrame. iPureIntro. naive_solver.
    - destruct a as [lv' [Hhead Htail]] eqn:Heq; subst.
      tp_pures. iApply spec_update_ret. iFrame. iPureIntro. naive_solver.
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

  Lemma spec_list_tail E lv l K:
    is_list l lv ->
     ⤇ fill K (list_tail lv) -∗
     spec_update E
       (∃ (v:val), ⤇ (fill K v) ∗ ⌜is_list (tail l) v⌝).
  Proof.
    iIntros (a) "Hspec".
    rewrite /list_tail.
    tp_pures. destruct l; simpl in *; subst.
    - tp_pures. iApply spec_update_ret. iFrame. done.
    - destruct a as [lv' [Hhead Htail]] eqn:Heq; subst.
      tp_pures. iApply spec_update_ret. iFrame. done.
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

  Lemma spec_list_length K E l lv :
    ⌜ is_list l lv ⌝ -∗
    ⤇ fill K (list_length lv) -∗
    spec_update E (∃ v, ⤇ fill K (of_val v) ∗ ⌜v = inject (length l)⌝).
  Proof.
    iInduction l as [| a l'] "IH" forall (lv K);
    iIntros "%Hlist Hspec".
    - rewrite /list_length.
      tp_rec.
      apply is_list_inject in Hlist as ->.
      tp_pures.
      iModIntro.
      iExists _; iFrame.
      iPureIntro. done.
    - tp_lam.
      apply is_list_inject in Hlist as ->.
      tp_pure.
      fold inject_list.
      do 3 tp_pure.
      tp_bind (list_length _).
      (* iEval (rewrite ⤇ fill_bind) in "Hspec". *)
      iMod ("IH" $! _ _ _ with "Hspec") as (v) "[Hspec %Hv]".
      (* iEval (rewrite -⤇ fill_bind) in "Hspec". *)
      simpl.
      rewrite Hv.
      tp_op.
      iModIntro.
      iExists _; iFrame.
      iPureIntro.
      do 2 f_equal; lia.
      Unshelve. by apply is_list_inject.
   Qed.


  Lemma wp_list_iter_invariant' Φ1 Φ2 (Ψ: list A -> iProp Σ) P E l lv handler
         lrest:
    (∀ (a : A) l',
        {{{ ⌜∃ b, lrest ++ l = l' ++ a :: b⌝ ∗ P ∗ Ψ l' ∗ Φ1 a }}}
          (Val handler) (inject a) @ E
        {{{v, RET v; P ∗ Ψ (l' ++ [a]) ∗ Φ2 a }}}) -∗
    {{{ ⌜is_list l lv⌝ ∗ P ∗ Ψ lrest ∗ [∗ list] a∈l, Φ1 a}}}
      list_iter (Val handler) lv @ E
    {{{ RET #(); P ∗ Ψ (lrest++l) ∗ [∗ list] a∈l, Φ2 a }}}.
  Proof.
    rewrite /list_iter.
    iInduction l as [|a l'] "IH" forall (lv lrest);
    iIntros "#Helem"; iIntros (Φ') "!# (Ha & HP & Hl & HΦ) Hk";
    iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_pures.
    - rewrite app_nil_r. iApply "Hk"; iFrame. done.
    - assert (Helemof: a ∈ a :: l').
      { constructor. }
      destruct Ha as [lv' [Hlv Hlcoh]]; subst.
      wp_pures.
      iDestruct (big_sepL_cons with "HΦ") as "[Ha Hl']".
      wp_apply ("Helem" with "[HP Hl Ha]"); iFrame; eauto.
      iIntros (v) "(HP & Ha & HΦ)". simpl. wp_seq.
      iApply ("IH" $! lv' (lrest ++ [a]) with "[] [$HP Ha Hl']"); eauto.
      { iIntros (a' lrest' HΦ'') "!# (%Hin'&HP&Hlrest'&HΦ) Hk".
        wp_apply ("Helem" with "[HP Hlrest' HΦ]"); iFrame.
        iPureIntro. destruct Hin' as [b Hin']. exists b.
        by rewrite -app_assoc in Hin'. }
      { iSplit; eauto. iFrame. }
      iNext. iIntros "(HP & Hl)". iApply "Hk". iFrame.
        by rewrite -app_assoc /=.
  Qed.

  Lemma wp_list_iter_invariant Φ1 Φ2 (Ψ: list A -> iProp Σ) P E l lv handler :
    (∀ (a : A) l',
        {{{ ⌜∃ b, l = l' ++ a :: b⌝ ∗ P ∗ Ψ l' ∗ Φ1 a }}}
          (Val handler) (Val (inject a)) @ E
        {{{v, RET v; P ∗ Ψ (l' ++ [a]) ∗ Φ2 a }}}) -∗
    {{{ ⌜is_list l lv⌝ ∗ P ∗ Ψ [] ∗ [∗ list] a∈l, Φ1 a}}}
      list_iter (Val handler) lv @ E
    {{{ RET #(); P ∗ Ψ l ∗ [∗ list] a∈l, Φ2 a}}}.
  Proof.
    replace l with ([]++l); last by apply app_nil_l.
    iApply wp_list_iter_invariant'.
  Qed.

  Lemma wp_list_iter_idx_aux n Φ Ψ P E l lv handler :
    (∀ i (a : A),
        {{{ P ∗ Φ i a }}}
          (Val handler) (Val (inject a)) @ E
        {{{v, RET v; P ∗ Ψ i a }}}) -∗
    {{{ ⌜is_list l lv⌝ ∗ P ∗ [∗ list] i↦a ∈ l, Φ (n + i)%nat a }}}
      list_iter (Val handler) lv @ E
    {{{ RET #(); P ∗ [∗ list] i↦a ∈ l, Ψ (n + i)%nat a }}}.
  Proof.
    rewrite /list_iter.
    iIntros "#Helem"; iIntros (Φ') "!# (Ha & HP & Hl) HΦ".
    iLöb as "IH" forall (l lv n);
    destruct l as [|a l'];
    iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_pures.
    - iApply "HΦ"; eauto.
    - assert (Helemof: a ∈ a :: l').
      { constructor. }
      destruct Ha as [lv' [Hlv Hlcoh]]; subst.
      wp_pures.
      iDestruct (big_sepL_cons with "Hl") as "[Ha Hl']".
      wp_apply ("Helem" with "[HP Ha]"); iFrame; eauto.
      iIntros (v) "[HP Ha]". simpl. wp_seq.
      iApply ("IH" $! l' _ (S n) with "[] [$HP] [Hl']"); [done| |].
      { iApply (big_sepL_impl with "Hl' []").
        iIntros "!>" (k x Hlookup) "H".
        replace (n + S k)%nat with (S n + k)%nat by lia.
        done. }
      iNext. iIntros "(HP & Hl)". iApply "HΦ". iFrame.
      iApply (big_sepL_impl with "Hl []").
      iIntros "!>" (k x Hlookup) "H".
      replace (n + S k)%nat with (S n + k)%nat by lia.
      done.
  Qed.

  Lemma wp_list_iter_idx Φ Ψ P E l lv handler :
    (∀ i (a : A),
        {{{ P ∗ Φ i a }}}
          (Val handler) (Val (inject a)) @ E
        {{{v, RET v; P ∗ Ψ i a }}}) -∗
    {{{ ⌜is_list l lv⌝ ∗ P ∗ [∗ list] i↦a ∈ l, Φ i a }}}
      list_iter (Val handler) lv @ E
    {{{ RET #(); P ∗ [∗ list] i↦a ∈ l, Ψ i a }}}.
  Proof.
    iIntros "#H" (Φ') "!# (%Ha & HP & Hl) HΦ".
    iApply (wp_list_iter_idx_aux 0 Φ _ _ _ _ lv with "[H] [HP $Hl] HΦ").
    { iIntros (i a). iApply "H". }
    by iFrame.
  Qed.

  Lemma wp_list_iter Φ Ψ P E l lv handler :
    (∀ (a : A),
        {{{ P ∗ Φ a }}}
          (Val handler) (Val (inject a)) @ E
        {{{v, RET v; P ∗ Ψ a }}}) -∗
    {{{ ⌜is_list l lv⌝ ∗ P ∗ [∗ list] a ∈ l, Φ a }}}
      list_iter (Val handler) lv @ E
    {{{ RET #(); P ∗ [∗ list] a ∈ l, Ψ a }}}.
  Proof.
    rewrite /list_iter.
    iIntros "#H" (Φ') "!# (%Ha & HP & Hl) HΦ".
    iApply (wp_list_iter_idx with "[H] [HP $Hl] HΦ").
    { iIntros (i a). iApply "H". }
    by iFrame.
  Qed.

  Lemma wp_list_iteri_loop
        (k : nat) (l : list A) (fv lv : val)
        (P : iProp Σ) (Φ Ψ : nat -> A -> iProp Σ) E :
    is_list l lv →
    (∀ (i : nat) (x : A),
      {{{ P ∗ Φ i x }}} fv #i (inject x) @ E {{{ v, RET v; P ∗ Ψ i x }}}) -∗
    {{{ P ∗ ([∗ list] i ↦ a ∈ l, Φ (k+i)%nat a) }}}
      list_iteri_loop fv #k lv @ E
    {{{ RET #(); P ∗ [∗ list] i ↦ a ∈ l, Ψ (k+i)%nat a }}}.
  Proof.
    iIntros (Hl) "#Hf".
    iIntros (Φ') "!> [HP Hl] HΦ".
    iInduction l as [ | h l] "IH" forall (lv k Hl).
    { wp_lam. rewrite Hl. wp_pures. iApply "HΦ". by iFrame. }
    wp_lam. destruct Hl as [l' [-> Hl']]. wp_pures.
    iDestruct "Hl" as "[Ha Hl']". rewrite right_id_L.
    wp_apply ("Hf" with "[$HP $Ha]"). iIntros (v) "[HP HΨ]".
    wp_pures.
    replace (Z.add (Z.of_nat k) (Zpos xH)) with (Z.of_nat (k + 1)) by lia.
    iApply ("IH" $!l' (k+1)%nat with "[//] HP [Hl'] [HΨ HΦ]").
    { iApply (big_sepL_impl with "Hl'").
      iIntros "!>" (i x HSome) "HΦ".
      replace (k + S i)%nat with (k + 1 + i)%nat by lia. done. }
    iIntros "!> [HP Hl]".
    iApply "HΦ"=> /=. rewrite right_id_L. iFrame.
    iApply (big_sepL_impl with "Hl").
    iIntros "!>" (i x HSome) "HΦ".
    by replace (k + S i)%nat with (k + 1 + i)%nat by lia.
  Qed.

  Lemma wp_list_iteri
        (l : list A) (fv lv : val)
        (P : iProp Σ) (Φ Ψ : nat -> A -> iProp Σ) E :
    is_list l lv →
    (∀ (i : nat) (x : A),
      {{{ P ∗ Φ i x }}} fv #i (inject x) @ E {{{ v, RET v; P ∗ Ψ i x }}}) -∗
    {{{ P ∗ ([∗ list] i ↦ a ∈ l, Φ i a) }}}
      list_iteri fv lv @ E
    {{{ RET #(); P ∗ [∗ list] i ↦ a ∈ l, Ψ i a }}}.
  Proof.
    iIntros (Hl) "#Hf". iIntros (Φ') "!>[HP Hown] HΦ".
    wp_lam. wp_pures.
    iAssert (⌜#0 = #(0%nat)⌝%I) as %->; [done |].
    iApply (wp_list_iteri_loop 0 l with "Hf [$HP $Hown]"); [done|].
    by iFrame.
  Qed.

  Lemma wp_list_fold P Φ Ψ E handler (l : list A) acc lv :
    (∀ (a : A) acc lacc lrem,
        {{{ ⌜l = lacc ++ a :: lrem⌝ ∗ P lacc acc ∗ Φ a }}}
          (Val handler) (Val acc) (inject a) @ E
        {{{v, RET v; P (lacc ++ [a]) v ∗ Ψ a }}}) -∗
    {{{ ⌜is_list l lv⌝ ∗ P [] acc ∗ [∗ list] a∈l, Φ a }}}
      list_fold handler acc lv @ E
    {{{v, RET v; P l v ∗ [∗ list] a∈l, Ψ a }}}.
  Proof.
    iIntros "#Hcl". iIntros (Ξ) "!# (Hl & Hacc & HΦ) HΞ".
    change l with ([] ++ l) at 1 4.
    generalize (@nil A) at 1 3 4 as lproc => lproc.
    iInduction l as [|x l] "IHl" forall (Ξ lproc acc lv) "Hacc Hl HΞ".
    - iDestruct "Hl" as %?; simpl in *; simplify_eq.
      wp_rec. wp_pures. iApply "HΞ".
      rewrite app_nil_r; iFrame; done.
    - iDestruct "Hl" as %[lw [? Hlw]]; subst.
      iDestruct "HΦ" as "[Hx HΦ]".
      wp_rec. wp_pures.
      wp_apply ("Hcl" with "[$Hacc $Hx] [-]"); auto.
      iNext. iIntros (w) "[Hacc HΨ]"; simpl. wp_pures.
      iApply ("IHl" with "[] [$HΦ] [$Hacc] [] [HΨ HΞ]"); [|auto|].
      { rewrite -app_assoc; auto. }
      iNext. iIntros (v) "[HP HΨs]".
      rewrite -app_assoc.
      iApply "HΞ"; iFrame.
  Qed.

  Lemma wp_list_fold_generalized' E handler (l lp : list A) acc lv P Φ Ψ :
    □ (∀ (a : A) acc lacc lrem, (P lacc acc None (a::lrem) -∗ P lacc acc (Some a) lrem))%I -∗
      (∀ (a : A) acc lacc lrem,
          {{{ ⌜lp ++ l = lacc ++ a :: lrem⌝ ∗ P lacc acc (Some a) lrem ∗ Φ a }}}
            (Val handler) (Val acc) (inject a) @ E
          {{{v, RET v; P (lacc ++ [a]) v None lrem ∗ Ψ a }}}) -∗
    {{{ ⌜is_list l lv⌝ ∗ P lp acc None l ∗ [∗ list] a∈l, Φ a }}}
      list_fold (Val handler) (Val acc) (Val lv) @ E
    {{{v, RET v; P (lp ++ l) v None [] ∗ [∗ list] a∈l, Ψ a }}}.
  Proof.
    iIntros "#Hvs #Hcl". iIntros (Ξ) "!# (Hl & Hacc & HΦ) HΞ".
    iInduction l as [|x l] "IHl" forall (Ξ lp acc lv) "Hacc Hl HΞ".
    - iDestruct "Hl" as %?; simpl in *; simplify_eq.
      wp_rec. wp_pures. iApply "HΞ".
      rewrite app_nil_r; iFrame. done.
    - iDestruct "Hl" as %[lw [? Hlw]]; subst.
      iDestruct "HΦ" as "[Hx HΦ]".
      wp_rec; wp_pures.
      iPoseProof ("Hvs" with "Hacc") as "Hacc".
      wp_apply ("Hcl" with "[$Hacc $Hx] [-]"); auto.
      iNext. iIntros (w) "[Hacc HΨ]"; simpl. wp_let.
      iApply ("IHl" with "[] [$HΦ] [$Hacc] [] [HΨ HΞ]"); [|auto|].
      { rewrite -app_assoc; auto. }
      iNext. iIntros (v) "[HP HΨs]".
      rewrite -app_assoc.
      iApply "HΞ"; iFrame.
  Qed.

  Lemma wp_list_fold' E handler (l : list A) acc lv P Φ Ψ :
    □ (∀ (a : A) acc lacc lrem, (P lacc acc None (a::lrem) -∗ P lacc acc (Some a) lrem))%I -∗
      (∀ (a : A) acc lacc lrem,
          {{{ ⌜l = lacc ++ a :: lrem⌝ ∗ P lacc acc (Some a) lrem ∗ Φ a }}}
            (Val handler) (Val acc) (inject a) @ E
          {{{v, RET v; P (lacc ++ [a]) v None lrem ∗ Ψ a }}}) -∗
    {{{ ⌜is_list l lv⌝ ∗ P [] acc None l ∗ [∗ list] a∈l, Φ a }}}
      list_fold (Val handler) (Val acc) lv @ E
    {{{v, RET v; P l v None [] ∗ [∗ list] a∈l, Ψ a }}}.
  Proof.
    iIntros "#Hvs #Hcl".
    iApply (wp_list_fold_generalized' _ handler l [] with "[-]"); eauto.
  Qed.

  Lemma wp_list_sub E k l lv  :
    {{{ ⌜is_list l lv⌝ }}}
      list_sub #k lv @ E
    {{{ v, RET v; ⌜is_list (take k l) v ⌝}}}.
  Proof.
   iIntros (Φ) "Hcoh HΦ".
   iInduction l as [|a l'] "IH" forall (k lv Φ);
   iDestruct "Hcoh" as %Hcoh; simpl in Hcoh; subst; wp_rec;
   wp_pures; case_bool_decide; wp_if; wp_pures.
   - iApply "HΦ"; by rewrite take_nil.
   - iApply "HΦ"; by rewrite take_nil.
   - iApply "HΦ". assert (k = O) as H1 by lia. by rewrite H1 firstn_O.
   - destruct Hcoh as [lv' [Hlv Hlcoh]]; subst.
     wp_match. wp_proj. wp_bind (list_sub _ _). wp_op.
     destruct k as [|k]; first done.
     assert (((Z.of_nat (S k)) - 1)%Z = Z.of_nat k) as -> by lia.
     iApply ("IH" $! k _ _ Hlcoh). iIntros (tl Hcoh_tl).
     iNext. wp_pures. rewrite firstn_cons. by wp_apply (wp_list_cons).
  Qed.

  Lemma wp_list_nth E (i: nat) l lv  :
   {{{ ⌜is_list l lv⌝ }}}
      list_nth (Val lv) #i @ E
    {{{ v, RET v; (⌜v = NONEV⌝ ∧ ⌜length l <= i⌝) ∨
              ⌜∃ r, v = SOMEV (inject r) ∧ nth_error l i = Some r⌝ }}}.
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

  Lemma spec_list_nth E l lv (i:nat) K:
    is_list l lv ->
    ⤇ fill K (list_nth (Val lv) #i) -∗ spec_update E (∃ v, (⤇ fill K (of_val v)) ∗
                                                           ((⌜v = NONEV⌝ ∧ ⌜length l <= i⌝) ∨
                                                              ⌜∃ r, v = SOMEV (inject r) ∧ nth_error l i = Some r⌝)).
  Proof.
    iIntros "%Ha Hspec".
    iInduction l as [|a l'] "IH" forall (i lv Ha);
      simpl in Ha; subst; rewrite /list_nth; tp_pures; rewrite -/list_nth.
    - iApply spec_update_ret. iFrame. iLeft. iPureIntro. split; [done|simpl; lia].
    - destruct Ha as [lv' [Hlv Hlcoh]]; subst.
      tp_pures; first naive_solver. case_bool_decide; tp_pures.
      + iApply spec_update_ret. iFrame. iRight. iPureIntro. simplify_eq.
        replace i with 0%nat; last lia. simpl. naive_solver.
      + destruct i; first done.
        assert ((S i - 1)%Z = i) as -> by lia.
        iApply spec_update_mono.
        iSplitL.
        -- iApply ("IH" $! i lv' _ with "[Hspec]"); done.
        -- iIntros "(%&?&[%|[%%]])".
           ++ iFrame. iLeft. iPureIntro. simpl. split; [naive_solver|lia].
           ++ iFrame. iRight. iPureIntro. naive_solver.
              Unshelve.
              done.
  Qed.

  Lemma wp_list_nth_some E (i: nat) l lv  :
    {{{  ⌜is_list l lv ∧ i < length l⌝  }}}
      list_nth (Val lv) #i @ E
    {{{ v, RET v; ⌜∃ r, v = SOMEV (inject r) ∧ nth_error l i = Some r⌝ }}}.
  Proof.
    iIntros (Φ (Hcoh & Hi)) "HΦ".
    iApply (wp_list_nth $! Hcoh).
    iIntros (v [H | H]); first eauto with lia.
    by iApply "HΦ".
  Qed.

  (*
  Lemma wp_list_mem `{!EqDecision A} E (l : list A) lv a :
    {{{ ⌜is_list l lv⌝ }}}
      list_mem (inject a) lv @ E
    {{{ (b : bool), RET #b; if b then ⌜a ∈ l⌝ else ⌜a ∉ l ∨ l = nil⌝ }}}.
  Proof.
    iIntros (Φ).
    iInduction l as [|a' l'] "IH" forall (lv Φ);
      iIntros (Hl) "HΦ"; wp_rec; wp_pures.
    - rewrite Hl. wp_pures. iApply "HΦ". auto.
    - destruct Hl as [lv' [-> Hl']]. wp_pures.
      wp_op; first apply bin_op_eval_eq_val.
      case_bool_decide as Heq; wp_if.
      { simplify_eq. iApply "HΦ". iPureIntro; set_solver. }
      iApply ("IH" with "[//]").
      iIntros "!>" ([] Ha).
      { iApply "HΦ". iPureIntro; set_solver. }
      iApply "HΦ".
      iPureIntro. left.
      simplify_eq.
      apply not_inj_fn in Heq; [|apply _].
      destruct Ha; set_solver.
  Qed.
  *)


  Lemma wp_remove_nth E (l : list A) lv (i : nat) :
    {{{ ⌜is_list l lv /\ i < length l⌝ }}}
      list_remove_nth lv #i @ E
    {{{ v, RET v; ∃ e lv' l1 l2,
                ⌜l = l1 ++ e :: l2 ∧
                 length l1 = i /\
                v = SOMEV ((inject e), lv') ∧
                is_list (l1 ++ l2) lv'⌝ }}}.
  Proof.
    iIntros (Φ) "Ha Hφ".
    iInduction l as [|a l'] "IH" forall (i lv Φ);
      iDestruct "Ha" as "(%Hl & %Hi)"; simpl in Hl; subst; wp_rec; wp_let.
    - inversion Hi.
    - destruct Hl as [lv' [Hlv Hlcoh]]; subst.
      wp_match. wp_pures. case_bool_decide; wp_pures.
      + iApply "Hφ".
        iExists a, (inject l'), [], l'.
        destruct i; auto.
        iPureIntro; split; auto.
        split; auto.
        split.
        * by apply is_list_inject in Hlcoh as ->.
        * by apply is_list_inject.
      + destruct i; first done.
        assert ((S i - 1)%Z = i) as -> by lia.
        assert (is_list l' lv' /\ i < length l') as Haux.
        { split; auto.
          inversion Hi; auto. lia.
        }
        wp_bind (list_remove_nth _ _).
        iApply ("IH" $! i lv' _  Haux).
        iNext. iIntros (v (e & v' & l1 & l2 & (-> & Hlen & -> & Hil))); simpl.
        wp_pures.
        wp_bind (list_cons _ _). iApply wp_list_cons; [done|].
        iIntros "!>" (v Hcons).
        wp_pures.
        iApply "Hφ".
        iExists e, (inject ((a :: l1) ++ l2)), (a :: l1), l2.
        iPureIntro.
        split; auto.
        split; [rewrite cons_length Hlen // |].
        split.
        * by apply is_list_inject in Hcons as ->.
        * by apply is_list_inject.
  Qed.


  Lemma spec_remove_nth E K (l : list A) lv (i : nat) :
    (⌜is_list l lv /\ i < length l⌝ ) -∗
    ⤇ fill K (list_remove_nth lv #i) -∗
    spec_update E
    (∃ v, ⤇ fill K (of_val v) ∗
     ∃ e lv' l1 l2,
            (⌜l = l1 ++ e :: l2 ∧
             length l1 = i /\
            v = SOMEV ((inject e), lv') ∧
            is_list (l1 ++ l2) lv'⌝)).
  Proof.
    iIntros "Hl Hspec".
    iInduction l as [|a l'] "IH" forall (i lv K);
      iDestruct "Hl" as "(%Hl & %Hi)"; simpl in Hl; subst.
    - inversion Hi.
    - destruct Hl as [lv' [Hlv Hlcoh]]; subst.
      rewrite /list_remove_nth.
      tp_pures.
      { rewrite /vals_compare_safe /val_is_unboxed /lit_is_unboxed. auto. }
      fold list_remove_nth.
      case_bool_decide; tp_pures.
      + iModIntro.
        iExists _.
        iFrame.
        iExists a, (inject l'), [], l'.
        destruct i; auto.
        iPureIntro; split; auto.
        split; auto.
        split; auto.
        * by apply is_list_inject in Hlcoh as ->.
        * by apply is_list_inject.
      + destruct i; first done.
        assert ((S i - 1)%Z = i) as -> by lia.
        iAssert (⌜ is_list l' lv' /\ i < length l' ⌝%I) as "Haux".
        {
          iPureIntro.
          split; auto.
          inversion Hi; auto. lia.
        }
        tp_bind (list_remove_nth _ _).
        (* iEval (rewrite ⤇ fill_bind) in "Hspec". *)
        iMod ("IH" $! _ _ _ with "Haux Hspec") as (v) "(Hspec & (%e & %v' & %l1 & %l2 & (-> & %Hlen & -> & %Hil)))".
        (* iEval (rewrite -⤇ fill_bind /=) in "Hspec". *) simpl.
        tp_pures.
        tp_bind (list_cons _ _).
        (* iEval (rewrite ⤇ fill_bind ) in "Hspec". *)
        iMod (spec_list_cons $! Hil with "Hspec") as (v'') "(Hspec & %Hv'')".
        (* iEval (rewrite -⤇ fill_bind /=) in "Hspec". *)
        simpl.
        tp_pures.
        iModIntro.
        iExists _.
        iFrame.
        iExists _, (inject ((a :: l1) ++ l2)), (a :: l1), l2.
        iSplit.
        { iPureIntro; auto. }
        iPureIntro.
        split; [rewrite cons_length Hlen // |].
        split; auto.
        * simpl. by apply is_list_inject in Hv'' as ->.
        * by apply is_list_inject.
  Qed.

  Lemma wp_remove_nth_total E (l : list A) lv (i : nat) :
    {{{ ⌜is_list l lv /\ i < length l⌝ }}}
      list_remove_nth_total lv #i @ E
    {{{ v, RET v; ∃ e lv' l1 l2,
                ⌜l = l1 ++ e :: l2 ∧
                 length l1 = i /\
                v = lv' ∧
                is_list (l1 ++ l2) lv'⌝ }}}.
  Proof.
    iIntros (Φ) "Ha Hφ".
    iInduction l as [|a l'] "IH" forall (i lv Φ);
      iDestruct "Ha" as "(%Hl & %Hi)"; simpl in Hl; subst; wp_rec; wp_let.
    - inversion Hi.
    - destruct Hl as [lv' [Hlv Hlcoh]]; subst.
      wp_match. wp_pures. case_bool_decide; wp_pures.
      + iApply "Hφ".
        iExists a, (inject l'), [], l'.
        destruct i; auto.
        iPureIntro; split; auto.
        split; auto.
        split.
        * by apply is_list_inject in Hlcoh.
        * by apply is_list_inject.
      + destruct i; first done.
        assert ((S i - 1)%Z = i) as -> by lia.
        assert (is_list l' lv' /\ i < length l') as Haux.
        { split; auto.
          inversion Hi; auto. lia.
        }
        wp_bind (list_remove_nth_total _ _).
        iApply ("IH" $! i lv' _  Haux).
        iNext. iIntros (v (e & v' & l1 & l2 & (-> & Hlen & -> & Hil))); simpl.
        wp_pures.
        iApply wp_list_cons; [done |].
        iIntros "!>" (v Hcons).
        iApply "Hφ".
        iExists e, (inject ((a :: l1) ++ l2)), (a :: l1), l2.
        iPureIntro.
        split; auto.
        split; [rewrite cons_length Hlen // |].
        split.
        * by apply is_list_inject in Hcons.
        * by apply is_list_inject.
  Qed.


  Lemma wp_find_remove E (l : list A) lv (Ψ : A → iProp Σ) (fv : val) :
    (∀ (a : A),
        {{{ True }}}
          fv (inject a) @ E
        {{{ (b : bool), RET #b; if b then Ψ a else True }}}) -∗
    {{{ ⌜is_list l lv⌝ }}}
      list_find_remove fv lv @ E
    {{{ v, RET v; ⌜v = NONEV⌝ ∨
                       ∃ e lv' l1 l2,
                         ⌜l = l1 ++ e :: l2 ∧
                         v = SOMEV ((inject e), lv') ∧
                         is_list (l1 ++ l2) lv'⌝
                         ∗ Ψ e}}}.
  Proof.
    iIntros "#Hf" (Φ).
    iInduction l as [|a l'] "IH" forall (lv Φ);
      iIntros (Hl) "!> HΦ"; wp_rec; wp_pures.
    { rewrite Hl. wp_pures. iApply "HΦ".
      iLeft; iPureIntro; split; set_solver. }
    destruct Hl as [lv' [-> Hl']]. wp_pures.
    wp_bind (fv _). iApply ("Hf" with "[//]").
    iIntros "!>" (b) "Hb /=".
    destruct b.
    { wp_pures.
      iApply "HΦ".
      iRight; iExists _, _, [], _; eauto. }
    wp_pures.
    wp_bind (list_find_remove _ _).
    iApply ("IH" with "[//]").
    iIntros "!>" (w) "[->| He] /="; wp_pures.
    { iApply "HΦ".
      iLeft; done. }
    iDestruct "He" as (e lv'' l1 l2) "[He HHΨ]".
    iDestruct "He" as %(-> & -> & Hlv'').
    wp_pures.
    wp_bind (list_cons _ _). iApply wp_list_cons; [done|].
    iIntros "!>" (v Hcoh) "/=". wp_pures.
    iApply "HΦ". iRight.
    iExists _, _, (_ :: _), _; eauto.
  Qed.

  Local Lemma wp_list_rev_aux E l lM r rM:
   {{{ ⌜is_list lM l ∧ is_list rM r⌝ }}}
     list_rev_aux (Val l) (Val r) @ E
   {{{ v, RET v; ⌜is_list (rev_append lM rM) v⌝ }}}.
  Proof.
    iIntros (? [Hl Hr]) "H".
    iInduction lM as [|a lM] "IH" forall (l r rM Hl Hr).
    - simpl in *; subst. rewrite /list_rev_aux. wp_pures. by iApply "H".
    - destruct Hl as [l' [Hl'eq Hl']]; subst.
      wp_rec; wp_pures.
      wp_apply wp_list_cons; [done|].
      iIntros (w Hw).
      wp_pures. by iApply "IH".
 Qed.

  Lemma wp_list_rev E l lM :
    {{{ ⌜is_list lM l⌝ }}}
      list_rev (Val l) @ E
    {{{ v, RET v; ⌜is_list (reverse lM) v⌝ }}}.
  Proof.
    iIntros (??) "H". rewrite /list_rev. wp_pures.
    by iApply (wp_list_rev_aux _ _ _ NONEV []).
  Qed.

  Lemma wp_list_append E l lM r rM :
    {{{ ⌜is_list lM l⌝ ∗ ⌜is_list rM r⌝}}}
      list_append (Val l) (Val r) @ E
    {{{ v, RET v; ⌜is_list (lM ++ rM) v⌝ }}}.
  Proof.
    iIntros (Φ) "[%Hl %Hr] HΦ". rewrite /list_append.
    iInduction lM as [|a lM] "IH" forall (l r Hl Hr Φ).
    - simpl in Hl; subst. wp_pures. by iApply "HΦ".
    - destruct Hl as [l' [Hl'eq Hl']]; subst.
      do 12 wp_pure _.
      wp_bind (((rec: "list_append" _ _:= _)%V _ _)).
      iApply "IH"; [done..|].
      iIntros "!>" (v Hv).
      by wp_apply wp_list_cons.
  Qed.

  Lemma wp_list_forall Φ Ψ E (l : list A) lv (fv : val) :
    (∀ (a : A),
        {{{ True }}}
          fv (inject a) @ E
        {{{ (b : bool), RET #b; if b then Φ a else Ψ a }}}) -∗
    {{{ ⌜is_list l lv⌝ }}}
      list_forall fv lv @ E
    {{{ (b : bool), RET #b; if b then [∗ list] a ∈ l, Φ a else ∃ a, ⌜a ∈ l⌝ ∗ Ψ a }}}.
  Proof.
    rewrite /list_forall.
    iInduction l as [|a l'] "IH" forall (lv);
      iIntros "#Hfv" (Ξ) "!# %Hl HΞ".
    - simpl in Hl; subst. wp_pures. iApply "HΞ"; auto.
    - destruct Hl as [l'' [Hl'eq Hl']]; subst.
      wp_pures.
      wp_apply "Hfv"; [done|].
      iIntros ([]) "Hb".
      + wp_if. iApply ("IH"); [done..|].
        iIntros "!>" ([]).
        * iIntros "Ha". iApply "HΞ".
          rewrite big_sepL_cons. iFrame.
        * iDestruct 1 as (a') "[% ?]".
          iApply "HΞ". iExists _. iFrame.
          iPureIntro. apply elem_of_cons. by right.
      + wp_if. iApply "HΞ". iExists _. iFrame.
        iPureIntro. apply elem_of_cons. by left.
  Qed.

  Lemma wp_list_is_empty l v E :
    {{{ ⌜is_list l v⌝ }}}
      list_is_empty v @ E
    {{{ v, RET #v;
        ⌜v = match l with [] => true | _ => false end⌝ }}}.
  Proof.
    iIntros (Φ Hl) "HΦ". wp_rec. destruct l.
    - rewrite Hl. wp_pures. by iApply "HΦ".
    - destruct Hl as [? [-> _]]. wp_pures. by iApply "HΦ".
  Qed.

  Lemma is_list_eq lM :
    ∀ l1 l2, is_list lM l1 → is_list lM l2 → l1 = l2.
  Proof. induction lM; intros []; naive_solver eauto with f_equal. Qed.

  Lemma is_list_inv_l l:
    ∀ lM1 lM2, is_list lM1 l → lM1 = lM2 → is_list lM2 l.
  Proof. by intros ? ? ? <-. Qed.

  Lemma is_list_snoc lM x : ∃ lv, is_list (lM ++ [x]) lv.
  Proof. induction lM; naive_solver eauto. Qed.

  Lemma wp_list_filter (l : list A) (P : A -> bool) (f lv : val) E :
    {{{ (∀ (x : A),
            {{{ True }}}
              f (inject x) @ E
            {{{ w, RET w; ⌜w = inject (P x)⌝ }}} ) ∗
        ⌜is_list l lv⌝ }}}
       list_filter f lv @ E
     {{{ rv, RET rv; ⌜is_list (List.filter P l) rv⌝ }}}.
  Proof.
    iIntros (Φ) "[#Hf %Hil] HΦ".
    iInduction l as [ | h t] "IH" forall (lv Hil Φ); simpl in Hil.
    - subst.
      rewrite /list_filter; wp_pures.
      iApply "HΦ"; done.
    - destruct Hil as (lv' & -> & Hil).
      rewrite /list_filter.
      do 7 (wp_pure _).
      fold list_filter.
      wp_apply ("IH" $! lv'); [done |].
      iIntros (rv) "%Hilp"; wp_pures.
      wp_apply "Hf"; [done |].
      iIntros (w) "->".
      destruct (P h) eqn:HP; wp_pures.
      + wp_apply wp_list_cons; [by eauto |].
        iIntros (v) "%Hil'".
        iApply "HΦ"; iPureIntro.
        simpl; rewrite HP; simpl.
        simpl in Hil'; done.
      + iApply "HΦ"; iPureIntro.
        simpl. rewrite HP. done.
  Qed.
End list_specs.

Global Arguments wp_list_nil : clear implicits.
Global Arguments wp_list_nil {_ _ _} _ {_}.

(* Start a new section because some of the specs below (e.g. wp_list_map) need
   access to the type parameter in e.g. is_list, since they operate on more than one
   list type. *)
Section list_specs_extra.

  Context `{!parisGS Σ}.
  Context `[!Inject A val].

  Lemma wp_list_map_strong `{!Inject B val} (l : list A) (f : A -> B) (fv lv : val)
        (γ : A -> iProp Σ) (ψ : B -> iProp Σ) E :
    {{{ □ (∀ (x : A),
          {{{ γ x }}}
            fv (inject x) @ E
          {{{ fr, RET fr; ⌜fr = inject (f x)⌝ ∗ ψ (f x) }}}) ∗
          ⌜is_list l lv⌝ ∗
          [∗ list] x ∈ l, γ x
    }}}
      list_map fv lv @ E
    {{{ rv, RET rv; ⌜is_list (List.map f l) rv⌝ ∗
        [∗ list] y ∈ (List.map f l), ψ y
    }}}.
  Proof.
    iIntros (Φ) "[#Hf [%Hil Hl]] HΦ".
    iInduction l as [ | h t] "IH" forall (lv Hil Φ); simpl in Hil; try subst; rewrite /list_map.
    - wp_pures.
      iApply "HΦ". iModIntro.
      iSplit.
      * iPureIntro. rewrite /is_list; done.
      * rewrite /=. auto.
    - wp_pures.
      iDestruct "Hl" as "(Hd&Htl)".
      destruct Hil as (lv' & -> & Hil').
      do 4 wp_pure _.
      fold list_map.
      wp_apply ("IH" with "[] Htl"); [done |].
      iIntros (rv) "(%Hil_rv&Htl)"; wp_pures.
      wp_apply ("Hf" with "Hd").
      iIntros (fr) "(->&Hhd)".
      wp_apply wp_list_cons; [done |].
      iIntros (v) "%Hilf".
      iApply "HΦ"; auto.
      rewrite /=; iFrame. auto.
  Qed.

  Lemma wp_list_map `{!Inject B val} (l : list A) (f : A -> B) (fv lv : val) E :
    {{{ (∀ (x : A),
          {{{ True }}}
            fv (inject x) @ E
          {{{ fr, RET fr; ⌜fr = inject (f x)⌝ }}}) ∗
          ⌜is_list l lv⌝ }}}
      list_map fv lv @ E
    {{{ rv, RET rv; ⌜is_list (List.map f l) rv⌝ }}}.
  Proof.
    iIntros (Φ) "[#Hf %Hil] HΦ".
    iInduction l as [ | h t] "IH" forall (lv Hil Φ); simpl in Hil; try subst; rewrite /list_map.
    - wp_pures.
      iApply "HΦ"; iPureIntro.
      rewrite /is_list; done.
    - wp_pures.
      destruct Hil as (lv' & -> & Hil').
      do 4 wp_pure _.
      fold list_map.
      wp_apply "IH"; [done |].
      iIntros (rv) "%Hil_rv"; wp_pures.
      wp_apply "Hf"; [done |].
      iIntros (fr) "->".
      wp_apply wp_list_cons; [done |].
      iIntros (v) "%Hilf".
      iApply "HΦ"; auto.
  Qed.

  Lemma spec_list_map `{!Inject B val} K (l : list A) (f : A -> B) (fv lv : val) E :
    □ (∀ K (x : A),
          ⤇ fill K (fv (inject x)) -∗
          spec_update E (∃ fr : val, ⤇ fill K fr ∗ ⌜fr = inject (f x)⌝)) -∗
      ⌜is_list l lv⌝ -∗
      ⤇ fill K (list_map fv lv) -∗
    spec_update E (∃ rv : val, ⤇ fill K rv ∗ ⌜is_list (List.map f l) rv⌝).
  Proof.
    iIntros "#Hf %Hil HK".
    iInduction l as [ | h t] "IH" forall (K lv Hil); simpl in Hil; try subst; rewrite /list_map.
    - tp_pures. iModIntro; iFrame; eauto.
    - tp_pures.
      destruct Hil as (lv' & -> & Hil').
      do 4 tp_pure.
      fold list_map.
      tp_bind (list_map _ _).
      iMod ("IH" with "[//] [$]") as (rv) "(Hspec&%Hil_rv)".
      simpl. tp_pures.
      tp_bind (fv _).
      iMod ("Hf" with "[$]") as (fr) "(HK&->)".
      simpl.
      iMod (spec_list_cons with "[//] [$]") as (v) "(HK&%Hilf)".
      iModIntro; iExists _; iFrame. eauto.
  Qed.

  (* TODO: is this in some Coq library? *)
  Fixpoint mapi_loop {B : Type} (f : nat -> A -> B) (k : nat) (l : list A) : list B :=
    match l with
    | h :: t => (f k h) :: (mapi_loop f (S k) t)
    | [] => []
    end.

  Lemma mapi_loop_i {B : Type} (f : nat -> A -> B) (l : list A) (i k : nat) :
    (i < length l)%nat ->
    exists v w, l !! i = Some v ∧
           (mapi_loop f k l) !! i = Some w ∧
           w = f (k + i)%nat v.
  Proof.
    generalize dependent i.
    generalize dependent k.
    induction l as [ | h t IH]; intros k i Hlt; simpl in *.
    - exfalso; lia.
    - destruct i as [ | i']; simpl.
      { exists h, (f k h).
        replace (k + 0)%nat with k; auto. lia. }
      apply Nat.succ_lt_mono in Hlt.
      pose proof (IH (S k) i' Hlt) as (v & w & -> & -> & Heq).
      replace (k + S i')%nat with (S k + i')%nat by lia.
      eauto.
  Qed.

  Definition mapi {B : Type} (f : nat -> A -> B) (l : list A) : list B :=
    mapi_loop f 0 l.

  Lemma mapi_i {B : Type} (f : nat -> A -> B) (l : list A) (i : nat) :
    (i < length l)%nat ->
    exists v w, l !! i = Some v ∧
           (mapi f l) !! i = Some w ∧
           w = f i v.
  Proof.
    intros Hlt.
    pose proof (mapi_loop_i f l i O Hlt) as (v & w & H1 & H2 & H3).
    eauto.
  Qed.

  (* TODO: clean up *)
  Lemma wp_list_mapi_loop `{!Inject B val}
        (f : nat -> A -> B) (k : nat) (l : list A) (fv lv : val)
        (γ : nat -> A -> iProp Σ) (ψ : nat -> B -> iProp Σ) E :
    {{{ □ (∀ (i : nat) (x : A),
              {{{ γ (k + i)%nat x }}}
                fv (inject (k + i)%nat) (inject x) @ E
                {{{ fr, RET fr;
                    let r := f (k + i)%nat x in
                    ⌜fr = (inject r)⌝ ∗ ψ (k + i)%nat r }}}) ∗
        ⌜is_list l lv⌝ ∗
        ([∗ list] i ↦ a ∈ l, γ (k + i)%nat a)
    }}}
      list_mapi_loop fv #k lv @ E
    {{{ rv, RET rv;
        let l' := mapi_loop f k l in
        ⌜is_list l' rv⌝ ∗
        ([∗ list] i ↦ a ∈ l', ψ (k + i)%nat a)}}}.
  Proof.
    iInduction l as [ | h l'] "IH" forall (lv k);
      iIntros (Φ) "[#Hf [%Hil Hown]] HΦ"; simpl in Hil;
      rewrite /list_mapi_loop.
    - subst.
      wp_pures.
      iApply "HΦ".
      iSplitL ""; done.
    - destruct Hil as [lv' [-> Hil']].
      do 10 wp_pure _.
      fold list_mapi_loop.
      wp_bind (list_mapi_loop _ _ _).
      iAssert (⌜#(k + 1) = #(k + 1)%nat⌝%I) as "->".
      { iPureIntro.
        do 2 apply f_equal; lia. }
      iDestruct (big_sepL_cons with "Hown") as "[Hhead Hown]".
      iApply ("IH" with "[Hown]").
      + iSplitL "".
        * iModIntro.
          iIntros (i x).
          iPoseProof ("Hf"  $! (1 + i)%nat x) as "Hf'".
          iAssert (⌜(k + (1 + i))%nat = (k + 1 + i)%nat⌝%I) as %<-.
          {  iPureIntro; by lia. }
          iApply "Hf".
        * iSplitL ""; [done |].
          iApply (big_sepL_impl with "Hown").
          iModIntro.
          iIntros (k' x) "_ Hpre".
          iAssert (⌜(k + 1 + k')%nat = (k + S k')%nat⌝%I) as %->.
          { iPureIntro; lia. }
          done.
      + iModIntro.
        iIntros (rv) "[%Hil'' Hown]".
        wp_pures.
        iAssert (⌜#k = (inject (k + 0)%nat)⌝%I) as %->.
        { simpl.
          iPureIntro.
          do 2 f_equal.
          lia. }
        wp_apply ("Hf" with "Hhead").
        iIntros (fr) "[-> HΨ]".
        wp_apply wp_list_cons; [done | ].
        iIntros (v) "%Hil'''".
        iApply "HΦ".
        iSplitL ""; [iPureIntro |].
        { assert (f (k + 0)%nat h :: mapi_loop f (k + 1) l' = mapi_loop f k (h :: l')) as <-.
          { simpl.
            assert ((k + 0)%nat = k) as -> by lia.
            assert (k + 1 = S k)%nat as -> by lia.
            reflexivity. }
          done. }
        simpl.
        iSplitL "HΨ".
        { assert (f k h = f (k + 0)%nat h) as ->.
          { assert (k = (k + 0))%nat as <- by lia; done. }
          done. }
        iAssert (⌜(k + 1)%nat = S k⌝%I) as %->.
        { iPureIntro.
          do 2 f_equal.
          lia. }
        iApply (big_sepL_impl with "Hown").
        iModIntro.
        iIntros (k' x) "_ HΨ".
        iAssert (⌜(S k + k')%nat = (k + S k')%nat⌝%I) as %->.
        { iPureIntro.
          lia. }
        done.
  Qed.

  Lemma wp_list_mapi `{!Inject B val}
        (f : nat -> A -> B) (l : list A) (fv lv : val)
        (γ : nat -> A -> iProp Σ) (ψ : nat -> B -> iProp Σ) E :
    {{{ □ (∀ (i : nat) (x : A),
              {{{ γ i x }}}
                fv #i (inject x) @ E
                {{{ fr, RET fr;
                    let r := f i x in
                    ⌜fr = (inject r)⌝ ∗ ψ i r }}}) ∗
        ⌜is_list l lv⌝ ∗
        ([∗ list] i ↦ a ∈ l, γ i a)
    }}}
      list_mapi fv lv @ E
    {{{ rv, RET rv;
        let l' := mapi f l in
        ⌜is_list l' rv⌝ ∗
        ([∗ list] i ↦ a ∈ l', ψ i a)}}}.
  Proof.
    iIntros (Φ) "[#Hf [%Hil Hown]] HΦ".
    rewrite /list_mapi.
    do 3 wp_pure _.
    iAssert (⌜#0 = #(0%nat)⌝%I) as %->; [done |].
    iApply (wp_list_mapi_loop with "[Hown]").
    - iSplitL ""; last first.
      + iFrame; done.
      + iModIntro.
        iIntros (i x).
        iAssert (⌜(0 + i)%nat = i⌝%I) as %->; [done |].
        iApply "Hf".
    - iModIntro.
      assert (mapi f l = mapi_loop f 0 l) as <-; [done |].
      iFrame.
  Qed.

  (* TODO: is there a standard library lemma for this? *)
  Lemma list_lookup_succ (h : A) (l : list A) (i : nat) :
    (h :: l) !! (S i) = l !! i.
  Proof. auto. Qed.

  Lemma wp_list_seq E n m :
    {{{ True }}}
      list_seq #n #m @ E
    {{{ v, RET v; ⌜is_list (seq n m) v⌝ }}}.
  Proof.
    iIntros (Φ) "_ Hφ".
    iInduction m as [ | p] "IHm" forall (n Φ).
    - rewrite /list_seq.
      wp_pures.
      iApply "Hφ".
      iPureIntro.
      rewrite /seq.
      by apply is_list_inject.
    - rewrite /list_seq.
      wp_rec.
      do 6 wp_pure.
      assert (#(S p - 1) = #p) as ->.
      { do 3 f_equal. lia. }
      fold list_seq.
      assert (#(n + 1) = #(Z.of_nat (S n))) as ->.
      { do 3 f_equal. lia. }
      wp_apply "IHm".
      iIntros (v Hv).
      wp_apply (wp_list_cons with "[//]").
      iIntros (v' Hv').
      iApply "Hφ".
      iPureIntro.
      apply (is_list_inject) in Hv' as ->.
      by apply is_list_inject.
  Qed.


  Lemma spec_list_seq E K (n m : nat) :
    ⤇ fill K (list_seq #n #m) -∗ spec_update E (∃ v, (⤇ fill K (of_val v) ∗ ⌜is_list (seq n m) v⌝)).
  Proof.
    iIntros "Hspec".
    iInduction m as [ | p] "IHm" forall (n K).
    - rewrite /list_seq.
      tp_pures.
      iModIntro.
      iExists _.
      iFrame.
      iPureIntro.
      rewrite /seq.
      by apply is_list_inject.
    - rewrite /list_seq.
      tp_rec.
      do 6 tp_pure.
      assert (#(S p - 1) = #p) as ->.
      { do 3 f_equal. lia. }
      fold list_seq.
      assert (#(n + 1) = #(Z.of_nat (S n))) as ->.
      { do 3 f_equal. lia. }
      tp_bind (list_seq _ _).
      iMod ("IHm" $! (S n) with "[$Hspec]") as (v) "(Hspec & %Hlist)".
      simpl.
      assert (#n = (inject n)) as -> by done.
      iMod (spec_list_cons $! Hlist with "Hspec") as (v') "(Hspec & %Hlist')".
      iModIntro.
      iExists _. iFrame.
      iPureIntro.
      exists (inject (seq (S n) p)).
      apply is_list_inject in Hlist' as ->.
      split; auto.
      by apply is_list_inject.
  Qed.

End list_specs_extra.

Section list_rel.

    Context `{!parisRGS Σ}.
    Context `[!Inject B val].

    Lemma refines_list_length_l E K e A lv (l:list B):
      ⌜is_list l lv⌝ -∗
      (∀ v : nat, ⌜v = length l⌝  -∗ REL (fill K (of_val #v)) << e @ E : A)
      -∗ REL (fill K (list_length lv)) << e @ E : A.
    Proof.
      iIntros (?) "Hlog".
      iApply refines_wp_l.
      by iApply wp_list_length.
    Qed.
    
    Lemma refines_list_length_r E K e A lv (l:list B):
      ⌜is_list l lv⌝ -∗
      (∀ v : nat, ⌜v = length l⌝  -∗ REL e << (fill K (of_val #v)) @ E : A)
      -∗ REL e << (fill K (list_length lv)) @ E : A.
    Proof.
      iIntros "? Hlog".
      iApply refines_step_r.
      iIntros.
      iMod (spec_list_length with "[$][$]") as "(%&?&->)".
      iModIntro.
      iFrame. simpl.
      by iApply ("Hlog").
    Qed.

    Lemma refines_list_remove_nth_l E K e A lv (l:list B) (i:nat):
      ⌜is_list l lv ∧ i < length l⌝ -∗      
      (∀ v : val, (∃ (e : B) (lv' : val) (l1 l2 : list B),
                      ⌜l = l1 ++ e :: l2 ∧ length l1 = i ∧ v = InjRV (inject e, lv') ∧ is_list (l1 ++ l2) lv'⌝)
                  -∗ REL (fill K (of_val v)) << e @ E : A)
      -∗ REL (fill K (list_remove_nth lv #i)) << e @ E : A.
    Proof.
      iIntros (?) "Hlog".
      iApply refines_wp_l.
      by iApply wp_remove_nth.
    Qed.

    
    Lemma refines_list_remove_nth_r E K e A lv (l:list B) (i:nat):
      ⌜is_list l lv ∧ i < length l⌝ -∗      
      (∀ v : val, (∃ (e : B) (lv' : val) (l1 l2 : list B),
                      ⌜l = l1 ++ e :: l2 ∧ length l1 = i ∧ v = InjRV (inject e, lv') ∧ is_list (l1 ++ l2) lv'⌝)
                  -∗ REL e << (fill K (of_val v)) @ E : A)
      -∗ REL e << (fill K (list_remove_nth lv #i)) @ E : A.
    Proof.
      iIntros "?Hlog".
      iApply refines_step_r.
      iIntros.
      iMod (spec_remove_nth with "[$][$]") as "(%&?&%&%&%&%&->&<-&->&%)".
      iModIntro.
      iFrame.
      iApply ("Hlog").
      iPureIntro.
      naive_solver.
    Qed.
    
End list_rel.
