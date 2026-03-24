From stdpp Require Import list. 
From iris.base_logic.lib Require Import fancy_updates.
From clutch.common Require Export inject.
From clutch.prob_lang Require Export lang notation gwp.gen_weakestpre.

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

Definition list_hd : val :=
  λ:"xs", match: "xs" with NONE => #0 #0 | SOME "x_xs" => Fst "x_xs" end.

Definition list_tl : val :=
  λ:"xs", match: "xs" with NONE => "xs" | SOME "x_xs" => Snd "x_xs" end.

Definition list_init : val :=
  λ: "len" "f",
  (rec: "aux" "acc" "i" :=
    (if: "i" = #0
     then  "acc"
     else  "aux" (("f" "i") :: "acc") ("i" - #1))) [] "len".

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

Definition list_find : val :=
  rec: "list_find" "f" "xs" :=
    match: "xs" with
      SOME "a" =>
        let, ("x", "xs") := "a" in
        if: "f" "x" then SOME "x"
        else "list_find" "f" "xs"
    | NONE => NONE
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

Definition list_max_index_aux : val :=
  λ:"y" "xs",
    list_fold
      (λ: "(y, iy, ix)" "x",
         let, ("y", "iy", "ix") := "(y, iy, ix)" in
         if: "y" < "x" then ("x", "ix", "ix"+#1) else ("y", "iy", "ix"+#1))
      ("y", #0, #1) "xs".

Definition list_max_index : val :=
  λ:"xs",
    match: "xs" with
    | NONE => #0
    | SOME "y_xs" =>
        let, ("y", "xs") := "y_xs" in
        let, ("_y", "iy", "_ix") :=
          list_max_index_aux "y" "xs"
        in "iy"
    end.

End list_code.

Notation "[ ]" := (list_nil) (format "[ ]") : expr_scope.
Infix "::" := list_cons (at level 60, right associativity) : expr_scope.
Notation "[ x ]" := (list_cons x list_nil) (format "[ x ]") : expr_scope.
Notation "[ x ; y ; .. ; z ]" := (list_cons x (list_cons y .. (list_cons z list_nil) ..)) : expr_scope.
Infix "@@" := list_append (at level 60, right associativity) : expr_scope.

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

(** Later-generic specs *)
Section list_specs.
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.
  Context `[!Inject A val].

  Fixpoint is_list (l : list A) (v : val) :=
    match l with
    | [] => v = NONEV
    | a::l' => ∃ lv, v = SOMEV (inject a, lv) ∧ is_list l' lv
  end.

  Lemma is_list_inject xs v :
    is_list xs v ↔ v = inject xs.
  Proof.
    revert v.
    induction xs as [|x xs IH]; [done|]. split.
    - destruct 1 as (? & -> & ?). simpl.
      do 2 f_equal. by apply IH.
    - intros ->. eexists. split; [done|]. by apply IH.
  Qed.

  Lemma gwp_list_nil s E :
    G{{{ True }}}
      [] @ s ; E
    {{{ v, RET v; ⌜is_list [] v⌝}}}.
  Proof. iIntros (Φ) "_ HΦ". gwp_pures. by iApply "HΦ". Qed.

  Lemma gwp_list_cons a l lv E :
    G{{{ ⌜is_list l lv⌝ }}}
      inject a :: lv @ g; E
    {{{ v, RET v; ⌜is_list (a::l) v⌝ }}}.
  Proof.
    iIntros (Φ) "% HΦ". gwp_lam. gwp_pures.
    iApply "HΦ". iPureIntro; by eexists.
  Qed.

  Lemma gwp_list_singleton E a :
    G{{{ True }}}
      [inject a] @ g; E
    {{{ v, RET v; ⌜is_list [a] v⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ". gwp_pures.
    gwp_apply (gwp_list_cons _ []); [done|].
    iIntros (v' Hv').
    by iApply "HΦ".
  Qed.

  Lemma gwp_list_head E lv l :
    G{{{ ⌜is_list l lv⌝ }}}
      list_head lv @ g; E
    {{{ v, RET v;
        ⌜(l = [] ∧ v = NONEV) ∨ (∃ a l', l = a :: l' ∧ v = SOMEV (inject a))⌝ }}}.
  Proof.
    iIntros (Φ a) "HΦ".
    gwp_lam. destruct l; simpl in *; subst.
    - gwp_pures. iApply "HΦ". iPureIntro. by left.
    - destruct a as [lv' [Hhead Htail]] eqn:Heq; subst.
      gwp_pures. iApply "HΦ". iPureIntro. right. eauto.
  Qed.

  Lemma gwp_list_head_nil E lv :
    G{{{ ⌜is_list [] lv⌝ }}}
      list_head lv @ g; E
    {{{ RET NONEV; True }}}.
  Proof.
    iIntros (Φ a) "HΦ".
    gwp_apply (gwp_list_head _ _ [] with "[//]").
    iIntros (v) "[[_ ->] | (% & % & % & _)]"; simplify_eq.
    by iApply "HΦ".
  Qed.

  Lemma gwp_list_head_cons E lv a l :
    G{{{ ⌜is_list (a :: l) lv⌝ }}}
      list_head lv @ g; E
    {{{ RET (SOMEV (inject a)); True }}}.
  Proof.
    iIntros (Φ Hl) "HΦ".
    gwp_apply (gwp_list_head _ _ (a :: l) with "[//]").
    iIntros (v) "[[% ->] | (% & % & % & ->)]"; simplify_eq.
    by iApply "HΦ".
  Qed.

  Lemma gwp_list_head_opt E lv l :
    G{{{ ⌜is_list l lv⌝ }}}
      list_head lv @ g; E
    {{{ w, RET w; ⌜w = inject (hd_error l)⌝ }}}.
  Proof.
    iIntros (Φ a) "HΦ".
    gwp_lam. destruct l; simpl in *; subst.
    - gwp_pures. by iApply "HΦ".
    - destruct a as [lv' [Hhead Htail]] eqn:Heq; subst.
      gwp_pures. by iApply "HΦ".
  Qed.

  Lemma gwp_list_tail E lv l :
    G{{{ ⌜is_list l lv⌝ }}}
      list_tail lv @ g; E
    {{{ v, RET v; ⌜is_list (tail l) v⌝}}}.
  Proof.
    iIntros (Φ a) "HΦ".
    gwp_lam. destruct l; simpl in *; subst.
    - gwp_match. gwp_inj. by iApply "HΦ".
    - destruct a as [lv' [Hhead Htail]] eqn:Heq; subst.
      gwp_match. gwp_proj. by iApply "HΦ".
  Qed.

  Lemma gwp_list_length E l lv :
    G{{{ ⌜is_list l lv⌝ }}}
      list_length lv @ g; E
    {{{ v, RET #v; ⌜v = length l⌝ }}}.
  Proof.
    iIntros (Φ) "Ha HΦ".
    iInduction l as [|a l'] "IH" forall (lv Φ);
    iDestruct "Ha" as %Ha; simpl in Ha; subst; gwp_rec.
    - gwp_match. iApply ("HΦ" $! 0%nat); done.
    - destruct Ha as [lv' [Hlv Hlcoh]]; subst.
      gwp_match. gwp_proj. gwp_bind (list_length _).
      iApply ("IH" $! _ _ Hlcoh). iNext. iIntros; simpl.
      gwp_op. iSpecialize ("HΦ" $! (1 + v)%nat).
      rewrite Nat2Z.inj_add. iApply "HΦ"; by auto.
  Qed.

  Lemma gwp_list_iter_invariant' Φ1 Φ2 (Ψ: list A → iProp _) P E l lv handler lrest :
    (∀ (a : A) l',
        G{{{ ⌜∃ b, lrest ++ l = l' ++ a :: b⌝ ∗ P ∗ Ψ l' ∗ Φ1 (length l') a }}}
          (Val handler) (inject a) @ g; E
        {{{v, RET v; P ∗ Ψ (l' ++ [a]) ∗ Φ2 (length l') a }}}) -∗
    G{{{ ⌜is_list l lv⌝ ∗ P ∗ Ψ lrest ∗ [∗ list] i ↦ a ∈ l, Φ1 (length lrest + i) a}}}
      list_iter (Val handler) lv @ g; E
    {{{ RET #(); P ∗ Ψ (lrest++l) ∗ [∗ list] i ↦ a ∈ l, Φ2 (length lrest + i) a }}}.
  Proof.
    rewrite /list_iter.
    iInduction l as [|a l'] "IH" forall (lv lrest);
    iIntros "#Helem"; iIntros (Φ') "!# (Ha & HP & Hl & HΦ) Hk";
    iDestruct "Ha" as %Ha; simpl in Ha; subst; gwp_pures.
    - rewrite app_nil_r. iApply "Hk"; iFrame. done.
    - assert (Helemof: a ∈ a :: l').
      { constructor. }
      destruct Ha as [lv' [Hlv Hlcoh]]; subst.
      gwp_pures.
      iDestruct (big_sepL_cons with "HΦ") as "[Ha Hl']".
      rewrite Nat.add_0_r.
      gwp_apply ("Helem" with "[HP Hl Ha]"); iFrame; eauto.
      iIntros (v) "(HP & Ha & HΦ)". simpl. gwp_seq.
      iApply ("IH" $! lv' (lrest ++ [a]) with "[] [$HP Ha Hl']"); eauto.
      { iIntros (a' lrest' HΦ'') "!# (%Hin'&HP&Hlrest'&HΦ) Hk".
        gwp_apply ("Helem" with "[HP Hlrest' HΦ]"); iFrame.
        iPureIntro. destruct Hin' as [b Hin']. exists b.
        by rewrite -app_assoc in Hin'. }
      { iSplit; eauto. iFrame.
        rewrite length_app /=.
        iApply (big_sepL_impl with "Hl'").
        iIntros "!#" (???) "Hl".
        rewrite -Nat.add_1_l Nat.add_assoc //. }
      iNext. iIntros "(HP & Hl & Hlp)". iApply "Hk". iFrame.
      rewrite -app_assoc /= Nat.add_0_r length_app /=.
      iFrame.
      iApply (big_sepL_impl with "Hlp").
      iIntros "!#" (???) "Hl".
      rewrite -Nat.add_assoc.
      replace (1 + k) with (S k) by lia.
      done.
  Qed.

  Lemma gwp_list_iter_invariant Φ1 Φ2 (Ψ: list A -> iProp _) P E l lv handler :
    (∀ (a : A) l',
        G{{{ ⌜∃ b, l = l' ++ a :: b⌝ ∗ P ∗ Ψ l' ∗ Φ1 (length l') a }}}
          (Val handler) (Val (inject a)) @ g; E
        {{{v, RET v; P ∗ Ψ (l' ++ [a]) ∗ Φ2 (length l') a }}}) -∗
    G{{{ ⌜is_list l lv⌝ ∗ P ∗ Ψ [] ∗ [∗ list] i ↦ a ∈l, Φ1 i a}}}
      list_iter (Val handler) lv @ g; E
    {{{ RET #(); P ∗ Ψ l ∗ [∗ list] i ↦ a ∈ l, Φ2 i a}}}.
  Proof.
    replace l with ([]++l); last by apply app_nil_l.
    iApply gwp_list_iter_invariant'.
  Qed.

  (** TODO: do this without loeb induction *)
  (* Lemma gwp_list_iter_idx_aux n Φ Ψ P E l lv handler s : *)
  (*   (∀ i (a : A), *)
  (*       G{{{ P ∗ Φ i a }}} *)
  (*         (Val handler) (Val (inject a)) @ g; E *)
  (*       {{{v, RET v; P ∗ Ψ i a }}}) -∗ *)
  (*   G{{{ ⌜is_list l lv⌝ ∗ P ∗ [∗ list] i↦a ∈ l, Φ (n + i)%nat a }}} *)
  (*     list_iter (Val handler) lv @ g; E *)
  (*   {{{ RET #(); P ∗ [∗ list] i↦a ∈ l, Ψ (n + i)%nat a }}}. *)
  (* Proof. *)
  (*   rewrite /list_iter. *)
  (*   iIntros "#Helem"; iIntros (Φ') "!# (Ha & HP & Hl) HΦ". *)
  (*   iLöb as "IH" forall (l lv n); *)
  (*   destruct l as [|a l']; *)
  (*   iDestruct "Ha" as %Ha; simpl in Ha; subst; gwp_pures. *)
  (*   - simpl. iApply "HΦ"; eauto. *)
  (*   - assert (Helemof: a ∈ a :: l'). *)
  (*     { constructor. } *)
  (*     destruct Ha as [lv' [Hlv Hlcoh]]; subst. *)
  (*     gwp_pures. *)
  (*     iDestruct (big_sepL_cons with "Hl") as "[Ha Hl']". *)
  (*     gwp_apply ("Helem" with "[HP Ha]"); iFrame; eauto. *)
  (*     iIntros (v) "[HP Ha]". simpl. gwp_seq. *)
  (*     iApply ("IH" $! l' _ (S n) with "[] [$HP] [Hl']"); [done| |]. *)
  (*     { iApply (big_sepL_impl with "Hl' []"). *)
  (*       iIntros "!>" (k x Hlookup) "H". *)
  (*       replace (n + S k)%nat with (S n + k)%nat by lia. *)
  (*       done. } *)
  (*     iNext. iIntros "(HP & Hl)". iApply "HΦ". iFrame. *)
  (*     iApply (big_sepL_impl with "Hl []"). *)
  (*     iIntros "!>" (k x Hlookup) "H". *)
  (*     replace (n + S k)%nat with (S n + k)%nat by lia. *)
  (*     done. *)
  (* Qed. *)

  (* Lemma gwp_list_iter_idx Φ Ψ P E l lv handler s : *)
  (*   (∀ i (a : A), *)
  (*       G{{{ P ∗ Φ i a }}} *)
  (*         (Val handler) (Val (inject a)) @ g; E *)
  (*       {{{v, RET v; P ∗ Ψ i a }}}) -∗ *)
  (*   G{{{ ⌜is_list l lv⌝ ∗ P ∗ [∗ list] i↦a ∈ l, Φ i a }}} *)
  (*     list_iter (Val handler) lv @ g; E *)
  (*   {{{ RET #(); P ∗ [∗ list] i↦a ∈ l, Ψ i a }}}. *)
  (* Proof. *)
  (*   iIntros "#H" (Φ') "!# (%Ha & HP & Hl) HΦ". *)
  (*   iApply (gwp_list_iter_idx_aux 0 Φ _ _ _ _ lv with "[H] [HP $Hl] HΦ"). *)
  (*   { iIntros (i a). iApply "H". } *)
  (*   by iFrame. *)
  (* Qed. *)

  (* Lemma gwp_list_iter Φ Ψ P E l lv handler s: *)
  (*   (∀ (a : A), *)
  (*       G{{{ P ∗ Φ a }}} *)
  (*         (Val handler) (Val (inject a)) @ g; E *)
  (*       {{{v, RET v; P ∗ Ψ a }}}) -∗ *)
  (*   G{{{ ⌜is_list l lv⌝ ∗ P ∗ [∗ list] a ∈ l, Φ a }}} *)
  (*     list_iter (Val handler) lv @ g; E *)
  (*   {{{ RET #(); P ∗ [∗ list] a ∈ l, Ψ a }}}. *)
  (* Proof. *)
  (*   rewrite /list_iter. *)
  (*   iIntros "#H" (Φ') "!# (%Ha & HP & Hl) HΦ". *)
  (*   iApply (gwp_list_iter_idx with "[H] [HP $Hl] HΦ"). *)
  (*   { iIntros (i a). iApply "H". } *)
  (*   by iFrame. *)
  (* Qed. *)

  Lemma gwp_list_iteri_loop
        (k : nat) (l : list A) (fv lv : val)
        (P : iProp _) (Φ Ψ : nat -> A -> iProp _) E :
    is_list l lv →
    (∀ (i : nat) (x : A),
      G{{{ P ∗ Φ i x }}} fv #i (inject x) @ g; E {{{ v, RET v; P ∗ Ψ i x }}}) -∗
    G{{{ P ∗ ([∗ list] i ↦ a ∈ l, Φ (k+i)%nat a) }}}
      list_iteri_loop fv #k lv @ g; E
    {{{ RET #(); P ∗ [∗ list] i ↦ a ∈ l, Ψ (k+i)%nat a }}}.
  Proof.
    iIntros (Hl) "#Hf".
    iIntros (Φ') "!> [HP Hl] HΦ".
    iInduction l as [ | h l] "IH" forall (lv k Hl).
    { gwp_lam. rewrite Hl. gwp_pures. iApply "HΦ". by iFrame. }
    gwp_lam. destruct Hl as [l' [-> Hl']]. gwp_pures.
    iDestruct "Hl" as "[Ha Hl']". rewrite right_id_L.
    gwp_apply ("Hf" with "[$HP $Ha]"). iIntros (v) "[HP HΨ]".
    gwp_pures.
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

  Lemma gwp_list_iteri
        (l : list A) (fv lv : val)
        (P : iProp _) (Φ Ψ : nat -> A -> iProp _) E :
    is_list l lv →
    (∀ (i : nat) (x : A),
      G{{{ P ∗ Φ i x }}} fv #i (inject x) @ g; E {{{ v, RET v; P ∗ Ψ i x }}}) -∗
    G{{{ P ∗ ([∗ list] i ↦ a ∈ l, Φ i a) }}}
      list_iteri fv lv @ g; E
    {{{ RET #(); P ∗ [∗ list] i ↦ a ∈ l, Ψ i a }}}.
  Proof.
    iIntros (Hl) "#Hf". iIntros (Φ') "!>[HP Hown] HΦ".
    gwp_lam. gwp_pures.
    iAssert (⌜#0 = #(0%nat)⌝%I) as %->; [done |].
    iApply (gwp_list_iteri_loop 0 l with "Hf [$HP $Hown]"); [done|].
    by iFrame.
  Qed.

  Lemma gwp_list_fold P Φ Ψ E handler (l : list A) acc lv :
    (∀ (a : A) acc lacc lrem,
        G{{{ ⌜l = lacc ++ a :: lrem⌝ ∗ P lacc acc ∗ Φ a }}}
          (Val handler) (Val acc) (inject a) @ g; E
        {{{v, RET v; P (lacc ++ [a]) v ∗ Ψ a }}}) -∗
    G{{{ ⌜is_list l lv⌝ ∗ P [] acc ∗ [∗ list] a∈l, Φ a }}}
      list_fold handler acc lv @ g; E
    {{{v, RET v; P l v ∗ [∗ list] a∈l, Ψ a }}}.
  Proof.
    iIntros "#Hcl". iIntros (Ξ) "!# (Hl & Hacc & HΦ) HΞ".
    change l with ([] ++ l) at 1 4.
    generalize (@nil A) at 1 3 4 as lproc => lproc.
    iInduction l as [|x l] "IHl" forall (Ξ lproc acc lv) "Hacc Hl HΞ".
    - iDestruct "Hl" as %?; simpl in *; simplify_eq.
      gwp_rec. gwp_pures. iApply "HΞ".
      rewrite app_nil_r; iFrame; done.
    - iDestruct "Hl" as %[lw [? Hlw]]; subst.
      iDestruct "HΦ" as "[Hx HΦ]".
      gwp_rec. gwp_pures.
      gwp_apply ("Hcl" with "[$Hacc $Hx] [-]"); auto.
      iNext. iIntros (w) "[Hacc HΨ]"; simpl. gwp_pures.
      iApply ("IHl" with "[] [$HΦ] [$Hacc] [] [HΨ HΞ]"); [|auto|].
      { rewrite -app_assoc; auto. }
      iNext. iIntros (v) "[HP HΨs]".
      rewrite -app_assoc.
      iApply "HΞ"; iFrame.
  Qed.

  Lemma gwp_list_fold_generalized' E handler (l lp : list A) acc lv P Φ Ψ :
    □ (∀ (a : A) acc lacc lrem, (P lacc acc None (a::lrem) -∗ P lacc acc (Some a) lrem))%I -∗
      (∀ (a : A) acc lacc lrem,
          G{{{ ⌜lp ++ l = lacc ++ a :: lrem⌝ ∗ P lacc acc (Some a) lrem ∗ Φ a }}}
            (Val handler) (Val acc) (inject a) @ g; E
          {{{v, RET v; P (lacc ++ [a]) v None lrem ∗ Ψ a }}}) -∗
    G{{{ ⌜is_list l lv⌝ ∗ P lp acc None l ∗ [∗ list] a∈l, Φ a }}}
      list_fold (Val handler) (Val acc) (Val lv) @ g; E
    {{{v, RET v; P (lp ++ l) v None [] ∗ [∗ list] a∈l, Ψ a }}}.
  Proof.
    iIntros "#Hvs #Hcl". iIntros (Ξ) "!# (Hl & Hacc & HΦ) HΞ".
    iInduction l as [|x l] "IHl" forall (Ξ lp acc lv) "Hacc Hl HΞ".
    - iDestruct "Hl" as %?; simpl in *; simplify_eq.
      gwp_rec. gwp_pures. iApply "HΞ".
      rewrite app_nil_r; iFrame. done.
    - iDestruct "Hl" as %[lw [? Hlw]]; subst.
      iDestruct "HΦ" as "[Hx HΦ]".
      gwp_rec; gwp_pures.
      iPoseProof ("Hvs" with "Hacc") as "Hacc".
      gwp_apply ("Hcl" with "[$Hacc $Hx] [-]"); auto.
      iNext. iIntros (w) "[Hacc HΨ]"; simpl. gwp_let.
      iApply ("IHl" with "[] [$HΦ] [$Hacc] [] [HΨ HΞ]"); [|auto|].
      { rewrite -app_assoc; auto. }
      iNext. iIntros (v) "[HP HΨs]".
      rewrite -app_assoc.
      iApply "HΞ"; iFrame.
  Qed.

  Lemma gwp_list_fold' E handler (l : list A) acc lv P Φ Ψ :
    □ (∀ (a : A) acc lacc lrem, (P lacc acc None (a::lrem) -∗ P lacc acc (Some a) lrem))%I -∗
      (∀ (a : A) acc lacc lrem,
          G{{{ ⌜l = lacc ++ a :: lrem⌝ ∗ P lacc acc (Some a) lrem ∗ Φ a }}}
            (Val handler) (Val acc) (inject a) @ g; E
          {{{v, RET v; P (lacc ++ [a]) v None lrem ∗ Ψ a }}}) -∗
    G{{{ ⌜is_list l lv⌝ ∗ P [] acc None l ∗ [∗ list] a∈l, Φ a }}}
      list_fold (Val handler) (Val acc) lv @ g; E
    {{{v, RET v; P l v None [] ∗ [∗ list] a∈l, Ψ a }}}.
  Proof.
    iIntros "#Hvs #Hcl".
    iApply (gwp_list_fold_generalized' _ handler l [] with "[-]"); eauto.
  Qed.

  Lemma gwp_list_sub E k l lv :
    G{{{ ⌜is_list l lv⌝ }}}
      list_sub #k lv @ g; E
    {{{ v, RET v; ⌜is_list (take k l) v ⌝}}}.
  Proof.
   iIntros (Φ) "Hcoh HΦ".
   iInduction l as [|a l'] "IH" forall (k lv Φ);
   iDestruct "Hcoh" as %Hcoh; simpl in Hcoh; subst; gwp_rec;
   gwp_pures; case_bool_decide; gwp_if; gwp_pures.
   - iApply "HΦ"; by rewrite take_nil.
   - iApply "HΦ"; by rewrite take_nil.
   - iApply "HΦ". assert (k = O) as H1 by lia. by rewrite H1 firstn_O.
   - destruct Hcoh as [lv' [Hlv Hlcoh]]; subst.
     gwp_match. gwp_proj. gwp_bind (list_sub _ _). gwp_op.
     destruct k as [|k]; first done.
     assert (((Z.of_nat (S k)) - 1)%Z = Z.of_nat k) as -> by lia.
     iApply ("IH" $! k _ _ Hlcoh). iIntros (tl Hcoh_tl).
     iNext. gwp_pures. rewrite firstn_cons. by gwp_apply (gwp_list_cons).
  Qed.

  Lemma gwp_list_nth E (i: nat) l lv :
    G{{{ ⌜is_list l lv⌝ }}}
      list_nth (Val lv) #i @ g; E
    {{{ v, RET v; (⌜v = NONEV⌝ ∧ ⌜length l <= i⌝) ∨
              ⌜∃ r, v = SOMEV (inject r) ∧ nth_error l i = Some r⌝ }}}.
  Proof.
    iIntros (Φ) "Ha HΦ".
    iInduction l as [|a l'] "IH" forall (i lv Φ);
    iDestruct "Ha" as %Ha; simpl in Ha; subst; gwp_rec; gwp_let.
    - gwp_match. gwp_pures.
      iApply ("HΦ" $! (InjLV #())). iLeft. simpl. eauto with lia.
    - destruct Ha as [lv' [Hlv Hlcoh]]; subst.
      gwp_match. gwp_pures. case_bool_decide; gwp_pures.
      + iApply "HΦ". iRight. simpl. iExists a. by destruct i.
      + destruct i; first done.
        assert ((S i - 1)%Z = i) as -> by lia.
        iApply ("IH" $! i lv' _  Hlcoh).
        iNext. iIntros (v [ (Hv & Hs) | Hps]); simpl.
        * iApply "HΦ"; try eauto with lia.
        * iApply "HΦ"; try eauto with lia.
  Qed.

  Lemma gwp_list_nth_some E (i: nat) l lv  :
    G{{{ ⌜is_list l lv ∧ i < length l⌝ }}}
      list_nth (Val lv) #i @ g; E
    {{{ v, RET v; ⌜∃ r, v = SOMEV (inject r) ∧ nth_error l i = Some r⌝ }}}.
  Proof.
    iIntros (Φ (Hcoh & Hi)) "HΦ".
    iApply (gwp_list_nth $! Hcoh).
    iIntros (v [? | ?]); first eauto with lia.
    by iApply "HΦ".
  Qed.

  Lemma gwp_list_mem (l : list A) lv a E :
    val_is_unboxed (inject a) →
    G{{{ ⌜is_list l lv⌝ }}}
      list_mem (inject a) lv @ g; E
    {{{ (b : bool), RET #b; if b then ⌜a ∈ l⌝ else ⌜a ∉ l ∨ l = nil⌝ }}}.
  Proof.
    iIntros (? Φ).
    iInduction l as [|a' l'] "IH" forall (lv Φ);
      iIntros (Hl) "HΦ"; gwp_rec; gwp_pures.
    - rewrite Hl. gwp_pures. iApply "HΦ". auto.
    - destruct Hl as [lv' [-> Hl']]. gwp_pures.
      case_bool_decide as Heq; gwp_if.
      { simplify_eq. iApply "HΦ". iPureIntro; set_solver. }
      iApply ("IH" with "[//]").
      iIntros "!>" ([] Ha).
      { iApply "HΦ". iPureIntro; set_solver. }
      iApply "HΦ".
      iPureIntro. left.
      simplify_eq.
      destruct Ha; set_solver.
  Qed.

  Lemma gwp_remove_nth E (l : list A) lv (i : nat) :
    G{{{ ⌜is_list l lv /\ i < length l⌝ }}}
      list_remove_nth lv #i @ g; E
    {{{ v, RET v; ∃ e lv' l1 l2,
                ⌜l = l1 ++ e :: l2 ∧
                 length l1 = i /\
                v = SOMEV ((inject e), lv') ∧
                is_list (l1 ++ l2) lv'⌝ }}}.
  Proof.
    iIntros (Φ) "Ha Hφ".
    iInduction l as [|a l'] "IH" forall (i lv Φ);
      iDestruct "Ha" as "(%Hl & %Hi)"; simpl in Hl; subst; gwp_rec; gwp_let.
    - inversion Hi.
    - destruct Hl as [lv' [Hlv Hlcoh]]; subst.
      gwp_match. gwp_pures. case_bool_decide; gwp_pures.
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
        gwp_bind (list_remove_nth _ _).
        iApply ("IH" $! i lv' _  Haux).
        iNext. iIntros (v (e & v' & l1 & l2 & (-> & Hlen & -> & Hil))); simpl.
        gwp_pures.
        gwp_bind (list_cons _ _). iApply gwp_list_cons; [done|].
        iIntros "!>" (v Hcons).
        gwp_pures.
        iApply "Hφ".
        iExists e, (inject ((a :: l1) ++ l2)), (a :: l1), l2.
        iPureIntro.
        split; auto.
        split; [rewrite length_cons Hlen // |].
        split.
        * by apply is_list_inject in Hcons as ->.
        * by apply is_list_inject.
  Qed.

  Lemma gwp_remove_nth_total E (l : list A) lv (i : nat) :
    G{{{ ⌜is_list l lv /\ i < length l⌝ }}}
      list_remove_nth_total lv #i @ g; E
    {{{ v, RET v; ∃ e lv' l1 l2,
                ⌜l = l1 ++ e :: l2 ∧
                 length l1 = i /\
                v = lv' ∧
                is_list (l1 ++ l2) lv'⌝ }}}.
  Proof.
    iIntros (Φ) "Ha Hφ".
    iInduction l as [|a l'] "IH" forall (i lv Φ);
      iDestruct "Ha" as "(%Hl & %Hi)"; simpl in Hl; subst; gwp_rec; gwp_let.
    - inversion Hi.
    - destruct Hl as [lv' [Hlv Hlcoh]]; subst.
      gwp_match. gwp_pures. case_bool_decide; gwp_pures.
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
        gwp_bind (list_remove_nth_total _ _).
        iApply ("IH" $! i lv' _  Haux).
        iNext. iIntros (v (e & v' & l1 & l2 & (-> & Hlen & -> & Hil))); simpl.
        gwp_pures.
        iApply gwp_list_cons; [done |].
        iIntros "!>" (v Hcons).
        iApply "Hφ".
        iExists e, (inject ((a :: l1) ++ l2)), (a :: l1), l2.
        iPureIntro.
        split; auto.
        split; [rewrite length_cons Hlen // |].
        split.
        * by apply is_list_inject in Hcons.
        * by apply is_list_inject.
  Qed.

  Lemma gwp_list_find P Ψ Φ E (l : list A) (fv lv : val) :
    (∀ (a : A),
        G{{{ Φ a ∗ P }}}
          fv (inject a) @ g; E
         {{{ (b : bool), RET #b; P ∗ if b then Ψ a else True }}}) -∗
      G{{{ ⌜is_list l lv⌝ ∗ P ∗ [∗ list] a ∈ l, Φ a}}}
        list_find fv lv @ g; E
       {{{ v, RET v; P ∗ (⌜v = NONEV⌝ ∨ ∃ a, ⌜v = SOMEV (inject a)⌝ ∗ ⌜a ∈ l⌝ ∗ Ψ a) }}}.
  Proof.
    iIntros "#Hf".
    iInduction l as [|a l'] "IH" forall (lv);
      iIntros (Ξ) "!> (%Hl & HP & HΦ) Hcnt"; gwp_rec; gwp_pures. 
    { rewrite Hl. gwp_pures. iApply "Hcnt". iFrame "HP". by iLeft. }
    destruct Hl as [lv' [-> Hl']]. gwp_pures.
    gwp_bind (fv _).
    iDestruct "HΦ" as "[Ha HΦ]".
    iApply ("Hf" with "[$Ha $HP //]").
    iIntros "!>" (b) "[HP Hb] /=".
    destruct b.
    { gwp_pures. iApply "Hcnt". iFrame "HP".
      iModIntro. iRight. iFrame "Hb".
      iSplit; [done|]. iPureIntro. constructor. }
    gwp_pures.
    gwp_apply ("IH" with "[$HΦ $HP //]").
    iIntros (v) "Hv".
    iApply "Hcnt".
    iDestruct "Hv" as "[$ [-> | (% & -> & % & HΨ)]]"; [by iLeft|].
    iRight. iFrame. iSplit; [done|]. iPureIntro. by constructor.
  Qed.

  Lemma gwp_find_remove E (l : list A) lv (Ψ : A → iProp _) (fv : val) :
    (∀ (a : A),
        G{{{ True }}}
          fv (inject a) @ g; E
        {{{ (b : bool), RET #b; if b then Ψ a else True }}}) -∗
    G{{{ ⌜is_list l lv⌝ }}}
      list_find_remove fv lv @ g; E
    {{{ v, RET v; ⌜v = NONEV⌝ ∨
                       ∃ e lv' l1 l2,
                         ⌜l = l1 ++ e :: l2 ∧
                         v = SOMEV ((inject e), lv') ∧
                         is_list (l1 ++ l2) lv'⌝
                         ∗ Ψ e}}}.
  Proof.
    iIntros "#Hf" (Φ).
    iInduction l as [|a l'] "IH" forall (lv Φ);
      iIntros (Hl) "!> HΦ"; gwp_rec; gwp_pures.
    { rewrite Hl. gwp_pures. iApply "HΦ".
      iLeft; iPureIntro; split; set_solver. }
    destruct Hl as [lv' [-> Hl']]. gwp_pures.
    gwp_bind (fv _). iApply ("Hf" with "[//]").
    iIntros "!>" (b) "Hb /=".
    destruct b.
    { gwp_pures.
      iApply "HΦ".
      iRight; iExists _, _, [], _; eauto. }
    gwp_pures.
    gwp_bind (list_find_remove _ _).
    iApply ("IH" with "[//]").
    iIntros "!>" (w) "[->| He] /="; gwp_pures.
    { iApply "HΦ".
      iLeft; done. }
    iDestruct "He" as (e lv'' l1 l2) "[He HHΨ]".
    iDestruct "He" as %(-> & -> & Hlv'').
    gwp_pures.
    gwp_bind (list_cons _ _). iApply gwp_list_cons; [done|].
    iIntros "!>" (v Hcoh) "/=". gwp_pures.
    iApply "HΦ". iRight.
    iExists _, _, (_ :: _), _; eauto.
  Qed.

  Local Lemma gwp_list_rev_aux E l lM r rM :
   G{{{ ⌜is_list lM l ∧ is_list rM r⌝ }}}
     list_rev_aux (Val l) (Val r) @ g; E
   {{{ v, RET v; ⌜is_list (rev_append lM rM) v⌝ }}}.
  Proof.
    iIntros (? [Hl Hr]) "H".
    iInduction lM as [|a lM] "IH" forall (l r rM Hl Hr).
    - simpl in *; subst. rewrite /list_rev_aux. gwp_pures. by iApply "H".
    - destruct Hl as [l' [Hl'eq Hl']]; subst.
      gwp_rec; gwp_pures.
      gwp_apply gwp_list_cons; [done|].
      iIntros (w Hw).
      gwp_pures. by iApply "IH".
 Qed.

  Lemma gwp_list_rev E l lM :
    G{{{ ⌜is_list lM l⌝ }}}
      list_rev (Val l) @ g; E
    {{{ v, RET v; ⌜is_list (reverse lM) v⌝ }}}.
  Proof.
    iIntros (??) "H". rewrite /list_rev. gwp_pures.
    by iApply (gwp_list_rev_aux _ _ _ NONEV []).
  Qed.

  Lemma gwp_list_append E l lM r rM :
    G{{{ ⌜is_list lM l⌝ ∗ ⌜is_list rM r⌝}}}
      list_append (Val l) (Val r) @ g; E
    {{{ v, RET v; ⌜is_list (lM ++ rM) v⌝ }}}.
  Proof.
    iIntros (Φ) "[%Hl %Hr] HΦ". rewrite /list_append.
    iInduction lM as [|a lM] "IH" forall (l r Hl Hr Φ).
    - simpl in Hl; subst. gwp_pures. by iApply "HΦ".
    - destruct Hl as [l' [Hl'eq Hl']]; subst.
      do 12 gwp_pure _.
      gwp_bind (((rec: "list_append" _ _:= _)%V _ _)).
      iApply "IH"; [done..|].
      iIntros "!>" (v Hv).
      by gwp_apply gwp_list_cons.
  Qed.

  Lemma gwp_list_forall Φ Ψ E (l : list A) lv (fv : val) :
    (∀ (a : A),
        G{{{ True }}}
          fv (inject a) @ g; E
        {{{ (b : bool), RET #b; if b then Φ a else Ψ a }}}) -∗
    G{{{ ⌜is_list l lv⌝ }}}
      list_forall fv lv @ g; E
    {{{ (b : bool), RET #b; if b then [∗ list] a ∈ l, Φ a else ∃ a, ⌜a ∈ l⌝ ∗ Ψ a }}}.
  Proof.
    rewrite /list_forall.
    iInduction l as [|a l'] "IH" forall (lv);
      iIntros "#Hfv" (Ξ) "!# %Hl HΞ".
    - simpl in Hl; subst. gwp_pures. iApply "HΞ"; auto.
    - destruct Hl as [l'' [Hl'eq Hl']]; subst.
      gwp_pures.
      gwp_apply "Hfv"; [done|].
      iIntros ([]) "Hb".
      + gwp_if. iApply ("IH"); [done..|].
        iIntros "!>" ([]).
        * iIntros "Ha". iApply "HΞ".
          rewrite big_sepL_cons. iFrame.
        * iDestruct 1 as (a') "[% ?]".
          iApply "HΞ". iExists _. iFrame.
          iPureIntro. apply elem_of_cons. by right.
      + gwp_if. iApply "HΞ". iExists _. iFrame.
        iPureIntro. apply elem_of_cons. by left.
  Qed.

  Lemma gwp_list_is_empty l v E :
    G{{{ ⌜is_list l v⌝ }}}
      list_is_empty v @ g; E
    {{{ RET #(match l with [] => true | _ => false end); True }}}.
  Proof.
    iIntros (Φ Hl) "HΦ". gwp_rec. destruct l.
    - rewrite Hl. gwp_pures. by iApply "HΦ".
    - destruct Hl as [? [-> _]]. gwp_pures. by iApply "HΦ".
  Qed.

  Lemma is_list_eq lM :
    ∀ l1 l2, is_list lM l1 → is_list lM l2 → l1 = l2.
  Proof. induction lM; intros []; naive_solver eauto with f_equal. Qed.

  Lemma is_list_inv_l l:
    ∀ lM1 lM2, is_list lM1 l → lM1 = lM2 → is_list lM2 l.
  Proof. by intros ? ? ? <-. Qed.

  Lemma is_list_snoc lM x : ∃ lv, is_list (lM ++ [x]) lv.
  Proof. induction lM; naive_solver eauto. Qed.

  Lemma gwp_list_filter (P : A → bool) (l : list A) (f lv : val) E :
    G{{{ (∀ (x : A),
            G{{{ True }}}
              f (inject x) @ g; E
            {{{ w, RET w; ⌜w = inject (P x)⌝ }}}) ∗
        ⌜is_list l lv⌝ }}}
       list_filter f lv @ g; E
     {{{ rv, RET rv; ⌜is_list (filter P l) rv⌝ }}}.
  Proof.
    iIntros (Φ) "[#Hf %Hil] HΦ".
    iInduction l as [ | h t] "IH" forall (lv Hil Φ); simpl in Hil.
    - subst.
      rewrite /list_filter; gwp_pures.
      iApply "HΦ"; done.
    - destruct Hil as (lv' & -> & Hil).
      rewrite /list_filter.
      do 7 (gwp_pure _).
      fold list_filter.
      gwp_apply ("IH" $! lv'); [done |].
      iIntros (rv) "%Hilp"; gwp_pures.
      gwp_apply "Hf"; [done |].
      iIntros (w) "->".
      destruct (P h) eqn:Heq ; gwp_pures.
      + gwp_apply gwp_list_cons; [by eauto |].
        iIntros (v) "%Hil'".
        iApply "HΦ"; iPureIntro.
        rewrite filter_cons_True //.
        rewrite Heq //. 
      + iApply "HΦ"; iPureIntro.
        rewrite filter_cons_False //.
        rewrite Heq //. intros []. 
  Qed.
End list_specs.

Global Arguments gwp_list_nil : clear implicits.
Global Arguments gwp_list_nil {_ _ _} _ {_}.

(* Start a new section because some of the specs below (e.g. gwp_list_map) need
   access to the type parameter in e.g. is_list, since they operate on more than one
   list type. *)
Section list_specs_extra.
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.
  Context `[!Inject A val].

  Lemma gwp_list_map `{!Inject B val} (l : list A) (f : A -> B) (fv lv : val) E :
    G{{{ (∀ (x : A),
          G{{{ True }}}
            fv (inject x) @ g; E
          {{{ fr, RET fr; ⌜fr = inject (f x)⌝ }}}) ∗
          ⌜is_list l lv⌝ }}}
      list_map fv lv @ g; E
    {{{ rv, RET rv; ⌜is_list (List.map f l) rv⌝ }}}.
  Proof.
    iIntros (Φ) "[#Hf %Hil] HΦ".
    iInduction l as [ | h t] "IH" forall (lv Hil Φ); simpl in Hil; try subst; rewrite /list_map.
    - gwp_pures.
      iApply "HΦ"; iPureIntro.
      rewrite /is_list; done.
    - gwp_pures.
      destruct Hil as (lv' & -> & Hil').
      do 4 gwp_pure _.
      fold list_map.
      gwp_apply "IH"; [done |].
      iIntros (rv) "%Hil_rv"; gwp_pures.
      gwp_apply "Hf"; [done |].
      iIntros (fr) "->".
      gwp_apply gwp_list_cons; [done |].
      iIntros (v) "%Hilf".
      iApply "HΦ"; auto.
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

  Lemma mapi_length {B} (f : nat -> A -> B) (xs : list A) : length (mapi f xs) = length xs.
  Proof. rewrite /mapi. generalize 0%nat. induction xs => //= ?. by rewrite IHxs. Qed.

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
  Lemma gwp_list_mapi_loop `{!Inject B val}
        (f : nat -> A -> B) (k : nat) (l : list A) (fv lv : val)
        (γ : nat -> A -> iProp _) (ψ : nat -> B -> iProp _) E :
    G{{{ □ (∀ (i : nat) (x : A),
              G{{{ γ (k + i)%nat x }}}
                fv (inject (k + i)%nat) (inject x) @ g; E
                {{{ fr, RET fr;
                    let r := f (k + i)%nat x in
                    ⌜fr = (inject r)⌝ ∗ ψ (k + i)%nat r }}}) ∗
        ⌜is_list l lv⌝ ∗
        ([∗ list] i ↦ a ∈ l, γ (k + i)%nat a)
    }}}
      list_mapi_loop fv #k lv @ g; E
    {{{ rv, RET rv;
        let l' := mapi_loop f k l in
        ⌜is_list l' rv⌝ ∗
        ([∗ list] i ↦ a ∈ l', ψ (k + i)%nat a)}}}.
  Proof.
    iInduction l as [ | h l'] "IH" forall (lv k);
      iIntros (Φ) "[#Hf [%Hil Hown]] HΦ"; simpl in Hil;
      rewrite /list_mapi_loop.
    - subst.
      gwp_pures.
      iApply "HΦ".
      iSplitL ""; done.
    - destruct Hil as [lv' [-> Hil']].
      do 10 gwp_pure _.
      fold list_mapi_loop.
      gwp_bind (list_mapi_loop _ _ _).
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
        gwp_pures.
        iAssert (⌜#k = (inject (k + 0)%nat)⌝%I) as %->.
        { simpl.
          iPureIntro.
          do 2 f_equal.
          lia. }
        gwp_apply ("Hf" with "Hhead").
        iIntros (fr) "[-> HΨ]".
        gwp_apply gwp_list_cons; [done | ].
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

  Lemma gwp_list_mapi `{!Inject B val}
        (f : nat -> A -> B) (l : list A) (fv lv : val)
        (γ : nat -> A -> iProp _) (ψ : nat -> B -> iProp _) E :
    G{{{ □ (∀ (i : nat) (x : A),
              G{{{ γ i x }}}
                fv #i (inject x) @ g; E
                {{{ fr, RET fr;
                    let r := f i x in
                    ⌜fr = (inject r)⌝ ∗ ψ i r }}}) ∗
        ⌜is_list l lv⌝ ∗
        ([∗ list] i ↦ a ∈ l, γ i a)
    }}}
      list_mapi fv lv @ g; E
    {{{ rv, RET rv;
        let l' := mapi f l in
        ⌜is_list l' rv⌝ ∗
        ([∗ list] i ↦ a ∈ l', ψ i a)}}}.
  Proof.
    iIntros (Φ) "[#Hf [%Hil Hown]] HΦ".
    rewrite /list_mapi.
    do 3 gwp_pure _.
    iAssert (⌜#0 = #(0%nat)⌝%I) as %->; [done |].
    iApply (gwp_list_mapi_loop with "[Hown]").
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

  Lemma gwp_list_seq E n m :
    G{{{ True }}}
      list_seq #n #m @ g; E
    {{{ v, RET v; ⌜is_list (seq n m) v⌝ }}}.
  Proof.
    iIntros (Φ) "_ Hφ".
    iInduction m as [ | p] "IHm" forall (n Φ).
    - rewrite /list_seq.
      gwp_pures.
      iApply "Hφ".
      iPureIntro.
      rewrite /seq.
      by apply is_list_inject.
    - rewrite /list_seq.
      gwp_rec.
      do 6 gwp_pure.
      assert (#(S p - 1) = #p) as ->.
      { do 3 f_equal. lia. }
      fold list_seq.
      assert (#(n + 1) = #(Z.of_nat (S n))) as ->.
      { do 3 f_equal. lia. }
      gwp_apply "IHm".
      iIntros (v Hv).
      gwp_apply (gwp_list_cons with "[//]").
      iIntros (v' Hv').
      iApply "Hφ".
      iPureIntro.
      apply (is_list_inject) in Hv' as ->.
      by apply is_list_inject.
  Qed.

  Lemma gwp_list_suf E (n:nat) l lv :
    G{{{ ⌜is_list l lv⌝ }}}
      list_suf #n lv @ g; E
    {{{ v, RET v; ⌜is_list (drop n l) v⌝ }}}.
  Proof.
   iIntros (Φ) "%Hl HΦ".
   iInduction l as [|a l'] "IH" forall (n lv Hl Φ) "HΦ".
   - rewrite /list_suf.
     inversion Hl; subst.
     gwp_pures. case_bool_decide; gwp_pures.
     all: (iModIntro; iApply "HΦ"; simpl; rewrite drop_nil; iPureIntro; constructor).
   - inversion Hl as [? [-> Hl']]. rewrite /list_suf.
     gwp_pures. case_bool_decide; gwp_pure.
     + iModIntro. iApply "HΦ".
       iPureIntro. replace n with 0; last first.
       { simplify_eq. lia. }
       simpl. naive_solver.
     + rewrite -/list_suf.
       gwp_pures.
       replace (n-1)%Z with (Z.of_nat (n-1)); last first.
       { assert (n≠0); [naive_solver|lia].
       }
       iApply "IH"; try done.
       iModIntro. iIntros. iApply "HΦ".
       iPureIntro.
       replace (drop _ (_::_)) with (drop (n-1) l'); first done.
       erewrite <-skipn_cons. f_equal.
       assert (n≠0); [naive_solver|lia].
  Qed.

  Lemma gwp_list_inf_ofs E (n ofs:nat) l lv :
    G{{{ ⌜is_list l lv⌝ }}}
      list_inf_ofs #n #ofs lv @ g; E
    {{{ v, RET v; ⌜is_list (take ofs (drop n l)) v⌝ }}}.
  Proof.
    iIntros (Φ) "%Hl HΦ".
    rewrite /list_inf_ofs.
    gwp_pures; case_bool_decide; gwp_pures.
    - iModIntro. iApply "HΦ". iPureIntro. assert (ofs = 0) as -> by lia.
      rewrite take_0. constructor.
    - gwp_apply gwp_list_suf; first done.
      iIntros (v) "%". gwp_apply gwp_list_sub; first done.
      done.
  Qed.

  Lemma gwp_list_inf E (i j:nat) l lv :
    i<=j->
    G{{{ ⌜is_list l lv⌝ }}}
      list_inf #i #j lv @ g; E
    {{{ v, RET v; ⌜is_list (take (j-i+1) (drop i l)) v⌝ }}}.
  Proof.
    iIntros (Hineq Φ) "%Hl HΦ".
    rewrite /list_inf.
    gwp_pures.
    replace (_-_+1)%Z with (Z.of_nat (j-i+1)) by lia.
    gwp_apply gwp_list_inf_ofs; first done.
    done.
  Qed.

  Definition List_max_index_aux y xs :=
    List.fold_left
      (λ '(y, iy, ix) x,
         if (Z.ltb y x)%Z then (x, ix, ix+1)%nat else (y, iy, ix+1)%nat)
      xs (y, 0, 1)%nat.

  Definition List_max_index (xs : list Z) : nat :=
  match xs with
  | [] => 0%nat
  | y :: xs =>
      let '(_, iy, _) :=
        List_max_index_aux y xs
      in iy
  end.

  Lemma gwp_list_max_index_aux E (y : Z) xs vxs :
    G{{{ ⌜is_list xs vxs⌝ }}}
      list_max_index_aux #y vxs @ g ; E
                 {{{ (y' : Z) (ix iy : nat), RET (#y', #iy, #ix); ⌜(y', iy, ix) = List_max_index_aux y xs⌝}}}.
  Proof.
    iIntros "%post %hxs hpost".
    rewrite /list_max_index_aux. gwp_pures.
    gwp_apply (gwp_list_fold
                 (λ l v, ∃ (y' : Z) (iy' ix : nat),
                     ⌜v = (#y', #iy', #ix)%V⌝ ∗
                     ⌜(y', iy', ix) = List_max_index_aux y l⌝ )
                 (λ _, emp) (λ _, emp))%I.
    2:{ repeat iSplit => //. iExists _,_,_. rewrite /List_max_index_aux /=.
        iSplit => //. done. }
    2:{ iIntros "%v ((%y' & %iy' & %ix' & %eq1 & %eq2) & _)".
        rewrite eq1. iApply "hpost". done. }
    iIntros. iIntros "%post' !> (%&(%&%&%&->&%IH)&_) hpost'".
    simplify_eq.
    gwp_pures.
    rewrite /List_max_index_aux.
    rewrite fold_left_app.
    rewrite /List_max_index_aux in IH. rewrite -IH.
    case_bool_decide ; gwp_pures ; iModIntro ;
      replace (Z.of_nat ix+1)%Z with (Z.of_nat $ ix+1) by lia.
    - iApply "hpost'". iSplit => //. iExists _,_,_. iPureIntro.
      intuition auto => /=.
      destruct (y' <? a)%Z eqn:h ; try apply Z.ltb_lt in h ; try lia.
      reflexivity.
    - iApply "hpost'". iSplit => //. iExists _,_,_. iPureIntro.
      intuition auto => /=.
      destruct (y' <? a)%Z eqn:h ; try apply Z.ltb_lt in h ; try lia.
      reflexivity.
  Qed.

  Lemma gwp_list_max_index E xs vxs :
    G{{{ ⌜is_list xs vxs⌝ }}}
      list_max_index vxs @ g ; E
                 {{{ (i : nat), RET #i; ⌜i = List_max_index xs⌝}}}.
  Proof.
    iIntros (Φ) "%Hxs HΦ". rewrite /list_max_index.
    gwp_pures.
    rewrite /List_max_index.
    destruct xs as [|y xs'].
    { rewrite Hxs. gwp_pures.
      replace 0%Z with (Z.of_nat 0) => //.
      iApply "HΦ". done. }
    destruct Hxs as (vxs' & -> & Hxs'). gwp_pures.
    gwp_bind (list_max_index_aux _ _).
    iApply gwp_list_max_index_aux => //.
    iIntros "!> % % % <-". gwp_pures. by iApply "HΦ".
  Qed.

  Lemma gwp_list_hd E xs vxs :
    G{{{ ⌜is_list xs vxs⌝ ∗ ⌜0 < length xs⌝ }}}
      list_hd vxs @ g ; E
                 {{{ v, RET v; ⌜List.hd v xs = v⌝}}}.
  Proof.
    iIntros (Φ) "(%Hxs & %Hlen) HΦ". rewrite /list_hd.
    gwp_pures.
    destruct xs as [|v xs]. 1: simpl in Hlen ; by (exfalso ; lia).
    simpl in Hxs.
    destruct Hxs as (? & -> & ?). gwp_pures.
    iApply "HΦ". done.
  Qed.

  Lemma gwp_list_tl E xs vxs :
    G{{{ ⌜is_list xs vxs⌝ ∗ ⌜0 < length xs⌝ }}}
      list_tl vxs @ g ; E
                 {{{ v, RET v; ⌜is_list (List.tl xs) v⌝}}}.
  Proof.
    iIntros (Φ) "(%Hxs & %Hlen) HΦ". rewrite /list_tl.
    gwp_pures.
    destruct xs as [|v xs]. 1: simpl in Hlen ; by (exfalso ; lia).
    simpl in Hxs.
    destruct Hxs as (? & -> & ?). gwp_pures.
    iApply "HΦ". done.
  Qed.

End list_specs_extra.
