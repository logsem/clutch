From iris.base_logic.lib Require Import fancy_updates.
From clutch.common Require Export inject.
From clutch.prob_lang Require Export lang notation gwp.gen_weakestpre.
Set Default Proof Using "Type*".

Module LinkedList.

  Definition empty : val :=
    λ: <>, ref NONE.

  Definition insert : val :=
    λ: "l" "v", ref (SOME ("v", "l")).

  Definition head : val :=
    λ: "l",
      match: !"l" with
        NONE => NONE
      | SOME "p" => SOME (Fst "p")
      end.

  Definition tail : val :=
    λ: "l",
      match: !"l" with
        NONE => NONE
      | SOME "p" => SOME (Snd "p")
      end.

  Definition mem : val :=
    rec: "mem" "l" "v" :=
      match: !"l" with
        NONE => #false
      | SOME "p" =>
          let, ("w", "next") := "p" in
          ("w" = "v") || "mem" "next" "v"
      end.

  Definition find_aux : val :=
    rec: "find" "l" "f" "idx" :=
      match: !"l" with
        NONE => NONE
      | SOME "p" =>
          let, ("v", "next") := "p" in
          if: "f" "v" then SOME ("idx", "v")
          else "find" "next" "f" ("idx" + #1)
      end.

  Definition find : val :=
    λ: "l" "f", find_aux "l" "f" #0%nat.

  Definition alter : val :=
    rec: "alter" "l" "f" "idx"  :=
      match: !"l" with
        NONE => #()
      | SOME "p" =>
          let, ("v", "next") := "p" in
          if: "idx" = #0%nat then
            "l" <- SOME ("f" "v", "next")
          else
            "alter" "next" "f" ("idx" - #1%nat)
      end.

  Definition nth : val :=
    rec: "nth" "l" "idx" :=
      match: !"l" with
        NONE => NONE
      | SOME "p" =>
          let, ("w", "next") := "p" in
          if: "idx" = #0 then SOME "w" else "nth" "next" ("idx" - #1)
      end.

  Definition filter : val :=
    rec: "filter" "l" "f" :=
      match: !"l" with
        NONE => "l"
      | SOME "p" =>
          let, ("v", "next") := "p" in
          let: "l'" := "filter" "next" "f" in
          if: "f" "v" then "l" <- SOME ("v", "l'");; "l"
          else "l'"
      end.

End LinkedList.

Section LinkedList.
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.
  Context `[A : Type, !Inject A val].

  Implicit Types a : A.

  #[local] Notation "l G↦ dq v" := (gwp_pointsto g l dq v)
    (at level 20, dq custom dfrac at level 1, format "l  G↦ dq  v") : bi_scope.

  Fixpoint is_linked_list (l : loc) (vs : list A) : iProp Σ :=
    match vs with
    | nil => l G↦ NONEV
    | a :: vs => ∃ (l' : loc), l G↦ SOMEV (inject a, #l') ∗ is_linked_list l' vs
  end.

  #[global] Instance is_linked_list_Timeless l vs :
    Timeless (is_linked_list l vs).
  Proof. induction vs in l |-*; apply _. Qed.

  Import LinkedList.

  Lemma gwp_linked_list_empty E :
    G{{{ True }}}
      empty #() @ g; E
    {{{ l, RET #l; is_linked_list l [] }}}.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /empty.
    gwp_pures. gwp_alloc l.
    iModIntro. by iApply "HΦ".
  Qed.

  Lemma gwp_linked_list_insert a l vs E :
    G{{{ is_linked_list l vs }}}
      insert #l (inject a) @ g; E
    {{{ l', RET #l'; is_linked_list l' (a :: vs) }}}.
  Proof.
    iIntros (Φ) "H HΦ".
    rewrite /insert. gwp_pures. gwp_alloc l' as "H'". iModIntro. iApply "HΦ".
    iExists l. iFrame.
  Qed.

  Lemma gwp_linked_list_head l vs E :
    G{{{ is_linked_list l vs }}}
      head #l @ g; E
    {{{ RET (inject (List.head vs)); is_linked_list l vs }}}.
  Proof.
    iIntros (Φ) "H HΦ". rewrite /head. gwp_pures.
    destruct vs => /=.
    - gwp_load. gwp_pures. iModIntro. by iApply "HΦ".
    - iDestruct "H" as (l') "[Hl Hl']".
      gwp_load. gwp_pures. iModIntro. iApply "HΦ". iFrame.
  Qed.

  Lemma gwp_linked_list_tail l vs E :
    G{{{ is_linked_list l vs }}}
      tail #l @ g; E
    {{{ (o : option val), RET (inject o);
        from_option
          (λ w, ∃ (l' : loc) a vs', ⌜vs = a :: vs'⌝ ∗ ⌜w = #l'⌝ ∗ l G↦ SOMEV (inject a, #l') ∗ is_linked_list l' vs')
          (⌜vs = []⌝ ∗ is_linked_list l vs) o }}}.
  Proof.
    iIntros (Φ) "H HΦ". rewrite /tail /=. gwp_pures.
    destruct vs eqn:Heq.
    - gwp_load. gwp_pures. iModIntro. iApply ("HΦ" $! None). by iFrame.
    - iDestruct "H" as (l') "[Hl Hl']".
      gwp_load. gwp_pures. iModIntro. iApply ("HΦ" $! (Some _)). by iFrame.
  Qed.

  Lemma gwp_linked_list_tail_cons E l vs a :
    G{{{ is_linked_list l (a :: vs) }}}
      tail #l @ g; E
    {{{ (l' : loc), RET SOMEV #l'; l G↦ SOMEV (inject a, #l') ∗ is_linked_list l' vs }}}.
  Proof.
    iIntros (Φ) "H HΦ".
    gwp_apply (gwp_linked_list_tail with "H").
    iIntros ([]) "(% & % & H) /="; [|simplify_eq].
    iDestruct "H" as (???) "[Hl Hl']". simplify_eq.
    iApply "HΦ". iFrame.
  Qed.

  Lemma gwp_linked_list_mem `{!EqDecision A} l (vs : list A) a E :
    Forall (vals_compare_safe (inject a)) (inject <$> vs) →
    G{{{ is_linked_list l vs }}}
      mem #l (inject a) @ g ; E
    {{{ RET #(bool_decide (a ∈ vs)); is_linked_list l vs }}}.
  Proof.
    iIntros (Hcmp Φ) "H HΦ".
    iInduction vs as [|a' vs] "IH" forall (l).
    - rewrite /mem. gwp_load. gwp_pures.
      iModIntro. by iApply "HΦ".
    - rewrite {2}/mem /=.
      iDestruct "H" as (l') "[Hl Hl']".
      inversion_clear Hcmp.
      gwp_load. gwp_pures.
      destruct (decide (a' = a)) as [->|?].
      + iEval (rewrite bool_decide_eq_true_2).
        gwp_pures.
        assert (bool_decide (a ∈ a :: vs) = true) as ->.
        { apply bool_decide_eq_true_2. left. }
        iApply "HΦ". by iFrame.
      + assert (bool_decide (inject a' = inject a) = false) as ->.
        { rewrite bool_decide_eq_false_2 //. intros ?. simplify_eq. }
        gwp_if.
        gwp_apply ("IH" with "[//] Hl'").
        iIntros "Hl'".
        assert (bool_decide (a ∈ a' :: vs) = bool_decide (a ∈ vs)) as ->.
        { do 2 case_bool_decide; set_solver. }
        iApply "HΦ". iFrame.
  Qed.

  #[local] Lemma gwp_linked_list_find_aux l vs (f : val) E (n : nat) (P : A → Prop) `{∀ x, Decision (P x)} :
    (∀ a,
      G{{{ True }}} f (inject a) @ g; E {{{ RET #(bool_decide (P a)); True }}}) ⊢
    G{{{ is_linked_list l vs }}}
      find_aux #l f #n @ g ; E
    {{{ (o : option val), RET (inject o); is_linked_list l vs ∗
          from_option (λ w, ∃ (m : nat) a, ⌜w = (#(n + m), inject a)%V⌝ ∗
                                ⌜vs !! m = Some a ∧ P a ∧ ∀ j y, vs !! j = Some y → j < m → ¬P y⌝)
          (⌜Forall (λ x, ¬ P x) vs⌝) o }}}.
  Proof.
    iIntros "#Hf" (Ψ) "!# H HΨ".
    iInduction vs as [|v' vs] "IH" forall (l Ψ n).
    - rewrite /find_aux. gwp_pures. gwp_load. gwp_pures.
      iModIntro. iApply ("HΨ" $! None). iFrame. done.
    - rewrite {2}/find_aux. gwp_rec. rewrite -/find_aux /=. gwp_pures.
      iDestruct "H" as (l') "[Hl Hl']".
      gwp_load. gwp_pures.
      gwp_apply "Hf"; [done|]. iIntros "_".
      case_bool_decide.
      + gwp_pures. iModIntro. iApply ("HΨ" $! (Some _)).
        iFrame "∗ %". iExists 0.
        assert (#(n + 0%nat) = #n) as -> by (do 2 f_equal; lia).
        iPureIntro.
        eexists. do 3 (split; [done|]). lia.
      + gwp_pures.
        replace #(n + 1) with #(n + 1)%nat by (do 2 f_equal; lia).
        gwp_apply ("IH" with "Hl'").
        iIntros (o) "[Hl' Ho]".
        iApply "HΨ". iFrame.
        destruct o.
        * iDestruct "Ho" as (?? -> ??) "%Hlt".
          iExists (S m), _. iFrame "%".
          iPureIntro. split.
          { do 3 f_equal. lia. }
          simpl.
          do 2 (split; [done|]).
          intros ????.
          destruct j; simplify_eq/=; [done|].
          eapply Hlt; [done|]. lia.
        * iDestruct "Ho" as %?. iPureIntro. by apply Forall_cons.
  Qed.

  Lemma gwp_linked_list_find l vs (f : val) E (P : A → Prop) `{∀ x, Decision (P x)} :
    (∀ a,
      G{{{ True }}} f (inject a) @ g; E {{{ RET #(bool_decide (P a)); True }}}) ⊢
    G{{{ is_linked_list l vs }}}
      find #l f @ g ; E
    {{{ RET (inject (list_find P vs)); is_linked_list l vs }}}.
  Proof.
    iIntros "#Hf" (Ψ) "!# H HΨ".
    rewrite /find. gwp_pures.
    gwp_apply (gwp_linked_list_find_aux with "Hf H").
    iIntros (o) "[Hl Ho]".
    destruct o.
    - iDestruct "Ho" as (n w -> ??) "%".
      assert (list_find P vs = Some (n, w)) as -> by by apply list_find_Some.
      replace (#(0%nat + n)) with #n by (do 2 f_equal; lia).
      by iApply "HΨ".
    - iDestruct "Ho" as %?.
      assert (list_find P vs = None) as -> by by apply list_find_None.
      by iApply "HΨ".
  Qed.

  Lemma gwp_linked_list_alter l vs idx (f : A → A) (fv : val) E :
    (∀ a,
      G{{{ True }}} fv (inject a) @ g; E {{{ RET (inject (f a)); True }}}) ⊢
    G{{{ is_linked_list l vs }}}
      alter #l fv #idx @ g ; E
    {{{ RET #(); is_linked_list l (list_alter f idx vs) }}}.
  Proof.
    iIntros "#Hf" (Ψ) "!# Hl HΨ".
    iInduction vs as [|v' vs] "IH" forall (l idx).
    - rewrite /alter. gwp_pures. gwp_load. gwp_pures. by iApply "HΨ".
    - rewrite {2}/alter. gwp_rec. rewrite -/alter /=. gwp_pures.
      iDestruct "Hl" as (l') "[Hl Hl']".
      gwp_load. gwp_pures.
      case_bool_decide; simplify_eq.
      + gwp_pures. gwp_apply "Hf"; [done|]. iIntros "_".
        gwp_store. iModIntro. iApply "HΨ". iFrame.
      + gwp_pures.
        destruct idx; [done|].
        replace #(S idx - 1%nat) with #idx by (do 2 f_equal; lia).
        gwp_apply ("IH" with "Hl'").
        iIntros "Hl'".
        iApply "HΨ". iFrame.
  Qed.

  Lemma gwp_linked_list_nth l vs (k : nat) E :
    G{{{ is_linked_list l vs }}}
      nth #l #k @ g; E
    {{{ RET (inject (vs !! k)); is_linked_list l vs }}}.
  Proof.
    iIntros (Φ) "H HΦ".
    iInduction vs as [|v' vs] "IH" forall (l k).
    - rewrite /nth. gwp_pures. gwp_load. gwp_pures. by iApply "HΦ".
    - rewrite {2}/nth. iSimpl in "H".
      gwp_pures. rewrite -/nth.
      iDestruct "H" as (l') "[Hl Hl']".
      gwp_load. gwp_pures.
      case_bool_decide as Hk.
      + gwp_pures. iModIntro.
        rewrite -Nat2Z.inj_0 in Hk.
        simplify_eq => /=.
        iApply "HΦ". by iFrame.
      + gwp_pures.
        destruct k; [done|].
        replace #(S k - 1) with #k by (do 2 f_equal; lia).
        gwp_apply ("IH" with "Hl'").
        iIntros "Hl'".
        iApply "HΦ". by iFrame.
  Qed.

  Lemma gwp_linked_list_filter l vs (f : val) E (P : A → Prop) `{∀ x, Decision (P x)} :
    (∀ a,
      G{{{ True }}} f (inject a) @ g; E {{{ RET #(bool_decide (P a)); True }}}) ⊢
    G{{{ is_linked_list l vs }}}
      filter #l f @ g; E
     {{{ l', RET #l'; is_linked_list l' (base.filter P vs) }}}.
  Proof.
    iIntros "#Hf" (Ψ) "!# Hl HΨ".
    iInduction vs as [|v vs] "IH" forall (l Ψ).
    - rewrite /filter. gwp_pures. gwp_load. gwp_pures. by iApply "HΨ".
    - rewrite {2}/filter. gwp_rec. rewrite -/filter /=. gwp_pures.
      iDestruct "Hl" as (next) "[Hl Hnext]".
      gwp_load. gwp_pures.
      gwp_apply ("IH" with "Hnext").
      iIntros (l') "Hl'". gwp_pures.
      gwp_apply ("Hf" with "[//]"); iIntros "_".
      case_bool_decide.
      + gwp_pures. gwp_store. iApply "HΨ".
        rewrite filter_cons_True //. by iFrame.
      + gwp_pures. iModIntro. iApply "HΨ".
        rewrite filter_cons_False //.
  Qed.

End LinkedList.
