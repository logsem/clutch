From clutch Require Export clutch.

Set Default Proof Using "Type*".


Section list.

(* Simple linked list with operations operating on indices of list *)

  Definition get_list_idx : val :=
    (rec: "get" "h" "idx" :=
       match: !"h" with
         NONE => NONE
       | SOME "p" =>
           let: "kv" := Fst "p" in
           let: "next" := Snd "p" in
           if: "idx" = #0 then SOME ("kv") else "get" "next" ("idx" - #1)
       end).

  Definition cons_list : val :=
    λ: "h" "v", ref (SOME ("v", "h")).

  Definition init_list : val :=
    λ:<>, ref NONE.

  Context `{!clutchRGS Σ}.

  (* Impl *)
  Fixpoint linked_list (l : loc) (vs : list val) : iProp Σ :=
    match vs with
    | nil => l ↦ NONEV
    | v :: vs => ∃ (l' : loc), l ↦ SOMEV (v, #l') ∗ linked_list l' vs
  end.

  (* Spec/ghost *)
  Fixpoint linked_slist (l : loc) (vs : list val) : iProp Σ :=
    match vs with
    | nil => l ↦ₛ NONEV
    | v :: vs => ∃ (l' : loc), l ↦ₛ SOMEV (v, #l') ∗ linked_slist l' vs
  end.

  #[global] Instance timeless_linked_list l vs :
    Timeless (linked_list l vs).
  Proof. revert l. induction vs as [| ?] => l /=; apply _. Qed.

  #[global] Instance timeless_linked_slist l vs :
    Timeless (linked_slist l vs).
  Proof. revert l. induction vs as [| ?] => l /=; apply _. Qed.

  Lemma wp_init_list E :
    {{{ True }}}
      init_list #() @ E
    {{{ l, RET LitV (LitLoc l); linked_list l nil }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /init_list. wp_pures. wp_alloc l. iModIntro. iApply "HΦ". eauto.
  Qed.

  Lemma spec_init_list E K :
    ↑specN ⊆ E →
    refines_right K (init_list #()) ={E}=∗ ∃ (l: loc), refines_right K (#l) ∗ linked_slist l [].
  Proof.
    iIntros (?) "H".
    rewrite /init_list.
    tp_pures.
    tp_alloc as l "Hl".
    iExists _. iFrame. auto.
  Qed.

  Lemma wp_cons_list E l vs (v : val) :
    {{{ linked_list l vs }}}
      cons_list #l v @ E
    {{{ l', RET LitV (LitLoc l'); linked_list l' (v :: vs) }}}.
  Proof.
    iIntros (Φ) "H HΦ".
    rewrite /cons_list. wp_pures. wp_alloc l' as "H'". iModIntro. iApply "HΦ".
    iExists l. iFrame.
  Qed.

  Lemma spec_cons_list E K l vs (v : val) :
    ↑specN ⊆ E →
    linked_slist l vs -∗
    refines_right K (cons_list #l v) ={E}=∗
    ∃ (l: loc), refines_right K (#l) ∗ linked_slist l (v :: vs).
  Proof.
    iIntros (?) "H Hr".
    rewrite /cons_list.
    tp_pures.
    tp_alloc as l' "Hl".
    iExists _. iFrame. iExists _; iFrame. auto.
  Qed.

  Definition opt_to_val (ov: option val) :=
    match ov with
    | Some v => SOMEV v
    | None => NONEV
    end.

  Lemma wp_get_list_idx E l vs (k: nat) :
    {{{ linked_list l vs }}}
      get_list_idx #l #k @ E
    {{{ v, RET v;
        linked_list l vs ∗ ⌜ v = opt_to_val (vs !! k) ⌝
    }}}.
  Proof.
    iIntros (Φ) "Hassoc HΦ".
    rewrite /get_list_idx. iInduction vs as [|v' vs] "IH" forall (l k).
    - wp_pures. rewrite /linked_list. wp_load. wp_pures. iModIntro. iApply "HΦ"; auto.
    - wp_pures. iDestruct "Hassoc" as (?) "(Hl&Hassoc)". rewrite -/linked_list.
      wp_load. wp_pures. case_bool_decide as Hcase.
      { wp_pures. inversion Hcase. destruct k; try lia; [].
        iApply "HΦ". simpl.
        iModIntro. iSplit; last done. iExists _; iFrame; eauto. }
      { wp_pure. wp_pure. destruct k.
        { exfalso. apply Hcase. f_equal. }
        replace ((Z.of_nat (S k) - 1))%Z with (Z.of_nat k) by lia; last first.
        iApply ("IH" with "[$]"). iNext.
        iIntros (v) "Hfind". iApply "HΦ".
        iEval simpl. 
        iDestruct "Hfind" as "(?&$)". iExists _; iFrame.
      }
  Qed.

  Lemma wp_get_list_idx_Z E l vs (z: Z) :
    (0 ≤ z)%Z →
    {{{ linked_list l vs }}}
      get_list_idx #l #z @ E
    {{{ v, RET v;
        linked_list l vs ∗ ⌜ v = opt_to_val (vs !! (Z.to_nat z)) ⌝
    }}}.
  Proof.
    iIntros (Hnonneg Φ) "Hassoc HΦ".
    replace z with (Z.of_nat (Z.to_nat z)) by lia.
    wp_apply (wp_get_list_idx with "[$]").
    rewrite Z2Nat.id //.
  Qed.

  Lemma spec_get_list_idx E K l vs (k : nat):
    ↑specN ⊆ E →
    linked_slist l vs -∗
    refines_right K (get_list_idx #l #k) ={E}=∗
    refines_right K (opt_to_val (vs !! k)) ∗ linked_slist l vs.
  Proof.
    iIntros (?) "H Hr".
    rewrite /get_list_idx. iInduction vs as [| v' vs] "IH" forall (l k).
    - tp_pures. rewrite /linked_list. tp_load. tp_pures. iModIntro. iFrame.
    - tp_pures. iDestruct "H" as (?) "(Hl&Hassoc)".
      tp_load. tp_pures; first solve_vals_compare_safe. case_bool_decide as Hcase.
      { tp_pures. inversion Hcase. destruct k; try lia; [].
        iModIntro. iFrame "Hr". iExists _; iFrame; eauto. }
      { tp_pure. tp_pure. destruct k.
        { exfalso. apply Hcase. f_equal. }
        replace ((Z.of_nat (S k) - 1))%Z with (Z.of_nat k) by lia; last first.
        iMod ("IH" with "[$Hassoc] [$]") as "(?&?)".
        iEval simpl.
        iFrame. iModIntro. iExists _; iFrame.
      }
  Qed.

  Lemma spec_get_list_idx_Z E K l vs (z : Z):
    (0 ≤ z)%Z →
    ↑specN ⊆ E →
    linked_slist l vs -∗
    refines_right K (get_list_idx #l #z) ={E}=∗
    refines_right K (opt_to_val (vs !! (Z.to_nat z))) ∗ linked_slist l vs.
  Proof.
    iIntros (??) "H Hr".
    replace z with (Z.of_nat (Z.to_nat z)) by lia.
    iApply (spec_get_list_idx with "[$]"); auto.
    rewrite ?Z2Nat.id //.
  Qed.


End list.
