From clutch Require Export clutch.

Set Default Proof Using "Type*".


Section map.

(* Simple map as an associative linked list, based on the examples
   from the transfinite Iris repo *)

  Definition find_list : val :=
    (rec: "find" "h" "k" :=
       match: !"h" with
         NONE => NONE
       | SOME "p" =>
           let: "kv" := Fst "p" in
           let: "next" := Snd "p" in
           if: (Fst "kv") = "k" then SOME (Snd "kv") else "find" "next" "k"
       end).

  Definition cons_list : val :=
    λ: "h" "v", ref (SOME ("v", "h")).

  Definition init_list : val :=
    λ:<>, ref NONE.

  Context `{!clutchRGS Σ}.

  (* Impl *)
  Fixpoint assoc_list (l : loc) (vs : list (nat * val)) : iProp Σ :=
    match vs with
    | nil => l ↦ NONEV
    | (k, v) :: vs => ∃ (l' : loc), l ↦ SOMEV ((#k, v), #l') ∗ assoc_list l' vs
  end.

  (* Spec/ghost *)
  Fixpoint assoc_slist (l : loc) (vs : list (nat * val)) : iProp Σ :=
    match vs with
    | nil => l ↦ₛ NONEV
    | (k, v) :: vs => ∃ (l' : loc), l ↦ₛ SOMEV ((#k, v), #l') ∗ assoc_slist l' vs
  end.

  #[global] Instance timeless_assoc_list l vs :
    Timeless (assoc_list l vs).
  Proof. revert l. induction vs as [| (?&?)] => l /=; apply _. Qed.

  #[global] Instance timeless_assoc_slist l vs :
    Timeless (assoc_slist l vs).
  Proof. revert l. induction vs as [| (?&?)] => l /=; apply _. Qed.

  Lemma wp_init_list E :
    {{{ True }}}
      init_list #() @ E
    {{{ l, RET LitV (LitLoc l); assoc_list l nil }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /init_list. wp_pures. wp_alloc l. iModIntro. iApply "HΦ". eauto.
  Qed.

  Lemma spec_init_list E K :
    ↑specN ⊆ E →
    refines_right K (init_list #()) ={E}=∗ ∃ (l: loc), refines_right K (#l) ∗ assoc_slist l [].
  Proof.
    iIntros (?) "H".
    rewrite /init_list.
    tp_pures.
    tp_alloc as l "Hl".
    iExists _. iFrame. auto.
  Qed.

  Lemma wp_cons_list E l vs (k : nat) (v : val) :
    {{{ assoc_list l vs }}}
      cons_list #l (#k, v)%V @ E
    {{{ l', RET LitV (LitLoc l'); assoc_list l' ((k, v) :: vs) }}}.
  Proof.
    iIntros (Φ) "H HΦ".
    rewrite /cons_list. wp_pures. wp_alloc l' as "H'". iModIntro. iApply "HΦ".
    iExists l. iFrame.
  Qed.

  Lemma spec_cons_list E K l vs (k : nat) v :
    ↑specN ⊆ E →
    assoc_slist l vs -∗
    refines_right K (cons_list #l (#k, v)%V) ={E}=∗
    ∃ (l: loc), refines_right K (#l) ∗ assoc_slist l ((k, v) :: vs).
  Proof.
    iIntros (?) "H Hr".
    rewrite /cons_list.
    tp_pures.
    tp_alloc as l' "Hl".
    iExists _. iFrame. iExists _; iFrame. auto.
  Qed.

  Fixpoint find_list_gallina (vs: list (nat * val)) (k: nat) :=
    match vs with
    | nil => None
    | (k', v') :: vs =>
        if bool_decide (k' = k) then
          Some v'
        else
          find_list_gallina vs k
    end.

  Definition opt_to_val (ov: option val) :=
    match ov with
    | Some v => SOMEV v
    | None => NONEV
    end.

  Lemma wp_find_list E l vs (k: nat) :
    {{{ assoc_list l vs }}}
      find_list #l #k @ E
    {{{ v, RET v;
        assoc_list l vs ∗ ⌜ v = opt_to_val (find_list_gallina vs k) ⌝
    }}}.
  Proof.
    iIntros (Φ) "Hassoc HΦ".
    rewrite /find_list. iInduction vs as [|(k', v') vs] "IH" forall (l).
    - wp_pures. rewrite /assoc_list. wp_load. wp_pures. iModIntro. iApply "HΦ"; auto.
    - wp_pures. iDestruct "Hassoc" as (?) "(Hl&Hassoc)".
      wp_load. wp_pures. case_bool_decide as Hcase.
      { wp_pures.  iApply "HΦ". simpl. rewrite bool_decide_true //; last first.
        { inversion Hcase; auto. lia. }
        iModIntro. iSplit; last done. iExists _; iFrame; eauto. }
      { wp_pure. iApply ("IH" with "[$]"). iNext.
        iIntros (v) "Hfind". iApply "HΦ".
        iEval simpl. rewrite bool_decide_false //; last by congruence.
        iDestruct "Hfind" as "(?&$)". iExists _; iFrame.
      }
  Qed.

  Lemma wp_find_list_Z E l vs (z: Z) :
    {{{ assoc_list l vs }}}
      find_list #l #z @ E
    {{{ v, RET v;
        assoc_list l vs ∗ ⌜ v = if bool_decide (z < 0)%Z then
                                  opt_to_val None
                                else opt_to_val (find_list_gallina vs (Z.to_nat z)) ⌝
    }}}.
  Proof.
    iIntros (Φ) "Hassoc HΦ".
    rewrite /find_list. iInduction vs as [|(k', v') vs] "IH" forall (l).
    - wp_pures. rewrite /assoc_list. wp_load. wp_pures. iModIntro. iApply "HΦ"; auto.
      rewrite /=. iFrame. destruct (bool_decide _) => //=.
    - wp_pures. iDestruct "Hassoc" as (?) "(Hl&Hassoc)".
      wp_load. wp_pures.
      destruct (bool_decide (#k' = #z)) eqn:Hbool.
      { apply bool_decide_eq_true_1 in Hbool.
        wp_pures.  iApply "HΦ". simpl. inversion Hbool.
        rewrite bool_decide_false //; last by lia.
        rewrite bool_decide_true //; last by lia.
        iModIntro. iSplit; last done. iExists _; iFrame; eauto. }
      { wp_pure. iApply ("IH" with "[$]"). iNext.
        iIntros (v) "Hfind". iApply "HΦ".
        apply bool_decide_eq_false_1 in Hbool.
        iEval (simpl).
        case_bool_decide.
        { iDestruct "Hfind" as "(?&$)". iExists _. iFrame. }
        rewrite (bool_decide_false (k' = _)); last first.
        { intros Heq. apply Hbool. rewrite Heq. f_equal. rewrite Z2Nat.id; auto. lia. }
        iDestruct "Hfind" as "(?&$)". iExists _; iFrame.
      }
  Qed.

  Lemma spec_find_list E K l vs (k : nat):
    ↑specN ⊆ E →
    assoc_slist l vs -∗
    refines_right K (find_list #l #k) ={E}=∗
    refines_right K (opt_to_val (find_list_gallina vs k)) ∗ assoc_slist l vs.
  Proof.
    iIntros (?) "H Hr".
    rewrite /find_list. iInduction vs as [|(k', v') vs] "IH" forall (l).
    - tp_pures. rewrite /assoc_list. tp_load. tp_pures. iModIntro. iFrame.
    - tp_pures. iDestruct "H" as (?) "(Hl&Hassoc)".
      tp_load. tp_pures; first solve_vals_compare_safe. case_bool_decide as Hcase.
      { tp_pures. simpl. rewrite bool_decide_true //; last first.
        { inversion Hcase; auto. lia. }
        iModIntro. iFrame "Hr". iExists _; iFrame; eauto. }
      { tp_pure. iMod ("IH" with "[$Hassoc] [$]") as "(?&?)".
        iEval simpl. rewrite bool_decide_false //; last by congruence.
        iFrame. iModIntro. iExists _; iFrame.
      }
  Qed.

  Lemma spec_find_list_Z E K l vs (z : Z):
    ↑specN ⊆ E →
    assoc_slist l vs -∗
    refines_right K (find_list #l #z) ={E}=∗
    refines_right K (if bool_decide (z < 0)%Z then
                       opt_to_val None
                     else opt_to_val (find_list_gallina vs (Z.to_nat z))) ∗ assoc_slist l vs.
  Proof.
    iIntros (?) "H Hr".
    rewrite /find_list. iInduction vs as [|(k', v') vs] "IH" forall (l).
    - tp_pures. rewrite /assoc_list. tp_load. tp_pures. iModIntro. iFrame.
      rewrite /=. iFrame. destruct (bool_decide _) => //=.
    - tp_pures. iDestruct "H" as (?) "(Hl&Hassoc)".
      tp_load. tp_pures; first solve_vals_compare_safe.
      destruct (bool_decide (#k' = #z)) eqn:Hbool.
      { apply bool_decide_eq_true_1 in Hbool.
        tp_pures. simpl. inversion Hbool. subst.
        rewrite bool_decide_false //; last by lia.
        rewrite bool_decide_true //; last by lia.
        iModIntro. iFrame. iExists _; iFrame; eauto. }
      { tp_pure. iMod ("IH" with "[$Hassoc] [$]") as "(?&?)".
        apply bool_decide_eq_false_1 in Hbool.
        iEval (simpl).
        case_bool_decide.
        { iFrame. iExists _. by iFrame. }
        rewrite (bool_decide_false (k' = _)); last first.
        { intros Heq. apply Hbool. rewrite Heq. f_equal. rewrite Z2Nat.id; auto. lia. }
        iFrame. iModIntro. iExists _; iFrame.
      }
  Qed.

  Definition init_map : val :=
    λ: <>, ref (init_list #()).

  Definition get : val :=
    λ: "m" "k", find_list !"m" "k".

  Definition set : val :=
    λ: "m" "k" "v", "m" <- cons_list !"m" ("k", "v").

  Definition map_list lm (m: gmap nat val) : iProp Σ :=
    ∃ (lv : loc) vs, lm ↦ #lv ∗ ⌜ list_to_map vs = m ⌝ ∗ assoc_list lv vs.

  Definition map_slist lm (m: gmap nat val) : iProp Σ :=
    ∃ (lv : loc) vs, lm ↦ₛ #lv ∗ ⌜ list_to_map vs = m ⌝ ∗ assoc_slist lv vs.

  #[global] Instance timeless_map_list l m :
    Timeless (map_list l m).
  Proof. apply _. Qed.

  #[global] Instance timeless_map_slist l m :
    Timeless (map_slist l m).
  Proof. apply _. Qed.

  Lemma wp_init_map E :
    {{{ True }}}
      init_map #() @ E
    {{{ l, RET LitV (LitLoc l); map_list l ∅ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /init_map. wp_pures. wp_apply (wp_init_list with "[//]").
    iIntros (l) "Halloc". wp_alloc lm. iApply "HΦ".
    iModIntro. iExists _, _. iFrame. eauto.
  Qed.

  Lemma spec_init_map E K :
    ↑specN ⊆ E →
    refines_right K (init_map #()) ={E}=∗ ∃ (l: loc), refines_right K (#l) ∗ map_slist l ∅.
  Proof.
    iIntros (?) "H".
    rewrite /init_map.
    tp_pures.
    tp_bind (init_list #()).
    rewrite refines_right_bind.
    iMod (spec_init_list with "[$]") as (l) "(HK&Halloc)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    tp_alloc as lm "Hl".
    iExists _. iFrame. iExists _, _; iFrame; auto.
  Qed.

  Lemma find_list_gallina_map_lookup vs (m : gmap nat val) n :
    list_to_map vs = m →
    find_list_gallina vs n = m !! n.
  Proof.
    revert m.
    induction vs as [| (k, v) vs IH] => m Heq.
    - rewrite /=. simpl in Heq. subst; auto.
    - rewrite list_to_map_cons in Heq. subst.
      destruct (decide (k = n)).
      { subst. rewrite lookup_insert /= bool_decide_true //. }
      rewrite lookup_insert_ne //= bool_decide_false //. eauto.
  Qed.

  Lemma wp_get E lm m (n: nat) :
    {{{ map_list lm m }}}
      get #lm #n @ E
    {{{ res, RET res; map_list lm m ∗ ⌜ res = opt_to_val (m !! n) ⌝ }}}.
  Proof.
    iIntros (Φ) "Hm HΦ".
    rewrite /get. wp_pures.
    iDestruct "Hm" as (ll vs) "(Hll&%Heq&Hassoc)".
    wp_load. wp_apply (wp_find_list with "[$]").
    iIntros (vret) "(Hassoc&Hm)". iApply "HΦ". iSplit.
    { iExists _, _. iFrame. eauto. }
    rewrite (find_list_gallina_map_lookup vs m) //.
  Qed.

  Lemma wp_get_Z E lm m (z: Z) :
    {{{ map_list lm m }}}
      get #lm #z @ E
    {{{ res, RET res; map_list lm m ∗
                        ⌜ res = if (bool_decide (z < 0)%Z) then
                                  opt_to_val None
                                else  opt_to_val (m !! Z.to_nat z)⌝
    }}}.
  Proof.
    iIntros (Φ) "Hm HΦ".
    rewrite /get. wp_pures.
    iDestruct "Hm" as (ll vs) "(Hll&%Heq&Hassoc)".
    wp_load. wp_apply (wp_find_list_Z with "[$]").
    iIntros (vret) "(Hassoc&Hm)". iApply "HΦ". iSplit.
    { iExists _, _. iFrame. eauto. }
    rewrite (find_list_gallina_map_lookup vs m) //.
  Qed.

  Lemma spec_get E K lm m (n : nat) :
    ↑specN ⊆ E →
    map_slist lm m -∗
    refines_right K (get #lm #n) ={E}=∗ refines_right K (opt_to_val (m !! n)) ∗ map_slist lm m.
  Proof.
    iIntros (?) "Hm Hr".
    rewrite /get.
    tp_pures.
    iDestruct "Hm" as (ll vs) "(Hll&%Heq&Hassoc)".
    tp_load.
    iMod (spec_find_list with "[$] [$]") as "(HK&Halloc)"; first done.
    rewrite (find_list_gallina_map_lookup vs m) //. iFrame.
    iExists _ ,_. iFrame. eauto.
  Qed.

  Lemma spec_get_Z E K lm m (z : Z) :
    ↑specN ⊆ E →
    map_slist lm m -∗
    refines_right K (get #lm #z) ={E}=∗
    refines_right K (if bool_decide (z < 0)%Z then
                       opt_to_val None
                     else opt_to_val (m !! Z.to_nat z)) ∗ map_slist lm m.
  Proof.
    iIntros (?) "Hm Hr".
    rewrite /get.
    tp_pures.
    iDestruct "Hm" as (ll vs) "(Hll&%Heq&Hassoc)".
    tp_load.
    iMod (spec_find_list_Z with "[$] [$]") as "(HK&Halloc)"; first done.
    rewrite (find_list_gallina_map_lookup vs m) //. iFrame.
    iExists _ ,_. iFrame. eauto.
  Qed.

  Lemma wp_set E lm m (n: nat) (v: val) :
    {{{ map_list lm m }}}
      set #lm #n v @ E
    {{{ RET #(); map_list lm (<[n := v]>m) }}}.
  Proof.
    iIntros (Φ) "Hm HΦ".
    rewrite /set. wp_pures.
    iDestruct "Hm" as (??) "(?&%Heq&Hassoc)".
    wp_load. wp_pures. wp_apply (wp_cons_list with "[$]").
    iIntros (l') "Hassoc'". wp_store. iModIntro.
    iApply "HΦ". iExists _, _. iFrame. rewrite list_to_map_cons Heq //.
  Qed.

  Lemma spec_set E K lm m (n : nat) (v: val) :
    ↑specN ⊆ E →
    map_slist lm m -∗
    refines_right K (set #lm #n v) ={E}=∗ refines_right K #() ∗ map_slist lm (<[n := v]>m).
  Proof.
    iIntros (?) "Hm Hr".
    rewrite /set.
    tp_pures.
    iDestruct "Hm" as (ll vs) "(Hll&%Heq&Hassoc)".
    tp_load. tp_pures.
    tp_bind (cons_list _ _).
    iEval (rewrite refines_right_bind) in "Hr".
    iMod (spec_cons_list with "[$] [$]") as (?)"(Hr&Halloc)"; first done.
    iEval (rewrite -refines_right_bind /=) in "Hr".
    tp_store.
    iFrame. iExists _, _. iFrame. rewrite list_to_map_cons Heq //.
  Qed.

End map.
