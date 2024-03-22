From stdpp Require Import namespaces.
From clutch.prob_lang Require Export lang notation tactics.
From iris.proofmode Require Export proofmode.
From clutch.ert_logic Require Export
  primitive_laws derived_laws proofmode ert_rules cost_models.
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

  Context `{!ert_clutchGS Σ CostTick}.

  (* Impl *)
  Fixpoint assoc_list (l : loc) (vs : list (nat * val)) : iProp Σ :=
    match vs with
    | nil => l ↦ NONEV
    | (k, v) :: vs => ∃ (l' : loc), l ↦ SOMEV ((#k, v), #l') ∗ assoc_list l' vs
  end.


  #[global] Instance timeless_assoc_list l vs :
    Timeless (assoc_list l vs).
  Proof. revert l. induction vs as [| (?&?)] => l /=; apply _. Qed.

  Lemma wp_init_list E :
    {{{ True }}}
      init_list #() @ E
    {{{ l, RET LitV (LitLoc l); assoc_list l nil }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /init_list. wp_pures. wp_alloc l. iApply "HΦ". eauto.
  Qed.

  Lemma wp_cons_list E l vs (k : nat) (v : val) :
    {{{ assoc_list l vs }}}
      cons_list #l (#k, v)%V @ E
    {{{ l', RET LitV (LitLoc l'); assoc_list l' ((k, v) :: vs) }}}.
  Proof.
    iIntros (Φ) "H HΦ".
    rewrite /cons_list. wp_pures. wp_alloc l' as "H'". iApply "HΦ".
    iExists l. iFrame.
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
    - wp_pures. rewrite /assoc_list. wp_load. iIntros "Hassoc". wp_pures. iModIntro. iApply "HΦ"; auto.
    - wp_pures. iDestruct "Hassoc" as (?) "(Hl&Hassoc)".
      wp_load. iIntros "Hl". wp_pures. case_bool_decide as Hcase.
      { subst. case_bool_decide; last done. wp_pures. iApply "HΦ". simpl. 
        iModIntro. iSplit; last done. iExists _; iFrame; eauto. }
      { case_bool_decide as K ; first (exfalso; inversion K; naive_solver).
        wp_pure. iApply ("IH" with "[$]"). iNext.
        iIntros (v) "Hfind". iApply "HΦ".
        iEval simpl. 
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
    - wp_pures. rewrite /assoc_list. wp_load. iIntros "Hl". wp_pures. iModIntro. iApply "HΦ"; auto.
      rewrite /=. iFrame. destruct (bool_decide _) => //=.
    - wp_pures. iDestruct "Hassoc" as (?) "(Hl&Hassoc)".
      wp_apply (wp_load with "[$Hl]").
      { repeat case_bool_decide; done. } iIntros "Hl".
      wp_pures.
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


  Definition init_map : val :=
    λ: <>, ref (init_list #()).

  Definition get : val :=
    λ: "m" "k", find_list !"m" "k".

  Definition set : val :=
    λ: "m" "k" "v", "m" <- cons_list !"m" ("k", "v").

  Definition map_list lm (m: gmap nat val) : iProp Σ :=
    ∃ (lv : loc) vs, lm ↦ #lv ∗ ⌜ list_to_map vs = m ⌝ ∗ assoc_list lv vs.

  #[global] Instance timeless_map_list l m :
    Timeless (map_list l m).
  Proof. apply _. Qed.

  Lemma wp_init_map E :
    {{{ True }}}
      init_map #() @ E
    {{{ l, RET LitV (LitLoc l); map_list l ∅ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /init_map. wp_pures. wp_apply (wp_init_list with "[//]").
    iIntros (l) "Halloc". wp_alloc lm. iApply "HΦ".
    iExists _, _. iFrame. instantiate (1:=[]). eauto.
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
    wp_load. iIntros "Hl". wp_apply (wp_find_list with "[$]").
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
    wp_load. iIntros "Hl". wp_apply (wp_find_list_Z with "[$]").
    iIntros (vret) "(Hassoc&Hm)". iApply "HΦ". iSplit.
    { iExists _, _. iFrame. eauto. }
    rewrite (find_list_gallina_map_lookup vs m) //.
  Qed.


  Lemma wp_set E lm m (n: nat) (v: val) :
    {{{ map_list lm m }}}
      set #lm #n v @ E
    {{{ RET #(); map_list lm (<[n := v]>m) }}}.
  Proof.
    iIntros (Φ) "Hm HΦ".
    rewrite /set. wp_pures.
    iDestruct "Hm" as (??) "(?&%Heq&Hassoc)".
    wp_load. iIntros "Hl". wp_pures. wp_apply (wp_cons_list with "[$]").
    iIntros (l') "Hassoc'". wp_store. iIntros "Hl".
    iApply "HΦ". iExists _, _. iFrame. erewrite list_to_map_cons.
    erewrite Heq. eauto.
  Qed.

End map.
