From stdpp Require Import namespaces.
From iris.base_logic Require Import invariants na_invariants.
From self.prob_lang Require Import notation proofmode primitive_laws spec_rules spec_tactics.
From self.logrel Require Import model rel_rules rel_tactics.
From iris.algebra Require Import auth gmap excl frac agree.
From self.prelude Require Import base.

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

  Context `{!prelogrelGS Σ}.

  (* Impl *)
  Fixpoint assoc_list (l: loc) (vs: list (nat * val)) : iProp Σ :=
    match vs with
    | nil => l ↦ NONEV
    | (k, v) :: vs => ∃ (l' : loc), l ↦ SOMEV ((#k, v), #l') ∗ assoc_list l' vs
  end.

  (* Spec/ghost *)
  Fixpoint assoc_slist (l: loc) (vs: list (nat * val)) : iProp Σ :=
    match vs with
    | nil => l ↦ₛ NONEV
    | (k, v) :: vs => ∃ (l' : loc), l ↦ₛ SOMEV ((#k, v), #l') ∗ assoc_slist l' vs
  end.

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
    tp_pures K.
    tp_alloc K as l "Hl".
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
    tp_pures K.
    tp_alloc K as l' "Hl".
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

  Lemma spec_find_list E K l vs (k : nat):
    ↑specN ⊆ E →
    assoc_slist l vs -∗
    refines_right K (find_list #l #k) ={E}=∗
    refines_right K (opt_to_val (find_list_gallina vs k)) ∗ assoc_slist l vs.
  Proof.
    iIntros (?) "H Hr".
    rewrite /find_list. iInduction vs as [|(k', v') vs] "IH" forall (l).
    - tp_pures K. rewrite /assoc_list. tp_load K. tp_pures K. iModIntro. iFrame.
    - tp_pures K. iDestruct "H" as (?) "(Hl&Hassoc)".
      tp_load K. tp_pures K; first solve_vals_compare_safe. case_bool_decide as Hcase.
      { tp_pures K. simpl. rewrite bool_decide_true //; last first.
        { inversion Hcase; auto. lia. }
        iModIntro. iFrame "Hr". iExists _; iFrame; eauto. }
      { tp_pure K _. iMod ("IH" with "[$Hassoc] [$]") as "(?&?)".
        iEval simpl. rewrite bool_decide_false //; last by congruence.
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
    tp_pures K.
    tp_bind K (init_list #()).
    rewrite refines_right_bind.
    iMod (spec_init_list with "[$]") as (l) "(HK&Halloc)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    tp_alloc K as lm "Hl".
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

  Lemma spec_get E K lm m (n : nat) :
    ↑specN ⊆ E →
    map_slist lm m -∗
    refines_right K (get #lm #n) ={E}=∗ refines_right K (opt_to_val (m !! n)) ∗ map_slist lm m.
  Proof.
    iIntros (?) "Hm Hr".
    rewrite /get.
    tp_pures K.
    iDestruct "Hm" as (ll vs) "(Hll&%Heq&Hassoc)".
    tp_load K.
    iMod (spec_find_list with "[$] [$]") as "(HK&Halloc)"; first done.
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
    tp_pures K.
    iDestruct "Hm" as (ll vs) "(Hll&%Heq&Hassoc)".
    tp_load K. tp_pures K.
    tp_bind K (cons_list _ _).
    iEval (rewrite refines_right_bind) in "Hr".
    iMod (spec_cons_list with "[$] [$]") as (?)"(Hr&Halloc)"; first done.
    iEval (rewrite -refines_right_bind /=) in "Hr".
    tp_store K.
    iFrame. iExists _, _. iFrame. rewrite list_to_map_cons Heq //.
  Qed.

End map.


Section simple_bit_hash.

  Context `{!prelogrelGS Σ}.

  (* A simple bit hash map. *)

  (* A hash function's internal state is a map from previously queried keys to their hash value *)
  Definition init_hash_state : val := init_map.

  (* To hash a value v, we check whether it is in the map (i.e. it has been previously hashed).
     If it has we return the saved hash value, otherwise we flip a bit and save it in the map *)
  Definition compute_hash_specialized hm : val :=
    λ: "v",
      match: get hm "v" with
      | SOME "b" => "b"
      | NONE =>
          let: "b" := flip #() in
          set hm "v" "b";;
          "b"
      end.
  Definition compute_hash : val :=
    λ: "hm" "v",
      match: get "hm" "v" with
      | SOME "b" => "b"
      | NONE =>
          let: "b" := flip #() in
          set "hm" "v" "b";;
          "b"
      end.

  (* init_hash returns a hash as a function, basically wrapping the internal state
     in the returned function *)
  Definition init_hash : val :=
    λ: "_",
      let: "hm" := init_hash_state #() in
      compute_hash "hm".

  Definition hashfun f m : iProp Σ :=
    ∃ (hm : loc), ⌜ f = compute_hash_specialized #hm ⌝ ∗ map_list hm ((λ b, LitV (LitBool b)) <$> m).

  Definition shashfun f m : iProp Σ :=
    ∃ (hm : loc), ⌜ f = compute_hash_specialized #hm ⌝ ∗ map_slist hm ((λ b, LitV (LitBool b)) <$> m).
  
  Lemma wp_init_hash E :
    {{{ True }}}
      init_hash #() @ E
    {{{ f, RET f; hashfun f ∅ }}}.
  Proof.
    rewrite /init_hash.
    iIntros (Φ) "_ HΦ".
    wp_pures. rewrite /init_hash_state.
    wp_apply (wp_init_map with "[//]").
    iIntros (?) "Hm". wp_pures.
    rewrite /compute_hash. wp_pures.
    iApply "HΦ". iExists _. rewrite fmap_empty. iFrame. eauto.
  Qed.

  Lemma spec_init_hash E K :
    ↑specN ⊆ E →
    refines_right K (init_hash #()) ={E}=∗ ∃ f, refines_right K (of_val f) ∗ shashfun f ∅.
  Proof.
    rewrite /init_hash.
    iIntros (?) "Hspec".
    rewrite /init_hash_state.
    tp_pures K.
    tp_bind K (init_map _).
    iEval (rewrite refines_right_bind) in "Hspec".
    iMod (spec_init_map with "[$]") as (l) "(Hspec&Hm)"; auto.
    iEval (rewrite -refines_right_bind /=) in "Hspec".
    rewrite /compute_hash.
    tp_pures K.
    iExists _. iFrame. iModIntro. iExists _. iSplit; first done. rewrite fmap_empty. iFrame.
  Qed.
    
  Lemma wp_hashfun_prev E f m (n : nat) (b : bool) :
    m !! n = Some b →
    {{{ hashfun f m }}}
      f #n @ E
    {{{ RET #b; hashfun f m }}}.
  Proof.
    iIntros (Hlookup Φ) "Hhash HΦ".
    iDestruct "Hhash" as (hm ->) "H".
    rewrite /compute_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)". 
    rewrite lookup_fmap Hlookup /=. wp_pures. iModIntro. iApply "HΦ".
    iExists _. eauto.
  Qed.

  Lemma spec_hashfun_prev E K f m (n : nat) (b: bool) :
    m !! n = Some b →
    ↑specN ⊆ E →
    shashfun f m -∗
    refines_right K (f #n) ={E}=∗ refines_right K (of_val #b) ∗ shashfun f m.
  Proof.
    iIntros (Hlookup ?) "Hhash HK".
    iDestruct "Hhash" as (hm ->) "H".
    rewrite /compute_hash_specialized.
    tp_pures K.
    tp_bind K (get _ _).
    iEval (rewrite refines_right_bind) in "HK".
    iMod (spec_get with "[$] [$]") as "(HK&Hm)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    rewrite lookup_fmap Hlookup /=.
    tp_pures K. iFrame. iModIntro. iExists _. eauto.
  Qed.
  
  Lemma wp_hashfun_couple_eq E K (f : val) (m : gmap nat bool) (sf: val) (sm : gmap nat bool) (n : nat) :
    ↑specN ⊆ E →
    m !! n = None →
    sm !! n = None →
    {{{ refines_right K (sf #n) ∗ hashfun f m ∗ shashfun sf sm }}}
      f #n @ E
    {{{ (b: bool), RET #b;
        refines_right K (of_val #b) ∗ hashfun f (<[ n := b ]>m) ∗ shashfun sf (<[n := b]>sm) }}}.
  Proof. 
    iIntros (Hspec Hnonem Hnonesm Φ) "(HK&Hhash&Hshash) HΦ".
    iDestruct "Hhash" as (hm ->) "Hm".
    iDestruct "Hshash" as (hsm ->) "Hsm".
    rewrite /compute_hash_specialized.
    wp_pures.
    tp_pures K.
    
    (* spec get *)
    tp_bind K (get _ _).
    iEval (rewrite refines_right_bind) in "HK".
    iMod (spec_get with "[$] [$]") as "(HK&Hsm)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    rewrite lookup_fmap Hnonesm /=.
    tp_pures K.
    
    (* impl get *)
    wp_apply (wp_get with "[$]").
    iIntros (res) "(Hm&->)".
    rewrite lookup_fmap Hnonem /=.
    wp_pures.
    
    (* couple -- FIXME: breaking abstraction *)
    tp_bind K (flip #()) %E.
    iEval (rewrite refines_right_bind) in "HK".
    wp_apply (wp_couple_flips_lr); first done.
    iDestruct "HK" as "(#Hspec&HK)".
    iFrame "Hspec". iFrame "HK".
    iIntros (b) "HK".
    iAssert (refines_right _ _) with "[$Hspec $HK]" as "HK".
    iEval (rewrite -refines_right_bind /=) in "HK".
    tp_pures K.
    do 2 wp_pures.
    
    tp_bind K (set _ _ _).
    iEval (rewrite refines_right_bind) in "HK".
    iMod (spec_set with "[$] [$]") as "(HK&Hsm)"; first done.
    iEval (rewrite -refines_right_bind /=) in "HK".
    tp_pures K.
    
    wp_apply (wp_set with "[$]").
    iIntros "Hm". wp_pures. iApply "HΦ".
    iFrame. iModIntro.
    iSplitL "Hm".
    { iExists _. iSplit; first auto. rewrite fmap_insert //. }
    { iExists _. iSplit; first auto. rewrite fmap_insert //. }
  Qed.

  
  (* But we cannot sample ahead, so for example one cannot prove that if f is a hashmap
    (f 1; f 2) refines (f 2; f1)  *)

End simple_bit_hash.
