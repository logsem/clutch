From clutch.approxis Require Import approxis map list security_aux option.
From clutch.approxis Require Export bounded_oracle.
Set Default Proof Using "Type*".


(* rand_output is currently unused ; it would be useful if a PRF module had
   abstract types. *)
Class PRF :=
  { card_key : nat
  ; card_input : nat
  ; card_output : nat
  ; keygen : val
  ; prf : val
  ; rand_output : val
  }.

Section random_function.
  Context `{PRF}.

  (* An idealised random function family. *)
  Definition random_function : val :=
    λ: "_key",
      (* Create a reference to a functional map *)
      let: "mapref" := init_map #() in
      λ: "x",
        match: get "mapref" "x" with
        | SOME "y" => "y"
        | NONE =>
            let: "y" := (rand #card_output) in
            set "mapref" "x" "y";;
            "y"
        end.

  Definition lrel_key {Σ} : lrel Σ := lrel_int_bounded 0 card_key.
  Definition lrel_input {Σ} : lrel Σ := lrel_int_bounded 0 card_input.
  Definition lrel_output {Σ} : lrel Σ := lrel_int_bounded 0 card_output.
  Definition lrel_keygen `{!approxisRGS Σ} : lrel Σ := (lrel_unit → lrel_key).
  Definition lrel_prf `{!approxisRGS Σ} : lrel Σ := lrel_key → lrel_input → lrel_output.

  Definition lrel_PRF_Adv `{!approxisRGS Σ} := ((lrel_input → (lrel_option lrel_output)) → lrel_bool)%lrel.

End random_function.


Module LR_prf.
  Import Ltac2.
  Export LR_bounded.

  Ltac2 Set pattern_of_lr2 as previous :=
    fun lr (xs : constr list) =>
      lazy_match! lr with
      | lrel_input => bounded (get_head_name xs)
      | lrel_output => bounded (get_head_name xs)
      (* | lrel_message => bounded (get_head_name xs) *)
      | lrel_key => bounded (get_head_name xs)
      | _ => previous lr xs
      end.

  Ltac2 Set rel_vals as previous :=
       fun lr =>
         lazy_match! lr with
         | (lrel_car lrel_output _ _) =>
             ltac1:(iExists _ ; iPureIntro ; intuition lia)
         | _ => previous lr
         end.

End LR_prf.
Export LR_prf.

Section random_function.
  Context `{PRF}.

  Fact random_function_sem_typed `{!approxisRGS Σ} A :
    ⊢ REL random_function
        << random_function : A → lrel_input → lrel_output.
  Proof with (rel_pures_l ; rel_pures_r).
    rel_arrow_val ; iIntros (??) "_".
    rewrite /random_function...
    rel_bind_r (init_map #()). iApply refines_init_map_r => /=... iIntros (map_r) "map_r".
    rel_bind_l (init_map #()). iApply refines_init_map_l. iIntros (map_l) "map_l" => /=...
    iApply (refines_na_alloc
              ( ∃ (M : gmap nat val),
                  map_list map_l M
                  ∗ map_slist map_r M
                  ∗ ⌜ ∀ y, y ∈ @map_img nat val (gmap nat val) _ (gset val) _ _ _ M
                           → ∃ k : nat, y = #k ∧ k <= card_output ⌝
                  ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S card_input)%nat ⌝
              )%I
              (nroot.@"RED")) ; iFrame.
    iSplitL ; iFrame.
    1: { iPureIntro; split ; [|set_solver].
         intros y hy. exfalso. clear -hy.
         rewrite map_img_empty in hy.
         opose proof (proj1 (elem_of_empty y) hy). done.
    }
    iIntros "#Hinv".
    rel_arrow_val. lrintro "x"...
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "(> (%M & map_l & map_r & %range_int & %dom_range) & Hclose)".
    rel_bind_l (get _ _). rel_bind_r (get _ _).
    opose proof (IZN x _) as [x' ->] => //. rename x' into x.
    rel_apply_l (refines_get_l with "[-map_l] [$map_l]"). iIntros (?) "map_l #->"...
    rel_apply_r (refines_get_r with "[-map_r] [$map_r]"). iIntros (?) "map_r #->"...

    destruct (M !! x) as [y |] eqn:x_fresh ...
    + iApply (refines_na_close with "[-]") ;
        iFrame ; repeat iSplitL.
      { iFrame. iNext. iFrame. iPureIntro. split. 2: set_solver. done. }
      opose proof (elem_of_map_img_2 M x y x_fresh) as hy.
      destruct (range_int y hy) as [y' [??]]. subst.
      rel_vals.
    + rel_apply (refines_couple_UU card_output id); first auto.
      iIntros (y) "!> %"...
      rel_apply_r (refines_set_r with "[-map_r] [$map_r]"). iIntros "map_r"...
      rel_apply_l (refines_set_l with "[-map_l] [$map_l]"). iIntros "map_l"...
      iApply (refines_na_close with "[-]") ;
        iFrame ; repeat iSplitL. 1: iExists _ ; iFrame.
      1: { iPureIntro.
           repeat split ; last first.
           - rewrite -Forall_forall.
             rewrite dom_insert.
             rewrite elements_union_singleton.
             + apply Forall_cons_2. 1: lia. rewrite Forall_forall. done.
             + apply not_elem_of_dom_2. done.
           - intros y' hy'. rewrite (map_img_insert M x (#y)) in hy'.
             rewrite elem_of_union in hy'. destruct hy'.
             + exists y. set_solver.
             + apply range_int.
               opose proof (delete_subseteq M x).
               eapply map_img_delete_subseteq. done.
      }
      rel_vals. Unshelve. all: apply _.
  Qed.
End random_function.

(** PRF security definitions using the variant of q_calls with explicit bounds
    checks in the code. **)
Module bound_checks.

  Context `{PRF}.

  (* Variable Key Input Output : nat.

     Let keygen PRF_scheme : expr := Fst PRF_scheme.
     Let prf PRF_scheme : expr := Fst (Snd PRF_scheme).
     Let rand_output PRF_scheme : expr := Snd (Snd PRF_scheme). *)

  Let q_calls := q_calls card_input.

  Definition PRF_real_rand : val :=
    λ:"b" "adv" "PRF_scheme" "Q",
      let: "key" := keygen "PRF_scheme" #() in
      let: "prf_key_b" :=
        if: "b" then
          prf "PRF_scheme" "key"
        else
          random_function "key" in
      let: "oracle" := q_calls "Q" "prf_key_b" in
      let: "b'" := "adv" "oracle" in
      "b'".

  Definition wPRF : val :=
    λ:"b" "PRF_scheme" "Q",
      let: "key" := keygen "PRF_scheme" #() in
      let: "prf_key_b" :=
        if: "b" then
          prf "PRF_scheme" "key"
        else
          random_function "key" in
      let: "res" := ref list_nil in
      letrec: "loop" "i" :=
          if: "i" = #0 then #() else
            let: "x" := rand #card_input in
            let: "y" := "prf_key_b" "x" in
            "res" <- list_cons ("x", "y") (!"res") ;;
            "loop" ("i" - #1)
      in
      ("loop" "Q") ;;
      ! "res".

  (* Rosulek, Def. 6.1 (PRF security) *)
  (* NB: Rosulek samples the key from {0,1}^λ, we sample it from [0,card_key]. *)
  Definition PRF_real : val :=
    λ:"PRF_scheme" "Q",
      let: "k" := keygen "PRF_scheme" #() in
      let: "lookup" := prf "PRF_scheme" "k" in
      let: "oracle" := q_calls "Q" "lookup" in
      "oracle".

  Definition PRF_rand : val :=
    λ:"PRF_scheme" "Q",
      let: "lookup" := random_function #() in
      let: "oracle" := q_calls "Q" "lookup" in
      "oracle".

  Section spec_ideal.

    Context `{!approxisGS Σ}.

    (* To hash a value v, we check whether it is in the map (i.e. it has been previously hashed).
     If it has we return the saved hash value, otherwise we draw a hash value and save it in the map *)
    Definition compute_rf_specialized hm : val :=
      λ: "x",
        match: get hm "x" with
        | SOME "y" => "y"
        | NONE =>
            let: "y" := (rand #card_output) in
            set hm "x" "y";;
            "y"
        end.
    Definition compute_rf : val :=
      λ: "mapref" "x",
        match: get "mapref" "x" with
        | SOME "y" => "y"
        | NONE =>
            let: "y" := (rand #card_output) in
            set "mapref" "x" "y";;
            "y"
        end.

    Definition is_random_function f m : iProp Σ :=
      ∃ (mapref : loc), ⌜ f = compute_rf_specialized #mapref ⌝ ∗ map_list mapref ((λ b, LitV (LitInt b)) <$> m).

    Definition is_srandom_function f m : iProp Σ :=
      ∃ (mapref : loc), ⌜ f = compute_rf_specialized #mapref ⌝ ∗ map_slist mapref ((λ b, LitV (LitInt b)) <$> m).

    #[global] Instance timeless_is_random_function f m :
      Timeless (is_random_function f m).
    Proof. apply _. Qed.

    #[global] Instance timeless_is_srandom_function f m :
      Timeless (is_srandom_function f m).
    Proof. apply _. Qed.

    Lemma wp_random_function E :
      {{{ True }}}
        random_function #() @ E
        {{{ f, RET f; is_random_function f ∅ }}}.
    Proof.
      rewrite /random_function.
      iIntros (Φ) "_ HΦ".
      wp_pures.
      wp_apply (wp_init_map with "[//]").
      iIntros (?) "Hm". wp_pures.
      iApply "HΦ". iExists _. rewrite fmap_empty. iFrame. eauto.
    Qed.

    Lemma spec_random_function E K:
      ⤇ fill K (random_function #()) -∗
      spec_update E (∃ (f:val), ⤇ fill K f ∗ is_srandom_function f ∅).
    Proof.
      rewrite /random_function.
      iIntros "Hspec".
      tp_pures.
      tp_bind (init_map _).
      iMod (spec_init_map with "[$]") as "(%&?&?)".
      simpl. tp_pures.
      iApply spec_update_ret.
      by iFrame.
    Qed.

    Lemma wp_random_function_prev E f m (n : nat) (b : Z) :
      m !! n = Some b →
      {{{ is_random_function f m }}}
        f #n @ E
        {{{ RET #b; is_random_function f m }}}.
    Proof.
      iIntros (Hlookup Φ) "Hhash HΦ".
      iDestruct "Hhash" as (hm ->) "H".
      rewrite /compute_rf_specialized.
      wp_pures.
      wp_apply (wp_get with "[$]").
      iIntros (vret) "(Hhash&->)".
      rewrite lookup_fmap Hlookup /=. wp_pures. iModIntro. iApply "HΦ".
      iExists _. eauto.
    Qed.

    
    Lemma spec_random_function_prev E f m (n : nat) (b : Z) K:
      m !! n = Some b →
      is_srandom_function f m -∗
      ⤇ fill K (f #n) -∗
      spec_update E (⤇ fill K #b ∗ is_srandom_function f m).
    Proof.
      iIntros (Hlookup) "Hhash Hspec".
      iDestruct "Hhash" as (hm ->) "H".
      rewrite /compute_rf_specialized.
      tp_pures.
      tp_bind (get _ _).
      iMod (spec_get with "[$][$]") as "(?&?)".
      simpl. 
      rewrite lookup_fmap Hlookup /=. tp_pures. iModIntro.
      iFrame. auto.
    Qed.
    
  End spec_ideal.

End bound_checks.

(** PRF security definitions using the variant of q_calls using semantic typing
    instead of bounds checks. **)
Module sem.

  Context `{PRF}.

  Let q_calls := q_calls_poly.

  Definition PRF_real : val :=
    λ:"Q",
      let: "k" := keygen #() in
      let: "lookup" := prf "k" in
      let: "oracle" := q_calls_poly #() #() "Q" "lookup" in
      "oracle".

  Definition PRF_rand : val :=
    λ:"PRF_scheme" "Q",
      let: "lookup" := random_function #() in
      let: "oracle" := q_calls_poly #() #() "Q" "lookup" in
      "oracle".

  Section spec_ideal.

    Context `{!approxisGS Σ}.

    (* To hash a value v, we check whether it is in the map (i.e. it has been previously hashed).
     If it has we return the saved hash value, otherwise we draw a hash value and save it in the map *)
    Definition compute_rf_specialized hm : val :=
      λ: "x",
        match: get hm "x" with
        | SOME "y" => "y"
        | NONE =>
            let: "y" := (rand #card_output) in
            set hm "x" "y";;
            "y"
        end.
    Definition compute_rf : val :=
      λ: "mapref" "x",
        match: get "mapref" "x" with
        | SOME "y" => "y"
        | NONE =>
            let: "y" := (rand #card_output) in
            set "mapref" "x" "y";;
            "y"
        end.

    Definition is_random_function f m : iProp Σ :=
      ∃ (mapref : loc), ⌜ f = compute_rf_specialized #mapref ⌝ ∗ map_list mapref ((λ b, LitV (LitInt b)) <$> m).

    Definition is_srandom_function f m : iProp Σ :=
      ∃ (mapref : loc), ⌜ f = compute_rf_specialized #mapref ⌝ ∗ map_slist mapref ((λ b, LitV (LitInt b)) <$> m).

    #[global] Instance timeless_is_random_function f m :
      Timeless (is_random_function f m).
    Proof. apply _. Qed.

    #[global] Instance timeless_is_srandom_function f m :
      Timeless (is_srandom_function f m).
    Proof. apply _. Qed.

    Lemma wp_random_function E :
      {{{ True }}}
        random_function #() @ E
        {{{ f, RET f; is_random_function f ∅ }}}.
    Proof.
      rewrite /random_function.
      iIntros (Φ) "_ HΦ".
      wp_pures.
      wp_apply (wp_init_map with "[//]").
      iIntros (?) "Hm". wp_pures.
      iApply "HΦ". iExists _. rewrite fmap_empty. iFrame. eauto.
    Qed.

    Lemma spec_random_function E K:
      ⤇ fill K (random_function #()) -∗
      spec_update E (∃ (f:val), ⤇ fill K f ∗ is_srandom_function f ∅).
    Proof.
      rewrite /random_function.
      iIntros "Hspec".
      tp_pures.
      tp_bind (init_map _).
      iMod (spec_init_map with "[$]") as "(%&?&?)".
      simpl. tp_pures.
      iApply spec_update_ret.
      by iFrame.
    Qed.

    Lemma wp_random_function_prev E f m (n : nat) (b : Z) :
      m !! n = Some b →
      {{{ is_random_function f m }}}
        f #n @ E
        {{{ RET #b; is_random_function f m }}}.
    Proof.
      iIntros (Hlookup Φ) "Hhash HΦ".
      iDestruct "Hhash" as (hm ->) "H".
      rewrite /compute_rf_specialized.
      wp_pures.
      wp_apply (wp_get with "[$]").
      iIntros (vret) "(Hhash&->)".
      rewrite lookup_fmap Hlookup /=. wp_pures. iModIntro. iApply "HΦ".
      iExists _. eauto.
    Qed.


    Lemma spec_random_function_prev E f m (n : nat) (b : Z) K:
      m !! n = Some b →
      is_srandom_function f m -∗
      ⤇ fill K (f #n) -∗
      spec_update E (⤇ fill K #b ∗ is_srandom_function f m).
    Proof.
      iIntros (Hlookup) "Hhash Hspec".
      iDestruct "Hhash" as (hm ->) "H".
      rewrite /compute_rf_specialized.
      tp_pures.
      tp_bind (get _ _).
      iMod (spec_get with "[$][$]") as "(?&?)".
      simpl.
      rewrite lookup_fmap Hlookup /=. tp_pures. iModIntro.
      iFrame. auto.
    Qed.

  End spec_ideal.

End sem.
