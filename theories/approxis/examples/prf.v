From clutch Require Import lib.flip.
From clutch.approxis Require Import approxis map list.
From clutch.approxis Require Export bounded_oracle.
Set Default Proof Using "Type*".

Section definition.

  Variable Key Input Output : nat.

  Let keygen PRF_scheme : expr := Fst PRF_scheme.
  Let prf PRF_scheme : expr := Fst (Snd PRF_scheme).
  Let rand_output PRF_scheme : expr := Snd (Snd PRF_scheme).

  (* An idealised random function family. *)
  Definition random_function : val :=
    λ: "_key",
      (* Create a reference to a functional map *)
      let: "mapref" := init_map #() in
      λ: "x",
        match: get "mapref" "x" with
        | SOME "y" => "y"
        | NONE =>
            let: "y" := (rand #Output) in
            set "mapref" "x" "y";;
            "y"
        end.

  Let q_calls := q_calls Input.

  Definition PRF : val :=
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
            let: "x" := rand #Input in
            let: "y" := "prf_key_b" "x" in
            "res" <- list_cons ("x", "y") (!"res") ;;
            "loop" ("i" - #1)
      in
      ("loop" "Q") ;;
      ! "res"
  .

  Section spec_ideal.

    Context `{!approxisGS Σ}.

    (* To hash a value v, we check whether it is in the map (i.e. it has been previously hashed).
     If it has we return the saved hash value, otherwise we draw a hash value and save it in the map *)
    Definition compute_rf_specialized hm : val :=
      λ: "x",
        match: get hm "x" with
        | SOME "y" => "y"
        | NONE =>
            let: "y" := (rand #Output) in
            set hm "x" "y";;
            "y"
        end.
    Definition compute_rf : val :=
      λ: "mapref" "x",
        match: get "mapref" "x" with
        | SOME "y" => "y"
        | NONE =>
            let: "y" := (rand #Output) in
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

End definition.
