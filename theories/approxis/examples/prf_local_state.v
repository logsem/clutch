From clutch.prob_lang Require Import typing.tychk.
From clutch.approxis Require Import approxis map list security_aux option.
From clutch.approxis Require Export bounded_oracle.
Set Default Proof Using "Type*".

(* Right-associative tuples. Alas, this breaks Coq's built-in tuple notation. *)
(* Notation "( e1 ; e2 )" := (Pair e1 e2) : expr_scope.
   Notation "( e1 ; e2 ; .. ; en' ; en )" := (Pair e1 (Pair e2 .. (Pair en' en) ..)) : expr_scope.
   Notation "( e1 ; e2 )" := (PairV e1 e2) : val_scope.
   Notation "( e1 ; e2 ; .. ; en' ; en )" := (PairV e1 (PairV e2 .. (PairV en' en) ..)) : val_scope. *)

Class PRF_localstate_params :=
  { card_key : nat
  ; card_input : nat
  ; card_output : nat
  ; prf_localstate_params : val := (#card_key, #card_input, #card_output) }.

Definition TKey := TNat.
Definition TInput := TNat.
Definition TOutput := TNat.
Definition T_PRF_params := (TKey * TInput * TOutput)%ty.

Definition get_param_card_key : val := λ:"prf_params", Fst (Fst "prf_params").
Definition get_param_card_input : val := λ:"prf_params", Snd (Fst "prf_params").
Definition get_param_card_output : val := λ:"prf_params", Snd "prf_params".

(* rand_output is currently unused ; it would be useful if a PRF module had
   abstract types. *)
Class PRF_localstate `{PRF_localstate_params} :=
  { keygen : val
  ; prf : val
  ; rand_output : val
  ; prf_scheme : val := (prf_localstate_params, keygen, prf, rand_output)%V
  }.

Definition TKeygen : type := TUnit → TKey.
Definition TPRF : type := TKey → TInput → TOutput.
Definition T_rand_output : type := TUnit → TNat.
Definition T_PRF_scheme := (T_PRF_params * TKeygen * TPRF * T_rand_output)%ty.

Definition T_PRF_Adv := ((TInput → (TOption TOutput)) → TBool)%ty.

Definition get_params : val := λ:"prf_scheme", Fst (Fst (Fst "prf_scheme")).
Definition get_card_key : val := λ:"prf_scheme", Fst (Fst (Fst (Fst (Fst "prf_scheme")))).
Definition get_card_input : val := λ:"prf_scheme", Snd (Fst (Fst (Fst (Fst "prf_scheme")))).
Definition get_card_output : val := λ:"prf_scheme", Snd (Fst (Fst (Fst "prf_scheme"))).
Definition get_keygen : val := λ:"prf_scheme", Snd (Fst (Fst "prf_scheme")).
Definition get_prf : val := λ:"prf_scheme", Snd (Fst ("prf_scheme")).
Definition get_rand_output : val := λ:"prf_scheme", Snd "prf_scheme".


(* An idealised random function family. *)
Definition random_function : val :=
  λ: "mapref" "card_output",
    λ: "x",
      match: get "mapref" "x" with
      | SOME "y" => "y"
      | NONE =>
          let: "y" := (rand "card_output") in
          set "mapref" "x" "y";;
          "y"
      end.
      

(** PRF security definitions using the variant of q_calls with explicit bounds
    checks in the code. **)
Module bounds_check.
  Section bounds_check.

    (* Context `{PRF_scheme : PRF}. *)

    (* Variable Key Input Output : nat.

     Let keygen PRF_scheme : expr := Fst PRF_scheme.
     Let prf PRF_scheme : expr := Fst (Snd PRF_scheme).
     Let rand_output PRF_scheme : expr := Snd (Snd PRF_scheme). *)

    (* Let q_calls := q_calls (card_input PRF_scheme). *)

    Definition PRF_real_rand : val :=
      λ:"b" "adv" "PRF_scheme" "Q",
        let: "key" := get_keygen "PRF_scheme" #() in
        let: "prf_key_b" :=
          if: "b" then
            get_prf "PRF_scheme" "key"
          else
            let: "mapref" := init_map #() in
              random_function "mapref" (get_card_output "PRF_scheme") in
        let: "oracle" := q_calls (get_card_input "PRF_scheme") "Q" "prf_key_b" in
        let: "b'" := "adv" "oracle" in
        "b'".

    Definition wPRF : val :=
      λ:"b" "PRF_scheme" "Q",
        let: "key" := get_keygen "PRF_scheme" #() in
        let: "prf_key_b" :=
          if: "b" then
            get_prf "PRF_scheme" "key"
          else
            let: "mapref" := init_map #() in
              random_function "mapref" (get_card_output "PRF_scheme") in
        let: "res" := ref list_nil in
        letrec: "loop" "i" :=
        if: "i" = #0 then #() else
          let: "x" := rand (get_card_input "PRF_scheme") in
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
        let: "k" := get_keygen "PRF_scheme" #() in
        let: "lookup" := get_prf "PRF_scheme" "k" in
        let: "oracle" := q_calls (get_card_input "PRF_scheme") "Q" "lookup" in
        "oracle".

    Definition PRF_rand : val :=
      λ:"PRF_scheme" "Q",
        let: "lookup" := 
          let: "mapref" := init_map #() in
            random_function "mapref" (get_card_output "PRF_scheme") in
        let: "oracle" := q_calls (get_card_input "PRF_scheme") "Q" "lookup" in
        "oracle".

  End bounds_check.
End bounds_check.

Module sem.
  (** PRF security definitions using the variant of q_calls using semantic typing
    instead of bounds checks. **)
  Section sem.

    Definition PRF_real : val :=
      λ:"PRF" "Q",
        let: "k" := get_keygen "PRF" #() in
        let: "lookup" := get_prf "PRF" "k" in
        let: "oracle" := q_calls_poly #() #() "Q" "lookup" in
        "oracle".

    Definition PRF_rand : val :=
      λ:"PRF" "Q",
        let: "lookup" := 
          let: "mapref" := init_map #() in
            random_function "mapref" (get_card_output "PRF") in
        let: "oracle" := q_calls_poly #() #() "Q" "lookup" in
        "oracle".

  End sem.
End sem.


Section prf_lrel.
  Context `{PRF_localstate_params : PRF_localstate}.

  Definition lrel_key {Σ} : lrel Σ := lrel_int_bounded 0 card_key.
  Definition lrel_input {Σ} : lrel Σ := lrel_int_bounded 0 card_input.
  Definition lrel_output {Σ} : lrel Σ := lrel_int_bounded 0 card_output.
  Definition lrel_keygen `{!approxisRGS Σ} : lrel Σ := (lrel_unit → lrel_key).
  Definition lrel_prf `{!approxisRGS Σ} : lrel Σ := lrel_key → lrel_input → lrel_output.

  Definition lrel_PRF_Adv `{!approxisRGS Σ} := ((lrel_input → (lrel_option lrel_output)) → lrel_bool)%lrel.

End prf_lrel.

Module LR_prf.
  Import Ltac2 (* Printf *).
  Export LR_bounded.

  Ltac2 prf_intro (typ : constr) xs k :=
    (* printf "entering prf_intro, typ: %t" typ ; *)
    lazy_match! typ with
      | lrel_input =>
          (* printf "found `lrel_input`, unfolding" ; *)
          let typ := eval unfold lrel_input in $typ in
            k typ xs
      | lrel_output =>
          (* printf "found `lrel_output`, unfolding" ; *)
          let typ := eval unfold lrel_output in $typ in
            k typ xs
      | lrel_key =>
          (* printf "found `lrel_key`, unfolding" ; *)
          let typ := eval unfold lrel_key in $typ in
            k typ xs
    | _ => None
    end.
  Ltac2 Set Basic.lrintro_tacs as prev := fun () => FMap.add "prf" prf_intro (prev ()).

  Ltac2 prf_val typ k :=
    (* printf "entering prf_val, typ: %t" typ ; *)
    lazy_match! typ with
    | (lrel_car lrel_input ?v1 ?v2) =>
        (* printf "found `lrel_input %t %t`, unfolding" v1 v2 ; *)
        (* ltac1:(iExists _ ; iPureIntro ; (intuition lia || eauto)) ; Progressed *)
        let typ := eval unfold lrel_input in $typ in
          k typ
    | (lrel_car lrel_output ?v1 ?v2) =>
        (* printf "found `lrel_output %t %t`, unfolding" v1 v2 ; *)
        (* ltac1:(iExists _ ; iPureIntro ; (intuition lia || eauto)) ; Progressed *)
        let typ := eval unfold lrel_output in $typ in
          k typ
    | _ => Stuck
    end.
  Ltac2 Set Basic.rel_val_tacs as prev := fun () => FMap.add "prf" prf_val (prev ()).

  (* Ltac2 Set rel_vals as previous :=
          fun lr =>
            lazy_match! lr with
            | (lrel_car lrel_output _ _) =>
                ltac1:(iExists _ ; iPureIntro ; intuition lia)
            | (lrel_car lrel_input _ _) =>
                ltac1:(iExists _ ; iPureIntro ; intuition lia)
            | _ => previous lr
            end. *)

End LR_prf.
Export LR_prf.

Section typing.

  Lemma random_function_sem_typed_inv `{!approxisRGS Σ} {prf_params : PRF_localstate_params}
    lm lm' (𝒩 : namespace) (P : iProp Σ):
    (∃ Q,
      P ⊣⊢
        (Q
      ∗ (∃ (M : gmap nat val),
        map_list  lm  M
      ∗ map_slist lm' M
      ∗ ⌜ ∀ y, y ∈ @map_img nat val (gmap nat val) _ (gset val) _ _ _ M
        → ∃ k : nat, y = #k ∧ k <= card_output ⌝
      ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S card_input)%nat ⌝))
    ) ->
    na_invP 𝒩 P
     ⊢ refines top (random_function #lm #card_output)
      (random_function #lm' #card_output) (lrel_input → lrel_output).
  Proof with (rel_pures_l ; rel_pures_r).
    intros [Q HP]. apply bi.equiv_entails in HP. destruct HP as [HP1 HP2].
    iIntros "#Hinv".
    rewrite /random_function...
    rel_arrow_val. lrintro "x"...
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "[HP Hclose]".
    iPoseProof (HP1 with "HP") as "(HQ & >(%M & map_l & map_r & %range_int & %dom_range))".
    rel_bind_l (get _ _). rel_bind_r (get _ _).
    opose proof (IZN x _) as [x' ->] => //. rename x' into x.
    rel_apply_l (refines_get_l with "[-map_l] [$map_l]"). iIntros (?) "map_l #->"...
    rel_apply_r (refines_get_r with "[-map_r] [$map_r]"). iIntros (?) "map_r #->"...
    destruct (M !! x) as [y |] eqn:x_fresh ...
    + iApply (refines_na_close with "[-]") ;
        iFrame ; repeat iSplitL.
      { iApply HP2. iFrame. iNext. iFrame. iPureIntro. split. 2: set_solver. done. }
      opose proof (elem_of_map_img_2 M x y x_fresh) as hy.
      destruct (range_int y hy) as [y' [??]]. subst.
      rel_vals.
    + rel_apply (refines_couple_UU card_output id) => //.
      iIntros (y) "!> %"...
      rel_apply_r (refines_set_r with "[-map_r] [$map_r]"). iIntros "map_r"...
      rel_apply_l (refines_set_l with "[-map_l] [$map_l]"). iIntros "map_l"...
      iApply (refines_na_close with "[-]") ;
        iFrame ; repeat iSplitL. 2: rel_vals; iExists _ ; iFrame.
      iApply HP2; iFrame.
      iPureIntro.
      repeat split ; last first.
      - rewrite -Forall_forall.
        rewrite dom_insert.
        rewrite elements_union_singleton.
        * apply Forall_cons_2. 1: lia. rewrite Forall_forall. done.
        * apply not_elem_of_dom_2. done.
      - intros y' hy'. rewrite (map_img_insert M x (#y)) in hy'.
        rewrite elem_of_union in hy'. destruct hy'.
        * exists y. set_solver.
        * apply range_int.
          opose proof (delete_subseteq M x).
          eapply map_img_delete_subseteq. done.
      Unshelve. all: apply _.
  Qed.

  Lemma random_function_sem_typed `{!approxisRGS Σ} {prf_params : PRF_localstate_params}
    (lm lm' : loc) (M : gmap nat val) :
        map_list  lm  M
      ∗ map_slist lm' M
      ∗ ⌜ ∀ y, y ∈ @map_img nat val (gmap nat val) _ (gset val) _ _ _ M
        → ∃ k : nat, y = #k ∧ k <= card_output ⌝
      ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S card_input)%nat ⌝
     ⊢ refines top (random_function #lm #card_output)
      (random_function #lm' #card_output) (lrel_input → lrel_output).
  Proof with (rel_pures_l ; rel_pures_r).
    iIntros "[Hmap [Hmap' [%Himg %Hdom]]]".
    set (P := (∃ (M : gmap nat val),
        map_list  lm  M
      ∗ map_slist lm' M
      ∗ ⌜ ∀ y, y ∈ @map_img nat val (gmap nat val) _ (gset val) _ _ _ M
        → ∃ k : nat, y = #k ∧ k <= card_output ⌝
      ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S card_input)%nat ⌝)%I).
    rel_apply (refines_na_alloc P (nroot.@"random_function_sem_typed")).
    iFrame. iSplitL.
    {
      iPureIntro. split; assumption.
    }
    iIntros "Hinv".
    rel_apply random_function_sem_typed_inv; last iAssumption.
    exists True%I. rewrite /P.
    apply bi.equiv_entails; split;
    [iIntros "HP"; iSplitR; first done | iIntros "[_ HP]"];
    iAssumption.
  Qed.

  Fact PRF_rand_sem_typed `{!approxisRGS Σ} {_ : PRF_localstate_params} {kg f ro kg' f' ro' : val} :
    ⊢ REL sem.PRF_rand (prf_localstate_params, kg, f, ro)%V << sem.PRF_rand (prf_localstate_params, kg', f', ro')%V
      : (interp TInt []) → lrel_input → lrel_option lrel_output.
  Proof with (rel_pures_l ; rel_pures_r).
    rewrite /sem.PRF_rand...
    rel_arrow_val. lrintro "Q"...
    rewrite /get_card_output.
    subst...
    rel_apply refines_app.
    2: {
      rel_apply refines_init_map_l; iIntros (lm) "Hmap";
      rel_apply refines_init_map_r; iIntros (lm') "Hmap'"...
      simpl.
      iApply random_function_sem_typed; iFrame.
      iPureIntro; split ; [|set_solver].
      intros y hy. exfalso. clear -hy.
      rewrite map_img_empty in hy.
      opose proof (proj1 (elem_of_empty y) hy). done.
    }
    rel_arrow. iIntros (rf rf') "#hrf"...
    rel_apply refines_app => //.
    { rel_arrow. iIntros... done. }
    by iApply q_calls_poly_sem_typed_app.
  Qed.

  Section spec_ideal.

    Context `{!approxisGS Σ}.
    Variable (card_output : nat).

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
        let: "mapref" := init_map #() in random_function "mapref" #card_output @ E
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
      ⤇ fill K (let: "mapref" := init_map #() in random_function "mapref" #card_output) -∗
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

End typing.
