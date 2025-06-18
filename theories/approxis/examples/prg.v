From clutch.prob_lang Require Import typing.tychk.
From clutch.approxis Require Import approxis map list security_aux option.
From clutch.approxis Require Export bounded_oracle.
Set Default Proof Using "Type*".

(* Right-associative tuples. Alas, this breaks Coq's built-in tuple notation. *)
(* Notation "( e1 ; e2 )" := (Pair e1 e2) : expr_scope.
   Notation "( e1 ; e2 ; .. ; en' ; en )" := (Pair e1 (Pair e2 .. (Pair en' en) ..)) : expr_scope.
   Notation "( e1 ; e2 )" := (PairV e1 e2) : val_scope.
   Notation "( e1 ; e2 ; .. ; en' ; en )" := (PairV e1 (PairV e2 .. (PairV en' en) ..)) : val_scope. *)

Class PRG_params :=
  { card_input : nat
  ; card_extension : nat
  ; prg_params : val := (#card_input, #card_extension) }.

Definition TInput := TNat.
Definition TExtension := TNat.
Definition TOutput := (TNat * TNat)%ty.
Definition T_PRG_params := (TInput * TExtension)%ty.

Definition get_param_card_input : val := λ:"prg_params", Fst "prg_params".
Definition get_param_card_extension : val := λ:"prg_params", Snd "prg_params".

Class PRG `{PRG_params} :=
  { prg : val
  (* ; rand_output : val *)
  ; prg_scheme : val := (prg_params, prg)%V
  }.

Definition TPRG : type := () → TOutput.
Definition T_PRG_scheme := (T_PRG_params * TPRG)%ty.

Definition T_PRG_Adv := ((() → (TOption TOutput)) → TBool)%ty.

Definition get_params : val := λ:"prg_scheme", Fst "prg_scheme".
Definition get_card_input : val := λ:"prg_scheme", Fst (Fst "prg_scheme").
Definition get_card_extension : val := λ:"prg_scheme", Snd (Fst "prg_scheme").
Definition get_prg : val := λ:"prg_scheme", Snd "prg_scheme".

(* An idealised random generator. *)
Definition random_generator : val :=
  λ: "card_input" "card_extension",
    λ: "x",
      (rand (#1 ≪ "card_input" - #1),
      rand (#1 ≪ "card_extension" - #1)).

(** PRG security definitions using the variant of q_calls with explicit bounds
    checks in the code. **)
Module bounds_check.
  Section bounds_check.

    (* Context `{PRG_scheme : PRG}. *)

    (* Variable Input Extension : nat.

     Let prg PRG_scheme : expr := Fst (Snd PRF_scheme).
     Let rand_output PRF_scheme : expr := Snd (Snd PRF_scheme). *)

    (* Let q_calls := q_calls (card_input PRG_scheme). *)

    Definition PRG_real_rand : val :=
      λ:"b" "adv" "PRG_scheme" "Q",
        let: "input" := get_card_input "PRG_scheme" in
        let: "prg_key_b" :=
          if: "b" then
            λ: <>, (get_prg "PRG_scheme") (rand "input")
          else
            random_generator (get_card_input "PRG_scheme") (get_card_extension "PRG_scheme") in
        let: "oracle" := q_calls (get_card_input "PRG_scheme") "Q" "prg_key_b" in
        let: "b'" := "adv" "oracle" in
        "b'".
    (* NOW I removed that, I have yet to find out if this will be useful
    Definition wPRF : val :=
      λ:"b" "PRF_scheme" "Q",
        let: "key" := get_keygen "PRF_scheme" #() in
        let: "prf_key_b" :=
          if: "b" then
            get_prf "PRF_scheme" "key"
          else
            random_function (get_card_output "PRF_scheme") in
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
    *)

    (* Rosulek, Def. 6.1 (PRF security) *)
    (* NB: Rosulek samples the key from {0,1}^λ, we sample it from [0,card_key]. *)
    (* NOW
    Definition PRF_real : val :=
      λ:"PRF_scheme" "Q",
        let: "k" := get_keygen "PRF_scheme" #() in
        let: "lookup" := get_prf "PRF_scheme" "k" in
        let: "oracle" := q_calls (get_card_input "PRF_scheme") "Q" "lookup" in
        "oracle".

    Definition PRF_rand : val :=
      λ:"PRF_scheme" "Q",
        let: "lookup" := random_function (get_card_output "PRF_scheme") in
        let: "oracle" := q_calls (get_card_input "PRF_scheme") "Q" "lookup" in
        "oracle".
    *)

  End bounds_check.
End bounds_check.

Module sem.
  (** PRF security definitions using the variant of q_calls using semantic typing
    instead of bounds checks. **)
  Section sem.
    (* NOW
    Definition PRF_real : val :=
      λ:"PRF" "Q",
        let: "k" := get_keygen "PRF" #() in
        let: "lookup" := get_prf "PRF" "k" in
        let: "oracle" := q_calls_poly #() #() "Q" "lookup" in
        "oracle".

    Definition PRF_rand : val :=
      λ:"PRF" "Q",
        let: "lookup" := random_function (get_card_output "PRF") in
        let: "oracle" := q_calls_poly #() #() "Q" "lookup" in
        "oracle".
    *)
  End sem.
End sem.


Section prg_lrel.
  Context `{PRG_params : PRG}.

  Definition lrel_input {Σ} : lrel Σ := lrel_int_bounded 0 card_input.
  Definition lrel_output {Σ} : lrel Σ := lrel_int_bounded 0 (card_input + card_extension).
  Definition lrel_prg `{!approxisRGS Σ} : lrel Σ := lrel_input → lrel_output.

  Definition lrel_PRG_Adv `{!approxisRGS Σ} := ((lrel_input → (lrel_option lrel_output)) → lrel_bool)%lrel.

End prg_lrel.

Module LR_prg.
  Import Ltac2 (* Printf *).
  Export LR_bounded.
  (* NOW
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
  *)
End LR_prg.
Export LR_prg.

Section typing.

  (* NOW
  Fact random_function_sem_typed `{!approxisRGS Σ} {prf_params : PRF_params} :
    ⊢ REL random_function #card_output
        << random_function #card_output : lrel_input → lrel_output.
  Proof with (rel_pures_l ; rel_pures_r).
    (* rel_arrow_val ; (* iIntros (??) "_" *) lrintro "max". *)
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
    + rel_apply (refines_couple_UU card_output id) => //.
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

  Fact PRF_rand_sem_typed `{!approxisRGS Σ} {_ : PRF_params} {kg f ro kg' f' ro' : val} :
    ⊢ REL sem.PRF_rand (prf_params, kg, f, ro)%V << sem.PRF_rand (prf_params, kg', f', ro')%V
      : (interp TInt []) → lrel_input → lrel_option lrel_output.
  Proof with (rel_pures_l ; rel_pures_r).
    rewrite /sem.PRF_rand...
    rel_arrow_val. lrintro "Q"...
    rewrite /get_card_output.
    subst...
    rel_apply refines_app.
    2: iApply random_function_sem_typed.
    rel_arrow. iIntros (rf rf') "#hrf"...
    rel_apply refines_app => //.
    { rel_arrow. iIntros... done. }
    by iApply q_calls_poly_sem_typed_app.
  Qed.
  *)
  Section spec_ideal.
  (* NOW
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
        random_function #card_output @ E
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
      ⤇ fill K (random_function #card_output) -∗
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
*)
  End spec_ideal.

End typing.
