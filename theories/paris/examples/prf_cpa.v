(* CPA security of a PRF based symmetric encryption scheme. *)
(* From clutch Require Import paris lib.flip. *)
From clutch Require Import lib.flip.
From clutch.paris Require Import paris map list.
Set Default Proof Using "Type*".

Section proofs.

  Context `{!parisRGS Σ}.

  (* symmetric encryption scheme = { keygen : unit -> key ; enc : key -> message -> cipher } *)

  (* prf : Key -> Input -> Output *)
  (* xor : 2^n -> 2^n -> 2^n *)
  (* The scheme computes the ciphertext as *)
  (* let r = rand_input () in (r, (xor (prf key r) msg)) *)
  (* hence for the sake of the scheme, Output = Message and Cipher = Input * Output. *)

  Variable Key : nat.
  Variable Input : nat.
  Variable Output : nat.
  Let Message := Output.
  Let Cipher := Input * Output.

  (* Let rand_cipher := (λ:<>, rand #Cipher)%E. *)
  Let keygen scheme : expr := Fst scheme.
  Let enc scheme : expr := Fst (Snd scheme).
  Let rand_cipher scheme : expr := Snd (Snd scheme).

  Definition q_calls : val :=
    λ:"Q" "f" "g",
      let: "counter" := ref #0 in
      λ:"x", if: ! "counter" < "Q" then ("counter" <- !"counter" + #1 ;; "f" "x") else "g" "x".

  Definition CPA : val :=
    λ:"b" "adv" "scheme" "Q",
      let: "rr_key_b" :=
        let: "key" := keygen "scheme" #() in
        let: "enc_key" := enc "scheme" "key" in
        if: "b" then
          "enc_key"
        else
          rand_cipher "scheme" in
      let: "oracle" := q_calls "Q" "rr_key_b" (rand_cipher "scheme") in
      let: "b'" := "adv" "oracle" in
      "b'".

  Variable xor : val.
  (* We probably need to assume that forall x, Bij (xor x). *)
  Variable (xor_sem : fin (S Message) -> fin (S Output) -> fin (S Output)).
  Variable H_xor : forall x, Bij (xor x).

  Definition prf_enc : val :=
    λ:"prf" "key",
      let: "prf_key" := "prf" "key" in
      λ: "msg",
        let: "r" := rand #Input in
        let: "z" := "prf_key" "r" in
        ("r", xor "z" "msg").

  Section security_defs.
    (* Tentative sketch of security definitions as we'd write them at the toplevel. *)
    (* Arguments to the game (adversary, scheme, ...) are omitted. *)

    Variable ε : R.

    (* book statement *)
    Check
      (let φ := (λ v, bool_decide (v = #true)) in
       forall σ, prob (lim_exec ((CPA #true)%E, σ)) φ = prob (lim_exec ((CPA #false)%E, σ)) φ + ε)%R.

    (* what we get from ARcoupl_eq_elim *)
    Check
      (forall σ, (lim_exec ((CPA #true)%E, σ)) #true = (lim_exec ((CPA #false)%E, σ)) #true + ε)%R.

    (* what we get from adequacy *)
    Check
      (forall σ,
          ARcoupl (lim_exec ((CPA #true)%E, σ)) (lim_exec ((CPA #false)%E, σ)) (=) ε).

    (* the refinement we might prove for some ε *)
    Check
      (⊢  ⤇ (CPA #true) -∗ ↯ ε -∗ WP (CPA #false) {{ v, ∃ v', ⤇ Val v' ∗ ⌜v = v'⌝ }} ).
  End security_defs.

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

  Definition rf_keygen : val := λ:<>, rand #Key.
  Definition rf_enc : expr := prf_enc random_function.
  Definition rf_rand_cipher : val := λ:<>, let:"i" := rand #Input in let:"o" := rand #Output in ("i", "o").
  Definition rf_scheme : expr := (rf_keygen, (rf_enc, rf_rand_cipher)).

  Definition CPA_rf : val := λ:"b" "adv", CPA "b" "adv" rf_scheme.

  Definition TMessage := TInt.
  Definition TKey := TInt.
  Definition TInput := TInt.
  Definition TOutput := TInt.
  Definition TCipher := (TInput * TMessage)%ty.
  Definition TAdv := ((TMessage → TCipher) → TBool)%ty.
  Variable adv : val.
  Variable adv_typed : (∅ ⊢ₜ adv : TAdv).


  (* TODO: Should we prove a logical refinement, or a WP refinement? *)
  Theorem rf_is_CPA (Q : nat) :
    ↯ (Q * Q / (2 * Input)) ⊢ (REL (CPA #true adv rf_scheme #Q) << (CPA #false adv rf_scheme #Q) : lrel_bool).
  Proof with (rel_pures_l ; rel_pures_r).
    iIntros "ε".
    rel_pures_l.
    rewrite /CPA.
    rewrite /rf_scheme/rf_keygen/rf_enc/prf_enc/enc/keygen.
    rel_pures_l.
    rel_pures_r.
    rel_apply refines_couple_UU.
    iIntros (key) "!>".
    rel_pures_l ; rel_pures_r.
    rewrite /random_function. rel_pures_r.
    rewrite /init_map. rel_pures_r.
    rewrite /init_list.
    rel_alloc_r listref' as "listref'". rel_pures_r.
    rel_alloc_r mapref' as "mapref'". rel_pures_r.
    rel_alloc_l listref as "listref". rel_pures_l.
    rel_alloc_l mapref as "mapref". rel_pures_l.
    rel_bind_l (q_calls _ _ _)%E.
    rel_bind_r (q_calls _ _ _)%E.
    unshelve iApply (refines_bind with "[ε] []").
    1:{ exact (interp (TMessage → TCipher) []). }
    2:{
      iIntros (f f') "Hff'".
      simpl.
      unshelve iApply (refines_app with "[] [Hff']").
      3: rel_values.
      rel_arrow_val.
      iIntros (o o') "Hoo'". rel_pures_l ; rel_pures_r.
      repeat rel_apply refines_app. 3: rel_values.
      Unshelve.
      3: exact (interp TBool []).
      1: { rel_arrow_val. iIntros (??) "#(%_&->&->)". rel_pures_l ; rel_pures_r. rel_values. }
      replace (lrel_arr (lrel_arr lrel_int (lrel_prod lrel_int lrel_int))
                 (interp TBool nil)) with
        (interp TAdv []) by easy.
      iApply refines_typed.
      assumption.
    }

    rewrite /q_calls. rel_pures_l. rel_pures_r.
    rel_alloc_l counter as "counter". rel_alloc_r counter' as "counter'". rel_pures_l ; rel_pures_r.
    iApply (refines_na_alloc (∃ q : nat , ↯ ((Q-q) * (Q-q) / (2 * Input)) ∗ counter ↦ #q ∗ counter' ↦ₛ #q)%I
              (nroot.@"cpa")); iFrame.
    iSplitL.
    1: { iExists 0. rewrite Rminus_0_r. iFrame. }

    iIntros "#Hinv".

    rel_arrow_val.
    iIntros (??) "#(%msg&->&->)" ; rel_pures_l ; rel_pures_r.
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "(> (%q & ε & counter & counter') & Hclose)".
    rel_load_l ; rel_load_r...
    rewrite /rf_rand_cipher.
    case_bool_decide as Hq...
    - rel_load_l ; rel_load_r... rel_store_l ; rel_store_r...
      assert (Z.to_nat msg < S Message) as Hmsg by admit.
      rel_apply (refines_couple_UU).
      iIntros (r_in) "!>"...
      rel_bind_l (Match _ _ _ _ _).
      rel_bind_r (Rand _ _).
      unshelve iApply (refines_bind with "[-]").
      1: exact lrel_int.
      2: { iIntros (??) "#(%out&->&->)" => /=...  }
      (* (xor_sem (Fin.of_nat_lt Hmsg)) *)
      (* 1: rewrite Nat2Z.id. *)
      give_up.
    - iApply (refines_na_close with "[-]").
      iFrame.
      rel_apply refines_couple_UU.
      iIntros (?) "!>"...
      rel_apply refines_couple_UU.
      iIntros (?) "!>"...
      rel_values => //.
      iModIntro.
      iExists _,_,_,_.
      repeat iSplit ; try done.
      all: iExists _ ; done.
      

  Abort.

  Theorem rf_is_CPA (Q : nat) :
    (↯ (Q * Q / (2 * Input)) ⊢  ⤇ (CPA #false adv rf_scheme #Q) -∗ WP (CPA #true adv rf_scheme #Q) {{ v, ∃ v', ⤇ Val v' ∗ ⌜v = v'⌝ }} ).
  Proof.
    iIntros "ε spec".
    rewrite /CPA.
    rewrite /rf_scheme /rf_enc /prf_enc /rf_keygen.
    wp_pures. tp_pures.
    tp_bind (rand _)%E.
    wp_bind (rand _)%E.
    iApply (wp_couple_rand_rand with "spec").
    iIntros "!> %key spec" => /=.
    wp_pures ; tp_pures.
    wp_bind (q_calls _ _).
    tp_bind (q_calls _ _).
    rewrite /q_calls ; wp_pures ; tp_pures.
    wp_alloc r. tp_alloc as rs. wp_pures ; tp_pures.

  Abort.

End proofs.
