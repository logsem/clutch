From clutch.approxis Require Import approxis map list.
From clutch.approxis.examples Require Import iterable_expression security_aux.
From clutch.approxis Require Export bounded_oracle.
Set Default Proof Using "Type*".

Section symmetric.

  Context `{approxisRGS Σ}.

  (** A symmetric encryption [scheme] is given by three functions (keygen, encrypt, decrypt).

The set of keys, messages, and ciphertexts are modelled by finite sets of integers [0, Key], [0, Input], and [0, Output].
   *)

  Class SYM_init_params :=
    { card_key : nat
    ; card_message : nat
    ; card_cipher : nat
    ; sym_params : val := (#card_key, #card_message, #card_cipher) }.

  (* Variable Key Message Cipher : nat. *)

  (* Let keygen scheme : expr := Fst scheme.
     Let enc scheme : expr := Fst (Snd scheme).
     Let rand_cipher scheme : expr := Snd (Snd scheme). *)

  Definition get_param_card_key : val := λ:"sym_params", Fst (Fst "sym_params").
  Definition get_param_card_message : val := λ:"sym_params", Snd (Fst "sym_params").
  Definition get_param_card_cipher : val := λ:"sym_params", Snd "sym_params".

  (* rand_cipher is currently unused ; it would be useful if a SYM module had
   abstract types. *)
  (* enc_scheme can be any expression that reduces to a triplet of the form:
  `(keygen, (enc, dec))%V`. This way we can initialize a local state that can
  be shared between the three functions.
  We thunk `enc_scheme`, this way, it doesn't have to be evaluated every time
  we want to access a parameter or `rand_cipher`.
  For now, the state is also shared with `keygen`, we'll see if it's relevant.
  *)

  Class SYM_init `{SYM_init_params} :=
    { keygen : val

    ; enc_scheme : (PACKAGE_STRUCT 2)
    ; enc_scheme_params : (PACKAGE_PARAMS 2)
    ; enc_scheme_props : @PACKAGE _ _ _ enc_scheme enc_scheme_params
    ; rand_cipher : val
    
    ; sym_scheme : val := (sym_params, (keygen, λ: <>, package), rand_cipher)%V
    }.

  Definition find_in_bounds {X} (i : nat) (l : list X) (Hlen : i < length l) : X :=
    is_Some_proj (lookup_lt_is_Some_2 l i Hlen).

  Lemma le02 : 0 < 2. Proof. by lia. Qed.
  Lemma le12 : 1 < 2. Proof. by lia. Qed.

  (* `get_enc` and `get_dec` should now be called with an
   encryption scheme i.e. only the tuple of these three, this ensures
   the state is shared between them *)
  Definition get_params : val := λ:"sym_scheme", Fst (Fst "sym_scheme").
  Definition get_card_key : val := λ:"sym_scheme", Fst (Fst (Fst (Fst "sym_scheme"))).
  Definition get_card_message : val := λ:"sym_scheme", Snd (Fst (Fst (Fst "sym_scheme"))).
  Definition get_card_cipher : val := λ:"sym_scheme", Snd (Fst (Fst "sym_scheme")).
  Definition get_enc_scheme : val := λ:"sym_scheme", Snd (Snd (Fst "sym_scheme")).
  Definition get_keygen : val := λ:"sym_scheme", Fst (Snd (Fst "sym_scheme")).
  Definition get_enc `{PACKAGE_STRUCT 2} : val :=
    λ:"enc_scheme", (find_in_bounds 0 getters (package_getter_valid_index le02)) "enc_scheme".
  Definition get_dec `{PACKAGE_STRUCT 2} : val :=
    λ:"enc_scheme", (find_in_bounds 1 getters (package_getter_valid_index le12)) "enc_scheme".
  Definition get_rand_cipher : val := λ:"sym_scheme", Snd "sym_scheme".

  Section CPA.

    Context `{PACKAGE_STRUCT 2}.

    (** Indistinguishability of Chosen Plaintext Attacks security
      for symmetric/private key encryption.

Real vs random variant (sometimes called "CPA$").

References:
- Definition 7.2, Mike Rosulek, 2020, The Joy of Cryptography.
- Definition 3.22, Jonathan Katz and Yehuda Lindell, 2021, Introduction to Modern Cryptography (3rd edition).

Our definition deviates from Rosulek's and Katz/Lindell in that we wrap the encryption oracle with [q_calls] to enforce the bound [Q] on the number of oracle calls, while loc. cit. rely on the assumption that the adversary runs in polynomial time in the security parameter.

Our definition further differs from Katz/Lindell in that, depending on the value of [b], the encryption oracle either encrypts the adversary's message or return a random ciphertext, whereas in Katz/Lindell, the encryption oracle encrypts one of two messages provided by the adversary. These two notions are equivalent by Claim 7.3 in Rosulek's book.
     *)

    Definition CPA : val :=
      λ:"b" "adv" "scheme" "Q",
        let: "rr_key_b" :=
          let: "enc_scheme" := get_enc_scheme "scheme" #() in
          let: "key" := get_keygen "scheme" #() in
          (* let: "enc_key" := enc "scheme" "key" in *)
          if: "b" then
            (* "enc_key" *)
            get_enc "enc_scheme" "key"
          else
            get_rand_cipher "scheme" in
        let: "oracle" := q_calls (get_card_message "scheme") "Q" "rr_key_b" in
        let: "b'" := "adv" "oracle" in
        "b'".

    Definition CPA_real : val :=
      λ:"scheme" "Q",
        let: "enc_scheme" := get_enc_scheme "scheme" #() in
        let: "key" := get_keygen "scheme" #() in
        q_calls (get_card_message "scheme") "Q" (get_enc "enc_scheme" "key").

    (* TODO this should just use `rand` instead of get_rand_cipher. *)
    Definition CPA_rand : val :=
      λ:"scheme" "Q",
        q_calls (get_card_message "scheme") "Q" (get_rand_cipher "scheme").

  End CPA.

End symmetric.

Module CPA_sem.

  Context `{PACKAGE_STRUCT 2}.

  Definition CPA_real : val :=
    λ:"scheme" "Q",
      let: "enc_scheme" := get_enc_scheme "scheme" #() in
      let: "key" := get_keygen "scheme" #() in
      q_calls_poly #() #() "Q" (get_enc "enc_scheme" "key").

  (* TODO this should just use `rand` instead of get_rand_cipher. *)
  Definition CPA_rand : val :=
    λ:"scheme" "Q",
      q_calls_poly #() #() "Q" (get_rand_cipher "scheme").

End CPA_sem.

From clutch.approxis.examples Require Import xor.

Section instance_test.

  (** Upper bound of messages. *)
  Variable N : nat.

  Let Message := N.
  Let Key := N.
  Let Output := N.
  Let Cipher := N.

  Local Opaque INR.

  Variable xor_struct : XOR (Key := Message) (Support := Cipher).

  (** We specialize the construction to an idealized random function family. *)
  Definition otp_keygen : val := λ:<>, rand #Key.
  Definition otp_keygen_tape : expr := let: "α" := alloc #Key in λ: <>, rand("α") #Key.
  Definition otp_enc : val :=
    λ: "key" "msg", xor "msg" "key".
  Definition otp_enc_delay : val :=
    λ: "α" <> "msg", let: "key" := rand("α") #Key in xor "msg" "key".
  Definition otp_rand_cipher : val :=
    λ: <>, rand #Output. (* let:"o" := rand #Output in "o". *)
  Definition otp_rand_cipher_tape : expr :=
    let: "β" := alloc #Output in
    λ: <>, rand("β") #Output. (* let:"o" := rand(#lbl:β) #Output in "o". *)
  Definition otp_dec : val :=
    λ: "key" "c", xor "c" "key".
  
  Definition otp_scheme : expr :=
    (otp_enc, otp_dec).
  Definition otp_scheme_delay : expr :=
    let: "α" := alloc #Key in
    (otp_enc_delay "α", otp_dec).

  Local Instance SYM_otp_param : SYM_init_params :=
    {| card_key := Key ; card_message := Message ; card_cipher := Cipher |}.

  Lemma len2 {X} (x y : X) : length [x; y] = 2. Proof. reflexivity. Qed.
  Local Instance otp_package_struct : PACKAGE_STRUCT 2 := {|
      package := otp_scheme
    ; getters := [(λ: "x", Fst "x")%V; (λ: "x", Snd "x")%V]
    ; len_getters := len2 (λ: "x", Fst "x")%V (λ: "x", Snd "x")%V
  |}.


  Local Instance otp_package_params {Σ} : @PACKAGE_PARAMS Σ 2.
  Proof using Cipher Message N xor_struct. unshelve econstructor.
    - exact [2; 2].
    - exact (λ _ _, True%I).
    - exact (λ _ _, True%I).
    - exact (λ _ _ _ _, True%I).
    - exact (λ _ _ _ _, True%I).
    - reflexivity.
    - exact (λ _ args retv, match args with
        | nil => True
        | key :: tl => match tl with
          | nil => True
          | msg :: tl => ⌜∃ (n_key n_msg : nat),
              key = #n_key
            ∧ msg = #n_msg
            ∧ retv = #(xor_sem n_msg n_key)⌝
        end
      end%I).
    - exact (λ _ args retv, match args with
        | nil => True
        | key :: tl => match tl with
          | nil => True
          | msg :: tl => ⌜∃ (n_key n_msg : nat),
              key = #n_key
            ∧ msg = #n_msg
            ∧ retv = #(xor_sem n_msg n_key)⌝
        end
      end%I).
    - intros *. simpl. apply bi.equiv_entails; split.
      + iIntros "_". done.
      + iIntros "_". done.
  Defined.

  Context `{!approxisRGS Σ}.
  
  Variable xor_spec : XOR_spec.

  Local Instance otp_package : PACKAGE.
  Proof. unshelve econstructor.
    - exact [lrel_int_bounded 0 N; lrel_int_bounded 0 N].
    - exact [[lrel_int_bounded 0 N; lrel_int_bounded 0 N];
      [lrel_int_bounded 0 N; lrel_int_bounded 0 N]].
    - simpl. repeat constructor.
    - iStartProof.
      iIntros (K e E A).
      iExists (λ _, (otp_enc, otp_dec)%V), [], [].
      repeat iSplitL. 1: done. 1: done.
      + iPureIntro. exists (λ _, otp_enc%V).
        clear K e E A.
        split;
        first (intros *; split;
            iIntros "H"; rel_pures_l; rel_pures_r; iAssumption).
        rewrite /package_function_spec.
        intros * args_sem_typed.
        inversion args_sem_typed as
          [|key y targs tlrel H1 args_sem_typed_tl eq1 eq2]; subst.
        inversion args_sem_typed_tl as
          [|msg y targs' tlrel' H1' args_sem_typed_tl' eq1 eq2]; subst.
        clear args_sem_typed_tl args_sem_typed.
        destruct targs' as [|hd tl'''].
        2: inversion args_sem_typed_tl'.
        clear  args_sem_typed_tl'.
        split; last split.
        * iIntros "_".
          iPoseProof H1 as "Hrelkey".
          iPoseProof H1' as "Hrelmsg".
          iPure "Hrelkey" as Hrelkey.
          iPure "Hrelmsg" as Hrelmsg.
          destruct Hrelkey as [n_key [eq1 [eq2 Hkeybound]]].
          destruct Hrelmsg as [n_msg [eq1' [eq2' Hmsgbound]]]; subst.
          iExists #(xor_sem (Z.to_nat n_msg) (Z.to_nat n_key)).
          iIntros "Hrel_args".
          simpl.
          rewrite /otp_enc. rel_pures_l.
          rewrite -(Z2Nat.id n_key); last lia.
          rel_apply xor_correct_l; try lia.
          rewrite Nat2Z.id.
          rel_apply "Hrel_args".
          iSplit; last done. iPureIntro.
          exists (Z.to_nat n_key), (Z.to_nat n_msg).
          repeat split; try done.
          rewrite Z2Nat.id; last lia.
          reflexivity.
        * iIntros "_".
          iPoseProof H1 as "Hrelkey".
          iPoseProof H1' as "Hrelmsg".
          iPure "Hrelkey" as Hrelkey.
          iPure "Hrelmsg" as Hrelmsg.
          destruct Hrelkey as [n_key [eq1 [eq2 Hkeybound]]].
          destruct Hrelmsg as [n_msg [eq1' [eq2' Hmsgbound]]]; subst.
          iExists #(xor_sem (Z.to_nat n_msg) (Z.to_nat n_key)).
          iIntros "Hrel_args".
          simpl.
          rewrite /otp_enc. rel_pures_r.
          rewrite -(Z2Nat.id n_key); last lia.
          rel_apply xor_correct_r; try lia.
          rewrite Nat2Z.id.
          rel_apply "Hrel_args".
          iSplit; last done. iPureIntro.
          exists (Z.to_nat n_key), (Z.to_nat n_msg).
          repeat split; try done.
          rewrite Z2Nat.id; last lia.
          reflexivity.
        * intros * HIinv. iIntros "Inv".
          rewrite /otp_enc.
          simpl.
          rel_arrow_val.
          iIntros (v1 v2 [n_key [eq1 [eq2 Hkeybound]]]); subst.
          rel_arrow_val.
          iIntros (v1 v2 [n_msg [eq1 [eq2 Hmsgbound]]]); subst.
          rel_pures_l; rel_pures_r.
          rewrite -(Z2Nat.id n_key); last lia.
          rel_apply xor_correct_l; try lia.
          rel_apply xor_correct_r; try lia.
          rel_vals.
          apply inj_le.
          apply PeanoNat.lt_n_Sm_le.
          apply xor_dom; lia.
      + iPureIntro. exists (λ _, otp_dec%V).
        clear K e E A.
        split;
        first (intros *; split;
            iIntros "H"; rel_pures_l; rel_pures_r; iAssumption).
        rewrite /package_function_spec.
        intros * args_sem_typed.
        inversion args_sem_typed as
          [|key y targs tlrel H1 args_sem_typed_tl eq1 eq2]; subst.
        inversion args_sem_typed_tl as
          [|msg y targs' tlrel' H1' args_sem_typed_tl' eq1 eq2]; subst.
        clear args_sem_typed_tl args_sem_typed.
        destruct targs' as [|hd tl'''].
        2: inversion args_sem_typed_tl'.
        clear  args_sem_typed_tl'.
        split; last split.
        * iIntros "_".
          iPoseProof H1 as "Hrelkey".
          iPoseProof H1' as "Hrelmsg".
          iPure "Hrelkey" as Hrelkey.
          iPure "Hrelmsg" as Hrelmsg.
          destruct Hrelkey as [n_key [eq1 [eq2 Hkeybound]]].
          destruct Hrelmsg as [n_msg [eq1' [eq2' Hmsgbound]]]; subst.
          iExists #(xor_sem (Z.to_nat n_msg) (Z.to_nat n_key)).
          iIntros "Hrel_args".
          simpl.
          rewrite /otp_dec. rel_pures_l.
          rewrite -(Z2Nat.id n_key); last lia.
          rel_apply xor_correct_l; try lia.
          rewrite Nat2Z.id.
          rel_apply "Hrel_args".
          iSplit; last done. iPureIntro.
          exists (Z.to_nat n_key), (Z.to_nat n_msg).
          repeat split; try done.
          rewrite Z2Nat.id; last lia.
          reflexivity.
        * iIntros "_".
          iPoseProof H1 as "Hrelkey".
          iPoseProof H1' as "Hrelmsg".
          iPure "Hrelkey" as Hrelkey.
          iPure "Hrelmsg" as Hrelmsg.
          destruct Hrelkey as [n_key [eq1 [eq2 Hkeybound]]].
          destruct Hrelmsg as [n_msg [eq1' [eq2' Hmsgbound]]]; subst.
          iExists #(xor_sem (Z.to_nat n_msg) (Z.to_nat n_key)).
          iIntros "Hrel_args".
          simpl.
          rewrite /otp_dec. rel_pures_r.
          rewrite -(Z2Nat.id n_key); last lia.
          rel_apply xor_correct_r; try lia.
          rewrite Nat2Z.id.
          rel_apply "Hrel_args".
          iSplit; last done. iPureIntro.
          exists (Z.to_nat n_key), (Z.to_nat n_msg).
          repeat split; try done.
          rewrite Z2Nat.id; last lia.
          reflexivity.
        * intros * HIinv. iIntros "Inv".
          rewrite /otp_dec.
          simpl.
          rel_arrow_val.
          iIntros (v1 v2 [n_key [eq1 [eq2 Hkeybound]]]); subst.
          rel_arrow_val.
          iIntros (v1 v2 [n_msg [eq1 [eq2 Hmsgbound]]]); subst.
          rel_pures_l; rel_pures_r.
          rewrite -(Z2Nat.id n_key); last lia.
          rel_apply xor_correct_l; try lia.
          rel_apply xor_correct_r; try lia.
          rel_vals.
          apply inj_le.
          apply PeanoNat.lt_n_Sm_le.
          apply xor_dom; lia.
      + iPureIntro. iIntros "H". rewrite /package. simpl.
        rewrite /otp_scheme. rel_pures_l. iAssumption.
      + iPureIntro. iIntros "H". rewrite /package. simpl.
        rewrite /otp_scheme. rel_pures_r. iAssumption.
  Qed.
      
  Local Instance SYM_otp_scheme : SYM_init :=
    {|  keygen := otp_keygen
      ; enc_scheme := otp_package_struct
      ; enc_scheme_params := otp_package_params
      ; enc_scheme_props := otp_package
      ; rand_cipher := otp_rand_cipher |}.

End instance_test.
