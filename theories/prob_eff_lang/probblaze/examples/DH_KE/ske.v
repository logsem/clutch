From clutch.prob_eff_lang.probblaze Require Import notation logic.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import valgroup.
Set Default Proof Using "Type*".

Section symmetric.

  (** A symmetric encryption [scheme] is given by three functions (keygen, encrypt, decrypt).

      The set of keys, messages, and ciphertexts are modelled by finite sets of integers [0, Key], [0, Input], and [0, Output].
   *)

  Class SYM_params :=
    { card_key : nat
    ; card_message : nat
    ; card_cipher : nat
    ; sym_params : val := (#card_key, #card_message, #card_cipher)%V
    ; msg_of_int : val :=  λ: "m", if: ("m" < #card_message) then SOME "m" else NONE }.

  Definition get_param_card_key : val := λ:"sym_params", Fst (Fst "sym_params").
  Definition get_param_card_message : val := λ:"sym_params", Snd (Fst "sym_params").
  Definition get_param_card_cipher : val := λ:"sym_params", Snd "sym_params".

  (* rand_cipher is currently unused ; it would be useful if a SYM module had
   abstract types. *)
  Class SYM_struct `{Sym_params : SYM_params} :=
    { enc : val
    ; dec : val
    ; rand_cipher : val
    ; sym_scheme : val := (sym_params, enc, dec, rand_cipher)%V
    }.

  Class SYM `{probblazeRGS Σ} `{sym_struct : SYM_struct} :=
    { enc_sem : nat → nat → nat
    ; dec_sem : nat → nat → nat
    ; dec_enc_sem_correct k m : k ≤ card_key → m ≤ card_message → dec_sem k (enc_sem k m) = m
    ; enc_correct_l : ∀ E K k m X R e,
        (BREL fill K #(enc_sem k m) ≤ e @ E <|X|> {{R}}) -∗
        (BREL fill K (enc #k #m) ≤ e @ E <|X|> {{R}})
    ; enc_correct_r : ∀ E K k m X R e,
        BREL e ≤ fill K #(enc_sem k m) @ E <|X|> {{R}} -∗
        BREL e ≤ fill K (enc #k #m) @ E <|X|> {{R}}
    ; dec_correct_l : ∀ E K k m X R e,
        BREL fill K #(dec_sem k m) ≤ e @ E <|X|> {{R}} -∗
        BREL fill K (dec #k #m) ≤ e @ E <|X|> {{R}}
    ; dec_correct_r : ∀ E K k m X R e,
        BREL e ≤ fill K #(dec_sem k m) @ E <|X|> {{R}} -∗
        BREL e ≤ fill K (dec #k #m) @ E <|X|> {{R}}
    (* [rand_cipher] draws a uniform ciphertext.  Unlike [enc]/[dec] it has no
       deterministic semantics, so what the relational logic needs is a
       *synchronous self-coupling*: two simultaneous draws can be made to agree.
       This is the identity coupling, and it is what lets a simulator that
       answers with [rand_cipher #()] be related to a reduction that encrypts
       with a one-time key. *)
    ; rand_cipher_coupl : ∀ E K K' X R,
        (∀ c : nat, ⌜(c ≤ card_cipher)%nat⌝ -∗
            BREL fill K #c ≤ fill K' #c @ E <|X|> {{R}}) -∗
        BREL fill K (rand_cipher #()%V) ≤ fill K' (rand_cipher #()%V) @ E <|X|> {{R}}
    }.


  Definition get_params : val := λ:"sym_scheme", Fst (Fst (Fst "sym_scheme")).
  Definition get_card_key : val := λ:"sym_scheme", Fst (Fst (Fst (Fst (Fst "sym_scheme")))).
  Definition get_card_message : val := λ:"sym_scheme", Snd (Fst (Fst (Fst (Fst "sym_scheme")))).
  Definition get_card_cipher : val := λ:"sym_scheme", Snd (Fst (Fst (Fst "sym_scheme"))).
  Definition get_enc : val := λ:"sym_scheme", Snd (Fst (Fst ("sym_scheme"))).
  Definition get_dec : val := λ:"sym_scheme", Snd (Fst "sym_scheme").
  Definition get_rand_cipher : val := λ:"sym_scheme", Snd "sym_scheme".


End symmetric.

Module OTS.

  Definition OTS_real : val :=
    λ:"scheme" "m",
      let: "key" := rand (get_card_key "scheme") in
      get_enc "scheme" "key" "m".

  (* TODO this should just use `rand` instead of get_rand_cipher. *)
  Definition OTS_rand : val :=
    λ:"scheme" "m", get_rand_cipher "scheme" #()%V.

End OTS.
