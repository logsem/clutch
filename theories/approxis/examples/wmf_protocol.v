From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From clutch.prob_lang Require Import advantage typing.tychk.
From clutch.approxis Require Import map reltac2 approxis option.
From clutch.approxis.examples Require Import
  security_aux option symmetric_init
  bounded_oracle pubkey advantage_laws iterable_expression.
From mathcomp Require Import ssrbool.
Set Default Proof Using "All".
Import map.

Section protocol.

(*
  A → S : (A,{B, n}_ka)
  S → B : {A, n}_kb
*)

(* security parameter *)
Variable η : nat.

Let N := 2^η.

Variable Key : nat.
Variable Output : nat.

#[local] Instance sym_params : SYM_init_params := {|
    card_key := Key
  ; card_message := 2*N
  ; card_cipher := Output
|}.

Context `{sym : !SYM_init}.
Context `{!approxisRGS Σ}.

(* ASSUMPTION ON THE ENCRYPTION SCHEME *)

Definition left_lrel (τ : lrel Σ) (v : val) : iProp Σ := ∃ v', (lrel_car τ) v v'.
Definition right_lrel (τ : lrel Σ) (v : val) : iProp Σ := ∃ v', (lrel_car τ) v' v.

Definition lrel_input : lrel Σ := lrel_int_bounded 0 N * lrel_int_bounded 0 N.
Definition lrel_rand : lrel Σ := lrel_int_bounded 0 N.
Variable lrel_output : lrel Σ.
Variable lrel_key : lrel Σ.

Variable senc : list loc → val.
Variable sdec : list loc → val.

Variable P0l : list loc → iProp Σ.
Variable P0r : list loc → iProp Σ.

Variable Pl : list loc → iProp Σ.
Variable Pr : list loc → iProp Σ.
Variable Plr : list loc → list loc → iProp Σ.

Definition P0_P_l_prop := ∀ lls, P0l lls -∗ Pl lls.
Definition P0_P_r_prop := ∀ rls, P0r rls -∗ Pr rls.
Definition P0lr_Plr_prop := ∀ lls rls, P0l lls -∗ P0r rls -∗ Plr lls rls.
Hypothesis P0_P_l : P0_P_l_prop.
Hypothesis P0_P_r : P0_P_r_prop.
Hypothesis P0lr_Plr : P0lr_Plr_prop.

Definition refines_init_scheme_l_prop := forall K e E A,
  (∀ lls,
    P0l lls -∗
    refines E
      (fill K (senc lls, sdec lls))
      e A)
  ⊢ refines E
      (fill K (symmetric_init.get_enc_scheme symmetric_init.sym_scheme #()))
      e A.

Definition refines_init_scheme_r_prop := forall K e E A,
  (∀ rls,
    P0r rls -∗
    refines E
      e
      (fill K (senc rls, sdec rls))
      A)
  ⊢ refines E
      e
      (fill K (symmetric_init.get_enc_scheme symmetric_init.sym_scheme #()))
      A.

Hypothesis refines_init_scheme_l : refines_init_scheme_l_prop.

Hypothesis refines_init_scheme_r : refines_init_scheme_r_prop.

Definition refines_sym_keygen_couple_prop := forall K K' E A,
  (∀ key,
    (lrel_car lrel_key) key key -∗
      refines E
        (fill K  (Val key))
        (fill K' (Val key))
        A)
  ⊢ refines E
      (fill K  (symmetric_init.keygen #()))
      (fill K' (symmetric_init.keygen #()))
      A.
Hypothesis refines_sym_keygen_couple : refines_sym_keygen_couple_prop.

Definition refines_keygen_l_prop := forall K e E A,
  (∀ key,
    left_lrel lrel_key key -∗
    refines E
      (fill K (Val key))
      e A)
  ⊢ refines E
      (fill K (symmetric_init.keygen #()))
      e A.
Definition refines_keygen_r_prop := forall K e E A,
  (∀ key,
    right_lrel lrel_key key -∗
    refines E
      e
      (fill K (Val key))
      A)
  ⊢ refines E
      e
      (fill K (symmetric_init.keygen #()))
      A.
Hypothesis refines_keygen_l : refines_keygen_l_prop.
Hypothesis refines_keygen_r : refines_keygen_r_prop.

Definition sym_is_cipher_lr_l {lls rls : list loc} (msg : val) (c k : val) : iProp Σ :=
  ∀ K e E A,
    (Plr lls rls -∗
      refines E
      (fill K (Val msg))
      e A)
  -∗ refines E
      (fill K (sdec lls k c))
      e A.

Definition refines_senc_lr_prop :=
  ∀ (lls rls : list loc) (msg msg' : val) (k k' : val) K K' E A,
  lrel_key k k' ∗ lrel_input msg msg' ∗ Plr lls rls ⊢
    ((∀ (c c' : val),
       lrel_output c c'
    -∗ @sym_is_cipher_lr_l lls rls msg c k
    -∗ refines E
        (fill K (Val c))
        (fill K' (Val c'))
        A)
  -∗ refines E
      (fill K  (senc lls k  msg ))
      (fill K' (senc rls k' msg'))
      A).

Hypothesis refines_couple_senc_lr : refines_senc_lr_prop.

Definition senc_sem_typed_prop :=
  ∀ lls rls (𝒩 : namespace) (P : iProp Σ),
  (∃ (Q : iProp Σ),
    P ⊣⊢
      (Q
    ∗ Plr lls rls)
  ) →
  na_invP 𝒩 P
    ⊢ refines top (senc lls)
    (senc rls) (lrel_key → lrel_input → lrel_output).

Hypothesis senc_sem_typed : senc_sem_typed_prop.

(* agent name *)
(* Variable A : val.
Variable lrel_msg : lrel Σ.
Hypothesis test : ⊢ (lrel_car (lrel_nat → lrel_nat → lrel_nat → lrel_msg)) A A.

Definition lazy_rand : val :=
  λ: "N",
    let: "mem" := init_map #() in
    λ: "i", match: get "mem" "i" with 
      | NONE => let: "r" := rand "N" in
        set "mem" "i" "r";; "r"
      | SOME "r" => "r"
    end. *)

Definition init_scheme (e : expr) : expr :=
  let: "scheme" := symmetric_init.get_enc_scheme symmetric_init.sym_scheme
    #() in
  e "scheme".

Definition a_to_s : val :=
  λ: "b" "nonce_count" "senc",
  λ: "i" "j" "k",
    if: get "nonce_count" ("i", "j", "k") = #false then
      set "nonce_count" ("i", "j", "k") #true;;
      if: "b" then
        λ: "ka",
          ((A "i", "senc" ("ka" "i") (A "j", rand #N)), "r_adv")
      else
        λ: "ka",
          ((A "i", "senc" ("ka" "i") (A "j", "r_adv")), "r_adv")
    else #().

Definition s_to_b : val :=
  λ: "b" "nonce_count" "senc" "sdec",
  λ: "i" "j" "k",
    if: get "nonce_count" ("i", "j", "k") = #false then
      set "nonce_count" ("i", "j", "k") #true;;
      λ: "ka" "input",
        let: "nonce" := "sdec" "ka" (Snd "input") in
        let: "sender" := Fst "input" in
        let: "dest" := Fst "nonce" in
        let: "nonce" := Snd "nonce" in
        if: "sender" = A "i" `and` "dest" = A "j" then
          "senc" ("ka" "j") ("sender", "nonce")
        else #()
    else #().

Definition a_to_s_once : val :=
  λ: "b" "senc" "ka", (* parameters of the protocol *)
    λ: "r_adv", (* attacker provided random *)
      if: "b" then
        (#0, "senc" "ka" (#1, rand #N))
      else
        (#0, "senc" "ka" (#1, "r_adv")).

Definition s_to_b_once : val :=
  λ: "b" "senc" "sdec" "ka" "kb", (* parameters of the protocol *)
    λ: "input",
      let: "nonce" := "sdec" "ka" (Snd "input") in
      let: "sender" := Fst "input" in
      let: "dest" := Fst "nonce" in
      let: "nonce" := Snd "nonce" in
      if: "sender" = #0 `and` "dest" = #1 then
        "senc" "kb" ("sender", "nonce")
      else #().

Definition b_recv_once : val :=
  λ: "b" "kb" "sdec", (* parameters of the protocol *)
    λ: "input", #().
      (* let: "nonce" := "sdec" "kb" "input" in
      let: "sender" := Fst "nonce" in
      let: "nonce" := Snd "nonce" in
      if: "sender" = #0 then
        #()
      else #(). *)

Definition wmf_once : expr :=
  λ: "b" "enc_scheme",
    (a_to_s_once "b" (symmetric_init.get_enc "enc_scheme"),
     s_to_b_once "b" "nonce_count" (symmetric_init.get_enc "enc_scheme")
      (symmetric_init.get_dec "enc_scheme")).

  Section eavesdropping_attacker.
  
  Definition wmf_eav : expr :=
    λ: "b" "scheme",
      let: "r_adv" := rand #N in
      ("r_adv",
        let: "ka" := keygen #() in
        let: "kb" := keygen #() in
        let: "msg1" :=
          a_to_s_once "b" (symmetric_init.get_enc "scheme") "ka" "r_adv" in
        ("msg1",
          let: "msg2" :=
            s_to_b_once "b"
              (symmetric_init.get_enc "scheme")
              (symmetric_init.get_dec "scheme")
              "ka" "kb" "msg1" in
          ("msg2",
           b_recv_once "b" "kb" (symmetric_init.get_dec "scheme") #())
        )
      ).
  
  Definition s_to_b_delay : val :=
    λ: "b" "senc" "ka" "kb", (* parameters of the protocol *)
      λ: "input",
        let: "sender" := #0 in
        let: "dest" := #1 in
        let: "nonce" := rand #N in
        if: "sender" = #0 `and` "dest" = #1 then
          ("senc" "kb" ("sender", "nonce"), ("sender", "senc" "ka" ("dest", "nonce")))
        else #().
      
  Definition wmf_eav_delay : expr :=
    λ: "b" "scheme",
      let: "r_adv" := rand #N in
      ("r_adv",
        let: "ka" := keygen #() in
        let: "kb" := keygen #() in
        let: "msg2" :=
          s_to_b_delay "b"
            (symmetric_init.get_enc "scheme")
            "ka" "kb" #() in
        (Snd "msg2",
          (
            Fst "msg2",
            b_recv_once "b" "kb" (symmetric_init.get_dec "scheme") #()
          )
        )
      ).

  Definition lrel_id : lrel Σ := lrel_int_bounded 0 1.

  Lemma wmf_eav__wmf_eav_delay : 
    ⊢ REL init_scheme (wmf_eav #true) <<
      init_scheme (wmf_eav_delay #true) :
        (lrel_rand * ((lrel_id * lrel_output) * (lrel_output * ()))).
  Proof with (rel_pures_l; rel_pures_r).
    rewrite /init_scheme...
    rel_apply refines_init_scheme_l.
    iIntros (lls) "HP".
    rel_apply refines_init_scheme_r.
    iIntros (rls) "HP'"...
    rel_apply refines_couple_UU; first done.
    iIntros (r_dummy Hrdummybound). iModIntro...
    rel_apply refines_sym_keygen_couple.
    iIntros (ka) "#Hrelka"...
    rel_apply refines_sym_keygen_couple.
    iIntros (kb) "#Hrelkb"...
    rel_apply refines_pair.
    { rel_vals. iExists r_dummy. iPureIntro; repeat split; lia. }
    rewrite /a_to_s_once/s_to_b_delay/get_dec/get_enc...
    rel_apply refines_couple_UU; first done.
    iModIntro; iIntros (nonce Hnoncebound)...
    rel_apply (refines_couple_senc_lr with "[HP HP']").
    {
      iSplitR; first iAssumption.
      iSplitR; last (iApply (P0lr_Plr with "HP HP'")).
      iExists _, _, _, _.
      repeat iSplit; try (iPureIntro; done).
      - iExists 1. repeat iSplit; iPureIntro; try done.
        apply Z2Nat.inj_le; try lia. rewrite /N.
        rewrite Nat2Z.id. rewrite Nat2Z.id.
        apply fin.pow_ge_1. lia.
      - iExists nonce; repeat iSplit; iPureIntro; try done; try lia.
    }
    iIntros (c c') "#Hrelcipher Hcipher"...
    rewrite /s_to_b_once...
    rel_apply "Hcipher".
    iIntros "HP"...
    rel_bind_l (senc _ _ _).
    rel_bind_r (senc _ _ _).
    rel_apply (refines_bind with "[HP]").
    {
      rel_apply (refines_na_alloc (Plr lls rls) (nroot.@"wmf__delay")).
      iFrame.
      iIntros "#Inv".
      repeat rel_apply refines_app.
      - rel_apply senc_sem_typed; last iAssumption. exists True%I.
        apply bi.equiv_entails; split; iIntros "H";
        try iDestruct "H" as "[_ H]"; iFrame.
      - rel_vals.
      - rel_vals.
    }
    iIntros (c2 c2') "#Hcipher2"... rel_apply refines_pair...
    {
      rel_vals; last iAssumption.
      iExists 0; done.
    }
    rel_apply refines_pair...
    { rel_vals. }
    rewrite /b_recv_once...
    rel_vals.
  Qed.

  Definition s_to_b_adv : val :=
    λ: "b" "senc" "oracle" "ka" "kb", (* parameters of the protocol *)
      λ: "input",
        let: "sender" := #0 in
        let: "dest" := #1 in
        let: "nonce" := rand #N in
        if: "sender" = #0 `and` "dest" = #1 then
          ("senc" "kb" ("sender", "nonce"), ("sender", "oracle" ("dest", "nonce")))
        else #().

  Definition wmf_eav_adv : expr :=
    λ: "α" "b" "enc" "oracle",
      let: "r_adv" := rand("α") #N in
      ("r_adv",
        let: "ka" := keygen #() in
        let: "kb" := keygen #() in
        let: "msg2" :=
          s_to_b_delay "b"
            (symmetric_init.get_enc "enc" "oracle")
            "ka" "kb" #() in
        (Snd "msg2",
          (
            Fst "msg2",
            b_recv_once "b" "kb" (symmetric_init.get_dec "scheme") #()
          )
        )
      ).

    Definition CPA' : val :=
      λ:"b" "adv" "scheme" "Q",
        let: "rr_key_b" :=
          let: "enc_scheme" := get_enc_scheme "scheme" #() in
          let: "key" := get_keygen "scheme" #() in
          (* let: "enc_key" := enc "scheme" "key" in *)
          if: "b" then
            (* "enc_key" *)
            let: "enc" := get_enc "enc_scheme" in
            λ: "msg", "enc" "key" "msg"
          else
            get_rand_cipher "scheme" in
        let: "oracle" := q_calls (get_card_message "scheme") "Q" "rr_key_b" in
        let: "b'" := "adv" "enc" "oracle" in
        "b'".
  
  Lemma wmf_eav_adv__adv (adv : val) :
    (lrel_rand * ((lrel_id * lrel_output) * (lrel_output * ())) → lrel_bool)%lrel
      adv adv
    ⊢ REL (adv (init_scheme (wmf_eav_delay #true))) <<
      (let: "α" := alloc #N in
        CPA' #true (λ: "senc" "oracle",
          adv (wmf_eav_adv "α" #true "senc" "oracle"))
        (symmetric_init.sym_scheme) #2) : lrel_bool.
  Proof with (rel_pures_l; rel_pures_r).
    iIntros "#Hreladv".
    rewrite /wmf_eav_delay/wmf_eav_adv/CPA'/init_scheme...
    rel_alloctape_r α as "Hα".
    rel_apply refines_init_scheme_l.
    iIntros (lls) "HP"...
    rel_apply refines_init_scheme_r.
    iIntros (rls) "HP'"...
    rel_apply refines_couple_UT; first done; iFrame.
    iModIntro. iIntros (r_dummy Hrdummybound) "Hα"; simpl...
    rewrite /get_keygen...
    rel_apply refines_sym_keygen_couple.
    iIntros (ka) "#Hrelka"...
    rewrite /get_enc/q_calls/get_card_message...
    rel_alloc_r cnt2 as "Hcnt2"...
    rel_bind_l (adv _).
    rel_bind_r (adv _).
    rel_apply refines_bind.
    2:{
      iIntros (v v') "Hrel"...
      rel_vals.
    }
    rel_apply (refines_app with "[-]").
    { rel_vals. }

    




  End eavesdropping_attacker.

End protocol.