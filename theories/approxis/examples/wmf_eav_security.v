From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From clutch.prob_lang Require Import advantage typing.tychk.
From clutch.approxis Require Import map reltac2 approxis option.
From clutch.approxis.examples Require Import
  security_aux option symmetric_init wmf_protocol
  pubkey advantage_laws iterable_expression.
From clutch.approxis.examples Require
  kemdem_hybrid_cpa_generic.
From mathcomp Require Import ssrbool.
Set Default Proof Using "All".
Import map.

Section logrel.

  Context `{!approxisRGS Σ}.

  (* security parameter *)
  Variable η : nat.

  Let N := 2^η.

  Variable Key Output : nat.

  (* ASSUMPTION ON THE ENCRYPTION SCHEME *)

  Definition left_lrel (τ : lrel Σ) (v : val) : iProp Σ := ∃ v', (lrel_car τ) v v'.
  Definition right_lrel (τ : lrel Σ) (v : val) : iProp Σ := ∃ v', (lrel_car τ) v' v.

  Definition lrel_id : lrel Σ := lrel_int_bounded 0 1.

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
  
  #[local] Instance sym_params : SYM_init_params := @sym_params_wmf η Key Output.

  Context `{sym : !SYM_init}.

  Let init_scheme : expr → expr := init_scheme η Key Output.

  Let CPA' : val := CPA' η Key Output.

  Definition refines_init_scheme_l_prop := forall K e E A,
    (∀ lls,
      P0l lls -∗
      refines E
        (fill K (senc lls, sdec lls))
        e A)
    ⊢ refines E
        (fill K (get_enc_scheme sym_scheme #()))
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
        (fill K (get_enc_scheme sym_scheme #()))
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
        (fill K  (keygen #()))
        (fill K' (keygen #()))
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
  
  Definition sym_is_cipher_lr_r {lls rls : list loc} (msg : val) (c k : val) : iProp Σ :=
    ∀ K e E A,
      (Plr lls rls -∗
        refines E
        e (fill K (Val msg)) A)
    -∗ refines E
        e (fill K (sdec rls k c)) A.

  Definition refines_senc_lr_l_prop :=
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
      
  Definition refines_senc_lr_r_prop :=
    ∀ (lls rls : list loc) (msg msg' : val) (k k' : val) K K' E A,
    lrel_key k k' ∗ lrel_input msg msg' ∗ Plr lls rls ⊢
      ((∀ (c c' : val),
        lrel_output c c'
      -∗ @sym_is_cipher_lr_r lls rls msg c' k
      -∗ refines E
          (fill K (Val c))
          (fill K' (Val c'))
          A)
    -∗ refines E
        (fill K  (senc lls k  msg ))
        (fill K' (senc rls k' msg'))
        A).

  Hypothesis refines_couple_senc_lr_l : refines_senc_lr_l_prop.

  Hypothesis refines_couple_senc_lr_r : refines_senc_lr_r_prop.

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

    Section eavesdropping_attacker.
    
    Definition s_to_b_delay : val :=
      (* "b" : either we encrypt `r_adv` or a nonce
         "b'": either we encrypt or we use `rand_cipher *)
      λ: "b" "b'" "r_adv" "senc" "ka" "kb", (* parameters of the protocol *)
        λ: "input",
          let: "sender" := #0 in
          let: "dest" := #1 in
          let: "nonce" := if: "b" then rand #N else "r_adv" in
          let: "senc2" :=
            if: "b'" then "senc"
            else λ: <>, get_rand_cipher symmetric_init.sym_scheme in
          if: "sender" = #0 `and` "dest" = #1 then
            ("senc2" "kb" ("sender", "nonce"),
              ("sender", "senc2" "ka" ("dest", "nonce")))
          else #().
        
    Definition wmf_eav_delay : expr :=
      λ: "b" "b'" "scheme",
        let: "r_adv" := rand #N in
        ("r_adv",
          let: "ka" := keygen #() in
          let: "kb" := keygen #() in
          let: "msg2" :=
            s_to_b_delay "b" "b'" "r_adv"
              (symmetric_init.get_enc "scheme")
              "ka" "kb" #() in
          (Snd "msg2",
            (
              Fst "msg2",
              b_recv_once_eav "b" "kb" #()
            )
          )
        ).

    Let wmf_eav := @wmf_eav η Key Output sym.

    Lemma wmf_eav_true__wmf_eav_delay_true : 
      ⊢ REL init_scheme (wmf_eav #true) <<
        init_scheme (wmf_eav_delay #true #true) :
          (lrel_rand * ((lrel_id * lrel_output) * (lrel_output * ()))).
    Proof with (rel_pures_l; rel_pures_r).
      rewrite /init_scheme/wmf_protocol.init_scheme...
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
      rewrite /a_to_s_once_eav/s_to_b_delay/get_dec/get_enc...
      rel_apply refines_couple_UU; first done.
      iModIntro; iIntros (nonce Hnoncebound)...
      rel_apply (refines_couple_senc_lr_l with "[HP HP']").
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
      rewrite /s_to_b_once_eav...
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
      rewrite /b_recv_once_eav...
      rel_vals.
    Qed.

    Lemma wmf_eav_delay_true__wmf_eav_true : 
      ⊢ REL init_scheme (wmf_eav_delay #true #true) <<
          init_scheme (wmf_eav #true):
          (lrel_rand * ((lrel_id * lrel_output) * (lrel_output * ()))).
    Proof with (rel_pures_l; rel_pures_r).
      rewrite /init_scheme/wmf_protocol.init_scheme...
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
      rewrite /a_to_s_once_eav/s_to_b_delay/get_dec/get_enc...
      rel_apply refines_couple_UU; first done.
      iModIntro; iIntros (nonce Hnoncebound)...
      rel_apply (refines_couple_senc_lr_r with "[HP HP']").
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
      rewrite /s_to_b_once_eav...
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
      rewrite /b_recv_once_eav...
      rel_vals.
    Qed.

    Definition s_to_b_adv : val :=
      λ: "b" "r_adv" "senc" "oracle" "ka" "kb", (* parameters of the protocol *)
        λ: "input",
          let: "sender" := #0 in
          let: "dest" := #1 in
          let: "nonce" := if: "b" then rand #N else "r_adv" in
          if: "sender" = #0 `and` "dest" = #1 then
            let:m "cipher" :=  "oracle" ("dest", "nonce") in
            ("senc" "kb" ("sender", "nonce"), ("sender", "cipher"))
          else #().

    Definition wmf_eav_adv : expr :=
      λ: "α" "b" "enc" "oracle",
        let: "r_adv" := rand("α") #N in
        ("r_adv",
          let: "ka" := keygen #() in
          let: "kb" := keygen #() in
          let: "msg2" :=
            s_to_b_adv "b" "r_adv" "enc" "oracle"
              "ka" "kb" #() in
          (Snd "msg2",
            (
              Fst "msg2",
              b_recv_once_eav "b" "kb" #()
            )
          )
        ).
    
    Lemma wmf_eav_delay_true__adv_true (adv : val) :
      (lrel_rand * ((lrel_id * lrel_output) * (lrel_output * ())) → lrel_bool)%lrel
        adv adv
      ⊢ REL (adv (init_scheme (wmf_eav_delay #true #true))) <<
        (let: "α" := alloc #N in
          CPA' #true (λ: "senc" "oracle",
            adv (wmf_eav_adv "α" #true "senc" "oracle"))
          (symmetric_init.sym_scheme) #1) : lrel_bool.
    Proof with (rel_pures_l; rel_pures_r).
      iIntros "#Hreladv".
      rewrite /wmf_eav_delay/wmf_eav_adv/CPA'/wmf_protocol.CPA'
      /init_scheme/wmf_protocol.init_scheme...
      rel_alloctape_r α as "Hα".
      rel_apply refines_init_scheme_l.
      iIntros (lls) "HP"...
      rel_apply refines_init_scheme_r.
      iIntros (rls) "HP'"...
      rel_apply refines_couple_UT; first done; iFrame.
      iModIntro. iIntros (r_dummy Hrdummybound) "Hα"; simpl...
      rewrite /get_keygen/get_enc...
      rel_apply refines_sym_keygen_couple.
      iIntros (ka) "#Hrelka"...
      rewrite /get_card_message/sym_scheme...
      rewrite /get_enc/q_calls/is_plaintext_inst...
      rel_alloc_r cnt2 as "Hcnt2"...
      rel_bind_l (adv _).
      rel_bind_r (adv _).
      rel_apply (refines_bind with "[-]").
      2:{
        iIntros (v v') "Hrel"...
        rel_vals.
      }
      rel_apply refines_app.
      { rel_vals. }
      rel_apply (refines_randT_r with "Hα").
      iIntros "Hα _"...
      rel_apply refines_pair;
        first (rel_vals; iExists _; iPureIntro; repeat split; lia).
      rel_apply refines_keygen_r.
      iIntros (kadummy) "_"...
      rel_apply refines_sym_keygen_couple.
      iIntros (kb) "#Hrelkb"...
      rewrite /s_to_b_delay/s_to_b_adv...
      rel_apply refines_couple_UU; first done; iModIntro.
      iIntros (nonce Hnoncebound)...
      rel_apply (refines_na_alloc (Plr lls rls) (nroot.@"wmf_delay__adv")).
      iSplitL "HP HP'".
      { iApply (P0lr_Plr with "HP HP'"). }
      iIntros "#Inv"...
      rewrite /get_card_cipher...
      assert (Hbool1 : bool_decide (0 ≤ nonce)%Z = true); last
      assert (Hbool2 : bool_decide (nonce ≤ N)%Z = true);
        try (apply bool_decide_eq_true; lia);
      rewrite Hbool1 Hbool2; clear Hbool1 Hbool2.
      rel_load_r... rel_load_r; rel_store_r...
      rel_bind_l (senc _ _ _).
      rel_bind_r (senc _ _ _).
      rel_apply refines_bind.
      - repeat rel_apply refines_app;
          first (rel_apply senc_sem_typed; last iAssumption).
        + exists True%I. apply bi.equiv_entails. split; iIntros "H";
          try iDestruct "H" as "[_ H]"; iFrame.
        + rel_vals.
        + rel_vals.
          apply Z2Nat.inj_le; try lia. rewrite /N.
          rewrite Nat2Z.id. replace (Z.to_nat 1) with 1 by lia.
          apply fin.pow_ge_1. lia.
      - iIntros (c1 c1') "Hrelcipher"...
        rel_bind_l (senc _ _ _).
        rel_bind_r (senc _ _ _).
        { rel_apply refines_bind.
      - repeat rel_apply refines_app;
          first (rel_apply senc_sem_typed; last iAssumption).
        + exists True%I. apply bi.equiv_entails. split; iIntros "H";
          try iDestruct "H" as "[_ H]"; iFrame.
        + rel_vals.
        + rel_vals.
      - iIntros (c2 c2') "Hrelcipher2"...
        rewrite /b_recv_once_eav...
        rel_vals; try iAssumption.
        + iExists 0. done.
        + done. }
    Qed.

    Lemma wmf_eav_adv_true__wmf_eav_delay_true (adv : val) :
      (lrel_rand * ((lrel_id * lrel_output) * (lrel_output * ())) → lrel_bool)%lrel
        adv adv
      ⊢ REL (let: "α" := alloc #N in
            CPA' #true (λ: "senc" "oracle",
              adv (wmf_eav_adv "α" #true "senc" "oracle"))
            (symmetric_init.sym_scheme) #1) <<
          (adv (init_scheme (wmf_eav_delay #true #true))) : lrel_bool.
    Proof with (rel_pures_l; rel_pures_r).
      iIntros "#Hreladv".
      rewrite /wmf_eav_delay/wmf_eav_adv/CPA'/wmf_protocol.CPA'
      /init_scheme/wmf_protocol.init_scheme...
      rel_alloctape_l α as "Hα"...
      rel_apply refines_init_scheme_l.
      iIntros (lls) "HP"...
      rel_apply refines_init_scheme_r.
      iIntros (rls) "HP'"...
      rel_apply refines_couple_TU; first done; iFrame.
      iIntros (r_dummy Hrdummybound) "Hα"; simpl...
      rewrite /get_keygen/get_enc...
      rel_apply refines_sym_keygen_couple.
      iIntros (ka) "#Hrelka"...
      rewrite /get_card_message/sym_scheme...
      rewrite /get_enc/q_calls/is_plaintext_inst...
      rel_alloc_l cnt2 as "Hcnt2"...
      rel_bind_l (adv _).
      rel_bind_r (adv _).
      rel_apply (refines_bind with "[-]").
      2:{
        iIntros (v v') "Hrel"...
        rel_vals.
      }
      rel_apply refines_app.
      { rel_vals. }
      rel_apply (refines_randT_l). iFrame. iModIntro.
      iIntros "Hα _"...
      rel_apply refines_pair;
        first (rel_vals; iExists _; iPureIntro; repeat split; lia).
      rel_apply refines_keygen_l.
      iIntros (kadummy) "_"...
      rel_apply refines_sym_keygen_couple.
      iIntros (kb) "#Hrelkb"...
      rewrite /s_to_b_delay/s_to_b_adv...
      rel_apply refines_couple_UU; first done; iModIntro.
      iIntros (nonce Hnoncebound)...
      rel_apply (refines_na_alloc (Plr lls rls) (nroot.@"wmf_delay__adv")).
      iSplitL "HP HP'".
      { iApply (P0lr_Plr with "HP HP'"). }
      iIntros "#Inv"...
      rewrite /get_card_cipher...
      assert (Hbool1 : bool_decide (0 ≤ nonce)%Z = true); last
      assert (Hbool2 : bool_decide (nonce ≤ N)%Z = true);
        try (apply bool_decide_eq_true; lia);
      rewrite Hbool1 Hbool2; clear Hbool1 Hbool2.
      rel_load_l... rel_load_l; rel_store_l...
      rel_bind_l (senc _ _ _).
      rel_bind_r (senc _ _ _).
      rel_apply refines_bind.
      - repeat rel_apply refines_app;
          first (rel_apply senc_sem_typed; last iAssumption).
        + exists True%I. apply bi.equiv_entails. split; iIntros "H";
          try iDestruct "H" as "[_ H]"; iFrame.
        + rel_vals.
        + rel_vals.
          apply Z2Nat.inj_le; try lia. rewrite /N.
          rewrite Nat2Z.id. replace (Z.to_nat 1) with 1 by lia.
          apply fin.pow_ge_1. lia.
      - iIntros (c1 c1') "Hrelcipher"...
        rel_bind_l (senc _ _ _).
        rel_bind_r (senc _ _ _).
        { rel_apply refines_bind.
      - repeat rel_apply refines_app;
          first (rel_apply senc_sem_typed; last iAssumption).
        + exists True%I. apply bi.equiv_entails. split; iIntros "H";
          try iDestruct "H" as "[_ H]"; iFrame.
        + rel_vals.
        + rel_vals.
      - iIntros (c2 c2') "Hrelcipher2"...
        rewrite /b_recv_once_eav...
        rel_vals; try iAssumption.
        + iExists 0. done.
        + done. }
    Qed.

    Definition s_to_b_delay_adv_kb : val :=
      λ: "b" "r_adv" "senc" "ka" "kb", (* parameters of the protocol *)
        λ: "input",
          let: "sender" := #0 in
          let: "dest" := #1 in
          let: "nonce" := if: "b" then rand #N else "r_adv" in
          let: "cipher1" := (λ: <>, get_rand_cipher symmetric_init.sym_scheme) "ka" ("dest", "nonce") in
          let:m "cipher2" := "senc" ("sender", "nonce") in
          if: "sender" = #0 `and` "dest" = #1 then
            ("cipher2",
              ("sender", "cipher1"))
          else #().
    
    Definition wmf_eav_adv_kb : val :=
      λ: "α" "b" "enc" "oracle",
        let: "r_adv" := rand("α") #N in
        ("r_adv",
          let: "ka" := keygen #() in
          let: "kb" := keygen #() in
          let: "msg2" :=
            s_to_b_delay_adv_kb "b" "r_adv" "oracle"
              "ka" "kb" #() in
          (Snd "msg2",
            (
              Fst "msg2",
              b_recv_once_eav "b" "kb" #()
            )
          )
        ).

    Hypothesis rand_cipher_sem_typed :
      ⊢ REL rand_cipher << rand_cipher :
        kemdem_hybrid_cpa_generic.lrel_trivial → lrel_output.

    Lemma wmf_eav_adv__adv_kb_false (adv : val) :
      (lrel_rand * ((lrel_id * lrel_output) * (lrel_output * ())) → lrel_bool)%lrel
        adv adv
      ⊢ REL
          (let: "α" := alloc #N in
            CPA' #false (λ: "senc" "oracle",
              adv (wmf_eav_adv "α" #true "senc" "oracle"))
            (symmetric_init.sym_scheme) #1)
          <<
          (let: "α" := alloc #N in
            CPA' #true (λ: "senc" "oracle",
              adv (wmf_eav_adv_kb "α" #true "senc" "oracle"))
            (symmetric_init.sym_scheme) #1) : lrel_bool.
    Proof with rel_pures_l; rel_pures_r.
      iIntros "#Hreladv".
      rel_alloctape_l α as "Hα";
      rel_alloctape_r α' as "Hα'"...
      rewrite /CPA'/wmf_protocol.CPA'...
      rel_apply refines_init_scheme_l.
      iIntros (lls) "HP".
      rel_apply refines_init_scheme_r.
      iIntros (rls) "HP'"...
      rewrite /get_enc/get_keygen/get_rand_cipher...
      rel_apply refines_keygen_l.
      iIntros (ka_dummy) "#Hrelka_dummy"...
      rewrite /q_calls/is_plaintext_inst...
      rel_alloc_l cnt as "Hcnt"...
      rel_apply refines_couple_TT; iFrame.
      iIntros (r_adv) "[Hα [Hα' %Hradvbound]]".
      rel_apply refines_randT_l; iFrame.
      iModIntro. iIntros "Hα _"...
      rel_apply refines_keygen_l.
      iIntros (ka_dummy') "#Hrelka_dummy'"...
      rel_apply refines_sym_keygen_couple.
      iIntros (kb) "#Hrelkb"...
      rel_alloc_r cnt' as "Hcnt'"...
      rel_bind_l (adv _).
      rel_bind_r (adv _).
      rel_apply (refines_bind with "[-]").
      2:{
        iIntros (v v') "Hrel"...
        rel_vals.
      }
      rel_apply refines_app; first (rel_vals; iAssumption).
      rewrite /wmf_eav_adv_kb...
      rel_apply (refines_randT_r with "Hα'").
      iIntros "Hα' _"...
      rel_apply refines_pair;
        first (rel_vals; iExists r_adv; iPureIntro; repeat split; lia).
      rel_apply refines_keygen_r.
      iIntros (kb_dummy) "#Hrelkb_dummy"...
      rel_apply refines_keygen_r.
      iIntros (kb_dummy') "#Hrelkb_dummy'"...
      rewrite /s_to_b_adv/s_to_b_delay_adv_kb...
      rel_apply refines_couple_UU; first done.
      iModIntro; iIntros (nonce Hnoncebound)...
      rewrite /get_card_cipher/get_rand_cipher...
      assert (Hbool1 : bool_decide (0 ≤ nonce)%Z = true); last
      assert (Hbool2 : bool_decide (nonce ≤ N)%Z = true);
        try (apply bool_decide_eq_true; lia);
      rewrite Hbool1 Hbool2.
      rel_load_l; rel_load_l; rel_store_l...
      rel_apply (refines_na_alloc (Plr lls rls) (nroot.@"wmf_delay__adv")).
      iSplitL "HP HP'".
      { iApply (P0lr_Plr with "HP HP'"). }
      iIntros "#Inv"...
      rel_bind_l (rand_cipher _).
      rel_bind_r (rand_cipher _).
      rel_apply refines_bind.
      - rel_apply refines_app.
        + rel_apply rand_cipher_sem_typed.
        + rel_vals.
      - iIntros (c1 c1') "Hrelcipher"...
        rewrite Hbool1 Hbool2; clear Hbool1 Hbool2...
        rel_load_r; rel_load_r; rel_store_r...
        rel_bind_l (senc _ _ _).
        rel_bind_r (senc _ _ _).
        { rel_apply refines_bind.
      - repeat rel_apply refines_app;
          first (rel_apply senc_sem_typed; last iAssumption).
        + exists True%I. apply bi.equiv_entails. split; iIntros "H";
          try iDestruct "H" as "[_ H]"; iFrame.
        + rel_vals.
        + rel_vals.
      - iIntros (c2 c2') "Hrelcipher2"...
        rewrite /b_recv_once_eav...
        rel_vals; try iAssumption.
        + iExists 0. done.
        + done. }
    Qed.
      
    Lemma wmf_eav_adv_kb__adv_false (adv : val) :
      (lrel_rand * ((lrel_id * lrel_output) * (lrel_output * ())) → lrel_bool)%lrel
        adv adv
      ⊢ REL
          (let: "α" := alloc #N in
            CPA' #true (λ: "senc" "oracle",
              adv (wmf_eav_adv_kb "α" #true "senc" "oracle"))
            (symmetric_init.sym_scheme) #1)
          <<
          (let: "α" := alloc #N in
            CPA' #false (λ: "senc" "oracle",
              adv (wmf_eav_adv "α" #true "senc" "oracle"))
            (symmetric_init.sym_scheme) #1) : lrel_bool.
    Proof with rel_pures_l; rel_pures_r.
      iIntros "#Hreladv".
      rel_alloctape_l α as "Hα";
      rel_alloctape_r α' as "Hα'"...
      rewrite /CPA'/wmf_protocol.CPA'...
      rel_apply refines_init_scheme_l.
      iIntros (lls) "HP".
      rel_apply refines_init_scheme_r.
      iIntros (rls) "HP'"...
      rewrite /get_enc/get_keygen/get_rand_cipher...
      rel_apply refines_keygen_r.
      iIntros (ka_dummy) "#Hrelka_dummy"...
      rewrite /q_calls/is_plaintext_inst...
      rel_alloc_r cnt' as "Hcnt'"...
      rel_apply refines_couple_TT; iFrame.
      iIntros (r_adv) "[Hα [Hα' %Hradvbound]]"...
      rel_apply (refines_randT_r with "Hα'"); iFrame.
      iIntros "Hα' _"...
      rel_apply refines_keygen_r.
      iIntros (ka_dummy') "#Hrelka_dummy'"...
      rel_apply refines_sym_keygen_couple.
      iIntros (kb) "#Hrelkb"...
      rel_alloc_l cnt as "Hcnt"...
      rel_bind_l (adv _).
      rel_bind_r (adv _).
      rel_apply (refines_bind with "[-]").
      2:{
        iIntros (v v') "Hrel"...
        rel_vals.
      }
      rel_apply refines_app; first (rel_vals; iAssumption).
      rewrite /wmf_eav_adv_kb...
      rel_apply refines_randT_l; iFrame.
      iModIntro; iIntros "Hα _"...
      rel_apply refines_pair;
        first (rel_vals; iExists r_adv; iPureIntro; repeat split; lia).
      rel_apply refines_keygen_l.
      iIntros (kb_dummy) "#Hrelkb_dummy"...
      rel_apply refines_keygen_l.
      iIntros (kb_dummy') "#Hrelkb_dummy'"...
      rewrite /s_to_b_adv/s_to_b_delay_adv_kb...
      rel_apply refines_couple_UU; first done.
      iModIntro; iIntros (nonce Hnoncebound)...
      rewrite /get_card_cipher/get_rand_cipher...
      assert (Hbool1 : bool_decide (0 ≤ nonce)%Z = true); last
      assert (Hbool2 : bool_decide (nonce ≤ N)%Z = true);
        try (apply bool_decide_eq_true; lia);
      rewrite Hbool1 Hbool2.
      rel_load_r; rel_load_r; rel_store_r...
      rel_apply (refines_na_alloc (Plr lls rls) (nroot.@"wmf_delay__adv")).
      iSplitL "HP HP'".
      { iApply (P0lr_Plr with "HP HP'"). }
      iIntros "#Inv"...
      rel_bind_l (rand_cipher _).
      rel_bind_r (rand_cipher _).
      rel_apply refines_bind.
      - rel_apply refines_app.
        + rel_apply rand_cipher_sem_typed.
        + rel_vals.
      - iIntros (c1 c1') "Hrelcipher"...
        rewrite Hbool1 Hbool2; clear Hbool1 Hbool2...
        rel_load_l; rel_load_l; rel_store_l...
        rel_bind_l (senc _ _ _).
        rel_bind_r (senc _ _ _).
        { rel_apply refines_bind.
      - repeat rel_apply refines_app;
          first (rel_apply senc_sem_typed; last iAssumption).
        + exists True%I. apply bi.equiv_entails. split; iIntros "H";
          try iDestruct "H" as "[_ H]"; iFrame.
        + rel_vals.
        + rel_vals.
      - iIntros (c2 c2') "Hrelcipher2"...
        rewrite /b_recv_once_eav...
        rel_vals; try iAssumption.
        + iExists 0. done.
        + done. }
    Qed.

    Lemma wmf_eav_adv_false__wmf_eav_false (adv : val) :
      (lrel_rand * ((lrel_id * lrel_output) * (lrel_output * ())) → lrel_bool)%lrel
        adv adv
      ⊢ REL
          (let: "α" := alloc #N in
            CPA' #false (λ: "senc" "oracle",
              adv (wmf_eav_adv_kb "α" #true "senc" "oracle"))
            (symmetric_init.sym_scheme) #1)
          <<
          (adv (init_scheme (wmf_eav_delay #true #false))) : lrel_bool.
    Proof with rel_pures_l; rel_pures_r.
      iIntros "#Hreladv".
      rel_alloctape_l α as "Hα"...
      rewrite /CPA'/wmf_protocol.CPA'/init_scheme/wmf_protocol.init_scheme...
      rel_apply refines_init_scheme_l.
      iIntros (lls) "HP".
      rel_apply refines_init_scheme_r.
      iIntros (rls) "HP'"...
      rewrite /get_enc/get_keygen/get_rand_cipher...
      rel_apply refines_keygen_l.
      iIntros (ka_dummy) "#Hrelka_dummy"...
      rewrite /q_calls/is_plaintext_inst...
      rel_alloc_l cnt as "Hcnt"...
      rel_apply refines_couple_TU; first done; iFrame.
      iIntros (r_adv Hradv_bound) "Hα".
      rewrite /wmf_eav_adv_kb...
      rel_apply refines_randT_l; iFrame; iModIntro; iIntros "Hα _"...
      rel_bind_l (adv _).
      rel_bind_r (adv _).
      rel_apply (refines_bind with "[-]").
      2:{
        iIntros (v v') "Hrel"...
        rel_vals.
      }
      rel_apply refines_app; first (rel_vals; iAssumption).
      rel_apply refines_pair;
        first (rel_vals; iExists r_adv; iPureIntro; repeat split; lia).
      rel_apply refines_sym_keygen_couple.
      iIntros (ka_dummy') "#Hrelka_dummy'"...
      rel_apply refines_sym_keygen_couple.
      iIntros (kb_dummy) "#Hrelkb_dummy"...
      rewrite /s_to_b_delay_adv_kb/s_to_b_delay...
      rel_apply refines_couple_UU; first done.
      iModIntro; iIntros (nonce Hnoncebound)...
      rewrite /get_card_cipher/get_rand_cipher/sym_scheme...
      rel_bind_l (rand_cipher _).
      rel_bind_r (rand_cipher _).
      rel_apply refines_bind.
      - rel_apply refines_app.
        + rel_apply rand_cipher_sem_typed.
        + rel_vals.
      - iIntros (c1 c1') "Hrelcipher"...
        assert (Hbool1 : bool_decide (0 ≤ nonce)%Z = true); last
        assert (Hbool2 : bool_decide (nonce ≤ N)%Z = true);
          try (apply bool_decide_eq_true; lia);
        rewrite Hbool1 Hbool2. clear Hbool1 Hbool2.
        rel_load_l; rel_load_l; rel_store_l...
        rel_bind_l (rand_cipher _).
        rel_bind_r (rand_cipher _).
        { rel_apply refines_bind.
      - repeat rel_apply refines_app;
          first (rel_apply rand_cipher_sem_typed).
        rel_vals.
      - iIntros (c2 c2') "Hrelcipher2"...
        rewrite /b_recv_once_eav...
        rel_vals; try iAssumption.
        + iExists 0. done.
        + done. }
    Qed.

    Lemma wmf_eav_false__wmf_eav_adv_false (adv : val) :
      (lrel_rand * ((lrel_id * lrel_output) * (lrel_output * ())) → lrel_bool)%lrel
        adv adv
      ⊢ REL
          (adv (init_scheme (wmf_eav_delay #true #false)))
          <<
          (let: "α" := alloc #N in
            CPA' #false (λ: "senc" "oracle",
              adv (wmf_eav_adv_kb "α" #true "senc" "oracle"))
            (symmetric_init.sym_scheme) #1) : lrel_bool.
    Proof with rel_pures_l; rel_pures_r.
      iIntros "#Hreladv".
      rel_alloctape_r α as "Hα"...
      rewrite /CPA'/wmf_protocol.CPA'/init_scheme/wmf_protocol.init_scheme...
      rel_apply refines_init_scheme_l.
      iIntros (lls) "HP".
      rel_apply refines_init_scheme_r.
      iIntros (rls) "HP'"...
      rewrite /get_enc/get_keygen/get_rand_cipher...
      rel_apply refines_keygen_r.
      iIntros (ka_dummy) "#Hrelka_dummy"...
      rewrite /q_calls/is_plaintext_inst...
      rel_alloc_r cnt' as "Hcnt'"...
      rel_apply refines_couple_UT; first done; iFrame.
      iModIntro; iIntros (r_adv Hradv_bound) "Hα".
      rewrite /wmf_eav_adv_kb...
      rel_apply (refines_randT_r with "Hα"); iIntros "Hα _"...
      rel_bind_l (adv _).
      rel_bind_r (adv _).
      rel_apply (refines_bind with "[-]").
      2:{
        iIntros (v v') "Hrel"...
        rel_vals.
      }
      rel_apply refines_app; first (rel_vals; iAssumption).
      rel_apply refines_pair;
        first (rel_vals; iExists r_adv; iPureIntro; repeat split; lia).
      rel_apply refines_sym_keygen_couple.
      iIntros (ka_dummy') "#Hrelka_dummy'"...
      rel_apply refines_sym_keygen_couple.
      iIntros (kb_dummy) "#Hrelkb_dummy"...
      rewrite /s_to_b_delay_adv_kb/s_to_b_delay...
      rel_apply refines_couple_UU; first done.
      iModIntro; iIntros (nonce Hnoncebound)...
      rewrite /get_card_cipher/get_rand_cipher/sym_scheme...
      rel_bind_l (rand_cipher _).
      rel_bind_r (rand_cipher _).
      rel_apply refines_bind.
      - rel_apply refines_app.
        + rel_apply rand_cipher_sem_typed.
        + rel_vals.
      - iIntros (c1 c1') "Hrelcipher"...
        assert (Hbool1 : bool_decide (0 ≤ nonce)%Z = true); last
        assert (Hbool2 : bool_decide (nonce ≤ N)%Z = true);
          try (apply bool_decide_eq_true; lia);
        rewrite Hbool1 Hbool2. clear Hbool1 Hbool2.
        rel_load_r; rel_load_r; rel_store_r...
        rel_bind_l (rand_cipher _).
        rel_bind_r (rand_cipher _).
        { rel_apply refines_bind.
      - repeat rel_apply refines_app;
          first (rel_apply rand_cipher_sem_typed).
        rel_vals.
      - iIntros (c2 c2') "Hrelcipher2"...
        rewrite /b_recv_once_eav...
        rel_vals; try iAssumption.
        + iExists 0. done.
        + done. }
    Qed.

    Lemma wmf_delay_true_false__wmf_delay_false_false (adv : val) :
      ⊢ REL
          init_scheme (wmf_eav_delay #true #false) <<
          init_scheme (wmf_eav_delay #false #false) :
          (lrel_rand * ((lrel_id * lrel_output) * (lrel_output * ()))).
    Proof with rel_pures_l; rel_pures_r.
      rewrite /init_scheme/wmf_protocol.init_scheme.
      rel_apply refines_init_scheme_l.
      iIntros (lls) "HP".
      rel_apply refines_init_scheme_r.
      iIntros (rls) "HP'"...
      rel_apply refines_couple_UU; first done.
      iModIntro; iIntros (r_adv Hradvbound)...
      rel_apply refines_sym_keygen_couple.
      iIntros (ka) "#Hrelka"...
      rel_apply refines_sym_keygen_couple.
      iIntros (kb) "#Hrelkb".
      rewrite /get_enc/s_to_b_delay...
      rel_apply refines_randU_l.
      iIntros (nonce_dummy Hnoncebound)...
      rewrite /get_rand_cipher/sym_scheme...
      rel_bind_l (rand_cipher _).
      rel_bind_r (rand_cipher _).
      rel_apply refines_bind.
      {
        rel_apply refines_app; first rel_apply rand_cipher_sem_typed.
        rel_vals.
      }
      iIntros (c1 c1') "#Hrelc1"...
      rel_bind_l (rand_cipher _).
      rel_bind_r (rand_cipher _).
      rel_apply refines_bind.
      {
        rel_apply refines_app; first rel_apply rand_cipher_sem_typed.
        rel_vals.
      }
      iIntros (c2 c2') "#Hrelc2"...
      rewrite /b_recv_once_eav...
      rel_vals; try iExists _; try iPureIntro; repeat split; try lia; try done.
    Qed.

    Lemma wmf_delay_false_false__wmf_delay_true_false (adv : val) :
      ⊢ REL
          init_scheme (wmf_eav_delay #false #false) <<
          init_scheme (wmf_eav_delay #true #false) :
          (lrel_rand * ((lrel_id * lrel_output) * (lrel_output * ()))).
    Proof with rel_pures_l; rel_pures_r.
      rewrite /init_scheme/wmf_protocol.init_scheme.
      rel_apply refines_init_scheme_l.
      iIntros (lls) "HP".
      rel_apply refines_init_scheme_r.
      iIntros (rls) "HP'"...
      rel_apply refines_couple_UU; first done.
      iModIntro; iIntros (r_adv Hradvbound)...
      rel_apply refines_sym_keygen_couple.
      iIntros (ka) "#Hrelka"...
      rel_apply refines_sym_keygen_couple.
      iIntros (kb) "#Hrelkb".
      rewrite /get_enc/s_to_b_delay...
      rel_apply refines_randU_r.
      iIntros (nonce_dummy Hnoncebound)...
      rewrite /get_rand_cipher/sym_scheme...
      rel_bind_l (rand_cipher _).
      rel_bind_r (rand_cipher _).
      rel_apply refines_bind.
      {
        rel_apply refines_app; first rel_apply rand_cipher_sem_typed.
        rel_vals.
      }
      iIntros (c1 c1') "#Hrelc1"...
      rel_bind_l (rand_cipher _).
      rel_bind_r (rand_cipher _).
      rel_apply refines_bind.
      {
        rel_apply refines_app; first rel_apply rand_cipher_sem_typed.
        rel_vals.
      }
      iIntros (c2 c2') "#Hrelc2"...
      rewrite /b_recv_once_eav...
      rel_vals; try iExists _; try iPureIntro; repeat split; try lia; try done.
    Qed.
    
    Lemma wmf_adv_false_false__wmf_delay_false_false (adv : val) :
      (lrel_rand * ((lrel_id * lrel_output) * (lrel_output * ())) → lrel_bool)%lrel
        adv adv
      ⊢ REL
          (let: "α" := alloc #N in
            CPA' #false (λ: "senc" "oracle",
              adv (wmf_eav_adv_kb "α" #false "senc" "oracle"))
            (symmetric_init.sym_scheme) #1) <<
          adv (init_scheme (wmf_eav_delay #false #false)): lrel_bool.
    Proof with rel_pures_l; rel_pures_r.
      iIntros "#Hreladv".
      rel_alloctape_l α as "Hα"...
      rewrite /CPA'/wmf_protocol.CPA'
        /init_scheme/wmf_protocol.init_scheme...
      rel_apply refines_init_scheme_l.
      iIntros (lls) "HP".
      rel_apply refines_init_scheme_r.
      iIntros (rls) "HP'"...
      rel_apply refines_couple_TU; first done; iFrame.
      iIntros (r_adv Hradvbound) "Hα"; simpl...
      rewrite /get_enc/get_keygen/get_rand_cipher...
      rel_apply refines_sym_keygen_couple.
      iIntros (ka) "#Hrelka"...
      rewrite /q_calls/is_plaintext_inst...
      rel_alloc_l cnt as "Hcnt"...
      rel_bind_l (adv _).
      rel_bind_r (adv _).
      rel_apply (refines_bind with "[-]").
      2:{
        iIntros (v v') "Hrel"...
        rel_vals.
      }
      rel_apply refines_app.
      { rel_vals. }
      rewrite /wmf_eav_adv_kb...
      rel_apply refines_randT_l. iFrame.
      iModIntro; iIntros "Hα _"... 
      rel_apply refines_keygen_l.
      iIntros (ka_dummy) "#Hrelkadummy"...
      rel_apply refines_sym_keygen_couple.
      iIntros (kb) "#Hrelkb"...
      rewrite /s_to_b_delay/s_to_b_delay_adv_kb/get_rand_cipher...
      rel_bind_l (rand_cipher _).
      rel_bind_r (rand_cipher _).
      rel_apply refines_bind.
      {
        rel_apply refines_app; first rel_apply rand_cipher_sem_typed.
        rel_vals.
      }
      iIntros (c1 c1') "#Hrelc1"...
      rewrite /get_card_cipher/symmetric_init.sym_params...
      assert (Hbool1 : bool_decide (0 ≤ r_adv)%Z = true); last
      assert (Hbool2 : bool_decide (r_adv ≤ N)%Z = true);
        try (apply bool_decide_eq_true; lia);
      rewrite Hbool1 Hbool2; clear Hbool1 Hbool2.
      rel_load_l... rel_load_l; rel_store_l...
      rel_bind_l (rand_cipher _).
      rel_bind_r (rand_cipher _).
      rel_apply refines_bind.
      {
        rel_apply refines_app; first rel_apply rand_cipher_sem_typed.
        rel_vals.
      }
      iIntros (c2 c2') "#Hrelc2"...
      rewrite /b_recv_once_eav...
      rel_vals; try iExists _; try iPureIntro; repeat split; try lia; try done.
    Qed.

    Lemma wmf_eav_adv_kb_true_false__wmf_eav_adv_false_false (adv : val) :
      (lrel_rand * ((lrel_id * lrel_output) * (lrel_output * ())) → lrel_bool)%lrel
        adv adv
      ⊢ REL
          (let: "α" := alloc #N in
            CPA' #true (λ: "senc" "oracle",
              adv (wmf_eav_adv_kb "α" #false "senc" "oracle"))
            (symmetric_init.sym_scheme) #1) <<
          (let: "α" := alloc #N in
            CPA' #false (λ: "senc" "oracle",
              adv (wmf_eav_adv "α" #false "senc" "oracle"))
            (symmetric_init.sym_scheme) #1) : lrel_bool.
    Proof with rel_pures_l; rel_pures_r.
      iIntros "#Hreladv".
      rel_alloctape_l α as "Hα".
      rel_alloctape_r α' as "Hα'"...
      rel_apply refines_couple_TT; iFrame.
      iIntros (r_adv) "[Hα [Hα' %Hradvbound]]".
      rewrite /CPA'/wmf_protocol.CPA'...
      rel_apply refines_init_scheme_l.
      iIntros (lls) "HP".
      rel_apply refines_init_scheme_r;
      iIntros (rls) "HP'".
      rewrite /get_enc/get_keygen...
      rel_apply refines_keygen_r;
      iIntros (kb') "#Hrelkb'"...
      rewrite /get_rand_cipher/q_calls/is_plaintext_inst...
      rel_alloc_r cnt' as "Hcnt'"...
      rel_apply (refines_randT_r with "Hα'")...
      iIntros "Hα' _"...
      rel_apply refines_keygen_r.
      iIntros (ka2) "#Hrelka2"...
      rel_apply refines_sym_keygen_couple;
      iIntros (ka) "#Hrelka".
      rel_alloc_l cnt as "Hcnt"...
      rel_bind_l (adv _).
      rel_bind_r (adv _).
      rel_apply (refines_bind with "[-]").
      2:{
        iIntros (v v') "Hrel"...
        rel_vals.
      }
      rel_apply refines_app.
      { rel_vals. }
      rewrite /wmf_eav_adv_kb...
      rel_apply refines_randT_l; iFrame.
      iModIntro; iIntros "Hα _"...
      rel_apply refines_pair; first (rel_vals; iExists _; iPureIntro; repeat split; lia).
      rel_apply refines_keygen_l.
      iIntros (ka_dummy) "#Hrelkadummy"...
      rel_apply refines_keygen_l.
      iIntros (kb_dummy) "#Hrelkbdummy"...
      rewrite /s_to_b_adv/s_to_b_delay_adv_kb/get_rand_cipher/get_card_cipher...
      assert (Hbool1 : bool_decide (0 ≤ r_adv)%Z = true); last
      assert (Hbool2 : bool_decide (r_adv ≤ N)%Z = true);
        try (apply bool_decide_eq_true; lia);
      rewrite Hbool1 Hbool2.
      rel_load_r... rel_load_r; rel_store_r...
      rel_bind_l (rand_cipher _).
      rel_bind_r (rand_cipher _).
      rel_apply refines_bind.
      {
        rel_apply refines_app; first rel_apply rand_cipher_sem_typed.
        rel_vals.
      }
      iIntros (c1 c1') "#Hrelc1"...
      rewrite Hbool1 Hbool2; clear Hbool1 Hbool2.
      rel_load_l... rel_load_l; rel_store_l...
      rel_bind_l (senc _ _ _).
      rel_bind_r (senc _ _ _).
      rel_apply (refines_bind with "[HP HP']").
      {
        rel_apply (refines_na_alloc (Plr lls rls) (nroot.@"wmf__delay")).
        iSplitL "HP HP'"; first iApply (P0lr_Plr with "HP HP'").
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
      rewrite /b_recv_once_eav...
      rel_vals.
    Qed.

    Lemma wmf_eav_adv_false_false__wmf_eav_adv_kb_true_false (adv : val) :
      (lrel_rand * ((lrel_id * lrel_output) * (lrel_output * ())) → lrel_bool)%lrel
        adv adv
      ⊢ REL
          (let: "α" := alloc #N in
            CPA' #true (λ: "senc" "oracle",
              adv (wmf_eav_adv_kb "α" #false "senc" "oracle"))
            (symmetric_init.sym_scheme) #1) <<
          (let: "α" := alloc #N in
            CPA' #false (λ: "senc" "oracle",
              adv (wmf_eav_adv "α" #false "senc" "oracle"))
            (symmetric_init.sym_scheme) #1) : lrel_bool.
    Proof with rel_pures_l; rel_pures_r.
      iIntros "#Hreladv".
      rel_alloctape_l α as "Hα".
      rel_alloctape_r α' as "Hα'"...
      rel_apply refines_couple_TT; iFrame.
      iIntros (r_adv) "[Hα [Hα' %Hradvbound]]".
      rewrite /CPA'/wmf_protocol.CPA'...
      rel_apply refines_init_scheme_l.
      iIntros (lls) "HP".
      rel_apply refines_init_scheme_r;
      iIntros (rls) "HP'".
      rewrite /get_enc/get_keygen...
      rel_apply refines_keygen_r;
      iIntros (kb') "#Hrelkb'"...
      rewrite /get_rand_cipher/q_calls/is_plaintext_inst...
      rel_alloc_r cnt' as "Hcnt'"...
      rel_apply (refines_randT_r with "Hα'")...
      iIntros "Hα' _"...
      rel_apply refines_keygen_r.
      iIntros (ka2) "#Hrelka2"...
      rel_apply refines_sym_keygen_couple;
      iIntros (ka) "#Hrelka".
      rel_alloc_l cnt as "Hcnt"...
      rel_bind_l (adv _).
      rel_bind_r (adv _).
      rel_apply (refines_bind with "[-]").
      2:{
        iIntros (v v') "Hrel"...
        rel_vals.
      }
      rel_apply refines_app.
      { rel_vals. }
      rewrite /wmf_eav_adv_kb...
      rel_apply refines_randT_l; iFrame.
      iModIntro; iIntros "Hα _"...
      rel_apply refines_pair; first (rel_vals; iExists _; iPureIntro; repeat split; lia).
      rel_apply refines_keygen_l.
      iIntros (ka_dummy) "#Hrelkadummy"...
      rel_apply refines_keygen_l.
      iIntros (kb_dummy) "#Hrelkbdummy"...
      rewrite /s_to_b_adv/s_to_b_delay_adv_kb/get_rand_cipher/get_card_cipher...
      assert (Hbool1 : bool_decide (0 ≤ r_adv)%Z = true); last
      assert (Hbool2 : bool_decide (r_adv ≤ N)%Z = true);
        try (apply bool_decide_eq_true; lia);
      rewrite Hbool1 Hbool2.
      rel_load_r... rel_load_r; rel_store_r...
      rel_bind_l (rand_cipher _).
      rel_bind_r (rand_cipher _).
      rel_apply refines_bind.
      {
        rel_apply refines_app; first rel_apply rand_cipher_sem_typed.
        rel_vals.
      }
      iIntros (c1 c1') "#Hrelc1"...
      rewrite Hbool1 Hbool2; clear Hbool1 Hbool2.
      rel_load_l... rel_load_l; rel_store_l...
      rel_bind_l (senc _ _ _).
      rel_bind_r (senc _ _ _).
      rel_apply (refines_bind with "[HP HP']").
      {
        rel_apply (refines_na_alloc (Plr lls rls) (nroot.@"wmf__delay")).
        iSplitL "HP HP'"; first iApply (P0lr_Plr with "HP HP'").
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
      rewrite /b_recv_once_eav...
      rel_vals.
    Qed.

    Lemma wmf_eav_adv_true_false__wmf_eav_delay_true_false (adv : val) :
      (lrel_rand * ((lrel_id * lrel_output) * (lrel_output * ())) → lrel_bool)%lrel
        adv adv
      ⊢ REL (let: "α" := alloc #N in
          CPA' #true (λ: "senc" "oracle",
            adv (wmf_eav_adv "α" #false "senc" "oracle"))
          (symmetric_init.sym_scheme) #1) <<
        adv (init_scheme (wmf_eav_delay #false #true)) : lrel_bool.
    Proof with rel_pures_l; rel_pures_r.
      iIntros "#Hreladv".
      rel_alloctape_l α as "Hα"...
      rewrite /CPA'/init_scheme
        /wmf_protocol.CPA'/wmf_protocol.init_scheme...
      rel_apply refines_init_scheme_l.
      iIntros (lls) "HP".
      rel_apply refines_init_scheme_r.
      iIntros (rls) "HP'"...
      rewrite /get_enc/get_keygen...
      rel_apply refines_couple_TU; first done.
      iFrame.
      iIntros (r_adv Hradvbound) "Hα"...
      rel_apply refines_sym_keygen_couple.
      iIntros (ka) "#Hrelka"...
      rewrite /q_calls/is_plaintext_inst...
      rel_alloc_l cnt as "Hcnt"...
      rel_bind_l (adv _).
      rel_bind_r (adv _).
      rel_apply (refines_bind with "[-]").
      2:{
        iIntros (v v') "Hrel"...
        rel_vals.
      }
      rel_apply refines_app.
      { rel_vals. }
      rel_apply refines_randT_l. iFrame.
      iModIntro; iIntros "Hα _"...
      rel_apply refines_pair;
        first (rel_vals; iExists _; iPureIntro; repeat split; lia).
      rel_apply refines_keygen_l.
      iIntros (ka2) "#Hrelka2"...
      rel_apply refines_sym_keygen_couple.
      iIntros (kb) "#Hrelkb"...
      rewrite /s_to_b_adv/s_to_b_delay/get_rand_cipher/get_card_cipher...
      assert (Hbool1 : bool_decide (0 ≤ r_adv)%Z = true); last
      assert (Hbool2 : bool_decide (r_adv ≤ N)%Z = true);
        try (apply bool_decide_eq_true; lia);
      rewrite Hbool1 Hbool2; clear Hbool1 Hbool2.
      rel_load_l... rel_load_l; rel_store_l...
      rel_apply (refines_na_alloc (Plr lls rls) (nroot.@"wmf__delay")).
      iSplitL "HP HP'"; first iApply (P0lr_Plr with "HP HP'").
      iIntros "#Inv".
      rel_bind_l (senc _ _ _).
      rel_bind_r (senc _ _ _).
      rel_apply refines_bind.
      {
        repeat rel_apply refines_app.
        - rel_apply senc_sem_typed; last iAssumption. exists True%I.
          apply bi.equiv_entails; split; iIntros "H";
          try iDestruct "H" as "[_ H]"; iFrame.
        - rel_vals.
        - rel_vals. apply Z2Nat.inj_le; try lia. rewrite /N.
          rewrite Nat2Z.id. replace (Z.to_nat 1) with 1 by lia.
          apply fin.pow_ge_1. lia.
      }
      iIntros (c1 c1') "#Hrelc1"...
      rel_bind_l (senc _ _ _).
      rel_bind_r (senc _ _ _).
      rel_apply refines_bind.
      {
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
      rewrite /b_recv_once_eav...
      rel_vals.
    Qed.

    Lemma wmf_eav_delay_true_false__wmf_eav_adv_true_false (adv : val) :
      (lrel_rand * ((lrel_id * lrel_output) * (lrel_output * ())) → lrel_bool)%lrel
        adv adv
      ⊢ REL adv (init_scheme (wmf_eav_delay #false #true)) <<
          (let: "α" := alloc #N in
            CPA' #true (λ: "senc" "oracle",
              adv (wmf_eav_adv "α" #false "senc" "oracle"))
            (symmetric_init.sym_scheme) #1) : lrel_bool.
    Proof with rel_pures_l; rel_pures_r.
      iIntros "#Hreladv".
      rel_alloctape_r α as "Hα"...
      rewrite /CPA'/init_scheme
        /wmf_protocol.CPA'/wmf_protocol.init_scheme...
        rel_apply refines_init_scheme_l.
      iIntros (lls) "HP".
      rel_apply refines_init_scheme_r.
      iIntros (rls) "HP'"...
      rewrite /get_enc/get_keygen...
      rel_apply refines_couple_UT; first done.
      iFrame. iModIntro.
      iIntros (r_adv Hradvbound) "Hα"...
      rel_apply refines_sym_keygen_couple.
      iIntros (ka) "#Hrelka"...
      rewrite /q_calls/is_plaintext_inst...
      rel_alloc_r cnt as "Hcnt"...
      rel_bind_l (adv _).
      rel_bind_r (adv _).
      rel_apply (refines_bind with "[-]").
      2:{
        iIntros (v v') "Hrel"...
        rel_vals.
      }
      rel_apply refines_app.
      { rel_vals. }
      rel_apply (refines_randT_r with "Hα").
      iIntros "Hα _"...
      rel_apply refines_pair;
        first (rel_vals; iExists _; iPureIntro; repeat split; lia).
      rel_apply refines_keygen_r.
      iIntros (ka2) "#Hrelka2"...
      rel_apply refines_sym_keygen_couple.
      iIntros (kb) "#Hrelkb"...
      rewrite /s_to_b_adv/s_to_b_delay/get_rand_cipher/get_card_cipher...
      assert (Hbool1 : bool_decide (0 ≤ r_adv)%Z = true); last
      assert (Hbool2 : bool_decide (r_adv ≤ N)%Z = true);
        try (apply bool_decide_eq_true; lia);
      rewrite Hbool1 Hbool2; clear Hbool1 Hbool2.
      rel_load_r... rel_load_r; rel_store_r...
      rel_apply (refines_na_alloc (Plr lls rls) (nroot.@"wmf__delay")).
      iSplitL "HP HP'"; first iApply (P0lr_Plr with "HP HP'").
      iIntros "#Inv".
      rel_bind_l (senc _ _ _).
      rel_bind_r (senc _ _ _).
      rel_apply refines_bind.
      {
        repeat rel_apply refines_app.
        - rel_apply senc_sem_typed; last iAssumption. exists True%I.
          apply bi.equiv_entails; split; iIntros "H";
          try iDestruct "H" as "[_ H]"; iFrame.
        - rel_vals.
        - rel_vals. apply Z2Nat.inj_le; try lia. rewrite /N.
          rewrite Nat2Z.id. replace (Z.to_nat 1) with 1 by lia.
          apply fin.pow_ge_1. lia.
      }
      iIntros (c1 c1') "#Hrelc1"...
      rel_bind_l (senc _ _ _).
      rel_bind_r (senc _ _ _).
      rel_apply refines_bind.
      {
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
      rewrite /b_recv_once_eav...
      rel_vals.
    Qed.

    Lemma wmf_eav_delay_false_true__wmf_eav_false : 
      ⊢ REL init_scheme (wmf_eav_delay #false #true) <<
         init_scheme (wmf_eav #false) :
          (lrel_rand * ((lrel_id * lrel_output) * (lrel_output * ()))).
    Proof with rel_pures_l; rel_pures_r.
      rewrite /init_scheme/wmf_protocol.init_scheme.
      rel_apply refines_init_scheme_l.
      iIntros (lls) "HP".
      rel_apply refines_init_scheme_r.
      iIntros (rls) "HP'"...
      rel_apply refines_couple_UU; first done.
      iModIntro. iIntros (r_adv Hradvbound)...
      rel_apply refines_pair;
        first (rel_vals; iExists r_adv; iPureIntro; repeat split; lia).
      rel_apply refines_sym_keygen_couple.
      iIntros (ka) "#Hrelka"...
      rel_apply refines_sym_keygen_couple.
      iIntros (kb) "#Hrelkb"...
      rewrite /get_enc/s_to_b_delay/a_to_s_once_eav/s_to_b_once_eav...
      rel_apply (refines_couple_senc_lr_r with "[HP HP']").
      {
        iSplitR; first iAssumption.
        iSplitR.
        - iExists _, _, _, _. iPureIntro.
          repeat split; eexists; repeat split; try lia.
          apply Z2Nat.inj_le; try lia. rewrite /N.
          rewrite Nat2Z.id. replace (Z.to_nat 1) with 1 by lia.
          apply fin.pow_ge_1. lia.
        - iApply (P0lr_Plr with "HP HP'").
      }
      iIntros (c1 c1') "#Hrelc1 Hcipher1"...
      rewrite /get_dec/sym_is_cipher_lr_r...
      rel_apply "Hcipher1".
      iIntros "HP"...
      rel_apply (refines_na_alloc (Plr lls rls) (nroot.@"wmf__delay")).
      iSplitL "HP"; first iAssumption.
      iIntros "#Inv".
      rel_bind_l (senc _ _ _).
      rel_bind_r (senc _ _ _).
      rel_apply refines_bind.
      {
        repeat rel_apply refines_app.
        - rel_apply senc_sem_typed; last iAssumption. exists True%I.
          apply bi.equiv_entails; split; iIntros "H";
          try iDestruct "H" as "[_ H]"; iFrame.
        - rel_vals.
        - rel_vals.
      }
      iIntros (c2 c2') "#Hrelc2"...
      rewrite /b_recv_once_eav...
      rel_vals; try iExists _; try iPureIntro; repeat split; done.
    Qed.

    Lemma wmf_eav_false__wmf_eav_delay_false_true : 
      ⊢ REL init_scheme (wmf_eav #false) <<
          init_scheme (wmf_eav_delay #false #true) :
          (lrel_rand * ((lrel_id * lrel_output) * (lrel_output * ()))).
    Proof with rel_pures_l; rel_pures_r.
      rewrite /init_scheme/wmf_protocol.init_scheme.
      rel_apply refines_init_scheme_l.
      iIntros (lls) "HP".
      rel_apply refines_init_scheme_r.
      iIntros (rls) "HP'"...
      rel_apply refines_couple_UU; first done.
      iModIntro. iIntros (r_adv Hradvbound)...
      rel_apply refines_pair;
        first (rel_vals; iExists r_adv; iPureIntro; repeat split; lia).
      rel_apply refines_sym_keygen_couple.
      iIntros (ka) "#Hrelka"...
      rel_apply refines_sym_keygen_couple.
      iIntros (kb) "#Hrelkb"...
      rewrite /get_enc/s_to_b_delay/a_to_s_once_eav/s_to_b_once_eav...
      rel_apply (refines_couple_senc_lr_l with "[HP HP']").
      {
        iSplitR; first iAssumption.
        iSplitR.
        - iExists _, _, _, _. iPureIntro.
          repeat split; eexists; repeat split; try lia.
          apply Z2Nat.inj_le; try lia. rewrite /N.
          rewrite Nat2Z.id. replace (Z.to_nat 1) with 1 by lia.
          apply fin.pow_ge_1. lia.
        - iApply (P0lr_Plr with "HP HP'").
      }
      iIntros (c1 c1') "#Hrelc1 Hcipher1"...
      rewrite /get_dec/sym_is_cipher_lr_l...
      rel_apply "Hcipher1".
      iIntros "HP"...
      rel_apply (refines_na_alloc (Plr lls rls) (nroot.@"wmf__delay")).
      iSplitL "HP"; first iAssumption.
      iIntros "#Inv".
      rel_bind_l (senc _ _ _).
      rel_bind_r (senc _ _ _).
      rel_apply refines_bind.
      {
        repeat rel_apply refines_app.
        - rel_apply senc_sem_typed; last iAssumption. exists True%I.
          apply bi.equiv_entails; split; iIntros "H";
          try iDestruct "H" as "[_ H]"; iFrame.
        - rel_vals.
        - rel_vals.
      }
      iIntros (c2 c2') "#Hrelc2"...
      rewrite /b_recv_once_eav...
      rel_vals; try iExists _; try iPureIntro; repeat split; done.
    Qed.

  End eavesdropping_attacker.

End logrel.