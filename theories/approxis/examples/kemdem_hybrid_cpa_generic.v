From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From clutch.prob_lang Require Import advantage typing.tychk.
From clutch.approxis Require Import map reltac2 approxis option.
From clutch.approxis.examples Require Import
  valgroup security_aux option bounded_oracle
  pubkey_class advantage_laws iterable_expression.
From clutch.approxis.examples Require symmetric_init.
From mathcomp Require Import ssrbool.
Set Default Proof Using "All".
Import map.

Section Hybrid_scheme.

Definition lrel_trivial {Σ} : lrel Σ.
Proof. unshelve econstructor.
  - exact (λ v v', True%I).
  - iIntros (v1 v2). rewrite /Persistent.
    iIntros "H". iModIntro. done.
Defined.

(* VARIABLES*)

(* PARAMETERS OF THE ENCRYPTION SCHEMES *)

(* Symmetric *)
Variable SymKey : nat.
Variable Input : nat.
Variable SymOutput : nat.

#[local] Instance sym_params : symmetric_init.SYM_init_params := {|
    symmetric_init.card_key := SymKey
  ; symmetric_init.card_message := Input
  ; symmetric_init.card_cipher := SymOutput
|}.

Context `{symmetric_init.SYM_init}.

(* Asymmetric *)

Variable Key : nat.
Variable MessageSymKey : nat.
Variable Output : nat.

#[local] Instance asym_params : ASYM_params := {|
    card_key := Key
  ; card_message := MessageSymKey
  ; card_cipher := Output
|}.

Context `{asym : ASYM (H := asym_params)}.

Definition keygen_kem : val := keygen.

Definition encaps : val :=
  λ: "pk",
    let: "k" := symmetric_init.get_keygen symmetric_init.sym_scheme #() in
    let: "ckem" := enc "pk" "k" in
    ("ckem", "k").

Definition encaps_ideal : val :=
  λ: "pk",
    let: "k" := symmetric_init.get_keygen symmetric_init.sym_scheme #() in
    let: "ckem" := rand_cipher #() in
    ("ckem", "k").

Definition decaps : val :=
  λ: "sk" "c",
    (dec "sk" "c").

Definition enc_hyb : val :=
  λ: "enc_scheme" "pk" "msg",
    let: "caps" := encaps "pk" in
    let: "k" := Snd "caps" in
    let: "ckem" := Fst "caps" in
    let: "cdem" := (symmetric_init.get_enc "enc_scheme") "k" "msg" in
    ("cdem", "ckem").

Definition dec_hyb : val :=
  λ: "enc_scheme" "sk" "msg",
    let: "cdem" := Fst "msg" in
    let: "ckem" := Snd "msg" in
    let: "k" := decaps "sk" "ckem" in
    ((symmetric_init.get_dec "enc_scheme") "k" "cdem").

Section logrel.

  Context `{!approxisRGS Σ}.
  Context {Δ : listO (lrelC Σ)}.
  
  (* ASSUMPTIONS ON THE SCHEMES FOR CORRECTNESS *)

  Definition left_lrel (τ : lrel Σ) (v : val) : iProp Σ := ∃ v', (lrel_car τ) v v'.
  Definition right_lrel (τ : lrel Σ) (v : val) : iProp Σ := ∃ v', (lrel_car τ) v' v.
  
  (* Semantic types *)
  (* Symmetric *)
  Variable lrel_input : lrel Σ.
  Variable lrel_output : lrel Σ.
  Variable lrel_key : lrel Σ.

  (* Asymmetric *)
  Variable lrel_kem_msg : lrel Σ.
  Variable lrel_asym_output : lrel Σ.
  Variable lrel_sk : lrel Σ.
  Variable lrel_pk : lrel Σ.

  (* Encryption functions *)
  Variable senc : list loc → val.
  Variable sdec : list loc → val.

  (* Properties *)
  Variable is_asym_key_l : val → val → iProp Σ.
  Variable is_asym_key_r : val → val → iProp Σ.
  Variable is_asym_key_lr : val → val → iProp Σ.

  Variable P0l : list loc → iProp Σ.
  Variable P0r : list loc → iProp Σ.

  Variable Pl : list loc → iProp Σ.
  Variable Pr : list loc → iProp Σ.
  Variable Plr : list loc → list loc → iProp Σ.

  (* ASSUMPTIONS *)
  (* About semantic types *)
  Hypothesis is_asym_key_lrel : ∀ sk pk, is_asym_key_lr sk pk
    ⊢ (lrel_car lrel_pk pk pk).
  Hypothesis is_asym_key_l_persistent :
    ∀ sk pk, Persistent (is_asym_key_l sk pk).
  Hypothesis is_asym_key_r_persistent :
    ∀ sk pk, Persistent (is_asym_key_r sk pk).
  Hypothesis is_asym_key_lr_persistent :
    ∀ sk pk, Persistent (is_asym_key_lr sk pk).
  Hypothesis asym_key_lr_l_r :
    ∀ sk pk, is_asym_key_lr sk pk -∗ is_asym_key_l sk pk ∗ is_asym_key_r sk pk. 
  Hypothesis lrel_skey_amsg : forall v v', lrel_key v v' -∗ lrel_kem_msg v v'.

  (* About hypothesis for the symmetric scheme *)
  Definition P0_P_l_prop := ∀ lls, P0l lls -∗ Pl lls.
  Definition P0_P_r_prop := ∀ rls, P0r rls -∗ Pr rls.
  Definition P0lr_Plr_prop := ∀ lls rls, P0l lls -∗ P0r rls -∗ Plr lls rls.
  Hypothesis P0_P_l : P0_P_l_prop.
  Hypothesis P0_P_r : P0_P_r_prop.
  Hypothesis P0lr_Plr : P0lr_Plr_prop.

  (* Refinements *)
  (* Symmetric *)
  (* initialization *)
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

  (* key generation *)
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

  (* encryption *)
  Definition sym_is_cipher_l {lls : list loc} (msg : val) (c k : val) : iProp Σ :=
    ∀ K e E A,
      (Pl lls -∗
       refines E
        (fill K (Val msg))
        e A)
    -∗ refines E
        (fill K (sdec lls k c))
        e A.

  Definition refines_senc_l_prop :=
    ∀ (lls : list loc) (msg : val) (k : val) K e E A,
    left_lrel lrel_key k ∗ left_lrel lrel_input msg ∗ Pl lls ⊢
      ((∀ (c : val),
         @sym_is_cipher_l lls msg c k
      -∗ refines E
          (fill K (Val c))
          e A)
    -∗ refines E
        (fill K (senc lls k msg))
        e A).
  Hypothesis refines_senc_l : refines_senc_l_prop.

  (* asymmetric scheme *)

  Definition refines_akeygen_l_prop := forall K e E A,
    (∀ sk pk,
      is_asym_key_l sk pk -∗
      refines E
        (fill K (Val (sk, pk)))
        e A)
    ⊢ refines E
        (fill K (keygen #()))
        e A.
  Definition refines_akeygen_r_prop := forall K e E A,
    (∀ sk pk,
      is_asym_key_r sk pk -∗
      refines E
        e
        (fill K (Val (sk, pk)))
        A)
    ⊢ refines E
        e
        (fill K (keygen #()))
        A.
  Definition refines_akeygen_couple_prop := forall K K' E A,
    (∀ sk pk,
      is_asym_key_lr sk pk -∗
      refines E
        (fill K  (Val (sk, pk)))
        (fill K' (Val (sk, pk)))
        A)
    ⊢ refines E
        (fill K  (keygen #()))
        (fill K' (keygen #()))
        A.
  Hypothesis refines_akeygen_l : refines_akeygen_l_prop.
  Hypothesis refines_akeygen_r : refines_akeygen_r_prop.
  Hypothesis refines_akeygen_couple : refines_akeygen_couple_prop.

  Definition asym_is_cipher_l (msg c pk : val) : iProp Σ :=
    ∀ K e E A sk,
      is_asym_key_l sk pk
    -∗ refines E
       (fill K (Val msg))
       e A
    -∗ refines E
        (fill K (dec sk c))
        e A.
  
  Definition refines_aenc_l_prop :=
    ∀ (msg pk sk : val) K e E A,
    left_lrel lrel_kem_msg msg ∗ is_asym_key_l sk pk ⊢
      ((∀ (c : val),
         @asym_is_cipher_l msg c pk
      -∗ refines E
          (fill K (Val c))
          e A)
    -∗ refines E
        (fill K (enc pk msg))
        e A).

  Hypothesis refines_aenc_l : refines_aenc_l_prop.

  (* Tactics *)

  Ltac simpl_exp := try (rel_apply refines_exp_l; rel_pures_l);
    try (rel_apply refines_exp_r; rel_pures_r).
  Local Tactic Notation "rel_bind" open_constr(pat) :=
    rel_bind_l pat; rel_bind_r pat.

  Definition init_scheme (e : expr) : expr :=
    let: "scheme" := symmetric_init.get_enc_scheme symmetric_init.sym_scheme
      #() in
    e "scheme".

  Section Correctness.

    Import mathcomp.fingroup.fingroup.

    Lemma hybrid_scheme_correct :
      ⊢ refines top
          (init_scheme (λ: "scheme", (let, ("sk", "pk") := keygen #() in
          λ:"msg", dec_hyb "scheme" "sk" (enc_hyb "scheme" "pk" "msg"))))
          (λ: "msg", "msg")%V
          (lrel_input → lrel_input).
    Proof with rel_pures_l; rel_pures_r.
      rewrite /init_scheme.
      rel_apply refines_init_scheme_l.
      iIntros (lls) "HP0"...
      rel_apply refines_akeygen_l.
      iIntros (sk pk) "#Hakey"...
      simpl_exp.
      set (P := (Pl lls)%I).
      rel_apply (refines_na_alloc P (nroot.@"hybrid_scheme_correct")).
      iSplitL; first (iApply P0_P_l; iFrame).
      iIntros "#Inv".
      rel_arrow_val.
      iIntros (msg1 msg2) "#Hrelmsg"...
      rewrite /enc_hyb...
      rewrite /encaps...
      rewrite /symmetric_init.get_keygen...
      rel_apply refines_keygen_l.
      iIntros (key) "[%vk' #Hkrel]".
      iPoseProof (lrel_skey_amsg with "Hkrel") as "#HkGrel".
      rewrite /dec_hyb...
      rel_apply refines_na_inv; iSplitL; first iAssumption.
      iIntros "[HPl Hclose]"...
      rel_apply refines_aenc_l.
      {
        iSplit.
        - iExists vk'. iAssumption.
        - iAssumption.
      }
      iIntros (k_cipher) "Hkcipher".
      rewrite /symmetric_init.get_enc...
      rel_apply (refines_senc_l with "[HPl]");
      try iSplit; try iFrame; try iExists _; try iAssumption.
      iIntros (c) "Hcipher".
      simpl...
      rewrite /dec_hyb...
      rewrite /decaps...
      rel_apply "Hkcipher"; first iAssumption.
      rewrite /dec...
      rewrite /symmetric_init.get_dec...
      rewrite /sym_is_cipher_l.
      rel_apply "Hcipher". iIntros "HP".
      rel_apply refines_na_close. iFrame. iFrame...
      rel_vals.
    Qed.

  End Correctness.

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

  Definition aenc_sem_typed_prop :=
     ⊢ refines top enc enc (lrel_pk → lrel_kem_msg → lrel_asym_output).
  Hypothesis aenc_sem_typed : aenc_sem_typed_prop.

  Hypothesis asym_rand_cipher_couple :
    ∀ (v v' : val) K K' E A,
      (∀ r r', lrel_asym_output r r' -∗
      refines E (fill K (Val r)) (fill K' (Val r')) A)
    ⊢ refines E (fill K (rand_cipher v)) (fill K' (rand_cipher v')) A.
    
  Hypothesis rand_cipher_sem_typed : 
    ⊢ refines top symmetric_init.rand_cipher
      symmetric_init.rand_cipher (lrel_trivial → lrel_output).
      
  (* One Time Secrecy assumption on symmetric encryption scheme
    tweaked version of `CPA _ _ _ #1`, the only difference is
    the place where we generate the key. *)
  Definition OTS : val :=
      λ:"b" "adv" "scheme",
        let: "enc_scheme" := symmetric_init.get_enc_scheme "scheme" #() in
        let: "oracle" :=
          let: "counter" := ref #0 in
          λ: "msg",
            if: ! "counter" = #0 then
              "counter" <- #1;;
              let: "k" := (symmetric_init.get_keygen "scheme" #()) in
                InjR (
                  (if: "b" then
                    symmetric_init.get_enc "enc_scheme" "k"
                  else
                    symmetric_init.get_rand_cipher "scheme") "msg")
            else
              InjLV #()
        in
        let: "b'" := "adv" "oracle" in
        "b'".

  (* Intermediate steps *)

  Definition pk_real : expr :=
    λ: "enc_scheme",
      let, ("sk", "pk") := keygen #() in
      let: "count" := ref #0 in
      let: "query" := λ: "msg",
        assert (!"count" = #0);;;
        "count" <- #1;;
        let: "k" := symmetric_init.get_keygen symmetric_init.sym_scheme #() in
        let: "ckem" := enc "pk" "k" in
        let: "cdem" := (symmetric_init.get_enc "enc_scheme") "k" "msg" in
        ("cdem", "ckem")
      in
      ("pk", "query").

  Definition adv_pk_real : expr :=
    λ: "enc_scheme" "asym_oracle",
      let: "pk" := Fst "asym_oracle" in
      let: "asym_oracle" := Snd "asym_oracle" in
      let: "count" := ref #0 in
      let: "query" := λ: "msg",
        assert (!"count" = #0);;;
        "count" <- #1;;
        let: "k" := symmetric_init.get_keygen symmetric_init.sym_scheme #() in
        let:m "ckem" := "asym_oracle" "k" in
        let: "cdem" := (symmetric_init.get_enc "enc_scheme") "k" "msg" in
        ("cdem", "ckem")
      in
      ("pk", "query").

  Definition pk_real_arand : expr :=
    λ: "enc_scheme",
      let, ("sk", "pk") := keygen #() in
      let: "count" := ref #0 in
      let: "query" := λ: "msg",
        assert (!"count" = #0);;;
        "count" <- #1;;
        let: "k" := symmetric_init.get_keygen symmetric_init.sym_scheme #() in
        let: "ckem" := rand_cipher #() in
        let: "cdem" := (symmetric_init.get_enc "enc_scheme") "k" "msg" in
        ("cdem", "ckem")
      in
      ("pk", "query").

  Definition pk_real_arand_permute : expr :=
    λ: "enc_scheme",
      let, ("sk", "pk") := keygen #() in
      let: "count" := ref #0 in
      let: "query" := λ: "msg",
        assert (!"count" = #0);;;
        "count" <- #1;;
        let: "ckem" := rand_cipher #() in
        let: "k" := symmetric_init.get_keygen symmetric_init.sym_scheme #() in
        let: "cdem" := (symmetric_init.get_enc "enc_scheme") "k" "msg" in
        ("cdem", "ckem")
      in
      ("pk", "query").

  Definition adv_pk_real_arand_permute : expr :=
    λ: "enc_oracle",
      let, ("sk", "pk") := keygen #() in
      let: "count" := ref #0 in
      let: "query" := λ: "msg",
        assert (!"count" = #0);;;
        "count" <- #1;;
        let: "ckem" := rand_cipher #() in
        let:m "cdem" := "enc_oracle" "msg" in
        ("cdem", "ckem")
      in
      ("pk", "query").


  Definition pk_rand_srand : expr :=
    let, ("sk", "pk") := keygen #() in
    let: "count" := ref #0 in
    let: "query" := λ: "msg",
      assert (!"count" = #0);;;
      "count" <- #1;;
      let: "ckem" := rand_cipher #() in
      let: "cdem" :=
        symmetric_init.get_rand_cipher
          symmetric_init.sym_scheme #() in
      ("cdem", "ckem")
    in
    ("pk", "query").
    
  Definition pk_rand : expr :=
    let, ("sk", "pk") := keygen #() in
    let: "count" := ref #0 in
    let: "query" := λ: "msg",
      assert (!"count" = #0);;;
      "count" <- #1;;
      let: "ckem" := Fst (encaps_ideal "pk") in
      let: "cdem" :=
        symmetric_init.get_rand_cipher
          symmetric_init.sym_scheme #() in
      ("cdem", "ckem")
    in
    ("pk", "query").

  Let lrel_kemdem_output : lrel Σ := lrel_output * lrel_asym_output.

  Local Ltac refines_until tac :=
    repeat (rel_pure_l; rel_pure_r; try (rel_apply tac)).

  Lemma pk_real_adv :
    ⊢ refines top (init_scheme pk_real) ((init_scheme adv_pk_real) (CPA_OTS_real))
      (lrel_pk * (lrel_input → (() + lrel_kemdem_output))).
  Proof with rel_pures_l; rel_pures_r.
    rewrite /pk_real/adv_pk_real.
    rewrite /init_scheme...
    rewrite /CPA_OTS_real/CPA_real...
    rel_apply_l refines_init_scheme_l.
    iIntros (lls) "HP"...
    rel_apply refines_akeygen_couple.
    iIntros (sk pk) "#Hakey"...
    rewrite /q_calls_poly...
    rel_alloc_r cnt2 as "Hcnt2"...
    rel_apply_r refines_init_scheme_r.
    iIntros (rls) "HP'"...
    rel_alloc_l cnt as "Hcnt".
    rel_alloc_r cnt' as "Hcnt'".
    refines_until refines_pair;
      first (rel_vals; iApply is_asym_key_lrel; iAssumption).
    set (P := (
       (cnt ↦ #0 ∗ cnt' ↦ₛ #0 ∗ cnt2 ↦ₛ #0
      ∨ cnt ↦ #1 ∗ cnt' ↦ₛ #1 ∗ cnt2 ↦ₛ #1)
      ∗ Plr lls rls
    )%I).
    rel_apply (refines_na_alloc P (nroot.@"pk_real__adv")).
    iSplitL.
    {
      iSplitR "HP HP'".
      - iLeft. iFrame.
      - iApply (P0lr_Plr with "HP HP'").
    }
    iIntros "#Inv".
    rel_arrow_val.
    iIntros (msg1 msg2) "#Hrelmsg"...
    rel_apply refines_na_inv; iSplitL; first iAssumption.
    iIntros "[[[ [Hcnt [Hcnt' Hcnt2]]|[Hcnt [Hcnt' Hcnt2]] ] HP] Hclose]";
    rel_load_l; rel_load_r...
    - rel_store_l; rel_store_r...
      rewrite /symmetric_init.get_keygen...
      rel_apply refines_sym_keygen_couple.
      iIntros (k) "#Hrelk"...
      rel_load_r... rel_load_r... rel_store_r...
      replace (0+1)%Z with 1%Z by lia.
      rel_apply refines_na_close; iFrame; iFrame.
      iSplitL; first (iRight; iFrame).
      rel_bind (enc _ _).
      rel_apply refines_bind.
      + repeat rel_apply refines_app.
        * rel_apply aenc_sem_typed.
        * rel_vals. iApply is_asym_key_lrel. iAssumption.
        * rel_vals. iApply lrel_skey_amsg. iApply "Hrelk".
      + iIntros (kem kem') "#Hrelkem"...
        rewrite /symmetric_init.get_enc...
        rel_bind_l (senc _ _ _).
        rel_bind_r (senc _ _ _).
        rel_apply refines_bind.
        { repeat rel_apply refines_app.
          - rel_apply senc_sem_typed; last iAssumption.
            eexists. done.
          - rel_vals.
          - rel_vals. }
        iIntros (c c') "#Hrelcipher"...
        rel_vals; iAssumption.
    - rel_apply refines_na_close; iFrame; iFrame.
      iSplitL; first (iRight; iFrame).
      rel_vals.
  Qed.

  Lemma adv__pk_real_arand :
    ⊢ refines top ((init_scheme adv_pk_real) (CPA_OTS_rand))
      (init_scheme pk_real_arand)
      (lrel_pk * (lrel_input → (() + lrel_kemdem_output))).
  Proof with (rel_pures_l; rel_pures_r).
    rewrite /init_scheme...
    rel_apply refines_init_scheme_r.
    iIntros (rls) "HP'".
    rewrite /CPA_OTS_rand/CPA_rand...
    rel_apply refines_akeygen_couple.
    iIntros (sk pk) "#Hakey"...
    rewrite /q_calls_poly...
    rel_alloc_l cnt2 as "Hcnt2"...
    rewrite /adv_pk_real...
    rel_apply refines_init_scheme_l.
    iIntros (lls) "HP"...
    rel_alloc_l cnt as "Hcnt".
    rel_alloc_r cnt' as "Hcnt'".
    refines_until refines_pair;
      first (rel_vals; iApply is_asym_key_lrel; iAssumption).
    set (P := (
       (cnt ↦ #0 ∗ cnt' ↦ₛ #0 ∗ cnt2 ↦ #0
      ∨ cnt ↦ #1 ∗ cnt' ↦ₛ #1 ∗ cnt2 ↦ #1)
      ∗ Plr lls rls
    )%I).
    rel_apply (refines_na_alloc P (nroot.@"adv__pk_real_arand")).
    iSplitL.
    {
      iSplitR "HP HP'".
      - iLeft. iFrame.
      - iApply (P0lr_Plr with "HP HP'").
    }
    iIntros "#Inv".
    rel_arrow_val.
    iIntros (msg1 msg2) "#Hrelmsg"...
    rel_apply refines_na_inv; iSplitL; first iAssumption.
    iIntros "[[[ [Hcnt [Hcnt' Hcnt2]]|[Hcnt [Hcnt' Hcnt2]] ] HP] Hclose]";
    rel_load_l; rel_load_r...
    - rel_store_l; rel_store_r...
      rewrite /symmetric_init.get_keygen...
      rel_apply refines_sym_keygen_couple.
      iIntros (k) "#Hrelk"...
      rel_load_l; rel_load_l; rel_store_l...
      rel_apply asym_rand_cipher_couple.
      iIntros (r r') "#Hrelr"...
      replace (0+1)%Z with 1%Z by lia.
      rewrite /symmetric_init.get_enc...
      rel_apply refines_na_close; iFrame; iFrame.
      iSplitL; first (iRight; iFrame).
      rel_bind_l (senc _ _ _).
      rel_bind_r (senc _ _ _).
      rel_apply refines_bind.
      {
        repeat rel_apply refines_app.
        - rel_apply senc_sem_typed; last iAssumption.
          eexists; done.
        - rel_vals.
        - rel_vals.
      }
      iIntros (c c') "#Hrelcipher"...
      rel_vals; iAssumption.
    - rel_apply refines_na_close; iFrame; iFrame.
      iSplitL; first (iRight; iFrame).
      rel_vals.
  Qed.

  Lemma pk_real_arand_perm__adv :
    ⊢ refines top (init_scheme pk_real_arand_permute)
      (OTS #true adv_pk_real_arand_permute symmetric_init.sym_scheme)
      (lrel_pk * (lrel_input → (() + lrel_kemdem_output))).
  Proof with (rel_pures_l; rel_pures_r).
    rewrite /init_scheme/OTS...
    rel_apply refines_init_scheme_l.
    iIntros (lls) "HP"...
    rel_apply refines_init_scheme_r.
    iIntros (rls) "HP'"...
    rel_alloc_r cnt2 as "Hcnt2"...
    rel_apply refines_akeygen_couple.
    iIntros (sk pk) "#Hakey"...
    rel_alloc_l cnt as "Hcnt".
    rel_alloc_r cnt' as "Hcnt'"...
    set (P := (
       (cnt ↦ #0 ∗ cnt' ↦ₛ #0 ∗ cnt2 ↦ₛ #0
      ∨ cnt ↦ #1 ∗ cnt' ↦ₛ #1 ∗ cnt2 ↦ₛ #1)
      ∗ Plr lls rls
    )%I).
    rel_apply (refines_na_alloc P (nroot.@"pk_real__adv")).
    iSplitL.
    {
      iSplitR "HP HP'".
      - iLeft. iFrame.
      - iApply (P0lr_Plr with "HP HP'").
    }
    iIntros "#Inv".
    rel_vals; first (iApply is_asym_key_lrel; iAssumption).
    iIntros (msg1 msg2). iModIntro. iIntros "#Hrelmsg"...
    rel_apply refines_na_inv; iSplitL; first iAssumption.
    iIntros "[[[ [Hcnt [Hcnt' Hcnt2]]|[Hcnt [Hcnt' Hcnt2]] ] HP] Hclose]";
    rel_load_l; rel_load_r...
    - rel_store_l; rel_store_r...
      rel_apply asym_rand_cipher_couple.
      iIntros (r r') "#Hrelrand"...
      rel_load_r; rel_store_r...
      rewrite /symmetric_init.get_keygen...
      rel_apply refines_sym_keygen_couple.
      iIntros (k) "#Hrelk"...
      rewrite /symmetric_init.get_enc...
      rel_apply refines_na_close; iFrame; iFrame.
      iSplitL; first (iRight; iFrame).
      rel_bind_l (senc _ _ _).
      rel_bind_r (senc _ _ _).
      rel_apply refines_bind.
      {
        repeat rel_apply refines_app.
        - rel_apply senc_sem_typed; last iAssumption.
          eexists; done.
        - rel_vals.
        - rel_vals.
      }
      iIntros (c c') "#Hrelcipher"...
      rel_vals; iAssumption.
    - rel_apply refines_na_close; iFrame; iFrame.
      iSplitL; first (iRight; iFrame).
      rel_vals.
  Qed.

  Lemma adv__pk_rand_srand :
    ⊢ refines top (OTS #false adv_pk_real_arand_permute symmetric_init.sym_scheme)
      (pk_rand_srand)
      (lrel_pk * (lrel_input → (() + lrel_kemdem_output))).
  Proof with (rel_pures_l; rel_pures_r).
    rewrite /OTS/init_scheme/pk_rand_srand...
    rel_apply refines_init_scheme_l.
    iIntros (lls) "HP"...
    rel_alloc_l cnt2 as "Hcnt2"...
    rel_apply refines_akeygen_couple.
    iIntros (sk pk) "#Hakey"...
    rel_alloc_l cnt as "Hcnt";
    rel_alloc_r cnt' as "Hcnt'"...
    set (P := (
       (cnt ↦ #0 ∗ cnt' ↦ₛ #0 ∗ cnt2 ↦ #0
      ∨ cnt ↦ #1 ∗ cnt' ↦ₛ #1 ∗ cnt2 ↦ #1)
      ∗ Pl lls
    )%I).
    rel_apply (refines_na_alloc P (nroot.@"pk_real__adv")).
    iSplitL.
    {
      iSplitR "HP".
      - iLeft. iFrame.
      - iApply (P0_P_l with "HP").
    }
    iIntros "#Inv"...
    rel_vals; first (iApply is_asym_key_lrel; iAssumption).
    iIntros (msg1 msg2). iModIntro. iIntros "#Hrelmsg"...
    rel_apply refines_na_inv; iSplitL; first iAssumption.
    iIntros "[[[ [Hcnt [Hcnt' Hcnt2]]|[Hcnt [Hcnt' Hcnt2]] ] HP] Hclose]";
    rel_load_l; rel_load_r...
    - rel_store_l; rel_store_r...
      rel_apply asym_rand_cipher_couple.
      iIntros (r r') "#Hrelrand"...
      rel_load_l; rel_store_l...
      rewrite /symmetric_init.get_keygen...
      rel_apply refines_keygen_l.
      iIntros (k) "#Hrelk"...
      rewrite /symmetric_init.get_rand_cipher...
      rel_apply refines_na_close; iFrame; iFrame.
      iSplitL; first (iRight; iFrame).
      rel_bind_l (symmetric_init.rand_cipher _);
      rel_bind_r (symmetric_init.rand_cipher _).
      rel_apply refines_bind.
      { rel_apply refines_app; first rel_apply rand_cipher_sem_typed.
        rel_vals. }
      iIntros (sym_r sym_r') "#Hrelrandsym"...
      rel_vals; iAssumption.
    - rel_apply refines_na_close; iFrame; iFrame.
      iSplitL; first (iRight; iFrame).
      rel_vals.
  Qed.

  Lemma pk_rand_srand__rand :
    ⊢ refines top (pk_rand_srand)
      pk_rand
      (lrel_pk * (lrel_input → (() + lrel_kemdem_output))).
  Proof with (rel_pures_l; rel_pures_r).
    rewrite /pk_rand_srand/pk_rand...
    rel_apply refines_akeygen_couple.
    iIntros (sk pk) "#Hakey"...
    rel_alloc_l cnt as "Hcnt".
    rel_alloc_r cnt' as "Hcnt'".
    refines_until refines_pair;
      first (rel_vals; iApply is_asym_key_lrel; iAssumption).
    rel_apply (refines_na_alloc (cnt ↦ #0 ∗ cnt' ↦ₛ #0 ∨ cnt ↦ #1 ∗ cnt' ↦ₛ #1)
      (nroot.@"pk_rand_srand__rand")).
      iSplitL; first (iLeft; iFrame).
      iIntros "#Inv".
      rel_arrow_val.
      iIntros (msg1 msg2) "#Hrelmsg"...
      rel_apply refines_na_inv; iSplitL; first iAssumption.
      iIntros "[[[Hcnt Hcnt']|[Hcnt Hcnt']] Hclose]"; rel_load_l; rel_load_r...
      - rel_store_l; rel_store_r...
        rewrite /encaps_ideal...
        rewrite /symmetric_init.get_keygen...
        rel_apply refines_keygen_r.
        iIntros (k) "#Hrelk"...
        rel_apply refines_na_close; iFrame.
        iSplitL; first (iRight; iFrame).
        rel_apply asym_rand_cipher_couple.
        iIntros (r r') "#Hrelrand"...
        rewrite /symmetric_init.get_rand_cipher...
        rel_bind (symmetric_init.rand_cipher _).
        rel_apply refines_bind.
        + rel_apply refines_app.
          * rel_apply rand_cipher_sem_typed.
          * rel_vals.
        + iIntros (sym_r sym_r') "#Hsymrand"...
          rel_vals; iAssumption.
      - rel_apply refines_na_close; iFrame.
        iSplitL; first (iRight; iFrame).
        rel_vals.
  Qed.

End logrel.

End Hybrid_scheme.