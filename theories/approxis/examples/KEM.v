From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From clutch.prob_lang Require Import advantage typing.tychk.
From clutch.approxis Require Import approxis map list option reltac2.
From clutch.approxis.examples Require Import symmetric security_aux sum_seq xor prf advantage_laws.
Set Default Proof Using "All".

Section KEM.

(* KEM real/random chosen plaintext attack. *)
Class KEM_STRUCT :=
  { KeyGen : val
  ; Encaps : val
  ; Decaps : val }.

Record typ := { carrier `{!approxisRGS Σ} : lrel Σ
             ; rnd : val
             ; rnd_typed `{!approxisRGS Σ} : ⊢ REL rnd << rnd : lrel_unit → carrier }.
#[global] Arguments carrier _ {_ _} /.
#[global] Arguments rnd _ /.
#[global] Arguments rnd_typed _ {_ _} /.
End KEM.

Module aux.
  #[global] Coercion lrel_of_typ `{!approxisRGS Σ} (τ : typ) := carrier τ.
  #[global] Arguments lrel_of_typ {_ _} _.
End aux.

Import aux.

Section KEM.

Class KEM_PARAMS :=
  { SharedSecret : typ
  ; Ciphertext : typ
  ; PublicKey : typ
  ; SecretKey : typ
  }.

Class KEM {KEM_struct : KEM_STRUCT} {KEM_params : KEM_PARAMS} :=
  { KeyGen_typed `{!approxisRGS Σ} : ⊢ REL KeyGen << KeyGen : lrel_unit → SecretKey * PublicKey
  ; Encaps_typed `{!approxisRGS Σ} : ⊢ REL Encaps << Encaps : PublicKey → Ciphertext * SharedSecret
  ; Decaps_typed `{!approxisRGS Σ} : ⊢ REL Decaps << Decaps : SecretKey → Ciphertext → SharedSecret
  }.

Context `{KEM_STRUCT, KEM_PARAMS}.

Definition CPA_real (Q : Z) : expr :=
  let, ("sk", "pk") := KeyGen #() in
  let: "ENC" := λ:"_", Encaps "pk" in
  let: "ENC" := q_calls_poly #() #() #Q "ENC" in
  ("pk", "ENC").

Definition CPA_ideal (Q : Z) : expr :=
  let, ("sk", "pk") := KeyGen #() in
  let: "ENC" := λ:"_", let, ("ctxt", "_") := Encaps "pk" in
                       let: "shsec" := rnd SharedSecret #() in
                       ("ctxt", "shsec") in
  let: "ENC" := q_calls_poly #() #() #Q "ENC" in
  ("pk", "ENC").

Definition CPA_rand (Q : Z) : expr :=
  let, ("sk", "pk") := KeyGen #() in
  let: "ENC" := λ:"_", let: "ctxt" := rnd Ciphertext #() in
                       let: "shsec" := rnd SharedSecret #() in
                       ("ctxt", "shsec") in
  let: "ENC" := q_calls_poly #() #() #Q "ENC" in
  ("pk", "ENC").


Definition CPA_OTS_rand := CPA_rand 1.
Definition CPA_OTS_real := CPA_real 1.

Definition τ_cpa `{!approxisRGS Σ} := (PublicKey * (lrel_unit → lrel_option (Ciphertext * SharedSecret)))%lrel.

(* Definition hybrid (h Q : Z) : val :=
     λ:"pk_challenge",
       let, ("pk", "challenge") := "pk_challenge" in
       let: "counter" := ref #0 in
       let: "challenge" :=
         λ: "msg",
           let: "count" := ! "counter" in
           if: ("count" < #Q) then
             "counter" <- "count" + #1 ;;
             if: ("count" < #h) then
               SOME (enc "pk" "msg")
             else if: ("count" = #h) then
                    "challenge" "msg"
                  else SOME (rand_cipher "msg")
           else NONE
       in
       ("pk", "challenge"). *)

(* Lemma hybrid_typed `{!approxisRGS Σ} h Q : ⊢ REL hybrid h Q << hybrid h Q : τ_cpa → τ_cpa.
   Proof with ireds.
     rel_arrow_val. rewrite /τ_cpa. lrintro "pk challenge". rewrite /hybrid...
     iApply (refines_na_alloc ( ∃ (q : Z), counter ↦ #q ∗ counterₛ ↦ₛ #q)%I (nroot.@"pk")).
     iSplitL ; [iFrame|].
     iIntros "#Hinv". rel_vals => //. iIntros (m_l m_r) "!> #m"...
     iApply (refines_na_inv with "[$Hinv]"); [done|].
     iIntros "(> (%q & counter & counterₛ) & Hclose)"...
     case_bool_decide as qQ...
     2: iApply (refines_na_close with "[-]") ; iFrame ; rel_vals.
     case_bool_decide as qh...
     - iApply (refines_na_close with "[-]") ; iFrame.
       rel_bind_l (enc _ _) ; rel_bind_r (enc _ _) ; iApply refines_bind => /=.
       1: repeat rel_apply refines_app => //.
       1: iApply enc_typed.
       all: iIntros ; ireds ; rel_vals.
     - case_bool_decide as qh'...
       + iApply (refines_na_close with "[-]") ; iFrame.
         rel_bind_l (challenge_l _) ; rel_bind_r (challenge_r _) ; iApply refines_bind.
         2:{ iIntros => /=... rel_vals. }
         by iApply "challenge".
       + iApply (refines_na_close with "[-]") ; iFrame.
         rel_bind_l (rand_cipher _) ; rel_bind_r (rand_cipher _) ; iApply refines_bind.
         2:{ iIntros => /=... rel_vals. }
         rel_apply refines_app.
         1: iApply rand_cipher_typed.
         rel_vals.
   Qed. *)

Lemma Encaps_eta_typed `{!approxisRGS Σ} `{KEM} pk_l pk_r :
  PublicKey pk_l pk_r
    ⊢ REL (λ:"_", Encaps pk_l)%V << (λ:"_", Encaps pk_r)%V : lrel_unit → Ciphertext * SharedSecret.
Proof.
  iIntros. rel_arrow_val. iIntros. rel_pures_l ; rel_pures_r.
  rel_apply refines_app. 1: iApply Encaps_typed. all: rel_vals.
Qed.

Lemma CPA_real_typed `{!approxisRGS Σ} `{!KEM} Q : ⊢ REL CPA_real Q << CPA_real Q : τ_cpa.
Proof with (rel_pures_r ; rel_pures_l).
  rewrite /CPA_real...
  rel_bind_l (KeyGen _) ; rel_bind_r (KeyGen _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply KeyGen_typed|rel_vals].
  lrintro "sk pk"...
  rel_bind_l (q_calls_poly _ _ _ _) ; rel_bind_r (q_calls_poly _ _ _ _) ; rel_apply refines_bind.
  1: iApply q_calls_poly_sem_typed_app. 1: iApply Encaps_eta_typed. 1: done.
  iIntros (challenge_l challenge_r) "challenge"...
  rel_vals => //.
Qed.

Lemma CPA_rand_typed `{!approxisRGS Σ} `{!KEM} Q : ⊢ REL CPA_rand Q << CPA_rand Q : τ_cpa.
Proof with (rel_pures_r ; rel_pures_l).
  rewrite /CPA_rand...
  rel_bind_l (KeyGen _) ; rel_bind_r (KeyGen _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply KeyGen_typed|rel_vals].
  lrintro "sk pk"...
  rel_bind_l (q_calls_poly _ _ _ _) ; rel_bind_r (q_calls_poly _ _ _ _) ; rel_apply refines_bind.
  1: iApply q_calls_poly_sem_typed_app.
  2: iIntros (challenge_l challenge_r) "challenge"...
  2: rel_vals => //.
  rel_arrow_val. iIntros. rel_pures_l ; rel_pures_r.
  rel_bind_l (rnd Ciphertext _) ; rel_bind_r (rnd Ciphertext _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply rnd_typed|rel_vals].
  iIntros (??) "#ctxt"...
  repeat rel_apply refines_app ; [|iApply rnd_typed|rel_vals]...
  rel_arrow_val. iIntros (??) "#shsec"... rel_vals => //.
Qed.

Lemma CPA_ideal_typed `{!approxisRGS Σ} `{!KEM} Q : ⊢ REL CPA_ideal Q << CPA_ideal Q : τ_cpa.
Proof with (rel_pures_r ; rel_pures_l).
  rewrite /CPA_ideal...
  rel_bind_l (KeyGen _) ; rel_bind_r (KeyGen _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply KeyGen_typed|rel_vals].
  lrintro "sk pk"...
  rel_bind_l (q_calls_poly _ _ _ _) ; rel_bind_r (q_calls_poly _ _ _ _) ; rel_apply refines_bind.
  1: iApply q_calls_poly_sem_typed_app.
  2: iIntros (challenge_l challenge_r) "challenge"...
  2: rel_vals => //.
  rel_arrow_val. iIntros. rel_pures_l ; rel_pures_r.
  rel_bind_l (Encaps _) ; rel_bind_r (Encaps _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply Encaps_typed|rel_vals].
  lrintro "ctxt _"...
  repeat rel_apply refines_app ; [|iApply rnd_typed|rel_vals]...
  rel_arrow_val. iIntros (??) "#shsec"... rel_vals => //.
Qed.

End KEM.
