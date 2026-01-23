From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From clutch.prob_lang Require Import advantage typing.tychk.
From clutch.approxis Require Import approxis map list option reltac2.
From clutch.approxis.examples Require Import security_aux sum_seq xor advantage_laws.
From clutch.approxis.examples Require pubkey symmetric KEM.
Import KEM.aux.
Module sym := symmetric.
Set Default Proof Using "All".

Section KEMDEM.

(* KEM real/random chosen plaintext attack. *)
(* proof sketch

(* pke.real = hyb.enc(m) *)
ENC(m) =
     let c_kem, k_kem = Encaps(pk) in
     let c_dem = Sym.enc (k_kem, m) in
     (c_kem, c_dem).

(* by hyb.real ~ hyb.rand *)
ENC(m) =
     let c_kem, k_kem = rnd KEM.ciphertext, rnd KEM.sharedsecret in
     let c_dem = Sym.enc (k_kem, m) in
     (c_kem, c_dem).

(* by sym.real ~ sym.rand *)
ENC(m) =
     let c_kem, k_kem = rnd KEM.ciphertext, rnd KEM.sharedsecret in
     let c_dem = rnd Sym.cipher in
     (c_kem, c_dem).

(* pke.ideal = λ m, rnd hyb.ciphertext () *)
ENC(m) =
     let c_kem = rnd KEM.ciphertext in
     let c_dem = rnd Sym.ciphertext in
     (c_kem, c_dem)
 *)


Context `{KEM_struct : KEM.KEM_STRUCT}.
Context `{KEM_params : !KEM.KEM_PARAMS}.
Context `{kem : !KEM.KEM}.


Context `{sym : sym.SYM}.
Context (Sym_Message : ∀ `{!approxisRGS Σ}, lrel Σ).
Definition Sym_SecretKey := KEM.SharedSecret.
Context (Sym_Ciphertext : ∀ `{!approxisRGS Σ}, lrel Σ).

Context (Sym_rand_cipher_typed : ∀ `{!approxisRGS Σ}, ⊢ REL sym.rand_cipher << sym.rand_cipher : lrel_unit → Sym_Ciphertext _ _).


Definition Hyb_PublicKey := KEM.PublicKey.
Definition Hyb_SecretKey := KEM.SecretKey.
Definition Hyb_Message := Sym_Message.
Definition Hyb_Ciphertext : KEM.typ.
Proof.
  unshelve econstructor.
  - exact (λ Σ H, (KEM.carrier KEM.Ciphertext) * (Sym_Ciphertext Σ H))%lrel.
  - exact (λ:"_", let: "c_kem" := KEM.rnd KEM.Ciphertext #() in
                       let: "c_dem" := sym.rand_cipher #() in
                       ("c_kem", "c_dem"))%V.
  - intros. rel_arrow_val. lrintro. ireds.
    rel_bind_l (KEM.rnd _ _) ; rel_bind_r (KEM.rnd _ _).
    iApply refines_bind. 1: iApply refines_app. 1: iApply KEM.rnd_typed. 1: rel_vals.
    iIntros => /=. ireds. rel_bind_l (sym.rand_cipher _) ; rel_bind_r (sym.rand_cipher _).
    iApply refines_bind. 1: iApply refines_app. 1: iApply Sym_rand_cipher_typed. 1: rel_vals.
    iIntros => /=. ireds. rel_vals => //.
Defined.

Definition Hyb_KeyGen := KEM.KeyGen.
Definition Hyb_Enc : val := λ:"pk" "msg",
    let, ("c_kem", "k_dem") := KEM.Encaps "pk" in
    let: "c_dem" := sym.enc "k_dem" "msg" in
    ("c_kem", "c_dem").
Definition Hyb_Dec : val := λ:"sk" "c",
    let, ("c_kem", "c_dem") := "c" in
    let: "k_dem" := KEM.Decaps "sk" "c_kem" in
    sym.dec "k_dem" "c_dem".

Definition τ_pke_cpa `{!approxisRGS Σ} := pubkey.τ_cpa (λ Σ H, KEM.carrier Hyb_PublicKey (Σ:= Σ)) Hyb_Message (λ Σ H, KEM.carrier Hyb_Ciphertext (Σ:= Σ)).

Context (Sym_keygen_typed : ∀ `{!approxisRGS Σ}, ⊢ REL sym.keygen << sym.keygen : lrel_unit → Sym_SecretKey).
Context (Sym_enc_typed : ∀ `{!approxisRGS Σ}, ⊢ REL sym.enc << sym.enc : Sym_SecretKey → Sym_Message _ _ → Sym_Ciphertext _ _).

Variable (Q : Z).

Definition Game0 : expr :=
  let, ("sk", "pk") := KEM.KeyGen #() in
  let: "ENC" := λ:"msg",
      let, ("c_kem", "k_dem") := KEM.Encaps "pk" in
      let: "c_dem" := sym.enc "k_dem" "msg" in
      ("c_kem", "c_dem")
  in
  let: "ENC" := q_calls_poly #() #() #Q "ENC" in
  ("pk", "ENC").


Context `{!approxisRGS Σ}.

Lemma Step1 : ⊢ REL (pubkey.CPA_real Hyb_KeyGen Hyb_Enc Q) << Game0 : τ_pke_cpa.
Proof with (iredpures ; rewrite -?/(@q_calls' _ _ _) -?/(@q_calls'' _ _ _)).
  rewrite /pubkey.CPA_real...
  rewrite /Hyb_KeyGen...
  rel_bind_l (KEM.KeyGen _) ; rel_bind_r (KEM.KeyGen _) ; iApply refines_bind.
  { iApply refines_app. 1: iApply KEM.KeyGen_typed. rel_vals. }
  lrintro "sk pk" => /=...
  rewrite /q_calls_poly... ireds...
  iApply (refines_na_alloc (∃ (q : Z), counter ↦ #q ∗ counterₛ ↦ₛ #q)%I (nroot.@"KEM")) ; iFrame.
  iIntros "#Hinv".
  rel_vals ; [by rewrite /Hyb_PublicKey|].
  iIntros (msg_l msg_r) "!> #msg".
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & counter & counter') & Hclose)". rewrite /q_calls''...
  ireds. case_bool_decide ; ireds.
  2: iApply (refines_na_close with "[-]") ; iFrame ; rel_vals.
  rewrite /Hyb_Enc...
  iApply (refines_na_close with "[-]") ; iFrame.
  rel_bind_l (KEM.Encaps _) ; rel_bind_r (KEM.Encaps _) ; iApply refines_bind.
  { iApply refines_app. 1: iApply KEM.Encaps_typed. rel_vals. }
  lrintro "c_kem shsec" => /=...
  rel_bind_l (sym.enc _ _) ; rel_bind_r (sym.enc _ _) ; iApply refines_bind.
  { repeat iApply refines_app. 1: iApply Sym_enc_typed. 1,2: rel_vals. }
  iIntros (??) "#c_dem" => /=...
  rel_vals => //.
Qed.

Lemma Step1' : ⊢ REL Game0 << (pubkey.CPA_real Hyb_KeyGen Hyb_Enc Q) : τ_pke_cpa.
Proof with (iredpures ; rewrite -?/(@q_calls' _ _ _) -?/(@q_calls'' _ _ _)).
  rewrite /pubkey.CPA_real...
  rewrite /Hyb_KeyGen...
  rel_bind_l (KEM.KeyGen _) ; rel_bind_r (KEM.KeyGen _) ; iApply refines_bind.
  { iApply refines_app. 1: iApply KEM.KeyGen_typed. rel_vals. }
  lrintro "sk pk" => /=...
  rewrite /q_calls_poly... ireds...
  iApply (refines_na_alloc (∃ (q : Z), counter ↦ #q ∗ counterₛ ↦ₛ #q)%I (nroot.@"KEM")) ; iFrame.
  iIntros "#Hinv".
  rel_vals ; [by rewrite /Hyb_PublicKey|].
  iIntros (msg_l msg_r) "!> #msg".
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & counter & counter') & Hclose)". rewrite /q_calls''...
  ireds. case_bool_decide ; ireds.
  2: iApply (refines_na_close with "[-]") ; iFrame ; rel_vals.
  rewrite /Hyb_Enc...
  iApply (refines_na_close with "[-]") ; iFrame.
  rel_bind_l (KEM.Encaps _) ; rel_bind_r (KEM.Encaps _) ; iApply refines_bind.
  { iApply refines_app. 1: iApply KEM.Encaps_typed. rel_vals. }
  lrintro "c_kem shsec" => /=...
  rel_bind_l (sym.enc _ _) ; rel_bind_r (sym.enc _ _) ; iApply refines_bind.
  { repeat iApply refines_app. 1: iApply Sym_enc_typed. 1,2: rel_vals. }
  iIntros (??) "#c_dem" => /=...
  rel_vals => //.
Qed.


Definition R1 : val :=
  λ:"pk_ENC",
    let, ("pk", "ENC") := "pk_ENC" in
    let: "ENC" := λ:"msg",
        let:m "venc" := "ENC" #() in
        let, ("c_kem", "k_dem") := "venc" in
        let: "c_dem" := sym.enc "k_dem" "msg" in
        SOME ("c_kem", "c_dem")
    in
    ("pk", "ENC").

Definition R1_KEM_real : expr := R1 (KEM.CPA_real Q).

Lemma Step2 : ⊢ REL Game0 << R1_KEM_real : τ_pke_cpa.
Proof with (iredpures ; rewrite -?/(@q_calls' _ _ _) -?/(@q_calls'' _ _ _)).
  rewrite /R1_KEM_real /R1...
  rewrite /sym.CPA_sem.CPA_real... rewrite /sym.get_keygen...
  rel_bind_l (KEM.KeyGen _) ; rel_bind_r (KEM.KeyGen _) ; iApply refines_bind.
  { iApply refines_app. 1: iApply KEM.KeyGen_typed. rel_vals. }
  lrintro "sk pk" => /=...
  rewrite /q_calls_poly ; ireds...
  iApply (refines_na_alloc (∃ (q : Z), counter ↦ #q ∗ counterₛ ↦ₛ #q)%I (nroot.@"KEM")) ; iFrame.
  iIntros "#Hinv".
  rel_vals ; [by rewrite /Hyb_PublicKey|].
  iIntros (msg_l msg_r) "!> #msg".
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & counter & counter') & Hclose)"... rewrite /q_calls''...
  ireds. case_bool_decide ; ireds.
  2: iApply (refines_na_close with "[-]") ; iFrame ; rel_vals.
  rewrite /Hyb_Enc...
  iApply (refines_na_close with "[-]") ; iFrame.
  rel_bind_l (KEM.Encaps _) ; rel_bind_r (KEM.Encaps _) ; iApply refines_bind.
  { iApply refines_app. 1: iApply KEM.Encaps_typed. rel_vals. }
  lrintro "c_kem shsec" => /=...
  rel_bind_l (sym.enc _ _) ; rel_bind_r (sym.enc _ _) ; iApply refines_bind.
  { repeat iApply refines_app. 1: iApply Sym_enc_typed. 1,2: rel_vals. }
  iIntros (??) "#c_dem" => /=...
  rel_vals => //.
Qed.

Lemma Step2' : ⊢ REL R1_KEM_real << Game0 : τ_pke_cpa.
Proof with (iredpures ; rewrite -?/(@q_calls' _ _ _) -?/(@q_calls'' _ _ _)).
  rewrite /R1_KEM_real /R1...
  rewrite /sym.CPA_sem.CPA_real... rewrite /sym.get_keygen...
  rel_bind_l (KEM.KeyGen _) ; rel_bind_r (KEM.KeyGen _) ; iApply refines_bind.
  { iApply refines_app. 1: iApply KEM.KeyGen_typed. rel_vals. }
  lrintro "sk pk" => /=...
  rewrite /q_calls_poly ; ireds...
  iApply (refines_na_alloc (∃ (q : Z), counter ↦ #q ∗ counterₛ ↦ₛ #q)%I (nroot.@"KEM")) ; iFrame.
  iIntros "#Hinv".
  rel_vals ; [by rewrite /Hyb_PublicKey|].
  iIntros (msg_l msg_r) "!> #msg".
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & counter & counter') & Hclose)"... rewrite /q_calls''...
  ireds. case_bool_decide ; ireds.
  2: iApply (refines_na_close with "[-]") ; iFrame ; rel_vals.
  rewrite /Hyb_Enc...
  iApply (refines_na_close with "[-]") ; iFrame.
  rel_bind_l (KEM.Encaps _) ; rel_bind_r (KEM.Encaps _) ; iApply refines_bind.
  { iApply refines_app. 1: iApply KEM.Encaps_typed. rel_vals. }
  lrintro "c_kem shsec" => /=...
  rel_bind_l (sym.enc _ _) ; rel_bind_r (sym.enc _ _) ; iApply refines_bind.
  { repeat iApply refines_app. 1: iApply Sym_enc_typed. 1,2: rel_vals. }
  iIntros (??) "#c_dem" => /=...
  rel_vals => //.
Qed.

Definition Game1 : expr :=
  let, ("sk", "pk") := KEM.KeyGen #() in
  let: "ENC" := λ:"msg",
      (* let, ("c_kem", "k_dem") := KEM.Encaps "pk" in *)
      let: "c_kem" := KEM.rnd KEM.Ciphertext #() in
      let: "k_dem" := KEM.rnd KEM.SharedSecret #() in
      let: "c_dem" := sym.enc "k_dem" "msg" in
      ("c_kem", "c_dem")
  in
  let: "ENC" := q_calls_poly #() #() #Q "ENC" in
  ("pk", "ENC").

Lemma Step4 : ⊢ REL R1 (KEM.CPA_rand Q) << Game1 : τ_pke_cpa.
Proof with (iredpures ; rewrite -?/(@q_calls' _ _ _) -?/(@q_calls'' _ _ _)).
  rewrite /R1_KEM_real /R1...
  rewrite /sym.CPA_sem.CPA_real... rewrite /sym.get_keygen...
  rel_bind_l (KEM.KeyGen _) ; rel_bind_r (KEM.KeyGen _) ; iApply refines_bind.
  { iApply refines_app. 1: iApply KEM.KeyGen_typed. rel_vals. }
  lrintro "sk pk" => /=...
  rewrite /q_calls_poly ; ireds...
  iApply (refines_na_alloc (∃ (q : Z), counter ↦ #q ∗ counterₛ ↦ₛ #q)%I (nroot.@"KEM")) ; iFrame.
  iIntros "#Hinv".
  rel_vals ; [by rewrite /Hyb_PublicKey|].
  iIntros (msg_l msg_r) "!> #msg".
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & counter & counter') & Hclose)"... rewrite /q_calls''...
  ireds. case_bool_decide ; ireds.
  2: iApply (refines_na_close with "[-]") ; iFrame ; rel_vals.
  rewrite /Hyb_Enc...
  iApply (refines_na_close with "[-]") ; iFrame.
  rel_bind_l (KEM.rnd KEM.Ciphertext _) ; rel_bind_r (KEM.rnd KEM.Ciphertext _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply KEM.rnd_typed|rel_vals].
  iIntros (??) "#c_kem"...
  rel_bind_l (KEM.rnd KEM.SharedSecret _) ; rel_bind_r (KEM.rnd KEM.SharedSecret _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply KEM.rnd_typed|rel_vals].
  iIntros (??) "#c_dem"...
  rel_bind_l (sym.enc _ _) ; rel_bind_r (sym.enc _ _) ; iApply refines_bind.
  { repeat iApply refines_app. 1: iApply Sym_enc_typed. 1,2: rel_vals. }
  iIntros (??) "#c_dem'" => /=...
  rel_vals => //.
Qed.

Lemma Step4' : ⊢ REL Game1 << R1 (KEM.CPA_rand Q) : τ_pke_cpa.
Proof with (iredpures ; rewrite -?/(@q_calls' _ _ _) -?/(@q_calls'' _ _ _)).
  rewrite /R1_KEM_real /R1...
  rewrite /sym.CPA_sem.CPA_real... rewrite /sym.get_keygen...
  rel_bind_l (KEM.KeyGen _) ; rel_bind_r (KEM.KeyGen _) ; iApply refines_bind.
  { iApply refines_app. 1: iApply KEM.KeyGen_typed. rel_vals. }
  lrintro "sk pk" => /=...
  rewrite /q_calls_poly ; ireds...
  iApply (refines_na_alloc (∃ (q : Z), counter ↦ #q ∗ counterₛ ↦ₛ #q)%I (nroot.@"KEM")) ; iFrame.
  iIntros "#Hinv".
  rel_vals ; [by rewrite /Hyb_PublicKey|].
  iIntros (msg_l msg_r) "!> #msg".
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & counter & counter') & Hclose)"... rewrite /q_calls''...
  ireds. case_bool_decide ; ireds.
  2: iApply (refines_na_close with "[-]") ; iFrame ; rel_vals.
  rewrite /Hyb_Enc...
  iApply (refines_na_close with "[-]") ; iFrame.
  rel_bind_l (KEM.rnd KEM.Ciphertext _) ; rel_bind_r (KEM.rnd KEM.Ciphertext _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply KEM.rnd_typed|rel_vals].
  iIntros (??) "#c_kem"...
  rel_bind_l (KEM.rnd KEM.SharedSecret _) ; rel_bind_r (KEM.rnd KEM.SharedSecret _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply KEM.rnd_typed|rel_vals].
  iIntros (??) "#c_dem"...
  rel_bind_l (sym.enc _ _) ; rel_bind_r (sym.enc _ _) ; iApply refines_bind.
  { repeat iApply refines_app. 1: iApply Sym_enc_typed. 1,2: rel_vals. }
  iIntros (??) "#c_dem'" => /=...
  rel_vals => //.
Qed.

Definition R2 : val := λ: "ENC",
    let, ("sk", "pk") := KEM.KeyGen #() in
    let: "ENC" := λ:"msg",
        (* let, ("c_kem", "k_dem") := KEM.Encaps "pk" in *)
        let: "c_kem" := KEM.rnd KEM.Ciphertext #() in
        let: "c_dem" := "ENC" "msg" in
        ("c_kem", "c_dem")
    in
    let: "ENC" := q_calls_poly #() #() #Q "ENC" in
    ("pk", "ENC").


Definition sym_OTS_real : val :=
  λ:"msg",
    (* TODO should be using sym.keygen instead of sampling "by hand". *)
    (* let: "key" := sym.keygen #() in *)
    let: "key" := KEM.rnd Sym_SecretKey #() in
    sym.enc "key" "msg".

Definition sym_OTS_rand : val :=
  λ:"msg",
    (* let: "key" := sym.keygen #() in *)
    sym.rand_cipher #().

Lemma Step5 : ⊢ REL Game1 << R2 sym_OTS_real : τ_pke_cpa.
Proof with (iredpures ; rewrite -?/(@q_calls' _ _ _) -?/(@q_calls'' _ _ _)).
  rewrite /R2...
  rewrite /sym_OTS_real...
  rel_bind_l (KEM.KeyGen _) ; rel_bind_r (KEM.KeyGen _) ; iApply refines_bind.
  { iApply refines_app. 1: iApply KEM.KeyGen_typed. rel_vals. }
  lrintro "sk pk" => /=...
  rewrite /q_calls_poly ; ireds...
  iApply (refines_na_alloc (∃ (q : Z), counter ↦ #q ∗ counterₛ ↦ₛ #q)%I (nroot.@"KEM")) ; iFrame.
  iIntros "#Hinv".
  rel_vals ; [by rewrite /Hyb_PublicKey|].
  iIntros (msg_l msg_r) "!> #msg".
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & counter & counter') & Hclose)"... rewrite /q_calls''...
  ireds. case_bool_decide ; ireds.
  2: iApply (refines_na_close with "[-]") ; iFrame ; rel_vals.
  iApply (refines_na_close with "[-]") ; iFrame.
  rel_bind_l (KEM.rnd KEM.Ciphertext _) ; rel_bind_r (KEM.rnd KEM.Ciphertext _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply KEM.rnd_typed|rel_vals].
  iIntros (??) "#c_kem"...
  (* TODO Now we would have to replace the sym.keygen on the right with rnd KEM.SharedSecret *)
  rel_bind_l (KEM.rnd KEM.SharedSecret _) ; rel_bind_r (KEM.rnd KEM.SharedSecret _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply KEM.rnd_typed|rel_vals].
  iIntros (??) "#c_dem"...
  rel_bind_l (sym.enc _ _) ; rel_bind_r (sym.enc _ _) ; iApply refines_bind.
  { repeat iApply refines_app. 1: iApply Sym_enc_typed. 1,2: rel_vals. }
  iIntros (??) "#c_dem'" => /=...
  rel_vals => //.
Qed.

Lemma Step5' : ⊢ REL R2 sym_OTS_real << Game1 : τ_pke_cpa.
Proof with (iredpures ; rewrite -?/(@q_calls' _ _ _) -?/(@q_calls'' _ _ _)).
  rewrite /R2...
  rewrite /sym_OTS_real...
  rel_bind_l (KEM.KeyGen _) ; rel_bind_r (KEM.KeyGen _) ; iApply refines_bind.
  { iApply refines_app. 1: iApply KEM.KeyGen_typed. rel_vals. }
  lrintro "sk pk" => /=...
  rewrite /q_calls_poly ; ireds...
  iApply (refines_na_alloc (∃ (q : Z), counter ↦ #q ∗ counterₛ ↦ₛ #q)%I (nroot.@"KEM")) ; iFrame.
  iIntros "#Hinv".
  rel_vals ; [by rewrite /Hyb_PublicKey|].
  iIntros (msg_l msg_r) "!> #msg".
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & counter & counter') & Hclose)"... rewrite /q_calls''...
  ireds. case_bool_decide ; ireds.
  2: iApply (refines_na_close with "[-]") ; iFrame ; rel_vals.
  iApply (refines_na_close with "[-]") ; iFrame.
  rel_bind_l (KEM.rnd KEM.Ciphertext _) ; rel_bind_r (KEM.rnd KEM.Ciphertext _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply KEM.rnd_typed|rel_vals].
  iIntros (??) "#c_kem"...
  (* TODO Now we would have to replace the sym.keygen on the right with rnd KEM.SharedSecret *)
  rel_bind_l (KEM.rnd KEM.SharedSecret _) ; rel_bind_r (KEM.rnd KEM.SharedSecret _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply KEM.rnd_typed|rel_vals].
  iIntros (??) "#c_dem"...
  rel_bind_l (sym.enc _ _) ; rel_bind_r (sym.enc _ _) ; iApply refines_bind.
  { repeat iApply refines_app. 1: iApply Sym_enc_typed. 1,2: rel_vals. }
  iIntros (??) "#c_dem'" => /=...
  rel_vals => //.
Qed.


Lemma Step78 : ⊢ REL R2 sym_OTS_rand << (pubkey.CPA_rand Hyb_KeyGen (KEM.rnd Hyb_Ciphertext) Q) : τ_pke_cpa.
Proof with (iredpures ; rewrite -?/(@q_calls' _ _ _) -?/(@q_calls'' _ _ _)).
  rewrite /R2...
  rewrite /sym_OTS_real...
  rel_bind_l (KEM.KeyGen _) ; rel_bind_r (KEM.KeyGen _) ; iApply refines_bind.
  { iApply refines_app. 1: iApply KEM.KeyGen_typed. rel_vals. }
  lrintro "sk pk" => /=...
  rewrite /q_calls_poly ; ireds...
  iApply (refines_na_alloc (∃ (q : Z), counter ↦ #q ∗ counterₛ ↦ₛ #q)%I (nroot.@"KEM")) ; iFrame.
  iIntros "#Hinv".
  rel_vals ; [by rewrite /Hyb_PublicKey|].
  iIntros (msg_l msg_r) "!> #msg".
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & counter & counter') & Hclose)"... rewrite /q_calls''...
  ireds. case_bool_decide ; ireds.
  2: iApply (refines_na_close with "[-]") ; iFrame ; rel_vals.
  iApply (refines_na_close with "[-]") ; iFrame.
  rel_bind_l (KEM.rnd KEM.Ciphertext _) ; rel_bind_r (KEM.rnd KEM.Ciphertext _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply KEM.rnd_typed|rel_vals].
  iIntros (??) "#c_kem"...
  rewrite /sym_OTS_rand...
  iIntros => /=. ireds. rel_bind_l (sym.rand_cipher _) ; rel_bind_r (sym.rand_cipher _).
  iApply refines_bind. 1: iApply refines_app. 1: iApply Sym_rand_cipher_typed. 1: rel_vals.
  iIntros => /=. ireds. rel_vals => //.
Qed.

Lemma Step78' : ⊢ REL (pubkey.CPA_rand Hyb_KeyGen (KEM.rnd Hyb_Ciphertext) Q) << R2 sym_OTS_rand : τ_pke_cpa.
Proof with (iredpures ; rewrite -?/(@q_calls' _ _ _) -?/(@q_calls'' _ _ _)).
  rewrite /R2...
  rewrite /sym_OTS_real...
  rel_bind_l (KEM.KeyGen _) ; rel_bind_r (KEM.KeyGen _) ; iApply refines_bind.
  { iApply refines_app. 1: iApply KEM.KeyGen_typed. rel_vals. }
  lrintro "sk pk" => /=...
  rewrite /q_calls_poly ; ireds...
  iApply (refines_na_alloc (∃ (q : Z), counter ↦ #q ∗ counterₛ ↦ₛ #q)%I (nroot.@"KEM")) ; iFrame.
  iIntros "#Hinv".
  rel_vals ; [by rewrite /Hyb_PublicKey|].
  iIntros (msg_l msg_r) "!> #msg".
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & counter & counter') & Hclose)"... rewrite /q_calls''...
  ireds. case_bool_decide ; ireds.
  2: iApply (refines_na_close with "[-]") ; iFrame ; rel_vals.
  iApply (refines_na_close with "[-]") ; iFrame.
  rel_bind_l (KEM.rnd KEM.Ciphertext _) ; rel_bind_r (KEM.rnd KEM.Ciphertext _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply KEM.rnd_typed|rel_vals].
  iIntros (??) "#c_kem"...
  rewrite /sym_OTS_rand...
  iIntros => /=. ireds. rel_bind_l (sym.rand_cipher _) ; rel_bind_r (sym.rand_cipher _).
  iApply refines_bind. 1: iApply refines_app. 1: iApply Sym_rand_cipher_typed. 1: rel_vals.
  iIntros => /=. ireds. rel_vals => //.
Qed.

(* Definition Game2 : expr :=
     let, ("sk", "pk") := KEM.KeyGen #() in
     let: "ENC" := λ:"_",
         let: "c_kem" := KEM.rnd KEM.Ciphertext #() in
         (* let: "k_dem" := KEM.rnd KEM.SharedSecret #() in *)
         let: "c_dem" := sym.rand_cipher #() in
         ("c_kem", "c_dem")
     in
     let: "ENC" := q_calls_poly #() #() #Q "ENC" in
     ("pk", "ENC").

   Lemma Step7 : ⊢ REL R2 sym_OTS_rand << Game2 : τ_pke_cpa.
   Proof with (iredpures ; rewrite -?/(@q_calls' _ _ _) -?/(@q_calls'' _ _ _)).
     rewrite /R2...
     rewrite /sym_OTS_real...
     rel_bind_l (KEM.KeyGen _) ; rel_bind_r (KEM.KeyGen _) ; iApply refines_bind.
     { iApply refines_app. 1: iApply KEM.KeyGen_typed. rel_vals. }
     lrintro "sk pk" => /=...
     rewrite /q_calls_poly ; ireds...
     iApply (refines_na_alloc (∃ (q : Z), counter ↦ #q ∗ counterₛ ↦ₛ #q)%I (nroot.@"KEM")) ; iFrame.
     iIntros "#Hinv".
     rel_vals ; [by rewrite /Hyb_PublicKey|].
     iIntros (msg_l msg_r) "!> #msg".
     iApply (refines_na_inv with "[$Hinv]"); [done|].
     iIntros "(> (%q & counter & counter') & Hclose)"... rewrite /q_calls''...
     ireds. case_bool_decide ; ireds.
     2: iApply (refines_na_close with "[-]") ; iFrame ; rel_vals.
     iApply (refines_na_close with "[-]") ; iFrame.
     rel_bind_l (KEM.rnd KEM.Ciphertext _) ; rel_bind_r (KEM.rnd KEM.Ciphertext _) ; iApply refines_bind => /=.
     1: rel_apply refines_app ; [iApply KEM.rnd_typed|rel_vals].
     iIntros (??) "#c_kem"...
     rewrite /sym_OTS_rand...
     iIntros => /=. ireds. rel_bind_l (sym.rand_cipher _) ; rel_bind_r (sym.rand_cipher _).
     iApply refines_bind. 1: iApply refines_app. 1: iApply Sym_rand_cipher_typed. 1: rel_vals.
     iIntros => /=. ireds. rel_vals => //.
   Qed.

   Lemma Step8 : ⊢ REL Game2 << (pubkey.CPA_rand Hyb_KeyGen (KEM.rnd Hyb_Ciphertext) Q) : τ_pke_cpa.
   Proof with (iredpures ; rewrite -?/(@q_calls' _ _ _) -?/(@q_calls'' _ _ _)).
     rewrite /Hyb_KeyGen...
     rel_bind_l (KEM.KeyGen _) ; rel_bind_r (KEM.KeyGen _) ; iApply refines_bind.
     { iApply refines_app. 1: iApply KEM.KeyGen_typed. rel_vals. }
     lrintro "sk pk" => /=...
     rewrite /q_calls_poly ; ireds...
     iApply (refines_na_alloc (∃ (q : Z), counter ↦ #q ∗ counterₛ ↦ₛ #q)%I (nroot.@"KEM")) ; iFrame.
     iIntros "#Hinv".
     rel_vals ; [by rewrite /Hyb_PublicKey|].
     iIntros (msg_l msg_r) "!> #msg".
     iApply (refines_na_inv with "[$Hinv]"); [done|].
     iIntros "(> (%q & counter & counter') & Hclose)"... rewrite /q_calls''...
     ireds. case_bool_decide ; ireds.
     2: iApply (refines_na_close with "[-]") ; iFrame ; rel_vals.
     iApply (refines_na_close with "[-]") ; iFrame.
     rel_bind_l (KEM.rnd KEM.Ciphertext _) ; rel_bind_r (KEM.rnd KEM.Ciphertext _) ; iApply refines_bind => /=.
     1: rel_apply refines_app ; [iApply KEM.rnd_typed|rel_vals].
     iIntros (??) "#c_kem"...
     rel_bind_l (sym.rand_cipher _) ; rel_bind_r (sym.rand_cipher _).
     iApply refines_bind. 1: iApply refines_app. 1: iApply Sym_rand_cipher_typed. 1: rel_vals.
     iIntros => /=. ireds. rel_vals => //.
   Qed. *)

End KEMDEM.

Section meta.

Context `{KEM_struct : KEM.KEM_STRUCT}.
Context `{KEM_params : !KEM.KEM_PARAMS}.
Context `{kem : !KEM.KEM}.


Context `{sym : sym.SYM}.
Context (Sym_Message : ∀ `{!approxisRGS Σ}, lrel Σ).
Context (Sym_Ciphertext : ∀ `{!approxisRGS Σ}, lrel Σ).

Context (Sym_keygen_typed : ∀ `{!approxisRGS Σ}, ⊢ REL sym.keygen << sym.keygen : lrel_unit → Sym_SecretKey).
Context (Sym_enc_typed : ∀ `{!approxisRGS Σ}, ⊢ REL sym.enc << sym.enc : Sym_SecretKey → Sym_Message _ _ → Sym_Ciphertext _ _).
Context (Sym_rand_cipher_typed : ∀ `{!approxisRGS Σ}, ⊢ REL sym.rand_cipher << sym.rand_cipher : lrel_unit → Sym_Ciphertext _ _).

Context (adversary : val).
Context (adversary_sem_typed : ∀ `{!approxisRGS Σ} ,
            ⊢ REL adversary << adversary : (τ_pke_cpa Sym_Message Sym_Ciphertext Sym_rand_cipher_typed → lrel_bool)).
Context (b : bool).
Variable (Q : Z).

Lemma PKE_Real_G0 : (advantage adversary (pubkey.CPA_real Hyb_KeyGen Hyb_Enc Q) (Game0 Q) #b <= 0)%R.
Proof.
  opose proof (λ Σ H, Step1 (Σ := Σ) Sym_Message Sym_Ciphertext Sym_rand_cipher_typed Sym_keygen_typed Sym_enc_typed Q) as step1.
  opose proof (λ Σ H, Step1' (Σ := Σ) Sym_Message Sym_Ciphertext Sym_rand_cipher_typed Sym_keygen_typed Sym_enc_typed Q) as step1'.
  eapply (lr_advantage _ _ _ _ _ step1 step1' b).
  Unshelve. 1: apply _. done.
Qed.

Lemma G0_KEM_Real : (advantage adversary (Game0 Q) (R1_KEM_real Q) #b <= 0)%R.
Proof.
  opose proof (λ Σ H, Step2 (Σ := Σ) Sym_Message Sym_Ciphertext Sym_rand_cipher_typed Sym_keygen_typed Sym_enc_typed Q) as step2.
  opose proof (λ Σ H, Step2' (Σ := Σ) Sym_Message Sym_Ciphertext Sym_rand_cipher_typed Sym_keygen_typed Sym_enc_typed Q) as step2'.
  eapply (lr_advantage _ _ _ _ _ step2 step2' b).
  Unshelve. 1: apply _. done.
Qed.

Lemma KEM_Rand_G1 : (advantage adversary (R1 (KEM.CPA_rand Q)) (Game1 Q) #b <= 0)%R.
Proof.
  opose proof (λ Σ H, Step4 (Σ := Σ) Sym_Message Sym_Ciphertext Sym_rand_cipher_typed Sym_keygen_typed Sym_enc_typed Q) as step4.
  opose proof (λ Σ H, Step4' (Σ := Σ) Sym_Message Sym_Ciphertext Sym_rand_cipher_typed Sym_keygen_typed Sym_enc_typed Q) as step4'.
  eapply (lr_advantage _ _ _ _ _ step4 step4' b).
  Unshelve. 1: apply _. done.
Qed.

Lemma G1_Sym_real : (advantage adversary (Game1 Q) (R2 Q sym_OTS_real) #b <= 0)%R.
Proof.
  opose proof (λ Σ H, Step5 (Σ := Σ) Sym_Message Sym_Ciphertext Sym_rand_cipher_typed Sym_keygen_typed Sym_enc_typed Q) as step5.
  opose proof (λ Σ H, Step5' (Σ := Σ) Sym_Message Sym_Ciphertext Sym_rand_cipher_typed Sym_keygen_typed Sym_enc_typed Q) as step5'.
  eapply (lr_advantage _ _ _ _ _ step5 step5' b).
  Unshelve. 1: apply _. done.
Qed.

Lemma Sym_rand_PKE_rand : (advantage adversary (R2 Q sym_OTS_rand) (pubkey.CPA_rand Hyb_KeyGen (KEM.rnd (Hyb_Ciphertext Sym_Message Sym_Ciphertext Sym_rand_cipher_typed)) Q) #b <= 0)%R.
Proof.
  opose proof (λ Σ H, Step78 (Σ := Σ) Sym_Message Sym_Ciphertext Sym_rand_cipher_typed Sym_keygen_typed Sym_enc_typed Q) as step78.
  opose proof (λ Σ H, Step78' (Σ := Σ) Sym_Message Sym_Ciphertext Sym_rand_cipher_typed Sym_keygen_typed Sym_enc_typed Q) as step78'.
  eapply (lr_advantage _ _ _ _ _ step78 step78' b).
  Unshelve. done.
Qed.

Definition τ_SYM_OTS {Σ} `{!approxisRGS Σ} : lrel Σ := Sym_Message _ _ → Sym_Ciphertext _ _.

Lemma Hyb_is_CPA :
  (advantage adversary
     (pubkey.CPA_real Hyb_KeyGen Hyb_Enc Q)
     (pubkey.CPA_rand Hyb_KeyGen (KEM.rnd (Hyb_Ciphertext Sym_Message Sym_Ciphertext Sym_rand_cipher_typed)) Q) #b
   <=
     advantage (λ:"v", adversary (R1 "v"))%V (KEM.CPA_real Q) (KEM.CPA_rand Q) #b +
       advantage (λ:"v", adversary (R2 Q "v"))%V sym_OTS_real sym_OTS_rand #b
  )%R.
Proof.
  eapply advantage_triangle.
  1: eapply PKE_Real_G0.
  2: shelve.
  eapply advantage_triangle.
  1: eapply G0_KEM_Real.
  2: shelve.
  unfold R1_KEM_real.
  eapply (advantage_triangle _ _ (R1 (KEM.CPA_rand Q))).
  1: reflexivity.
  2: shelve.
  eapply advantage_triangle.
  1: eapply KEM_Rand_G1. 2: shelve.
  eapply advantage_triangle.
  1: eapply G1_Sym_real. 2: shelve.
  eapply (advantage_triangle _ _ (R2 Q sym_OTS_rand)).
  1: reflexivity.
  1: eapply Sym_rand_PKE_rand.
  reflexivity.
  Unshelve. all: try reflexivity.
  field_simplify.
  apply Rplus_le_compat.
  - eapply (advantage_reduction_lr adversary R1
              (KEM.CPA_real Q) (KEM.CPA_rand Q) b).
    iIntros (??).
    eexists KEM.τ_cpa.
    eexists (τ_pke_cpa Sym_Message Sym_Ciphertext Sym_rand_cipher_typed).
    intuition auto.
    2: eapply KEM.CPA_real_typed.
    2: eapply KEM.CPA_rand_typed.
    rewrite /R1.
    rel_arrow_val.
    rewrite /KEM.τ_cpa.
    lrintro "pk ENC".
    ireds.
    rel_vals => //.
    iIntros (msg_l msg_r) "!> #msg". ireds.
    rel_bind_l (ENC_l _) ; rel_bind_r (ENC_r _).
    iApply refines_bind => /=. 1: iApply "ENC". 1: done.
    lrintro "c_kem shsec" ; ireds. 1: rel_vals.
    rel_bind_l (sym.enc _ _) ; rel_bind_r (sym.enc _ _) ; iApply refines_bind.
    { repeat iApply refines_app. 1: iApply Sym_enc_typed. 1,2: rel_vals. }
    iIntros (??) "#c_dem'" => /=. ireds.
    rel_vals => //.
  - eapply (advantage_reduction_lr).
    iIntros (??).
    eexists τ_SYM_OTS.
    eexists (τ_pke_cpa Sym_Message Sym_Ciphertext Sym_rand_cipher_typed).
    intuition auto.
    2:{
      rewrite /sym_OTS_real.
      rel_arrow_val. iIntros (??) "#msg". ireds.
      rel_bind_l (KEM.rnd Sym_SecretKey _) ; rel_bind_r (KEM.rnd Sym_SecretKey _) ; iApply refines_bind => /=.
      1: rel_apply refines_app ; [iApply KEM.rnd_typed|rel_vals].
      iIntros (??) "#key" ; ireds.
      rel_bind_l (sym.enc _ _) ; rel_bind_r (sym.enc _ _) ; iApply refines_bind.
      { repeat iApply refines_app. 1: iApply Sym_enc_typed. 1,2: rel_vals. }
      iIntros (??) "#c" => /=...
      rel_vals => //.
    }
    2:{
      rewrite /sym_OTS_rand.
      rel_arrow_val. iIntros (??) "#msg". ireds.
      iApply refines_app. 1: iApply Sym_rand_cipher_typed. rel_vals.
    }
    rewrite /R2.
    rel_arrow_val.
    rewrite /τ_SYM_OTS.
    iIntros (enc_l enc_r) "#enc" ; ireds.
    rel_bind_l (KEM.KeyGen _) ; rel_bind_r (KEM.KeyGen _) ; iApply refines_bind.
    { iApply refines_app. 1: iApply KEM.KeyGen_typed. rel_vals. }
    lrintro "sk pk" => /= ; ireds.
    rewrite /q_calls_poly ; ireds...
    iApply (refines_na_alloc (∃ (q : Z), counter ↦ #q ∗ counterₛ ↦ₛ #q)%I (nroot.@"KEM")) ; iFrame.
    iIntros "#Hinv".
    rel_vals ; [by rewrite /Hyb_PublicKey|].
    iIntros (msg_l msg_r) "!> #msg".
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "(> (%q & counter & counter') & Hclose)"... rewrite /q_calls''...
    ireds. case_bool_decide ; ireds.
    2: iApply (refines_na_close with "[-]") ; iFrame ; rel_vals.
    iApply (refines_na_close with "[-]") ; iFrame.
    rel_bind_l (KEM.rnd KEM.Ciphertext _) ; rel_bind_r (KEM.rnd KEM.Ciphertext _) ; iApply refines_bind => /=.
    1: rel_apply refines_app ; [iApply KEM.rnd_typed|rel_vals].
    iIntros (??) "#c_kem" ; ireds.
    rel_bind_l (enc_l _) ; rel_bind_r (enc_r _).
    iApply refines_bind. 1: iApply "enc" => //.
    iIntros => /=. ireds. rel_vals => //.
    Unshelve.
    eauto.
Qed.


End meta.
