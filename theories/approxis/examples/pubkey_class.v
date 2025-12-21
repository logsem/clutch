From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From clutch.prob_lang Require Import advantage typing.tychk.
From clutch.approxis Require Import approxis map list option reltac2.
From clutch.approxis.examples Require Import symmetric security_aux sum_seq xor prf advantage_laws.
Set Default Proof Using "All".

Section pubkey.

(* Public key real/random chosen plaintext attack and one-time security. *)

Class ASYM_params :=
  { card_key : nat
  ; card_message : nat
  ; card_cipher : nat
  ; sym_params : val := (#card_key, #card_message, #card_cipher) }.

Context (pkey : ∀ `{!approxisRGS Σ}, lrel Σ).
Context (skey : ∀ `{!approxisRGS Σ}, lrel Σ).
Context (msg : ∀ `{!approxisRGS Σ}, lrel Σ).
Context (cipher : ∀ `{!approxisRGS Σ}, lrel Σ).

Class ASYM `{ASYM_params} := {
    keygen : val
  ; enc : val
  ; dec : val
  ; rand_cipher : val
}.

Context `{asym : ASYM}.

Context (keygen_typed : ∀ `{!approxisRGS Σ}, ⊢ REL keygen << keygen : lrel_unit → skey Σ _ * pkey _ _).
Context (enc_typed : ∀ `{!approxisRGS Σ}, ⊢ REL enc << enc : pkey _ _ → msg _ _ → cipher _ _).
Context (rand_cipher_typed : ∀ `{!approxisRGS Σ}, ⊢ REL rand_cipher << rand_cipher : msg _ _ → cipher _ _).


Definition CPA_rand (Q : Z) : expr :=
  let, ("sk", "pk") := keygen #() in
  let: "challenge" := rand_cipher in
  let: "challenge" := q_calls_poly #() #() #Q "challenge" in
  ("pk", "challenge").

Definition CPA_real (Q : Z) : expr :=
  let, ("sk", "pk") := keygen #() in
  let: "challenge" := λ:"msg", enc "pk" "msg" in
  let: "challenge" := q_calls_poly #() #() #Q "challenge" in
  ("pk", "challenge").

Definition CPA_OTS_rand := CPA_rand 1.
Definition CPA_OTS_real := CPA_real 1.

Definition hybrid (h Q : Z) : val :=
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
    ("pk", "challenge").

Definition τ_cpa `{!approxisRGS Σ} := (pkey _ _ * (msg _ _ → lrel_option (cipher _ _)))%lrel.

Lemma hybrid_typed `{!approxisRGS Σ} h Q : ⊢ REL hybrid h Q << hybrid h Q : τ_cpa → τ_cpa.
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
Qed.

Lemma enc_eta_typed `{approxisRGS Σ} pk_l pk_r :
  pkey _ _ pk_l pk_r
    ⊢ REL (λ:"msg", enc pk_l "msg")%V << (λ:"msg", enc pk_r "msg")%V : msg _ _ → cipher _ _.
Proof.
  iIntros. rel_arrow_val. iIntros. rel_pures_l ; rel_pures_r.
  repeat rel_apply refines_app. 1: iApply enc_typed. all: rel_vals.
Qed.

Lemma CPA_real_typed `{!approxisRGS Σ} Q : ⊢ REL CPA_real Q << CPA_real Q : τ_cpa.
Proof with (rel_pures_r ; rel_pures_l).
  rewrite /CPA_real...
  rel_bind_l (keygen _) ; rel_bind_r (keygen _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply keygen_typed|rel_vals].
  lrintro "sk pk"...
  rel_bind_l (q_calls_poly _ _ _ _) ; rel_bind_r (q_calls_poly _ _ _ _) ; rel_apply refines_bind.
  1: iApply q_calls_poly_sem_typed_app. 1: iApply enc_eta_typed. 1: done.
  iIntros (challenge_l challenge_r) "challenge"...
  rel_vals => //.
Qed.

Lemma CPA_rand_typed `{!approxisRGS Σ} Q : ⊢ REL CPA_rand Q << CPA_rand Q : τ_cpa.
Proof with (rel_pures_r ; rel_pures_l).
  rewrite /CPA_OTS_rand/CPA_rand...
  rel_bind_l (keygen _) ; rel_bind_r (keygen _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply keygen_typed|rel_vals].
  lrintro "sk pk"...
  rel_bind_l (q_calls_poly _ _ _ _) ; rel_bind_r (q_calls_poly _ _ _ _) ; rel_apply refines_bind.
  1: iApply q_calls_poly_sem_typed_app ; iApply rand_cipher_typed.
  iIntros (challenge_l challenge_r) "challenge"...
  rel_vals => //.
Qed.

Fact hybrid_OTS_rand_typed k Q `{!approxisRGS Σ} :
  ⊢ REL (hybrid k Q CPA_OTS_rand) << (hybrid k Q CPA_OTS_rand) : τ_cpa.
Proof.
  rel_apply refines_app. 1: iApply hybrid_typed. rewrite /CPA_OTS_rand. iApply CPA_rand_typed.
Qed.

Fact cpa_hyb_real_alt Q `{!approxisRGS Σ} :
  ⊢ REL CPA_real Q << (hybrid Q Q CPA_OTS_rand) : τ_cpa.
Proof with iredpures.
  rewrite /CPA_OTS_rand. rewrite /CPA_real/CPA_rand.
  rel_bind_l (keygen _) ; rel_bind_r (keygen _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply keygen_typed|rel_vals].
  lrintro "sk pk"...
  rewrite {2}/q_calls_poly... rel_alloc_r counter_ots as "counter_ots"...
  rewrite /hybrid... rel_alloc_r counter_hybrid as "counter_hybrid"...
  rewrite /q_calls_poly... rel_alloc_l counter_cpa as "counter_cpa"...
  iApply (refines_na_alloc ( ∃ (q : Z), counter_cpa ↦ #q ∗ counter_hybrid ↦ₛ #q ∗ (⌜q < Q⌝ -∗ counter_ots ↦ₛ #0)%Z)%I (nroot.@"pk")).
  iSplitL ; [iFrame;easy|].
  iIntros "#Hinv". rel_vals => //. iIntros (m_l m_r) "!> #m"...
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & counter_cpa & counter_hybrid & counter_ots) & Hclose)" ; ireds.
  case_bool_decide as qh...
  2:{ iApply (refines_na_close with "[-]") ; iFrame. rel_vals. }
  ireds. destruct_decide (@bool_decide_reflect (q < Q)%Z _)... 2: lia.
  iApply (refines_na_close with "[-]").
  iFrame "Hclose". iSplitL.
  { iExists (q+1)%Z. iFrame. iIntros "!> ?". iApply "counter_ots". done. }
  rel_bind_l (enc pk_l _) ; rel_bind_r (enc pk_r _) ; iApply refines_bind.
  2: iIntros (c_l c_r) "#c" => /=... 2: rel_vals.
  repeat rel_apply refines_app ; [iApply enc_typed | rel_vals..].
Qed.

Fact cpa_hyb_real_alt' Q `{!approxisRGS Σ} :
  ⊢ REL (hybrid Q Q CPA_OTS_rand) << CPA_real Q : τ_cpa.
Proof with iredpures.
  rewrite /CPA_OTS_rand. rewrite /CPA_real/CPA_rand.
  rel_bind_l (keygen _) ; rel_bind_r (keygen _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply keygen_typed|rel_vals].
  lrintro "sk pk"...
  rewrite {1}/q_calls_poly... rel_alloc_l counter_ots as "counter_ots"...
  rewrite /hybrid... rel_alloc_l counter_hybrid as "counter_hybrid"...
  rewrite /q_calls_poly... rel_alloc_r counter_cpa as "counter_cpa"...
  iApply (refines_na_alloc ( ∃ (q : Z), counter_cpa ↦ₛ #q ∗ counter_hybrid ↦ #q ∗ (⌜q < Q⌝ -∗ counter_ots ↦ #0)%Z)%I (nroot.@"pk")).
  iSplitL ; [iFrame;easy|].
  iIntros "#Hinv". rel_vals => //. iIntros (m_l m_r) "!> #m"...
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & counter_cpa & counter_hybrid & counter_ots) & Hclose)"...
  ireds. case_bool_decide as qh...
  2:{ iApply (refines_na_close with "[-]") ; iFrame. rel_vals. }
  ireds. case_bool_decide... 2: lia.
  iApply (refines_na_close with "[-]").
  iFrame "Hclose". iSplitL.
  { iExists (q+1)%Z. iFrame. iIntros "!> h". iApply "counter_ots". done. }
  rel_bind_l (enc pk_l _) ; rel_bind_r (enc pk_r _) ; iApply refines_bind.
  2: iIntros (c_l c_r) "#c" => /=... 2: rel_vals.
  repeat rel_apply refines_app. 2,3: rel_vals. iApply enc_typed.
Qed.

(* Base case for CPA_rand. *)
Fact cpa_hyb_rand_alt Q `{!approxisRGS Σ} :
  ⊢ REL CPA_rand Q << (hybrid 0 Q CPA_OTS_rand) : τ_cpa.
Proof with iredpures.
  rewrite /CPA_OTS_rand. rewrite /CPA_real/CPA_rand.
  rel_bind_l (keygen _) ; rel_bind_r (keygen _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply keygen_typed|rel_vals].
  lrintro "sk pk"...
  rewrite {2}/q_calls_poly... rel_alloc_r counter_ots as "counter_ots"...
  rewrite /hybrid... rel_alloc_r counter_hybrid as "counter_hybrid"...
  rewrite /q_calls_poly... rel_alloc_l counter_cpa as "counter_cpa"...
  iApply (refines_na_alloc ( ∃ (q : Z), counter_cpa ↦ #q ∗ counter_hybrid ↦ₛ #q ∗ (⌜q = 0⌝ -∗ counter_ots ↦ₛ #0)%Z
                                        ∗ ⌜0 <= q⌝%Z)%I (nroot.@"pk")).
  iSplitL ; [iFrame;easy|].
  iIntros "#Hinv". rel_vals => //. iIntros (m_l m_r) "!> #m"...
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & counter_cpa & counter_hybrid & counter_ots & %qpos) & Hclose)"...
  ireds. case_bool_decide as qh...
  2:{ iApply (refines_na_close with "[-]") ; iFrame. iSplitR ; [done|]. rel_vals. }
  ireds. case_bool_decide... 1: lia.
  case_bool_decide as eq_q_0...
  2:{
    iApply (refines_na_close with "[-]").
    iFrame "Hclose". iSplitL.
    { iExists (q+1)%Z. iFrame. iSplitL. 2: iPureIntro ; lia. iIntros "!> %h". lia. }
    rel_bind_l (rand_cipher _) ; rel_bind_r (rand_cipher _) ; iApply refines_bind.
    2:{ iIntros => /=... rel_vals. }
    rel_apply refines_app. 1: iApply rand_cipher_typed. rel_vals.
  }
  inversion eq_q_0 as [q0].
  iSpecialize ("counter_ots" $! eq_refl). ireds.
  iApply (refines_na_close with "[-]"). iFrame "Hclose". iSplitL.
  { iExists (q+1)%Z. subst. iFrame. iSplitL. 2: iPureIntro ; lia. iIntros "!> %h". lia. }
  rel_bind_l (rand_cipher _) ; rel_bind_r (rand_cipher _) ; iApply refines_bind.
  2:{ iIntros => /=... rel_vals. }
  rel_apply refines_app. 1: iApply rand_cipher_typed. rel_vals.
Qed.

Fact cpa_hyb_rand_alt' Q `{!approxisRGS Σ} :
  ⊢ REL (hybrid 0 Q CPA_OTS_rand) << CPA_rand Q : τ_cpa.
Proof with iredpures.
  rewrite /CPA_OTS_rand. rewrite /CPA_real/CPA_rand.
  rel_bind_l (keygen _) ; rel_bind_r (keygen _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply keygen_typed|rel_vals].
  lrintro "sk pk"...
  rewrite {1}/q_calls_poly... rel_alloc_l counter_ots as "counter_ots"...
  rewrite /hybrid... rel_alloc_l counter_hybrid as "counter_hybrid"...
  rewrite /q_calls_poly... rel_alloc_r counter_cpa as "counter_cpa"...
  iApply (refines_na_alloc ( ∃ (q : Z), counter_cpa ↦ₛ #q ∗ counter_hybrid ↦ #q ∗ (⌜q = 0⌝ -∗ counter_ots ↦ #0)%Z
                                        ∗ ⌜0 <= q⌝%Z)%I (nroot.@"pk")).
  iSplitL ; [iFrame;easy|].
  iIntros "#Hinv". rel_vals => //. iIntros (m_l m_r) "!> #m"...
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & counter_cpa & counter_hybrid & counter_ots & %qpos) & Hclose)"...
  ireds. case_bool_decide as qh...
  2:{ iApply (refines_na_close with "[-]") ; iFrame. iSplitR ; [done|]. rel_vals. }
  ireds. case_bool_decide... 1: lia.
  case_bool_decide as eq_q_0...
  2:{
    iApply (refines_na_close with "[-]"). iFrame "Hclose". iSplitL.
    { iExists (q+1)%Z. iFrame. iSplitL. 2: iPureIntro ; lia. iIntros "!> %h". lia. }
    rel_bind_l (rand_cipher _) ; rel_bind_r (rand_cipher _) ; iApply refines_bind.
    2:{ iIntros => /=... rel_vals. }
    rel_apply refines_app. 1: iApply rand_cipher_typed. rel_vals.
  }
  inversion eq_q_0 as [q0].
  iSpecialize ("counter_ots" $! eq_refl). ireds.
  iApply (refines_na_close with "[-]"). iFrame "Hclose". iSplitL.
  { iExists (q+1)%Z. subst. iFrame. iSplitL. 2: iPureIntro ; lia. iIntros "!> %h". lia. }
  rel_bind_l (rand_cipher _) ; rel_bind_r (rand_cipher _) ; iApply refines_bind.
  2:{ iIntros => /=... rel_vals. }
  rel_apply refines_app. 1: iApply rand_cipher_typed. rel_vals.
Qed.


Context (adversary : val).
Context (adversary_typed : forall `{!approxisRGS Σ}, ⊢ REL adversary << adversary : τ_cpa → lrel_bool).

Definition ε_OTS h Q b := advantage (λ:"v", adversary (hybrid h Q "v"))%V CPA_OTS_real CPA_OTS_rand #b.

Fact advantage_hybrid_OTS h Q (b : bool) :
  (advantage adversary (hybrid h Q CPA_OTS_real) (hybrid h Q CPA_OTS_rand) #b <= ε_OTS h Q b)%R.
Proof.
  apply advantage_reduction_lr. intros.
  exists τ_cpa, τ_cpa.
  intuition auto.
  - apply hybrid_typed.
  - apply CPA_real_typed.
  - apply CPA_rand_typed.
Qed.

(* Switch back from rand to real by stepping k. *)
Fact cpa_hyb_real_rand Q k (kpos : (0 <= k)%Z) `{!approxisRGS Σ} :
  ⊢ REL (hybrid k Q CPA_OTS_real) << (hybrid (k+1) Q CPA_OTS_rand) : τ_cpa.
Proof with iredpures.
  rewrite /CPA_OTS_real/CPA_real... rewrite /CPA_OTS_rand/CPA_rand...
  rel_bind_l (keygen _) ; rel_bind_r (keygen _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply keygen_typed|rel_vals].
  lrintro "sk pk"...
  rewrite {1}/q_calls_poly... rel_alloc_l counter_ots_l as "counter_ots_l"...
  rewrite {1}/hybrid... rel_alloc_l counter_hyb_l as "counter_hyb_l"...
  rewrite {1}/q_calls_poly... rel_alloc_r counter_ots_r as "counter_ots_r"...
  rewrite {1}/hybrid... rel_alloc_r counter_hyb_r as "counter_hyb_r"...
  iApply (refines_na_alloc ( ∃ (q q_ots_l q_ots_r : Z),
                (counter_hyb_l ↦ #q ∗ counter_hyb_r ↦ₛ #q
                ∗ counter_ots_l ↦ #q_ots_l ∗ counter_ots_r ↦ₛ #q_ots_r)
                ∗ (⌜ 0 <= q ∧
                     (q <= k -> (q_ots_l = 0 ∧ q_ots_r = 0)) ∧
                     (q = k+1 -> q_ots_r < 1)%Z⌝ )%Z)%I
            (nroot.@"pk")).
  iSplitL ; [iFrame|]. 1: iPureIntro ; intuition auto ; try lia.
  iIntros "#Hinv". rel_vals => //. iIntros (m_l m_r) "!> #m"...
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & %q_ots_l & %q_ots_r & (counter_cpa & counter_hybrid & counter_ots_l & counter_ots_r) & %rest) & Hclose)".
  ireds. case_bool_decide as lt_q_Q...
  2:{ iApply (refines_na_close with "[-]") ; iFrame. iSplitR. 1: done. rel_vals. }
  ireds. case_bool_decide as lt_q_k...
  - case_bool_decide as lt_q_Sk... 2: lia.
    iApply (refines_na_close with "[-]") ; iFrame.
    iSplitL ; [iFrame|]. 1: iPureIntro ; intuition auto ; try lia.
    rel_bind_l (enc pk_l _) ; rel_bind_r (enc pk_r _) ; iApply refines_bind.
    2: iIntros (c_l c_r) "#c" => /=... 2: rel_vals.
    repeat rel_apply refines_app. 2,3: rel_vals. iApply enc_typed.
  - case_bool_decide as eq_q_k...
    + inversion eq_q_k. ireds.
      destruct rest as (q_pos & xyz).
      assert (q_ots_l = 0). { apply xyz. lia. }
      case_bool_decide... 2: lia.
      case_bool_decide... 2: lia.
      ireds. iApply (refines_na_close with "[-]") ; iFrame.
      iSplitL ; [iFrame|]. 1: iPureIntro ; intuition auto ; try lia.
      rel_bind_l (enc pk_l _) ; rel_bind_r (enc pk_r _) ; iApply refines_bind.
      2: iIntros (c_l c_r) "#c" => /=... 2: rel_vals.
      repeat rel_apply refines_app. 2,3: rel_vals. iApply enc_typed.
    + assert (q ≠ k). 1: intros -> ; by apply eq_q_k.
      case_bool_decide as lt_q_Sk... 1: lia.
      case_bool_decide as eq_q_Sk...
      * ireds. destruct rest as (q_pos & ql & qr).
        inversion eq_q_Sk as [eq_q_Sk'].
        case_bool_decide as lt_q_qts_r... 2: lia.
        ireds. iApply (refines_na_close with "[-]") ; iFrame.
        iSplitL ; [iFrame|]. 1: iPureIntro ; intuition auto ; try lia.
        rel_bind_l (rand_cipher _) ; rel_bind_r (rand_cipher _) ; iApply refines_bind.
        2:{ iIntros => /=... rel_vals. }
        rel_apply refines_app. 1: iApply rand_cipher_typed. rel_vals.
      * iApply (refines_na_close with "[-]") ; iFrame.
        iSplitL ; [iFrame|]. 1: iPureIntro ; intuition auto ; try lia.
        rel_bind_l (rand_cipher _) ; rel_bind_r (rand_cipher _) ; iApply refines_bind.
        2:{ iIntros => /=... rel_vals. }
        rel_apply refines_app. 1: iApply rand_cipher_typed. rel_vals.
Qed.

(* Symmetric to above. *)
Fact cpa_hyb_real_rand' Q k (kpos : (0 <= k)%Z) `{!approxisRGS Σ} :
  ⊢ REL (hybrid (k+1) Q CPA_OTS_rand) << (hybrid k Q CPA_OTS_real) : τ_cpa.
Proof with (rel_pures_r ; rel_pures_l).
  rewrite /CPA_OTS_real/CPA_real... rewrite /CPA_OTS_rand/CPA_rand...
  rel_bind_l (keygen _) ; rel_bind_r (keygen _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply keygen_typed|rel_vals].
  lrintro "sk pk"...
  rewrite {1}/q_calls_poly... rel_alloc_l counter_ots_l as "counter_ots_l"...
  rewrite {1}/hybrid... rel_alloc_l counter_hyb_l as "counter_hyb_l"...
  rewrite {1}/q_calls_poly... rel_alloc_r counter_ots_r as "counter_ots_r"...
  rewrite {1}/hybrid... rel_alloc_r counter_hyb_r as "counter_hyb_r"...
  iApply (refines_na_alloc ( ∃ (q q_ots_l q_ots_r : Z),
                (counter_hyb_l ↦ #q ∗ counter_hyb_r ↦ₛ #q
                ∗ counter_ots_l ↦ #q_ots_l ∗ counter_ots_r ↦ₛ #q_ots_r)
                ∗ (⌜ 0 <= q ∧
                     (q <= k -> (q_ots_l = 0 ∧ q_ots_r = 0)) ∧
                     (q = k+1 -> q_ots_l < 1)%Z⌝ )%Z)%I
            (nroot.@"pk")).
  iSplitL ; [iFrame|]. 1: iPureIntro ; intuition auto ; try lia.
  iIntros "#Hinv". rel_vals => //. iIntros (m_l m_r) "!> #m"...
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & %q_ots_l & %q_ots_r & (counter_cpa & counter_hybrid & counter_ots_l & counter_ots_r) & %rest) & Hclose)".
  ireds. case_bool_decide as lt_q_Q...
  2:{ iApply (refines_na_close with "[-]") ; iFrame. iSplitR. 1: done. rel_vals. }
  ireds. destruct_decide (@bool_decide_reflect ((q < k)%Z) _) as lt_q_k...
  - case_bool_decide as lt_q_Sk... 2: lia.
    iApply (refines_na_close with "[-]") ; iFrame.
    iSplitL ; [iFrame|]. 1: iPureIntro ; intuition auto ; try lia.
    rel_bind_l (enc pk_l _) ; rel_bind_r (enc pk_r _) ; iApply refines_bind.
    2: iIntros (c_l c_r) "#c" => /=... 2: rel_vals.
    repeat rel_apply refines_app. 2,3: rel_vals. iApply enc_typed.
  - destruct_decide (@bool_decide_reflect (#q = #k) _) as eq_q_k...
    + inversion eq_q_k.
      ireds. destruct rest as (q_pos & xyz).
      assert (q_ots_l = 0). { apply xyz. lia. }
      case_bool_decide... 2: lia.
      case_bool_decide... 2: lia.
      ireds. iApply (refines_na_close with "[-]") ; iFrame.
      iSplitL ; [iFrame|]. 1: iPureIntro ; intuition auto ; try lia.
      rel_bind_l (enc pk_l _) ; rel_bind_r (enc pk_r _) ; iApply refines_bind.
      2: iIntros (c_l c_r) "#c" => /=... 2: rel_vals.
      repeat rel_apply refines_app. 2,3: rel_vals. iApply enc_typed.
    + assert (q ≠ k). 1: intros -> ; by apply eq_q_k.
      case_bool_decide as lt_q_Sk... 1: lia.
      case_bool_decide as eq_q_Sk...
      * ireds. destruct rest as (q_pos & ql & qr).
        inversion eq_q_Sk as [eq_q_Sk'].
        case_bool_decide as lt_q_qts_r... 2: lia.
        rel_load_l ; rel_store_l...
        iApply (refines_na_close with "[-]") ; iFrame.
        iSplitL ; [iFrame|]... 1: iPureIntro ; intuition auto ; try lia.
        rel_bind_l (rand_cipher _) ; rel_bind_r (rand_cipher _) ; iApply refines_bind.
        2:{ iIntros => /=... rel_vals. }
        rel_apply refines_app. 1: iApply rand_cipher_typed. rel_vals.
      * iApply (refines_na_close with "[-]") ; iFrame.
        iSplitL ; [iFrame|]... 1: iPureIntro ; intuition auto ; try lia.
        rel_bind_l (rand_cipher _) ; rel_bind_r (rand_cipher _) ; iApply refines_bind.
        2:{ iIntros => /=... rel_vals. }
        rel_apply refines_app. 1: iApply rand_cipher_typed. rel_vals.
Qed.


(* TODO define ε' instead of assuming it exists. *)
(* the fact that ε_OTS varies with Q is annoying in the proof; we can just take ε' to be the max over ε_OTS. *)

Lemma Claim_15_5_aux_alt (Q : Z) (k : nat) (b : bool) (ε' : R) (ε_max : ∀ k, (ε_OTS k Q b <= ε')%R) :
  (advantage adversary (hybrid 0 Q CPA_OTS_rand) (hybrid k Q CPA_OTS_rand) #b <= k * ε')%R.
Proof.
  intros. set (ε := ε'). induction k.
  - replace (0%nat * ε)%R with 0%R. 2: real_solver. replace (_ 0%nat) with 0%Z by lia.
    eapply lr_advantage_reflexive.
    1: apply adversary_typed. apply hybrid_OTS_rand_typed.
  - replace (S k) with (k + 1) by lia.
    replace (INR (k+1)) with (INR k + 1)%R by real_solver.
    eapply (advantage_triangle _ _ _ _ _ (k*ε) ε). 3: lra.
    1: apply IHk. clear IHk.
    replace ε with (ε+0)%R by lra.
    eapply (advantage_triangle _ _ (hybrid k Q CPA_OTS_real) _ _ ε 0%R) => //.
    { etrans. 2: apply ε_max.
      opose proof (advantage_hybrid_OTS k Q b) as bar. rewrite advantage_sym. apply bar. }
    replace (Z.of_nat (k+1)) with (k + 1)%Z by lia.
    opose proof (lr_advantage _ _ _ _ adversary_typed (@cpa_hyb_real_rand Q k _) (@cpa_hyb_real_rand' _ _ _) b)
      as step.
    1,2: lia.
    apply step.
Qed.

Lemma cpa_hyb_real_adv_alt (b : bool) Q :
  (nonneg (advantage adversary (CPA_real Q) (hybrid Q Q CPA_OTS_rand) #b) <= 0)%R.
Proof. apply (lr_advantage _ _ _ _ adversary_typed (@cpa_hyb_real_alt Q) (@cpa_hyb_real_alt' Q)). Qed.

Lemma cpa_hyb_rand_adv_alt (b : bool) Q :
  (nonneg (advantage adversary (CPA_rand Q) (hybrid 0 Q CPA_OTS_rand) #b) <= 0)%R.
Proof. apply (lr_advantage _ _ _ _ adversary_typed (@cpa_hyb_rand_alt Q) (@cpa_hyb_rand_alt' Q)). Qed.

Lemma Claim_15_5 (Q : nat) (b : bool) (ε' : R) (ε_max : ∀ k, (ε_OTS k Q b <= ε')%R) :
    (advantage adversary (CPA_real Q) (CPA_rand Q) #b <= Q * ε')%R.
Proof.
  intros.
  eapply advantage_triangle.
  1: apply cpa_hyb_real_adv_alt.
  1: eapply advantage_triangle.
  2: rewrite advantage_sym.
  2: apply cpa_hyb_rand_adv_alt.
  1: rewrite advantage_sym.
  1: apply Claim_15_5_aux_alt.
  1: apply ε_max.
  1: reflexivity. field_simplify. reflexivity.
Qed.

End pubkey.
