From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From clutch.prob_lang Require Import advantage typing.tychk.
From clutch.approxis Require Import approxis map list option.
From clutch.approxis.examples Require Import symmetric security_aux sum_seq xor prf advantage_laws.
Set Default Proof Using "All".


Section pubkey.

(* Public key OTS-CPA$ security (one-time secrecy chosen plaintext attack -
   real/random). *)

(* Definition rand_cipher := λ:"msg",
       let: "b" := rnd #() in
       let: "x" := rnd #() in
       let, ("B", "X") := (g^"b", g^"x") in
       ("B", "X"). *)

(* Context `{!approxisRGS Σ}. *)

Context (pkey : ∀ `{!approxisRGS Σ}, lrel Σ).
Context (skey : ∀ `{!approxisRGS Σ}, lrel Σ).
Context (msg : ∀ `{!approxisRGS Σ}, lrel Σ).
Context (cipher : ∀ `{!approxisRGS Σ}, lrel Σ).

Context (keygen : val).
Context (enc : val).
Context (rand_cipher : val).

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
  let: "challenge" := enc "pk" in
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
        if: (! "counter" < #Q) then
          "counter" <- !"counter" + #1 ;;
          if: (! "counter" < #h) then
            SOME (enc "pk" "msg")
          else if: (! "counter" = #h) then
                 "challenge" "msg"
               else SOME (rand_cipher "msg")
        else NONE

        (* if: (! "counter" < #h)
           then SOME (enc "pk" "msg")
           else if: (! "counter" = #h) then
                  ("challenge" "msg")
                else if: (! "counter" < #Q)
                     then SOME (rand_cipher "msg")
                     else NONE *)

    in
    ("pk", "challenge").

Definition τ_cpa `{!approxisRGS Σ} := (pkey _ _ * (msg _ _ → lrel_option (cipher _ _)))%lrel.

Lemma hybrid_typed `{!approxisRGS Σ} h Q : ⊢ REL hybrid h Q << hybrid h Q : τ_cpa → τ_cpa.
Proof with (rel_pures_r ; rel_pures_l).
  rel_arrow_val.
  rewrite /τ_cpa.
  lrintro "pk challenge".
  rewrite /hybrid...
  rel_alloc_l counter_l as "counter_l" ; rel_alloc_r counter_r as "counter_r"...
  iApply (refines_na_alloc ( ∃ (q : Z), counter_l ↦ #q ∗ counter_r ↦ₛ #q)%I
            (nroot.@"pk")).
  iSplitL ; [iFrame|].
  iIntros "#Hinv".
  rel_vals => //.
  iIntros (m_l m_r) "!> #m"...
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & counter_l & counter_r) & Hclose)".
  rel_load_l ; rel_load_r...

  destruct_decide (@bool_decide_reflect ((q < Q)%Z) _) as qQ...
  - rel_load_l ; rel_load_r ; rel_store_l ; rel_store_r ; rel_load_l ; rel_load_r...
    destruct_decide (@bool_decide_reflect (q+1 < h)%Z _) as qh...
    + iApply (refines_na_close with "[-]") ; iFrame.
      rel_bind_l (enc _ _) ; rel_bind_r (enc _ _) ; iApply refines_bind.
      2:{ iIntros => /=... rel_vals. }
      repeat rel_apply refines_app => //. 2,3: rel_vals.
      iApply enc_typed.
    + rel_load_l ; rel_load_r...
      destruct_decide (@bool_decide_reflect (#(q+1) = #h)%Z _) as qh'...
      * iApply (refines_na_close with "[-]") ; iFrame.
      rel_bind_l (challenge_l _) ; rel_bind_r (challenge_r _) ; iApply refines_bind.
      2:{ iIntros => /=... rel_vals. }
      by iApply "challenge".
      * iApply (refines_na_close with "[-]") ; iFrame.
        rel_bind_l (rand_cipher _) ; rel_bind_r (rand_cipher _) ; iApply refines_bind.
        2:{ iIntros => /=... rel_vals. }
        rel_apply refines_app.
        1: iApply rand_cipher_typed.
        rel_vals.
  - iApply (refines_na_close with "[-]") ; iFrame.
    rel_vals.
Qed.

Lemma CPA_real_typed `{!approxisRGS Σ} Q : ⊢ REL CPA_real Q << CPA_real Q : τ_cpa.
Proof with (rel_pures_r ; rel_pures_l).
  rewrite /CPA_real...
  rel_bind_l (keygen _) ; rel_bind_r (keygen _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply keygen_typed|rel_vals].
  lrintro "sk pk"...
  rel_bind_l (enc _) ; rel_bind_r (enc _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply enc_typed|rel_vals].
  iIntros (m_l m_r) "#m"...
  rel_bind_l (q_calls_poly _ _ _ _) ; rel_bind_r (q_calls_poly _ _ _ _) ; rel_apply refines_bind.
  1: iApply q_calls_poly_sem_typed_app ; rel_vals.
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

(* Base case for CPA_real. *)
Fact cpa_hyb_real Q `{!approxisRGS Σ} :
  ⊢ REL CPA_real Q << (hybrid Q Q CPA_OTS_real) : τ_cpa.
Proof with (rel_pures_r ; rel_pures_l).
  rewrite /CPA_OTS_real. rewrite /CPA_real.
  rel_bind_l (keygen _) ; rel_bind_r (keygen _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply keygen_typed|rel_vals].
  lrintro "sk pk"...
  rel_bind_l (enc _) ; rel_bind_r (enc _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply enc_typed|rel_vals].
  iIntros (enc_pk_l enc_pk_r) "#enc_pk"...
  rewrite {2}/q_calls_poly...
  rel_alloc_r counter_ots as "counter_ots"...
  rewrite /hybrid...
  rel_alloc_r counter_hybrid as "counter_hybrid"...
  rewrite /q_calls_poly... rel_alloc_l counter_cpa as "counter_cpa"...

  iApply (refines_na_alloc ( ∃ (q : Z), counter_cpa ↦ #q ∗ counter_hybrid ↦ₛ #q
                                          ∗ (⌜q < Q⌝ -∗ counter_ots ↦ₛ #0)%Z
            )%I
            (nroot.@"pk")).
  iSplitL ; [iFrame;easy|].
  iIntros "#Hinv".
  rel_vals => //.
  iIntros (m_l m_r) "!> #m"...
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & counter_cpa & counter_hybrid & counter_ots) & Hclose)"...
  rel_load_l ; rel_load_r...
  set (h := Q).
  destruct_decide (@bool_decide_reflect (q < h)%Z _) as qh...
  2:{ iApply (refines_na_close with "[-]") ; iFrame.
      rel_vals. }
  rel_load_l ; rel_load_r ; rel_store_l ; rel_store_r ; rel_load_r...
  destruct_decide (@bool_decide_reflect (q+1 < h)%Z _) as Sqh...
  - iApply (refines_na_close with "[-]").
    iFrame "Hclose". iSplitL.
    { iExists (q+1)%Z. iFrame.
      iIntros "!> h". iApply "counter_ots". iPureIntro. lia. }
    rel_bind_l (enc_pk_l _) ; rel_bind_r (enc pk_r _) ; iApply refines_bind.
    2: iIntros (c_l c_r) "#c" => /=... 2: rel_vals.
    iSpecialize ("enc_pk" with "m").
    (* TODO what to do with enc_pk here? *)
    admit.
  - rel_load_r... destruct_decide (@bool_decide_reflect (#(q+1) = #h)%Z _) as qh'...
    2:{ subst h.
        exfalso. assert (q+1 = Q -> False)%Z as SqQ. { intros <-. apply qh'. done. }
        apply SqQ. lia. }
    iSpecialize ("counter_ots" $! qh).
    rel_load_r... rel_load_r ; rel_store_r...
    iApply (refines_na_close with "[-]") ; iFrame...
    iSplitL.
    { iIntros "!> %". done. }
    rel_bind_l (enc_pk_l _) ; rel_bind_r (enc_pk_r _) ; iApply refines_bind.
    1: iApply "enc_pk" => //.
    iIntros (c_l c_r) "#c" => /=...
    rel_vals.
Admitted.

(* just symmetry *)
Fact cpa_hyb_real' Q `{!approxisRGS Σ} :
  ⊢ REL (hybrid Q Q CPA_OTS_real) << CPA_real Q : τ_cpa.
Admitted.

Fact cpa_hyb_rand Q `{!approxisRGS Σ} :
  ⊢ REL CPA_rand Q << (hybrid 0 Q CPA_OTS_rand) : τ_cpa.
Proof with (rel_pures_r ; rel_pures_l).
  rewrite /CPA_OTS_rand. rewrite /CPA_rand.
  rel_bind_l (keygen _) ; rel_bind_r (keygen _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply keygen_typed|rel_vals].
  lrintro "sk pk"...
  rewrite {2}/q_calls_poly...
  rel_alloc_r counter_ots as "counter_ots"...
  rewrite /hybrid...
  rel_alloc_r counter_hybrid as "counter_hybrid"...
  rewrite /q_calls_poly... rel_alloc_l counter_cpa as "counter_cpa"...

  iApply (refines_na_alloc ( ∃ (q : Z), ⌜0 <= q⌝%Z ∗ counter_cpa ↦ #q ∗ counter_hybrid ↦ₛ #q
                                          ∗ (⌜q = 0⌝ -∗ counter_ots ↦ₛ #0)%Z)%I
            (nroot.@"pk")).
  iSplitL ; [iFrame;easy|].
  iIntros "#Hinv".
  rel_vals => //.
  iIntros (m_l m_r) "!> #m"...
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & %qpos & counter_cpa & counter_hybrid & counter_ots) & Hclose)"...
  rel_load_l ; rel_load_r...
  set (h := 0%Z).
  destruct_decide (@bool_decide_reflect (q < Q)%Z _) as qh...
  2:{ iApply (refines_na_close with "[-]") ; iFrame. iSplitR. 1: done.
      rel_vals. }
  rel_load_l ; rel_load_r ; rel_store_l ; rel_store_r ; rel_load_r...
  destruct_decide (@bool_decide_reflect (q+1 < h)%Z _) as Sqh...
  - iApply (refines_na_close with "[-]").
    iFrame "Hclose". iSplitL.
    { iExists (q+1)%Z. iFrame. iSplitR. 1: iPureIntro ; lia.
      iIntros "!> %hh". lia. }
    exfalso. lia.
  - rel_load_r... destruct_decide (@bool_decide_reflect (#(q+1) = #h)%Z _) as qh'...
    2:{ subst h.
        iApply (refines_na_close with "[-]") ; iFrame "Hclose"...
        iSplitL.
        { iIntros "!>". iExists (q+1)%Z. iFrame. iSplitR. 1: iPureIntro ; lia.
          iIntros "%hh". lia. }
        rel_bind_l (rand_cipher _) ; rel_bind_r (rand_cipher _) ; iApply refines_bind.
        2:{ iIntros => /=... rel_vals. }
        rel_apply refines_app.
        1: iApply rand_cipher_typed.
        rel_vals.
    }
    subst h.
    inversion qh'. lia.
Qed.

Fact cpa_hyb_rand' Q `{!approxisRGS Σ} :
  ⊢ REL (hybrid 0 Q CPA_OTS_rand) << CPA_rand Q : τ_cpa.
Proof with (rel_pures_r ; rel_pures_l).
  rewrite /CPA_OTS_rand. rewrite /CPA_rand.
  rel_bind_l (keygen _) ; rel_bind_r (keygen _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply keygen_typed|rel_vals].
  lrintro "sk pk"...
  rewrite {1}/q_calls_poly...
  rel_alloc_l counter_ots as "counter_ots"...
  rewrite /hybrid...
  rel_alloc_l counter_hybrid as "counter_hybrid"...
  rewrite /q_calls_poly... rel_alloc_r counter_cpa as "counter_cpa"...

  iApply (refines_na_alloc ( ∃ (q : Z), ⌜0 <= q⌝%Z ∗ counter_cpa ↦ₛ #q ∗ counter_hybrid ↦ #q
                                          ∗ (⌜q = 0⌝ -∗ counter_ots ↦ #0)%Z)%I
            (nroot.@"pk")).
  iSplitL ; [iFrame;easy|].
  iIntros "#Hinv".
  rel_vals => //.
  iIntros (m_l m_r) "!> #m"...
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "(> (%q & %qpos & counter_cpa & counter_hybrid & counter_ots) & Hclose)"...
  rel_load_l ; rel_load_r...
  set (h := 0%Z).
  destruct_decide (@bool_decide_reflect (q < Q)%Z _) as qh...
  2:{ iApply (refines_na_close with "[-]") ; iFrame. iSplitR. 1: done.
      rel_vals. }
  rel_load_l ; rel_load_r ; rel_store_l ; rel_store_r ; rel_load_l...
  destruct_decide (@bool_decide_reflect (q+1 < h)%Z _) as Sqh...
  - iApply (refines_na_close with "[-]").
    iFrame "Hclose". iSplitL.
    { iExists (q+1)%Z. iFrame. iSplitR. 1: iPureIntro ; lia.
      iIntros "!> %hh". lia. }
    exfalso. lia.
  - rel_load_l... destruct_decide (@bool_decide_reflect (#(q+1) = #h)%Z _) as qh'...
    2:{ subst h.
        iApply (refines_na_close with "[-]") ; iFrame "Hclose"...
        iSplitL.
        { iIntros "!>". iExists (q+1)%Z. iFrame. iSplitR. 1: iPureIntro ; lia.
          iIntros "%hh". lia. }
        rel_bind_l (rand_cipher _) ; rel_bind_r (rand_cipher _) ; iApply refines_bind.
        2:{ iIntros => /=... rel_vals. }
        rel_apply refines_app.
        1: iApply rand_cipher_typed.
        rel_vals.
    }
    subst h.
    inversion qh'. lia.
Qed.

Context (adversary : val).
Context (adversary_typed : forall `{!approxisRGS Σ}, ⊢ REL adversary << adversary : τ_cpa → lrel_bool).

Definition ε_OTS h Q b := advantage (λ:"v", adversary (hybrid h Q "v")) CPA_OTS_real CPA_OTS_rand #b.

Fact foo h Q (b : bool) :
  (advantage adversary (hybrid h Q CPA_OTS_real) (hybrid h Q CPA_OTS_rand) #b <= ε_OTS h Q b)%R.
Proof with (rel_pures_r ; rel_pures_l).
  apply advantage_reduction_lr. intros.
  exists τ_cpa, τ_cpa.
  intuition auto.
  - apply hybrid_typed.
  - apply CPA_real_typed.
  - apply CPA_rand_typed.
Qed.

(* Switch back from rand to real by stepping k. *)
(* TODO prove one of these *)
Fact cpa_hyb_real_rand Q k `{!approxisRGS Σ} :
  ⊢ REL (hybrid k Q CPA_OTS_rand) << (hybrid (k+1) Q CPA_OTS_real) : τ_cpa.
Proof with (rel_pures_r ; rel_pures_l).
  rewrite /CPA_OTS_real/CPA_real...
  rewrite /CPA_OTS_rand/CPA_rand...
  rel_bind_l (keygen _) ; rel_bind_r (keygen _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply keygen_typed|rel_vals].
  lrintro "sk pk"...
  rewrite {1}/q_calls_poly...
  rel_alloc_l counter_ots_l as "counter_ots_l"...
  rewrite {1}/hybrid...
  rel_alloc_l counter_hyb_l as "counter_hyb_l"...
  (* how to progress with enc pk_r on the right? *)
Admitted.

(* Symmetric to above. *)
Fact cpa_hyb_real_rand' Q k `{!approxisRGS Σ} :
  ⊢ REL (hybrid (k+1) Q CPA_OTS_real) << (hybrid k Q CPA_OTS_rand) : τ_cpa.
Admitted.

(* TODO prove one of these *)
Lemma induction_base_lr Q `{!approxisRGS Σ} :
  ⊢ REL (hybrid 0 Q CPA_OTS_real) << (hybrid 0 Q CPA_OTS_rand) : τ_cpa.
Proof with (rel_pures_r ; rel_pures_l).
  rewrite /CPA_OTS_real/CPA_real...
  rewrite /CPA_OTS_rand/CPA_rand...
  rel_bind_l (keygen _) ; rel_bind_r (keygen _) ; iApply refines_bind => /=.
  1: rel_apply refines_app ; [iApply keygen_typed|rel_vals].
  lrintro "sk pk"...
  (* Same problem with enc pk_l as above. *)
Admitted.

(* symmetric *)
Lemma induction_base_lr' Q `{!approxisRGS Σ} :
  ⊢ REL (hybrid 0 Q CPA_OTS_rand) << (hybrid 0 Q CPA_OTS_real) : τ_cpa.
Admitted.

Lemma induction_base Q (b : bool) :
  (nonneg (advantage adversary (hybrid 0 Q CPA_OTS_real) (hybrid 0 Q CPA_OTS_rand) #b) <= 0)%R.
Proof. eapply (lr_advantage _ _ _ _ adversary_typed (@induction_base_lr Q) (@induction_base_lr' Q)). Qed.

(* TODO define ε' instead of assuming it exists. *)
(* the fact that ε_OTS varies with Q is annoying in the proof; we can just take ε' to be the max over ε_OTS. *)
Variable ε' : forall (Q : Z) (b : bool), R.
Hypothesis (ε_max : forall Q (b : bool) k, (ε_OTS k Q b <= ε' Q b)%R).


Lemma Claim_15_5_aux (Q : Z) (k : nat) (b : bool) :
  (advantage adversary (hybrid k Q CPA_OTS_real) (hybrid 0 Q CPA_OTS_rand) #b
   <= k * ε' Q b)%R.
Proof.
  intros. set (ε := ε' Q b). induction k.
  - replace (0%nat * ε)%R with 0%R by real_solver. 1: eapply induction_base.
  - replace (S k) with (k + 1) by lia.
    replace (INR (k+1)) with (INR k + 1)%R by real_solver.
    eapply (advantage_triangle _ _ _ _ _ ε (k*ε)). 3: lra.
    2: apply IHk. clear IHk.
    opose proof (lr_advantage _ _ _ _ adversary_typed (@cpa_hyb_real_rand' _ _) (@cpa_hyb_real_rand _ _) b)
      as step.
    replace ε with (0+ε)%R by lra.
    eapply advantage_triangle. 3: reflexivity.
    2:{ etrans. 2: apply ε_max.
        opose proof (foo k Q b) as bar. rewrite advantage_sym in bar. apply bar. }
    replace (Z.of_nat (k+1)) with (k + 1)%Z by lia.
    apply step.
Qed.


Lemma cpa_hyb_real_adv (b : bool) Q :
  (nonneg (advantage adversary (CPA_real Q) (hybrid Q Q CPA_OTS_real) #b) <= 0)%R.
Proof. eapply (lr_advantage _ _ _ _ adversary_typed (@cpa_hyb_real Q) (@cpa_hyb_real' Q)). Qed.

Lemma cpa_hyb_rand_adv (b : bool) Q :
  (nonneg (advantage adversary (hybrid 0 Q CPA_OTS_rand) (CPA_rand Q) #b) <= 0)%R.
Proof. eapply (lr_advantage _ _ _ _ adversary_typed (@cpa_hyb_rand' Q) (@cpa_hyb_rand Q)). Qed.

Lemma Claim_15_5 (Q : nat) (b : bool) :
    (advantage adversary (CPA_real Q) (CPA_rand Q) #b <= Q * ε' Q b)%R.
Proof.
  intros.
  eapply advantage_triangle.
  1: apply cpa_hyb_real_adv.
  1: eapply advantage_triangle.
  2: apply cpa_hyb_rand_adv.
  1: apply Claim_15_5_aux.
  1: reflexivity. field_simplify. done.
Qed.


(* A CPA_real ~ A (hybrid Q Q CPA_OTS.real)

   A (hybrid h Q CPA_OTS.real) ~ A (hybrid h Q CPA_OTS.rand)
   because
   A (hybrid h Q CPA_OTS.real)
   =   (A ∘ hybrid h Q) CPA_OTS.real
   ~ε~ (A ∘ hybrid h Q) CPA_OTS.rand
   =   A (hybrid h Q CPA_OTS.rand)

   where ε = adv (A ∘ hybrid h Q) CPA_OTS.real CPA_OTS.rand
   although this should also hold for
   ε' = adv A CPA_OTS.real CPA_OTS.rand
   since (A ∘ hybrid h Q) can't distinguish the games except at the h-th query.
   In other words, it should be possible to prove ε = ε'.
   But even ε is an advantage against a single-time security game, so maybe that's good enough. *)

End pubkey.
