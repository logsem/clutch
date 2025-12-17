(* CPA security of a PRF based symmetric encryption scheme. *)
From clutch.approxis Require Import approxis map list.
From clutch.approxis.examples Require Import symmetric_init security_aux option xor.
From clutch.approxis.examples Require prf_local_state.
Set Default Proof Using "Type*".

Section defs.

  (** We will prove CPA security xof a symmetric encryption scheme based on an
  (idealised) PRF.

References for the encryption scheme:
- Definition 7.4, Mike Rosulek, 2020, The Joy of Cryptography.
- Construction 3.28, Jonathan Katz and Yehuda Lindell, 2021, Introduction to Modern Cryptography (3rd edition).

References for the CPA security proof:
- Claim 7.5, Mike Rosulek, 2020, The Joy of Cryptography.
- Theorem 3.29, Jonathan Katz and Yehuda Lindell, 2021, Introduction to Modern Cryptography (3rd edition).

We prove the portions of the above theorems that are concerned with the reduction after the PRF is replaced with the idealised PRF.
*)

  (** Parameters of the PRF. *)
  Variable Key : nat.
  Variable Input : nat.
  Variable Output : nat.

  Local Instance prf_params : prf_local_state.PRF_localstate_params := {|
      prf_local_state.card_key := Key
    ; prf_local_state.card_input := Input
    ; prf_local_state.card_output := Output
  |}.

  Let Message := Output.
  Let Cipher := Input * Output.

  Local Opaque INR.

  (** Parameters of the generic PRF-based encryption scheme. *)
  Variable xor_struct : XOR (Key := Message) (Support := Output).

  (** Generic PRF-based symmetric encryption. *)
  Definition prf_enc : val :=
    λ:"prf" "key",
      let: "prf_key" := "prf" "key" in
      λ: "msg",
        let: "r" := rand #Input in
        let: "z" := "prf_key" "r" in
        ("r", xor "msg" "z").

  Definition prf_dec : val :=
    λ:"prf" "key",
      let: "prf_key" := "prf" "key" in
      λ: "cipher",
        let: "r" := Fst "cipher" in
        let: "c" := Snd "cipher" in
        let: "z" := "prf_key" "r" in
        xor "c" "z".

  (** We specialize the construction to an idealized random function family. *)
  Definition rf_keygen : val := λ:<>, rand #Key.
  Definition rf_enc : val :=
    λ: "mapref" "key", prf_enc (λ:<>, prf_local_state.random_function "mapref" #Output) "key".
  Definition rf_rand_cipher : val :=
    λ:<>, let:"i" := rand #Input in let:"o" := rand #Output in ("i", "o").
  Definition rf_dec : val :=
    λ: "mapref" "key", prf_dec (λ:<>, prf_local_state.random_function "mapref" #Output) "key".
  
  Definition rf_scheme : expr :=
    let: "mapref" := init_map #() in
    (rf_enc "mapref", rf_dec "mapref").
  #[local] Instance SYM_param : SYM_init_params :=
    {| card_key := Key ; card_message := Message ; card_cipher := Cipher |}.

  #[local] Instance sym_rf_scheme : SYM_init :=
    {|  keygen := rf_keygen
      ; enc_scheme := rf_scheme
      ; rand_cipher := rf_rand_cipher |}.

  (** RandML types of the scheme. *)
  Definition TMessage := TInt.
  Definition TKey := TInt.
  Definition TInput := TInt.
  Definition TOutput := TInt.
  Definition TCipher := (TInput * TMessage)%ty.

  Section Correctness.
    Context `{!approxisRGS Σ}.
    Variable xor_spec : XOR_spec.

    Lemma prf_enc_sem_typed (HleInOut : Input ≤ Output) : ⊢
      REL prf_enc <<
        prf_enc :
          (lrel_int → prf_local_state.lrel_input → prf_local_state.lrel_output) →
          lrel_int → prf_local_state.lrel_input →
            lrel_int * lrel_int.
    Proof with rel_pures_l; rel_pures_r.
      rewrite /prf_enc... rel_arrow_val.
      iIntros (prf1 prf2) "#H"...
      rel_arrow_val.
      iIntros (v1 v2 [x [eq1 eq2]]); subst...
      rel_bind_l (prf1 _); rel_bind_r (prf2 _).
      rel_apply (refines_bind _ _ _ (prf_local_state.lrel_input → prf_local_state.lrel_output)).
      { rel_apply "H". rewrite /lrel_car. simpl. iExists _. done. }
      clear x; iIntros (prfkeyed1 prfkeyed2) "#H'"...
      rel_arrow_val.
      iIntros (v1 v2 [msg [eq1 [eq2 ineqmsg]]]); subst...
      rel_apply refines_couple_UU; first done.
      iIntros (n Hbound). iModIntro...
      rel_bind_l (prfkeyed1 _); rel_bind_r (prfkeyed2 _).
      rel_apply refines_bind.
      - rel_apply "H'". iPureIntro.
        exists n. repeat split; try done; try (rewrite /card_input; rewrite /dummy_prf_params); try lia.
        rewrite /prf_local_state.card_input. simpl. lia.
      - iIntros (v v' [x [eq1 [eq2 ineq]]]); subst...
        rel_apply refines_pair; first rel_values.
        rewrite /prf_local_state.card_input in ineqmsg. simpl in ineqmsg.
        rewrite /prf_local_state.card_output in ineq. simpl in ineq.
        replace x with (Z.of_nat (Z.to_nat x)) by lia.
        rel_apply_l (xor_correct_l ⊤ []); try lia.
        rel_apply_r (xor_correct_r ⊤ []); try lia.
        rel_values.
    Qed.

    Lemma rf_enc_sem_typed_applied (HleInOut : Input ≤ Output) lm lm' M :
        map_list lm M ∗ map_slist lm' M
      ∗ ⌜ ∀ y, y ∈ @map_img nat val (gmap nat val) _ (gset val) _ _ _ M
          → ∃ k : nat, y = #k ∧ k <= prf_local_state.card_output ⌝
      ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S prf_local_state.card_input)%nat ⌝ ⊢
      REL prf_enc (λ: <>, prf_local_state.random_function #lm #prf_local_state.card_output)%V <<
      prf_enc (λ: <>, prf_local_state.random_function #lm' #prf_local_state.card_output)%V :
          lrel_int → prf_local_state.lrel_input → lrel_int * lrel_int.
    Proof with rel_pures_l; rel_pures_r.
      iIntros "[Hmap [Hmap' [%Himg %Hdom]]]".
      rewrite /rf_enc...
      set (P := ( ∃ (M : gmap nat val),
                      map_list  lm  M
                    ∗ map_slist lm' M
                    ∗ ⌜ ∀ y, y ∈ @map_img nat val (gmap nat val) _ (gset val) _ _ _ M
                            → ∃ k : nat, y = #k ∧ k <= prf_local_state.card_output ⌝
                    ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S prf_local_state.card_input)%nat ⌝
                )%I).
      rel_apply (refines_na_alloc P
        (nroot.@"RED") with "[Hmap Hmap']") ; iFrame.
      iSplitL. { iPureIntro. split; assumption. }
      iIntros "#Hinv".
      repeat rel_apply refines_app.
      - rel_apply prf_enc_sem_typed. assumption. 
      - rel_arrow_val. lrintro "tmp"...
        rel_apply prf_local_state.random_function_sem_typed_inv; last iAssumption.
        exists True%I. rewrite /P.
        apply bi.equiv_entails; split;
        [iIntros "HP"; iSplitR; first done | iIntros "[_ HP]"];
        iAssumption.
    Qed.
    

    Lemma rf_enc_sem_typed (HleInOut : Input ≤ Output) lm lm' M :
        map_list lm M ∗ map_slist lm' M
      ∗ ⌜ ∀ y, y ∈ @map_img nat val (gmap nat val) _ (gset val) _ _ _ M
          → ∃ k : nat, y = #k ∧ k <= prf_local_state.card_output ⌝
      ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S prf_local_state.card_input)%nat ⌝ ⊢
      REL rf_enc #lm <<
        rf_enc #lm' :
          lrel_int → prf_local_state.lrel_input → lrel_int * lrel_int.
    Proof with rel_pures_l; rel_pures_r.
      iIntros "[Hmap [Hmap' [%Himg %Hdom]]]".
      rewrite /rf_enc...
      set (P := ( ∃ (M : gmap nat val),
                      map_list  lm  M
                    ∗ map_slist lm' M
                    ∗ ⌜ ∀ y, y ∈ @map_img nat val (gmap nat val) _ (gset val) _ _ _ M
                            → ∃ k : nat, y = #k ∧ k <= prf_local_state.card_output ⌝
                    ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S prf_local_state.card_input)%nat ⌝
                )%I).
      rel_apply (refines_na_alloc P
        (nroot.@"RED") with "[Hmap Hmap']") ; iFrame.
      iSplitL. { iPureIntro. split; assumption. }
      iIntros "#Hinv".
      rel_arrow_val.
      iIntros (v1 v2 [x [eq1 eq2]]); subst...
      repeat rel_apply refines_app.
      - rel_apply prf_enc_sem_typed. assumption. 
      - rel_arrow_val. clear x. lrintro "tmp"...
        rel_apply prf_local_state.random_function_sem_typed_inv; last iAssumption.
        exists True%I. rewrite /P.
        apply bi.equiv_entails; split;
        [iIntros "HP"; iSplitR; first done | iIntros "[_ HP]"];
        iAssumption.
      - rel_vals.
    Qed.

    Theorem rf_scheme_correct lm M :
        map_list lm M
      ∗ ⌜ ∀ y, y ∈ @map_img nat val (gmap nat val) _ (gset val) _ _ _ M
          → ∃ k : nat, y = #k ∧ k <= prf_local_state.card_output ⌝
      ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S prf_local_state.card_input)%nat ⌝
      ⊢ refines top
        (let: "rf_dec" := (rf_enc #lm, rf_dec #lm) in
        let: "rf_enc" := Fst "rf_dec" in
        let: "rf_dec" := Snd "rf_dec" in
        let: "k" := rf_keygen #() in
        λ: "msg",
          "rf_dec" "k" ("rf_enc" "k" "msg"))
        (λ: "msg", "msg") (prf_local_state.lrel_output → prf_local_state.lrel_output).
    Proof with rel_pures_l; rel_pures_r.
      iIntros "[Hmap [%Himg %Hdom]]".
      rewrite /rf_enc/rf_dec...
      set (P :=
        (∃ M, map_list lm M
        ∗ ⌜ ∀ y, y ∈ @map_img nat val (gmap nat val) _ (gset val) _ _ _ M
            → ∃ k : nat, y = #k ∧ k <= Output ⌝
        ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S Input)%nat ⌝
      )%I).
      rel_apply (refines_na_alloc P (nroot.@"rf_scheme_correc"));
      iFrame. iSplitR; first (iPureIntro; split; assumption).
      iIntros "#Inv".
      rewrite /rf_keygen...
      rel_apply refines_randU_l.
      iIntros (k Hkbound)...
      rel_arrow_val.
      iIntros (v1 v2 [msg [eq1 [eq2 Hmsgbound]]]); subst...
      rewrite /prf_local_state.card_input in Hmsgbound. simpl in Hmsgbound.
      rewrite /prf_enc...
      rewrite /prf_local_state.random_function...
      rewrite -/prf_local_state.random_function. clear Himg Hdom M.
      rel_apply refines_na_inv; iSplitL; first iAssumption.
      iIntros "[[%M >[Hmap [%Himg %Hdom]]] Hclose]".
      rel_apply refines_randU_l.
      iIntros (r Hrbound)...
      rel_apply (refines_get_l with "[-Hmap]"); last iAssumption.
      iIntros (z) "Hmap %Hz"; subst.
      destruct (M !! r) as [y |] eqn:eq; simpl...
      - eapply elem_of_map_img_2 in eq as Hy.
        apply Himg in Hy as [z [eqyz Hzbound]]; subst...
        rewrite /prf_local_state.card_output in Hzbound. simpl in Hzbound.
        rel_bind_l (xor _ _).
        replace msg with (Z.of_nat (Z.to_nat msg)) by lia.
        rel_apply xor_correct_l; try lia.
        rewrite /prf_dec...
        rewrite /prf_local_state.random_function...
        rel_apply (refines_get_l with "[-Hmap]"); last by iAssumption.
        iIntros (tmpres) "Hmap %eq'".
        rewrite eq in eq'. simpl in eq'. subst...
        assert (xor_ineq : Z.to_nat (xor_sem (Z.to_nat msg) z) < S Message)
          by (rewrite Nat2Z.id; apply xor_dom; lia).
        rel_apply xor_correct_l; try lia.
        { rewrite Z2Nat.id; lia. }
        rel_apply refines_na_close; iFrame; iFrame; iSplitR;
        first (iPureIntro; split; assumption).
        rel_vals. iExists _.
        iPureIntro. repeat split.
        * rewrite Nat2Z.id. rewrite xor_sem_inverse_r; try lia; symmetry.
          rewrite Z2Nat.id; try lia. reflexivity.
        * apply Nat2Z.is_nonneg.
        * rewrite /prf_local_state.card_input; simpl.
          apply inj_le.
          apply PeanoNat.lt_n_Sm_le.
          apply xor_dom; last lia.
          rewrite Nat2Z.id. apply xor_dom; lia.
      - rel_apply refines_randU_l.
        iIntros (z Hzbound)...
        rel_apply (refines_set_l with "[-Hmap]"); last iAssumption.
        iIntros "Hmap"...
        replace msg with (Z.of_nat (Z.to_nat msg)) by lia.
        rel_apply xor_correct_l; try lia...
        rewrite /prf_dec...
        rewrite /prf_local_state.random_function...
        rel_apply (refines_get_l with "[-Hmap]"); last iAssumption.
        iIntros (tmpres) "Hmap %Hreseq".
        rewrite lookup_insert in Hreseq.
        simpl in Hreseq. subst...
        assert (xor_ineq : Z.to_nat (xor_sem (Z.to_nat msg) z) < S Message)
          by (rewrite Nat2Z.id; apply xor_dom; lia).
        rel_apply xor_correct_l; try (rewrite Nat2Z.id; apply xor_dom); try lia.
        rel_apply refines_na_close; iFrame; iFrame; iSplitR.
        {
          iPureIntro. split.
          - intros y Hy. apply map_img_insert in Hy.
            rewrite elem_of_union in Hy. destruct Hy as [Heq | Hy].
            + rewrite elem_of_singleton in Heq; subst.
              exists z; split; done.
            + apply Himg. 
              eapply map_img_delete_subseteq. apply Hy.
          - intros x Hx. rewrite dom_insert in Hx. rewrite elem_of_elements in Hx.
            rewrite elem_of_union in Hx. destruct Hx as [Hxeq | Hx].
            + rewrite elem_of_singleton in Hxeq; subst.
              rewrite /prf_local_state.card_input. simpl. rewrite /Message.
              eapply Nat.le_lt_trans; first apply Hrbound. lia.
            + apply Hdom. apply elem_of_elements. apply Hx.
        }
        rel_vals. iExists _.
        iPureIntro. repeat split.
        * rewrite Nat2Z.id. rewrite xor_sem_inverse_r; try lia. symmetry.
          rewrite Nat2Z.id. reflexivity.
        * apply Nat2Z.is_nonneg.
        * rewrite /prf_local_state.card_input; simpl.
          apply inj_le.
          apply PeanoNat.lt_n_Sm_le.
          apply xor_dom; try (rewrite Nat2Z.id; apply xor_dom); try lia.
      Unshelve. apply gset_fin_set.
    Qed.

  End Correctness.

  (** We will prove CPA security of the scheme using the idealised random
      function. We assume that the adversaries are well-typed. *)
  Variable adv : val.
  Definition TAdv := ((TMessage → (TOption TCipher)) → TBool)%ty.
  Variable adv_typed : (∅ ⊢ₜ adv : TAdv).

  Section proofs.
    Context `{!approxisRGS Σ}.
    Variable xor_spec : XOR_spec.

    Lemma refines_rf_scheme_l K E e A :
      (∀ lm, map_list lm ∅ -∗
        refines E (fill K (rf_enc #lm, rf_dec #lm)) e A)
      ⊢ refines E (fill K rf_scheme) e A.
    Proof. iIntros "H".
      rewrite /rf_scheme.
      rel_apply refines_init_map_l.
      iIntros (lm0) "Hmap".
      rel_pures_l.
      rel_apply "H". iAssumption.
    Qed.

    Lemma refines_rf_scheme_r K E e A :
      (∀ lm, map_slist lm ∅ -∗
        refines E e (fill K (rf_enc #lm, rf_dec #lm)) A)
      ⊢ refines E e (fill K rf_scheme) A.
    Proof. iIntros "H".
      rewrite /rf_scheme.
      rel_apply refines_init_map_r.
      iIntros (lm0) "Hmap".
      rel_pures_r.
      rel_apply "H". iAssumption.
    Qed.

(* Proof Sketch

We track the previously sampled PRF elements in the map M. To ensure that we
query a fresh element and PRF behaves randomly, we pay |dom(M)| error credits.
The counter q tracks this size, i.e., q = |dom(M)|.PRF

In total, we have an error budget of ε₀ = (Q-1)Q/2N. This is enough to sum over
Q calls, each of which consumes error q/N, where q is the number of previously
executed calls. For example, on the first call, q=0 and we need 0 error credits.
On the second call, we start with q=1, and we need 1/N error credits for the
current round, and end up with q=2 and ε₀ - 1/N credits. On the third call, q=2,
we need ↯ 2/N, and end up with q=3 and ↯ (ε₀ - 1/N - 2/N). In the last round, we
start with q=Q-1, spend q/N, and have end up having consumed all ε₀ credits.

| call q | initial budget       | cost    | q end | budget end           |
|--------|----------------------|---------|-------|----------------------|
|      0 | ε₀                   | 0/N     |     1 | ε₀                   |
|      1 | ε₀                   | 1/N     |     2 | ε₀ - 1/N             |
|      2 | ε₀ - 1/N             | 2/N     |     3 | ε₀ - 1/N - 2/N       |
|      3 | ε₀ - 1/N - 2/N       | 3/N     |     4 | ε₀ - 1/N - 2/N - 3/N |
|      q | ε₀ - (0+1+2+…+q-1)/N | q/N     |   q+1 | ε₀ - (0+1+…+q-1+q)/N |
|    Q-1 | ε₀ - (0+1+2+…+Q-2)/N | (Q-1)/N |     Q | 0                    |


Since sum_{i=0}^{q-1} i/N = (q-1)q/2N, each round starts with
ε_q = ε₀ - (q-1)q/2N and ends with ε_(q+1) = ε₀ - q(q+1)/2N.

Let ε_q = 0/N+1/N+...+(q-1)/N = sum_{i=0}^{q-1}{i/N} = (q-1)q/2N
be the amount of credits spent so far.

The credits stored in the invariant step from ε_Q-ε_q to ε_Q-ε_q+1.

Since ε_{q+1} = q(q+1)/2N = (q*q + q)/2N = (q*q - q + 2q)/2N = ((q-1)q + 2q)/2N
 = ε_q + q/N

we can split off q/N credits to spend on sampling a fresh element, as required.
*)



    (* Auxiliary lemmas *)
    Lemma split_credit_step (Q N' q : nat) :
      ((Q - 1) * Q / (2 * (S N')) - (q-1) * q / (2*(S N')) )%R
      =
        ((Q - 1) * Q / (2 * (S N')) - (((q+1)-1) * (q+1) / (2* (S N'))) + q/(S N') )%R.
    Proof. field. real_solver. Qed.

    Lemma map_insert_fresh_size (N' : nat) (q : nat) (M : gmap nat val)
      (l' : list (fin (S N')))
      (dom_q : size (dom M) = q)
      (Hl' : fin_to_nat <$> l' = elements (dom M))
      (r_in : fin (S N'))
      (r_fresh : r_in ∉ l') (y : nat) :
      size (dom (<[(fin_to_nat r_in):=#y]> M)) = q + 1.
    Proof.
      rewrite size_dom. rewrite size_dom in dom_q.
      rewrite map_size_insert_None ; [clear -dom_q ; lia|].
      apply not_elem_of_dom_1.
      rewrite -elem_of_elements.
      rewrite -Hl'.
      intros K.
      apply elem_of_list_fmap_2_inj in K ; last apply fin_to_nat_inj.
      done.
    Qed.

    (* TODO Make it so that `iFrame "ε"` generates the obligation `ε = ε'`.
       Currently, one has to write the equation or apply ec_eq manually. *)
    Local Instance ec_frame_eq ε ε' :
      ε = ε' ->
      Frame false (↯ ε) (↯ ε') emp | 0.
    Proof.
      intros ->. simpl. iIntros "[??]". iFrame.
    Defined.

    Theorem rf_is_CPA (Q : nat) :
      ↯ ((Q-1) * Q / (2 * S Input))
      ⊢
      (REL (CPA #true adv sym_scheme #Q)
           <<
           (CPA #false adv sym_scheme #Q) : lrel_bool).
    Proof with (rel_pures_l ; rel_pures_r).
      iIntros "ε".
      rewrite /CPA...
      rewrite /get_enc_scheme/get_keygen...
      rewrite /rf_scheme...
      rel_apply refines_init_map_l;
      iIntros (mapref) "Hmap".
      rel_apply refines_init_map_r;
      iIntros (mapref') "Hmap'"...
      rewrite /rf_enc/rf_dec...
      rewrite /rf_keygen...
      rel_apply (refines_couple_UU Key id) => //.
      iIntros (key) "!> %"...
      rewrite /get_enc...
      rewrite /prf_enc /prf_local_state.random_function...
      rewrite /get_rand_cipher...
      rel_bind_l (q_calls _ _ _)%E ; rel_bind_r (q_calls _ _ _)%E.
      unshelve iApply (refines_bind with "[-] []").
      1: exact (interp (TMessage → (TOption TCipher)) []).
      2:{
        iIntros (f f') "Hff'" => /=.
        unshelve iApply (refines_app with "[] [Hff']").
        3: rel_values.
        rel_arrow_val.
        iIntros (o o') "Hoo'"...
        repeat rel_apply refines_app. 3: rel_values.
        Unshelve. 3: exact (interp TBool []).
        1: { rel_arrow_val. lrintro... rel_values. }
        replace (_ → _)%lrel with (interp TAdv []) by easy.
        iApply refines_typed. assumption.
      }
      rewrite /get_card_message...
      rewrite /q_calls...
      rel_alloc_l counter as "counter" ; rel_alloc_r counter' as "counter'"...

      iApply (refines_na_alloc
                (∃ (q : nat) M,
                    ↯ (((Q-1)*Q) / (2 * S Input) -
                              ((q-1)*q) / (2 * S Input))
                    ∗ counter ↦ #q
                    ∗ counter' ↦ₛ #q
                    ∗ map_list mapref M
                    ∗ ⌜ size (dom M) = q ⌝
                    ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S Input)%nat ⌝
                )%I
                (nroot.@"cpa")); iFrame.
      iSplitL.
      1: { iExists 0. iFrame. iSplitL ; [|iPureIntro ; set_solver].
           (* See TODO ec_frame_eq. *)
           (* try iFrame "ε".
              iNext.
              eapply (coq_tactics.tac_frame _ "ε" false _ _ True).
                1: simpl. 1: reflexivity.
                2: simpl ; done.
                apply ec_frame_eq. *)
           iApply (ec_eq with "[$]").
           (* setoid_rewrite Qdiv_0_l. setoid_rewrite Qminus_0_r.
                done. *)
           (* apply Qreals.Qeq_eqR. *)
           qify_r ; zify_q ; nia.
      }
      iIntros "#Hinv".
      rel_arrow_val ; lrintro "msg"...
      iApply (refines_na_inv with "[$Hinv]"); [done|].
      iIntros "(> (%q & %M & ε & counter & counter' & mapref & %dom_q & %dom_range) & Hclose)".
      case_bool_decide as Hm.
      - rel_load_l ; rel_load_r...
        rewrite /rf_rand_cipher.
        rewrite -bool_decide_and.
        case_bool_decide as Hq.
        + rel_load_l ; rel_load_r... rel_store_l ; rel_store_r...
          assert (Z.to_nat msg < S Message) as Hmsg by lia.
          pose proof nat_to_fin_list _ (elements(dom M)) dom_range as [l' Hl'].
          rel_apply (refines_couple_couple_avoid _ l').
          { apply (NoDup_fmap fin_to_nat). rewrite Hl'. apply NoDup_elements. }
          replace (length l') with q. 2: by erewrite <-length_fmap, Hl'.
          pose proof pos_INR_S (Input).
          rewrite split_credit_step.
          iDestruct (ec_split with "[$]") as "[ε ε']".
          1,2: qify_r ; zify_q ; nia.
          iFrame.
          iIntros (r_in) "!> %r_fresh"...
          rel_apply_l (refines_get_l with "[-mapref] [$mapref]").
          iIntros (?) "mapref #->"...
          assert ((M !! fin_to_nat r_in) = None) as ->.
          { apply not_elem_of_dom_1. rewrite -elem_of_elements -Hl'. intros K.
            by apply elem_of_list_fmap_2_inj in K ; [|apply fin_to_nat_inj]. }
          simpl...
          rel_apply (refines_couple_UU _ (xor_sem (Z.to_nat msg))).
          1: by apply xor_dom. 
          iIntros (y) "!> %"...
          rel_apply_l (refines_set_l with "[-mapref] [$mapref]").
          iIntros "mapref"...
          rel_bind_l (xor _ _).
          replace msg with (Z.of_nat (Z.to_nat msg)) by lia.
          rel_apply_l xor_correct_l; [ lia | lia | lia |].
          iApply (refines_na_close with "[-]").
          iFrame. iSplitL... 2: rel_vals.
          iExists (q+1).
          nify_r.
          replace (Z.of_nat q + 1)%Z with (Z.of_nat (q+1)) by lia.
          iFrame.
          iPureIntro; split.
          * eapply map_insert_fresh_size ; eauto.
          * intros x. rewrite elem_of_elements. set_unfold.
            intros [|]; last naive_solver. subst. apply fin_to_nat_lt.
        + iApply (refines_na_close with "[-]").
          iFrame ; iSplit... 1: done. rel_vals.
      - rel_load_l ; rel_load_r... rewrite andb_false_r...
        iApply (refines_na_close with "[-]").
        iFrame ; iSplit... 1: done. rel_vals.
        Unshelve. apply xor_bij.
    Qed.

    Theorem rf_is_CPA' (Q : nat) :
      ↯ ((Q-1) * Q / (2 * S Input)) ⊢
        (REL (CPA #false adv sym_scheme #Q) << (CPA #true adv sym_scheme #Q) : lrel_bool).
    Proof with (rel_pures_l ; rel_pures_r).
      iIntros "ε".
      rewrite /CPA...
      rewrite /get_enc_scheme/get_keygen...
      rewrite /rf_scheme...
      rel_apply refines_init_map_l;
      iIntros (mapref') "Hmap'".
      rel_apply refines_init_map_r;
      iIntros (mapref) "Hmap"...
      rewrite /rf_enc/rf_dec...
      rewrite /rf_keygen...
      rel_apply (refines_couple_UU Key id) => //.
      iIntros (key) "!> %"...
      rewrite /get_enc...
      rewrite /prf_enc /prf_local_state.random_function...
      rewrite /get_rand_cipher...
      rel_bind_l (q_calls _ _ _)%E ; rel_bind_r (q_calls _ _ _)%E.
      unshelve iApply (refines_bind with "[-] []").
      1: exact (interp (TMessage → (TOption TCipher)) []).
      2:{
        iIntros (f f') "Hff'" => /=.
        unshelve iApply (refines_app with "[] [Hff']").
        3: rel_values.
        rel_arrow_val.
        iIntros (o o') "Hoo'"...
        repeat rel_apply refines_app. 3: rel_values.
        Unshelve. 3: exact (interp TBool []).
        1: { rel_arrow_val. lrintro... rel_values. }
        replace (_ → _)%lrel with (interp TAdv []) by easy.
        iApply refines_typed. assumption.
      }
      rewrite /get_card_message...
      rewrite /q_calls...
      rel_alloc_l counter as "counter" ; rel_alloc_r counter' as "counter'"...

      iApply (refines_na_alloc
                (∃ (q : nat) M,
                    ↯ (((Q-1)*Q) / (2 * S Input) -
                         ((q-1)*q) / (2 * S Input))
                    ∗ counter ↦ #q
                    ∗ counter' ↦ₛ #q
                    ∗ map_slist mapref M
                    ∗ ⌜ size (dom M) = q ⌝
                    ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S Input)%nat ⌝
                )%I
                (nroot.@"cpa")); iFrame.
      iSplitL.
      1: { iExists 0.
           iFrame. iSplitL. 2: iPureIntro ; set_solver.
           iApply (ec_eq with "[$]").
           field_simplify_eq ; try real_solver. nify_r. nat_solver. }
      iIntros "#Hinv".
      rel_arrow_val ; lrintro "msg"...
      iApply (refines_na_inv with "[$Hinv]"); [done|].
      iIntros "(> (%q & %M & ε & counter & counter' & mapref & %dom_q & %dom_range) & Hclose)".
      case_bool_decide as Hm.
      - rel_load_l ; rel_load_r...
        rewrite /rf_rand_cipher.
        rewrite -bool_decide_and.
        case_bool_decide as Hq.
        + rel_load_l ; rel_load_r... rel_store_l ; rel_store_r...
          assert (Z.to_nat msg < S Message) as Hmsg by lia.
          pose proof nat_to_fin_list _ (elements(dom M)) dom_range as [l' Hl'].
          rel_apply (refines_couple_couple_avoid _ l').
          { apply NoDup_fmap with fin_to_nat; [apply fin_to_nat_inj|].
            rewrite Hl'. apply NoDup_elements. }
          replace (length l') with q. 2: by erewrite <-length_fmap, Hl'.
          pose proof pos_INR_S (Input).
          rewrite split_credit_step.
          iDestruct (ec_split with "[$]") as "[ε ε']".
          1,2: qify_r ; zify_q ; nia.
          iFrame.
          iIntros (r_in) "!> %r_fresh"...
          rel_apply_r (refines_get_r with "[-mapref] [$mapref]").
          iIntros (?) "mapref #->"...
          assert ((M !! fin_to_nat r_in) = None) as ->.
          { apply not_elem_of_dom_1. rewrite -elem_of_elements -Hl'. intros K.
            by apply elem_of_list_fmap_2_inj in K ; [|apply fin_to_nat_inj]. }
          simpl...
          unshelve rel_apply (refines_couple_UU _ (f_inv (xor_sem (Z.to_nat msg)))).
          3: apply _.
          { apply xor_bij. }
          { split.
            - intros ?? H'.
              apply (f_equal (xor_sem (Z.to_nat msg))) in H'.
              by rewrite !f_inv_cancel_r in H'.
            - intros y. exists (xor_sem (Z.to_nat msg) y).
              apply f_inv_cancel_l. apply xor_bij.
          }
          {
            apply fin.f_inv_restr; auto. by apply xor_dom.
          }
          iIntros (y) "!> %"...
          rel_apply_r (refines_set_r with "[-mapref] [$mapref]").
          iIntros "mapref"...
          rel_bind_r (xor _ _).
          rel_apply_r xor_correct_r; [lia | lia | |].
          { apply fin.f_inv_restr; auto. 2: lia. by apply xor_dom. }
          iApply (refines_na_close with "[-]").
          iFrame. iSplitL...
          2: { rel_vals. by erewrite f_inv_cancel_r. }
          iExists (q+1).
          nify_r.
          replace (Z.of_nat q + 1)%Z with (Z.of_nat (q+1)) by lia.
          iFrame.
          iPureIntro; split.
          * eapply map_insert_fresh_size ; eauto.
          * intros x. rewrite elem_of_elements. set_unfold.
            intros [|]; last naive_solver. subst. apply fin_to_nat_lt.
        + iApply (refines_na_close with "[-]").
          iFrame ; iSplit... 1: done. rel_vals.
      - rel_load_l ; rel_load_r... rewrite andb_false_r...
        iApply (refines_na_close with "[-]").
        iFrame ; iSplit... 1: done. rel_vals.
    Qed.


  End proofs.


  Lemma rf_CPA_ARC `{approxisRGpreS Σ} `{forall foo, @XOR_spec Σ foo _ _ xor_struct} σ σ' (Q : nat) :
    ARcoupl
      (lim_exec ((CPA #true adv sym_scheme #Q), σ))
      (lim_exec ((CPA #false adv sym_scheme #Q), σ'))
      (=)
      ((Q-1) * Q / (2 * S Input)).
  Proof.
    unshelve eapply approximates_coupling ; eauto.
    - exact (fun _ => lrel_bool).
    - qify_r ; zify_q ; nia.
    - by iIntros (???) "#(%b&->&->)".
    - iIntros ; iApply rf_is_CPA ; auto.
  Qed.

  Lemma rf_CPA_ARC' Σ `{approxisRGpreS Σ} `{forall foo, @XOR_spec Σ foo _ _ xor_struct} σ σ' (Q : nat) :
    ARcoupl
      (lim_exec ((CPA #false adv sym_scheme #Q), σ))
      (lim_exec ((CPA #true adv sym_scheme #Q), σ'))
      (=)
      ((Q-1) * Q / (2 * S Input)).
  Proof.
    unshelve eapply approximates_coupling ; eauto.
    - exact (fun _ => lrel_bool).
    - qify_r ; zify_q ; nia.
    - by iIntros (???) "#(%b&->&->)".
    - by iIntros ; iApply rf_is_CPA'.
  Qed.

  Corollary CPA_bound_1 Σ `{approxisRGpreS Σ} `{forall foo, @XOR_spec Σ foo _ _ xor_struct} σ σ' (Q : nat) :
    (((lim_exec ((CPA #true adv sym_scheme #Q), σ)) #true)
     <=
       ((lim_exec ((CPA #false adv sym_scheme #Q), σ')) #true) + ((Q-1) * Q / (2 * S Input)))%R.
  Proof.
    apply ARcoupl_eq_elim.
    by eapply rf_CPA_ARC.
  Qed.

  Corollary CPA_bound_2 Σ `{approxisRGpreS Σ} `{forall foo, @XOR_spec Σ foo _ _ xor_struct} σ σ' (Q : nat) :
    (((lim_exec ((CPA #false adv sym_scheme #Q), σ)) #true)
     <=
       ((lim_exec ((CPA #true adv sym_scheme #Q), σ')) #true) + ((Q-1) * Q / (2 * S Input)))%R.
  Proof.
    apply ARcoupl_eq_elim.
    by eapply rf_CPA_ARC'.
  Qed.

  Lemma CPA_bound Σ `{approxisRGpreS Σ} `{forall foo, @XOR_spec Σ foo _ _ xor_struct} σ σ' (Q : nat) :
    (Rabs (((lim_exec ((CPA #true adv sym_scheme #Q), σ)) #true) -
           ((lim_exec ((CPA #false adv sym_scheme #Q), σ')) #true)) <= ((Q-1) * Q / (2 * S Input)))%R.
  Proof.
    apply Rabs_le.
    pose proof CPA_bound_1 Σ σ σ' Q.
    pose proof CPA_bound_2 Σ σ' σ Q.
    split; lra.
  Qed.

End defs.

Section implementation.

  (* Definition bit:=64. *)
  Variable bit : nat.
  Variable Q : nat.
  Variable adv : val.
  Variable adv_typed : (∅ ⊢ₜ adv : TAdv).

  Definition Output' := xor.Output' bit.
  Definition Input' := xor.Output' bit.
  Definition Key' := xor.Output' bit.

  #[local] Instance XOR_minus_mod : @xor.XOR Output' Output' := xor.XOR_minus_mod bit.
  #[local] Instance XOR_spec_mod `{!approxisRGS Σ} : @xor.XOR_spec _ _ _ _ XOR_minus_mod :=
    xor.XOR_spec_minus_mod bit.

  Lemma CPA_bound_realistic σ σ' :
    (Rabs (((lim_exec ((CPA #true adv
      (@sym_scheme (SYM_param Key' Input' Output') (sym_rf_scheme Key' Input' Output' XOR_minus_mod))
      #Q), σ)) #true) -
             ((lim_exec ((CPA #false adv
      (@sym_scheme (SYM_param Key' Input' Output') (sym_rf_scheme Key' Input' Output' XOR_minus_mod))
      #Q), σ')) #true)) <= ((Q-1) * Q / (2 * S Input')))%R.
  Proof.
    unshelve epose proof CPA_bound Key' Input' Output' XOR_minus_mod adv _ _ σ σ' Q as H.
    - apply adv_typed.
    - apply approxisRΣ.
    - apply subG_approxisRGPreS. apply subG_refl.
    - intros. apply _.
    - done.
  Qed.


End implementation.
