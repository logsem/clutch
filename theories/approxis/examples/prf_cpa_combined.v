From clutch.prob_lang.typing Require Import tychk.
From clutch.approxis Require Import approxis map list.
From clutch.approxis.examples Require Import prf symmetric (* prf_cpa *) security_aux xor advantage.
Set Default Proof Using "Type*".

Section combined.

  (*** A PRF *)

  (** PRF Parameters. *)
  Variable Key : nat.
  Variable Input : nat.
  Variable Output : nat.

  Definition q_calls := q_calls Input.

  Definition N := S Input.

  (** PRF Security: Local instances of the PRF games. **)
  Definition PRF_rand := PRF_rand Input Output.
  Definition PRF_real := PRF_real Input.
  (* Max number of oracle calls *)
  Variable (Q : nat).

  Let ε_Q := (INR Q * INR Q / (2 * INR (S Input)))%R.

  Local Opaque INR.

  (** The PRF: (keygen, F, rand_output) *)
  Variable keygen : val.
  Variable F : val.
  Definition rand_output : val := λ:"_", rand #Output.

  Definition PRF_scheme_F : val := (keygen, (F, rand_output)).

  (** RandML types: PRF and PRF adversary *)
  Definition TKey := TNat.
  Definition TInput := TNat.
  Definition TOutput := TNat.
  Definition TKeygen : type := (TUnit → TKey)%ty.
  Definition TPRF : type := TKey → TInput → TOutput.

  Definition T_PRF_Adv := ((TInput → (TOption TOutput)) → TBool)%ty.

  (** Assumption: the PRF is typed. *)
  (* TODO: The type TPRF requires F to be safe for all inputs ; maybe this
     assumption is unrealistic, and F should only be required to be safe only
     for inputs in {0..Key}x{0..Input}. *)
  Hypothesis F_typed : (⊢ᵥ F : TPRF).
  Hypothesis keygen_typed : (⊢ᵥ keygen : TKeygen).


  (*** Symmetric scheme sym_scheme_F based on the PRF **)
  (** Symmetric Scheme Parameters **)
  Let Message := Output.
  Let Cipher := Input * Output.

  (** Security for Symmetric Encryption *)
  Let CPA_real := CPA_real Message.
  Let CPA_rand := CPA_rand Message.

  (** RandML typing *)
  Definition TMessage := TInt.
  Definition TCipher := (TInput * TOutput)%ty.

  (** Parameters required for the construction of sym_scheme_F *)
  (* H_in_out is required to make sense of the assumption that xor is a bijection. *)
  Hypothesis H_in_out : (Input = Output).
  (* An abstract `xor`, in RandML and in Coq. *)
  Context `{XOR Message Output}.

  (** Generic PRF-based symmetric encryption. *)
  (* Redefined here to make it parametrised by the PRF on the Coq level. *)
  Definition prf_enc (prf : val) : val :=
    λ:"key",
      let: "prf_key" := prf "key" in
      λ: "msg",
        let: "r" := rand #Input in
        let: "z" := "prf_key" "r" in
        ("r", xor "msg" "z").

  Let F_keygen := keygen.
  Definition F_enc : val := prf_enc F.
  Definition F_rand_cipher : val := λ:<>, let:"i" := rand #Input in let:"o" := rand #Output in ("i", "o").
  Definition sym_scheme_F : val := (F_keygen, (F_enc, F_rand_cipher)).

  (** An IND$-CPA adversary. *)
  Variable adversary : val.
  Definition T_IND_CPA_Adv : type := (TMessage → TOption TCipher) → TBool.
  (* Assumption: the adversary is typed. *)
  Hypothesis adversary_typed : (⊢ᵥ adversary : T_IND_CPA_Adv).

  (** The reduction to PRF security. *)
  Definition R_prf : val :=
    λ:"prf_key",
      let: "prf_key_q" := q_calls #Q
                     (λ: "msg",
                        let: "r" := rand #Input in
                        let: "z" := "prf_key" "r" in
                        match: "z" with
                        | SOME "z" => SOME ("r", xor "msg" "z")
                        | NONE => NONE
                        end
                     ) in
      λ:"msg", opt_mult ("prf_key_q" "msg").

  Definition RED : val :=
    λ:"prf_key", adversary (R_prf "prf_key").

  Fact red_typed : (⊢ᵥ RED : T_PRF_Adv).
  Proof.
    rewrite /RED. tychk. 1: eauto.
    rewrite /R_prf. constructor.
    type_expr 4.
    all: try by tychk.
    1: constructor ; apply opt_mult_typed.
    1: rewrite /q_calls. 1: eapply q_calls_typed_int.
    tychk. apply xor_typed.
  Qed.

  Section approxis_proofs.

  Context `{!approxisRGS Σ}.

  Lemma reduction :
    ⊢ (REL (adversary (CPA_real sym_scheme_F #Q))
         << (RED (PRF_real PRF_scheme_F #Q)) : lrel_bool).
  Proof.
    rewrite /RED. rel_pures_r.
    rewrite /PRF_scheme_F/PRF_real/prf.PRF_real.
    rel_pures_r.
    rewrite /CPA_real/symmetric.CPA_real.
    rel_pures_l. rewrite /F_keygen.
    rel_bind_l (keygen _)%E.
    rel_bind_r (keygen _)%E.
    unshelve iApply (refines_bind with "[-] []").
    1: exact (interp TKey []).
    { iApply refines_typed. by tychk. }
    iIntros (??(key&->&->)). simpl.
    rel_pures_l. rel_pures_r.
    rewrite /F_enc/prf_enc. rel_pures_l.
    rel_bind_l (F #key)%E.
    rel_bind_r (F #key)%E.
    unshelve iApply (refines_bind with "[-] []").
    1: exact (interp (TInput → TOutput) []).
    { iApply refines_typed. type_expr 1. 1: by tychk. do 2 constructor.  }
    rewrite /TInput/TOutput.
    iIntros (F_key F_key') "#rel_prf_key". iSimpl in "rel_prf_key".
    simpl. rel_pures_l ; rel_pures_r.
    rewrite {2}/bounded_oracle.q_calls. rel_pures_r.
    rel_alloc_r counter_r as "counter_r". rel_pures_r.
    rewrite /R_prf. rel_pures_r. rewrite /q_calls.
    rewrite /Message.
    rewrite -{1}H_in_out.
    rel_bind_l (bounded_oracle.q_calls _ _ _)%E.
    (* rel_bind_r (bounded_oracle.q_calls _ _ _)%E. *)
    rel_bind_r (let: _ := _ in _)%E.
    unshelve iApply (refines_bind with "[-] []").
    1: exact (interp (TMessage → TOption TCipher) []).
    2:{ simpl. iIntros (f f') "H_f_f'".
        rel_pures_r.
        iApply refines_app. 2: rel_values.
        set (t := (interp T_IND_CPA_Adv [])).
        pose proof (eq_refl t) as h.
        rewrite {1}/t in h.
        rewrite {1}/T_IND_CPA_Adv in h.
        simpl in h.
        rewrite h.
        rewrite /t.
        iApply refines_typed. by tychk. }
    simpl.
    rewrite /bounded_oracle.q_calls/opt_mult.
    rel_pures_l ; rel_pures_r.
    rel_alloc_l counter_l as "counter_l".
    rel_alloc_r counter_r' as "counter_r'".
    rel_pures_l ; rel_pures_r.
    (* Invariant: all counters agree. *)
    iApply (refines_na_alloc
              ( ∃ (q : nat), counter_l ↦ #q
                             ∗ counter_r ↦ₛ #q
                             ∗ counter_r' ↦ₛ #q )%I
              (nroot.@"RED")) ; iFrame.
      iSplitL.
      1: iExists 0 ; iFrame.
      iIntros "#Hinv".
      rel_arrow_val.
      iIntros (??) "#(%msg&->&->)" ; rel_pures_l ; rel_pures_r.
      iApply (refines_na_inv with "[$Hinv]"); [done|].
      iIntros "(> (%q & counter_l & counter_r & counter_r') & Hclose)".
      rel_load_l ; rel_load_r.
      case_bool_decide as Hmsg_pos.
      all: case_bool_decide as H_msg_max.
      all: simpl ; rel_pures_l ; rel_pures_r.
      all: try case_bool_decide as qQ.
      all: simpl ; rel_pures_l ; rel_pures_r.
      2-8: iApply (refines_na_close with "[-]") ;
      iFrame ; rel_values ;
      iExists _,_ ; iLeft ; done.
      rel_load_l ; rel_load_r.
      simpl ; rel_pures_l ; rel_pures_r.
      rel_store_l ; rel_store_r.
      simpl ; rel_pures_l ; rel_pures_r.
      rel_apply (refines_couple_UU Input id); first auto.
      iIntros (r) "!> %".
      simpl ; rel_pures_l ; rel_pures_r.
      rel_load_r. rel_pures_r.
      case_bool_decide. 2: by exfalso.
      case_bool_decide.
      1: case_bool_decide.
      all: simpl ; rel_pures_l ; rel_pures_r.
      2,3: by exfalso ; lia.

      rel_load_r. rel_store_r. rel_pures_r.
      1: assert ((q+1)%Z = q+1) as -> by lia.
      iApply (refines_na_close with "[-]") ; iFrame.
      rel_bind_l (F_key #r)%E.
      rel_bind_r (F_key' #r)%E.
      iApply (refines_bind with "[-] []") => /=.
      { iApply "rel_prf_key". by iExists _. }
      iIntros (??) "#(%z&->&->)" ; rel_pures_l ; rel_pures_r.
      replace (() + lrel_nat * lrel_nat)%lrel with (interp (TOption (TNat * TNat)) []) by easy.
      rel_pures_r.
      rel_bind_l (#r, _)%E.
      rel_bind_r (#r, _)%E.
      iApply (refines_bind _ _ _ (interp (TNat * TOutput) []) with "[-] []") => /=.
      1: { replace (lrel_nat * lrel_nat)%lrel with (interp (TNat * TNat) []) by easy.
           iApply refines_typed.
           type_expr 1.
           1: constructor. 1: apply Nat_val_typed.
           1: type_expr 1.
           1: type_expr 1.
           1: constructor ; apply xor_typed.
           2: rewrite /xor.TInput.
           all: tychk.
      }
      iIntros (??) "#( % & % & % & % & -> & -> & (% & -> & ->) & % & -> & ->)" ; rel_pures_l ; rel_pures_r.
      rel_values. iExists _,_. iPureIntro. right. repeat split.
      eexists _,_,_,_. repeat split. all: by eexists _.
  Qed.

  Definition I := random_function Output.
  Definition PRF_scheme_I := (λ:"_", #(), (I, rand_output))%V.

  (* Should be just syntactic since PRF_rand doesn't use the PRF. *)
  Lemma F_I :
    ⊢ (REL (RED (PRF_rand PRF_scheme_F #Q))
         << (RED (PRF_rand PRF_scheme_I #Q)) : lrel_bool).
  Proof with (rel_pures_l ; rel_pures_r).
    rewrite /PRF_scheme_F/PRF_scheme_I/PRF_rand/prf.PRF_rand...
    replace lrel_bool with (interp TBool []) by auto.
    iApply refines_typed. unshelve tychk.
    3: apply red_typed.
    1: exact (TInput → TOutput)%ty.
    2:{ rewrite /random_function.
        tychk.
        - eapply get_typed => //. constructor.
        - apply set_typed => //.
        - apply init_map_typed.
    }
    apply q_calls_typed_nat.
  Qed.

  Definition I_enc := prf_enc I.
  Definition sym_scheme_I := (λ:"_", #(), (I_enc, F_rand_cipher))%V.

  Lemma reduction' :
    ⊢ (REL (RED (PRF_rand PRF_scheme_I #Q))
         << (adversary (CPA_real sym_scheme_I #Q)) : lrel_bool).
  Proof
    using (F_typed keygen_typed adversary_typed H_in_out)
    with (rel_pures_l ; rel_pures_r).
    rewrite /PRF_scheme_I/sym_scheme_I/PRF_rand/prf.PRF_rand/CPA_real/symmetric.CPA_real...
    rewrite /F_keygen.

    rewrite /I_enc. rewrite /prf_enc. rewrite /RED/R_prf. rewrite /I...
    rewrite /random_function...
    rel_bind_r (init_map #())%E.
    iApply refines_init_map_r => /=...
    iIntros (map_r) "map_r".
    rel_bind_l (init_map #())%E.
    iApply refines_init_map_l.
    iIntros (map_l) "map_l" => /=...
    rewrite /q_calls/bounded_oracle.q_calls...
    rel_alloc_r counter_r as "counter_r"...
    rel_alloc_l counter_l as "counter_l"...
    rel_alloc_l counter_l' as "counter_l'"...
    unshelve rel_apply refines_app.
    { exact (interp (TMessage → TOption TCipher) []). }
    { replace (interp (TMessage → TOption TCipher) [] → lrel_bool)%lrel with (interp T_IND_CPA_Adv []) by easy.
        iApply refines_typed. by tychk. }
    (* more or less: (enc_prf rand_fun|Q)|Q = (enc_prf rand_fun)|Q *)
    iApply (refines_na_alloc
              ( ∃ (q : nat) (M : gmap nat val), counter_l ↦ #q
                             ∗ counter_l' ↦ #q
                             ∗ counter_r ↦ₛ #q
                             ∗ map_list map_l M
                             ∗ map_slist map_r M
                             ∗ ⌜ ∀ y, y ∈ @map_img nat val (gmap nat val) _ (gset val) _ _ _ M → ∃ k : nat, y = #k ⌝
                             (* ∗ ⌜ size (dom M) = q ⌝ *)
                             ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S Input)%nat ⌝
              )%I
              (nroot.@"RED")) ; iFrame.
      iSplitL.
      1: { iExists 0 ; iFrame. iPureIntro; split ; [|set_solver].
           intros y hy. exfalso. clear -hy.
           rewrite map_img_empty in hy.
           opose proof (proj1 (elem_of_empty y)hy ). done.
      }
      iIntros "#Hinv".
      rel_arrow_val.
      iIntros (??) "#(%msg&->&->)" ; rel_pures_l ; rel_pures_r.
      iApply (refines_na_inv with "[$Hinv]"); [done|].
      iIntros "(> (%q & %M & counter_l & counter_l' & counter_r & map_l & map_r & %range_int & %dom_range) & Hclose)".
      rel_load_l ; rel_load_r.
      rewrite /Message.
      replace (bool_decide (msg ≤ Output))%bool%Z with
        (bool_decide (msg ≤ Input))%bool%Z by (rewrite H_in_out ; auto).
      case_bool_decide as Hmsg_pos.
      all: rel_pures_r ; rel_pures_l.
      (* TODO: the order of && in q_calls should be changed so that it properly
      evaluates left to right and evaluates lazily in all 3 arguments. *)
      all: case_bool_decide as qQ.
      all: simpl ; rel_pures_l ; rel_pures_r.
      1: case_bool_decide as H_msg_max.
      all: simpl ; rel_pures_l ; rel_pures_r.
      2-5: rewrite /opt_mult...
      2-5:iApply (refines_na_close with "[-]");
      iFrame; repeat iSplitL ; try done ;
       try (rel_values ; iExists _,_ ; iLeft ; done).
      rel_load_l ; rel_load_r...
      rel_store_l ; rel_store_r...
      rel_apply (refines_couple_UU Input id); first auto.
      iIntros (r) "!> %".
      simpl ; rel_pures_l ; rel_pures_r.
      rel_load_l. rel_pures_l.
      case_bool_decide. 2: by exfalso.
      case_bool_decide.
      1: case_bool_decide.
      all: simpl ; rel_pures_l ; rel_pures_r.
      2,3: by exfalso ; lia.

      rel_load_l. rel_store_l. rel_pures_l.
      1: assert ((q+1)%Z = q+1) as -> by lia.

      rel_apply_r (refines_get_r with "[-map_r] [$map_r]").
      iIntros (?) "map_r #->"...
      rel_apply_l (refines_get_l with "[-map_l] [$map_l]").
      iIntros (?) "map_l #->"...

      destruct (M !! r) as [y |] eqn:r_fresh ...
      1: {
        iApply (refines_na_close with "[-]") ;
        iFrame ; repeat iSplitL. 1: iExists _ ; iFrame.
        { iPureIntro. split. 2: set_solver. done. }
        replace (() + lrel_nat * lrel_nat)%lrel with (interp (TOption TCipher) []) by auto.

      rel_bind_l (#r, _)%E.
      rel_bind_r (#r, _)%E.
      iApply (refines_bind _ _ _ (interp (TNat * TOutput) []) with "[-] []") => /=.
      1: { replace (lrel_nat * lrel_nat)%lrel with (interp (TNat * TNat) []) by easy.
           iApply refines_typed.
           type_expr 1.
           1: constructor. 1: apply Nat_val_typed.
           1: type_expr 1.
           1: type_expr 1.

           1: constructor ; apply xor_typed.
           all: tychk ; compute.
           opose proof (elem_of_map_img_2 M r y r_fresh) as hy.
           destruct (range_int y hy). subst. tychk.
      }
      iIntros (??) "#( % & % & % & % & -> & -> & (% & -> & ->) & % & -> & ->)" ; rel_pures_l ; rel_pures_r.
      rewrite /opt_mult...
      rel_values. iExists _,_. iPureIntro. right. repeat split.
      eexists _,_,_,_. repeat split. all: by eexists _.
      }

      (*   rel_bind_l (λ:"x", _)%V.
           rel_bind_r (λ:"x", _)%V.
           unshelve iApply (refines_bind with "[-] []") => /=.
           1:{ exact (interp (TMessage → (TUnit + TCipher)) []). }

           iApply refines_typed.
           unshelve tychk. 1: exact TInt. 1: done.
           (* TYPING *)
           (* Here's the reason we need to keep track of the fact that ∀ y ∈ M, ∃ k : Z, y = #k. *)
           opose proof (elem_of_map_img_2 M r y r_fresh) as hy.
           destruct (range_int y hy). subst. tychk.
         } *)

      rel_apply (refines_couple_UU Output id); first auto.
      iIntros (y) "!> %"...

      rel_apply_r (refines_set_r with "[-map_r] [$map_r]").
      iIntros "map_r"...
      rel_apply_l (refines_set_l with "[-map_l] [$map_l]").
      iIntros "map_l"...
      iApply (refines_na_close with "[-]") ;
      iFrame ; repeat iSplitL. 1: iExists _ ; iFrame.
      1: { iPureIntro.
           split ; last first.
           - rewrite -Forall_forall.
             rewrite dom_insert.
             rewrite elements_union_singleton.
             + apply Forall_cons_2.
               1: lia.
               rewrite Forall_forall.
               done.
             + apply not_elem_of_dom_2. done.
           - intros y' hy'.
             opose proof (map_img_insert M r (#y)) as eq.
             rewrite eq in hy'.
             rewrite elem_of_union in hy'.
             destruct hy'.
             + exists y. set_solver.
             + apply range_int.
               opose proof (delete_subseteq M r) as h.
               eapply map_img_delete_subseteq. done.
      }
      replace (() + lrel_nat * lrel_nat)%lrel with (interp (TOption TCipher) []) by easy.

      rel_bind_l (#r, _)%E.
      rel_bind_r (#r, _)%E.
      iApply (refines_bind _ _ _ (interp (TNat * TOutput) []) with "[-] []") => /=.
      1: { replace (lrel_nat * lrel_nat)%lrel with (interp (TNat * TNat) []) by easy.
           iApply refines_typed.
           type_expr 1.
           1: constructor. 1: apply Nat_val_typed.
           1: type_expr 1.
           1: type_expr 1.
           1: by constructor ; apply xor_typed. all: tychk.
           repeat constructor.
      }
      iIntros (??) "#( % & % & % & % & -> & -> & (% & -> & ->) & % & -> & ->)" ; rel_pures_l ; rel_pures_r.
      rewrite /opt_mult...
      rel_values. iExists _,_. iPureIntro. right. repeat split.
      eexists _,_,_,_. repeat split. all: by eexists _.
      Unshelve. all: apply _.
  Qed.


  (* This should be the result proven for the Approxis paper. *)
  Lemma cpa_I `{!XOR_spec} :
    ↯ ε_Q
    ⊢ (REL (adversary (CPA_real sym_scheme_I #Q))
         << (adversary (CPA_rand sym_scheme_I #Q)) : lrel_bool).
  Proof
    using (adversary_typed keygen_typed F_typed)
    with (rel_pures_l ; rel_pures_r).
    clear H_in_out.
    iIntros "ε".
    rewrite /CPA_real/CPA_rand.
    rewrite /symmetric.CPA_real/symmetric.CPA_rand...
    rewrite /F_rand_cipher.
    rewrite /I_enc/I...
    (* should be more or less the old proof. *)
    rewrite /prf_enc...
    rewrite /random_function...
    rel_bind_l (init_map #())%E.
    iApply refines_init_map_l.
    iIntros (map_l) "map_l" => /=...
    rewrite /q_calls/bounded_oracle.q_calls...
    rel_alloc_r counter_r as "counter_r"...
    rel_alloc_l counter_l as "counter_l"...

    rel_bind_l (λ:"x", _)%V.
    rel_bind_r (λ:"x", _)%V.
    unshelve iApply (refines_bind with "[-] []") => /=.
    1:{ exact (interp (TMessage → (TUnit + TCipher)) []). }

    2:{
      iIntros (f f') "Hff'".
      simpl.
      unshelve iApply (refines_app with "[] [Hff']").
      3: rel_values.
      (* rel_arrow_val.
         iIntros (o o') "Hoo'". rel_pures_l ; rel_pures_r.
         repeat rel_apply refines_app. (* 3: rel_values. *)
         Unshelve.
         3: exact (interp TBool []).
         1: { rel_arrow_val. iIntros (??) "#(%_&->&->)". rel_pures_l ; rel_pures_r. rel_values. } *)
      replace (lrel_arr
                 (lrel_arr lrel_int
                    (lrel_sum lrel_unit (lrel_prod lrel_nat lrel_nat)))
                 (interp TBool nil)) with
        (interp T_IND_CPA_Adv []) by easy.
      iApply refines_typed.
      tychk. done.
    }

      iApply (refines_na_alloc
                (∃ (q : nat) M,
                    ↯ ((Q*Q-q*q) / (2 * S Input))
                    ∗ counter_l ↦ #q
                    ∗ counter_r ↦ₛ #q
                    ∗ map_list map_l M
                    ∗ ⌜ size (dom M) = q ⌝
                    ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S Input)%nat ⌝
                )%I
                (nroot.@"cpa")); iFrame.
      iSplitL.
      1: { iExists 0.
           rewrite INR_0.
           replace (Q*Q-0*0)%R with (Q*Q)%R by lra.
           iFrame. iPureIntro; set_solver.
      }
      iIntros "#Hinv".
      rel_arrow_val.
      iIntros (??) "#(%msg&->&->)" ; rel_pures_l ; rel_pures_r.
      iApply (refines_na_inv with "[$Hinv]"); [done|].
      iIntros "(> (%q & %M & ε & counter & counter' & mapref & %dom_q & %dom_range) & Hclose)".
      case_bool_decide as Hm.
      - rel_load_l ; rel_load_r...
        rewrite -bool_decide_and.
        case_bool_decide as Hq.
        + rel_load_l ; rel_load_r... rel_store_l ; rel_store_r...
          assert (Z.to_nat msg < S Message) as Hmsg by lia.
          pose proof nat_to_fin_list _ (elements(dom M)) dom_range as [l' Hl'].
          rel_apply (refines_couple_couple_avoid _ l').
          { apply NoDup_fmap with fin_to_nat; first apply fin_to_nat_inj.
            rewrite Hl'. apply NoDup_elements. }
          replace (length l') with q; last first.
          { erewrite <-fmap_length, Hl'.
            by replace (length (elements (dom M))) with (size (dom M)).
          }
          pose proof pos_INR_S (Input).
          assert (0<=q/S Input)%R.
          { apply Rcomplements.Rdiv_le_0_compat; last done.
            apply pos_INR. }
          assert (0<=(Q * Q - (q+1)%nat * (q+1)%nat)/(2*S Input))%R.
          { apply Rcomplements.Rdiv_le_0_compat; last lra.
            rewrite -!mult_INR. apply Rle_0_le_minus.
            apply le_INR. rewrite -Nat.square_le_mono. lia. }
          iDestruct (ec_weaken _ (q/S Input+((Q * Q - (q + 1)%nat * (q + 1)%nat))/ (2 * S Input)) with "[$]") as "ε".
          { split; first lra.
            apply Rcomplements.Rle_minus_r.
            rewrite Rminus_def -Rdiv_opp_l -Rdiv_plus_distr.
            rewrite Rdiv_mult_distr.
            rewrite !Rdiv_def.
            apply Rmult_le_compat_r.
            { apply Rlt_le. by apply Rinv_0_lt_compat. }
            rewrite -Rcomplements.Rle_div_r; last lra.
            trans ((q + 1)%nat * (q + 1)%nat-q*q)%R; last lra.
            rewrite plus_INR.
            replace (INR 1) with 1%R by done. lra.
          }
          iDestruct (ec_split with "[$]") as "[ε ε']"; [done|done|].
          iFrame.
          iIntros (r_in) "!> %r_fresh"...
          rel_apply_l (refines_get_l with "[-mapref] [$mapref]").
          iIntros (?) "mapref #->"...
          assert ((M !! fin_to_nat r_in) = None) as ->.
          { apply not_elem_of_dom_1.
            rewrite -elem_of_elements.
            rewrite -Hl'.
            intros K. apply elem_of_list_fmap_2_inj in K; last apply fin_to_nat_inj.
            done.
          }
          simpl...
          unshelve rel_apply (refines_couple_UU _ (@xor_sem _ _ H (Z.to_nat msg))) ;
            [apply xor_bij|apply xor_dom => //|..].
          iIntros (y) "!> %"...
          rel_apply_l (refines_set_l with "[-mapref] [$mapref]").
          iIntros "mapref"...
          rel_bind_l (xor _ _).
          rel_apply_l xor_correct_l; [done | lia | lia |].
          iApply (refines_na_close with "[-]").
          iFrame.
          iSplitL.
          { replace (Z.of_nat q + 1)%Z with (Z.of_nat (q+1)) by lia.
            iFrame.
            iModIntro.
            iPureIntro; split.
            - rewrite size_dom. rewrite size_dom in dom_q.
              rewrite map_size_insert_None; first lia.
              apply not_elem_of_dom_1.
              rewrite -elem_of_elements.
              rewrite -Hl'.
              intros K.
              apply elem_of_list_fmap_2_inj in K; last apply fin_to_nat_inj.
              done.
            - intros x.
              rewrite elem_of_elements.
              set_unfold.
              intros [|]; last naive_solver.
              subst. apply fin_to_nat_lt.
          }
          idtac...
          rel_values.
          repeat iExists _.
          iModIntro. iRight. repeat iSplit ; iPureIntro ; eauto.
          simpl. by repeat unshelve eexists.
        + iApply (refines_na_close with "[-]").
          iFrame.
          iSplit...
          { done. }
          rel_values. repeat iExists _. iLeft. done.
      - rel_load_l ; rel_load_r...
        rewrite andb_false_r...
        iApply (refines_na_close with "[-]").
        iFrame.
        iSplit.
        { done. }
        rel_values. repeat iExists _. iLeft. done.
    Qed.

  (* Should be just syntactic since CPA_rand doesn't use the PRF. *)
  Lemma cpa_F :
    ⊢ (REL (adversary (CPA_rand sym_scheme_I #Q))
         << (adversary (CPA_rand sym_scheme_F #Q)) : lrel_bool).
  Proof with (rel_pures_l ; rel_pures_r).
    rewrite /sym_scheme_I/sym_scheme_F/I_enc/F_enc/I.
    rewrite /CPA_rand/symmetric.CPA_rand. idtac...
    replace lrel_bool with (interp TBool []) by auto.
    iApply refines_typed. rewrite /F_rand_cipher. tychk.
    1: apply adversary_typed.
    apply q_calls_typed_int.
  Qed.

  End approxis_proofs.

  (* Next, we will:
     - for each step of logical refinement, write the corresponding ARcoupling
     - chain these together to obtain an ARcoupling for one direction
     - admit the other direction
     - combine both directions to get a bound on the difference of observing a #true
   *)

  Ltac lr_arc := unshelve eapply approximates_coupling ; eauto ;
                 [apply (λ _, lrel_bool)|try lra|by iIntros (???) "#(%b&->&->)"|iIntros].

  Lemma reduction_ARC Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl (lim_exec ((adversary (CPA_real sym_scheme_F #Q)), σ))
      (lim_exec ((RED (PRF_real PRF_scheme_F #Q)), σ'))
      eq 0.
  Proof. lr_arc ; iApply reduction. Qed.

  Lemma F_I_ARC Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl (lim_exec ((RED (PRF_rand PRF_scheme_F #Q)), σ))
      (lim_exec ((RED (PRF_rand PRF_scheme_I #Q)), σ'))
      eq 0.
  Proof. lr_arc ; iApply F_I. Qed.

  Lemma reduction'_ARC Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl (lim_exec ((RED (PRF_rand PRF_scheme_I #Q)), σ))
      (lim_exec ((adversary (CPA_real sym_scheme_I #Q)), σ'))
      eq 0.
  Proof using (keygen_typed F_typed adversary_typed H_in_out).
    lr_arc ; iApply reduction'.
  Qed.

  Fact ε_Q_pos : (0 <= ε_Q)%R.
  Proof.
    repeat apply Rmult_le_pos ; try apply pos_INR.
    pose proof Rdiv_INR_ge_0 (S Input).
    cut ((0 <= (2*1) / (2 * INR (S Input))))%R ; first lra.
    rewrite Rdiv_mult_distr. lra.
  Qed.

  Lemma cpa_I_ARC Σ `{!approxisRGpreS Σ} (bla : forall (HΣ' : approxisRGS Σ), @XOR_spec Σ HΣ' Message Output H) σ σ' :
    ARcoupl (lim_exec ((adversary (CPA_real sym_scheme_I #Q)), σ))
      (lim_exec ((adversary (CPA_rand sym_scheme_I #Q)), σ'))
      eq ε_Q.
  Proof using F_typed H_in_out adversary_typed keygen_typed.
    lr_arc. 1: apply ε_Q_pos. iApply cpa_I. iFrame.
  Qed.

  Lemma cpa_F_ARC Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl (lim_exec ((adversary (CPA_rand sym_scheme_I #Q)), σ))
      (lim_exec ((adversary (CPA_rand sym_scheme_F #Q)), σ'))
      eq 0.
  Proof using F_typed H_in_out adversary_typed keygen_typed. lr_arc ; iApply cpa_F. Qed.

  (** The PRF advantage of RED against F. *)
  Let ε_F := advantage (RED (PRF_real PRF_scheme_F #Q)) (RED (PRF_rand PRF_scheme_F #Q)) #true.

  (* We will now explore different ways of stating the assumption that F is a
     PRF. Concretely, we will need to assume that the advantage of the
     adversary RED, which was constructed by reduction from the adversary
     against the symmetric scheme, is bounded by some number ε_F. *)

  (* Predicate that states that `ε_F` is an upper bound on the PRF-advantage of
  `adversary` (in the logical relation!). *)
  Definition PRF_advantage_upper_bound `{!approxisRGS Σ} (adversary : val) (ε_F : nonnegreal) :=
    (↯ ε_F ⊢ (REL (adversary (PRF_real PRF_scheme_F #Q)) << (adversary (PRF_rand PRF_scheme_F #Q)) : lrel_bool))
    /\
      (↯ ε_F ⊢ (REL (adversary (PRF_rand PRF_scheme_F #Q)) << (adversary (PRF_real PRF_scheme_F #Q)) : lrel_bool)).

  (** This assumption states that owning ↯ ε_F error credits allows to prove
      the refinement about RED in Approxis. **)
  Hypothesis H_ε_LR : forall `{approxisRGS Σ},
      PRF_advantage_upper_bound RED ε_F.

  (* By adequacy, we deduce from the previous assumption that a corresponding
     approximate refinement coupling holds up to ε_F. *)
  Fact H_ε_ARC_from_LR Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl (lim_exec (RED (PRF_real PRF_scheme_F #Q), σ))
      (lim_exec (RED (PRF_rand PRF_scheme_F #Q), σ'))
      eq ε_F.
  Proof.
    intros ; lr_arc. 1: apply cond_nonneg. by iApply (proj1 H_ε_LR).
  Qed.

  (* Alternatively, we can directly make the (weaker) assumption that such an
     ε_F-ARcoupling exists, since our only use for H_ε_LR is to build this
     ARcoupling. *)
  Hypothesis H_ε_ARC :
    forall σ σ',
    ARcoupl (lim_exec (RED (PRF_real PRF_scheme_F #Q), σ))
      (lim_exec (RED (PRF_rand PRF_scheme_F #Q), σ'))
      eq ε_F.

  (* Either way, we can compose the ARC-level reduction lemmas and the
     assumption H_ε_ARC to get an ARC. *)
  Lemma prf_cpa_ARC Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl (lim_exec ((adversary (CPA_real sym_scheme_F #Q)), σ))
      (lim_exec ((adversary (CPA_rand sym_scheme_F #Q)), σ'))
      eq (ε_Q + ε_F).
  Proof.
    set (ε := (ε_Q + NNRbar_to_real (NNRbar.Finite ε_F))%R).
    assert (0 <= ε_F)%R by apply cond_nonneg. pose proof ε_Q_pos.
    assert (0 <= ε)%R.
    { unfold ε. apply Rplus_le_le_0_compat ; auto. }
    replace ε with (0+ε)%R by lra.
    eapply ARcoupl_eq_trans_l => //.
    1: eapply reduction_ARC => //.
    replace ε with (ε_F+ε_Q)%R by (unfold ε ; lra).
    eapply ARcoupl_eq_trans_l. 1,2 : auto.
    1: eapply (H_ε_ARC σ σ').
    replace ε_Q with (0 + ε_Q)%R by lra.
    eapply ARcoupl_eq_trans_l => //.
    1: eapply F_I_ARC => //.
    replace ε_Q with (0 + ε_Q)%R by lra.
    eapply ARcoupl_eq_trans_l => //.
    1: eapply reduction'_ARC => //.
    replace ε_Q with (ε_Q + 0)%R by lra.
    eapply ARcoupl_eq_trans_l => //.
    1: eapply cpa_I_ARC => //.
    1:
      (* TODO stupid type classes *)
      admit.
    eapply cpa_F_ARC => //.
    Unshelve. all: eauto.
  Admitted.

  (* The converse direction of the refinement. We expect it to hold with the
     same bound. *)
  Variable prf_cpa_ARC' : forall Σ `{approxisRGpreS Σ} σ σ',
    ARcoupl (lim_exec ((adversary (CPA_rand sym_scheme_F #Q)), σ))
      (lim_exec ((adversary (CPA_real sym_scheme_F #Q)), σ'))
      eq (ε_Q + ε_F).

  Corollary CPA_bound_1 Σ `{approxisRGpreS Σ} σ σ' :
    ( (lim_exec ((adversary (CPA_real sym_scheme_F #Q)), σ) #true)
      <= (lim_exec ((adversary (CPA_rand sym_scheme_F #Q)), σ') #true)
         + (ε_Q + ε_F))%R.
  Proof. apply ARcoupl_eq_elim. by eapply prf_cpa_ARC. Qed.

  Corollary CPA_bound_2 Σ `{approxisRGpreS Σ} σ σ' :
    ( (lim_exec ((adversary (CPA_rand sym_scheme_F #Q)), σ) #true)
      <= (lim_exec ((adversary (CPA_real sym_scheme_F #Q)), σ') #true)
         + (ε_Q + ε_F))%R.
  Proof using prf_cpa_ARC'. apply ARcoupl_eq_elim. by eapply prf_cpa_ARC'. Qed.

  Theorem CPA_bound_st Σ `{approxisRGpreS Σ} σ σ' :
    (pr_dist (adversary (CPA_real sym_scheme_F #Q)) (adversary (CPA_rand sym_scheme_F #Q)) σ σ' #true
     <= ε_Q + ε_F)%R.
  Proof using F_typed H_in_out H_ε_ARC H_ε_LR adversary_typed keygen_typed prf_cpa_ARC'.
    apply Rabs_le.
    pose proof CPA_bound_1 Σ σ σ'.
    pose proof CPA_bound_2 Σ σ' σ.
    set (lhs := lim_exec (adversary (CPA_real sym_scheme_F #Q), σ) #true).
    set (rhs := lim_exec (adversary (CPA_rand sym_scheme_F #Q), σ') #true).
    assert (lhs <= rhs + (ε_Q + ε_F))%R by easy.
    assert (rhs <= lhs + (ε_Q + ε_F))%R by easy.
    split ; lra.
  Qed.

  (** Instead of making an assumption about F at the ARcoupl level, we can work
  directly with pr_dist. Since ε_F is defined to be the advantage, no further
  assumptions are needed. We prove the (ε_Q+ε_F) bound by lowering all the
  reduction lemmas to the pr_dist level and composing there. **)

  (* Reduce from CPA security to a statement about PRF security of F (real side) *)
  Lemma red_to_prf Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl (lim_exec (adversary (CPA_real sym_scheme_F #Q), σ))
      (lim_exec ((RED (PRF_real PRF_scheme_F #Q)), σ')) eq 0%R.
  Proof. eapply reduction_ARC => //. Qed.

  (* The reverse direction *)
  Hypothesis red_to_prf' : forall Σ `{approxisRGpreS Σ} σ σ',
    ARcoupl (lim_exec ((RED (PRF_real PRF_scheme_F #Q)), σ'))
      (lim_exec (adversary (CPA_real sym_scheme_F #Q), σ)) eq 0%R.

  (* Combine to get the pr_dist bound. *)
  Lemma pr_dist_adv_F `{approxisRGpreS Σ} v σ σ' :
    (pr_dist (adversary (CPA_real sym_scheme_F #Q)) (RED (PRF_real PRF_scheme_F #Q)) σ σ' v
     <= 0)%R.
  Proof.
    rewrite /pr_dist.
    eapply Rabs_le.
    split.
    - opose proof (ARcoupl_eq_elim _ _ _ (red_to_prf' _ σ σ') v) as hred.
      set (y := (lim_exec (adversary _, σ)) v).
      set (x := lim_exec (RED _, σ') v).
      assert (x <= y + 0)%R by easy.
      lra.
    - opose proof (ARcoupl_eq_elim _ _ _ (red_to_prf _ σ σ') v) as hred.
      set (x := (lim_exec (adversary _, σ)) v).
      set (y := lim_exec (RED _, σ') v).
      assert (x <= y + 0)%R by easy.
      lra.
  Qed.

  (* Reduce from CPA security to a statement about PRF security of F (rand side) *)
  Lemma red_from_prf Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl (lim_exec (RED (PRF_rand PRF_scheme_F #Q), σ))
      (lim_exec (adversary (CPA_rand sym_scheme_F #Q), σ'))
      eq ε_Q.
  Proof.
    pose proof ε_Q_pos.
    replace ε_Q with (0 + ε_Q)%R by lra.
    eapply ARcoupl_eq_trans_l => //.
    1: eapply (F_I_ARC _ _ σ) => //.
    replace ε_Q with (0 + ε_Q)%R by lra.
    eapply ARcoupl_eq_trans_l => //.
    1: eapply (reduction'_ARC _ _ σ) => //.
    replace ε_Q with (ε_Q + 0)%R by lra.
    eapply ARcoupl_eq_trans_l => //.
    1: eapply (cpa_I_ARC _ _ _ σ) => //.
    eapply cpa_F_ARC => //.
    Unshelve. all: eauto.
    admit.                      (* TODO stupid type classes again *)
  Admitted.

  (* The reverse direction *)
  Hypothesis red_from_prf' : forall Σ `{approxisRGpreS Σ} σ σ',
    ARcoupl (lim_exec (adversary (CPA_rand sym_scheme_F #Q), σ'))
      (lim_exec (RED (PRF_rand PRF_scheme_F #Q), σ))
      eq ε_Q.

  (* Combine to get the pr_dist bound. *)
  Lemma pr_dist_F_adv `{approxisRGpreS Σ} v σ σ' :
    (pr_dist (RED (PRF_rand PRF_scheme_F #Q)) (adversary (CPA_rand sym_scheme_F #Q)) σ σ' v
     <= ε_Q)%R.
  Proof.
    rewrite /pr_dist. eapply Rabs_le. split.
    - opose proof (ARcoupl_eq_elim _ _ _ (red_from_prf' _ σ σ') v) as hred.
      set (x := lim_exec (RED _, σ) v).
      set (y := (lim_exec (adversary _, σ')) v).
      assert (y <= x + ε_Q)%R by easy. lra.
    - opose proof (ARcoupl_eq_elim _ _ _ (red_from_prf _ σ σ') v) as hred.
      set (x := lim_exec (RED _, σ) v).
      set (y := (lim_exec (adversary _, σ')) v).
      assert (x <= y + ε_Q)%R by easy. lra.
  Qed.

  (* Same statement as CPA_bound_st but proven without assuming H_ε_ARC or H_ε_LR. *)
  Theorem CPA_bound_st' Σ `{approxisRGpreS Σ} σ σ' :
    (pr_dist (adversary (CPA_real sym_scheme_F #Q)) (adversary (CPA_rand sym_scheme_F #Q)) σ σ' #true
     <= ε_Q + ε_F)%R.
  Proof.
    eapply pr_dist_triangle.
    1: eapply pr_dist_adv_F.
    1: eapply pr_dist_triangle.
    2: eapply pr_dist_F_adv.
    1: eapply (advantage_ub).
    1: right ; eauto.
    unfold ε_Q, ε_F. lra.
  Qed.

  Theorem CPA_bound Σ `{approxisRGpreS Σ} :
    (advantage
       (adversary (CPA_real sym_scheme_F #Q))
       (adversary (CPA_rand sym_scheme_F #Q))
       #true
     <= ε_Q + ε_F)%R.
  Proof using prf_cpa_ARC' F_typed H_in_out H_ε_ARC H_ε_LR Key adversary_typed keygen_typed.
    apply advantage_uniform.
    by eapply CPA_bound_st => //.
  Qed.

  (* TODO Something about PPT and proving that if (isNegligable ε_F) then also
     (isNegligable (ε_F + ε_Q))... *)
  Variable PPT : expr → Prop.
  Hypothesis adv_in_PPT : PPT adversary.
  Hypothesis RED_in_PPT : PPT adversary → PPT RED.

  (*

Recall that a function f is negligible if any n, there exists M_n, s.t. for all
λ > M_n, f(λ) < 1/λ^n.

Definition (Advantage).

The distinguishing advantage between two programs X and Y is defined as

advantage(X, Y) = max_(σ,σ') | lim_exec(X,σ)(true) - lim_exec(Y,σ')(true) | .


Nota bene: In security statements, X and Y are typically of the form (A G_real)
and (A G_rand), but in security reductions they may, for instance, be of the
form (A G_real) and (RED H_rand) so rather than defining the advantage for a
fixed adversary and two games, we instead define it directly for two programs.


Definition (PRF security).

Let F = (F)_λ be a family of functions indexed by a security parameter λ. F is
a secure PRF if for all adversaries A, if A is PPT, then the function

    f(λ) = advantage (A λ (PRF_real (F λ))) (A λ (PRF_rand (F λ)))

is negligible.


Definition (IND$-CPA security).

Let Σ = (Σ)_λ be a family of symmetric encryption schemes indexed by a security
parameter λ. Σ has IND$-CPA security if for all adversaries A, if A is PPT,
then the function

    f(λ) = advantage (A λ (IND$_CPA_real (Σ λ))) (A λ (IND$_CPA_rand (Σ λ)))

is negligible.


The theorem CPA_bound states that for any function F, the IND$-CPA advantage of
any adversary A is bounded by ε = ε_F + ε_Q, where ε_Q = Q²/2N and ε_F is the
PRF advantage of A against F [TODO "the PRF advantage of A" is undefined]

If we want to conclude that Σ_F is secure against PPT CPA adversaries because F
is, then we need to use the fact that RED is a PPT PRF adversary.
[TODO spell this out]

Note, however, that the PPT assumption plays no role in the concrete security
setting. When λ is fixed to, say, 2048 bits, and ε_F is e.g. 1/2^128, then the
ε_F + ε_Q bound

   *)



End combined.
