From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From clutch.prob_lang Require Import advantage typing.tychk.
From clutch.approxis Require Import approxis map list option.
From clutch.approxis.examples Require Import symmetric security_aux sum_seq xor prf.
Import prf.sem.
Import symmetric.CPA_sem.
Set Default Proof Using "All".


Section combined.

(* TODO prove this rule, generalizing the lhs to be an arbitrary term e *)
Hypothesis refines_tape_couple_avoid : forall `{!approxisRGS Σ} (N:nat) α l z E K K' A,
    NoDup l ->
    TCEq N (Z.to_nat z) →
    ↯ (length l / (S N)) ∗
    α ↪N (N; []) ∗
    ▷ (∀ (n : fin (S N)), ⌜n ∉ l⌝ -∗ α ↪N (N; []) -∗ REL fill K (Val #n) << fill K' (Val #n) @ E : A)
    ⊢ REL fill K (rand(#lbl:α) #z) << fill K' (rand #z) @ E : A.

  (*** A PRF *)
  Context `{PRF}.

  (* Max number of oracle calls *)
  Variable (Q : nat).

  Let ε_Q := ε_bday Q (S card_input).

  Local Opaque INR.

  (** The PRF: (keygen, F, rand_output) *)
  Definition rand_output : val := λ:"_", rand #card_output.

  Definition PRF_scheme_F : val := prf_scheme.

  (** RandML types: PRF and PRF adversary *)
  Definition TKey := TNat.
  Definition TInput := TNat.
  Definition TOutput := TNat.
  Definition TKeygen : type := (TUnit → TKey)%ty.
  Definition TPRF : type := TKey → TInput → TOutput.

  Definition T_PRF_Adv := ((TInput → (TOption TOutput)) → TBool)%ty.


  Context `{!approxisRGS Σ}.
  (** Assumption: the PRF is typed. *)
  Hypothesis F_sem_typed : (⊢ REL prf << prf : lrel_prf).
  Hypothesis keygen_sem_typed : (⊢ REL keygen << keygen : lrel_keygen).


  (** Symmetric scheme sym_scheme_F based on the PRF **)
  (** Symmetric Scheme Parameters **)
  #[local] Instance sym_params : SYM_params :=
    { card_key := prf.card_key ;
      card_message := prf.card_output ;
      card_cipher := prf.card_input * prf.card_output }.
  Let Message := card_output.
  Let Cipher := card_input * card_output.

  (** RandML typing *)
  Definition TMessage := TInt.
  Definition TCipher := (TInput * TOutput)%ty.
  Definition lrel_message {Σ} : lrel Σ := lrel_int_bounded 0 Message.
  Definition lrel_cipher {Σ} : lrel Σ := lrel_input * lrel_output.

  Ltac2 prf_cpa_intro (typ : constr) xs k :=
    lazy_match! typ with
      | lrel_message =>
          let typ := eval unfold lrel_message in $typ in
            k typ xs
      | lrel_cipher =>
          let typ := eval unfold lrel_cipher in $typ in
            k typ xs
    | _ => None
    end.
  Ltac2 Set Basic.lrintro_tacs as prev := fun () => FMap.add "prf_cpa" prf_cpa_intro (prev ()).

  Ltac2 prf_cpa_val typ k :=
    lazy_match! typ with
    | (lrel_car lrel_message ?v1 ?v2) =>
        let typ := eval unfold lrel_message in $typ in k typ
    | (lrel_car lrel_cipher ?v1 ?v2) =>
        let typ := eval unfold lrel_cipher in $typ in k typ
    | _ => Stuck
    end.
  Ltac2 Set Basic.rel_val_tacs as prev := fun () => FMap.add "prf_cpa" prf_cpa_val (prev ()).

  (** Parameters required for the construction of sym_scheme_F *)
  Context `{xor_struct : XOR card_output card_output}.

  (** Generic PRF-based symmetric encryption. *)
  (* Redefined here to make it parametrised by the PRF on the Coq level. *)
  Definition prf_enc (prf : val) : val :=
    λ:"key",
      let: "prf_key" := prf "key" in
      let: "α" := AllocTape #card_input in
      λ: "msg",
        let: "r" := rand("α") #card_input in
        let: "z" := "prf_key" "r" in
        ("r", xor "msg" "z").

  Let F_keygen := keygen.
  Definition F_enc : val := prf_enc prf.
  Definition F_rand_cipher : val := λ:<>, let:"i" := rand #card_input in let:"o" := rand #card_output in ("i", "o").
  #[local] Instance sym : SYM :=
    { keygen := prf.keygen ;
      enc := F_enc ;
      dec := #() ;
      rand_cipher := F_rand_cipher }.
  Definition sym_scheme_F : val := sym_scheme.

  (** An IND$-CPA adversary. *)
  Variable adversary : val.
  (* Definition T_IND_CPA_Adv : type := (TMessage → TOption TCipher) → TBool. *)

  Definition lrel_IND_CPA_Adv : lrel Σ :=
    (lrel_message → lrel_option lrel_cipher) → lrel_bool.
  (* Assumption: the adversary is semantically typed. *)
  Hypothesis adversary_sem_typed :
      (⊢ REL adversary << adversary : lrel_IND_CPA_Adv).

  (** The reduction to PRF security. *)
  Definition R_prf : val :=
    λ:"prf_key",
      let: "α" := AllocTape #card_input in
                     (λ: "msg",
                        let: "r" := rand("α") #card_input in
                        let: "z" := "prf_key" "r" in
                        match: "z" with
                        | SOME "z" => SOME ("r", xor "msg" "z")
                        | NONE => NONE
                        end
                     ).


  Definition RED : val :=
    λ:"prf_key", adversary (R_prf "prf_key").

  Section approxis_proofs.

  (* Context `{!approxisRGS Σ}. *)
  Context `{!XOR_spec}.

  Fact R_prf_sem_typed :
    ⊢ REL R_prf << R_prf :
      (lrel_input → lrel_option lrel_output) → lrel_message → lrel_option lrel_cipher.
  Proof with (rel_pures_r ; rel_pures_l).
    rel_arrow ; iIntros (f f') "#hff'" ; rel_pures_l ; rel_pures_r.
    rewrite /R_prf...
    rel_alloctape_l α as "α".
    rel_alloctape_r α' as "α'"...
    iApply (refines_na_alloc ( α ↪N (card_input; []) ∗ α' ↪ₛN (card_input; []))%I
              (nroot.@"tapes")) ; iFrame.
    iIntros "#Hinv".
    rel_arrow_val ; lrintro "msg"...
    rel_bind_l (rand(_) _)%E. rel_bind_r (rand(_) _)%E. rel_apply (refines_bind _ _ _ lrel_input).

    { iApply (refines_na_inv with "[$Hinv]"); [done|].
      iIntros "(> (α & α') & Hclose)".
      iMod ec_zero.
      rel_apply (refines_couple_TT_err card_input card_input _ _ _ _ _ _ _ _ 0%R) => // ; [lra|].
      iFrame. iIntros (?) "(?&?&%)"...
      rel_apply (refines_rand_r with "[$]") ; iIntros "α' %".
      rel_apply (refines_rand_l). iFrame. iIntros "!> α %".
      iApply (refines_na_close with "[-]") ; iFrame ; iFrame. rel_vals. }
    lrintro "r"...
    rel_bind_l (f _). rel_bind_r (f' _). rel_apply refines_bind.
    { rel_apply refines_app. 1: done. rel_vals. }
    lrintro "z"...
    1: rel_vals.
    rel_bind_l (xor _ _). rel_bind_r (xor _ _). rel_apply refines_bind.
    { repeat rel_apply refines_app.
      1: rel_vals ; iApply xor_sem_typed. all: rel_vals. }
    iIntros (??) "(%c&->&->&%&%)"... rel_vals. Unshelve. exact Σ.
  Qed.

  Fact red_sem_typed : (⊢ REL RED <<  RED : lrel_PRF_Adv).
  Proof with (rel_pures_r ; rel_pures_l).
    rel_arrow ; iIntros (f f') "#hff'" ; rel_pures_l ; rel_pures_r.
    unfold RED...
    rel_apply refines_app => //.
    1: try iApply adversary_sem_typed.
    rel_apply refines_app => //. iApply R_prf_sem_typed.
  Qed.

  Lemma reduction :
    ⊢ (REL (adversary (CPA_real sym_scheme_F #Q))
         << (RED (PRF_real PRF_scheme_F #Q)) : lrel_bool).
  Proof with (rel_pures_l ; rel_pures_r).
    rewrite /PRF_scheme_F/PRF_real...
    rewrite /CPA_real/symmetric.CPA_real/symmetric.get_keygen.
    rel_pures_l. rewrite /F_keygen/get_keygen...
    rel_bind_l (keygen _)%E. rel_bind_r (keygen _)%E.
    unshelve iApply (refines_bind _ _ _ lrel_key with "[-] []").
    1: rel_apply refines_app ; [iApply keygen_sem_typed|by rel_values].
    lrintro "key" => /=...
    rewrite /get_enc...
    rewrite /F_enc/prf_enc/get_prf...
    rel_bind_l (prf #key)%E. rel_bind_r (prf #key)%E.
    iApply (refines_bind with "[-] []").
    1: rel_apply refines_app ; [iApply F_sem_typed|].
    1: rel_values ; iExists _ ; easy.
    iIntros (F_key F_key') "#rel_prf_key". simpl...
    rewrite {2}/q_calls_poly. rel_pures_r.
    rel_alloc_r counter_r as "counter_r"...
    rewrite /RED. rel_pures_r.
    rel_bind_l (q_calls_poly _ _ _ _). rel_bind_r (R_prf _).
    iApply (refines_bind with "[-] []").
    2:{ simpl. iIntros (f f') "H_f_f'".
        rel_pures_r.
        iApply refines_app. 1: iApply adversary_sem_typed.
        rel_values. }
    simpl. rewrite /R_prf... rewrite /q_calls_poly...
    rel_alloctape_l α as "α".
    rel_alloctape_r α' as "α'"...
    rel_alloc_l counter_l as "counter_l"...
    iApply (refines_na_alloc
              ( ∃ (q : Z) xs ys, counter_l ↦ #q
                                 ∗ counter_r ↦ₛ #q
                                 ∗ (α ↪N (card_input; xs))
                                 ∗ (α' ↪ₛN (card_input; []))
                                 ∗ (⌜(q < Q)%Z⌝ -∗ ⌜xs = [] ∧ ys = []⌝)
              )%I
              (nroot.@"RED")).
    iSplitL ; [iFrame|]. 1: by iExists [].
    iIntros "#Hinv".
    rel_arrow_val ; lrintro "msg"...
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "(> (%q & %xs & %ys & counter_l & counter_r & α & α' & HqQ) & Hclose)".
    destruct_decide (@bool_decide_reflect (q < Q)%Z _) as qQ.

    - iDestruct ("HqQ" $! _) as "(-> & ->)".
      iMod ec_zero.
      rel_apply (refines_couple_TT_err card_input card_input _ _ _ _ _ _ _ _ 0%R) ; [auto|lra|].
      iFrame. iIntros (r) "(α&?&%)"...
      rel_apply (refines_rand_r with "[$]")...
      iIntros "α' %"...
      rel_load_l ; rel_load_r...
      case_bool_decide as qQ' ; [|by exfalso]...
      rel_load_l ; rel_load_r... rel_store_l ; rel_store_r...
      rel_apply_l (refines_rand_l with "[-$α]") ; iIntros "!> α %"...
      iApply (refines_na_close with "[-]") ; iFrame ; iFrame.
      iSplitL ; iFrame. 1: iExists [] ; iFrame ; done.

      rel_bind_l (F_key #r)%E. rel_bind_r (F_key' #r)%E.
      iApply (refines_bind with "[-] []") => /=.
      { iApply "rel_prf_key". rel_vals. }
      lrintro "z"...
      rel_bind_l (xor _ _)%E. rel_bind_r (xor _ _)%E.
      iApply (refines_bind _ _ _ lrel_output with "[-] []") => /=.
      { repeat rel_apply refines_app ; rel_values.
        1: iApply xor_sem_typed. 1,2: rel_vals. }
      lrintro "x"... rel_vals.
    - rel_apply (refines_randT_empty_r with "[-$α']").
      iIntros (?) "α' %"...
      rel_load_l ; rel_load_r...
      case_bool_decide as qQ' ; [by exfalso|]...
      iApply (refines_na_close with "[-]").
      iFrame. iFrame. rel_vals. Unshelve. 1: exact nat. done.
  Qed.

  Definition I := random_function.
  Definition PRF_scheme_I := (prf_params, keygen, I, rand_output)%V.

  (* Should be just syntactic since PRF_rand doesn't use the PRF. *)
  Lemma PRF_F_I :
    ⊢ (REL (PRF_rand PRF_scheme_F #Q)
         << (PRF_rand PRF_scheme_I #Q) : (lrel_input → lrel_option lrel_output)).
  Proof with (rel_pures_l ; rel_pures_r).
    rewrite /PRF_scheme_F/PRF_scheme_I/PRF_rand...
    unshelve rel_apply refines_app.
    1: exact (lrel_input → lrel_output)%lrel.
    - rel_arrow. iIntros (rf rf') "#hrf"...
      rel_apply refines_app => //.
      { rel_arrow. iIntros... done. }
      rel_apply refines_app => //.
      rel_apply refines_app. 2: iApply refines_typed ; tychk. simpl.
      iPoseProof (q_calls_poly_sem_typed $! lrel_input #() #() _) as "bla".
      rel_bind_l (q_calls_poly #()). rel_bind_r (q_calls_poly #()).
      rel_apply refines_bind.
      1: iApply "bla".
      iIntros (??) "#foo".
      iApply ("foo" $! lrel_output) => //.
    - rewrite /get_card_output/get_param_card_output/get_params... iApply random_function_sem_typed.
      Unshelve. 2: eauto. exact [].
  Qed.

  Lemma F_I :
    ⊢ (REL (RED (PRF_rand PRF_scheme_F #Q))
         << (RED (PRF_rand PRF_scheme_I #Q)) : lrel_bool).
  Proof.
    rel_apply refines_app.
    1: iApply red_sem_typed.
    iApply PRF_F_I.
  Qed.

  Definition I_enc := prf_enc I.
  Definition sym_scheme_I :=
    (@symmetric.sym_params sym_params, (λ:"_", #card_output), I_enc, dec, F_rand_cipher)%V.

  Fact red_r_prf :
    ⊢ REL RED
        (PRF_rand PRF_scheme_I #Q)
        <<
        (adversary (R_prf (PRF_rand PRF_scheme_I #Q)))%V
    : lrel_bool.
  Proof with (rel_pures_r ; rel_pures_l).
    rewrite /PRF_scheme_I/sym_scheme_I/PRF_rand/CPA_real/symmetric.CPA_real...
    rewrite /I_enc. rewrite /prf_enc/get_card_output/get_params/get_param_card_output...
    rel_bind_l (random_function _). rel_bind_r (random_function _). rel_apply refines_bind.
    1: iApply random_function_sem_typed.
    iIntros (rf rf') "#rf"...
    rel_bind_l (q_calls_poly _ _ _ _). rel_bind_r (q_calls_poly _ _ _ _).
    rel_apply refines_bind.
    {
      rel_apply refines_app. 2: by rel_arrow_val.
      rel_apply refines_app. 2: iApply refines_typed ; tychk. simpl.
      iPoseProof (q_calls_poly_sem_typed $! lrel_input #() #() _) as "bla".
      rel_bind_l (q_calls_poly #()). rel_bind_r (q_calls_poly #()).
      rel_apply refines_bind.
      1: iApply "bla".
      iIntros (??) "#foo".
      iApply ("foo" $! lrel_output) => //. }
    iIntros. rewrite /RED...
    rel_apply refines_app.
    1: iApply adversary_sem_typed.
    rel_apply refines_app. 1: iApply R_prf_sem_typed.
    rel_values.
    Unshelve. all: by constructor.
  Qed.

  Fact r_prf_cpa_real :
    ⊢ REL (R_prf (PRF_rand PRF_scheme_I #Q))
        << (CPA_real sym_scheme_I #Q) : (lrel_message → lrel_option lrel_cipher).
  Proof with (rel_pures_r ; rel_pures_l).
    rewrite /PRF_scheme_I/sym_scheme_I/PRF_rand/CPA_real/symmetric.CPA_real/get_card_output/get_param_card_output/get_params...
    rewrite /symmetric.get_keygen/get_enc...
    rewrite /I_enc. rewrite /prf_enc. rewrite /RED/R_prf. rewrite /I...
    rel_bind_l (random_function _). rel_bind_r (random_function _). rel_apply refines_bind.
    1: iApply random_function_sem_typed.
    iIntros (rf rf') "#rf"...

    rewrite /q_calls_poly...
    rel_alloc_l counter_l as "counter_l"...
    rel_alloctape_l α as "α".
    rel_alloctape_r α' as "α'".
    rel_alloc_r counter_r as "counter_r"...
    iApply (refines_na_alloc
              ( ∃ (q : Z) (ys : list nat), counter_l ↦ #q
                                                ∗ counter_r ↦ₛ #q
                                                ∗ (α ↪N (card_input; []))
                                                ∗ (α' ↪ₛN (card_input; ys))
                                                ∗ (⌜(q < Q)%Z⌝ -∗ ⌜ys = []⌝)
              )%I
              (nroot.@"RED")).
    iFrame ; iSplitL ; [by iFrame|].
    iIntros "#Hinv".
    rel_arrow_val.
    lrintro "msg".
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "(> (%q & %ys & counter_l & counter_r & α & α' & hα) & Hclose)".
    destruct_decide (@bool_decide_reflect (q < Q)%Z _) as qQ...

    - iDestruct ("hα" $! _) as "->".
      iMod ec_zero.
      rel_apply (refines_couple_TT_err card_input card_input _ _ _ _ _ _ _ _ 0%R) ; [auto|lra|].
      iFrame. iIntros (r) "(α&α'&%)"...
      rel_apply (refines_rand_l with "[-$α]")...
      iIntros "!> α %"...
      rel_load_l ; rel_load_r...
      case_bool_decide as qQ' ; [|by exfalso]...
      rel_load_l. rel_load_r... rel_store_l ; rel_store_r...
      rel_apply_r (refines_rand_r with "[$α']") ; iIntros "α' %"...
      iApply (refines_na_close with "[-]") ;
        iFrame ; repeat iSplitL. 1: by iFrame.
      rel_bind_l (rf _). rel_bind_r (rf' _). rel_apply refines_bind.
      1: iApply "rf" ; rel_vals.
      lrintro "z"...
      rel_bind_l (xor _ _). rel_bind_r (xor _ _).
      iApply (refines_bind _ _ _ lrel_output with "[-] []") => /=.
      { repeat rel_apply refines_app ; rel_vals.
        1: iApply xor_sem_typed. all: rel_vals. }
      lrintro "x"... rel_vals.

    - rel_apply (refines_randT_empty_l with "[-$α]"). iIntros "!>" (?) "α %"...
      rel_load_l ; rel_load_r...
      case_bool_decide as qQ' ; [by exfalso|]...
      iApply (refines_na_close with "[-]").
      iFrame ; iFrame "α". rel_vals. Unshelve. 1: assumption.
  Qed.

  Lemma reduction'' :
    ⊢ REL adversary (R_prf (PRF_rand PRF_scheme_I #Q))
        << adversary (CPA_real sym_scheme_I #Q) : lrel_bool.
  Proof with (rel_pures_l ; rel_pures_r).
    rel_apply refines_app. 1: iApply adversary_sem_typed.
    iApply r_prf_cpa_real.
  Qed.

  Lemma reduction' :
    ⊢ (REL (RED (PRF_rand PRF_scheme_I #Q))
         << (adversary (CPA_real sym_scheme_I #Q)) : lrel_bool).
  Proof with (rel_pures_l ; rel_pures_r).
    rewrite /RED.
    rewrite /PRF_scheme_I/sym_scheme_I/PRF_rand/CPA_real/symmetric.CPA_real/get_card_output/get_params/get_param_card_output...
    rewrite /symmetric.get_keygen/get_enc...
    rewrite /I_enc. rewrite /prf_enc. rewrite /RED/R_prf. rewrite /I...
    rel_bind_l (random_function _). rel_bind_r (random_function _). rel_apply refines_bind.
    1: iApply random_function_sem_typed.
    iIntros (rf rf') "#rf"...

    rel_alloctape_r α' as "α'"...
    rewrite /q_calls_poly...
    rel_alloc_l counter_l as "counter_l"...
    rel_alloctape_l α as "α".
    rel_alloc_r counter_r as "counter_r"...
    rel_apply refines_app.
    1: iApply adversary_sem_typed.
    iApply (refines_na_alloc
              ( ∃ (q : Z) (ys : list nat), counter_l ↦ #q
                                                ∗ counter_r ↦ₛ #q
                                                ∗ (α ↪N (card_input; []))
                                                ∗ (α' ↪ₛN (card_input; ys))
                                                ∗ (⌜(q < Q)%Z⌝ -∗ ⌜ys = []⌝)
              )%I
              (nroot.@"RED")).
    iFrame ; iSplitL ; [by iFrame|].
    iIntros "#Hinv".
    rel_arrow_val.
    lrintro "msg".
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "(> (%q & %ys & counter_l & counter_r & α & α' & hα) & Hclose)".
    destruct_decide (@bool_decide_reflect (q < Q)%Z _) as qQ...

    - iDestruct ("hα" $! _) as "->".
      iMod ec_zero.
      rel_apply (refines_couple_TT_err card_input card_input _ _ _ _ _ _ _ _ 0%R) ; [auto|lra|].
      iFrame. iIntros (r) "(α&α'&%)"...
      rel_apply (refines_rand_l with "[-$α]")...
      iIntros "!> α %"...
      rel_load_l ; rel_load_r...
      case_bool_decide as qQ' ; [|by exfalso]...
      rel_load_l. rel_load_r... rel_store_l ; rel_store_r...
      rel_apply_r (refines_rand_r with "[$α']") ; iIntros "α' %"...
      iApply (refines_na_close with "[-]") ;
        iFrame ; repeat iSplitL. 1: by iFrame.
      rel_bind_l (rf _). rel_bind_r (rf' _). rel_apply refines_bind.
      1: iApply "rf" ; rel_vals.
      lrintro "z"...
      rel_bind_l (xor _ _). rel_bind_r (xor _ _).
      iApply (refines_bind _ _ _ lrel_output with "[-] []") => /=.
      { repeat rel_apply refines_app ; rel_vals.
        1: iApply xor_sem_typed. all: rel_vals. }
      lrintro "x"... rel_vals.

    - rel_apply (refines_randT_empty_l with "[-$α]"). iIntros "!>" (?) "α %"...
      rel_load_l ; rel_load_r...
      case_bool_decide as qQ' ; [by exfalso|]...
      iApply (refines_na_close with "[-]").
      iFrame ; iFrame "α". rel_vals. Unshelve. 1: assumption.
  Qed.

  Definition q_calls' {Q : nat} {counter : loc} (f : val) : val :=
    λ: "x",
      if: ! #counter < #Q
      then #counter <- ! #counter + #1;; InjR (f "x") else
        InjLV #().
  Definition rand_fun {map_l} :=
    (λ: "x",
       match: get #map_l "x" with
         InjL <> => let: "y" := rand #card_output in set #map_l "x" "y";; "y"
       | InjR "y" => "y"
       end)%V.
  Definition prf_enc' (prf_key : val) α := (λ: "msg",
       let: "r" := rand(#lbl:α) #card_input in
       let: "z" := prf_key "r" in ("r", xor "msg" "z"))%V.

  (* This should be the result proven for the Approxis paper. *)
  Lemma cpa_I :
    ↯ ε_Q
    ⊢ (REL (adversary (CPA_real sym_scheme_I #Q))
         << (adversary (CPA_rand sym_scheme_I #Q)) : lrel_bool).
  Proof with (rel_pures_l ; rel_pures_r).
    iIntros "ε".
    rel_apply refines_app ; [iApply adversary_sem_typed|].
    rewrite /CPA_real/CPA_rand.
    rewrite /symmetric.CPA_real/symmetric.CPA_rand...
    rewrite /symmetric.get_keygen/get_enc/get_rand_cipher...
    rewrite /I_enc/I...
    (* should be more or less the old proof. *)
    rewrite /prf_enc...
    rewrite /random_function/prf.random_function...
    rel_bind_l (init_map #())%E. iApply refines_init_map_l. iIntros (map_l) "map_l" => /=...
    rewrite /q_calls_poly...
    rel_alloc_r counter_r as "counter_r"...
    rel_alloctape_l α as "α".
    rel_alloc_l counter_l as "counter_l"...

    iApply (refines_na_alloc
              (∃ (q : nat) M,
                  ↯ (((Q-1)*Q-(q-1)*q) / (2 * S card_input))
                  ∗ counter_l ↦ #q
                  ∗ counter_r ↦ₛ #q
                  ∗ map_list map_l M
                  ∗ ⌜ size (dom M) = q ⌝
                  ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S card_input)%nat ⌝
                  ∗ α ↪N (card_input; [])
              )%I
              (nroot.@"cpa")); iFrame.
    iSplitL.
    1: { iExists 0.
         rewrite INR_0.
         replace ((Q-1)*Q-(0-1)*0)%R with ((Q-1)*Q)%R by lra.
         iFrame. iPureIntro; set_solver.
    }
    iIntros "#Hinv". rel_arrow_val. lrintro "msg".
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "(> (%q & %M & ε & counter & counter' & mapref & %dom_q & %dom_range & α) & Hclose)".

    fold (@rand_fun map_l).
    fold (@prf_enc' (@rand_fun map_l) α).
    fold (@q_calls' Q counter_l (@prf_enc' (@rand_fun map_l) α)).
    fold F_rand_cipher. fold (@q_calls' Q counter_r F_rand_cipher).

    rewrite /q_calls'...

    rel_load_l ; rel_load_r...
    case_bool_decide as Hq.
    + rel_load_l ; rel_load_r... rel_store_l ; rel_store_r...
      rewrite /prf_enc'/F_rand_cipher...
      assert (Z.to_nat msg < S Message) as Hmsg by lia.
      pose proof nat_to_fin_list _ (elements(dom M)) dom_range as [l' Hl'].
      rel_apply (refines_tape_couple_avoid _ α l').
      { apply NoDup_fmap with fin_to_nat; first apply fin_to_nat_inj.
        rewrite Hl'. apply NoDup_elements. }
      replace (length l') with q; last first.
      { erewrite <-fmap_length, Hl'.
        by replace (length (elements (dom M))) with (size (dom M)).
      }
      pose proof pos_INR_S (card_input).
      assert (0<=q/S card_input)%R.
      { apply Rcomplements.Rdiv_le_0_compat; last done.
        apply pos_INR. }
      assert (q < Q)%nat by lia.
      assert (q < Q)%R. 1: by apply lt_INR.
      assert (q * (q + 1) <= (Q - 1) * Q)%R.
      {
        rewrite -INR_1.
        apply Rmult_le_compat ; try real_solver.
        - rewrite -minus_INR. 2: lia. apply le_INR. lia.
        - rewrite -plus_INR. apply le_INR. lia.
      }
      assert (0 <= ((Q - 1) * Q - q * (q + 1)))%R.
      1: lra.
      assert (0<=((Q-1) * Q - q * (q+1))/(2*S card_input))%R.
      1: apply Rcomplements.Rdiv_le_0_compat ; lra.
      iDestruct (ec_weaken _ (q/S card_input+(((Q-1) * Q - q * (q + 1)))/ (2 * S card_input)) with "[$]") as "ε".
      {
        split ; [lra|].
        apply Rcomplements.Rle_minus_r.
        rewrite Rminus_def -Rdiv_opp_l -Rdiv_plus_distr.
        rewrite Rdiv_mult_distr.
        rewrite !Rdiv_def.
        apply Rmult_le_compat_r.
        { apply Rlt_le. by apply Rinv_0_lt_compat. }
        rewrite -Rcomplements.Rle_div_r; last lra.
        trans ((q + 1) * q - q*(q-1))%R ; last lra.
        lra.
      }
      iDestruct (ec_split with "[$]") as "[ε ε']"; [done|done|].
      iFrame.
      iIntros (r_in) "!> %r_fresh α"...
      rewrite /rand_fun...
      rel_apply_l (refines_get_l with "[-mapref] [$mapref]").
      iIntros (?) "mapref #->"...
      assert ((M !! fin_to_nat r_in) = None) as r_fresh_M.
      { apply not_elem_of_dom_1. rewrite -elem_of_elements. rewrite -Hl'.
        intros K. apply elem_of_list_fmap_2_inj in K; [done | apply fin_to_nat_inj]. }
      rewrite r_fresh_M...
      unshelve rel_apply (refines_couple_UU _ (@xor_sem _ _ xor_struct (Z.to_nat msg))) ;
        [apply xor_bij|apply xor_dom => //|..].
      iIntros (y) "!> %"...
      rel_apply_l (refines_set_l with "[-mapref] [$mapref]") ; iIntros "mapref"...
      rel_bind_l (xor _ _).
      rel_apply_l xor_correct_l; [done | lia | lia |].
      iApply (refines_na_close with "[-]") ; iFrame ; iSplitL.
      { replace (Z.of_nat q + 1)%Z with (Z.of_nat (q+1)) by lia.
        iFrame.
        replace ((q+1)%nat - 1)%R with (INR q).
        2:{ replace 1%R with (INR 1) => //.
            rewrite -minus_INR. 2: lia. f_equal. lia. }
        replace (INR (q+1)%nat) with (q+1)%R.
        2:{ rewrite plus_INR. replace (INR 1) with 1%R => //. }
        iFrame.
        iPureIntro; split.
        - rewrite size_dom. rewrite size_dom in dom_q.
          rewrite map_size_insert_None; first lia. assumption.
        - intros x. rewrite elem_of_elements. set_unfold.
          intros [|]; last naive_solver.
          subst. apply fin_to_nat_lt. }
      idtac... rel_values. repeat iExists _.
      iModIntro. iRight. repeat iSplit ; iPureIntro ; eauto.
      simpl. repeat unshelve eexists ; try by lia.
      * assert (r_in <= card_input). 2: lia. clear. apply fin.fin_to_nat_le.
      * cut ((xor_sem (Z.to_nat msg) y < S card_output)) ; [lia|].
        apply xor_dom ; lia.
    + iApply (refines_na_close with "[-]").
      iFrame. iSplit ; [done|]... rel_vals.
  Qed.

  (* Should be just syntactic since CPA_rand doesn't use the PRF. *)
  Lemma cpa_F :
    ⊢ (REL (adversary (CPA_rand sym_scheme_I #Q))
         << (adversary (CPA_rand sym_scheme_F #Q)) : lrel_bool).
  Proof with (rel_pures_l ; rel_pures_r).
    rewrite /sym_scheme_I/sym_scheme_F/I_enc/F_enc/I.
    rewrite /CPA_rand/symmetric.CPA_rand/get_rand_cipher. idtac...
    rel_apply refines_app. 1: iApply adversary_sem_typed.
    rel_apply (refines_app _ _ _ _ (lrel_message → lrel_cipher)%lrel).
    2:{ rewrite /F_rand_cipher... rel_arrow_val ; lrintro...
        unshelve rel_apply (refines_couple_UU) => //.
        iModIntro ; iIntros...
        unshelve rel_apply (refines_couple_UU) => //.
        iModIntro ; iIntros...
        rel_vals.
    }
    rel_apply refines_app. 2: iApply refines_typed ; tychk. simpl.
    iPoseProof (q_calls_poly_sem_typed $! lrel_message #() #() _) as "bla".
    rel_bind_l (q_calls_poly #()). rel_bind_r (q_calls_poly #()).
    rel_apply refines_bind.
    1: iApply "bla".
    iIntros (??) "#foo".
    iApply ("foo" $! lrel_cipher) => //.
    Unshelve.
    1: exact []. done.
  Qed.

  End approxis_proofs.

(*   (* Next, we will:
        - for each step of logical refinement, write the corresponding ARcoupling
        - chain these together to obtain an ARcoupling for one direction
        - admit the other direction
        - combine both directions to get a bound on the difference of observing a #true
      *)

     Ltac lr_arc := unshelve eapply approximates_coupling ; eauto ;
                    [apply (λ _, lrel_bool)|try lra|by iIntros (???) "#(%b&->&->)"|iIntros].

     Lemma reduction_ARC Σ `{approxisRGpreS Σ} (bla : forall (HΣ' : approxisRGS Σ), @XOR_spec Σ HΣ' card_output card_output xor_struct) σ σ' :
       ARcoupl (lim_exec ((adversary (CPA_real sym_scheme_F #Q)), σ))
         (lim_exec ((RED (PRF_real PRF_scheme_F #Q)), σ'))
         eq 0.
     Proof. lr_arc ; iApply reduction. Qed.

     Lemma F_I_ARC Σ `{approxisRGpreS Σ} (bla : forall (HΣ' : approxisRGS Σ), @XOR_spec Σ HΣ' Message card_output xor_struct) σ σ' :
       ARcoupl (lim_exec ((RED (PRF_rand PRF_scheme_F #Q)), σ))
         (lim_exec ((RED (PRF_rand PRF_scheme_I #Q)), σ'))
         eq 0.
     Proof. lr_arc ; iApply F_I. Qed.

     Lemma reduction'_ARC Σ `{approxisRGpreS Σ} (bla : forall (HΣ' : approxisRGS Σ), @XOR_spec Σ HΣ' Message card_output xor_struct) σ σ' :
       ARcoupl (lim_exec ((RED (PRF_rand PRF_scheme_I #Q)), σ))
         (lim_exec ((adversary (CPA_real sym_scheme_I #Q)), σ'))
         eq 0.
     Proof. lr_arc ; iApply reduction'. Qed.

     Fact ε_Q_pos : (0 <= ε_Q)%R.
     Proof.
       unfold ε_Q, ε_bday.
       destruct Q. 1: rewrite INR_0 ; lra.
       rewrite -INR_1. rewrite -minus_INR. 2: lia. simpl.
       repeat apply Rmult_le_pos ; try apply pos_INR.
       pose proof Rdiv_INR_ge_0 (S card_input).
       cut ((0 <= (2*1) / (2 * INR (S card_input))))%R ; first (rewrite /N ; lra).
       rewrite Rdiv_mult_distr. lra.
     Qed.

     Lemma cpa_I_ARC Σ `{!approxisRGpreS Σ} (bla : forall (HΣ' : approxisRGS Σ), @XOR_spec Σ HΣ' Message card_output xor_struct) σ σ' :
       ARcoupl (lim_exec ((adversary (CPA_real sym_scheme_I #Q)), σ))
         (lim_exec ((adversary (CPA_rand sym_scheme_I #Q)), σ'))
         eq ε_Q.
     Proof. lr_arc. 1: apply ε_Q_pos. iApply cpa_I. iFrame. Qed.

     Lemma cpa_F_ARC Σ `{approxisRGpreS Σ} (bla : forall (HΣ' : approxisRGS Σ), @XOR_spec Σ HΣ' Message card_output xor_struct) σ σ' :
       ARcoupl (lim_exec ((adversary (CPA_rand sym_scheme_I #Q)), σ))
         (lim_exec ((adversary (CPA_rand sym_scheme_F #Q)), σ'))
         eq 0.
     Proof. lr_arc ; iApply cpa_F. Qed.

     (** The PRF advantage of RED against F. *)
     Definition ε_F :=
       advantage (RED (PRF_real PRF_scheme_F #Q)) (RED (PRF_rand PRF_scheme_F #Q)) #true.

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
       (∀ HΣ' : approxisRGS Σ, XOR_spec) →
       ARcoupl (lim_exec ((adversary (CPA_real sym_scheme_F #Q)), σ))
         (lim_exec ((adversary (CPA_rand sym_scheme_F #Q)), σ'))
         eq (ε_Q + ε_F).
     Proof.
       intros.
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
       eapply cpa_F_ARC => //.
       Unshelve. all: eauto.
     Qed.

     (* The converse direction of the refinement. We expect it to hold with the
        same bound. *)
     Variable prf_cpa_ARC' : forall Σ `{approxisRGpreS Σ} σ σ',
       ARcoupl (lim_exec ((adversary (CPA_rand sym_scheme_F #Q)), σ))
         (lim_exec ((adversary (CPA_real sym_scheme_F #Q)), σ'))
         eq (ε_Q + ε_F).

     Corollary CPA_bound_1 Σ `{approxisRGpreS Σ} σ σ' :
       (∀ HΣ' : approxisRGS Σ, XOR_spec) →
       ( (lim_exec ((adversary (CPA_real sym_scheme_F #Q)), σ) #true)
         <= (lim_exec ((adversary (CPA_rand sym_scheme_F #Q)), σ') #true)
            + (ε_Q + ε_F))%R.
     Proof. intros. apply ARcoupl_eq_elim. by eapply prf_cpa_ARC. Qed.

     Corollary CPA_bound_2 Σ `{approxisRGpreS Σ} σ σ' :
       (∀ HΣ' : approxisRGS Σ, XOR_spec) →
       ( (lim_exec ((adversary (CPA_rand sym_scheme_F #Q)), σ) #true)
         <= (lim_exec ((adversary (CPA_real sym_scheme_F #Q)), σ') #true)
            + (ε_Q + ε_F))%R.
     Proof using prf_cpa_ARC'. intros ; apply ARcoupl_eq_elim. by eapply prf_cpa_ARC'. Qed.

     Theorem CPA_bound_st Σ `{approxisRGpreS Σ} σ σ' :
       (∀ HΣ' : approxisRGS Σ, XOR_spec) →
       (pr_dist (adversary (CPA_real sym_scheme_F #Q)) (adversary (CPA_rand sym_scheme_F #Q)) σ σ' #true
        <= ε_Q + ε_F)%R.
     Proof.
       intros.
       apply Rabs_le.
       pose proof (CPA_bound_1 Σ σ σ' _).
       pose proof (CPA_bound_2 Σ σ' σ _).
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
     Lemma red_to_prf Σ `{approxisRGpreS Σ} (_ : ∀ HΣ' : approxisRGS Σ, XOR_spec) σ σ' :
       ARcoupl (lim_exec (adversary (CPA_real sym_scheme_F #Q), σ))
         (lim_exec ((RED (PRF_real PRF_scheme_F #Q)), σ')) eq 0%R.
     Proof. eapply reduction_ARC => //. Qed.

     (* The reverse direction *)
     Hypothesis red_to_prf' : forall Σ `{approxisRGpreS Σ} σ σ',
       ARcoupl (lim_exec ((RED (PRF_real PRF_scheme_F #Q)), σ'))
         (lim_exec (adversary (CPA_real sym_scheme_F #Q), σ)) eq 0%R.

     (* Combine to get the pr_dist bound. *)
     Lemma pr_dist_adv_F `{approxisRGpreS Σ} (_ : ∀ HΣ' : approxisRGS Σ, XOR_spec) v σ σ' :
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
       - opose proof (ARcoupl_eq_elim _ _ _ (red_to_prf _ _ σ σ') v) as hred.
         set (x := (lim_exec (adversary _, σ)) v).
         set (y := lim_exec (RED _, σ') v).
         assert (x <= y + 0)%R by easy.
         lra.
     Qed.

     (* Reduce from CPA security to a statement about PRF security of F (rand side) *)
     Lemma red_from_prf Σ `{approxisRGpreS Σ} (_ : ∀ HΣ' : approxisRGS Σ, XOR_spec) σ σ' :
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
     Qed.

     (* The reverse direction *)
     Hypothesis red_from_prf' : forall Σ `{approxisRGpreS Σ} σ σ',
       ARcoupl (lim_exec (adversary (CPA_rand sym_scheme_F #Q), σ'))
         (lim_exec (RED (PRF_rand PRF_scheme_F #Q), σ))
         eq ε_Q.

     (* Combine to get the pr_dist bound. *)
     Lemma pr_dist_F_adv `{approxisRGpreS Σ} (_ : ∀ HΣ' : approxisRGS Σ, XOR_spec) v σ σ' :
       (pr_dist (RED (PRF_rand PRF_scheme_F #Q)) (adversary (CPA_rand sym_scheme_F #Q)) σ σ' v
        <= ε_Q)%R.
     Proof.
       rewrite /pr_dist. eapply Rabs_le. split.
       - opose proof (ARcoupl_eq_elim _ _ _ (red_from_prf' _ σ σ') v) as hred.
         set (x := lim_exec (RED _, σ) v).
         set (y := (lim_exec (adversary _, σ')) v).
         assert (y <= x + ε_Q)%R by easy. lra.
       - opose proof (ARcoupl_eq_elim _ _ _ (red_from_prf _ _ σ σ') v) as hred.
         set (x := lim_exec (RED _, σ) v).
         set (y := (lim_exec (adversary _, σ')) v).
         assert (x <= y + ε_Q)%R by easy. lra.
     Qed.

     (* Same statement as CPA_bound_st but proven without assuming H_ε_ARC or H_ε_LR. *)
     Theorem CPA_bound_st' Σ `{approxisRGpreS Σ} (_ : ∀ HΣ' : approxisRGS Σ, XOR_spec) σ σ' :
       (pr_dist (adversary (CPA_real sym_scheme_F #Q)) (adversary (CPA_rand sym_scheme_F #Q)) σ σ' #true
        <= ε_Q + ε_F)%R.
     Proof.
       eapply pr_dist_triangle.
       1: eapply pr_dist_adv_F => //.
       1: eapply pr_dist_triangle.
       2: eapply pr_dist_F_adv => //.
       1: eapply (advantage_ub).
       1: right ; eauto.
       unfold ε_Q, ε_F. lra.
     Qed.

     Theorem CPA_bound Σ `{approxisRGpreS Σ} (_ : ∀ HΣ' : approxisRGS Σ, XOR_spec) :
       (advantage
          (adversary (CPA_real sym_scheme_F #Q))
          (adversary (CPA_rand sym_scheme_F #Q))
          #true
        <= ε_Q + ε_F)%R.
     Proof.
       apply advantage_uniform => //. intros.
       eapply CPA_bound_st => //.
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

      *) *)

End combined.
