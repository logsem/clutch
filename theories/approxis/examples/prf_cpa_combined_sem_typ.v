From clutch.prob_lang.typing Require Import tychk.
From clutch.approxis Require Import approxis map list.
From clutch.approxis.examples Require Import prf symmetric security_aux xor advantage.
Set Default Proof Using "Type*".

Section combined.

  (*** A PRF *)

  (** PRF Parameters. *)
  Variable Key : nat.
  Variable Input : nat.
  Variable Output : nat.

  Definition N := S Input.

  Definition PRF_real : val :=
    let keygen PRF_scheme : expr := Fst PRF_scheme in
    let prf PRF_scheme : expr := Fst (Snd PRF_scheme) in
    λ:"PRF_scheme" "Q",
      let: "k" := keygen "PRF_scheme" #() in
      let: "lookup" := prf "PRF_scheme" "k" in
      let: "oracle" := q_calls_poly #() #() "Q" "lookup" in
      "oracle".

  Definition PRF_rand : val :=
    let rand_output PRF_scheme : expr := Snd (Snd PRF_scheme) in
    λ:"PRF_scheme" "Q",
      let: "lookup" := random_function Output #() in
      let: "oracle" := q_calls_poly #() #() "Q" "lookup" in
      "oracle".

  (** PRF Security: Local instances of the PRF games. **)
  (* Definition PRF_rand := PRF_rand Input Output.
     Definition PRF_real := PRF_real Input. *)
  (* Max number of oracle calls *)
  Variable (Q : nat).

  Let ε_Q := (INR Q * INR Q / (2 * INR N))%R.

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


  Definition lrel_key {Σ} : lrel Σ := lrel_int_bounded 0 Key.
  Definition lrel_input {Σ} : lrel Σ := lrel_int_bounded 0 Input.
  Definition lrel_output {Σ} : lrel Σ := lrel_int_bounded 0 Output.
  Definition lrel_keygen `{!approxisRGS Σ} : lrel Σ := (lrel_unit → lrel_key).
  Definition lrel_prf `{!approxisRGS Σ} : lrel Σ := lrel_key → lrel_input → lrel_output.

  Definition lrel_PRF_Adv `{!approxisRGS Σ} := ((lrel_input → (lrel_option lrel_output)) → lrel_bool)%lrel.

  (** Assumption: the PRF is typed. *)
  (* TODO: The type TPRF requires F to be safe for all inputs ; maybe this
     assumption is unrealistic, and F should only be required to be safe only
     for inputs in {0..Key}x{0..Input}. *)
  Hypothesis F_typed : (⊢ᵥ F : TPRF).
  Hypothesis keygen_typed : (⊢ᵥ keygen : TKeygen).
  Hypothesis F_sem_typed : forall `{!approxisRGS Σ}, (⊢ REL F << F : lrel_prf).
  Hypothesis keygen_sem_typed : forall `{!approxisRGS Σ}, (⊢ REL keygen << keygen : lrel_keygen).


  (*** Symmetric scheme sym_scheme_F based on the PRF **)
  (** Symmetric Scheme Parameters **)
  Let Message := Output.
  Let Cipher := Input * Output.

  (** Security for Symmetric Encryption *)
  (* Let CPA_real := CPA_real Message.
     Let CPA_rand := CPA_rand Message. *)

  Definition CPA_real : val :=
    let keygen scheme : expr := Fst scheme in
    let enc scheme : expr := Fst (Snd scheme) in
    λ:"scheme" "Q",
      let: "key" := keygen "scheme" #() in
      q_calls_poly #() #() "Q" (enc "scheme" "key").

  Definition CPA_rand : val :=
    let rand_cipher scheme : expr := Snd (Snd scheme) in
    λ:"scheme" "Q",
      q_calls_poly #() #() "Q" (rand_cipher "scheme").

  (** RandML typing *)
  Definition TMessage := TInt.
  Definition TCipher := (TInput * TOutput)%ty.
  Definition lrel_message {Σ} : lrel Σ := lrel_int_bounded 0 Message.
  Definition lrel_cipher {Σ} : lrel Σ := lrel_input * lrel_output.

  (** Parameters required for the construction of sym_scheme_F *)
  (* An abstract `xor`, in RandML and in Coq. *)
  Context `{XOR Message Output}.
  (* TODO relax typing of xor to be semantic *)

  Hypothesis xor_sem_typed : forall `{!approxisRGS Σ} (Key Support : nat) (xor_struct : @XOR Key Support),
    ⊢ (lrel_int_bounded 0 Key → lrel_int_bounded 0 Support → lrel_int_bounded 0 Support)%lrel
        (@xor _ _ xor_struct) (@xor _ _ xor_struct).

  (** Generic PRF-based symmetric encryption. *)
  (* Redefined here to make it parametrised by the PRF on the Coq level. *)
  Definition prf_enc (prf : val) : val :=
    λ:"key",
      let: "prf_key" := prf "key" in
      let: "α" := AllocTape #Input in
      λ: "msg",
        let: "r" := rand("α") #Input in
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

  Definition lrel__IND_CPA_Adv `{!approxisRGS Σ} : lrel Σ :=
    (lrel_message → lrel_option lrel_cipher) → lrel_bool.
  (* Assumption: the adversary is semantically typed. *)
  Hypothesis adversary_sem_typed : forall `{!approxisRGS Σ},
      (⊢ REL adversary << adversary : lrel__IND_CPA_Adv).

  (** The reduction to PRF security. *)
  Definition R_prf : val :=
    λ:"prf_key",
      let: "α" := AllocTape #Input in
                     (λ: "msg",
                        let: "r" := rand("α") #Input in
                        let: "z" := "prf_key" "r" in
                        match: "z" with
                        | SOME "z" => SOME ("r", xor "msg" "z")
                        | NONE => NONE
                        end
                     ).


  Definition RED : val :=
    λ:"prf_key", adversary (R_prf "prf_key").

  (* TODO prove this rule, generalizing the lhs to be an arbitrary term e *)
  Hypothesis refines_tape_couple_avoid : forall `{!approxisRGS Σ} (N:nat) α l z E K K' A,
    NoDup l ->
    TCEq N (Z.to_nat z) →
    ↯ (length l / (S N)) ∗
    α ↪N (Input; []) ∗
    ▷ (∀ (n : fin (S N)), ⌜n ∉ l⌝ -∗ α ↪N (Input; []) -∗ REL fill K (Val #n) << fill K' (Val #n) @ E : A)
    ⊢ REL fill K (rand(#lbl:α) #z) << fill K' (rand #z) @ E : A.

  Ltac rel_vals' :=
    lazymatch goal with
    | |- environments.envs_entails _ (_ (InjRV _) (InjRV _)) =>
        iExists _,_ ; iRight ; iSplit ; [eauto|iSplit ; eauto]
    | |- environments.envs_entails _ (_ (InjLV _) (InjLV _)) =>
        iExists _,_ ; iLeft ; iSplit ; [eauto|iSplit ; eauto]
    | |- environments.envs_entails _ (_ (_ , _)%V (_ , _)%V) =>
        iExists _,_,_,_ ; iSplit ; [eauto|iSplit ; [eauto | iSplit]]
    | |- environments.envs_entails _ (_ _ (lrel_int_bounded _ _) _ _) =>
        iExists _ ; iPureIntro ; intuition lia
    | |- environments.envs_entails _ (_ _ lrel_input _ _) =>
        iExists _ ; iPureIntro ; intuition lia
    | |- environments.envs_entails _ (_ _ lrel_output _ _) =>
        iExists _ ; iPureIntro ; intuition lia
    | _ => fail "rel_vals: case not covered"
    end.
  Ltac rel_vals := try rel_values ; repeat iModIntro ; repeat (rel_vals' ; eauto).

  Section approxis_proofs.

  Context `{!approxisRGS Σ}.

    Ltac pattern_of_lr lr x :=
      (* idtac "hello " lr x ; *)
      let bounded := constr:(append "(%" (x ++ "&->&->&%" ++ x ++ "_min&%" ++ x ++ "_max)")) in
      lazymatch lr with
      | lrel_input => bounded
      | lrel_output => bounded
      | lrel_message => bounded
      | lrel_int_bounded _ _ => bounded
      | lrel_key => bounded
      | lrel_int => constr:("(%&->&->)")
      | @lrel_unit => constr:("(->&->)")
      | lrel_option ?A =>
          let a := pattern_of_lr A x in
          let u := pattern_of_lr lrel_unit x in
          constr:(append "#(%" (" " ++ "&% &[(->&->&" ++ u ++ ") | (->&->&"++a++")])"))
      | _ => fail 0 "lrintro: encountered unhandled logical relation: " lr
      end.

  Local Tactic Notation "lrintro" constr(x) :=
    try iIntros (??) ;
    lazymatch goal with
    | |- environments.envs_entails _ (lrel_car ?A _ _ -∗ _) =>
        let x' := pattern_of_lr A x in
        iIntros x'
    end.

  Fact R_prf_sem_typed :
    ⊢ REL R_prf << R_prf :
      (lrel_input → lrel_option lrel_output) → lrel_message → lrel_option lrel_cipher.
  Proof using (xor_sem_typed)
    with (rel_pures_r ; rel_pures_l).
    rel_arrow ; iIntros (f f') "#hff'" ; rel_pures_l ; rel_pures_r.
    rewrite /R_prf...
    rel_alloctape_l α as "α".
    rel_alloctape_r α' as "α'"...
    iApply (refines_na_alloc ( α ↪N (Input; []) ∗ α' ↪ₛN (Input; []))%I
              (nroot.@"tapes")) ; iFrame.
    iIntros "#Hinv".
    rel_arrow_val ; lrintro "msg"...
    rel_bind_l (rand(_) _)%E. rel_bind_r (rand(_) _)%E. rel_apply (refines_bind _ _ _ lrel_input).

    { iApply (refines_na_inv with "[$Hinv]"); [done|].
      iIntros "(> (α & α') & Hclose)".
      iMod ec_zero.
      rel_apply (refines_couple_TT_err Input Input _ _ _ _ _ _ _ _ 0%R) => // ; [lra|].
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
    iIntros (??) "(%c&->&->&%&%)"... rel_vals.
  Qed.

  Fact red_sem_typed : (⊢ REL RED <<  RED : lrel_PRF_Adv).
  Proof using (xor_sem_typed adversary_sem_typed)
    with (rel_pures_r ; rel_pures_l).
    rel_arrow ; iIntros (f f') "#hff'" ; rel_pures_l ; rel_pures_r.
    unfold RED...
    rel_apply refines_app => //.
    1: iApply adversary_sem_typed.
    rel_apply refines_app => //. iApply R_prf_sem_typed.
  Qed.

  Lemma reduction :
    ⊢ (REL (adversary (CPA_real sym_scheme_F #Q))
         << (RED (PRF_real PRF_scheme_F #Q)) : lrel_bool).
  Proof using (xor_sem_typed adversary_sem_typed keygen_sem_typed Key F_sem_typed)
    with (rel_pures_l ; rel_pures_r).
    rewrite /PRF_scheme_F/PRF_real/prf.PRF_real...
    rewrite /CPA_real/symmetric.CPA_real.
    rel_pures_l. rewrite /F_keygen.
    rel_bind_l (keygen _)%E. rel_bind_r (keygen _)%E.
    unshelve iApply (refines_bind _ _ _ lrel_key with "[-] []").
    1: rel_apply refines_app ; [iApply keygen_sem_typed|by rel_values].
    lrintro "key" => /=...
    rewrite /F_enc/prf_enc...
    rel_bind_l (F #key)%E. rel_bind_r (F #key)%E.
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
                                 ∗ (α ↪N (Input; xs))
                                 ∗ (α' ↪ₛN (Input; []))
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
      rel_apply (refines_couple_TT_err Input Input _ _ _ _ _ _ _ _ 0%R) ; [auto|lra|].
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

  Definition I := random_function Output.
  Definition PRF_scheme_I := (λ:"_", #(), (I, rand_output))%V.

  Fact random_function_sem_typed A :
    ⊢ REL random_function Output
        << random_function Output : A → lrel_input → lrel_output.
  Proof using (Cipher F F_keygen F_sem_typed F_typed H Input Key Message Output
                 Q adversary adversary_sem_typed adversary_typed approxisRGS0 keygen
                 keygen_sem_typed keygen_typed refines_tape_couple_avoid xor_sem_typed Σ ε_Q)
    with (rel_pures_l ; rel_pures_r).
    rel_arrow_val ; iIntros (??) "_".
    rewrite /random_function...
    rel_bind_r (init_map #()). iApply refines_init_map_r => /=... iIntros (map_r) "map_r".
    rel_bind_l (init_map #()). iApply refines_init_map_l. iIntros (map_l) "map_l" => /=...
    iApply (refines_na_alloc
              ( ∃ (M : gmap nat val),
                  map_list map_l M
                  ∗ map_slist map_r M
                  ∗ ⌜ ∀ y, y ∈ @map_img nat val (gmap nat val) _ (gset val) _ _ _ M
                           → ∃ k : nat, y = #k ∧ k <= Output ⌝
                  ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S Input)%nat ⌝
              )%I
              (nroot.@"RED")) ; iFrame.
    iSplitL ; iFrame.
    1: { iPureIntro; split ; [|set_solver].
         intros y hy. exfalso. clear -hy.
         rewrite map_img_empty in hy.
         opose proof (proj1 (elem_of_empty y) hy). done.
    }
    iIntros "#Hinv".
    rel_arrow_val ; lrintro "x"...
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "(> (%M & map_l & map_r & %range_int & %dom_range) & Hclose)".
    rel_bind_l (get _ _). rel_bind_r (get _ _).
    opose proof (IZN x _) as [x' ->] => //. rename x' into x.
    rel_apply_l (refines_get_l with "[-map_l] [$map_l]"). iIntros (?) "map_l #->"...
    rel_apply_r (refines_get_r with "[-map_r] [$map_r]"). iIntros (?) "map_r #->"...

    destruct (M !! x) as [y |] eqn:x_fresh ...
    + iApply (refines_na_close with "[-]") ;
        iFrame ; repeat iSplitL.
      { iFrame. iNext. iFrame. iPureIntro. split. 2: set_solver. done. }
      opose proof (elem_of_map_img_2 M x y x_fresh) as hy.
      destruct (range_int y hy) as [y' [??]]. subst. rel_vals.
    + rel_apply (refines_couple_UU Output id); first auto.
      iIntros (y) "!> %"...
      rel_apply_r (refines_set_r with "[-map_r] [$map_r]"). iIntros "map_r"...
      rel_apply_l (refines_set_l with "[-map_l] [$map_l]"). iIntros "map_l"...
      iApply (refines_na_close with "[-]") ;
        iFrame ; repeat iSplitL. 1: iExists _ ; iFrame.
      1: { iPureIntro.
           repeat split ; last first.
           - rewrite -Forall_forall.
             rewrite dom_insert.
             rewrite elements_union_singleton.
             + apply Forall_cons_2. 1: lia. rewrite Forall_forall. done.
             + apply not_elem_of_dom_2. done.
           - intros y' hy'. rewrite (map_img_insert M x (#y)) in hy'.
             rewrite elem_of_union in hy'. destruct hy'.
             + exists y. set_solver.
             + apply range_int.
               opose proof (delete_subseteq M x).
               eapply map_img_delete_subseteq. done.
      }
      rel_vals. Unshelve. all: apply _.
  Qed.

  (* Should be just syntactic since PRF_rand doesn't use the PRF. *)
  Lemma PRF_F_I :
    ⊢ (REL (PRF_rand PRF_scheme_F #Q)
         << (PRF_rand PRF_scheme_I #Q) : (lrel_input → lrel_option lrel_output)).
Proof using (Cipher F F_keygen F_sem_typed F_typed H Input Key Message Output
Q adversary adversary_sem_typed adversary_typed approxisRGS0 keygen
keygen_sem_typed keygen_typed refines_tape_couple_avoid xor_sem_typed Σ ε_Q)
    with (rel_pures_l ; rel_pures_r).
    rewrite /PRF_scheme_F/PRF_scheme_I/PRF_rand/prf.PRF_rand...
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
    - rel_apply refines_app. 1: iApply (random_function_sem_typed lrel_unit).
      rel_vals.
      Unshelve. 2: eauto. exact [].
  Qed.

  Lemma F_I :
    ⊢ (REL (RED (PRF_rand PRF_scheme_F #Q))
         << (RED (PRF_rand PRF_scheme_I #Q)) : lrel_bool).
  Proof using (xor_sem_typed refines_tape_couple_avoid keygen_typed keygen_sem_typed
                 adversary_typed adversary_sem_typed F_typed F_sem_typed).
    rel_apply refines_app.
    1: iApply red_sem_typed.
    iApply PRF_F_I.
  Qed.

  Definition I_enc := prf_enc I.
  Definition sym_scheme_I := (λ:"_", #(), (I_enc, F_rand_cipher))%V.

  Fact red_r_prf :
    ⊢ REL RED
        (PRF_rand PRF_scheme_I #Q)
        <<
        (adversary (R_prf (PRF_rand PRF_scheme_I #Q)))%V
    : lrel_bool.
  Proof using (Cipher F F_keygen F_sem_typed F_typed H Input Key Message Output
                 Q adversary adversary_sem_typed adversary_typed approxisRGS0 keygen
                 keygen_sem_typed keygen_typed refines_tape_couple_avoid xor_sem_typed Σ ε_Q)
    with (rel_pures_r ; rel_pures_l).
    rewrite /PRF_scheme_I/sym_scheme_I/PRF_rand/prf.PRF_rand/CPA_real/symmetric.CPA_real...
    rewrite /I_enc. rewrite /prf_enc.
    (* rewrite /RED/R_prf. rewrite /I... *)
    rel_bind_l (random_function _ _). rel_bind_r (random_function _ _). rel_apply refines_bind.
    1: rel_apply refines_app ; [iApply (random_function_sem_typed lrel_unit)|rel_vals].
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
Proof using (Cipher F F_keygen F_sem_typed F_typed H Input Key Message Output
Q adversary adversary_sem_typed adversary_typed approxisRGS0 keygen
keygen_sem_typed keygen_typed refines_tape_couple_avoid xor_sem_typed Σ ε_Q)
 with (rel_pures_r ; rel_pures_l).
    rewrite /PRF_scheme_I/sym_scheme_I/PRF_rand/prf.PRF_rand/CPA_real/symmetric.CPA_real...
    rewrite /I_enc. rewrite /prf_enc. rewrite /RED/R_prf. rewrite /I...
    rel_bind_l (random_function _ _). rel_bind_r (random_function _ _). rel_apply refines_bind.
    1: rel_apply refines_app ; [iApply (random_function_sem_typed lrel_unit)|rel_vals].
    iIntros (rf rf') "#rf"...

    rewrite /q_calls_poly...
    rel_alloc_l counter_l as "counter_l"...
    rel_alloctape_l α as "α".
    rel_alloctape_r α' as "α'".
    rel_alloc_r counter_r as "counter_r"...
    iApply (refines_na_alloc
              ( ∃ (q : Z) (ys : list nat), counter_l ↦ #q
                                                ∗ counter_r ↦ₛ #q
                                                ∗ (α ↪N (Input; []))
                                                ∗ (α' ↪ₛN (Input; ys))
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
      rel_apply (refines_couple_TT_err Input Input _ _ _ _ _ _ _ _ 0%R) ; [auto|lra|].
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
  Proof
    using (keygen_typed adversary_typed refines_tape_couple_avoid F_typed
             xor_sem_typed keygen_sem_typed adversary_sem_typed Key F_sem_typed)
    with (rel_pures_l ; rel_pures_r).
    rel_apply refines_app. 1: iApply adversary_sem_typed.
    iApply r_prf_cpa_real.
  Qed.

  Lemma reduction' :
    ⊢ (REL (RED (PRF_rand PRF_scheme_I #Q))
         << (adversary (CPA_real sym_scheme_I #Q)) : lrel_bool).
  Proof
    using (keygen_typed adversary_typed refines_tape_couple_avoid F_typed
             xor_sem_typed keygen_sem_typed adversary_sem_typed Key F_sem_typed)
    with (rel_pures_l ; rel_pures_r).
    rewrite /RED.
    rewrite /PRF_scheme_I/sym_scheme_I/PRF_rand/prf.PRF_rand/CPA_real/symmetric.CPA_real...
    rewrite /I_enc. rewrite /prf_enc. rewrite /RED/R_prf. rewrite /I...
    rel_bind_l (random_function _ _). rel_bind_r (random_function _ _). rel_apply refines_bind.
    1: rel_apply refines_app ; [iApply (random_function_sem_typed lrel_unit)|rel_vals].
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
                                                ∗ (α ↪N (Input; []))
                                                ∗ (α' ↪ₛN (Input; ys))
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
      rel_apply (refines_couple_TT_err Input Input _ _ _ _ _ _ _ _ 0%R) ; [auto|lra|].
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
         InjL <> => let: "y" := rand #Output in set #map_l "x" "y";; "y"
       | InjR "y" => "y"
       end)%V.
  Definition prf_enc' (prf_key : val) α := (λ: "msg",
       let: "r" := rand(#lbl:α) #Input in
       let: "z" := prf_key "r" in ("r", xor "msg" "z"))%V.

  (* This should be the result proven for the Approxis paper. *)
  (* TODO actually isolate the part that does the "sampling without repetition"
     into a reusable lemma. *)
  Lemma cpa_I `{!XOR_spec} :
    ↯ ε_Q
    ⊢ (REL (adversary (CPA_real sym_scheme_I #Q))
         << (adversary (CPA_rand sym_scheme_I #Q)) : lrel_bool).
  Proof
    using (adversary_typed keygen_typed F_typed xor_sem_typed refines_tape_couple_avoid
             keygen_sem_typed adversary_sem_typed Key F_sem_typed)
    with (rel_pures_l ; rel_pures_r).
    iIntros "ε".
    rel_apply refines_app ; [iApply adversary_sem_typed|].
    rewrite /CPA_real/CPA_rand.
    rewrite /symmetric.CPA_real/symmetric.CPA_rand...
    rewrite /F_rand_cipher.
    rewrite /I_enc/I...
    (* should be more or less the old proof. *)
    rewrite /prf_enc...
    rewrite /random_function...
    rel_bind_l (init_map #())%E. iApply refines_init_map_l. iIntros (map_l) "map_l" => /=...
    rewrite /q_calls_poly...
    rel_alloc_r counter_r as "counter_r"...
    rel_alloctape_l α as "α".
    rel_alloc_l counter_l as "counter_l"...

    iApply (refines_na_alloc
              (∃ (q : nat) M,
                  ↯ ((Q*Q-q*q) / (2 * S Input))
                  ∗ counter_l ↦ #q
                  ∗ counter_r ↦ₛ #q
                  ∗ map_list map_l M
                  ∗ ⌜ size (dom M) = q ⌝
                  ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S Input)%nat ⌝
                  ∗ α ↪N (Input; [])
              )%I
              (nroot.@"cpa")); iFrame.
    iSplitL.
    1: { iExists 0.
         rewrite INR_0.
         replace (Q*Q-0*0)%R with (Q*Q)%R by lra.
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
      iIntros (r_in) "!> %r_fresh α"...
      rewrite /rand_fun...
      rel_apply_l (refines_get_l with "[-mapref] [$mapref]").
      iIntros (?) "mapref #->"...
      assert ((M !! fin_to_nat r_in) = None) as r_fresh_M.
      { apply not_elem_of_dom_1. rewrite -elem_of_elements. rewrite -Hl'.
        intros K. apply elem_of_list_fmap_2_inj in K; [done | apply fin_to_nat_inj]. }
      rewrite r_fresh_M...
      unshelve rel_apply (refines_couple_UU _ (@xor_sem _ _ H (Z.to_nat msg))) ;
        [apply xor_bij|apply xor_dom => //|..].
      iIntros (y) "!> %"...
      rel_apply_l (refines_set_l with "[-mapref] [$mapref]") ; iIntros "mapref"...
      rel_bind_l (xor _ _).
      rel_apply_l xor_correct_l; [done | lia | lia |].
      iApply (refines_na_close with "[-]") ; iFrame ; iSplitL.
      { replace (Z.of_nat q + 1)%Z with (Z.of_nat (q+1)) by lia.
        iFrame. iPureIntro; split.
        - rewrite size_dom. rewrite size_dom in dom_q.
          rewrite map_size_insert_None; first lia. assumption.
        - intros x. rewrite elem_of_elements. set_unfold.
          intros [|]; last naive_solver.
          subst. apply fin_to_nat_lt. }
      idtac... rel_values. repeat iExists _.
      iModIntro. iRight. repeat iSplit ; iPureIntro ; eauto.
      simpl. repeat unshelve eexists ; try by lia.
      * assert (r_in <= Input). 2: lia. clear. apply fin.fin_to_nat_le.
      * cut ((xor_sem (Z.to_nat msg) y < S Output)) ; [lia|].
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
    rewrite /CPA_rand/symmetric.CPA_rand. idtac...
    replace lrel_bool with (interp TBool []) by auto.
    iApply refines_typed. rewrite /F_rand_cipher. tychk.
    1: apply adversary_typed.
    rewrite /q_calls_poly. tychk.
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
  Proof using (xor_sem_typed keygen_sem_typed adversary_sem_typed Key
F_sem_typed).
    lr_arc ; iApply reduction.
  Qed.

  Lemma F_I_ARC Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl (lim_exec ((RED (PRF_rand PRF_scheme_F #Q)), σ))
      (lim_exec ((RED (PRF_rand PRF_scheme_I #Q)), σ'))
      eq 0.
  Proof using xor_sem_typed refines_tape_couple_avoid keygen_typed keygen_sem_typed
    adversary_typed adversary_sem_typed Key F_typed F_sem_typed.
    lr_arc ; iApply F_I.
  Qed.

  Lemma reduction'_ARC Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl (lim_exec ((RED (PRF_rand PRF_scheme_I #Q)), σ))
      (lim_exec ((adversary (CPA_real sym_scheme_I #Q)), σ'))
      eq 0.
  Proof using (keygen_typed F_typed adversary_typed
                 xor_sem_typed refines_tape_couple_avoid keygen_sem_typed
                 adversary_sem_typed Key F_sem_typed).
    lr_arc ; iApply reduction'.
  Qed.

  Fact ε_Q_pos : (0 <= ε_Q)%R.
  Proof.
    repeat apply Rmult_le_pos ; try apply pos_INR.
    pose proof Rdiv_INR_ge_0 (S Input).
    cut ((0 <= (2*1) / (2 * INR (S Input))))%R ; first (rewrite /N ; lra).
    rewrite Rdiv_mult_distr. lra.
  Qed.

  Lemma cpa_I_ARC Σ `{!approxisRGpreS Σ} (bla : forall (HΣ' : approxisRGS Σ), @XOR_spec Σ HΣ' Message Output H) σ σ' :
    ARcoupl (lim_exec ((adversary (CPA_real sym_scheme_I #Q)), σ))
      (lim_exec ((adversary (CPA_rand sym_scheme_I #Q)), σ'))
      eq ε_Q.
  Proof using F_typed adversary_typed keygen_typed xor_sem_typed
    refines_tape_couple_avoid keygen_sem_typed adversary_sem_typed Key F_sem_typed.
    lr_arc. 1: apply ε_Q_pos. iApply cpa_I. iFrame.
  Qed.

  Lemma cpa_F_ARC Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl (lim_exec ((adversary (CPA_rand sym_scheme_I #Q)), σ))
      (lim_exec ((adversary (CPA_rand sym_scheme_F #Q)), σ'))
      eq 0.
  Proof using F_typed adversary_typed keygen_typed
  refines_tape_couple_avoid keygen_sem_typed adversary_sem_typed Key F_sem_typed.
    lr_arc ; iApply cpa_F. Qed.

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
  Proof using F_typed H_ε_ARC H_ε_LR adversary_typed keygen_typed prf_cpa_ARC'
  refines_tape_couple_avoid keygen_sem_typed adversary_sem_typed Key F_sem_typed.
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
  Proof using keygen_sem_typed adversary_sem_typed Key
F_sem_typed xor_sem_typed.
    eapply reduction_ARC => //. Qed.

  (* The reverse direction *)
  Hypothesis red_to_prf' : forall Σ `{approxisRGpreS Σ} σ σ',
    ARcoupl (lim_exec ((RED (PRF_real PRF_scheme_F #Q)), σ'))
      (lim_exec (adversary (CPA_real sym_scheme_F #Q), σ)) eq 0%R.

  (* Combine to get the pr_dist bound. *)
  Lemma pr_dist_adv_F `{approxisRGpreS Σ} v σ σ' :
    (pr_dist (adversary (CPA_real sym_scheme_F #Q)) (RED (PRF_real PRF_scheme_F #Q)) σ σ' v
     <= 0)%R.
  Proof using xor_sem_typed red_to_prf' keygen_sem_typed adversary_sem_typed Key F_sem_typed.
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
  Proof using xor_sem_typed refines_tape_couple_avoid red_to_prf'
    red_from_prf' prf_cpa_ARC' keygen_typed keygen_sem_typed adversary_typed
    adversary_sem_typed Key H_ε_LR H_ε_ARC F_typed F_sem_typed.
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
  Proof using Cipher F F_keygen F_sem_typed F_typed H H_ε_ARC H_ε_LR
    Input Key Message Output Q adversary adversary_sem_typed adversary_typed
    keygen keygen_sem_typed keygen_typed prf_cpa_ARC' refines_tape_couple_avoid
    ε_Q.
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
