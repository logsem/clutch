From clutch.approxis Require Import approxis map list.
From clutch.approxis.examples Require Import prf symmetric prf_cpa security_aux xor.
Set Default Proof Using "Type*".

Section combined.

  (** Parameters of the PRF. *)
  Variable Key : nat.
  Variable Input : nat.
  Variable Output : nat.

  Definition q_calls := q_calls Input.

  Definition N := S Input.

  Local Opaque INR.

  (* The PRF: (keygen, F) *)
  Variable keygen : val.
  Variable F : val.

  Definition rand_output : val := λ:"_", rand #Output.

  (* Max number of oracle calls *)
  Variable (Q : nat).

  (* RandML types *)

  (* PRF *)
  Definition TKey := TNat.
  Definition TInput := TNat.
  Definition TOutput := TNat.
  Definition TPRF : type := TKey → TInput → TOutput.

  (* PRF adversary *)
  Definition T_PRF_Adv := ((TInput → (TOption TOutput)) → TBool)%ty.

  (* Local definitions of the PRF games and PRF scheme. *)
  Definition PRF_rand := PRF_rand Input Output.
  Definition PRF_real := PRF_real Input.
  Definition PRF_scheme_F : val := (keygen, (F, rand_output)).


  (* Symmetric scheme based on the PRF *)
  Let Message := Output.
  Let Cipher := Input * Output.

  Definition TMessage := TInt.
  Definition TKeygen : type := (TUnit → TKey)%ty.
  Definition TCipher := (TInput * TOutput)%ty.

  Context `{XOR Message Output}.

  (* Variable xor : val.
     (** Parameters of the generic PRF-based encryption scheme. *)
     Variable (xor_sem : nat -> nat -> nat).
     Variable H_xor : forall x, Bij (xor_sem x).
     Variable H_xor_dom: forall x, x < S Message -> (∀ n : nat, n < S Output → xor_sem x n < S Output).
     Definition XOR_CORRECT_L := forall `{!approxisRGS Σ} E K (x : Z) (y : nat)
                                (_: (0<=x)%Z)
                                (_: ((Z.to_nat x) < S Message))
                                (_: y < S Message) e A,
       (REL (fill K (of_val #(xor_sem (Z.to_nat x) (y)))) << e @ E : A)
       -∗ REL (fill K (xor #x #y)) << e @ E : A.
     Definition XOR_CORRECT_R := ∀ `{!approxisRGS Σ} E K (x : Z) (y : nat)
                                (_: (0<=x)%Z)
                                (_: ((Z.to_nat x) < S Message))
                                (_: y < S Message) e A,
       (REL e << (fill K (of_val #(xor_sem (Z.to_nat x) (y)))) @ E : A)
       -∗ REL e << (fill K (xor #x #y)) @ E : A.
     Variable (xor_correct_l: XOR_CORRECT_L).
     Variable (xor_correct_r: XOR_CORRECT_R).
     (* TODO: should xor be partial? `xor key input` may fail unless 0 <= key <=
        Key /\ 0 <= input <= Input

        If xor were to operate on strings / byte arrays / bit lists instead, it
        may fail if `key` and `input` are of different lengths. *)
     Hypothesis xor_typed : (⊢ᵥ xor : (TMessage → TOutput → TOutput)). *)
  Hypothesis keygen_typed : (⊢ᵥ keygen : TKeygen).
  Hypothesis F_typed : (⊢ᵥ F : TPRF).
  Hypothesis H_in_out : (Input = Output).


  (* An IND$-CPA adversary. *)
  Variable adversary : val.
  Definition T_IND_CPA_Adv : type := (TMessage → TOption TCipher) → TBool.
  Variable adversary_typed : (⊢ᵥ adversary : T_IND_CPA_Adv).


  (** The reduction to PRF security. *)
  (* PROOF SKETCH *)
  (* CPA security starts from (adversary (CPA_real sym_scheme_F #Q)). *)
  (* Via some administrative reductions, CPA_real sym_scheme_F #Q evaluates
     to: *)
  (* let: "key" := keygen #() in
     q_calls #Q
       ( let: "prf_key" := F "key" in
         λ: "msg",
           let: "r" := rand #Input in
           let: "z" := "prf_key" "r" in
           ("r", xor "msg" "z") ). *)
  (* Goal: find R_prf s.t. this is equivalent to (R_prf (PRF_real PRF_scheme_F #Q)) *)
  (* Reduce (PRF_real PRF_scheme_F #Q): *)
  (* let: "key" := keygen #() in
     q_calls #Q (F "key").
     (* Let R_prf := *)
     λ:"prf_key",
         q_calls #Q
           (λ: "msg"
              let: "r" := rand #Input in
              let: "z" := "prf_key" "r" in
              ("r", xor "msg" "z")). *)
  (* Now we have (R_prf (PRF_real PRF_scheme_F #Q)) ≈ *)
  (* let: "key" := keygen #() in
     q_calls #Q
           (λ: "msg"
              let: "r" := rand #Input in
              let: "z" := (q_calls #Q (F "key")) "r" in
              ("r", xor "msg" "z")). *)
  (* We now compose adversary ∘ R_prf to obtain RED. *)

  (* If the security definition of a PRF allowed an arbitrary context as
  adversary (at what logical relation?) instead of a boolean-valued one, we
  could use the assumption that F is an ε_F-secure PRF to directly conclude
  that

    R_prf PRF_real ~ R_prf PRF_rand

  and derive from this, together with well-typedness of adversary, that

    adversary (R_prf PRF_real) ~ adversary (R_prf PRF_rand)

  However, with the current definition, we instead have to construct RED as
  defined below, and prove

    adversary (R_prf PRF_real) ~(1)~ RED PRF_real ~(2)~ RED PRF_rand ~(3)~
    adversary (R_prf PRF_rand)

  where (1) and (3) require some administrative work, and (2) follows from the
  PRF assumption on F.

   *)

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


  Section approxis_proofs.

  Context `{!approxisRGS Σ}.

  Definition PRF_advantage_upper_bound (adversary : val) (ε_F : nonnegreal) :=
    (↯ ε_F ⊢ (REL (adversary (PRF_real PRF_scheme_F #Q)) << (adversary (PRF_rand PRF_scheme_F #Q)) : lrel_bool))
    /\
      (↯ ε_F ⊢ (REL (adversary (PRF_rand PRF_scheme_F #Q)) << (adversary (PRF_real PRF_scheme_F #Q)) : lrel_bool)).

  (* Definition f_is_prf (ε_f : nonnegreal)
       :=
       forall (adversary : val) (adversary_typed : (⊢ᵥ adversary : T_PRF_Adv)),
       (↯ ε_f ⊢ (REL (adversary (PRF_real PRF_scheme_F #Q)) << (adversary (PRF_rand PRF_scheme_F #Q)) : lrel_bool))
       /\
         (↯ ε_f ⊢ (REL (adversary (PRF_rand PRF_scheme_F #Q)) << (adversary (PRF_real PRF_scheme_F #Q)) : lrel_bool)). *)

  (** Generic PRF-based symmetric encryption. *)
  (* Redefined here to make it parametrised by the PRF on the Coq level. *)
  Definition prf_enc (prf : val) : val :=
    λ:"key",
      let: "prf_key" := prf "key" in
      λ: "msg",
        let: "r" := rand #Input in
        let: "z" := "prf_key" "r" in
        ("r", xor "msg" "z").

  (* Let F_keygen := rf_keygen Key. *)
  Let F_keygen := keygen.
  Definition F_enc : val := prf_enc F.
  Let F_rand_cipher := rf_rand_cipher Input Output.
  Definition sym_scheme_F : val := (F_keygen, (F_enc, F_rand_cipher)).

  Let CPA_real := CPA_real Message.
  Let CPA_rand := CPA_rand Message.


(* Simple-minded syntax-directed type checker. The econstructor tactic can go
   wrong by applying non-syntax directed (insufficiently constrained)
   constructors, and get stuck, so we explicitly select constructors where it's
   unambiguous instead.

   The definition is recursive since it uses a very small amount of
   backtracking. Thus, invoking `type_expr N` is not quite equivalent to
   calling `do N type_expr 1`. *)
Ltac type_expr n :=
  lazymatch eval compute in n with
  | O => idtac
  | _ =>
      (* (lazymatch goal with
         | |- ?g => idtac g
         end ) ; *)
      lazymatch goal with
      | |- _ ⊢ₜ Var _ : _ => eapply Var_typed ; (try by eauto)
      | |- _ ⊢ₜ Val _ : _ => eapply Val_typed ; type_val n
      | |- _ ⊢ₜ BinOp ?op _ _ : _ =>
          match eval compute in (binop_int_res_type op) with
          | Some _ => eapply BinOp_typed_int ; [type_expr (n-1) | type_expr (n-1) | try by eauto]
          | _ => match eval compute in (binop_bool_res_type op) with
                 | Some _ => eapply BinOp_typed_bool ; [type_expr (n-1) | type_expr (n-1) | try by eauto]
                 end
          end
      | |- _ ⊢ₜ UnOp ?op _ : _ =>
          match eval compute in (unop_int_res_type op) with
          | Some _ => eapply UnOp_typed_int ; [type_expr (n-1) | try by eauto]
          | _ => match eval compute in (unop_bool_res_type op) with
                 | Some _ => eapply UnOp_typed_bool ; [type_expr (n-1) | try by eauto]
                 end
          end
      | |- _ ⊢ₜ BinOp EqOp _ _ : _ => eapply UnboxedEq_typed ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ Pair _ _ : _ => eapply Pair_typed ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ Fst _ : _ => eapply Fst_typed ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ Snd _ : _ => eapply Snd_typed ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ InjL _ : _ => eapply InjL_typed ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ InjR _ : _ => eapply InjR_typed ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ Case _ _ _ : _ => eapply Case_typed ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ If _ _ _ : _ => eapply If_typed ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ (Rec _ _ _) : _ =>
          (* could also try TLam_typed here *)
          eapply Rec_typed ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ App _ _ : _ =>
          (* could also try TApp_typed here *)
          eapply App_typed ; (try by eauto) ; type_expr (n-1)
      (* | TLam_typed Γ e τ : *)
      (*     ⤉ Γ ⊢ₜ e : τ → *)
      (*     Γ ⊢ₜ (Λ: e) : ∀: τ *)
      (*  | TApp_typed Γ e τ τ' : *)
      (*     Γ ⊢ₜ e : (∀: τ) → *)
      (*     Γ ⊢ₜ e #() : τ.[τ'/] *)
      (*  | TFold Γ e τ : *)
      (*     Γ ⊢ₜ e : τ.[(μ: τ)%ty/] → *)
      (*     Γ ⊢ₜ e : (μ: τ) *)
      (*  | TUnfold Γ e τ : *)
      (*     Γ ⊢ₜ e : (μ: τ)%ty → *)
      (*     Γ ⊢ₜ rec_unfold e : τ.[(μ: τ)%ty/] *)
      (*  | TPack Γ e τ τ' : *)
      (*     Γ ⊢ₜ e : τ.[τ'/] → *)
      (*     Γ ⊢ₜ e : (∃: τ) *)
      (*  | TUnpack Γ e1 x e2 τ τ2 : *)
      (*     Γ ⊢ₜ e1 : (∃: τ) → *)
      (*     <[x:=τ]>(⤉ Γ) ⊢ₜ e2 : (Autosubst_Classes.subst (ren (+1)) τ2) → *)
      (*     Γ ⊢ₜ (unpack: x := e1 in e2) : τ2 *)
      | |- _ ⊢ₜ Alloc _ : _ => eapply TAlloc ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ Load _ : _ => eapply TLoad ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ Store _ _ : _ => eapply TStore ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ AllocTape _ : _ => eapply TAllocTape ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ Rand _ _ : _ =>
          first [ eapply TRand ; (try by eauto) ; [ type_expr (n-1) | by type_expr (n-1) ]
                | eapply TRandU ; (try by eauto) ; type_expr (n-1)]
      | |- _ => idtac
      end
  end

    with type_val n :=
    lazymatch eval compute in n with
    | O => idtac
    | _ =>
        lazymatch goal with
        | |- ⊢ᵥ LitV LitUnit : _ => eapply Unit_val_typed
        | |- ⊢ᵥ _ : TNat => eapply Nat_val_typed
        | |- ⊢ᵥ LitV (LitInt _) : _ => eapply Int_val_typed
        (* | |- ⊢ᵥ LitV (LitInt _) : _ => eapply Nat_val_typed *)
        | |- ⊢ᵥ LitV (LitBool _) : _ => eapply Bool_val_typed
        | |- ⊢ᵥ PairV _ _ : _ => eapply Pair_val_typed ; type_val (n-1)
        | |- ⊢ᵥ InjLV _ : _ => eapply InjL_val_typed ; type_val (n-1)
        | |- ⊢ᵥ InjRV _ : _ => eapply InjR_val_typed ; type_val (n-1)
        | |- ⊢ᵥ RecV _ _ _ : _ => eapply Rec_val_typed ; type_expr (n-1)
        | |- ⊢ᵥ (Λ: _) : (∀: _) => idtac
        (* TODO does this overlap with the RecV case? Does the below work for
        Λ: λ:"x","x"? *)
        (* eapply TLam_val_typed ; type_expr (n-1) *)
        | _ => idtac
        end
    end.

Ltac type_ctx :=
  match goal with
  | |- typed_ctx nil ?ctx_in ?ty_in ?ctx_out ?ty_out =>
      apply TPCTX_nil
  | |- typed_ctx (?k :: ?K) ?ctx_in ?ty_in ?ctx_out ?ty_out =>
      econstructor ; last first ; [type_ctx | econstructor]
  | _ => idtac
  end.

Ltac tychk := try type_ctx ; try type_expr 100 ; try type_val 100.

  Fact red_typed : (⊢ᵥ RED : T_PRF_Adv).
  Proof.
    rewrite /RED. tychk. 1: eauto.
    rewrite /R_prf. constructor.
    type_expr 4.
    all: try by tychk.
    Unshelve.
    1: constructor ; apply opt_mult_typed.
    1: rewrite /q_calls/prf_cpa.q_calls. 1: apply (q_calls_typed Input (TOption TCipher)).
    (* 3: exact (TOption (TOption TCipher)). *)
    all: tychk.
    apply xor_typed.
  Qed.

  (* Should also prove that PPT(adversary) ⇒ PPT(RED). *)

  Lemma reduction :
    ⊢ (REL (adversary (CPA_real sym_scheme_F #Q))
         << (RED (PRF_real PRF_scheme_F #Q)) : lrel_bool).
  Proof.
    rewrite /RED. rel_pures_r.
    rewrite /PRF_scheme_F/PRF_real/prf.PRF_real.
    rel_pures_r.
    rewrite /CPA_real/symmetric.CPA_real.
    rel_pures_l. rewrite /F_keygen/rf_keygen.
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
    rewrite /R_prf. rel_pures_r. rewrite /q_calls/prf_cpa.q_calls.
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


  Definition TList α := (μ: (ref (() + α * #0)))%ty.
  Fact init_list_typed α : ⊢ᵥ init_list : (() → TList α).
  Proof. rewrite /init_list /TList. type_val 1. constructor. tychk. Qed.

  Definition TMap k v : type := ref (TList (k * v)).
  Fact init_map_typed k v : ⊢ᵥ init_map : (() → TMap k v).
  Proof. rewrite /init_map /TMap. type_val 1. constructor. tychk.
         apply init_list_typed.
  Qed.

  Definition find_list : val :=
    (rec: "find" "h" "k" :=
       match: ! (rec_unfold "h") with
         NONE => NONE
       | SOME "p" =>
           let: "kv" := Fst "p" in
           let: "next" := Snd "p" in
           if: (Fst "kv") = "k" then SOME (Snd "kv") else "find" "next" "k"
       end).

(* Hypothesis Subsume_int_nat : forall Γ e, Γ ⊢ₜ e : TNat -> Γ ⊢ₜ e : TInt. *)


Definition type_closed a := ∀ f, (a = a.[f])%ty.
Fact find_list_typed v : type_closed v -> ⊢ᵥ find_list : (TList (TInput * v) → TInput → TOption v).
Proof.
  clear. intros v_closed. set (k := TInput).
  rewrite /find_list. type_val 1.
  type_expr 3 ; try by tychk.
  2: {
    type_expr 5.
    2: tychk. 2: tychk.
    type_expr 1.
    all: apply Subsume_int_nat. all: tychk.
  }
  Unshelve.
  2: exact TUnit.
  (* 3: exact ((k * v) * TList (k * v))%ty. *)
  -

    fold TInput. rewrite -/k.
    set (α := (k * v)%ty).
    set (unfolded := (ref (() + α * TList α))%ty).
    (* set (τ := (λ list, (ref (() + α * (TVar list))))%ty). *)
    assert (unfolded = ((ref (() + α * #0))%ty).[(μ: (ref (() + α * #0)))%ty/]) as hfold.
    { simpl. rewrite /unfolded. replace TNat with TNat.[(μ: (ref (() + α * #0)))%ty/] by easy.
      rewrite /k /TInput. subst α k. simpl. unfold TList, TInput.
      assert (v = v.[μ: ref (() + TNat * v * #0)/])%ty as <-.
      2: done.
      asimpl.
      by rewrite -v_closed.
    }
    rewrite hfold.
    eapply TUnfold ; tychk.
Qed.

Fact get_typed : ⊢ᵥ get : (TMap TInput TOutput → TInput → () + TOutput)%ty.
Proof. rewrite /get. tychk. apply find_list_typed. done. Qed.

Fact set_typed :
  ⊢ᵥ set : (TMap TInput TOutput → TInput → TOutput → TUnit)%ty.
Proof.
  rewrite /set. tychk.
  rewrite /cons_list. type_val 2.
  rewrite /TList.
  constructor.
  simpl. tychk.
Qed.

Fact q_calls_typed_io :
  ⊢ᵥ bounded_oracle.q_calls Input
    : (TInt → (TInput → TOutput) → TInput → TOption TOutput).
Proof.
  rewrite /bounded_oracle.q_calls.
  type_val 8 ; try by tychk.
  all: type_expr 1 ; try by tychk.
  all: apply Subsume_int_nat. all: tychk.
Qed.

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
        - apply get_typed.
        - apply set_typed.
        - apply init_map_typed.
    }
    apply q_calls_typed_io.
Qed.

  Lemma rand_real :
    ⊢ (REL (RED (PRF_rand PRF_scheme_I #Q))
         << (RED (PRF_real PRF_scheme_I #Q)) : lrel_bool).
  Proof with (rel_pures_l ; rel_pures_r).
    rewrite /PRF_scheme_I/PRF_rand/prf.PRF_rand.
    rewrite /PRF_scheme_I/PRF_real/prf.PRF_real...
    rewrite /I/random_function...
    replace lrel_bool with (interp TBool []) by auto.
    iApply refines_typed. tychk.
    1: apply red_typed.
    2: apply get_typed.
    2: apply set_typed.
    2: apply init_map_typed.
    apply q_calls_typed_io.
  Qed.

  Definition I_enc := prf_enc I.
  Definition sym_scheme_I := (λ:"_", #(), (I_enc, F_rand_cipher))%V.
  Lemma reduction' :
    ⊢ (REL (RED (PRF_rand PRF_scheme_I #Q))
         << (adversary (CPA_real sym_scheme_I #Q)) : lrel_bool).
Proof
  using (CPA_rand CPA_real Cipher F F_keygen F_rand_cipher F_typed
H_in_out Input Message Output Q adversary adversary_typed
approxisRGS0 keygen keygen_typed Σ
)
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
    rewrite /q_calls/prf_cpa.q_calls/bounded_oracle.q_calls...
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


    Fact nat_to_fin_list (l:list nat):
      (∀ x, x ∈ l -> (x < S Input)%nat) ->
      ∃ l': (list (fin (S Input))), fin_to_nat <$> l' = l.
    Proof.
      clear.
      induction l as [|a l'].
      - intros. exists []. naive_solver.
      - intros. set_unfold.
        assert (a<S Input) as H' by naive_solver.
        unshelve epose proof IHl' _ as [l ?]; first naive_solver.
        exists (nat_to_fin H'::l).
        simpl.
        repeat f_equal; last done.
        by rewrite fin_to_nat_to_fin.
    Qed.

  (* This should be the result proven for the Approxis paper. *)
  Lemma cpa_I `{!XOR_spec} :
    ↯ (Q * Q / (2 * S Input))
    ⊢ (REL (adversary (CPA_real sym_scheme_I #Q))
         << (adversary (CPA_rand sym_scheme_I #Q)) : lrel_bool).
Proof
  using (CPA_rand CPA_real Cipher F F_rand_cipher F_typed H_in_out
           Input Message Output Q adversary adversary_typed approxisRGS0
keygen keygen_typed Σ)
  with (rel_pures_l ; rel_pures_r).
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
    rewrite /q_calls/prf_cpa.q_calls/bounded_oracle.q_calls...
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
        rewrite /rf_rand_cipher.
        rewrite -bool_decide_and.
        case_bool_decide as Hq.
        + rel_load_l ; rel_load_r... rel_store_l ; rel_store_r...
          assert (Z.to_nat msg < S Message) as Hmsg by lia.
          pose proof nat_to_fin_list (elements(dom M)) dom_range as [l' Hl'].
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
        rewrite /rf_rand_cipher.
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
    iApply refines_typed. tychk.
    1: done.
    -
      rewrite /bounded_oracle.q_calls.
      type_val 8 ; try by tychk.
      (* all: type_expr 1 ; try by tychk.
         all: apply Subsume_int_nat. all: tychk. *)
    - rewrite /F_rand_cipher/rf_rand_cipher. tychk.
  Qed.

  (* Goal
       (↯ (2*ε_F + Q*Q/(2*N)) ⊢ (REL (adversary (CPA_real sym_scheme_F #Q)) << (adversary (CPA_rand sym_scheme_F #Q)) : lrel_bool)).
     Proof.
     Abort. *)
  (* forall adversary ε_f,
       PRF_advantage adversary ε_f ->
       CPA_advantage (RED adversary) (Q*ε_f + Q*Q/2N) (enc_prf f). *)

  End approxis_proofs.

  (* PLAN:
     - for each step of logical refinement, write the corresponding ARcoupling
     - chain these together to obtain an ARcoupling for one direction
     - admit the other direction
     - combine both directions to get a bound on the difference of observing a #true
   *)

  Let CPA_real := CPA_real Message.
  Let CPA_rand := CPA_rand Message.

  Lemma reduction_ARC Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl
      (lim_exec ((adversary (CPA_real sym_scheme_F #Q)), σ))
      (lim_exec ((RED (PRF_real PRF_scheme_F #Q)), σ'))
      (=)
      0.
  Proof.
    unshelve eapply approximates_coupling ; eauto.
    1: exact (fun _ => lrel_bool).
    1: lra.
    1: by iIntros (???) "#(%b&->&->)".
    iIntros. iApply reduction.
  Qed.

  Lemma F_I_ARC Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl
      (lim_exec ((RED (PRF_rand PRF_scheme_F #Q)), σ))
      (lim_exec ((RED (PRF_rand PRF_scheme_I #Q)), σ'))
      (=)
      0.
  Proof.
    unshelve eapply approximates_coupling ; eauto.
    1: exact (fun _ => lrel_bool).
    1: lra.
    1: by iIntros (???) "#(%b&->&->)".
    iIntros. iApply F_I.
  Qed.

  Lemma rand_real_ARC Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl
      (lim_exec ((RED (PRF_rand PRF_scheme_I #Q)), σ))
      (lim_exec ((RED (PRF_real PRF_scheme_I #Q)), σ'))
      (=)
      0.
  Proof.
    unshelve eapply approximates_coupling ; eauto.
    1: exact (fun _ => lrel_bool).
    1: lra.
    1: by iIntros (???) "#(%b&->&->)".
    iIntros. iApply rand_real.
  Qed.

  Lemma reduction'_ARC Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl
      (lim_exec ((RED (PRF_rand PRF_scheme_I #Q)), σ))
      (lim_exec ((adversary (CPA_real sym_scheme_I #Q)), σ'))
      (=)
      0.
  Proof using CPA_rand CPA_real Cipher F F_typed H_in_out Input
    Message Output Q adversary adversary_typed keygen keygen_typed.
    unshelve eapply approximates_coupling ; eauto.
    1: exact (fun _ => lrel_bool).
    1: lra.
    1: by iIntros (???) "#(%b&->&->)".
    iIntros. iApply reduction'.
  Qed.


  Let ε_Q := (INR Q * INR Q / (2 * INR (S Input)))%R.

  Fact ε_collision_pos : (0 <= ε_Q)%R.
  Proof.
    { repeat apply Rmult_le_pos; try apply pos_INR.
      rewrite -Rdiv_1_l.
      pose proof Rdiv_INR_ge_0 (S Input).
      cut ((0 <= (2*1) / (2 * INR (S Input))))%R; first lra.
      rewrite Rmult_comm.
      rewrite Rmult_div_swap.
      rewrite (Rmult_comm 2%R).
      rewrite Rdiv_mult_distr.
      lra.
    }
  Qed.

  Lemma cpa_I_ARC Σ `{!approxisRGpreS Σ} (bla : forall (HΣ' : approxisRGS Σ), @XOR_spec Σ HΣ' Message Output H) σ σ' :
    ARcoupl
      (lim_exec ((adversary (CPA_real sym_scheme_I #Q)), σ))
      (lim_exec ((adversary (CPA_rand sym_scheme_I #Q)), σ'))
      (=)
      ε_Q.
Proof using CPA_rand CPA_real Cipher F F_typed H_in_out Input
Message Output Q adversary adversary_typed keygen keygen_typed

.
    unshelve eapply approximates_coupling ; eauto.
    1: exact (fun _ => lrel_bool).
    1: apply ε_collision_pos.
    1: by iIntros (???) "#(%b&->&->)".
    iIntros. iApply cpa_I. iFrame.
  Qed.

  Lemma cpa_F_ARC Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl
      (lim_exec ((adversary (CPA_rand sym_scheme_I #Q)), σ))
      (lim_exec ((adversary (CPA_rand sym_scheme_F #Q)), σ'))
      (=)
      0.
  Proof using CPA_rand CPA_real Cipher F F_typed H_in_out Input
    Message Output Q adversary adversary_typed keygen keygen_typed.
    unshelve eapply approximates_coupling ; eauto.
    1: exact (fun _ => lrel_bool).
    1: lra.
    1: by iIntros (???) "#(%b&->&->)".
    iIntros. iApply cpa_F.
  Qed.

  (* We will now explore different ways of stating the assumption that F is a
     PRF. Concretely, we will need to assume that the advantage of the
     adversary RED, which was constructed by reduction from the adversary
     against the symmetric scheme, is bounded by some number ε_F. *)
  Variable ε_F : nonnegreal.

  (* We may assume that owning ↯ ε_F error credits allows to prove the
     refinement about RED in Approxis. *)
  Hypothesis H_ε_PRF : forall `{approxisRGS Σ},
      PRF_advantage_upper_bound RED ε_F.

  (* By adequacy, we deduce from the previous assumption that a corresponding
     approximate refinement coupling holds up to ε_F. *)
  Fact H_ε_ARC_from_LR Σ `{approxisRGpreS Σ} :
    forall σ σ',
    ARcoupl (lim_exec (RED (PRF_real PRF_scheme_F #Q), σ))
      (lim_exec (RED (PRF_rand PRF_scheme_F #Q), σ'))
      eq ε_F.
  Proof.
    intros.
    unshelve eapply approximates_coupling ; eauto.
    1: exact (fun _ => lrel_bool).
    1: apply cond_nonneg.
    1: by iIntros (???) "#(%b&->&->)".
    iIntros.
    by iApply (proj1 H_ε_PRF).
  Qed.

  (* Alternatively, we can directly make the (weaker) assumption that such an
     ε_F-ARcoupling exists, since our only use for H_ε_PRF is to build this
     ARcoupling. *)
  Hypothesis H_ε_ARC :
    forall σ σ',
    ARcoupl (lim_exec (RED (PRF_real PRF_scheme_F #Q), σ))
      (lim_exec (RED (PRF_rand PRF_scheme_F #Q), σ'))
      eq ε_F.

  From clutch.approxis.examples Require Import advantage.

  Let ε_adv :=
        advantage adversary
          (RED (PRF_real PRF_scheme_F #Q))
          (RED (PRF_rand PRF_scheme_F #Q)).

  (* We shouldn't expect to use the same adversary on both sides. *)
  Definition pr_dist (X Y : expr)
    (σ σ' : state) (v : val) :=
    Rabs ( (( lim_exec (X, σ)) v) - (lim_exec (Y, σ') v) )%R.

  Fact pr_dist_triangle' X Y Z σ σ' σ'' v :
    (pr_dist X Z σ σ'' v <= (pr_dist X Y σ σ' v) + (pr_dist Y Z σ' σ'' v))%R.
  Proof.
    rewrite /pr_dist. etrans. 2: apply Rabs_triang. right. f_equal. lra.
  Qed.

  Fact pr_dist_triangle X Y Z v ε1 ε2 ε3 :
    ((∀ σ σ', pr_dist X Y σ σ' v <= ε1) →
     (∀ σ σ', pr_dist Y Z σ σ' v <= ε2) →
     (ε1 + ε2 <= ε3) →
     ∀ σ σ', pr_dist X Z σ σ' v <= ε3)%R.
  Proof.
    clear.
    intros. etrans.
    1: eapply (pr_dist_triangle' _ Y _ _ σ).
    etrans. 2: eauto.
    apply Rplus_le_compat => //.
  Qed.


  Fact adv_is_good : Rbar.Rbar_le ε_adv (Rbar.Finite ε_F).
  Abort.

  (* Compose lemmas and the assumption H_ε_ARC to get an ARC. *)
  Lemma prf_cpa_ARC Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl
      (lim_exec ((adversary (CPA_real sym_scheme_F #Q)), σ))
      (lim_exec ((adversary (CPA_rand sym_scheme_F #Q)), σ'))
      (=)
      (ε_Q + ε_F).
  Proof.
    set (ε := (ε_Q + NNRbar_to_real (NNRbar.Finite ε_F))%R).
    assert (0 <= ε_F)%R by apply cond_nonneg. pose proof ε_collision_pos.
    assert (0 <= ε)%R.
    { unfold ε. apply Rplus_le_le_0_compat ; auto. }
    replace ε with (0+ε)%R by lra.
    eapply ARcoupl_eq_trans_l => //.
    1: eapply reduction_ARC => //.
    replace ε with (ε_F+ε_Q)%R by (unfold ε ; lra).
    eapply ARcoupl_eq_trans_l => //.
    1: eapply H_ε_ARC.
    replace ε_Q with (0 + ε_Q)%R by lra.
    eapply ARcoupl_eq_trans_l => //.
    1: eapply F_I_ARC => //.
    replace ε_Q with (0 + ε_Q)%R by lra.
    eapply ARcoupl_eq_trans_l => //.
    (* 1: eapply rand_real_ARC => //.
       replace ε_Q with (0 + ε_Q)%R by lra.
       eapply ARcoupl_eq_trans_l => //. *)
    1: eapply reduction'_ARC => //.
    replace ε_Q with (ε_Q + 0)%R by lra.
    eapply ARcoupl_eq_trans_l => //.
    1: eapply cpa_I_ARC => //.
    1:
      (* TODO ugh *)
      admit.
    eapply cpa_F_ARC => //.
    Unshelve. all: eauto.
  Admitted.

  (* The converse direction of the refinement. We expect it to hold with the
     same bound. *)
  Lemma prf_cpa_ARC' Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl
      (lim_exec ((adversary (CPA_rand sym_scheme_F #Q)), σ))
      (lim_exec ((adversary (CPA_real sym_scheme_F #Q)), σ'))
      (=)
      ((Q * Q / (2 * S Input)) + ε_F).
  Admitted.

  Corollary CPA_bound_1 Σ `{approxisRGpreS Σ} σ σ' :
    ( (lim_exec ((adversary (CPA_real sym_scheme_F #Q)), σ) #true)
      <=
      (lim_exec ((adversary (CPA_rand sym_scheme_F #Q)), σ') #true)
      + ((Q * Q / (2 * S Input)) + ε_F))%R.
  Proof.
    apply ARcoupl_eq_elim.
    by eapply prf_cpa_ARC.
  Qed.

  Corollary CPA_bound_2 Σ `{approxisRGpreS Σ} σ σ' :
    ( (lim_exec ((adversary (CPA_rand sym_scheme_F #Q)), σ) #true)
      <=
      (lim_exec ((adversary (CPA_real sym_scheme_F #Q)), σ') #true)
      + ((Q * Q / (2 * S Input)) + ε_F))%R.
  Proof using CPA_rand CPA_real Cipher F F_typed H_in_out
    H_ε_ARC H_ε_PRF Input Key Message Output Q adversary adversary_typed keygen
    keygen_typed ε_F
  .
    apply ARcoupl_eq_elim.
    by eapply prf_cpa_ARC'.
  Qed.

  Theorem CPA_bound Σ `{approxisRGpreS Σ} σ σ' :
    (Rabs (((lim_exec ((adversary (CPA_real sym_scheme_F #Q)), σ)) #true) -
             ((lim_exec ((adversary (CPA_rand sym_scheme_F #Q)), σ')) #true)) <=
       (Q * Q / (2 * S Input)) + ε_F)%R.
  Proof using CPA_rand CPA_real Cipher F F_typed H_in_out
    H_ε_ARC H_ε_PRF Input Key Message Output Q adversary adversary_typed keygen
    keygen_typed ε_F
  .
    apply Rabs_le.
    pose proof CPA_bound_1 Σ σ σ' as h1.
    pose proof CPA_bound_2 Σ σ' σ as h2.
    split ; lra.
  Qed.

  (* Instead of making an assumption about F at the ARcoupl level, we can work
  directly with pr_dist. We hence lower all the reduction lemmas to the pr_dist
  level and compose there. *)
  Lemma red_to_prf Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl (lim_exec (adversary (CPA_real sym_scheme_F #Q), σ))
      (lim_exec ((RED (PRF_real PRF_scheme_F #Q)), σ')) eq 0%R.
  Proof.
    eapply reduction_ARC => //.
  Qed.

  (* TODO prove this direction *)
  Hypothesis red_to_prf' : forall Σ `{approxisRGpreS Σ} σ σ',
    ARcoupl (lim_exec ((RED (PRF_real PRF_scheme_F #Q)), σ'))
      (lim_exec (adversary (CPA_real sym_scheme_F #Q), σ)) eq 0%R.

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

  Lemma red_from_prf Σ `{approxisRGpreS Σ} σ σ' :
    ARcoupl
      (lim_exec (RED (PRF_rand PRF_scheme_F #Q), σ))
      (lim_exec (adversary (CPA_rand sym_scheme_F #Q), σ'))
      (=)
      ε_Q.
  Proof.
    pose proof ε_collision_pos.
    replace ε_Q with (0 + ε_Q)%R by lra.
    eapply ARcoupl_eq_trans_l => //.
    1: eapply F_I_ARC => //.
    replace ε_Q with (0 + ε_Q)%R by lra.
    eapply ARcoupl_eq_trans_l => //.
    1: eapply reduction'_ARC => //.
    replace ε_Q with (ε_Q + 0)%R by lra.
    eapply ARcoupl_eq_trans_l => //.
    1: eapply cpa_I_ARC => //.
    1: admit.
    eapply cpa_F_ARC => //.
    Unshelve. all: eauto.
  Admitted.

  (* TODO prove this reverse direction *)
  Hypothesis red_from_prf' : forall Σ `{approxisRGpreS Σ} σ σ',
    ARcoupl
      (lim_exec (adversary (CPA_rand sym_scheme_F #Q), σ'))
      (lim_exec (RED (PRF_rand PRF_scheme_F #Q), σ))
      (=)
      ε_Q.

  Lemma pr_dist_F_adv `{approxisRGpreS Σ} v σ σ' :
    (pr_dist (RED (PRF_rand PRF_scheme_F #Q)) (adversary (CPA_rand sym_scheme_F #Q)) σ σ' v
     <= ε_Q)%R.
  Proof.
    rewrite /pr_dist.
    eapply Rabs_le.
    split.
    - opose proof (ARcoupl_eq_elim _ _ _ (red_from_prf' _ σ σ') v) as hred.
      set (x := lim_exec (RED _, σ) v).
      set (y := (lim_exec (adversary _, σ')) v).
      assert (y <= x + ε_Q)%R by easy.
      lra.
    - opose proof (ARcoupl_eq_elim _ _ _ (red_from_prf _ σ σ') v) as hred.
      set (x := lim_exec (RED _, σ) v).
      set (y := (lim_exec (adversary _, σ')) v).
      assert (x <= y + ε_Q)%R by easy.
      lra.
  Qed.

  Variable PPT : expr → Prop.
  Hypothesis adv_in_PPT : PPT adversary.
  Hypothesis RED_in_PPT : PPT adversary → PPT RED.

  Hypothesis H_ε_pr_dist :
    forall σ σ',
      (pr_dist (RED (PRF_real PRF_scheme_F #Q)) (RED (PRF_rand PRF_scheme_F #Q)) σ σ' #true <= ε_F)%R.

  Theorem CPA_bound' Σ `{approxisRGpreS Σ} σ σ' :
    (Rabs (((lim_exec ((adversary (CPA_real sym_scheme_F #Q)), σ)) #true) -
             ((lim_exec ((adversary (CPA_rand sym_scheme_F #Q)), σ')) #true)) <=
       (Q * Q / (2 * S Input)) + ε_F)%R.
  Proof.
    eapply pr_dist_triangle.
    1: eapply pr_dist_adv_F.
    1: eapply pr_dist_triangle.
    1: eapply H_ε_pr_dist.
    1: eapply pr_dist_F_adv.
    1: right ; eauto.
    unfold ε_Q. lra.
  Qed.

End combined.
