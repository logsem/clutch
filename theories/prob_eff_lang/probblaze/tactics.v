From iris.proofmode Require Import base proofmode classes environments coq_tactics ltac_tactics reduction.
From iris.base_logic.lib Require Import  na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra 
  class_instances notation.

Module Export Tactics.

Tactic Notation "foldkont" ident(k) open_constr(kctx) :=
    match goal with
    | |- context[KontV ?kont] =>
        unify kont kctx ; set (k := KontV kont)
    end.

  Tactic Notation "foldkont" ident(k) := foldkont k _.

  Tactic Notation "foldkont" := let k := fresh "kont" in foldkont k.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  let rec go K e :=
  match e with
  | _ => tac K e
  | App ?e (Val ?v) => go (K ++ [AppLCtx v]) e
  | App ?e1 ?e2 => go (K ++ [AppRCtx e1]) e2
  | UnOp ?op ?e => go (K ++ [UnOpCtx op]) e
  | BinOp ?op ?e (Val ?v) => go (K ++ [BinOpLCtx op v]) e
  | BinOp ?op ?e1 ?e2 => go (K ++ [BinOpRCtx op e1]) e2
  | If ?e0 ?e1 ?e2 => go (K ++ [IfCtx e1 e2]) e0
  | Pair ?e (Val ?v) => go (K ++ [PairLCtx v]) e
  | Pair ?e1 ?e2 => go (K ++ [PairRCtx e1]) e2
  | Fst ?e => go (K ++ [FstCtx]) e
  | Snd ?e => go (K ++ [SndCtx]) e
  | InjL ?e => go (K ++ [InjLCtx]) e
  | InjR ?e => go (K ++ [InjRCtx]) e
  | Case ?e0 ?e1 ?e2 => go (K ++ [CaseCtx e1 e2]) e0
  | AllocN ?e (Val ?v) => go (K ++ [AllocNLCtx v]) e
  | AllocN ?e1 ?e2 => go (K ++ [AllocNRCtx e1]) e2
  | Load ?e => go (K ++ [LoadCtx]) e
  | Store ?e (Val ?v) => go (K ++ [StoreLCtx v]) e
  | Store ?e1 ?e2 => go (K ++ [StoreRCtx e1]) e2
  | AllocTape ?e => go (K ++ [AllocTapeCtx]) e
  | Rand ?e (Val ?v) => go (K ++ [RandLCtx v]) e
  | Rand ?e1 ?e2 => go (K ++ [RandRCtx e1]) e2
  end in go (@nil syntax.frame) e.

  
 (* reshape_expr from meas_lang modified to match syntax for prob_eff_lang*) 
 Ltac reshape_expr_eff e tac :=
    let rec go K e :=
      match e with
      | _ => tac K e
      | App ?e (Val ?v) => go (AppLCtx v :: K) e
      | App ?e1 ?e2 => go (AppRCtx e1 :: K) e2
      | UnOp ?op ?e => go (UnOpCtx op :: K) e
      | BinOp ?op ?e (Val ?v) => go (BinOpLCtx op v :: K) e
      | BinOp ?op ?e1 ?e2 => go (BinOpRCtx op e1 :: K) e2
      | If ?e0 ?e1 ?e2 => go (IfCtx e1 e2 :: K) e0
      | Pair ?e (Val ?v) => go (PairLCtx v :: K) e
      | Pair ?e1 ?e2 => go (PairRCtx e1 :: K) e2
      | Fst ?e => go (FstCtx :: K) e
      | Snd ?e => go (SndCtx :: K) e
      | InjL ?e => go (InjLCtx :: K) e
      | InjR ?e => go (InjRCtx :: K) e
      | Case ?e0 ?e1 ?e2 => go (CaseCtx e1 e2 :: K) e0
      | AllocN ?e (Val ?v) => go (AllocNLCtx v :: K) e
      | AllocN ?e1 ?e2 => go (AllocNRCtx e1 :: K) e2
      | Load ?e => go (LoadCtx :: K) e
      | Store ?e (Val ?v) => go (StoreLCtx v :: K) e
      | Store ?e1 ?e2 => go (StoreRCtx e1 :: K) e2
      | AllocTape ?e => go (AllocTapeCtx :: K) e
      | Rand ?e (Val ?v) => go (RandLCtx v :: K) e
      | Rand ?e1 ?e2 => go (RandRCtx e1 :: K) e2
      | Tick ?e => go (TickCtx :: K) e
      | Do ?n ?e => go (DoCtx n :: K) e
      | Handle ?hs ?m ?n ?e1 ?e2 ?e3 => go (HandleCtx hs m n e2 e3 :: K) e1
      end in go (@ectx_item) e.

 (* a variant of tp_bind_helper for prob_eff_lang*)
 Ltac tp_bind_helper_eff :=
   simpl;
    lazymatch goal with
  | |- fill ?K ?e = fill _ ?efoc =>
     reshape_expr_eff e ltac:(fun K' e' =>
       unify e' efoc;
       let K'' := eval cbn[app] in (K' ++ K) in
       replace (fill K e) with (fill K'' e') by (by rewrite ?fill_app))
  | |- ?e = fill _ ?efoc =>
     reshape_expr_eff e ltac:(fun K' e' =>
       unify e' efoc;
       replace e with (fill K' e') by (by rewrite ?fill_app))
    end; reflexivity.

 
 (* a variant of tp_binder_helper using the IntoCtx typeclass*)
 Ltac tp_binder_helper_eff_into_ctx :=
   simpl;
   lazymatch goal with
   | |- fill ?K ?e = fill _ ?efoc =>
       let Hk := fresh in
       unshelve eassert (IntoCtx e (TCEq efoc) _) as Hk by tc_solve;
       lazymatch type of Hk with
       | (IntoCtx _ _ ?K') =>
          let K'' := eval cbn[app] in (K' ++ K) in
          replace (fill K e) with (fill K'' e) by (by rewrite ?fill_app)
       end
   | |- ?e = fill _ ?efoc =>
       let Hk := fresh in
       unshelve eassert (IntoCtx e (TCEq efoc) _) as Hk by tc_solve;
       lazymatch type of Hk with
       | (IntoCtx _ _ ?K') =>
         replace e with (fill K' e) by (by rewrite ?fill_app)
       end
   end; reflexivity.
                 
Tactic Notation "tac_bind_helper" open_constr(efoc) :=
  lazymatch goal with
  | |- fill ?K ?e = fill _ _ =>
     reshape_expr_eff e ltac:(fun K' e' =>
       unify e' efoc;
       let K'' := eval cbn[app] in (K' ++ K) in
       replace (fill K e) with (fill K'' e') by (by rewrite ?fill_app))
  | |- ?e = fill _ _ =>
     reshape_expr_eff e ltac:(fun K' e' =>
       unify e' efoc;
       replace e with (fill K' e') by (by rewrite ?fill_app))
  end; reflexivity.

Lemma tac_brel_bind_l `{!probblazeRGS Σ} eₗ eₗ' eᵣ K Δ E X R:
  (*eₗ = fill K eₗ' ->*)
  IntoCtx eₗ (TCEq eₗ') K ->
  envs_entails Δ (brel E (fill K eₗ') eᵣ X R) ->
  envs_entails Δ (brel E eₗ eᵣ X R).
  Proof. 
  intros. apply tc_eq_fill in H. rewrite <- H. auto. Qed.

  Lemma tac_brel_bind_r `{!probblazeRGS Σ} eₗ eᵣ eᵣ' K Δ E X R:
    (*eᵣ = fill K eᵣ' ->*)
    IntoCtx eᵣ (TCEq eᵣ') K ->
    envs_entails Δ (brel E eₗ (fill K eᵣ') X R) ->
    envs_entails Δ (brel E eₗ eᵣ X R).
  Proof.
    intros. apply tc_eq_fill in H. rewrite <- H. auto. Qed.

  Tactic Notation "brel_bind_l" :=
    iStartProof;
    eapply (tac_brel_bind_l);
    [ tc_solve
    | ].

  Tactic Notation "brel_bind_r" :=
    iStartProof;
    eapply (tac_brel_bind_r);
    [ tc_solve
    | ].

  Tactic Notation "tac_bind_helper" open_constr(efoc) :=
  lazymatch goal with
  | |- fill ?K ?e = fill _ _ =>
     reshape_expr_eff e ltac:(fun K' e' =>
       unify e' efoc;
       let K'' := eval cbn[app] in (K' ++ K) in
       replace (fill K e) with (fill K'' e') by (by rewrite ?fill_app))
  | |- ?e = fill _ _ =>
     reshape_expr_eff e ltac:(fun K' e' =>
       unify e' efoc;
       replace e with (fill K' e') by (by rewrite ?fill_app))
  end; reflexivity.


  Ltac rel_bind_ctx_l K :=
    eapply (tac_brel_bind_l _ K);
    [pm_reflexivity || tp_bind_helper_eff
    |].

  Ltac rel_bind_ctx_r K :=
    eapply (tac_brel_bind_r _ K);
    [pm_reflexivity || tp_bind_helper_eff
    |].

  (*replace the expression on the left until the tactic tac can be applied to it*)
  Ltac brel_reshape_cont_l tac :=
    lazymatch goal with
    | |- envs_entails _ (brel _ (fill ?K ?e) _ _) =>
        reshape_expr_eff e ltac:(fun K' e' =>
                                   tac (K' ++ K) e')
    | |- envs_entails _ (brel _ ?e _ _) =>
        reshape_expr_eff e ltac:(fun K' e' => tac K' e')
    end.

  Ltac brel_reshape_cont_r tac :=
    lazymatch goal with
    | |- envs_entails _ (brel _ _ (fill ?K ?e) _) =>
        reshape_expr_eff e ltac:(fun K' e' =>
                                   tac (K' ++ K) e')
    | |- envs_entails _ (brel _ _ ?e _) =>
        reshape_expr_eff e ltac:(fun K' e' => tac K' e')
    end.

  Lemma tac_brel_load_l `{!probblazeRGS Σ} K Δ Δ' i1 p (l : loc) q v
     eₛ eₜ eₛ' R E L:
     IntoCtx eₛ (TCEq (Load (# l))) K →
     MaybeIntoLaterNEnvs 1 Δ Δ' →
     envs_lookup i1 Δ' = Some (p, l ↦{q} v)%I →
     eₛ' = fill K (of_val v) →
     envs_entails Δ' (brel E eₛ' eₜ L R) ->
     envs_entails Δ (brel E eₛ eₜ L R).
     Proof.
      rewrite envs_entails_unseal.
      iIntros (? ?? -> HΔ) "HΔ'".
      iDestruct (into_laterN_env_sound with "HΔ'") as "HΔ'". 
      iDestruct (envs_lookup_split with "HΔ'") as "[Hl Hclose]"; first done. 
      rewrite HΔ.
      apply tc_eq_fill in H.
      rewrite <- H.
      destruct p; simpl.
      -
       iDestruct "Hl" as "#Hl".
       iApply (brel_load_l E L R K l q v); iModIntro; try done.
       iIntros. iApply "Hclose". iApply "Hl".
      -  iApply (brel_load_l E L R K l q v with "Hl").
         iModIntro. iIntros "Hl". iApply "Hclose". iApply "Hl".
    Qed.

     Tactic Notation "brel_load_l" :=
       iStartProof;
       lazymatch goal with
        | |- environments.envs_entails _ (brel _ _ _ _ _) =>
             (*match goal with |- ?G => idtac "RAW GOAL:" G end;*)
             eapply tac_brel_load_l;
           [ tc_solve || fail "cannot find a Load operation"
            (* the first IntoCtx that looks for a load in a context*)
           | tc_solve (*maybelaterenvs *)
           | let l := match goal with
                       | |- _ = Some (_, (?l ↦{_} _)%I) => l end in
             iAssumptionCore || fail "brel_load_l: cannot find" l "↦ ?"
             (* look up the value that l points to*)
           | reflexivity || fail "eₛ' already set" (*the second IntoCtx *)
           | simpl (*new goal*) ]
        | |- _ => fail "brel_load_l: goal not a brel"
       end.
     
   Tactic Notation "test_brel_load_l" :=
  lazymatch goal with
  | |- environments.envs_entails _ (brel _ _ _ _ _) =>
      eapply tac_brel_load_l;
      [ tc_solve || fail "cannot find a load"
      | tc_solve || fail "cannot resolve laters"
      | let l := match goal with
                       | |- _ = Some (_, (?l ↦{_} _)%I) => l end in
             iAssumptionCore || fail "brel_load_l: cannot find" l "↦ ?"
      | reflexivity || fail "unable to unify with previous equality"
      | simpl; pm_prettify]
  end.
   

Lemma tac_brel_load_r `{probblazeRGS Σ} K Δ E i1 p (l : loc) q v eₛ eₜ eₜ' L R :
     IntoCtx eₜ (TCEq (Load (# l))) K →
     envs_lookup i1 Δ = Some (p, l ↦ₛ{q} v)%I →
     eₜ' = fill K (of_val v) →
     envs_entails Δ (brel E eₛ eₜ' L R) ->
     envs_entails Δ (brel E eₛ eₜ L R).
Proof.
      rewrite envs_entails_unseal. iIntros (? ? -> HΔ) "Hi".
      iDestruct (envs_lookup_split with "Hi") as "[Hl Hclose]"; first done.
      apply tc_eq_fill in H0. rewrite <- H0.
      rewrite HΔ. destruct p; simpl.
      - iDestruct "Hl" as "#Hl". iApply (brel_load_r with "Hl").
      iIntros "_". by iApply "Hclose".
      - by iApply (brel_load_r with "Hl").
Qed.

Tactic Notation "brel_load_r" :=
  iStartProof;
  lazymatch goal with
   | |- envs_entails _ (brel _ _ _ _ _) =>
       eapply tac_brel_load_r;
       [ tc_solve || fail "cannot find a load operation"
        | let l := match goal with
                    | |- _ = Some (_, (?l ↦ₛ{_} _)%I) => l end in
           iAssumptionCore || fail "brel_load_r: cannot find" l "↦ₛ ?"  (*look for the load on the right side*)
        | reflexivity
        | simpl (*new goal *)]
             
   | |- _ => fail "brel_load_r: goal not a brel"
   end.

     (* In approxis the lemma for rel_store_l(and _r) allows the storage of an expression, provided we know that IntoVal e v holds, however the brel_store_l lemma in probblaze reuires a value to be stored*)
Lemma tac_brel_store_l `{!probblazeRGS Σ} E K Δ Δ' Δ'' i1 (l: loc) v v' eₛ eₛ' eₜ L R :
  IntoCtx eₛ (TCEq (Store (#l) (of_val v))) K ->
  (*IntoVal e v ->*)
  MaybeIntoLaterNEnvs 1 Δ Δ' ->
  envs_lookup i1 Δ' = Some (false, l ↦ v')%I ->
  envs_simple_replace i1 false (Esnoc Enil i1 (l ↦ v)) Δ' = Some Δ'' ->
  eₛ' = fill K #()%V ->
  envs_entails Δ'' (brel E eₛ' eₜ L R) ->
  envs_entails Δ (brel E eₛ eₜ L R).
Proof.
  rewrite envs_entails_unseal. (*intros ?????? Hg.*)
  iIntros (??????) "Hi".
  apply tc_eq_fill in H. rewrite <- H. rewrite -> H3 in H4.
  rewrite into_laterN_env_sound envs_simple_replace_sound //; simpl.
  rewrite bi.later_sep.
  rewrite right_id.
  simpl in *.
  iDestruct "Hi" as "[Hl Hclose]".
  iApply (brel_store_l E L R K l v' v eₜ with "Hl").
  iModIntro. iIntros "Hl".
  iApply H4. iApply "Hclose". auto.
Qed.

Lemma tac_brel_store_r `{probblazeRGS Σ} E K Δ Δ' i1 (l: loc) v v' eₛ eₜ eₜ' L R :
  IntoCtx eₜ (TCEq (Store (#l) (of_val v))) K ->
  envs_lookup i1 Δ = Some (false, l ↦ₛ v')%I ->
  envs_simple_replace i1 false (Esnoc Enil i1 (l ↦ₛ v)) Δ = Some Δ' ->
  eₜ' = fill K #()%V ->
  envs_entails Δ' (brel E eₛ eₜ' L R) ->
  envs_entails Δ (brel E eₛ eₜ L R).
Proof.
  rewrite envs_entails_unseal.
  iIntros (?????) "Hi".
  apply tc_eq_fill in H0. rewrite <- H0. rewrite -> H3 in H4.
  rewrite envs_simple_replace_sound //; simpl.
  iDestruct "Hi" as "[Hl Hclose]".
  About brel_store_r.
  iApply (brel_store_r E L R eₛ K l v' v with "Hl").
  iIntros "Hl". iApply H4. iApply "Hclose". auto.
Qed.

Tactic Notation "brel_store_l" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (brel _ _ _ _ _ ) =>
      eapply tac_brel_store_l;
      [ tc_solve || fail "failed to find a store operation"
      | tc_solve (*later envs*)
      | let l:= match goal with
                | |- _ = Some (_, (?l ↦ _)%I) => l
                end in
        iAssumptionCore || fail "brel_store_l: cannot find" l "↦ ?"
      | reduction.pm_reflexivity || fail "unable to update environment after a store"
      | reflexivity
      | simpl (*new goal*)
      ]
  | |- _ => fail "brel_store_l: goal not a brel"
  end.

Tactic Notation "brel_store_r" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (brel _ _ _ _ _ ) =>
      eapply tac_brel_store_r;
      [ tc_solve || fail "failed to find a store operation"
      | let l:= match goal with
                | |- _ = Some (_, (?l ↦ₛ _)%I) => l
                end in
        iAssumptionCore || fail "brel_store_r: cannot find" l "↦ₛ ?"
      | reduction.pm_reflexivity || fail "unable to update environment after a store"
      | reflexivity
      | simpl (*new goal *)        
      ]
  | |- _ => fail "brel_store_r: goal not a brel"
  end.

Lemma tac_brel_alloc_l `{!probblazeRGS Σ} E K Δ Δ' eₛ eₜ v L R:
  IntoCtx eₛ (TCEq (Alloc (of_val v))) K ->
  MaybeIntoLaterNEnvs 1 Δ Δ' ->
  (*eₛ' = fill K (of_val #l) ->*)
  (envs_entails Δ' (∀ (l : loc),
                      (l ↦ v -∗ brel E (fill K (of_val #l)) eₜ L R))) ->
  envs_entails Δ (brel E eₛ eₜ L R).
Proof.
  rewrite envs_entails_unseal.
  iIntros (???) "Hi".
  rewrite into_laterN_env_sound /=.
  apply tc_eq_fill in H. rewrite <- H.
  (*rewrite -> H1 in H2.*)
  iApply (brel_alloc_l E L R K v eₜ).
  iModIntro. iApply H1. auto.
Qed.

Tactic Notation "brel_alloc_l" simple_intropattern(l) "as" constr(Hl) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (brel _ _ _ _ _ ) =>
      eapply tac_brel_alloc_l;
      [ match goal with |- IntoCtx ?e _ _ => idtac "eₛ is:" e end;
        tc_solve || fail "no reference allocation found in the goal"
      | tc_solve (*later envs *)
      | simpl; iIntros (l) Hl (* new goal *)
      ]
  | |- _ => fail "brel_alloc_l: goal not a brel"
  end.


Lemma tac_brel_alloc_r `{!probblazeRGS Σ} E K Δ eₛ eₜ v L R :
  IntoCtx eₜ (TCEq (Alloc (of_val v))) K ->
  (envs_entails Δ (∀ (l: loc),
     (l ↦ₛ v -∗ brel E eₛ (fill K (of_val #l)) L R))) ->
  envs_entails Δ (brel E eₛ eₜ L R).
Proof.
  rewrite envs_entails_unseal.
  iIntros (??) "Hi".
  apply tc_eq_fill in H. rewrite <- H.
  iApply (brel_alloc_r E L R eₛ K v).
  iApply H0. auto.
Qed.

Tactic Notation "brel_alloc_r" simple_intropattern(l) "as" constr(Hl) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (brel _ _ _ _ _) =>
      eapply tac_brel_alloc_r;
      [ tc_solve || fail "no reference allocation found in the goal"
      | simpl; iIntros (l) Hl (* new goal *)
      ]
  | |- _ => fail "brel_alloc_r: goal not a brel"
  end.

Lemma tac_brel_effect_l `{!probblazeRGS Σ} E K Δ Δ' e s eₛ eₜ L R:
  IntoCtx eₛ (TCEq (Effect s e)) K ->
  MaybeIntoLaterNEnvs 1 Δ Δ' ->
  (envs_entails Δ' (∀ (l : label),
                      (is_label l (DfracOwn 1) ==∗ brel E (fill K (lbl_subst s l e)) eₜ L R))) ->
  envs_entails Δ (brel E eₛ eₜ L R).
Proof.
  rewrite envs_entails_unseal.
  iIntros (???) "Hi".
  rewrite into_laterN_env_sound /=.
  apply tc_eq_fill in H. rewrite <- H.
  iApply (brel_effect_l E L R K s e eₜ).
  iModIntro. iApply H1. auto.
Qed.

Tactic Notation "brel_effect_l" simple_intropattern(l) "as" constr(Hl) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (brel _ _ _ _ _ ) =>
      eapply tac_brel_effect_l;
      [ tc_solve || fail "no effect allocation found in the goal"
      | tc_solve (*later envs *)
      | simpl; iIntros (l) Hl; iModIntro (* new goal *)
      ]
  | |- _ => fail "brel_effect_l: goal not a brel"
  end.


Lemma tac_brel_effect_r `{!probblazeRGS Σ} E K Δ eₛ eₜ e s L R :
  IntoCtx eₜ (TCEq (Effect s e)) K ->
  (envs_entails Δ (∀ (l: label),
     (spec_labels_frag l (DfracOwn 1) ==∗ brel E eₛ (fill K (lbl_subst s l e)) L R))) ->
  envs_entails Δ (brel E eₛ eₜ L R).
Proof.
  rewrite envs_entails_unseal.
  iIntros (??) "Hi".
  apply tc_eq_fill in H. rewrite <- H.
  iApply (brel_effect_r E L R eₛ K s e ).
  iApply H0. auto.
Qed.

Tactic Notation "brel_effect_r" simple_intropattern(l) "as" constr(Hl) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (brel _ _ _ _ _) =>
      eapply tac_brel_effect_r;
      [ tc_solve || fail "no effect allocation found in the goal"
      | simpl; iIntros (l) Hl; iModIntro (* new goal *)
      ]
  | |- _ => fail "brel_effect_r: goal not a brel"
  end.


(*tape allocation requires all invariant namespaces to be closed*)
Lemma tac_brel_alloctape_l `{!probblazeRGS Σ} K Δ Δ' eₛ eₜ N z L R:
  TCEq N (Z.to_nat z) ->
  IntoCtx eₛ (TCEq (AllocTape #z)) K ->
  MaybeIntoLaterNEnvs 1 Δ Δ' ->
  (envs_entails Δ' (∀ (α : loc),
      (α ↪N (N; []) -∗ brel ⊤ (fill K (of_val #lbl:α)) eₜ L R))) ->
  envs_entails Δ (brel ⊤ eₛ eₜ L R).
Proof.
  rewrite envs_entails_unseal.
  iIntros (????) "Hi".
  rewrite into_laterN_env_sound /=.
  apply tc_eq_fill in H0. rewrite <- H0.
  About brel_alloctape_l.
  iApply (brel_alloctape_l K N z eₜ L R).
  iModIntro. iApply H2. auto.
Qed.

Lemma tac_brel_alloctape_r `{!probblazeRGS Σ} K Δ eₛ eₜ N z L R:
  TCEq N (Z.to_nat z) ->
  IntoCtx eₜ (TCEq (AllocTape #z)) K ->
  (envs_entails Δ (∀ (α : loc),
    α ↪ₛ (N; []) -∗ brel ⊤ eₛ (fill K (of_val #lbl:α)) L R)) ->
  envs_entails Δ (brel ⊤ eₛ eₜ L R).
Proof.
  rewrite envs_entails_unseal.
  iIntros (???) "Hi".
  apply tc_eq_fill in H0. rewrite <- H0.
  About brel_alloctape_r.
  iApply (brel_alloctape_r K N z eₛ L R).
  iApply H1. auto.
Qed.

Tactic Notation "brel_alloctape_l" simple_intropattern(α) "as" constr(Hα) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (brel _ _ _ _ _) =>
      eapply tac_brel_alloctape_l;
      [ tc_solve (*math equality*)
      | tc_solve || fail "no tape allocation found in the goal"
      | tc_solve (*later envs*)
      | simpl; iIntros (α) Hα (* new goal *)
      ]
  | |- _ => fail "brel_alloctape_l: goal not a brel"
  end.

Tactic Notation "brel_alloctape_r" simple_intropattern(α) "as" constr(Hα) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (brel _ _ _ _ _) =>
      eapply tac_brel_alloctape_r;
      [ tc_solve (*math equality*)
      | tc_solve || fail "no tape allocation found in the goal"
      | simpl; iIntros (α) Hα (* new goal *)
      ]
  | |- _ => fail"brel_alloctape_r: goal not a brel"
  end.


Lemma tac_brel_rand_l `{probblazeRGS Σ} E K Δ Δ' i1 (α : loc) N (z : Z) n ns eₛ
  eₛ' eₜ L R:
  IntoCtx eₛ (TCEq (Rand #z (#lbl:α ))) K ->
  envs_lookup i1 Δ = Some (false, α ↪N (N; n::ns))%I ->
  TCEq N (Z.to_nat z) ->
  envs_simple_replace i1 false (Esnoc Enil i1 (α ↪N (N; ns))) Δ = Some Δ' ->
  eₛ' = fill K (of_val #n) ->
  envs_entails Δ' (⌜n ≤ N⌝ -∗ brel E eₛ' eₜ L R) ->
  envs_entails Δ (brel E eₛ eₜ L R).
Proof.
  rewrite envs_entails_unseal.
  iIntros (??????) "Hi".
  apply tc_eq_fill in H0.
  rewrite <- H0. rewrite -> H4 in H5.
  rewrite envs_simple_replace_sound //; simpl.
  iDestruct "Hi" as "[Hl Hclose]".
  iApply (brel_rand_l E K α N z n ns eₜ L R).
  iSplitL "Hl"; iModIntro; try auto. 
  iIntros "Hα". iApply H5. iApply "Hclose". auto.
Qed.


Lemma tac_brel_rand_r `{probblazeRGS Σ} E K Δ Δ' i1 (α : loc) N (z : Z) n ns eₛ eₜ
  eₜ' L R:
  IntoCtx eₜ (TCEq (Rand #z (#lbl:α))) K ->
  envs_lookup i1 Δ = Some (false, α ↪ₛN (N; n::ns))%I ->
  TCEq N (Z.to_nat z) ->
  envs_simple_replace i1 false (Esnoc Enil i1 (α ↪ₛN (N; ns))) Δ
  = Some Δ' ->
  eₜ' = fill K (of_val #n) ->
  envs_entails Δ' (⌜n ≤ N⌝ -∗ brel E eₛ eₜ' L R) ->
  envs_entails Δ (brel E eₛ eₜ L R).
Proof.
  rewrite envs_entails_unseal.
  iIntros (??????) "Hi".
  apply tc_eq_fill in H0.
  rewrite <- H0. rewrite -> H4 in H5.
  rewrite envs_simple_replace_sound //; simpl.
  iDestruct "Hi" as "[Hl Hclose]".
  About brel_rand_r.
  iApply (brel_rand_r E K α N z n ns eₛ L R with "Hl").
  iIntros "Hα". iApply H5. iApply "Hclose". auto.
Qed.

Tactic Notation "brel_rand_l" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (brel _ _ _ _ _ ) =>
      eapply tac_brel_rand_l;
      [ tc_solve ||
          fail "unable to find a rand operation in the goal"
      | let α := match goal with
                 | |- _ = Some ( _ ,(?α ↪N ( _ ; _ ))%I) => α
                 end in
        iAssumptionCore || fail "brel_rand_l: cannot find" α "↪N ?"
      | match goal with |- ?G => idtac "LOOKUP GOAL:" G end;
        tc_solve || fail "cant solve" (*math equality*)
      | pm_reflexivity || fail "unable to update environment"
      | reflexivity
      | simpl (*new goal*)
      ]
  | |- _ => fail "brel_rand_l: goal not a brel"
  end.

Tactic Notation "brel_rand_r" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (brel _ _ _ _ _ ) =>
      eapply tac_brel_rand_r;
      [ tc_solve || fail "unable to find a rand operation in the goal"
      | let α := match goal with
                 | |- _ = Some ( _ ,(?α ↪ₛN ( _ ; _ ))%I) => α
                 end in
        iAssumptionCore || fail "brel_rand_r: cannot find" α "↪ₛN ?"
      | tc_solve (*math equality*)
      | pm_reflexivity || fail "unable to update environment"
      | reflexivity
      | simpl (*new goal*)
      ]
  | |- _ => fail "brel_rand_r: goal not a brel"
  end.


End Tactics.

