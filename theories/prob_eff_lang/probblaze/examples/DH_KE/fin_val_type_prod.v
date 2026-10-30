From clutch.prob_eff_lang.probblaze Require Import notation types sem_def interp metatheory logic tactics proofmode.
From clutch.prob_eff_lang.probblaze Require sem_types.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq choice fintype.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import fin_val_type.
Import fintype.
Set Default Proof Using "Type*".

(** The product of two [fin_val]s.  A pair [(x, y)] is the value
    [(fvtval x, fvtval y)] and has integer code [int x * N2 + int y], where
    [N2 = card t2]; decoding splits a code with [quot]/[rem] by [N2]. *)

Section fin_val_type_prod.
  Context {t1 t2 : fin_val_type}.

  Program Definition prod_fvt : fin_val_type :=
    {| fvT := (fvT (fin_val_type := t1) * fvT (fin_val_type := t2))%type
     ; fvtval xy := PairV (fvtval xy.1) (fvtval xy.2) |}.
  Next Obligation.
    intros [x1 y1] [x2 y2] [= H1 H2] => /=.
    by rewrite (fvtval_inj _ _ H1) (fvtval_inj _ _ H2).
  Qed.

  Lemma prod_fvt_card :
    fin_val_type.card (fin_val_type := prod_fvt) =
      (fin_val_type.card (fin_val_type := t1) * fin_val_type.card (fin_val_type := t2))%nat.
  Proof. rewrite /fin_val_type.card /=. apply card_prod. Qed.

End fin_val_type_prod.

Section fin_val_type_struct_prod.
  Context {t1 t2 : fin_val_type} {s1 : @fin_val_type_struct t1} {s2 : @fin_val_type_struct t2}.

  #[local] Notation N2 := (fin_val_type.card (fin_val_type := t2)).

  Definition int_of_prod : syntax.val :=
    λ: "v", s1.(int_of_fvt) (Fst "v") * #N2 + s2.(int_of_fvt) (Snd "v").

  Definition prod_of_int : syntax.val :=
    λ: "n",
      match: s1.(fvt_of_int) ("n" `quot` #N2) with
        NONE => NONE
      | SOME "x" =>
          match: s2.(fvt_of_int) ("n" `rem` #N2) with
            NONE => NONE
          | SOME "y" => SOME ("x", "y")
          end
      end.

  Lemma int_of_prod_closed : is_closed_val int_of_prod.
  Proof. is_closed. Qed.
  Lemma prod_of_int_closed : is_closed_val prod_of_int.
  Proof. is_closed. Qed.

  (** Each component is duplicable, and [TBangProd_le] pushes the bang over the pair. *)
  Lemma τFT_prod_multi : le.MultiT (s1.(τFT) * s2.(τFT))%ty.
  Proof.
    eapply le.TTrans_le; last apply le.TBangProd_le.
    apply le.TProd_le; apply τFT_multi.
  Qed.

  Local Lemma RNil_rtype (τ : type) : RNil R⪯T τ.
  Proof. apply le.Once_le. exists true. apply le.RFlipNil_le. Qed.

  Local Lemma RNil_rctx (Γ : ctx) : RNil R⪯C Γ.
  Proof.
    induction Γ as [|[x t] Γ IH].
    - apply le.NilR_le.
    - apply (le.ConsR_le RNil (BNamed x) t Γ); [apply RNil_rtype | exact IH].
  Qed.

  (* A duplicable ([![MS]]) arrow in function position, as [App_typed] wants. *)
  Local Ltac coerce_fn :=
    eapply Sub_typed;
      [ apply CRefl_le | apply CRefl_le | apply RRefl_le | apply le.TBangElim_le | ].

  Lemma int_of_prod_typed : val_typed int_of_prod ((s1.(τFT) * s2.(τFT)) ⇾ TInt)%ty.
  Proof.
    apply Rec_val_typed; first done. cbn [ctx_insert].
    apply (Contraction_typed _ _ _ _ _ _ (BNamed "v") (s1.(τFT) * s2.(τFT))%ty);
      first apply τFT_prod_multi.
    eapply BinOp_typed; [apply syn_typed_bin_op_plus| |].
    - eapply BinOp_typed; [apply syn_typed_bin_op_mult| |apply Val_typed; apply Int_val_typed].
      eapply App_typed; [apply le.RNil_le|apply le.RNil_le|apply RNil_rtype|apply RNil_rctx| |].
      + eapply Fst_typed. apply Var_typed.
      + coerce_fn. apply Val_typed. apply int_of_fvt_typed.
    - eapply App_typed; [apply le.RNil_le|apply le.RNil_le|apply RNil_rtype|apply RNil_rctx| |].
      + eapply Snd_typed. apply Var_typed.
      + coerce_fn. apply Val_typed. apply int_of_fvt_typed.
    Unshelve. all: first [exact true | exact OS].
  Qed.

  Lemma prod_of_int_typed : val_typed prod_of_int (TInt ⇾ () + (s1.(τFT) * s2.(τFT)))%ty.
  Proof.
    apply Rec_val_typed; first done. cbn [ctx_insert].
    apply (Contraction_typed _ _ _ _ _ _ (BNamed "n") TInt); first apply le.TBangInt_le.
    eapply (Match_typed _ _ [("n", TInt)] ∅);
      [ (cbn; set_solver) | (cbn; set_solver) | (cbn; set_solver) | (cbn; set_solver) | | | ].
    - eapply App_typed; [apply le.RNil_le|apply le.RNil_le|apply RNil_rtype|apply RNil_rctx| |].
      + eapply BinOp_typed;
          [apply syn_typed_bin_op_quot|apply Var_typed|apply Val_typed; apply Int_val_typed].
      + coerce_fn. apply Val_typed. apply fvt_of_int_typed.
    - cbn [ctx_insert]. apply (Weakening_typed _ ∅ _ _ _ _ (BNamed "n") TInt).
      apply InjL_typed. apply Val_typed. apply Unit_val_typed.
    - cbn [ctx_insert].
      eapply (Match_typed _ _ [("x", s1.(τFT))] ∅);
        [ (cbn; set_solver) | (cbn; set_solver) | (cbn; set_solver) | (cbn; set_solver) | | | ].
      + eapply App_typed; [apply le.RNil_le|apply le.RNil_le|apply RNil_rtype|apply RNil_rctx| |].
        * eapply BinOp_typed; [apply syn_typed_bin_op_rem| |apply Val_typed; apply Int_val_typed].
          (* bring ["n"] in front of ["x"] *)
          eapply (Sub_typed _ _ [("n", TInt); ("x", s1.(τFT))] _ [("x", s1.(τFT))] RNil RNil _ TInt TInt).
          { cbn. exists TInt, [("x", s1.(τFT))], []. split; [done|]. split; [apply le.TRefl_le|].
            exists s1.(τFT), [], []. split; [done|]. split; [apply le.TRefl_le|done]. }
          { apply CRefl_le. }
          { apply RRefl_le. }
          { apply le.TRefl_le. }
          apply Var_typed.
        * coerce_fn. apply Val_typed. apply fvt_of_int_typed.
      + cbn [ctx_insert]. apply (Weakening_typed _ ∅ _ _ _ _ (BNamed "x") s1.(τFT)).
        apply InjL_typed. apply Val_typed. apply Unit_val_typed.
      + cbn [ctx_insert]. apply InjR_typed.
        eapply Pair_typed; [apply RNil_rtype|apply Var_typed|apply Var_typed].
    Unshelve. all: first [exact true | exact OS].
  Qed.

  Program Definition prod_fvts : @fin_val_type_struct (@prod_fvt t1 t2) :=
    {| int_of_fvt := int_of_prod ; fvt_of_int := prod_of_int ; τFT := (s1.(τFT) * s2.(τFT))%ty |}.
  Next Obligation. exact int_of_prod_closed. Defined.
  Next Obligation. exact prod_of_int_closed. Defined.
  Next Obligation. exact int_of_prod_typed. Defined.
  Next Obligation. exact prod_of_int_typed. Defined.
  Next Obligation. exact τFT_prod_multi. Defined.

End fin_val_type_struct_prod.

(* [quot]/[rem] on non-negative integers are [div]/[mod]; also for a zero divisor. *)
Lemma Z_quot_of_nat (n m : nat) : (Z.of_nat n `quot` Z.of_nat m)%Z = Z.of_nat (n `div` m).
Proof.
  destruct m as [|m]; first by destruct n.
  rewrite Z.quot_div_nonneg; [|lia|lia]. by rewrite Nat2Z.inj_div.
Qed.

Lemma Z_rem_of_nat (n m : nat) : (Z.of_nat n `rem` Z.of_nat m)%Z = Z.of_nat (n `mod` m).
Proof.
  destruct m as [|m]; first by destruct n.
  rewrite Z.rem_mod_nonneg; [|lia|lia]. by rewrite Nat2Z.inj_mod.
Qed.

Section fin_val_prod.
  Context `{!probblazeRGS Σ}.
  Context {t1 t2 : fin_val_type} {s1 : @fin_val_type_struct t1} {s2 : @fin_val_type_struct t2}.
  Context (fv1 : @fin_val Σ _ t1 s1) (fv2 : @fin_val Σ _ t2 s2).

  #[local] Notation N2 := (fin_val_type.card (fin_val_type := t2)).
  #[local] Notation PT := (@prod_fvt t1 t2).
  #[local] Notation INT := (@int_of_prod t1 t2 s1 s2).
  #[local] Notation DEC := (@prod_of_int t1 t2 s1 s2).

  Definition int_of_prod_sem (xy : fvT (fin_val_type := PT)) : nat :=
    (int_of_fvt_sem (fin_val := fv1) xy.1 * N2 + int_of_fvt_sem (fin_val := fv2) xy.2)%nat.

  Definition prod_of_int_sem (n : nat) : option (fvT (fin_val_type := PT)) :=
    match fvt_of_int_sem (fin_val := fv1) (n `div` N2), fvt_of_int_sem (fin_val := fv2) (n `mod` N2) with
    | Some x, Some y => Some (x, y)
    | _, _ => None
    end.

  Lemma int_of_prod_sem_bound xy :
    (int_of_prod_sem xy < fin_val_type.card (fin_val_type := PT))%nat.
  Proof.
    rewrite prod_fvt_card /int_of_prod_sem.
    pose proof (int_of_fvt_sem_bound (fin_val := fv1) xy.1).
    pose proof (int_of_fvt_sem_bound (fin_val := fv2) xy.2). nia.
  Qed.

  Lemma prod_of_int_of_prod_sem n xy : prod_of_int_sem n = Some xy → int_of_prod_sem xy = n.
  Proof.
    rewrite /prod_of_int_sem /int_of_prod_sem.
    destruct (fvt_of_int_sem (n `div` N2)) as [x|] eqn:Hx; last done.
    destruct (fvt_of_int_sem (n `mod` N2)) as [y|] eqn:Hy; last done.
    intros [= <-]. simpl.
    rewrite (fvt_of_int_of_fvt_sem _ _ Hx) (fvt_of_int_of_fvt_sem _ _ Hy).
    rewrite Nat.mul_comm. symmetry. apply Nat.Div0.div_mod.
  Qed.

  Lemma int_of_prod_of_int_sem xy : prod_of_int_sem (int_of_prod_sem xy) = Some xy.
  Proof.
    destruct xy as [x y]. rewrite /prod_of_int_sem /int_of_prod_sem /=.
    pose proof (int_of_fvt_sem_bound (fin_val := fv2) y).
    rewrite Nat.div_add_l; [|lia]. rewrite (Nat.div_small (int_of_fvt_sem y)) // Nat.add_0_r.
    rewrite Nat.add_comm Nat.Div0.mod_add Nat.mod_small //.
    by rewrite !int_of_fvt_of_int_sem.
  Qed.

  Lemma brel_int_of_prod_correct_l E K xy X R e :
    (BREL fill K #(int_of_prod_sem xy) ≤ e @ E <|X|> {{R}}) -∗
    BREL fill K (INT (fvtval (fin_val_type := PT) xy)) ≤ e @ E <|X|> {{R}}.
  Proof.
    iIntros "H". destruct xy as [x y]. rewrite /int_of_prod /int_of_prod_sem /=. brel_pures_l.
    iApply (brel_int_of_fvt_sem_correct_l (fin_val := fv2)). rewrite fill_app /=.
    iApply (brel_int_of_fvt_sem_correct_l (fin_val := fv1)). rewrite fill_app /=.
    brel_pures_l. by rewrite Nat2Z.inj_add Nat2Z.inj_mul.
  Qed.

  Lemma brel_int_of_prod_correct_r E K xy X R e :
    (BREL e ≤ fill K #(int_of_prod_sem xy) @ E <|X|> {{R}}) -∗
    BREL e ≤ fill K (INT (fvtval (fin_val_type := PT) xy)) @ E <|X|> {{R}}.
  Proof.
    iIntros "H". destruct xy as [x y]. rewrite /int_of_prod /int_of_prod_sem /=. brel_pures_r.
    iApply (brel_int_of_fvt_sem_correct_r (fin_val := fv2)). rewrite fill_app /=.
    iApply (brel_int_of_fvt_sem_correct_r (fin_val := fv1)). rewrite fill_app /=.
    brel_pures_r. by rewrite Nat2Z.inj_add Nat2Z.inj_mul.
  Qed.

  Lemma brel_prod_of_int_correct_l E K X R e n xy :
    prod_of_int_sem n = Some xy →
    (BREL fill K (SOMEV (fvtval (fin_val_type := PT) xy)) ≤ e @ E <|X|> {{R}}) -∗
    BREL fill K (DEC #n) ≤ e @ E <|X|> {{R}}.
  Proof.
    rewrite /prod_of_int_sem.
    destruct (fvt_of_int_sem (n `div` N2)) as [x|] eqn:Hx; last done.
    destruct (fvt_of_int_sem (n `mod` N2)) as [y|] eqn:Hy; last done.
    intros [= <-]. iIntros "H". rewrite /prod_of_int. brel_pures_l.
    rewrite Z_quot_of_nat.
    iApply (brel_fvt_of_int_correct_l (fin_val := fv1) _ (K ++ [CaseCtx _ _])); first exact Hx.
    rewrite fill_app /=. brel_pures_l. rewrite Z_rem_of_nat.
    iApply (brel_fvt_of_int_correct_l (fin_val := fv2) _ (K ++ [CaseCtx _ _])); first exact Hy.
    rewrite fill_app /=. by brel_pures_l.
  Qed.

  Lemma brel_prod_of_int_correct_r E K X R e n xy :
    prod_of_int_sem n = Some xy →
    (BREL e ≤ fill K (SOMEV (fvtval (fin_val_type := PT) xy)) @ E <|X|> {{R}}) -∗
    BREL e ≤ fill K (DEC #n) @ E <|X|> {{R}}.
  Proof.
    rewrite /prod_of_int_sem.
    destruct (fvt_of_int_sem (n `div` N2)) as [x|] eqn:Hx; last done.
    destruct (fvt_of_int_sem (n `mod` N2)) as [y|] eqn:Hy; last done.
    intros [= <-]. iIntros "H". rewrite /prod_of_int. brel_pures_r.
    rewrite Z_quot_of_nat.
    iApply (brel_fvt_of_int_correct_r (fin_val := fv1) _ (K ++ [CaseCtx _ _])); first exact Hx.
    rewrite fill_app /=. brel_pures_r. rewrite Z_rem_of_nat.
    iApply (brel_fvt_of_int_correct_r (fin_val := fv2) _ (K ++ [CaseCtx _ _])); first exact Hy.
    rewrite fill_app /=. by brel_pures_r.
  Qed.

  Lemma brel_prod_of_int_none_l E K X R e n :
    prod_of_int_sem n = None →
    (BREL fill K NONEV ≤ e @ E <|X|> {{R}}) -∗
    BREL fill K (DEC #n) ≤ e @ E <|X|> {{R}}.
  Proof.
    rewrite /prod_of_int_sem. intros Hn. iIntros "H". rewrite /prod_of_int. brel_pures_l.
    rewrite Z_quot_of_nat.
    destruct (fvt_of_int_sem (n `div` N2)) as [x|] eqn:Hx.
    - iApply (brel_fvt_of_int_correct_l (fin_val := fv1) _ (K ++ [CaseCtx _ _])); first exact Hx.
      rewrite fill_app /=. brel_pures_l. rewrite Z_rem_of_nat.
      destruct (fvt_of_int_sem (n `mod` N2)) as [y|] eqn:Hy; first done.
      iApply (brel_fvt_of_int_none_l (fin_val := fv2) _ (K ++ [CaseCtx _ _])); first exact Hy.
      rewrite fill_app /=. by brel_pures_l.
    - iApply (brel_fvt_of_int_none_l (fin_val := fv1) _ (K ++ [CaseCtx _ _])); first exact Hx.
      rewrite fill_app /=. by brel_pures_l.
  Qed.

  Lemma brel_prod_of_int_none_r E K X R e n :
    prod_of_int_sem n = None →
    (BREL e ≤ fill K NONEV @ E <|X|> {{R}}) -∗
    BREL e ≤ fill K (DEC #n) @ E <|X|> {{R}}.
  Proof.
    rewrite /prod_of_int_sem. intros Hn. iIntros "H". rewrite /prod_of_int. brel_pures_r.
    rewrite Z_quot_of_nat.
    destruct (fvt_of_int_sem (n `div` N2)) as [x|] eqn:Hx.
    - iApply (brel_fvt_of_int_correct_r (fin_val := fv1) _ (K ++ [CaseCtx _ _])); first exact Hx.
      rewrite fill_app /=. brel_pures_r. rewrite Z_rem_of_nat.
      destruct (fvt_of_int_sem (n `mod` N2)) as [y|] eqn:Hy; first done.
      iApply (brel_fvt_of_int_none_r (fin_val := fv2) _ (K ++ [CaseCtx _ _])); first exact Hy.
      rewrite fill_app /=. by brel_pures_r.
    - iApply (brel_fvt_of_int_none_r (fin_val := fv1) _ (K ++ [CaseCtx _ _])); first exact Hx.
      rewrite fill_app /=. by brel_pures_r.
  Qed.

  Lemma τFT_prod_subtype v1 v2 η μ δ ξ :
    sem_ty_fvt (vg := PT) v1 v2 ⊢
      interp._ty η μ δ (s1.(τFT) * s2.(τFT))%ty ξ v1 v2.
  Proof.
    iIntros "(%xy & -> & ->)". destruct xy as [x y]. simpl.
    iExists _, _, _, _. do 2 (iSplit; [done|]).
    iSplitL; [iApply (τFT_subtype (fin_val := fv1))|iApply (τFT_subtype (fin_val := fv2))];
      by iExists _.
  Qed.

  Lemma fvtval_prod_typed (xy : fvT (fin_val_type := PT)) :
    val_typed (fvtval (fin_val_type := PT) xy) (s1.(τFT) * s2.(τFT))%ty.
  Proof. destruct xy as [x y]. apply (Pair_val_typed (fvtval x) (fvtval y)); apply fvtval_typed. Qed.

  Program Definition prod_fv : @fin_val Σ _ PT (@prod_fvts t1 t2 s1 s2) :=
    {| int_of_fvt_sem := int_of_prod_sem
     ; fvt_of_int_sem := prod_of_int_sem |}.
  Next Obligation. intros. apply τFT_prod_subtype. Defined.
  Next Obligation. exact fvtval_prod_typed. Defined.
  Next Obligation. exact int_of_prod_sem_bound. Defined.
  Next Obligation. exact prod_of_int_of_prod_sem. Defined.
  Next Obligation. exact int_of_prod_of_int_sem. Defined.
  Next Obligation. intros. apply brel_int_of_prod_correct_l. Defined.
  Next Obligation. intros. apply brel_int_of_prod_correct_r. Defined.
  Next Obligation. intros. by apply brel_prod_of_int_correct_l. Defined.
  Next Obligation. intros. by apply brel_prod_of_int_correct_r. Defined.
  Next Obligation. intros. by apply brel_prod_of_int_none_l. Defined.
  Next Obligation. intros. by apply brel_prod_of_int_none_r. Defined.

  (** The semantic type of the product is the product of the semantic types. *)
  Lemma sem_τFT_prod v1 v2 :
    sem_τFT (fin_val := prod_fv) v1 v2 ⊣⊢
      sem_types.sem_ty_prod (sem_τFT (fin_val := fv1)) (sem_τFT (fin_val := fv2)) v1 v2.
  Proof.
    iSplit.
    - iIntros "(%xy & -> & ->)". destruct xy as [x y].
      iExists (fvtval x), (fvtval x), (fvtval y), (fvtval y).
      do 2 (iSplit; [done|]). iSplit; by iExists _.
    - iIntros "(% & % & % & % & -> & -> & (%x & -> & ->) & (%y & -> & ->))".
      by iExists (x, y).
  Qed.

End fin_val_prod.
